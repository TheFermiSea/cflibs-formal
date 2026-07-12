# -*- coding: utf-8 -*-
"""
gated_delay_2dcos_engine.py
================================================================================
A highly optimized, double-precision JAX-accelerated implementation of Gated-Delay
Two-Dimensional Linear Correlation Spectroscopy (2DCOS) for time-resolved LIBS.

This engine features:
- Double-precision x64 numerical accuracy.
- Explicit vectorized Hilbert-Noda transformation matrix calculation.
- Strictly enforced skew-symmetric asynchronous matrix computation.
- Self-absorption indicator via off-diagonal wing-to-center correlation coefficients.
- Compositional projection onto the Aitchison simplex constraint space.
- Full compatibility with the JAX XLA compiler (jit) and vectorizer (vmap).

References:
- Noda I. (1993) Generalized 2D Correlation Spectroscopy, Appl. Spectrosc. 47:1329
# ERRATA: original citation dropped the co-author (Hirschberg). The real paper is
#   Hinnov E. & Hirschberg J.G. (1962) "Electron-Ion Recombination in Dense
#   Plasmas", Phys. Rev. 125:795 (helium/hydrogen afterglow plasmas, e-e-ion
#   three-body recombination). Corrected below; content of the citation
#   (three-body recombination) is otherwise accurate.
- Hinnov E. & Hirschberg J.G. (1962) Electron-Ion Recombination in Dense Plasmas, Phys. Rev. 125:795
- Aitchison J. (1986) The Statistical Analysis of Compositional Data
================================================================================
"""

import jax
# Enforce double-precision x64 floating point representations
jax.config.update("jax_enable_x64", True)

import jax.numpy as jnp
from typing import NamedTuple

# ERRATA (FATAL/SYNTAX): "2DCOSMetrics" is not a legal Python identifier — a
# class/variable name cannot start with a digit. The original file could not
# be parsed/imported at all. Renamed to TwoDCOSMetrics everywhere (class def,
# both function return annotations, and both `return TwoDCOSMetrics(...)` call
# sites below).
class TwoDCOSMetrics(NamedTuple):
    sync_matrix: jnp.ndarray       # Synchronous correlation matrix (n x n)
    async_matrix: jnp.ndarray      # Asynchronous correlation matrix (n x n)
    compositions: jnp.ndarray      # Projected simplex weight fractions (D_elements)
    raw_abundances: jnp.ndarray    # Unnormalized absolute abundances (D_elements)


@jax.jit
def process_gated_delay_2dcos(
    spectra_matrix: jnp.ndarray,
    idx_atom: jnp.ndarray,
    idx_ion: jnp.ndarray,
    xi_parameters: jnp.ndarray,
    epsilon: float = 1.0e-12
) -> TwoDCOSMetrics:
    """
    Executes the Gate-Delay 2DCOS inversion pipeline on raw LPP matrices.

    NOTE (Model B caveat, see monograph ERRATA C1/C2): this pipeline is NOT
    standardless or temperature-free. `xi_parameters` = xi(T) below must be
    supplied precomputed and encodes the partition functions U(T), the Saha
    exponential exp(-E_ion/kT), the T^{3/2} factor, the three-body scaling
    k_r(T) ~ T_e^(-9/2), and the absolute optical collection factor — so an
    independent temperature determination and absolute rate/intensity
    calibration are prerequisites, not eliminated unknowns. The word
    "standardless" was removed from this docstring accordingly.

    Parameters:
    -----------
    spectra_matrix : jnp.ndarray, shape (m_delays, n_channels)
        Double-precision temporal matrix containing area-normalized emission records.
        Typically pre-processed to remove baseline drift and continuum.
        # ERRATA (MINOR/robustness): requires m_delays >= 2. If m == 1 the
        # dynamic spectrum is identically zero and the (1/(m-1)) normalization
        # below divides by zero, silently producing NaN throughout sync_matrix
        # and async_matrix instead of a clear error. Enforced via an assert on
        # the static shape below (m is a Python int at trace time under jit,
        # so this check costs nothing at runtime and does not break tracing).
    idx_atom : jnp.ndarray, shape (D_elements,)
        Indices of channels corresponding to unblended neutral atomic lines.
        # ERRATA (MINOR/robustness): JAX's default gather semantics CLIP
        # out-of-range indices instead of raising (unlike NumPy, which raises
        # IndexError). An out-of-bounds idx_atom/idx_ion entry will silently
        # read channel (n-1) rather than fail. Caller must validate indices
        # are in [0, n) before invoking this jitted function.
    idx_ion : jnp.ndarray, shape (D_elements,)
        Indices of channels corresponding to coupled ionic lines of the same elements.
    xi_parameters : jnp.ndarray, shape (D_elements,)
        Precomputed thermodynamic integrated parameters xi(T) linking the Saha-Eggert
        and three-body recombination rate constants. (See Model B caveat above:
        this is a T- and instrument-dependent quantity, not a bundle of constants.)
    epsilon : float
        Regularizer added to the denominator of the Model B radical fraction to prevent
        NaN or Inf gradients during auto-differentiation at phase singularity regions.

    Returns:
    --------
    TwoDCOSMetrics
        NamedTuple containing computed correlation tensors and the projected Aitchison
        compositions.
    """
    m, n = spectra_matrix.shape
    # ERRATA (MINOR/robustness): guard the (m-1) normalization below. m is a
    # static (Python-int) shape value under jax.jit, so this assert is a
    # trace-time check, not a traced op — it does not affect compiled
    # performance and will not silently pass through to NaN outputs.
    assert m > 1, "process_gated_delay_2dcos requires at least 2 delay steps (m > 1); m=1 makes the dynamic spectrum identically zero and (1/(m-1)) divides by zero."

    # --------------------------------------------------------------------------
    # 1. Temporal Mean Subtraction to form the Dynamic Spectrum
    # --------------------------------------------------------------------------
    mean_spectrum = jnp.mean(spectra_matrix, axis=0)
    dynamic_spectra = spectra_matrix - mean_spectrum

    # --------------------------------------------------------------------------
    # 2. Synchronous Matrix Generation (Covariance Space)
    # --------------------------------------------------------------------------
    sync_matrix = (1.0 / (m - 1)) * jnp.matmul(dynamic_spectra.T, dynamic_spectra)

    # --------------------------------------------------------------------------
    # 3. Skew-Symmetric Hilbert-Noda Kernel Formulation
    # --------------------------------------------------------------------------
    # Generates a strictly skew-symmetric discrete Hilbert transform matrix.
    # Convention check: Noda's Hilbert-Noda matrix is defined N_jk = 0 (j=k),
    # N_jk = 1/(pi*(k-j)) (j != k) — see Noda, Appl. Spectrosc. 54:994 (2000)
    # and Noda, Appl. Spectrosc. 47:1329 (1993). With indexing='ij' below, j is
    # the row index and k the column index, and raw_kernel[j,k] = 1/(pi*(k-j)):
    # this matches Noda's convention exactly (orientation is NOT flipped).
    idx_range = jnp.arange(m)
    j, k = jnp.meshgrid(idx_range, idx_range, indexing='ij')
    diff = k - j
    raw_kernel = jnp.where(diff == 0, 0.0, 1.0 / (jnp.pi * diff))
    # ERRATA (MINOR/CODE, no functional bug): this symmetrization is a no-op.
    # raw_kernel[j,k] = 1/(pi*(k-j)) and raw_kernel[k,j] = 1/(pi*(j-k)) =
    # -1/(pi*(k-j)) are exact IEEE-754 negatives of one another (negation and
    # reciprocal-of-negation are both exact operations here), so
    # raw_kernel.T == -raw_kernel bit-for-bit already, making
    # 0.5*(raw_kernel - raw_kernel.T) identically equal to raw_kernel. This
    # differs from the async_matrix symmetrization in step 4 (which DOES
    # remove genuine floating-point accumulation error from chained matmuls).
    # Left in place as harmless defensive code; comment corrected to not
    # imply it changes any value.
    hilbert_kernel = 0.5 * (raw_kernel - raw_kernel.T)

    # --------------------------------------------------------------------------
    # 4. Asynchronous Matrix Generation
    # --------------------------------------------------------------------------
    transformed_dynamic = jnp.matmul(hilbert_kernel, dynamic_spectra)
    raw_async = (1.0 / (m - 1)) * jnp.matmul(dynamic_spectra.T, transformed_dynamic)
    # Enforce strict zero-diagonal and skew-symmetry to eliminate accumulation noise.
    # (This step is NOT a no-op: raw_async and raw_async.T are each products of
    # independent matmul calls whose floating-point accumulation order differs,
    # so this genuinely cancels rounding-level asymmetry — unlike step 3 above.)
    async_matrix = 0.5 * (raw_async - raw_async.T)

    # --------------------------------------------------------------------------
    # 5. Coordinate Extraction for Model B Inversion
    # --------------------------------------------------------------------------
    phi_atom_atom = jnp.diagonal(sync_matrix)[idx_atom]
    phi_ion_ion = jnp.diagonal(sync_matrix)[idx_ion]

    # Advanced 2D gather to extract off-diagonal asynchronous cross-peaks
    psi_ion_atom = async_matrix[idx_ion, idx_atom]

    # --------------------------------------------------------------------------
    # 6. Evaluation of the Invariant No-Ne Model B Equation
    # --------------------------------------------------------------------------
    # ERRATA (out of code-review scope, flagged not fixed): this block
    # faithfully implements monograph Section 6 as far as the missing
    # equations allow, but the structure raises dimensional-consistency
    # questions that only the underlying (unrecovered) equation can resolve:
    #   - phi_atom_atom / phi_ion_ion are VARIANCES (units of intensity^2) of
    #     the dynamic spectrum, not mean intensities; using sqrt(variance) as
    #     an abundance proxy (term_neutral) is an unusual choice relative to
    #     standard CF-LIBS practice, which uses line intensity directly.
    #   - term_neutral carries units of "intensity", while term_ionic scales
    #     as xi * sqrt(intensity^2 * intensity^2) / sqrt(intensity^2) =
    #     xi * intensity, so raw_abundances = term_neutral + term_ionic is
    #     only dimensionally consistent if xi_parameters is dimensionless —
    #     this is plausible but not verifiable without the source equation.
    #   - This is a physics/derivation question for the separate Model B
    #     audit (see ERRATA C1/C2), not a code defect; no code change made here.
    # Core neutral population variance tracking
    term_neutral = jnp.sqrt(jnp.maximum(phi_atom_atom, 0.0))

    # Saha-recombination coupled ionic population variance tracking
    numerator_covariant = jnp.maximum(phi_atom_atom * phi_ion_ion, 0.0)
    denominator_protected = jnp.abs(psi_ion_atom) + epsilon
    term_ionic = xi_parameters * (jnp.sqrt(numerator_covariant) / jnp.sqrt(denominator_protected))

    # Total absolute elemental abundances
    raw_abundances = term_neutral + term_ionic

    # --------------------------------------------------------------------------
    # 7. Manifold Projection onto the Aitchison Simplex (Compositional Closure)
    # --------------------------------------------------------------------------
    # ERRATA (FATAL/mislabel, monograph C3): softmax(log(x))_i = exp(log(x_i)) /
    # sum_j exp(log(x_j)) = x_i / sum_j(x_j) for x_i > 0 (jax.nn.softmax's
    # internal max-subtraction is only a numerical-stability trick and does not
    # change this identity). That is exactly the Aitchison CLOSURE operation
    # C(x) (Aitchison 1986), i.e. plain normalization to the simplex — it is
    # NOT an Isometric Log-Ratio (ILR) transform. A true ILR (Egozcue et al.,
    # "Isometric Logratio Transformations for Compositional Data Analysis",
    # Mathematical Geology 35:279, 2003) maps a D-part composition to an
    # UNCONSTRAINED (D-1)-dimensional real vector via an orthonormal
    # log-ratio basis; it does not itself return a point back on the simplex.
    # This code returns a D-dimensional vector summing to 1, which is the
    # closure, not ILR coordinates. Comment corrected below; the computation
    # itself (softmax-of-log as a numerically-safe closure map with
    # everywhere-defined gradients) is left unchanged since it is a
    # legitimate — if formerly mislabeled — closure operation.
    log_abundances = jnp.log(jnp.maximum(raw_abundances, 1.0e-15))
    projected_simplex = jax.nn.softmax(log_abundances)

    return TwoDCOSMetrics(
        sync_matrix=sync_matrix,
        async_matrix=async_matrix,
        compositions=projected_simplex,
        raw_abundances=raw_abundances
    )


@jax.jit
def evaluate_self_absorption_wing_coupling(
    async_matrix: jnp.ndarray,
    idx_center: int,
    idx_wing: int
) -> jnp.ndarray:
    """
    Computes an off-diagonal wing-to-center asynchronous phase-lag coefficient
    proposed as a self-absorption signature.

    NOTE (monograph ERRATA C8/C9): the vanishing async diagonal is a universal
    property of Noda's antisymmetric operator and does not by itself falsify any
    self-absorption model; and the wing-to-center "butterfly" signature this
    coefficient targets is an unvalidated hypothesis, not an established
    2DCOS-of-LIBS diagnostic. Treat the returned value as exploratory.

    Parameters:
    -----------
    async_matrix : jnp.ndarray, shape (n, n)
        Asynchronous correlation matrix (strictly zero diagonal).
    idx_center : int
        Index of the target transition coordinate matching the self-reversed line center (lambda_0).
    idx_wing : int
        Index of the coordinate matching the optically thin profile wing (lambda_0 + Delta lambda).

    Returns:
    --------
    jnp.ndarray, scalar
        Magnitude of the off-diagonal self-absorption diagnostic coefficient.
    """
    # The diagonal is mathematically guaranteed to be exactly zero.
    # We evaluate the off-diagonal cross-peak wing coupling:
    sa_indicator = jnp.abs(async_matrix[idx_center, idx_wing])
    return sa_indicator
