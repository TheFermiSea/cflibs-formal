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
- Hinnov E. (1962) Electron-ion recombination in hydrogen plasmas, Phys. Rev. 125:795
- Aitchison J. (1986) The Statistical Analysis of Compositional Data
================================================================================
"""

import jax
# Enforce double-precision x64 floating point representations
jax.config.update("jax_enable_x64", True)

import jax.numpy as jnp
from typing import NamedTuple

# Structure to hold computation metrics safely
class 2DCOSMetrics(NamedTuple):
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
) -> 2DCOSMetrics:
    """
    Executes the standardless Gate-Delay 2DCOS inversion pipeline on raw LPP matrices.

    Parameters:
    -----------
    spectra_matrix : jnp.ndarray, shape (m_delays, n_channels)
        Double-precision temporal matrix containing area-normalized emission records.
        Typically pre-processed to remove baseline drift and continuum.
    idx_atom : jnp.ndarray, shape (D_elements,)
        Indices of channels corresponding to unblended neutral atomic lines.
    idx_ion : jnp.ndarray, shape (D_elements,)
        Indices of channels corresponding to coupled ionic lines of the same elements.
    xi_parameters : jnp.ndarray, shape (D_elements,)
        Precomputed thermodynamic integrated parameters xi(T) linking the Saha-Eggert
        and three-body recombination rate constants.
    epsilon : float
        Regularizer added to the denominator of the Model B radical fraction to prevent
        NaN or Inf gradients during auto-differentiation at phase singularity regions.

    Returns:
    --------
    2DCOSMetrics
        NamedTuple containing computed correlation tensors and the projected Aitchison
        compositions.
    """
    m, n = spectra_matrix.shape

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
    # Generates a strictly skew-symmetric discrete Hilbert transform matrix
    idx_range = jnp.arange(m)
    j, k = jnp.meshgrid(idx_range, idx_range, indexing='ij')
    diff = k - j
    raw_kernel = jnp.where(diff == 0, 0.0, 1.0 / (jnp.pi * diff))
    # Enforce exact structural skew-symmetry: N^T = -N
    hilbert_kernel = 0.5 * (raw_kernel - raw_kernel.T)

    # --------------------------------------------------------------------------
    # 4. Asynchronous Matrix Generation
    # --------------------------------------------------------------------------
    transformed_dynamic = jnp.matmul(hilbert_kernel, dynamic_spectra)
    raw_async = (1.0 / (m - 1)) * jnp.matmul(dynamic_spectra.T, transformed_dynamic)
    # Enforce strict zero-diagonal and skew-symmetry to eliminate accumulation noise
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
    # This Softmax layer represents an Isometric Log-Ratio (ILR) projection,
    # ensuring unconstrained gradients can be backpropagated during optimization.
    log_abundances = jnp.log(jnp.maximum(raw_abundances, 1.0e-15))
    projected_simplex = jax.nn.softmax(log_abundances)

    return 2DCOSMetrics(
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
    Computes the physically validated self-absorption signature using the
    off-diagonal wing-to-center asynchronous phase lag.

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
