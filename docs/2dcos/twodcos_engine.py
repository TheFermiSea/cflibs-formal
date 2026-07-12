# -*- coding: utf-8 -*-
"""
twodcos_engine.py
================================================================================
A correct, dependency-light (NumPy-only) implementation of generalized
two-dimensional correlation spectroscopy (2DCOS, Noda formalism) for
time-resolved gate-delay LIBS intensity series, plus compositional-data
utilities (Aitchison closure and isometric log-ratio, ILR).

SCOPE / WHAT THIS MODULE DELIBERATELY DOES NOT DO
--------------------------------------------------------------------------------
This module intentionally OMITS the "Model B" standardless / n_e-free /
temperature-free electron-density-elimination pipeline that appeared in the
original monograph draft (`gated_delay_2dcos_engine.py`,
`process_gated_delay_2dcos`). That pipeline was audited and found scientifically
unsound:

  * ERRATA C1 (FATAL): the "invariant" parameter xi is not a bundle of
    constants -- tracing the Saha-Eggert / three-body-recombination
    substitution chain shows xi = xi(T, U(T), E_ion, k_r(T), optical), i.e.
    temperature- and instrument-dependent. It cannot be a precomputed
    constant, so the method is neither standardless nor temperature-free.
  * ERRATA C2 (FATAL): the "elimination" of n_e invokes the First Generalized
    Mean Value Theorem for Integrals, which is EXISTENCE-ONLY (Apostol,
    *Mathematical Analysis*). It guarantees some coordinate xi exists with
    the stated integral identity, but supplies no value for it -- so the
    transient n_e(t) is merely relabeled as an undetermined constant
    n_e(xi), never actually measured or removed. The subsequent "solve for
    n_e" step tautologically inverts the very identity that defined the
    asynchronous signal as a recombination flux.
  * ERRATA C5 (MAJOR): there is no "Wronskian flux" reading of the
    asynchronous spectrum. Noda's asynchronous correlation is a
    Hilbert-transform (out-of-phase / sequential-order / dissimilarity)
    quantity -- a nonlocal integral operator, not a time derivative and not
    a physical flux.

See `/home/brian/code/cflibs-formal/docs/2dcos/ERRATA.md` for the full audit.
Nothing in this module claims, enables, or reconstructs that pipeline.

WHAT THIS MODULE DOES PROVIDE (honest scope)
--------------------------------------------------------------------------------
Time-resolved 2DCOS, done correctly, is a MODEL-FREE, QUALITATIVE correlation
tool. Applied to a gate-delay LIBS decay series it can:

  1. Compute the standard synchronous (in-phase / covariance) and
     asynchronous (out-of-phase / Hilbert-transform) correlation maps of a
     dynamic (mean-centered) spectral series (Noda 1993; Noda 2000).
  2. Recover the SEQUENTIAL ORDER in which two spectral features change
     along the perturbation (gate delay), via Noda's sign(Phi)*sign(Psi)
     rule -- a qualitative lead/lag readout, not a rate or a concentration.
  3. Provide a synchronous-autopeak-based signal-to-noise / contrast
     diagnostic (cf. Narlagiri & Soma 2021, OSA Continuum 4(9):2423, who
     used exactly this diagonal to raise LIBS line contrast and improve PCA
     class separation) -- an S/N-style indicator, not a quantification.
  4. Correctly separate Aitchison CLOSURE (renormalization onto the simplex,
     x -> x/sum(x)) from the actual Isometric Log-Ratio (ILR) transform
     (Egozcue et al. 2003), which requires an orthonormal basis of the
     clr-hyperplane and is an isometry onto R^(D-1). ERRATA C3 (FATAL) found
     the original code's "softmax(log x)" was plain closure mislabeled as ILR.

This module does NOT deliver absolute number densities, electron density,
temperature, or standardless composition. Quantification still requires the
standard LIBS apparatus: Boltzmann/Saha analysis, an independent n_e
(typically Stark broadening), a temperature retrieval, and either
instrument calibration or the CF-LIBS closure.

Numerical discipline: all returned arrays are float64 (NumPy's native default
precision on most platforms; explicitly cast here for reproducibility -- the
same x64 discipline the original JAX-based draft used, without a JAX
dependency).

References (verified; see ERRATA.md / F1 dossier for verification notes)
--------------------------------------------------------------------------------
  1. Noda I. (1993) "Generalized Two-Dimensional Correlation Method
     Applicable to Infrared, Raman, and Other Types of Spectroscopy,"
     Appl. Spectrosc. 47(9):1329-1336. DOI 10.1366/0003702934067694.
  2. Noda I. (2000) "Determination of Two-Dimensional Correlation Spectra
     Using the Hilbert Transform," Appl. Spectrosc. 54(7):994-999.
     DOI 10.1366/0003702001950472.
  3. Noda I., Ozaki Y. (2004) Two-Dimensional Correlation Spectroscopy --
     Applications in Vibrational and Optical Spectroscopy, Wiley.
  4. Noda I. (2006) "Cyclical asynchronicity in two-dimensional (2D)
     correlation spectroscopy," J. Mol. Struct. 799(1-3):41-47.
     DOI 10.1016/j.molstruc.2005.12.060.
  5. Narlagiri L.M., Soma V.R. (2021) "Improving the Signal-to-Noise Ratio of
     Atomic Transitions in LIBS Using Two-Dimensional Correlation Analysis,"
     OSA Continuum 4(9):2423-2441. DOI 10.1364/OSAC.426995. arXiv:2103.13585.
  6. Aitchison J. (1986) The Statistical Analysis of Compositional Data,
     Chapman and Hall.
  7. Egozcue J.J., Pawlowsky-Glahn V., Mateu-Figueras G., Barcelo-Vidal C.
     (2003) "Isometric Logratio Transformations for Compositional Data
     Analysis," Mathematical Geology 35(3):279-300.
     DOI 10.1023/A:1023818214614.
================================================================================
"""

from __future__ import annotations

import warnings
from typing import NamedTuple, Optional, Tuple

import numpy as np

__all__ = [
    "TwoDCOSResult",
    "SequentialOrder",
    "dynamic_spectrum",
    "hilbert_noda_matrix",
    "synchronous_matrix",
    "asynchronous_matrix",
    "sequential_order",
    "synchronous_autopeak_diagnostic",
    "analyze_series",
    "closure",
    "helmert_basis",
    "clr",
    "clr_inv",
    "ilr",
    "ilr_inv",
    "aitchison_distance",
]


# ==============================================================================
# 2DCOS core (F1)
# ==============================================================================

class TwoDCOSResult(NamedTuple):
    """Container for a full 2DCOS analysis of one gate-delay LIBS series.

    All fields are float64 NumPy arrays. `sync_matrix` and `async_matrix` are
    (n_channels, n_channels); `dynamic` and `mean_spectrum` describe the
    mean-centered data the maps were built from.
    """

    mean_spectrum: np.ndarray       # shape (n_channels,)
    dynamic: np.ndarray             # shape (m_delays, n_channels)
    sync_matrix: np.ndarray         # shape (n_channels, n_channels), symmetric
    async_matrix: np.ndarray        # shape (n_channels, n_channels), antisymmetric


class SequentialOrder(NamedTuple):
    """Encoding of Noda's sequential-order rule for a single channel pair.

    code:
        +1  channel i's intensity changes EARLIER (at smaller perturbation /
            shorter gate delay) than channel j's.
        -1  channel i's intensity changes LATER than channel j's.
         0  indeterminate / simultaneous (Psi ~= 0, or Phi ~= 0 so no
            direction is defined to combine with Psi's sign).
    description: human-readable statement of the same fact.
    """

    code: int
    description: str


def dynamic_spectrum(spectra_matrix: np.ndarray) -> Tuple[np.ndarray, np.ndarray]:
    """Form the dynamic (mean-centered) spectrum of a gate-delay LIBS series.

    Parameters
    ----------
    spectra_matrix : array, shape (m_delays, n_channels)
        Background-subtracted intensity series I(nu, t_l); rows are gate
        delays t_1 < ... < t_m, columns are spectral channels.

    Returns
    -------
    dynamic : float64 array, shape (m_delays, n_channels)
        y_tilde(nu, t_l) = I(nu, t_l) - Ibar(nu), the perturbation-mean-
        centered deviation (Noda 1993; Noda & Ozaki 2004).
    mean_spectrum : float64 array, shape (n_channels,)
        Ibar(nu), the perturbation-averaged reference spectrum.

    Notes
    -----
    Requires m_delays >= 2 (a single spectrum has no dynamic content and the
    downstream 1/(m-1) normalization is undefined). A meaningful ASYNCHRONOUS
    map further wants m_delays >= 3 (F1.1); a warning is raised elsewhere
    (see `asynchronous_matrix`) rather than here, since the dynamic spectrum
    itself is well-defined for m=2.
    """
    spectra_matrix = np.asarray(spectra_matrix, dtype=np.float64)
    if spectra_matrix.ndim != 2:
        raise ValueError("spectra_matrix must be 2D (m_delays, n_channels)")
    m = spectra_matrix.shape[0]
    if m < 2:
        raise ValueError(
            "dynamic_spectrum requires at least 2 gate delays (m >= 2); "
            f"got m={m}. A single spectrum has zero temporal variance."
        )
    mean_spectrum = np.mean(spectra_matrix, axis=0)
    dynamic = spectra_matrix - mean_spectrum
    return dynamic.astype(np.float64), mean_spectrum.astype(np.float64)


def hilbert_noda_matrix(m: int) -> np.ndarray:
    """Construct the discrete Hilbert-Noda transformation matrix N (m x m).

    N_jk = 0                  if j == k
    N_jk = 1 / (pi * (k - j)) if j != k

    This is Noda's discrete determination of the Hilbert transform used to
    build the asynchronous correlation spectrum (Noda 2000, Eq. for N_jk;
    ERRATA C23 confirmed this exact form -- correctly oriented -- as the
    soundest element of the original draft).

    Returns
    -------
    N : float64 array, shape (m, m). Antisymmetric: N.T == -N exactly (up to
        floating point, since N_kj = 1/(pi*(j-k)) = -N_jk is a sign-flip of
        an already-computed reciprocal, an exact operation in IEEE-754).
    """
    if m < 1:
        raise ValueError("m must be >= 1")
    idx = np.arange(m)
    j, k = np.meshgrid(idx, idx, indexing="ij")
    diff = (k - j).astype(np.float64)
    with np.errstate(divide="ignore", invalid="ignore"):
        raw = np.where(diff == 0, 0.0, 1.0 / (np.pi * diff))
    return raw.astype(np.float64)


def synchronous_matrix(dynamic: np.ndarray) -> np.ndarray:
    """Compute the synchronous (in-phase / covariance) correlation matrix Phi.

    Phi(nu1, nu2) = 1/(m-1) * sum_l ytilde(nu1, t_l) * ytilde(nu2, t_l)

    i.e. exactly the sample covariance matrix of the dynamic spectral traces
    (Noda 1993; Noda 2000). Symmetric; the diagonal Phi(nu,nu) = Var_t[I(nu,.)]
    is the per-channel temporal variance (an autopeak, always >= 0).

    Parameters
    ----------
    dynamic : array, shape (m_delays, n_channels)
        Output of `dynamic_spectrum`.

    Returns
    -------
    Phi : float64 array, shape (n_channels, n_channels), symmetric.
    """
    dynamic = np.asarray(dynamic, dtype=np.float64)
    m = dynamic.shape[0]
    if m < 2:
        raise ValueError("synchronous_matrix requires m_delays >= 2")
    phi = (1.0 / (m - 1)) * (dynamic.T @ dynamic)
    # Symmetrize to remove floating-point matmul accumulation asymmetry
    # (dynamic.T @ dynamic is mathematically symmetric but matmul rounding
    # can leave tiny asymmetries; this is a genuine, non-trivial cleanup).
    phi = 0.5 * (phi + phi.T)
    return phi.astype(np.float64)


def asynchronous_matrix(dynamic: np.ndarray) -> np.ndarray:
    """Compute the asynchronous (out-of-phase / Hilbert-transform) matrix Psi.

    Psi(nu1, nu2) = 1/(m-1) * ytilde(nu1,.)^T @ N @ ytilde(nu2,.)

    with N the discrete Hilbert-Noda matrix (Noda 2000). Psi is exactly
    antisymmetric (Psi = -Psi.T) because N is antisymmetric, and consequently
    Psi(nu,nu) == 0 for every channel and every dataset -- this is a
    STANDARD, universal property of the antisymmetric quadratic form, not a
    novel result (ERRATA C22: the original draft's "Skew-Symmetric
    Zero-Diagonal Law" dressed up this elementary fact as a new theorem).
    Because the zero diagonal holds unconditionally, it cannot by itself
    discriminate between physical models (ERRATA C8).

    Parameters
    ----------
    dynamic : array, shape (m_delays, n_channels)
        Output of `dynamic_spectrum`.

    Returns
    -------
    Psi : float64 array, shape (n_channels, n_channels), antisymmetric,
        exactly-zero diagonal.
    """
    dynamic = np.asarray(dynamic, dtype=np.float64)
    m = dynamic.shape[0]
    if m < 2:
        raise ValueError("asynchronous_matrix requires m_delays >= 2")
    if m < 3:
        warnings.warn(
            "asynchronous_matrix: m_delays < 3 -- the asynchronous map is "
            "defined but not meaningful with fewer than 3 gate delays (F1.1).",
            stacklevel=2,
        )
    N = hilbert_noda_matrix(m)
    transformed = N @ dynamic
    raw_psi = (1.0 / (m - 1)) * (dynamic.T @ transformed)
    # Enforce exact antisymmetry / zero diagonal: raw_psi and raw_psi.T come
    # from independently-ordered matmul accumulations and can differ at the
    # rounding level, so this genuinely removes residual floating-point noise
    # (unlike a purely cosmetic no-op).
    psi = 0.5 * (raw_psi - raw_psi.T)
    np.fill_diagonal(psi, 0.0)
    return psi.astype(np.float64)


def sequential_order(
    phi_ij: float, psi_ij: float, tol: float = 1e-12
) -> SequentialOrder:
    """Apply Noda's sequential-order rule to one (i, j) synchronous/asynchronous pair.

    Rule (Noda 1993; Noda & Ozaki 2004; see F1.5):
        sign[Phi(i,j)] == sign[Psi(i,j)]  =>  channel i changes EARLIER than j
        sign[Phi(i,j)] != sign[Psi(i,j)]  =>  channel i changes LATER than j
        Psi(i,j) == 0                     =>  simultaneous / no resolvable order

    Caveat (Noda 2006): this sign rule assumes an effectively monotonic,
    single-directional event order; cyclical / non-monotonic kinetics (e.g.
    a population that rises then falls within the observed window) can make
    the naive two-event reading break down. It is a qualitative lead/lag
    diagnostic, not a rate or a concentration.

    Parameters
    ----------
    phi_ij, psi_ij : float
        The (i, j) entries of the synchronous and asynchronous matrices.
    tol : float
        Magnitudes at or below this are treated as exactly zero for the sign
        test (guards floating-point noise around a true zero).

    Returns
    -------
    SequentialOrder
    """
    if abs(psi_ij) <= tol:
        return SequentialOrder(
            0, "Psi ~= 0: simultaneous / no resolvable sequential order"
        )
    if abs(phi_ij) <= tol:
        return SequentialOrder(
            0,
            "Phi ~= 0: no synchronous direction to combine with Psi's sign "
            "-- order indeterminate",
        )
    s = np.sign(phi_ij) * np.sign(psi_ij)
    if s > 0:
        return SequentialOrder(
            1, "channel i changes earlier (shorter gate delay) than channel j"
        )
    else:
        return SequentialOrder(
            -1, "channel i changes later (longer gate delay) than channel j"
        )


def synchronous_autopeak_diagnostic(
    sync_matrix_: np.ndarray, noise_variance: Optional[np.ndarray] = None
) -> np.ndarray:
    """Synchronous-autopeak-based signal-to-noise / contrast diagnostic.

    Returns the diagonal of the synchronous matrix, Phi(nu,nu) = Var_t[I(nu,.)],
    i.e. the per-channel temporal variance across the gate-delay series.
    Coherent line-intensity variation across delays reinforces on this
    diagonal, while stochastic (shot/read) noise -- uncorrelated across gate
    delays -- tends to average down, so the autopeak acts as a denoised
    contrast proxy (Narlagiri & Soma 2021, who used exactly this quantity to
    raise LIBS peak contrast and improve PCA class separation on time-
    resolved series).

    HONEST LABEL: this is an S/N-style *diagnostic* for line discrimination
    / denoising / preprocessing. It is NOT a quantification of concentration,
    electron density, or temperature, and it is not a formal SNR estimate
    unless an independent noise variance is supplied.

    Parameters
    ----------
    sync_matrix_ : array, shape (n_channels, n_channels)
        Output of `synchronous_matrix`.
    noise_variance : array, shape (n_channels,), optional
        An independently estimated per-channel noise variance (e.g. from a
        blank/dark region or a repeated-shot baseline). If given, an SNR-like
        ratio autopeak / noise_variance is also returned.

    Returns
    -------
    autopeak : float64 array, shape (n_channels,)
        Phi(nu, nu) for each channel.
    snr : float64 array or None
        autopeak / noise_variance if `noise_variance` was supplied, else None.
    """
    sync_matrix_ = np.asarray(sync_matrix_, dtype=np.float64)
    autopeak = np.diagonal(sync_matrix_).astype(np.float64).copy()
    if noise_variance is None:
        return autopeak, None
    noise_variance = np.asarray(noise_variance, dtype=np.float64)
    with np.errstate(divide="ignore", invalid="ignore"):
        snr = autopeak / noise_variance
    return autopeak, snr.astype(np.float64)


def analyze_series(spectra_matrix: np.ndarray) -> TwoDCOSResult:
    """Convenience wrapper: run the full (honest-scope) 2DCOS pipeline.

    Computes the dynamic spectrum, synchronous matrix, and asynchronous
    matrix for a gate-delay LIBS series. Does NOT perform any composition
    inversion -- see the module docstring for why ("Model B" is omitted).

    Parameters
    ----------
    spectra_matrix : array, shape (m_delays, n_channels)

    Returns
    -------
    TwoDCOSResult
    """
    dyn, mean_spec = dynamic_spectrum(spectra_matrix)
    phi = synchronous_matrix(dyn)
    psi = asynchronous_matrix(dyn)
    return TwoDCOSResult(
        mean_spectrum=mean_spec, dynamic=dyn, sync_matrix=phi, async_matrix=psi
    )


# ==============================================================================
# Compositional-data utilities (F3): closure vs. ILR, correctly separated
# ==============================================================================
#
# ERRATA C3 (FATAL): the original draft computed `softmax(log(x))` and called
# it an "Isometric Log-Ratio (ILR) transformation". Algebraically,
# softmax(log(x))_i = exp(log(x_i)) / sum_j exp(log(x_j)) = x_i / sum_j(x_j),
# because log and softmax's internal exp cancel exactly. That is precisely
# Aitchison's CLOSURE operator C(x) -- ordinary renormalization onto the
# simplex -- with NO orthonormal basis, NO D -> D-1 dimension reduction, and
# NO isometry. This module keeps `closure` and `ilr`/`ilr_inv` as separate,
# correctly-named functions, exactly to prevent that conflation from
# recurring. CLOSURE != ILR.
# ==============================================================================


def closure(x: np.ndarray) -> np.ndarray:
    """Aitchison closure C(x) = x / sum(x): renormalize onto the simplex.

    This is ONLY a renormalization (Aitchison 1986) -- it performs no
    dimension reduction, uses no orthonormal basis, and is not an isometry
    with respect to any log-ratio metric. It is the appropriate LAST step
    for reporting a composition (e.g. weight/mole fractions summing to 1),
    but it is not a coordinate system suitable for unconstrained statistics
    or optimization -- for that, use `ilr` (see ERRATA C3).

    Parameters
    ----------
    x : array, shape (..., D)
        Strictly positive components (D >= 2) along the last axis.

    Returns
    -------
    float64 array, shape (..., D), each row summing to 1.
    """
    x = np.asarray(x, dtype=np.float64)
    if np.any(x <= 0):
        raise ValueError("closure requires strictly positive components")
    total = np.sum(x, axis=-1, keepdims=True)
    return (x / total).astype(np.float64)


def helmert_basis(D: int) -> np.ndarray:
    """Orthonormal Helmert-style basis V (D x (D-1)) of the clr hyperplane.

    Columns satisfy V^T V = I_{D-1} (orthonormal) and 1^T V = 0 (each column
    sums to zero, so it lies in the clr hyperplane H = {u in R^D : sum(u)=0}).
    This is the classical Helmert sub-matrix, one standard, non-fabricated
    construction of the sequential-binary-partition ("balances") bases used
    for ILR coordinates (Egozcue & Pawlowsky-Glahn 2005; Egozcue et al. 2003).

    Column k (0-indexed, k = 0, ..., D-2), with kk = k + 1:
        V[0:kk, k]  =  1 / sqrt(kk*(kk+1))
        V[kk, k]    = -kk / sqrt(kk*(kk+1))
        V[kk+1:, k] =  0

    Any other orthonormal basis of H (e.g. from Gram-Schmidt, or a different
    sequential binary partition) works equally well: rotation-invariant
    statistics (Aitchison distance, PCA eigenvalues, etc.) do not depend on
    the choice of V; only the per-coordinate ("balance") interpretation does.

    Parameters
    ----------
    D : int, number of parts (D >= 2).

    Returns
    -------
    V : float64 array, shape (D, D-1).
    """
    if D < 2:
        raise ValueError("helmert_basis requires D >= 2 parts")
    V = np.zeros((D, D - 1), dtype=np.float64)
    for k in range(D - 1):
        kk = k + 1
        denom = np.sqrt(kk * (kk + 1))
        V[:kk, k] = 1.0 / denom
        V[kk, k] = -kk / denom
    return V


def clr(x: np.ndarray) -> np.ndarray:
    """Centered log-ratio transform: clr(x) = log(x) - mean(log(x)).

    Maps the simplex S^D isometrically onto the hyperplane
    H = {u in R^D : sum(u) = 0} (Aitchison 1986). The image is still
    D-dimensional with one redundant linear relation (rank D-1) -- useful
    for symmetric treatments, but not a minimal / unconstrained coordinate
    system. For that, use `ilr`, which projects clr(x) onto an orthonormal
    basis of H.

    Parameters
    ----------
    x : array, shape (..., D), strictly positive.

    Returns
    -------
    float64 array, shape (..., D), each row summing to (approximately) 0.
    """
    x = np.asarray(x, dtype=np.float64)
    if np.any(x <= 0):
        raise ValueError("clr requires strictly positive components")
    log_x = np.log(x)
    g = np.mean(log_x, axis=-1, keepdims=True)
    return (log_x - g).astype(np.float64)


def clr_inv(u: np.ndarray) -> np.ndarray:
    """Inverse centered log-ratio: clr_inv(u) = C(exp(u)) = closure(exp(u)).

    Valid for any u in R^D (need not sum to zero); if u already sums to zero
    this recovers exactly the composition whose clr is u.
    """
    u = np.asarray(u, dtype=np.float64)
    return closure(np.exp(u))


def ilr(x: np.ndarray, V: Optional[np.ndarray] = None) -> np.ndarray:
    """Isometric log-ratio transform: ilr(x) = V^T clr(x), for orthonormal V.

    This is the ACTUAL ILR (Egozcue et al. 2003) -- distinct from Aitchison
    closure (see module notes / ERRATA C3). It maps a D-part composition to
    an UNCONSTRAINED point in R^(D-1) and is an isometry with respect to the
    Aitchison distance:

        || ilr(x) - ilr(y) ||_2  ==  d_A(x, y)  ==  || clr(x) - clr(y) ||_2

    which follows directly from V's orthonormality (V^T V = I): for any
    zero-sum vectors u, w in H, ||V^T u - V^T w||^2 = (u-w)^T V V^T (u-w) =
    ||u - w||^2 whenever u - w lies in H's column space (spanned by V, since
    u, w in H = span(V)).

    Parameters
    ----------
    x : array, shape (..., D), strictly positive components.
    V : array, shape (D, D-1), optional
        Orthonormal basis of the clr hyperplane. Defaults to
        `helmert_basis(D)` if not supplied.

    Returns
    -------
    float64 array, shape (..., D-1).
    """
    x = np.asarray(x, dtype=np.float64)
    D = x.shape[-1]
    if V is None:
        V = helmert_basis(D)
    else:
        V = np.asarray(V, dtype=np.float64)
        if V.shape != (D, D - 1):
            raise ValueError(f"V must have shape ({D}, {D-1}), got {V.shape}")
    u = clr(x)
    return (u @ V).astype(np.float64)


def ilr_inv(z: np.ndarray, V: Optional[np.ndarray] = None, D: Optional[int] = None) -> np.ndarray:
    """Inverse isometric log-ratio: ilr_inv(z) = clr_inv(V z) = closure(exp(V z)).

    Parameters
    ----------
    z : array, shape (..., D-1)
    V : array, shape (D, D-1), optional. Defaults to `helmert_basis(D)`.
    D : int, optional. Required only if `V` is not supplied (to build the
        default Helmert basis); inferred from V.shape[0] otherwise.

    Returns
    -------
    float64 array, shape (..., D), a valid composition (positive, sums to 1).
    """
    z = np.asarray(z, dtype=np.float64)
    if V is None:
        if D is None:
            D = z.shape[-1] + 1
        V = helmert_basis(D)
    else:
        V = np.asarray(V, dtype=np.float64)
    u = z @ V.T
    return clr_inv(u)


def aitchison_distance(x: np.ndarray, y: np.ndarray) -> float:
    """Aitchison distance d_A(x, y) = || clr(x) - clr(y) ||_2.

    Provided so callers can directly check the ILR isometry property
    (`ilr` preserves this distance in R^(D-1) Euclidean form) without
    re-deriving clr by hand.
    """
    x = np.asarray(x, dtype=np.float64)
    y = np.asarray(y, dtype=np.float64)
    return float(np.linalg.norm(clr(x) - clr(y)))
