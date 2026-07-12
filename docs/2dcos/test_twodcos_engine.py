# -*- coding: utf-8 -*-
"""
test_twodcos_engine.py
================================================================================
Plain-assert test suite for twodcos_engine.py. Run directly with
`python3 test_twodcos_engine.py` (no pytest dependency required, though it is
pytest-collectible too since all functions are named test_*).
================================================================================
"""

import numpy as np

from twodcos_engine import (
    aitchison_distance,
    analyze_series,
    asynchronous_matrix,
    closure,
    clr,
    clr_inv,
    dynamic_spectrum,
    helmert_basis,
    hilbert_noda_matrix,
    ilr,
    ilr_inv,
    sequential_order,
    synchronous_autopeak_diagnostic,
    synchronous_matrix,
)


def test_hilbert_noda_matrix_skew_symmetric():
    for m in (2, 3, 4, 7, 12):
        N = hilbert_noda_matrix(m)
        assert N.dtype == np.float64
        assert np.allclose(N.T, -N), f"Hilbert-Noda matrix not skew-symmetric at m={m}"
        assert np.all(np.diagonal(N) == 0.0), f"Hilbert-Noda diagonal not exactly zero at m={m}"
        # spot-check the defining formula off-diagonal (use indices valid for
        # every tested m, including the smallest case m=2)
        j, k = 0, 1
        expected = 1.0 / (np.pi * (k - j))
        assert np.isclose(N[j, k], expected)
        assert np.isclose(N[k, j], -expected)
    print("test_hilbert_noda_matrix_skew_symmetric: PASS")


def test_asynchronous_matrix_zero_diagonal_and_antisymmetric():
    rng = np.random.default_rng(0)
    m, n = 9, 5
    spectra = rng.normal(size=(m, n)) + 10.0  # arbitrary positive-ish data
    dyn, _ = dynamic_spectrum(spectra)
    psi = asynchronous_matrix(dyn)
    assert psi.dtype == np.float64
    assert np.all(psi.diagonal() == 0.0), "asynchronous matrix diagonal must be exactly zero"
    assert np.allclose(psi, -psi.T, atol=1e-12), "asynchronous matrix must be antisymmetric"

    phi = synchronous_matrix(dyn)
    assert np.allclose(phi, phi.T, atol=1e-12), "synchronous matrix must be symmetric"
    assert np.all(phi.diagonal() >= -1e-12), "synchronous diagonal (variance) must be >= 0"
    print("test_asynchronous_matrix_zero_diagonal_and_antisymmetric: PASS")


def test_closure_sums_to_one():
    x = np.array([1.0, 2.0, 7.0, 0.5])
    c = closure(x)
    assert np.isclose(np.sum(c), 1.0)
    assert c.dtype == np.float64
    # batched
    X = np.array([[1.0, 1.0, 2.0], [3.0, 3.0, 3.0]])
    C = closure(X)
    assert np.allclose(np.sum(C, axis=-1), 1.0)
    print("test_closure_sums_to_one: PASS")


def test_ilr_roundtrip_and_isometry():
    rng = np.random.default_rng(1)
    D = 5
    x = rng.uniform(0.1, 5.0, size=D)
    y = rng.uniform(0.1, 5.0, size=D)

    V = helmert_basis(D)
    # orthonormality of the basis itself
    assert np.allclose(V.T @ V, np.eye(D - 1), atol=1e-10)
    assert np.allclose(np.sum(V, axis=0), 0.0, atol=1e-10)

    z_x = ilr(x, V)
    x_back = ilr_inv(z_x, V)
    assert np.allclose(x_back, closure(x), atol=1e-8), "ilr_inv(ilr(x)) must recover closure(x)"

    # isometry: Euclidean distance in ilr-space equals the Aitchison distance
    z_y = ilr(y, V)
    d_ilr = np.linalg.norm(z_x - z_y)
    d_aitchison = aitchison_distance(x, y)
    assert np.isclose(d_ilr, d_aitchison, rtol=1e-8), (
        f"ilr must preserve Aitchison distance: {d_ilr} vs {d_aitchison}"
    )

    # closure != ilr: different shapes/semantics on the same input
    c = closure(x)
    assert c.shape[-1] == D
    assert z_x.shape[-1] == D - 1
    assert not np.isclose(np.sum(z_x), 1.0)  # ilr coords do not sum to 1
    print("test_ilr_roundtrip_and_isometry: PASS")


def test_clr_hyperplane_and_inverse():
    x = np.array([2.0, 3.0, 5.0])
    u = clr(x)
    assert np.isclose(np.sum(u), 0.0, atol=1e-10)
    x_rec = clr_inv(u)
    assert np.allclose(x_rec, closure(x), atol=1e-10)
    print("test_clr_hyperplane_and_inverse: PASS")


def test_synchronous_autopeak_diagnostic():
    rng = np.random.default_rng(2)
    m, n = 10, 4
    spectra = rng.normal(size=(m, n)) * 0.01 + np.array([1.0, 5.0, 1.0, 1.0])
    # channel 1 has a much bigger dynamic swing injected
    t = np.linspace(0, 1, m)
    spectra[:, 1] += 3.0 * np.exp(-3 * t)
    dyn, _ = dynamic_spectrum(spectra)
    phi = synchronous_matrix(dyn)
    autopeak, snr = synchronous_autopeak_diagnostic(phi)
    assert snr is None
    assert autopeak.shape == (n,)
    assert autopeak[1] > autopeak[0]  # the perturbed channel has larger variance
    autopeak2, snr2 = synchronous_autopeak_diagnostic(phi, noise_variance=np.ones(n) * 0.5)
    assert snr2 is not None
    assert np.allclose(snr2, autopeak2 / 0.5)
    print("test_synchronous_autopeak_diagnostic: PASS")


def test_sequential_order_synthetic_two_line_decay():
    """Synthetic two-line decaying series: channel A decays first (fast),
    channel B decays later (slow, delayed onset) -- e.g. an ionic line (A)
    recombining into a neutral line (B) whose intensity change lags behind.
    Noda's sign(Phi)*sign(Psi) rule should recover that A leads B.
    """
    m = 40
    t = np.linspace(0.0, 1.0, m)
    # Channel A: fast exponential decay starting immediately.
    line_a = 5.0 * np.exp(-8.0 * t)
    # Channel B: a delayed decay -- negligible change until ~t=0.3, then falls.
    # This creates a genuine lag/lead structure across the gate-delay series.
    line_b = 5.0 * np.exp(-8.0 * np.clip(t - 0.3, 0.0, None))

    spectra = np.stack([line_a, line_b], axis=1)  # shape (m, 2)
    dyn, _ = dynamic_spectrum(spectra)
    phi = synchronous_matrix(dyn)
    psi = asynchronous_matrix(dyn)

    order = sequential_order(phi[0, 1], psi[0, 1])
    assert order.code in (1, -1), "expected a resolvable sequential order for this synthetic series"
    # Channel A (index 0) starts changing before channel B (index 1): code should be +1.
    assert order.code == 1, f"expected channel A to lead channel B, got code={order.code} ({order.description})"

    # Sanity: the reverse pair gives the exactly negated Psi sign (antisymmetry)
    # and hence the flipped verdict.
    order_rev = sequential_order(phi[1, 0], psi[1, 0])
    assert order_rev.code == -1
    print("test_sequential_order_synthetic_two_line_decay: PASS")


def test_analyze_series_end_to_end():
    rng = np.random.default_rng(3)
    m, n = 15, 6
    spectra = rng.uniform(1.0, 10.0, size=(m, n))
    result = analyze_series(spectra)
    assert result.sync_matrix.shape == (n, n)
    assert result.async_matrix.shape == (n, n)
    assert result.dynamic.shape == (m, n)
    assert result.mean_spectrum.shape == (n,)
    assert np.allclose(result.sync_matrix, result.sync_matrix.T)
    assert np.all(result.async_matrix.diagonal() == 0.0)
    print("test_analyze_series_end_to_end: PASS")


def test_m_equals_one_rejected():
    try:
        dynamic_spectrum(np.array([[1.0, 2.0, 3.0]]))
        raised = False
    except ValueError:
        raised = True
    assert raised, "dynamic_spectrum must reject m=1 (singular 1/(m-1) normalization)"
    print("test_m_equals_one_rejected: PASS")


def _run_all():
    test_hilbert_noda_matrix_skew_symmetric()
    test_asynchronous_matrix_zero_diagonal_and_antisymmetric()
    test_closure_sums_to_one()
    test_ilr_roundtrip_and_isometry()
    test_clr_hyperplane_and_inverse()
    test_synchronous_autopeak_diagnostic()
    test_sequential_order_synthetic_two_line_decay()
    test_analyze_series_end_to_end()
    test_m_equals_one_rejected()
    print("\nALL TESTS PASSED")


if __name__ == "__main__":
    _run_all()
