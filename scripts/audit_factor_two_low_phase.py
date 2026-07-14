#!/usr/bin/env python3
"""Numerically audit the concrete factor-two finite-low phase pencil.

This is a deterministic discovery tool, not a proof.  It reconstructs the
matrices defined in the following Lean modules directly from their analytic
definitions:

* ``YoshidaFactorTwoPhaseConcreteCleanEvenMatrix``;
* ``YoshidaFactorTwoPhaseConcreteCleanOddMatrix``;
* ``YoshidaFactorTwoPhaseConcreteLowMatrix``; and
* ``YoshidaFactorTwoPhaseConcreteLowDiskSchur``;
* ``YoshidaFactorTwoPhaseConcreteLowToeplitz``; and
* ``YoshidaFactorTwoPhaseConcreteLowSplitToeplitz``.

The one-sided correlations are integrated exactly in the spatial variable by
using their finite Fourier expansions.  Gauss--Legendre quadrature is used
only for the remaining one-dimensional integrals.  The singular endpoint is
regularized before quadrature: for a weight ``W`` the script computes

    integral W(t) (exp(i*pi*n*t) - 1) dt

and

    integral W(t) (2 - t) exp(i*pi*n*t) dt,

both of which are continuous at ``t = 2``.  The clean Gram is reconstructed
from the Section-6 sine and diagonal moments, including the extra frequency
200 used by the endpoint-adapted even basis.

Typical invocation (the repository intentionally has no Python environment):

    OPENBLAS_NUM_THREADS=1 \
      uv run --with numpy --with scipy \
      python scripts/audit_factor_two_low_phase.py

No floating-point result emitted here is consumed by Lean.
"""

from __future__ import annotations

import argparse
import math
from dataclasses import dataclass

import numpy as np
from scipy.linalg import eigvalsh, solve_triangular
from scipy.optimize import minimize_scalar
from scipy.special import roots_legendre


EVEN_DIM = 200
ODD_DIM = 10
MAX_FREQUENCY = 200
EULER_GAMMA = 0.57721566490153286060651209


@dataclass(frozen=True)
class Blocks:
    clean_even: np.ndarray
    perturb_even: np.ndarray
    clean_odd: np.ndarray
    perturb_odd: np.ndarray
    alternating: np.ndarray


def adjacent_smooth_kernel(s: np.ndarray) -> np.ndarray:
    """Stable positive-argument evaluation of the adjacent smooth kernel."""

    odd_half = np.exp(-s / 2) / (-np.expm1(-2 * s))
    return 2 * np.cosh(s / 2) - odd_half


def ordered_kernel_from_regularized_fourier(
    regularized: np.ndarray,
    endpoint_scaled: np.ndarray,
    frequencies: np.ndarray,
) -> np.ndarray:
    """Return ``integral W(t) Cross(exp_k, exp_l, t) dt``."""

    k = frequencies[:, None]
    ell = frequencies[None, :]
    total = k + ell
    result = np.empty(total.shape, dtype=np.complex128)

    rows, columns = np.nonzero(total == 0)
    result[rows, columns] = endpoint_scaled[rows]

    rows, columns = np.nonzero(total != 0)
    q = total[rows, columns]
    parity = np.where(q % 2 == 0, 1.0, -1.0)
    # Array index ``r`` represents frequency ``r - MAX_FREQUENCY``.
    # Thus frequency ``-ell`` has index ``2 * MAX_FREQUENCY - columns``.
    result[rows, columns] = (
        parity
        * (regularized[2 * MAX_FREQUENCY - columns] - regularized[rows])
        / (1j * math.pi * q)
    )
    return result


def point_ordered_kernel(t: float, frequencies: np.ndarray) -> np.ndarray:
    """Return the ordered Fourier cross-correlation kernel at one ``t``."""

    k = frequencies[:, None]
    ell = frequencies[None, :]
    total = k + ell
    delta = 2 - t
    result = np.empty(total.shape, dtype=np.complex128)

    rows, columns = np.nonzero(total == 0)
    result[rows, columns] = delta * np.exp(1j * math.pi * frequencies[rows] * t)

    rows, columns = np.nonzero(total != 0)
    q = total[rows, columns]
    parity = np.where(q % 2 == 0, 1.0, -1.0)
    result[rows, columns] = (
        np.exp(1j * math.pi * frequencies[rows] * t)
        * parity
        * np.expm1(1j * math.pi * q * delta)
        / (1j * math.pi * q)
    )
    return result


def centered_basis_coefficients(
    endpoint_scale: float, frequencies: np.ndarray
) -> tuple[np.ndarray, np.ndarray]:
    """Return adapted-even and canonical-odd finite Fourier coefficients."""

    even = np.zeros((EVEN_DIM, frequencies.size), dtype=np.complex128)
    odd = np.zeros((ODD_DIM, frequencies.size), dtype=np.complex128)
    center = MAX_FREQUENCY
    sqrt_scale = math.sqrt(endpoint_scale)

    even[0, center] = 1 / math.sqrt(2 * endpoint_scale)
    even[0, [0, 2 * center]] = -1 / (2 * math.sqrt(2 * endpoint_scale))
    for n in range(1, EVEN_DIM):
        even[n, [center - n, center + n]] = 1 / (2 * sqrt_scale)
        even[n, [0, 2 * center]] = -((-1.0) ** n) / (2 * sqrt_scale)

    for row, n in enumerate(range(1, ODD_DIM + 1)):
        odd[row, center + n] = -1j / (2 * sqrt_scale)
        odd[row, center - n] = 1j / (2 * sqrt_scale)
    return even, odd


def phase_blocks(
    nodes: np.ndarray,
    weights: np.ndarray,
    endpoint_scale: float,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Compute the two symmetric perturbation blocks and alternating block."""

    frequencies = np.arange(-MAX_FREQUENCY, MAX_FREQUENCY + 1)
    t = nodes + 1  # Transform [-1, 1] to [0, 2]; the scale factor is one.
    delta = 2 - t

    left = adjacent_smooth_kernel(endpoint_scale * (2 + t))
    right = adjacent_smooth_kernel(endpoint_scale * (2 - t))
    symmetric_weight = left + right
    antisymmetric_weight = left - right

    phase = np.exp(1j * math.pi * frequencies[:, None] * (t[None, :] - 2))

    def regularized(weight: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
        r = ((phase - 1) * (weights * weight)[None, :]).sum(axis=1)
        g = (phase * (weights * weight * delta)[None, :]).sum(axis=1)
        return r, g

    symmetric_r, symmetric_g = regularized(symmetric_weight)
    alternating_r, alternating_g = regularized(antisymmetric_weight)
    symmetric_integral = ordered_kernel_from_regularized_fourier(
        symmetric_r, symmetric_g, frequencies
    )
    alternating_integral = ordered_kernel_from_regularized_fourier(
        alternating_r, alternating_g, frequencies
    )

    prime_two = point_ordered_kernel(0.0, frequencies)
    prime_three_shift = math.log(1.5) / endpoint_scale
    prime_three = point_ordered_kernel(prime_three_shift, frequencies)

    def sym(matrix: np.ndarray) -> np.ndarray:
        return (matrix + matrix.T) / 2

    def alt(matrix: np.ndarray) -> np.ndarray:
        return matrix.T - matrix

    symmetric_form = (
        endpoint_scale * sym(symmetric_integral)
        - math.log(2) / math.sqrt(2) * sym(prime_two)
        - math.log(3) / math.sqrt(3) * sym(prime_three)
    )
    alternating_form = endpoint_scale * alt(alternating_integral) - math.log(
        3
    ) / math.sqrt(3) * alt(prime_three)

    even_basis, odd_basis = centered_basis_coefficients(endpoint_scale, frequencies)
    even = even_basis @ symmetric_form @ even_basis.T
    odd = odd_basis @ symmetric_form @ odd_basis.T
    alternating = even_basis @ alternating_form @ odd_basis.T

    imaginary_error = max(
        np.max(np.abs(even.imag)),
        np.max(np.abs(odd.imag)),
        np.max(np.abs(alternating.imag)),
    )
    if imaginary_error > 1e-9:
        raise RuntimeError(f"unexpected imaginary matrix residue {imaginary_error}")
    return even.real, odd.real, alternating.real


def section_six_moments(
    nodes: np.ndarray, weights: np.ndarray
) -> tuple[np.ndarray, np.ndarray]:
    """Evaluate ``S_0..S_200`` and ``D_0..D_200`` by quadrature."""

    length = math.log(2)
    u = (nodes + 1) * length / 2
    scaled_weights = weights * length / 2
    odd_half = np.exp(-u / 2) / (-np.expm1(-2 * u))
    weight_plus = 2 * (np.exp(u / 2) + np.exp(-u / 2) - odd_half) + 1 / u

    frequencies = np.arange(MAX_FREQUENCY + 1)
    argument = 2 * math.pi * frequencies[:, None] * u[None, :] / length
    sine = np.sin(argument)
    cosine = np.cos(argument)
    sine_moments = (
        scaled_weights[None, :] * (weight_plus[None, :] * sine - sine / u[None, :])
    ).sum(axis=1)
    diagonal_moments = (
        scaled_weights[None, :]
        * (
            weight_plus[None, :] * ((length - u) / length)[None, :] * cosine
            + 2 * np.sin(argument / 2) ** 2 / u[None, :]
            + cosine / length
        )
    ).sum(axis=1)
    diagonal_moments -= math.log(length) + EULER_GAMMA + math.log(2) + math.log(math.pi)
    return sine_moments, diagonal_moments


def clean_blocks(
    nodes: np.ndarray,
    weights: np.ndarray,
    endpoint_scale: float,
) -> tuple[np.ndarray, np.ndarray]:
    """Reconstruct the adapted-even and canonical-odd clean Gram blocks."""

    sine, diagonal = section_six_moments(nodes, weights)
    canonical_even = np.empty((MAX_FREQUENCY + 1, MAX_FREQUENCY + 1))
    for n in range(MAX_FREQUENCY + 1):
        for m in range(MAX_FREQUENCY + 1):
            if n == 0:
                value = (
                    diagonal[0]
                    if m == 0
                    else (-1.0) ** (m + 1) * sine[m] / (m * math.pi * math.sqrt(2))
                )
            elif m == 0:
                value = (-1.0) ** (n + 1) * sine[n] / (n * math.pi * math.sqrt(2))
            elif n == m:
                value = diagonal[n] - sine[n] / (2 * n * math.pi)
            else:
                value = (
                    (-1.0) ** (n + m)
                    * (m * sine[m] - n * sine[n])
                    / ((n * n - m * m) * math.pi)
                )
            canonical_even[n, m] = value

    odd = np.empty((ODD_DIM, ODD_DIM))
    for row, n in enumerate(range(1, ODD_DIM + 1)):
        for column, m in enumerate(range(1, ODD_DIM + 1)):
            odd[row, column] = (
                diagonal[n] + sine[n] / (2 * n * math.pi)
                if n == m
                else (-1.0) ** (n + m)
                * (n * sine[m] - m * sine[n])
                / ((n * n - m * m) * math.pi)
            )

    transform = np.zeros((EVEN_DIM, MAX_FREQUENCY + 1))
    transform[:, :EVEN_DIM] = np.eye(EVEN_DIM)
    trace = np.ones(EVEN_DIM)
    trace[0] = 1 / math.sqrt(2)
    trace[1:] = (-1.0) ** np.arange(1, EVEN_DIM)
    transform[:, MAX_FREQUENCY] = -trace
    return (
        transform @ canonical_even @ transform.T / endpoint_scale,
        odd / endpoint_scale,
    )


def construct_blocks(order: int) -> Blocks:
    nodes, weights = roots_legendre(order)
    endpoint_scale = math.log(2) / 2
    perturb_even, perturb_odd, alternating = phase_blocks(
        nodes, weights, endpoint_scale
    )
    clean_even, clean_odd = clean_blocks(nodes, weights, endpoint_scale)
    return Blocks(
        clean_even,
        perturb_even,
        clean_odd,
        perturb_odd,
        alternating,
    )


def phase_matrix(blocks: Blocks, a: float, b: float) -> np.ndarray:
    even = blocks.clean_even + a * blocks.perturb_even
    odd = blocks.clean_odd + a * blocks.perturb_odd
    return np.block(
        [
            [even, b * blocks.alternating / 2],
            [b * blocks.alternating.T / 2, odd],
        ]
    )


def schur_ratio(blocks: Blocks, a: float) -> float:
    """Return the sharp normalized scalar-Schur ratio at one ``a``."""

    even = blocks.clean_even + a * blocks.perturb_even
    odd = blocks.clean_odd + a * blocks.perturb_odd
    even_cholesky = np.linalg.cholesky(even)
    odd_cholesky = np.linalg.cholesky(odd)
    whitened = solve_triangular(even_cholesky, blocks.alternating, lower=True)
    whitened = solve_triangular(odd_cholesky, whitened.T, lower=True).T
    largest_singular = np.linalg.svd(whitened, compute_uv=False)[0]
    return (1 - a * a) * largest_singular * largest_singular / 4


def audit(blocks: Blocks, phase_grid: int) -> None:
    print(
        "clean minimum eigenvalues:",
        eigvalsh(blocks.clean_even, subset_by_index=[0, 0])[0],
        eigvalsh(blocks.clean_odd, subset_by_index=[0, 0])[0],
    )
    for a in (-1.0, 1.0):
        print(
            f"pencil minima at a={a:+.0f}:",
            eigvalsh(
                blocks.clean_even + a * blocks.perturb_even,
                subset_by_index=[0, 0],
            )[0],
            eigvalsh(
                blocks.clean_odd + a * blocks.perturb_odd,
                subset_by_index=[0, 0],
            )[0],
        )

    zero = np.zeros((EVEN_DIM, ODD_DIM))
    clean = np.block([[blocks.clean_even, zero], [zero.T, blocks.clean_odd]])
    perturbation = np.block([[blocks.perturb_even, zero], [zero.T, blocks.perturb_odd]])
    alternating = np.block(
        [
            [np.zeros((EVEN_DIM, EVEN_DIM)), blocks.alternating / 2],
            [blocks.alternating.T / 2, np.zeros((ODD_DIM, ODD_DIM))],
        ]
    )
    split_even_plus = np.block(
        [
            [
                blocks.clean_even + blocks.perturb_even,
                blocks.alternating / 2,
            ],
            [
                blocks.alternating.T / 2,
                blocks.clean_odd - blocks.perturb_odd,
            ],
        ]
    )
    split_even_minus = np.block(
        [
            [
                blocks.clean_even - blocks.perturb_even,
                blocks.alternating / 2,
            ],
            [
                blocks.alternating.T / 2,
                blocks.clean_odd + blocks.perturb_odd,
            ],
        ]
    )
    print(
        "static split minimum eigenvalues:",
        eigvalsh(split_even_plus, subset_by_index=[0, 0])[0],
        eigvalsh(split_even_minus, subset_by_index=[0, 0])[0],
    )
    clean_cholesky = np.linalg.cholesky(clean)
    complex_direction = perturbation - 1j * alternating
    normalized = solve_triangular(clean_cholesky, complex_direction, lower=True)
    normalized = (
        solve_triangular(clean_cholesky, normalized.conj().T, lower=True).conj().T
    )
    contraction = np.linalg.svd(normalized, compute_uv=False)[0]
    print(
        "static normalized contraction and margin:",
        contraction,
        1 - contraction,
    )

    a_grid = np.linspace(-1 + 1e-10, 1 - 1e-10, phase_grid)
    ratios = np.array([schur_ratio(blocks, a) for a in a_grid])
    index = int(np.argmax(ratios))
    step = a_grid[1] - a_grid[0]
    lower = max(-1 + 1e-12, a_grid[index] - step)
    upper = min(1 - 1e-12, a_grid[index] + step)
    ratio_result = minimize_scalar(
        lambda a: -schur_ratio(blocks, a),
        bounds=(lower, upper),
        method="bounded",
        options={"xatol": 1e-13},
    )
    worst_a = ratio_result.x
    print(
        "maximum scalar-Schur ratio:",
        schur_ratio(blocks, worst_a),
        "at a =",
        worst_a,
    )

    theta_grid = np.linspace(0, 2 * math.pi, phase_grid)

    def phase_minimum(theta: float) -> float:
        matrix = phase_matrix(blocks, math.cos(theta), math.sin(theta))
        return eigvalsh(matrix, subset_by_index=[0, 0])[0]

    values = np.array([phase_minimum(theta) for theta in theta_grid])
    index = int(np.argmin(values))
    step = theta_grid[1] - theta_grid[0]
    phase_result = minimize_scalar(
        phase_minimum,
        bounds=(theta_grid[index] - step, theta_grid[index] + step),
        method="bounded",
        options={"xatol": 1e-13},
    )
    theta = phase_result.x
    print(
        "minimum full-pencil eigenvalue:",
        phase_result.fun,
        "at (a, b) =",
        (math.cos(theta), math.sin(theta)),
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--order", type=int, default=2048)
    parser.add_argument("--phase-grid", type=int, default=257)
    args = parser.parse_args()
    if args.order < 512:
        parser.error("--order must be at least 512 for frequency 200")
    if args.phase_grid < 17:
        parser.error("--phase-grid must be at least 17")
    audit(construct_blocks(args.order), args.phase_grid)


if __name__ == "__main__":
    main()
