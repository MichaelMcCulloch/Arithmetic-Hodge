#!/usr/bin/env python3
"""Discover and exactly audit the four factor-two endpoint certificates.

This tool consumes the versioned JSON emitted by
``scripts/dump_factor_two_endpoint_scalar_targets.lean``.  It deliberately
does not parse Lean source.  From the scalar interval tables it reconstructs
the current canonical ``201 x 201`` even endpoint targets and the direct
``10 x 10`` odd endpoint targets using exact ``Fraction`` interval
arithmetic.

Floating point is used only to discover sparse inverse-Cholesky rows and a
positive weight vector.  The congruence products, error bounds, and weighted
diagonal-dominance margins are then recomputed from scratch over exact
rationals.  A nonpositive exact margin is fatal.

Typical use from the repository root::

    just guarded lake env lean --run \
      scripts/dump_factor_two_endpoint_scalar_targets.lean \
      | python scripts/generate_factor_two_endpoint_sparse_congruence.py -

Pass ``--json`` to emit the complete canonical audit payload, including the
sparse rows and weights.  The tool never emits Lean files.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import resource
import sys
import time
from collections.abc import Callable, Sequence
from fractions import Fraction as F
from pathlib import Path
from typing import Any, TextIO

import numpy as np

from generate_yoshida_even_sparse_congruence import (
    interval_inv_positive,
    interval_mul,
    interval_sub,
    pure,
)

# Trusted extractor output contains normalized exact rationals whose
# numerators and denominators legitimately exceed Python's default 4300-digit
# JSON conversion guard.  Resource control belongs at the process boundary
# for this provenance workload.
if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)


SOURCE_SCHEMA = "arithmetic-hodge.factor-two-endpoint-scalars.v1"
AUDIT_SCHEMA = "arithmetic-hodge.factor-two-endpoint-sparse-audit.v1"
CERTIFICATE_SCHEMA = "arithmetic-hodge.factor-two-endpoint-certificate.v1"

EVEN_DIMENSION = 201
ODD_DIMENSION = 10
DISCOVERY_SEED = 0  # No PRNG is used; this records the deterministic policy.
DEFAULT_P_THRESHOLD = F(1, 200)
DEFAULT_P_DENOMINATOR = 10_000
DEFAULT_WEIGHT_DENOMINATOR = 1_000
DEFAULT_CENTER_DENOMINATOR = 1_000_000_000_000

# The endpoint certificate handoff uses clean width <= 1/15000 and
# perturbation width <= 1/16000 for both canonical-even and direct-odd target
# matrices.  Addition/subtraction adds widths, and a midpoint error is half
# the width: (1/15000 + 1/16000) / 2 = 31/480000.
STRUCTURAL_ENDPOINT_HALF_WIDTH = F(31, 480_000)

Interval = tuple[F, F]
Matrix = list[list[Interval]]
RationalMatrix = list[list[F]]
SparseRow = dict[int, F]


def canonical_json(value: object) -> bytes:
    """Return the stable JSON encoding used for provenance hashes."""
    return (
        json.dumps(
            value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
        ).encode("ascii")
        + b"\n"
    )


def sha256(value: object) -> str:
    return hashlib.sha256(canonical_json(value)).hexdigest()


def fraction_pair(q: F) -> list[int]:
    return [q.numerator, q.denominator]


def fraction_text(q: F) -> str:
    return f"{q.numerator}/{q.denominator}"


def rational_digit_lengths(values: Sequence[F]) -> dict[str, int]:
    return {
        "max_denominator_digits": max(len(str(value.denominator)) for value in values),
        "max_numerator_digits": max(len(str(abs(value.numerator))) for value in values),
    }


def interval_matrix_sha256(matrix: Matrix) -> str:
    payload = [
        [[fraction_pair(lower), fraction_pair(upper)] for lower, upper in row]
        for row in matrix
    ]
    return sha256(payload)


def rational_matrix_sha256(matrix: RationalMatrix) -> str:
    return sha256([[fraction_pair(value) for value in row] for row in matrix])


def parse_fraction_text(value: str) -> F:
    try:
        return F(value)
    except (ValueError, ZeroDivisionError) as exc:
        raise argparse.ArgumentTypeError(f"invalid rational {value!r}") from exc


def interval_add(x: Interval, y: Interval) -> Interval:
    return x[0] + y[0], x[1] + y[1]


def interval_div_positive(x: Interval, y: Interval) -> Interval:
    return interval_mul(x, interval_inv_positive(y))


def interval_scale(q: F, x: Interval) -> Interval:
    return interval_mul(pure(q), x)


def round_to_grid_ties_to_even(value: F, denominator: int) -> F:
    """Round an exact rational to ``1 / denominator``, ties to even."""
    if denominator <= 0:
        raise ValueError("center denominator must be positive")
    scaled_numerator = value.numerator * denominator
    lower, remainder = divmod(scaled_numerator, value.denominator)
    comparison = 2 * remainder - value.denominator
    if comparison < 0:
        numerator = lower
    elif comparison > 0:
        numerator = lower + 1
    else:
        numerator = lower if lower % 2 == 0 else lower + 1
    return F(numerator, denominator)


def quantize_center_matrix(
    centers: RationalMatrix, denominator: int
) -> tuple[RationalMatrix, F]:
    quantized = [
        [round_to_grid_ties_to_even(value, denominator) for value in row]
        for row in centers
    ]
    maximum_error = max(
        abs(centers[i][j] - quantized[i][j])
        for i in range(len(centers))
        for j in range(len(centers))
    )
    if maximum_error > F(1, 2 * denominator):
        raise AssertionError("nearest-grid rounding exceeded half a grid cell")
    return quantized, maximum_error


def require_valid(name: str, value: Interval) -> Interval:
    if value[0] > value[1]:
        raise ValueError(f"invalid interval {name}: {value!r}")
    return value


def parse_pair(value: object, location: str) -> F:
    if (
        not isinstance(value, list)
        or len(value) != 2
        or isinstance(value[0], bool)
        or isinstance(value[1], bool)
        or not isinstance(value[0], int)
        or not isinstance(value[1], int)
    ):
        raise ValueError(f"{location} is not an integer rational pair")
    numerator, denominator = value
    if denominator <= 0:
        raise ValueError(f"{location} has nonpositive denominator")
    result = F(numerator, denominator)
    if result.numerator != numerator or result.denominator != denominator:
        raise ValueError(f"{location} is not in normalized rational form")
    return result


def parse_interval(value: object, location: str) -> Interval:
    if not isinstance(value, dict):
        raise ValueError(f"{location} is not an interval object")
    result = (
        parse_pair(value.get("lower"), f"{location}.lower"),
        parse_pair(value.get("upper"), f"{location}.upper"),
    )
    return require_valid(location, result)


def parse_table(value: object, name: str) -> list[Interval]:
    if not isinstance(value, list):
        raise ValueError(f"tables.{name} is not a list")
    result: list[Interval | None] = [None] * EVEN_DIMENSION
    for position, entry in enumerate(value):
        location = f"tables.{name}[{position}]"
        if not isinstance(entry, dict):
            raise ValueError(f"{location} is not an object")
        mode = entry.get("mode")
        if isinstance(mode, bool) or not isinstance(mode, int):
            raise ValueError(f"{location}.mode is not an integer")
        if not 0 <= mode < EVEN_DIMENSION:
            raise ValueError(f"{location}.mode is out of range: {mode}")
        if result[mode] is not None:
            raise ValueError(f"tables.{name} repeats mode {mode}")
        result[mode] = parse_interval(entry, location)
    missing = [mode for mode, interval in enumerate(result) if interval is None]
    if missing:
        raise ValueError(f"tables.{name} is missing modes {missing}")
    return [interval for interval in result if interval is not None]


def load_scalar_payload(stream: TextIO) -> dict[str, object]:
    try:
        raw = json.load(stream)
    except json.JSONDecodeError as exc:
        raise ValueError(f"invalid scalar JSON: {exc}") from exc
    if not isinstance(raw, dict):
        raise ValueError("scalar JSON root is not an object")
    if raw.get("schema") != SOURCE_SCHEMA:
        raise ValueError(
            f"unsupported scalar schema {raw.get('schema')!r}; "
            f"expected {SOURCE_SCHEMA!r}"
        )
    if raw.get("mode_range") != [0, 200]:
        raise ValueError("mode_range is not exactly [0, 200]")

    raw_tables = raw.get("tables")
    if not isinstance(raw_tables, dict):
        raise ValueError("tables is not an object")
    tables = {name: parse_table(raw_tables.get(name), name) for name in "SDsc"}

    raw_constants = raw.get("constants")
    if not isinstance(raw_constants, dict):
        raise ValueError("constants is not an object")
    constants = {
        name: parse_interval(raw_constants.get(name), f"constants.{name}")
        for name in ("invPi", "invSqrtTwo", "endpointScale")
    }
    if constants["invPi"] != (F(10_000, 31_416), F(10_000, 31_415)):
        raise ValueError("invPi no longer matches the odd and even target formulas")
    if constants["invSqrtTwo"][0] <= 0:
        raise ValueError("invSqrtTwo is not positive")
    if constants["endpointScale"][0] <= 0:
        raise ValueError("endpointScale is not positive")

    return {
        "constants": constants,
        "raw": raw,
        "source_sha256": sha256(raw),
        "tables": tables,
    }


def even_zero_coefficient(mode: int) -> F:
    if mode == 0:
        raise ValueError("the even zero-mode coefficient requires a positive mode")
    return F((-1) ** (mode + 1), mode)


def off_diagonal_coefficient(n: int, m: int) -> F:
    denominator = n * n - m * m
    if denominator == 0:
        raise ValueError("off-diagonal coefficient received equal modes")
    return F((-1) ** (n + m), denominator)


def canonical_even_clean_unscaled(data: dict[str, object], n: int, m: int) -> Interval:
    tables: dict[str, list[Interval]] = data["tables"]  # type: ignore[assignment]
    constants: dict[str, Interval] = data["constants"]  # type: ignore[assignment]
    sine = tables["S"]
    diagonal = tables["D"]
    inv_pi = constants["invPi"]
    inv_sqrt_two = constants["invSqrtTwo"]

    if n == 0:
        if m == 0:
            return diagonal[0]
        return interval_mul(
            interval_mul(
                interval_mul(pure(even_zero_coefficient(m)), inv_pi),
                inv_sqrt_two,
            ),
            sine[m],
        )
    if m == 0:
        return canonical_even_clean_unscaled(data, 0, n)
    if n == m:
        correction = interval_mul(interval_mul(pure(F(1, 2 * n)), inv_pi), sine[n])
        return interval_sub(diagonal[n], correction)
    difference = interval_sub(
        interval_scale(F(m), sine[m]), interval_scale(F(n), sine[n])
    )
    return interval_mul(
        interval_mul(pure(off_diagonal_coefficient(n, m)), inv_pi), difference
    )


def canonical_even_clean(data: dict[str, object], n: int, m: int) -> Interval:
    constants: dict[str, Interval] = data["constants"]  # type: ignore[assignment]
    return interval_div_positive(
        canonical_even_clean_unscaled(data, n, m), constants["endpointScale"]
    )


def canonical_even_perturbation(data: dict[str, object], n: int, m: int) -> Interval:
    tables: dict[str, list[Interval]] = data["tables"]  # type: ignore[assignment]
    constants: dict[str, Interval] = data["constants"]  # type: ignore[assignment]
    sine = tables["s"]
    affine_cosine = tables["c"]
    inv_pi = constants["invPi"]
    inv_sqrt_two = constants["invSqrtTwo"]
    endpoint_scale = constants["endpointScale"]

    if n == 0:
        if m == 0:
            numerator = interval_scale(F(1, 2), affine_cosine[0])
        else:
            numerator = interval_mul(
                interval_mul(
                    interval_mul(pure(even_zero_coefficient(m)), inv_pi),
                    inv_sqrt_two,
                ),
                sine[m],
            )
    elif m == 0:
        return canonical_even_perturbation(data, 0, n)
    elif n == m:
        correction = interval_mul(interval_mul(pure(F(1, n)), inv_pi), sine[n])
        numerator = interval_scale(F(1, 2), interval_sub(affine_cosine[n], correction))
    else:
        difference = interval_sub(
            interval_scale(F(m), sine[m]), interval_scale(F(n), sine[n])
        )
        numerator = interval_mul(
            interval_mul(pure(off_diagonal_coefficient(n, m)), inv_pi),
            difference,
        )
    return interval_div_positive(numerator, endpoint_scale)


def odd_clean(data: dict[str, object], i: int, j: int) -> Interval:
    tables: dict[str, list[Interval]] = data["tables"]  # type: ignore[assignment]
    constants: dict[str, Interval] = data["constants"]  # type: ignore[assignment]
    n, m = i + 1, j + 1
    sine = tables["S"]
    diagonal = tables["D"]
    inv_pi = constants["invPi"]

    if i == j:
        correction = interval_mul(interval_mul(pure(F(1, 2 * n)), inv_pi), sine[n])
        numerator = interval_add(diagonal[n], correction)
    else:
        difference = interval_sub(
            interval_scale(F(n), sine[m]), interval_scale(F(m), sine[n])
        )
        numerator = interval_mul(
            interval_mul(pure(off_diagonal_coefficient(n, m)), inv_pi),
            difference,
        )
    return interval_div_positive(numerator, constants["endpointScale"])


def odd_perturbation(data: dict[str, object], i: int, j: int) -> Interval:
    tables: dict[str, list[Interval]] = data["tables"]  # type: ignore[assignment]
    constants: dict[str, Interval] = data["constants"]  # type: ignore[assignment]
    n, m = i + 1, j + 1
    sine = tables["s"]
    affine_cosine = tables["c"]
    inv_pi = constants["invPi"]

    if i == j:
        correction = interval_mul(interval_mul(pure(F(1, n)), inv_pi), sine[n])
        numerator = interval_scale(F(1, 2), interval_add(affine_cosine[n], correction))
    else:
        difference = interval_sub(
            interval_scale(F(n), sine[m]), interval_scale(F(m), sine[n])
        )
        numerator = interval_mul(
            interval_mul(pure(off_diagonal_coefficient(n, m)), inv_pi),
            difference,
        )
    return interval_div_positive(numerator, constants["endpointScale"])


def build_endpoint_pair(
    dimension: int,
    clean_entry: Callable[[int, int], Interval],
    perturbation_entry: Callable[[int, int], Interval],
) -> tuple[Matrix, Matrix]:
    plus = [[pure(F(0)) for _ in range(dimension)] for _ in range(dimension)]
    minus = [[pure(F(0)) for _ in range(dimension)] for _ in range(dimension)]
    for i in range(dimension):
        for j in range(i, dimension):
            clean = require_valid(f"clean[{i},{j}]", clean_entry(i, j))
            perturbation = require_valid(
                f"perturbation[{i},{j}]", perturbation_entry(i, j)
            )
            plus_value = require_valid(
                f"plus[{i},{j}]", interval_add(clean, perturbation)
            )
            minus_value = require_valid(
                f"minus[{i},{j}]", interval_sub(clean, perturbation)
            )
            plus[i][j] = plus[j][i] = plus_value
            minus[i][j] = minus[j][i] = minus_value
    return plus, minus


def build_endpoint_matrices(data: dict[str, object]) -> dict[str, Matrix]:
    even_plus, even_minus = build_endpoint_pair(
        EVEN_DIMENSION,
        lambda i, j: canonical_even_clean(data, i, j),
        lambda i, j: canonical_even_perturbation(data, i, j),
    )
    odd_plus, odd_minus = build_endpoint_pair(
        ODD_DIMENSION,
        lambda i, j: odd_clean(data, i, j),
        lambda i, j: odd_perturbation(data, i, j),
    )
    return {
        "canonical_even_plus": even_plus,
        "canonical_even_minus": even_minus,
        "odd_plus": odd_plus,
        "odd_minus": odd_minus,
    }


def matrix_centers_and_radii(
    intervals: Matrix,
) -> tuple[RationalMatrix, RationalMatrix, F, tuple[int, int]]:
    dimension = len(intervals)
    centers = [[F(0) for _ in range(dimension)] for _ in range(dimension)]
    radii = [[F(0) for _ in range(dimension)] for _ in range(dimension)]
    maximum = F(-1)
    location = (-1, -1)
    for i in range(dimension):
        if len(intervals[i]) != dimension:
            raise ValueError("interval matrix is not square")
        for j in range(dimension):
            lower, upper = require_valid(f"matrix[{i},{j}]", intervals[i][j])
            centers[i][j] = (lower + upper) / 2
            radii[i][j] = (upper - lower) / 2
            if radii[i][j] > maximum:
                maximum = radii[i][j]
                location = (i, j)
            if intervals[i][j] != intervals[j][i]:
                raise ValueError(f"interval matrix is not symmetric at ({i}, {j})")
    return centers, radii, maximum, location


def discover_preconditioner(
    centers: RationalMatrix, threshold: F, denominator: int
) -> tuple[list[list[tuple[int, int]]], list[SparseRow], float]:
    dimension = len(centers)
    center_float = np.array(
        [[float(value) for value in row] for row in centers], dtype=np.float64
    )
    eigenvalues = np.linalg.eigvalsh(center_float)
    minimum_eigenvalue = float(eigenvalues[0])
    try:
        cholesky = np.linalg.cholesky(center_float)
    except np.linalg.LinAlgError as exc:
        raise ValueError(
            f"center is not numerically positive definite; "
            f"minimum eigenvalue={minimum_eigenvalue:.18g}"
        ) from exc
    inverse_cholesky = np.linalg.solve(cholesky, np.eye(dimension, dtype=np.float64))

    threshold_float = float(threshold)
    grid_rows: list[list[tuple[int, int]]] = []
    rows: list[SparseRow] = []
    for i in range(dimension):
        grid_row: list[tuple[int, int]] = []
        rational_row: SparseRow = {}
        for j in range(i + 1):
            value = float(inverse_cholesky[i, j])
            if not math.isfinite(value):
                raise ValueError(
                    "inverse-Cholesky discovery produced a nonfinite value"
                )
            if abs(value) >= threshold_float:
                numerator = int(np.rint(value * denominator))
                if numerator:
                    grid_row.append((j, numerator))
                    rational_row[j] = F(numerator, denominator)
        if rational_row.get(i, F(0)) <= 0:
            raise ValueError(
                f"sparse preconditioner row {i} lost its positive diagonal"
            )
        grid_rows.append(grid_row)
        rows.append(rational_row)
    return grid_rows, rows, minimum_eigenvalue


def exact_congruence(
    rows: Sequence[SparseRow], centers: RationalMatrix
) -> RationalMatrix:
    dimension = len(rows)
    result = [[F(0) for _ in range(dimension)] for _ in range(dimension)]
    for i in range(dimension):
        for j in range(i, dimension):
            value = sum(
                (
                    p_i_k * centers[k][ell] * p_j_ell
                    for k, p_i_k in rows[i].items()
                    for ell, p_j_ell in rows[j].items()
                ),
                F(0),
            )
            result[i][j] = result[j][i] = value
    return result


def discover_weights(
    congruence: RationalMatrix,
    row_l1: Sequence[F],
    epsilon: F,
    denominator: int,
) -> list[int]:
    dimension = len(congruence)
    transformed = np.array(
        [[float(value) for value in row] for row in congruence], dtype=np.float64
    )
    l1_float = np.array([float(value) for value in row_l1], dtype=np.float64)
    epsilon_float = float(epsilon)
    diagonal_lower = np.diag(transformed) - epsilon_float * l1_float * l1_float
    if float(np.min(diagonal_lower)) <= 0:
        raise ValueError(
            "a transformed diagonal lower bound is numerically nonpositive"
        )
    comparison = np.abs(transformed) + epsilon_float * np.outer(l1_float, l1_float)
    np.fill_diagonal(comparison, 0.0)
    comparison /= diagonal_lower[:, None]

    eigenvalues, eigenvectors = np.linalg.eig(comparison)
    index = int(np.argmax(np.abs(eigenvalues)))
    if abs(float(eigenvalues[index].imag)) > 1e-10:
        raise ValueError("dominant comparison eigenvalue is unexpectedly nonreal")
    vector = np.abs(np.real(eigenvectors[:, index]))
    if not np.all(np.isfinite(vector)) or float(np.min(vector)) <= 0:
        raise ValueError("Perron discovery vector is not strictly positive")
    vector /= np.min(vector)
    weights = [max(1, int(np.rint(value * denominator))) for value in vector]
    if len(weights) != dimension:
        raise AssertionError("weight discovery changed dimension")
    return weights


def audit_matrix(
    name: str,
    intervals: Matrix,
    source_sha256: str,
    epsilon: F,
    p_threshold: F,
    p_denominator: int,
    weight_denominator: int,
    center_denominator: int,
) -> dict[str, object]:
    exact_centers, _radii, max_radius, max_radius_location = matrix_centers_and_radii(
        intervals
    )
    if max_radius > epsilon:
        raise ValueError(
            f"{name}: exact maximum half-width {max_radius} exceeds "
            f"the audit bound {epsilon}"
        )

    if center_denominator:
        audit_centers, exact_center_rounding_error = quantize_center_matrix(
            exact_centers, center_denominator
        )
        center_rounding_error_bound = F(1, 2 * center_denominator)
    else:
        audit_centers = exact_centers
        exact_center_rounding_error = F(0)
        center_rounding_error_bound = F(0)
    audit_epsilon = epsilon + center_rounding_error_bound
    exact_interval_to_audit_center = max(
        max(
            audit_centers[i][j] - intervals[i][j][0],
            intervals[i][j][1] - audit_centers[i][j],
        )
        for i in range(len(intervals))
        for j in range(len(intervals))
    )
    if exact_interval_to_audit_center > audit_epsilon:
        raise ValueError(
            f"{name}: an exact source interval escapes its audit-center box: "
            f"required {exact_interval_to_audit_center}, bound {audit_epsilon}"
        )

    grid_rows, rows, minimum_eigenvalue = discover_preconditioner(
        audit_centers, p_threshold, p_denominator
    )
    dimension = len(rows)
    support_sizes = [len(row) for row in rows]
    nnz = sum(support_sizes)
    congruence = exact_congruence(rows, audit_centers)
    row_l1 = [sum((abs(value) for value in row.values()), F(0)) for row in rows]
    weight_grid = discover_weights(
        congruence, row_l1, audit_epsilon, weight_denominator
    )
    weights = [F(value, weight_denominator) for value in weight_grid]

    diagonal_lowers: list[F] = []
    margins: list[F] = []
    ratios: list[F] = []
    for i in range(dimension):
        diagonal_lower = congruence[i][i] - audit_epsilon * row_l1[i] * row_l1[i]
        off_diagonal = sum(
            (
                (abs(congruence[i][j]) + audit_epsilon * row_l1[i] * row_l1[j])
                * weights[j]
                for j in range(dimension)
                if j != i
            ),
            F(0),
        )
        weighted_diagonal = diagonal_lower * weights[i]
        margin = weighted_diagonal - off_diagonal
        diagonal_lowers.append(diagonal_lower)
        margins.append(margin)
        ratios.append(off_diagonal / weighted_diagonal)
    bad_rows = [i for i, margin in enumerate(margins) if margin <= 0]
    if bad_rows:
        raise ValueError(f"{name}: exact weighted dominance failed in rows {bad_rows}")

    minimum_margin_row = min(range(dimension), key=margins.__getitem__)
    maximum_ratio_row = max(range(dimension), key=ratios.__getitem__)
    index_order = (
        "transported canonical frequencies 0..200 via "
        "factorTwoCanonicalEndpointLinearOrder"
        if name.startswith("canonical_even_")
        else "Fin 10 natural order 0..9 (frequencies 1..10)"
    )
    payload = {
        "audit_center_denominator": center_denominator,
        "audit_center_matrix_sha256": rational_matrix_sha256(audit_centers),
        "center_rounding_error_bound": fraction_pair(center_rounding_error_bound),
        "dimension": dimension,
        "exact_center_matrix_sha256": rational_matrix_sha256(exact_centers),
        "index_order": index_order,
        "interval_matrix_sha256": interval_matrix_sha256(intervals),
        "matrix": name,
        "p_denominator": p_denominator,
        "p_rows": grid_rows,
        "p_threshold": fraction_pair(p_threshold),
        "schema": CERTIFICATE_SCHEMA,
        "source_scalars_sha256": source_sha256,
        "source_interval_half_width": fraction_pair(epsilon),
        "uniform_half_width": fraction_pair(audit_epsilon),
        "weight_denominator": weight_denominator,
        "weights": weight_grid,
    }
    payload_sha256 = sha256(payload)
    return {
        "center_min_eigenvalue_float": minimum_eigenvalue,
        "exact_digit_lengths": {
            "audit_center": rational_digit_lengths(
                [value for row in audit_centers for value in row]
            ),
            "exact_center": rational_digit_lengths(
                [value for row in exact_centers for value in row]
            ),
            "congruence": rational_digit_lengths(
                [value for row in congruence for value in row]
            ),
            "weighted_margins": rational_digit_lengths(margins),
        },
        "dimension": dimension,
        "exact_max_half_width": fraction_pair(max_radius),
        "exact_max_half_width_location": list(max_radius_location),
        "exact_max_center_rounding_error": fraction_pair(exact_center_rounding_error),
        "exact_max_interval_to_audit_center": fraction_pair(
            exact_interval_to_audit_center
        ),
        "max_offdiag_to_diag_ratio_float": float(ratios[maximum_ratio_row]),
        "max_offdiag_to_diag_ratio_row": maximum_ratio_row,
        "min_exact_diagonal_lower": fraction_pair(min(diagonal_lowers)),
        "min_exact_weighted_margin": fraction_pair(margins[minimum_margin_row]),
        "min_exact_weighted_margin_row": minimum_margin_row,
        "nnz": nnz,
        "payload": payload,
        "payload_sha256": payload_sha256,
        "row_l1_max": fraction_pair(max(row_l1)),
        "row_l1_min": fraction_pair(min(row_l1)),
        "support_max": max(support_sizes),
        "support_min": min(support_sizes),
        "source_half_width_slack": fraction_pair(epsilon - max_radius),
        "uniform_half_width_slack": fraction_pair(
            audit_epsilon - max_radius - exact_center_rounding_error
        ),
        "weight_numerator_max": max(weight_grid),
        "weight_numerator_min": min(weight_grid),
    }


def audit(
    data: dict[str, object],
    epsilon: F,
    p_threshold: F,
    p_denominator: int,
    weight_denominator: int,
    center_denominator: int,
) -> dict[str, object]:
    if epsilon <= 0:
        raise ValueError("uniform half-width must be positive")
    if p_threshold < 0:
        raise ValueError("P threshold must be nonnegative")
    if p_denominator <= 0 or weight_denominator <= 0:
        raise ValueError("rounding denominators must be positive")
    if center_denominator < 0:
        raise ValueError("center denominator must be nonnegative")

    source_sha256: str = data["source_sha256"]  # type: ignore[assignment]
    matrices = build_endpoint_matrices(data)
    certificates = {
        name: audit_matrix(
            name,
            matrix,
            source_sha256,
            epsilon,
            p_threshold,
            p_denominator,
            weight_denominator,
            center_denominator,
        )
        for name, matrix in matrices.items()
    }
    core = {
        "certificates": certificates,
        "discovery": {
            "audit_center_denominator": center_denominator,
            "audit_center_rounding": (
                "exact Fraction nearest grid; ties to even"
                if center_denominator
                else "exact midpoint"
            ),
            "center_rounding_error_bound": fraction_pair(
                F(1, 2 * center_denominator) if center_denominator else F(0)
            ),
            "p_denominator": p_denominator,
            "p_rounding": "binary64 inverse Cholesky; abs threshold; numpy rint",
            "p_threshold": fraction_pair(p_threshold),
            "seed": DISCOVERY_SEED,
            "source_interval_half_width": fraction_pair(epsilon),
            "uniform_half_width": fraction_pair(
                epsilon + (F(1, 2 * center_denominator) if center_denominator else F(0))
            ),
            "uniform_half_width_source": (
                "(clean width 1/15000 + perturbation width 1/16000) / 2"
                if epsilon == STRUCTURAL_ENDPOINT_HALF_WIDTH
                else "command line override"
            ),
            "weight_denominator": weight_denominator,
            "weight_rounding": "Perron/min; numpy rint",
        },
        "schema": AUDIT_SCHEMA,
        "source_schema": SOURCE_SCHEMA,
        "source_scalars_sha256": source_sha256,
    }
    return {"audit_payload_sha256": sha256(core), **core}


def print_report(result: dict[str, object], stream: TextIO) -> None:
    certificates: dict[str, dict[str, Any]] = result["certificates"]  # type: ignore[assignment]
    discovery: dict[str, Any] = result["discovery"]  # type: ignore[assignment]
    run_metrics: dict[str, Any] = result["run_metrics"]  # type: ignore[assignment]
    print("Factor-two endpoint sparse-congruence audit: PASS", file=stream)
    print(f"source_scalars_sha256={result['source_scalars_sha256']}", file=stream)
    print(f"audit_payload_sha256={result['audit_payload_sha256']}", file=stream)
    print(
        "discovery_seed=0 (no PRNG) "
        f"P_threshold={fraction_text(F(*discovery['p_threshold']))} "
        f"P_denominator={discovery['p_denominator']} "
        f"center_denominator={discovery['audit_center_denominator']} "
        f"weight_denominator={discovery['weight_denominator']} "
        f"uniform_half_width={fraction_text(F(*discovery['uniform_half_width']))}",
        file=stream,
    )
    print(
        f"python_seconds={run_metrics['python_seconds']:.6f} "
        f"peak_rss_kib={run_metrics['peak_rss_kib']}",
        file=stream,
    )
    for name, certificate in certificates.items():
        max_radius = F(*certificate["exact_max_half_width"])
        rounding_error = F(*certificate["exact_max_center_rounding_error"])
        interval_to_center = F(*certificate["exact_max_interval_to_audit_center"])
        slack = F(*certificate["uniform_half_width_slack"])
        margin = F(*certificate["min_exact_weighted_margin"])
        radius_digits = rational_digit_lengths([max_radius])
        print(
            f"{name}: dimension={certificate['dimension']} "
            f"center_min_eigenvalue~{certificate['center_min_eigenvalue_float']:.18g} "
            f"P_nnz={certificate['nnz']} "
            f"support={certificate['support_min']}..{certificate['support_max']} "
            f"max_half_width~{float(max_radius):.18g} "
            f"at={certificate['exact_max_half_width_location']} "
            f"rounding_error~{float(rounding_error):.18g} "
            f"interval_to_center~{float(interval_to_center):.18g} "
            f"radius_digits={radius_digits['max_numerator_digits']}/"
            f"{radius_digits['max_denominator_digits']} "
            f"slack~{float(slack):.18g}",
            file=stream,
        )
        digit_lengths = certificate["exact_digit_lengths"]
        print(
            "  exact_digits="
            f"midpoint(n={digit_lengths['exact_center']['max_numerator_digits']},"
            f"d={digit_lengths['exact_center']['max_denominator_digits']}) "
            f"audit_center(n={digit_lengths['audit_center']['max_numerator_digits']},"
            f"d={digit_lengths['audit_center']['max_denominator_digits']}) "
            f"congruence(n={digit_lengths['congruence']['max_numerator_digits']},"
            f"d={digit_lengths['congruence']['max_denominator_digits']}) "
            f"margins(n={digit_lengths['weighted_margins']['max_numerator_digits']},"
            f"d={digit_lengths['weighted_margins']['max_denominator_digits']})",
            file=stream,
        )
        payload = certificate["payload"]
        print(
            f"  interval_matrix_sha256={payload['interval_matrix_sha256']} "
            f"exact_center_sha256={payload['exact_center_matrix_sha256']} "
            f"audit_center_sha256={payload['audit_center_matrix_sha256']}",
            file=stream,
        )
        print(
            f"  min_exact_weighted_margin_row="
            f"{certificate['min_exact_weighted_margin_row']} "
            f"margin={fraction_text(margin)} (~{float(margin):.18g}) "
            f"max_ratio~{certificate['max_offdiag_to_diag_ratio_float']:.18g} "
            f"payload_sha256={certificate['payload_sha256']}",
            file=stream,
        )


def open_input(path: str) -> tuple[TextIO, bool]:
    if path == "-":
        return sys.stdin, False
    return Path(path).open(encoding="utf-8"), True


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "input",
        nargs="?",
        default="-",
        help="scalar-target JSON path, or - for stdin (default: -)",
    )
    parser.add_argument(
        "--epsilon",
        type=parse_fraction_text,
        default=STRUCTURAL_ENDPOINT_HALF_WIDTH,
        help="uniform entry half-width bound (default: structural production bound)",
    )
    parser.add_argument(
        "--p-threshold",
        type=parse_fraction_text,
        default=DEFAULT_P_THRESHOLD,
        help="inverse-Cholesky retention threshold (default: 1/200)",
    )
    parser.add_argument(
        "--p-denominator",
        type=int,
        default=DEFAULT_P_DENOMINATOR,
        help="preconditioner rounding denominator (default: 10000)",
    )
    parser.add_argument(
        "--weight-denominator",
        type=int,
        default=DEFAULT_WEIGHT_DENOMINATOR,
        help="weight rounding denominator (default: 1000)",
    )
    parser.add_argument(
        "--center-denominator",
        type=int,
        default=DEFAULT_CENTER_DENOMINATOR,
        help=(
            "exact midpoint rounding grid (default: 1000000000000; "
            "use 0 for the unquantized midpoint baseline)"
        ),
    )
    parser.add_argument(
        "--json", action="store_true", help="emit the complete audit JSON"
    )
    parser.add_argument(
        "--expect-source-sha256",
        help="fail unless the canonical scalar payload has this SHA-256",
    )
    parser.add_argument(
        "--expect-audit-sha256",
        help="fail unless the complete audit payload has this SHA-256",
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    started = time.perf_counter()
    args = parse_args(argv)
    stream, should_close = open_input(args.input)
    try:
        data = load_scalar_payload(stream)
    finally:
        if should_close:
            stream.close()
    if args.expect_source_sha256 and data["source_sha256"] != args.expect_source_sha256:
        raise ValueError(
            "source scalar digest drifted: "
            f"expected {args.expect_source_sha256}, got {data['source_sha256']}"
        )
    result = audit(
        data,
        args.epsilon,
        args.p_threshold,
        args.p_denominator,
        args.weight_denominator,
        args.center_denominator,
    )
    result["run_metrics"] = {
        "peak_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        "python_seconds": time.perf_counter() - started,
    }
    if (
        args.expect_audit_sha256
        and result["audit_payload_sha256"] != args.expect_audit_sha256
    ):
        raise ValueError(
            "audit payload digest drifted: "
            f"expected {args.expect_audit_sha256}, "
            f"got {result['audit_payload_sha256']}"
        )
    if args.json:
        json.dump(result, sys.stdout, indent=2, sort_keys=True)
        sys.stdout.write("\n")
    else:
        print_report(result, sys.stdout)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise SystemExit(1) from exc
