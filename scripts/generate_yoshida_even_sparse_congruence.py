#!/usr/bin/env python3
"""Generate and exactly audit the sparse Yoshida-even congruence certificate.

This is a tracked provenance/discovery tool.  It parses the rational target
boxes from ``YoshidaEvenMomentTargets.lean``, reconstructs the exact interval
matrix used by ``inflatedEvenMomentIntervalGram``, discovers a sparse rational
inverse-Cholesky preconditioner, and then forgets all floating-point claims:
the final 200 weighted diagonal-dominance inequalities are recomputed with
``fractions.Fraction``.

Discovery is deterministic and uses no random numbers.  ``DISCOVERY_SEED`` is
recorded as zero solely to make that rule explicit.  The two rounding rules
are:

* retain a lower-triangular inverse-Cholesky entry iff its binary64 absolute
  value is at least 0.005, then round it to the nearest 1/10000 with NumPy's
  ties-to-even ``rint``;
* normalize the positive Perron vector of the comparison matrix so its
  smallest entry is one, then round to the nearest 1/1000 with the same rule.

The canonical payload SHA-256 is a drift gate.  Different BLAS/LAPACK output
is harmless only if it rounds to exactly the same rational certificate.  The
tool never writes files.  ``--emit-lean`` writes the complete Phase-A Lean
data module to stdout, with the canonical payload represented once as
computable ``(column, coefficient)`` lists and bridged to sparse ``Finsupp``
rows; all audit diagnostics then go to stderr.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import re
import sys
from fractions import Fraction as F
from pathlib import Path
from typing import TextIO

import numpy as np


N = 200
DISCOVERY_SEED = 0  # Reserved: this script deliberately uses no PRNG.
P_THRESHOLD = 0.005
P_DENOMINATOR = 10_000
WEIGHT_DENOMINATOR = 1_000
UNIFORM_HALF_WIDTH = F(51, 100_000)
BLOCK_BUDGET_DENOMINATOR = 1_000_000_000_000

TARGET_SOURCE = Path("ArithmeticHodge/Analysis/YoshidaEvenMomentTargets.lean")
INTERVAL_SOURCE = Path(
    "ArithmeticHodge/Analysis/YoshidaEvenIntervalCertificate.lean"
)

EXPECTED_TARGETS_SHA256 = (
    "ff6bd4c66efdbfda0395f89f0e70263a1e6f1bc59778d2f833f4fbafbd265491"
)
EXPECTED_PAYLOAD_SHA256 = (
    "cdb37a48b2b2c28a71f266efdd84ed32bccd2d4c418037277b9bbd5a89dea9db"
)
EXPECTED_MAX_HALF_WIDTH = F(41_214_331, 80_896_200_000)
EXPECTED_MAX_HALF_WIDTH_LOCATION = (1, 1)
EXPECTED_NNZ = 762
EXPECTED_SUPPORT_MIN = 1
EXPECTED_SUPPORT_MAX = 10

Interval = tuple[F, F]
SparseRow = dict[int, F]

_TARGET_CASE = re.compile(
    r"\|\s*(\d+)\s*=>\s*⟨\s*(-?\d+)\s*/\s*(\d+)\s*,"
    r"\s*(-?\d+)\s*/\s*(\d+)\s*⟩"
)


def _canonical_json(value: object) -> bytes:
    return (
        json.dumps(
            value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
        ).encode("ascii")
        + b"\n"
    )


def _sha256(blob: bytes) -> str:
    return hashlib.sha256(blob).hexdigest()


def _fraction_pair(q: F) -> list[int]:
    return [q.numerator, q.denominator]


def _fraction_text(q: F) -> str:
    return f"{q.numerator}/{q.denominator}"


def _round_up_fraction(q: F, denominator: int) -> F:
    scaled = q * denominator
    numerator = -(-scaled.numerator // scaled.denominator)
    return F(numerator, denominator)


def _definition_body(source: str, name: str) -> str:
    marker = f"def {name}"
    try:
        body = source.split(marker, 1)[1]
    except IndexError as exc:
        raise ValueError(f"definition {name!r} was not found") from exc
    boundary = re.search(
        r"\n(?:def |theorem |private theorem |instance |end )", body
    )
    return body if boundary is None else body[: boundary.start()]


def _parse_targets(source: str, name: str) -> dict[int, Interval]:
    body = _definition_body(source, name)
    result = {
        int(n): (F(int(lo), int(ld)), F(int(hi), int(hd)))
        for n, lo, ld, hi, hd in _TARGET_CASE.findall(body)
    }
    if not result:
        raise ValueError(f"no interval cases parsed from {name}")
    return result


def _parse_named_interval(source: str, name: str) -> Interval:
    body = _definition_body(source, name)
    match = re.search(
        r"⟨\s*(-?\d+)\s*/\s*(\d+)\s*,\s*(-?\d+)\s*/\s*(\d+)\s*⟩",
        body,
    )
    if match is None:
        raise ValueError(f"could not parse interval definition {name}")
    lo, ld, hi, hd = map(int, match.groups())
    return F(lo, ld), F(hi, hd)


def _parse_named_fraction(source: str, name: str) -> F:
    body = _definition_body(source, name)
    match = re.search(r":=\s*(-?\d+)\s*/\s*(\d+)", body)
    if match is None:
        raise ValueError(f"could not parse rational definition {name}")
    return F(int(match.group(1)), int(match.group(2)))


def interval_mul(x: Interval, y: Interval) -> Interval:
    products = tuple(a * b for a in x for b in y)
    return min(products), max(products)


def interval_sub(x: Interval, y: Interval) -> Interval:
    return x[0] - y[1], x[1] - y[0]


def interval_inv_positive(x: Interval) -> Interval:
    if x[0] <= 0:
        raise ValueError(f"positive interval required, got {x}")
    return 1 / x[1], 1 / x[0]


def pure(q: F) -> Interval:
    return q, q


def read_source_data(repo_root: Path) -> dict[str, object]:
    target_path = repo_root / TARGET_SOURCE
    interval_path = repo_root / INTERVAL_SOURCE
    target_text = target_path.read_text(encoding="utf-8")
    interval_text = interval_path.read_text(encoding="utf-8")

    sine = _parse_targets(target_text, "yoshidaEvenSineTargets")
    diagonal = _parse_targets(target_text, "yoshidaEvenDiagonalTargets")
    if set(sine) != set(range(1, N)):
        raise ValueError("sine targets are not exactly modes 1 through 199")
    if set(diagonal) != set(range(N)):
        raise ValueError("diagonal targets are not exactly modes 0 through 199")
    if any(lo > hi for lo, hi in [*sine.values(), *diagonal.values()]):
        raise ValueError("an input target interval is invalid")

    inv_pi = _parse_named_interval(interval_text, "evenInvPiInterval")
    sqrt_two = _parse_named_interval(interval_text, "evenSqrtTwoInterval")
    inv_sqrt_two = interval_inv_positive(sqrt_two)
    correction = _parse_named_fraction(interval_text, "evenCorrectionRadius")

    expected_constants = {
        "inv_pi": (F(10_000, 31_416), F(10_000, 31_415)),
        "sqrt_two": (F(141_421, 100_000), F(141_422, 100_000)),
        "correction": F(1, 2_000),
    }
    actual_constants = {
        "inv_pi": inv_pi,
        "sqrt_two": sqrt_two,
        "correction": correction,
    }
    if actual_constants != expected_constants:
        raise ValueError(
            "source constants changed; update the audited matrix reconstruction: "
            f"{actual_constants!r}"
        )

    target_object = {
        "diagonal": [
            [n, _fraction_pair(diagonal[n][0]), _fraction_pair(diagonal[n][1])]
            for n in range(N)
        ],
        "sine": [
            [n, _fraction_pair(sine[n][0]), _fraction_pair(sine[n][1])]
            for n in range(1, N)
        ],
    }
    targets_sha256 = _sha256(_canonical_json(target_object))
    if targets_sha256 != EXPECTED_TARGETS_SHA256:
        raise ValueError(
            "canonical source-target digest drifted: "
            f"expected {EXPECTED_TARGETS_SHA256}, got {targets_sha256}"
        )

    return {
        "sine": sine,
        "diagonal": diagonal,
        "inv_pi": inv_pi,
        "inv_sqrt_two": inv_sqrt_two,
        "correction": correction,
        "targets_sha256": targets_sha256,
    }


def base_interval_entry(data: dict[str, object], n: int, m: int) -> Interval:
    sine: dict[int, Interval] = data["sine"]  # type: ignore[assignment]
    diagonal: dict[int, Interval] = data["diagonal"]  # type: ignore[assignment]
    inv_pi: Interval = data["inv_pi"]  # type: ignore[assignment]
    inv_sqrt_two: Interval = data["inv_sqrt_two"]  # type: ignore[assignment]

    if n == 0:
        if m == 0:
            return diagonal[0]
        coefficient = pure(F((-1) ** (m + 1), m))
        return interval_mul(
            interval_mul(interval_mul(coefficient, inv_pi), inv_sqrt_two),
            sine[m],
        )
    if m == 0:
        return base_interval_entry(data, 0, n)
    if n == m:
        correction = interval_mul(
            interval_mul(pure(F(1, 2 * n)), inv_pi), sine[n]
        )
        return interval_sub(diagonal[n], correction)

    coefficient = pure(F((-1) ** (n + m), n * n - m * m))
    difference = interval_sub(
        interval_mul(pure(F(m)), sine[m]),
        interval_mul(pure(F(n)), sine[n]),
    )
    return interval_mul(interval_mul(coefficient, inv_pi), difference)


def build_interval_matrix(
    data: dict[str, object],
) -> tuple[list[list[Interval]], list[list[F]], list[list[F]], F, tuple[int, int]]:
    correction: F = data["correction"]  # type: ignore[assignment]
    intervals: list[list[Interval]] = [[(F(0), F(0)) for _ in range(N)] for _ in range(N)]
    centers: list[list[F]] = [[F(0) for _ in range(N)] for _ in range(N)]
    radii: list[list[F]] = [[F(0) for _ in range(N)] for _ in range(N)]
    max_radius = F(-1)
    max_location = (-1, -1)

    for i in range(N):
        for j in range(i, N):
            lo, hi = base_interval_entry(data, i, j)
            lo -= correction
            hi += correction
            if lo > hi:
                raise ValueError(f"invalid reconstructed entry ({i}, {j})")
            center = (lo + hi) / 2
            radius = (hi - lo) / 2
            intervals[i][j] = intervals[j][i] = (lo, hi)
            centers[i][j] = centers[j][i] = center
            radii[i][j] = radii[j][i] = radius
            if radius > max_radius:
                max_radius = radius
                max_location = (i, j)

    if max_radius != EXPECTED_MAX_HALF_WIDTH:
        raise ValueError(
            "maximum half-width drifted: "
            f"expected {EXPECTED_MAX_HALF_WIDTH}, got {max_radius}"
        )
    if max_location != EXPECTED_MAX_HALF_WIDTH_LOCATION:
        raise ValueError(
            "maximum half-width location drifted: "
            f"expected {EXPECTED_MAX_HALF_WIDTH_LOCATION}, got {max_location}"
        )
    if max_radius > UNIFORM_HALF_WIDTH:
        raise ValueError("the advertised uniform half-width is too small")
    return intervals, centers, radii, max_radius, max_location


def discover_preconditioner(
    centers: list[list[F]],
) -> tuple[list[list[tuple[int, int]]], list[SparseRow]]:
    center_float = np.array(
        [[float(q) for q in row] for row in centers], dtype=np.float64
    )
    cholesky = np.linalg.cholesky(center_float)
    inverse_cholesky = np.linalg.solve(
        cholesky, np.eye(N, dtype=np.float64)
    )

    grid_rows: list[list[tuple[int, int]]] = []
    rational_rows: list[SparseRow] = []
    for i in range(N):
        grid_row: list[tuple[int, int]] = []
        rational_row: SparseRow = {}
        for j in range(i + 1):
            value = float(inverse_cholesky[i, j])
            if not math.isfinite(value):
                raise ValueError("non-finite inverse-Cholesky entry")
            if abs(value) >= P_THRESHOLD:
                grid_value = int(np.rint(value * P_DENOMINATOR))
                if grid_value != 0:
                    grid_row.append((j, grid_value))
                    rational_row[j] = F(grid_value, P_DENOMINATOR)
        grid_rows.append(grid_row)
        rational_rows.append(rational_row)
    return grid_rows, rational_rows


def exact_congruence(
    rows: list[SparseRow], centers: list[list[F]]
) -> list[list[F]]:
    result = [[F(0) for _ in range(N)] for _ in range(N)]
    for i in range(N):
        for j in range(i, N):
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
    congruence: list[list[F]], row_l1: list[F]
) -> list[int]:
    b = np.array(
        [[float(q) for q in row] for row in congruence], dtype=np.float64
    )
    a = np.array([float(q) for q in row_l1], dtype=np.float64)
    epsilon = float(UNIFORM_HALF_WIDTH)
    diagonal_lower = np.diag(b) - epsilon * a * a
    if np.min(diagonal_lower) <= 0:
        raise ValueError("discovered transformed diagonal lower bound is nonpositive")
    comparison = np.abs(b) + epsilon * np.outer(a, a)
    np.fill_diagonal(comparison, 0.0)
    comparison /= diagonal_lower[:, None]

    eigenvalues, eigenvectors = np.linalg.eig(comparison)
    index = int(np.argmax(np.abs(eigenvalues)))
    if abs(eigenvalues[index].imag) > 1e-10:
        raise ValueError("dominant comparison eigenvalue is unexpectedly non-real")
    vector = np.abs(np.real(eigenvectors[:, index]))
    if np.min(vector) <= 0 or not np.all(np.isfinite(vector)):
        raise ValueError("Perron discovery vector is not strictly positive and finite")
    vector /= np.min(vector)
    return [
        max(1, int(np.rint(value * WEIGHT_DENOMINATOR))) for value in vector
    ]


def build_payload(
    targets_sha256: str,
    grid_rows: list[list[tuple[int, int]]],
    weight_grid: list[int],
) -> dict[str, object]:
    return {
        "dimension": N,
        "epsilon": _fraction_pair(UNIFORM_HALF_WIDTH),
        "p_denominator": P_DENOMINATOR,
        "p_rows": grid_rows,
        "schema": "yoshida-even-congruence-v1",
        "source": TARGET_SOURCE.as_posix(),
        "source_targets_sha256": targets_sha256,
        "weight_denominator": WEIGHT_DENOMINATOR,
        "weights": weight_grid,
    }


def audit(repo_root: Path) -> dict[str, object]:
    data = read_source_data(repo_root)
    intervals, centers, _radii, max_radius, max_location = build_interval_matrix(data)
    grid_rows, rows = discover_preconditioner(centers)
    if len(grid_rows) != N or len(rows) != N:
        raise ValueError(
            f"preconditioner row count drifted: expected {N}, "
            f"got grid={len(grid_rows)}, rational={len(rows)}"
        )
    duplicate_columns = any(
        len({column for column, _ in row}) != len(row) for row in grid_rows
    )
    if duplicate_columns:
        raise ValueError("a sparse row contains duplicate columns")

    nnz = sum(len(row) for row in rows)
    support_sizes = [len(row) for row in rows]
    triangular = all(j <= i for i, row in enumerate(rows) for j in row)
    positive_diagonal = all(rows[i].get(i, F(0)) > 0 for i in range(N))
    if nnz != EXPECTED_NNZ:
        raise ValueError(f"preconditioner nnz drifted: expected {EXPECTED_NNZ}, got {nnz}")
    if min(support_sizes) != EXPECTED_SUPPORT_MIN:
        raise ValueError("minimum sparse-row support drifted")
    if max(support_sizes) != EXPECTED_SUPPORT_MAX:
        raise ValueError("maximum sparse-row support drifted")
    if not triangular or not positive_diagonal:
        raise ValueError("preconditioner is not lower triangular with positive diagonal")

    congruence = exact_congruence(rows, centers)
    row_l1 = [sum((abs(q) for q in row.values()), F(0)) for row in rows]
    weight_grid = discover_weights(congruence, row_l1)
    if len(weight_grid) != N:
        raise ValueError(
            f"weight count drifted: expected {N}, got {len(weight_grid)}"
        )
    weights = [F(q, WEIGHT_DENOMINATOR) for q in weight_grid]
    if min(weight_grid) <= 0:
        raise ValueError("a rational weight is nonpositive")

    margins: list[F] = []
    ratios: list[float] = []
    diagonal_lowers: list[F] = []
    for i in range(N):
        diagonal_lower = (
            congruence[i][i]
            - UNIFORM_HALF_WIDTH * row_l1[i] * row_l1[i]
        )
        off_diagonal = sum(
            (
                (
                    abs(congruence[i][j])
                    + UNIFORM_HALF_WIDTH * row_l1[i] * row_l1[j]
                )
                * weights[j]
                for j in range(N)
                if j != i
            ),
            F(0),
        )
        lhs = diagonal_lower * weights[i]
        diagonal_lowers.append(diagonal_lower)
        margins.append(lhs - off_diagonal)
        ratios.append(float(off_diagonal / lhs))
    if any(margin <= 0 for margin in margins):
        bad = [i for i, margin in enumerate(margins) if margin <= 0]
        raise ValueError(f"exact weighted-dominance audit failed in rows {bad}")

    raw_margins = [
        intervals[i][i][0]
        - sum(
            (
                max(abs(intervals[i][j][0]), abs(intervals[i][j][1]))
                for j in range(N)
                if j != i
            ),
            F(0),
        )
        for i in range(N)
    ]

    block_budgets: list[list[F]] = []
    rounded_margins: list[F] = []
    for i, row in enumerate(rows):
        block_count = len(row)
        if block_count <= 0:
            raise ValueError(f"sparse row {i} has no residue block")
        budgets: list[F] = []
        for block in range(block_count):
            contribution = sum(
                (
                    (
                        abs(congruence[i][j])
                        + UNIFORM_HALF_WIDTH * row_l1[i] * row_l1[j]
                    )
                    * weights[j]
                    for j in range(N)
                    if j != i and j % block_count == block
                ),
                F(0),
            )
            budget = _round_up_fraction(
                contribution, BLOCK_BUDGET_DENOMINATOR
            )
            if contribution > budget:
                raise ValueError(
                    f"rounded block budget is unsound at ({i}, {block})"
                )
            budgets.append(budget)
        rounded_margin = diagonal_lowers[i] * weights[i] - sum(budgets, F(0))
        if rounded_margin <= 0:
            raise ValueError(f"rounded block budgets fail in row {i}")
        block_budgets.append(budgets)
        rounded_margins.append(rounded_margin)

    payload = build_payload(
        data["targets_sha256"], grid_rows, weight_grid  # type: ignore[arg-type]
    )
    canonical_payload = _canonical_json(payload)
    payload_sha256 = _sha256(canonical_payload)
    if payload_sha256 != EXPECTED_PAYLOAD_SHA256:
        raise ValueError(
            "canonical certificate payload drifted: "
            f"expected {EXPECTED_PAYLOAD_SHA256}, got {payload_sha256}"
        )

    minimum_margin_row = min(range(N), key=margins.__getitem__)
    maximum_ratio_row = max(range(N), key=ratios.__getitem__)
    return {
        "canonical_payload": canonical_payload,
        "block_budgets": block_budgets,
        "centers": centers,
        "congruence": congruence,
        "diagonal_lowers": diagonal_lowers,
        "duplicate_columns": duplicate_columns,
        "grid_rows": grid_rows,
        "margins": margins,
        "max_half_width": max_radius,
        "max_half_width_location": max_location,
        "max_ratio": ratios[maximum_ratio_row],
        "max_ratio_row": maximum_ratio_row,
        "min_margin": margins[minimum_margin_row],
        "min_margin_row": minimum_margin_row,
        "nnz": nnz,
        "payload": payload,
        "payload_sha256": payload_sha256,
        "positive_diagonal": positive_diagonal,
        "raw_bad_rows": [i for i, margin in enumerate(raw_margins) if margin <= 0],
        "raw_pass_count": sum(margin > 0 for margin in raw_margins),
        "rounded_margins": rounded_margins,
        "row_count": len(grid_rows),
        "row_l1": row_l1,
        "support_max": max(support_sizes),
        "support_min": min(support_sizes),
        "targets_sha256": data["targets_sha256"],
        "triangular": triangular,
        "weight_grid": weight_grid,
    }


def print_report(result: dict[str, object], stream: TextIO) -> None:
    max_half_width: F = result["max_half_width"]  # type: ignore[assignment]
    min_margin: F = result["min_margin"]  # type: ignore[assignment]
    diagonal_lowers: list[F] = result["diagonal_lowers"]  # type: ignore[assignment]
    weight_grid: list[int] = result["weight_grid"]  # type: ignore[assignment]
    row_l1: list[F] = result["row_l1"]  # type: ignore[assignment]
    block_budgets: list[list[F]] = result["block_budgets"]  # type: ignore[assignment]
    rounded_margins: list[F] = result["rounded_margins"]  # type: ignore[assignment]
    print("Yoshida even sparse-congruence certificate: PASS", file=stream)
    print(
        f"discovery_seed={DISCOVERY_SEED} (no PRNG; deterministic LAPACK discovery)",
        file=stream,
    )
    print(
        "rounding=P(abs(x)>=0.005)->rint(x*10000)/10000; "
        "weights=Perron/min->rint(x*1000)/1000; ties-to-even",
        file=stream,
    )
    print(f"source_targets_sha256={result['targets_sha256']}", file=stream)
    print(f"canonical_payload_sha256={result['payload_sha256']}", file=stream)
    print(
        f"max_interval_width={_fraction_text(2 * max_half_width)} "
        f"(~{float(2 * max_half_width):.18g})",
        file=stream,
    )
    print(
        f"max_half_width={_fraction_text(max_half_width)} "
        f"(~{float(max_half_width):.18g}) "
        f"at={result['max_half_width_location']}",
        file=stream,
    )
    print(
        f"uniform_half_width={_fraction_text(UNIFORM_HALF_WIDTH)} "
        f"slack={_fraction_text(UNIFORM_HALF_WIDTH - max_half_width)}",
        file=stream,
    )
    print(
        f"P_rows={result['row_count']} P_nnz={result['nnz']} "
        f"support={result['support_min']}..{result['support_max']} "
        f"duplicate_columns={result['duplicate_columns']} "
        f"lower_triangular={result['triangular']} "
        f"positive_diagonal={result['positive_diagonal']}",
        file=stream,
    )
    print(
        f"P_row_l1={min(row_l1):.6g}..{max(row_l1):.6g}",
        file=stream,
    )
    print(
        f"weights_grid={min(weight_grid)}..{max(weight_grid)} denominator={WEIGHT_DENOMINATOR}",
        file=stream,
    )
    print(
        f"transformed_diagonal_lower_min={_fraction_text(min(diagonal_lowers))} "
        f"(~{float(min(diagonal_lowers)):.18g})",
        file=stream,
    )
    print(
        f"min_exact_weighted_margin_row={result['min_margin_row']} "
        f"margin={_fraction_text(min_margin)} (~{float(min_margin):.18g})",
        file=stream,
    )
    min_rounded_row = min(range(N), key=rounded_margins.__getitem__)
    print(
        f"dominance_residue_blocks={sum(map(len, block_budgets))} "
        f"budget_denominator={BLOCK_BUDGET_DENOMINATOR} "
        f"min_rounded_margin_row={min_rounded_row} "
        f"margin={_fraction_text(rounded_margins[min_rounded_row])}",
        file=stream,
    )
    print(
        f"max_offdiag_to_diag_ratio_row={result['max_ratio_row']} "
        f"ratio~{result['max_ratio']:.18g}",
        file=stream,
    )
    print(
        f"raw_interval_gershgorin_pass={result['raw_pass_count']}/{N} "
        f"bad_rows={result['raw_bad_rows']}",
        file=stream,
    )


def _lean_fraction(numerator: int, denominator: int) -> str:
    return f"(({numerator} : ℚ) / {denominator})"


def _lean_entry_term(column: int, numerator: int) -> str:
    return (
        f"(({column} : YoshidaEvenIndex), "
        f"{_lean_fraction(numerator, P_DENOMINATOR)})"
    )


def emit_lean(result: dict[str, object], stream: TextIO) -> None:
    grid_rows: list[list[tuple[int, int]]] = result["grid_rows"]  # type: ignore[assignment]
    weight_grid: list[int] = result["weight_grid"]  # type: ignore[assignment]
    min_margin: F = result["min_margin"]  # type: ignore[assignment]
    max_half_width: F = result["max_half_width"]  # type: ignore[assignment]

    print("/-", file=stream)
    print("Generated by scripts/generate_yoshida_even_sparse_congruence.py", file=stream)
    print("Deterministic discovery seed: 0 (no PRNG)", file=stream)
    print(f"Source targets SHA-256: {result['targets_sha256']}", file=stream)
    print(f"Canonical payload schema: {result['payload']['schema']}", file=stream)  # type: ignore[index]
    print(f"Canonical payload SHA-256: {result['payload_sha256']}", file=stream)
    print(
        "Exact maximum half-width: "
        f"{_fraction_text(max_half_width)} at {result['max_half_width_location']}",
        file=stream,
    )
    print(
        f"Sparse rows: {result['row_count']}; nonzeros: {result['nnz']}; "
        f"support: {result['support_min']}..{result['support_max']}; "
        f"duplicate columns: {result['duplicate_columns']}",
        file=stream,
    )
    print(
        f"Lower triangular: {result['triangular']}; "
        f"positive diagonal: {result['positive_diagonal']}",
        file=stream,
    )
    print(f"Minimum exact weighted margin row: {result['min_margin_row']}", file=stream)
    print(f"Minimum exact weighted margin numerator: {min_margin.numerator}", file=stream)
    print(f"Minimum exact weighted margin denominator: {min_margin.denominator}", file=stream)
    print("Rows use exact numerator/10000 coefficients; weights use numerator/1000.", file=stream)
    print("-/", file=stream)
    print("", file=stream)
    print("import ArithmeticHodge.Analysis.SparseEntriesCertificate", file=stream)
    print("import ArithmeticHodge.Analysis.YoshidaEvenMomentTargets", file=stream)
    print("", file=stream)
    print("set_option autoImplicit false", file=stream)
    print("", file=stream)
    print("open Matrix", file=stream)
    print("open scoped BigOperators", file=stream)
    print("", file=stream)
    print("namespace ArithmeticHodge.Analysis.YoshidaEvenSparseCongruenceData", file=stream)
    print("", file=stream)
    print("open RatInterval", file=stream)
    print("open SparseCongruenceCertificate", file=stream)
    print("open SparseEntriesCertificate", file=stream)
    print("open YoshidaEvenIntervalCertificate", file=stream)
    print("open YoshidaEvenMomentTargets", file=stream)
    print("", file=stream)
    print("def evenSparseEpsilon : ℚ := 51 / 100000", file=stream)
    print("", file=stream)
    print("def evenTargetInterval :", file=stream)
    print("    Matrix YoshidaEvenIndex YoshidaEvenIndex RatInterval :=", file=stream)
    print("  inflatedEvenMomentIntervalGram evenCorrectionRadius", file=stream)
    print("    yoshidaEvenSineTargets yoshidaEvenDiagonalTargets", file=stream)
    print("", file=stream)
    print("def evenTargetCenter : Matrix YoshidaEvenIndex YoshidaEvenIndex ℚ :=", file=stream)
    print("  fun i j ↦", file=stream)
    print("    ((evenTargetInterval i j).lower + (evenTargetInterval i j).upper) / 2", file=stream)
    print("", file=stream)
    print("def evenSparseEntries", file=stream)
    print("    (i : YoshidaEvenIndex) : SparseEntries YoshidaEvenIndex :=", file=stream)
    print("  match i.val with", file=stream)
    for row_index, row in enumerate(grid_rows):
        print(f"  | {row_index} => [", file=stream)
        for term_index, (column, numerator) in enumerate(row):
            suffix = "," if term_index + 1 < len(row) else ""
            print(f"      {_lean_entry_term(column, numerator)}{suffix}", file=stream)
        print("    ]", file=stream)
    print("  | _ => []", file=stream)
    print("", file=stream)
    print("def evenSparseRows (i : YoshidaEvenIndex) : SparseRow YoshidaEvenIndex :=", file=stream)
    print("  rowOfEntries (evenSparseEntries i)", file=stream)
    print("", file=stream)
    print("def evenSparseWeights (i : YoshidaEvenIndex) : ℚ :=", file=stream)
    print("  match i.val with", file=stream)
    for row_index, numerator in enumerate(weight_grid):
        print(f"  | {row_index} => {_lean_fraction(numerator, WEIGHT_DENOMINATOR)}", file=stream)
    print("  | _ => 1", file=stream)
    print("", file=stream)
    print("def evenSparseRowL1 (i : YoshidaEvenIndex) : ℚ :=", file=stream)
    print("  entriesL1 (evenSparseEntries i)", file=stream)
    print("", file=stream)
    print("def evenSparseCenterCongruenceEntries", file=stream)
    print("    (i j : YoshidaEvenIndex) : ℚ :=", file=stream)
    print("  entriesCongruence (evenSparseEntries i)", file=stream)
    print("    (evenSparseEntries j) evenTargetCenter", file=stream)
    print("", file=stream)
    print("def evenSparseCenterCongruence (i j : YoshidaEvenIndex) : ℚ :=", file=stream)
    print("  sparseCongruenceEntry evenSparseRows evenTargetCenter i j", file=stream)
    print("", file=stream)
    print("end ArithmeticHodge.Analysis.YoshidaEvenSparseCongruenceData", file=stream)


def emit_dominance_lean(result: dict[str, object], stream: TextIO) -> None:
    block_budgets: list[list[F]] = result["block_budgets"]  # type: ignore[assignment]
    rounded_margins: list[F] = result["rounded_margins"]  # type: ignore[assignment]
    min_rounded_row = min(range(N), key=rounded_margins.__getitem__)

    print("/-", file=stream)
    print("Generated by scripts/generate_yoshida_even_sparse_congruence.py", file=stream)
    print(f"Canonical payload SHA-256: {result['payload_sha256']}", file=stream)
    print(f"Residue blocks: {sum(map(len, block_budgets))}", file=stream)
    print(f"Block budget denominator: {BLOCK_BUDGET_DENOMINATOR}", file=stream)
    print(f"Minimum rounded margin row: {min_rounded_row}", file=stream)
    print(
        "Minimum rounded margin: "
        f"{_fraction_text(rounded_margins[min_rounded_row])}",
        file=stream,
    )
    print("-/", file=stream)
    print("", file=stream)
    print(
        "import ArithmeticHodge.Analysis."
        "YoshidaEvenSparseCongruenceDominanceCore",
        file=stream,
    )
    print("", file=stream)
    print("set_option autoImplicit false", file=stream)
    print("", file=stream)
    print(
        "namespace ArithmeticHodge.Analysis."
        "YoshidaEvenSparseCongruenceChecks",
        file=stream,
    )
    print("", file=stream)
    print("def evenSparseDominanceBlockBudgets", file=stream)
    print("    (i : YoshidaEvenIndex) : List ℚ :=", file=stream)
    print("  match i.val with", file=stream)
    for row, budgets in enumerate(block_budgets):
        rendered = ", ".join(
            _lean_fraction(q.numerator, q.denominator) for q in budgets
        )
        print(f"  | {row} => [{rendered}]", file=stream)
    print("  | _ => []", file=stream)
    print("", file=stream)
    print("def evenSparseDominanceBlockBudget", file=stream)
    print("    (i : YoshidaEvenIndex) (b : ℕ) : ℚ :=", file=stream)
    print("  (evenSparseDominanceBlockBudgets i).getD b 0", file=stream)
    print("", file=stream)
    print(
        "end ArithmeticHodge.Analysis."
        "YoshidaEvenSparseCongruenceChecks",
        file=stream,
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=Path(__file__).resolve().parents[1],
        help="Arithmetic-Hodge repository root (default: inferred from script path)",
    )
    output = parser.add_mutually_exclusive_group()
    output.add_argument(
        "--audit-only",
        action="store_true",
        help="run the exact audit and print its report (the default)",
    )
    output.add_argument(
        "--emit-lean",
        action="store_true",
        help="audit, then emit the complete Phase-A Lean data module to stdout",
    )
    output.add_argument(
        "--emit-dominance-lean",
        action="store_true",
        help="audit, then emit the rounded residue-block budget module",
    )
    output.add_argument(
        "--emit-canonical-json",
        action="store_true",
        help="audit, then emit the canonical hashed JSON payload to stdout",
    )
    args = parser.parse_args()

    result = audit(args.repo_root.resolve())
    if args.emit_lean:
        print_report(result, sys.stderr)
        emit_lean(result, sys.stdout)
    elif args.emit_dominance_lean:
        print_report(result, sys.stderr)
        emit_dominance_lean(result, sys.stdout)
    elif args.emit_canonical_json:
        print_report(result, sys.stderr)
        sys.stdout.buffer.write(result["canonical_payload"])  # type: ignore[arg-type]
    else:
        print_report(result, sys.stdout)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
