# Signed Factor-Two Real-Channel Factorization Plan

**Status:** Complete.  The signed channels are now exact core-plus-full-
residual identities; the two resulting coercivity inequalities remain the
analytic make-or-break obligations.

**Goal:** Rewrite each exact signed real parity channel as its full structural
core plus one half of the complete positive diagonal residual energy of the
explicit test `g ± normalizedDilation 2 g`.

**Decisive obligation:** If this succeeds, it replaces the open bounds
`-D(g) ≤ R(g) ≤ D(g)` in Gate 3 by two exact core-versus-positive-residual
coercivity inequalities.  If either coercivity inequality fails strictly, the
same identities give an explicit negative Bombieri test with scalar `1` or
`-1`.

## Constraints

- All proofs and every transitive dependency must be structural.  No finite
  mode table, enclosure, generated certificate, evaluator, `native_decide`,
  `unsafe`, custom axiom, `sorry`, or protected fallback import is admissible.
- Retain the complete `tsum` of diagonal residuals.  The tests
  `g ± normalizedDilation 2 g` can have support ratio four, so their residual
  sum may not be replaced by a ratio-two physical resummation.
- Do not assume the false core-only norm bound.  The positive residual is
  load-bearing and must remain coupled to the indefinite core.
- Run all Lean/Lake workloads sequentially through the root `Justfile`.
- Preserve the 159 archived artifacts and 24 fallback modules byte-for-byte.

## Files

- Modify:
  `ArithmeticHodge/Analysis/YoshidaBombieriResidualPairing.lean`
- Create:
  `ArithmeticHodge/Analysis/YoshidaFactorTwoRealChannel.lean`
- Modify: `ArithmeticHodge.lean`
- Modify: `docs/research/rh-terminal-distance-audit-2026-07-11.md`
- Create/modify this plan.
- Modify `GOAL.md` only if its stable same-seed determinant directive has
  actually become stale.

## RED

Through `just guarded`, first require unknown-identifier failure for
`bombieriDiagonalResidual_add`, `bombieriDiagonalResidual_sub`, and the two
signed core-residual factorization names.  Separately require the expected
missing-object failure when importing the absent real-channel module.

The reproducible RED probes are:

```console
just guarded lake env lean .superpowers/sdd/real-channel-red-symbols.lean
just guarded lake env lean .superpowers/sdd/real-channel-red-import.lean
```

The first scratch file imports `YoshidaBombieriResidualPairing` and checks the
four absent names.  The second imports
`ArithmeticHodge.Analysis.YoshidaFactorTwoRealChannel`.  Both commands must
fail before the corresponding production edit.

## Task 1: residual Hermitian polarization

**Complete.**

Prove structurally, for every pair of Bombieri tests and every residual index,

```lean
bombieriDiagonalResidual (f + g) n =
  bombieriDiagonalResidual f n + bombieriDiagonalResidual g n +
    2 * (bombieriResidualCross f g n).re

bombieriDiagonalResidual (f - g) n =
  bombieriDiagonalResidual f n + bombieriDiagonalResidual g n -
    2 * (bombieriResidualCross f g n).re
```

Use the exact residual integral and Mellin linearity, or exported
sesquilinearity plus Hermitian swap.  Every integral split must use proved
integrability; no formal manipulation of a potentially nonintegrable Bochner
integral is allowed.

## Task 2: exact signed channel identities

**Complete.**

For a ratio-at-most-two seed `g`, write
`d = normalizedDilation 2 (by norm_num) g`.  Prove the following endpoints,
each with `{a b}`, `ha : 0 < a`, `hab : a ≤ b`,
`hsupport : tsupport g ⊆ Set.Icc a b`, and `hratio : b / a ≤ 2`:

```lean
factorTwoDiagonalCoordinate_sub_symmetric_eq_coreResidual :
  factorTwoDiagonalCoordinate g - factorTwoSymmetricCoordinate g =
  (bombieriCoreDiagonal g - (factorTwoCoreCrossSymbol g).re) +
    (1 / 2 : ℝ) * ∑' n, bombieriDiagonalResidual (g - d) n

factorTwoDiagonalCoordinate_add_symmetric_eq_coreResidual :
  factorTwoDiagonalCoordinate g + factorTwoSymmetricCoordinate g =
  (bombieriCoreDiagonal g + (factorTwoCoreCrossSymbol g).re) +
    (1 / 2 : ℝ) * ∑' n, bombieriDiagonalResidual (g + d) n
```

The proof must combine the existing exact diagonal/core decomposition, the
exact global-cross/core decomposition, normalized-dilation invariance of each
diagonal residual, the new polarization identities, and structural `tsum`
linearity.  Coefficient-conjugation fixedness is not needed for these
identities; it is only their canonical real-channel application.

## Task 3: export the actual make-or-break alternatives

**Complete.**

Export `factorTwoRealChannel_sub_nonneg_iff_coreResidual` and
`factorTwoRealChannel_add_nonneg_iff_coreResidual`, each with the same full
ratio-two support hypotheses as Task 2, and with right sides

```text
-(coreDiagonal(g) ± Re coreCross(g))
  ≤ (1/2) * sum residual(g ± D2g),
```

and exact strict-failure iff statements
`bombieriFunctional_twoBump_neg_one_neg_iff_coreResidual` and
`bombieriFunctional_twoBump_one_neg_iff_coreResidual`, again with the full
ratio-two support hypotheses, showing that the explicit scalar `c = -1` or
`c = 1` two-bump Bombieri functional is negative precisely when the
corresponding inequality is strictly reversed.  Parenthesize the right side
as `-(coreD ± Re coreX)`.  Derive these statements from the production
two-bump formula, not from an existential choice.

## Gates and publication

**Complete through local commit preparation.**  Focused and umbrella strict
checks, the 8,613-job full build, eight-endpoint axiom audit, recursive source
closure, and both protected inventories pass.  Independent focused and broad
mathematical reviews found no defect.

Run focused strict checks for both modified/new modules, umbrella strict, one
sequential full build, guarded `#print axioms` for every public endpoint, a
recursive tracked dependency-closure scan, and both protected inventories.
Request independent task and broad mathematical review.  Append the five-part
terminal-distance audit, stage only the five intended tracked files, commit
with message `factor the signed factor-two real channels`, and push `main`.

After this increment, attack the two core-versus-residual coercivity
inequalities directly through a positive real-space square or produce a
strict reverse.  Do not substitute the stronger already-falsified core norm
bound or an abstract copositivity theorem for this analytic obligation.
