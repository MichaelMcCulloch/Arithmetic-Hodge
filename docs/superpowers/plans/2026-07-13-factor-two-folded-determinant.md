# Factor-Two Folded Determinant Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the abstract factor-two determinant by an exact structural inequality between the folded physical diagonal and the real/imaginary parity channels.

**Architecture:** Add one merge module above `YoshidaFactorTwoDiagonalPhysical` and `MultiplicativeWeilTwoBumpDeterminant`. It introduces no duplicate coordinate definitions: four public rewrite theorems expose the exact norm-square, determinant gap, universal nonnegativity equivalence, and strict-negative equivalence.

**Tech Stack:** Lean 4, Mathlib, Lake, the root `Justfile`, Git.

## Global Constraints

- Every Lean- or Lake-related command must run through a root `Justfile` recipe.
- The complete transitive proof closure must be structural; finite tables, mode enumeration, generated certificates, target enclosures, pivot replay, `decide +kernel`, `native_decide`, `unsafe`, `sorry`, `admit`, and custom axioms are forbidden.
- Computation may select or kill a candidate route but may not prove a terminal-path lemma.
- Never touch, stage, or import any of the 159 protected legacy artifacts or 24 fallback modules.
- Run no concurrent high-memory Lean workloads.

---

### Task 1: Exact folded determinant merge node

**Files:**
- Create: `ArithmeticHodge/Analysis/YoshidaFactorTwoParityDeterminant.lean`
- Modify: `ArithmeticHodge.lean`
- Modify: `docs/research/rh-terminal-distance-audit-2026-07-11.md`
- Create: `docs/superpowers/plans/2026-07-13-factor-two-folded-determinant.md`

**Interfaces:**
- Consumes: `factorTwoGlobalCrossSymbol_re_eq_parity`, `factorTwoGlobalCrossSymbol_im_eq_parity`, `bombieriFunctional_quadratic_re_eq_factorTwoDiagonalPhysical_with_endpoint`, `bombieriFunctional_twoBump_nonneg_iff`, and `exists_bombieriFunctional_twoBump_neg_iff`.
- Produces: `factorTwoGlobalCrossSymbol_normSq_eq_foldedParity`, `bombieriFactorTwoDeterminantGap_eq_foldedParity`, `bombieriFunctional_twoBump_nonneg_iff_foldedParity`, and `exists_bombieriFunctional_twoBump_neg_iff_foldedParity`.

- [x] **Step 1: Write and verify the failing interface probe**

Run through the guard:

```console
print -r -- 'import ArithmeticHodge.Analysis.YoshidaFactorTwoParityDeterminant' | just guarded lake env lean /dev/stdin
```

Expected: failure because the merge module does not yet exist.

- [x] **Step 2: Implement the exact norm-square and gap identities**

Create the module with these imports and namespace:

```lean
import ArithmeticHodge.Analysis.YoshidaFactorTwoDiagonalPhysical
import ArithmeticHodge.Analysis.MultiplicativeWeilTwoBumpDeterminant

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoParityDeterminant

noncomputable section

open MultiplicativeWeil
open YoshidaCriticalLogCorrelation
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoCrossDistribution
open YoshidaFactorTwoDiagonalGeometric
open YoshidaFactorTwoDiagonalPhysical
```

In every theorem, use proposition-local `let`s rather than new global aliases:

```lean
let D : ℝ :=
  (∫ s : ℝ in 0..factorTwoLogLength,
      factorTwoDiagonalPhysicalIntegrand g s) -
    (Real.log factorTwoLogLength + Real.eulerMascheroniConstant +
      Real.log 2 + Real.log Real.pi) * factorTwoSelfCorrelationRe g 0 -
    2 * (Real.log 2 / Real.sqrt 2) *
      factorTwoSelfCorrelationRe g factorTwoLogLength
let R : ℝ :=
  (∫ s : ℝ in 0..factorTwoLogLength,
      factorTwoSymmetricWeight s * (factorTwoSelfCorrelation g s).re) -
    (Real.log 2 / Real.sqrt 2) * (factorTwoSelfCorrelation g 0).re -
    (Real.log 3 / Real.sqrt 3) *
      (factorTwoSelfCorrelation g factorTwoPrimeShift).re
let I : ℝ :=
  (∫ s : ℝ in 0..factorTwoLogLength,
      factorTwoAntisymmetricWeight s * (factorTwoSelfCorrelation g s).im) -
    (Real.log 3 / Real.sqrt 3) *
      (factorTwoSelfCorrelation g factorTwoPrimeShift).im
```

State `factorTwoGlobalCrossSymbol_normSq_eq_foldedParity` as
`let R := ...; let I := ...; Complex.normSq (factorTwoGlobalCrossSymbol g) =
R ^ 2 + I ^ 2`. Repeat the complete `R` and `I` expressions above, then prove:

```lean
dsimp only
rw [Complex.normSq_apply,
  factorTwoGlobalCrossSymbol_re_eq_parity g ha hab hsupport hratio,
  factorTwoGlobalCrossSymbol_im_eq_parity g ha hab hsupport hratio]
```

State `bombieriFactorTwoDeterminantGap_eq_foldedParity` with left side

```lean
(bombieriFunctional (bombieriQuadraticTest g)).re ^ 2 -
  Complex.normSq (factorTwoGlobalCrossSymbol g)
```

and right side `D ^ 2 - R ^ 2 - I ^ 2`, repeating all three exact local lets above. Prove it by `dsimp only`, rewriting the endpoint-retaining diagonal and new norm-square theorems, and closing with `ring`.

- [x] **Step 3: Implement the positive and strict-negative equivalences**

State `bombieriFunctional_twoBump_nonneg_iff_foldedParity` with the existing universal two-bump proposition on the left and, after repeating the complete local lets above, the exact right side

```lean
R ^ 2 + I ^ 2 ≤ D ^ 2
```

Prove by `dsimp only` and rewriting with `bombieriFunctional_twoBump_nonneg_iff`, the new norm-square theorem, and the endpoint-retaining diagonal theorem.

State `exists_bombieriFunctional_twoBump_neg_iff_foldedParity` analogously, with exact right side `D ^ 2 < R ^ 2 + I ^ 2`, and rewrite with `exists_bombieriFunctional_twoBump_neg_iff` plus the same two exact identities. Close the namespace and section.

- [x] **Step 4: Run RED/GREEN, strict, axiom, closure, and umbrella gates**

Run sequentially:

```console
just strict ArithmeticHodge/Analysis/YoshidaFactorTwoParityDeterminant.lean
just strict ArithmeticHodge.lean
just build
```

Use guarded `/dev/stdin` `#print axioms` commands for all four public theorems. Require exactly `propext`, `Classical.choice`, and `Quot.sound`. Recursively audit imports and reject any missing, untracked, cyclic, certificate-style, enclosure, pivot, payload, evaluator, `sorry`, `admit`, custom-axiom, `unsafe`, `decide +kernel`, or `native_decide` dependency.

- [x] **Step 5: Record terminal distance, independently review, and commit**

Append the five-part audit entry. Recheck all 159 archived artifacts byte-for-byte and all 24 fallbacks without modifying them. Request independent review of signs, squares, inequality orientations, endpoint atom, and no-overclaim scope. Stage only the four named files, run `git diff --cached --check`, and commit:

```console
git commit -m "expose the folded factor-two determinant"
```
