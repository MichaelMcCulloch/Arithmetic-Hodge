# Factor-Two Parity Realification Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` or
> `superpowers:executing-plans` task by task.

**Goal:** Rewrite the exact same-seed factor-two determinant as two
conjugation-fixed diagonal channels coupled by one alternating real bilinear
channel, without adding a positivity hypothesis or a stronger surrogate
inequality.

**Architecture:** First add the missing coefficient-conjugation projections on
`BombieriTest`.  Next expose the sesquilinear algebra of the existing critical
cross-correlation.  Finally add one merge module defining exact `D`, `R`, `I`,
and mixed-coupling coordinates and proving the realified positive and
strict-negative determinant equivalences.

**Tech Stack:** Lean 4, Mathlib, Lake, the root `Justfile`, Git.

## Global constraints

- The terminal objective is a proof or falsification of RH.  Every theorem in
  the complete transitive terminal path must be structural; finite tables,
  mode exhaustion, generated certificates, target enclosures, pivot replay,
  evaluators, `decide +kernel`, `native_decide`, `unsafe`, `sorry`, `admit`,
  custom axioms, and opaque proof substitutes are forbidden.
- Computation may select or kill a route but may not establish any theorem in
  this plan.
- Every Lean- or Lake-related command must run through a root `Justfile`
  recipe.  Run no concurrent high-memory Lean workloads.
- Never edit, stage, import, or otherwise depend on the 159 protected legacy
  artifacts or 24 untracked fallback modules.
- Treat each task below as a coherent increment: RED/GREEN, audit, independent
  review, commit, and push it before editing files owned by the next task.
- Stage only explicitly named files.  Preserve all unrelated tracked and
  untracked worktree content.

---

### Task 1: Conjugation projections on Bombieri tests

**Status:** Complete and verified on 2026-07-13.

**Files:**

- Modify: `ArithmeticHodge/Analysis/MultiplicativeWeilQuadraticReality.lean`
- Modify: `docs/research/rh-terminal-distance-audit-2026-07-11.md`
- Create/modify:
  `docs/superpowers/plans/2026-07-13-factor-two-parity-realification.md`

**RED:** Through `just guarded lake env lean /dev/stdin`, import
`MultiplicativeWeilQuadraticReality` and `#check` the proposed
`bombieriRealPartTest` and `bombieriImagPartTest`.  Require unknown-identifier
failure before production edits.

**Implementation:** In namespace `MultiplicativeWeil`, add and prove:

```lean
@[simp] theorem bombieriConjugateTest_add ...
theorem bombieriConjugateTest_smul ...
@[simp] theorem bombieriConjugateTest_conjugateTest ...
theorem tsupport_bombieriConjugateTest ...

def bombieriRealPartTest (g : BombieriTest) : BombieriTest :=
  (1 / 2 : ℂ) • (g + bombieriConjugateTest g)

def bombieriImagPartTest (g : BombieriTest) : BombieriTest :=
  (Complex.I / 2) • (bombieriConjugateTest g - g)
```

Export pointwise real/imaginary formulas, conjugation fixedness,

```lean
bombieriRealPartTest g +
    Complex.I • bombieriImagPartTest g = g,
```

and both support inclusions into `tsupport g`.  Prove only by extensionality,
the pointwise conjugation definition, `Complex.ext`, topology-of-support
lemmas, and symbolic `simp`/`ring` normalization.

**GREEN and gates:**

```console
just strict ArithmeticHodge/Analysis/MultiplicativeWeilQuadraticReality.lean
just strict ArithmeticHodge.lean
just build
```

Audit every new public theorem with guarded `#print axioms`; require only
`propext`, `Classical.choice`, and `Quot.sound`.  Recursively scan its project
closure for forbidden proof mechanisms and protected imports.  Recheck the
159/24 protected inventories.  Append the five-part terminal-distance entry,
request independent review, stage only the three named files, and commit/push:

```console
git commit -m "add real and imaginary Bombieri projections"
git push origin main
```

---

### Task 2: Structural cross-correlation sesquilinearity

**Status:** Complete and verified on 2026-07-13.

**Files:**

- Modify: `ArithmeticHodge/Analysis/YoshidaBombieriCrossDistribution.lean`
- Modify: `docs/research/rh-terminal-distance-audit-2026-07-11.md`
- Modify:
  `docs/superpowers/plans/2026-07-13-factor-two-parity-realification.md`

**RED:** Through the root guard, import
`YoshidaBombieriCrossDistribution` and `#check` the proposed add-left,
add-right, smul-left, smul-right, and conjugate-swap names.  Require
unknown-identifier failure before editing.

**Implementation:** Make the existing critical cross-correlation integrability
and continuity theorems public.  Add a private convolution-existence helper,
then prove:

```lean
bombieriCriticalCrossCorrelation_add_left
bombieriCriticalCrossCorrelation_add_right
bombieriCriticalCrossCorrelation_smul_left
bombieriCriticalCrossCorrelation_smul_right
bombieriCriticalCrossCorrelation_neg_eq_star_swap
```

The left scalar must be conjugated; the right scalar must not be.  Addition
must use `ConvolutionExists.add_distrib`/`distrib_add`, scalar transport must
use `smul_convolution`/`convolution_smul`, and the swap theorem must generalize
the structural translation-and-conjugation proof of
`factorTwoSelfCorrelation_neg`.  No Fourier truncation or sampled identity is
admissible.

Run the same focused strict, umbrella strict, full-build, axiom, recursive
closure, and protected-inventory gates.  Append the five-part audit entry,
independently review conjugate-linearity and the swap orientation, stage only
the three named files, and commit/push:

```console
git commit -m "expose Bombieri cross-correlation sesquilinearity"
git push origin main
```

---

### Task 3: Exact realified factor-two determinant

**Status:** Complete and verified on 2026-07-13.

**Files:**

- Create:
  `ArithmeticHodge/Analysis/YoshidaFactorTwoParityRealification.lean`
- Modify: `ArithmeticHodge.lean`
- Modify: `GOAL.md` only if its current make-or-break statement has become
  stale rather than merely more explicit
- Modify: `docs/research/rh-terminal-distance-audit-2026-07-11.md`
- Modify:
  `docs/superpowers/plans/2026-07-13-factor-two-parity-realification.md`

**RED:** Import the absent realification module through the root guard and
require the missing-`.olean` failure.

**Implementation:** Define exact named coordinates
`factorTwoDiagonalCoordinate`, `factorTwoSymmetricCoordinate`,
`factorTwoAntisymmetricCoordinate`, and
`factorTwoMixedParityCoupling`.  Prove:

1. mixed correlations of conjugation-fixed tests have zero imaginary part;
2. the exact expansion
   `C_g = C_u + C_v + I * (C_uv - C_vu)` for the canonical real/imaginary
   parts `u` and `v`;
3. the corresponding real and imaginary correlation identities;
4. the unconditional identities `D(g) = D(u) + D(v)` and
   `I(g) = Ω(u,v)`, together with `R(g) = R(u) + R(v)` under the
   ratio-two support hypotheses that make the singular-endpoint symmetric
   integrands interval-integrable.  The support hypotheses are transported
   to `u` and `v`, and their integrability is derived from the exact folded
   complex integrand before interval-integral additivity is used;
5. exact universal-nonnegative and strict-negative equivalences with

```text
(R(u) + R(v))^2 + Ω(u,v)^2 <= (D(u) + D(v))^2
```

and its strict reverse.

Use only exact sesquilinearity, conjugation fixedness, interval-integral
linearity with proved integrability, and symbolic algebra.  Do not assume a
row contraction, operator completion, or any positivity beyond the already
proved ratio-two diagonal theorem consumed by the existing determinant.

Run focused/umbrella strict and one sequential full build.  Audit every public
endpoint and its recursive source closure, recheck protected inventories,
append the five-part terminal-distance entry, independently review all signs
and inequality directions, stage only the intended files, and commit/push:

```console
git commit -m "realify the folded factor-two determinant"
git push origin main
```

After Task 3, the next make-or-break theorem is no longer an abstract complex
determinant.  It is the exact real-channel bound together with the sharp
alternating-coupling margin.  Prove those structural inequalities or produce
a strict reverse and immediately export the negative Bombieri witness.
