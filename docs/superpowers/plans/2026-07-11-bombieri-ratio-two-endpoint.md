# Bombieri Ratio-Two Endpoint Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` to implement and independently
> review this plan.

**Goal:** Extend the source-faithful Bombieri quadratic support reduction from
`b / a < 2` to the closed endpoint `b / a ≤ 2`.

**Architecture:** Prove directly that the multiplicative autocorrelation
vanishes at `2` and `1/2`: at either endpoint, simultaneous nonvanishing of
the two factors confines the integration variable to a singleton, which is
null for the restricted volume measure.  Then handle the von Mangoldt series
term by term, separating the `n = 2` endpoint from `n > 2`, and expose the
closed-window polar/archimedean and critical-line formulas needed for
Yoshida's ratio-two positivity theorem.

**Tech stack:** Lean 4, Mathlib Bochner integration and almost-everywhere
filters, existing multiplicative Bombieri support and critical-line APIs.

## Global constraints

- No `sorry`, `admit`, custom `axiom`, unsafe declaration, or
  theorem-equivalent typeclass assumption.
- Do not use RH, Bombieri all-test positivity, zero-side positivity, the
  legacy Weil model, Hodge assumptions, or adelic class-space assumptions.
- Production must compile with `-DwarningAsError=true`, pass the full build,
  and pass strict production proof and naming scans.
- Preserve all 159 legacy root-level Lean research artifacts; they are
  inventoried on `main` and archived at
  `refs/archive/legacy-lean-2026-07-11`.

---

### Task 1: Closed ratio-two prime elimination and local form

**Files:**

- Create:
  `ArithmeticHodge/Analysis/MultiplicativeWeilQuadraticEndpoint.lean`
- Modify: `ArithmeticHodge.lean`
- Test: `RatioTwoEndpointScratch.lean` (temporary; delete before commit)

**Imports:**

```lean
import ArithmeticHodge.Analysis.MultiplicativeWeilQuadraticCriticalLine
```

**Public interfaces:**

```lean
theorem bombieriQuadraticTest_apply_two_eq_zero_of_support_ratio_le_two
    (g : BombieriTest) {a b : ℝ} (ha : 0 < a)
    (hsupport : tsupport g ⊆ Set.Icc a b) (hratio : b / a ≤ 2) :
    bombieriQuadraticTest g 2 = 0

theorem bombieriQuadraticTest_apply_half_eq_zero_of_support_ratio_le_two
    (g : BombieriTest) {a b : ℝ} (ha : 0 < a)
    (hsupport : tsupport g ⊆ Set.Icc a b) (hratio : b / a ≤ 2) :
    bombieriQuadraticTest g (1 / 2 : ℝ) = 0

theorem primeSum_bombieriQuadraticTest_eq_zero_of_support_ratio_le_two
    (g : BombieriTest) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b) (hratio : b / a ≤ 2) :
    primeSum (bombieriQuadraticTest g) = 0

theorem bombieriFunctional_quadratic_eq_polar_add_arch_of_support_ratio_le_two
    (g : BombieriTest) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b) (hratio : b / a ≤ 2) :
    bombieriFunctional (bombieriQuadraticTest g) =
      mellin (bombieriQuadraticTest g : ℝ → ℂ) 1 +
        mellin (bombieriQuadraticTest g : ℝ → ℂ) 0 +
          bombieriArchTerm (bombieriQuadraticTest g)

theorem bombieriFunctional_quadratic_eq_local_critical_form_le_two
    (g : BombieriTest) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b) (hratio : b / a ≤ 2) :
    bombieriFunctional (bombieriQuadraticTest g) =
      ((2 * (mellin (g : ℝ → ℂ) 1 *
        starRingEnd ℂ (mellin (g : ℝ → ℂ) 0)).re : ℝ) : ℂ) +
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ,
          (((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * Complex.I)).re -
            Real.log Real.pi : ℝ) : ℂ) *
              (Complex.normSq
                (mellin (g : ℝ → ℂ)
                  ((1 / 2 : ℝ) + v * Complex.I)) : ℂ)
```

- [ ] **Step 1: Record the RED declarations**

Add the exact five declarations to `RatioTwoEndpointScratch.lean` with
intentionally unproved bodies and run strict Lean.  Imports and interfaces
must resolve; only the proof goals may fail.

- [ ] **Step 2: Prove endpoint autocorrelation vanishing**

Unfold `bombieriQuadraticTest_apply` and `autocorrelation`.  At `x = 2`, use

```lean
(countable_singleton a).ae_notMem (volume.restrict (Set.Ioi 0))
```

and show simultaneous nonvanishing of `g y` and `g (2*y)` forces `y = a`.
At `x = 1/2`, the analogous singleton is `{2*a}`.  Use `subset_tsupport`,
the support bounds, and `(div_le_iff₀ ha).mp hratio`.

- [ ] **Step 3: Eliminate the full prime series**

Unfold `primeSum` and prove every `vonMangoldtPrimeSummand` is zero.  Handle
`n = 2` with the endpoint theorems.  For `n > 2`, use
`bombieriQuadraticTest_tsupport_subset_Icc`; do the same for `n⁻¹` before
rewriting the transpose.  Do not try to strengthen the topological support
to the open interval: endpoint pointwise vanishing does not imply that.

- [ ] **Step 4: Derive both closed-window functional formulas**

Rewrite `bombieriFunctional_apply` with the new prime theorem, then reuse
`bombieriQuadratic_polar_eq_two_re` and
`bombieriArchTerm_quadratic_eq_critical_normSq_integral`.

- [ ] **Step 5: Promote, verify, review, and commit**

```bash
lake env lean -DwarningAsError=true \
  ArithmeticHodge/Analysis/MultiplicativeWeilQuadraticEndpoint.lean
lake build ArithmeticHodge
if rg -n --glob '*.lean' \
  '^\s*(private\s+)?axiom\b|^\s*sorry\b|\bby\s+sorry\b' ArithmeticHodge; then
  exit 1
fi
if rg -n '_scratch|Scratch' ArithmeticHodge --glob '*.lean'; then
  exit 1
fi
git diff --check
git add ArithmeticHodge.lean \
  ArithmeticHodge/Analysis/MultiplicativeWeilQuadraticEndpoint.lean
git commit -m "extend Bombieri prime elimination to ratio two"
```

Expected: all commands exit zero, the temporary scratch file is absent, and
a fresh reviewer finds no Critical or Important issue before the task is
marked complete.
