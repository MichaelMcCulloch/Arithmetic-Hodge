# Bombieri--Yoshida Small-Support Positivity Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove that Bombieri's concrete quadratic functional is strictly positive on every nonzero test whose multiplicative support ratio is bounded by one universal constant `R₀ < 2`.

**Architecture:** Work entirely on the source-faithful multiplicative Bombieri path.  The existing support theorem kills the prime sum, and the existing critical-line theorem rewrites the remaining value as a polar cross term plus a real digamma-weighted Mellin norm-square integral.  New focused modules prove a coarse digamma lower bound, a compact-support Fourier uncertainty estimate, polar control, and the final constant selection.

**Tech Stack:** Lean 4, Mathlib Schwartz/Fourier/Mellin APIs, `lake`, `rg`, Bombieri's 2000 paper Section 12.

## Global Constraints

- No `sorry`, `admit`, custom `axiom`, or theorem-equivalent typeclass assumption.
- Do not use `RiemannHypothesis`, `BombieriNonnegativity`, zero-side positivity, `ArakelovIntersectionTheory`, `AdeleClassSpaceData`, or legacy `weilFunctionalFull`.
- Use the concrete `bombieriFunctional`, `bombieriQuadraticTest`, and bundled `BombieriTest` APIs.
- Every production module must compile with `lake env lean -DwarningAsError=true <file>`.
- Run the strict production proof and naming scans before every commit.
- Preserve all unrelated untracked scratch and audit files.

---

### Task 1: Coarse lower bound for the critical digamma kernel

**Files:**
- Create: `ArithmeticHodge/Analysis/MultiplicativeWeilDigammaLower.lean`
- Modify: `ArithmeticHodge.lean`
- Test: `DigammaLowerScratch.lean` (temporary, delete before commit)

**Interfaces:**
- Consumes: `digamma_quarter_vertical_re_eq`, `bombieriDigammaKernel`, harmonic-sum/log estimates from Mathlib.
- Produces:

```lean
theorem exists_bombieriCriticalGammaKernel_log_lower :
    ∃ C : ℝ, 0 < C ∧ ∀ v : ℝ,
      (1 / 2 : ℝ) * Real.log (max 1 |v|) - C ≤
        (Complex.digamma ((1 / 4 : ℝ) + (v / 2) * Complex.I)).re -
          Real.log Real.pi
```

- [ ] **Step 1: Write the failing declaration**

Create the theorem above in `DigammaLowerScratch.lean`, importing `ArithmeticHodge.Analysis.MultiplicativeWeilDigamma`, and run Lean before supplying a body.

- [ ] **Step 2: Verify the missing proof is the only failure**

Run:

```bash
lake env lean -DwarningAsError=true DigammaLowerScratch.lean
```

Expected: failure at `exists_bombieriCriticalGammaKernel_log_lower`, with all imports resolved.

- [ ] **Step 3: Prove finite kernel and harmonic estimates**

Add these helper declarations, keeping implementation-only lemmas private:

```lean
private theorem bombieriDigammaKernel_nonneg (k : ℕ) (v : ℝ) :
    0 ≤ bombieriDigammaKernel k v

private theorem bombieriDigammaKernel_le_div_sq
    (k : ℕ) {v : ℝ} (hv : 1 ≤ |v|) :
    bombieriDigammaKernel k v ≤ (4 * k + 1 : ℝ) / v ^ 2

private theorem harmonic_sum_lower_log (N : ℕ) :
    Real.log (N + 1 : ℝ) ≤
      ∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ)⁻¹
```

For `|v| ≥ 4`, take `N = ⌊Real.sqrt |v|⌋ₙ`.  Use the exact digamma series, discard its nonnegative tail, bound the first `N` rational kernels by `O(N²/v²)`, and use `N + 1 > sqrt |v|` to obtain one half of `log |v|`.  On `|v| ≤ 4`, use continuity on the compact interval and an existential lower bound.  Enlarge the constant to absorb `log π` and Euler's constant.

- [ ] **Step 4: Promote and verify**

Move the green declarations into `MultiplicativeWeilDigammaLower.lean`, add its root import, and run:

```bash
lake env lean -DwarningAsError=true ArithmeticHodge/Analysis/MultiplicativeWeilDigammaLower.lean
```

Expected: exit 0.

- [ ] **Step 5: Commit**

```bash
git add ArithmeticHodge.lean ArithmeticHodge/Analysis/MultiplicativeWeilDigammaLower.lean
git commit -m "prove logarithmic lower bound for Bombieri gamma kernel"
```

---

### Task 2: Logarithmic support and Plancherel identities

**Files:**
- Create: `ArithmeticHodge/Analysis/MultiplicativeWeilLogSupport.lean`
- Modify: `ArithmeticHodge.lean`
- Test: `BombieriLogSupportScratch.lean` (temporary, delete before commit)

**Interfaces:**
- Consumes: `BombieriTest.logarithmicPullbackSchwartz`, `bombieriMellin_vertical_eq_fourier`, Fourier Plancherel for `SchwartzMap`.
- Produces:

```lean
theorem logarithmicPullbackSchwartz_eq_zero_outside
    (g : BombieriTest) {a b u : ℝ} (ha : 0 < a)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hu : u ∉ Set.Icc (-Real.log b) (-Real.log a)) :
    g.logarithmicPullbackSchwartz (1 / 2) u = 0

theorem mellin_critical_normSq_integral_eq_logPullback_normSq
    (g : BombieriTest) :
    ((1 / (2 * Real.pi)) * ∫ v : ℝ,
      Complex.normSq
        (mellin (g : ℝ → ℂ) ((1 / 2 : ℝ) + v * Complex.I))) =
      ∫ u : ℝ, Complex.normSq (g.logarithmicPullbackSchwartz (1 / 2) u)
```

- [ ] **Step 1: Add the failing support and norm declarations**

Use exactly the signatures above.  The interval length is later rewritten by
`(-log a) - (-log b) = log (b/a)` using `Real.log_div` and positivity.

- [ ] **Step 2: Verify the declarations fail only at their proof bodies**

Run:

```bash
lake env lean -DwarningAsError=true BombieriLogSupportScratch.lean
```

- [ ] **Step 3: Prove support transport**

Unfold `BombieriTest.logarithmicPullbackSchwartz` and
`BombieriTest.logarithmicPullback`.  If the value is nonzero, use
`subset_tsupport` and `hsupport`, then convert `a ≤ exp(-u) ≤ b` to
`-log b ≤ u ≤ -log a` with `Real.exp_le_exp`, `Real.exp_log`, and the
strict monotonicity of `Real.log`.

- [ ] **Step 4: Prove the norm identity**

Rewrite the Mellin transform with `bombieriMellin_vertical_eq_fourier`.
Change variables `v = 2πξ`; then apply the Schwartz Fourier Plancherel
identity and map the real-valued norm-square integrals through the scaling
formula.  Keep the `2π` normalization explicit until the final `ring` step.

- [ ] **Step 5: Verify and commit**

```bash
lake env lean -DwarningAsError=true ArithmeticHodge/Analysis/MultiplicativeWeilLogSupport.lean
git add ArithmeticHodge.lean ArithmeticHodge/Analysis/MultiplicativeWeilLogSupport.lean
git commit -m "connect Bombieri log support with Mellin Plancherel"
```

---

### Task 3: Compact-support logarithmic uncertainty estimate

**Files:**
- Create: `ArithmeticHodge/Analysis/CompactSupportLogUncertainty.lean`
- Modify: `ArithmeticHodge.lean`
- Test: `CompactSupportLogUncertaintyScratch.lean` (temporary, delete before commit)

**Interfaces:**
- Consumes: Mathlib Fourier transform and Plancherel; support interval facts from Task 2.
- Produces:

```lean
theorem exists_fourier_log_weight_lower_of_intervalSupport :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : SchwartzMap ℝ ℂ) (c δ : ℝ),
      0 < δ →
      δ ≤ Real.exp (-4) →
      (∀ u ∉ Set.Icc (c - δ / 2) (c + δ / 2), F u = 0) →
      (Real.log (1 / δ) - Real.log (Real.log (Real.exp 1 / δ)) - C) *
          ∫ u : ℝ, Complex.normSq (F u) ≤
        ∫ ξ : ℝ,
          Real.log (max 1 |ξ|) * Complex.normSq (𝓕 F ξ)
```

- [ ] **Step 1: State the theorem in a scratch file and confirm failure**

Run the strict Lean command and confirm no missing import/API error precedes the proof.

- [ ] **Step 2: Formalize the sinc cutoff estimate**

For `K > 1`, use

```lean
∫ ξ in {ξ | K < |ξ|}, ‖𝓕 F ξ‖ ^ 2 =
  ∫ ξ, ‖𝓕 F ξ‖ ^ 2 -
    ∫ ξ in {ξ | |ξ| ≤ K}, ‖𝓕 F ξ‖ ^ 2
```

and bound the low-frequency integral by inserting the multiplier
`sin (ξ / K) / ξ`.  Identify its inverse Fourier transform with convolution
by the interval indicator `[-1/K,1/K]`, apply Cauchy--Schwarz, and use that the
convolution support has length `δ + 2/K`.

- [ ] **Step 3: Choose Bombieri's scale**

Set `K = δ⁻¹ * (1 + Real.log δ⁻¹)⁻¹`.  Prove `K > 1` after
restricting to an explicit existential `0 < δ₀ < exp(-4)`.  Substitute into
the preceding estimate and absorb bounded algebraic terms into `C`.

- [ ] **Step 4: Verify and commit**

```bash
lake env lean -DwarningAsError=true ArithmeticHodge/Analysis/CompactSupportLogUncertainty.lean
git add ArithmeticHodge.lean ArithmeticHodge/Analysis/CompactSupportLogUncertainty.lean
git commit -m "prove Fourier log uncertainty for compact support"
```

---

### Task 4: Polar cross-term bound

**Files:**
- Create: `ArithmeticHodge/Analysis/MultiplicativeWeilQuadraticPolarBound.lean`
- Modify: `ArithmeticHodge.lean`
- Test: `BombieriQuadraticPolarBoundScratch.lean` (temporary, delete before commit)

**Interfaces:**
- Consumes: logarithmic pullback from Task 2 and the polar identity `bombieriQuadratic_polar_eq_two_re`.
- Produces:

```lean
theorem bombieriQuadratic_polar_re_lower_of_support
    (g : BombieriTest) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b) :
    -4 * Real.log (b / a) * Real.cosh (Real.log (b / a) / 2) *
        ∫ u : ℝ, Complex.normSq (g.logarithmicPullbackSchwartz (1 / 2) u) ≤
      (mellin (bombieriQuadraticTest g : ℝ → ℂ) 1 +
        mellin (bombieriQuadraticTest g : ℝ → ℂ) 0).re
```

- [ ] **Step 1: Confirm the target is initially unproved**

Add the declaration to the scratch file and run strict Lean.

- [ ] **Step 2: Rewrite endpoint Mellin values in log coordinates**

Use the substitution `x = exp(-u)` to express `M g(1)` and `M g(0)` as
integrals of `exp(−u/2)F(u)` and `exp(u/2)F(u)`.  Translate the support
interval to length `δ = log(b/a)` and recenter it; the common translation
phase cancels in the real cross product.

- [ ] **Step 3: Apply Cauchy--Schwarz and the exponential oscillation bound**

Bound the negative part of twice the real cross product by
`4*δ*cosh(δ/2)*‖F‖²`, matching Bombieri's estimate (12.6).  Use
`integral_norm_mul_le_L2`/Cauchy--Schwarz and the
pointwise bounds of `exp(±u/2)` across an interval of length `δ`.

- [ ] **Step 4: Verify and commit**

```bash
lake env lean -DwarningAsError=true ArithmeticHodge/Analysis/MultiplicativeWeilQuadraticPolarBound.lean
git add ArithmeticHodge.lean ArithmeticHodge/Analysis/MultiplicativeWeilQuadraticPolarBound.lean
git commit -m "bound Bombieri quadratic polar cross term"
```

---

### Task 5: Universal small-support strict positivity

**Files:**
- Create: `ArithmeticHodge/Analysis/MultiplicativeWeilSmallSupportPositivity.lean`
- Modify: `ArithmeticHodge.lean`
- Test: `BombieriSmallSupportPositivityScratch.lean` (temporary, delete before commit)

**Interfaces:**
- Consumes: Tasks 1--4, `bombieriFunctional_quadratic_eq_local_critical_form`, `bombieriFunctional_bombieriQuadraticTest_im_eq_zero`, and `bombieriQuadraticTest_ne_zero`.
- Produces:

```lean
theorem exists_support_ratio_bombieriQuadratic_strictPos :
    ∃ R₀ : ℝ, 1 < R₀ ∧ R₀ < 2 ∧
      ∀ (g : BombieriTest) {a b : ℝ},
        0 < a → a ≤ b → tsupport g ⊆ Set.Icc a b →
        b / a ≤ R₀ → g ≠ 0 →
        (bombieriFunctional (bombieriQuadraticTest g)).im = 0 ∧
          0 < (bombieriFunctional (bombieriQuadraticTest g)).re
```

- [ ] **Step 1: Add the final declaration and confirm the dependency boundary**

The initial strict Lean run must fail only because the Task 1--4 estimates
have not yet been combined.

- [ ] **Step 2: Choose a support-width constant**

Let `C` be the sum of the constants from Tasks 1 and 3.  By
`Real.tendsto_log_nhdsGT_zero_atTop` and the slower growth of `log log`, choose
`0 < δ₀ < min (log 2) 1` such that

```lean
C + 4 * δ₀ * Real.cosh (δ₀ / 2) <
  (1 / 2) * (Real.log (1 / δ₀) -
    Real.log (Real.log (Real.exp 1 / δ₀)))
```

and define `R₀ = exp δ₀`.

- [ ] **Step 3: Combine the local form and estimates**

For `b/a ≤ R₀`, set `δ = log(b/a)`.  Prime vanishing follows from
`R₀ < 2`.  Apply the critical-line local form, the digamma bound, the
uncertainty estimate, and the polar lower bound.  The result is a positive
constant times the log-pullback `L²` norm.  Prove that norm is positive from
`g ≠ 0` and the logarithmic coordinate equivalence.

- [ ] **Step 4: Add reality and strict positivity**

Use `bombieriFunctional_bombieriQuadraticTest_im_eq_zero g` for the imaginary
part and the estimate from Step 3 for the real part.

- [ ] **Step 5: Verify, audit, and commit**

```bash
lake env lean -DwarningAsError=true ArithmeticHodge/Analysis/MultiplicativeWeilSmallSupportPositivity.lean
if rg -n --glob '*.lean' '^\s*(private\s+)?axiom\b|^\s*sorry\b|\bby\s+sorry\b' ArithmeticHodge; then exit 1; fi
if rg -n '_scratch|Scratch' ArithmeticHodge --glob '*.lean'; then exit 1; fi
lake build ArithmeticHodge
git add ArithmeticHodge.lean ArithmeticHodge/Analysis/MultiplicativeWeilSmallSupportPositivity.lean
git commit -m "prove Bombieri quadratic positivity for small supports"
```

Expected: all commands exit 0; the full build may retain pre-existing linter warnings but introduces no new warning in the added module.

---

## Self-Review

- Spec coverage: the plan proves the strongest noncircular subclass identified by Bombieri's Section 12 and stops short of the all-support statement equivalent to RH.
- Placeholder scan: every task names concrete files, signatures, proof ingredients, validation commands, and commit boundaries.
- Type consistency: all later signatures consume production theorem names already present or introduced explicitly by an earlier task.
- Circularity check: no task uses RH, zero-side positivity, the legacy Weil model, Hodge assumptions, or the inconsistent adelic class.
