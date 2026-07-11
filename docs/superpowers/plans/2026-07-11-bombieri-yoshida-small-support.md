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

First prove `bombieriDigammaKernel k v ≤ k⁻¹` for `1 ≤ k`, so every
tail difference in the exact digamma series is nonnegative, and prove
`bombieriDigammaKernel 0 v ≤ 4`.  For `|v| ≥ 1`, take
`N = ⌊|v|⌋ₙ`; then `N ≤ |v| < N+1`, the harmonic partial sum is at
least `log (N+1)`, and
`∑ k=1..N bombieriDigammaKernel k v ≤ (2*N^2+3*N)/|v|^2 ≤ 5`.
For `|v| < 1`, discard the entire nonnegative tail.  A single coarse constant
absorbing `9`, `|eulerMascheroniConstant|`, and `|log pi|` proves the global
statement (in fact with coefficient `1` in front of the logarithm).

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

- [ ] **Step 2: Prove the direct low-frequency estimate**

Let `A = ∫ u, Complex.normSq (F u)`.  Hölder on the support interval gives

```lean
(∫ u, ‖F u‖) ^ 2 ≤ δ * A.
```

Combine this with `SchwartzMap.norm_fourier_apply_le_toLp_one` to obtain the
pointwise bound `Complex.normSq (𝓕 F ξ) ≤ δ * A`.  Integrating over
`Set.Icc (-K) K` gives

```lean
∫ ξ in Set.Icc (-K) K, Complex.normSq (𝓕 F ξ) ≤ 2 * K * δ * A.
```

Use Plancherel to express the complementary Fourier mass as `A` minus this
low-frequency mass.  Since `log (max 1 |ξ|) ≥ log K` off `[-K,K]` for
`K > 1`, deduce

```lean
Real.log K * (1 - 2 * K * δ) * A ≤
  ∫ ξ, Real.log (max 1 |ξ|) * Complex.normSq (𝓕 F ξ).
```

Prove the logarithmically weighted Fourier norm-square is integrable from
Schwartz decay before splitting it into the interval and its complement.

- [ ] **Step 3: Choose Bombieri's scale with an explicit constant**

Set

```lean
K = 1 / (δ * Real.log (Real.exp 1 / δ)).
```

For `0 < δ ≤ exp (-4)`, prove `K > 1` and

```lean
Real.log (1 / δ) - Real.log (Real.log (Real.exp 1 / δ)) - 2 ≤
  Real.log K * (1 - 2 * K * δ).
```

Thus the public existential theorem has the explicit witness `C = 2`.  This
route matches Mathlib's unitary `exp (-2π i x ξ)` Fourier normalization and
does not require a separately normalized sinc/box transform identity.

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
interval to `[−log b, −log a]`, whose length is `δ = log(b/a)`.  The
opposite positive real endpoint weights multiply to `exp(δ/2)`, so the
center of the original multiplicative interval cancels from the product.
Keep the two endpoint Mellin identities as private implementation helpers.

- [ ] **Step 3: Apply Hölder and the endpoint exponential bounds**

First prove on an interval `[l,r]` that

```lean
(∫ u in Set.Icc l r, ‖F u‖) ^ 2 ≤
  (r - l) * ∫ u in Set.Icc l r, Complex.normSq (F u).
```

Use `Real.HolderConjugate.two_two` on the restricted measure.  Bound the two
endpoint Mellin norms by `exp(-l/2)` and `exp(r/2)` times that interval
`L¹` norm.  Their product is therefore at most
`exp(δ/2) * δ * ‖F‖²`.  The real part of twice their cross product is at
least minus twice this value, and

```lean
2 * Real.exp (δ / 2) ≤ 4 * Real.cosh (δ / 2)
```

gives the stated bound, matching Bombieri's estimate (12.6).

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

Obtain constants `C₁` and `C₃` from Tasks 1 and 3.  Derive
`Tendsto (fun x ↦ x - Real.log x) atTop atTop` from
`Real.isLittleO_log_id_atTop`.  Choose `T` far enough out, set
`δ₀ = exp (-max T 4)`, and prove the uniform statement

```lean
∀ δ, 0 < δ → δ ≤ δ₀ →
  C₁ + 4 * δ * Real.cosh (δ / 2) <
    (1 / 2) * (Real.log (1 / δ) -
      Real.log (Real.log (Real.exp 1 / δ)) - C₃)
```

Use `log (1+x) ≤ log 2 + log x` for `x ≥ 1` and bound the polar
penalty uniformly by `4 * exp (1/2)`.  This avoids relying on a nonexistent
one-sided-log limit theorem and proves the estimate for every actual support
width, not only at `δ₀`.

Define `R₀ = min (exp δ₀) (3/2)`.  Then `1 < R₀ < 2`, while
`b/a ≤ R₀` implies `log (b/a) ≤ δ₀`.

- [ ] **Step 3: Combine the local form and estimates**

For `b/a ≤ R₀`, set `δ = log(b/a)`.  Prime vanishing follows from
`R₀ < 2`.  Apply the critical-line local form, the digamma bound, the
uncertainty estimate, and the polar lower bound.  Before Task 3, recenter the
logarithmic support interval `[-log b,-log a]` at
`c = (-log b - log a)/2`.

Add a private normalized scaling bridge using `v = 2πξ`:

```lean
∫ ξ, Real.log (max 1 |ξ|) * |𝓕F ξ|² ≤
  (1 / (2 * Real.pi)) *
    ∫ v, Real.log (max 1 |v|) * |M g (1/2 + iv)|².
```

Its pointwise comparison is
`log (max 1 |ξ|) ≤ log (max 1 |2πξ|)`; prove both weighted
integrands are genuinely integrable from Schwartz decay before applying
integral monotonicity.

Prove directly that `g ≠ 0` makes the log-pullback norm-square integral
strictly positive.  This also rules out `b/a = 1` (a zero-width support
interval has measure zero), supplying the strict `0 < δ` required by Task 3.
The combined local estimate is then a positive coefficient times that
strictly positive `L²` mass.

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
