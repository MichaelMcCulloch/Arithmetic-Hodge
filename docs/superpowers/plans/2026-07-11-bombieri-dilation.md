# Bombieri Normalized Dilation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` to implement this plan with
> test-driven development and an independent post-commit proof review.

**Goal:** Formalize the normalized multiplicative dilation that translates a
critical logarithmic pullback while leaving its Bombieri autocorrelation and
quadratic functional exactly unchanged.

**Architecture:** For `λ > 0`, bundle
`D_λ g (x) = sqrt(λ) * g (λ*x)` as a `BombieriTest`.  Scaling the Haar
integration variable shows `autocorrelation (D_λ g) = autocorrelation g`.
The critical logarithmic pullback is translated by `log λ`.  A specialization
at `λ = exp ((log a + log b)/2)` therefore centers any positive support
interval without changing the quadratic value.

**Tech Stack:** Lean 4, Mathlib, the existing `ArithmeticHodge.Analysis`
Bombieri-test and multiplicative-Weil modules.

## Global Constraints

- No `sorry`, `admit`, custom `axiom`, unsafe declaration, or forbidden
  RH-equivalent dependency.
- Preserve all 159 legacy untracked Lean research files.
- Keep raw function/support construction helpers private.
- Strict-compile the production module, run the full build and scans, commit
  only the module and umbrella import, then obtain an independent review.

---

### Task 1: Normalized dilation and logarithmic centering

**Namespace:** All declarations below live in
`ArithmeticHodge.Analysis.MultiplicativeWeil`, matching the existing
Bombieri and multiplicative-Weil API. Do not add parent-namespace aliases.

**Files:**

- Create: `ArithmeticHodge/Analysis/MultiplicativeWeilDilation.lean`
- Modify: `ArithmeticHodge.lean`
- Test: `BombieriDilationScratch.lean` (temporary; delete before commit)

**Imports:**

```lean
import ArithmeticHodge.Analysis.MultiplicativeWeilQuadraticReality
import ArithmeticHodge.Analysis.MultiplicativeWeilLogSupport
```

**Produces:** The following public interfaces.

```lean
def normalizedDilation (λ : ℝ) (hλ : 0 < λ)
    (g : BombieriTest) : BombieriTest

@[simp] theorem normalizedDilation_apply
    (λ : ℝ) (hλ : 0 < λ) (g : BombieriTest) (x : ℝ) :
    normalizedDilation λ hλ g x =
      ((Real.sqrt λ : ℝ) : ℂ) * g (λ * x)

theorem normalizedDilation_tsupport
    (λ : ℝ) (hλ : 0 < λ) (g : BombieriTest) :
    tsupport (normalizedDilation λ hλ g) =
      (Homeomorph.mulLeft₀ λ hλ.ne') ⁻¹' tsupport g

theorem normalizedDilation_tsupport_subset_Icc
    (λ : ℝ) (hλ : 0 < λ) (g : BombieriTest)
    {a b : ℝ} (hs : tsupport g ⊆ Set.Icc a b) :
    tsupport (normalizedDilation λ hλ g) ⊆
      Set.Icc (a / λ) (b / λ)

theorem autocorrelation_normalizedDilation
    (λ : ℝ) (hλ : 0 < λ) (g : BombieriTest) (x : ℝ) :
    autocorrelation (normalizedDilation λ hλ g : ℝ → ℂ) x =
      autocorrelation (g : ℝ → ℂ) x

theorem bombieriQuadraticTest_normalizedDilation
    (λ : ℝ) (hλ : 0 < λ) (g : BombieriTest) :
    bombieriQuadraticTest (normalizedDilation λ hλ g) =
      bombieriQuadraticTest g

theorem bombieriFunctional_quadratic_normalizedDilation
    (λ : ℝ) (hλ : 0 < λ) (g : BombieriTest) :
    bombieriFunctional
        (bombieriQuadraticTest (normalizedDilation λ hλ g)) =
      bombieriFunctional (bombieriQuadraticTest g)

theorem normalizedDilation_logarithmicPullbackSchwartz_critical
    (λ : ℝ) (hλ : 0 < λ) (g : BombieriTest) (u : ℝ) :
    (normalizedDilation λ hλ g).logarithmicPullbackSchwartz
        (1 / 2) u =
      g.logarithmicPullbackSchwartz (1 / 2) (u - Real.log λ)

theorem normalizedDilation_ne_zero_iff
    (λ : ℝ) (hλ : 0 < λ) (g : BombieriTest) :
    normalizedDilation λ hλ g ≠ 0 ↔ g ≠ 0

theorem normalizedDilation_eq_zero_iff
    (λ : ℝ) (hλ : 0 < λ) (g : BombieriTest) :
    normalizedDilation λ hλ g = 0 ↔ g = 0

def logarithmicCenter (a b : ℝ) : ℝ :=
  Real.exp ((Real.log a + Real.log b) / 2)

def logarithmicHalfWidth (a b : ℝ) : ℝ :=
  (Real.log b - Real.log a) / 2

theorem logarithmicCenter_pos (a b : ℝ) :
    0 < logarithmicCenter a b

theorem log_div_logarithmicCenter_left
    {a b : ℝ} (ha : 0 < a) :
    Real.log (a / logarithmicCenter a b) =
      -logarithmicHalfWidth a b

theorem log_div_logarithmicCenter_right
    {a b : ℝ} (hb : 0 < b) :
    Real.log (b / logarithmicCenter a b) =
      logarithmicHalfWidth a b

theorem logarithmicCenter_endpoint_reciprocal
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a / logarithmicCenter a b =
      (b / logarithmicCenter a b)⁻¹

theorem logCenteredNormalizedDilation_tsupport_subset_Icc
    (g : BombieriTest) {a b : ℝ}
    (hs : tsupport g ⊆ Set.Icc a b) :
    tsupport (normalizedDilation (logarithmicCenter a b)
      (logarithmicCenter_pos a b) g) ⊆
        Set.Icc (a / logarithmicCenter a b)
          (b / logarithmicCenter a b)

theorem logCenteredNormalizedDilation_logarithmicPullback_eq_zero_outside
    (g : BombieriTest) {a b u : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hs : tsupport g ⊆ Set.Icc a b)
    (hu : u ∉ Set.Icc (-logarithmicHalfWidth a b)
      (logarithmicHalfWidth a b)) :
    BombieriTest.logarithmicPullbackSchwartz
      (normalizedDilation (logarithmicCenter a b)
        (logarithmicCenter_pos a b) g) (1 / 2) u = 0
```

## Steps

- [ ] Create the exact declarations in the scratch file and record the RED
  warning-as-error compile.
- [ ] Bundle the raw dilation with `TestFunction.mk`; prove its exact
  topological support using `tsupport_comp_eq_preimage` and
  `Homeomorph.mulLeft₀`.
- [ ] Prove autocorrelation invariance with
  `integral_comp_mul_left_Ioi` and `Real.sq_sqrt hλ.le`; derive quadratic and
  functional invariance.
- [ ] Prove the critical log-translation identity from
  `sqrt λ = exp (log λ / 2)` and `exp_log hλ`.
- [ ] Prove zero/nonzero preservation and the centered support theorem using
  `logarithmicCenter` and `logarithmicHalfWidth`; do not introduce a redundant
  centered-dilation wrapper or a second geometric-center API.
- [ ] Promote, delete scratch, strict-compile, full-build, scan, commit as
  `formalize Bombieri normalized dilation`, and independently review.
