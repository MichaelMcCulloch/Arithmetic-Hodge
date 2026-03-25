/-
  LAYER 3: The Weil Positivity Criterion

  Weil's criterion (1952): The Riemann Hypothesis is equivalent to
  the non-negativity of the Weil functional on autocorrelations.

  W(g ∗ g̃) ≥ 0 for all admissible g  ⟺  RH

  This is the form that connects to the Arithmetic Hodge Index:
  the intersection pairing being negative-definite on degree-zero classes
  is equivalent to W being non-negative on autocorrelations.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Integral

import ArithmeticHodge.Analysis.WeilExplicit

open MeasureTheory Real MeasureTheory.Measure

namespace ArithmeticHodge.Analysis

-- ============================================================
-- Autocorrelations
-- ============================================================

/-- A function f : ℝ → ℝ is an autocorrelation if it can be written as
    f = g ∗ g̃ for some g, where g̃(x) = g(-x) and ∗ is convolution.

    For real-valued g, this means f(x) = ∫ g(y) · g(y + x) dy.

    Autocorrelations are always:
    - Even: f(x) = f(-x)
    - Maximized at 0: f(0) ≥ |f(x)| for all x
    - Positive-definite as distributions (f̂ ≥ 0) -/
def IsAutocorrelation (f : ℝ → ℝ) : Prop :=
  ∃ g : ℝ → ℝ, Integrable g volume ∧
    ∀ x : ℝ, f x = ∫ y : ℝ, g y * g (y + x) ∂volume

/-- Autocorrelations are non-negative at the origin.
    f(0) = ∫ g(y)² dy ≥ 0 since the integrand is non-negative.
    SORRY COUNT: 0 — PROVED. -/
theorem autocorrelation_nonneg_at_zero (f : ℝ → ℝ) (hf : IsAutocorrelation f) :
    0 ≤ f 0 := by
  obtain ⟨g, _, hg⟩ := hf
  rw [hg 0]
  simp only [add_zero]
  exact integral_nonneg (fun y => mul_self_nonneg (g y))

/-- Autocorrelations are even: f(x) = f(-x).
    Proof: f(-x) = ∫ g(y)g(y-x) dy. By translation (integral_add_left_eq_self),
    this equals ∫ g(u+x)g(u) du = ∫ g(u)g(u+x) du = f(x).
    SORRY COUNT: 0 — PROVED. -/
theorem autocorrelation_even (f : ℝ → ℝ) (hf : IsAutocorrelation f) :
    ∀ x : ℝ, f x = f (-x) := by
  obtain ⟨g, _, hg⟩ := hf
  intro x
  rw [hg x, hg (-x)]
  -- Goal: ∫ g(y) g(y+x) dy = ∫ g(y) g(y+(-x)) dy
  -- Step 1: LHS = ∫ g(y+x) * g(y) dy  (by mul_comm under integral)
  -- Step 2: RHS = ∫ g((-x)+y+x) * g((-x)+y) dy  (rewrite integrand)
  -- Step 3: By integral_add_left_eq_self, step 2 = ∫ g(y+x) * g(y) dy = step 1
  rw [show (fun y => g y * g (y + x)) = (fun y => g (y + x) * g y) from by ext y; ring]
  rw [show (fun y => g y * g (y + (-x))) = (fun y => g ((-x) + y + x) * g ((-x) + y)) from
    by ext y; ring]
  exact (integral_add_left_eq_self (μ := (volume : MeasureTheory.Measure ℝ))
    (fun y => g (y + x) * g y) (-x)).symm

/-- **Auxiliary lemma**: For integrable g with g² integrable and g·g(·+x) integrable,
    the autocorrelation is maximized at the origin.
    Proved via AM-GM: g(y)*g(y+x) ≤ (g(y)² + g(y+x)²)/2, then
    translation invariance gives ∫ g(·+x)² = ∫ g².
    SORRY COUNT: 0 — PROVED. -/
theorem integral_mul_le_integral_sq (g : ℝ → ℝ) (x : ℝ)
    (hg_sq : Integrable (fun y => g y ^ 2) volume)
    (hg_prod : Integrable (fun y => g y * g (y + x)) volume) :
    ∫ y, g y * g (y + x) ≤ ∫ y, g y ^ 2 := by
  have hgx_sq : Integrable (fun y => g (y + x) ^ 2) volume :=
    hg_sq.comp_add_right x
  -- AM-GM pointwise: a*b ≤ (a² + b²)/2
  have h_amgm : ∀ y, g y * g (y + x) ≤ (g y ^ 2 + g (y + x) ^ 2) / 2 := by
    intro y; nlinarith [sq_nonneg (g y - g (y + x))]
  -- Integrate the bound
  have h1 : Integrable (fun y => (g y ^ 2 + g (y + x) ^ 2) / 2) volume :=
    (hg_sq.add hgx_sq).div_const 2
  have h2 : ∫ y, g y * g (y + x) ≤ ∫ y, (g y ^ 2 + g (y + x) ^ 2) / 2 :=
    integral_mono hg_prod h1 h_amgm
  -- Simplify: ∫ (g² + g(·+x)²)/2 = (∫ g² + ∫ g(·+x)²)/2 = ∫ g²
  have h3 : ∫ y, (g y ^ 2 + g (y + x) ^ 2) / 2 = ∫ y, g y ^ 2 := by
    have : (fun y => (g y ^ 2 + g (y + x) ^ 2) / 2) =
        fun y => (1 / 2 : ℝ) * ((fun y => g y ^ 2) + (fun y => g (y + x) ^ 2)) y := by
      ext y; simp [Pi.add_apply]; ring
    rw [this, integral_const_mul, integral_add' hg_sq hgx_sq,
        integral_add_right_eq_self (fun y => g y ^ 2) x]; ring
  linarith

/-- Autocorrelations are maximized at the origin.
    Uses AM-GM: g(y)*g(y+x) ≤ (g²(y) + g²(y+x))/2, then translation invariance.

    The proof requires g ∈ L²(ℝ) (i.e., g² integrable) and g·g(·+x) integrable.
    These hold automatically for Schwartz-class test functions, which are the
    relevant case for the Weil explicit formula.

    SORRY COUNT: 0 — PROVED (given integrability hypotheses). -/
theorem autocorrelation_max_at_zero (g : ℝ → ℝ)
    (hg_sq : Integrable (fun y => g y ^ 2) volume)
    (hg_prod : ∀ x, Integrable (fun y => g y * g (y + x)) volume) :
    ∀ x : ℝ, ∫ y, g y * g (y + x) ≤ ∫ y, g y ^ 2 := by
  intro x
  exact integral_mul_le_integral_sq g x hg_sq (hg_prod x)

-- ============================================================
-- Autocorrelation at zero: the L² norm squared
-- ============================================================

/-- f(0) = ‖g‖₂² for an autocorrelation f = g ∗ g̃. -/
theorem autocorrelation_zero_eq_L2_norm_sq (f : ℝ → ℝ) (hf : IsAutocorrelation f) :
    f 0 = ∫ y : ℝ, (hf.choose y) ^ 2 ∂volume := by
  have hg := hf.choose_spec.2
  rw [hg 0]
  simp only [add_zero]
  congr 1; ext y; ring

-- ============================================================
-- Weil's Positivity Criterion
-- ============================================================

/-- **Weil's Positivity Criterion — Forward Direction.**

    RH implies Weil positivity: if all nontrivial zeros have Re = 1/2,
    then W(f) ≥ 0 for every autocorrelation f = g ∗ g̃.

    Proof sketch: By the Weil explicit formula,
      W(f) = Σ_ρ |ĝ(γ_ρ)|² ≥ 0
    where ρ = 1/2 + iγ_ρ. Since all γ_ρ are real (by RH), the
    Fourier transform ĝ is evaluated at real points and the sum is non-negative.

    [DEEP] Requires: Weil explicit formula (Layer 2).
    Once the explicit formula is available, this is ~5 lines. -/
theorem weil_criterion_forward :
    RiemannHypothesis →
    (∀ f : ℝ → ℝ, IsAutocorrelation f →
      ∀ fHat_zero fHat_one : ℝ,
      0 ≤ weilFunctional f fHat_zero fHat_one) := by
  sorry -- [DEEP] Needs: explicit formula. Proof: W(f) = Σ|ĝ(γ)|² ≥ 0.

/-- **Weil's Positivity Criterion — Backward Direction.**

    Weil positivity implies RH: if W(g ∗ g̃) ≥ 0 for all admissible g,
    then all nontrivial zeros have Re = 1/2.

    Contrapositive: if ρ₀ = 1/2 + δ + iγ₀ with δ ≠ 0, construct
    a Paley-Wiener test function g with Fourier transform concentrated
    near γ₀ such that W(g ∗ g̃) < 0.

    [DEEP] Requires: Weil explicit formula + Paley-Wiener theory. -/
theorem weil_criterion_backward :
    (∀ f : ℝ → ℝ, IsAutocorrelation f →
      ∀ fHat_zero fHat_one : ℝ,
      0 ≤ weilFunctional f fHat_zero fHat_one) →
    RiemannHypothesis := by
  sorry -- [DEEP] Needs: explicit formula + Paley-Wiener test functions.

/-- **Weil's Positivity Criterion (1952) — Combined.**

    The following are equivalent:
    (i)  All nontrivial zeros of ζ have real part 1/2 (RH).
    (ii) The Weil functional W(f) ≥ 0 for every autocorrelation f.

    This combines the forward and backward directions. -/
theorem weil_criterion :
    RiemannHypothesis ↔
    (∀ f : ℝ → ℝ, IsAutocorrelation f →
      ∀ fHat_zero fHat_one : ℝ,
      0 ≤ weilFunctional f fHat_zero fHat_one) :=
  ⟨weil_criterion_forward, weil_criterion_backward⟩

end ArithmeticHodge.Analysis
