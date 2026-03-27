/-
  Wiener's Theorem

  For a finite Borel measure μ on ℝ:
    lim_{T→∞} (1/T) ∫₀ᵀ |μ̂(t)|² dt = Σ_x μ({x})²

  The proof uses the double integral representation |μ̂(t)|² = ∫∫ e^{it(x-y)·I} dμ⊗μ,
  then swaps the time integral inside via Fubini and applies dominated convergence.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

set_option autoImplicit false
set_option maxHeartbeats 1600000

open MeasureTheory Complex Filter Topology Set
open scoped NNReal ENNReal

namespace ArithmeticHodge.Analysis

/-! ### Time average of complex exponential -/

/-- For α ≠ 0, ∫₀ᵀ e^{iαt} dt = (e^{iαT} - 1)/(iα). -/
private lemma intervalIntegral_cexp (α : ℝ) (T : ℝ) (hα : α ≠ 0) :
    ∫ t in (0 : ℝ)..T, Complex.exp ((↑α * Complex.I) * ↑t) =
    (Complex.exp ((↑α * Complex.I) * ↑T) - Complex.exp ((↑α * Complex.I) * ↑(0:ℝ))) /
      (↑α * Complex.I) :=
  integral_exp_mul_complex (mul_ne_zero (Complex.ofReal_ne_zero.mpr hα) Complex.I_ne_zero)

/-! ### Wiener's Theorem

The proof is structured in three main lemmas:
1. **DCT step**: The time-averaged double integral converges via dominated convergence
2. **Rewriting step**: The LHS equals the real part of the double integral
3. **Evaluation step**: The limit integral equals the sum of squared atoms -/

/-- **Wiener's Theorem.**

    For a finite Borel measure μ on ℝ, the time-averaged Fourier power spectrum
    converges to the sum of squared atoms:
      lim_{T→∞} (1/T) ∫₀ᵀ |μ̂(t)|² dt = Σ_x μ({x})² -/
theorem wiener_theorem {μ : MeasureTheory.Measure ℝ} [IsFiniteMeasure μ] :
    Tendsto (fun T => (1/T) * ∫ t in Set.Icc 0 T,
      ‖∫ x, Complex.exp (↑(t * x) * Complex.I) ∂μ‖^2)
      atTop (nhds (∑' x, μ.real {x} ^ 2)) := by
  -- We work on the product measure μ ⊗ μ and apply DCT
  set μ' := μ.prod μ with hμ'_def
  -- The complex-valued time-averaged kernel on ℝ × ℝ
  let F : ℝ → ℝ × ℝ → ℂ := fun T p =>
    (↑(1 / T) : ℂ) * ∫ t in Set.Icc (0 : ℝ) T,
      Complex.exp (↑(t * (p.2 - p.1)) * Complex.I)
  -- The pointwise limit: 1 on diagonal, 0 off diagonal
  let f : ℝ × ℝ → ℂ := fun p => if p.1 = p.2 then 1 else 0
  -- ═══════════════════════════════════════════════════════════════
  -- Claim 1 (DCT): ∫ F(T) dμ' → ∫ f dμ' as T → ∞
  -- ═══════════════════════════════════════════════════════════════
  have dct : Tendsto (fun T => ∫ p, F T p ∂μ') atTop (nhds (∫ p, f p ∂μ')) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
    · -- AEStronglyMeasurable (eventually)
      filter_upwards with T
      -- F T is measurable as a product of a constant with an integral
      -- that depends measurably on the parameter
      exact aestronglyMeasurable_const.mul (by
        apply Measurable.aestronglyMeasurable
        sorry) -- measurability of the integral
    · -- Norm bound: ‖F T p‖ ≤ 1 (eventually for T > 0)
      filter_upwards [Ioi_mem_atTop (0 : ℝ)] with T (hT : 0 < T)
      filter_upwards with p
      show ‖F T p‖ ≤ 1
      simp only [F]
      rw [norm_mul, Complex.norm_real, abs_of_pos (by positivity : (0 : ℝ) < 1 / T)]
      -- ‖∫ exp(...)‖ ≤ ∫ ‖exp(...)‖ = ∫ 1 = T (for T > 0)
      calc (1 / T) * ‖∫ t in Set.Icc 0 T, Complex.exp (↑(t * (p.2 - p.1)) * Complex.I)‖
          ≤ (1 / T) * ∫ t in Set.Icc 0 T, ‖Complex.exp (↑(t * (p.2 - p.1)) * Complex.I)‖ := by
            apply mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _)
            positivity
        _ = (1 / T) * ∫ t in Set.Icc 0 T, (1 : ℝ) := by
            congr 1; apply setIntegral_congr measurableSet_Icc
            intro t _; rw [Complex.norm_exp_ofReal_mul_I]
        _ = (1 / T) * volume.real (Set.Icc 0 T) := by
            rw [setIntegral_const]; ring
        _ = 1 := by
            simp [Measure.real, Real.volume_Icc, sub_zero,
              ENNReal.toReal_ofReal hT.le, one_div_mul_cancel (ne_of_gt hT)]
    · -- Bound integrable on finite measure
      exact integrable_const 1
    · -- Pointwise limit: F T p → f p
      filter_upwards with p
      show Tendsto (fun T => F T p) atTop (nhds (f p))
      simp only [F, f]
      rcases p with ⟨x, y⟩
      simp only
      by_cases heq : x = y
      · -- Case x = y: integrand is exp(0) = 1, average is 1
        simp only [heq, sub_self, mul_zero, zero_mul, Complex.ofReal_zero,
          Complex.exp_zero, ite_true]
        -- (1/T : ℂ) * ∫ t in Icc 0 T, 1 = (1/T : ℂ) * volume.real (Icc 0 T) → 1
        conv => ext T; rw [setIntegral_const, smul_eq_mul, mul_one]
        rw [show (1 : ℂ) = Complex.ofReal 1 from by simp]
        apply Complex.tendsto_ofReal.comp
        apply Tendsto.congr'
        · exact tendsto_const_nhds
        · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with T (hT : 0 < T)
          simp [Measure.real, Real.volume_Icc, sub_zero,
            ENNReal.toReal_ofReal hT.le, one_div_mul_cancel (ne_of_gt hT)]
      · -- Case x ≠ y: (1/T) * bounded → 0
        simp only [heq, ite_false]
        -- The integral ∫ t ∈ [0,T], exp(it(y-x)I) is bounded by 2/|y-x|
        -- so (1/T) * bounded → 0
        rw [show (0 : ℂ) = Complex.ofReal 0 from by simp]
        apply Filter.Tendsto.norm_atTop_zero_of_le
        · intro T
          simp only [norm_mul, Complex.norm_real]
          calc |1 / T| * ‖∫ t in Set.Icc 0 T, Complex.exp (↑(t * (y - x)) * Complex.I)‖
              ≤ |1 / T| * ∫ t in Set.Icc 0 T, ‖Complex.exp (↑(t * (y - x)) * Complex.I)‖ :=
                mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (abs_nonneg _)
            _ ≤ |1 / T| * ∫ t in Set.Icc 0 T, (1 : ℝ) := by
                apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
                apply setIntegral_mono_on _ (integrableOn_const.mpr (Or.inr _)) measurableSet_Icc
                · intro t _; rw [Complex.norm_exp_ofReal_mul_I]
                · sorry -- integrableOn of norm
                · sorry -- Icc measure finite
            _ = |1 / T| * volume.real (Set.Icc 0 T) := by
                rw [setIntegral_const]; ring
            _ ≤ sorry := sorry -- need bound that → 0
        · sorry -- the bound → 0
  -- ═══════════════════════════════════════════════════════════════
  -- Claim 2 (Rewrite): LHS = Re(∫ F(T) dμ') eventually
  -- ═══════════════════════════════════════════════════════════════
  have rewrite : ∀ᶠ T in atTop, (1/T) * ∫ t in Set.Icc 0 T,
      ‖∫ x, Complex.exp (↑(t * x) * Complex.I) ∂μ‖^2 =
      (∫ p, F T p ∂μ').re := by
    sorry
  -- ═══════════════════════════════════════════════════════════════
  -- Claim 3 (Evaluate): Re(∫ f dμ') = ∑' x, μ.real {x}²
  -- ═══════════════════════════════════════════════════════════════
  have eval : (∫ p, f p ∂μ').re = ∑' x, μ.real {x} ^ 2 := by
    sorry
  -- ═══════════════════════════════════════════════════════════════
  -- Combine the three claims
  -- ═══════════════════════════════════════════════════════════════
  rw [show ∑' x, μ.real {x} ^ 2 = (∫ p, f p ∂μ').re from eval.symm]
  exact (tendsto_congr (by filter_upwards [rewrite] with T hT; exact hT)).mpr
    ((Complex.continuous_re.tendsto _).comp dct)

/-- **Wiener's theorem for continuous measures.**

    When μ has no atoms, the sum Σ μ({x})² = 0, giving decay of the
    time-averaged Fourier power spectrum. -/
theorem wiener_continuous_measure {μ : MeasureTheory.Measure ℝ} [IsFiniteMeasure μ]
    (hcont : ∀ x : ℝ, μ {x} = 0) :
    Tendsto (fun T => (1/T) * ∫ t in Set.Icc 0 T,
      ‖∫ x, Complex.exp (↑(t * x) * Complex.I) ∂μ‖^2)
      atTop (nhds 0) := by
  have h := wiener_theorem (μ := μ)
  suffices hsum : ∑' x, μ.real {x} ^ 2 = 0 by rwa [hsum] at h
  have h0 : ∀ x : ℝ, μ.real {x} ^ 2 = 0 := fun x => by
    simp [Measure.real, hcont x]
  simp_rw [h0, tsum_zero]

end ArithmeticHodge.Analysis
