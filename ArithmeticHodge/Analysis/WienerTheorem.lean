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
set_option maxHeartbeats 3200000

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

/-! ### Wiener's Theorem -/

/-- The time-averaged exponential kernel on ℝ × ℝ, parametrized by T. -/
private noncomputable def wienerKernel (T : ℝ) (p : ℝ × ℝ) : ℂ :=
  (↑(1 / T) : ℂ) * ∫ t in Set.Icc (0 : ℝ) T,
    Complex.exp (↑(t * (p.2 - p.1)) * Complex.I)

/-- The pointwise limit of the kernel: 1 on diagonal, 0 off diagonal. -/
private noncomputable def wienerLimit (p : ℝ × ℝ) : ℂ :=
  if p.1 = p.2 then 1 else 0

/-- **Wiener's Theorem.**

    For a finite Borel measure μ on ℝ, the time-averaged Fourier power spectrum
    converges to the sum of squared atoms:
      lim_{T→∞} (1/T) ∫₀ᵀ |μ̂(t)|² dt = Σ_x μ({x})² -/
theorem wiener_theorem {μ : MeasureTheory.Measure ℝ} [IsFiniteMeasure μ] :
    Tendsto (fun T => (1/T) * ∫ t in Set.Icc 0 T,
      ‖∫ x, Complex.exp (↑(t * x) * Complex.I) ∂μ‖^2)
      atTop (nhds (∑' x, μ.real {x} ^ 2)) := by
  -- ═══════════════════════════════════════════════════════════════
  -- Setup: product measure and shorthand
  -- ═══════════════════════════════════════════════════════════════
  set μ' := μ.prod μ with hμ'_def
  set F := wienerKernel with hF_def
  set f := wienerLimit with hf_def

  -- ═══════════════════════════════════════════════════════════════
  -- Claim 1 (DCT): ∫ F(T) dμ' → ∫ f dμ' as T → ∞
  -- ═══════════════════════════════════════════════════════════════
  have dct : Tendsto (fun T => ∫ p, F T p ∂μ') atTop (nhds (∫ p, f p ∂μ')) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
    · -- (a) AEStronglyMeasurable F T μ' (eventually)
      filter_upwards with T
      simp only [hF_def, wienerKernel]
      exact aestronglyMeasurable_const.mul
        (StronglyMeasurable.aestronglyMeasurable (by measurability))
    · -- (b) ‖F T p‖ ≤ 1 for a.e. p (eventually for T > 0)
      filter_upwards [Ioi_mem_atTop (0 : ℝ)] with T (hT : 0 < T)
      filter_upwards with p
      simp only [hF_def, wienerKernel]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < 1 / T)]
      calc (1 / T) * ‖∫ t in Set.Icc 0 T,
              Complex.exp (↑(t * (p.2 - p.1)) * Complex.I)‖
          ≤ (1 / T) * ∫ t in Set.Icc 0 T,
              ‖Complex.exp (↑(t * (p.2 - p.1)) * Complex.I)‖ := by
            apply mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _)
            positivity
        _ = (1 / T) * ∫ _ in Set.Icc 0 T, (1 : ℝ) := by
            congr 1; apply setIntegral_congr measurableSet_Icc
            intro t _; exact Complex.norm_exp_ofReal_mul_I _
        _ = (1 / T) * volume.real (Set.Icc 0 T) := by
            rw [setIntegral_const, smul_eq_mul, mul_one]
        _ = 1 := by
            rw [Measure.real, Real.volume_Icc, sub_zero,
              ENNReal.toReal_ofReal hT.le]
            exact one_div_mul_cancel (ne_of_gt hT)
    · -- (c) Bound integrable on finite measure
      exact integrable_const 1
    · -- (d) Pointwise limit: F T p → f p
      filter_upwards with ⟨x, y⟩
      simp only [hF_def, wienerKernel, hf_def, wienerLimit]
      by_cases heq : x = y
      · -- Diagonal: exp(0) = 1, so average of 1 → 1
        simp only [heq, sub_self, mul_zero, zero_mul, Complex.ofReal_zero,
          Complex.exp_zero, ite_true]
        -- Need: (↑(1/T):ℂ) * ∫ t in Icc 0 T, 1 → 1
        suffices h : Tendsto (fun T : ℝ => (↑(1 / T) : ℂ) * ↑(volume.real (Set.Icc 0 T)))
            atTop (nhds 1) by
          refine h.congr (fun T => ?_)
          congr 1; rw [← setIntegral_const]; congr 1 with t
          simp [smul_eq_mul]
        -- (↑(1/T) : ℂ) * ↑T → 1 for large T
        rw [show (1 : ℂ) = ↑(1 : ℝ) from by simp]
        apply Complex.continuous_ofReal.continuousAt.tendsto.comp
        apply Tendsto.congr'
        · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with T (hT : 0 < T)
          simp [Measure.real, Real.volume_Icc, sub_zero,
            ENNReal.toReal_ofReal hT.le, one_div_mul_cancel (ne_of_gt hT)]
        · exact tendsto_const_nhds
      · -- Off-diagonal: the time average → 0
        simp only [heq, ite_false]
        set α := y - x with hα_def
        have hα : α ≠ 0 := sub_ne_zero.mpr (Ne.symm heq)
        -- Use squeeze_zero_norm: ‖F T (x,y)‖ ≤ (2/|α|) * |1/T| → 0
        apply squeeze_zero_norm
        · -- Bound: ‖(1/T:ℂ) * integral‖ ≤ (2/|α|) / T for T > 0, else 0
          intro T
          by_cases hT : (0 : ℝ) < T
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos (by positivity : (0:ℝ) < 1/T)]
            -- Bound the integral using explicit antiderivative
            have hconv : ∫ t in Set.Icc 0 T,
                Complex.exp (↑(t * α) * Complex.I) =
                ∫ t in (0 : ℝ)..T,
                Complex.exp ((↑α * Complex.I) * ↑t) := by
              rw [intervalIntegral.integral_of_le hT.le]
              apply setIntegral_congr measurableSet_Ioc
              intro t _
              ring_nf
            rw [hconv, intervalIntegral_cexp α T hα]
            rw [norm_div, Complex.norm_mul, Complex.norm_real, Complex.norm_eq_abs,
              Complex.abs_I, mul_one]
            calc (1 / T) * (‖Complex.exp ((↑α * Complex.I) * ↑T) -
                    Complex.exp ((↑α * Complex.I) * ↑(0:ℝ))‖ / |α|)
                ≤ (1 / T) * (2 / |α|) := by
                  apply mul_le_mul_of_nonneg_left _ (by positivity)
                  apply div_le_div_of_nonneg_right _ (by positivity : (0:ℝ) < |α|)
                  calc ‖Complex.exp ((↑α * Complex.I) * ↑T) -
                        Complex.exp ((↑α * Complex.I) * ↑(0:ℝ))‖
                      ≤ ‖Complex.exp ((↑α * Complex.I) * ↑T)‖ +
                        ‖Complex.exp ((↑α * Complex.I) * ↑(0:ℝ))‖ :=
                        norm_sub_le _ _
                    _ = 1 + 1 := by
                        constructor
                        all_goals (rw [map_mul, Complex.norm_real, Complex.norm_eq_abs,
                          Complex.abs_I, mul_one]; simp [Complex.abs_exp_ofReal_mul_I])
                    _ = 2 := by norm_num
              _ = 2 / |α| / T := by ring
          · -- T ≤ 0: norm is 0
            simp only [not_lt] at hT
            have : Set.Icc (0 : ℝ) T = ∅ ∨ Set.Icc (0 : ℝ) T = {0} ∨
                Set.Icc (0 : ℝ) T ⊆ Set.Icc 0 0 := by
              rcases le_antisymm hT (le_refl 0) |>.symm ▸ Or.inl rfl with h | h
              · exact Or.inr (Or.inl h)
              · left; exact Set.Icc_eq_empty (not_le.mpr (lt_of_le_of_lt hT
                  (lt_of_lt_of_le (by linarith : T < 0) (le_refl 0))
                  |>.not_le |>.elim))
            -- The integral over a measure-zero set is 0
            simp only [norm_mul]
            apply mul_nonneg (norm_nonneg _) (norm_nonneg _)
        · -- The bound → 0 as T → ∞
          have : Tendsto (fun T : ℝ => 2 / |α| / T) atTop (nhds 0) := by
            rw [show (0 : ℝ) = 2 / |α| * 0 from by ring]
            exact Tendsto.const_mul tendsto_inv_atTop_zero (2 / |α|)
          exact this.congr (fun T => by ring)
  -- ═══════════════════════════════════════════════════════════════
  -- Claim 2 (Rewrite): LHS = Re(∫ F(T) dμ') for large T
  -- This is the double integral representation:
  --   ‖μ̂(t)‖² = Re(∫∫ exp(it(y-x)·I) dμ⊗μ)
  -- combined with Fubini to swap time and measure integrals.
  -- ═══════════════════════════════════════════════════════════════
  have rewrite : ∀ᶠ T in atTop, (1/T) * ∫ t in Set.Icc 0 T,
      ‖∫ x, Complex.exp (↑(t * x) * Complex.I) ∂μ‖^2 =
      (∫ p, F T p ∂μ').re := by
    sorry
  -- ═══════════════════════════════════════════════════════════════
  -- Claim 3 (Evaluate): Re(∫ f dμ') = ∑' x, μ.real {x}²
  -- ∫ 1_{diag} d(μ⊗μ) = ∫ μ.real{x} dμ(x) = Σ μ.real{x}²
  -- ═══════════════════════════════════════════════════════════════
  have eval : (∫ p, f p ∂μ').re = ∑' x, μ.real {x} ^ 2 := by
    sorry
  -- ═══════════════════════════════════════════════════════════════
  -- Combine: from DCT + rewrite + eval, conclude Tendsto
  -- ═══════════════════════════════════════════════════════════════
  rw [show ∑' x, μ.real {x} ^ 2 = (∫ p, f p ∂μ').re from eval.symm]
  exact (tendsto_congr rewrite).mpr ((Complex.continuous_re.tendsto _).comp dct)

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
