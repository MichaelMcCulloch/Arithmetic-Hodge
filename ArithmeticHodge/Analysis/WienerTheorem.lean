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

/-- Norm bound on the set integral of exp for α ≠ 0, T > 0. -/
private lemma norm_setIntegral_cexp_le {α : ℝ} (hα : α ≠ 0) {T : ℝ} (hT : 0 < T) :
    ‖∫ t in Set.Icc (0 : ℝ) T, Complex.exp (↑(t * α) * Complex.I)‖ ≤ 2 / |α| := by
  -- Convert Icc set integral to Ioc, then to interval integral
  rw [show ∫ t in Set.Icc (0 : ℝ) T, Complex.exp (↑(t * α) * Complex.I) =
      ∫ t in (0 : ℝ)..T, Complex.exp ((↑α * Complex.I) * ↑t) from by
    rw [intervalIntegral.integral_of_le hT.le]
    rw [← setIntegral_congr_set Ioc_ae_eq_Icc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro t _; ring_nf]
  rw [intervalIntegral_cexp α T hα]
  rw [norm_div]
  apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) < ‖↑α * Complex.I‖)
  calc ‖Complex.exp ((↑α * Complex.I) * ↑T) -
        Complex.exp ((↑α * Complex.I) * ↑(0:ℝ))‖
      ≤ ‖Complex.exp ((↑α * Complex.I) * ↑T)‖ +
        ‖Complex.exp ((↑α * Complex.I) * ↑(0:ℝ))‖ := norm_sub_le _ _
    _ = 2 := by
        simp only [mul_zero, Complex.exp_zero, norm_one]
        have : ‖Complex.exp ((↑α * Complex.I) * ↑T)‖ = 1 := by
          rw [show (↑α * Complex.I) * ↑T = ↑(α * T) * Complex.I from by push_cast; ring]
          exact Complex.norm_exp_ofReal_mul_I _
        linarith

/-- **Wiener's Theorem.**

    For a finite Borel measure μ on ℝ, the time-averaged Fourier power spectrum
    converges to the sum of squared atoms:
      lim_{T→∞} (1/T) ∫₀ᵀ |μ̂(t)|² dt = Σ_x μ({x})² -/
theorem wiener_theorem {μ : MeasureTheory.Measure ℝ} [IsFiniteMeasure μ] :
    Tendsto (fun T => (1/T) * ∫ t in Set.Icc 0 T,
      ‖∫ x, Complex.exp (↑(t * x) * Complex.I) ∂μ‖^2)
      atTop (nhds (∑' x, μ.real {x} ^ 2)) := by
  set μ' := μ.prod μ with hμ'_def
  set F := wienerKernel with hF_def
  set f := wienerLimit with hf_def

  -- ═══════════════════════════════════════════════════════════════
  -- Claim 1 (DCT): ∫ F(T) dμ' → ∫ f dμ' as T → ∞
  -- ═══════════════════════════════════════════════════════════════
  have dct : Tendsto (fun T => ∫ p, F T p ∂μ') atTop (nhds (∫ p, f p ∂μ')) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
    · -- (a) AEStronglyMeasurable (eventually)
      filter_upwards with T
      simp only [hF_def, wienerKernel]
      apply AEStronglyMeasurable.const_mul
      -- The parametric integral is continuous in p, hence AE strongly measurable
      exact (continuous_of_dominated
        (F := fun (p : ℝ × ℝ) (t : ℝ) =>
          Complex.exp (↑(t * (p.2 - p.1)) * Complex.I))
        (bound := fun _ => 1)
        (μ := volume.restrict (Set.Icc 0 T))
        (hF_meas := fun p =>
          (Complex.continuous_exp.comp
            ((Complex.continuous_ofReal.comp
              (continuous_id'.mul continuous_const)).mul
              continuous_const)).aestronglyMeasurable)
        (h_bound := fun p => by
          filter_upwards with t
          exact le_of_eq (Complex.norm_exp_ofReal_mul_I _))
        (bound_integrable := by
          exact integrable_const_iff.mpr (Or.inr (by
            rw [Measure.restrict_apply_univ]; exact isCompact_Icc.measure_lt_top)))
        (h_cont := by
          filter_upwards with t
          exact Complex.continuous_exp.comp
            ((Complex.continuous_ofReal.comp
              (continuous_const.mul
                (continuous_snd.sub continuous_fst))).mul
              continuous_const))).aestronglyMeasurable
    · -- (b) ‖F T p‖ ≤ 1 for a.e. p (eventually for T > 0)
      filter_upwards [Ioi_mem_atTop (0 : ℝ)] with T (hT : 0 < T)
      filter_upwards with p
      simp only [hF_def, wienerKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < 1 / T)]
      calc (1 / T) * ‖∫ t in Set.Icc 0 T,
              Complex.exp (↑(t * (p.2 - p.1)) * Complex.I)‖
          ≤ (1 / T) * ∫ t in Set.Icc 0 T,
              ‖Complex.exp (↑(t * (p.2 - p.1)) * Complex.I)‖ :=
            mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
        _ = (1 / T) * ∫ _ in Set.Icc 0 T, (1 : ℝ) := by
            congr 1
            apply setIntegral_congr_fun measurableSet_Icc
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
      · -- Diagonal: exp(0) = 1, average → 1
        simp only [heq, sub_self, mul_zero, zero_mul, Complex.ofReal_zero,
          Complex.exp_zero, ite_true]
        apply tendsto_const_nhds.congr'
        filter_upwards [Ioi_mem_atTop (0 : ℝ)] with T (hT : 0 < T)
        show (1 : ℂ) = ↑(1 / T) * ∫ _ in Set.Icc 0 T, (1 : ℂ)
        rw [setIntegral_const, Complex.real_smul, mul_one, ← Complex.ofReal_mul,
          Measure.real, Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal hT.le,
          one_div_mul_cancel (ne_of_gt hT), Complex.ofReal_one]
      · -- Off-diagonal: time average → 0
        simp only [heq, ite_false]
        set α := y - x with hα_def
        have hα : α ≠ 0 := sub_ne_zero.mpr (Ne.symm heq)
        -- Use squeeze_zero_norm: bound by (2/|α|) * ‖(1/T:ℂ)‖ → 0
        apply squeeze_zero_norm
        · -- Bound for all T
          intro T
          simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          by_cases hT : (0 : ℝ) < T
          · -- T > 0: use explicit integral formula
            calc |1 / T| * ‖∫ t in Set.Icc 0 T,
                    Complex.exp (↑(t * α) * Complex.I)‖
                ≤ |1 / T| * (2 / |α|) := by
                  apply mul_le_mul_of_nonneg_left (norm_setIntegral_cexp_le hα hT)
                  exact abs_nonneg _
              _ = 2 / |α| * |1 / T| := by ring
          · -- T ≤ 0: integral is 0 (empty or null set)
            simp only [not_lt] at hT
            have hIcc : volume.real (Set.Icc (0 : ℝ) T) = 0 := by
              rw [Measure.real, Real.volume_Icc]
              simp [ENNReal.toReal_ofReal, sub_nonpos.mpr hT]
            calc |1 / T| * ‖∫ t in Set.Icc 0 T,
                    Complex.exp (↑(t * α) * Complex.I)‖
                ≤ |1 / T| * ∫ t in Set.Icc 0 T,
                    ‖Complex.exp (↑(t * α) * Complex.I)‖ :=
                  mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (abs_nonneg _)
              _ ≤ |1 / T| * ∫ _ in Set.Icc 0 T, (1 : ℝ) := by
                  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
                  apply setIntegral_mono_on
                  · apply IntegrableOn.congr (integrableOn_const.mpr (Or.inr (by
                      rw [← Measure.real]; simp [hIcc]; exact Or.inl (by norm_num))))
                    intro t ht; exact (Complex.norm_exp_ofReal_mul_I _).symm
                  · exact integrableOn_const.mpr (Or.inr (by
                      rw [← Measure.real]; simp [hIcc]; exact Or.inl (by norm_num)))
                  · exact measurableSet_Icc
                  · intro t _; exact le_of_eq (Complex.norm_exp_ofReal_mul_I _)
              _ = |1 / T| * volume.real (Set.Icc 0 T) := by
                  rw [setIntegral_const, smul_eq_mul, mul_one]
              _ = 0 := by rw [hIcc, mul_zero]
              _ ≤ 2 / |α| * |1 / T| := by positivity
        · -- Bound tends to 0
          have : Tendsto (fun T : ℝ => 2 / |α| * |1 / T|) atTop (nhds 0) := by
            rw [show (0 : ℝ) = 2 / |α| * 0 from by ring]
            apply Filter.Tendsto.const_mul
            show Tendsto (fun T : ℝ => |1 / T|) atTop (nhds 0)
            have h := tendsto_inv_atTop_zero (α := ℝ)
            apply h.congr'
            filter_upwards [Ioi_mem_atTop (0 : ℝ)] with T (hT : 0 < T)
            rw [one_div, abs_of_pos (inv_pos.mpr hT)]
          exact this

  -- ═══════════════════════════════════════════════════════════════
  -- Claim 2 (Rewrite): LHS = Re(∫ F(T) dμ') for large T
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
  -- Combine
  -- ═══════════════════════════════════════════════════════════════
  rw [show ∑' x, μ.real {x} ^ 2 = (∫ p, f p ∂μ').re from eval.symm]
  exact ((Complex.continuous_re.tendsto _).comp dct).congr'
    (rewrite.mono fun T hT => hT.symm)

/-- **Wiener's theorem for continuous measures.** -/
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
