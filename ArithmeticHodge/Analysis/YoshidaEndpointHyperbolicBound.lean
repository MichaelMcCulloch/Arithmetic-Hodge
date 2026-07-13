import ArithmeticHodge.Analysis.HyperbolicKernelRankTwo
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false

open MeasureTheory Real

namespace ArithmeticHodge.Analysis.YoshidaEndpointHyperbolicBound

noncomputable section

/-!
# Structural endpoint hyperbolic loss

The negative rank-one part of the endpoint hyperbolic kernel is controlled by
the exact squared `sinh` weight.  This clean module has no dependency on the
legacy coercivity numerics or certificate hierarchy.
-/

/-- Exact squared `sinh` mass on the scaled centered interval. -/
theorem integral_sinh_scaled_sq
    {a : ℝ} (ha : a ≠ 0) :
    (∫ x : ℝ in -1..1, Real.sinh (a * x / 2) ^ 2) =
      (Real.sinh a - a) / a := by
  have hpoint (x : ℝ) :
      Real.sinh (a * x / 2) ^ 2 =
        (Real.cosh (a * x) - 1) / 2 := by
    have htwo := Real.cosh_two_mul (a * x / 2)
    rw [show 2 * (a * x / 2) = a * x by ring] at htwo
    have hdiff := Real.cosh_sq_sub_sinh_sq (a * x / 2)
    nlinarith
  let F : ℝ → ℝ := fun x ↦ (Real.sinh (a * x) / a - x) / 2
  have hderiv (x : ℝ) :
      HasDerivAt F ((Real.cosh (a * x) - 1) / 2) x := by
    have hax : HasDerivAt (fun y : ℝ ↦ a * y) a x := by
      simpa only [mul_one] using (hasDerivAt_id x).const_mul a
    have hsinh := (Real.hasDerivAt_sinh (a * x)).comp x hax
    dsimp only [F]
    convert (hsinh.div_const a |>.sub (hasDerivAt_id x)).div_const 2 using 1
    field_simp [ha]
  rw [show (fun x : ℝ ↦ Real.sinh (a * x / 2) ^ 2) =
      fun x ↦ (Real.cosh (a * x) - 1) / 2 by
    funext x
    exact hpoint x]
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _hx ↦ hderiv x)
      (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
  rw [hint]
  dsimp only [F]
  rw [mul_one, mul_neg, Real.sinh_neg]
  field_simp [ha]
  ring

/-- Cauchy--Schwarz control of the negative endpoint `sinh` moment. -/
theorem normSq_integral_sinh_scaled_le
    {a : ℝ} (ha : 0 < a) (f : ℝ → ℂ) (hf : Continuous f) :
    Complex.normSq
        (∫ x : ℝ in -1..1, (Real.sinh (a * x / 2) : ℂ) * f x) ≤
      ((Real.sinh a - a) / a) *
        (∫ x : ℝ in -1..1, ‖f x‖ ^ 2) := by
  let I : Set ℝ := Set.Ioc (-1) 1
  let μ : Measure ℝ := volume.restrict I
  let w : ℝ → ℂ := fun x ↦ (Real.sinh (a * x / 2) : ℂ)
  have hwMeas : AEStronglyMeasurable w μ := by
    exact (by fun_prop : Continuous w).aestronglyMeasurable.restrict
  have hw : MemLp w 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hwMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖w x‖ ^ 2)
        (Set.Icc (-1) 1) :=
      (by fun_prop : Continuous (fun x : ℝ ↦ ‖w x‖ ^ 2))
        |>.continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Set.Ioc_subset_Icc_self
  have hfMeas : AEStronglyMeasurable f μ :=
    hf.aestronglyMeasurable.restrict
  have hfLp : MemLp f 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hfMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖f x‖ ^ 2)
        (Set.Icc (-1) 1) :=
      (hf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Set.Ioc_subset_Icc_self
  have hw' : MemLp w (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hw
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hfLp
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (p := 2) (q := 2) (f := w) (g := f) (μ := μ)
    Real.HolderConjugate.two_two hw' hf'
  have hA0 : 0 ≤ ∫ x : ℝ, ‖w x‖ ^ 2 ∂μ :=
    integral_nonneg fun _ ↦ sq_nonneg _
  have hB0 : 0 ≤ ∫ x : ℝ, ‖f x‖ ^ 2 ∂μ :=
    integral_nonneg fun _ ↦ sq_nonneg _
  have hholder' :
      (∫ x : ℝ, ‖w x‖ * ‖f x‖ ∂μ) ≤
        Real.sqrt (∫ x : ℝ, ‖w x‖ ^ 2 ∂μ) *
          Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2 ∂μ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    simpa only [Real.rpow_two] using hholder
  have hnorm :
      ‖∫ x : ℝ in -1..1, w x * f x‖ ≤
        ∫ x : ℝ, ‖w x‖ * ‖f x‖ ∂μ := by
    calc
      ‖∫ x : ℝ in -1..1, w x * f x‖ ≤
          ∫ x : ℝ in -1..1, ‖w x * f x‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by norm_num)
      _ = ∫ x : ℝ in -1..1, ‖w x‖ * ‖f x‖ := by
        apply intervalIntegral.integral_congr
        intro x _
        change ‖w x * f x‖ = ‖w x‖ * ‖f x‖
        rw [norm_mul]
      _ = ∫ x : ℝ, ‖w x‖ * ‖f x‖ ∂μ := by
        rw [intervalIntegral.integral_of_le (by norm_num)]
  have hbound := hnorm.trans hholder'
  have hsq :
      ‖∫ x : ℝ in -1..1, w x * f x‖ ^ 2 ≤
        (∫ x : ℝ, ‖w x‖ ^ 2 ∂μ) *
          (∫ x : ℝ, ‖f x‖ ^ 2 ∂μ) := by
    calc
      ‖∫ x : ℝ in -1..1, w x * f x‖ ^ 2 ≤
          (Real.sqrt (∫ x : ℝ, ‖w x‖ ^ 2 ∂μ) *
            Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2 ∂μ)) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hbound
      _ = (∫ x : ℝ, ‖w x‖ ^ 2 ∂μ) *
          (∫ x : ℝ, ‖f x‖ ^ 2 ∂μ) := by
        rw [mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt hB0]
  have hweight :
      (∫ x : ℝ, ‖w x‖ ^ 2 ∂μ) = (Real.sinh a - a) / a := by
    change (∫ x : ℝ in I, ‖w x‖ ^ 2) = _
    rw [show (∫ x : ℝ in I, ‖w x‖ ^ 2) =
        ∫ x : ℝ in -1..1, Real.sinh (a * x / 2) ^ 2 by
      rw [intervalIntegral.integral_of_le (by norm_num)]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x _
      dsimp only [w]
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]]
    exact integral_sinh_scaled_sq ha.ne'
  have henergy :
      (∫ x : ℝ, ‖f x‖ ^ 2 ∂μ) =
        ∫ x : ℝ in -1..1, ‖f x‖ ^ 2 := by
    change (∫ x : ℝ in I, ‖f x‖ ^ 2) = _
    rw [intervalIntegral.integral_of_le (by norm_num)]
  rw [Complex.normSq_eq_norm_sq]
  dsimp only [w] at hsq ⊢
  rw [hweight, henergy] at hsq
  exact hsq

/-- The endpoint half-width in the scaled Yoshida form. -/
def yoshidaEndpointA : ℝ := Real.log 2 / 2

theorem yoshidaEndpointA_pos : 0 < yoshidaEndpointA := by
  unfold yoshidaEndpointA
  positivity

/-- Exact closed form of the endpoint negative hyperbolic loss. -/
theorem two_mul_sinh_yoshidaEndpointA_sub_eq :
    2 * (Real.sinh yoshidaEndpointA - yoshidaEndpointA) =
      1 / Real.sqrt 2 - Real.log 2 := by
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hexp : Real.exp yoshidaEndpointA = Real.sqrt 2 := by
    have hsqExp : Real.exp yoshidaEndpointA ^ 2 = 2 := by
      rw [pow_two, ← Real.exp_add]
      rw [show yoshidaEndpointA + yoshidaEndpointA = Real.log 2 by
        unfold yoshidaEndpointA
        ring]
      rw [Real.exp_log (by norm_num)]
    nlinarith [Real.exp_pos yoshidaEndpointA]
  rw [Real.sinh_eq, hexp, Real.exp_neg, hexp]
  unfold yoshidaEndpointA
  field_simp [hsqrtPos.ne']
  nlinarith

/-- The endpoint rank-two hyperbolic contribution on `[-1,1]`. -/
def yoshidaEndpointHyperbolicQuadratic (f : ℝ → ℂ) : ℝ :=
  2 * yoshidaEndpointA *
    (Complex.normSq
        (∫ x : ℝ in -1..1,
          (Real.cosh (yoshidaEndpointA * x / 2) : ℂ) * f x) -
      Complex.normSq
        (∫ x : ℝ in -1..1,
          (Real.sinh (yoshidaEndpointA * x / 2) : ℂ) * f x))

/-- Structural lower bound for the endpoint hyperbolic rank-two term. -/
theorem yoshidaEndpointHyperbolicQuadratic_lower
    (f : ℝ → ℂ) (hf : Continuous f) :
    -(1 / Real.sqrt 2 - Real.log 2) *
        (∫ x : ℝ in -1..1, ‖f x‖ ^ 2) ≤
      yoshidaEndpointHyperbolicQuadratic f := by
  let E : ℝ := ∫ x : ℝ in -1..1, ‖f x‖ ^ 2
  let C : ℝ := Complex.normSq
    (∫ x : ℝ in -1..1,
      (Real.cosh (yoshidaEndpointA * x / 2) : ℂ) * f x)
  let S : ℝ := Complex.normSq
    (∫ x : ℝ in -1..1,
      (Real.sinh (yoshidaEndpointA * x / 2) : ℂ) * f x)
  have hS : S ≤
      ((Real.sinh yoshidaEndpointA - yoshidaEndpointA) /
        yoshidaEndpointA) * E := by
    simpa only [S, E] using normSq_integral_sinh_scaled_le
      yoshidaEndpointA_pos f hf
  have hscaled :
      2 * yoshidaEndpointA *
          ((Real.sinh yoshidaEndpointA - yoshidaEndpointA) /
            yoshidaEndpointA) =
        1 / Real.sqrt 2 - Real.log 2 := by
    calc
      _ = 2 * (Real.sinh yoshidaEndpointA - yoshidaEndpointA) := by
        field_simp [yoshidaEndpointA_pos.ne']
      _ = _ := two_mul_sinh_yoshidaEndpointA_sub_eq
  have hloss :
      2 * yoshidaEndpointA * S ≤
        (1 / Real.sqrt 2 - Real.log 2) * E := by
    calc
      2 * yoshidaEndpointA * S ≤
          2 * yoshidaEndpointA *
            (((Real.sinh yoshidaEndpointA - yoshidaEndpointA) /
              yoshidaEndpointA) * E) :=
        mul_le_mul_of_nonneg_left hS
          (mul_nonneg (by norm_num) yoshidaEndpointA_pos.le)
      _ = _ := by rw [← mul_assoc, hscaled]
  have hC : 0 ≤ 2 * yoshidaEndpointA * C :=
    mul_nonneg
      (mul_nonneg (by norm_num) yoshidaEndpointA_pos.le)
      (Complex.normSq_nonneg _)
  unfold yoshidaEndpointHyperbolicQuadratic
  change -(1 / Real.sqrt 2 - Real.log 2) * E ≤
    2 * yoshidaEndpointA * (C - S)
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaEndpointHyperbolicBound
