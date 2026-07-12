import ArithmeticHodge.Analysis.YoshidaClippedParityOrthogonality
import ArithmeticHodge.Analysis.YoshidaClippedCircleBridge
import ArithmeticHodge.Analysis.YoshidaSectionSixAnalytic
import ArithmeticHodge.Analysis.YoshidaWeightedTailBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.MeanInequalities

set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaOddPolarBound

open YoshidaClippedCircleBridge
open YoshidaCoercivityNumerics
open YoshidaSectionSixAnalytic
open YoshidaWeightedTailBounds

/-!
# Exact odd polar loss

For pointwise-odd clipped data, the two polar samples are negatives of one
another and the negative polar sample is exactly integration against
`sinh (x / 2)`.  Cauchy--Schwarz therefore bounds the polar loss by the
`L²` mass of that weight.  At `a = log 2 / 2`, the latter evaluates exactly to
`1 / sqrt 2 - log 2`, which is the polar constant used in Yoshida's Section 6.
-/

theorem integral_sinh_half_sq (a : ℝ) :
    (∫ x : ℝ in -a..a, Real.sinh (x / 2) ^ 2) =
      Real.sinh a - a := by
  have hpoint (x : ℝ) :
      Real.sinh (x / 2) ^ 2 = (Real.cosh x - 1) / 2 := by
    have htwo := Real.cosh_two_mul (x / 2)
    rw [show 2 * (x / 2) = x by ring] at htwo
    have hdiff := Real.cosh_sq_sub_sinh_sq (x / 2)
    nlinarith
  rw [show (fun x : ℝ ↦ Real.sinh (x / 2) ^ 2) =
      fun x ↦ (Real.cosh x - 1) / 2 by
    funext x
    exact hpoint x]
  have hderiv : ∀ x ∈ Set.uIcc (-a) a,
      HasDerivAt (fun y : ℝ ↦ (Real.sinh y - y) / 2)
        ((Real.cosh x - 1) / 2) x := by
    intro x _
    convert ((Real.hasDerivAt_sinh x).sub (hasDerivAt_id x)).div_const 2 using 1
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (Continuous.intervalIntegrable (by fun_prop) (-a) a)
  rw [hint, Real.sinh_neg]
  ring

theorem negativePolar_eq_sinh_integral_of_odd
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a)
    (hodd : ∀ x : ℝ, f (-x) = -f x) :
    yoshidaNegativePolarLinear a ha f =
      ∫ x : ℝ in -a..a, (Real.sinh (x / 2) : ℂ) * f x := by
  have hpolar := yoshidaPositivePolar_odd_eq_neg_negative ha f hodd
  have hplusInt : IntervalIntegrable (fun x : ℝ ↦
      Complex.exp (-((1 / 2 : ℂ) * (x : ℂ))) * f x)
      volume (-a) a := by
    exact ((by fun_prop : Continuous (fun x : ℝ ↦
      Complex.exp (-((1 / 2 : ℂ) * (x : ℂ))))).continuousOn.mul
        f.property.1.continuousOn).intervalIntegrable_of_Icc (by linarith)
  have hminusInt : IntervalIntegrable (fun x : ℝ ↦
      Complex.exp (-((-1 / 2 : ℂ) * (x : ℂ))) * f x)
      volume (-a) a := by
    exact ((by fun_prop : Continuous (fun x : ℝ ↦
      Complex.exp (-((-1 / 2 : ℂ) * (x : ℂ))))).continuousOn.mul
        f.property.1.continuousOn).intervalIntegrable_of_Icc (by linarith)
  calc
    yoshidaNegativePolarLinear a ha f =
        (1 / 2 : ℂ) *
          (yoshidaNegativePolarLinear a ha f -
            yoshidaPositivePolarLinear a ha f) := by rw [hpolar]; ring
    _ = (1 / 2 : ℂ) *
        ((∫ x : ℝ in -a..a,
            Complex.exp (-((-1 / 2 : ℂ) * (x : ℂ))) * f x) -
          ∫ x : ℝ in -a..a,
            Complex.exp (-((1 / 2 : ℂ) * (x : ℂ))) * f x) := rfl
    _ = (1 / 2 : ℂ) *
        (∫ x : ℝ in -a..a,
          (Complex.exp (-((-1 / 2 : ℂ) * (x : ℂ))) * f x -
            Complex.exp (-((1 / 2 : ℂ) * (x : ℂ))) * f x)) := by
      rw [intervalIntegral.integral_sub hminusInt hplusInt]
    _ = ∫ x : ℝ in -a..a,
        (1 / 2 : ℂ) *
          (Complex.exp (-((-1 / 2 : ℂ) * (x : ℂ))) * f x -
            Complex.exp (-((1 / 2 : ℂ) * (x : ℂ))) * f x) :=
      (intervalIntegral.integral_const_mul (1 / 2 : ℂ)
        (fun x : ℝ ↦
          Complex.exp (-((-1 / 2 : ℂ) * (x : ℂ))) * f x -
            Complex.exp (-((1 / 2 : ℂ) * (x : ℂ))) * f x)).symm
    _ = ∫ x : ℝ in -a..a, (Real.sinh (x / 2) : ℂ) * f x := by
      apply intervalIntegral.integral_congr
      intro x _
      change (1 / 2 : ℂ) *
          (Complex.exp (-((-1 / 2 : ℂ) * (x : ℂ))) * f x -
            Complex.exp (-((1 / 2 : ℂ) * (x : ℂ))) * f x) =
        (Real.sinh (x / 2) : ℂ) * f x
      rw [show -((-1 / 2 : ℂ) * (x : ℂ)) = ((x / 2 : ℝ) : ℂ) by
        push_cast
        ring]
      rw [show -((1 / 2 : ℂ) * (x : ℂ)) = ((-(x / 2) : ℝ) : ℂ) by
        push_cast
        ring]
      push_cast
      rw [← sub_mul, ← Complex.two_sinh]
      ring

theorem normSq_sinh_integral_le
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a) :
    Complex.normSq
        (∫ x : ℝ in -a..a, (Real.sinh (x / 2) : ℂ) * f x) ≤
      (Real.sinh a - a) *
        (∫ x : ℝ in -a..a, ‖f x‖ ^ 2) := by
  let I : Set ℝ := Set.Ioc (-a) a
  let μ : Measure ℝ := volume.restrict I
  let w : ℝ → ℂ := fun x ↦ (Real.sinh (x / 2) : ℂ)
  have hwMeas : AEStronglyMeasurable w μ := by
    exact (by fun_prop : Continuous w).aestronglyMeasurable.restrict
  have hw : MemLp w 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hwMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖w x‖ ^ 2)
        (Set.Icc (-a) a) :=
      (by fun_prop : Continuous (fun x : ℝ ↦ ‖w x‖ ^ 2))
        |>.continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have hf : MemLp (fun x : ℝ ↦ f x) 2 μ := by
    simpa only [μ, I] using yoshidaClippedSmooth_memLp_two f
  have hw' : MemLp w (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hw
  have hf' : MemLp (fun x : ℝ ↦ f x) (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hf
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (p := 2) (q := 2) (f := w) (g := fun x : ℝ ↦ f x) (μ := μ)
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
      ‖∫ x : ℝ in -a..a, w x * f x‖ ≤
        ∫ x : ℝ, ‖w x‖ * ‖f x‖ ∂μ := by
    calc
      ‖∫ x : ℝ in -a..a, w x * f x‖ ≤
          ∫ x : ℝ in -a..a, ‖w x * f x‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by linarith)
      _ = ∫ x : ℝ in -a..a, ‖w x‖ * ‖f x‖ := by
        apply intervalIntegral.integral_congr
        intro x _
        change ‖w x * f x‖ = ‖w x‖ * ‖f x‖
        rw [norm_mul]
      _ = ∫ x : ℝ, ‖w x‖ * ‖f x‖ ∂μ := by
        rw [intervalIntegral.integral_of_le (by linarith)]
  have hbound := hnorm.trans hholder'
  have hsq :
      ‖∫ x : ℝ in -a..a, w x * f x‖ ^ 2 ≤
        (∫ x : ℝ, ‖w x‖ ^ 2 ∂μ) *
          (∫ x : ℝ, ‖f x‖ ^ 2 ∂μ) := by
    calc
      ‖∫ x : ℝ in -a..a, w x * f x‖ ^ 2 ≤
          (Real.sqrt (∫ x : ℝ, ‖w x‖ ^ 2 ∂μ) *
            Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2 ∂μ)) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hbound
      _ = (∫ x : ℝ, ‖w x‖ ^ 2 ∂μ) *
          (∫ x : ℝ, ‖f x‖ ^ 2 ∂μ) := by
        rw [mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt hB0]
  have hweight : (∫ x : ℝ, ‖w x‖ ^ 2 ∂μ) = Real.sinh a - a := by
    change (∫ x : ℝ in I, ‖w x‖ ^ 2) = _
    rw [show (∫ x : ℝ in I, ‖w x‖ ^ 2) =
        ∫ x : ℝ in -a..a, Real.sinh (x / 2) ^ 2 by
      rw [intervalIntegral.integral_of_le (by linarith)]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x _
      dsimp only [w]
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]]
    exact integral_sinh_half_sq a
  have henergy : (∫ x : ℝ, ‖f x‖ ^ 2 ∂μ) =
      ∫ x : ℝ in -a..a, ‖f x‖ ^ 2 := by
    change (∫ x : ℝ in I, ‖f x‖ ^ 2) = _
    rw [intervalIntegral.integral_of_le (by linarith)]
  rw [Complex.normSq_eq_norm_sq]
  dsimp only [w] at hsq ⊢
  rw [hweight, henergy] at hsq
  exact hsq

theorem clippedPolarEnergy_odd_lower
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a)
    (hodd : ∀ x : ℝ, f (-x) = -f x) :
    -2 * (Real.sinh a - a) *
        (∫ x : ℝ in -a..a, ‖f x‖ ^ 2) ≤
      clippedPolarEnergy a ha f := by
  have hpolar := yoshidaPositivePolar_odd_eq_neg_negative ha f hodd
  have hsinh := negativePolar_eq_sinh_integral_of_odd ha f hodd
  have hbound := normSq_sinh_integral_le ha f
  rw [← hsinh] at hbound
  unfold clippedPolarEnergy
  rw [hpolar]
  have hvalue :
      2 * (star (-yoshidaNegativePolarLinear a ha f) *
        yoshidaNegativePolarLinear a ha f).re =
        -2 * Complex.normSq (yoshidaNegativePolarLinear a ha f) := by
    simp [Complex.normSq_apply, Complex.mul_re]
    ring
  rw [hvalue]
  nlinarith

theorem two_mul_sinh_yoshidaA_sub_eq :
    2 * (Real.sinh yoshidaA - yoshidaA) =
      1 / Real.sqrt 2 - Real.log 2 := by
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hexp : Real.exp yoshidaA = Real.sqrt 2 := by
    have hsqExp : Real.exp yoshidaA ^ 2 = 2 := by
      rw [pow_two, ← Real.exp_add]
      rw [show yoshidaA + yoshidaA = Real.log 2 by
        unfold yoshidaA
        ring]
      rw [Real.exp_log (by norm_num)]
    nlinarith [Real.exp_pos yoshidaA]
  rw [Real.sinh_eq, hexp, Real.exp_neg, hexp]
  unfold yoshidaA
  field_simp [hsqrtPos.ne']
  nlinarith

/-- The exact Section 6 polar lower bound for unit-energy pointwise-odd data
on Yoshida's ratio-two interval. -/
theorem odd_polar_section6_lower_bound
    (f : YoshidaClippedSmooth yoshidaA)
    (hodd : ∀ x : ℝ, f (-x) = -f x)
    (henergy :
      (∫ x : ℝ in -yoshidaA..yoshidaA, ‖f x‖ ^ 2) = 1) :
    -(1 / Real.sqrt 2 - Real.log 2) ≤
      clippedPolarEnergy yoshidaA yoshidaA_pos f := by
  have h := clippedPolarEnergy_odd_lower yoshidaA_pos f hodd
  rw [henergy, mul_one] at h
  nlinarith [two_mul_sinh_yoshidaA_sub_eq]

end ArithmeticHodge.Analysis.YoshidaOddPolarBound
