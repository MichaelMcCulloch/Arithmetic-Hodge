import ArithmeticHodge.Analysis.YoshidaClippedDomain
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Yoshida's clipped local critical form

This module constructs the archimedean local critical form on
`YoshidaClippedSmooth a`. The clipped functions may jump at the endpoints,
so the integration-by-parts identity retains both boundary terms and uses
`derivWithin` on `Set.Icc (-a) a`.

The critical cross integral is shown to be unconditionally integrable on this
algebraic carrier, the resulting form is Hermitian, and it agrees with the
smooth Bombieri local critical form on supported critical pullbacks. No
positivity, coercivity, bounded extension to all `CircleL2`, or all-support
claim is made here.
-/

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ContDiff

namespace ArithmeticHodge.Analysis

noncomputable section

local instance : IsBoundedSMul ℝ ℂ :=
  NormedSpace.toIsBoundedSMul

/-- The one-sided interval derivative of a clipped smooth function. -/
def yoshidaClippedDeriv
    (a : ℝ) (f : YoshidaClippedSmooth a) : ℝ → ℂ :=
  derivWithin (f : ℝ → ℂ) (Set.Icc (-a) a)

private theorem yoshidaClipped_hasDerivWithinAt
    {a : ℝ} (f : YoshidaClippedSmooth a)
    {x : ℝ} (hx : x ∈ Set.Icc (-a) a) :
    HasDerivWithinAt (f : ℝ → ℂ) (yoshidaClippedDeriv a f x)
      (Set.Icc (-a) a) x := by
  exact ((f.property.1.differentiableOn (by simp)) x hx).hasDerivWithinAt

private theorem yoshidaCriticalWeight_hasDerivAt
    (v x : ℝ) :
    HasDerivAt
      (fun t : ℝ ↦ Complex.exp (-((v : ℂ) * Complex.I * (t : ℂ))))
      (-((v : ℂ) * Complex.I) *
        Complex.exp (-((v : ℂ) * Complex.I * (x : ℂ)))) x := by
  let c : ℂ := -((v : ℂ) * Complex.I)
  have hinner : HasFDerivAt (fun t : ℝ ↦ c * (t : ℂ))
      (c • Complex.ofRealCLM) x :=
    Complex.ofRealCLM.hasFDerivAt.const_mul c
  have hexp := hinner.cexp
  have hderivC : HasDerivAt
      (fun t : ℝ ↦ Complex.exp (c * (t : ℂ)))
      (c * Complex.exp (c * (x : ℂ))) x := by
    convert hexp.differentiableAt.hasDerivAt using 1
    symm
    change (fderiv ℝ (fun t : ℝ ↦ Complex.exp (c * (t : ℂ))) x) 1 = _
    have hfderiv :
        fderiv ℝ (fun t : ℝ ↦ Complex.exp (c * (t : ℂ))) x =
          Complex.exp (c * (x : ℂ)) • c • Complex.ofRealCLM := by
      simpa using hexp.fderiv
    rw [hfderiv]
    simp
    ring
  simpa [c] using hderivC

private theorem yoshidaClippedDeriv_intervalIntegrable
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a) :
    IntervalIntegrable (yoshidaClippedDeriv a f) volume (-a) a := by
  have hcont : ContinuousOn (yoshidaClippedDeriv a f) (Set.Icc (-a) a) := by
    exact f.property.1.continuousOn_derivWithin
      (uniqueDiffOn_Icc (by linarith : -a < a)) (by simp)
  exact hcont.intervalIntegrable_of_Icc (by linarith)

private theorem yoshidaCriticalWeight_intervalIntegrable
    {a v : ℝ} (ha : 0 < a) :
    IntervalIntegrable
      (fun x : ℝ ↦ Complex.exp (-((v : ℂ) * Complex.I * (x : ℂ))))
      volume (-a) a := by
  exact (by fun_prop : Continuous (fun x : ℝ ↦
    Complex.exp (-((v : ℂ) * Complex.I * (x : ℂ)))))
    |>.continuousOn.intervalIntegrable_of_Icc (by linarith)

/-- Exact endpoint-aware integration by parts for the critical sample.
The identity is valid at `v = 0`; division by `v` occurs only in the decay
estimate below. -/
theorem yoshidaCriticalSample_mul_neg_mul_I_eq_boundary_sub_derivIntegral
    {a : ℝ} (ha : 0 < a) (v : ℝ) (f : YoshidaClippedSmooth a) :
    yoshidaCriticalSampleLinear a ha v f * (-((v : ℂ) * Complex.I)) =
      f a * Complex.exp (-((v : ℂ) * Complex.I * (a : ℂ))) -
        f (-a) * Complex.exp (-((v : ℂ) * Complex.I * ((-a : ℝ) : ℂ))) -
      ∫ x : ℝ in -a..a,
        yoshidaClippedDeriv a f x *
          Complex.exp (-((v : ℂ) * Complex.I * (x : ℂ))) := by
  have hfderiv : ∀ x ∈ Set.uIcc (-a) a,
      HasDerivWithinAt (f : ℝ → ℂ) (yoshidaClippedDeriv a f x)
        (Set.uIcc (-a) a) x := by
    intro x hx
    rw [uIcc_of_le (by linarith : -a ≤ a)] at hx ⊢
    exact yoshidaClipped_hasDerivWithinAt f hx
  have hwderiv : ∀ x ∈ Set.uIcc (-a) a,
      HasDerivWithinAt
        (fun t : ℝ ↦ Complex.exp (-((v : ℂ) * Complex.I * (t : ℂ))))
        (-((v : ℂ) * Complex.I) *
          Complex.exp (-((v : ℂ) * Complex.I * (x : ℂ))))
        (Set.uIcc (-a) a) x := by
    intro x _
    exact (yoshidaCriticalWeight_hasDerivAt v x).hasDerivWithinAt
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    hfderiv hwderiv (yoshidaClippedDeriv_intervalIntegrable ha f)
      ((yoshidaCriticalWeight_intervalIntegrable ha).const_mul
        (-((v : ℂ) * Complex.I)))
  rw [yoshidaCriticalSampleLinear, yoshidaCenteredLaplaceLinear_apply]
  change
    (∫ x : ℝ in -a..a,
      Complex.exp (-((v : ℂ) * Complex.I * (x : ℂ))) * f x) *
        (-((v : ℂ) * Complex.I)) = _
  calc
    (∫ x : ℝ in -a..a,
        Complex.exp (-((v : ℂ) * Complex.I * (x : ℂ))) * f x) *
          (-((v : ℂ) * Complex.I)) =
        ∫ x : ℝ in -a..a,
          f x * (-((v : ℂ) * Complex.I) *
            Complex.exp (-((v : ℂ) * Complex.I * (x : ℂ)))) := by
      calc
        (∫ x : ℝ in -a..a,
            Complex.exp (-((v : ℂ) * Complex.I * (x : ℂ))) * f x) *
              (-((v : ℂ) * Complex.I)) =
            ∫ x : ℝ in -a..a,
              (Complex.exp (-((v : ℂ) * Complex.I * (x : ℂ))) * f x) *
                (-((v : ℂ) * Complex.I)) :=
          (intervalIntegral.integral_mul_const
            (-((v : ℂ) * Complex.I))
            (fun x : ℝ ↦
              Complex.exp (-((v : ℂ) * Complex.I * (x : ℂ))) * f x)).symm
        _ = _ := by
          apply intervalIntegral.integral_congr
          intro x _
          ring
    _ = _ := hibp

/-- Boundary values plus the interval `L¹` norm of the one-sided derivative. -/
def yoshidaCriticalDecayConstant
    (a : ℝ) (f : YoshidaClippedSmooth a) : ℝ :=
  ‖f a‖ + ‖f (-a)‖ +
    ∫ x : ℝ in -a..a, ‖yoshidaClippedDeriv a f x‖

theorem yoshidaCriticalDecayConstant_nonneg
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a) :
    0 ≤ yoshidaCriticalDecayConstant a f := by
  unfold yoshidaCriticalDecayConstant
  have hint : 0 ≤ ∫ x : ℝ in -a..a, ‖yoshidaClippedDeriv a f x‖ :=
    intervalIntegral.integral_nonneg (by linarith) fun _ _ ↦ norm_nonneg _
  positivity

/-- The endpoint-aware `O(1 / |v|)` bound for nonzero critical frequency. -/
theorem yoshidaCriticalSample_norm_le_inv_abs
    {a : ℝ} (ha : 0 < a) (v : ℝ) (hv : v ≠ 0)
    (f : YoshidaClippedSmooth a) :
    ‖yoshidaCriticalSampleLinear a ha v f‖ ≤
      yoshidaCriticalDecayConstant a f / |v| := by
  have habs : 0 < |v| := abs_pos.mpr hv
  apply (le_div_iff₀ habs).2
  have hformula :=
    yoshidaCriticalSample_mul_neg_mul_I_eq_boundary_sub_derivIntegral
      ha v f
  have hnormformula := congrArg norm hformula
  have hleft :
      ‖yoshidaCriticalSampleLinear a ha v f *
          (-((v : ℂ) * Complex.I))‖ =
        ‖yoshidaCriticalSampleLinear a ha v f‖ * |v| := by
    rw [norm_mul, norm_neg, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, norm_I, mul_one]
  rw [hleft] at hnormformula
  rw [hnormformula]
  have hintegral :
      ‖∫ x : ℝ in -a..a,
          yoshidaClippedDeriv a f x *
            Complex.exp (-((v : ℂ) * Complex.I * (x : ℂ)))‖ ≤
        ∫ x : ℝ in -a..a, ‖yoshidaClippedDeriv a f x‖ := by
    calc
      ‖∫ x : ℝ in -a..a,
          yoshidaClippedDeriv a f x *
            Complex.exp (-((v : ℂ) * Complex.I * (x : ℂ)))‖ ≤
          ∫ x : ℝ in -a..a,
            ‖yoshidaClippedDeriv a f x *
              Complex.exp (-((v : ℂ) * Complex.I * (x : ℂ)))‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by linarith)
      _ = ∫ x : ℝ in -a..a, ‖yoshidaClippedDeriv a f x‖ := by
        apply intervalIntegral.integral_congr
        intro x _
        change ‖yoshidaClippedDeriv a f x *
          Complex.exp (-((v : ℂ) * Complex.I * (x : ℂ)))‖ =
            ‖yoshidaClippedDeriv a f x‖
        rw [norm_mul, Complex.norm_exp]
        simp
  calc
    ‖f a * Complex.exp (-((v : ℂ) * Complex.I * (a : ℂ))) -
        f (-a) * Complex.exp (-((v : ℂ) * Complex.I * ((-a : ℝ) : ℂ))) -
        ∫ x : ℝ in -a..a,
          yoshidaClippedDeriv a f x *
            Complex.exp (-((v : ℂ) * Complex.I * (x : ℂ)))‖ ≤
      ‖f a * Complex.exp (-((v : ℂ) * Complex.I * (a : ℂ))) -
        f (-a) * Complex.exp (-((v : ℂ) * Complex.I * ((-a : ℝ) : ℂ)))‖ +
        ‖∫ x : ℝ in -a..a,
          yoshidaClippedDeriv a f x *
            Complex.exp (-((v : ℂ) * Complex.I * (x : ℂ)))‖ :=
      norm_sub_le _ _
    _ ≤
      (‖f a * Complex.exp (-((v : ℂ) * Complex.I * (a : ℂ)))‖ +
        ‖f (-a) * Complex.exp
          (-((v : ℂ) * Complex.I * ((-a : ℝ) : ℂ)))‖) +
        ∫ x : ℝ in -a..a, ‖yoshidaClippedDeriv a f x‖ := by
      gcongr
      exact norm_sub_le _ _
    _ = yoshidaCriticalDecayConstant a f := by
      simp [yoshidaCriticalDecayConstant, Complex.norm_exp]

private theorem continuous_digamma_quarter_vertical :
    Continuous (fun v : ℝ ↦
      Complex.digamma ((1 / 4 : ℝ) + (v / 2) * Complex.I)) := by
  rw [continuous_iff_continuousAt]
  intro v
  let z : ℂ := (1 / 4 : ℝ) + (v / 2) * Complex.I
  have hzre : 0 < z.re := by simp [z]
  have havoid : ∀ m : ℕ, z ≠ -m := by
    intro m hm
    have hre := congrArg Complex.re hm
    simp [z] at hre
    have hmnonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    norm_num at hre
    linarith
  have hGammaDiff : DifferentiableAt ℂ Complex.Gamma z :=
    Complex.differentiableAt_Gamma z havoid
  have hGammaAnalytic : AnalyticAt ℂ Complex.Gamma z :=
    (Meromorphic.Gamma z).analyticAt hGammaDiff.continuousAt
  have hdigammaAnalytic : AnalyticAt ℂ Complex.digamma z := by
    rw [Complex.digamma_def]
    exact hGammaAnalytic.deriv.div hGammaAnalytic
      (Complex.Gamma_ne_zero havoid)
  exact hdigammaAnalytic.continuousAt.comp_of_eq
    (by fun_prop : ContinuousAt
      (fun v : ℝ ↦ ((1 / 4 : ℝ) + (v / 2) * Complex.I : ℂ)) v) rfl

/-- Continuity of the real-valued Bombieri critical kernel. -/
theorem continuous_bombieriLocalCriticalKernel :
    Continuous
      MultiplicativeWeil.bombieriLocalCriticalKernel := by
  unfold MultiplicativeWeil.bombieriLocalCriticalKernel
  exact Complex.continuous_ofReal.comp
    ((continuous_re.comp continuous_digamma_quarter_vertical).sub
      continuous_const)

/-- A global logarithmic norm bound for the Bombieri critical kernel. -/
theorem exists_bombieriLocalCriticalKernel_log_norm_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ v : ℝ,
      ‖MultiplicativeWeil.bombieriLocalCriticalKernel v‖ ≤
        C * (1 + Real.log (max 1 |v|)) := by
  obtain ⟨D, hDpos, hD⟩ :=
    digamma_growth_bound (1 / 4 : ℝ) (1 / 4 : ℝ)
  obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_Icc : IsCompact (Set.Icc (-4 : ℝ) 4))
    continuous_bombieriLocalCriticalKernel.continuousOn
  let C : ℝ := D + |Real.log Real.pi| + |M| + 1
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hCpos, ?_⟩
  intro v
  by_cases hv : |v| ≤ 4
  · have hvIcc : v ∈ Set.Icc (-4 : ℝ) 4 := (abs_le.mp hv)
    have hkernel := hM v hvIcc
    have hlognonneg : 0 ≤ Real.log (max 1 |v|) :=
      Real.log_nonneg (le_max_left 1 |v|)
    have hMle : M ≤ C := by
      dsimp [C]
      nlinarith [le_abs_self M, abs_nonneg (Real.log Real.pi), hDpos]
    nlinarith
  · have hv4 : 4 < |v| := lt_of_not_ge hv
    let z : ℂ := (1 / 4 : ℝ) + (v / 2) * Complex.I
    have hzre : z.re = (1 / 4 : ℝ) := by simp [z]
    have hzim : |z.im| = |v| / 2 := by
      simp [z, abs_div]
    have hzheight : 2 ≤ |z.im| := by rw [hzim]; linarith
    have hpsi : ‖Complex.digamma z‖ ≤
        D * Real.log |z.im| := hD z (by rw [hzre]) (by rw [hzre]) hzheight
    have hlogmono : Real.log |z.im| ≤ Real.log |v| := by
      rw [hzim]
      apply Real.log_le_log (by positivity)
      linarith [abs_nonneg v]
    have hpsi' : ‖Complex.digamma z‖ ≤
        D * Real.log |v| :=
      hpsi.trans (mul_le_mul_of_nonneg_left hlogmono hDpos.le)
    have hlognonneg : 0 ≤ Real.log |v| :=
      Real.log_nonneg (by linarith : 1 ≤ |v|)
    rw [show max 1 |v| = |v| by exact max_eq_right (by linarith)]
    rw [MultiplicativeWeil.bombieriLocalCriticalKernel,
      Complex.norm_real, Real.norm_eq_abs]
    have hreal : |(Complex.digamma z).re| ≤ ‖Complex.digamma z‖ :=
      Complex.abs_re_le_norm _
    have hraw : |(Complex.digamma z).re - Real.log Real.pi| ≤
        D * Real.log |v| + |Real.log Real.pi| := by
      calc
        |(Complex.digamma z).re - Real.log Real.pi| ≤
            |(Complex.digamma z).re| + |Real.log Real.pi| := abs_sub _ _
        _ ≤ ‖Complex.digamma z‖ + |Real.log Real.pi| := by gcongr
        _ ≤ D * Real.log |v| + |Real.log Real.pi| := by gcongr
    change |(Complex.digamma z).re - Real.log Real.pi| ≤ _
    calc
      |(Complex.digamma z).re - Real.log Real.pi| ≤
          D * Real.log |v| + |Real.log Real.pi| := hraw
      _ ≤ C * (1 + Real.log |v|) := by
        dsimp [C]
        nlinarith [abs_nonneg (Real.log Real.pi), abs_nonneg M]

/-- The Bombieri kernel multiplied by two clipped critical samples. -/
def yoshidaClippedCriticalCrossIntegrand
    (a : ℝ) (ha : 0 < a)
    (f g : YoshidaClippedSmooth a) (v : ℝ) : ℂ :=
  MultiplicativeWeil.bombieriLocalCriticalKernel v *
    star (yoshidaCriticalSampleLinear a ha v f) *
    yoshidaCriticalSampleLinear a ha v g

/-- The clipped critical sample is the Fourier transform at frequency
`v / (2 * π)`. Endpoint jumps are harmless because only integrability is
needed for this identity and the ensuing continuity argument. -/
theorem yoshidaCriticalSample_eq_fourier
    {a : ℝ} (ha : 0 < a) (v : ℝ) (f : YoshidaClippedSmooth a) :
    yoshidaCriticalSampleLinear a ha v f =
      FourierTransform.fourier (f : ℝ → ℂ)
        (v / (2 * Real.pi)) := by
  rw [yoshidaCriticalSampleLinear, yoshidaCenteredLaplaceLinear_apply,
    Real.fourier_real_eq_integral_exp_smul]
  change
    (∫ x : ℝ in -a..a,
      Complex.exp (-((v : ℂ) * Complex.I * (x : ℂ))) * f x) =
    ∫ x : ℝ,
      Complex.exp
        (((-2 * Real.pi * x * (v / (2 * Real.pi)) : ℝ) : ℂ) *
          Complex.I) * f x
  rw [intervalIntegral.integral_of_le (by linarith),
    ← integral_Icc_eq_integral_Ioc]
  calc
    (∫ x : ℝ in Set.Icc (-a) a,
        Complex.exp (-((v : ℂ) * Complex.I * (x : ℂ))) * f x) =
      ∫ x : ℝ in Set.Icc (-a) a,
        Complex.exp
          (((-2 * Real.pi * x * (v / (2 * Real.pi)) : ℝ) : ℂ) *
            Complex.I) * f x := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x _
      push_cast
      field_simp [Real.pi_ne_zero]
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx ↦ by simp [yoshidaClippedSmooth_eq_zero_outside f hx])

private theorem continuous_yoshidaCriticalSample
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a) :
    Continuous (fun v : ℝ ↦ yoshidaCriticalSampleLinear a ha v f) := by
  have hfint : Integrable (f : ℝ → ℂ) :=
    f.property.1.continuousOn.integrableOn_Icc
      |>.integrable_of_forall_notMem_eq_zero
        (fun x hx ↦ yoshidaClippedSmooth_eq_zero_outside f hx)
  have hfourier : Continuous (FourierTransform.fourier (f : ℝ → ℂ)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      continuous_inner hfint
  have heq : (fun v : ℝ ↦ yoshidaCriticalSampleLinear a ha v f) =
      fun v : ℝ ↦ FourierTransform.fourier (f : ℝ → ℂ)
        (v / (2 * Real.pi)) := by
    funext v
    exact yoshidaCriticalSample_eq_fourier ha v f
  rw [heq]
  exact hfourier.comp (by fun_prop)

theorem continuous_yoshidaClippedCriticalCrossIntegrand
    {a : ℝ} (ha : 0 < a) (f g : YoshidaClippedSmooth a) :
    Continuous (yoshidaClippedCriticalCrossIntegrand a ha f g) := by
  exact continuous_bombieriLocalCriticalKernel.mul
    (continuous_yoshidaCriticalSample ha f).star |>.mul
      (continuous_yoshidaCriticalSample ha g)

private theorem integrable_max_one_abs_rpow_neg_three_halves :
    Integrable (fun v : ℝ ↦
      (max 1 |v|) ^ (-(3 / 2 : ℝ))) := by
  let r : ℝ := 3 / 2
  have hr : (1 : ℝ) < r := by norm_num [r]
  have hbase : Integrable (fun v : ℝ ↦
      (1 + ‖v‖) ^ (-r)) :=
    integrable_one_add_norm (E := ℝ) (r := r) (by simpa using hr)
  have hmajor := hbase.const_mul (2 ^ r)
  apply hmajor.mono'
  · exact ((continuous_const.max continuous_abs).rpow_const
      (fun v ↦ Or.inl (ne_of_gt
        (lt_of_lt_of_le zero_lt_one (le_max_left 1 |v|)))))
      |>.aestronglyMeasurable
  · filter_upwards with v
    let m : ℝ := max 1 |v|
    have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one (le_max_left 1 |v|)
    have hcompare : 1 + |v| ≤ 2 * m := by
      dsimp [m]
      nlinarith [le_max_left (1 : ℝ) |v|, le_max_right (1 : ℝ) |v|]
    have hneg : -r ≤ 0 := by norm_num [r]
    have hrpow : (2 * m) ^ (-r) ≤ (1 + |v|) ^ (-r) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hcompare hneg
    have heq : m ^ (-r) = 2 ^ r * (2 * m) ^ (-r) := by
      rw [Real.mul_rpow (by positivity) hmpos.le]
      rw [← mul_assoc, ← Real.rpow_add zero_lt_two]
      norm_num
    rw [Real.norm_eq_abs]
    change |m ^ (-r)| ≤ 2 ^ r * (1 + |v|) ^ (-r)
    rw [abs_of_nonneg (Real.rpow_nonneg hmpos.le _)]
    rw [heq]
    exact mul_le_mul_of_nonneg_left hrpow (Real.rpow_nonneg (by positivity) _)

private theorem yoshidaClippedCriticalCrossIntegrand_norm_le_tail
    {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (hkernel : ∀ v : ℝ,
      ‖MultiplicativeWeil.bombieriLocalCriticalKernel v‖ ≤
        C * (1 + Real.log (max 1 |v|)))
    (f g : YoshidaClippedSmooth a) {v : ℝ}
    (hv : v ∉ Set.Icc (-1 : ℝ) 1) :
    ‖yoshidaClippedCriticalCrossIntegrand a ha f g v‖ ≤
      (3 * C * yoshidaCriticalDecayConstant a f *
          yoshidaCriticalDecayConstant a g) *
        (max 1 |v|) ^ (-(3 / 2 : ℝ)) := by
  have habs : 1 < |v| := by
    by_contra h
    apply hv
    exact abs_le.mp (le_of_not_gt h)
  have hvne : v ≠ 0 := abs_pos.mp (zero_lt_one.trans habs)
  have hmax : max 1 |v| = |v| := max_eq_right habs.le
  have hCf : 0 ≤ yoshidaCriticalDecayConstant a f :=
    yoshidaCriticalDecayConstant_nonneg ha f
  have hCg : 0 ≤ yoshidaCriticalDecayConstant a g :=
    yoshidaCriticalDecayConstant_nonneg ha g
  have hf := yoshidaCriticalSample_norm_le_inv_abs ha v hvne f
  have hg := yoshidaCriticalSample_norm_le_inv_abs ha v hvne g
  have hk := hkernel v
  rw [hmax] at hk
  have hlog := Real.log_le_rpow_div (x := |v|) (abs_nonneg v)
    (show 0 < (1 / 2 : ℝ) by norm_num)
  have hrpow_one : 1 ≤ |v| ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow habs.le (by norm_num)
  have hlog' : Real.log |v| ≤ 2 * |v| ^ (1 / 2 : ℝ) := by
    calc
      Real.log |v| ≤ |v| ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) := hlog
      _ = 2 * |v| ^ (1 / 2 : ℝ) := by ring
  have hlogbound : 1 + Real.log |v| ≤
      3 * |v| ^ (1 / 2 : ℝ) := by
    nlinarith
  have hlognonneg : 0 ≤ Real.log |v| := Real.log_nonneg habs.le
  have hpow : |v| ^ (-(3 / 2 : ℝ)) =
      |v| ^ (1 / 2 : ℝ) / |v| ^ 2 := by
    rw [show (-(3 / 2 : ℝ)) = (1 / 2 : ℝ) - 2 by ring,
      Real.rpow_sub (abs_pos.mpr hvne), Real.rpow_two]
  rw [hmax]
  calc
    ‖yoshidaClippedCriticalCrossIntegrand a ha f g v‖ =
        ‖MultiplicativeWeil.bombieriLocalCriticalKernel v‖ *
          ‖yoshidaCriticalSampleLinear a ha v f‖ *
          ‖yoshidaCriticalSampleLinear a ha v g‖ := by
      simp [yoshidaClippedCriticalCrossIntegrand]
    _ ≤ (C * (1 + Real.log |v|)) *
          (yoshidaCriticalDecayConstant a f / |v|) *
          (yoshidaCriticalDecayConstant a g / |v|) := by
      gcongr
    _ ≤ (C * (3 * |v| ^ (1 / 2 : ℝ))) *
          (yoshidaCriticalDecayConstant a f / |v|) *
          (yoshidaCriticalDecayConstant a g / |v|) := by
      gcongr
    _ = (3 * C * yoshidaCriticalDecayConstant a f *
          yoshidaCriticalDecayConstant a g) *
        |v| ^ (-(3 / 2 : ℝ)) := by
      rw [hpow]
      field_simp

/-- The clipped critical cross integrand is integrable for every pair in
the algebraic carrier. -/
theorem yoshidaClippedCriticalCrossIntegrand_integrable
    {a : ℝ} (ha : 0 < a) (f g : YoshidaClippedSmooth a) :
    Integrable (yoshidaClippedCriticalCrossIntegrand a ha f g) := by
  obtain ⟨C, hCpos, hkernel⟩ :=
    exists_bombieriLocalCriticalKernel_log_norm_bound
  let K : ℝ := 3 * C * yoshidaCriticalDecayConstant a f *
    yoshidaCriticalDecayConstant a g
  let q : ℝ → ℝ := fun v ↦ (max 1 |v|) ^ (-(3 / 2 : ℝ))
  let S : Set ℝ := Set.Icc (-1 : ℝ) 1
  have hcompact : IntegrableOn
      (yoshidaClippedCriticalCrossIntegrand a ha f g) S := by
    exact (continuous_yoshidaClippedCriticalCrossIntegrand ha f g).continuousOn
      |>.integrableOn_compact isCompact_Icc
  have hq : Integrable q := by
    simpa only [q] using integrable_max_one_abs_rpow_neg_three_halves
  have hCf : 0 ≤ yoshidaCriticalDecayConstant a f :=
    yoshidaCriticalDecayConstant_nonneg ha f
  have hCg : 0 ≤ yoshidaCriticalDecayConstant a g :=
    yoshidaCriticalDecayConstant_nonneg ha g
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hmajor : Integrable (fun v ↦ K * q v) := hq.const_mul K
  have htail : IntegrableOn
      (yoshidaClippedCriticalCrossIntegrand a ha f g) Sᶜ := by
    apply hmajor.integrableOn.mono'
    · exact (continuous_yoshidaClippedCriticalCrossIntegrand ha f g)
        |>.aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with v hv
      have hbound := yoshidaClippedCriticalCrossIntegrand_norm_le_tail
        ha hCpos.le hkernel f g hv
      simpa only [K, q] using hbound
  rw [← integrableOn_univ]
  simpa only [S, union_compl_self] using hcompact.union htail

private theorem integral_yoshidaClippedCriticalCrossIntegrand_add_right
    {a : ℝ} (ha : 0 < a)
    (f g h : YoshidaClippedSmooth a) :
    (∫ v : ℝ, yoshidaClippedCriticalCrossIntegrand a ha f (g + h) v) =
      (∫ v : ℝ, yoshidaClippedCriticalCrossIntegrand a ha f g v) +
        ∫ v : ℝ, yoshidaClippedCriticalCrossIntegrand a ha f h v := by
  rw [← integral_add
    (yoshidaClippedCriticalCrossIntegrand_integrable ha f g)
    (yoshidaClippedCriticalCrossIntegrand_integrable ha f h)]
  apply integral_congr_ae
  filter_upwards [] with v
  simp only [yoshidaClippedCriticalCrossIntegrand, map_add]
  ring

private theorem integral_yoshidaClippedCriticalCrossIntegrand_smul_right
    {a : ℝ} (ha : 0 < a)
    (f g : YoshidaClippedSmooth a) (c : ℂ) :
    (∫ v : ℝ, yoshidaClippedCriticalCrossIntegrand a ha f (c • g) v) =
      c * ∫ v : ℝ, yoshidaClippedCriticalCrossIntegrand a ha f g v := by
  calc
    (∫ v : ℝ, yoshidaClippedCriticalCrossIntegrand a ha f (c • g) v) =
        ∫ v : ℝ, c * yoshidaClippedCriticalCrossIntegrand a ha f g v := by
      apply integral_congr_ae
      filter_upwards [] with v
      simp [yoshidaClippedCriticalCrossIntegrand]
      ring
    _ = _ := MeasureTheory.integral_const_mul c _

private theorem integral_yoshidaClippedCriticalCrossIntegrand_add_left
    {a : ℝ} (ha : 0 < a)
    (f g h : YoshidaClippedSmooth a) :
    (∫ v : ℝ, yoshidaClippedCriticalCrossIntegrand a ha (f + g) h v) =
      (∫ v : ℝ, yoshidaClippedCriticalCrossIntegrand a ha f h v) +
        ∫ v : ℝ, yoshidaClippedCriticalCrossIntegrand a ha g h v := by
  rw [← integral_add
    (yoshidaClippedCriticalCrossIntegrand_integrable ha f h)
    (yoshidaClippedCriticalCrossIntegrand_integrable ha g h)]
  apply integral_congr_ae
  filter_upwards [] with v
  simp [yoshidaClippedCriticalCrossIntegrand, map_add]
  ring

private theorem integral_yoshidaClippedCriticalCrossIntegrand_smul_left
    {a : ℝ} (ha : 0 < a)
    (f g : YoshidaClippedSmooth a) (c : ℂ) :
    (∫ v : ℝ, yoshidaClippedCriticalCrossIntegrand a ha (c • f) g v) =
      star c * ∫ v : ℝ, yoshidaClippedCriticalCrossIntegrand a ha f g v := by
  calc
    (∫ v : ℝ, yoshidaClippedCriticalCrossIntegrand a ha (c • f) g v) =
        ∫ v : ℝ, star c *
          yoshidaClippedCriticalCrossIntegrand a ha f g v := by
      apply integral_congr_ae
      filter_upwards [] with v
      simp [yoshidaClippedCriticalCrossIntegrand]
      ring
    _ = _ := MeasureTheory.integral_const_mul (star c) _

/-- The clipped local critical pairing, including both polar terms. -/
def yoshidaClippedLocalCriticalPairing
    (a : ℝ) (ha : 0 < a)
    (f g : YoshidaClippedSmooth a) : ℂ :=
  star (yoshidaPositivePolarLinear a ha f) *
      yoshidaNegativePolarLinear a ha g +
    star (yoshidaNegativePolarLinear a ha f) *
      yoshidaPositivePolarLinear a ha g +
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ v : ℝ, yoshidaClippedCriticalCrossIntegrand a ha f g v)

/-- The clipped local critical pairing bundled as a conjugate-linear/linear
form. This definition does not assert positivity or boundedness. -/
def yoshidaClippedLocalCriticalForm
    (a : ℝ) (ha : 0 < a) :
    YoshidaClippedSmooth a →ₗ⋆[ℂ] YoshidaClippedSmooth a →ₗ[ℂ] ℂ where
  toFun f :=
    { toFun := yoshidaClippedLocalCriticalPairing a ha f
      map_add' := fun g h ↦ by
        simp only [yoshidaClippedLocalCriticalPairing, map_add,
          integral_yoshidaClippedCriticalCrossIntegrand_add_right ha]
        ring
      map_smul' := fun c g ↦ by
        simp only [yoshidaClippedLocalCriticalPairing, map_smul,
          integral_yoshidaClippedCriticalCrossIntegrand_smul_right ha,
          smul_eq_mul, RingHom.id_apply]
        ring }
  map_add' f g := by
    ext h
    change yoshidaClippedLocalCriticalPairing a ha (f + g) h =
      yoshidaClippedLocalCriticalPairing a ha f h +
        yoshidaClippedLocalCriticalPairing a ha g h
    simp only [yoshidaClippedLocalCriticalPairing, map_add,
      integral_yoshidaClippedCriticalCrossIntegrand_add_left ha, star_add]
    ring
  map_smul' c f := by
    ext g
    change yoshidaClippedLocalCriticalPairing a ha (c • f) g =
      star c * yoshidaClippedLocalCriticalPairing a ha f g
    simp only [yoshidaClippedLocalCriticalPairing, map_smul,
      integral_yoshidaClippedCriticalCrossIntegrand_smul_left ha,
      smul_eq_mul, star_mul]
    ring

@[simp] theorem yoshidaClippedLocalCriticalForm_apply
    {a : ℝ} (ha : 0 < a) (f g : YoshidaClippedSmooth a) :
    yoshidaClippedLocalCriticalForm a ha f g =
      yoshidaClippedLocalCriticalPairing a ha f g := rfl

theorem star_bombieriLocalCriticalKernel (v : ℝ) :
    star (MultiplicativeWeil.bombieriLocalCriticalKernel v) =
      MultiplicativeWeil.bombieriLocalCriticalKernel v := by
  simp [MultiplicativeWeil.bombieriLocalCriticalKernel]

private theorem star_integral_yoshidaClippedCriticalCrossIntegrand
    {a : ℝ} (ha : 0 < a) (f g : YoshidaClippedSmooth a) :
    star (∫ v : ℝ, yoshidaClippedCriticalCrossIntegrand a ha g f v) =
      ∫ v : ℝ, yoshidaClippedCriticalCrossIntegrand a ha f g v := by
  change (starRingEnd ℂ)
    (∫ v : ℝ, yoshidaClippedCriticalCrossIntegrand a ha g f v) = _
  calc
    (starRingEnd ℂ)
        (∫ v : ℝ, yoshidaClippedCriticalCrossIntegrand a ha g f v) =
      ∫ v : ℝ, (starRingEnd ℂ)
        (yoshidaClippedCriticalCrossIntegrand a ha g f v) :=
      (integral_conj
        (f := fun v : ℝ ↦ yoshidaClippedCriticalCrossIntegrand a ha g f v)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with v
      simp only [yoshidaClippedCriticalCrossIntegrand, map_mul,
        starRingEnd_apply, star_star, star_bombieriLocalCriticalKernel]
      ring

/-- Hermitian symmetry of the clipped local critical pairing. -/
theorem yoshidaClippedLocalCriticalPairing_conj
    {a : ℝ} (ha : 0 < a) (f g : YoshidaClippedSmooth a) :
    star (yoshidaClippedLocalCriticalPairing a ha g f) =
      yoshidaClippedLocalCriticalPairing a ha f g := by
  have hc : star ((((1 / (2 * Real.pi) : ℝ) : ℂ))) =
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) := by simp
  simp only [yoshidaClippedLocalCriticalPairing, star_add, star_mul,
    star_star, star_integral_yoshidaClippedCriticalCrossIntegrand ha]
  rw [hc]
  ring

/-- Hermitian symmetry of the bundled clipped local critical form. -/
theorem yoshidaClippedLocalCriticalForm_conj_apply
    {a : ℝ} (ha : 0 < a) (f g : YoshidaClippedSmooth a) :
    star (yoshidaClippedLocalCriticalForm a ha g f) =
      yoshidaClippedLocalCriticalForm a ha f g :=
  yoshidaClippedLocalCriticalPairing_conj ha f g

/-- On a supported smooth critical pullback, the clipped sample agrees with
the Bombieri Mellin sample. -/
theorem yoshidaCriticalSample_crop_eq_mellin
    {a : ℝ} (ha : 0 < a) (v : ℝ)
    (f : MultiplicativeWeil.BombieriTest)
    (hf : YoshidaCriticalPullbackSupported a f) :
    yoshidaCriticalSampleLinear a ha v
        (yoshidaCriticalPullbackCropLinear a f) =
      MultiplicativeWeil.mellinLinearMap
        ((1 / 2 : ℝ) + v * Complex.I) f := by
  rw [yoshidaCriticalSample_eq_fourier,
    yoshidaCriticalPullbackCrop_eq_logarithmicPullbackSchwartz hf,
    MultiplicativeWeil.mellinLinearMap_apply]
  exact (MultiplicativeWeil.bombieriMellin_vertical_eq_fourier
    f (1 / 2) v).symm

private theorem yoshidaCenteredLaplace_crop_eq_integral
    {a : ℝ} (ha : 0 < a) (z : ℂ)
    (f : MultiplicativeWeil.BombieriTest)
    (hf : YoshidaCriticalPullbackSupported a f) :
    yoshidaCenteredLaplaceLinear a ha z
        (yoshidaCriticalPullbackCropLinear a f) =
      ∫ x : ℝ,
        Complex.exp (-(z * (x : ℂ))) *
          f.logarithmicPullbackSchwartz (1 / 2) x := by
  rw [yoshidaCenteredLaplaceLinear_apply]
  have heq :=
    yoshidaCriticalPullbackCrop_eq_logarithmicPullbackSchwartz hf
  change
    (∫ x : ℝ in -a..a,
      Complex.exp (-(z * (x : ℂ))) *
        yoshidaCriticalPullbackCropLinear a f x) = _
  rw [show (yoshidaCriticalPullbackCropLinear a f : ℝ → ℂ) =
      f.logarithmicPullbackSchwartz (1 / 2) from heq]
  rw [intervalIntegral.integral_of_le (by linarith),
    ← integral_Icc_eq_integral_Ioc]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx ↦ by rw [hf x hx, mul_zero])

private theorem mellin_one_eq_integral_exp_neg_half_mul_criticalPullback
    (f : MultiplicativeWeil.BombieriTest) :
    mellin (f : ℝ → ℂ) 1 =
      ∫ u : ℝ, (Real.exp (-u / 2) : ℂ) *
        f.logarithmicPullbackSchwartz (1 / 2) u := by
  calc
    mellin (f : ℝ → ℂ) 1 =
        FourierTransform.fourier
          (f.logarithmicPullbackSchwartz 1) 0 := by
      simpa using MultiplicativeWeil.bombieriMellin_vertical_eq_fourier f 1 0
    _ = ∫ u : ℝ, f.logarithmicPullbackSchwartz 1 u := by
      rw [SchwartzMap.fourier_coe, Real.fourier_real_eq]
      simp
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with u
      simp only [MultiplicativeWeil.BombieriTest.logarithmicPullbackSchwartz_apply,
        MultiplicativeWeil.BombieriTest.logarithmicPullback]
      rw [show -1 * u = -u / 2 + (-(1 / 2) * u) by ring,
        Real.exp_add]
      push_cast
      ring

private theorem mellin_zero_eq_integral_exp_half_mul_criticalPullback
    (f : MultiplicativeWeil.BombieriTest) :
    mellin (f : ℝ → ℂ) 0 =
      ∫ u : ℝ, (Real.exp (u / 2) : ℂ) *
        f.logarithmicPullbackSchwartz (1 / 2) u := by
  calc
    mellin (f : ℝ → ℂ) 0 =
        FourierTransform.fourier
          (f.logarithmicPullbackSchwartz 0) 0 := by
      simpa using MultiplicativeWeil.bombieriMellin_vertical_eq_fourier f 0 0
    _ = ∫ u : ℝ, f.logarithmicPullbackSchwartz 0 u := by
      rw [SchwartzMap.fourier_coe, Real.fourier_real_eq]
      simp
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with u
      simp only [MultiplicativeWeil.BombieriTest.logarithmicPullbackSchwartz_apply,
        MultiplicativeWeil.BombieriTest.logarithmicPullback, zero_mul,
        neg_zero, Real.exp_zero, Complex.ofReal_one, one_mul]
      have hweight : (Real.exp (u / 2) : ℂ) *
          (Real.exp (-(1 / 2) * u) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, ← Real.exp_add]
        rw [show u / 2 + -(1 / 2) * u = 0 by ring]
        simp
      rw [← mul_assoc, hweight, one_mul]

theorem yoshidaPositivePolar_crop_eq_mellin_one
    {a : ℝ} (ha : 0 < a)
    (f : MultiplicativeWeil.BombieriTest)
    (hf : YoshidaCriticalPullbackSupported a f) :
    yoshidaPositivePolarLinear a ha
        (yoshidaCriticalPullbackCropLinear a f) =
      MultiplicativeWeil.mellinLinearMap 1 f := by
  rw [yoshidaPositivePolarLinear,
    yoshidaCenteredLaplace_crop_eq_integral ha (1 / 2) f hf,
    MultiplicativeWeil.mellinLinearMap_apply,
    mellin_one_eq_integral_exp_neg_half_mul_criticalPullback]
  apply integral_congr_ae
  filter_upwards [] with x
  congr 1
  rw [show -((1 / 2 : ℂ) * (x : ℂ)) = ((-x / 2 : ℝ) : ℂ) by
    push_cast
    ring]
  exact (Complex.ofReal_exp _).symm

theorem yoshidaNegativePolar_crop_eq_mellin_zero
    {a : ℝ} (ha : 0 < a)
    (f : MultiplicativeWeil.BombieriTest)
    (hf : YoshidaCriticalPullbackSupported a f) :
    yoshidaNegativePolarLinear a ha
        (yoshidaCriticalPullbackCropLinear a f) =
      MultiplicativeWeil.mellinLinearMap 0 f := by
  rw [yoshidaNegativePolarLinear,
    yoshidaCenteredLaplace_crop_eq_integral ha (-1 / 2) f hf,
    MultiplicativeWeil.mellinLinearMap_apply,
    mellin_zero_eq_integral_exp_half_mul_criticalPullback]
  apply integral_congr_ae
  filter_upwards [] with x
  congr 1
  rw [show -((-1 / 2 : ℂ) * (x : ℂ)) = ((x / 2 : ℝ) : ℂ) by
    push_cast
    ring]
  exact (Complex.ofReal_exp _).symm

theorem yoshidaClippedCriticalCrossIntegrand_crop_eq
    {a : ℝ} (ha : 0 < a)
    (f g : MultiplicativeWeil.BombieriTest)
    (hf : YoshidaCriticalPullbackSupported a f)
    (hg : YoshidaCriticalPullbackSupported a g)
    (v : ℝ) :
    yoshidaClippedCriticalCrossIntegrand a ha
        (yoshidaCriticalPullbackCropLinear a f)
        (yoshidaCriticalPullbackCropLinear a g) v =
      MultiplicativeWeil.bombieriLocalCriticalCrossIntegrand f g v := by
  rw [yoshidaClippedCriticalCrossIntegrand,
    MultiplicativeWeil.bombieriLocalCriticalCrossIntegrand,
    yoshidaCriticalSample_crop_eq_mellin ha v f hf,
    yoshidaCriticalSample_crop_eq_mellin ha v g hg]

theorem yoshidaClippedLocalCriticalPairing_crop_eq
    {a : ℝ} (ha : 0 < a)
    (f g : MultiplicativeWeil.BombieriTest)
    (hf : YoshidaCriticalPullbackSupported a f)
    (hg : YoshidaCriticalPullbackSupported a g) :
    yoshidaClippedLocalCriticalPairing a ha
        (yoshidaCriticalPullbackCropLinear a f)
        (yoshidaCriticalPullbackCropLinear a g) =
      MultiplicativeWeil.bombieriLocalCriticalPairing f g := by
  rw [yoshidaClippedLocalCriticalPairing,
    MultiplicativeWeil.bombieriLocalCriticalPairing,
    yoshidaPositivePolar_crop_eq_mellin_one ha f hf,
    yoshidaNegativePolar_crop_eq_mellin_zero ha f hf,
    yoshidaPositivePolar_crop_eq_mellin_one ha g hg,
    yoshidaNegativePolar_crop_eq_mellin_zero ha g hg]
  congr 1
  apply congrArg (fun z : ℂ ↦ (((1 / (2 * Real.pi) : ℝ) : ℂ) * z))
  apply integral_congr_ae
  filter_upwards [] with v
  exact yoshidaClippedCriticalCrossIntegrand_crop_eq ha f g hf hg v

/-- The clipped form agrees exactly with the Bombieri local critical form
on crops of supported smooth critical pullbacks. -/
theorem yoshidaClippedLocalCriticalForm_crop_eq_bombieriLocalCriticalForm
    {a : ℝ} (ha : 0 < a)
    (f g : MultiplicativeWeil.BombieriTest)
    (hf : YoshidaCriticalPullbackSupported a f)
    (hg : YoshidaCriticalPullbackSupported a g) :
    yoshidaClippedLocalCriticalForm a ha
        (yoshidaCriticalPullbackCropLinear a f)
        (yoshidaCriticalPullbackCropLinear a g) =
      MultiplicativeWeil.bombieriLocalCriticalForm f g := by
  rw [yoshidaClippedLocalCriticalForm_apply,
    MultiplicativeWeil.bombieriLocalCriticalForm_apply]
  exact yoshidaClippedLocalCriticalPairing_crop_eq ha f g hf hg

end

end ArithmeticHodge.Analysis
