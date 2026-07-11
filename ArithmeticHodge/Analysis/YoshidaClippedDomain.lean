import ArithmeticHodge.Analysis.MultiplicativeWeilLocalCriticalForm
import ArithmeticHodge.Analysis.YoshidaFourierModes
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ContDiff

namespace ArithmeticHodge.Analysis

noncomputable section

/-- Functions that are smooth on the closed log interval and vanish outside
it. Endpoint jumps are intentional: smoothness is required only on the
interval. -/
def yoshidaClippedSmoothSubmodule (a : ℝ) : Submodule ℂ (ℝ → ℂ) where
  carrier f :=
    ContDiffOn ℝ ∞ f (Set.Icc (-a) a) ∧
      ∀ x ∉ Set.Icc (-a) a, f x = 0
  zero_mem' := ⟨contDiffOn_const, by simp⟩
  add_mem' := by
    rintro f g ⟨hf, hfs⟩ ⟨hg, hgs⟩
    refine ⟨hf.add hg, ?_⟩
    intro x hx
    simp [hfs x hx, hgs x hx]
  smul_mem' := by
    rintro c f ⟨hf, hfs⟩
    refine ⟨hf.const_smul c, ?_⟩
    intro x hx
    simp [hfs x hx]

/-- The direct algebraic ambient domain for Yoshida's clipped modes. -/
abbrev YoshidaClippedSmooth (a : ℝ) :=
  yoshidaClippedSmoothSubmodule a

instance {a : ℝ} : CoeFun (YoshidaClippedSmooth a) (fun _ ↦ ℝ → ℂ) :=
  ⟨fun f ↦ (f : ℝ → ℂ)⟩

@[simp] theorem yoshidaClippedSmooth_eq_zero_outside
    {a x : ℝ} (f : YoshidaClippedSmooth a)
    (hx : x ∉ Set.Icc (-a) a) :
    f x = 0 :=
  f.property.2 x hx

private def yoshidaExponentialCore (a : ℝ) (n : ℤ) (x : ℝ) : ℂ :=
  ((Real.sqrt (2 * a))⁻¹ : ℂ) *
    Complex.exp
      (Real.pi * Complex.I * (n : ℂ) * (x : ℂ) / (a : ℝ))

/-- Yoshida's clipped exponential, normalized to have Lebesgue `L²` norm
one when `a > 0`. -/
def yoshidaClippedExponential
    (a : ℝ) (n : ℤ) : YoshidaClippedSmooth a :=
  ⟨fun x ↦ if x ∈ Set.Icc (-a) a then
      yoshidaExponentialCore a n x else 0, by
    constructor
    · have hcore : ContDiff ℝ ∞ (yoshidaExponentialCore a n) := by
        unfold yoshidaExponentialCore
        have hcast : ContDiff ℝ ∞ (fun x : ℝ ↦ (x : ℂ)) :=
          Complex.ofRealCLM.contDiff
        have harg : ContDiff ℝ ∞ (fun x : ℝ ↦
            Real.pi * Complex.I * (n : ℂ) * (x : ℂ) /
              (a : ℝ)) := by
          fun_prop
        exact contDiff_const.mul (Complex.contDiff_exp.comp harg)
      exact hcore.contDiffOn.congr fun x hx ↦ by simp [hx]
    · intro x hx
      simp [hx]⟩

@[simp] theorem yoshidaClippedExponential_apply_of_mem
    {a x : ℝ} (n : ℤ) (hx : x ∈ Set.Icc (-a) a) :
    yoshidaClippedExponential a n x =
      ((Real.sqrt (2 * a))⁻¹ : ℂ) *
        Complex.exp
          (Real.pi * Complex.I * (n : ℂ) * (x : ℂ) / (a : ℝ)) := by
  change (if x ∈ Set.Icc (-a) a then
    yoshidaExponentialCore a n x else 0) = _
  rw [if_pos hx]
  rfl

@[simp] theorem yoshidaClippedExponential_apply_of_not_mem
    {a x : ℝ} (n : ℤ) (hx : x ∉ Set.Icc (-a) a) :
    yoshidaClippedExponential a n x = 0 := by
  simp [yoshidaClippedExponential, hx]

private theorem yoshidaIntervalIntegrable_weight_mul
    {a : ℝ} (ha : 0 < a) (z : ℂ) (f : YoshidaClippedSmooth a) :
    IntervalIntegrable
      (fun x : ℝ ↦ Complex.exp (-(z * (x : ℂ))) * f x)
      volume (-a) a := by
  have hf : ContinuousOn (f : ℝ → ℂ) (Set.Icc (-a) a) :=
    f.property.1.continuousOn
  have hw : Continuous (fun x : ℝ ↦
      Complex.exp (-(z * (x : ℂ)))) := by
    fun_prop
  exact (hw.continuousOn.mul hf).intervalIntegrable_of_Icc (by linarith)

/-- Centered bilateral Laplace evaluation on the clipped log interval. -/
def yoshidaCenteredLaplaceLinear
    (a : ℝ) (ha : 0 < a) (z : ℂ) :
    YoshidaClippedSmooth a →ₗ[ℂ] ℂ where
  toFun f := ∫ x : ℝ in -a..a,
    Complex.exp (-(z * (x : ℂ))) * f x
  map_add' f g := by
    rw [← intervalIntegral.integral_add
      (yoshidaIntervalIntegrable_weight_mul ha z f)
      (yoshidaIntervalIntegrable_weight_mul ha z g)]
    apply intervalIntegral.integral_congr
    intro x _
    simp only [Submodule.coe_add, Pi.add_apply]
    ring
  map_smul' c f := by
    calc
      (∫ x : ℝ in -a..a,
          Complex.exp (-(z * (x : ℂ))) * (c • f) x) =
          ∫ x : ℝ in -a..a,
            c * (Complex.exp (-(z * (x : ℂ))) * f x) := by
        apply intervalIntegral.integral_congr
        intro x _
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
        ring
      _ = c * ∫ x : ℝ in -a..a,
          Complex.exp (-(z * (x : ℂ))) * f x :=
        intervalIntegral.integral_const_mul c _
      _ = c • ∫ x : ℝ in -a..a,
          Complex.exp (-(z * (x : ℂ))) * f x := by
        rw [smul_eq_mul]

@[simp] theorem yoshidaCenteredLaplaceLinear_apply
    {a : ℝ} (ha : 0 < a) (z : ℂ) (f : YoshidaClippedSmooth a) :
    yoshidaCenteredLaplaceLinear a ha z f =
      ∫ x : ℝ in -a..a,
        Complex.exp (-(z * (x : ℂ))) * f x := rfl

theorem yoshidaCenteredLaplaceLinear_add
    {a : ℝ} (ha : 0 < a) (z : ℂ)
    (f g : YoshidaClippedSmooth a) :
    yoshidaCenteredLaplaceLinear a ha z (f + g) =
      yoshidaCenteredLaplaceLinear a ha z f +
        yoshidaCenteredLaplaceLinear a ha z g := by
  exact map_add (yoshidaCenteredLaplaceLinear a ha z) f g

theorem yoshidaCenteredLaplaceLinear_smul
    {a : ℝ} (ha : 0 < a) (z c : ℂ)
    (f : YoshidaClippedSmooth a) :
    yoshidaCenteredLaplaceLinear a ha z (c • f) =
      c * yoshidaCenteredLaplaceLinear a ha z f := by
  simpa only [smul_eq_mul] using
    map_smul (yoshidaCenteredLaplaceLinear a ha z) c f

/-- Critical-line sampling in the centered logarithmic coordinate. -/
def yoshidaCriticalSampleLinear
    (a : ℝ) (ha : 0 < a) (v : ℝ) :
    YoshidaClippedSmooth a →ₗ[ℂ] ℂ :=
  yoshidaCenteredLaplaceLinear a ha (v * Complex.I)

/-- The `s = 1` polar sample in the centered logarithmic coordinate. -/
def yoshidaPositivePolarLinear
    (a : ℝ) (ha : 0 < a) :
    YoshidaClippedSmooth a →ₗ[ℂ] ℂ :=
  yoshidaCenteredLaplaceLinear a ha (1 / 2 : ℂ)

/-- The `s = 0` polar sample in the centered logarithmic coordinate. -/
def yoshidaNegativePolarLinear
    (a : ℝ) (ha : 0 < a) :
    YoshidaClippedSmooth a →ₗ[ℂ] ℂ :=
  yoshidaCenteredLaplaceLinear a ha (-1 / 2 : ℂ)

/-- The exponential coefficient appearing in a clipped mode's centered
Laplace transform. -/
def yoshidaModeLaplaceExponent
    (a : ℝ) (n : ℤ) (z : ℂ) : ℂ :=
  -z + ((Real.pi * (n : ℝ) / a : ℝ) : ℂ) * Complex.I

/-- The entire interval-exponential quotient, with its removable value at
zero made explicit before any algebraic splitting. -/
def yoshidaIntervalExpQuotient (a : ℝ) (c : ℂ) : ℂ :=
  if c = 0 then ((2 * a : ℝ) : ℂ)
  else
    (Complex.exp (c * a) - Complex.exp (c * (-a))) / c

@[simp] theorem yoshidaIntervalExpQuotient_zero (a : ℝ) :
    yoshidaIntervalExpQuotient a 0 = ((2 * a : ℝ) : ℂ) := by
  simp [yoshidaIntervalExpQuotient]

theorem yoshidaIntervalExpQuotient_of_ne
    {a : ℝ} {c : ℂ} (hc : c ≠ 0) :
    yoshidaIntervalExpQuotient a c =
      (Complex.exp (c * a) - Complex.exp (c * (-a))) / c := by
  simp [yoshidaIntervalExpQuotient, hc]

private theorem yoshidaCenteredLaplace_clippedExponential_as_integral
    {a : ℝ} (ha : 0 < a) (z : ℂ) (n : ℤ) :
    yoshidaCenteredLaplaceLinear a ha z
        (yoshidaClippedExponential a n) =
      ((Real.sqrt (2 * a))⁻¹ : ℂ) *
        ∫ x : ℝ in -a..a,
          Complex.exp
            (yoshidaModeLaplaceExponent a n z * (x : ℂ)) := by
  rw [yoshidaCenteredLaplaceLinear_apply]
  calc
    (∫ x : ℝ in -a..a,
        Complex.exp (-(z * (x : ℂ))) *
          yoshidaClippedExponential a n x) =
        ∫ x : ℝ in -a..a,
          ((Real.sqrt (2 * a))⁻¹ : ℂ) *
            Complex.exp
              (yoshidaModeLaplaceExponent a n z * (x : ℂ)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hxIcc : x ∈ Set.Icc (-a) a := by
        simpa only [uIcc_of_le (by linarith : -a ≤ a)] using hx
      change Complex.exp (-(z * (x : ℂ))) *
        yoshidaClippedExponential a n x = _
      rw [yoshidaClippedExponential_apply_of_mem n hxIcc]
      unfold yoshidaModeLaplaceExponent
      calc
        Complex.exp (-(z * (x : ℂ))) *
            (((Real.sqrt (2 * a))⁻¹ : ℂ) *
              Complex.exp
                (Real.pi * Complex.I * (n : ℂ) * (x : ℂ) /
                  (a : ℝ))) =
            ((Real.sqrt (2 * a))⁻¹ : ℂ) *
              (Complex.exp (-(z * (x : ℂ))) *
                Complex.exp
                  (Real.pi * Complex.I * (n : ℂ) * (x : ℂ) /
                    (a : ℝ))) := by ring
        _ = ((Real.sqrt (2 * a))⁻¹ : ℂ) *
              Complex.exp
                (-(z * (x : ℂ)) +
                  Real.pi * Complex.I * (n : ℂ) * (x : ℂ) /
                    (a : ℝ)) := by
              rw [Complex.exp_add]
        _ = _ := by
              congr 2
              push_cast
              field_simp [ha.ne']
    _ = ((Real.sqrt (2 * a))⁻¹ : ℂ) *
        ∫ x : ℝ in -a..a,
          Complex.exp
            (yoshidaModeLaplaceExponent a n z * (x : ℂ)) :=
      intervalIntegral.integral_const_mul _ _

/-- Exact clipped-mode transform, including the removable zero-exponent
branch. -/
theorem yoshidaCenteredLaplace_clippedExponential
    {a : ℝ} (ha : 0 < a) (z : ℂ) (n : ℤ) :
    yoshidaCenteredLaplaceLinear a ha z
        (yoshidaClippedExponential a n) =
      ((Real.sqrt (2 * a))⁻¹ : ℂ) *
        yoshidaIntervalExpQuotient a
          (yoshidaModeLaplaceExponent a n z) := by
  rw [yoshidaCenteredLaplace_clippedExponential_as_integral ha z n]
  by_cases hc : yoshidaModeLaplaceExponent a n z = 0
  · rw [hc, yoshidaIntervalExpQuotient_zero]
    congr 1
    simp
    change (((a + a : ℝ) : ℂ) * (1 : ℂ)) =
      (2 : ℂ) * (a : ℂ)
    push_cast
    ring
  · rw [integral_exp_mul_complex hc,
      yoshidaIntervalExpQuotient_of_ne hc]
    simp

/-- Nonzero-denominator form of the exact clipped-mode transform. -/
theorem yoshidaCenteredLaplace_clippedExponential_of_ne
    {a : ℝ} (ha : 0 < a) (z : ℂ) (n : ℤ)
    (hc : yoshidaModeLaplaceExponent a n z ≠ 0) :
    yoshidaCenteredLaplaceLinear a ha z
        (yoshidaClippedExponential a n) =
      ((Real.sqrt (2 * a))⁻¹ : ℂ) *
        ((Complex.exp (yoshidaModeLaplaceExponent a n z * a) -
            Complex.exp (yoshidaModeLaplaceExponent a n z * (-a))) /
          yoshidaModeLaplaceExponent a n z) := by
  rw [yoshidaCenteredLaplace_clippedExponential ha z n,
    yoshidaIntervalExpQuotient_of_ne hc]

private theorem yoshidaModeLaplaceExponent_positivePolar_ne
    (a : ℝ) (n : ℤ) :
    yoshidaModeLaplaceExponent a n (1 / 2 : ℂ) ≠ 0 := by
  intro h
  have hre := congr_arg Complex.re h
  norm_num [yoshidaModeLaplaceExponent] at hre

private theorem yoshidaModeLaplaceExponent_negativePolar_ne
    (a : ℝ) (n : ℤ) :
    yoshidaModeLaplaceExponent a n (-1 / 2 : ℂ) ≠ 0 := by
  intro h
  have hre := congr_arg Complex.re h
  norm_num [yoshidaModeLaplaceExponent] at hre

theorem yoshidaPositivePolar_clippedExponential
    {a : ℝ} (ha : 0 < a) (n : ℤ) :
    yoshidaPositivePolarLinear a ha (yoshidaClippedExponential a n) =
      ((Real.sqrt (2 * a))⁻¹ : ℂ) *
        ((Complex.exp
              (yoshidaModeLaplaceExponent a n (1 / 2 : ℂ) * a) -
            Complex.exp
              (yoshidaModeLaplaceExponent a n (1 / 2 : ℂ) * (-a))) /
          yoshidaModeLaplaceExponent a n (1 / 2 : ℂ)) := by
  exact yoshidaCenteredLaplace_clippedExponential_of_ne ha (1 / 2) n
    (yoshidaModeLaplaceExponent_positivePolar_ne a n)

theorem yoshidaNegativePolar_clippedExponential
    {a : ℝ} (ha : 0 < a) (n : ℤ) :
    yoshidaNegativePolarLinear a ha (yoshidaClippedExponential a n) =
      ((Real.sqrt (2 * a))⁻¹ : ℂ) *
        ((Complex.exp
              (yoshidaModeLaplaceExponent a n (-1 / 2 : ℂ) * a) -
            Complex.exp
              (yoshidaModeLaplaceExponent a n (-1 / 2 : ℂ) * (-a))) /
          yoshidaModeLaplaceExponent a n (-1 / 2 : ℂ)) := by
  exact yoshidaCenteredLaplace_clippedExponential_of_ne ha (-1 / 2) n
    (yoshidaModeLaplaceExponent_negativePolar_ne a n)

/-- Crop a smooth Bombieri critical logarithmic pullback to the closed log
interval. -/
def yoshidaCriticalPullbackCropLinear (a : ℝ) :
    MultiplicativeWeil.BombieriTest →ₗ[ℂ]
      YoshidaClippedSmooth a where
  toFun f :=
    ⟨fun x ↦ if x ∈ Set.Icc (-a) a then
        f.logarithmicPullbackSchwartz (1 / 2) x else 0, by
      constructor
      · exact (f.logarithmicPullback_contDiff (1 / 2)).contDiffOn.congr
          fun x hx ↦ by simp [hx]
      · intro x hx
        simp [hx]⟩
  map_add' f g := by
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ Set.Icc (-a) a
    · change
        (if x ∈ Set.Icc (-a) a then
          (f + g).logarithmicPullbackSchwartz (1 / 2) x else 0) =
        (if x ∈ Set.Icc (-a) a then
          f.logarithmicPullbackSchwartz (1 / 2) x else 0) +
        (if x ∈ Set.Icc (-a) a then
          g.logarithmicPullbackSchwartz (1 / 2) x else 0)
      simp only [hx, if_pos,
        MultiplicativeWeil.BombieriTest.logarithmicPullbackSchwartz_apply,
        MultiplicativeWeil.BombieriTest.logarithmicPullback,
        TestFunction.coe_add, Pi.add_apply]
      ring
    · simp [hx]
  map_smul' c f := by
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ Set.Icc (-a) a
    · change
        (if x ∈ Set.Icc (-a) a then
          (c • f).logarithmicPullbackSchwartz (1 / 2) x else 0) =
        c • (if x ∈ Set.Icc (-a) a then
          f.logarithmicPullbackSchwartz (1 / 2) x else 0)
      simp only [hx, if_pos,
        MultiplicativeWeil.BombieriTest.logarithmicPullbackSchwartz_apply,
        MultiplicativeWeil.BombieriTest.logarithmicPullback,
        TestFunction.coe_smul, Pi.smul_apply, smul_eq_mul]
      ring
    · simp [hx]

/-- A Bombieri test function whose critical logarithmic pullback is already
supported on the clipping interval. -/
def YoshidaCriticalPullbackSupported
    (a : ℝ) (f : MultiplicativeWeil.BombieriTest) : Prop :=
  ∀ x ∉ Set.Icc (-a) a,
    f.logarithmicPullbackSchwartz (1 / 2) x = 0

@[simp] theorem yoshidaCriticalPullbackCropLinear_apply_of_mem
    {a x : ℝ} (f : MultiplicativeWeil.BombieriTest)
    (hx : x ∈ Set.Icc (-a) a) :
    yoshidaCriticalPullbackCropLinear a f x =
      f.logarithmicPullbackSchwartz (1 / 2) x := by
  change (if x ∈ Set.Icc (-a) a then
    f.logarithmicPullbackSchwartz (1 / 2) x else 0) = _
  rw [if_pos hx]

@[simp] theorem yoshidaCriticalPullbackCropLinear_apply_of_not_mem
    {a x : ℝ} (f : MultiplicativeWeil.BombieriTest)
    (hx : x ∉ Set.Icc (-a) a) :
    yoshidaCriticalPullbackCropLinear a f x = 0 := by
  change (if x ∈ Set.Icc (-a) a then
    f.logarithmicPullbackSchwartz (1 / 2) x else 0) = 0
  rw [if_neg hx]

theorem yoshidaCriticalPullbackCrop_eq_logarithmicPullbackSchwartz
    {a : ℝ} {f : MultiplicativeWeil.BombieriTest}
    (hf : YoshidaCriticalPullbackSupported a f) :
    (yoshidaCriticalPullbackCropLinear a f : ℝ → ℂ) =
      f.logarithmicPullbackSchwartz (1 / 2) := by
  funext x
  by_cases hx : x ∈ Set.Icc (-a) a
  · exact yoshidaCriticalPullbackCropLinear_apply_of_mem f hx
  · rw [yoshidaCriticalPullbackCropLinear_apply_of_not_mem f hx,
      hf x hx]

theorem yoshidaCriticalPullbackCropLinear_add
    (a : ℝ) (f g : MultiplicativeWeil.BombieriTest) :
    yoshidaCriticalPullbackCropLinear a (f + g) =
      yoshidaCriticalPullbackCropLinear a f +
        yoshidaCriticalPullbackCropLinear a g := by
  exact map_add (yoshidaCriticalPullbackCropLinear a) f g

theorem yoshidaCriticalPullbackCropLinear_smul
    (a : ℝ) (c : ℂ) (f : MultiplicativeWeil.BombieriTest) :
    yoshidaCriticalPullbackCropLinear a (c • f) =
      c • yoshidaCriticalPullbackCropLinear a f := by
  exact map_smul (yoshidaCriticalPullbackCropLinear a) c f

end


end ArithmeticHodge.Analysis
