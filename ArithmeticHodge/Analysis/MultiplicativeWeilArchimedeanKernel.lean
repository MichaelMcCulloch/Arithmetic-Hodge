/-
  The Cauchy-kernel form of Bombieri's archimedean smoothing.

  This is the Fourier--Mellin calculation underlying the positive weight
  `min(x, x⁻¹)^a` used in Enrico Bombieri's ``Remarks on Weil's quadratic
  functional''.  The Fourier normalization is Mathlib's `2π` normalization.
-/

import ArithmeticHodge.Analysis.MultiplicativeWeilMellinFourier
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false

open Complex MeasureTheory Real Set
open scoped FourierTransform

local notation "FT" => FourierTransform.fourier
local notation "IFT" => FourierTransform.fourierInv

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- The two-sided exponential kernel whose Fourier transform is the Cauchy
kernel. -/
def laplaceKernel (a x : ℝ) : ℂ :=
  Complex.exp (-(a : ℂ) * (↑|x| : ℂ))

/-- The two-sided exponential kernel is integrable for every positive decay
parameter. -/
theorem laplaceKernel_integrable (a : ℝ) (ha : 0 < a) :
    Integrable (laplaceKernel a) := by
  have hleft : IntegrableOn (fun x : ℝ ↦ Complex.exp ((a : ℂ) * x)) (Iic 0) :=
    integrableOn_exp_mul_complex_Iic (by simpa using ha) 0
  have hright : IntegrableOn (fun x : ℝ ↦ Complex.exp (-(a : ℂ) * x)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi (by simpa using ha) 0
  have hleft' : IntegrableOn (laplaceKernel a) (Iic 0) := by
    refine hleft.congr_fun ?_ measurableSet_Iic
    intro x hx
    change x ≤ 0 at hx
    simp [laplaceKernel, abs_of_nonpos hx, mul_neg]
  have hright' : IntegrableOn (laplaceKernel a) (Ioi 0) := by
    refine hright.congr_fun ?_ measurableSet_Ioi
    intro x hx
    change 0 < x at hx
    simp [laplaceKernel, abs_of_pos hx]
  rw [← integrableOn_univ]
  simpa only [Iic_union_Ioi] using hleft'.union hright'

/-- Fourier transform of the two-sided exponential in Mathlib's `2π`
normalization. -/
theorem fourier_laplaceKernel (a w : ℝ) (ha : 0 < a) :
    FT (laplaceKernel a) w =
      (2 * a : ℂ) / ((a : ℂ) ^ 2 + (2 * Real.pi * w : ℂ) ^ 2) := by
  rw [fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  let b : ℂ := (2 * Real.pi * w : ℝ)
  have hleft : IntegrableOn
      (fun x : ℝ ↦ Complex.exp ((a - b * I) * x)) (Iic 0) := by
    apply integrableOn_exp_mul_complex_Iic
    simp [b, ha]
  have hright : IntegrableOn
      (fun x : ℝ ↦ Complex.exp ((-a - b * I) * x)) (Ioi 0) := by
    apply integrableOn_exp_mul_complex_Ioi
    simp [b, ha]
  have hleft_eq : ∀ x ∈ Iic (0 : ℝ),
      Complex.exp (↑(-2 * Real.pi * x * w) * I) * laplaceKernel a x =
        Complex.exp ((a - b * I) * x) := by
    intro x hx
    change x ≤ 0 at hx
    unfold laplaceKernel
    rw [← Complex.exp_add]
    congr 1
    simp [abs_of_nonpos hx, b]
    ring
  have hright_eq : ∀ x ∈ Ioi (0 : ℝ),
      Complex.exp (↑(-2 * Real.pi * x * w) * I) * laplaceKernel a x =
        Complex.exp ((-a - b * I) * x) := by
    intro x hx
    change 0 < x at hx
    unfold laplaceKernel
    rw [← Complex.exp_add]
    congr 1
    simp [abs_of_pos hx, b]
    ring
  have hleftI : IntegrableOn
      (fun x : ℝ ↦ Complex.exp (↑(-2 * Real.pi * x * w) * I) *
        laplaceKernel a x) (Iic 0) :=
    hleft.congr_fun (fun x hx ↦ (hleft_eq x hx).symm) measurableSet_Iic
  have hrightI : IntegrableOn
      (fun x : ℝ ↦ Complex.exp (↑(-2 * Real.pi * x * w) * I) *
        laplaceKernel a x) (Ioi 0) :=
    hright.congr_fun (fun x hx ↦ (hright_eq x hx).symm) measurableSet_Ioi
  rw [← intervalIntegral.integral_Iic_add_Ioi hleftI hrightI]
  rw [setIntegral_congr_fun measurableSet_Iic hleft_eq,
    setIntegral_congr_fun measurableSet_Ioi hright_eq]
  rw [integral_exp_mul_complex_Iic (by simp [b, ha]) 0,
    integral_exp_mul_complex_Ioi (by simp [b, ha]) 0]
  simp only [neg_div]
  dsimp only [b]
  push_cast
  have hleftden : (a : ℂ) - (2 * Real.pi * w : ℂ) * I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hrightden : -(a : ℂ) - (2 * Real.pi * w : ℂ) * I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hquad : (a : ℂ) ^ 2 + (2 * Real.pi * w : ℂ) ^ 2 ≠ 0 := by
    have hreal : a ^ 2 + (2 * Real.pi * w) ^ 2 ≠ 0 := by
      positivity
    exact_mod_cast hreal
  apply (eq_div_iff hquad).2
  field_simp [hleftden, hrightden]
  simp only [mul_zero, zero_mul, Complex.exp_zero]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Applying Mathlib's Fourier transform twice reflects an integrable,
continuous function whose Fourier transform is also integrable. -/
theorem fourier_fourier_apply_of_integrable
    {H : ℝ → ℂ} (hH : Integrable H) (hFH : Integrable (FT H))
    (hHcont : Continuous H) (x : ℝ) :
    FT (FT H) x = H (-x) := by
  calc
    FT (FT H) x = IFT (FT H) (-x) := by
      rw [fourierInv_eq_fourier_neg]
      simp
    _ = H (-x) := hH.fourierInv_fourier_eq hFH hHcont.continuousAt

/-- Fourier pairing of the Cauchy kernel with an arbitrary integrable,
continuous function whose Fourier transform is integrable. -/
theorem integral_fourier_laplaceKernel_mul_fourier
    {H : ℝ → ℂ} (hH : Integrable H) (hFH : Integrable (FT H))
    (hHcont : Continuous H) (a : ℝ) (ha : 0 < a) :
    (∫ w : ℝ, FT (laplaceKernel a) w * FT H w) =
      ∫ x : ℝ, laplaceKernel a x * H x := by
  have hpair := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (μ := volume) (ν := volume)
    (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner
    (laplaceKernel_integrable a ha) hFH
  have hpair' : (∫ w : ℝ, FT (laplaceKernel a) w * FT H w) =
      ∫ x : ℝ, laplaceKernel a x * FT (FT H) x := by
    simpa only [smul_eq_mul, flip_innerₗ] using hpair
  calc
    (∫ w : ℝ, FT (laplaceKernel a) w * FT H w) =
        ∫ x : ℝ, laplaceKernel a x * H (-x) := by
      rw [hpair']
      apply integral_congr_ae
      filter_upwards [] with x
      rw [fourier_fourier_apply_of_integrable hH hFH hHcont]
    _ = ∫ x : ℝ, laplaceKernel a (-x) * H x := by
      simpa only [neg_neg] using
        (MeasureTheory.integral_neg_eq_self
          (fun x : ℝ ↦ laplaceKernel a (-x) * H x) volume)
    _ = _ := by
      simp [laplaceKernel]

private theorem integral_fourier_laplace_mul_fourier
    (H : SchwartzMap ℝ ℂ) (a : ℝ) (ha : 0 < a) :
    (∫ w : ℝ, FT (laplaceKernel a) w * FT H w) =
      ∫ x : ℝ, laplaceKernel a x * H x :=
  integral_fourier_laplaceKernel_mul_fourier
    H.integrable (FT H).integrable H.continuous a ha

private theorem bombieriMellin_laplaceKernel_frequency
    (f : BombieriTest) (a : ℝ) (ha : 0 < a) :
    (∫ w : ℝ,
        (2 * a : ℂ) /
            ((a : ℂ) ^ 2 + (2 * Real.pi * w : ℂ) ^ 2) *
          mellin (f : ℝ → ℂ)
            ((1 / 2 : ℝ) + (2 * Real.pi * w) * I)) =
      ∫ x : ℝ, laplaceKernel a x *
        f.logarithmicPullbackSchwartz (1 / 2) x := by
  rw [← integral_fourier_laplace_mul_fourier
    (f.logarithmicPullbackSchwartz (1 / 2)) a ha]
  apply integral_congr_ae
  filter_upwards [] with w
  rw [fourier_laplaceKernel a w ha]
  congr 1
  simpa using bombieriMellin_vertical_eq_fourier
    f (1 / 2) (2 * Real.pi * w)

private theorem bombieriMellin_cauchyKernel_integral
    (f : BombieriTest) (a : ℝ) (ha : 0 < a) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ,
          (2 * a : ℂ) / ((a : ℂ) ^ 2 + (v : ℂ) ^ 2) *
            mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I) =
      ∫ x : ℝ, laplaceKernel a x *
        f.logarithmicPullbackSchwartz (1 / 2) x := by
  let G : ℝ → ℂ := fun v ↦
    (2 * a : ℂ) / ((a : ℂ) ^ 2 + (v : ℂ) ^ 2) *
      mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I)
  have hscale := Measure.integral_comp_mul_left G (2 * Real.pi)
  calc
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ v : ℝ, G v =
        |(2 * Real.pi)⁻¹| • ∫ v : ℝ, G v := by
      rw [Complex.real_smul]
      congr 1
      rw [abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) Real.pi_pos))]
      push_cast
      rw [one_div]
    _ = ∫ w : ℝ, G ((2 * Real.pi) * w) := hscale.symm
    _ = _ := by
      simpa only [G, ofReal_mul] using
        bombieriMellin_laplaceKernel_frequency f a ha

/-- Bombieri's multiplicative Cauchy weight.  On the positive half-line it
is `min(x, x⁻¹)^a`; the exponential form is convenient at the logarithmic
Fourier coordinate. -/
def bombieriCauchyWeight (f : BombieriTest) (a x : ℝ) : ℂ :=
  (Real.exp (-a * |Real.log x|) : ℂ) * f x

/-- The source-oriented positive-half-line form of `bombieriCauchyWeight`. -/
theorem bombieriCauchyWeight_apply_of_pos
    (f : BombieriTest) (a : ℝ) {x : ℝ} (hx : 0 < x) :
    bombieriCauchyWeight f a x = ((min x x⁻¹) ^ a : ℝ) • f x := by
  have hmin_pos : 0 < min x x⁻¹ := lt_min hx (inv_pos.mpr hx)
  have hexp : Real.exp (-a * |Real.log x|) = (min x x⁻¹) ^ a := by
    rw [Real.rpow_def_of_pos hmin_pos]
    congr 1
    by_cases hle : x ≤ 1
    · have hxx : x ≤ x⁻¹ := by
        rw [inv_eq_one_div]
        exact (le_div_iff₀ hx).2 (by nlinarith)
      rw [min_eq_left hxx]
      rw [abs_of_nonpos (Real.log_nonpos hx.le hle)]
      ring
    · have hone : 1 ≤ x := (lt_of_not_ge hle).le
      have hxx : x⁻¹ ≤ x := by
        rw [inv_eq_one_div]
        exact (div_le_iff₀ hx).2 (by nlinarith)
      rw [min_eq_right hxx, Real.log_inv]
      rw [abs_of_nonneg (Real.log_nonneg hone)]
      ring
  rw [bombieriCauchyWeight, hexp, Complex.real_smul]

/-- Multiplication by the Cauchy weight preserves Mellin convergence.  This
is unconditional because the original Bombieri test has compact support in
the positive half-line. -/
theorem bombieriCauchyWeight_mellinConvergent
    (f : BombieriTest) (a : ℝ) (s : ℂ) :
    MellinConvergent (bombieriCauchyWeight f a) s := by
  let F : ℝ → ℂ := fun x ↦
    (x : ℂ) ^ (s - 1) * bombieriCauchyWeight f a x
  have hF_cont : ContinuousOn F (tsupport f) := by
    intro x hx
    have hx_pos : 0 < x := f.tsupport_subset hx
    have hlog : ContinuousAt Real.log x :=
      Real.continuousAt_log hx_pos.ne'
    have hrealWeight : ContinuousAt
        (fun y : ℝ ↦ Real.exp (-a * |Real.log y|)) x :=
      Real.continuous_exp.continuousAt.comp
        (continuousAt_const.mul hlog.abs)
    have hweight : ContinuousAt
        (fun y : ℝ ↦ (Real.exp (-a * |Real.log y|) : ℂ)) x :=
      Complex.ofRealCLM.continuous.continuousAt.comp hrealWeight
    exact ((Complex.continuousAt_ofReal_cpow_const x (s - 1)
      (Or.inr hx_pos.ne')).mul
        (hweight.mul f.contDiff.continuous.continuousAt)).continuousWithinAt
  have hF_integrableOn : IntegrableOn F (tsupport f) :=
    hF_cont.integrableOn_compact f.hasCompactSupport
  have hF_support : Function.support F ⊆ tsupport f := by
    intro x hx
    apply subset_tsupport f
    apply Function.mem_support.mpr
    intro hfx
    apply hx
    simp [F, bombieriCauchyWeight, hfx]
  have hF_integrable : Integrable F :=
    (integrableOn_iff_integrable_of_support_subset hF_support).mp hF_integrableOn
  change IntegrableOn F (Ioi 0)
  exact hF_integrable.integrableOn

private theorem mellin_bombieriCauchyWeight_eq_log_integral
    (f : BombieriTest) (a σ : ℝ) :
    mellin (bombieriCauchyWeight f a) σ =
      ∫ u : ℝ, laplaceKernel a u *
        f.logarithmicPullbackSchwartz σ u := by
  rw [mellin_eq_fourier]
  rw [fourier_real_eq]
  simp only [ofReal_re, ofReal_im, zero_div, mul_zero, neg_zero]
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [bombieriCauchyWeight,
    BombieriTest.logarithmicPullbackSchwartz_apply,
    BombieriTest.logarithmicPullback]
  rw [Real.log_exp]
  simp only [abs_neg]
  unfold laplaceKernel
  rw [show Real.fourierChar (0 : ℝ) = 1 by simp]
  simp only [one_smul]
  change (Real.exp (-σ * u) : ℂ) *
      ((Real.exp (-a * |u|) : ℂ) * f (Real.exp (-u))) = _
  simp only [ofReal_exp, ofReal_neg, ofReal_mul]
  ring

/-- The Cauchy kernel times a vertical Bombieri--Mellin transform is Bochner
integrable. -/
theorem bombieriMellin_cauchyKernel_integrable
    (f : BombieriTest) (a : ℝ) (ha : 0 < a) :
    Integrable (fun v : ℝ ↦
      (2 * a : ℂ) / ((a : ℂ) ^ 2 + (v : ℂ) ^ 2) *
        mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I)) := by
  let K : ℝ → ℂ := fun v ↦
    (2 * a : ℂ) / ((a : ℂ) ^ 2 + (v : ℂ) ^ 2)
  have hden (v : ℝ) : (a : ℂ) ^ 2 + (v : ℂ) ^ 2 ≠ 0 := by
    have hreal : a ^ 2 + v ^ 2 ≠ 0 := by positivity
    exact_mod_cast hreal
  have hK_cont : Continuous K := by
    exact continuous_const.div
      (continuous_const.add (Complex.ofRealCLM.continuous.pow 2)) hden
  have hK_fourier (v : ℝ) :
      K v = FT (laplaceKernel a) (v / (2 * Real.pi)) := by
    rw [fourier_laplaceKernel a (v / (2 * Real.pi)) ha]
    simp only [K]
    congr 2
    push_cast
    congr 1
    field_simp [Real.pi_ne_zero]
  let C : ℝ := ∫ x : ℝ, ‖laplaceKernel a x‖
  have hK_bound : ∀ v : ℝ, ‖K v‖ ≤ C := by
    intro v
    rw [hK_fourier v]
    exact VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ ℝ) (laplaceKernel a)
        (v / (2 * Real.pi))
  have hM := f.mellin_verticalIntegrable (1 / 2)
  have hprod := hM.mul_bdd (c := C) hK_cont.aestronglyMeasurable
    (Filter.Eventually.of_forall hK_bound)
  simpa only [K, mul_comm] using hprod

/-- Bombieri's Cauchy-kernel average on the critical line equals the Mellin
transform after multiplication by the positive weight `min(x, x⁻¹)^a`.
The factor `1/(2π)` matches Mathlib's Fourier normalization. -/
theorem bombieriMellin_cauchyKernel_eq_weightedMellin
    (f : BombieriTest) (a : ℝ) (ha : 0 < a) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ,
          (2 * a : ℂ) / ((a : ℂ) ^ 2 + (v : ℂ) ^ 2) *
            mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I) =
      mellin (bombieriCauchyWeight f a) (1 / 2 : ℝ) := by
  rw [bombieriMellin_cauchyKernel_integral f a ha,
    mellin_bombieriCauchyWeight_eq_log_integral]

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
