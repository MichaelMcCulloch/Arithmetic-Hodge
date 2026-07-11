import ArithmeticHodge.Analysis.MultiplicativeWeilMellinFourier
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false

open Complex MeasureTheory Real Set
open scoped FourierTransform

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

private def laplaceKernel (a x : ℝ) : ℂ :=
  Complex.exp (-(a : ℂ) * (↑|x| : ℂ))

private theorem laplaceKernel_integrable (a : ℝ) (ha : 0 < a) :
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

private theorem fourier_laplaceKernel (a w : ℝ) (ha : 0 < a) :
    𝓕 (laplaceKernel a) w =
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
    simp [laplaceKernel, abs_of_nonpos hx, b]
    ring
  have hright_eq : ∀ x ∈ Ioi (0 : ℝ),
      Complex.exp (↑(-2 * Real.pi * x * w) * I) * laplaceKernel a x =
        Complex.exp ((-a - b * I) * x) := by
    intro x hx
    change 0 < x at hx
    unfold laplaceKernel
    rw [← Complex.exp_add]
    congr 1
    simp [laplaceKernel, abs_of_pos hx, b]
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
  simp only [mul_zero, Complex.exp_zero, neg_div]
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

private theorem fourier_fourier_schwartz_apply
    (H : SchwartzMap ℝ ℂ) (x : ℝ) :
    𝓕 ((𝓕 H : SchwartzMap ℝ ℂ) : ℝ → ℂ) x = H (-x) := by
  calc
    𝓕 ((𝓕 H : SchwartzMap ℝ ℂ) : ℝ → ℂ) x =
        𝓕⁻ ((𝓕 H : SchwartzMap ℝ ℂ) : ℝ → ℂ) (-x) := by
      rw [fourierInv_eq_fourier_neg]
      simp
    _ = H (-x) := H.integrable.fourierInv_fourier_eq
      (𝓕 H).integrable H.continuous.continuousAt

private theorem integral_fourier_laplace_mul_fourier
    (H : SchwartzMap ℝ ℂ) (a : ℝ) (ha : 0 < a) :
    (∫ w : ℝ, 𝓕 (laplaceKernel a) w * 𝓕 H w) =
      ∫ x : ℝ, laplaceKernel a x * H x := by
  have hpair := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (μ := volume) (ν := volume)
    (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner
    (laplaceKernel_integrable a ha) (𝓕 H).integrable
  have hpair' : (∫ w : ℝ, 𝓕 (laplaceKernel a) w * 𝓕 H w) =
      ∫ x : ℝ, laplaceKernel a x *
        𝓕 ((𝓕 H : SchwartzMap ℝ ℂ) : ℝ → ℂ) x := by
    simpa only [smul_eq_mul, flip_innerₗ] using hpair
  calc
    (∫ w : ℝ, 𝓕 (laplaceKernel a) w * 𝓕 H w) =
        ∫ x : ℝ, laplaceKernel a x * H (-x) := by
      rw [hpair']
      apply integral_congr_ae
      filter_upwards [] with x
      rw [fourier_fourier_schwartz_apply]
    _ = ∫ x : ℝ, laplaceKernel a (-x) * H x := by
      simpa only [neg_neg] using
        (MeasureTheory.integral_neg_eq_self
          (fun x : ℝ ↦ laplaceKernel a (-x) * H x) volume)
    _ = _ := by
      simp [laplaceKernel]

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

private def multiplicativeLaplaceWeight
    (f : BombieriTest) (a x : ℝ) : ℂ :=
  (Real.exp (-a * |Real.log x|) : ℂ) * f x

private theorem mellin_multiplicativeLaplaceWeight_eq_log_integral
    (f : BombieriTest) (a σ : ℝ) :
    mellin (multiplicativeLaplaceWeight f a) σ =
      ∫ u : ℝ, laplaceKernel a u *
        f.logarithmicPullbackSchwartz σ u := by
  rw [mellin_eq_fourier]
  rw [fourier_real_eq]
  simp only [ofReal_re, ofReal_im, zero_div, mul_zero, neg_zero,
    map_zero, one_smul]
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [multiplicativeLaplaceWeight,
    BombieriTest.logarithmicPullbackSchwartz_apply,
    BombieriTest.logarithmicPullback, Complex.real_smul]
  rw [Real.log_exp]
  simp only [abs_neg]
  unfold laplaceKernel
  rw [show 𝐞 (0 : ℝ) = 1 by simp]
  simp only [one_smul]
  change (Real.exp (-σ * u) : ℂ) *
      ((Real.exp (-a * |u|) : ℂ) * f (Real.exp (-u))) = _
  simp only [ofReal_exp, ofReal_neg, ofReal_mul]
  ring

private theorem bombieriMellin_cauchyKernel_eq_weightedMellin
    (f : BombieriTest) (a : ℝ) (ha : 0 < a) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ,
          (2 * a : ℂ) / ((a : ℂ) ^ 2 + (v : ℂ) ^ 2) *
            mellin (f : ℝ → ℂ) ((1 / 2 : ℝ) + v * I) =
      mellin (multiplicativeLaplaceWeight f a) (1 / 2 : ℝ) := by
  rw [bombieriMellin_cauchyKernel_integral f a ha,
    mellin_multiplicativeLaplaceWeight_eq_log_integral]

#print axioms fourier_laplaceKernel
#print axioms integral_fourier_laplace_mul_fourier
#print axioms bombieriMellin_laplaceKernel_frequency
#print axioms bombieriMellin_cauchyKernel_integral
#print axioms mellin_multiplicativeLaplaceWeight_eq_log_integral
#print axioms bombieriMellin_cauchyKernel_eq_weightedMellin

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
