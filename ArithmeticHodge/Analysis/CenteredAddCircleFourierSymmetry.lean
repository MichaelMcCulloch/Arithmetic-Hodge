import ArithmeticHodge.Analysis.CenteredAddCircleFourierBasic

set_option autoImplicit false

noncomputable section

open Complex MeasureTheory
open scoped ComplexConjugate

namespace ArithmeticHodge.Analysis

variable {T : ℝ} [hT : Fact (0 < T)]

theorem fourierCoeff_conj_apply (f : AddCircle T → ℂ) (n : ℤ) :
    fourierCoeff (fun x => conj (f x)) n =
      conj (fourierCoeff f (-n)) := by
  simp only [fourierCoeff, neg_neg, smul_eq_mul]
  calc
    (∫ t : AddCircle T, fourier (-n) t * conj (f t)
        ∂AddCircle.haarAddCircle) =
        ∫ t : AddCircle T, conj (fourier n t * f t)
          ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [map_mul, fourier_neg]
    _ = conj (∫ t : AddCircle T, fourier n t * f t
          ∂AddCircle.haarAddCircle) := integral_conj

omit hT in
private theorem fourier_neg_input (n : ℤ) (x : ℝ) :
    fourier n ((-x : ℝ) : AddCircle T) =
      fourier (-n) (x : AddCircle T) := by
  simp only [fourier_apply, AddCircle.coe_neg, smul_neg, neg_smul]

theorem fourierCoeff_comp_neg (f : AddCircle T → ℂ) (n : ℤ) :
    fourierCoeff (fun x => f (-x)) n = fourierCoeff f (-n) := by
  rw [fourierCoeff_eq_intervalIntegral _ _ (-(T / 2)),
    fourierCoeff_eq_intervalIntegral _ _ (-(T / 2))]
  have hcenter : -(T / 2) + T = T / 2 := by ring
  rw [hcenter]
  congr 1
  simp only [neg_neg, smul_eq_mul]
  calc
    (∫ x : ℝ in -(T / 2)..T / 2,
        fourier (-n) (x : AddCircle T) * f (-(x : AddCircle T))) =
        ∫ x : ℝ in -(T / 2)..T / 2,
          fourier n ((-x : ℝ) : AddCircle T) *
            f ((-x : ℝ) : AddCircle T) := by
      apply intervalIntegral.integral_congr
      intro x _
      change fourier (-n) (x : AddCircle T) * f (-(x : AddCircle T)) =
        fourier n ((-x : ℝ) : AddCircle T) *
          f ((-x : ℝ) : AddCircle T)
      rw [fourier_neg_input]
      rfl
    _ = ∫ x : ℝ in -(T / 2)..T / 2,
          fourier n (x : AddCircle T) * f (x : AddCircle T) := by
      simpa using intervalIntegral.integral_comp_neg
        (a := -(T / 2)) (b := T / 2)
        (fun x : ℝ => fourier n (x : AddCircle T) * f (x : AddCircle T))

theorem centeredFourierCoeff_conj
    {a : ℝ} (ha : 0 < a) (f : ℝ → ℂ) (n : ℤ) :
    centeredFourierCoeff ha (fun x => conj (f x)) n =
      conj (centeredFourierCoeff ha f (-n)) := by
  haveI : Fact (0 < a - -a) := ⟨by linarith⟩
  unfold centeredFourierCoeff fourierCoeffOn
  exact fourierCoeff_conj_apply (AddCircle.liftIoc (a - -a) (-a) f) n

theorem centeredFourierCoeff_reflect
    {a : ℝ} (ha : 0 < a) (f : ℝ → ℂ) (n : ℤ) :
    centeredFourierCoeff ha (fun x => f (-x)) n =
      centeredFourierCoeff ha f (-n) := by
  have hp : 0 < a - -a := by linarith
  letI : Fact (0 < a - -a) := ⟨hp⟩
  unfold centeredFourierCoeff
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  congr 1
  simp only [neg_neg, smul_eq_mul]
  calc
    (∫ x : ℝ in -a..a,
        fourier (-n) (x : AddCircle (a - -a)) * f (-x)) =
        ∫ x : ℝ in -a..a,
          fourier n ((-x : ℝ) : AddCircle (a - -a)) * f (-x) := by
      apply intervalIntegral.integral_congr
      intro x _
      change fourier (-n) (x : AddCircle (a - -a)) * f (-x) =
        fourier n ((-x : ℝ) : AddCircle (a - -a)) * f (-x)
      rw [fourier_neg_input]
    _ = ∫ x : ℝ in -a..a,
          fourier n (x : AddCircle (a - -a)) * f x := by
      simpa using intervalIntegral.integral_comp_neg
        (a := -a) (b := a)
        (fun x : ℝ => fourier n (x : AddCircle (a - -a)) * f x)

theorem centeredFourierCoeff_even
    {a : ℝ} (ha : 0 < a) (f : ℝ → ℂ)
    (hf : ∀ x, f (-x) = f x) (n : ℤ) :
    centeredFourierCoeff ha f (-n) = centeredFourierCoeff ha f n := by
  rw [← centeredFourierCoeff_reflect ha f n]
  congr 1
  funext x
  exact hf x

theorem centeredFourierCoeff_real
    {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ) (n : ℤ) :
    centeredFourierCoeff ha (fun x => (f x : ℂ)) (-n) =
      conj (centeredFourierCoeff ha (fun x => (f x : ℂ)) n) := by
  simpa only [neg_neg, conj_ofReal] using
    centeredFourierCoeff_conj ha (fun x => (f x : ℂ)) (-n)

end ArithmeticHodge.Analysis
