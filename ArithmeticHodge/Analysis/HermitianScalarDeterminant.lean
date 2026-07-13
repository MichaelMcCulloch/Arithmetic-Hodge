import ArithmeticHodge.Analysis.MultiplicativeWeilTwoBumpFunctional

set_option autoImplicit false

open Complex

namespace ArithmeticHodge.Analysis

noncomputable section

/-!
# Scalar Hermitian determinant criterion

This file isolates the exact two-dimensional algebra used by the factor-two
Bombieri family.  Positivity for every complex scalar is equivalent to one
determinant inequality; strict failure is equivalent to an explicit negative
direction.
-/

def hermitianScalarValue (A : ℝ) (Z c : ℂ) : ℝ :=
  (1 + Complex.normSq c) * A + 2 * (c * Z).re

theorem hermitianScalar_completedSquare (A : ℝ) (Z c : ℂ) :
    A * hermitianScalarValue A Z c =
      Complex.normSq ((A : ℂ) * c + starRingEnd ℂ Z) +
        A ^ 2 - Complex.normSq Z := by
  unfold hermitianScalarValue
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im]
  ring

theorem hermitianScalar_nonneg_iff
    (A : ℝ) (Z : ℂ) (hA : 0 ≤ A) :
    (∀ c : ℂ, 0 ≤ hermitianScalarValue A Z c) ↔
      Complex.normSq Z ≤ A ^ 2 := by
  constructor
  · intro hall
    by_cases hAzero : A = 0
    · subst A
      have hvalue := hall (-starRingEnd ℂ Z)
      have hcross :
          ((-starRingEnd ℂ Z) * Z).re = -Complex.normSq Z := by
        simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im,
          Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
        ring
      unfold hermitianScalarValue at hvalue
      rw [hcross] at hvalue
      norm_num at hvalue ⊢
      linarith
    · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAzero)
      let c₀ : ℂ := -((A : ℂ)⁻¹ * starRingEnd ℂ Z)
      have hAc : (A : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr hApos.ne'
      have hc₀ : (A : ℂ) * c₀ + starRingEnd ℂ Z = 0 := by
        dsimp only [c₀]
        rw [mul_neg, ← mul_assoc, mul_inv_cancel₀ hAc, one_mul,
          neg_add_cancel]
      have hvalue := hall c₀
      have hscaled : 0 ≤ A * hermitianScalarValue A Z c₀ :=
        mul_nonneg hA hvalue
      rw [hermitianScalar_completedSquare, hc₀,
        Complex.normSq_zero, zero_add] at hscaled
      linarith
  · intro hdet c
    by_cases hAzero : A = 0
    · subst A
      have hzsq : Complex.normSq Z = 0 :=
        le_antisymm (by simpa using hdet) (Complex.normSq_nonneg Z)
      have hz : Z = 0 := Complex.normSq_eq_zero.mp hzsq
      subst Z
      simp [hermitianScalarValue]
    · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAzero)
      have hsquare :
          0 ≤ Complex.normSq ((A : ℂ) * c + starRingEnd ℂ Z) +
              A ^ 2 - Complex.normSq Z := by
        nlinarith [Complex.normSq_nonneg
          ((A : ℂ) * c + starRingEnd ℂ Z)]
      have hscaled : 0 ≤ A * hermitianScalarValue A Z c := by
        rw [hermitianScalar_completedSquare]
        exact hsquare
      exact (mul_nonneg_iff_of_pos_left hApos).mp hscaled

theorem exists_hermitianScalar_neg_iff
    (A : ℝ) (Z : ℂ) (hA : 0 ≤ A) :
    (∃ c : ℂ, hermitianScalarValue A Z c < 0) ↔
      A ^ 2 < Complex.normSq Z := by
  classical
  simpa only [not_forall, not_le] using
    not_congr (hermitianScalar_nonneg_iff A Z hA)

end

end ArithmeticHodge.Analysis
