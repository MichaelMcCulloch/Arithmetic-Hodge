import ArithmeticHodge.Analysis.HermitianScalarDeterminant
import ArithmeticHodge.Analysis.MultiplicativeWeilRestrictedSupportEndpointPositive
import ArithmeticHodge.Analysis.MultiplicativeWeilTwoBumpCrossFormula

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ContDiff Distributions

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

open ArithmeticHodge.Analysis
open ArithmeticHodge.Analysis.MultiplicativeWeilRestrictedSupportEndpointPositive

noncomputable section

/-!
# Exact adjacent two-seed factor-two reduction

The usual factor-two family uses one seed twice.  This file keeps the two
seeds independent.  Real polarization recovers the complex mixed prime
symbol from its values in the `1` and `I` directions.  The resulting global
cross gives an exact Hermitian quadratic for

`f + c • normalizedDilation 2 (by norm_num) g`.

No same-seed estimate controls this cross.  Under separate honest
ratio-at-most-two support hypotheses for `f` and `g`, positivity of the whole
complex scalar family is equivalent to the unequal-diagonal determinant
bound.
-/

/-- Complex polarization of the mixed prime functional.  Only real parts of
the two symmetric mixed tests are needed, in the directions `1` and `I`. -/
def bombieriPolarizedPrimeCross (f h : BombieriTest) : ℂ :=
  (((primeSum (bombieriQuadraticCrossTest f h)).re / 2 : ℝ) : ℂ) -
    (((primeSum
      (bombieriQuadraticCrossTest f (Complex.I • h))).re / 2 : ℝ) : ℂ) *
      Complex.I

/-- The honest adjacent two-seed factor-two cross: local Hermitian cross
minus the polarized mixed prime contribution. -/
def factorTwoTwoSeedGlobalCrossSymbol (f g : BombieriTest) : ℂ :=
  bombieriLocalCriticalForm f
      (normalizedDilation 2 (by norm_num) g) -
    bombieriPolarizedPrimeCross f
      (normalizedDilation 2 (by norm_num) g)

/-- Real polarization of a mixed quadratic test in its second seed. -/
theorem bombieriQuadraticCrossTest_smul_eq_re_im_polarization
    (f h : BombieriTest) (c : ℂ) :
    bombieriQuadraticCrossTest f (c • h) =
      (c.re : ℂ) • bombieriQuadraticCrossTest f h +
        (c.im : ℂ) •
          bombieriQuadraticCrossTest f (Complex.I • h) := by
  ext x
  simp only [TestFunction.coe_add, Pi.add_apply, TestFunction.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  rw [bombieriQuadraticCrossTest_apply,
    bombieriQuadraticCrossTest_apply,
    bombieriQuadraticCrossTest_apply]
  simp only [bombieriDirectedCorrelation_smul_left,
    bombieriDirectedCorrelation_smul_right]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
      Complex.I_re, Complex.I_im, zero_mul, sub_zero]
    ring
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
      Complex.I_re, Complex.I_im, zero_mul, add_zero, zero_add]
    ring

/-- Applying the prime functional to real polarization recovers twice the
real part of the scalar times the polarized prime symbol. -/
theorem primeSum_bombieriQuadraticCrossTest_smul_re_eq_polarized
    (f h : BombieriTest) (c : ℂ) :
    (primeSum (bombieriQuadraticCrossTest f (c • h))).re =
      2 * (c * bombieriPolarizedPrimeCross f h).re := by
  rw [bombieriQuadraticCrossTest_smul_eq_re_im_polarization,
    primeSum_add, primeSum_smul, primeSum_smul]
  unfold bombieriPolarizedPrimeCross
  simp only [Complex.add_re, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    zero_mul, mul_zero, add_zero, sub_zero]
  ring

/-- On the original one-seed family, real polarization recovers exactly the
production factor-two prime symbol.  This is a compatibility statement, not
an estimate for independent seeds. -/
theorem bombieriPolarizedPrimeCross_sameSeed_factorTwo
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    bombieriPolarizedPrimeCross g
        (normalizedDilation 2 (by norm_num) g) =
      factorTwoPrimeCrossSymbol g := by
  have hone :=
    primeSum_bombieriQuadraticCrossTest_smul_dilation_two_eq
      g (1 : ℂ) ha hab hsupport hratio
  have hI :=
    primeSum_bombieriQuadraticCrossTest_smul_dilation_two_eq
      g Complex.I ha hab hsupport hratio
  simp only [one_smul, one_mul] at hone
  unfold bombieriPolarizedPrimeCross
  rw [hone, hI]
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul,
      mul_zero, sub_zero]
    ring
  · simp only [Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, add_zero]
    ring

/-- Consequently the two-seed symbol specializes to the existing production
global cross when the seeds coincide. -/
theorem factorTwoTwoSeedGlobalCrossSymbol_sameSeed
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    factorTwoTwoSeedGlobalCrossSymbol g g =
      factorTwoGlobalCrossSymbol g := by
  unfold factorTwoTwoSeedGlobalCrossSymbol factorTwoGlobalCrossSymbol
  rw [bombieriPolarizedPrimeCross_sameSeed_factorTwo
    g ha hab hsupport hratio]

/-- The local Hermitian cross has the same real-polarization law. -/
theorem bombieriLocalCriticalForm_smul_cross_re
    (f h : BombieriTest) (c : ℂ) :
    (bombieriLocalCriticalForm f (c • h) +
        bombieriLocalCriticalForm (c • h) f).re =
      2 * (c * bombieriLocalCriticalForm f h).re := by
  simp only [map_smul, smul_eq_mul]
  have hleft := LinearMap.map_smulₛₗ₂
    bombieriLocalCriticalForm c h f
  simp only [smul_eq_mul] at hleft
  rw [hleft]
  rw [← bombieriLocalCriticalForm_conj_apply h f]
  simp only [Complex.add_re, Complex.mul_re, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  ring

/-- Support-free exact mixed functional for two independent adjacent seeds. -/
theorem bombieriFunctional_quadraticCross_twoSeedFactorTwo_re
    (f g : BombieriTest) (c : ℂ) :
    (bombieriFunctional
      (bombieriQuadraticCrossTest f
        (c • normalizedDilation 2 (by norm_num) g))).re =
      2 * (c * factorTwoTwoSeedGlobalCrossSymbol f g).re := by
  rw [bombieriFunctional_quadraticCross_eq_localCross_sub_prime]
  simp only [Complex.sub_re]
  rw [bombieriLocalCriticalForm_smul_cross_re,
    primeSum_bombieriQuadraticCrossTest_smul_re_eq_polarized]
  unfold factorTwoTwoSeedGlobalCrossSymbol
  simp only [mul_sub, Complex.sub_re]

/-- Exact unequal-diagonal Hermitian expansion for the adjacent two-seed
factor-two family.  It is independent of support assumptions. -/
theorem bombieriFunctional_twoSeedFactorTwo_re
    (f g : BombieriTest) (c : ℂ) :
    (bombieriFunctional
      (bombieriQuadraticTest
        (f + c • normalizedDilation 2 (by norm_num) g))).re =
      (bombieriFunctional (bombieriQuadraticTest f)).re +
        Complex.normSq c *
          (bombieriFunctional (bombieriQuadraticTest g)).re +
        2 * (c * factorTwoTwoSeedGlobalCrossSymbol f g).re := by
  rw [bombieriFunctional_quadratic_add_eq_diagonal_add_cross,
    bombieriFunctional_quadratic_smul_normalizedDilation]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  rw [bombieriFunctional_quadraticCross_twoSeedFactorTwo_re]
  simp only [Complex.mul_re]

/-! ## The unequal-diagonal scalar determinant -/

/-- The scalar Hermitian quadratic with independent diagonal coefficients. -/
def twoSeedHermitianValue (A B : ℝ) (Z c : ℂ) : ℝ :=
  A + Complex.normSq c * B + 2 * (c * Z).re

/-- Completion of the square using the second diagonal. -/
theorem twoSeedHermitian_completedSquare
    (A B : ℝ) (Z c : ℂ) :
    B * twoSeedHermitianValue A B Z c =
      Complex.normSq ((B : ℂ) * c + starRingEnd ℂ Z) +
        A * B - Complex.normSq Z := by
  unfold twoSeedHermitianValue
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im]
  ring

/-- Nonnegativity in every complex scalar direction is exactly the honest
unequal-diagonal determinant inequality. -/
theorem twoSeedHermitian_nonneg_iff
    (A B : ℝ) (Z : ℂ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (∀ c : ℂ, 0 ≤ twoSeedHermitianValue A B Z c) ↔
      Complex.normSq Z ≤ A * B := by
  constructor
  · intro hall
    by_cases hBzero : B = 0
    · subst B
      have hZzero : Z = 0 := by
        by_contra hZ
        have hZsqpos : 0 < Complex.normSq Z :=
          Complex.normSq_pos.mpr hZ
        let t : ℝ := (A + 1) / (2 * Complex.normSq Z)
        let c₀ : ℂ := -((t : ℂ) * starRingEnd ℂ Z)
        have hvalue := hall c₀
        have hcross : (c₀ * Z).re = -t * Complex.normSq Z := by
          dsimp only [c₀]
          simp only [Complex.neg_re, Complex.neg_im, Complex.mul_re,
            Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
            Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
          ring
        have ht : 2 * t * Complex.normSq Z = A + 1 := by
          dsimp only [t]
          field_simp [hZsqpos.ne']
        unfold twoSeedHermitianValue at hvalue
        simp only [mul_zero, add_zero] at hvalue
        rw [hcross] at hvalue
        nlinarith
      subst Z
      simp
    · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hBzero)
      let c₀ : ℂ := -((B : ℂ)⁻¹ * starRingEnd ℂ Z)
      have hBc : (B : ℂ) * c₀ + starRingEnd ℂ Z = 0 := by
        dsimp only [c₀]
        have hBcne : (B : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr hBpos.ne'
        rw [mul_neg, ← mul_assoc, mul_inv_cancel₀ hBcne, one_mul,
          neg_add_cancel]
      have hvalue := hall c₀
      have hscaled : 0 ≤ B * twoSeedHermitianValue A B Z c₀ :=
        mul_nonneg hB hvalue
      rw [twoSeedHermitian_completedSquare, hBc,
        Complex.normSq_zero, zero_add] at hscaled
      linarith
  · intro hdet c
    by_cases hBzero : B = 0
    · subst B
      have hZsq : Complex.normSq Z = 0 :=
        le_antisymm (by simpa using hdet) (Complex.normSq_nonneg Z)
      have hZ : Z = 0 := Complex.normSq_eq_zero.mp hZsq
      subst Z
      simpa [twoSeedHermitianValue] using hA
    · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hBzero)
      have hsquare :
          0 ≤ Complex.normSq ((B : ℂ) * c + starRingEnd ℂ Z) +
              A * B - Complex.normSq Z := by
        nlinarith [Complex.normSq_nonneg
          ((B : ℂ) * c + starRingEnd ℂ Z)]
      have hscaled : 0 ≤ B * twoSeedHermitianValue A B Z c := by
        rw [twoSeedHermitian_completedSquare]
        exact hsquare
      exact (mul_nonneg_iff_of_pos_left hBpos).mp hscaled

/-! ## Structural two-seed factor-two criterion -/

/-- Under separate honest support hypotheses for the two seeds, the adjacent
two-seed family is nonnegative for every complex scalar exactly when its
polarized cross satisfies the unequal-diagonal contraction bound. -/
theorem bombieriFunctional_twoSeedFactorTwo_nonneg_iff
    (f g : BombieriTest) {a₁ b₁ a₂ b₂ : ℝ}
    (ha₁ : 0 < a₁) (hab₁ : a₁ ≤ b₁)
    (hsupport₁ : tsupport f ⊆ Set.Icc a₁ b₁)
    (hratio₁ : b₁ / a₁ ≤ 2)
    (ha₂ : 0 < a₂) (hab₂ : a₂ ≤ b₂)
    (hsupport₂ : tsupport g ⊆ Set.Icc a₂ b₂)
    (hratio₂ : b₂ / a₂ ≤ 2) :
    (∀ c : ℂ,
      0 ≤ (bombieriFunctional
        (bombieriQuadraticTest
          (f + c • normalizedDilation 2 (by norm_num) g))).re) ↔
      Complex.normSq (factorTwoTwoSeedGlobalCrossSymbol f g) ≤
        (bombieriFunctional (bombieriQuadraticTest f)).re *
          (bombieriFunctional (bombieriQuadraticTest g)).re := by
  have hA : 0 ≤ (bombieriFunctional (bombieriQuadraticTest f)).re :=
    bombieriFunctional_quadratic_re_nonneg_of_ratio_le_two
      f ha₁ hab₁ hsupport₁ hratio₁
  have hB : 0 ≤ (bombieriFunctional (bombieriQuadraticTest g)).re :=
    bombieriFunctional_quadratic_re_nonneg_of_ratio_le_two
      g ha₂ hab₂ hsupport₂ hratio₂
  simpa only [bombieriFunctional_twoSeedFactorTwo_re,
    twoSeedHermitianValue] using
    twoSeedHermitian_nonneg_iff
      (bombieriFunctional (bombieriQuadraticTest f)).re
      (bombieriFunctional (bombieriQuadraticTest g)).re
      (factorTwoTwoSeedGlobalCrossSymbol f g) hA hB

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
