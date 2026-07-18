import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorDirectAtanhRationalStructural

set_option autoImplicit false

open Matrix MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorDirectAtanhPolynomialLoewnerStructural

noncomputable section

open FiniteIntervalMultiplierGramLoewnerStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorDirectAtanhLoewnerStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorDirectAtanhRationalStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorGramStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorQuotientStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorReciprocalLoewnerStructural

/-!
# Polynomial Loewner majorant for the direct retained atanh weight

The degree-twelve polynomial below majorizes the reciprocal of the direct
two-term atanh weight.  Its proof is one exact Bernstein-form identity on
`y = x² ∈ [0,1]`.  The resulting polynomial multiplier Gram still dominates
the exact selector Gram in full Loewner order.
-/

/-- Degree-twelve reciprocal majorant in `y = x²`. -/
def directP6RetainedEvenAtanhReciprocalMajorantPolynomial (y : ℝ) : ℝ :=
  (1 / 10000000000 : ℝ) *
    (76923076924 - 145617603551 * y + 202849522255 * y ^ 2 -
      294710036225 * y ^ 3 + 421376308419 * y ^ 4 -
      599317271003 * y ^ 5 + 808303816338 * y ^ 6 -
      954869647945 * y ^ 7 + 906267634041 * y ^ 8 -
      638236787837 * y ^ 9 + 307543123575 * y ^ 10 -
      89628564269 * y ^ 11 + 11835030233 * y ^ 12)

def directP6RetainedEvenAtanhReciprocalMajorant (x : ℝ) : ℝ :=
  directP6RetainedEvenAtanhReciprocalMajorantPolynomial (x ^ 2)

/-- Manifestly nonnegative Bernstein remainder for the reciprocal
majorization.  The integer coefficients include the factors `choose 15 k`. -/
def directP6RetainedEvenAtanhReciprocalBernsteinRemainder (y : ℝ) : ℝ :=
  (1 / 10000000000 : ℝ) *
    (768 * (1 - y) ^ 15 +
      11236 * y * (1 - y) ^ 14 +
      76923 * y ^ 2 * (1 - y) ^ 13 +
      327153 * y ^ 3 * (1 - y) ^ 12 +
      966983 * y ^ 4 * (1 - y) ^ 11 +
      4826978801608 * y ^ 5 * (1 - y) ^ 10 +
      3474403 * y ^ 6 * (1 - y) ^ 9 +
      4429538 * y ^ 7 * (1 - y) ^ 8 +
      4385942 * y ^ 8 * (1 - y) ^ 7 +
      48347470492 * y ^ 9 * (1 - y) ^ 6 +
      1983898 * y ^ 10 * (1 - y) ^ 5 +
      107227805667 * y ^ 11 * (1 - y) ^ 4 +
      283436 * y ^ 12 * (1 - y) ^ 3 +
      62982 * y ^ 13 * (1 - y) ^ 2 +
      8925 * y ^ 14 * (1 - y) +
      695 * y ^ 15)

/-- Exact numerator identity behind the polynomial reciprocal majorant. -/
theorem directP6RetainedEvenAtanhReciprocalMajorant_factor (y : ℝ) :
    directP6RetainedEvenAtanhNumerator y *
          directP6RetainedEvenAtanhReciprocalMajorantPolynomial y -
        800 * (2 - y) ^ 3 =
      directP6RetainedEvenAtanhReciprocalBernsteinRemainder y := by
  unfold directP6RetainedEvenAtanhNumerator
    directP6RetainedEvenAtanhReciprocalMajorantPolynomial
    directP6RetainedEvenAtanhReciprocalBernsteinRemainder
  ring

theorem directP6RetainedEvenAtanhReciprocalBernsteinRemainder_nonneg
    {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ directP6RetainedEvenAtanhReciprocalBernsteinRemainder y := by
  have hone : 0 ≤ 1 - y := sub_nonneg.mpr hy1
  unfold directP6RetainedEvenAtanhReciprocalBernsteinRemainder
  positivity

/-- Pointwise reciprocal majorization on the whole physical interval. -/
theorem inv_directP6RetainedEvenAtanhTwoTermWeight_le_polynomialMajorant
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    (directP6RetainedEvenAtanhTwoTermWeight x)⁻¹ ≤
      directP6RetainedEvenAtanhReciprocalMajorant x := by
  have hxAbs : |x| ≤ 1 := abs_le.mpr hx
  have hy0 : 0 ≤ x ^ 2 := sq_nonneg x
  have hy1 : x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one x).2 hxAbs
  have hnum := directP6RetainedEvenAtanhNumerator_pos_on_Icc hx
  have hrem := directP6RetainedEvenAtanhReciprocalBernsteinRemainder_nonneg
    hy0 hy1
  have hfactor := directP6RetainedEvenAtanhReciprocalMajorant_factor (x ^ 2)
  rw [inv_directP6RetainedEvenAtanhTwoTermWeight_eq_rational hx]
  unfold directP6RetainedEvenAtanhReciprocalMajorant
  rw [div_le_iff₀ hnum]
  nlinarith

theorem intervalIntegrable_factorTwoIntrinsicNineDirectP6ExactResidualPolynomialMajorant
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) (i j : Fin 3) :
    IntervalIntegrable (fun x ↦
      directP6RetainedEvenAtanhReciprocalMajorant x *
        factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder sigma q i x *
        factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder sigma q j x)
      volume (-1) 1 := by
  have hcross :=
    intervalIntegrable_factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder_mul
      sigma q i j
  have hmult : Continuous directP6RetainedEvenAtanhReciprocalMajorant := by
    unfold directP6RetainedEvenAtanhReciprocalMajorant
      directP6RetainedEvenAtanhReciprocalMajorantPolynomial
    fun_prop
  simpa only [mul_assoc] using hcross.continuousOn_mul hmult.continuousOn

/-- Polynomial-multiplier upper Gram for the three shifted direct rows. -/
def factorTwoIntrinsicNineDirectP6ExactResidualPolynomialMajorantUpperGram
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) : Matrix (Fin 3) (Fin 3) ℝ :=
  finiteIntervalMultiplierGram (-1) 1
    directP6RetainedEvenAtanhReciprocalMajorant
    (factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder sigma q)

/-- The polynomial Gram dominates the sharper direct-atanh reciprocal Gram. -/
theorem factorTwoIntrinsicNineDirectP6ExactResidualPolynomialMajorantUpperGram_sub_directAtanh_posSemidef
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) :
    (factorTwoIntrinsicNineDirectP6ExactResidualPolynomialMajorantUpperGram
        sigma q -
      factorTwoIntrinsicNineDirectP6ExactResidualDirectAtanhUpperGram
        sigma q).PosSemidef := by
  exact finiteIntervalMultiplierGram_sub_posSemidef_of_le_Ioo
    (-1) 1 (by norm_num)
    (fun x ↦ (directP6RetainedEvenAtanhTwoTermWeight x)⁻¹)
    directP6RetainedEvenAtanhReciprocalMajorant
    (factorTwoIntrinsicNineDirectP6ExactResidualShiftedRemainder sigma q)
    (intervalIntegrable_factorTwoIntrinsicNineDirectP6ExactResidualDirectAtanh
      sigma q)
    (intervalIntegrable_factorTwoIntrinsicNineDirectP6ExactResidualPolynomialMajorant
      sigma q)
    (fun _x hx ↦
      inv_directP6RetainedEvenAtanhTwoTermWeight_le_polynomialMajorant
        ⟨hx.1.le, hx.2.le⟩)

/-- Complete polynomial upper selector Gram. -/
def factorTwoIntrinsicNineDirectP6ExactResidualPolynomialMajorantUpperSelectorGram
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) : Matrix (Fin 3) (Fin 3) ℝ :=
  factorTwoIntrinsicNineDirectP6ExactResidualNonquotientGram sigma q +
    factorTwoIntrinsicNineDirectP6ExactResidualPolynomialMajorantUpperGram sigma q

/-- Adding the common nonquotient part preserves the polynomial-to-direct
Loewner comparison. -/
theorem factorTwoIntrinsicNineDirectP6ExactResidualPolynomialMajorantUpperSelectorGram_sub_directAtanh_posSemidef
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) :
    (factorTwoIntrinsicNineDirectP6ExactResidualPolynomialMajorantUpperSelectorGram
        sigma q -
      factorTwoIntrinsicNineDirectP6ExactResidualDirectAtanhUpperSelectorGram
        sigma q).PosSemidef := by
  simpa only [
    factorTwoIntrinsicNineDirectP6ExactResidualPolynomialMajorantUpperSelectorGram,
    factorTwoIntrinsicNineDirectP6ExactResidualDirectAtanhUpperSelectorGram,
    add_sub_add_left_eq_sub] using
    factorTwoIntrinsicNineDirectP6ExactResidualPolynomialMajorantUpperGram_sub_directAtanh_posSemidef
      sigma q

/-- The complete polynomial selector Gram remains a full Loewner upper bound
for the exact selector Gram. -/
theorem factorTwoIntrinsicNineDirectP6ExactResidualPolynomialMajorantUpperSelectorGram_sub_exact_posSemidef
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) :
    (factorTwoIntrinsicNineDirectP6ExactResidualPolynomialMajorantUpperSelectorGram
        sigma q -
      factorTwoIntrinsicNineDirectP6ExactResidualSelectorGram sigma q).PosSemidef := by
  have hPoly :=
    factorTwoIntrinsicNineDirectP6ExactResidualPolynomialMajorantUpperSelectorGram_sub_directAtanh_posSemidef
      sigma q
  have hAtanh :=
    factorTwoIntrinsicNineDirectP6ExactResidualDirectAtanhUpperSelectorGram_sub_posSemidef
      sigma q
  have hsum := hPoly.add hAtanh
  have heq :
      factorTwoIntrinsicNineDirectP6ExactResidualPolynomialMajorantUpperSelectorGram
          sigma q -
        factorTwoIntrinsicNineDirectP6ExactResidualSelectorGram sigma q =
      (factorTwoIntrinsicNineDirectP6ExactResidualPolynomialMajorantUpperSelectorGram
          sigma q -
        factorTwoIntrinsicNineDirectP6ExactResidualDirectAtanhUpperSelectorGram
          sigma q) +
      (factorTwoIntrinsicNineDirectP6ExactResidualDirectAtanhUpperSelectorGram
          sigma q -
        factorTwoIntrinsicNineDirectP6ExactResidualSelectorGram sigma q) := by
    module
  rw [heq]
  exact hsum

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorDirectAtanhPolynomialLoewnerStructural
