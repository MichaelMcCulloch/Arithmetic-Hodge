import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveOddMinorStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotSecondSharpStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourC2Structural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4P3AlternatingSharpStructural

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveC2Structural

noncomputable section

open Polynomial
open CenteredOddOneThreeEnergy
open ThreeByThreePositiveMixedDeterminant
open YoshidaEndpointOddFullPolarization
open YoshidaEndpointOcticPotential
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseDiskSchur
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicLowControlStep23EvenSlopeStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4PlusEndpointExactSchur
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelSharp
open YoshidaFactorTwoPhaseIntrinsicLowStaticMinusRationalSchur
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicOddCleanSharp
open YoshidaFactorTwoPhaseIntrinsicOddPerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicSixP4P1AlternatingStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateCoefficientsStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveCoefficientsStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveOddMinorStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourC2Structural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotSecondSharpStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotQuantitativeStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4P3AlternatingSharpStructural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLowSchur

/-!
# The second mixed raw five-mode coefficient

The exact coefficient is split into two correlated Schur gates.  The first
is the determinant of the hybrid endpoint block with the plus even form,
the minus odd form, and the fixed alternating columns.  The second is the
remaining mixed exterior-square reserve.  This keeps the cancellations
inside the two adjugate contractions instead of estimating the convolution
terms independently.
-/

private def e00p : ℝ := factorTwoStructuralPhaseLow00 1
private def e02p : ℝ := factorTwoStructuralPhaseLow02 1
private def e22p : ℝ := factorTwoStructuralPhaseLow22 1
private def e04p : ℝ := factorTwoIntrinsicFourP45Cross04 1
private def e24p : ℝ := factorTwoIntrinsicFourP45Cross24 1
private def e44p : ℝ := factorTwoIntrinsicSixP4Diagonal 1

private def e00m : ℝ := factorTwoStructuralPhaseLow00 (-1)
private def e02m : ℝ := factorTwoStructuralPhaseLow02 (-1)
private def e22m : ℝ := factorTwoStructuralPhaseLow22 (-1)
private def e04m : ℝ := factorTwoIntrinsicFourP45Cross04 (-1)
private def e24m : ℝ := factorTwoIntrinsicFourP45Cross24 (-1)
private def e44m : ℝ := factorTwoIntrinsicSixP4Diagonal (-1)

private def o11p : ℝ := factorTwoIntrinsicOddPhaseLow11 1
private def o13p : ℝ := factorTwoIntrinsicOddPhaseLow13 1
private def o33p : ℝ := factorTwoIntrinsicOddPhaseLow33 1
private def o11m : ℝ := factorTwoIntrinsicOddPhaseLow11 (-1)
private def o13m : ℝ := factorTwoIntrinsicOddPhaseLow13 (-1)
private def o33m : ℝ := factorTwoIntrinsicOddPhaseLow33 (-1)

private def u0 : ℝ := factorTwoIntrinsicAlternating01
private def u2 : ℝ := factorTwoIntrinsicAlternating21
private def u4 : ℝ := factorTwoIntrinsicFourP45Cross41
private def v0 : ℝ := factorTwoIntrinsicAlternating03
private def v2 : ℝ := factorTwoIntrinsicAlternating23
private def v4 : ℝ := factorTwoIntrinsicFourP45Cross43

/-- The polarized adjugate of the plus even endpoint. -/
private def plusAdjugatePair
    (x0 x2 x4 y0 y2 y4 : ℝ) : ℝ :=
  (e22p * e44p - e24p ^ 2) * x0 * y0 +
    (e04p * e24p - e02p * e44p) * (x0 * y2 + x2 * y0) +
    (e02p * e24p - e04p * e22p) * (x0 * y4 + x4 * y0) +
    (e00p * e44p - e04p ^ 2) * x2 * y2 +
    (e02p * e04p - e00p * e24p) * (x2 * y4 + x4 * y2) +
    (e00p * e22p - e02p ^ 2) * x4 * y4

/-- The coefficient linear in the minus endpoint of the polarized even
adjugate pencil. -/
private def mixedAdjugatePair
    (x0 x2 x4 y0 y2 y4 : ℝ) : ℝ :=
  (e22p * e44m + e22m * e44p - 2 * e24p * e24m) * x0 * y0 +
    (e04p * e24m + e04m * e24p - e02p * e44m - e02m * e44p) *
      (x0 * y2 + x2 * y0) +
    (e02p * e24m + e02m * e24p - e04p * e22m - e04m * e22p) *
      (x0 * y4 + x4 * y0) +
    (e00p * e44m + e00m * e44p - 2 * e04p * e04m) * x2 * y2 +
    (e02p * e04m + e02m * e04p - e00p * e24m - e00m * e24p) *
      (x2 * y4 + x4 * y2) +
    (e00p * e22m + e00m * e22p - 2 * e02p * e02m) * x4 * y4

private def minusAdjugatePair
    (x0 x2 x4 y0 y2 y4 : ℝ) : ℝ :=
  (e22m * e44m - e24m ^ 2) * x0 * y0 +
    (e04m * e24m - e02m * e44m) * (x0 * y2 + x2 * y0) +
    (e02m * e24m - e04m * e22m) * (x0 * y4 + x4 * y0) +
    (e00m * e44m - e04m ^ 2) * x2 * y2 +
    (e02m * e04m - e00m * e24m) * (x2 * y4 + x4 * y2) +
    (e00m * e22m - e02m ^ 2) * x4 * y4

private theorem rawAdjugatePairPolynomial_expansion
    (x0 x2 x4 y0 y2 y4 : ℝ) :
    coefficientRawAdjugatePairPolynomial x0 x2 x4 y0 y2 y4 =
      C (plusAdjugatePair x0 x2 x4 y0 y2 y4) +
        C (mixedAdjugatePair x0 x2 x4 y0 y2 y4) * X +
        C (minusAdjugatePair x0 x2 x4 y0 y2 y4) * X ^ 2 := by
  unfold coefficientRawAdjugatePairPolynomial
    coefficientLowDetPolynomial coefficientLow00Polynomial
    coefficientLow02Polynomial coefficientLow22Polynomial
    coefficientCross04Polynomial coefficientCross24Polynomial
    coefficientP4DiagonalPolynomial endpointAffinePolynomial
    plusAdjugatePair mixedAdjugatePair minusAdjugatePair
    e00p e02p e22p e04p e24p e44p
    e00m e02m e22m e04m e24m e44m
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  ring

private theorem coeff_one_affine_mul_quadratic
    (a b p q r : ℝ) :
    ((C a + C b * X) * (C p + C q * X + C r * X ^ 2)).coeff 1 =
      a * q + b * p := by
  rw [show
      (C a + C b * X) * (C p + C q * X + C r * X ^ 2) =
        C (a * p) + C (a * q + b * p) * X +
          C (a * r + b * q) * X ^ 2 + C (b * r) * X ^ 3 by
    simp only [map_add, map_mul]
    ring]
  norm_num
  simp only [← map_mul, ← map_add, coeff_C_mul_X_pow]
  norm_num

private theorem coeff_one_two_mul_affine_mul_quadratic
    (a b p q r : ℝ) :
    (2 * (C a + C b * X) *
        (C p + C q * X + C r * X ^ 2)).coeff 1 =
      2 * (a * q + b * p) := by
  rw [show
      2 * (C a + C b * X) * (C p + C q * X + C r * X ^ 2) =
        C (2 * a * p) + C (2 * (a * q + b * p)) * X +
          C (2 * (a * r + b * q)) * X ^ 2 + C (2 * b * r) * X ^ 3 by
    simp only [map_add, map_mul, map_ofNat]
    ring]
  norm_num
  simp only [← map_mul, ← map_add, coeff_C_mul_X_pow]
  norm_num

private def plusCrossEnergy : ℝ :=
  let z0 := u2 * v4 - u4 * v2
  let z2 := u4 * v0 - u0 * v4
  let z4 := u0 * v2 - u2 * v0
  e00p * z0 ^ 2 + 2 * e02p * z0 * z2 + 2 * e04p * z0 * z4 +
    e22p * z2 ^ 2 + 2 * e24p * z2 * z4 + e44p * z4 ^ 2

private theorem rawFiveCouplingCoeff_one_eq :
    rawFiveCouplingCoeff 1 =
      o33p * mixedAdjugatePair u0 u2 u4 u0 u2 u4 +
        o33m * plusAdjugatePair u0 u2 u4 u0 u2 u4 -
        2 * (o13p * mixedAdjugatePair u0 u2 u4 v0 v2 v4 +
          o13m * plusAdjugatePair u0 u2 u4 v0 v2 v4) +
        o11p * mixedAdjugatePair v0 v2 v4 v0 v2 v4 +
        o11m * plusAdjugatePair v0 v2 v4 v0 v2 v4 := by
  change
    factorTwoIntrinsicSixProjectiveRawMinorFiveCouplingCoefficientPolynomial.coeff 1 = _
  unfold factorTwoIntrinsicSixProjectiveRawMinorFiveCouplingCoefficientPolynomial
  rw [rawAdjugatePairPolynomial_expansion,
    rawAdjugatePairPolynomial_expansion,
    rawAdjugatePairPolynomial_expansion]
  unfold coefficientOdd11Polynomial coefficientOdd13Polynomial
    coefficientOdd33Polynomial endpointAffinePolynomial
    o11p o13p o33p o11m o13m o33m
  simp only [coeff_add, coeff_sub, coeff_one_affine_mul_quadratic,
    coeff_one_two_mul_affine_mul_quadratic]
  unfold u0 u2 u4 v0 v2 v4
  ring

private theorem rawFiveCrossEnergyCoeff_zero_eq :
    rawFiveCrossEnergyCoeff 0 = plusCrossEnergy := by
  change
    factorTwoIntrinsicSixProjectiveRawMinorFiveCrossEnergyCoefficientPolynomial.coeff 0 = _
  rw [Polynomial.coeff_zero_eq_eval_zero]
  unfold factorTwoIntrinsicSixProjectiveRawMinorFiveCrossEnergyCoefficientPolynomial
    factorTwoIntrinsicSixProjectiveRawMinorFiveCross0Polynomial
    factorTwoIntrinsicSixProjectiveRawMinorFiveCross2Polynomial
    factorTwoIntrinsicSixProjectiveRawMinorFiveCross4Polynomial
    coefficientLow00Polynomial coefficientLow02Polynomial
    coefficientLow22Polynomial coefficientCross04Polynomial
    coefficientCross24Polynomial coefficientP4DiagonalPolynomial
    endpointAffinePolynomial plusCrossEnergy
    e00p e02p e22p e04p e24p e44p u0 u2 u4 v0 v2 v4
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_X]
  ring

/-- The endpoint-hybrid determinant gate. -/
private def endpointHybridGate : ℝ :=
  pivotCoeff 0 * rawFiveOddMinorCoeff 2 -
    (o33m * plusAdjugatePair u0 u2 u4 u0 u2 u4 -
      2 * o13m * plusAdjugatePair u0 u2 u4 v0 v2 v4 +
      o11m * plusAdjugatePair v0 v2 v4 v0 v2 v4) +
    plusCrossEnergy

/-- The genuinely mixed exterior-square gate. -/
private def mixedExteriorGate : ℝ :=
  pivotCoeff 1 * rawFiveOddMinorCoeff 1 +
    pivotCoeff 2 * rawFiveOddMinorCoeff 0 -
    (o33p * mixedAdjugatePair u0 u2 u4 u0 u2 u4 -
      2 * o13p * mixedAdjugatePair u0 u2 u4 v0 v2 v4 +
      o11p * mixedAdjugatePair v0 v2 v4 v0 v2 v4)

/-- Exact cancellation-preserving decomposition of the second coefficient. -/
private theorem coefficient_two_eq_gates :
    factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient 2 =
      endpointHybridGate + mixedExteriorGate := by
  simp only [factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient]
  rw [rawFiveCouplingCoeff_one_eq, rawFiveCrossEnergyCoeff_zero_eq]
  unfold endpointHybridGate mixedExteriorGate
  ring

/-! ## Raw-four reserve plus the correlated `P3` residual -/

private def p3CorrelatedResidual : ℝ :=
  -(pivotCoeff 0 * o13m ^ 2 +
      2 * pivotCoeff 1 * o13p * o13m + pivotCoeff 2 * o13p ^ 2) +
    2 * (o13m * plusAdjugatePair u0 u2 u4 v0 v2 v4 +
      o13p * mixedAdjugatePair u0 u2 u4 v0 v2 v4) -
    (o11m * plusAdjugatePair v0 v2 v4 v0 v2 v4 +
      o11p * mixedAdjugatePair v0 v2 v4 v0 v2 v4) +
    plusCrossEnergy

private theorem p1AlternatingAdjugatePolynomial_eq_raw :
    coefficientP1AlternatingAdjugatePolynomial =
      coefficientRawAdjugatePairPolynomial u0 u2 u4 u0 u2 u4 := by
  unfold coefficientP1AlternatingAdjugatePolynomial
    coefficientRawAdjugatePairPolynomial u0 u2 u4
  ring

private theorem rawFourCoefficient_one_eq_here :
    factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient 1 =
      pivotCoeff 0 * o11m + pivotCoeff 1 * o11p -
        plusAdjugatePair u0 u2 u4 u0 u2 u4 := by
  simp only [factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient]
  unfold p1AlternatingAdjugateCoeff coefficientOdd11Polynomial
    endpointAffinePolynomial o11p o11m
  rw [p1AlternatingAdjugatePolynomial_eq_raw]
  change
    pivotCoeff 0 * (C o11p + C o11m * X).coeff 1 +
        pivotCoeff 1 * (C o11p + C o11m * X).coeff 0 -
          (coefficientRawAdjugatePairPolynomial u0 u2 u4 u0 u2 u4).coeff 0 = _
  rw [rawAdjugatePairPolynomial_expansion]
  simp [o11p, o11m]

private theorem rawFourCoefficient_two_eq_here :
    factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient 2 =
      pivotCoeff 1 * o11m + pivotCoeff 2 * o11p -
        mixedAdjugatePair u0 u2 u4 u0 u2 u4 := by
  simp only [factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient]
  unfold p1AlternatingAdjugateCoeff coefficientOdd11Polynomial
    endpointAffinePolynomial o11p o11m
  rw [p1AlternatingAdjugatePolynomial_eq_raw]
  change
    pivotCoeff 1 * (C o11p + C o11m * X).coeff 1 +
        pivotCoeff 2 * (C o11p + C o11m * X).coeff 0 -
          (coefficientRawAdjugatePairPolynomial u0 u2 u4 u0 u2 u4).coeff 1 = _
  rw [rawAdjugatePairPolynomial_expansion]
  simp [o11p, o11m]

/-! ## Correlated midpoint coordinates

The endpoint boxes are not used independently: doing so discards exactly the
clean--perturbation cancellation which makes this coefficient positive.  The
following polynomial keeps the clean midpoint and its negative perturbation
as the primitive variables. -/

private def alignedEntry00 (A X C : ℝ) : ℝ := (A + C + 2 * X) / 4
private def alignedEntry02 (A C : ℝ) : ℝ := (A - C) / 4
private def alignedEntry22 (A X C : ℝ) : ℝ := (A + C - 2 * X) / 4
private def alignedEntry04 (R D : ℝ) : ℝ := (R - D) / 2
private def alignedEntry24 (R D : ℝ) : ℝ := (R + D) / 2

private def alignedDeterminant (A X R C D F : ℝ) : ℝ :=
  (F * (A * C - X ^ 2) - A * D ^ 2 - C * R ^ 2 - 2 * X * R * D) / 4

private def alignedMixedDeterminant
    (A X R C D F a x r c d f : ℝ) : ℝ :=
  mixedDeterminantOne
    (alignedEntry00 A X C) (alignedEntry02 A C) (alignedEntry04 R D)
    (alignedEntry22 A X C) (alignedEntry24 R D) F
    (alignedEntry00 a x c) (alignedEntry02 a c) (alignedEntry04 r d)
    (alignedEntry22 a x c) (alignedEntry24 r d) f

private def alignedAdjugatePair
    (A X R C D F sx dx zx sy dy zy : ℝ) : ℝ :=
  ((F * C - D ^ 2) * sx * sy +
      (F * A - R ^ 2) * dx * dy -
      (F * X + R * D) * (sx * dy + dx * sy) -
      (C * R + X * D) * (sx * zy + zx * sy) +
      (X * R + A * D) * (dx * zy + zx * dy) +
      (A * C - X ^ 2) * zx * zy) / 4

private def alignedMixedAdjugatePair
    (A X R C D F a x r c d f sx dx zx sy dy zy : ℝ) : ℝ :=
  ((F * c + f * C - 2 * D * d) * sx * sy +
      (F * a + f * A - 2 * R * r) * dx * dy -
      (F * x + f * X + R * d + r * D) * (sx * dy + dx * sy) -
      (C * r + c * R + X * d + x * D) * (sx * zy + zx * sy) +
      (X * r + x * R + A * d + a * D) * (dx * zy + zx * dy) +
      (A * c + a * C - 2 * X * x) * zx * zy) / 4

private def alignedCrossEnergy
    (A X R C D F su du u4 sv dv v4 : ℝ) : ℝ :=
  let zs := u4 * dv - v4 * du
  let zd := v4 * su - u4 * sv
  let z4 := (du * sv - su * dv) / 2
  (A * zs ^ 2 + 2 * X * zs * zd + C * zd ^ 2 +
      4 * R * zs * z4 - 4 * D * zd * z4 + 4 * F * z4 ^ 2) / 4

private def correlatedCoefficientTwo
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ) : ℝ :=
  let Ap := A - a
  let Xp := X - x
  let Rp := R - r
  let Cp := C - c
  let Dp := D - d
  let Fp := F - f
  let Am := A + a
  let Xm := X + x
  let Rm := R + r
  let Cm := C + c
  let Dm := D + d
  let Fm := F + f
  let o11p := q11 + h11
  let o13p := q13 + h13
  let o33p := q33 + h33
  let o11m := q11 - h11
  let o13m := q13 - h13
  let o33m := q33 - h33
  let oddPlus := o11p * o33p - o13p ^ 2
  let oddMixed := o11p * o33m + o11m * o33p - 2 * o13p * o13m
  let oddMinus := o11m * o33m - o13m ^ 2
  let plusCoupling :=
    o33m * alignedAdjugatePair Ap Xp Rp Cp Dp Fp su du u4 su du u4 -
      2 * o13m * alignedAdjugatePair Ap Xp Rp Cp Dp Fp su du u4 sv dv v4 +
      o11m * alignedAdjugatePair Ap Xp Rp Cp Dp Fp sv dv v4 sv dv v4
  let mixedCoupling :=
    o33p * alignedMixedAdjugatePair Ap Xp Rp Cp Dp Fp
        Am Xm Rm Cm Dm Fm su du u4 su du u4 -
      2 * o13p * alignedMixedAdjugatePair Ap Xp Rp Cp Dp Fp
        Am Xm Rm Cm Dm Fm su du u4 sv dv v4 +
      o11p * alignedMixedAdjugatePair Ap Xp Rp Cp Dp Fp
        Am Xm Rm Cm Dm Fm sv dv v4 sv dv v4
  alignedDeterminant Ap Xp Rp Cp Dp Fp * oddMinus +
    alignedMixedDeterminant Ap Xp Rp Cp Dp Fp Am Xm Rm Cm Dm Fm * oddMixed +
    alignedMixedDeterminant Am Xm Rm Cm Dm Fm Ap Xp Rp Cp Dp Fp * oddPlus -
    plusCoupling - mixedCoupling +
    alignedCrossEnergy Ap Xp Rp Cp Dp Fp su du u4 sv dv v4

private theorem alignedDeterminant_eq
    (q00 q02 q04 q22 q24 q44 : ℝ) :
    alignedDeterminant
        (q00 + 2 * q02 + q22) (q00 - q22) (q04 + q24)
        (q00 - 2 * q02 + q22) (q24 - q04) q44 =
      ThreeByThreeRankOneSchur.symmetricDeterminant
        q00 q02 q04 q22 q24 q44 := by
  unfold alignedDeterminant ThreeByThreeRankOneSchur.symmetricDeterminant
  ring

private theorem alignedMixedDeterminant_eq
    (p00 p02 p04 p22 p24 p44 m00 m02 m04 m22 m24 m44 : ℝ) :
    alignedMixedDeterminant
        (p00 + 2 * p02 + p22) (p00 - p22) (p04 + p24)
        (p00 - 2 * p02 + p22) (p24 - p04) p44
        (m00 + 2 * m02 + m22) (m00 - m22) (m04 + m24)
        (m00 - 2 * m02 + m22) (m24 - m04) m44 =
      mixedDeterminantOne
        p00 p02 p04 p22 p24 p44 m00 m02 m04 m22 m24 m44 := by
  unfold alignedMixedDeterminant alignedEntry00 alignedEntry02 alignedEntry04
    alignedEntry22 alignedEntry24
  ring

private theorem alignedAdjugatePair_eq
    (q00 q02 q04 q22 q24 q44 x0 x2 x4 y0 y2 y4 : ℝ) :
    alignedAdjugatePair
        (q00 + 2 * q02 + q22) (q00 - q22) (q04 + q24)
        (q00 - 2 * q02 + q22) (q24 - q04) q44
        (x0 + x2) (x0 - x2) x4 (y0 + y2) (y0 - y2) y4 =
      (q22 * q44 - q24 ^ 2) * x0 * y0 +
        (q04 * q24 - q02 * q44) * (x0 * y2 + x2 * y0) +
        (q02 * q24 - q04 * q22) * (x0 * y4 + x4 * y0) +
        (q00 * q44 - q04 ^ 2) * x2 * y2 +
        (q02 * q04 - q00 * q24) * (x2 * y4 + x4 * y2) +
        (q00 * q22 - q02 ^ 2) * x4 * y4 := by
  unfold alignedAdjugatePair
  ring

private theorem alignedMixedAdjugatePair_eq
    (p00 p02 p04 p22 p24 p44 m00 m02 m04 m22 m24 m44
      x0 x2 x4 y0 y2 y4 : ℝ) :
    alignedMixedAdjugatePair
        (p00 + 2 * p02 + p22) (p00 - p22) (p04 + p24)
        (p00 - 2 * p02 + p22) (p24 - p04) p44
        (m00 + 2 * m02 + m22) (m00 - m22) (m04 + m24)
        (m00 - 2 * m02 + m22) (m24 - m04) m44
        (x0 + x2) (x0 - x2) x4 (y0 + y2) (y0 - y2) y4 =
      (p22 * m44 + m22 * p44 - 2 * p24 * m24) * x0 * y0 +
        (p04 * m24 + m04 * p24 - p02 * m44 - m02 * p44) *
          (x0 * y2 + x2 * y0) +
        (p02 * m24 + m02 * p24 - p04 * m22 - m04 * p22) *
          (x0 * y4 + x4 * y0) +
        (p00 * m44 + m00 * p44 - 2 * p04 * m04) * x2 * y2 +
        (p02 * m04 + m02 * p04 - p00 * m24 - m00 * p24) *
          (x2 * y4 + x4 * y2) +
        (p00 * m22 + m00 * p22 - 2 * p02 * m02) * x4 * y4 := by
  unfold alignedMixedAdjugatePair
  ring

private theorem alignedCrossEnergy_eq
    (q00 q02 q04 q22 q24 q44 u0 u2 u4 v0 v2 v4 : ℝ) :
    alignedCrossEnergy
        (q00 + 2 * q02 + q22) (q00 - q22) (q04 + q24)
        (q00 - 2 * q02 + q22) (q24 - q04) q44
        (u0 + u2) (u0 - u2) u4 (v0 + v2) (v0 - v2) v4 =
      let z0 := u2 * v4 - u4 * v2
      let z2 := u4 * v0 - u0 * v4
      let z4 := u0 * v2 - u2 * v0
      q00 * z0 ^ 2 + 2 * q02 * z0 * z2 + 2 * q04 * z0 * z4 +
        q22 * z2 ^ 2 + 2 * q24 * z2 * z4 + q44 * z4 ^ 2 := by
  unfold alignedCrossEnergy
  dsimp only
  ring

private theorem endpoint_aligned_coordinates :
    cleanStrong - perturbStrong = e00p + 2 * e02p + e22p ∧
      cleanSkew - perturbSkew = e00p - e22p ∧
      cleanCrossSum - perturbCrossSum = e04p + e24p ∧
      cleanWeak - perturbWeak = e00p - 2 * e02p + e22p ∧
      cleanCrossDifference - perturbCrossDifference = e24p - e04p ∧
      cleanP4 - perturbP4 = e44p ∧
      cleanStrong + perturbStrong = e00m + 2 * e02m + e22m ∧
      cleanSkew + perturbSkew = e00m - e22m ∧
      cleanCrossSum + perturbCrossSum = e04m + e24m ∧
      cleanWeak + perturbWeak = e00m - 2 * e02m + e22m ∧
      cleanCrossDifference + perturbCrossDifference = e24m - e04m ∧
      cleanP4 + perturbP4 = e44m := by
  unfold cleanStrong cleanSkew cleanCrossSum cleanWeak cleanCrossDifference
    cleanP4 perturbStrong perturbSkew perturbCrossSum perturbWeak
    perturbCrossDifference perturbP4
    e00p e02p e22p e04p e24p e44p e00m e02m e22m e04m e24m e44m
    factorTwoStructuralPhaseLow00 factorTwoStructuralPhaseLow02
    factorTwoStructuralPhaseLow22 evenNegativePerturbation00
    evenNegativePerturbation02 evenNegativePerturbation22
    factorTwoIntrinsicP4PlusCrossSum factorTwoIntrinsicP4PlusCrossDifference
    factorTwoIntrinsicFourP45Cross04 factorTwoIntrinsicFourP45Cross24
    factorTwoIntrinsicSixP4Diagonal factorTwoEndpointPhaseDiagonal
  unfold cleanCrossSum cleanCrossDifference
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

private theorem pivotCoeff_zero_eq_even_plus :
    pivotCoeff 0 =
      ThreeByThreeRankOneSchur.symmetricDeterminant
        e00p e02p e04p e22p e24p e44p := by
  change factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial.coeff 0 = _
  rw [Polynomial.coeff_zero_eq_eval_zero]
  unfold factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial
    coefficientAdjugateTwoPolynomial coefficientLowDetPolynomial
    coefficientLow00Polynomial coefficientLow02Polynomial
    coefficientLow22Polynomial coefficientCross04Polynomial
    coefficientCross24Polynomial coefficientP4DiagonalPolynomial
    endpointAffinePolynomial e00p e02p e04p e22p e24p e44p
    ThreeByThreeRankOneSchur.symmetricDeterminant
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X]
  ring

private theorem pivot_coefficients_eq_correlated :
    pivotCoeff 0 = alignedDeterminant
        (cleanStrong - perturbStrong) (cleanSkew - perturbSkew)
        (cleanCrossSum - perturbCrossSum) (cleanWeak - perturbWeak)
        (cleanCrossDifference - perturbCrossDifference) (cleanP4 - perturbP4) ∧
      pivotCoeff 1 = alignedMixedDeterminant
        (cleanStrong - perturbStrong) (cleanSkew - perturbSkew)
        (cleanCrossSum - perturbCrossSum) (cleanWeak - perturbWeak)
        (cleanCrossDifference - perturbCrossDifference) (cleanP4 - perturbP4)
        (cleanStrong + perturbStrong) (cleanSkew + perturbSkew)
        (cleanCrossSum + perturbCrossSum) (cleanWeak + perturbWeak)
        (cleanCrossDifference + perturbCrossDifference) (cleanP4 + perturbP4) ∧
      pivotCoeff 2 = alignedMixedDeterminant
        (cleanStrong + perturbStrong) (cleanSkew + perturbSkew)
        (cleanCrossSum + perturbCrossSum) (cleanWeak + perturbWeak)
        (cleanCrossDifference + perturbCrossDifference) (cleanP4 + perturbP4)
        (cleanStrong - perturbStrong) (cleanSkew - perturbSkew)
        (cleanCrossSum - perturbCrossSum) (cleanWeak - perturbWeak)
        (cleanCrossDifference - perturbCrossDifference) (cleanP4 - perturbP4) := by
  rcases endpoint_aligned_coordinates with
    ⟨hAp, hXp, hRp, hCp, hDp, hFp, hAm, hXm, hRm, hCm, hDm, hFm⟩
  constructor
  · rw [hAp, hXp, hRp, hCp, hDp, hFp, alignedDeterminant_eq]
    exact pivotCoeff_zero_eq_even_plus
  constructor
  · rw [hAp, hXp, hRp, hCp, hDp, hFp, hAm, hXm, hRm, hCm, hDm, hFm,
      alignedMixedDeterminant_eq]
    simpa only [e00p, e02p, e04p, e22p, e24p, e44p,
      e00m, e02m, e04m, e22m, e24m, e44m] using
      pivotCoeff_one_eq_exact_mixed
  · rw [hAm, hXm, hRm, hCm, hDm, hFm, hAp, hXp, hRp, hCp, hDp, hFp,
      alignedMixedDeterminant_eq]
    simpa only [e00p, e02p, e04p, e22p, e24p, e44p,
      e00m, e02m, e04m, e22m, e24m, e44m] using
      pivotCoeff_two_eq_exact_mixed

private theorem adjugate_pairs_eq_correlated
    (x0 x2 x4 y0 y2 y4 : ℝ) :
    plusAdjugatePair x0 x2 x4 y0 y2 y4 =
        alignedAdjugatePair
          (cleanStrong - perturbStrong) (cleanSkew - perturbSkew)
          (cleanCrossSum - perturbCrossSum) (cleanWeak - perturbWeak)
          (cleanCrossDifference - perturbCrossDifference) (cleanP4 - perturbP4)
          (x0 + x2) (x0 - x2) x4 (y0 + y2) (y0 - y2) y4 ∧
      mixedAdjugatePair x0 x2 x4 y0 y2 y4 =
        alignedMixedAdjugatePair
          (cleanStrong - perturbStrong) (cleanSkew - perturbSkew)
          (cleanCrossSum - perturbCrossSum) (cleanWeak - perturbWeak)
          (cleanCrossDifference - perturbCrossDifference) (cleanP4 - perturbP4)
          (cleanStrong + perturbStrong) (cleanSkew + perturbSkew)
          (cleanCrossSum + perturbCrossSum) (cleanWeak + perturbWeak)
          (cleanCrossDifference + perturbCrossDifference) (cleanP4 + perturbP4)
          (x0 + x2) (x0 - x2) x4 (y0 + y2) (y0 - y2) y4 := by
  rcases endpoint_aligned_coordinates with
    ⟨hAp, hXp, hRp, hCp, hDp, hFp, hAm, hXm, hRm, hCm, hDm, hFm⟩
  constructor
  · rw [hAp, hXp, hRp, hCp, hDp, hFp, alignedAdjugatePair_eq]
    rfl
  · rw [hAp, hXp, hRp, hCp, hDp, hFp, hAm, hXm, hRm, hCm, hDm, hFm,
      alignedMixedAdjugatePair_eq]
    rfl

private theorem plusCrossEnergy_eq_correlated :
    plusCrossEnergy = alignedCrossEnergy
      (cleanStrong - perturbStrong) (cleanSkew - perturbSkew)
      (cleanCrossSum - perturbCrossSum) (cleanWeak - perturbWeak)
      (cleanCrossDifference - perturbCrossDifference) (cleanP4 - perturbP4)
      (u0 + u2) (u0 - u2) u4 (v0 + v2) (v0 - v2) v4 := by
  rcases endpoint_aligned_coordinates with
    ⟨hAp, hXp, hRp, hCp, hDp, hFp, _⟩
  rw [hAp, hXp, hRp, hCp, hDp, hFp, alignedCrossEnergy_eq]
  rfl

private theorem rawFiveOddMinorCoeff_zero_eq_here :
    rawFiveOddMinorCoeff 0 = o11p * o33p - o13p ^ 2 := by
  change factorTwoIntrinsicSixProjectiveOddMinorTwoCoefficientPolynomial.coeff 0 = _
  rw [Polynomial.coeff_zero_eq_eval_zero]
  unfold factorTwoIntrinsicSixProjectiveOddMinorTwoCoefficientPolynomial
    coefficientOdd11Polynomial coefficientOdd13Polynomial coefficientOdd33Polynomial
    endpointAffinePolynomial o11p o13p o33p
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X]
  ring

private theorem rawFiveOddMinorCoeff_two_eq_here :
    rawFiveOddMinorCoeff 2 = o11m * o33m - o13m ^ 2 := by
  change factorTwoIntrinsicSixProjectiveOddMinorTwoCoefficientPolynomial.coeff 2 = _
  have hpoly :
      factorTwoIntrinsicSixProjectiveOddMinorTwoCoefficientPolynomial =
        C (o11p * o33p - o13p ^ 2) +
          C (o11p * o33m + o11m * o33p - 2 * o13p * o13m) * X +
          C (o11m * o33m - o13m ^ 2) * X ^ 2 := by
    unfold factorTwoIntrinsicSixProjectiveOddMinorTwoCoefficientPolynomial
      coefficientOdd11Polynomial coefficientOdd13Polynomial coefficientOdd33Polynomial
      endpointAffinePolynomial o11p o13p o33p o11m o13m o33m
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    ring
  rw [hpoly]
  simp only [coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow]
  norm_num

/-- Exact reserve decomposition.  The two raw-four terms and the `P3`
remainder must remain correlated; independent interval bounds lose the
decisive cancellation. -/
private theorem coefficient_two_eq_rawFour_reserve :
    factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient 2 =
      o33m * factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient 1 +
        o33p * factorTwoIntrinsicSixProjectiveRawMinorFourCoefficient 2 +
          p3CorrelatedResidual := by
  rw [coefficient_two_eq_gates, rawFourCoefficient_one_eq_here,
    rawFourCoefficient_two_eq_here]
  unfold endpointHybridGate mixedExteriorGate p3CorrelatedResidual
  rw [rawFiveOddMinorCoeff_zero_eq_here,
    rawFiveOddMinorCoeff_one_eq, rawFiveOddMinorCoeff_two_eq_here]
  unfold o11p o11m o13p o13m o33p o33m
  ring

set_option maxHeartbeats 800000 in
private theorem coefficient_two_eq_correlated :
    factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient 2 =
      correlatedCoefficientTwo
        cleanStrong cleanSkew cleanCrossSum cleanWeak cleanCrossDifference cleanP4
        perturbStrong perturbSkew perturbCrossSum perturbWeak
        perturbCrossDifference perturbP4
        (u0 + u2) (u0 - u2) u4 (v0 + v2) (v0 - v2) v4
        yoshidaEndpointOddLowGram11 yoshidaEndpointOddLowGram13
        yoshidaEndpointOddLowGram33
        (factorTwoCenteredSymmetricPerturbation centeredP1)
        (factorTwoCenteredSymmetricPerturbationBilinear centeredP1 centeredP3)
        (factorTwoCenteredSymmetricPerturbation centeredP3) := by
  rw [coefficient_two_eq_gates]
  unfold endpointHybridGate mixedExteriorGate correlatedCoefficientTwo
  dsimp only
  rw [pivot_coefficients_eq_correlated.1,
    pivot_coefficients_eq_correlated.2.1,
    pivot_coefficients_eq_correlated.2.2,
    rawFiveOddMinorCoeff_zero_eq_here,
    rawFiveOddMinorCoeff_one_eq,
    rawFiveOddMinorCoeff_two_eq_here,
    (adjugate_pairs_eq_correlated u0 u2 u4 u0 u2 u4).1,
    (adjugate_pairs_eq_correlated u0 u2 u4 u0 u2 u4).2,
    (adjugate_pairs_eq_correlated u0 u2 u4 v0 v2 v4).1,
    (adjugate_pairs_eq_correlated u0 u2 u4 v0 v2 v4).2,
    (adjugate_pairs_eq_correlated v0 v2 v4 v0 v2 v4).1,
    (adjugate_pairs_eq_correlated v0 v2 v4 v0 v2 v4).2,
    plusCrossEnergy_eq_correlated]
  unfold o11p o13p o33p o11m o13m o33m
    factorTwoIntrinsicOddPhaseLow11 factorTwoIntrinsicOddPhaseLow13
    factorTwoIntrinsicOddPhaseLow33
  ring

private def quadraticSecant (g : ℝ → ℝ) (s t : ℝ) : ℝ :=
  ((g 1 + g (-1) - 2 * g 0) / 2) * (s + t) + (g 1 - g (-1)) / 2

/-- A coordinate law is quadratic when its three values at `-1`, `0`, and
`1` recover it by interpolation.  This is the structural hypothesis used by
the coordinate telescope; it does not inspect any finite grid. -/
private def IsQuadraticLaw (g : ℝ → ℝ) : Prop :=
  ∀ z,
    g z = ((g 1 + g (-1) - 2 * g 0) / 2) * z ^ 2 +
      ((g 1 - g (-1)) / 2) * z + g 0

/-- Exact one-coordinate step for a quadratic law. -/
private theorem quadraticSecant_exact
    (g : ℝ → ℝ) (hg : IsQuadraticLaw g) (s t : ℝ) :
    g s - g t = (s - t) * quadraticSecant g s t := by
  rw [hg s, hg t]
  unfold quadraticSecant
  ring

private theorem quadratic_lower_at_left
    (g : ℝ → ℝ) (hg : IsQuadraticLaw g) (s left : ℝ)
    (hleft : left ≤ s) (hsec : 0 ≤ quadraticSecant g s left) :
    g left ≤ g s := by
  rw [← sub_nonneg, quadraticSecant_exact g hg s left]
  exact mul_nonneg (sub_nonneg.mpr hleft) hsec

private theorem quadratic_lower_at_right
    (g : ℝ → ℝ) (hg : IsQuadraticLaw g) (s right : ℝ)
    (hright : s ≤ right) (hsec : quadraticSecant g s right ≤ 0) :
    g right ≤ g s := by
  rw [← sub_nonneg, quadraticSecant_exact g hg s right]
  exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hright) hsec

private structure CorrelatedBox
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ) : Prop where
  A_mem : (137423 / 100000 : ℝ) ≤ A ∧ A ≤ 137442 / 100000
  X_mem : (3962 / 100000 : ℝ) ≤ X ∧ X ≤ 3977 / 100000
  R_mem : (242817 / 1000000 : ℝ) ≤ R ∧ R ≤ 242898 / 1000000
  C_mem : (1323 / 100000 : ℝ) ≤ C ∧ C ≤ 1342 / 100000
  D_mem : (42817 / 1000000 : ℝ) ≤ D ∧ D ≤ 42898 / 1000000
  F_mem : (1571 / 5000 : ℝ) ≤ F ∧ F ≤ 63 / 200
  a_mem : (824479 / 1000000 : ℝ) ≤ a ∧ a ≤ 826465 / 1000000
  x_mem : (37851 / 1000000 : ℝ) ≤ x ∧ x ≤ 39761 / 1000000
  r_mem : (49817 / 1000000 : ℝ) ≤ r ∧ r ≤ 57183 / 1000000
  c_mem : (5179 / 1000000 : ℝ) ≤ c ∧ c ≤ 7165 / 1000000
  d_mem : (23317 / 1000000 : ℝ) ≤ d ∧ d ≤ 27183 / 1000000
  f_mem : (4411 / 25000 : ℝ) ≤ f ∧ f ≤ 4416 / 25000
  su_mem : (56168 / 100000 : ℝ) ≤ su ∧ su ≤ 56173 / 100000
  du_mem : (1687 / 100000 : ℝ) ≤ du ∧ du ≤ 1692 / 100000
  u4_mem : (141 / 1000 : ℝ) ≤ u4 ∧ u4 ≤ 144 / 1000
  sv_mem : (53815 / 100000 : ℝ) ≤ sv ∧ sv ≤ 53836 / 100000
  dv_mem : (555 / 10000 : ℝ) ≤ dv ∧ dv ≤ 558 / 10000
  v4_mem : (-4 / 1000 : ℝ) ≤ v4 ∧ v4 ≤ -2 / 1000
  q11_mem : (1778 / 10000 : ℝ) ≤ q11 ∧ q11 ≤ 179 / 1000
  q13_mem : (1 / 5 : ℝ) ≤ q13 ∧ q13 ≤ 2002 / 10000
  q33_mem : (3315 / 10000 : ℝ) ≤ q33 ∧ q33 ≤ 333 / 1000
  h11_mem : (14 / 1000 : ℝ) ≤ h11 ∧ h11 ≤ 20 / 1000
  h13_mem : (-11 / 1000 : ℝ) ≤ h13 ∧ h13 ≤ -9 / 1000
  h33_mem : (-120 / 1000 : ℝ) ≤ h33 ∧ h33 ≤ -117 / 1000

private theorem actual_correlated_box :
    CorrelatedBox
      cleanStrong cleanSkew cleanCrossSum cleanWeak cleanCrossDifference cleanP4
      perturbStrong perturbSkew perturbCrossSum perturbWeak
      perturbCrossDifference perturbP4
      (u0 + u2) (u0 - u2) u4 (v0 + v2) (v0 - v2) v4
      yoshidaEndpointOddLowGram11 yoshidaEndpointOddLowGram13
      yoshidaEndpointOddLowGram33
      (factorTwoCenteredSymmetricPerturbation centeredP1)
      (factorTwoCenteredSymmetricPerturbationBilinear centeredP1 centeredP3)
      (factorTwoCenteredSymmetricPerturbation centeredP3) := by
  have hc := clean_aligned_bounds
  have hp := perturb_aligned_bounds
  have hF := factorTwoP4_clean_diagonal_lt_three_hundred_fifteen_thousandths
  have hf := factorTwoP4_negative_perturbation_gt_one_seventy_six_forty_five
  have hJ := factorTwoIntrinsicAlternatingSharpBounds
  unfold FactorTwoIntrinsicAlternatingSharpBounds at hJ
  have hu4 := factorTwoIntrinsicFourP45Cross41_bounds
  have hv4 := factorTwoIntrinsicFourP45Cross43_bounds
  have hq11L := yoshidaEndpointOddLowGram11_gt_1778_div_10000
  have hq13 := yoshidaEndpointOddLowGram13_bounds
  have hq33L := yoshidaEndpointOddLowGram33_gt_3315_div_10000
  have hqU := yoshidaEndpointOddLowGram_diagonal_upper_bounds
  have hh := oddStructuralLow_perturbation_sharp_bounds
  rcases hc with
    ⟨hAL, hAU, hXL, hXU, hRL, hRU, hCL, hCU, hDL, hDU, hFL⟩
  rcases hp with
    ⟨haL, haU, hxL, hxU, hrL, hrU, hcL, hcU, hdL, hdU, _hfCoarse, hfU⟩
  rcases hJ with
    ⟨hsuL, hsuU, hduL, hduU, hsvL, hsvU, hdvL, hdvU⟩
  rcases hh with ⟨⟨hh11L, hh11U⟩, ⟨hh13L, hh13U⟩,
    ⟨hh33L, hh33U⟩⟩
  have hF' : cleanP4 < (63 / 200 : ℝ) := by
    unfold cleanP4
    norm_num at hF ⊢
    exact hF
  have hfL : (4411 / 25000 : ℝ) < perturbP4 := by
    simpa only [perturbP4] using
      (lt_trans (by norm_num : (4411 / 25000 : ℝ) < 17645 / 100000) hf)
  have hsuL' : (56168 / 100000 : ℝ) < u0 + u2 := by
    simpa only [u0, u2] using hsuL
  have hsuU' : u0 + u2 < (56173 / 100000 : ℝ) := by
    simpa only [u0, u2] using hsuU
  have hduL' : (1687 / 100000 : ℝ) < u0 - u2 := by
    simpa only [u0, u2] using hduL
  have hduU' : u0 - u2 < (1692 / 100000 : ℝ) := by
    simpa only [u0, u2] using hduU
  have hsvL' : (53815 / 100000 : ℝ) < v0 + v2 := by
    simpa only [v0, v2] using hsvL
  have hsvU' : v0 + v2 < (53836 / 100000 : ℝ) := by
    simpa only [v0, v2] using hsvU
  have hdvL' : (555 / 10000 : ℝ) < v0 - v2 := by
    simpa only [v0, v2] using hdvL
  have hdvU' : v0 - v2 < (558 / 10000 : ℝ) := by
    unfold v0 v2
    norm_num at hdvU ⊢
    exact hdvU
  exact ⟨⟨hAL.le, hAU.le⟩, ⟨hXL.le, hXU.le⟩,
    ⟨hRL.le, hRU.le⟩, ⟨hCL.le, hCU.le⟩, ⟨hDL.le, hDU.le⟩,
    ⟨hFL.le, hF'.le⟩, ⟨haL.le, haU.le⟩, ⟨hxL.le, hxU.le⟩,
    ⟨hrL.le, hrU.le⟩, ⟨hcL.le, hcU.le⟩, ⟨hdL.le, hdU.le⟩,
    ⟨hfL.le, hfU.le⟩, ⟨hsuL'.le, hsuU'.le⟩,
    ⟨hduL'.le, hduU'.le⟩, ⟨hu4.1.le, hu4.2.le⟩,
    ⟨hsvL'.le, hsvU'.le⟩, ⟨hdvL'.le, hdvU'.le⟩,
    ⟨hv4.1.le, hv4.2.le⟩, ⟨hq11L.le, hqU.1.le⟩,
    ⟨hq13.1.le, hq13.2.le⟩, ⟨hq33L.le, hqU.2.le⟩,
    ⟨hh11L.le, hh11U.le⟩, ⟨hh13L.le, hh13U.le⟩,
    ⟨hh33L.le, hh33U.le⟩⟩

private def alignedAdjugateASlope
    (F C D dx zx dy zy : ℝ) : ℝ :=
  (F * dx * dy + D * (dx * zy + zx * dy) + C * zx * zy) / 4

private def alignedMixedAdjugateBothASlope
    (F C D dx zx dy zy : ℝ) : ℝ :=
  (F * dx * dy + D * (dx * zy + zx * dy) + C * zx * zy) / 2

private def oddCouplingD
    (du dv o11 o13 o33 : ℝ) : ℝ :=
  o33 * du ^ 2 - 2 * o13 * du * dv + o11 * dv ^ 2

private def oddCouplingCross
    (du u4 dv v4 o11 o13 o33 : ℝ) : ℝ :=
  o33 * du * u4 - o13 * (du * v4 + u4 * dv) + o11 * dv * v4

private def oddCouplingFour
    (u4 v4 o11 o13 o33 : ℝ) : ℝ :=
  o33 * u4 ^ 2 - 2 * o13 * u4 * v4 + o11 * v4 ^ 2

private def oddCouplingCore
    (F C D du u4 dv v4 o11 o13 o33 : ℝ) : ℝ :=
  F * oddCouplingD du dv o11 o13 o33 +
    2 * D * oddCouplingCross du u4 dv v4 o11 o13 o33 +
      C * oddCouplingFour u4 v4 o11 o13 o33

private theorem oddCouplingCore_du_step
    (F C D du du0 u4 dv v4 o11 o13 o33 : ℝ) :
    oddCouplingCore F C D du u4 dv v4 o11 o13 o33 -
        oddCouplingCore F C D du0 u4 dv v4 o11 o13 o33 =
      (du - du0) *
        (F * (o33 * (du + du0) - 2 * o13 * dv) +
          2 * D * (o33 * u4 - o13 * v4)) := by
  unfold oddCouplingCore oddCouplingD oddCouplingCross oddCouplingFour
  ring

private theorem oddCouplingCore_u4_step
    (F C D du u4 u40 dv v4 o11 o13 o33 : ℝ) :
    oddCouplingCore F C D du u4 dv v4 o11 o13 o33 -
        oddCouplingCore F C D du u40 dv v4 o11 o13 o33 =
      (u4 - u40) *
        (2 * D * (o33 * du - o13 * dv) +
          C * (o33 * (u4 + u40) - 2 * o13 * v4)) := by
  unfold oddCouplingCore oddCouplingD oddCouplingCross oddCouplingFour
  ring

private theorem oddCouplingCore_dv_step
    (F C D du u4 dv dv0 v4 o11 o13 o33 : ℝ) :
    oddCouplingCore F C D du u4 dv v4 o11 o13 o33 -
        oddCouplingCore F C D du u4 dv0 v4 o11 o13 o33 =
      (dv - dv0) *
        (F * (o11 * (dv + dv0) - 2 * o13 * du) +
          2 * D * (o11 * v4 - o13 * u4)) := by
  unfold oddCouplingCore oddCouplingD oddCouplingCross oddCouplingFour
  ring

private theorem oddCouplingCore_v4_step
    (F C D du u4 dv v4 v40 o11 o13 o33 : ℝ) :
    oddCouplingCore F C D du u4 dv v4 o11 o13 o33 -
        oddCouplingCore F C D du u4 dv v40 o11 o13 o33 =
      (v4 - v40) *
        (2 * D * (o11 * dv - o13 * du) +
          C * (o11 * (v4 + v40) - 2 * o13 * u4)) := by
  unfold oddCouplingCore oddCouplingD oddCouplingCross oddCouplingFour
  ring

private def correlatedASlope
    (C D F c d f
      du u4 dv v4 q11 q13 q33 h11 h13 h33 : ℝ) : ℝ :=
  let Cp := C - c
  let Dp := D - d
  let Fp := F - f
  let Cm := C + c
  let Dm := D + d
  let Fm := F + f
  let o11p := q11 + h11
  let o13p := q13 + h13
  let o33p := q33 + h33
  let o11m := q11 - h11
  let o13m := q13 - h13
  let o33m := q33 - h33
  let oddPlus := o11p * o33p - o13p ^ 2
  let oddMixed := o11p * o33m + o11m * o33p - 2 * o13p * o13m
  let oddMinus := o11m * o33m - o13m ^ 2
  let plusCouplingSlope :=
    o33m * alignedAdjugateASlope Fp Cp Dp du u4 du u4 -
      2 * o13m * alignedAdjugateASlope Fp Cp Dp du u4 dv v4 +
      o11m * alignedAdjugateASlope Fp Cp Dp dv v4 dv v4
  let mixedCouplingSlope :=
    o33p * alignedMixedAdjugateBothASlope F C D du u4 du u4 -
      2 * o13p * alignedMixedAdjugateBothASlope F C D du u4 dv v4 +
      o11p * alignedMixedAdjugateBothASlope F C D dv v4 dv v4
  ((Fp * Cp - Dp ^ 2) / 4) * oddMinus +
    ((Fm * Cp + Fp * Cm - 2 * Dp * Dm + Fp * Cp - Dp ^ 2) / 4) * oddMixed +
    ((Fp * Cm + Fm * Cp - 2 * Dp * Dm + Fm * Cm - Dm ^ 2) / 4) * oddPlus -
    plusCouplingSlope - mixedCouplingSlope + (u4 * dv - v4 * du) ^ 2 / 4

private theorem correlated_A_secant_eq
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ) :
    quadraticSecant
      (fun z ↦ correlatedCoefficientTwo z X R C D F a x r c d f
        su du u4 sv dv v4 q11 q13 q33 h11 h13 h33)
      A (137423 / 100000) =
        correlatedASlope C D F c d f
          du u4 dv v4 q11 q13 q33 h11 h13 h33 := by
  unfold quadraticSecant correlatedCoefficientTwo correlatedASlope
    alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
    alignedMixedAdjugatePair alignedCrossEnergy alignedAdjugateASlope
    alignedMixedAdjugateBothASlope alignedEntry00 alignedEntry02 alignedEntry04
    alignedEntry22 alignedEntry24 mixedDeterminantOne
  dsimp only
  ring

set_option maxHeartbeats 500000 in
private theorem oddASlope_bounds
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (26 / 1000 : ℝ) ≤
        (q11 - h11) * (q33 - h33) - (q13 - h13) ^ 2 ∧
      (41 / 1000 : ℝ) ≤
        (q11 + h11) * (q33 - h33) +
          (q11 - h11) * (q33 + h33) -
            2 * (q13 + h13) * (q13 - h13) ∧
      (4 / 1000 : ℝ) ≤
        (q11 + h11) * (q33 + h33) - (q13 + h13) ^ 2 := by
  rcases hbox.q11_mem with ⟨hq11L, hq11U⟩
  rcases hbox.q13_mem with ⟨hq13L, hq13U⟩
  rcases hbox.q33_mem with ⟨hq33L, hq33U⟩
  rcases hbox.h11_mem with ⟨hh11L, hh11U⟩
  rcases hbox.h13_mem with ⟨hh13L, hh13U⟩
  rcases hbox.h33_mem with ⟨hh33L, hh33U⟩
  have hOddMinus : (26 / 1000 : ℝ) ≤
      (q11 - h11) * (q33 - h33) - (q13 - h13) ^ 2 := by
    have hm11L : (1578 / 10000 : ℝ) ≤ q11 - h11 := by linarith
    have hm13U : q13 - h13 ≤ (2112 / 10000 : ℝ) := by linarith
    have hm13Nonneg : 0 ≤ q13 - h13 := by linarith
    have hm33L : (4485 / 10000 : ℝ) ≤ q33 - h33 := by linarith
    have hmProd : (1578 / 10000 : ℝ) * (4485 / 10000) ≤
        (q11 - h11) * (q33 - h33) := by bound
    have hmSq : (q13 - h13) ^ 2 ≤ (2112 / 10000 : ℝ) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hm13U)
        (by norm_num; linarith : 0 ≤ q13 - h13 + 2112 / 10000)]
    nlinarith only [hmProd, hmSq]
  have hOddMixed : (41 / 1000 : ℝ) ≤
      (q11 + h11) * (q33 - h33) +
        (q11 - h11) * (q33 + h33) -
          2 * (q13 + h13) * (q13 - h13) := by
    ring_nf
    have hqProd : (1778 / 10000 : ℝ) * (3315 / 10000) ≤ q11 * q33 := by
      bound
    have hq13Nonneg : 0 ≤ q13 := by linarith
    have hqSq : q13 ^ 2 ≤ (2002 / 10000 : ℝ) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hq13U)
        (by norm_num; linarith : 0 ≤ q13 + 2002 / 10000)]
    have hhProd : (14 / 1000 : ℝ) * (117 / 1000) ≤ h11 * (-h33) := by
      bound
    have hh13Neg : h13 ≤ 0 := by linarith
    have hhSq : (9 / 1000 : ℝ) ^ 2 ≤ h13 ^ 2 := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ -h13 - 9 / 1000)
        (by norm_num; linarith : 0 ≤ -h13 + 9 / 1000)]
    nlinarith only [hqProd, hqSq, hhProd, hhSq]
  have hOddPlus : (4 / 1000 : ℝ) ≤
      (q11 + h11) * (q33 + h33) - (q13 + h13) ^ 2 := by
    have hp11L : (1918 / 10000 : ℝ) ≤ q11 + h11 := by linarith
    have hp13U : q13 + h13 ≤ (1912 / 10000 : ℝ) := by linarith
    have hp13Nonneg : 0 ≤ q13 + h13 := by linarith
    have hp33L : (2115 / 10000 : ℝ) ≤ q33 + h33 := by linarith
    have hpProd : (1918 / 10000 : ℝ) * (2115 / 10000) ≤
        (q11 + h11) * (q33 + h33) := by bound
    have hpSq : (q13 + h13) ^ 2 ≤ (1912 / 10000 : ℝ) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hp13U)
        (by norm_num; linarith : 0 ≤ q13 + h13 + 1912 / 10000)]
    nlinarith only [hpProd, hpSq]
  exact ⟨hOddMinus, hOddMixed, hOddPlus⟩

set_option maxHeartbeats 500000 in
private theorem evenASlopeDeterminant_bounds
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (112 / 1000000 : ℝ) ≤
        ((F - f) * (C - c) - (D - d) ^ 2) / 4 ∧
      (91 / 100000 : ℝ) ≤
        ((F + f) * (C - c) + (F - f) * (C + c) -
          2 * (D - d) * (D + d) +
          (F - f) * (C - c) - (D - d) ^ 2) / 4 ∧
      (21 / 10000 : ℝ) ≤
        ((F - f) * (C + c) + (F + f) * (C - c) -
          2 * (D - d) * (D + d) +
          (F + f) * (C + c) - (D + d) ^ 2) / 4 := by
  rcases hbox.C_mem with ⟨hCL, hCU⟩
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.F_mem with ⟨hFL, hFU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  have hDetMinus : (112 / 1000000 : ℝ) ≤
      ((F - f) * (C - c) - (D - d) ^ 2) / 4 := by
    have hFstep : 0 ≤ (F - 1571 / 5000) * (C - c) :=
      mul_nonneg (by linarith) (by linarith)
    have hCstep : 0 ≤ (C - 1323 / 100000) * (1571 / 5000 - f) :=
      mul_nonneg (by linarith) (by linarith)
    have hcstep : 0 ≤ (7165 / 1000000 - c) * (1571 / 5000 - f) :=
      mul_nonneg (by linarith) (by linarith)
    have hfstep : 0 ≤ (4416 / 25000 - f) *
        (1323 / 100000 - 7165 / 1000000) :=
      mul_nonneg (by linarith) (by norm_num)
    have hDstep : 0 ≤ (42898 / 1000000 - D) *
        (42898 / 1000000 + D - 2 * d) :=
      mul_nonneg (by linarith) (by linarith)
    have hdstep : 0 ≤ (d - 23317 / 1000000) *
        (2 * (42898 / 1000000 : ℝ) - d - 23317 / 1000000) :=
      mul_nonneg (by linarith) (by linarith)
    have hcorner :
        (((1571 / 5000 - 4416 / 25000) *
            (1323 / 100000 - 7165 / 1000000) -
              (42898 / 1000000 - 23317 / 1000000) ^ 2) / 4 : ℝ) ≤
          ((F - f) * (C - c) - (D - d) ^ 2) / 4 := by
      nlinarith only [hFstep, hCstep, hcstep, hfstep, hDstep, hdstep]
    exact (by norm_num : (112 / 1000000 : ℝ) ≤
      ((1571 / 5000 - 4416 / 25000) *
          (1323 / 100000 - 7165 / 1000000) -
            (42898 / 1000000 - 23317 / 1000000) ^ 2) / 4).trans hcorner
  have hDetMixed : (91 / 100000 : ℝ) ≤
      ((F + f) * (C - c) + (F - f) * (C + c) -
          2 * (D - d) * (D + d) +
          (F - f) * (C - c) - (D - d) ^ 2) / 4 := by
    have hFstep : 0 ≤ (F - 1571 / 5000) * (3 * C - c) :=
      mul_nonneg (by linarith) (by linarith)
    have hCstep : 0 ≤ (C - 1323 / 100000) *
        (3 * (1571 / 5000 : ℝ) - f) :=
      mul_nonneg (by linarith) (by linarith)
    have hcstep : 0 ≤ (7165 / 1000000 - c) *
        (1571 / 5000 + f) :=
      mul_nonneg (by linarith) (by linarith)
    have hfstep : 0 ≤ (4416 / 25000 - f) *
        (1323 / 100000 + 7165 / 1000000) :=
      mul_nonneg (by linarith) (by norm_num)
    have hDstep : 0 ≤ (42898 / 1000000 - D) *
        (3 * (D + 42898 / 1000000) - 2 * d) :=
      mul_nonneg (by linarith) (by linarith)
    have hdstep : 0 ≤ (d - 23317 / 1000000) *
        (2 * (42898 / 1000000 : ℝ) + d + 23317 / 1000000) :=
      mul_nonneg (by linarith) (by linarith)
    have hcorner :
        ((3 * (1571 / 5000) * (1323 / 100000) -
            (1571 / 5000) * (7165 / 1000000) -
            (4416 / 25000) * (1323 / 100000) -
            (4416 / 25000) * (7165 / 1000000) -
            3 * (42898 / 1000000) ^ 2 +
            2 * (42898 / 1000000) * (23317 / 1000000) +
            (23317 / 1000000) ^ 2) / 4 : ℝ) ≤
          ((F + f) * (C - c) + (F - f) * (C + c) -
            2 * (D - d) * (D + d) +
            (F - f) * (C - c) - (D - d) ^ 2) / 4 := by
      nlinarith only [hFstep, hCstep, hcstep, hfstep, hDstep, hdstep]
    exact (by norm_num : (91 / 100000 : ℝ) ≤
      (3 * (1571 / 5000) * (1323 / 100000) -
          (1571 / 5000) * (7165 / 1000000) -
          (4416 / 25000) * (1323 / 100000) -
          (4416 / 25000) * (7165 / 1000000) -
          3 * (42898 / 1000000) ^ 2 +
          2 * (42898 / 1000000) * (23317 / 1000000) +
          (23317 / 1000000) ^ 2) / 4).trans hcorner
  have hDetPlus : (21 / 10000 : ℝ) ≤
      ((F - f) * (C + c) + (F + f) * (C - c) -
          2 * (D - d) * (D + d) +
          (F + f) * (C + c) - (D + d) ^ 2) / 4 := by
    have hFstep : 0 ≤ (F - 1571 / 5000) * (3 * C + c) :=
      mul_nonneg (by linarith) (by linarith)
    have hCstep : 0 ≤ (C - 1323 / 100000) *
        (3 * (1571 / 5000 : ℝ) + f) :=
      mul_nonneg (by linarith) (by linarith)
    have hcstep : 0 ≤ (c - 5179 / 1000000) *
        (1571 / 5000 - f) :=
      mul_nonneg (by linarith) (by linarith)
    have hfstep : 0 ≤ (f - 4411 / 25000) *
        (1323 / 100000 - 5179 / 1000000) :=
      mul_nonneg (by linarith) (by norm_num)
    have hDstep : 0 ≤ (42898 / 1000000 - D) *
        (3 * (D + 42898 / 1000000) + 2 * d) :=
      mul_nonneg (by linarith) (by linarith)
    have hdstep : 0 ≤ (27183 / 1000000 - d) *
        (2 * (42898 / 1000000 : ℝ) - d - 27183 / 1000000) :=
      mul_nonneg (by linarith) (by linarith)
    have hcorner :
        ((3 * (1571 / 5000) * (1323 / 100000) +
            (1571 / 5000) * (5179 / 1000000) +
            (4411 / 25000) * (1323 / 100000) -
            (4411 / 25000) * (5179 / 1000000) -
            3 * (42898 / 1000000) ^ 2 -
            2 * (42898 / 1000000) * (27183 / 1000000) +
            (27183 / 1000000) ^ 2) / 4 : ℝ) ≤
          ((F - f) * (C + c) + (F + f) * (C - c) -
            2 * (D - d) * (D + d) +
            (F + f) * (C + c) - (D + d) ^ 2) / 4 := by
      nlinarith only [hFstep, hCstep, hcstep, hfstep, hDstep, hdstep]
    exact (by norm_num : (21 / 10000 : ℝ) ≤
      (3 * (1571 / 5000) * (1323 / 100000) +
          (1571 / 5000) * (5179 / 1000000) +
          (4411 / 25000) * (1323 / 100000) -
          (4411 / 25000) * (5179 / 1000000) -
          3 * (42898 / 1000000) ^ 2 -
          2 * (42898 / 1000000) * (27183 / 1000000) +
          (27183 / 1000000) ^ 2) / 4).trans hcorner
  exact ⟨hDetMinus, hDetMixed, hDetPlus⟩

set_option maxHeartbeats 1000000 in
private theorem plusASlopeCoupling_upper
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
      (q33 - h33) *
            ((F - f) * du * du + (D - d) * (du * u4 + u4 * du) +
              (C - c) * u4 * u4) /
              4 -
          2 * (q13 - h13) *
            (((F - f) * du * dv + (D - d) * (du * v4 + u4 * dv) +
              (C - c) * u4 * v4) /
              4) +
          (q11 - h11) *
              ((F - f) * dv * dv + (D - d) * (dv * v4 + v4 * dv) +
                (C - c) * v4 * v4) /
                4 ≤
        (24 / 1000000 : ℝ) := by
  rcases hbox.C_mem with ⟨hCL, hCU⟩
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.F_mem with ⟨hFL, hFU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  rcases hbox.du_mem with ⟨hduL, hduU⟩
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  rcases hbox.v4_mem with ⟨hv4L, hv4U⟩
  rcases hbox.q11_mem with ⟨hq11L, hq11U⟩
  rcases hbox.q13_mem with ⟨hq13L, hq13U⟩
  rcases hbox.q33_mem with ⟨hq33L, hq33U⟩
  rcases hbox.h11_mem with ⟨hh11L, hh11U⟩
  rcases hbox.h13_mem with ⟨hh13L, hh13U⟩
  rcases hbox.h33_mem with ⟨hh33L, hh33U⟩
  rw [show
    (q33 - h33) *
          ((F - f) * du * du + (D - d) * (du * u4 + u4 * du) +
            (C - c) * u4 * u4) / 4 -
        2 * (q13 - h13) *
          (((F - f) * du * dv + (D - d) * (du * v4 + u4 * dv) +
            (C - c) * u4 * v4) / 4) +
        (q11 - h11) *
            ((F - f) * dv * dv + (D - d) * (dv * v4 + v4 * dv) +
              (C - c) * v4 * v4) / 4 =
      oddCouplingCore (F - f) (C - c) (D - d)
        du u4 dv v4 (q11 - h11) (q13 - h13) (q33 - h33) / 4 by
    unfold oddCouplingCore oddCouplingD oddCouplingCross oddCouplingFour
    ring]
  have hom11L : (1578 / 10000 : ℝ) ≤ q11 - h11 := by linarith
  have hom11U : q11 - h11 ≤ (165 / 1000 : ℝ) := by linarith
  have hom13L : (209 / 1000 : ℝ) ≤ q13 - h13 := by linarith
  have hom13U : q13 - h13 ≤ (2112 / 10000 : ℝ) := by linarith
  have hom33L : (4485 / 10000 : ℝ) ≤ q33 - h33 := by linarith
  have hom33U : q33 - h33 ≤ (453 / 1000 : ℝ) := by linarith
  have hduSqL : (1687 / 100000 : ℝ) ^ 2 ≤ du ^ 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ du - 1687 / 100000)
      (by norm_num; linarith : 0 ≤ du + 1687 / 100000)]
  have hduDvU : du * dv ≤ (1692 / 100000 : ℝ) * (558 / 10000) := by
    bound
  have hdvSqL : (555 / 10000 : ℝ) ^ 2 ≤ dv ^ 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ dv - 555 / 10000)
      (by norm_num; linarith : 0 ≤ dv + 555 / 10000)]
  have hEDpos : 0 ≤ oddCouplingD du dv
      (q11 - h11) (q13 - h13) (q33 - h33) := by
    have ht0 : (4485 / 10000 : ℝ) * (1687 / 100000) ^ 2 ≤
        (q33 - h33) * du ^ 2 := by bound
    have ht1 : (q13 - h13) * du * dv ≤
        (2112 / 10000 : ℝ) * (1692 / 100000) * (558 / 10000) := by
      bound
    have ht2 : (1578 / 10000 : ℝ) * (555 / 10000) ^ 2 ≤
        (q11 - h11) * dv ^ 2 := by bound
    unfold oddCouplingD
    nlinarith only [ht0, ht1, ht2]
  have hEFpos : 0 ≤ oddCouplingFour u4 v4
      (q11 - h11) (q13 - h13) (q33 - h33) := by
    unfold oddCouplingFour
    have h0 : 0 ≤ (q33 - h33) * u4 ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg u4)
    have h1 : 0 ≤ -2 * (q13 - h13) * u4 * v4 := by
      have : 0 ≤ 2 * (q13 - h13) * u4 * (-v4) :=
        mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
      linarith
    have h2 : 0 ≤ (q11 - h11) * v4 ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg v4)
    linarith
  have hduv4L : (1692 / 100000 : ℝ) * (-4 / 1000) ≤ du * v4 := by
    have hneg : 0 ≤ -v4 := by linarith
    have hmag : du * (-v4) ≤
        (1692 / 100000 : ℝ) * (4 / 1000) := by bound
    linarith
  have hu4dvL : (141 / 1000 : ℝ) * (555 / 10000) ≤ u4 * dv := by
    bound
  have hCrossArgL :
      (1692 / 100000 : ℝ) * (-4 / 1000) +
          (141 / 1000) * (555 / 10000) ≤ du * v4 + u4 * dv := by
    linarith
  have huTermU : (q33 - h33) * du * u4 ≤
      (453 / 1000 : ℝ) * (1692 / 100000) * (144 / 1000) := by
    bound
  have hmTermL :
      (209 / 1000 : ℝ) *
          ((1692 / 100000) * (-4 / 1000) +
            (141 / 1000) * (555 / 10000)) ≤
        (q13 - h13) * (du * v4 + u4 * dv) := by
    have h0 : 0 ≤
        ((1692 / 100000 : ℝ) * (-4 / 1000) +
          (141 / 1000) * (555 / 10000)) := by norm_num
    have h1 := mul_nonneg
      (by linarith : 0 ≤ (q13 - h13) - 209 / 1000)
      (by linarith : 0 ≤ du * v4 + u4 * dv)
    have h2 := mul_nonneg (by norm_num : (0 : ℝ) ≤ 209 / 1000)
      (by linarith : 0 ≤ du * v4 + u4 * dv -
        ((1692 / 100000) * (-4 / 1000) +
          (141 / 1000) * (555 / 10000)))
    nlinarith
  have hvTermU : (q11 - h11) * dv * v4 ≤
      -(1578 / 10000 : ℝ) * (555 / 10000) * (2 / 1000) := by
    have hmag : (1578 / 10000 : ℝ) * (555 / 10000) * (2 / 1000) ≤
        (q11 - h11) * dv * (-v4) := by bound
    linarith
  have hEXneg : oddCouplingCross du u4 dv v4
      (q11 - h11) (q13 - h13) (q33 - h33) ≤ 0 := by
    unfold oddCouplingCross
    norm_num at huTermU hmTermL hvTermU ⊢
    nlinarith only [huTermU, hmTermL, hvTermU]
  have hQuPos : 0 ≤
      (433 / 3125 : ℝ) * du ^ 2 +
        2 * (7817 / 500000) * du * u4 +
          (8241 / 1000000) * u4 ^ 2 := by positivity
  have hQvPos : 0 ≤
      (433 / 3125 : ℝ) * dv ^ 2 +
        2 * (7817 / 500000) * dv * v4 +
          (8241 / 1000000) * v4 ^ 2 := by
    have hfirst : (433 / 3125 : ℝ) * (555 / 10000) ^ 2 ≤
        (433 / 3125) * dv ^ 2 := by bound
    have hcross : 2 * (7817 / 500000 : ℝ) * dv * v4 ≥
        2 * (7817 / 500000) * (558 / 10000) * (-4 / 1000) := by
      have hmag : dv * (-v4) ≤ (558 / 10000 : ℝ) * (4 / 1000) := by
        bound
      calc
        2 * (7817 / 500000 : ℝ) * dv * v4 =
            -(2 * (7817 / 500000) * (dv * (-v4))) := by ring
        _ ≥ -(2 * (7817 / 500000) * ((558 / 10000) * (4 / 1000))) :=
          neg_le_neg (mul_le_mul_of_nonneg_left hmag (by norm_num))
        _ = 2 * (7817 / 500000) * (558 / 10000) * (-4 / 1000) := by ring
    nlinarith [sq_nonneg v4]
  have hQuvPos : 0 ≤
      (433 / 3125 : ℝ) * du * dv +
        (7817 / 500000) * (du * v4 + u4 * dv) +
          (8241 / 1000000) * u4 * v4 := by
    have hfirst : (433 / 3125 : ℝ) * (1687 / 100000) * (555 / 10000) ≤
        (433 / 3125) * du * dv := by bound
    have hmiddle : (7817 / 500000 : ℝ) *
        ((1692 / 100000) * (-4 / 1000) +
          (141 / 1000) * (555 / 10000)) ≤
        (7817 / 500000) * (du * v4 + u4 * dv) := by linarith
    have hlast : (8241 / 1000000 : ℝ) * u4 * v4 ≥
        (8241 / 1000000) * (144 / 1000) * (-4 / 1000) := by
      have hmag : u4 * (-v4) ≤ (144 / 1000 : ℝ) * (4 / 1000) := by
        bound
      calc
        (8241 / 1000000 : ℝ) * u4 * v4 =
            -((8241 / 1000000) * (u4 * (-v4))) := by ring
        _ ≥ -((8241 / 1000000) * ((144 / 1000) * (4 / 1000))) :=
          neg_le_neg (mul_le_mul_of_nonneg_left hmag (by norm_num))
        _ = (8241 / 1000000) * (144 / 1000) * (-4 / 1000) := by ring
    norm_num at hfirst hmiddle hlast ⊢
    linarith only [hfirst, hmiddle, hlast]
  have hcore :
      oddCouplingCore (F - f) (C - c) (D - d)
          du u4 dv v4 (q11 - h11) (q13 - h13) (q33 - h33) ≤
        oddCouplingCore (433 / 3125) (8241 / 1000000) (7817 / 500000)
          (1692 / 100000) (144 / 1000) (558 / 10000) (-4 / 1000)
          (165 / 1000) (209 / 1000) (453 / 1000) := by
    calc
      oddCouplingCore (F - f) (C - c) (D - d)
          du u4 dv v4 (q11 - h11) (q13 - h13) (q33 - h33) ≤
          oddCouplingCore (433 / 3125) (C - c) (D - d)
            du u4 dv v4 (q11 - h11) (q13 - h13) (q33 - h33) := by
              apply le_of_sub_nonneg
              rw [show
                oddCouplingCore (433 / 3125) (C - c) (D - d)
                    du u4 dv v4 (q11 - h11) (q13 - h13) (q33 - h33) -
                  oddCouplingCore (F - f) (C - c) (D - d)
                    du u4 dv v4 (q11 - h11) (q13 - h13) (q33 - h33) =
                  (433 / 3125 - (F - f)) *
                    oddCouplingD du dv (q11 - h11) (q13 - h13) (q33 - h33) by
                unfold oddCouplingCore; ring]
              exact mul_nonneg (by linarith) hEDpos
      _ ≤ oddCouplingCore (433 / 3125) (8241 / 1000000) (D - d)
            du u4 dv v4 (q11 - h11) (q13 - h13) (q33 - h33) := by
              apply le_of_sub_nonneg
              rw [show
                oddCouplingCore (433 / 3125) (8241 / 1000000) (D - d)
                    du u4 dv v4 (q11 - h11) (q13 - h13) (q33 - h33) -
                  oddCouplingCore (433 / 3125) (C - c) (D - d)
                    du u4 dv v4 (q11 - h11) (q13 - h13) (q33 - h33) =
                  (8241 / 1000000 - (C - c)) *
                    oddCouplingFour u4 v4 (q11 - h11) (q13 - h13) (q33 - h33) by
                unfold oddCouplingCore; ring]
              exact mul_nonneg (by linarith) hEFpos
      _ ≤ oddCouplingCore (433 / 3125) (8241 / 1000000) (7817 / 500000)
            du u4 dv v4 (q11 - h11) (q13 - h13) (q33 - h33) := by
              apply le_of_sub_nonneg
              rw [show
                oddCouplingCore (433 / 3125) (8241 / 1000000) (7817 / 500000)
                    du u4 dv v4 (q11 - h11) (q13 - h13) (q33 - h33) -
                  oddCouplingCore (433 / 3125) (8241 / 1000000) (D - d)
                    du u4 dv v4 (q11 - h11) (q13 - h13) (q33 - h33) =
                  2 * (7817 / 500000 - (D - d)) *
                    oddCouplingCross du u4 dv v4
                      (q11 - h11) (q13 - h13) (q33 - h33) by
                unfold oddCouplingCore; ring]
              exact mul_nonneg_of_nonpos_of_nonpos (by linarith) hEXneg
      _ ≤ oddCouplingCore (433 / 3125) (8241 / 1000000) (7817 / 500000)
            du u4 dv v4 (q11 - h11) (q13 - h13) (453 / 1000) := by
              rw [← sub_nonneg]
              convert mul_nonneg
                  (by linarith : 0 ≤ (453 / 1000 : ℝ) - (q33 - h33))
                  hQuPos using 1 <;>
                unfold oddCouplingCore oddCouplingD oddCouplingCross
                  oddCouplingFour <;> ring
      _ ≤ oddCouplingCore (433 / 3125) (8241 / 1000000) (7817 / 500000)
            du u4 dv v4 (q11 - h11) (209 / 1000) (453 / 1000) := by
              rw [← sub_nonneg]
              convert mul_nonneg
                  (by linarith : 0 ≤ 2 * ((q13 - h13) - 209 / 1000))
                  hQuvPos using 1 <;>
                unfold oddCouplingCore oddCouplingD oddCouplingCross
                  oddCouplingFour <;> ring
      _ ≤ oddCouplingCore (433 / 3125) (8241 / 1000000) (7817 / 500000)
            du u4 dv v4 (165 / 1000) (209 / 1000) (453 / 1000) := by
              rw [← sub_nonneg]
              convert mul_nonneg
                  (by linarith : 0 ≤ (165 / 1000 : ℝ) - (q11 - h11))
                  hQvPos using 1 <;>
                unfold oddCouplingCore oddCouplingD oddCouplingCross
                  oddCouplingFour <;> ring
      _ ≤ oddCouplingCore (433 / 3125) (8241 / 1000000) (7817 / 500000)
            (1692 / 100000) u4 dv v4
            (165 / 1000) (209 / 1000) (453 / 1000) := by
              rw [← sub_nonneg, oddCouplingCore_du_step]
              have hslope : 0 ≤
                  (433 / 3125 : ℝ) *
                      ((453 / 1000) * (du + 1692 / 100000) -
                        2 * (209 / 1000) * dv) +
                    2 * (7817 / 500000) *
                      ((453 / 1000) * u4 - (209 / 1000) * v4) := by
                norm_num at ⊢
                linarith
              simpa [add_comm] using mul_nonneg (by linarith) hslope
      _ ≤ oddCouplingCore (433 / 3125) (8241 / 1000000) (7817 / 500000)
            (1692 / 100000) (144 / 1000) dv v4
            (165 / 1000) (209 / 1000) (453 / 1000) := by
              rw [← sub_nonneg, oddCouplingCore_u4_step]
              have hslope : 0 ≤
                  2 * (7817 / 500000 : ℝ) *
                      ((453 / 1000) * (1692 / 100000) -
                        (209 / 1000) * dv) +
                    (8241 / 1000000) *
                      ((453 / 1000) * (u4 + 144 / 1000) -
                        2 * (209 / 1000) * v4) := by
                norm_num at ⊢
                linarith
              simpa [add_comm] using mul_nonneg (by linarith) hslope
      _ ≤ oddCouplingCore (433 / 3125) (8241 / 1000000) (7817 / 500000)
            (1692 / 100000) (144 / 1000) (558 / 10000) v4
            (165 / 1000) (209 / 1000) (453 / 1000) := by
              rw [← sub_nonneg, oddCouplingCore_dv_step]
              have hslope : 0 ≤
                  (433 / 3125 : ℝ) *
                      ((165 / 1000) * (dv + 558 / 10000) -
                        2 * (209 / 1000) * (1692 / 100000)) +
                    2 * (7817 / 500000) *
                      ((165 / 1000) * v4 -
                        (209 / 1000) * (144 / 1000)) := by
                norm_num at ⊢
                linarith
              simpa [add_comm] using mul_nonneg (by linarith) hslope
      _ ≤ oddCouplingCore (433 / 3125) (8241 / 1000000) (7817 / 500000)
            (1692 / 100000) (144 / 1000) (558 / 10000) (-4 / 1000)
            (165 / 1000) (209 / 1000) (453 / 1000) := by
              rw [← sub_nonpos, oddCouplingCore_v4_step]
              have hslope :
                  2 * (7817 / 500000 : ℝ) *
                      ((165 / 1000) * (558 / 10000) -
                        (209 / 1000) * (1692 / 100000)) +
                    (8241 / 1000000) *
                      ((165 / 1000) * (v4 + (-4 / 1000)) -
                        2 * (209 / 1000) * (144 / 1000)) ≤ 0 := by
                norm_num at ⊢
                linarith
              exact mul_nonpos_of_nonneg_of_nonpos (by linarith) hslope
  calc
    oddCouplingCore (F - f) (C - c) (D - d)
        du u4 dv v4 (q11 - h11) (q13 - h13) (q33 - h33) / 4 ≤
        oddCouplingCore (433 / 3125) (8241 / 1000000) (7817 / 500000)
          (1692 / 100000) (144 / 1000) (558 / 10000) (-4 / 1000)
          (165 / 1000) (209 / 1000) (453 / 1000) / 4 := by
            nlinarith only [hcore]
    _ ≤ (24 / 1000000 : ℝ) := by
      norm_num [oddCouplingCore, oddCouplingD, oddCouplingCross,
        oddCouplingFour]

set_option maxHeartbeats 1000000 in
private theorem mixedASlopeCoupling_upper
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
      (q33 + h33) *
            ((F * du * du + D * (du * u4 + u4 * du) + C * u4 * u4) /
              2) -
          2 * (q13 + h13) *
            ((F * du * dv + D * (du * v4 + u4 * dv) + C * u4 * v4) /
              2) +
          (q11 + h11) *
              ((F * dv * dv + D * (dv * v4 + v4 * dv) + C * v4 * v4) /
                2) ≤
        (39 / 1000000 : ℝ) := by
  have hOddPlus := (oddASlope_bounds
    A X R C D F a x r c d f
    su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox).2.2
  rcases hbox.C_mem with ⟨hCL, hCU⟩
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.F_mem with ⟨hFL, hFU⟩
  rcases hbox.du_mem with ⟨hduL, hduU⟩
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  rcases hbox.v4_mem with ⟨hv4L, hv4U⟩
  rcases hbox.q11_mem with ⟨hq11L, hq11U⟩
  rcases hbox.q13_mem with ⟨hq13L, hq13U⟩
  rcases hbox.q33_mem with ⟨hq33L, hq33U⟩
  rcases hbox.h11_mem with ⟨hh11L, hh11U⟩
  rcases hbox.h13_mem with ⟨hh13L, hh13U⟩
  rcases hbox.h33_mem with ⟨hh33L, hh33U⟩
  rw [show
    (q33 + h33) *
          ((F * du * du + D * (du * u4 + u4 * du) + C * u4 * u4) / 2) -
        2 * (q13 + h13) *
          ((F * du * dv + D * (du * v4 + u4 * dv) + C * u4 * v4) / 2) +
        (q11 + h11) *
            ((F * dv * dv + D * (dv * v4 + v4 * dv) + C * v4 * v4) / 2) =
      oddCouplingCore F C D du u4 dv v4
        (q11 + h11) (q13 + h13) (q33 + h33) / 2 by
    unfold oddCouplingCore oddCouplingD oddCouplingCross oddCouplingFour
    ring]
  have hop11L : (1918 / 10000 : ℝ) ≤ q11 + h11 := by linarith
  have hop11U : q11 + h11 ≤ (199 / 1000 : ℝ) := by linarith
  have hop13L : (189 / 1000 : ℝ) ≤ q13 + h13 := by linarith
  have hop13U : q13 + h13 ≤ (1912 / 10000 : ℝ) := by linarith
  have hop33L : (2115 / 10000 : ℝ) ≤ q33 + h33 := by linarith
  have hop33U : q33 + h33 ≤ (216 / 1000 : ℝ) := by linarith
  have hEDpos : 0 ≤ oddCouplingD du dv
      (q11 + h11) (q13 + h13) (q33 + h33) := by
    have hscaled : 0 ≤ (q33 + h33) *
        oddCouplingD du dv (q11 + h11) (q13 + h13) (q33 + h33) := by
      rw [show
        (q33 + h33) *
            oddCouplingD du dv (q11 + h11) (q13 + h13) (q33 + h33) =
          ((q33 + h33) * du - (q13 + h13) * dv) ^ 2 +
            ((q11 + h11) * (q33 + h33) - (q13 + h13) ^ 2) * dv ^ 2 by
        unfold oddCouplingD; ring]
      exact add_nonneg (sq_nonneg _)
        (mul_nonneg (by linarith) (sq_nonneg dv))
    exact nonneg_of_mul_nonneg_right hscaled (by linarith)
  have hEFpos : 0 ≤ oddCouplingFour u4 v4
      (q11 + h11) (q13 + h13) (q33 + h33) := by
    have hscaled : 0 ≤ (q33 + h33) *
        oddCouplingFour u4 v4 (q11 + h11) (q13 + h13) (q33 + h33) := by
      rw [show
        (q33 + h33) *
            oddCouplingFour u4 v4 (q11 + h11) (q13 + h13) (q33 + h33) =
          ((q33 + h33) * u4 - (q13 + h13) * v4) ^ 2 +
            ((q11 + h11) * (q33 + h33) - (q13 + h13) ^ 2) * v4 ^ 2 by
        unfold oddCouplingFour; ring]
      exact add_nonneg (sq_nonneg _)
        (mul_nonneg (by linarith) (sq_nonneg v4))
    exact nonneg_of_mul_nonneg_right hscaled (by linarith)
  have hduv4L : (1692 / 100000 : ℝ) * (-4 / 1000) ≤ du * v4 := by
    have hmag : du * (-v4) ≤ (1692 / 100000 : ℝ) * (4 / 1000) := by
      bound
    linarith
  have hu4dvL : (141 / 1000 : ℝ) * (555 / 10000) ≤ u4 * dv := by
    bound
  have hCrossArgL :
      (1692 / 100000 : ℝ) * (-4 / 1000) +
          (141 / 1000) * (555 / 10000) ≤ du * v4 + u4 * dv := by
    linarith
  have huTermU : (q33 + h33) * du * u4 ≤
      (216 / 1000 : ℝ) * (1692 / 100000) * (144 / 1000) := by
    bound
  have hmTermL :
      (189 / 1000 : ℝ) *
          ((1692 / 100000) * (-4 / 1000) +
            (141 / 1000) * (555 / 10000)) ≤
        (q13 + h13) * (du * v4 + u4 * dv) := by
    have h1 := mul_nonneg
      (by linarith : 0 ≤ (q13 + h13) - 189 / 1000)
      (by linarith : 0 ≤ du * v4 + u4 * dv)
    have h2 := mul_nonneg (by norm_num : (0 : ℝ) ≤ 189 / 1000)
      (by linarith : 0 ≤ du * v4 + u4 * dv -
        ((1692 / 100000) * (-4 / 1000) +
          (141 / 1000) * (555 / 10000)))
    nlinarith
  have hvTermU : (q11 + h11) * dv * v4 ≤
      -(1918 / 10000 : ℝ) * (555 / 10000) * (2 / 1000) := by
    have hmag : (1918 / 10000 : ℝ) * (555 / 10000) * (2 / 1000) ≤
        (q11 + h11) * dv * (-v4) := by bound
    linarith
  have hEXneg : oddCouplingCross du u4 dv v4
      (q11 + h11) (q13 + h13) (q33 + h33) ≤ 0 := by
    unfold oddCouplingCross
    norm_num at huTermU hmTermL hvTermU ⊢
    nlinarith only [huTermU, hmTermL, hvTermU]
  have hQuPos : 0 ≤
      (63 / 200 : ℝ) * du ^ 2 +
        2 * (42817 / 1000000) * du * u4 +
          (1342 / 100000) * u4 ^ 2 := by positivity
  have hQvPos : 0 ≤
      (63 / 200 : ℝ) * dv ^ 2 +
        2 * (42817 / 1000000) * dv * v4 +
          (1342 / 100000) * v4 ^ 2 := by
    have hfirst : (63 / 200 : ℝ) * (555 / 10000) ^ 2 ≤
        (63 / 200) * dv ^ 2 := by bound
    have hcross : 2 * (42817 / 1000000 : ℝ) * dv * v4 ≥
        2 * (42817 / 1000000) * (558 / 10000) * (-4 / 1000) := by
      have hmag : dv * (-v4) ≤ (558 / 10000 : ℝ) * (4 / 1000) := by
        bound
      calc
        2 * (42817 / 1000000 : ℝ) * dv * v4 =
            -(2 * (42817 / 1000000) * (dv * (-v4))) := by ring
        _ ≥ -(2 * (42817 / 1000000) * ((558 / 10000) * (4 / 1000))) :=
          neg_le_neg (mul_le_mul_of_nonneg_left hmag (by norm_num))
        _ = 2 * (42817 / 1000000) * (558 / 10000) * (-4 / 1000) := by ring
    nlinarith [sq_nonneg v4]
  have hQuvPos : 0 ≤
      (63 / 200 : ℝ) * du * dv +
        (42817 / 1000000) * (du * v4 + u4 * dv) +
          (1342 / 100000) * u4 * v4 := by
    have hfirst : (63 / 200 : ℝ) * (1687 / 100000) * (555 / 10000) ≤
        (63 / 200) * du * dv := by bound
    have hmiddle : (42817 / 1000000 : ℝ) *
        ((1692 / 100000) * (-4 / 1000) +
          (141 / 1000) * (555 / 10000)) ≤
        (42817 / 1000000) * (du * v4 + u4 * dv) := by linarith
    have hlast : (1342 / 100000 : ℝ) * u4 * v4 ≥
        (1342 / 100000) * (144 / 1000) * (-4 / 1000) := by
      have hmag : u4 * (-v4) ≤ (144 / 1000 : ℝ) * (4 / 1000) := by
        bound
      calc
        (1342 / 100000 : ℝ) * u4 * v4 =
            -((1342 / 100000) * (u4 * (-v4))) := by ring
        _ ≥ -((1342 / 100000) * ((144 / 1000) * (4 / 1000))) :=
          neg_le_neg (mul_le_mul_of_nonneg_left hmag (by norm_num))
        _ = (1342 / 100000) * (144 / 1000) * (-4 / 1000) := by ring
    norm_num at hfirst hmiddle hlast ⊢
    linarith only [hfirst, hmiddle, hlast]
  have hcore :
      oddCouplingCore F C D du u4 dv v4
          (q11 + h11) (q13 + h13) (q33 + h33) ≤
        oddCouplingCore (63 / 200) (1342 / 100000) (42817 / 1000000)
          (1687 / 100000) (144 / 1000) (558 / 10000) (-4 / 1000)
          (199 / 1000) (189 / 1000) (216 / 1000) := by
    calc
      oddCouplingCore F C D du u4 dv v4
          (q11 + h11) (q13 + h13) (q33 + h33) ≤
          oddCouplingCore (63 / 200) C D du u4 dv v4
            (q11 + h11) (q13 + h13) (q33 + h33) := by
              rw [← sub_nonneg]
              convert mul_nonneg (by linarith : 0 ≤ (63 / 200 : ℝ) - F)
                hEDpos using 1 <;> unfold oddCouplingCore <;> ring
      _ ≤ oddCouplingCore (63 / 200) (1342 / 100000) D du u4 dv v4
            (q11 + h11) (q13 + h13) (q33 + h33) := by
              rw [← sub_nonneg]
              convert mul_nonneg (by linarith : 0 ≤ (1342 / 100000 : ℝ) - C)
                hEFpos using 1 <;> unfold oddCouplingCore <;> ring
      _ ≤ oddCouplingCore (63 / 200) (1342 / 100000) (42817 / 1000000)
            du u4 dv v4 (q11 + h11) (q13 + h13) (q33 + h33) := by
              rw [← sub_nonneg]
              convert mul_nonneg_of_nonpos_of_nonpos
                  (by linarith : (2 : ℝ) * (42817 / 1000000 - D) ≤ 0)
                  hEXneg using 1 <;> unfold oddCouplingCore <;> ring
      _ ≤ oddCouplingCore (63 / 200) (1342 / 100000) (42817 / 1000000)
            du u4 dv v4 (q11 + h11) (q13 + h13) (216 / 1000) := by
              rw [← sub_nonneg]
              convert mul_nonneg
                  (by linarith : 0 ≤ (216 / 1000 : ℝ) - (q33 + h33))
                  hQuPos using 1 <;>
                unfold oddCouplingCore oddCouplingD oddCouplingCross
                  oddCouplingFour <;> ring
      _ ≤ oddCouplingCore (63 / 200) (1342 / 100000) (42817 / 1000000)
            du u4 dv v4 (q11 + h11) (189 / 1000) (216 / 1000) := by
              rw [← sub_nonneg]
              convert mul_nonneg
                  (by linarith : 0 ≤ 2 * ((q13 + h13) - 189 / 1000))
                  hQuvPos using 1 <;>
                unfold oddCouplingCore oddCouplingD oddCouplingCross
                  oddCouplingFour <;> ring
      _ ≤ oddCouplingCore (63 / 200) (1342 / 100000) (42817 / 1000000)
            du u4 dv v4 (199 / 1000) (189 / 1000) (216 / 1000) := by
              rw [← sub_nonneg]
              convert mul_nonneg
                  (by linarith : 0 ≤ (199 / 1000 : ℝ) - (q11 + h11))
                  hQvPos using 1 <;>
                unfold oddCouplingCore oddCouplingD oddCouplingCross
                  oddCouplingFour <;> ring
      _ ≤ oddCouplingCore (63 / 200) (1342 / 100000) (42817 / 1000000)
            (1687 / 100000) u4 dv v4
            (199 / 1000) (189 / 1000) (216 / 1000) := by
              rw [← sub_nonpos, oddCouplingCore_du_step]
              have hslope :
                  (63 / 200 : ℝ) *
                      ((216 / 1000) * (du + 1687 / 100000) -
                        2 * (189 / 1000) * dv) +
                    2 * (42817 / 1000000) *
                      ((216 / 1000) * u4 - (189 / 1000) * v4) ≤ 0 := by
                norm_num at ⊢
                linarith
              exact mul_nonpos_of_nonneg_of_nonpos (by linarith) hslope
      _ ≤ oddCouplingCore (63 / 200) (1342 / 100000) (42817 / 1000000)
            (1687 / 100000) (144 / 1000) dv v4
            (199 / 1000) (189 / 1000) (216 / 1000) := by
              rw [← sub_nonneg, oddCouplingCore_u4_step]
              have hslope : 0 ≤
                  2 * (42817 / 1000000 : ℝ) *
                      ((216 / 1000) * (1687 / 100000) -
                        (189 / 1000) * dv) +
                    (1342 / 100000) *
                      ((216 / 1000) * (u4 + 144 / 1000) -
                        2 * (189 / 1000) * v4) := by
                norm_num at ⊢
                linarith
              simpa [add_comm] using mul_nonneg (by linarith) hslope
      _ ≤ oddCouplingCore (63 / 200) (1342 / 100000) (42817 / 1000000)
            (1687 / 100000) (144 / 1000) (558 / 10000) v4
            (199 / 1000) (189 / 1000) (216 / 1000) := by
              rw [← sub_nonneg, oddCouplingCore_dv_step]
              have hslope : 0 ≤
                  (63 / 200 : ℝ) *
                      ((199 / 1000) * (dv + 558 / 10000) -
                        2 * (189 / 1000) * (1687 / 100000)) +
                    2 * (42817 / 1000000) *
                      ((199 / 1000) * v4 -
                        (189 / 1000) * (144 / 1000)) := by
                norm_num at ⊢
                linarith
              simpa [add_comm] using mul_nonneg (by linarith) hslope
      _ ≤ oddCouplingCore (63 / 200) (1342 / 100000) (42817 / 1000000)
            (1687 / 100000) (144 / 1000) (558 / 10000) (-4 / 1000)
            (199 / 1000) (189 / 1000) (216 / 1000) := by
              rw [← sub_nonpos, oddCouplingCore_v4_step]
              have hslope :
                  2 * (42817 / 1000000 : ℝ) *
                      ((199 / 1000) * (558 / 10000) -
                        (189 / 1000) * (1687 / 100000)) +
                    (1342 / 100000) *
                      ((199 / 1000) * (v4 + (-4 / 1000)) -
                        2 * (189 / 1000) * (144 / 1000)) ≤ 0 := by
                norm_num at ⊢
                linarith
              exact mul_nonpos_of_nonneg_of_nonpos (by linarith) hslope
  calc
    oddCouplingCore F C D du u4 dv v4
        (q11 + h11) (q13 + h13) (q33 + h33) / 2 ≤
        oddCouplingCore (63 / 200) (1342 / 100000) (42817 / 1000000)
          (1687 / 100000) (144 / 1000) (558 / 10000) (-4 / 1000)
          (199 / 1000) (189 / 1000) (216 / 1000) / 2 := by
            nlinarith only [hcore]
    _ ≤ (39 / 1000000 : ℝ) := by
      norm_num [oddCouplingCore, oddCouplingD, oddCouplingCross,
        oddCouplingFour]

set_option maxHeartbeats 500000 in
private theorem crossASlopeSquare_lower
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (77 / 5000000 : ℝ) ≤ (u4 * dv - v4 * du) ^ 2 / 4 := by
  rcases hbox.du_mem with ⟨hduL, hduU⟩
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  rcases hbox.v4_mem with ⟨hv4L, hv4U⟩
  have hCrossLinear : (785 / 100000 : ℝ) ≤ u4 * dv - v4 * du := by
    have hu4Nonneg : 0 ≤ u4 := by linarith
    have hdvNonneg : 0 ≤ dv := by linarith
    have hduNonneg : 0 ≤ du := by linarith
    have hv4NegNonneg : 0 ≤ -v4 := by linarith
    have hfirst : (141 / 1000 : ℝ) * (555 / 10000) ≤ u4 * dv := by
      bound
    have hsecond : (2 / 1000 : ℝ) * (1687 / 100000) ≤ (-v4) * du := by
      bound
    nlinarith only [hfirst, hsecond]
  have hCrossSquare : (77 / 5000000 : ℝ) ≤
      (u4 * dv - v4 * du) ^ 2 / 4 := by
    have hsum : 0 ≤ (785 / 100000 : ℝ) + (u4 * dv - v4 * du) := by
      linarith
    have hprod := mul_nonneg
      (by linarith : 0 ≤ (u4 * dv - v4 * du) - 785 / 100000) hsum
    nlinarith
  exact hCrossSquare

set_option maxHeartbeats 500000 in
private theorem correlated_A_secant_nonneg
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    0 ≤ quadraticSecant
      (fun z ↦ correlatedCoefficientTwo z X R C D F a x r c d f
        su du u4 sv dv v4 q11 q13 q33 h11 h13 h33)
      A (137423 / 100000) := by
  rw [correlated_A_secant_eq]
  unfold correlatedASlope alignedAdjugateASlope
    alignedMixedAdjugateBothASlope
  dsimp only
  rcases oddASlope_bounds
    A X R C D F a x r c d f
    su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox with
      ⟨hOddMinus, hOddMixed, hOddPlus⟩
  rcases evenASlopeDeterminant_bounds
    A X R C D F a x r c d f
    su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox with
      ⟨hDetMinus, hDetMixed, hDetPlus⟩
  have hPlusCoupling := plusASlopeCoupling_upper
    A X R C D F a x r c d f
    su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox
  have hMixedCoupling := mixedASlopeCoupling_upper
    A X R C D F a x r c d f
    su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox
  have hCrossSquare := crossASlopeSquare_lower
    A X R C D F a x r c d f
    su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox
  have hTermMinus :
      (112 / 1000000 : ℝ) * (26 / 1000) ≤
        (((F - f) * (C - c) - (D - d) ^ 2) / 4) *
          ((q11 - h11) * (q33 - h33) - (q13 - h13) ^ 2) := by
    have hprod := mul_nonneg
      (sub_nonneg.mpr hDetMinus)
      (by linarith : 0 ≤
        (q11 - h11) * (q33 - h33) - (q13 - h13) ^ 2 + 26 / 1000)
    nlinarith
  have hTermMixed :
      (91 / 100000 : ℝ) * (41 / 1000) ≤
        (((F + f) * (C - c) + (F - f) * (C + c) -
            2 * (D - d) * (D + d) +
            (F - f) * (C - c) - (D - d) ^ 2) / 4) *
          ((q11 + h11) * (q33 - h33) +
            (q11 - h11) * (q33 + h33) -
              2 * (q13 + h13) * (q13 - h13)) := by
    have hprod := mul_nonneg
      (sub_nonneg.mpr hDetMixed)
      (by linarith : 0 ≤
        (q11 + h11) * (q33 - h33) +
          (q11 - h11) * (q33 + h33) -
            2 * (q13 + h13) * (q13 - h13) + 41 / 1000)
    nlinarith
  have hTermPlus :
      (21 / 10000 : ℝ) * (4 / 1000) ≤
        (((F - f) * (C + c) + (F + f) * (C - c) -
            2 * (D - d) * (D + d) +
            (F + f) * (C + c) - (D + d) ^ 2) / 4) *
          ((q11 + h11) * (q33 + h33) - (q13 + h13) ^ 2) := by
    have hprod := mul_nonneg
      (sub_nonneg.mpr hDetPlus)
      (by linarith : 0 ≤
        (q11 + h11) * (q33 + h33) - (q13 + h13) ^ 2 + 4 / 1000)
    nlinarith
  nlinarith only [hTermMinus, hTermMixed, hTermPlus,
    hPlusCoupling, hMixedCoupling, hCrossSquare]

set_option maxHeartbeats 800000 in
private theorem correlated_A_lower_endpoint
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    correlatedCoefficientTwo
        (137423 / 100000) X R C D F a x r c d f
        su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 ≤
      correlatedCoefficientTwo A X R C D F a x r c d f
        su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 := by
  have hquadratic : IsQuadraticLaw
      (fun z ↦ correlatedCoefficientTwo z X R C D F a x r c d f
        su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) := by
    unfold IsQuadraticLaw correlatedCoefficientTwo alignedDeterminant
      alignedMixedDeterminant alignedAdjugatePair alignedMixedAdjugatePair
      alignedCrossEnergy alignedEntry00 alignedEntry02 alignedEntry04
      alignedEntry22 alignedEntry24 mixedDeterminantOne
    intro z
    dsimp only
    ring
  have hstep := quadraticSecant_exact
    (fun z ↦ correlatedCoefficientTwo z X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33)
    hquadratic A (137423 / 100000)
  have hsec := correlated_A_secant_nonneg
    A X R C D F a x r c d f
    su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox
  rw [← sub_nonneg]
  rw [hstep]
  exact mul_nonneg (sub_nonneg.mpr hbox.A_mem.1) hsec

/- The stronger uniform-tail version of the first face block is intentionally
kept out of the kernel proof: its raw expanded interval goal obscures the
coordinate structure.  The staged corner-tail theorem below is the statement
needed by the telescope. -/
/-
set_option maxHeartbeats 3000000 in
private theorem correlated_even_block_one_lower
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    correlatedCoefficientTwo
        (137423 / 100000) (3977 / 100000) (242898 / 1000000)
        (1323 / 100000) (42898 / 1000000) (1571 / 5000)
        (826465 / 1000000) x r c d f
        su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 ≤
      correlatedCoefficientTwo
        (137423 / 100000) X R C D F a x r c d f
        su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 := by
  rcases hbox with
    ⟨⟨hAL, hAU⟩, ⟨hXL, hXU⟩, ⟨hRL, hRU⟩, ⟨hCL, hCU⟩,
      ⟨hDL, hDU⟩, ⟨hFL, hFU⟩, ⟨haL, haU⟩, ⟨hxL, hxU⟩,
      ⟨hrL, hrU⟩, ⟨hcL, hcU⟩, ⟨hdL, hdU⟩, ⟨hfL, hfU⟩,
      ⟨hsuL, hsuU⟩, ⟨hduL, hduU⟩, ⟨hu4L, hu4U⟩,
      ⟨hsvL, hsvU⟩, ⟨hdvL, hdvU⟩, ⟨hv4L, hv4U⟩,
      ⟨hq11L, hq11U⟩, ⟨hq13L, hq13U⟩, ⟨hq33L, hq33U⟩,
      ⟨hh11L, hh11U⟩, ⟨hh13L, hh13U⟩, ⟨hh33L, hh33U⟩⟩
  calc
    correlatedCoefficientTwo
        (137423 / 100000) (3977 / 100000) (242898 / 1000000)
        (1323 / 100000) (42898 / 1000000) (1571 / 5000)
        (826465 / 1000000) x r c d f
        su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 ≤
      correlatedCoefficientTwo
        (137423 / 100000) (3977 / 100000) (242898 / 1000000)
        (1323 / 100000) (42898 / 1000000) (1571 / 5000)
        a x r c d f su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 := by
      refine quadratic_lower_at_right
        (fun z ↦ correlatedCoefficientTwo
          (137423 / 100000) (3977 / 100000) (242898 / 1000000)
          (1323 / 100000) (42898 / 1000000) (1571 / 5000)
          z x r c d f su du u4 sv dv v4 q11 q13 q33 h11 h13 h33)
        ?_ a (826465 / 1000000) haU ?_
      · unfold IsQuadraticLaw correlatedCoefficientTwo alignedDeterminant
          alignedMixedDeterminant alignedAdjugatePair alignedMixedAdjugatePair
          alignedCrossEnergy alignedEntry00 alignedEntry02 alignedEntry04
          alignedEntry22 alignedEntry24 mixedDeterminantOne
        intro z
        dsimp only
        ring
      · unfold quadraticSecant correlatedCoefficientTwo alignedDeterminant
          alignedMixedDeterminant alignedAdjugatePair alignedMixedAdjugatePair
          alignedCrossEnergy alignedEntry00 alignedEntry02 alignedEntry04
          alignedEntry22 alignedEntry24 mixedDeterminantOne
        dsimp only
        ring_nf
        nlinarith only [haU]
-/

private def evenBlockOneFace (X R C D F a u4 : ℝ) : ℝ :=
  correlatedCoefficientTwo
    (137423 / 100000) X R C D F a
    (37851 / 1000000) (49817 / 1000000) (7165 / 1000000)
    (23317 / 1000000) (4416 / 25000)
    (56173 / 100000) (1687 / 100000) u4
    (53815 / 100000) (558 / 10000) (-2 / 1000)
    (1778 / 10000) (2002 / 10000) (3315 / 10000)
    (14 / 1000) (-9 / 1000) (-120 / 1000)

private theorem terminal_corner_pos :
    (1 / 1000000 : ℝ) <
      evenBlockOneFace
        (3977 / 100000) (242898 / 1000000) (1323 / 100000)
        (42898 / 1000000) (1571 / 5000) (826465 / 1000000)
        (141 / 1000) := by
  unfold evenBlockOneFace correlatedCoefficientTwo alignedDeterminant
    alignedMixedDeterminant alignedAdjugatePair alignedMixedAdjugatePair
    alignedCrossEnergy alignedEntry00 alignedEntry02 alignedEntry04
    alignedEntry22 alignedEntry24 mixedDeterminantOne
  norm_num

private theorem u4_corner_lower
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    evenBlockOneFace
        (3977 / 100000) (242898 / 1000000) (1323 / 100000)
        (42898 / 1000000) (1571 / 5000) (826465 / 1000000)
        (141 / 1000) ≤
      evenBlockOneFace
        (3977 / 100000) (242898 / 1000000) (1323 / 100000)
        (42898 / 1000000) (1571 / 5000) (826465 / 1000000) u4 := by
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  have hstep :
      evenBlockOneFace
          (3977 / 100000) (242898 / 1000000) (1323 / 100000)
          (42898 / 1000000) (1571 / 5000) (826465 / 1000000) u4 -
        evenBlockOneFace
          (3977 / 100000) (242898 / 1000000) (1323 / 100000)
          (42898 / 1000000) (1571 / 5000) (826465 / 1000000)
          (141 / 1000) =
        (u4 - 141 / 1000) *
          (2360651172075389 / 16000000000000000000 -
            6548589077183 * u4 / 8000000000000000) := by
    unfold evenBlockOneFace correlatedCoefficientTwo alignedDeterminant
      alignedMixedDeterminant alignedAdjugatePair alignedMixedAdjugatePair
      alignedCrossEnergy alignedEntry00 alignedEntry02 alignedEntry04
      alignedEntry22 alignedEntry24 mixedDeterminantOne
    ring
  have hslope : (29 / 1000000 : ℝ) <
      2360651172075389 / 16000000000000000000 -
        6548589077183 * u4 / 8000000000000000 := by
    nlinarith only [hu4U]
  have hslope0 : (0 : ℝ) ≤
      2360651172075389 / 16000000000000000000 -
        6548589077183 * u4 / 8000000000000000 := by
    nlinarith only [hslope]
  rw [← sub_nonneg, hstep]
  exact mul_nonneg (sub_nonneg.mpr hu4L) hslope0

set_option maxHeartbeats 3000000 in
private theorem evenBlockOneFace_lower
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    evenBlockOneFace
        (3977 / 100000) (242898 / 1000000) (1323 / 100000)
        (42898 / 1000000) (1571 / 5000) (826465 / 1000000) u4 ≤
      evenBlockOneFace X R C D F a u4 := by
  rcases hbox.X_mem with ⟨hXL, hXU⟩
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.C_mem with ⟨hCL, hCU⟩
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.F_mem with ⟨hFL, hFU⟩
  rcases hbox.a_mem with ⟨haL, haU⟩
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  calc
    evenBlockOneFace
        (3977 / 100000) (242898 / 1000000) (1323 / 100000)
        (42898 / 1000000) (1571 / 5000) (826465 / 1000000) u4 ≤
      evenBlockOneFace
        (3977 / 100000) (242898 / 1000000) (1323 / 100000)
        (42898 / 1000000) (1571 / 5000) a u4 := by
      refine quadratic_lower_at_right
        (fun z ↦ evenBlockOneFace
          (3977 / 100000) (242898 / 1000000) (1323 / 100000)
          (42898 / 1000000) (1571 / 5000) z u4)
        ?_ a (826465 / 1000000) haU ?_
      · unfold IsQuadraticLaw evenBlockOneFace correlatedCoefficientTwo
          alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
          alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
          alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
          mixedDeterminantOne
        intro z
        dsimp only
        ring
      · unfold quadraticSecant evenBlockOneFace correlatedCoefficientTwo
          alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
          alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
          alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
          mixedDeterminantOne
        dsimp only
        ring_nf
        have hu4sqU : u4 ^ 2 ≤ (144 / 1000 : ℝ) ^ 2 := by
          bound
        nlinarith only [hu4L, hu4sqU]
    _ ≤ evenBlockOneFace
        (3977 / 100000) (242898 / 1000000) (1323 / 100000)
        (42898 / 1000000) F a u4 := by
      refine quadratic_lower_at_left
        (fun z ↦ evenBlockOneFace
          (3977 / 100000) (242898 / 1000000) (1323 / 100000)
          (42898 / 1000000) z a u4)
        ?_ F (1571 / 5000) hFL ?_
      · unfold IsQuadraticLaw evenBlockOneFace correlatedCoefficientTwo
          alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
          alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
          alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
          mixedDeterminantOne
        intro z
        dsimp only
        ring
      · unfold quadraticSecant evenBlockOneFace correlatedCoefficientTwo
          alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
          alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
          alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
          mixedDeterminantOne
        dsimp only
        ring_nf
        nlinarith only [haU]
    _ ≤ evenBlockOneFace
        (3977 / 100000) (242898 / 1000000) (1323 / 100000)
        D F a u4 := by
      refine quadratic_lower_at_right
        (fun z ↦ evenBlockOneFace
          (3977 / 100000) (242898 / 1000000) (1323 / 100000) z F a u4)
        ?_ D (42898 / 1000000) hDU ?_
      · unfold IsQuadraticLaw evenBlockOneFace correlatedCoefficientTwo
          alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
          alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
          alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
          mixedDeterminantOne
        intro z
        dsimp only
        ring
      · unfold quadraticSecant evenBlockOneFace correlatedCoefficientTwo
          alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
          alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
          alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
          mixedDeterminantOne
        dsimp only
        ring_nf
        have haD : a * D ≤
            (826465 / 1000000 : ℝ) * (42898 / 1000000) := by
          bound
        have hau4L :
            (824479 / 1000000 : ℝ) * (141 / 1000) ≤ a * u4 := by
          bound
        nlinarith only [haU, hDL, hu4U, haD, hau4L]
    _ ≤ evenBlockOneFace
        (3977 / 100000) (242898 / 1000000) C D F a u4 := by
      refine quadratic_lower_at_left
        (fun z ↦ evenBlockOneFace
          (3977 / 100000) (242898 / 1000000) z D F a u4)
        ?_ C (1323 / 100000) hCL ?_
      · unfold IsQuadraticLaw evenBlockOneFace correlatedCoefficientTwo
          alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
          alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
          alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
          mixedDeterminantOne
        intro z
        dsimp only
        ring
      · unfold quadraticSecant evenBlockOneFace correlatedCoefficientTwo
          alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
          alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
          alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
          mixedDeterminantOne
        dsimp only
        ring_nf
        have hFa : F * a ≤ (63 / 200 : ℝ) * (826465 / 1000000) := by
          bound
        have hu4sqU : u4 ^ 2 ≤ (144 / 1000 : ℝ) ^ 2 := by
          bound
        have hau4L :
            (824479 / 1000000 : ℝ) * (141 / 1000) ≤ a * u4 := by
          bound
        have hau4sqL :
            (824479 / 1000000 : ℝ) * (141 / 1000) ^ 2 ≤ a * u4 ^ 2 := by
          bound
        nlinarith only [hFL, haU, hu4L, hFa, hu4sqU, hau4L, hau4sqL]
    _ ≤ evenBlockOneFace (3977 / 100000) R C D F a u4 := by
      refine quadratic_lower_at_right
        (fun z ↦ evenBlockOneFace (3977 / 100000) z C D F a u4)
        ?_ R (242898 / 1000000) hRU ?_
      · unfold IsQuadraticLaw evenBlockOneFace correlatedCoefficientTwo
          alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
          alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
          alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
          mixedDeterminantOne
        intro z
        dsimp only
        ring
      · unfold quadraticSecant evenBlockOneFace correlatedCoefficientTwo
          alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
          alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
          alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
          mixedDeterminantOne
        dsimp only
        ring_nf
        have hCR : (1323 / 100000 : ℝ) * (242817 / 1000000) ≤ C * R := by
          bound
        have hCu4U : C * u4 ≤
            (1342 / 100000 : ℝ) * (144 / 1000) := by
          bound
        nlinarith only [hCL, hDL, hRU, hu4L, hCR, hCu4U]
    _ ≤ evenBlockOneFace X R C D F a u4 := by
      refine quadratic_lower_at_right
        (fun z ↦ evenBlockOneFace z R C D F a u4)
        ?_ X (3977 / 100000) hXU ?_
      · unfold IsQuadraticLaw evenBlockOneFace correlatedCoefficientTwo
          alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
          alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
          alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
          mixedDeterminantOne
        intro z
        dsimp only
        ring
      · unfold quadraticSecant evenBlockOneFace correlatedCoefficientTwo
          alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
          alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
          alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
          mixedDeterminantOne
        dsimp only
        ring_nf
        have hFX : (1571 / 5000 : ℝ) * (3962 / 100000) ≤ F * X := by
          bound
        have hDR : (42817 / 1000000 : ℝ) * (242817 / 1000000) ≤ D * R := by
          bound
        have hDu4U : D * u4 ≤
            (42898 / 1000000 : ℝ) * (144 / 1000) := by
          bound
        have hRu4U : R * u4 ≤
            (242898 / 1000000 : ℝ) * (144 / 1000) := by
          bound
        have hu4XU : u4 * X ≤
            (144 / 1000 : ℝ) * (3977 / 100000) := by
          bound
        have hu4sqL : (141 / 1000 : ℝ) ^ 2 ≤ u4 ^ 2 := by
          bound
        have hu4sqXU : u4 ^ 2 * X ≤
            (144 / 1000 : ℝ) ^ 2 * (3977 / 100000) := by
          bound
        nlinarith only [hFU, hDU, hRU, hXU, hu4L, hFX, hDR,
          hDu4U, hRu4U, hu4XU, hu4sqL, hu4sqXU]

private def evenBlockTwoFace
    (X R C D F a x r c d f u4 : ℝ) : ℝ :=
  correlatedCoefficientTwo
    (137423 / 100000) X R C D F a x r c d f
    (56173 / 100000) (1687 / 100000) u4
    (53815 / 100000) (558 / 10000) (-2 / 1000)
    (1778 / 10000) (2002 / 10000) (3315 / 10000)
    (14 / 1000) (-9 / 1000) (-120 / 1000)

set_option maxHeartbeats 3000000 in
private theorem evenBlockTwoFace_lower
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    evenBlockTwoFace X R C D F a
        (37851 / 1000000) (49817 / 1000000) (7165 / 1000000)
        (23317 / 1000000) (4416 / 25000) u4 ≤
      evenBlockTwoFace X R C D F a x r c d f u4 := by
  rcases hbox.X_mem with ⟨hXL, hXU⟩
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.C_mem with ⟨hCL, hCU⟩
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.F_mem with ⟨hFL, hFU⟩
  rcases hbox.a_mem with ⟨haL, haU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  calc
    evenBlockTwoFace X R C D F a
        (37851 / 1000000) (49817 / 1000000) (7165 / 1000000)
        (23317 / 1000000) (4416 / 25000) u4 ≤
      evenBlockTwoFace X R C D F a
        (37851 / 1000000) (49817 / 1000000) (7165 / 1000000)
        (23317 / 1000000) f u4 := by
      refine quadratic_lower_at_right
        (fun z ↦ evenBlockTwoFace X R C D F a
          (37851 / 1000000) (49817 / 1000000) (7165 / 1000000)
          (23317 / 1000000) z u4)
        ?_ f (4416 / 25000) hfU ?_
      · unfold IsQuadraticLaw evenBlockTwoFace correlatedCoefficientTwo
          alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
          alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
          alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
          mixedDeterminantOne
        intro z
        dsimp only
        ring
      · unfold quadraticSecant evenBlockTwoFace correlatedCoefficientTwo
          alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
          alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
          alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
          mixedDeterminantOne
        dsimp only
        ring_nf
        nlinarith only [hXL, hXU, hRL, hRU, hCL, hCU, hDL, hDU,
          hFL, hFU, haL, haU]
    _ ≤ evenBlockTwoFace X R C D F a
        (37851 / 1000000) (49817 / 1000000) (7165 / 1000000) d f u4 := by
      refine quadratic_lower_at_left
        (fun z ↦ evenBlockTwoFace X R C D F a
          (37851 / 1000000) (49817 / 1000000) (7165 / 1000000) z f u4)
        ?_ d (23317 / 1000000) hdL ?_
      · unfold IsQuadraticLaw evenBlockTwoFace correlatedCoefficientTwo
          alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
          alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
          alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
          mixedDeterminantOne
        intro z
        dsimp only
        ring
      · unfold quadraticSecant evenBlockTwoFace correlatedCoefficientTwo
          alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
          alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
          alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
          mixedDeterminantOne
        dsimp only
        ring_nf
        have haD : (824479 / 1000000 : ℝ) * (42817 / 1000000) ≤ a * D := by
          bound
        have had : a * d ≤
            (826465 / 1000000 : ℝ) * (27183 / 1000000) := by
          bound
        have hXR : (3962 / 100000 : ℝ) * (242817 / 1000000) ≤ X * R := by
          bound
        have hau4U : a * u4 ≤
            (826465 / 1000000 : ℝ) * (144 / 1000) := by
          bound
        have hXu4U : X * u4 ≤
            (3977 / 100000 : ℝ) * (144 / 1000) := by
          bound
        nlinarith only [haU, hXL, hDL, hRU, hdL, hu4L,
          haD, had, hXR, hau4U, hXu4U]
    _ ≤ evenBlockTwoFace X R C D F a
        (37851 / 1000000) (49817 / 1000000) c d f u4 := by
      refine quadratic_lower_at_right
        (fun z ↦ evenBlockTwoFace X R C D F a
          (37851 / 1000000) (49817 / 1000000) z d f u4)
        ?_ c (7165 / 1000000) hcU ?_
      · unfold IsQuadraticLaw evenBlockTwoFace correlatedCoefficientTwo
          alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
          alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
          alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
          mixedDeterminantOne
        intro z
        dsimp only
        ring
      · unfold quadraticSecant evenBlockTwoFace correlatedCoefficientTwo
          alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
          alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
          alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
          mixedDeterminantOne
        dsimp only
        ring_nf
        have hFaL :
            (1571 / 5000 : ℝ) * (824479 / 1000000) ≤ F * a := by
          bound
        have hfaU : f * a ≤
            (4416 / 25000 : ℝ) * (826465 / 1000000) := by
          bound
        have hau4U : a * u4 ≤
            (826465 / 1000000 : ℝ) * (144 / 1000) := by
          bound
        have hu4sqU : u4 ^ 2 ≤ (144 / 1000 : ℝ) ^ 2 := by
          bound
        have hau4sqL :
            (824479 / 1000000 : ℝ) * (141 / 1000) ^ 2 ≤ a * u4 ^ 2 := by
          bound
        have hRu4L :
            (242817 / 1000000 : ℝ) * (141 / 1000) ≤ R * u4 := by
          bound
        have hRsqU : R ^ 2 ≤ (242898 / 1000000 : ℝ) ^ 2 := by
          bound
        nlinarith only [hFL, hfL, haU, hRU, hu4U, hFaL, hfaU,
          hau4U, hu4sqU, hau4sqL, hRu4L, hRsqU]
    _ ≤ evenBlockTwoFace X R C D F a
        (37851 / 1000000) r c d f u4 := by
      refine quadratic_lower_at_left
        (fun z ↦ evenBlockTwoFace X R C D F a
          (37851 / 1000000) z c d f u4)
        ?_ r (49817 / 1000000) hrL ?_
      · unfold IsQuadraticLaw evenBlockTwoFace correlatedCoefficientTwo
          alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
          alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
          alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
          mixedDeterminantOne
        intro z
        dsimp only
        ring
      · unfold quadraticSecant evenBlockTwoFace correlatedCoefficientTwo
          alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
          alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
          alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
          mixedDeterminantOne
        dsimp only
        ring_nf
        have hCR : (1323 / 100000 : ℝ) * (242817 / 1000000) ≤ C * R := by
          bound
        have hCr : (1323 / 100000 : ℝ) * (49817 / 1000000) ≤ C * r := by
          bound
        have hcR : (5179 / 1000000 : ℝ) * (242817 / 1000000) ≤ c * R := by
          bound
        have hcr : c * r ≤
            (7165 / 1000000 : ℝ) * (57183 / 1000000) := by
          bound
        have hXD : (3962 / 100000 : ℝ) * (42817 / 1000000) ≤ X * D := by
          bound
        have hXd : (3962 / 100000 : ℝ) * (23317 / 1000000) ≤ X * d := by
          bound
        have hCu4U : C * u4 ≤
            (1342 / 100000 : ℝ) * (144 / 1000) := by
          bound
        have hcu4L :
            (5179 / 1000000 : ℝ) * (141 / 1000) ≤ c * u4 := by
          bound
        have hXu4U : X * u4 ≤
            (3977 / 100000 : ℝ) * (144 / 1000) := by
          bound
        nlinarith only [hCL, hXU, hRU, hDU, hcU, hdU, hrU, hu4L,
          hCR, hCr, hcR, hcr, hXD, hXd, hCu4U, hcu4L, hXu4U]
    _ ≤ evenBlockTwoFace X R C D F a x r c d f u4 := by
      refine quadratic_lower_at_left
        (fun z ↦ evenBlockTwoFace X R C D F a z r c d f u4)
        ?_ x (37851 / 1000000) hxL ?_
      · unfold IsQuadraticLaw evenBlockTwoFace correlatedCoefficientTwo
          alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
          alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
          alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
          mixedDeterminantOne
        intro z
        dsimp only
        ring
      · unfold quadraticSecant evenBlockTwoFace correlatedCoefficientTwo
          alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
          alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
          alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
          mixedDeterminantOne
        dsimp only
        ring_nf
        have hFX : (1571 / 5000 : ℝ) * (3962 / 100000) ≤ F * X := by
          bound
        have hFx : (1571 / 5000 : ℝ) * (37851 / 1000000) ≤ F * x := by
          bound
        have hfX : (4411 / 25000 : ℝ) * (3962 / 100000) ≤ f * X := by
          bound
        have hfx : f * x ≤
            (4416 / 25000 : ℝ) * (39761 / 1000000) := by
          bound
        have hDR : (42817 / 1000000 : ℝ) * (242817 / 1000000) ≤ D * R := by
          bound
        have hDr : (42817 / 1000000 : ℝ) * (49817 / 1000000) ≤ D * r := by
          bound
        have hdR : (23317 / 1000000 : ℝ) * (242817 / 1000000) ≤ d * R := by
          bound
        have hdr : d * r ≤
            (27183 / 1000000 : ℝ) * (57183 / 1000000) := by
          bound
        have hXu4U : X * u4 ≤
            (3977 / 100000 : ℝ) * (144 / 1000) := by
          bound
        have hXu4sqU : X * u4 ^ 2 ≤
            (3977 / 100000 : ℝ) * (144 / 1000) ^ 2 := by
          bound
        have hDu4U : D * u4 ≤
            (42898 / 1000000 : ℝ) * (144 / 1000) := by
          bound
        have hdu4L :
            (23317 / 1000000 : ℝ) * (141 / 1000) ≤ d * u4 := by
          bound
        have hRu4U : R * u4 ≤
            (242898 / 1000000 : ℝ) * (144 / 1000) := by
          bound
        have hru4U : r * u4 ≤
            (57183 / 1000000 : ℝ) * (144 / 1000) := by
          bound
        have hu4xU : u4 * x ≤
            (144 / 1000 : ℝ) * (39761 / 1000000) := by
          bound
        have hu4sqL : (141 / 1000 : ℝ) ^ 2 ≤ u4 ^ 2 := by
          bound
        have hu4sqxL :
            (141 / 1000 : ℝ) ^ 2 * (37851 / 1000000) ≤ u4 ^ 2 * x := by
          bound
        nlinarith only [hXU, hRU, hDU, hFU, hdL, hrU, hxU, hfU, hu4L,
          hFX, hFx, hfX, hfx, hDR, hDr, hdR, hdr, hXu4U, hXu4sqU,
          hDu4U, hdu4L, hRu4U, hru4U, hu4xU, hu4sqL, hu4sqxL]

/-! The alternating-coordinate secants are kept in cofactor-row form.  This
is the structural scale of the problem: expanding these six correlated row
products destroys the cancellation between the plus and mixed adjugates. -/

private def adjugateRowS
    (A X R C D F ws wd w4 : ℝ) : ℝ :=
  ((F * C - D ^ 2) * ws - (F * X + R * D) * wd -
      (C * R + X * D) * w4) / 4

private def adjugateRowD
    (A X R C D F ws wd w4 : ℝ) : ℝ :=
  (-(F * X + R * D) * ws + (F * A - R ^ 2) * wd +
      (X * R + A * D) * w4) / 4

private def adjugateRowFour
    (A X R C D F ws wd w4 : ℝ) : ℝ :=
  (-(C * R + X * D) * ws + (X * R + A * D) * wd +
      (A * C - X ^ 2) * w4) / 4

private def mixedAdjugateRowS
    (A X R C D F a x r c d f ws wd w4 : ℝ) : ℝ :=
  ((F * c + f * C - 2 * D * d) * ws -
      (F * x + f * X + R * d + r * D) * wd -
      (C * r + c * R + X * d + x * D) * w4) / 4

private def mixedAdjugateRowD
    (A X R C D F a x r c d f ws wd w4 : ℝ) : ℝ :=
  (-(F * x + f * X + R * d + r * D) * ws +
      (F * a + f * A - 2 * R * r) * wd +
      (X * r + x * R + A * d + a * D) * w4) / 4

private def mixedAdjugateRowFour
    (A X R C D F a x r c d f ws wd w4 : ℝ) : ℝ :=
  (-(C * r + c * R + X * d + x * D) * ws +
      (X * r + x * R + A * d + a * D) * wd +
      (A * c + a * C - 2 * X * x) * w4) / 4

private def crossGradientS (A X R zs zd zc : ℝ) : ℝ :=
  (A * zs + X * zd + 2 * R * zc) / 2

private def crossGradientD (X C D zs zd zc : ℝ) : ℝ :=
  (X * zs + C * zd - 2 * D * zc) / 2

private def crossGradientFour (R D F zs zd zc : ℝ) : ℝ :=
  R * zs - D * zd + 2 * F * zc

private def alternatingFace
    (X R C D F a x r c d f su du u4 sv dv v4 : ℝ) : ℝ :=
  correlatedCoefficientTwo
    (137423 / 100000) X R C D F a x r c d f su du u4 sv dv v4
    (1778 / 10000) (2002 / 10000) (3315 / 10000)
    (14 / 1000) (-9 / 1000) (-120 / 1000)

private def alternatingSuCoupling
    (X R C D F a x r c d f su su0 du u4 sv dv v4 : ℝ) : ℝ :=
  let A := (137423 / 100000 : ℝ)
  let Ap := A - a
  let Xp := X - x
  let Rp := R - r
  let Cp := C - c
  let Dp := D - d
  let Fp := F - f
  let Am := A + a
  let Xm := X + x
  let Rm := R + r
  let Cm := C + c
  let Dm := D + d
  let Fm := F + f
  let o13m := (2002 / 10000 : ℝ) - (-9 / 1000)
  let o33m := (3315 / 10000 : ℝ) - (-120 / 1000)
  let o13p := (2002 / 10000 : ℝ) + (-9 / 1000)
  let o33p := (3315 / 10000 : ℝ) + (-120 / 1000)
  let sm := (su + su0) / 2
  let wmS := o33m * sm - o13m * sv
  let wmD := o33m * du - o13m * dv
  let wm4 := o33m * u4 - o13m * v4
  let wpS := o33p * sm - o13p * sv
  let wpD := o33p * du - o13p * dv
  let wp4 := o33p * u4 - o13p * v4
  adjugateRowS Ap Xp Rp Cp Dp Fp wmS wmD wm4 +
    mixedAdjugateRowS Ap Xp Rp Cp Dp Fp
      Am Xm Rm Cm Dm Fm wpS wpD wp4

private def alternatingSuCross
    (X R C D F a x r c d f su su0 du u4 sv dv v4 : ℝ) : ℝ :=
  let Xp := X - x
  let Rp := R - r
  let Cp := C - c
  let Dp := D - d
  let Fp := F - f
  let sm := (su + su0) / 2
  let zs := u4 * dv - v4 * du
  let zd := v4 * sm - u4 * sv
  let zc := (du * sv - sm * dv) / 2
  v4 * crossGradientD Xp Cp Dp zs zd zc -
    (dv / 2) * crossGradientFour Rp Dp Fp zs zd zc

private def alternatingSuSlope
    (X R C D F a x r c d f su su0 du u4 sv dv v4 : ℝ) : ℝ :=
  -2 * alternatingSuCoupling X R C D F a x r c d f
      su su0 du u4 sv dv v4 +
    alternatingSuCross X R C D F a x r c d f
      su su0 du u4 sv dv v4

private theorem alternating_su_secant_eq
    (X R C D F a x r c d f su su0 du u4 sv dv v4 : ℝ) :
    quadraticSecant
        (fun z ↦ alternatingFace X R C D F a x r c d f
          z du u4 sv dv v4) su su0 =
      alternatingSuSlope X R C D F a x r c d f
        su su0 du u4 sv dv v4 := by
  unfold quadraticSecant alternatingFace alternatingSuSlope
    alternatingSuCoupling alternatingSuCross
    correlatedCoefficientTwo adjugateRowS mixedAdjugateRowS
    crossGradientD crossGradientFour alignedDeterminant
    alignedMixedDeterminant alignedAdjugatePair alignedMixedAdjugatePair
    alignedCrossEnergy alignedEntry00 alignedEntry02 alignedEntry04
    alignedEntry22 alignedEntry24 mixedDeterminantOne
  dsimp only
  ring

private def alternatingDuCoupling
    (X R C D F a x r c d f su du du0 u4 sv dv v4 : ℝ) : ℝ :=
  let A := (137423 / 100000 : ℝ)
  let Ap := A - a
  let Xp := X - x
  let Rp := R - r
  let Cp := C - c
  let Dp := D - d
  let Fp := F - f
  let Am := A + a
  let Xm := X + x
  let Rm := R + r
  let Cm := C + c
  let Dm := D + d
  let Fm := F + f
  let dbar := (du + du0) / 2
  let wmS := (903 / 2000) * su - (523 / 2500) * sv
  let wmD := (903 / 2000) * dbar - (523 / 2500) * dv
  let wm4 := (903 / 2000) * u4 - (523 / 2500) * v4
  let wpS := (2115 / 10000) * su - (1912 / 10000) * sv
  let wpD := (2115 / 10000) * dbar - (1912 / 10000) * dv
  let wp4 := (2115 / 10000) * u4 - (1912 / 10000) * v4
  (-2 : ℝ) *
    (adjugateRowD Ap Xp Rp Cp Dp Fp wmS wmD wm4 +
      mixedAdjugateRowD Ap Xp Rp Cp Dp Fp
        Am Xm Rm Cm Dm Fm wpS wpD wp4)

private def alternatingDuCross
    (X R C D F a x r c d f su du du0 u4 sv dv v4 : ℝ) : ℝ :=
  let A := (137423 / 100000 : ℝ)
  let Ap := A - a
  let Xp := X - x
  let Rp := R - r
  let Dp := D - d
  let Fp := F - f
  let dbar := (du + du0) / 2
  let zs := u4 * dv - v4 * dbar
  let zd := v4 * su - u4 * sv
  let zc := (dbar * sv - su * dv) / 2
  (-v4) * crossGradientS Ap Xp Rp zs zd zc +
    (sv / 2) * crossGradientFour Rp Dp Fp zs zd zc

private theorem alternating_du_secant_eq
    (X R C D F a x r c d f su du du0 u4 sv dv v4 : ℝ) :
    quadraticSecant
        (fun z ↦ alternatingFace X R C D F a x r c d f
          su z u4 sv dv v4) du du0 =
      alternatingDuCoupling X R C D F a x r c d f
          su du du0 u4 sv dv v4 +
        alternatingDuCross X R C D F a x r c d f
          su du du0 u4 sv dv v4 := by
  unfold quadraticSecant alternatingFace alternatingDuCoupling
    alternatingDuCross correlatedCoefficientTwo adjugateRowD
    mixedAdjugateRowD crossGradientS crossGradientFour alignedDeterminant
    alignedMixedDeterminant alignedAdjugatePair alignedMixedAdjugatePair
    alignedCrossEnergy alignedEntry00 alignedEntry02 alignedEntry04
    alignedEntry22 alignedEntry24 mixedDeterminantOne
  dsimp only
  ring

private def alternatingSvCoupling
    (X R C D F a x r c d f su du u4 sv sv0 dv v4 : ℝ) : ℝ :=
  let A := (137423 / 100000 : ℝ)
  let Ap := A - a
  let Xp := X - x
  let Rp := R - r
  let Cp := C - c
  let Dp := D - d
  let Fp := F - f
  let Am := A + a
  let Xm := X + x
  let Rm := R + r
  let Cm := C + c
  let Dm := D + d
  let Fm := F + f
  let svbar := (sv + sv0) / 2
  let wmS := (523 / 2500) * su - (819 / 5000) * svbar
  let wmD := (523 / 2500) * du - (819 / 5000) * dv
  let wm4 := (523 / 2500) * u4 - (819 / 5000) * v4
  let wpS := (239 / 1250) * su - (959 / 5000) * svbar
  let wpD := (239 / 1250) * du - (959 / 5000) * dv
  let wp4 := (239 / 1250) * u4 - (959 / 5000) * v4
  2 * (adjugateRowS Ap Xp Rp Cp Dp Fp wmS wmD wm4 +
    mixedAdjugateRowS Ap Xp Rp Cp Dp Fp
      Am Xm Rm Cm Dm Fm wpS wpD wp4)

private def alternatingSvCross
    (X R C D F a x r c d f su du u4 sv sv0 dv v4 : ℝ) : ℝ :=
  let Xp := X - x
  let Rp := R - r
  let Cp := C - c
  let Dp := D - d
  let Fp := F - f
  let svbar := (sv + sv0) / 2
  let zs := u4 * dv - v4 * du
  let zd := v4 * su - u4 * svbar
  let zc := (du * svbar - su * dv) / 2
  (-u4) * crossGradientD Xp Cp Dp zs zd zc +
    (du / 2) * crossGradientFour Rp Dp Fp zs zd zc

private theorem alternating_sv_secant_eq
    (X R C D F a x r c d f su du u4 sv sv0 dv v4 : ℝ) :
    quadraticSecant
        (fun z ↦ alternatingFace X R C D F a x r c d f
          su du u4 z dv v4) sv sv0 =
      alternatingSvCoupling X R C D F a x r c d f
          su du u4 sv sv0 dv v4 +
        alternatingSvCross X R C D F a x r c d f
          su du u4 sv sv0 dv v4 := by
  unfold quadraticSecant alternatingFace alternatingSvCoupling
    alternatingSvCross correlatedCoefficientTwo adjugateRowS
    mixedAdjugateRowS crossGradientD crossGradientFour alignedDeterminant
    alignedMixedDeterminant alignedAdjugatePair alignedMixedAdjugatePair
    alignedCrossEnergy alignedEntry00 alignedEntry02 alignedEntry04
    alignedEntry22 alignedEntry24 mixedDeterminantOne
  dsimp only
  ring

private def svCouplingSlopeX (D F d f du u4 : ℝ) : ℝ :=
  (-14790000 * D * u4 - 27370 * D - 14790000 * F * du +
    763623 * F + 5230000 * d * u4 + 8190 * d +
    5230000 * du * f - 228501 * f) / 50000000

private def svCouplingSlopeR (C D c d du u4 : ℝ) : ℝ :=
  (-14790000 * C * u4 - 27370 * C - 14790000 * D * du +
    763623 * D + 5230000 * c * u4 + 8190 * c +
    5230000 * d * du - 228501 * d) / 50000000

private def svCouplingSlopeC (F f r su sv u4 : ℝ) : ℝ :=
  (739500000000 * F * su - 342125000000 * F * sv -
    184114568750 * F - 261500000000 * f * su +
    102375000000 * f * sv + 55093106250 * f +
    261500000000 * r * u4 + 409500000 * r -
    179623071000 * u4 - 332405913) / 2500000000000

private def svCouplingSlopeDBig (su sv : ℝ) : ℝ :=
  -118320000000000 * su + 54740000000000 * sv + 29458331000000

private def svCouplingSlopedBig (su sv : ℝ) : ℝ :=
  83680000000000 * su - 32760000000000 * sv - 17629794000000

private def svCouplingSlopeduBig (r : ℝ) : ℝ :=
  41840000000000 * r - 28739691360000

private def svCouplingSlopeu4Big (x : ℝ) : ℝ :=
  41840000000000 * x - 4687838400000

private def svCouplingSlopeD (D d r x su du u4 sv : ℝ) : ℝ :=
  (D * svCouplingSlopeDBig su sv + d * svCouplingSlopedBig su sv +
    du * svCouplingSlopeduBig r - 1828008000000 * r -
    5066107440000 * su + 2343802580000 * sv +
    u4 * svCouplingSlopeu4Big x + 65520000000 * x +
    2736502158859) / 400000000000000

private def svCouplingSlopeF (c x su du sv : ℝ) : ℝ :=
  (-2092000000000 * c * su + 819000000000 * c * sv +
    440744850000 * c + 2092000000000 * du * x -
    234391920000 * du + 79392720000 * su - 36730540000 * sv -
    91400400000 * x - 7664642797) / 20000000000000

private def svCouplingSlopex (d f du u4 : ℝ) : ℝ :=
  (433000000000 * d * u4 + 1099000000 * d +
    433000000000 * du * f + 164326600000 * du -
    30662100000 * f + 22393291000 * u4 - 7144434297) /
      5000000000000

private def svCouplingSloper (c d du u4 : ℝ) : ℝ :=
  (4330000000000 * c * u4 + 10990000000 * c +
    4330000000000 * d * du - 306621000000 * d +
    223932910000 * du + 70186600000 * u4 - 9673817517) /
      50000000000000

private def svCouplingSlopec (f su sv u4 : ℝ) : ℝ :=
  (-1385600000 * f * su + 879200000 * f * sv + 473141480 * f -
    525845120 * su + 205863840 * sv + 475540528 * u4 + 111597409) /
      16000000000

private def svCouplingSloped (d su du u4 sv : ℝ) : ℝ :=
  (34640000000000 * d * su - 21980000000000 * d * sv -
    11828537000000 * d + 11888513200000 * du +
    4390627440000 * su - 1915192580000 * sv +
    3035021840000 * u4 - 1590788191447) / 400000000000000

private def svCouplingSlopef (su du sv : ℝ) : ℝ :=
  (607004368000 * du - 148178672000 * su + 66730804000 * sv +
    1919554651) / 80000000000000

private def svCouplingSlopesu : ℝ :=
  57940434443 / 125000000000000

private def svCouplingSlopedu : ℝ :=
  -1997198357049 / 625000000000000

private def svCouplingSlopeu4 : ℝ :=
  -4435817030303 / 5000000000000000

private def svCouplingSlopesv : ℝ :=
  -111907246129 / 500000000000000

set_option maxHeartbeats 3000000 in
private theorem alternatingSvCoupling_telescope
    (X R C D F a x r c d f su du u4 sv : ℝ) :
    alternatingSvCoupling X R C D F a x r c d f
          su du u4 sv (53815 / 100000) (558 / 10000) (-2 / 1000) -
        alternatingSvCoupling
          (1981 / 50000) (121449 / 500000) (671 / 50000)
          (42817 / 1000000) (1571 / 5000) a
          (39761 / 1000000) (49817 / 1000000) (5179 / 1000000)
          (23317 / 1000000) (4416 / 25000)
          (7021 / 12500) (423 / 25000) (18 / 125) (13459 / 25000)
          (53815 / 100000) (558 / 10000) (-2 / 1000) =
      (X - 1981 / 50000) * svCouplingSlopeX D F d f du u4 +
        (R - 121449 / 500000) * svCouplingSlopeR C D c d du u4 +
        (C - 671 / 50000) * svCouplingSlopeC F f r su sv u4 +
        (D - 42817 / 1000000) * svCouplingSlopeD D d r x su du u4 sv +
        (F - 1571 / 5000) * svCouplingSlopeF c x su du sv +
        (x - 39761 / 1000000) * svCouplingSlopex d f du u4 +
        (r - 49817 / 1000000) * svCouplingSloper c d du u4 +
        (c - 5179 / 1000000) * svCouplingSlopec f su sv u4 +
        (d - 23317 / 1000000) * svCouplingSloped d su du u4 sv +
        (f - 4416 / 25000) * svCouplingSlopef su du sv +
        (su - 7021 / 12500) * svCouplingSlopesu +
        (du - 423 / 25000) * svCouplingSlopedu +
        (u4 - 18 / 125) * svCouplingSlopeu4 +
        (sv - 13459 / 25000) * svCouplingSlopesv := by
  unfold alternatingSvCoupling adjugateRowS mixedAdjugateRowS
    svCouplingSlopeX svCouplingSlopeR svCouplingSlopeC svCouplingSlopeD
    svCouplingSlopeDBig svCouplingSlopedBig svCouplingSlopeduBig
    svCouplingSlopeu4Big svCouplingSlopeF svCouplingSlopex
    svCouplingSloper svCouplingSlopec svCouplingSloped svCouplingSlopef
    svCouplingSlopesu svCouplingSlopedu svCouplingSlopeu4
    svCouplingSlopesv
  dsimp only
  ring

set_option maxHeartbeats 3000000 in
private theorem svCoupling_first_five_signs
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    0 ≤ svCouplingSlopeX D F d f du u4 ∧
      svCouplingSlopeR C D c d du u4 ≤ 0 ∧
      svCouplingSlopeC F f r su sv u4 ≤ 0 ∧
      0 ≤ svCouplingSlopeD D d r x su du u4 sv ∧
      0 ≤ svCouplingSlopeF c x su du sv := by
  rcases hbox.C_mem with ⟨hCL, hCU⟩
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.F_mem with ⟨hFL, hFU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  rcases hbox.su_mem with ⟨hsuL, hsuU⟩
  rcases hbox.du_mem with ⟨hduL, hduU⟩
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  rcases hbox.sv_mem with ⟨hsvL, hsvU⟩
  have hSX : (0 : ℝ) ≤ svCouplingSlopeX D F d f du u4 := by
    have hDu4U : D * u4 ≤ (42898 / 1000000 : ℝ) * (144 / 1000) := by
      bound
    have hFduU : F * du ≤ (63 / 200 : ℝ) * (1692 / 100000) := by
      bound
    have hdu4L : (23317 / 1000000 : ℝ) * (141 / 1000) ≤ d * u4 := by
      bound
    have hdufL : (1687 / 100000 : ℝ) * (4411 / 25000) ≤ du * f := by
      bound
    unfold svCouplingSlopeX
    nlinarith only [hDu4U, hFduU, hdu4L, hdufL, hDU, hFL, hdL, hfU]
  have hSR : svCouplingSlopeR C D c d du u4 ≤ (0 : ℝ) := by
    have hCu4L : (1323 / 100000 : ℝ) * (141 / 1000) ≤ C * u4 := by
      bound
    have hDduL : (42817 / 1000000 : ℝ) * (1687 / 100000) ≤ D * du := by
      bound
    have hcu4U : c * u4 ≤ (7165 / 1000000 : ℝ) * (144 / 1000) := by
      bound
    have hdduU : d * du ≤ (27183 / 1000000 : ℝ) * (1692 / 100000) := by
      bound
    unfold svCouplingSlopeR
    nlinarith only [hCu4L, hDduL, hcu4U, hdduU, hCL, hDU, hcU, hdL]
  have hSC : svCouplingSlopeC F f r su sv u4 ≤ (0 : ℝ) := by
    have hFsuU : F * su ≤ (63 / 200 : ℝ) * (56173 / 100000) := by
      bound
    have hFsvL : (1571 / 5000 : ℝ) * (53815 / 100000) ≤ F * sv := by
      bound
    have hfsuL : (4411 / 25000 : ℝ) * (56168 / 100000) ≤ f * su := by
      bound
    have hfsvU : f * sv ≤ (4416 / 25000 : ℝ) * (53836 / 100000) := by
      bound
    have hru4U : r * u4 ≤ (57183 / 1000000 : ℝ) * (144 / 1000) := by
      bound
    unfold svCouplingSlopeC
    nlinarith only [hFsuU, hFsvL, hfsuL, hfsvU, hru4U,
      hFL, hfU, hrU, hu4L]
  have hSD : (0 : ℝ) ≤ svCouplingSlopeD D d r x su du u4 sv := by
    have hBDL : (-7547231600000 : ℝ) ≤ svCouplingSlopeDBig su sv := by
      unfold svCouplingSlopeDBig
      nlinarith only [hsuU, hsvL]
    have hBDU : svCouplingSlopeDBig su sv ≤ (-7529820200000 : ℝ) := by
      unfold svCouplingSlopeDBig
      nlinarith only [hsuL, hsvU]
    have hBdL : (11734914800000 : ℝ) ≤ svCouplingSlopedBig su sv := by
      unfold svCouplingSlopedBig
      nlinarith only [hsuL, hsvU]
    have hBduL : (-26655348080000 : ℝ) ≤ svCouplingSlopeduBig r := by
      unfold svCouplingSlopeduBig
      nlinarith only [hrL]
    have hBduU : svCouplingSlopeduBig r ≤ (-26347154640000 : ℝ) := by
      unfold svCouplingSlopeduBig
      nlinarith only [hrU]
    have hBuL : (-3104152560000 : ℝ) ≤ svCouplingSlopeu4Big x := by
      unfold svCouplingSlopeu4Big
      nlinarith only [hxL]
    have hBuU : svCouplingSlopeu4Big x ≤ (-3024238160000 : ℝ) := by
      unfold svCouplingSlopeu4Big
      nlinarith only [hxU]
    have hDBD : (42898 / 1000000 : ℝ) * (-7547231600000) ≤
        D * svCouplingSlopeDBig su sv := by
      have hleft : (0 : ℝ) ≤
          (42898 / 1000000 - D) * (-svCouplingSlopeDBig su sv) :=
        mul_nonneg (by nlinarith only [hDU]) (by nlinarith only [hBDU])
      have hright : (0 : ℝ) ≤
          (42898 / 1000000) *
            (svCouplingSlopeDBig su sv - (-7547231600000)) :=
        mul_nonneg (by norm_num) (by nlinarith only [hBDL])
      nlinarith only [hleft, hright]
    have hdBd : (23317 / 1000000 : ℝ) * 11734914800000 ≤
        d * svCouplingSlopedBig su sv := by
      have hleft : (0 : ℝ) ≤
          (d - 23317 / 1000000) * svCouplingSlopedBig su sv :=
        mul_nonneg (by nlinarith only [hdL]) (by nlinarith only [hBdL])
      have hright : (0 : ℝ) ≤
          (23317 / 1000000) *
            (svCouplingSlopedBig su sv - 11734914800000) :=
        mul_nonneg (by norm_num) (by nlinarith only [hBdL])
      nlinarith only [hleft, hright]
    have hduBdu : (1692 / 100000 : ℝ) * (-26655348080000) ≤
        du * svCouplingSlopeduBig r := by
      have hleft : (0 : ℝ) ≤
          (1692 / 100000 - du) * (-svCouplingSlopeduBig r) :=
        mul_nonneg (by nlinarith only [hduU]) (by nlinarith only [hBduU])
      have hright : (0 : ℝ) ≤
          (1692 / 100000) * (svCouplingSlopeduBig r - (-26655348080000)) :=
        mul_nonneg (by norm_num) (by nlinarith only [hBduL])
      nlinarith only [hleft, hright]
    have hu4Bu : (144 / 1000 : ℝ) * (-3104152560000) ≤
        u4 * svCouplingSlopeu4Big x := by
      have hleft : (0 : ℝ) ≤
          (144 / 1000 - u4) * (-svCouplingSlopeu4Big x) :=
        mul_nonneg (by nlinarith only [hu4U]) (by nlinarith only [hBuU])
      have hright : (0 : ℝ) ≤
          (144 / 1000) * (svCouplingSlopeu4Big x - (-3104152560000)) :=
        mul_nonneg (by norm_num) (by nlinarith only [hBuL])
      nlinarith only [hleft, hright]
    unfold svCouplingSlopeD
    nlinarith only [hDBD, hdBd, hduBdu, hu4Bu, hrU, hsuU, hsvL, hxL]
  have hSF : (0 : ℝ) ≤ svCouplingSlopeF c x su du sv := by
    have hcsuU : c * su ≤ (7165 / 1000000 : ℝ) * (56173 / 100000) := by
      bound
    have hcsvL : (5179 / 1000000 : ℝ) * (53815 / 100000) ≤ c * sv := by
      bound
    have hduxL : (1687 / 100000 : ℝ) * (37851 / 1000000) ≤ du * x := by
      bound
    unfold svCouplingSlopeF
    nlinarith only [hcsuU, hcsvL, hduxL, hcL, hduU, hsuL, hsvU, hxU]
  exact ⟨hSX, hSR, hSC, hSD, hSF⟩

set_option maxHeartbeats 3000000 in
private theorem svCoupling_last_nine_signs
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    svCouplingSlopex d f du u4 ≤ 0 ∧
      0 ≤ svCouplingSloper c d du u4 ∧
      0 ≤ svCouplingSlopec f su sv u4 ∧
      0 ≤ svCouplingSloped d su du u4 sv ∧
      svCouplingSlopef su du sv ≤ 0 ∧
      0 ≤ svCouplingSlopesu ∧
      svCouplingSlopedu ≤ 0 ∧
      svCouplingSlopeu4 ≤ 0 ∧
      svCouplingSlopesv ≤ 0 := by
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  rcases hbox.su_mem with ⟨hsuL, hsuU⟩
  rcases hbox.du_mem with ⟨hduL, hduU⟩
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  rcases hbox.sv_mem with ⟨hsvL, hsvU⟩
  have hSx : svCouplingSlopex d f du u4 ≤ (0 : ℝ) := by
    have hdu4U : d * u4 ≤ (27183 / 1000000 : ℝ) * (144 / 1000) := by
      bound
    have hdufU : du * f ≤ (1692 / 100000 : ℝ) * (4416 / 25000) := by
      bound
    unfold svCouplingSlopex
    nlinarith only [hdu4U, hdufU, hdU, hduU, hfL, hu4U]
  have hSr : (0 : ℝ) ≤ svCouplingSloper c d du u4 := by
    have hcu4L : (5179 / 1000000 : ℝ) * (141 / 1000) ≤ c * u4 := by
      bound
    have hdduL : (23317 / 1000000 : ℝ) * (1687 / 100000) ≤ d * du := by
      bound
    unfold svCouplingSloper
    nlinarith only [hcu4L, hdduL, hcL, hdU, hduL, hu4L]
  have hSc : (0 : ℝ) ≤ svCouplingSlopec f su sv u4 := by
    have hfsuU : f * su ≤ (4416 / 25000 : ℝ) * (56173 / 100000) := by
      bound
    have hfsvL : (4411 / 25000 : ℝ) * (53815 / 100000) ≤ f * sv := by
      bound
    unfold svCouplingSlopec
    nlinarith only [hfsuU, hfsvL, hfL, hsuU, hsvL, hu4L]
  have hSd : (0 : ℝ) ≤ svCouplingSloped d su du u4 sv := by
    have hdsuL : (23317 / 1000000 : ℝ) * (56168 / 100000) ≤ d * su := by
      bound
    have hdsvU : d * sv ≤ (27183 / 1000000 : ℝ) * (53836 / 100000) := by
      bound
    unfold svCouplingSloped
    nlinarith only [hdsuL, hdsvU, hdU, hduL, hsuL, hsvU, hu4L]
  have hSf : svCouplingSlopef su du sv ≤ (0 : ℝ) := by
    unfold svCouplingSlopef
    nlinarith only [hduU, hsuL, hsvU]
  have hSsu : (0 : ℝ) ≤ svCouplingSlopesu := by
    unfold svCouplingSlopesu
    norm_num
  have hSdu : svCouplingSlopedu ≤ (0 : ℝ) := by
    unfold svCouplingSlopedu
    norm_num
  have hSu4 : svCouplingSlopeu4 ≤ (0 : ℝ) := by
    unfold svCouplingSlopeu4
    norm_num
  have hSsv : svCouplingSlopesv ≤ (0 : ℝ) := by
    unfold svCouplingSlopesv
    norm_num
  exact ⟨hSx, hSr, hSc, hSd, hSf, hSsu, hSdu, hSu4, hSsv⟩

set_option maxHeartbeats 3000000 in
private theorem alternatingSvCoupling_lower
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (8 / 1000000 : ℝ) ≤
      alternatingSvCoupling X R C D F a x r c d f
        su du u4 sv (53815 / 100000) (558 / 10000) (-2 / 1000) := by
  rcases hbox.X_mem with ⟨hXL, hXU⟩
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.C_mem with ⟨hCL, hCU⟩
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.F_mem with ⟨hFL, hFU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  rcases hbox.su_mem with ⟨hsuL, hsuU⟩
  rcases hbox.du_mem with ⟨hduL, hduU⟩
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  rcases hbox.sv_mem with ⟨hsvL, hsvU⟩
  rcases svCoupling_first_five_signs
      A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox with
    ⟨hSX, hSR, hSC, hSD, hSF⟩
  rcases svCoupling_last_nine_signs
      A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox with
    ⟨hSx, hSr, hSc, hSd, hSf, hSsu, hSdu, hSu4, hSsv⟩
  have hX : 0 ≤ (X - 1981 / 50000) * svCouplingSlopeX D F d f du u4 :=
    mul_nonneg (by nlinarith only [hXL]) hSX
  have hR : 0 ≤ (R - 121449 / 500000) *
      svCouplingSlopeR C D c d du u4 :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hRU]) hSR
  have hC : 0 ≤ (C - 671 / 50000) *
      svCouplingSlopeC F f r su sv u4 :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hCU]) hSC
  have hD : 0 ≤ (D - 42817 / 1000000) *
      svCouplingSlopeD D d r x su du u4 sv :=
    mul_nonneg (by nlinarith only [hDL]) hSD
  have hF : 0 ≤ (F - 1571 / 5000) * svCouplingSlopeF c x su du sv :=
    mul_nonneg (by nlinarith only [hFL]) hSF
  have hx : 0 ≤ (x - 39761 / 1000000) * svCouplingSlopex d f du u4 :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hxU]) hSx
  have hr : 0 ≤ (r - 49817 / 1000000) * svCouplingSloper c d du u4 :=
    mul_nonneg (by nlinarith only [hrL]) hSr
  have hc : 0 ≤ (c - 5179 / 1000000) * svCouplingSlopec f su sv u4 :=
    mul_nonneg (by nlinarith only [hcL]) hSc
  have hd : 0 ≤ (d - 23317 / 1000000) *
      svCouplingSloped d su du u4 sv :=
    mul_nonneg (by nlinarith only [hdL]) hSd
  have hf : 0 ≤ (f - 4416 / 25000) * svCouplingSlopef su du sv :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hfU]) hSf
  have hsu : 0 ≤ (su - 7021 / 12500) * svCouplingSlopesu :=
    mul_nonneg (by nlinarith only [hsuL]) hSsu
  have hdu : 0 ≤ (du - 423 / 25000) * svCouplingSlopedu :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hduU]) hSdu
  have hu4 : 0 ≤ (u4 - 18 / 125) * svCouplingSlopeu4 :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hu4U]) hSu4
  have hsv : 0 ≤ (sv - 13459 / 25000) * svCouplingSlopesv :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hsvU]) hSsv
  have htel := alternatingSvCoupling_telescope
    X R C D F a x r c d f su du u4 sv
  have hcorner : (8 / 1000000 : ℝ) <
      alternatingSvCoupling
        (1981 / 50000) (121449 / 500000) (671 / 50000)
        (42817 / 1000000) (1571 / 5000) a
        (39761 / 1000000) (49817 / 1000000) (5179 / 1000000)
        (23317 / 1000000) (4416 / 25000)
        (7021 / 12500) (423 / 25000) (18 / 125) (13459 / 25000)
        (53815 / 100000) (558 / 10000) (-2 / 1000) := by
    unfold alternatingSvCoupling adjugateRowS mixedAdjugateRowS
    norm_num
  nlinarith only [htel, hcorner, hX, hR, hC, hD, hF, hx, hr, hc,
    hd, hf, hsu, hdu, hu4, hsv]

set_option maxHeartbeats 3000000 in
private theorem alternatingSvCross_lower
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (-4 / 1000000 : ℝ) ≤
      alternatingSvCross X R C D F a x r c d f
        su du u4 sv (53815 / 100000) (558 / 10000) (-2 / 1000) := by
  rcases hbox.X_mem with ⟨hXL, hXU⟩
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.C_mem with ⟨hCL, hCU⟩
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.F_mem with ⟨hFL, hFU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  rcases hbox.su_mem with ⟨hsuL, hsuU⟩
  rcases hbox.du_mem with ⟨hduL, hduU⟩
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  rcases hbox.sv_mem with ⟨hsvL, hsvU⟩
  let Xp := X - x
  let Rp := R - r
  let Cp := C - c
  let Dp := D - d
  let Fp := F - f
  let svbar := (sv + 53815 / 100000) / 2
  let zs := u4 * (558 / 10000) - (-2 / 1000) * du
  let zd := (-2 / 1000) * su - u4 * svbar
  let zc := (du * svbar - su * (558 / 10000)) / 2
  have hXpU : Xp ≤ (1919 / 1000000 : ℝ) := by
    dsimp [Xp]
    nlinarith only [hXU, hxL]
  have hRpL : (92817 / 500000 : ℝ) ≤ Rp := by
    dsimp [Rp]
    nlinarith only [hRL, hrU]
  have hCpL : (1213 / 200000 : ℝ) ≤ Cp := by
    dsimp [Cp]
    nlinarith only [hCL, hcU]
  have hDpL : (7817 / 500000 : ℝ) ≤ Dp := by
    dsimp [Dp]
    nlinarith only [hDL, hdU]
  have hDpU : Dp ≤ (19581 / 1000000 : ℝ) := by
    dsimp [Dp]
    nlinarith only [hDU, hdL]
  have hFpL : (3439 / 25000 : ℝ) ≤ Fp := by
    dsimp [Fp]
    nlinarith only [hFL, hfU]
  have hFpU : Fp ≤ (433 / 3125 : ℝ) := by
    dsimp [Fp]
    nlinarith only [hFU, hfL]
  have hsvbarL : (53815 / 100000 : ℝ) ≤ svbar := by
    dsimp [svbar]
    nlinarith only [hsvL]
  have hsvbarU : svbar ≤ (107651 / 200000 : ℝ) := by
    dsimp [svbar]
    nlinarith only [hsvU]
  have hu4svbarL : (141 / 1000 : ℝ) * (53815 / 100000) ≤
      u4 * svbar := by
    bound
  have hu4svbarU : u4 * svbar ≤
      (144 / 1000 : ℝ) * (107651 / 200000) := by
    bound
  have hdusvbarL : (1687 / 100000 : ℝ) * (53815 / 100000) ≤
      du * svbar := by
    bound
  have hdusvbarU : du * svbar ≤
      (1692 / 100000 : ℝ) * (107651 / 200000) := by
    bound
  have hzsL : (395077 / 50000000 : ℝ) ≤ zs := by
    dsimp [zs]
    nlinarith only [hduL, hu4L]
  have hzsU : zs ≤ (100863 / 12500000 : ℝ) := by
    dsimp [zs]
    nlinarith only [hduU, hu4U]
  have hzdL : (-3931609 / 50000000 : ℝ) ≤ zd := by
    dsimp [zd]
    nlinarith only [hsuU, hu4svbarU]
  have hzdU : zd ≤ (-7700251 / 100000000 : ℝ) := by
    dsimp [zd]
    nlinarith only [hsuL, hu4svbarL]
  have hzcL : (-44531887 / 4000000000 : ℝ) ≤ zc := by
    dsimp [zc]
    nlinarith only [hdusvbarL, hsuU]
  have hzcU : zc ≤ (-111172347 / 10000000000 : ℝ) := by
    dsimp [zc]
    nlinarith only [hdusvbarU, hsuL]
  have hXpzs : Xp * zs ≤
      (1919 / 1000000 : ℝ) * (100863 / 12500000) := by
    have hleft : (0 : ℝ) ≤ (1919 / 1000000 - Xp) * zs :=
      mul_nonneg (by nlinarith only [hXpU]) (by nlinarith only [hzsL])
    have hright : (0 : ℝ) ≤
        (1919 / 1000000) * (100863 / 12500000 - zs) :=
      mul_nonneg (by norm_num) (by nlinarith only [hzsU])
    nlinarith only [hleft, hright]
  have hCpzd : Cp * zd ≤
      (1213 / 200000 : ℝ) * (-7700251 / 100000000) := by
    have hleft : (0 : ℝ) ≤ (Cp - 1213 / 200000) * (-zd) :=
      mul_nonneg (by nlinarith only [hCpL]) (by nlinarith only [hzdU])
    have hright : (0 : ℝ) ≤
        (1213 / 200000) * ((-7700251 / 100000000) - zd) :=
      mul_nonneg (by norm_num) (by nlinarith only [hzdU])
    nlinarith only [hleft, hright]
  have hDpzc : (19581 / 1000000 : ℝ) *
        (-44531887 / 4000000000) ≤ Dp * zc := by
    have hleft : (0 : ℝ) ≤ (19581 / 1000000 - Dp) * (-zc) :=
      mul_nonneg (by nlinarith only [hDpU]) (by nlinarith only [hzcU])
    have hright : (0 : ℝ) ≤
        (19581 / 1000000) * (zc - (-44531887 / 4000000000)) :=
      mul_nonneg (by norm_num) (by nlinarith only [hzcL])
    nlinarith only [hleft, hright]
  have hgD : crossGradientD Xp Cp Dp zs zd zc ≤
      (-31092591433 / 4000000000000000 : ℝ) := by
    unfold crossGradientD
    nlinarith only [hXpzs, hCpzd, hDpzc]
  have hRpzs : (92817 / 500000 : ℝ) * (395077 / 50000000) ≤
      Rp * zs := by
    have hleft : (0 : ℝ) ≤ (Rp - 92817 / 500000) * zs :=
      mul_nonneg (by nlinarith only [hRpL]) (by nlinarith only [hzsL])
    have hright : (0 : ℝ) ≤
        (92817 / 500000) * (zs - 395077 / 50000000) :=
      mul_nonneg (by norm_num) (by nlinarith only [hzsL])
    nlinarith only [hleft, hright]
  have hDpzd : (7817 / 500000 : ℝ) * (7700251 / 100000000) ≤
      -Dp * zd := by
    have hleft : (0 : ℝ) ≤ (Dp - 7817 / 500000) * (-zd) :=
      mul_nonneg (by nlinarith only [hDpL]) (by nlinarith only [hzdU])
    have hright : (0 : ℝ) ≤
        (7817 / 500000) * ((-zd) - 7700251 / 100000000) :=
      mul_nonneg (by norm_num) (by nlinarith only [hzdU])
    nlinarith only [hleft, hright]
  have hFpzc : (433 / 3125 : ℝ) * (-44531887 / 4000000000) ≤
      Fp * zc := by
    have hleft : (0 : ℝ) ≤ Fp * (zc - (-44531887 / 4000000000)) :=
      mul_nonneg (by nlinarith only [hFpL]) (by nlinarith only [hzcL])
    have hright : (0 : ℝ) ≤
        (-44531887 / 4000000000) * (Fp - 433 / 3125) :=
      mul_nonneg_of_nonpos_of_nonpos (by norm_num)
        (by nlinarith only [hFpU])
    nlinarith only [hleft, hright]
  have hg4 : (-20725870683 / 50000000000000 : ℝ) ≤
      crossGradientFour Rp Dp Fp zs zd zc := by
    unfold crossGradientFour
    nlinarith only [hRpzs, hDpzd, hFpzc]
  have hfirst : (0 : ℝ) ≤
      (-u4) * crossGradientD Xp Cp Dp zs zd zc :=
    mul_nonneg_of_nonpos_of_nonpos
      (by nlinarith only [hu4L]) (by nlinarith only [hgD])
  have hkL : (0 : ℝ) ≤ du / 2 := by
    nlinarith only [hduL]
  have hkU : du / 2 ≤ (423 / 50000 : ℝ) := by
    nlinarith only [hduU]
  have hleft : (0 : ℝ) ≤
      (du / 2) *
        (crossGradientFour Rp Dp Fp zs zd zc -
          (-20725870683 / 50000000000000)) :=
    mul_nonneg hkL (by nlinarith only [hg4])
  have hright : (0 : ℝ) ≤
      (423 / 50000 - du / 2) *
        (-(-20725870683 / 50000000000000 : ℝ)) :=
    mul_nonneg (by nlinarith only [hkU]) (by norm_num)
  have hsecond : (423 / 50000 : ℝ) *
        (-20725870683 / 50000000000000) ≤
      (du / 2) * crossGradientFour Rp Dp Fp zs zd zc := by
    nlinarith only [hleft, hright]
  change (-u4) * crossGradientD Xp Cp Dp zs zd zc +
      (du / 2) * crossGradientFour Rp Dp Fp zs zd zc ≥
    (-4 / 1000000 : ℝ)
  nlinarith only [hfirst, hsecond]

private def alternatingDvCoupling
    (X R C D F a x r c d f su du u4 sv dv dv0 v4 : ℝ) : ℝ :=
  let A := (137423 / 100000 : ℝ)
  let Ap := A - a
  let Xp := X - x
  let Rp := R - r
  let Cp := C - c
  let Dp := D - d
  let Fp := F - f
  let Am := A + a
  let Xm := X + x
  let Rm := R + r
  let Cm := C + c
  let Dm := D + d
  let Fm := F + f
  let dvbar := (dv + dv0) / 2
  let wmS := (523 / 2500) * su - (819 / 5000) * sv
  let wmD := (523 / 2500) * du - (819 / 5000) * dvbar
  let wm4 := (523 / 2500) * u4 - (819 / 5000) * v4
  let wpS := (239 / 1250) * su - (959 / 5000) * sv
  let wpD := (239 / 1250) * du - (959 / 5000) * dvbar
  let wp4 := (239 / 1250) * u4 - (959 / 5000) * v4
  2 * (adjugateRowD Ap Xp Rp Cp Dp Fp wmS wmD wm4 +
    mixedAdjugateRowD Ap Xp Rp Cp Dp Fp
      Am Xm Rm Cm Dm Fm wpS wpD wp4)

private def alternatingDvCross
    (X R C D F a x r c d f su du u4 sv dv dv0 v4 : ℝ) : ℝ :=
  let A := (137423 / 100000 : ℝ)
  let Ap := A - a
  let Xp := X - x
  let Rp := R - r
  let Dp := D - d
  let Fp := F - f
  let dvbar := (dv + dv0) / 2
  let zs := u4 * dvbar - v4 * du
  let zd := v4 * su - u4 * sv
  let zc := (du * sv - su * dvbar) / 2
  u4 * crossGradientS Ap Xp Rp zs zd zc -
    (su / 2) * crossGradientFour Rp Dp Fp zs zd zc

private theorem alternating_dv_secant_eq
    (X R C D F a x r c d f su du u4 sv dv dv0 v4 : ℝ) :
    quadraticSecant
        (fun z ↦ alternatingFace X R C D F a x r c d f
          su du u4 sv z v4) dv dv0 =
      alternatingDvCoupling X R C D F a x r c d f
          su du u4 sv dv dv0 v4 +
        alternatingDvCross X R C D F a x r c d f
          su du u4 sv dv dv0 v4 := by
  unfold quadraticSecant alternatingFace alternatingDvCoupling
    alternatingDvCross correlatedCoefficientTwo adjugateRowD
    mixedAdjugateRowD crossGradientS crossGradientFour alignedDeterminant
    alignedMixedDeterminant alignedAdjugatePair alignedMixedAdjugatePair
    alignedCrossEnergy alignedEntry00 alignedEntry02 alignedEntry04
    alignedEntry22 alignedEntry24 mixedDeterminantOne
  dsimp only
  ring

private def dvCouplingTermOne
    (X R D F x r d f su sv : ℝ) : ℝ :=
  -(1046 * su - 819 * sv) *
    (D * R - D * r + F * X - F * x - R * d - X * f + d * r + f * x) /
      10000

private def dvCouplingTermTwo
    (R F a r f du dv : ℝ) : ℝ :=
  -(10460000 * du - 4095000 * dv - 228501) *
    (100000 * F * a - 137423 * F + 100000 * R ^ 2 -
      200000 * R * r - 100000 * a * f + 137423 * f + 100000 * r ^ 2) /
      10000000000000

private def dvCouplingTermThree
    (X R D a x r d u4 : ℝ) : ℝ :=
  (523000 * u4 + 819) *
    (-100000 * D * a + 137423 * D + 100000 * R * X -
      100000 * R * x - 100000 * X * r + 100000 * a * d -
      137423 * d + 100000 * r * x) / 500000000000

private def dvCouplingTermFour
    (X R D F x r d f su sv : ℝ) : ℝ :=
  (956 * su - 959 * sv) * (-D * R - F * X + d * r + f * x) / 5000

private def dvCouplingTermFive
    (R F a r f du dv : ℝ) : ℝ :=
  (9560000 * du - 4795000 * dv - 267561) *
    (137423 * F - 100000 * R ^ 2 - 100000 * a * f + 100000 * r ^ 2) /
      5000000000000

private def dvCouplingTermSix
    (X R D a x r d u4 : ℝ) : ℝ :=
  -(478000 * u4 + 959) *
    (-137423 * D - 100000 * R * X + 100000 * a * d + 100000 * r * x) /
      250000000000

private theorem alternatingDvCoupling_terms_eq
    (X R C D F a x r c d f su du u4 sv dv : ℝ) :
    alternatingDvCoupling X R C D F a x r c d f
        su du u4 sv dv (558 / 10000) (-2 / 1000) =
      dvCouplingTermOne X R D F x r d f su sv +
        dvCouplingTermTwo R F a r f du dv +
        dvCouplingTermThree X R D a x r d u4 +
        dvCouplingTermFour X R D F x r d f su sv +
        dvCouplingTermFive R F a r f du dv +
        dvCouplingTermSix X R D a x r d u4 := by
  unfold alternatingDvCoupling adjugateRowD mixedAdjugateRowD
    dvCouplingTermOne dvCouplingTermTwo dvCouplingTermThree
    dvCouplingTermFour dvCouplingTermFive dvCouplingTermSix
  dsimp only
  ring

set_option maxHeartbeats 3000000 in
private theorem alternatingDvCoupling_upper
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    alternatingDvCoupling X R C D F a x r c d f
        su du u4 sv dv (558 / 10000) (-2 / 1000) ≤
      (-32 / 100000 : ℝ) := by
  rcases hbox.X_mem with ⟨hXL, hXU⟩
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.F_mem with ⟨hFL, hFU⟩
  rcases hbox.a_mem with ⟨haL, haU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  rcases hbox.su_mem with ⟨hsuL, hsuU⟩
  rcases hbox.du_mem with ⟨hduL, hduU⟩
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  rcases hbox.sv_mem with ⟨hsvL, hsvU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  let Ap := (137423 / 100000 : ℝ) - a
  let Xp := X - x
  let Rp := R - r
  let Dp := D - d
  let Fp := F - f
  have hApL : (109553 / 200000 : ℝ) ≤ Ap := by
    dsimp [Ap]
    nlinarith only [haU]
  have hApU : Ap ≤ (549751 / 1000000 : ℝ) := by
    dsimp [Ap]
    nlinarith only [haL]
  have hXpL : (-141 / 1000000 : ℝ) ≤ Xp := by
    dsimp [Xp]
    nlinarith only [hXL, hxU]
  have hXpU : Xp ≤ (1919 / 1000000 : ℝ) := by
    dsimp [Xp]
    nlinarith only [hXU, hxL]
  have hRpL : (92817 / 500000 : ℝ) ≤ Rp := by
    dsimp [Rp]
    nlinarith only [hRL, hrU]
  have hRpU : Rp ≤ (193081 / 1000000 : ℝ) := by
    dsimp [Rp]
    nlinarith only [hRU, hrL]
  have hDpL : (7817 / 500000 : ℝ) ≤ Dp := by
    dsimp [Dp]
    nlinarith only [hDL, hdU]
  have hDpU : Dp ≤ (19581 / 1000000 : ℝ) := by
    dsimp [Dp]
    nlinarith only [hDU, hdL]
  have hFpL : (3439 / 25000 : ℝ) ≤ Fp := by
    dsimp [Fp]
    nlinarith only [hFL, hfU]
  have hFpU : Fp ≤ (433 / 3125 : ℝ) := by
    dsimp [Fp]
    nlinarith only [hFU, hfL]
  let A1 := 1046 * su - 819 * sv
  let B1 := D * R - D * r + F * X - F * x - R * d - X * f + d * r + f * x
  have hA1L : (3665011 / 25000 : ℝ) ≤ A1 := by
    dsimp [A1]
    nlinarith only [hsuL, hsvU]
  have hDpRpL :
      (7817 / 500000 : ℝ) * (92817 / 500000) ≤ Dp * Rp := by
    have hleft : (0 : ℝ) ≤ (Dp - 7817 / 500000) * Rp :=
      mul_nonneg (by nlinarith only [hDpL]) (by nlinarith only [hRpL])
    have hright : (0 : ℝ) ≤
        (7817 / 500000) * (Rp - 92817 / 500000) :=
      mul_nonneg (by norm_num) (by nlinarith only [hRpL])
    nlinarith only [hleft, hright]
  have hFpXpL :
      (433 / 3125 : ℝ) * (-141 / 1000000) ≤ Fp * Xp := by
    have hleft : (0 : ℝ) ≤ Fp * (Xp - (-141 / 1000000)) :=
      mul_nonneg (by nlinarith only [hFpL]) (by nlinarith only [hXpL])
    have hright : (0 : ℝ) ≤
        (-141 / 1000000) * (Fp - 433 / 3125) :=
      mul_nonneg_of_nonpos_of_nonpos (by norm_num)
        (by nlinarith only [hFpU])
    nlinarith only [hleft, hright]
  have hB1L : (5734158683 / 2000000000000 : ℝ) ≤ B1 := by
    dsimp [B1, Dp, Rp, Fp, Xp] at hDpRpL hFpXpL ⊢
    nlinarith only [hDpRpL, hFpXpL]
  have hA1B1 : (3665011 / 25000 : ℝ) *
        (5734158683 / 2000000000000) ≤ A1 * B1 := by
    have hleft : (0 : ℝ) ≤ (A1 - 3665011 / 25000) * B1 :=
      mul_nonneg (by nlinarith only [hA1L]) (by nlinarith only [hB1L])
    have hright : (0 : ℝ) ≤
        (3665011 / 25000) * (B1 - 5734158683 / 2000000000000) :=
      mul_nonneg (by norm_num) (by nlinarith only [hB1L])
    nlinarith only [hleft, hright]
  have hT1 : dvCouplingTermOne X R D F x r d f su sv ≤
      (-4 / 100000 : ℝ) := by
    unfold dvCouplingTermOne
    dsimp [A1, B1] at hA1B1
    nlinarith only [hA1B1]
  let A2 := 10460000 * du - 4095000 * dv - 228501
  let B2 := 100000 * F * a - 137423 * F + 100000 * R ^ 2 -
    200000 * R * r - 100000 * a * f + 137423 * f + 100000 * r ^ 2
  have hA2U : A2 ≤ (-2787903 / 10 : ℝ) := by
    dsimp [A2]
    nlinarith only [hduU, hdvL]
  have hFpApL :
      (3439 / 25000 : ℝ) * (109553 / 200000) ≤ Fp * Ap := by
    bound
  have hRpSqU : Rp ^ 2 ≤ (193081 / 1000000 : ℝ) ^ 2 := by
    bound
  have hB2U : B2 ≤ (-38069287839 / 10000000 : ℝ) := by
    dsimp [B2, Fp, Ap, Rp] at hFpApL hRpSqU ⊢
    nlinarith only [hFpApL, hRpSqU]
  have hA2B2 : (2787903 / 10 : ℝ) * (38069287839 / 10000000) ≤
      A2 * B2 := by
    have hleft : (0 : ℝ) ≤ ((-A2) - 2787903 / 10) * (-B2) :=
      mul_nonneg (by nlinarith only [hA2U]) (by nlinarith only [hB2U])
    have hright : (0 : ℝ) ≤
        (2787903 / 10) * ((-B2) - 38069287839 / 10000000) :=
      mul_nonneg (by norm_num) (by nlinarith only [hB2U])
    nlinarith only [hleft, hright]
  have hT2 : dvCouplingTermTwo R F a r f du dv ≤
      (-10 / 100000 : ℝ) := by
    unfold dvCouplingTermTwo
    dsimp [A2, B2] at hA2B2
    nlinarith only [hA2B2]
  let A3 := 523000 * u4 + 819
  let B3 := -100000 * D * a + 137423 * D + 100000 * R * X -
    100000 * R * x - 100000 * X * r + 100000 * a * d -
    137423 * d + 100000 * r * x
  have hA3U : A3 ≤ (76131 : ℝ) := by
    dsimp [A3]
    nlinarith only [hu4U]
  have hApDpU : Ap * Dp ≤
      (549751 / 1000000 : ℝ) * (19581 / 1000000) := by
    bound
  have hXpRpU : Xp * Rp ≤
      (1919 / 1000000 : ℝ) * (193081 / 1000000) := by
    have hleft : (0 : ℝ) ≤ (1919 / 1000000 - Xp) * Rp :=
      mul_nonneg (by nlinarith only [hXpU]) (by nlinarith only [hRpL])
    have hright : (0 : ℝ) ≤
        (1919 / 1000000) * (193081 / 1000000 - Rp) :=
      mul_nonneg (by norm_num) (by nlinarith only [hRpU])
    nlinarith only [hleft, hright]
  have hB3U : B3 ≤ (1113519677 / 1000000 : ℝ) := by
    dsimp [B3, Ap, Dp, Xp, Rp] at hApDpU hXpRpU ⊢
    nlinarith only [hApDpU, hXpRpU]
  have hApDpL :
      (109553 / 200000 : ℝ) * (7817 / 500000) ≤ Ap * Dp := by
    bound
  have hXpRpL :
      (-141 / 1000000 : ℝ) * (193081 / 1000000) ≤ Xp * Rp := by
    have hleft : (0 : ℝ) ≤ Rp * (Xp - (-141 / 1000000)) :=
      mul_nonneg (by nlinarith only [hRpL]) (by nlinarith only [hXpL])
    have hright : (0 : ℝ) ≤
        (-141 / 1000000) * (Rp - 193081 / 1000000) :=
      mul_nonneg_of_nonpos_of_nonpos (by norm_num)
        (by nlinarith only [hRpU])
    nlinarith only [hleft, hright]
  have hB30 : (0 : ℝ) ≤ B3 := by
    dsimp [B3, Ap, Dp, Xp, Rp] at hApDpL hXpRpL ⊢
    nlinarith only [hApDpL, hXpRpL]
  have hA3B3 : A3 * B3 ≤ (76131 : ℝ) * (1113519677 / 1000000) := by
    have hleft : (0 : ℝ) ≤ (76131 - A3) * B3 :=
      mul_nonneg (by nlinarith only [hA3U]) hB30
    have hright : (0 : ℝ) ≤
        76131 * (1113519677 / 1000000 - B3) :=
      mul_nonneg (by norm_num) (by nlinarith only [hB3U])
    nlinarith only [hleft, hright]
  have hT3 : dvCouplingTermThree X R D a x r d u4 ≤
      (17 / 100000 : ℝ) := by
    unfold dvCouplingTermThree
    dsimp [A3, B3] at hA3B3
    nlinarith only [hA3B3]
  let A4 := 956 * su - 959 * sv
  let B4 := -D * R - F * X + d * r + f * x
  have hA4L : (516971 / 25000 : ℝ) ≤ A4 := by
    dsimp [A4]
    nlinarith only [hsuL, hsvU]
  have hDRL : (42817 / 1000000 : ℝ) * (242817 / 1000000) ≤ D * R := by
    bound
  have hFXL : (1571 / 5000 : ℝ) * (3962 / 100000) ≤ F * X := by
    bound
  have hdrU : d * r ≤ (27183 / 1000000 : ℝ) * (57183 / 1000000) := by
    bound
  have hfxU : f * x ≤ (4416 / 25000 : ℝ) * (39761 / 1000000) := by
    bound
  have hB4U : B4 ≤ (-28534895359 / 2000000000000 : ℝ) := by
    dsimp [B4]
    nlinarith only [hDRL, hFXL, hdrU, hfxU]
  have hA4B4 : (516971 / 25000 : ℝ) *
      (28534895359 / 2000000000000) ≤ A4 * (-B4) := by
    have hleft : (0 : ℝ) ≤ (A4 - 516971 / 25000) * (-B4) :=
      mul_nonneg (by nlinarith only [hA4L]) (by nlinarith only [hB4U])
    have hright : (0 : ℝ) ≤
        (516971 / 25000) * ((-B4) - 28534895359 / 2000000000000) :=
      mul_nonneg (by norm_num) (by nlinarith only [hB4U])
    nlinarith only [hleft, hright]
  have hT4 : dvCouplingTermFour X R D F x r d f su sv ≤
      (-5 / 100000 : ℝ) := by
    unfold dvCouplingTermFour
    dsimp [A4, B4] at hA4B4
    nlinarith only [hA4B4]
  let A5 := 9560000 * du - 4795000 * dv - 267561
  let B5 := 137423 * F - 100000 * R ^ 2 - 100000 * a * f + 100000 * r ^ 2
  have hA5U : A5 ≤ (-3719283 / 10 : ℝ) := by
    dsimp [A5]
    nlinarith only [hduU, hdvL]
  have hafU : a * f ≤ (826465 / 1000000 : ℝ) * (4416 / 25000) := by
    bound
  have hRsqU : R ^ 2 ≤ (242898 / 1000000 : ℝ) ^ 2 := by
    bound
  have hrsqL : (49817 / 1000000 : ℝ) ^ 2 ≤ r ^ 2 := by
    bound
  have hB5L : (229251454507 / 10000000 : ℝ) ≤ B5 := by
    dsimp [B5]
    nlinarith only [hFL, hafU, hRsqU, hrsqL]
  have hA5B5 : (3719283 / 10 : ℝ) * (229251454507 / 10000000) ≤
      (-A5) * B5 := by
    have hleft : (0 : ℝ) ≤ ((-A5) - 3719283 / 10) * B5 :=
      mul_nonneg (by nlinarith only [hA5U]) (by nlinarith only [hB5L])
    have hright : (0 : ℝ) ≤
        (3719283 / 10) * (B5 - 229251454507 / 10000000) :=
      mul_nonneg (by norm_num) (by nlinarith only [hB5L])
    nlinarith only [hleft, hright]
  have hT5 : dvCouplingTermFive R F a r f du dv ≤
      (-17 / 10000 : ℝ) := by
    unfold dvCouplingTermFive
    dsimp [A5, B5] at hA5B5
    nlinarith only [hA5B5]
  let A6 := 478000 * u4 + 959
  let B6 := -137423 * D - 100000 * R * X + 100000 * a * d + 100000 * r * x
  have hA6U : A6 ≤ (69791 : ℝ) := by
    dsimp [A6]
    nlinarith only [hu4U]
  have hRXU : R * X ≤ (242898 / 1000000 : ℝ) * (3977 / 100000) := by
    bound
  have hadL : (824479 / 1000000 : ℝ) * (23317 / 1000000) ≤ a * d := by
    bound
  have hrxL : (49817 / 1000000 : ℝ) * (37851 / 1000000) ≤ r * x := by
    bound
  have hB6L : (-23756322679 / 5000000 : ℝ) ≤ B6 := by
    dsimp [B6]
    nlinarith only [hDU, hRXU, hadL, hrxL]
  have hRXL : (242817 / 1000000 : ℝ) * (3962 / 100000) ≤ R * X := by
    bound
  have hadU : a * d ≤ (826465 / 1000000 : ℝ) * (27183 / 1000000) := by
    bound
  have hrxU : r * x ≤ (57183 / 1000000 : ℝ) * (39761 / 1000000) := by
    bound
  have hB6U : B6 ≤ (-43721358017 / 10000000 : ℝ) := by
    dsimp [B6]
    nlinarith only [hDL, hRXL, hadU, hrxU]
  have hA6B6 : (69791 : ℝ) * (-23756322679 / 5000000) ≤ A6 * B6 := by
    have hleft : (0 : ℝ) ≤ (69791 - A6) * (-B6) :=
      mul_nonneg (by nlinarith only [hA6U]) (by nlinarith only [hB6U])
    have hright : (0 : ℝ) ≤
        69791 * ((-23756322679 / 5000000) * (-1) - (-B6)) :=
      mul_nonneg (by norm_num) (by nlinarith only [hB6L])
    nlinarith only [hleft, hright]
  have hT6 : dvCouplingTermSix X R D a x r d u4 ≤
      (14 / 10000 : ℝ) := by
    unfold dvCouplingTermSix
    dsimp [A6, B6] at hA6B6
    nlinarith only [hA6B6]
  rw [alternatingDvCoupling_terms_eq]
  nlinarith only [hT1, hT2, hT3, hT4, hT5, hT6]

set_option maxHeartbeats 3000000 in
private theorem alternatingDvCross_upper
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    alternatingDvCross X R C D F a x r c d f
        su du u4 sv dv (558 / 10000) (-2 / 1000) ≤
      (15 / 100000 : ℝ) := by
  rcases hbox.X_mem with ⟨hXL, hXU⟩
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.F_mem with ⟨hFL, hFU⟩
  rcases hbox.a_mem with ⟨haL, haU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  rcases hbox.su_mem with ⟨hsuL, hsuU⟩
  rcases hbox.du_mem with ⟨hduL, hduU⟩
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  rcases hbox.sv_mem with ⟨hsvL, hsvU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  let Ap := (137423 / 100000 : ℝ) - a
  let Xp := X - x
  let Rp := R - r
  let Dp := D - d
  let Fp := F - f
  let dbar := (dv + 558 / 10000) / 2
  let zs := u4 * dbar - (-2 / 1000) * du
  let zd := (-2 / 1000) * su - u4 * sv
  let zc := (du * sv - su * dbar) / 2
  have hApU : Ap ≤ (549751 / 1000000 : ℝ) := by
    dsimp [Ap]
    nlinarith only [haL]
  have hXpL : (-141 / 1000000 : ℝ) ≤ Xp := by
    dsimp [Xp]
    nlinarith only [hXL, hxU]
  have hRpL : (92817 / 500000 : ℝ) ≤ Rp := by
    dsimp [Rp]
    nlinarith only [hRL, hrU]
  have hDpL : (7817 / 500000 : ℝ) ≤ Dp := by
    dsimp [Dp]
    nlinarith only [hDL, hdU]
  have hFpL : (3439 / 25000 : ℝ) ≤ Fp := by
    dsimp [Fp]
    nlinarith only [hFL, hfU]
  have hFpU : Fp ≤ (433 / 3125 : ℝ) := by
    dsimp [Fp]
    nlinarith only [hFU, hfL]
  have hdbarL : (1113 / 20000 : ℝ) ≤ dbar := by
    dsimp [dbar]
    nlinarith only [hdvL]
  have hdbarU : dbar ≤ (279 / 5000 : ℝ) := by
    dsimp [dbar]
    nlinarith only [hdvU]
  have hu4dbarL : (141 / 1000 : ℝ) * (1113 / 20000) ≤ u4 * dbar := by
    bound
  have hu4dbarU : u4 * dbar ≤ (144 / 1000 : ℝ) * (279 / 5000) := by
    bound
  have hu4svL : (141 / 1000 : ℝ) * (53815 / 100000) ≤ u4 * sv := by
    bound
  have hu4svU : u4 * sv ≤ (144 / 1000 : ℝ) * (53836 / 100000) := by
    bound
  have hdusvL : (1687 / 100000 : ℝ) * (53815 / 100000) ≤ du * sv := by
    bound
  have hdusvU : du * sv ≤ (1692 / 100000 : ℝ) * (53836 / 100000) := by
    bound
  have hsudbarL : (56168 / 100000 : ℝ) * (1113 / 20000) ≤ su * dbar := by
    bound
  have hsudbarU : su * dbar ≤ (56173 / 100000 : ℝ) * (279 / 5000) := by
    bound
  have hzsL : (788039 / 100000000 : ℝ) ≤ zs := by
    dsimp [zs]
    nlinarith only [hu4dbarL, hduL]
  have hzsU : zs ≤ (100863 / 12500000 : ℝ) := by
    dsimp [zs]
    nlinarith only [hu4dbarU, hduU]
  have hzdL : (-786473 / 10000000 : ℝ) ≤ zd := by
    dsimp [zd]
    nlinarith only [hsuU, hu4svU]
  have hzdU : zd ≤ (-7700251 / 100000000 : ℝ) := by
    dsimp [zd]
    nlinarith only [hsuL, hu4svL]
  have hzcL : (-44531887 / 4000000000 : ℝ) ≤ zc := by
    dsimp [zc]
    nlinarith only [hdusvL, hsudbarU]
  have hzcU : zc ≤ (-27685551 / 2500000000 : ℝ) := by
    dsimp [zc]
    nlinarith only [hdusvU, hsudbarL]
  have hApzs : Ap * zs ≤
      (549751 / 1000000 : ℝ) * (100863 / 12500000) := by
    have hleft : (0 : ℝ) ≤ (549751 / 1000000 - Ap) * zs :=
      mul_nonneg (by nlinarith only [hApU]) (by nlinarith only [hzsL])
    have hright : (0 : ℝ) ≤
        (549751 / 1000000) * (100863 / 12500000 - zs) :=
      mul_nonneg (by norm_num) (by nlinarith only [hzsU])
    nlinarith only [hleft, hright]
  have hXpzd : Xp * zd ≤
      (-141 / 1000000 : ℝ) * (-786473 / 10000000) := by
    have hleft : (0 : ℝ) ≤ (Xp - (-141 / 1000000)) * (-zd) :=
      mul_nonneg (by nlinarith only [hXpL]) (by nlinarith only [hzdU])
    have hright : (0 : ℝ) ≤
        (141 / 1000000) * (zd - (-786473 / 10000000)) :=
      mul_nonneg (by norm_num) (by nlinarith only [hzdL])
    nlinarith only [hleft, hright]
  have hRpzc : Rp * zc ≤
      (92817 / 500000 : ℝ) * (-27685551 / 2500000000) := by
    have hleft : (0 : ℝ) ≤ (Rp - 92817 / 500000) * (-zc) :=
      mul_nonneg (by nlinarith only [hRpL]) (by nlinarith only [hzcU])
    have hright : (0 : ℝ) ≤
        (92817 / 500000) * ((-27685551 / 2500000000) - zc) :=
      mul_nonneg (by norm_num) (by nlinarith only [hzcU])
    nlinarith only [hleft, hright]
  have hgS : crossGradientS Ap Xp Rp zs zd zc ≤
      (419435523591 / 2500000000000000 : ℝ) := by
    unfold crossGradientS
    nlinarith only [hApzs, hXpzd, hRpzc]
  have hgScap : crossGradientS Ap Xp Rp zs zd zc ≤
      (17 / 100000 : ℝ) := by
    nlinarith only [hgS]
  have hRpzs : (92817 / 500000 : ℝ) * (788039 / 100000000) ≤ Rp * zs := by
    have hleft : (0 : ℝ) ≤ (Rp - 92817 / 500000) * zs :=
      mul_nonneg (by nlinarith only [hRpL]) (by nlinarith only [hzsL])
    have hright : (0 : ℝ) ≤
        (92817 / 500000) * (zs - 788039 / 100000000) :=
      mul_nonneg (by norm_num) (by nlinarith only [hzsL])
    nlinarith only [hleft, hright]
  have hDpzd : (7817 / 500000 : ℝ) * (7700251 / 100000000) ≤
      -Dp * zd := by
    have hleft : (0 : ℝ) ≤ (Dp - 7817 / 500000) * (-zd) :=
      mul_nonneg (by nlinarith only [hDpL]) (by nlinarith only [hzdU])
    have hright : (0 : ℝ) ≤
        (7817 / 500000) * ((-zd) - 7700251 / 100000000) :=
      mul_nonneg (by norm_num) (by nlinarith only [hzdU])
    nlinarith only [hleft, hright]
  have hFpzc : (433 / 3125 : ℝ) * (-44531887 / 4000000000) ≤ Fp * zc := by
    have hleft : (0 : ℝ) ≤ Fp * (zc - (-44531887 / 4000000000)) :=
      mul_nonneg (by nlinarith only [hFpL]) (by nlinarith only [hzcL])
    have hright : (0 : ℝ) ≤
        (-44531887 / 4000000000) * (Fp - 433 / 3125) :=
      mul_nonneg_of_nonpos_of_nonpos (by norm_num)
        (by nlinarith only [hFpU])
    nlinarith only [hleft, hright]
  have hg4 : (-10461089319 / 25000000000000 : ℝ) ≤
      crossGradientFour Rp Dp Fp zs zd zc := by
    unfold crossGradientFour
    nlinarith only [hRpzs, hDpzd, hFpzc]
  have hg4cap : (-42 / 100000 : ℝ) ≤
      crossGradientFour Rp Dp Fp zs zd zc := by
    nlinarith only [hg4]
  have hfirstLeft : (0 : ℝ) ≤
      u4 * (17 / 100000 - crossGradientS Ap Xp Rp zs zd zc) :=
    mul_nonneg (by nlinarith only [hu4L]) (by nlinarith only [hgScap])
  have hfirstRight : (0 : ℝ) ≤
      (144 / 1000 - u4) * (17 / 100000 : ℝ) :=
    mul_nonneg (by nlinarith only [hu4U]) (by norm_num)
  have hfirst : u4 * crossGradientS Ap Xp Rp zs zd zc ≤
      (144 / 1000 : ℝ) * (17 / 100000) := by
    nlinarith only [hfirstLeft, hfirstRight]
  have hkL : (0 : ℝ) ≤ su / 2 := by
    nlinarith only [hsuL]
  have hkU : su / 2 ≤ (56173 / 200000 : ℝ) := by
    nlinarith only [hsuU]
  have hsecondLeft : (0 : ℝ) ≤
      (su / 2) * (crossGradientFour Rp Dp Fp zs zd zc - (-42 / 100000)) :=
    mul_nonneg hkL (by nlinarith only [hg4cap])
  have hsecondRight : (0 : ℝ) ≤
      (56173 / 200000 - su / 2) * (42 / 100000 : ℝ) :=
    mul_nonneg (by nlinarith only [hkU]) (by norm_num)
  have hsecond : -(su / 2) * crossGradientFour Rp Dp Fp zs zd zc ≤
      (56173 / 200000 : ℝ) * (42 / 100000) := by
    nlinarith only [hsecondLeft, hsecondRight]
  change u4 * crossGradientS Ap Xp Rp zs zd zc -
      (su / 2) * crossGradientFour Rp Dp Fp zs zd zc ≤
    (15 / 100000 : ℝ)
  nlinarith only [hfirst, hsecond]

private def alternatingV4Coupling
    (X R C D F a x r c d f su du u4 sv dv v4 v40 : ℝ) : ℝ :=
  let A := (137423 / 100000 : ℝ)
  let Ap := A - a
  let Xp := X - x
  let Rp := R - r
  let Cp := C - c
  let Dp := D - d
  let Fp := F - f
  let Am := A + a
  let Xm := X + x
  let Rm := R + r
  let Cm := C + c
  let Dm := D + d
  let Fm := F + f
  let v4bar := (v4 + v40) / 2
  let wmS := (523 / 2500) * su - (819 / 5000) * sv
  let wmD := (523 / 2500) * du - (819 / 5000) * dv
  let wm4 := (523 / 2500) * u4 - (819 / 5000) * v4bar
  let wpS := (239 / 1250) * su - (959 / 5000) * sv
  let wpD := (239 / 1250) * du - (959 / 5000) * dv
  let wp4 := (239 / 1250) * u4 - (959 / 5000) * v4bar
  2 * (adjugateRowFour Ap Xp Rp Cp Dp Fp wmS wmD wm4 +
    mixedAdjugateRowFour Ap Xp Rp Cp Dp Fp
      Am Xm Rm Cm Dm Fm wpS wpD wp4)

private def alternatingV4Cross
    (X R C D F a x r c d f su du u4 sv dv v4 v40 : ℝ) : ℝ :=
  let A := (137423 / 100000 : ℝ)
  let Ap := A - a
  let Xp := X - x
  let Rp := R - r
  let Cp := C - c
  let Dp := D - d
  let v4bar := (v4 + v40) / 2
  let zs := u4 * dv - v4bar * du
  let zd := v4bar * su - u4 * sv
  let zc := (du * sv - su * dv) / 2
  (-du) * crossGradientS Ap Xp Rp zs zd zc +
    su * crossGradientD Xp Cp Dp zs zd zc

private def alternatingV4Slope
    (X R C D F a x r c d f su du u4 sv dv v4 v40 : ℝ) : ℝ :=
  alternatingV4Coupling X R C D F a x r c d f
      su du u4 sv dv v4 v40 +
    alternatingV4Cross X R C D F a x r c d f
      su du u4 sv dv v4 v40

private theorem alternating_v4_secant_eq
    (X R C D F a x r c d f su du u4 sv dv v4 v40 : ℝ) :
    quadraticSecant
        (fun z ↦ alternatingFace X R C D F a x r c d f
          su du u4 sv dv z) v4 v40 =
      alternatingV4Slope X R C D F a x r c d f
        su du u4 sv dv v4 v40 := by
  unfold quadraticSecant alternatingFace alternatingV4Slope
    alternatingV4Coupling alternatingV4Cross correlatedCoefficientTwo
    adjugateRowFour mixedAdjugateRowFour crossGradientS crossGradientD
    alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
    alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00 alignedEntry02
    alignedEntry04 alignedEntry22 alignedEntry24 mixedDeterminantOne
  dsimp only
  ring

private def v4WmS (su sv : ℝ) : ℝ :=
  (523 / 2500) * su - (819 / 5000) * sv

private def v4WmD (du dv : ℝ) : ℝ :=
  (523 / 2500) * du - (819 / 5000) * dv

private def v4Wm4 (u4 v4 : ℝ) : ℝ :=
  (523 / 2500) * u4 - (819 / 5000) * ((v4 + (-2 / 1000)) / 2)

private def v4WpS (su sv : ℝ) : ℝ :=
  (239 / 1250) * su - (959 / 5000) * sv

private def v4WpD (du dv : ℝ) : ℝ :=
  (239 / 1250) * du - (959 / 5000) * dv

private def v4Wp4 (u4 v4 : ℝ) : ℝ :=
  (239 / 1250) * u4 - (959 / 5000) * ((v4 + (-2 / 1000)) / 2)

private def v4Zs (du u4 dv v4 : ℝ) : ℝ :=
  u4 * dv - ((v4 + (-2 / 1000)) / 2) * du

private def v4Zd (su u4 sv v4 : ℝ) : ℝ :=
  ((v4 + (-2 / 1000)) / 2) * su - u4 * sv

private def v4Zc (su du sv dv : ℝ) : ℝ :=
  (du * sv - su * dv) / 2

private def v4SlopeX
    (X R D a x r d su du u4 sv dv v4 : ℝ) : ℝ :=
  let Xbar := (X + 1981 / 50000) / 2
  let Xp := Xbar - x
  let Rp := R - r
  let Dp := D - d
  (-Dp * v4WmS su sv + Rp * v4WmD du dv -
      2 * Xp * v4Wm4 u4 v4 - 2 * D * v4WpS su sv +
      2 * R * v4WpD du dv - 4 * Xbar * v4Wp4 u4 v4 -
      du * v4Zd su u4 sv v4 + su * v4Zs du u4 dv v4) / 2

private def v4SlopeR
    (C a x r c su du u4 sv dv v4 : ℝ) : ℝ :=
  let X := (1981 / 50000 : ℝ)
  let Xp := X - x
  let Cp := C - c
  (-Cp * v4WmS su sv + Xp * v4WmD du dv -
      2 * C * v4WpS su sv + 2 * X * v4WpD du dv) / 2 -
    du * v4Zc su du sv dv

private def v4SlopeC
    (a r su du u4 sv dv v4 : ℝ) : ℝ :=
  let A0 := (137423 / 100000 : ℝ)
  let Ap := A0 - a
  let Rp := (242817 / 1000000 : ℝ) - r
  (-Rp * v4WmS su sv + Ap * v4Wm4 u4 v4 -
      2 * (242817 / 1000000) * v4WpS su sv +
      2 * A0 * v4Wp4 u4 v4 + su * v4Zd su u4 sv v4) / 2

private def v4SlopeD
    (a x su du u4 sv dv v4 : ℝ) : ℝ :=
  let A0 := (137423 / 100000 : ℝ)
  let Ap := A0 - a
  let Xp := (1981 / 50000 : ℝ) - x
  (-Xp * v4WmS su sv + Ap * v4WmD du dv -
      2 * (1981 / 50000) * v4WpS su sv +
      2 * A0 * v4WpD du dv) / 2 - su * v4Zc su du sv dv

private def v4Slopex
    (x a r d su du u4 sv dv v4 : ℝ) : ℝ :=
  let xbar := (x + 39761 / 1000000) / 2
  let Xp := (1981 / 50000 : ℝ) - xbar
  let Rp := (242817 / 1000000 : ℝ) - r
  let Dp := (42817 / 1000000 : ℝ) - d
  (Dp * v4WmS su sv - Rp * v4WmD du dv +
      2 * Xp * v4Wm4 u4 v4 + 2 * d * v4WpS su sv -
      2 * r * v4WpD du dv + 4 * xbar * v4Wp4 u4 v4 +
      du * v4Zd su u4 sv v4 - su * v4Zs du u4 dv v4) / 2

private def v4Sloper
    (c su du u4 sv dv v4 : ℝ) : ℝ :=
  let Xp := (1981 / 50000 : ℝ) - 39761 / 1000000
  let Cp := (671 / 50000 : ℝ) - c
  (Cp * v4WmS su sv - Xp * v4WmD du dv +
      2 * c * v4WpS su sv -
      2 * (39761 / 1000000) * v4WpD du dv) / 2 +
    du * v4Zc su du sv dv

private def v4Slopec
    (a su du u4 sv dv v4 : ℝ) : ℝ :=
  let A0 := (137423 / 100000 : ℝ)
  let Ap := A0 - a
  let Rp := (242817 / 1000000 : ℝ) - 57183 / 1000000
  (Rp * v4WmS su sv - Ap * v4Wm4 u4 v4 +
      2 * (57183 / 1000000) * v4WpS su sv -
      2 * a * v4Wp4 u4 v4 - su * v4Zd su u4 sv v4) / 2

private def v4Sloped
    (a su du u4 sv dv v4 : ℝ) : ℝ :=
  let A0 := (137423 / 100000 : ℝ)
  let Ap := A0 - a
  let Xp := (1981 / 50000 : ℝ) - 39761 / 1000000
  (Xp * v4WmS su sv - Ap * v4WmD du dv +
      2 * (39761 / 1000000) * v4WpS su sv -
      2 * a * v4WpD du dv) / 2 + su * v4Zc su du sv dv

private def v4Slopesu
    (su du u4 sv dv v4 : ℝ) : ℝ :=
  -(-2900531250000 * du * dv + 244281250000 * du * sv -
      2203125000 * du * v4 + 4406250 * du -
      244281250000 * dv * su + 2203125000 * dv * u4 -
      137207892500 * dv - 64382812500 * su * v4 +
      128765625 * su + 128765625000 * sv * u4 -
      36162538125 * v4 + 26444472196) / 31250000000000

private def v4Slopedu
    (a du u4 sv dv v4 : ℝ) : ℝ :=
  (-125000000000000 * a * du * v4 + 250000000000 * a * du +
      250000000000000 * a * dv * u4 - 2115000000000 * a * v4 -
      3412123000000 * a - 46408500000000 * du * sv +
      171778750000000 * du * v4 - 343557500000 * du -
      343557500000000 * dv * u4 + 26066726280000 * dv -
      35250000000 * sv * u4 - 2980558100000 * sv +
      2926295670000 * v4 + 7443921621117) / 500000000000000

private def v4Slopeu4 (a sv dv : ℝ) : ℝ :=
  (42300000000000 * a * dv - 9261167000000 * a -
      58327921200000 * dv - 11577976500000 * sv +
      23564391505003) / 5000000000000000

private def v4Slopesv : ℝ :=
  5891735621 / 15625000000000

private def v4Slopedv (a : ℝ) : ℝ :=
  3 * (1285394000 * a - 2130626051) / 500000000000

private def v4Slopev4 (a : ℝ) : ℝ :=
  (15251269000000 * a - 29688673463861) / 20000000000000000

private def v4Slopea : ℝ :=
  2056491309 / 50000000000000

set_option maxHeartbeats 3000000 in
private theorem alternatingV4Slope_telescope
    (X R C D F a x r c d f su du u4 sv dv v4 : ℝ) :
    alternatingV4Slope X R C D F a x r c d f
        su du u4 sv dv v4 (-2 / 1000) -
      alternatingV4Slope
        (1981 / 50000) (242817 / 1000000) (671 / 50000)
        (42817 / 1000000) 0 (165293 / 200000)
        (39761 / 1000000) (57183 / 1000000) (5179 / 1000000)
        (27183 / 1000000) 0 (7021 / 12500) (423 / 25000)
        (18 / 125) (13459 / 25000) (111 / 2000) (-1 / 250)
        (-2 / 1000) =
      (X - 1981 / 50000) *
          v4SlopeX X R D a x r d su du u4 sv dv v4 +
        (R - 242817 / 1000000) *
          v4SlopeR C a x r c su du u4 sv dv v4 +
        (C - 671 / 50000) * v4SlopeC a r su du u4 sv dv v4 +
        (D - 42817 / 1000000) * v4SlopeD a x su du u4 sv dv v4 +
        (x - 39761 / 1000000) * v4Slopex x a r d su du u4 sv dv v4 +
        (r - 57183 / 1000000) * v4Sloper c su du u4 sv dv v4 +
        (c - 5179 / 1000000) * v4Slopec a su du u4 sv dv v4 +
        (d - 27183 / 1000000) * v4Sloped a su du u4 sv dv v4 +
        (su - 7021 / 12500) * v4Slopesu su du u4 sv dv v4 +
        (du - 423 / 25000) * v4Slopedu a du u4 sv dv v4 +
        (u4 - 18 / 125) * v4Slopeu4 a sv dv +
        (sv - 13459 / 25000) * v4Slopesv +
        (dv - 111 / 2000) * v4Slopedv a +
        (v4 - (-1 / 250)) * v4Slopev4 a +
        (a - 165293 / 200000) * v4Slopea := by
  unfold alternatingV4Slope alternatingV4Coupling alternatingV4Cross
    adjugateRowFour mixedAdjugateRowFour crossGradientS crossGradientD
    v4SlopeX v4SlopeR v4SlopeC v4SlopeD v4Slopex v4Sloper
    v4Slopec v4Sloped v4Slopesu v4Slopedu v4Slopeu4 v4Slopesv
    v4Slopedv v4Slopev4 v4Slopea
  unfold v4WmS v4WmD v4Wm4 v4WpS v4WpD v4Wp4 v4Zs v4Zd v4Zc
  dsimp only
  ring_nf

private theorem v4_nonnegative_product_lower
    (p q pL qL : ℝ) (hp : pL ≤ p) (hq : qL ≤ q)
    (hpL : 0 ≤ pL) (hq0 : 0 ≤ q) :
    pL * qL ≤ p * q := by
  have h1 := mul_nonneg (sub_nonneg.mpr hp) hq0
  have h2 := mul_nonneg hpL (sub_nonneg.mpr hq)
  nlinarith only [h1, h2]

private theorem v4_nonnegative_product_upper
    (p q pU qU : ℝ) (hp : p ≤ pU) (hq : q ≤ qU)
    (hpU : 0 ≤ pU) (hq0 : 0 ≤ q) :
    p * q ≤ pU * qU := by
  have h1 := mul_nonneg (sub_nonneg.mpr hp) hq0
  have h2 := mul_nonneg hpU (sub_nonneg.mpr hq)
  nlinarith only [h1, h2]

private theorem v4_positive_negative_product_lower
    (p q pU qL : ℝ) (hp0 : 0 ≤ p) (hq : qL ≤ q)
    (hqL : qL ≤ 0) (hp : p ≤ pU) :
    pU * qL ≤ p * q := by
  have h1 := mul_nonneg hp0 (sub_nonneg.mpr hq)
  have h2 := mul_nonneg_of_nonpos_of_nonpos hqL (sub_nonpos.mpr hp)
  nlinarith only [h1, h2]

private theorem v4_positive_negative_product_upper
    (p q pL qU : ℝ) (hp : pL ≤ p) (hq0 : q ≤ 0)
    (hpL : 0 ≤ pL) (hq : q ≤ qU) :
    p * q ≤ pL * qU := by
  have h1 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hp) hq0
  have h2 := mul_nonpos_of_nonneg_of_nonpos hpL (sub_nonpos.mpr hq)
  nlinarith only [h1, h2]

private theorem v4_lower_times_negative_product_upper
    (p q pL qL : ℝ) (hp : pL ≤ p) (hq : qL ≤ q)
    (hpL : pL ≤ 0) (hq0 : q ≤ 0) :
    p * q ≤ pL * qL := by
  have h1 := mul_nonneg (sub_nonneg.mpr hp) (neg_nonneg.mpr hq0)
  have h2 := mul_nonpos_of_nonpos_of_nonneg hpL (sub_nonneg.mpr hq)
  nlinarith only [h1, h2]

set_option maxHeartbeats 3000000 in
private theorem v4SlopeX_nonpos
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    v4SlopeX X R D a x r d su du u4 sv dv v4 ≤ (-19 / 10000 : ℝ) := by
  rcases hbox.X_mem with ⟨hXL, hXU⟩
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.a_mem with ⟨haL, haU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.su_mem with ⟨hsuL, hsuU⟩
  rcases hbox.du_mem with ⟨hduL, hduU⟩
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  rcases hbox.sv_mem with ⟨hsvL, hsvU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  rcases hbox.v4_mem with ⟨hv4L, hv4U⟩
  have hwmSL : (3665011 / 125000000 : ℝ) ≤ v4WmS su sv := by
    unfold v4WmS
    bound
  have hwmSU : v4WmS su sv ≤ (14682473 / 500000000 : ℝ) := by
    unfold v4WmS
    bound
  have hwmDL : (-1402709 / 250000000 : ℝ) ≤ v4WmD du dv := by
    unfold v4WmD
    bound
  have hwmDU : v4WmD du dv ≤ (-1387809 / 250000000 : ℝ) := by
    unfold v4WmD
    bound
  have hwm4L : (37281 / 1250000 : ℝ) ≤ v4Wm4 u4 v4 := by
    unfold v4Wm4
    bound
  have hwm4U : v4Wm4 u4 v4 ≤ (153081 / 5000000 : ℝ) := by
    unfold v4Wm4
    bound
  have hwpSL : (516971 / 125000000 : ℝ) ≤ v4WpS su sv := by
    unfold v4WpS
    bound
  have hwpSU : v4WpS su sv ≤ (2092803 / 500000000 : ℝ) := by
    unfold v4WpS
    bound
  have hwpDL : (-233653 / 31250000 : ℝ) ≤ v4WpD du dv := by
    unfold v4WpD
    bound
  have hwpDU : v4WpD du dv ≤ (-1852449 / 250000000 : ℝ) := by
    unfold v4WpD
    bound
  have hwp4L : (68357 / 2500000 : ℝ) ≤ v4Wp4 u4 v4 := by
    unfold v4Wp4
    bound
  have hwp4U : v4Wp4 u4 v4 ≤ (140541 / 5000000 : ℝ) := by
    unfold v4Wp4
    bound
  let nvbar := -((v4 + (-2 / 1000)) / 2)
  have hnvbarL : (1 / 500 : ℝ) ≤ nvbar := by
    dsimp [nvbar]
    nlinarith only [hv4U]
  have hnvbarU : nvbar ≤ (3 / 1000 : ℝ) := by
    dsimp [nvbar]
    nlinarith only [hv4L]
  have hu4dvL : (141 / 1000 : ℝ) * (555 / 10000) ≤ u4 * dv :=
    v4_nonnegative_product_lower u4 dv (141 / 1000) (555 / 10000)
      hu4L hdvL (by norm_num) (by nlinarith only [hdvL])
  have hu4dvU : u4 * dv ≤ (144 / 1000 : ℝ) * (558 / 10000) :=
    v4_nonnegative_product_upper u4 dv (144 / 1000) (558 / 10000)
      hu4U hdvU (by norm_num) (by nlinarith only [hdvL])
  have hnvduL : (1 / 500 : ℝ) * (1687 / 100000) ≤ nvbar * du :=
    v4_nonnegative_product_lower nvbar du (1 / 500) (1687 / 100000)
      hnvbarL hduL (by norm_num) (by nlinarith only [hduL])
  have hnvduU : nvbar * du ≤ (3 / 1000 : ℝ) * (1692 / 100000) :=
    v4_nonnegative_product_upper nvbar du (3 / 1000) (1692 / 100000)
      hnvbarU hduU (by norm_num) (by nlinarith only [hduL])
  have hzsL : (196481 / 25000000 : ℝ) ≤ v4Zs du u4 dv v4 := by
    unfold v4Zs
    dsimp [nvbar] at hnvduL
    nlinarith only [hu4dvL, hnvduL]
  have hzsU : v4Zs du u4 dv v4 ≤ (202149 / 25000000 : ℝ) := by
    unfold v4Zs
    dsimp [nvbar] at hnvduU
    nlinarith only [hu4dvU, hnvduU]
  have hnvsuL : (1 / 500 : ℝ) * (56168 / 100000) ≤ nvbar * su :=
    v4_nonnegative_product_lower nvbar su (1 / 500) (56168 / 100000)
      hnvbarL hsuL (by norm_num) (by nlinarith only [hsuL])
  have hnvsuU : nvbar * su ≤ (3 / 1000 : ℝ) * (56173 / 100000) :=
    v4_nonnegative_product_upper nvbar su (3 / 1000) (56173 / 100000)
      hnvbarU hsuU (by norm_num) (by nlinarith only [hsuL])
  have hu4svL : (141 / 1000 : ℝ) * (53815 / 100000) ≤ u4 * sv :=
    v4_nonnegative_product_lower u4 sv (141 / 1000) (53815 / 100000)
      hu4L hsvL (by norm_num) (by nlinarith only [hsvL])
  have hu4svU : u4 * sv ≤ (144 / 1000 : ℝ) * (53836 / 100000) :=
    v4_nonnegative_product_upper u4 sv (144 / 1000) (53836 / 100000)
      hu4U hsvU (by norm_num) (by nlinarith only [hsvL])
  have hzdL : (-7920903 / 100000000 : ℝ) ≤ v4Zd su u4 sv v4 := by
    unfold v4Zd
    dsimp [nvbar] at hnvsuU
    nlinarith only [hnvsuU, hu4svU]
  have hzdU : v4Zd su u4 sv v4 ≤ (-7700251 / 100000000 : ℝ) := by
    unfold v4Zd
    dsimp [nvbar] at hnvsuL
    nlinarith only [hnvsuL, hu4svL]
  have hDpL : (15634 / 1000000 : ℝ) ≤ D - d := by
    nlinarith only [hDL, hdU]
  have hRpL : (185634 / 1000000 : ℝ) ≤ R - r := by
    nlinarith only [hRL, hrU]
  have hXpL : (-141 / 1000000 : ℝ) ≤
      (X + 1981 / 50000) / 2 - x := by
    nlinarith only [hXL, hxU]
  have hXbarL : (1981 / 50000 : ℝ) ≤
      (X + 1981 / 50000) / 2 := by
    nlinarith only [hXL]
  have hT1 : -(D - d) * v4WmS su sv ≤
      -(15634 / 1000000 : ℝ) * (3665011 / 125000000) := by
    have hp := v4_nonnegative_product_lower
      (D - d) (v4WmS su sv)
      (15634 / 1000000) (3665011 / 125000000)
      hDpL hwmSL (by norm_num) (by nlinarith only [hwmSL])
    nlinarith only [hp]
  have hT2 : (R - r) * v4WmD du dv ≤
      (185634 / 1000000 : ℝ) * (-1387809 / 250000000) :=
    v4_positive_negative_product_upper
      (R - r) (v4WmD du dv)
      (185634 / 1000000) (-1387809 / 250000000)
      hRpL (by nlinarith only [hwmDU]) (by norm_num) hwmDU
  have hT3 : -2 * ((X + 1981 / 50000) / 2 - x) * v4Wm4 u4 v4 ≤
      -2 * (-141 / 1000000 : ℝ) * (153081 / 5000000) := by
    have hp := v4_positive_negative_product_lower
      (v4Wm4 u4 v4) ((X + 1981 / 50000) / 2 - x)
      (153081 / 5000000) (-141 / 1000000)
      (by nlinarith only [hwm4L]) hXpL (by norm_num) hwm4U
    nlinarith only [hp]
  have hT4 : -2 * D * v4WpS su sv ≤
      -2 * (42817 / 1000000 : ℝ) * (516971 / 125000000) := by
    have hp := v4_nonnegative_product_lower
      D (v4WpS su sv) (42817 / 1000000) (516971 / 125000000)
      hDL hwpSL (by norm_num) (by nlinarith only [hwpSL])
    nlinarith only [hp]
  have hT5 : 2 * R * v4WpD du dv ≤
      2 * (242817 / 1000000 : ℝ) * (-1852449 / 250000000) := by
    have hp := v4_positive_negative_product_upper
      R (v4WpD du dv) (242817 / 1000000) (-1852449 / 250000000)
      hRL (by nlinarith only [hwpDU]) (by norm_num) hwpDU
    nlinarith only [hp]
  have hT6 : -4 * ((X + 1981 / 50000) / 2) * v4Wp4 u4 v4 ≤
      -4 * (1981 / 50000 : ℝ) * (68357 / 2500000) := by
    have hp := v4_nonnegative_product_lower
      ((X + 1981 / 50000) / 2) (v4Wp4 u4 v4)
      (1981 / 50000) (68357 / 2500000)
      hXbarL hwp4L (by norm_num) (by nlinarith only [hwp4L])
    nlinarith only [hp]
  have hT7 : -du * v4Zd su u4 sv v4 ≤
      -(1692 / 100000 : ℝ) * (-7920903 / 100000000) := by
    have hp := v4_positive_negative_product_lower
      du (v4Zd su u4 sv v4)
      (1692 / 100000) (-7920903 / 100000000)
      (by nlinarith only [hduL]) hzdL (by norm_num) hduU
    nlinarith only [hp]
  have hT8 : su * v4Zs du u4 dv v4 ≤
      (56173 / 100000 : ℝ) * (202149 / 25000000) :=
    v4_nonnegative_product_upper
      su (v4Zs du u4 dv v4)
      (56173 / 100000) (202149 / 25000000)
      hsuU hzsU (by norm_num) (by nlinarith only [hzsL])
  unfold v4SlopeX
  dsimp only
  nlinarith only [hT1, hT2, hT3, hT4, hT5, hT6, hT7, hT8]

set_option maxHeartbeats 3000000 in
private theorem v4RemainingGeometrySlopeSigns
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    v4SlopeR C a x r c su du u4 sv dv v4 ≤ (-24 / 100000 : ℝ) ∧
      (19 / 1000 : ℝ) ≤ v4SlopeC a r su du u4 sv dv v4 ∧
      v4SlopeD a x su du u4 sv dv v4 ≤ (-56 / 10000 : ℝ) ∧
      (3 / 10000 : ℝ) ≤ v4Slopex x a r d su du u4 sv dv v4 ∧
      (2 / 10000 : ℝ) ≤ v4Sloper c su du u4 sv dv v4 ∧
      v4Slopec a su du u4 sv dv v4 ≤ (-53 / 10000 : ℝ) ∧
      (15 / 10000 : ℝ) ≤ v4Sloped a su du u4 sv dv v4 := by
  rcases hbox.C_mem with ⟨hCL, hCU⟩
  rcases hbox.a_mem with ⟨haL, haU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.su_mem with ⟨hsuL, hsuU⟩
  rcases hbox.du_mem with ⟨hduL, hduU⟩
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  rcases hbox.sv_mem with ⟨hsvL, hsvU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  rcases hbox.v4_mem with ⟨hv4L, hv4U⟩
  have hwmSL : (3665011 / 125000000 : ℝ) ≤ v4WmS su sv := by
    unfold v4WmS
    bound
  have hwmSU : v4WmS su sv ≤ (14682473 / 500000000 : ℝ) := by
    unfold v4WmS
    bound
  have hwmDL : (-1402709 / 250000000 : ℝ) ≤ v4WmD du dv := by
    unfold v4WmD
    bound
  have hwmDU : v4WmD du dv ≤ (-1387809 / 250000000 : ℝ) := by
    unfold v4WmD
    bound
  have hwm4L : (37281 / 1250000 : ℝ) ≤ v4Wm4 u4 v4 := by
    unfold v4Wm4
    bound
  have hwm4U : v4Wm4 u4 v4 ≤ (153081 / 5000000 : ℝ) := by
    unfold v4Wm4
    bound
  have hwpSL : (516971 / 125000000 : ℝ) ≤ v4WpS su sv := by
    unfold v4WpS
    bound
  have hwpSU : v4WpS su sv ≤ (2092803 / 500000000 : ℝ) := by
    unfold v4WpS
    bound
  have hwpDL : (-233653 / 31250000 : ℝ) ≤ v4WpD du dv := by
    unfold v4WpD
    bound
  have hwpDU : v4WpD du dv ≤ (-1852449 / 250000000 : ℝ) := by
    unfold v4WpD
    bound
  have hwp4L : (68357 / 2500000 : ℝ) ≤ v4Wp4 u4 v4 := by
    unfold v4Wp4
    bound
  have hwp4U : v4Wp4 u4 v4 ≤ (140541 / 5000000 : ℝ) := by
    unfold v4Wp4
    bound
  let nvbar := -((v4 + (-2 / 1000)) / 2)
  have hnvbarL : (1 / 500 : ℝ) ≤ nvbar := by
    dsimp [nvbar]
    nlinarith only [hv4U]
  have hnvbarU : nvbar ≤ (3 / 1000 : ℝ) := by
    dsimp [nvbar]
    nlinarith only [hv4L]
  have hu4dvL : (141 / 1000 : ℝ) * (555 / 10000) ≤ u4 * dv :=
    v4_nonnegative_product_lower u4 dv (141 / 1000) (555 / 10000)
      hu4L hdvL (by norm_num) (by nlinarith only [hdvL])
  have hu4dvU : u4 * dv ≤ (144 / 1000 : ℝ) * (558 / 10000) :=
    v4_nonnegative_product_upper u4 dv (144 / 1000) (558 / 10000)
      hu4U hdvU (by norm_num) (by nlinarith only [hdvL])
  have hnvduL : (1 / 500 : ℝ) * (1687 / 100000) ≤ nvbar * du :=
    v4_nonnegative_product_lower nvbar du (1 / 500) (1687 / 100000)
      hnvbarL hduL (by norm_num) (by nlinarith only [hduL])
  have hnvduU : nvbar * du ≤ (3 / 1000 : ℝ) * (1692 / 100000) :=
    v4_nonnegative_product_upper nvbar du (3 / 1000) (1692 / 100000)
      hnvbarU hduU (by norm_num) (by nlinarith only [hduL])
  have hzsL : (196481 / 25000000 : ℝ) ≤ v4Zs du u4 dv v4 := by
    unfold v4Zs
    dsimp [nvbar] at hnvduL
    nlinarith only [hu4dvL, hnvduL]
  have hzsU : v4Zs du u4 dv v4 ≤ (202149 / 25000000 : ℝ) := by
    unfold v4Zs
    dsimp [nvbar] at hnvduU
    nlinarith only [hu4dvU, hnvduU]
  have hnvsuL : (1 / 500 : ℝ) * (56168 / 100000) ≤ nvbar * su :=
    v4_nonnegative_product_lower nvbar su (1 / 500) (56168 / 100000)
      hnvbarL hsuL (by norm_num) (by nlinarith only [hsuL])
  have hnvsuU : nvbar * su ≤ (3 / 1000 : ℝ) * (56173 / 100000) :=
    v4_nonnegative_product_upper nvbar su (3 / 1000) (56173 / 100000)
      hnvbarU hsuU (by norm_num) (by nlinarith only [hsuL])
  have hu4svL : (141 / 1000 : ℝ) * (53815 / 100000) ≤ u4 * sv :=
    v4_nonnegative_product_lower u4 sv (141 / 1000) (53815 / 100000)
      hu4L hsvL (by norm_num) (by nlinarith only [hsvL])
  have hu4svU : u4 * sv ≤ (144 / 1000 : ℝ) * (53836 / 100000) :=
    v4_nonnegative_product_upper u4 sv (144 / 1000) (53836 / 100000)
      hu4U hsvU (by norm_num) (by nlinarith only [hsvL])
  have hzdL : (-7920903 / 100000000 : ℝ) ≤ v4Zd su u4 sv v4 := by
    unfold v4Zd
    dsimp [nvbar] at hnvsuU
    nlinarith only [hnvsuU, hu4svU]
  have hzdU : v4Zd su u4 sv v4 ≤ (-7700251 / 100000000 : ℝ) := by
    unfold v4Zd
    dsimp [nvbar] at hnvsuL
    nlinarith only [hnvsuL, hu4svL]
  have hdusvL : (1687 / 100000 : ℝ) * (53815 / 100000) ≤ du * sv :=
    v4_nonnegative_product_lower du sv (1687 / 100000) (53815 / 100000)
      hduL hsvL (by norm_num) (by nlinarith only [hsvL])
  have hdusvU : du * sv ≤ (1692 / 100000 : ℝ) * (53836 / 100000) :=
    v4_nonnegative_product_upper du sv (1692 / 100000) (53836 / 100000)
      hduU hsvU (by norm_num) (by nlinarith only [hsvL])
  have hsudvL : (56168 / 100000 : ℝ) * (555 / 10000) ≤ su * dv :=
    v4_nonnegative_product_lower su dv (56168 / 100000) (555 / 10000)
      hsuL hdvL (by norm_num) (by nlinarith only [hdvL])
  have hsudvU : su * dv ≤ (56173 / 100000 : ℝ) * (558 / 10000) :=
    v4_nonnegative_product_upper su dv (56173 / 100000) (558 / 10000)
      hsuU hdvU (by norm_num) (by nlinarith only [hdvL])
  have hzcL : (-44531887 / 4000000000 : ℝ) ≤ v4Zc su du sv dv := by
    unfold v4Zc
    nlinarith only [hdusvL, hsudvU]
  have hzcU : v4Zc su du sv dv ≤ (-6895059 / 625000000 : ℝ) := by
    unfold v4Zc
    nlinarith only [hdusvU, hsudvL]
  constructor
  · have hCpL : (6065 / 1000000 : ℝ) ≤ C - c := by
      nlinarith only [hCL, hcU]
    have hXpL : (-141 / 1000000 : ℝ) ≤ (1981 / 50000 : ℝ) - x := by
      nlinarith only [hxU]
    have hT1 : -(C - c) * v4WmS su sv ≤
        -(6065 / 1000000 : ℝ) * (3665011 / 125000000) := by
      have hp := v4_nonnegative_product_lower
        (C - c) (v4WmS su sv) (6065 / 1000000) (3665011 / 125000000)
        hCpL hwmSL (by norm_num) (by nlinarith only [hwmSL])
      nlinarith only [hp]
    have hT2 : ((1981 / 50000 : ℝ) - x) * v4WmD du dv ≤
        (-141 / 1000000 : ℝ) * (-1402709 / 250000000) :=
      v4_lower_times_negative_product_upper
        ((1981 / 50000 : ℝ) - x) (v4WmD du dv)
        (-141 / 1000000) (-1402709 / 250000000)
        hXpL hwmDL (by norm_num) (by nlinarith only [hwmDU])
    have hT3 : -2 * C * v4WpS su sv ≤
        -2 * (1323 / 100000 : ℝ) * (516971 / 125000000) := by
      have hp := v4_nonnegative_product_lower
        C (v4WpS su sv) (1323 / 100000) (516971 / 125000000)
        hCL hwpSL (by norm_num) (by nlinarith only [hwpSL])
      nlinarith only [hp]
    have hT4 : 2 * (1981 / 50000 : ℝ) * v4WpD du dv ≤
        2 * (1981 / 50000 : ℝ) * (-1852449 / 250000000) := by
      nlinarith only [hwpDU]
    have hT5 : -du * v4Zc su du sv dv ≤
        -(1692 / 100000 : ℝ) * (-44531887 / 4000000000) := by
      have hp := v4_positive_negative_product_lower
        du (v4Zc su du sv dv) (1692 / 100000) (-44531887 / 4000000000)
        (by nlinarith only [hduL]) hzcL (by norm_num) hduU
      nlinarith only [hp]
    unfold v4SlopeR
    dsimp only
    nlinarith only [hT1, hT2, hT3, hT4, hT5]
  constructor
  · have hRpU : (242817 / 1000000 : ℝ) - r ≤ (193 / 1000 : ℝ) := by
      nlinarith only [hrL]
    have hApL : (547765 / 1000000 : ℝ) ≤ (137423 / 100000 : ℝ) - a := by
      nlinarith only [haU]
    have hT1 : -(193 / 1000 : ℝ) * (14682473 / 500000000) ≤
        -((242817 / 1000000 : ℝ) - r) * v4WmS su sv := by
      have hp := v4_nonnegative_product_upper
        ((242817 / 1000000 : ℝ) - r) (v4WmS su sv)
        (193 / 1000) (14682473 / 500000000)
        hRpU hwmSU (by norm_num) (by nlinarith only [hwmSL])
      nlinarith only [hp]
    have hT2 : (547765 / 1000000 : ℝ) * (37281 / 1250000) ≤
        ((137423 / 100000 : ℝ) - a) * v4Wm4 u4 v4 :=
      v4_nonnegative_product_lower
        ((137423 / 100000 : ℝ) - a) (v4Wm4 u4 v4)
        (547765 / 1000000) (37281 / 1250000)
        hApL hwm4L (by norm_num) (by nlinarith only [hwm4L])
    have hT3 : -2 * (242817 / 1000000 : ℝ) * (2092803 / 500000000) ≤
        -2 * (242817 / 1000000 : ℝ) * v4WpS su sv := by
      nlinarith only [hwpSU]
    have hT4 : 2 * (137423 / 100000 : ℝ) * (68357 / 2500000) ≤
        2 * (137423 / 100000 : ℝ) * v4Wp4 u4 v4 := by
      nlinarith only [hwp4L]
    have hT5 : (56173 / 100000 : ℝ) * (-7920903 / 100000000) ≤
        su * v4Zd su u4 sv v4 :=
      v4_positive_negative_product_lower
        su (v4Zd su u4 sv v4) (56173 / 100000) (-7920903 / 100000000)
        (by nlinarith only [hsuL]) hzdL (by norm_num) hsuU
    unfold v4SlopeC
    dsimp only
    nlinarith only [hT1, hT2, hT3, hT4, hT5]
  constructor
  · have hXpL : (-141 / 1000000 : ℝ) ≤ (1981 / 50000 : ℝ) - x := by
      nlinarith only [hxU]
    have hApL : (547765 / 1000000 : ℝ) ≤ (137423 / 100000 : ℝ) - a := by
      nlinarith only [haU]
    have hT1 : -((1981 / 50000 : ℝ) - x) * v4WmS su sv ≤
        -(-141 / 1000000 : ℝ) * (14682473 / 500000000) := by
      have hp := v4_positive_negative_product_lower
        (v4WmS su sv) ((1981 / 50000 : ℝ) - x)
        (14682473 / 500000000) (-141 / 1000000)
        (by nlinarith only [hwmSL]) hXpL (by norm_num) hwmSU
      nlinarith only [hp]
    have hT2 : ((137423 / 100000 : ℝ) - a) * v4WmD du dv ≤
        (547765 / 1000000 : ℝ) * (-1387809 / 250000000) :=
      v4_positive_negative_product_upper
        ((137423 / 100000 : ℝ) - a) (v4WmD du dv)
        (547765 / 1000000) (-1387809 / 250000000)
        hApL (by nlinarith only [hwmDU]) (by norm_num) hwmDU
    have hT3 : -2 * (1981 / 50000 : ℝ) * v4WpS su sv ≤
        -2 * (1981 / 50000 : ℝ) * (516971 / 125000000) := by
      nlinarith only [hwpSL]
    have hT4 : 2 * (137423 / 100000 : ℝ) * v4WpD du dv ≤
        2 * (137423 / 100000 : ℝ) * (-1852449 / 250000000) := by
      nlinarith only [hwpDU]
    have hT5 : -su * v4Zc su du sv dv ≤
        -(56173 / 100000 : ℝ) * (-44531887 / 4000000000) := by
      have hp := v4_positive_negative_product_lower
        su (v4Zc su du sv dv) (56173 / 100000) (-44531887 / 4000000000)
        (by nlinarith only [hsuL]) hzcL (by norm_num) hsuU
      nlinarith only [hp]
    unfold v4SlopeD
    dsimp only
    nlinarith only [hT1, hT2, hT3, hT4, hT5]
  constructor
  · have hDpL : (15634 / 1000000 : ℝ) ≤ (42817 / 1000000 : ℝ) - d := by
      nlinarith only [hdU]
    have hRpL : (185634 / 1000000 : ℝ) ≤ (242817 / 1000000 : ℝ) - r := by
      nlinarith only [hrU]
    have hXpL : (-141 / 1000000 : ℝ) ≤
        (1981 / 50000 : ℝ) - (x + 39761 / 1000000) / 2 := by
      nlinarith only [hxU]
    have hxbarL : (19403 / 500000 : ℝ) ≤ (x + 39761 / 1000000) / 2 := by
      nlinarith only [hxL]
    have hT1 : (15634 / 1000000 : ℝ) * (3665011 / 125000000) ≤
        ((42817 / 1000000 : ℝ) - d) * v4WmS su sv :=
      v4_nonnegative_product_lower
        ((42817 / 1000000 : ℝ) - d) (v4WmS su sv)
        (15634 / 1000000) (3665011 / 125000000)
        hDpL hwmSL (by norm_num) (by nlinarith only [hwmSL])
    have hT2 : -(185634 / 1000000 : ℝ) * (-1387809 / 250000000) ≤
        -((242817 / 1000000 : ℝ) - r) * v4WmD du dv := by
      have hp := v4_positive_negative_product_upper
        ((242817 / 1000000 : ℝ) - r) (v4WmD du dv)
        (185634 / 1000000) (-1387809 / 250000000)
        hRpL (by nlinarith only [hwmDU]) (by norm_num) hwmDU
      nlinarith only [hp]
    have hT3 : 2 * (-141 / 1000000 : ℝ) * (153081 / 5000000) ≤
        2 * ((1981 / 50000 : ℝ) - (x + 39761 / 1000000) / 2) *
          v4Wm4 u4 v4 := by
      have hp := v4_positive_negative_product_lower
        (v4Wm4 u4 v4)
        ((1981 / 50000 : ℝ) - (x + 39761 / 1000000) / 2)
        (153081 / 5000000) (-141 / 1000000)
        (by nlinarith only [hwm4L]) hXpL (by norm_num) hwm4U
      nlinarith only [hp]
    have hT4 : 2 * (23317 / 1000000 : ℝ) * (516971 / 125000000) ≤
        2 * d * v4WpS su sv := by
      have hp := v4_nonnegative_product_lower
        d (v4WpS su sv) (23317 / 1000000) (516971 / 125000000)
        hdL hwpSL (by norm_num) (by nlinarith only [hwpSL])
      nlinarith only [hp]
    have hT5 : -2 * (49817 / 1000000 : ℝ) * (-1852449 / 250000000) ≤
        -2 * r * v4WpD du dv := by
      have hp := v4_positive_negative_product_upper
        r (v4WpD du dv) (49817 / 1000000) (-1852449 / 250000000)
        hrL (by nlinarith only [hwpDU]) (by norm_num) hwpDU
      nlinarith only [hp]
    have hT6 : 4 * (19403 / 500000 : ℝ) * (68357 / 2500000) ≤
        4 * ((x + 39761 / 1000000) / 2) * v4Wp4 u4 v4 := by
      have hp := v4_nonnegative_product_lower
        ((x + 39761 / 1000000) / 2) (v4Wp4 u4 v4)
        (19403 / 500000) (68357 / 2500000)
        hxbarL hwp4L (by norm_num) (by nlinarith only [hwp4L])
      nlinarith only [hp]
    have hT7 : (1692 / 100000 : ℝ) * (-7920903 / 100000000) ≤
        du * v4Zd su u4 sv v4 :=
      v4_positive_negative_product_lower
        du (v4Zd su u4 sv v4) (1692 / 100000) (-7920903 / 100000000)
        (by nlinarith only [hduL]) hzdL (by norm_num) hduU
    have hT8 : -(56173 / 100000 : ℝ) * (202149 / 25000000) ≤
        -su * v4Zs du u4 dv v4 := by
      have hp := v4_nonnegative_product_upper
        su (v4Zs du u4 dv v4) (56173 / 100000) (202149 / 25000000)
        hsuU hzsU (by norm_num) (by nlinarith only [hzsL])
      nlinarith only [hp]
    unfold v4Slopex
    dsimp only
    nlinarith only [hT1, hT2, hT3, hT4, hT5, hT6, hT7, hT8]
  constructor
  · have hCpL : (6255 / 1000000 : ℝ) ≤ (671 / 50000 : ℝ) - c := by
      nlinarith only [hcU]
    have hT1 : (6255 / 1000000 : ℝ) * (3665011 / 125000000) ≤
        ((671 / 50000 : ℝ) - c) * v4WmS su sv :=
      v4_nonnegative_product_lower
        ((671 / 50000 : ℝ) - c) (v4WmS su sv)
        (6255 / 1000000) (3665011 / 125000000)
        hCpL hwmSL (by norm_num) (by nlinarith only [hwmSL])
    have hT2 : -(-141 / 1000000 : ℝ) * (-1402709 / 250000000) ≤
        -(-141 / 1000000 : ℝ) * v4WmD du dv := by
      have hp := v4_lower_times_negative_product_upper
        (-141 / 1000000 : ℝ) (v4WmD du dv)
        (-141 / 1000000) (-1402709 / 250000000)
        (by norm_num) hwmDL (by norm_num) (by nlinarith only [hwmDU])
      nlinarith only [hp]
    have hT3 : 2 * (5179 / 1000000 : ℝ) * (516971 / 125000000) ≤
        2 * c * v4WpS su sv := by
      have hp := v4_nonnegative_product_lower
        c (v4WpS su sv) (5179 / 1000000) (516971 / 125000000)
        hcL hwpSL (by norm_num) (by nlinarith only [hwpSL])
      nlinarith only [hp]
    have hT4 : -2 * (39761 / 1000000 : ℝ) * (-1852449 / 250000000) ≤
        -2 * (39761 / 1000000 : ℝ) * v4WpD du dv := by
      nlinarith only [hwpDU]
    have hT5 : (1692 / 100000 : ℝ) * (-44531887 / 4000000000) ≤
        du * v4Zc su du sv dv :=
      v4_positive_negative_product_lower
        du (v4Zc su du sv dv) (1692 / 100000) (-44531887 / 4000000000)
        (by nlinarith only [hduL]) hzcL (by norm_num) hduU
    unfold v4Sloper
    dsimp only
    nlinarith only [hT1, hT2, hT3, hT4, hT5]
  constructor
  · have hApL : (547765 / 1000000 : ℝ) ≤ (137423 / 100000 : ℝ) - a := by
      nlinarith only [haU]
    have hT1 : (185634 / 1000000 : ℝ) * v4WmS su sv ≤
        (185634 / 1000000 : ℝ) * (14682473 / 500000000) := by
      nlinarith only [hwmSU]
    have hT2 : -((137423 / 100000 : ℝ) - a) * v4Wm4 u4 v4 ≤
        -(547765 / 1000000 : ℝ) * (37281 / 1250000) := by
      have hp := v4_nonnegative_product_lower
        ((137423 / 100000 : ℝ) - a) (v4Wm4 u4 v4)
        (547765 / 1000000) (37281 / 1250000)
        hApL hwm4L (by norm_num) (by nlinarith only [hwm4L])
      nlinarith only [hp]
    have hT3 : 2 * (57183 / 1000000 : ℝ) * v4WpS su sv ≤
        2 * (57183 / 1000000 : ℝ) * (2092803 / 500000000) := by
      nlinarith only [hwpSU]
    have hT4 : -2 * a * v4Wp4 u4 v4 ≤
        -2 * (824479 / 1000000 : ℝ) * (68357 / 2500000) := by
      have hp := v4_nonnegative_product_lower
        a (v4Wp4 u4 v4) (824479 / 1000000) (68357 / 2500000)
        haL hwp4L (by norm_num) (by nlinarith only [hwp4L])
      nlinarith only [hp]
    have hT5 : -su * v4Zd su u4 sv v4 ≤
        -(56173 / 100000 : ℝ) * (-7920903 / 100000000) := by
      have hp := v4_positive_negative_product_lower
        su (v4Zd su u4 sv v4) (56173 / 100000) (-7920903 / 100000000)
        (by nlinarith only [hsuL]) hzdL (by norm_num) hsuU
      nlinarith only [hp]
    unfold v4Slopec
    dsimp only
    nlinarith only [hT1, hT2, hT3, hT4, hT5]
  · have hApL : (547765 / 1000000 : ℝ) ≤ (137423 / 100000 : ℝ) - a := by
      nlinarith only [haU]
    have hT1 : (-141 / 1000000 : ℝ) * (14682473 / 500000000) ≤
        (-141 / 1000000 : ℝ) * v4WmS su sv := by
      nlinarith only [hwmSU]
    have hT2 : -(547765 / 1000000 : ℝ) * (-1387809 / 250000000) ≤
        -((137423 / 100000 : ℝ) - a) * v4WmD du dv := by
      have hp := v4_positive_negative_product_upper
        ((137423 / 100000 : ℝ) - a) (v4WmD du dv)
        (547765 / 1000000) (-1387809 / 250000000)
        hApL (by nlinarith only [hwmDU]) (by norm_num) hwmDU
      nlinarith only [hp]
    have hT3 : 2 * (39761 / 1000000 : ℝ) * (516971 / 125000000) ≤
        2 * (39761 / 1000000 : ℝ) * v4WpS su sv := by
      nlinarith only [hwpSL]
    have hT4 : -2 * (824479 / 1000000 : ℝ) * (-1852449 / 250000000) ≤
        -2 * a * v4WpD du dv := by
      have hp := v4_positive_negative_product_upper
        a (v4WpD du dv) (824479 / 1000000) (-1852449 / 250000000)
        haL (by nlinarith only [hwpDU]) (by norm_num) hwpDU
      nlinarith only [hp]
    have hT5 : (56173 / 100000 : ℝ) * (-44531887 / 4000000000) ≤
        su * v4Zc su du sv dv :=
      v4_positive_negative_product_lower
        su (v4Zc su du sv dv) (56173 / 100000) (-44531887 / 4000000000)
        (by nlinarith only [hsuL]) hzcL (by norm_num) hsuU
    unfold v4Sloped
    dsimp only
    nlinarith only [hT1, hT2, hT3, hT4, hT5]

set_option maxHeartbeats 3000000 in
private theorem v4StateSlopeSigns
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    v4Slopesu su du u4 sv dv v4 ≤ (-6 / 10000 : ℝ) ∧
      (57 / 10000 : ℝ) ≤ v4Slopedu a du u4 sv dv v4 ∧
      (16 / 10000 : ℝ) ≤ v4Slopeu4 a sv dv ∧
      (0 : ℝ) ≤ v4Slopesv ∧
      v4Slopedv a ≤ 0 ∧ v4Slopev4 a ≤ 0 := by
  rcases hbox.a_mem with ⟨haL, haU⟩
  rcases hbox.su_mem with ⟨hsuL, hsuU⟩
  rcases hbox.du_mem with ⟨hduL, hduU⟩
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  rcases hbox.sv_mem with ⟨hsvL, hsvU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  rcases hbox.v4_mem with ⟨hv4L, hv4U⟩
  constructor
  · have hdudvU : du * dv ≤ (1692 / 100000 : ℝ) * (558 / 10000) :=
      v4_nonnegative_product_upper du dv (1692 / 100000) (558 / 10000)
        hduU hdvU (by norm_num) (by nlinarith only [hdvL])
    have hdusvL : (1687 / 100000 : ℝ) * (53815 / 100000) ≤ du * sv :=
      v4_nonnegative_product_lower du sv (1687 / 100000) (53815 / 100000)
        hduL hsvL (by norm_num) (by nlinarith only [hsvL])
    have hduv4U : du * v4 ≤ (1687 / 100000 : ℝ) * (-2 / 1000) :=
      v4_positive_negative_product_upper du v4
        (1687 / 100000) (-2 / 1000)
        hduL (by nlinarith only [hv4U]) (by norm_num) hv4U
    have hdvsuU : dv * su ≤ (558 / 10000 : ℝ) * (56173 / 100000) := by
      have hp := v4_nonnegative_product_upper dv su
        (558 / 10000) (56173 / 100000)
        hdvU hsuU (by norm_num) (by nlinarith only [hsuL])
      nlinarith only [hp]
    have hdvu4L : (555 / 10000 : ℝ) * (141 / 1000) ≤ dv * u4 :=
      v4_nonnegative_product_lower dv u4 (555 / 10000) (141 / 1000)
        hdvL hu4L (by norm_num) (by nlinarith only [hu4L])
    have hsuv4U : su * v4 ≤ (56168 / 100000 : ℝ) * (-2 / 1000) :=
      v4_positive_negative_product_upper su v4
        (56168 / 100000) (-2 / 1000)
        hsuL (by nlinarith only [hv4U]) (by norm_num) hv4U
    have hsvu4L : (53815 / 100000 : ℝ) * (141 / 1000) ≤ sv * u4 :=
      v4_nonnegative_product_lower sv u4 (53815 / 100000) (141 / 1000)
        hsvL hu4L (by norm_num) (by nlinarith only [hu4L])
    have hT1 : -2900531250000 * ((1692 / 100000 : ℝ) * (558 / 10000)) ≤
        -2900531250000 * du * dv := by
      nlinarith only [hdudvU]
    have hT2 : 244281250000 * ((1687 / 100000 : ℝ) * (53815 / 100000)) ≤
        244281250000 * du * sv := by
      nlinarith only [hdusvL]
    have hT3 : -2203125000 * ((1687 / 100000 : ℝ) * (-2 / 1000)) ≤
        -2203125000 * du * v4 := by
      nlinarith only [hduv4U]
    have hT4 : 4406250 * (1687 / 100000 : ℝ) ≤ 4406250 * du := by
      nlinarith only [hduL]
    have hT5 : -244281250000 * ((558 / 10000 : ℝ) * (56173 / 100000)) ≤
        -244281250000 * dv * su := by
      nlinarith only [hdvsuU]
    have hT6 : 2203125000 * ((555 / 10000 : ℝ) * (141 / 1000)) ≤
        2203125000 * dv * u4 := by
      nlinarith only [hdvu4L]
    have hT7 : -137207892500 * (558 / 10000 : ℝ) ≤
        -137207892500 * dv := by
      nlinarith only [hdvU]
    have hT8 : -64382812500 * ((56168 / 100000 : ℝ) * (-2 / 1000)) ≤
        -64382812500 * su * v4 := by
      nlinarith only [hsuv4U]
    have hT9 : 128765625 * (56168 / 100000 : ℝ) ≤
        128765625 * su := by
      nlinarith only [hsuL]
    have hT10 : 128765625000 * ((53815 / 100000 : ℝ) * (141 / 1000)) ≤
        128765625000 * sv * u4 := by
      nlinarith only [hsvu4L]
    have hT11 : -36162538125 * (-2 / 1000 : ℝ) ≤
        -36162538125 * v4 := by
      nlinarith only [hv4U]
    unfold v4Slopesu
    nlinarith only [hT1, hT2, hT3, hT4, hT5, hT6, hT7, hT8,
      hT9, hT10, hT11]
  constructor
  · have hnvL : (2 / 1000 : ℝ) ≤ -v4 := by
      nlinarith only [hv4U]
    have haduL : (824479 / 1000000 : ℝ) * (1687 / 100000) ≤ a * du :=
      v4_nonnegative_product_lower a du (824479 / 1000000) (1687 / 100000)
        haL hduL (by norm_num) (by nlinarith only [hduL])
    have haduNvL :
        ((824479 / 1000000 : ℝ) * (1687 / 100000)) * (2 / 1000) ≤
          (a * du) * (-v4) :=
      v4_nonnegative_product_lower (a * du) (-v4)
        ((824479 / 1000000) * (1687 / 100000)) (2 / 1000)
        haduL hnvL (by norm_num) (by nlinarith only [hnvL])
    have hadvL : (824479 / 1000000 : ℝ) * (555 / 10000) ≤ a * dv :=
      v4_nonnegative_product_lower a dv (824479 / 1000000) (555 / 10000)
        haL hdvL (by norm_num) (by nlinarith only [hdvL])
    have hadvu4L :
        ((824479 / 1000000 : ℝ) * (555 / 10000)) * (141 / 1000) ≤
          (a * dv) * u4 :=
      v4_nonnegative_product_lower (a * dv) u4
        ((824479 / 1000000) * (555 / 10000)) (141 / 1000)
        hadvL hu4L (by norm_num) (by nlinarith only [hu4L])
    have haNvL : (824479 / 1000000 : ℝ) * (2 / 1000) ≤ a * (-v4) :=
      v4_nonnegative_product_lower a (-v4) (824479 / 1000000) (2 / 1000)
        haL hnvL (by norm_num) (by nlinarith only [hnvL])
    have hdusvU : du * sv ≤ (1692 / 100000 : ℝ) * (53836 / 100000) :=
      v4_nonnegative_product_upper du sv (1692 / 100000) (53836 / 100000)
        hduU hsvU (by norm_num) (by nlinarith only [hsvL])
    have hduv4L : (1692 / 100000 : ℝ) * (-4 / 1000) ≤ du * v4 :=
      v4_positive_negative_product_lower du v4
        (1692 / 100000) (-4 / 1000)
        (by nlinarith only [hduL]) hv4L (by norm_num) hduU
    have hdvu4U : dv * u4 ≤ (558 / 10000 : ℝ) * (144 / 1000) :=
      v4_nonnegative_product_upper dv u4 (558 / 10000) (144 / 1000)
        hdvU hu4U (by norm_num) (by nlinarith only [hu4L])
    have hsvu4U : sv * u4 ≤ (53836 / 100000 : ℝ) * (144 / 1000) :=
      v4_nonnegative_product_upper sv u4 (53836 / 100000) (144 / 1000)
        hsvU hu4U (by norm_num) (by nlinarith only [hu4L])
    have hT1 : 125000000000000 *
          (((824479 / 1000000 : ℝ) * (1687 / 100000)) * (2 / 1000)) ≤
        -125000000000000 * a * du * v4 := by
      nlinarith only [haduNvL]
    have hT2 : 250000000000 *
          ((824479 / 1000000 : ℝ) * (1687 / 100000)) ≤
        250000000000 * a * du := by
      nlinarith only [haduL]
    have hT3 : 250000000000000 *
          (((824479 / 1000000 : ℝ) * (555 / 10000)) * (141 / 1000)) ≤
        250000000000000 * a * dv * u4 := by
      nlinarith only [hadvu4L]
    have hT4 : 2115000000000 * ((824479 / 1000000 : ℝ) * (2 / 1000)) ≤
        -2115000000000 * a * v4 := by
      nlinarith only [haNvL]
    have hT5 : -3412123000000 * (826465 / 1000000 : ℝ) ≤
        -3412123000000 * a := by
      nlinarith only [haU]
    have hT6 : -46408500000000 *
          ((1692 / 100000 : ℝ) * (53836 / 100000)) ≤
        -46408500000000 * du * sv := by
      nlinarith only [hdusvU]
    have hT7 : 171778750000000 *
          ((1692 / 100000 : ℝ) * (-4 / 1000)) ≤
        171778750000000 * du * v4 := by
      nlinarith only [hduv4L]
    have hT8 : -343557500000 * (1692 / 100000 : ℝ) ≤
        -343557500000 * du := by
      nlinarith only [hduU]
    have hT9 : -343557500000000 *
          ((558 / 10000 : ℝ) * (144 / 1000)) ≤
        -343557500000000 * dv * u4 := by
      nlinarith only [hdvu4U]
    have hT10 : 26066726280000 * (555 / 10000 : ℝ) ≤
        26066726280000 * dv := by
      nlinarith only [hdvL]
    have hT11 : -35250000000 *
          ((53836 / 100000 : ℝ) * (144 / 1000)) ≤
        -35250000000 * sv * u4 := by
      nlinarith only [hsvu4U]
    have hT12 : -2980558100000 * (53836 / 100000 : ℝ) ≤
        -2980558100000 * sv := by
      nlinarith only [hsvU]
    have hT13 : 2926295670000 * (-4 / 1000 : ℝ) ≤
        2926295670000 * v4 := by
      nlinarith only [hv4L]
    unfold v4Slopedu
    nlinarith only [hT1, hT2, hT3, hT4, hT5, hT6, hT7, hT8,
      hT9, hT10, hT11, hT12, hT13]
  constructor
  · have hadvL : (824479 / 1000000 : ℝ) * (555 / 10000) ≤ a * dv :=
      v4_nonnegative_product_lower a dv (824479 / 1000000) (555 / 10000)
        haL hdvL (by norm_num) (by nlinarith only [hdvL])
    have hT1 : 42300000000000 *
          ((824479 / 1000000 : ℝ) * (555 / 10000)) ≤
        42300000000000 * a * dv := by
      nlinarith only [hadvL]
    have hT2 : -9261167000000 * (826465 / 1000000 : ℝ) ≤
        -9261167000000 * a := by
      nlinarith only [haU]
    have hT3 : -58327921200000 * (558 / 10000 : ℝ) ≤
        -58327921200000 * dv := by
      nlinarith only [hdvU]
    have hT4 : -11577976500000 * (53836 / 100000 : ℝ) ≤
        -11577976500000 * sv := by
      nlinarith only [hsvU]
    unfold v4Slopeu4
    nlinarith only [hT1, hT2, hT3, hT4]
  constructor
  · norm_num [v4Slopesv]
  constructor
  · unfold v4Slopedv
    nlinarith only [haU]
  · unfold v4Slopev4
    nlinarith only [haU]

set_option maxHeartbeats 3000000 in
private theorem alternatingV4Slope_upper
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    alternatingV4Slope X R C D F a x r c d f
        su du u4 sv dv v4 (-2 / 1000) ≤ (-6 / 1000000 : ℝ) := by
  rcases hbox.X_mem with ⟨hXL, hXU⟩
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.C_mem with ⟨hCL, hCU⟩
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.a_mem with ⟨haL, haU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.su_mem with ⟨hsuL, hsuU⟩
  rcases hbox.du_mem with ⟨hduL, hduU⟩
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  rcases hbox.sv_mem with ⟨hsvL, hsvU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  rcases hbox.v4_mem with ⟨hv4L, hv4U⟩
  have hSX := v4SlopeX_nonpos
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  rcases v4RemainingGeometrySlopeSigns
      A X R C D F a x r c d f su du u4 sv dv v4
        q11 q13 q33 h11 h13 h33 hbox with
    ⟨hSR, hSC, hSD, hSx, hSr, hSc, hSd⟩
  rcases v4StateSlopeSigns
      A X R C D F a x r c d f su du u4 sv dv v4
        q11 q13 q33 h11 h13 h33 hbox with
    ⟨hSsu, hSdu, hSu4, hSsv, hSdv, hSv4⟩
  have hSa : (0 : ℝ) ≤ v4Slopea := by
    norm_num [v4Slopea]
  have hPX := mul_nonpos_of_nonneg_of_nonpos
    (show (0 : ℝ) ≤ X - 1981 / 50000 by nlinarith only [hXL])
    (show v4SlopeX X R D a x r d su du u4 sv dv v4 ≤ 0 by
      nlinarith only [hSX])
  have hPR := mul_nonpos_of_nonneg_of_nonpos
    (show (0 : ℝ) ≤ R - 242817 / 1000000 by nlinarith only [hRL])
    (show v4SlopeR C a x r c su du u4 sv dv v4 ≤ 0 by
      nlinarith only [hSR])
  have hPC := mul_nonpos_of_nonpos_of_nonneg
    (show C - 671 / 50000 ≤ (0 : ℝ) by nlinarith only [hCU])
    (show (0 : ℝ) ≤ v4SlopeC a r su du u4 sv dv v4 by
      nlinarith only [hSC])
  have hPD := mul_nonpos_of_nonneg_of_nonpos
    (show (0 : ℝ) ≤ D - 42817 / 1000000 by nlinarith only [hDL])
    (show v4SlopeD a x su du u4 sv dv v4 ≤ 0 by
      nlinarith only [hSD])
  have hPx := mul_nonpos_of_nonpos_of_nonneg
    (show x - 39761 / 1000000 ≤ (0 : ℝ) by nlinarith only [hxU])
    (show (0 : ℝ) ≤ v4Slopex x a r d su du u4 sv dv v4 by
      nlinarith only [hSx])
  have hPr := mul_nonpos_of_nonpos_of_nonneg
    (show r - 57183 / 1000000 ≤ (0 : ℝ) by nlinarith only [hrU])
    (show (0 : ℝ) ≤ v4Sloper c su du u4 sv dv v4 by
      nlinarith only [hSr])
  have hPc := mul_nonpos_of_nonneg_of_nonpos
    (show (0 : ℝ) ≤ c - 5179 / 1000000 by nlinarith only [hcL])
    (show v4Slopec a su du u4 sv dv v4 ≤ 0 by
      nlinarith only [hSc])
  have hPd := mul_nonpos_of_nonpos_of_nonneg
    (show d - 27183 / 1000000 ≤ (0 : ℝ) by nlinarith only [hdU])
    (show (0 : ℝ) ≤ v4Sloped a su du u4 sv dv v4 by
      nlinarith only [hSd])
  have hPsu := mul_nonpos_of_nonneg_of_nonpos
    (show (0 : ℝ) ≤ su - 7021 / 12500 by nlinarith only [hsuL])
    (show v4Slopesu su du u4 sv dv v4 ≤ 0 by
      nlinarith only [hSsu])
  have hPdu := mul_nonpos_of_nonpos_of_nonneg
    (show du - 423 / 25000 ≤ (0 : ℝ) by nlinarith only [hduU])
    (show (0 : ℝ) ≤ v4Slopedu a du u4 sv dv v4 by
      nlinarith only [hSdu])
  have hPu4 := mul_nonpos_of_nonpos_of_nonneg
    (show u4 - 18 / 125 ≤ (0 : ℝ) by nlinarith only [hu4U])
    (show (0 : ℝ) ≤ v4Slopeu4 a sv dv by nlinarith only [hSu4])
  have hPsv := mul_nonpos_of_nonpos_of_nonneg
    (show sv - 13459 / 25000 ≤ (0 : ℝ) by nlinarith only [hsvU])
    hSsv
  have hPdv := mul_nonpos_of_nonneg_of_nonpos
    (show (0 : ℝ) ≤ dv - 111 / 2000 by nlinarith only [hdvL])
    hSdv
  have hPv4 := mul_nonpos_of_nonneg_of_nonpos
    (show (0 : ℝ) ≤ v4 - (-1 / 250) by nlinarith only [hv4L])
    hSv4
  have hPa := mul_nonpos_of_nonpos_of_nonneg
    (show a - 165293 / 200000 ≤ (0 : ℝ) by nlinarith only [haU])
    hSa
  have hcorner :
      alternatingV4Slope
          (1981 / 50000) (242817 / 1000000) (671 / 50000)
          (42817 / 1000000) 0 (165293 / 200000)
          (39761 / 1000000) (57183 / 1000000) (5179 / 1000000)
          (27183 / 1000000) 0 (7021 / 12500) (423 / 25000)
          (18 / 125) (13459 / 25000) (111 / 2000) (-1 / 250)
          (-2 / 1000) =
        (-85641662255683 / 12500000000000000000 : ℝ) := by
    norm_num [alternatingV4Slope, alternatingV4Coupling, alternatingV4Cross,
      adjugateRowFour, mixedAdjugateRowFour, crossGradientS, crossGradientD]
  have hcornerCap :
      alternatingV4Slope
          (1981 / 50000) (242817 / 1000000) (671 / 50000)
          (42817 / 1000000) 0 (165293 / 200000)
          (39761 / 1000000) (57183 / 1000000) (5179 / 1000000)
          (27183 / 1000000) 0 (7021 / 12500) (423 / 25000)
          (18 / 125) (13459 / 25000) (111 / 2000) (-1 / 250)
          (-2 / 1000) ≤ (-6 / 1000000 : ℝ) := by
    rw [hcorner]
    norm_num
  have htel := alternatingV4Slope_telescope
    X R C D F a x r c d f su du u4 sv dv v4
  nlinarith only [htel, hcornerCap, hPX, hPR, hPC, hPD, hPx, hPr, hPc,
    hPd, hPsu, hPdu, hPu4, hPsv, hPdv, hPv4, hPa]

private def duCouplingTermOne
    (X R D F x r d f su : ℝ) : ℝ :=
  (22575000 * su - 5629049) *
    (D * R - D * r + F * X - F * x - R * d - X * f + d * r + f * x) /
      100000000

private def duCouplingTermTwo
    (R F a r f du : ℝ) : ℝ :=
  3 * (30100000 * du - 1048661) *
    (100000 * F * a - 137423 * F + 100000 * R ^ 2 -
      200000 * R * r - 100000 * a * f + 137423 * f + 100000 * r ^ 2) /
      80000000000000

private def duCouplingTermThree
    (X R D a x r d u4 : ℝ) : ℝ :=
  -(564375 * u4 + 523) *
    (-100000 * D * a + 137423 * D + 100000 * R * X -
      100000 * R * x - 100000 * X * r + 100000 * a * d -
      137423 * d + 100000 * r * x) / 250000000000

private def duCouplingTermFour
    (X R D F x r d f su : ℝ) : ℝ :=
  -47 * (112500 * su - 54731) * (-D * R - F * X + d * r + f * x) /
    25000000

private def duCouplingTermFive
    (R F a r f du : ℝ) : ℝ :=
  -9 * (4700000 * du - 394887) *
    (137423 * F - 100000 * R ^ 2 - 100000 * a * f + 100000 * r ^ 2) /
      40000000000000

private def duCouplingTermSix
    (X R D a x r d u4 : ℝ) : ℝ :=
  (264375 * u4 + 478) *
    (-137423 * D - 100000 * R * X + 100000 * a * d + 100000 * r * x) /
      125000000000

private theorem alternatingDuCoupling_terms_eq
    (X R C D F a x r c d f su du u4 : ℝ) :
    alternatingDuCoupling X R C D F a x r c d f
        su du (1687 / 100000) u4
        (53815 / 100000) (558 / 10000) (-2 / 1000) =
      duCouplingTermOne X R D F x r d f su +
        duCouplingTermTwo R F a r f du +
        duCouplingTermThree X R D a x r d u4 +
        duCouplingTermFour X R D F x r d f su +
        duCouplingTermFive R F a r f du +
        duCouplingTermSix X R D a x r d u4 := by
  unfold alternatingDuCoupling adjugateRowD mixedAdjugateRowD
    duCouplingTermOne duCouplingTermTwo duCouplingTermThree
    duCouplingTermFour duCouplingTermFive duCouplingTermSix
  dsimp only
  ring

set_option maxHeartbeats 3000000 in
private theorem alternatingDuCoupling_lower
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (22 / 100000 : ℝ) ≤
      alternatingDuCoupling X R C D F a x r c d f
        su du (1687 / 100000) u4
        (53815 / 100000) (558 / 10000) (-2 / 1000) := by
  rcases hbox.X_mem with ⟨hXL, hXU⟩
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.F_mem with ⟨hFL, hFU⟩
  rcases hbox.a_mem with ⟨haL, haU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  rcases hbox.su_mem with ⟨hsuL, hsuU⟩
  rcases hbox.du_mem with ⟨hduL, hduU⟩
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  let Ap := (137423 / 100000 : ℝ) - a
  let Xp := X - x
  let Rp := R - r
  let Dp := D - d
  let Fp := F - f
  have hApL : (109553 / 200000 : ℝ) ≤ Ap := by
    dsimp [Ap]
    nlinarith only [haU]
  have hApU : Ap ≤ (549751 / 1000000 : ℝ) := by
    dsimp [Ap]
    nlinarith only [haL]
  have hXpL : (-141 / 1000000 : ℝ) ≤ Xp := by
    dsimp [Xp]
    nlinarith only [hXL, hxU]
  have hXpU : Xp ≤ (1919 / 1000000 : ℝ) := by
    dsimp [Xp]
    nlinarith only [hXU, hxL]
  have hRpL : (92817 / 500000 : ℝ) ≤ Rp := by
    dsimp [Rp]
    nlinarith only [hRL, hrU]
  have hRpU : Rp ≤ (193081 / 1000000 : ℝ) := by
    dsimp [Rp]
    nlinarith only [hRU, hrL]
  have hDpL : (7817 / 500000 : ℝ) ≤ Dp := by
    dsimp [Dp]
    nlinarith only [hDL, hdU]
  have hDpU : Dp ≤ (19581 / 1000000 : ℝ) := by
    dsimp [Dp]
    nlinarith only [hDU, hdL]
  have hFpL : (3439 / 25000 : ℝ) ≤ Fp := by
    dsimp [Fp]
    nlinarith only [hFL, hfU]
  have hFpU : Fp ≤ (433 / 3125 : ℝ) := by
    dsimp [Fp]
    nlinarith only [hFU, hfL]
  let A1 := 22575000 * su - 5629049
  let B1 := D * R - D * r + F * X - F * x - R * d - X * f + d * r + f * x
  have hA1L : (7050877 : ℝ) ≤ A1 := by
    dsimp [A1]
    nlinarith only [hsuL]
  have hDpRpL :
      (7817 / 500000 : ℝ) * (92817 / 500000) ≤ Dp * Rp := by
    have hleft : (0 : ℝ) ≤ (Dp - 7817 / 500000) * Rp :=
      mul_nonneg (by nlinarith only [hDpL]) (by nlinarith only [hRpL])
    have hright : (0 : ℝ) ≤
        (7817 / 500000) * (Rp - 92817 / 500000) :=
      mul_nonneg (by norm_num) (by nlinarith only [hRpL])
    nlinarith only [hleft, hright]
  have hFpXpL :
      (433 / 3125 : ℝ) * (-141 / 1000000) ≤ Fp * Xp := by
    have hleft : (0 : ℝ) ≤ Fp * (Xp - (-141 / 1000000)) :=
      mul_nonneg (by nlinarith only [hFpL]) (by nlinarith only [hXpL])
    have hright : (0 : ℝ) ≤
        (-141 / 1000000) * (Fp - 433 / 3125) :=
      mul_nonneg_of_nonpos_of_nonpos (by norm_num)
        (by nlinarith only [hFpU])
    nlinarith only [hleft, hright]
  have hB1L : (5734158683 / 2000000000000 : ℝ) ≤ B1 := by
    dsimp [B1, Dp, Rp, Fp, Xp] at hDpRpL hFpXpL ⊢
    nlinarith only [hDpRpL, hFpXpL]
  have hA1B1 : (7050877 : ℝ) * (5734158683 / 2000000000000) ≤
      A1 * B1 := by
    have hleft : (0 : ℝ) ≤ (A1 - 7050877) * B1 :=
      mul_nonneg (by nlinarith only [hA1L]) (by nlinarith only [hB1L])
    have hright : (0 : ℝ) ≤
        7050877 * (B1 - 5734158683 / 2000000000000) :=
      mul_nonneg (by norm_num) (by nlinarith only [hB1L])
    nlinarith only [hleft, hright]
  have hT1 : (2 / 10000 : ℝ) ≤
      duCouplingTermOne X R D F x r d f su := by
    unfold duCouplingTermOne
    dsimp [A1, B1] at hA1B1
    nlinarith only [hA1B1]
  let A2 := 30100000 * du - 1048661
  let B2 := 100000 * F * a - 137423 * F + 100000 * R ^ 2 -
    200000 * R * r - 100000 * a * f + 137423 * f + 100000 * r ^ 2
  have hA2U : A2 ≤ (-539369 : ℝ) := by
    dsimp [A2]
    nlinarith only [hduU]
  have hFpApL :
      (3439 / 25000 : ℝ) * (109553 / 200000) ≤ Fp * Ap := by
    have hleft : (0 : ℝ) ≤ (Fp - 3439 / 25000) * Ap :=
      mul_nonneg (by nlinarith only [hFpL]) (by nlinarith only [hApL])
    have hright : (0 : ℝ) ≤
        (3439 / 25000) * (Ap - 109553 / 200000) :=
      mul_nonneg (by norm_num) (by nlinarith only [hApL])
    nlinarith only [hleft, hright]
  have hRpSqU : Rp ^ 2 ≤ (193081 / 1000000 : ℝ) ^ 2 := by
    bound
  have hB2U : B2 ≤ (-38069287839 / 10000000 : ℝ) := by
    dsimp [B2, Fp, Ap, Rp] at hFpApL hRpSqU ⊢
    nlinarith only [hFpApL, hRpSqU]
  have hA2B2 : (-539369 : ℝ) * (-38069287839 / 10000000) ≤
      A2 * B2 := by
    have hleft : (0 : ℝ) ≤ ((-A2) - 539369) * (-B2) :=
      mul_nonneg (by nlinarith only [hA2U]) (by nlinarith only [hB2U])
    have hright : (0 : ℝ) ≤
        539369 * ((-B2) - 38069287839 / 10000000) :=
      mul_nonneg (by norm_num) (by nlinarith only [hB2U])
    nlinarith only [hleft, hright]
  have hT2 : (7 / 100000 : ℝ) ≤ duCouplingTermTwo R F a r f du := by
    unfold duCouplingTermTwo
    dsimp [A2, B2] at hA2B2
    nlinarith only [hA2B2]
  let A3 := 564375 * u4 + 523
  let B3 := -100000 * D * a + 137423 * D + 100000 * R * X -
    100000 * R * x - 100000 * X * r + 100000 * a * d -
    137423 * d + 100000 * r * x
  have hA3U : A3 ≤ (81793 : ℝ) := by
    dsimp [A3]
    nlinarith only [hu4U]
  have hApDpU : Ap * Dp ≤
      (549751 / 1000000 : ℝ) * (19581 / 1000000) := by
    bound
  have hXpRpU : Xp * Rp ≤
      (1919 / 1000000 : ℝ) * (193081 / 1000000) := by
    have hleft : (0 : ℝ) ≤ (1919 / 1000000 - Xp) * Rp :=
      mul_nonneg (by nlinarith only [hXpU]) (by nlinarith only [hRpL])
    have hright : (0 : ℝ) ≤
        (1919 / 1000000) * (193081 / 1000000 - Rp) :=
      mul_nonneg (by norm_num) (by nlinarith only [hRpU])
    nlinarith only [hleft, hright]
  have hB3U : B3 ≤ (1113519677 / 1000000 : ℝ) := by
    dsimp [B3, Ap, Dp, Xp, Rp] at hApDpU hXpRpU ⊢
    nlinarith only [hApDpU, hXpRpU]
  have hApDpL :
      (109553 / 200000 : ℝ) * (7817 / 500000) ≤ Ap * Dp := by
    bound
  have hXpRpL :
      (-141 / 1000000 : ℝ) * (193081 / 1000000) ≤ Xp * Rp := by
    have hleft : (0 : ℝ) ≤ Rp * (Xp - (-141 / 1000000)) :=
      mul_nonneg (by nlinarith only [hRpL]) (by nlinarith only [hXpL])
    have hright : (0 : ℝ) ≤
        (-141 / 1000000) * (Rp - 193081 / 1000000) :=
      mul_nonneg_of_nonpos_of_nonpos (by norm_num)
        (by nlinarith only [hRpU])
    nlinarith only [hleft, hright]
  have hB30 : (0 : ℝ) ≤ B3 := by
    dsimp [B3, Ap, Dp, Xp, Rp] at hApDpL hXpRpL ⊢
    nlinarith only [hApDpL, hXpRpL]
  have hA3B3 : A3 * B3 ≤ (81793 : ℝ) * (1113519677 / 1000000) := by
    have hleft : (0 : ℝ) ≤ (81793 - A3) * B3 :=
      mul_nonneg (by nlinarith only [hA3U]) hB30
    have hright : (0 : ℝ) ≤
        81793 * (1113519677 / 1000000 - B3) :=
      mul_nonneg (by norm_num) (by nlinarith only [hB3U])
    nlinarith only [hleft, hright]
  have hT3 : (-37 / 100000 : ℝ) ≤
      duCouplingTermThree X R D a x r d u4 := by
    unfold duCouplingTermThree
    dsimp [A3, B3] at hA3B3
    nlinarith only [hA3B3]
  let A4 := 112500 * su - 54731
  let B4 := -D * R - F * X + d * r + f * x
  have hA4L : (8458 : ℝ) ≤ A4 := by
    dsimp [A4]
    nlinarith only [hsuL]
  have hDRL : (42817 / 1000000 : ℝ) * (242817 / 1000000) ≤ D * R := by
    bound
  have hFXL : (1571 / 5000 : ℝ) * (3962 / 100000) ≤ F * X := by
    bound
  have hdrU : d * r ≤ (27183 / 1000000 : ℝ) * (57183 / 1000000) := by
    bound
  have hfxU : f * x ≤ (4416 / 25000 : ℝ) * (39761 / 1000000) := by
    bound
  have hB4U : B4 ≤ (-28534895359 / 2000000000000 : ℝ) := by
    dsimp [B4]
    nlinarith only [hDRL, hFXL, hdrU, hfxU]
  have hA4B4 : (8458 : ℝ) * (28534895359 / 2000000000000) ≤
      A4 * (-B4) := by
    have hleft : (0 : ℝ) ≤ (A4 - 8458) * (-B4) :=
      mul_nonneg (by nlinarith only [hA4L]) (by nlinarith only [hB4U])
    have hright : (0 : ℝ) ≤
        8458 * ((-B4) - 28534895359 / 2000000000000) :=
      mul_nonneg (by norm_num) (by nlinarith only [hB4U])
    nlinarith only [hleft, hright]
  have hT4 : (22 / 100000 : ℝ) ≤
      duCouplingTermFour X R D F x r d f su := by
    unfold duCouplingTermFour
    dsimp [A4, B4] at hA4B4
    nlinarith only [hA4B4]
  let A5 := 4700000 * du - 394887
  let B5 := 137423 * F - 100000 * R ^ 2 - 100000 * a * f + 100000 * r ^ 2
  have hA5U : A5 ≤ (-315363 : ℝ) := by
    dsimp [A5]
    nlinarith only [hduU]
  have hafU : a * f ≤ (826465 / 1000000 : ℝ) * (4416 / 25000) := by
    bound
  have hRsqU : R ^ 2 ≤ (242898 / 1000000 : ℝ) ^ 2 := by
    bound
  have hrsqL : (49817 / 1000000 : ℝ) ^ 2 ≤ r ^ 2 := by
    bound
  have hB5L : (229251454507 / 10000000 : ℝ) ≤ B5 := by
    dsimp [B5]
    nlinarith only [hFL, hafU, hRsqU, hrsqL]
  have hA5B5 : (315363 : ℝ) * (229251454507 / 10000000) ≤
      (-A5) * B5 := by
    have hleft : (0 : ℝ) ≤ ((-A5) - 315363) * B5 :=
      mul_nonneg (by nlinarith only [hA5U]) (by nlinarith only [hB5L])
    have hright : (0 : ℝ) ≤
        315363 * (B5 - 229251454507 / 10000000) :=
      mul_nonneg (by norm_num) (by nlinarith only [hB5L])
    nlinarith only [hleft, hright]
  have hT5 : (16 / 10000 : ℝ) ≤ duCouplingTermFive R F a r f du := by
    unfold duCouplingTermFive
    dsimp [A5, B5] at hA5B5
    nlinarith only [hA5B5]
  let A6 := 264375 * u4 + 478
  let B6 := -137423 * D - 100000 * R * X + 100000 * a * d + 100000 * r * x
  have hA6L : (302039 / 8 : ℝ) ≤ A6 := by
    dsimp [A6]
    nlinarith only [hu4L]
  have hA6U : A6 ≤ (38548 : ℝ) := by
    dsimp [A6]
    nlinarith only [hu4U]
  have hRXU : R * X ≤ (242898 / 1000000 : ℝ) * (3977 / 100000) := by
    bound
  have hadL : (824479 / 1000000 : ℝ) * (23317 / 1000000) ≤ a * d := by
    bound
  have hrxL : (49817 / 1000000 : ℝ) * (37851 / 1000000) ≤ r * x := by
    bound
  have hB6L : (-23756322679 / 5000000 : ℝ) ≤ B6 := by
    dsimp [B6]
    nlinarith only [hDU, hRXU, hadL, hrxL]
  have hRXL : (242817 / 1000000 : ℝ) * (3962 / 100000) ≤ R * X := by
    bound
  have hadU : a * d ≤ (826465 / 1000000 : ℝ) * (27183 / 1000000) := by
    bound
  have hrxU : r * x ≤ (57183 / 1000000 : ℝ) * (39761 / 1000000) := by
    bound
  have hB6U : B6 ≤ (-43721358017 / 10000000 : ℝ) := by
    dsimp [B6]
    nlinarith only [hDL, hRXL, hadU, hrxU]
  have hA6B6 : (38548 : ℝ) * (-23756322679 / 5000000) ≤ A6 * B6 := by
    have hleft : (0 : ℝ) ≤ (38548 - A6) * (-B6) :=
      mul_nonneg (by nlinarith only [hA6U]) (by nlinarith only [hB6U])
    have hright : (0 : ℝ) ≤
        38548 * ((-23756322679 / 5000000) * (-1) - (-B6)) :=
      mul_nonneg (by norm_num) (by nlinarith only [hB6L])
    nlinarith only [hleft, hright]
  have hT6 : (-15 / 10000 : ℝ) ≤
      duCouplingTermSix X R D a x r d u4 := by
    unfold duCouplingTermSix
    dsimp [A6, B6] at hA6B6
    nlinarith only [hA6B6]
  rw [alternatingDuCoupling_terms_eq]
  nlinarith only [hT1, hT2, hT3, hT4, hT5, hT6]

private theorem alternatingDuCross_lower
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (-12 / 100000 : ℝ) ≤
      alternatingDuCross X R C D F a x r c d f
        su du (1687 / 100000) u4
        (53815 / 100000) (558 / 10000) (-2 / 1000) := by
  rcases hbox.X_mem with ⟨hXL, hXU⟩
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.F_mem with ⟨hFL, hFU⟩
  rcases hbox.a_mem with ⟨haL, haU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  rcases hbox.su_mem with ⟨hsuL, hsuU⟩
  rcases hbox.du_mem with ⟨hduL, hduU⟩
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  let Ap := (137423 / 100000 : ℝ) - a
  let Xp := X - x
  let Rp := R - r
  let Dp := D - d
  let Fp := F - f
  let dbar := (du + 1687 / 100000) / 2
  let zs := u4 * (558 / 10000) - (-2 / 1000) * dbar
  let zd := (-2 / 1000) * su - u4 * (53815 / 100000)
  let zc := (dbar * (53815 / 100000) - su * (558 / 10000)) / 2
  have hApL : (109553 / 200000 : ℝ) ≤ Ap := by
    dsimp [Ap]
    nlinarith only [haU]
  have hXpU : Xp ≤ (1919 / 1000000 : ℝ) := by
    dsimp [Xp]
    nlinarith only [hXU, hxL]
  have hRpL : (92817 / 500000 : ℝ) ≤ Rp := by
    dsimp [Rp]
    nlinarith only [hRL, hrU]
  have hRpU : Rp ≤ (193081 / 1000000 : ℝ) := by
    dsimp [Rp]
    nlinarith only [hRU, hrL]
  have hDpL : (7817 / 500000 : ℝ) ≤ Dp := by
    dsimp [Dp]
    nlinarith only [hDL, hdU]
  have hFpL : (3439 / 25000 : ℝ) ≤ Fp := by
    dsimp [Fp]
    nlinarith only [hFL, hfU]
  have hFpU : Fp ≤ (433 / 3125 : ℝ) := by
    dsimp [Fp]
    nlinarith only [hFU, hfL]
  have hzsL : (395077 / 50000000 : ℝ) ≤ zs := by
    dsimp [zs, dbar]
    nlinarith only [hduL, hu4L]
  have hzsU : zs ≤ (806899 / 100000000 : ℝ) := by
    dsimp [zs, dbar]
    nlinarith only [hduU, hu4U]
  have hzdL : (-3930853 / 50000000 : ℝ) ≤ zd := by
    dsimp [zd]
    nlinarith only [hsuU, hu4U]
  have hzdU : zd ≤ (-7700251 / 100000000 : ℝ) := by
    dsimp [zd]
    nlinarith only [hsuL, hu4L]
  have hzcL : (-44531887 / 4000000000 : ℝ) ≤ zc := by
    dsimp [zc, dbar]
    nlinarith only [hduL, hsuU]
  have hzcU : zc ≤ (-88998799 / 8000000000 : ℝ) := by
    dsimp [zc, dbar]
    nlinarith only [hduU, hsuL]
  have hApzs :
      (109553 / 200000 : ℝ) * (395077 / 50000000) ≤ Ap * zs := by
    have hleft : (0 : ℝ) ≤ (Ap - 109553 / 200000) * zs :=
      mul_nonneg (by nlinarith only [hApL]) (by nlinarith only [hzsL])
    have hright : (0 : ℝ) ≤
        (109553 / 200000) * (zs - 395077 / 50000000) :=
      mul_nonneg (by norm_num) (by nlinarith only [hzsL])
    nlinarith only [hleft, hright]
  have hXpzd :
      (1919 / 1000000 : ℝ) * (-3930853 / 50000000) ≤ Xp * zd := by
    have hleft : (0 : ℝ) ≤ (1919 / 1000000 - Xp) * (-zd) :=
      mul_nonneg (by nlinarith only [hXpU]) (by nlinarith only [hzdU])
    have hright : (0 : ℝ) ≤
        (1919 / 1000000) * (zd - (-3930853 / 50000000)) :=
      mul_nonneg (by norm_num) (by nlinarith only [hzdL])
    nlinarith only [hleft, hright]
  have hRpzc :
      (193081 / 1000000 : ℝ) * (-44531887 / 4000000000) ≤ Rp * zc := by
    have hleft : (0 : ℝ) ≤ (193081 / 1000000 - Rp) * (-zc) :=
      mul_nonneg (by nlinarith only [hRpU]) (by nlinarith only [hzcU])
    have hright : (0 : ℝ) ≤
        (193081 / 1000000) * (zc - (-44531887 / 4000000000)) :=
      mul_nonneg (by norm_num) (by nlinarith only [hzcL])
    nlinarith only [hleft, hright]
  have hgS : (-61 / 1000000 : ℝ) ≤
      crossGradientS Ap Xp Rp zs zd zc := by
    unfold crossGradientS
    nlinarith only [hApzs, hXpzd, hRpzc]
  have hRpzs :
      (92817 / 500000 : ℝ) * (395077 / 50000000) ≤ Rp * zs := by
    have hleft : (0 : ℝ) ≤ (Rp - 92817 / 500000) * zs :=
      mul_nonneg (by nlinarith only [hRpL]) (by nlinarith only [hzsL])
    have hright : (0 : ℝ) ≤
        (92817 / 500000) * (zs - 395077 / 50000000) :=
      mul_nonneg (by norm_num) (by nlinarith only [hzsL])
    nlinarith only [hleft, hright]
  have hDpzd :
      (7817 / 500000 : ℝ) * (7700251 / 100000000) ≤ -Dp * zd := by
    have hleft : (0 : ℝ) ≤ (Dp - 7817 / 500000) * (-zd) :=
      mul_nonneg (by nlinarith only [hDpL]) (by nlinarith only [hzdU])
    have hright : (0 : ℝ) ≤
        (7817 / 500000) * ((-zd) - 7700251 / 100000000) :=
      mul_nonneg (by norm_num) (by nlinarith only [hzdU])
    nlinarith only [hleft, hright]
  have hFpzc :
      (433 / 3125 : ℝ) * (-44531887 / 4000000000) ≤ Fp * zc := by
    have hleft : (0 : ℝ) ≤ Fp * (zc - (-44531887 / 4000000000)) :=
      mul_nonneg (by nlinarith only [hFpL]) (by nlinarith only [hzcL])
    have hright : (0 : ℝ) ≤
        (-44531887 / 4000000000) * (Fp - 433 / 3125) :=
      mul_nonneg_of_nonpos_of_nonpos (by norm_num)
        (by nlinarith only [hFpU])
    nlinarith only [hleft, hright]
  have hg4 : (-42 / 100000 : ℝ) ≤
      crossGradientFour Rp Dp Fp zs zd zc := by
    unfold crossGradientFour
    nlinarith only [hRpzs, hDpzd, hFpzc]
  change (-(-2 / 1000)) * crossGradientS Ap Xp Rp zs zd zc +
      ((53815 / 100000) / 2) * crossGradientFour Rp Dp Fp zs zd zc ≥
    (-12 / 100000 : ℝ)
  nlinarith only [hgS, hg4]

private def suCouplingSlopeX (D F d f u4 : ℝ) : ℝ :=
  -1749 * D * u4 / 8000 - 1479 * D / 5000000 +
    3651693 * F / 800000000 + 903 * d * u4 / 8000 +
      523 * d / 5000000 - 811311 * f / 800000000

private def suCouplingSlopeR (C D F c d u4 : ℝ) : ℝ :=
  -1749 * C * u4 / 8000 - 1479 * C / 5000000 +
    3651693 * D / 800000000 + 903 * c * u4 / 8000 +
      523 * c / 5000000 - 811311 * d / 800000000

private def suCouplingSlopeC (F f r su u4 : ℝ) : ℝ :=
  1749 * F * su / 16000 - 29101239 * F / 1600000000 -
    903 * f * su / 16000 - 5691827 * f / 1600000000 +
      903 * r * u4 / 8000 + 523 * r / 5000000 -
        212414301 * u4 / 4000000000 - 179623071 / 2500000000000

private def suCouplingSlopeD (D d r su u4 x : ℝ) : ℝ :=
  -1749 * D * su / 16000 + 29101239 * D / 1600000000 +
    903 * d * su / 8000 + 5691827 * d / 800000000 -
      811311 * r / 800000000 - 37514301 * su / 8000000000 +
        903 * u4 * x / 8000 - 3464769 * u4 / 400000000 +
          523 * x / 5000000 + 60072228993 / 32000000000000

private def suCouplingSlopeF (c su x : ℝ) : ℝ :=
  -903 * c * su / 16000 - 5691827 * c / 1600000000 +
    2313927 * su / 1600000000 - 811311 * x / 800000000 -
      1912984773 / 32000000000000

private def suCouplingSlopex (d f u4 : ℝ) : ℝ :=
  -57 * d * u4 / 8000 + 433 * d / 5000000 -
    2029071 * f / 800000000 + 19368447 * u4 / 4000000000 -
      6283105289 / 20000000000000

private def suCouplingSloper (c d u4 : ℝ) : ℝ :=
  -57 * c * u4 / 8000 + 433 * c / 5000000 -
    2029071 * d / 800000000 + 1194669 * u4 / 800000000 -
      16848266439 / 400000000000000

private def suCouplingSlopec (f su u4 : ℝ) : ℝ :=
  57 * f * su / 16000 + 40484893 * f / 1600000000 -
    1418613 * su / 80000000 + 8659893 * u4 / 320000000 -
      8704089953 / 8000000000000

private def suCouplingSloped (d su u4 : ℝ) : ℝ :=
  -57 * d * su / 16000 - 40484893 * d / 1600000000 +
    76144719 * su / 16000000000 + 33510483 * u4 / 8000000000 -
      1039806271999 / 1600000000000000

private def suCouplingSlopef (su : ℝ) : ℝ :=
  -2307657 * su / 3200000000 - 10872680567 / 1600000000000000

private def suCouplingSlopesu : ℝ :=
  1756252986927 / 16000000000000000

private def suCouplingSlopeu4 : ℝ :=
  -41251824519 / 80000000000000

private theorem alternatingSuCoupling_telescope
    (X R C D F a x r c d f su u4 : ℝ) :
    alternatingSuCoupling X R C D F a x r c d f
          su (56173 / 100000) (1687 / 100000) u4
          (53815 / 100000) (558 / 10000) (-2 / 1000) -
        alternatingSuCoupling
          (1981 / 50000) (121449 / 500000) (1323 / 100000)
          (21449 / 500000) (1571 / 5000) a
          (39761 / 1000000) (49817 / 1000000) (1433 / 200000)
          (23317 / 1000000) (552 / 3125)
          (7021 / 12500) (56173 / 100000) (1687 / 100000) (18 / 125)
          (53815 / 100000) (558 / 10000) (-2 / 1000) =
      (X - 1981 / 50000) * suCouplingSlopeX D F d f u4 +
        (R - 121449 / 500000) * suCouplingSlopeR C D F c d u4 +
        (C - 1323 / 100000) * suCouplingSlopeC F f r su u4 +
        (D - 21449 / 500000) * suCouplingSlopeD D d r su u4 x +
        (F - 1571 / 5000) * suCouplingSlopeF c su x +
        (x - 39761 / 1000000) * suCouplingSlopex d f u4 +
        (r - 49817 / 1000000) * suCouplingSloper c d u4 +
        (c - 1433 / 200000) * suCouplingSlopec f su u4 +
        (d - 23317 / 1000000) * suCouplingSloped d su u4 +
        (f - 552 / 3125) * suCouplingSlopef su +
        (su - 7021 / 12500) * suCouplingSlopesu +
        (u4 - 18 / 125) * suCouplingSlopeu4 := by
  unfold alternatingSuCoupling adjugateRowS mixedAdjugateRowS
    suCouplingSlopeX suCouplingSlopeR suCouplingSlopeC suCouplingSlopeD
    suCouplingSlopeF suCouplingSlopex suCouplingSloper suCouplingSlopec
    suCouplingSloped suCouplingSlopef suCouplingSlopesu suCouplingSlopeu4
  dsimp only
  ring

private theorem suCoupling_first_three_steps
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    0 ≤ (X - 1981 / 50000) * suCouplingSlopeX D F d f u4 ∧
      0 ≤ (R - 121449 / 500000) * suCouplingSlopeR C D F c d u4 ∧
      0 ≤ (C - 1323 / 100000) * suCouplingSlopeC F f r su u4 := by
  rcases hbox.X_mem with ⟨hXL, hXU⟩
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.C_mem with ⟨hCL, hCU⟩
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.F_mem with ⟨hFL, hFU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  rcases hbox.su_mem with ⟨hsuL, hsuU⟩
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  have hSX : (0 : ℝ) ≤ suCouplingSlopeX D F d f u4 := by
    have hDu4U : D * u4 ≤
        (42898 / 1000000 : ℝ) * (144 / 1000) := by bound
    have hdu4L :
        (23317 / 1000000 : ℝ) * (141 / 1000) ≤ d * u4 := by bound
    unfold suCouplingSlopeX
    nlinarith only [hDU, hFL, hdL, hfU, hDu4U, hdu4L]
  have hSR : suCouplingSlopeR C D F c d u4 ≤ (0 : ℝ) := by
    have hCu4L :
        (1323 / 100000 : ℝ) * (141 / 1000) ≤ C * u4 := by bound
    have hcu4U : c * u4 ≤
        (7165 / 1000000 : ℝ) * (144 / 1000) := by bound
    unfold suCouplingSlopeR
    nlinarith only [hCL, hDU, hcU, hdL, hCu4L, hcu4U]
  have hSC : (0 : ℝ) ≤ suCouplingSlopeC F f r su u4 := by
    have hFsuL :
        (1571 / 5000 : ℝ) * (56168 / 100000) ≤ F * su := by bound
    have hfsuU : f * su ≤
        (4416 / 25000 : ℝ) * (56173 / 100000) := by bound
    have hru4L :
        (49817 / 1000000 : ℝ) * (141 / 1000) ≤ r * u4 := by bound
    unfold suCouplingSlopeC
    nlinarith only [hFU, hfU, hrL, hu4U, hFsuL, hfsuU, hru4L]
  exact ⟨mul_nonneg (by norm_num at hXL ⊢; exact hXL) hSX,
    mul_nonneg_of_nonpos_of_nonpos (by norm_num at hRU ⊢; exact hRU) hSR,
    mul_nonneg (by norm_num at hCL ⊢; exact hCL) hSC⟩

private theorem suCoupling_last_nine_steps
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    0 ≤ (D - 21449 / 500000) * suCouplingSlopeD D d r su u4 x ∧
      0 ≤ (F - 1571 / 5000) * suCouplingSlopeF c su x ∧
      0 ≤ (x - 39761 / 1000000) * suCouplingSlopex d f u4 ∧
      0 ≤ (r - 49817 / 1000000) * suCouplingSloper c d u4 ∧
      0 ≤ (c - 1433 / 200000) * suCouplingSlopec f su u4 ∧
      0 ≤ (d - 23317 / 1000000) * suCouplingSloped d su u4 ∧
      0 ≤ (f - 552 / 3125) * suCouplingSlopef su ∧
      0 ≤ (su - 7021 / 12500) * suCouplingSlopesu ∧
      0 ≤ (u4 - 18 / 125) * suCouplingSlopeu4 := by
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.F_mem with ⟨hFL, hFU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  rcases hbox.su_mem with ⟨hsuL, hsuU⟩
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  have hSD : suCouplingSlopeD D d r su u4 x ≤ (0 : ℝ) := by
    have hDsuL :
        (42817 / 1000000 : ℝ) * (56168 / 100000) ≤ D * su := by
      bound
    have hdsuU : d * su ≤
        (27183 / 1000000 : ℝ) * (56173 / 100000) := by
      bound
    have hu4xU : u4 * x ≤
        (144 / 1000 : ℝ) * (39761 / 1000000) := by
      bound
    unfold suCouplingSlopeD
    nlinarith only [hDsuL, hdsuU, hu4xU, hDU, hdU, hrL, hsuL,
      hu4L, hxU]
  have hSF : (0 : ℝ) ≤ suCouplingSlopeF c su x := by
    have hcsuU : c * su ≤
        (7165 / 1000000 : ℝ) * (56173 / 100000) := by
      bound
    unfold suCouplingSlopeF
    nlinarith only [hcsuU, hcU, hsuL, hxU]
  have hSx : suCouplingSlopex d f u4 ≤ (0 : ℝ) := by
    have hdu4L :
        (23317 / 1000000 : ℝ) * (141 / 1000) ≤ d * u4 := by
      bound
    unfold suCouplingSlopex
    nlinarith only [hdu4L, hdU, hfL, hu4U]
  have hSr : (0 : ℝ) ≤ suCouplingSloper c d u4 := by
    have hcu4U : c * u4 ≤
        (7165 / 1000000 : ℝ) * (144 / 1000) := by
      bound
    unfold suCouplingSloper
    nlinarith only [hcu4U, hcL, hdU, hu4L]
  have hSc : suCouplingSlopec f su u4 ≤ (0 : ℝ) := by
    have hfsuU : f * su ≤
        (4416 / 25000 : ℝ) * (56173 / 100000) := by
      bound
    unfold suCouplingSlopec
    nlinarith only [hfsuU, hfU, hsuL, hu4U]
  have hSd : (0 : ℝ) ≤ suCouplingSloped d su u4 := by
    have hdsuU : d * su ≤
        (27183 / 1000000 : ℝ) * (56173 / 100000) := by
      bound
    unfold suCouplingSloped
    nlinarith only [hdsuU, hdU, hsuL, hu4L]
  have hSf : suCouplingSlopef su ≤ (0 : ℝ) := by
    unfold suCouplingSlopef
    nlinarith only [hsuL]
  have hSsu : (0 : ℝ) ≤ suCouplingSlopesu := by
    unfold suCouplingSlopesu
    norm_num
  have hSu4 : suCouplingSlopeu4 ≤ (0 : ℝ) := by
    unfold suCouplingSlopeu4
    norm_num
  exact ⟨
    mul_nonneg_of_nonpos_of_nonpos
      (by norm_num at hDU ⊢; exact hDU) hSD,
    mul_nonneg (by norm_num at hFL ⊢; exact hFL) hSF,
    mul_nonneg_of_nonpos_of_nonpos
      (by norm_num at hxU ⊢; exact hxU) hSx,
    mul_nonneg (by norm_num at hrL ⊢; exact hrL) hSr,
    mul_nonneg_of_nonpos_of_nonpos
      (by norm_num at hcU ⊢; exact hcU) hSc,
    mul_nonneg (by norm_num at hdL ⊢; exact hdL) hSd,
    mul_nonneg_of_nonpos_of_nonpos
      (by norm_num at hfU ⊢; exact hfU) hSf,
    mul_nonneg (by norm_num at hsuL ⊢; exact hsuL) hSsu,
    mul_nonneg_of_nonpos_of_nonpos
      (by norm_num at hu4U ⊢; exact hu4U) hSu4⟩

private theorem alternatingSuCoupling_lower
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (29 / 4000000 : ℝ) ≤
      alternatingSuCoupling X R C D F a x r c d f
        su (56173 / 100000) (1687 / 100000) u4
        (53815 / 100000) (558 / 10000) (-2 / 1000) := by
  rcases suCoupling_first_three_steps
      A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox with ⟨hX, hR, hC⟩
  rcases suCoupling_last_nine_steps
      A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox with
    ⟨hD, hF, hx, hr, hc, hd, hf, hsu, hu4⟩
  have htel := alternatingSuCoupling_telescope
    X R C D F a x r c d f su u4
  have hcorner : (29 / 4000000 : ℝ) <
      alternatingSuCoupling
        (1981 / 50000) (121449 / 500000) (1323 / 100000)
        (21449 / 500000) (1571 / 5000) a
        (39761 / 1000000) (49817 / 1000000) (1433 / 200000)
        (23317 / 1000000) (552 / 3125)
        (7021 / 12500) (56173 / 100000) (1687 / 100000) (18 / 125)
        (53815 / 100000) (558 / 10000) (-2 / 1000) := by
    unfold alternatingSuCoupling adjugateRowS mixedAdjugateRowS
    norm_num
  nlinarith only [htel, hcorner, hX, hR, hC, hD, hF, hx, hr, hc,
    hd, hf, hsu, hu4]

private theorem alternatingSuCross_upper
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    alternatingSuCross X R C D F a x r c d f
        su (56173 / 100000) (1687 / 100000) u4
        (53815 / 100000) (558 / 10000) (-2 / 1000) ≤
      (25 / 2000000 : ℝ) := by
  rcases hbox.X_mem with ⟨hXL, hXU⟩
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.C_mem with ⟨hCL, hCU⟩
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.F_mem with ⟨hFL, hFU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  rcases hbox.su_mem with ⟨hsuL, hsuU⟩
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  let Xp := X - x
  let Rp := R - r
  let Cp := C - c
  let Dp := D - d
  let Fp := F - f
  let sm := (su + 56173 / 100000) / 2
  let zs := u4 * (558 / 10000) - (-2 / 1000) * (1687 / 100000)
  let zd := (-2 / 1000) * sm - u4 * (53815 / 100000)
  let zc := ((1687 / 100000) * (53815 / 100000) -
    sm * (558 / 10000)) / 2
  have hXpL : (-141 / 1000000 : ℝ) ≤ Xp := by
    dsimp [Xp]
    nlinarith only [hXL, hxU]
  have hRpL : (92817 / 500000 : ℝ) ≤ Rp := by
    dsimp [Rp]
    nlinarith only [hRL, hrU]
  have hCp0 : (0 : ℝ) ≤ Cp := by
    dsimp [Cp]
    nlinarith only [hCL, hcU]
  have hCpU : Cp ≤ (8241 / 1000000 : ℝ) := by
    dsimp [Cp]
    nlinarith only [hCU, hcL]
  have hDpL : (7817 / 500000 : ℝ) ≤ Dp := by
    dsimp [Dp]
    nlinarith only [hDL, hdU]
  have hFp0 : (0 : ℝ) ≤ Fp := by
    dsimp [Fp]
    nlinarith only [hFL, hfU]
  have hFpU : Fp ≤ (433 / 3125 : ℝ) := by
    dsimp [Fp]
    nlinarith only [hFU, hfL]
  have hzsL : (395077 / 50000000 : ℝ) ≤ zs := by
    dsimp [zs]
    nlinarith only [hu4L]
  have hzsU : zs ≤ (403447 / 50000000 : ℝ) := by
    dsimp [zs]
    nlinarith only [hu4U]
  have hzdL : (-3930853 / 50000000 : ℝ) ≤ zd := by
    dsimp [zd, sm]
    nlinarith only [hsuU, hu4U]
  have hzdU : zd ≤ (-240633 / 3125000 : ℝ) := by
    dsimp [zd, sm]
    nlinarith only [hsuL, hu4L]
  have hzcL : (-44531887 / 4000000000 : ℝ) ≤ zc := by
    dsimp [zc, sm]
    nlinarith only [hsuU]
  have hzcU : zc ≤ (-44529097 / 4000000000 : ℝ) := by
    dsimp [zc, sm]
    nlinarith only [hsuL]
  have hXpA : (0 : ℝ) ≤ (Xp - (-141 / 1000000)) * zs :=
    mul_nonneg (by nlinarith only [hXpL]) (by nlinarith only [hzsL])
  have hXpB : (0 : ℝ) ≤
      (-141 / 1000000) * (zs - 403447 / 50000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by norm_num)
      (by nlinarith only [hzsU])
  have hXpzs :
      (-141 / 1000000 : ℝ) * (403447 / 50000000) ≤ Xp * zs := by
    nlinarith only [hXpA, hXpB]
  have hCpA : (0 : ℝ) ≤ Cp * (zd - (-3930853 / 50000000)) :=
    mul_nonneg hCp0 (by nlinarith only [hzdL])
  have hCpB : (0 : ℝ) ≤
      (-3930853 / 50000000) * (Cp - 8241 / 1000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by norm_num)
      (by nlinarith only [hCpU])
  have hCpzd :
      (8241 / 1000000 : ℝ) * (-3930853 / 50000000) ≤ Cp * zd := by
    nlinarith only [hCpA, hCpB]
  have hDpA : (0 : ℝ) ≤
      (Dp - 7817 / 500000) * (-zc) :=
    mul_nonneg (by nlinarith only [hDpL]) (by nlinarith only [hzcU])
  have hDpB : (0 : ℝ) ≤
      (7817 / 500000) * ((-zc) - (-(-44529097 / 4000000000))) :=
    mul_nonneg (by norm_num) (by nlinarith only [hzcU])
  have hDpzc :
      -2 * (7817 / 500000 : ℝ) * (-44529097 / 4000000000) ≤
        -2 * Dp * zc := by
    nlinarith only [hDpA, hDpB]
  have hRpA : (0 : ℝ) ≤ (Rp - 92817 / 500000) * zs :=
    mul_nonneg (by nlinarith only [hRpL]) (by nlinarith only [hzsL])
  have hRpB : (0 : ℝ) ≤
      (92817 / 500000) * (zs - 395077 / 50000000) :=
    mul_nonneg (by norm_num) (by nlinarith only [hzsL])
  have hRpzs :
      (92817 / 500000 : ℝ) * (395077 / 50000000) ≤ Rp * zs := by
    nlinarith only [hRpA, hRpB]
  have hDzdA : (0 : ℝ) ≤
      (Dp - 7817 / 500000) * (-zd) :=
    mul_nonneg (by nlinarith only [hDpL]) (by nlinarith only [hzdU])
  have hDzdB : (0 : ℝ) ≤
      (7817 / 500000) * ((-zd) - (-(-240633 / 3125000))) :=
    mul_nonneg (by norm_num) (by nlinarith only [hzdU])
  have hDpzd :
      (7817 / 500000 : ℝ) * (240633 / 3125000) ≤ -Dp * zd := by
    nlinarith only [hDzdA, hDzdB]
  have hFpA : (0 : ℝ) ≤ Fp * (zc - (-44531887 / 4000000000)) :=
    mul_nonneg hFp0 (by nlinarith only [hzcL])
  have hFpB : (0 : ℝ) ≤
      (-44531887 / 4000000000) * (Fp - 433 / 3125) :=
    mul_nonneg_of_nonpos_of_nonpos (by norm_num)
      (by nlinarith only [hFpU])
  have hFpzc :
      (433 / 3125 : ℝ) * (-44531887 / 4000000000) ≤ Fp * zc := by
    nlinarith only [hFpA, hFpB]
  have hgd : (-601878712267 / 4000000000000000 : ℝ) ≤
      crossGradientD Xp Cp Dp zs zd zc := by
    unfold crossGradientD
    nlinarith only [hXpzs, hCpzd, hDpzc]
  have hg4 : (-83665056247 / 200000000000000 : ℝ) ≤
      crossGradientFour Rp Dp Fp zs zd zc := by
    unfold crossGradientFour
    nlinarith only [hRpzs, hDpzd, hFpzc]
  change (-2 / 1000) * crossGradientD Xp Cp Dp zs zd zc -
      (558 / 10000 / 2) * crossGradientFour Rp Dp Fp zs zd zc ≤
    (25 / 2000000 : ℝ)
  nlinarith only [hgd, hg4]

set_option maxHeartbeats 3000000 in
private theorem alternatingFace_lower
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    evenBlockTwoFace X R C D F a x r c d f u4 ≤
      alternatingFace X R C D F a x r c d f su du u4 sv dv v4 := by
  rcases hbox.X_mem with ⟨hXL, hXU⟩
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.C_mem with ⟨hCL, hCU⟩
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.F_mem with ⟨hFL, hFU⟩
  rcases hbox.a_mem with ⟨haL, haU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  rcases hbox.su_mem with ⟨hsuL, hsuU⟩
  rcases hbox.du_mem with ⟨hduL, hduU⟩
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  rcases hbox.sv_mem with ⟨hsvL, hsvU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  rcases hbox.v4_mem with ⟨hv4L, hv4U⟩
  change alternatingFace X R C D F a x r c d f
      (56173 / 100000) (1687 / 100000) u4
      (53815 / 100000) (558 / 10000) (-2 / 1000) ≤ _
  calc
    alternatingFace X R C D F a x r c d f
        (56173 / 100000) (1687 / 100000) u4
        (53815 / 100000) (558 / 10000) (-2 / 1000) ≤
      alternatingFace X R C D F a x r c d f
        su (1687 / 100000) u4
        (53815 / 100000) (558 / 10000) (-2 / 1000) := by
      refine quadratic_lower_at_right
        (fun z ↦ alternatingFace X R C D F a x r c d f
          z (1687 / 100000) u4
          (53815 / 100000) (558 / 10000) (-2 / 1000))
        ?_ su (56173 / 100000) hsuU ?_
      · unfold IsQuadraticLaw alternatingFace correlatedCoefficientTwo
          alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
          alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
          alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
          mixedDeterminantOne
        intro z
        dsimp only
        ring
      · rw [alternating_su_secant_eq]
        unfold alternatingSuSlope
        have hcoupling : (29 / 4000000 : ℝ) ≤
            alternatingSuCoupling X R C D F a x r c d f
              su (56173 / 100000) (1687 / 100000) u4
              (53815 / 100000) (558 / 10000) (-2 / 1000) := by
          exact alternatingSuCoupling_lower
            A X R C D F a x r c d f su du u4 sv dv v4
            q11 q13 q33 h11 h13 h33 hbox
        have hcross :
            alternatingSuCross X R C D F a x r c d f
                su (56173 / 100000) (1687 / 100000) u4
                (53815 / 100000) (558 / 10000) (-2 / 1000) ≤
              (25 / 2000000 : ℝ) := by
          exact alternatingSuCross_upper
            A X R C D F a x r c d f su du u4 sv dv v4
            q11 q13 q33 h11 h13 h33 hbox
        nlinarith only [hcoupling, hcross]
    _ ≤ alternatingFace X R C D F a x r c d f
        su du u4 (53815 / 100000) (558 / 10000) (-2 / 1000) := by
      refine quadratic_lower_at_left
        (fun z ↦ alternatingFace X R C D F a x r c d f
          su z u4 (53815 / 100000) (558 / 10000) (-2 / 1000))
        ?_ du (1687 / 100000) hduL ?_
      · unfold IsQuadraticLaw alternatingFace correlatedCoefficientTwo
          alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
          alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
          alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
          mixedDeterminantOne
        intro z
        dsimp only
        ring
      · rw [alternating_du_secant_eq]
        have hcoupling : (22 / 100000 : ℝ) ≤
            alternatingDuCoupling X R C D F a x r c d f
              su du (1687 / 100000) u4
              (53815 / 100000) (558 / 10000) (-2 / 1000) := by
          exact alternatingDuCoupling_lower
            A X R C D F a x r c d f su du u4 sv dv v4
            q11 q13 q33 h11 h13 h33 hbox
        have hcross : (-12 / 100000 : ℝ) ≤
            alternatingDuCross X R C D F a x r c d f
              su du (1687 / 100000) u4
              (53815 / 100000) (558 / 10000) (-2 / 1000) := by
          exact alternatingDuCross_lower
            A X R C D F a x r c d f su du u4 sv dv v4
            q11 q13 q33 h11 h13 h33 hbox
        nlinarith only [hcoupling, hcross]
    _ ≤ alternatingFace X R C D F a x r c d f
        su du u4 sv (558 / 10000) (-2 / 1000) := by
      refine quadratic_lower_at_left
        (fun z ↦ alternatingFace X R C D F a x r c d f
          su du u4 z (558 / 10000) (-2 / 1000))
        ?_ sv (53815 / 100000) hsvL ?_
      · unfold IsQuadraticLaw alternatingFace correlatedCoefficientTwo
          alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
          alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
          alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
          mixedDeterminantOne
        intro z
        dsimp only
        ring
      · rw [alternating_sv_secant_eq]
        have hcoupling : (8 / 1000000 : ℝ) ≤
            alternatingSvCoupling X R C D F a x r c d f
              su du u4 sv (53815 / 100000)
              (558 / 10000) (-2 / 1000) := by
          exact alternatingSvCoupling_lower
            A X R C D F a x r c d f su du u4 sv dv v4
            q11 q13 q33 h11 h13 h33 hbox
        have hcross : (-4 / 1000000 : ℝ) ≤
            alternatingSvCross X R C D F a x r c d f
              su du u4 sv (53815 / 100000)
              (558 / 10000) (-2 / 1000) := by
          exact alternatingSvCross_lower
            A X R C D F a x r c d f su du u4 sv dv v4
            q11 q13 q33 h11 h13 h33 hbox
        nlinarith only [hcoupling, hcross]
    _ ≤ alternatingFace X R C D F a x r c d f
        su du u4 sv dv (-2 / 1000) := by
      refine quadratic_lower_at_right
        (fun z ↦ alternatingFace X R C D F a x r c d f
          su du u4 sv z (-2 / 1000))
        ?_ dv (558 / 10000) hdvU ?_
      · unfold IsQuadraticLaw alternatingFace correlatedCoefficientTwo
          alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
          alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
          alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
          mixedDeterminantOne
        intro z
        dsimp only
        ring
      · rw [alternating_dv_secant_eq]
        have hcoupling :
            alternatingDvCoupling X R C D F a x r c d f
                su du u4 sv dv (558 / 10000) (-2 / 1000) ≤
              (-32 / 100000 : ℝ) := by
          exact alternatingDvCoupling_upper
            A X R C D F a x r c d f su du u4 sv dv v4
            q11 q13 q33 h11 h13 h33 hbox
        have hcross :
            alternatingDvCross X R C D F a x r c d f
                su du u4 sv dv (558 / 10000) (-2 / 1000) ≤
              (15 / 100000 : ℝ) := by
          exact alternatingDvCross_upper
            A X R C D F a x r c d f su du u4 sv dv v4
            q11 q13 q33 h11 h13 h33 hbox
        have hsec :
            alternatingDvCoupling X R C D F a x r c d f
                su du u4 sv dv (558 / 10000) (-2 / 1000) +
              alternatingDvCross X R C D F a x r c d f
                su du u4 sv dv (558 / 10000) (-2 / 1000) ≤
              (-17 / 100000 : ℝ) := by
          nlinarith only [hcoupling, hcross]
        nlinarith only [hsec]
    _ ≤ alternatingFace X R C D F a x r c d f
        su du u4 sv dv v4 := by
      refine quadratic_lower_at_right
        (fun z ↦ alternatingFace X R C D F a x r c d f
          su du u4 sv dv z)
        ?_ v4 (-2 / 1000) hv4U ?_
      · unfold IsQuadraticLaw alternatingFace correlatedCoefficientTwo
          alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
          alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
          alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
          mixedDeterminantOne
        intro z
        dsimp only
        ring
      · rw [alternating_v4_secant_eq]
        have hs := alternatingV4Slope_upper
          A X R C D F a x r c d f su du u4 sv dv v4
            q11 q13 q33 h11 h13 h33 hbox
        nlinarith only [hs]

/-! ## The odd-coordinate tail

The alternating block fixes the six odd coefficients at one correlated
corner.  The following face exposes those six coordinates again. -/

private def oddQ11Corner : ℝ := 1778 / 10000
private def oddQ13Corner : ℝ := 2002 / 10000
private def oddQ33Corner : ℝ := 3315 / 10000
private def oddH11Corner : ℝ := 14 / 1000
private def oddH13Corner : ℝ := -9 / 1000
private def oddH33Corner : ℝ := -120 / 1000

private def oddFace
    (X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 : ℝ) : ℝ :=
  correlatedCoefficientTwo
    (137423 / 100000) X R C D F a x r c d f
    su du u4 sv dv v4 q11 q13 q33 h11 h13 h33

private theorem alternatingFace_eq_oddFace_corner
    (X R C D F a x r c d f su du u4 sv dv v4 : ℝ) :
    alternatingFace X R C D F a x r c d f su du u4 sv dv v4 =
      oddFace X R C D F a x r c d f su du u4 sv dv v4
        oddQ11Corner oddQ13Corner oddQ33Corner
        oddH11Corner oddH13Corner oddH33Corner := by
  rfl

private def oddGm (X R C D F a x r c d f : ℝ) : ℝ :=
  alignedDeterminant
    ((137423 / 100000) - a) (X - x) (R - r) (C - c) (D - d) (F - f)

private def oddGx (X R C D F a x r c d f : ℝ) : ℝ :=
  alignedMixedDeterminant
    ((137423 / 100000) - a) (X - x) (R - r) (C - c) (D - d) (F - f)
    ((137423 / 100000) + a) (X + x) (R + r) (C + c) (D + d) (F + f)

private def oddGp (X R C D F a x r c d f : ℝ) : ℝ :=
  alignedMixedDeterminant
    ((137423 / 100000) + a) (X + x) (R + r) (C + c) (D + d) (F + f)
    ((137423 / 100000) - a) (X - x) (R - r) (C - c) (D - d) (F - f)

private def oddP11
    (X R C D F a x r c d f su du u4 sv dv v4 : ℝ) : ℝ :=
  -alignedAdjugatePair
    ((137423 / 100000) - a) (X - x) (R - r) (C - c) (D - d) (F - f)
    sv dv v4 sv dv v4

private def oddP13
    (X R C D F a x r c d f su du u4 sv dv v4 : ℝ) : ℝ :=
  2 * alignedAdjugatePair
    ((137423 / 100000) - a) (X - x) (R - r) (C - c) (D - d) (F - f)
    su du u4 sv dv v4

private def oddP33
    (X R C D F a x r c d f su du u4 sv dv v4 : ℝ) : ℝ :=
  -alignedAdjugatePair
    ((137423 / 100000) - a) (X - x) (R - r) (C - c) (D - d) (F - f)
    su du u4 su du u4

private def oddM11
    (X R C D F a x r c d f su du u4 sv dv v4 : ℝ) : ℝ :=
  -alignedMixedAdjugatePair
    ((137423 / 100000) - a) (X - x) (R - r) (C - c) (D - d) (F - f)
    ((137423 / 100000) + a) (X + x) (R + r) (C + c) (D + d) (F + f)
    sv dv v4 sv dv v4

private def oddM13
    (X R C D F a x r c d f su du u4 sv dv v4 : ℝ) : ℝ :=
  2 * alignedMixedAdjugatePair
    ((137423 / 100000) - a) (X - x) (R - r) (C - c) (D - d) (F - f)
    ((137423 / 100000) + a) (X + x) (R + r) (C + c) (D + d) (F + f)
    su du u4 sv dv v4

private def oddM33
    (X R C D F a x r c d f su du u4 sv dv v4 : ℝ) : ℝ :=
  -alignedMixedAdjugatePair
    ((137423 / 100000) - a) (X - x) (R - r) (C - c) (D - d) (F - f)
    ((137423 / 100000) + a) (X + x) (R + r) (C + c) (D + d) (F + f)
    su du u4 su du u4

private theorem oddFace_rawFour_decomposition
    (X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 : ℝ) :
    oddFace X R C D F a x r c d f su du u4 sv dv v4
        q11 q13 q33 h11 h13 h33 =
      oddGm X R C D F a x r c d f *
          ((q11 - h11) * (q33 - h33) - (q13 - h13) ^ 2) +
        oddGx X R C D F a x r c d f *
          ((q11 + h11) * (q33 - h33) +
            (q11 - h11) * (q33 + h33) -
              2 * (q13 + h13) * (q13 - h13)) +
        oddGp X R C D F a x r c d f *
          ((q11 + h11) * (q33 + h33) - (q13 + h13) ^ 2) +
        oddP11 X R C D F a x r c d f su du u4 sv dv v4 * (q11 - h11) +
        oddP13 X R C D F a x r c d f su du u4 sv dv v4 * (q13 - h13) +
        oddP33 X R C D F a x r c d f su du u4 sv dv v4 * (q33 - h33) +
        oddM11 X R C D F a x r c d f su du u4 sv dv v4 * (q11 + h11) +
        oddM13 X R C D F a x r c d f su du u4 sv dv v4 * (q13 + h13) +
        oddM33 X R C D F a x r c d f su du u4 sv dv v4 * (q33 + h33) +
        alignedCrossEnergy
          ((137423 / 100000) - a) (X - x) (R - r)
          (C - c) (D - d) (F - f) su du u4 sv dv v4 := by
  unfold oddFace correlatedCoefficientTwo oddGm oddGx oddGp
    oddP11 oddP13 oddP33 oddM11 oddM13 oddM33
  dsimp only
  ring

private def oddB11m
    (X R C D F a x r c d f su du u4 sv dv v4 q33 h33 : ℝ) : ℝ :=
  oddGm X R C D F a x r c d f * (q33 - h33) +
    oddGx X R C D F a x r c d f * (q33 + h33) +
      oddP11 X R C D F a x r c d f su du u4 sv dv v4

private def oddB11p
    (X R C D F a x r c d f su du u4 sv dv v4 q33 h33 : ℝ) : ℝ :=
  oddGx X R C D F a x r c d f * (q33 - h33) +
    oddGp X R C D F a x r c d f * (q33 + h33) +
      oddM11 X R C D F a x r c d f su du u4 sv dv v4

private def oddB33m
    (X R C D F a x r c d f su du u4 sv dv v4 q11 h11 : ℝ) : ℝ :=
  oddGm X R C D F a x r c d f * (q11 - h11) +
    oddGx X R C D F a x r c d f * (q11 + h11) +
      oddP33 X R C D F a x r c d f su du u4 sv dv v4

private def oddB33p
    (X R C D F a x r c d f su du u4 sv dv v4 q11 h11 : ℝ) : ℝ :=
  oddGx X R C D F a x r c d f * (q11 - h11) +
    oddGp X R C D F a x r c d f * (q11 + h11) +
      oddM33 X R C D F a x r c d f su du u4 sv dv v4

private def oddB13m
    (X R C D F a x r c d f su du u4 sv dv v4 q13 h13 : ℝ) : ℝ :=
  -2 * oddGm X R C D F a x r c d f * (q13 - h13) -
    2 * oddGx X R C D F a x r c d f * (q13 + h13) +
      oddP13 X R C D F a x r c d f su du u4 sv dv v4

private def oddB13p
    (X R C D F a x r c d f su du u4 sv dv v4 q13 h13 : ℝ) : ℝ :=
  -2 * oddGx X R C D F a x r c d f * (q13 - h13) -
    2 * oddGp X R C D F a x r c d f * (q13 + h13) +
      oddM13 X R C D F a x r c d f su du u4 sv dv v4

private def oddH33Slope
    (X R C D F a x r c d f su du u4 sv dv v4 : ℝ) : ℝ :=
  -oddB33m X R C D F a x r c d f su du u4 sv dv v4
      oddQ11Corner oddH11Corner +
    oddB33p X R C D F a x r c d f su du u4 sv dv v4
      oddQ11Corner oddH11Corner

private def oddH13Slope
    (X R C D F a x r c d f su du u4 sv dv v4 h13 : ℝ) : ℝ :=
  let hbar := (h13 + oddH13Corner) / 2
  (-oddB13m X R C D F a x r c d f su du u4 sv dv v4
        oddQ13Corner hbar +
      oddB13p X R C D F a x r c d f su du u4 sv dv v4
        oddQ13Corner hbar)

private def oddH11Slope
    (X R C D F a x r c d f su du u4 sv dv v4 h33 : ℝ) : ℝ :=
  -oddB11m X R C D F a x r c d f su du u4 sv dv v4
      oddQ33Corner h33 +
    oddB11p X R C D F a x r c d f su du u4 sv dv v4
      oddQ33Corner h33

private def oddQ33Slope
    (X R C D F a x r c d f su du u4 sv dv v4 h11 : ℝ) : ℝ :=
  oddB33m X R C D F a x r c d f su du u4 sv dv v4
      oddQ11Corner h11 +
    oddB33p X R C D F a x r c d f su du u4 sv dv v4
      oddQ11Corner h11

private def oddQ13Slope
    (X R C D F a x r c d f su du u4 sv dv v4 q13 h13 : ℝ) : ℝ :=
  let qbar := (q13 + oddQ13Corner) / 2
  (oddB13m X R C D F a x r c d f su du u4 sv dv v4 qbar h13 +
    oddB13p X R C D F a x r c d f su du u4 sv dv v4 qbar h13)

private def oddQ11Slope
    (X R C D F a x r c d f su du u4 sv dv v4 q33 h33 : ℝ) : ℝ :=
  oddB11m X R C D F a x r c d f su du u4 sv dv v4 q33 h33 +
    oddB11p X R C D F a x r c d f su du u4 sv dv v4 q33 h33

set_option maxHeartbeats 3000000 in
private theorem odd_h33_secant_eq
    (X R C D F a x r c d f su du u4 sv dv v4 h33 : ℝ) :
    quadraticSecant
        (fun z ↦ oddFace X R C D F a x r c d f su du u4 sv dv v4
          oddQ11Corner oddQ13Corner oddQ33Corner
          oddH11Corner oddH13Corner z)
        h33 oddH33Corner =
      oddH33Slope X R C D F a x r c d f su du u4 sv dv v4 := by
  unfold quadraticSecant oddFace correlatedCoefficientTwo oddH33Slope
    oddB33m oddB33p oddGm oddGx oddGp oddP33 oddM33
    oddQ11Corner oddQ13Corner oddQ33Corner oddH11Corner oddH13Corner
    oddH33Corner
  dsimp only
  ring

set_option maxHeartbeats 3000000 in
private theorem odd_h13_secant_eq
    (X R C D F a x r c d f su du u4 sv dv v4 h13 h33 : ℝ) :
    quadraticSecant
        (fun z ↦ oddFace X R C D F a x r c d f su du u4 sv dv v4
          oddQ11Corner oddQ13Corner oddQ33Corner oddH11Corner z h33)
        h13 oddH13Corner =
      oddH13Slope X R C D F a x r c d f su du u4 sv dv v4 h13 := by
  unfold quadraticSecant oddFace correlatedCoefficientTwo oddH13Slope
    oddB13m oddB13p oddGm oddGx oddGp oddP13 oddM13
    oddQ11Corner oddQ13Corner oddQ33Corner oddH11Corner oddH13Corner
  dsimp only
  ring

set_option maxHeartbeats 3000000 in
private theorem odd_h11_secant_eq
    (X R C D F a x r c d f su du u4 sv dv v4 h11 h13 h33 : ℝ) :
    quadraticSecant
        (fun z ↦ oddFace X R C D F a x r c d f su du u4 sv dv v4
          oddQ11Corner oddQ13Corner oddQ33Corner z h13 h33)
        h11 oddH11Corner =
      oddH11Slope X R C D F a x r c d f su du u4 sv dv v4 h33 := by
  unfold quadraticSecant oddFace correlatedCoefficientTwo oddH11Slope
    oddB11m oddB11p oddGm oddGx oddGp oddP11 oddM11
    oddQ11Corner oddQ13Corner oddQ33Corner oddH11Corner
  dsimp only
  ring

set_option maxHeartbeats 3000000 in
private theorem odd_q33_secant_eq
    (X R C D F a x r c d f su du u4 sv dv v4
      q33 h11 h13 h33 : ℝ) :
    quadraticSecant
        (fun z ↦ oddFace X R C D F a x r c d f su du u4 sv dv v4
          oddQ11Corner oddQ13Corner z h11 h13 h33)
        q33 oddQ33Corner =
      oddQ33Slope X R C D F a x r c d f su du u4 sv dv v4 h11 := by
  unfold quadraticSecant oddFace correlatedCoefficientTwo oddQ33Slope
    oddB33m oddB33p oddGm oddGx oddGp oddP33 oddM33
    oddQ11Corner oddQ13Corner oddQ33Corner
  dsimp only
  ring

set_option maxHeartbeats 3000000 in
private theorem odd_q13_secant_eq
    (X R C D F a x r c d f su du u4 sv dv v4
      q13 q33 h11 h13 h33 : ℝ) :
    quadraticSecant
        (fun z ↦ oddFace X R C D F a x r c d f su du u4 sv dv v4
          oddQ11Corner z q33 h11 h13 h33)
        q13 oddQ13Corner =
      oddQ13Slope X R C D F a x r c d f su du u4 sv dv v4 q13 h13 := by
  unfold quadraticSecant oddFace correlatedCoefficientTwo oddQ13Slope
    oddB13m oddB13p oddGm oddGx oddGp oddP13 oddM13
    oddQ11Corner oddQ13Corner
  dsimp only
  ring

set_option maxHeartbeats 3000000 in
private theorem odd_q11_secant_eq
    (X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 : ℝ) :
    quadraticSecant
        (fun z ↦ oddFace X R C D F a x r c d f su du u4 sv dv v4
          z q13 q33 h11 h13 h33)
        q11 oddQ11Corner =
      oddQ11Slope X R C D F a x r c d f su du u4 sv dv v4 q33 h33 := by
  unfold quadraticSecant oddFace correlatedCoefficientTwo oddQ11Slope
    oddB11m oddB11p oddGm oddGx oddGp oddP11 oddM11 oddQ11Corner
  dsimp only
  ring

set_option maxHeartbeats 3000000 in
private theorem odd_h33_lower_of_slope
    (X R C D F a x r c d f su du u4 sv dv v4 h33 : ℝ)
    (hh33 : oddH33Corner ≤ h33)
    (hslope :
      0 ≤ oddH33Slope X R C D F a x r c d f su du u4 sv dv v4) :
    oddFace X R C D F a x r c d f su du u4 sv dv v4
        oddQ11Corner oddQ13Corner oddQ33Corner
        oddH11Corner oddH13Corner oddH33Corner ≤
      oddFace X R C D F a x r c d f su du u4 sv dv v4
        oddQ11Corner oddQ13Corner oddQ33Corner
        oddH11Corner oddH13Corner h33 := by
  refine quadratic_lower_at_left
    (fun z ↦ oddFace X R C D F a x r c d f su du u4 sv dv v4
      oddQ11Corner oddQ13Corner oddQ33Corner
      oddH11Corner oddH13Corner z)
    ?_ h33 oddH33Corner hh33 ?_
  · unfold IsQuadraticLaw oddFace correlatedCoefficientTwo
      alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
      alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
      alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
      mixedDeterminantOne
    intro z
    dsimp only
    ring
  · rw [odd_h33_secant_eq]
    exact hslope

set_option maxHeartbeats 3000000 in
private theorem odd_h13_lower_of_slope
    (X R C D F a x r c d f su du u4 sv dv v4 h13 h33 : ℝ)
    (hh13 : h13 ≤ oddH13Corner)
    (hslope :
      oddH13Slope X R C D F a x r c d f su du u4 sv dv v4 h13 ≤ 0) :
    oddFace X R C D F a x r c d f su du u4 sv dv v4
        oddQ11Corner oddQ13Corner oddQ33Corner
        oddH11Corner oddH13Corner h33 ≤
      oddFace X R C D F a x r c d f su du u4 sv dv v4
        oddQ11Corner oddQ13Corner oddQ33Corner oddH11Corner h13 h33 := by
  refine quadratic_lower_at_right
    (fun z ↦ oddFace X R C D F a x r c d f su du u4 sv dv v4
      oddQ11Corner oddQ13Corner oddQ33Corner oddH11Corner z h33)
    ?_ h13 oddH13Corner hh13 ?_
  · unfold IsQuadraticLaw oddFace correlatedCoefficientTwo
      alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
      alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
      alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
      mixedDeterminantOne
    intro z
    dsimp only
    ring
  · rw [odd_h13_secant_eq]
    exact hslope

set_option maxHeartbeats 3000000 in
private theorem odd_h11_lower_of_slope
    (X R C D F a x r c d f su du u4 sv dv v4 h11 h13 h33 : ℝ)
    (hh11 : oddH11Corner ≤ h11)
    (hslope :
      0 ≤ oddH11Slope X R C D F a x r c d f su du u4 sv dv v4 h33) :
    oddFace X R C D F a x r c d f su du u4 sv dv v4
        oddQ11Corner oddQ13Corner oddQ33Corner oddH11Corner h13 h33 ≤
      oddFace X R C D F a x r c d f su du u4 sv dv v4
        oddQ11Corner oddQ13Corner oddQ33Corner h11 h13 h33 := by
  refine quadratic_lower_at_left
    (fun z ↦ oddFace X R C D F a x r c d f su du u4 sv dv v4
      oddQ11Corner oddQ13Corner oddQ33Corner z h13 h33)
    ?_ h11 oddH11Corner hh11 ?_
  · unfold IsQuadraticLaw oddFace correlatedCoefficientTwo
      alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
      alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
      alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
      mixedDeterminantOne
    intro z
    dsimp only
    ring
  · rw [odd_h11_secant_eq]
    exact hslope

set_option maxHeartbeats 3000000 in
private theorem odd_q33_lower_of_slope
    (X R C D F a x r c d f su du u4 sv dv v4
      q33 h11 h13 h33 : ℝ)
    (hq33 : oddQ33Corner ≤ q33)
    (hslope :
      0 ≤ oddQ33Slope X R C D F a x r c d f su du u4 sv dv v4 h11) :
    oddFace X R C D F a x r c d f su du u4 sv dv v4
        oddQ11Corner oddQ13Corner oddQ33Corner h11 h13 h33 ≤
      oddFace X R C D F a x r c d f su du u4 sv dv v4
        oddQ11Corner oddQ13Corner q33 h11 h13 h33 := by
  refine quadratic_lower_at_left
    (fun z ↦ oddFace X R C D F a x r c d f su du u4 sv dv v4
      oddQ11Corner oddQ13Corner z h11 h13 h33)
    ?_ q33 oddQ33Corner hq33 ?_
  · unfold IsQuadraticLaw oddFace correlatedCoefficientTwo
      alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
      alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
      alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
      mixedDeterminantOne
    intro z
    dsimp only
    ring
  · rw [odd_q33_secant_eq]
    exact hslope

set_option maxHeartbeats 3000000 in
private theorem odd_q13_lower_of_slope
    (X R C D F a x r c d f su du u4 sv dv v4
      q13 q33 h11 h13 h33 : ℝ)
    (hq13 : q13 ≤ oddQ13Corner)
    (hslope :
      oddQ13Slope X R C D F a x r c d f su du u4 sv dv v4 q13 h13 ≤ 0) :
    oddFace X R C D F a x r c d f su du u4 sv dv v4
        oddQ11Corner oddQ13Corner q33 h11 h13 h33 ≤
      oddFace X R C D F a x r c d f su du u4 sv dv v4
        oddQ11Corner q13 q33 h11 h13 h33 := by
  refine quadratic_lower_at_right
    (fun z ↦ oddFace X R C D F a x r c d f su du u4 sv dv v4
      oddQ11Corner z q33 h11 h13 h33)
    ?_ q13 oddQ13Corner hq13 ?_
  · unfold IsQuadraticLaw oddFace correlatedCoefficientTwo
      alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
      alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
      alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
      mixedDeterminantOne
    intro z
    dsimp only
    ring
  · rw [odd_q13_secant_eq]
    exact hslope

set_option maxHeartbeats 3000000 in
private theorem odd_q11_lower_of_slope
    (X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 : ℝ)
    (hq11 : oddQ11Corner ≤ q11)
    (hslope :
      0 ≤ oddQ11Slope X R C D F a x r c d f su du u4 sv dv v4 q33 h33) :
    oddFace X R C D F a x r c d f su du u4 sv dv v4
        oddQ11Corner q13 q33 h11 h13 h33 ≤
      oddFace X R C D F a x r c d f su du u4 sv dv v4
        q11 q13 q33 h11 h13 h33 := by
  refine quadratic_lower_at_left
    (fun z ↦ oddFace X R C D F a x r c d f su du u4 sv dv v4
      z q13 q33 h11 h13 h33)
    ?_ q11 oddQ11Corner hq11 ?_
  · unfold IsQuadraticLaw oddFace correlatedCoefficientTwo
      alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
      alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
      alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
      mixedDeterminantOne
    intro z
    dsimp only
    ring
  · rw [odd_q11_secant_eq]
    exact hslope

/-! ### Structural bounds for the `B₁₁⁻` coefficient

The three even coordinates `su`, `du`, and `u4` are phantom arguments of
`oddB11m`: its adjugate term uses only the `v` row.  Removing those arguments
leaves the exact sixteen-coordinate polynomial used below. -/

private def oddB11mCore
    (X R C D F a x r c d f sv dv v4 q33 h33 : ℝ) : ℝ :=
  oddB11m X R C D F a x r c d f 0 0 0 sv dv v4 q33 h33

private theorem oddB11m_eq_core
    (X R C D F a x r c d f su du u4 sv dv v4 q33 h33 : ℝ) :
    oddB11m X R C D F a x r c d f
        su du u4 sv dv v4 q33 h33 =
      oddB11mCore X R C D F a x r c d f sv dv v4 q33 h33 := by
  rfl

private structure OddB11mEndpoint where
  q33Value : ℝ
  h33Value : ℝ
  svValue : ℝ
  v4Value : ℝ
  bigX : ℝ
  bigR : ℝ
  bigC : ℝ
  bigD : ℝ
  bigF : ℝ
  littleA : ℝ
  littleX : ℝ
  littleR : ℝ
  littleC : ℝ
  littleD : ℝ
  littleF : ℝ
  dvValue : ℝ

private def oddB11mLowerEndpoint : OddB11mEndpoint where
  q33Value := 663 / 2000
  h33Value := -3 / 25
  svValue := 13459 / 25000
  v4Value := -1 / 250
  bigX := 3977 / 100000
  bigR := 121449 / 500000
  bigC := 1323 / 100000
  bigD := 21449 / 500000
  bigF := 1571 / 5000
  littleA := 165293 / 200000
  littleX := 37851 / 1000000
  littleR := 49817 / 1000000
  littleC := 1433 / 200000
  littleD := 23317 / 1000000
  littleF := 552 / 3125
  dvValue := 111 / 2000

private def oddB11mUpperEndpoint : OddB11mEndpoint where
  q33Value := 333 / 1000
  h33Value := -117 / 1000
  svValue := 10763 / 20000
  v4Value := -1 / 500
  bigX := 1981 / 50000
  bigR := 242817 / 1000000
  bigC := 671 / 50000
  bigD := 42817 / 1000000
  bigF := 63 / 200
  littleA := 824479 / 1000000
  littleX := 39761 / 1000000
  littleR := 57183 / 1000000
  littleC := 5179 / 1000000
  littleD := 27183 / 1000000
  littleF := 4411 / 25000
  dvValue := 111 / 2000

private def oddB11mSlopeQ33 (e : OddB11mEndpoint)
    (X R C D F a x r c d f sv dv v4 q33 h33 : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ oddB11mCore X R C D F a x r c d f sv dv v4 z h33)
    q33 e.q33Value

private def oddB11mSlopeH33 (e : OddB11mEndpoint)
    (X R C D F a x r c d f sv dv v4 h33 : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ oddB11mCore X R C D F a x r c d f
      sv dv v4 e.q33Value z)
    h33 e.h33Value

private def oddB11mSlopeSv (e : OddB11mEndpoint)
    (X R C D F a x r c d f sv dv v4 : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ oddB11mCore X R C D F a x r c d f
      z dv v4 e.q33Value e.h33Value)
    sv e.svValue

private def oddB11mSlopeV4 (e : OddB11mEndpoint)
    (X R C D F a x r c d f dv v4 : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ oddB11mCore X R C D F a x r c d f
      e.svValue dv z e.q33Value e.h33Value)
    v4 e.v4Value

private def oddB11mSlopeX (e : OddB11mEndpoint)
    (X R C D F a x r c d f dv : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ oddB11mCore z R C D F a x r c d f
      e.svValue dv e.v4Value e.q33Value e.h33Value)
    X e.bigX

private def oddB11mSlopeR (e : OddB11mEndpoint)
    (R C D F a x r c d f dv : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ oddB11mCore e.bigX z C D F a x r c d f
      e.svValue dv e.v4Value e.q33Value e.h33Value)
    R e.bigR

private def oddB11mSlopeC (e : OddB11mEndpoint)
    (C D F a x r c d f dv : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ oddB11mCore e.bigX e.bigR z D F a x r c d f
      e.svValue dv e.v4Value e.q33Value e.h33Value)
    C e.bigC

private def oddB11mSlopeD (e : OddB11mEndpoint)
    (D F a x r c d f dv : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ oddB11mCore e.bigX e.bigR e.bigC z F a x r c d f
      e.svValue dv e.v4Value e.q33Value e.h33Value)
    D e.bigD

private def oddB11mSlopeF (e : OddB11mEndpoint)
    (F a x r c d f dv : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ oddB11mCore e.bigX e.bigR e.bigC e.bigD z a x r c d f
      e.svValue dv e.v4Value e.q33Value e.h33Value)
    F e.bigF

private def oddB11mSlopeA (e : OddB11mEndpoint)
    (a x r c d f dv : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ oddB11mCore e.bigX e.bigR e.bigC e.bigD e.bigF
      z x r c d f e.svValue dv e.v4Value e.q33Value e.h33Value)
    a e.littleA

private def oddB11mSlopeLittleX (e : OddB11mEndpoint)
    (x r c d f dv : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ oddB11mCore e.bigX e.bigR e.bigC e.bigD e.bigF
      e.littleA z r c d f e.svValue dv e.v4Value
      e.q33Value e.h33Value)
    x e.littleX

private def oddB11mSlopeLittleR (e : OddB11mEndpoint)
    (r c d f dv : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ oddB11mCore e.bigX e.bigR e.bigC e.bigD e.bigF
      e.littleA e.littleX z c d f e.svValue dv e.v4Value
      e.q33Value e.h33Value)
    r e.littleR

private def oddB11mSlopeLittleC (e : OddB11mEndpoint)
    (c d f dv : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ oddB11mCore e.bigX e.bigR e.bigC e.bigD e.bigF
      e.littleA e.littleX e.littleR z d f e.svValue dv e.v4Value
      e.q33Value e.h33Value)
    c e.littleC

private def oddB11mSlopeLittleD (e : OddB11mEndpoint)
    (d f dv : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ oddB11mCore e.bigX e.bigR e.bigC e.bigD e.bigF
      e.littleA e.littleX e.littleR e.littleC z f
      e.svValue dv e.v4Value e.q33Value e.h33Value)
    d e.littleD

private def oddB11mSlopeLittleF (e : OddB11mEndpoint)
    (f dv : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ oddB11mCore e.bigX e.bigR e.bigC e.bigD e.bigF
      e.littleA e.littleX e.littleR e.littleC e.littleD z
      e.svValue dv e.v4Value e.q33Value e.h33Value)
    f e.littleF

private def oddB11mSlopeDv (e : OddB11mEndpoint) (dv : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ oddB11mCore e.bigX e.bigR e.bigC e.bigD e.bigF
      e.littleA e.littleX e.littleR e.littleC e.littleD e.littleF
      e.svValue z e.v4Value e.q33Value e.h33Value)
    dv e.dvValue

private def oddB11mEndpointValue (e : OddB11mEndpoint) : ℝ :=
  oddB11mCore e.bigX e.bigR e.bigC e.bigD e.bigF
    e.littleA e.littleX e.littleR e.littleC e.littleD e.littleF
    e.svValue e.dvValue e.v4Value e.q33Value e.h33Value

set_option maxHeartbeats 3000000 in
private theorem oddB11m_telescope
    (e : OddB11mEndpoint)
    (X R C D F a x r c d f sv dv v4 q33 h33 : ℝ) :
    oddB11mCore X R C D F a x r c d f sv dv v4 q33 h33 -
        oddB11mEndpointValue e =
      (q33 - e.q33Value) *
          oddB11mSlopeQ33 e X R C D F a x r c d f
            sv dv v4 q33 h33 +
        (h33 - e.h33Value) *
          oddB11mSlopeH33 e X R C D F a x r c d f sv dv v4 h33 +
        (sv - e.svValue) *
          oddB11mSlopeSv e X R C D F a x r c d f sv dv v4 +
        (v4 - e.v4Value) *
          oddB11mSlopeV4 e X R C D F a x r c d f dv v4 +
        (X - e.bigX) *
          oddB11mSlopeX e X R C D F a x r c d f dv +
        (R - e.bigR) *
          oddB11mSlopeR e R C D F a x r c d f dv +
        (C - e.bigC) *
          oddB11mSlopeC e C D F a x r c d f dv +
        (D - e.bigD) *
          oddB11mSlopeD e D F a x r c d f dv +
        (F - e.bigF) *
          oddB11mSlopeF e F a x r c d f dv +
        (a - e.littleA) *
          oddB11mSlopeA e a x r c d f dv +
        (x - e.littleX) *
          oddB11mSlopeLittleX e x r c d f dv +
        (r - e.littleR) *
          oddB11mSlopeLittleR e r c d f dv +
        (c - e.littleC) *
          oddB11mSlopeLittleC e c d f dv +
        (d - e.littleD) *
          oddB11mSlopeLittleD e d f dv +
        (f - e.littleF) *
          oddB11mSlopeLittleF e f dv +
        (dv - e.dvValue) * oddB11mSlopeDv e dv := by
  unfold oddB11mEndpointValue oddB11mSlopeQ33 oddB11mSlopeH33
    oddB11mSlopeSv oddB11mSlopeV4 oddB11mSlopeX oddB11mSlopeR
    oddB11mSlopeC oddB11mSlopeD oddB11mSlopeF oddB11mSlopeA
    oddB11mSlopeLittleX oddB11mSlopeLittleR oddB11mSlopeLittleC
    oddB11mSlopeLittleD oddB11mSlopeLittleF oddB11mSlopeDv
    quadraticSecant oddB11mCore oddB11m oddGm oddGx oddP11
    alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
    alignedEntry00 alignedEntry02 alignedEntry04 alignedEntry22
    alignedEntry24 mixedDeterminantOne
  dsimp only
  ring

private theorem oddB11m_lower_telescope
    (X R C D F a x r c d f sv dv v4 q33 h33 : ℝ) :
    oddB11mCore X R C D F a x r c d f sv dv v4 q33 h33 -
        oddB11mEndpointValue oddB11mLowerEndpoint =
      (q33 - oddB11mLowerEndpoint.q33Value) *
          oddB11mSlopeQ33 oddB11mLowerEndpoint
            X R C D F a x r c d f sv dv v4 q33 h33 +
        (h33 - oddB11mLowerEndpoint.h33Value) *
          oddB11mSlopeH33 oddB11mLowerEndpoint
            X R C D F a x r c d f sv dv v4 h33 +
        (sv - oddB11mLowerEndpoint.svValue) *
          oddB11mSlopeSv oddB11mLowerEndpoint
            X R C D F a x r c d f sv dv v4 +
        (v4 - oddB11mLowerEndpoint.v4Value) *
          oddB11mSlopeV4 oddB11mLowerEndpoint
            X R C D F a x r c d f dv v4 +
        (X - oddB11mLowerEndpoint.bigX) *
          oddB11mSlopeX oddB11mLowerEndpoint
            X R C D F a x r c d f dv +
        (R - oddB11mLowerEndpoint.bigR) *
          oddB11mSlopeR oddB11mLowerEndpoint R C D F a x r c d f dv +
        (C - oddB11mLowerEndpoint.bigC) *
          oddB11mSlopeC oddB11mLowerEndpoint C D F a x r c d f dv +
        (D - oddB11mLowerEndpoint.bigD) *
          oddB11mSlopeD oddB11mLowerEndpoint D F a x r c d f dv +
        (F - oddB11mLowerEndpoint.bigF) *
          oddB11mSlopeF oddB11mLowerEndpoint F a x r c d f dv +
        (a - oddB11mLowerEndpoint.littleA) *
          oddB11mSlopeA oddB11mLowerEndpoint a x r c d f dv +
        (x - oddB11mLowerEndpoint.littleX) *
          oddB11mSlopeLittleX oddB11mLowerEndpoint x r c d f dv +
        (r - oddB11mLowerEndpoint.littleR) *
          oddB11mSlopeLittleR oddB11mLowerEndpoint r c d f dv +
        (c - oddB11mLowerEndpoint.littleC) *
          oddB11mSlopeLittleC oddB11mLowerEndpoint c d f dv +
        (d - oddB11mLowerEndpoint.littleD) *
          oddB11mSlopeLittleD oddB11mLowerEndpoint d f dv +
        (f - oddB11mLowerEndpoint.littleF) *
          oddB11mSlopeLittleF oddB11mLowerEndpoint f dv +
        (dv - oddB11mLowerEndpoint.dvValue) *
          oddB11mSlopeDv oddB11mLowerEndpoint dv := by
  exact oddB11m_telescope oddB11mLowerEndpoint
    X R C D F a x r c d f sv dv v4 q33 h33

private theorem oddB11m_upper_telescope
    (X R C D F a x r c d f sv dv v4 q33 h33 : ℝ) :
    oddB11mCore X R C D F a x r c d f sv dv v4 q33 h33 -
        oddB11mEndpointValue oddB11mUpperEndpoint =
      (q33 - oddB11mUpperEndpoint.q33Value) *
          oddB11mSlopeQ33 oddB11mUpperEndpoint
            X R C D F a x r c d f sv dv v4 q33 h33 +
        (h33 - oddB11mUpperEndpoint.h33Value) *
          oddB11mSlopeH33 oddB11mUpperEndpoint
            X R C D F a x r c d f sv dv v4 h33 +
        (sv - oddB11mUpperEndpoint.svValue) *
          oddB11mSlopeSv oddB11mUpperEndpoint
            X R C D F a x r c d f sv dv v4 +
        (v4 - oddB11mUpperEndpoint.v4Value) *
          oddB11mSlopeV4 oddB11mUpperEndpoint
            X R C D F a x r c d f dv v4 +
        (X - oddB11mUpperEndpoint.bigX) *
          oddB11mSlopeX oddB11mUpperEndpoint
            X R C D F a x r c d f dv +
        (R - oddB11mUpperEndpoint.bigR) *
          oddB11mSlopeR oddB11mUpperEndpoint R C D F a x r c d f dv +
        (C - oddB11mUpperEndpoint.bigC) *
          oddB11mSlopeC oddB11mUpperEndpoint C D F a x r c d f dv +
        (D - oddB11mUpperEndpoint.bigD) *
          oddB11mSlopeD oddB11mUpperEndpoint D F a x r c d f dv +
        (F - oddB11mUpperEndpoint.bigF) *
          oddB11mSlopeF oddB11mUpperEndpoint F a x r c d f dv +
        (a - oddB11mUpperEndpoint.littleA) *
          oddB11mSlopeA oddB11mUpperEndpoint a x r c d f dv +
        (x - oddB11mUpperEndpoint.littleX) *
          oddB11mSlopeLittleX oddB11mUpperEndpoint x r c d f dv +
        (r - oddB11mUpperEndpoint.littleR) *
          oddB11mSlopeLittleR oddB11mUpperEndpoint r c d f dv +
        (c - oddB11mUpperEndpoint.littleC) *
          oddB11mSlopeLittleC oddB11mUpperEndpoint c d f dv +
        (d - oddB11mUpperEndpoint.littleD) *
          oddB11mSlopeLittleD oddB11mUpperEndpoint d f dv +
        (f - oddB11mUpperEndpoint.littleF) *
          oddB11mSlopeLittleF oddB11mUpperEndpoint f dv +
        (dv - oddB11mUpperEndpoint.dvValue) *
          oddB11mSlopeDv oddB11mUpperEndpoint dv := by
  exact oddB11m_telescope oddB11mUpperEndpoint
    X R C D F a x r c d f sv dv v4 q33 h33

/-! The `B₁₁⁺` lower bound uses the same sixteen-coordinate order, but a
different endpoint in the `v4` and `dv` coordinates. -/

private def oddB11pCore
    (X R C D F a x r c d f sv dv v4 q33 h33 : ℝ) : ℝ :=
  oddB11p X R C D F a x r c d f 0 0 0 sv dv v4 q33 h33

private theorem oddB11p_eq_core
    (X R C D F a x r c d f su du u4 sv dv v4 q33 h33 : ℝ) :
    oddB11p X R C D F a x r c d f
        su du u4 sv dv v4 q33 h33 =
      oddB11pCore X R C D F a x r c d f sv dv v4 q33 h33 := by
  rfl

private def oddB11pLowerEndpoint : OddB11mEndpoint where
  q33Value := 663 / 2000
  h33Value := -3 / 25
  svValue := 13459 / 25000
  v4Value := -1 / 500
  bigX := 3977 / 100000
  bigR := 121449 / 500000
  bigC := 1323 / 100000
  bigD := 21449 / 500000
  bigF := 1571 / 5000
  littleA := 165293 / 200000
  littleX := 37851 / 1000000
  littleR := 49817 / 1000000
  littleC := 1433 / 200000
  littleD := 23317 / 1000000
  littleF := 552 / 3125
  dvValue := 279 / 5000

private def oddB11pSlopeQ33 (e : OddB11mEndpoint)
    (X R C D F a x r c d f sv dv v4 q33 h33 : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ oddB11pCore X R C D F a x r c d f sv dv v4 z h33)
    q33 e.q33Value

private def oddB11pSlopeH33 (e : OddB11mEndpoint)
    (X R C D F a x r c d f sv dv v4 h33 : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ oddB11pCore X R C D F a x r c d f
      sv dv v4 e.q33Value z)
    h33 e.h33Value

private def oddB11pSlopeSv (e : OddB11mEndpoint)
    (X R C D F a x r c d f sv dv v4 : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ oddB11pCore X R C D F a x r c d f
      z dv v4 e.q33Value e.h33Value)
    sv e.svValue

private def oddB11pSlopeV4 (e : OddB11mEndpoint)
    (X R C D F a x r c d f dv v4 : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ oddB11pCore X R C D F a x r c d f
      e.svValue dv z e.q33Value e.h33Value)
    v4 e.v4Value

private def oddB11pSlopeX (e : OddB11mEndpoint)
    (X R C D F a x r c d f dv : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ oddB11pCore z R C D F a x r c d f
      e.svValue dv e.v4Value e.q33Value e.h33Value)
    X e.bigX

private def oddB11pSlopeR (e : OddB11mEndpoint)
    (R C D F a x r c d f dv : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ oddB11pCore e.bigX z C D F a x r c d f
      e.svValue dv e.v4Value e.q33Value e.h33Value)
    R e.bigR

private def oddB11pSlopeC (e : OddB11mEndpoint)
    (C D F a x r c d f dv : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ oddB11pCore e.bigX e.bigR z D F a x r c d f
      e.svValue dv e.v4Value e.q33Value e.h33Value)
    C e.bigC

private def oddB11pSlopeD (e : OddB11mEndpoint)
    (D F a x r c d f dv : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ oddB11pCore e.bigX e.bigR e.bigC z F a x r c d f
      e.svValue dv e.v4Value e.q33Value e.h33Value)
    D e.bigD

private def oddB11pSlopeF (e : OddB11mEndpoint)
    (F a x r c d f dv : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ oddB11pCore e.bigX e.bigR e.bigC e.bigD z a x r c d f
      e.svValue dv e.v4Value e.q33Value e.h33Value)
    F e.bigF

private def oddB11pSlopeA (e : OddB11mEndpoint)
    (a x r c d f dv : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ oddB11pCore e.bigX e.bigR e.bigC e.bigD e.bigF
      z x r c d f e.svValue dv e.v4Value e.q33Value e.h33Value)
    a e.littleA

private def oddB11pSlopeLittleX (e : OddB11mEndpoint)
    (x r c d f dv : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ oddB11pCore e.bigX e.bigR e.bigC e.bigD e.bigF
      e.littleA z r c d f e.svValue dv e.v4Value
      e.q33Value e.h33Value)
    x e.littleX

private def oddB11pSlopeLittleR (e : OddB11mEndpoint)
    (r c d f dv : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ oddB11pCore e.bigX e.bigR e.bigC e.bigD e.bigF
      e.littleA e.littleX z c d f e.svValue dv e.v4Value
      e.q33Value e.h33Value)
    r e.littleR

private def oddB11pSlopeLittleC (e : OddB11mEndpoint)
    (c d f dv : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ oddB11pCore e.bigX e.bigR e.bigC e.bigD e.bigF
      e.littleA e.littleX e.littleR z d f e.svValue dv e.v4Value
      e.q33Value e.h33Value)
    c e.littleC

private def oddB11pSlopeLittleD (e : OddB11mEndpoint)
    (d f dv : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ oddB11pCore e.bigX e.bigR e.bigC e.bigD e.bigF
      e.littleA e.littleX e.littleR e.littleC z f
      e.svValue dv e.v4Value e.q33Value e.h33Value)
    d e.littleD

private def oddB11pSlopeLittleF (e : OddB11mEndpoint)
    (f dv : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ oddB11pCore e.bigX e.bigR e.bigC e.bigD e.bigF
      e.littleA e.littleX e.littleR e.littleC e.littleD z
      e.svValue dv e.v4Value e.q33Value e.h33Value)
    f e.littleF

private def oddB11pSlopeDv (e : OddB11mEndpoint) (dv : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ oddB11pCore e.bigX e.bigR e.bigC e.bigD e.bigF
      e.littleA e.littleX e.littleR e.littleC e.littleD e.littleF
      e.svValue z e.v4Value e.q33Value e.h33Value)
    dv e.dvValue

private def oddB11pEndpointValue (e : OddB11mEndpoint) : ℝ :=
  oddB11pCore e.bigX e.bigR e.bigC e.bigD e.bigF
    e.littleA e.littleX e.littleR e.littleC e.littleD e.littleF
    e.svValue e.dvValue e.v4Value e.q33Value e.h33Value

set_option maxHeartbeats 3000000 in
private theorem oddB11p_telescope
    (e : OddB11mEndpoint)
    (X R C D F a x r c d f sv dv v4 q33 h33 : ℝ) :
    oddB11pCore X R C D F a x r c d f sv dv v4 q33 h33 -
        oddB11pEndpointValue e =
      (q33 - e.q33Value) *
          oddB11pSlopeQ33 e X R C D F a x r c d f
            sv dv v4 q33 h33 +
        (h33 - e.h33Value) *
          oddB11pSlopeH33 e X R C D F a x r c d f sv dv v4 h33 +
        (sv - e.svValue) *
          oddB11pSlopeSv e X R C D F a x r c d f sv dv v4 +
        (v4 - e.v4Value) *
          oddB11pSlopeV4 e X R C D F a x r c d f dv v4 +
        (X - e.bigX) *
          oddB11pSlopeX e X R C D F a x r c d f dv +
        (R - e.bigR) *
          oddB11pSlopeR e R C D F a x r c d f dv +
        (C - e.bigC) *
          oddB11pSlopeC e C D F a x r c d f dv +
        (D - e.bigD) *
          oddB11pSlopeD e D F a x r c d f dv +
        (F - e.bigF) *
          oddB11pSlopeF e F a x r c d f dv +
        (a - e.littleA) *
          oddB11pSlopeA e a x r c d f dv +
        (x - e.littleX) *
          oddB11pSlopeLittleX e x r c d f dv +
        (r - e.littleR) *
          oddB11pSlopeLittleR e r c d f dv +
        (c - e.littleC) *
          oddB11pSlopeLittleC e c d f dv +
        (d - e.littleD) *
          oddB11pSlopeLittleD e d f dv +
        (f - e.littleF) *
          oddB11pSlopeLittleF e f dv +
        (dv - e.dvValue) * oddB11pSlopeDv e dv := by
  unfold oddB11pEndpointValue oddB11pSlopeQ33 oddB11pSlopeH33
    oddB11pSlopeSv oddB11pSlopeV4 oddB11pSlopeX oddB11pSlopeR
    oddB11pSlopeC oddB11pSlopeD oddB11pSlopeF oddB11pSlopeA
    oddB11pSlopeLittleX oddB11pSlopeLittleR oddB11pSlopeLittleC
    oddB11pSlopeLittleD oddB11pSlopeLittleF oddB11pSlopeDv
    quadraticSecant oddB11pCore oddB11p oddGx oddGp oddM11
    alignedMixedDeterminant alignedMixedAdjugatePair alignedEntry00
    alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
    mixedDeterminantOne
  dsimp only
  ring

private theorem oddB11p_lower_telescope
    (X R C D F a x r c d f sv dv v4 q33 h33 : ℝ) :
    oddB11pCore X R C D F a x r c d f sv dv v4 q33 h33 -
        oddB11pEndpointValue oddB11pLowerEndpoint =
      (q33 - oddB11pLowerEndpoint.q33Value) *
          oddB11pSlopeQ33 oddB11pLowerEndpoint
            X R C D F a x r c d f sv dv v4 q33 h33 +
        (h33 - oddB11pLowerEndpoint.h33Value) *
          oddB11pSlopeH33 oddB11pLowerEndpoint
            X R C D F a x r c d f sv dv v4 h33 +
        (sv - oddB11pLowerEndpoint.svValue) *
          oddB11pSlopeSv oddB11pLowerEndpoint
            X R C D F a x r c d f sv dv v4 +
        (v4 - oddB11pLowerEndpoint.v4Value) *
          oddB11pSlopeV4 oddB11pLowerEndpoint
            X R C D F a x r c d f dv v4 +
        (X - oddB11pLowerEndpoint.bigX) *
          oddB11pSlopeX oddB11pLowerEndpoint
            X R C D F a x r c d f dv +
        (R - oddB11pLowerEndpoint.bigR) *
          oddB11pSlopeR oddB11pLowerEndpoint R C D F a x r c d f dv +
        (C - oddB11pLowerEndpoint.bigC) *
          oddB11pSlopeC oddB11pLowerEndpoint C D F a x r c d f dv +
        (D - oddB11pLowerEndpoint.bigD) *
          oddB11pSlopeD oddB11pLowerEndpoint D F a x r c d f dv +
        (F - oddB11pLowerEndpoint.bigF) *
          oddB11pSlopeF oddB11pLowerEndpoint F a x r c d f dv +
        (a - oddB11pLowerEndpoint.littleA) *
          oddB11pSlopeA oddB11pLowerEndpoint a x r c d f dv +
        (x - oddB11pLowerEndpoint.littleX) *
          oddB11pSlopeLittleX oddB11pLowerEndpoint x r c d f dv +
        (r - oddB11pLowerEndpoint.littleR) *
          oddB11pSlopeLittleR oddB11pLowerEndpoint r c d f dv +
        (c - oddB11pLowerEndpoint.littleC) *
          oddB11pSlopeLittleC oddB11pLowerEndpoint c d f dv +
        (d - oddB11pLowerEndpoint.littleD) *
          oddB11pSlopeLittleD oddB11pLowerEndpoint d f dv +
        (f - oddB11pLowerEndpoint.littleF) *
          oddB11pSlopeLittleF oddB11pLowerEndpoint f dv +
        (dv - oddB11pLowerEndpoint.dvValue) *
          oddB11pSlopeDv oddB11pLowerEndpoint dv := by
  exact oddB11p_telescope oddB11pLowerEndpoint
    X R C D F a x r c d f sv dv v4 q33 h33

set_option maxHeartbeats 3000000 in
private theorem oddB11mLowerSlopeQ33_eq
    (X R C D F a x r c d f sv dv v4 q33 h33 : ℝ) :
    oddB11mSlopeQ33 oddB11mLowerEndpoint
        X R C D F a x r c d f sv dv v4 q33 h33 =
      oddGm X R C D F a x r c d f +
        oddGx X R C D F a x r c d f := by
  unfold oddB11mSlopeQ33 oddB11mLowerEndpoint quadraticSecant
    oddB11mCore oddB11m
  dsimp only
  ring

private def oddB11mQ33Geometry
    (X R C D F a x r c d f : ℝ) : ℝ :=
  alignedMixedDeterminant
    ((137423 / 100000) - a) (X - x) (R - r)
      (C - c) (D - d) (F - f)
    ((4 * (137423 / 100000) + 2 * a) / 3)
      ((4 * X + 2 * x) / 3) ((4 * R + 2 * r) / 3)
      ((4 * C + 2 * c) / 3) ((4 * D + 2 * d) / 3)
      ((4 * F + 2 * f) / 3)

private theorem oddGm_add_oddGx_eq_q33Geometry
    (X R C D F a x r c d f : ℝ) :
    oddGm X R C D F a x r c d f +
        oddGx X R C D F a x r c d f =
      oddB11mQ33Geometry X R C D F a x r c d f := by
  unfold oddGm oddGx oddB11mQ33Geometry alignedDeterminant
    alignedMixedDeterminant alignedEntry00 alignedEntry02 alignedEntry04
    alignedEntry22 alignedEntry24 mixedDeterminantOne
  ring

private def oddB11mQ33GeometrySlopeX
    (X R D F x r d f : ℝ) : ℝ :=
  (-400000 * D * R + 200000 * D * r - 200000 * F * X +
      200000 * F * x - 7954 * F + 200000 * R * d +
      100000 * X * f + 3977 * f) / 200000

private def oddB11mQ33GeometrySlopeR
    (R C D x r c d : ℝ) : ℝ :=
  (-1000000 * C * R + 1000000 * C * r - 242898 * C +
      1000000 * D * x - 79540 * D + 500000 * R * c +
      121449 * c + 39770 * d) / 1000000

private def oddB11mQ33GeometrySlopeC
    (F a f r : ℝ) : ℝ :=
  (-125000000000 * F * a + 343557500000 * F -
      171778750000 * f + 60724500000 * r - 14749859601) /
    250000000000

private def oddB11mQ33GeometrySlopeD
    (D a x r d : ℝ) : ℝ :=
  (25000000000 * D * a - 68711500000 * D + 1072450000 * a +
      68711500000 * d + 1988500000 * r + 12144900000 * x -
      3913591273) / 50000000000

private def oddB11mQ33GeometrySlopeF
    (a x c : ℝ) : ℝ :=
  (-661500 * a - 68711500 * c + 3977000 * x + 1659941) /
    100000000

private def oddB11mQ33GeometrySlopeA (c d f : ℝ) : ℝ :=
  (250000000000 * c * f - 250000000000 * d ^ 2 - 579156899) /
    500000000000

private def oddB11mQ33GeometrySlopeLittleX
    (x r d f : ℝ) : ℝ :=
  -(250000000000 * d * r + 125000000000 * f * x +
      4731375000 * f - 5728893101) / 250000000000

private def oddB11mQ33GeometrySlopeLittleR
    (r c d : ℝ) : ℝ :=
  -(250000000 * c * r + 12454250 * c + 18925500 * d - 2459797) /
    500000000

private def oddB11mQ33GeometrySlopeLittleC (f : ℝ) : ℝ :=
  (165293000000 * f - 75053072217) / 400000000000

private def oddB11mQ33GeometrySlopeLittleD (d : ℝ) : ℝ :=
  -(826465000000 * d - 114181613061) / 2000000000000

private def oddB11mQ33GeometrySlopeLittleF : ℝ :=
  -3027621619 / 500000000000

set_option maxHeartbeats 3000000 in
private theorem oddB11mQ33Geometry_telescope
    (X R C D F a x r c d f : ℝ) :
    oddB11mQ33Geometry X R C D F a x r c d f -
        oddB11mQ33Geometry
          (3977 / 100000) (121449 / 500000) (1323 / 100000)
          (21449 / 500000) (1571 / 5000) (165293 / 200000)
          (37851 / 1000000) (49817 / 1000000) (1433 / 200000)
          (23317 / 1000000) (552 / 3125) =
      (X - 3977 / 100000) *
          oddB11mQ33GeometrySlopeX X R D F x r d f +
        (R - 121449 / 500000) *
          oddB11mQ33GeometrySlopeR R C D x r c d +
        (C - 1323 / 100000) *
          oddB11mQ33GeometrySlopeC F a f r +
        (D - 21449 / 500000) *
          oddB11mQ33GeometrySlopeD D a x r d +
        (F - 1571 / 5000) *
          oddB11mQ33GeometrySlopeF a x c +
        (a - 165293 / 200000) *
          oddB11mQ33GeometrySlopeA c d f +
        (x - 37851 / 1000000) *
          oddB11mQ33GeometrySlopeLittleX x r d f +
        (r - 49817 / 1000000) *
          oddB11mQ33GeometrySlopeLittleR r c d +
        (c - 1433 / 200000) *
          oddB11mQ33GeometrySlopeLittleC f +
        (d - 23317 / 1000000) *
          oddB11mQ33GeometrySlopeLittleD d +
        (f - 552 / 3125) * oddB11mQ33GeometrySlopeLittleF := by
  unfold oddB11mQ33Geometry oddB11mQ33GeometrySlopeX
    oddB11mQ33GeometrySlopeR oddB11mQ33GeometrySlopeC
    oddB11mQ33GeometrySlopeD oddB11mQ33GeometrySlopeF
    oddB11mQ33GeometrySlopeA oddB11mQ33GeometrySlopeLittleX
    oddB11mQ33GeometrySlopeLittleR oddB11mQ33GeometrySlopeLittleC
    oddB11mQ33GeometrySlopeLittleD oddB11mQ33GeometrySlopeLittleF
    alignedMixedDeterminant alignedEntry00 alignedEntry02 alignedEntry04
    alignedEntry22 alignedEntry24 mixedDeterminantOne
  ring

set_option maxHeartbeats 3000000 in
private theorem oddB11mLowerSlopeQ33_lower
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (1 / 10000 : ℝ) ≤
      oddB11mSlopeQ33 oddB11mLowerEndpoint
        X R C D F a x r c d f sv dv v4 q33 h33 := by
  rcases hbox.X_mem with ⟨hXL, hXU⟩
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.C_mem with ⟨hCL, hCU⟩
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.F_mem with ⟨hFL, hFU⟩
  rcases hbox.a_mem with ⟨haL, haU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  have hX0 : 0 ≤ X := by nlinarith only [hXL]
  have hR0 : 0 ≤ R := by nlinarith only [hRL]
  have hC0 : 0 ≤ C := by nlinarith only [hCL]
  have hD0 : 0 ≤ D := by nlinarith only [hDL]
  have hF0 : 0 ≤ F := by nlinarith only [hFL]
  have ha0 : 0 ≤ a := by nlinarith only [haL]
  have hx0 : 0 ≤ x := by nlinarith only [hxL]
  have hr0 : 0 ≤ r := by nlinarith only [hrL]
  have hc0 : 0 ≤ c := by nlinarith only [hcL]
  have hd0 : 0 ≤ d := by nlinarith only [hdL]
  have hf0 : 0 ≤ f := by nlinarith only [hfL]
  have hSX : oddB11mQ33GeometrySlopeX X R D F x r d f ≤ 0 := by
    have hDR : (42817 / 1000000 : ℝ) * (242817 / 1000000) ≤ D * R :=
      mul_le_mul hDL hRL (by norm_num) hD0
    have hDr : D * r ≤
        (42898 / 1000000 : ℝ) * (57183 / 1000000) :=
      mul_le_mul hDU hrU hr0 (by norm_num)
    have hFX : (1571 / 5000 : ℝ) * (3962 / 100000) ≤ F * X :=
      mul_le_mul hFL hXL (by norm_num) hF0
    have hFx : F * x ≤ (63 / 200 : ℝ) * (39761 / 1000000) :=
      mul_le_mul hFU hxU hx0 (by norm_num)
    have hRd : R * d ≤
        (242898 / 1000000 : ℝ) * (27183 / 1000000) :=
      mul_le_mul hRU hdU hd0 (by norm_num)
    have hXf : X * f ≤ (3977 / 100000 : ℝ) * (4416 / 25000) :=
      mul_le_mul hXU hfU hf0 (by norm_num)
    unfold oddB11mQ33GeometrySlopeX
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 200000)).2
    nlinarith only [hDR, hDr, hFX, hFx, hRd, hXf, hFL, hfU]
  have hSR : oddB11mQ33GeometrySlopeR R C D x r c d ≤ 0 := by
    have hCR : (1323 / 100000 : ℝ) * (242817 / 1000000) ≤ C * R :=
      mul_le_mul hCL hRL (by norm_num) hC0
    have hCr : C * r ≤
        (1342 / 100000 : ℝ) * (57183 / 1000000) :=
      mul_le_mul hCU hrU hr0 (by norm_num)
    have hDx : D * x ≤
        (42898 / 1000000 : ℝ) * (39761 / 1000000) :=
      mul_le_mul hDU hxU hx0 (by norm_num)
    have hRc : R * c ≤
        (242898 / 1000000 : ℝ) * (7165 / 1000000) :=
      mul_le_mul hRU hcU hc0 (by norm_num)
    unfold oddB11mQ33GeometrySlopeR
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1000000)).2
    nlinarith only [hCR, hCr, hDx, hRc, hCL, hDL, hcU, hdU]
  have hSC : 0 ≤ oddB11mQ33GeometrySlopeC F a f r := by
    have hFa : F * a ≤ (63 / 200 : ℝ) * (826465 / 1000000) :=
      mul_le_mul hFU haU ha0 (by norm_num)
    unfold oddB11mQ33GeometrySlopeC
    apply div_nonneg
    · nlinarith only [hFa, hFL, hfU, hrL]
    · norm_num
  have hSD : oddB11mQ33GeometrySlopeD D a x r d ≤ 0 := by
    have hDa : D * a ≤
        (42898 / 1000000 : ℝ) * (826465 / 1000000) :=
      mul_le_mul hDU haU ha0 (by norm_num)
    unfold oddB11mQ33GeometrySlopeD
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 50000000000)).2
    nlinarith only [hDa, hDL, haU, hxU, hrU, hdU]
  have hSF : 0 ≤ oddB11mQ33GeometrySlopeF a x c := by
    unfold oddB11mQ33GeometrySlopeF
    apply div_nonneg
    · nlinarith only [haU, hxL, hcU]
    · norm_num
  have hSa : oddB11mQ33GeometrySlopeA c d f ≤ 0 := by
    have hcf : c * f ≤
        (7165 / 1000000 : ℝ) * (4416 / 25000) :=
      mul_le_mul hcU hfU hf0 (by norm_num)
    have hdd : (23317 / 1000000 : ℝ) * (23317 / 1000000) ≤ d * d :=
      mul_le_mul hdL hdL (by norm_num) hd0
    unfold oddB11mQ33GeometrySlopeA
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 500000000000)).2
    nlinarith only [hcf, hdd]
  have hSx : 0 ≤ oddB11mQ33GeometrySlopeLittleX x r d f := by
    have hdr : d * r ≤
        (27183 / 1000000 : ℝ) * (57183 / 1000000) :=
      mul_le_mul hdU hrU hr0 (by norm_num)
    have hfx : f * x ≤
        (4416 / 25000 : ℝ) * (39761 / 1000000) :=
      mul_le_mul hfU hxU hx0 (by norm_num)
    unfold oddB11mQ33GeometrySlopeLittleX
    apply div_nonneg
    · nlinarith only [hdr, hfx, hfU]
    · norm_num
  have hSr : 0 ≤ oddB11mQ33GeometrySlopeLittleR r c d := by
    have hcr : c * r ≤
        (7165 / 1000000 : ℝ) * (57183 / 1000000) :=
      mul_le_mul hcU hrU hr0 (by norm_num)
    unfold oddB11mQ33GeometrySlopeLittleR
    apply div_nonneg
    · nlinarith only [hcr, hcU, hdU]
    · norm_num
  have hSc : oddB11mQ33GeometrySlopeLittleC f ≤ 0 := by
    unfold oddB11mQ33GeometrySlopeLittleC
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 400000000000)).2
    nlinarith only [hfU]
  have hSd : 0 ≤ oddB11mQ33GeometrySlopeLittleD d := by
    unfold oddB11mQ33GeometrySlopeLittleD
    apply div_nonneg
    · nlinarith only [hdU]
    · norm_num
  have hSf : oddB11mQ33GeometrySlopeLittleF ≤ 0 := by
    norm_num [oddB11mQ33GeometrySlopeLittleF]
  have hPX : (0 : ℝ) ≤
      (X - 3977 / 100000) * oddB11mQ33GeometrySlopeX X R D F x r d f :=
    mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hXU)
      hSX
  have hPR : (0 : ℝ) ≤
      (R - 121449 / 500000) * oddB11mQ33GeometrySlopeR R C D x r c d :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hRU])
      hSR
  have hPC : (0 : ℝ) ≤
      (C - 1323 / 100000) * oddB11mQ33GeometrySlopeC F a f r :=
    mul_nonneg (sub_nonneg.mpr hCL) hSC
  have hPD : (0 : ℝ) ≤
      (D - 21449 / 500000) * oddB11mQ33GeometrySlopeD D a x r d :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hDU])
      hSD
  have hPF : (0 : ℝ) ≤
      (F - 1571 / 5000) * oddB11mQ33GeometrySlopeF a x c :=
    mul_nonneg (sub_nonneg.mpr hFL) hSF
  have hPa : (0 : ℝ) ≤
      (a - 165293 / 200000) * oddB11mQ33GeometrySlopeA c d f :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [haU])
      hSa
  have hPx : (0 : ℝ) ≤
      (x - 37851 / 1000000) *
        oddB11mQ33GeometrySlopeLittleX x r d f :=
    mul_nonneg (sub_nonneg.mpr hxL) hSx
  have hPr : (0 : ℝ) ≤
      (r - 49817 / 1000000) * oddB11mQ33GeometrySlopeLittleR r c d :=
    mul_nonneg (sub_nonneg.mpr hrL) hSr
  have hPc : (0 : ℝ) ≤
      (c - 1433 / 200000) * oddB11mQ33GeometrySlopeLittleC f :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hcU])
      hSc
  have hPd : (0 : ℝ) ≤
      (d - 23317 / 1000000) * oddB11mQ33GeometrySlopeLittleD d :=
    mul_nonneg (sub_nonneg.mpr hdL) hSd
  have hPf : (0 : ℝ) ≤
      (f - 552 / 3125) * oddB11mQ33GeometrySlopeLittleF :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hfU])
      hSf
  have hcorner :
      oddB11mQ33Geometry
          (3977 / 100000) (121449 / 500000) (1323 / 100000)
          (21449 / 500000) (1571 / 5000) (165293 / 200000)
          (37851 / 1000000) (49817 / 1000000) (1433 / 200000)
          (23317 / 1000000) (552 / 3125) =
        (14961822985407 / 100000000000000000 : ℝ) := by
    norm_num [oddB11mQ33Geometry, alignedMixedDeterminant, alignedEntry00,
      alignedEntry02, alignedEntry04, alignedEntry22, alignedEntry24,
      mixedDeterminantOne]
  have hcornerCap : (1 / 10000 : ℝ) ≤
      oddB11mQ33Geometry
          (3977 / 100000) (121449 / 500000) (1323 / 100000)
          (21449 / 500000) (1571 / 5000) (165293 / 200000)
          (37851 / 1000000) (49817 / 1000000) (1433 / 200000)
          (23317 / 1000000) (552 / 3125) := by
    rw [hcorner]
    norm_num
  rw [oddB11mLowerSlopeQ33_eq, oddGm_add_oddGx_eq_q33Geometry]
  have htel := oddB11mQ33Geometry_telescope X R C D F a x r c d f
  nlinarith only [htel, hcornerCap, hPX, hPR, hPC, hPD, hPF, hPa,
    hPx, hPr, hPc, hPd, hPf]

set_option maxHeartbeats 3000000 in
private theorem oddB11mLowerSlopeH33_eq
    (X R C D F a x r c d f sv dv v4 h33 : ℝ) :
    oddB11mSlopeH33 oddB11mLowerEndpoint
        X R C D F a x r c d f sv dv v4 h33 =
      -oddGm X R C D F a x r c d f +
        oddGx X R C D F a x r c d f := by
  unfold oddB11mSlopeH33 oddB11mLowerEndpoint quadraticSecant
    oddB11mCore oddB11m
  dsimp only
  ring

private def oddB11mH33Geometry
    (X R C D F a x r c d f : ℝ) : ℝ :=
  alignedMixedDeterminant
    ((137423 / 100000) - a) (X - x) (R - r)
      (C - c) (D - d) (F - f)
    ((2 * (137423 / 100000) + 4 * a) / 3)
      ((2 * X + 4 * x) / 3) ((2 * R + 4 * r) / 3)
      ((2 * C + 4 * c) / 3) ((2 * D + 4 * d) / 3)
      ((2 * F + 4 * f) / 3)

private theorem neg_oddGm_add_oddGx_eq_h33Geometry
    (X R C D F a x r c d f : ℝ) :
    -oddGm X R C D F a x r c d f +
        oddGx X R C D F a x r c d f =
      oddB11mH33Geometry X R C D F a x r c d f := by
  unfold oddGm oddGx oddB11mH33Geometry alignedDeterminant
    alignedMixedDeterminant alignedEntry00 alignedEntry02 alignedEntry04
    alignedEntry22 alignedEntry24 mixedDeterminantOne
  ring

private def oddB11mH33GeometrySlopeX
    (X R D F x r d f : ℝ) : ℝ :=
  (-200000 * D * R - 100000 * F * X - 3977 * F +
      200000 * d * r + 200000 * f * x) / 200000

private def oddB11mH33GeometrySlopeR
    (R C D x r c d : ℝ) : ℝ :=
  (-500000 * C * R - 121449 * C - 39770 * D +
      1000000 * c * r + 1000000 * d * x) / 1000000

private def oddB11mH33GeometrySlopeC
    (F a f r : ℝ) : ℝ :=
  (343557500000 * F - 250000000000 * a * f +
      250000000000 * r ^ 2 - 14749859601) / 500000000000

private def oddB11mH33GeometrySlopeD
    (D a x r d : ℝ) : ℝ :=
  (-68711500000 * D + 100000000000 * a * d +
      100000000000 * r * x - 3913591273) / 100000000000

private def oddB11mH33GeometrySlopeF (a x c : ℝ) : ℝ :=
  (-100000000 * a * c + 100000000 * x ^ 2 + 1659941) /
    200000000

private def oddB11mH33GeometrySlopeA (c d f : ℝ) : ℝ :=
  (1000000 * c * f - 157100 * c - 1000000 * d ^ 2 +
      42898 * d - 6615 * f) / 1000000

private def oddB11mH33GeometrySlopeLittleX
    (x r d f : ℝ) : ℝ :=
  -(20000000000 * d * r - 2428980000 * d +
      10000000000 * f * x - 19190000 * f -
      428980000 * r - 1571000000 * x - 59463921) / 10000000000

private def oddB11mH33GeometrySlopeLittleR
    (r c d : ℝ) : ℝ :=
  -(1000000000000 * c * r - 193081000000 * c +
      35932000000 * d - 6615000000 * r - 1953271653) /
    1000000000000

private def oddB11mH33GeometrySlopeLittleC (f : ℝ) : ℝ :=
  3 * (46450000000 * f - 40072978441) / 1000000000000

private def oddB11mH33GeometrySlopeLittleD (d : ℝ) : ℝ :=
  -(69675000000 * d - 19804189687) / 500000000000

private def oddB11mH33GeometrySlopeLittleF : ℝ :=
  -1098996789 / 250000000000

set_option maxHeartbeats 3000000 in
private theorem oddB11mH33Geometry_telescope
    (X R C D F a x r c d f : ℝ) :
    oddB11mH33Geometry X R C D F a x r c d f -
        oddB11mH33Geometry
          (3977 / 100000) (121449 / 500000) (1323 / 100000)
          (21449 / 500000) (1571 / 5000) (165293 / 200000)
          (37851 / 1000000) (49817 / 1000000) (1433 / 200000)
          (23317 / 1000000) (552 / 3125) =
      (X - 3977 / 100000) *
          oddB11mH33GeometrySlopeX X R D F x r d f +
        (R - 121449 / 500000) *
          oddB11mH33GeometrySlopeR R C D x r c d +
        (C - 1323 / 100000) *
          oddB11mH33GeometrySlopeC F a f r +
        (D - 21449 / 500000) *
          oddB11mH33GeometrySlopeD D a x r d +
        (F - 1571 / 5000) *
          oddB11mH33GeometrySlopeF a x c +
        (a - 165293 / 200000) *
          oddB11mH33GeometrySlopeA c d f +
        (x - 37851 / 1000000) *
          oddB11mH33GeometrySlopeLittleX x r d f +
        (r - 49817 / 1000000) *
          oddB11mH33GeometrySlopeLittleR r c d +
        (c - 1433 / 200000) *
          oddB11mH33GeometrySlopeLittleC f +
        (d - 23317 / 1000000) *
          oddB11mH33GeometrySlopeLittleD d +
        (f - 552 / 3125) * oddB11mH33GeometrySlopeLittleF := by
  unfold oddB11mH33Geometry oddB11mH33GeometrySlopeX
    oddB11mH33GeometrySlopeR oddB11mH33GeometrySlopeC
    oddB11mH33GeometrySlopeD oddB11mH33GeometrySlopeF
    oddB11mH33GeometrySlopeA oddB11mH33GeometrySlopeLittleX
    oddB11mH33GeometrySlopeLittleR oddB11mH33GeometrySlopeLittleC
    oddB11mH33GeometrySlopeLittleD oddB11mH33GeometrySlopeLittleF
    alignedMixedDeterminant alignedEntry00 alignedEntry02 alignedEntry04
    alignedEntry22 alignedEntry24 mixedDeterminantOne
  ring

set_option maxHeartbeats 3000000 in
private theorem oddB11mLowerSlopeH33_lower
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (1 / 10000 : ℝ) ≤
      oddB11mSlopeH33 oddB11mLowerEndpoint
        X R C D F a x r c d f sv dv v4 h33 := by
  rcases hbox.X_mem with ⟨hXL, hXU⟩
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.C_mem with ⟨hCL, hCU⟩
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.F_mem with ⟨hFL, hFU⟩
  rcases hbox.a_mem with ⟨haL, haU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  have hX0 : 0 ≤ X := by nlinarith only [hXL]
  have hR0 : 0 ≤ R := by nlinarith only [hRL]
  have hC0 : 0 ≤ C := by nlinarith only [hCL]
  have hD0 : 0 ≤ D := by nlinarith only [hDL]
  have hF0 : 0 ≤ F := by nlinarith only [hFL]
  have ha0 : 0 ≤ a := by nlinarith only [haL]
  have hx0 : 0 ≤ x := by nlinarith only [hxL]
  have hr0 : 0 ≤ r := by nlinarith only [hrL]
  have hc0 : 0 ≤ c := by nlinarith only [hcL]
  have hd0 : 0 ≤ d := by nlinarith only [hdL]
  have hf0 : 0 ≤ f := by nlinarith only [hfL]
  have hSX : oddB11mH33GeometrySlopeX X R D F x r d f ≤ 0 := by
    have hDR : (42817 / 1000000 : ℝ) * (242817 / 1000000) ≤ D * R :=
      mul_le_mul hDL hRL (by norm_num) hD0
    have hFX : (1571 / 5000 : ℝ) * (3962 / 100000) ≤ F * X :=
      mul_le_mul hFL hXL (by norm_num) hF0
    have hdr : d * r ≤
        (27183 / 1000000 : ℝ) * (57183 / 1000000) :=
      mul_le_mul hdU hrU hr0 (by norm_num)
    have hfx : f * x ≤
        (4416 / 25000 : ℝ) * (39761 / 1000000) :=
      mul_le_mul hfU hxU hx0 (by norm_num)
    unfold oddB11mH33GeometrySlopeX
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 200000)).2
    nlinarith only [hDR, hFX, hdr, hfx, hFL]
  have hSR : oddB11mH33GeometrySlopeR R C D x r c d ≤ 0 := by
    have hCR : (1323 / 100000 : ℝ) * (242817 / 1000000) ≤ C * R :=
      mul_le_mul hCL hRL (by norm_num) hC0
    have hcr : c * r ≤
        (7165 / 1000000 : ℝ) * (57183 / 1000000) :=
      mul_le_mul hcU hrU hr0 (by norm_num)
    have hdx : d * x ≤
        (27183 / 1000000 : ℝ) * (39761 / 1000000) :=
      mul_le_mul hdU hxU hx0 (by norm_num)
    unfold oddB11mH33GeometrySlopeR
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1000000)).2
    nlinarith only [hCR, hcr, hdx, hCL, hDL]
  have hSC : 0 ≤ oddB11mH33GeometrySlopeC F a f r := by
    have haf : a * f ≤
        (826465 / 1000000 : ℝ) * (4416 / 25000) :=
      mul_le_mul haU hfU hf0 (by norm_num)
    unfold oddB11mH33GeometrySlopeC
    apply div_nonneg
    · nlinarith only [haf, hFL, sq_nonneg r]
    · norm_num
  have hSD : oddB11mH33GeometrySlopeD D a x r d ≤ 0 := by
    have had : a * d ≤
        (826465 / 1000000 : ℝ) * (27183 / 1000000) :=
      mul_le_mul haU hdU hd0 (by norm_num)
    have hrx : r * x ≤
        (57183 / 1000000 : ℝ) * (39761 / 1000000) :=
      mul_le_mul hrU hxU hx0 (by norm_num)
    unfold oddB11mH33GeometrySlopeD
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 100000000000)).2
    nlinarith only [hDL, had, hrx]
  have hSF : 0 ≤ oddB11mH33GeometrySlopeF a x c := by
    have hac : a * c ≤
        (826465 / 1000000 : ℝ) * (7165 / 1000000) :=
      mul_le_mul haU hcU hc0 (by norm_num)
    have hxx : (37851 / 1000000 : ℝ) * (37851 / 1000000) ≤ x * x :=
      mul_le_mul hxL hxL (by norm_num) hx0
    unfold oddB11mH33GeometrySlopeF
    apply div_nonneg
    · nlinarith only [hac, hxx]
    · norm_num
  have hSa : oddB11mH33GeometrySlopeA c d f ≤ 0 := by
    have hcf : c * f ≤
        (7165 / 1000000 : ℝ) * (4416 / 25000) :=
      mul_le_mul hcU hfU hf0 (by norm_num)
    have hdd : (23317 / 1000000 : ℝ) * (23317 / 1000000) ≤ d * d :=
      mul_le_mul hdL hdL (by norm_num) hd0
    unfold oddB11mH33GeometrySlopeA
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1000000)).2
    nlinarith only [hcf, hdd, hcL, hdU, hfL]
  have hSx : 0 ≤ oddB11mH33GeometrySlopeLittleX x r d f := by
    have hdr : d * r ≤
        (27183 / 1000000 : ℝ) * (57183 / 1000000) :=
      mul_le_mul hdU hrU hr0 (by norm_num)
    have hfx : f * x ≤
        (4416 / 25000 : ℝ) * (39761 / 1000000) :=
      mul_le_mul hfU hxU hx0 (by norm_num)
    unfold oddB11mH33GeometrySlopeLittleX
    apply div_nonneg
    · nlinarith only [hdr, hfx, hdL, hfL, hrL, hxL]
    · norm_num
  have hSr : 0 ≤ oddB11mH33GeometrySlopeLittleR r c d := by
    have hcr : c * r ≤
        (7165 / 1000000 : ℝ) * (57183 / 1000000) :=
      mul_le_mul hcU hrU hr0 (by norm_num)
    unfold oddB11mH33GeometrySlopeLittleR
    apply div_nonneg
    · nlinarith only [hcr, hcL, hdU, hrL]
    · norm_num
  have hSc : oddB11mH33GeometrySlopeLittleC f ≤ 0 := by
    unfold oddB11mH33GeometrySlopeLittleC
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1000000000000)).2
    nlinarith only [hfU]
  have hSd : 0 ≤ oddB11mH33GeometrySlopeLittleD d := by
    unfold oddB11mH33GeometrySlopeLittleD
    apply div_nonneg
    · nlinarith only [hdU]
    · norm_num
  have hSf : oddB11mH33GeometrySlopeLittleF ≤ 0 := by
    norm_num [oddB11mH33GeometrySlopeLittleF]
  have hPX : (0 : ℝ) ≤
      (X - 3977 / 100000) * oddB11mH33GeometrySlopeX X R D F x r d f :=
    mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hXU) hSX
  have hPR : (0 : ℝ) ≤
      (R - 121449 / 500000) * oddB11mH33GeometrySlopeR R C D x r c d :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hRU]) hSR
  have hPC : (0 : ℝ) ≤
      (C - 1323 / 100000) * oddB11mH33GeometrySlopeC F a f r :=
    mul_nonneg (sub_nonneg.mpr hCL) hSC
  have hPD : (0 : ℝ) ≤
      (D - 21449 / 500000) * oddB11mH33GeometrySlopeD D a x r d :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hDU]) hSD
  have hPF : (0 : ℝ) ≤
      (F - 1571 / 5000) * oddB11mH33GeometrySlopeF a x c :=
    mul_nonneg (sub_nonneg.mpr hFL) hSF
  have hPa : (0 : ℝ) ≤
      (a - 165293 / 200000) * oddB11mH33GeometrySlopeA c d f :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [haU]) hSa
  have hPx : (0 : ℝ) ≤
      (x - 37851 / 1000000) * oddB11mH33GeometrySlopeLittleX x r d f :=
    mul_nonneg (sub_nonneg.mpr hxL) hSx
  have hPr : (0 : ℝ) ≤
      (r - 49817 / 1000000) * oddB11mH33GeometrySlopeLittleR r c d :=
    mul_nonneg (sub_nonneg.mpr hrL) hSr
  have hPc : (0 : ℝ) ≤
      (c - 1433 / 200000) * oddB11mH33GeometrySlopeLittleC f :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hcU]) hSc
  have hPd : (0 : ℝ) ≤
      (d - 23317 / 1000000) * oddB11mH33GeometrySlopeLittleD d :=
    mul_nonneg (sub_nonneg.mpr hdL) hSd
  have hPf : (0 : ℝ) ≤
      (f - 552 / 3125) * oddB11mH33GeometrySlopeLittleF :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hfU]) hSf
  have hcorner :
      oddB11mH33Geometry
          (3977 / 100000) (121449 / 500000) (1323 / 100000)
          (21449 / 500000) (1571 / 5000) (165293 / 200000)
          (37851 / 1000000) (49817 / 1000000) (1433 / 200000)
          (23317 / 1000000) (552 / 3125) =
        (9168087626189 / 62500000000000000 : ℝ) := by
    norm_num [oddB11mH33Geometry, alignedMixedDeterminant, alignedEntry00,
      alignedEntry02, alignedEntry04, alignedEntry22, alignedEntry24,
      mixedDeterminantOne]
  have hcornerCap : (1 / 10000 : ℝ) ≤
      oddB11mH33Geometry
          (3977 / 100000) (121449 / 500000) (1323 / 100000)
          (21449 / 500000) (1571 / 5000) (165293 / 200000)
          (37851 / 1000000) (49817 / 1000000) (1433 / 200000)
          (23317 / 1000000) (552 / 3125) := by
    rw [hcorner]
    norm_num
  rw [oddB11mLowerSlopeH33_eq, neg_oddGm_add_oddGx_eq_h33Geometry]
  have htel := oddB11mH33Geometry_telescope X R C D F a x r c d f
  nlinarith only [htel, hcornerCap, hPX, hPR, hPC, hPD, hPF, hPa,
    hPx, hPr, hPc, hPd, hPf]

private def oddB11mSvMinorZero (C D F c d f : ℝ) : ℝ :=
  (C - c) * (F - f) - (D - d) ^ 2

private def oddB11mSvMinorOne (X R D F x r d f : ℝ) : ℝ :=
  (D - d) * (R - r) + (F - f) * (X - x)

private def oddB11mSvMinorTwo (X R C D x r c d : ℝ) : ℝ :=
  (C - c) * (R - r) + (X - x) * (D - d)

private def oddB11mSvBracket
    (X R C D F x r c d f sv dv v4 : ℝ) : ℝ :=
  oddB11mSvMinorZero C D F c d f * ((sv + 13459 / 25000) / 2) -
    oddB11mSvMinorOne X R D F x r d f * dv -
      oddB11mSvMinorTwo X R C D x r c d * v4

set_option maxHeartbeats 3000000 in
private theorem oddB11mLowerSlopeSv_eq
    (X R C D F a x r c d f sv dv v4 : ℝ) :
    oddB11mSlopeSv oddB11mLowerEndpoint
        X R C D F a x r c d f sv dv v4 =
      -oddB11mSvBracket X R C D F x r c d f sv dv v4 / 2 := by
  unfold oddB11mSlopeSv oddB11mLowerEndpoint quadraticSecant
    oddB11mCore oddB11m oddP11 oddB11mSvBracket oddB11mSvMinorZero
    oddB11mSvMinorOne oddB11mSvMinorTwo alignedAdjugatePair
  dsimp only
  ring

private theorem oddB11mLowerSlopeSv_upper
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    oddB11mSlopeSv oddB11mLowerEndpoint
        X R C D F a x r c d f sv dv v4 ≤
      (-9 / 1000000 : ℝ) := by
  rcases hbox.X_mem with ⟨hXL, hXU⟩
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.C_mem with ⟨hCL, hCU⟩
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.F_mem with ⟨hFL, hFU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  rcases hbox.sv_mem with ⟨hsvL, hsvU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  rcases hbox.v4_mem with ⟨hv4L, hv4U⟩
  have hCpL : (1213 / 200000 : ℝ) ≤ C - c := by
    nlinarith only [hCL, hcU]
  have hCp0 : 0 ≤ C - c := by nlinarith only [hCpL]
  have hFpL : (3439 / 25000 : ℝ) ≤ F - f := by
    nlinarith only [hFL, hfU]
  have hFp0 : 0 ≤ F - f := by nlinarith only [hFpL]
  have hFpU : F - f ≤ (433 / 3125 : ℝ) := by
    nlinarith only [hFU, hfL]
  have hDp0 : 0 ≤ D - d := by nlinarith only [hDL, hdU]
  have hDpU : D - d ≤ (19581 / 1000000 : ℝ) := by
    nlinarith only [hDU, hdL]
  have hRpL : (92817 / 500000 : ℝ) ≤ R - r := by
    nlinarith only [hRL, hrU]
  have hRp0 : 0 ≤ R - r := by nlinarith only [hRpL]
  have hRpU : R - r ≤ (193081 / 1000000 : ℝ) := by
    nlinarith only [hRU, hrL]
  have hXpL : (-141 / 1000000 : ℝ) ≤ X - x := by
    nlinarith only [hXL, hxU]
  have hXpU : X - x ≤ (1919 / 1000000 : ℝ) := by
    nlinarith only [hXU, hxL]
  have hCpFp : (1213 / 200000 : ℝ) * (3439 / 25000) ≤
      (C - c) * (F - f) :=
    mul_le_mul hCpL hFpL (by norm_num) hCp0
  have hDpSq : (D - d) * (D - d) ≤
      (19581 / 1000000 : ℝ) * (19581 / 1000000) :=
    mul_le_mul hDpU hDpU hDp0 (by norm_num)
  have hs0 : (450885839 / 1000000000000 : ℝ) ≤
      oddB11mSvMinorZero C D F c d f := by
    unfold oddB11mSvMinorZero
    nlinarith only [hCpFp, hDpSq]
  have hs00 : 0 ≤ oddB11mSvMinorZero C D F c d f := by
    nlinarith only [hs0]
  have hDpRp : (D - d) * (R - r) ≤
      (19581 / 1000000 : ℝ) * (193081 / 1000000) :=
    mul_le_mul hDpU hRpU hRp0 (by norm_num)
  have hFpXp1 : (F - f) * (X - x) ≤
      (F - f) * (1919 / 1000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hXpU hFp0
  have hFpXp2 : (F - f) * (1919 / 1000000 : ℝ) ≤
      (433 / 3125 : ℝ) * (1919 / 1000000) :=
    mul_le_mul_of_nonneg_right hFpU (by norm_num)
  have hs1 : oddB11mSvMinorOne X R D F x r d f ≤
      (4046615701 / 1000000000000 : ℝ) := by
    unfold oddB11mSvMinorOne
    nlinarith only [hDpRp, hFpXp1, hFpXp2]
  have hCpRp : (1213 / 200000 : ℝ) * (92817 / 500000) ≤
      (C - c) * (R - r) :=
    mul_le_mul hCpL hRpL (by norm_num) hCp0
  have hXpDp1 : (-141 / 1000000 : ℝ) * (19581 / 1000000) ≤
      (-141 / 1000000 : ℝ) * (D - d) :=
    mul_le_mul_of_nonpos_left hDpU (by norm_num)
  have hXpDp2 : (-141 / 1000000 : ℝ) * (D - d) ≤
      (X - x) * (D - d) :=
    mul_le_mul_of_nonneg_right hXpL hDp0
  have hs2 : (1123109289 / 1000000000000 : ℝ) ≤
      oddB11mSvMinorTwo X R C D x r c d := by
    unfold oddB11mSvMinorTwo
    nlinarith only [hCpRp, hXpDp1, hXpDp2]
  have hs20 : 0 ≤ oddB11mSvMinorTwo X R C D x r c d := by
    nlinarith only [hs2]
  have hsvBar : (107651 / 200000 : ℝ) ≤
      (sv + 13459 / 25000) / 2 := by
    nlinarith only [hsvL]
  have hs0Product :
      (450885839 / 1000000000000 : ℝ) * (107651 / 200000) ≤
        oddB11mSvMinorZero C D F c d f * ((sv + 13459 / 25000) / 2) :=
    mul_le_mul hs0 hsvBar (by norm_num) hs00
  have hdv0 : 0 ≤ dv := by nlinarith only [hdvL]
  have hs1Product : oddB11mSvMinorOne X R D F x r d f * dv ≤
      (4046615701 / 1000000000000 : ℝ) * (558 / 10000) :=
    mul_le_mul hs1 hdvU hdv0 (by norm_num)
  have hv4Neg : (2 / 1000 : ℝ) ≤ -v4 := by
    nlinarith only [hv4U]
  have hs2Product :
      (1123109289 / 1000000000000 : ℝ) * (2 / 1000) ≤
        oddB11mSvMinorTwo X R C D x r c d * (-v4) :=
    mul_le_mul hs2 hv4Neg (by norm_num) hs20
  have hbracket : (18 / 1000000 : ℝ) ≤
      oddB11mSvBracket X R C D F x r c d f sv dv v4 := by
    unfold oddB11mSvBracket
    nlinarith only [hs0Product, hs1Product, hs2Product]
  rw [oddB11mLowerSlopeSv_eq]
  nlinarith only [hbracket]

private def oddB11mV4Lead
    (X R C D a x r c d dv : ℝ) : ℝ :=
  -oddB11mSvMinorTwo X R C D x r c d * (13459 / 25000) +
    ((X - x) * (R - r) + ((137423 / 100000) - a) * (D - d)) * dv

private def oddB11mV4TailMinor (X C a x c : ℝ) : ℝ :=
  ((137423 / 100000) - a) * (C - c) - (X - x) ^ 2

private def oddB11mV4Bracket
    (X R C D a x r c d dv v4 : ℝ) : ℝ :=
  oddB11mV4Lead X R C D a x r c d dv +
    oddB11mV4TailMinor X C a x c * ((v4 - 1 / 250) / 2)

set_option maxHeartbeats 3000000 in
private theorem oddB11mLowerSlopeV4_eq
    (X R C D F a x r c d f dv v4 : ℝ) :
    oddB11mSlopeV4 oddB11mLowerEndpoint
        X R C D F a x r c d f dv v4 =
      -oddB11mV4Bracket X R C D a x r c d dv v4 / 2 := by
  unfold oddB11mSlopeV4 oddB11mLowerEndpoint quadraticSecant
    oddB11mCore oddB11m oddP11 oddB11mV4Bracket oddB11mV4Lead
    oddB11mV4TailMinor oddB11mSvMinorTwo alignedAdjugatePair
  dsimp only
  ring

private theorem oddB11mLowerSlopeV4_lower
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (4 / 1000000 : ℝ) ≤
      oddB11mSlopeV4 oddB11mLowerEndpoint
        X R C D F a x r c d f dv v4 := by
  rcases hbox.X_mem with ⟨hXL, hXU⟩
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.C_mem with ⟨hCL, hCU⟩
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.a_mem with ⟨haL, haU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  rcases hbox.v4_mem with ⟨hv4L, hv4U⟩
  have hRp0 : 0 ≤ R - r := by nlinarith only [hRL, hrU]
  have hDp0 : 0 ≤ D - d := by nlinarith only [hDL, hdU]
  have hdv0 : 0 ≤ dv := by nlinarith only [hdvL]
  have hXpL : (-141 / 1000000 : ℝ) ≤ X - x := by
    nlinarith only [hXL, hxU]
  have hXpU : X - x ≤ (1919 / 1000000 : ℝ) := by
    nlinarith only [hXU, hxL]
  have hSC : (13459 * (-R + r) / 25000 : ℝ) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · nlinarith only [hRp0]
    · norm_num
  have hSc : 0 ≤ (-13459 * (-R + r) / 25000 : ℝ) := by
    apply div_nonneg
    · nlinarith only [hRp0]
    · norm_num
  have hSa : dv * (-D + d) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hdv0 (by nlinarith only [hDp0])
  have hDvXp1 : dv * (X - x) ≤ dv * (1919 / 1000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hXpU hdv0
  have hDvXp2 : dv * (1919 / 1000000 : ℝ) ≤
      (558 / 10000 : ℝ) * (1919 / 1000000) :=
    mul_le_mul_of_nonneg_right hdvU (by norm_num)
  have hInnerR : 0 ≤
      -5000000000 * X * dv + 5000000000 * dv * x + 16325767 := by
    nlinarith only [hDvXp1, hDvXp2]
  have hSR :
      -(-5000000000 * X * dv + 5000000000 * dv * x + 16325767) /
          5000000000 ≤ (0 : ℝ) := by
    apply div_nonpos_of_nonpos_of_nonneg
    · nlinarith only [hInnerR]
    · norm_num
  have hSD : (0 : ℝ) ≤
      (-538360 * X + 549751 * dv + 538360 * x) / 1000000 := by
    apply div_nonneg
    · nlinarith only [hdvL, hXpU]
    · norm_num
  have hSr : (0 : ℝ) ≤
      (-5000000000 * X * dv + 5000000000 * dv * x + 16325767) /
          5000000000 := by
    exact div_nonneg hInnerR (by norm_num)
  have hSd :
      -(-538360 * X + 549751 * dv + 538360 * x) / 1000000 ≤
        (0 : ℝ) := by
    apply div_nonpos_of_nonpos_of_nonneg
    · nlinarith only [hSD]
    · norm_num
  have hSdv : (0 : ℝ) ≤
      -3 * (-61878000000 * X + 61878000000 * x - 3588224777) /
          1000000000000 := by
    apply div_nonneg
    · nlinarith only [hXpL]
    · norm_num
  have hSX : (-4581249 / 25000000000 : ℝ) ≤ 0 := by norm_num
  have hSx : (0 : ℝ) ≤ (4581249 / 25000000000 : ℝ) := by norm_num
  have htel :
      oddB11mV4Lead X R C D a x r c d dv -
          (-16965063567 / 3125000000000000 : ℝ) =
        (C - 1323 / 100000) * (13459 * (-R + r) / 25000) +
        (c - 1433 / 200000) * (-13459 * (-R + r) / 25000) +
        (a - 824479 / 1000000) * (dv * (-D + d)) +
        (R - 242817 / 1000000) *
          (-(-5000000000 * X * dv + 5000000000 * dv * x + 16325767) /
            5000000000) +
        (D - 21449 / 500000) *
          ((-538360 * X + 549751 * dv + 538360 * x) / 1000000) +
        (r - 57183 / 1000000) *
          ((-5000000000 * X * dv + 5000000000 * dv * x + 16325767) /
            5000000000) +
        (d - 23317 / 1000000) *
          (-(-538360 * X + 549751 * dv + 538360 * x) / 1000000) +
        (dv - 279 / 5000) *
          (-3 * (-61878000000 * X + 61878000000 * x - 3588224777) /
            1000000000000) +
        (X - 1981 / 50000) * (-4581249 / 25000000000) +
        (x - 39761 / 1000000) * (4581249 / 25000000000) := by
    unfold oddB11mV4Lead oddB11mSvMinorTwo
    ring
  have hPC :
      (C - 1323 / 100000) * (13459 * (-R + r) / 25000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hCL]) hSC
  have hPc :
      (c - 1433 / 200000) * (-13459 * (-R + r) / 25000) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hcU]) hSc
  have hPa : (a - 824479 / 1000000) * (dv * (-D + d)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [haL]) hSa
  have hPR : (R - 242817 / 1000000) *
      (-(-5000000000 * X * dv + 5000000000 * dv * x + 16325767) /
        5000000000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hRL]) hSR
  have hPD : (D - 21449 / 500000) *
      ((-538360 * X + 549751 * dv + 538360 * x) / 1000000) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hDU]) hSD
  have hPr : (r - 57183 / 1000000) *
      ((-5000000000 * X * dv + 5000000000 * dv * x + 16325767) /
        5000000000) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hrU]) hSr
  have hPd : (d - 23317 / 1000000) *
      (-(-538360 * X + 549751 * dv + 538360 * x) / 1000000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hdL]) hSd
  have hPdv : (dv - 279 / 5000) *
      (-3 * (-61878000000 * X + 61878000000 * x - 3588224777) /
        1000000000000) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hdvU]) hSdv
  have hPX :
      (X - 1981 / 50000) * (-4581249 / 25000000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hXL]) hSX
  have hPx :
      (x - 39761 / 1000000) * (4581249 / 25000000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hxU]) hSx
  have hLead : oddB11mV4Lead X R C D a x r c d dv ≤
      (-16965063567 / 3125000000000000 : ℝ) := by
    nlinarith only [htel, hPC, hPc, hPa, hPR, hPD, hPr, hPd, hPdv, hPX, hPx]
  have hApL : (109553 / 200000 : ℝ) ≤ (137423 / 100000) - a := by
    nlinarith only [haU]
  have hCpL : (1213 / 200000 : ℝ) ≤ C - c := by
    nlinarith only [hCL, hcU]
  have hApCp : (109553 / 200000 : ℝ) * (1213 / 200000) ≤
      ((137423 / 100000) - a) * (C - c) :=
    mul_le_mul hApL hCpL (by norm_num) (by nlinarith only [hApL])
  have hAbsLeft : -(1919 / 1000000 : ℝ) ≤ X - x := by
    nlinarith only [hXpL]
  have hAbsRight : 0 ≤ (1919 / 1000000 : ℝ) + (X - x) := by
    nlinarith only [hAbsLeft]
  have hSqProduct : 0 ≤
      ((1919 / 1000000 : ℝ) - (X - x)) *
        ((1919 / 1000000 : ℝ) + (X - x)) :=
    mul_nonneg (by nlinarith only [hXpU]) hAbsRight
  have hXpSq : (X - x) ^ 2 ≤ (1919 / 1000000 : ℝ) ^ 2 := by
    nlinarith only [hSqProduct]
  have ht2 : (829628041 / 250000000000 : ℝ) ≤
      oddB11mV4TailMinor X C a x c := by
    unfold oddB11mV4TailMinor
    nlinarith only [hApCp, hXpSq]
  have hvbarU : (v4 - 1 / 250) / 2 ≤ (-3 / 1000 : ℝ) := by
    nlinarith only [hv4U]
  have hvbar0 : (v4 - 1 / 250) / 2 ≤ (0 : ℝ) := by
    nlinarith only [hvbarU]
  have hTail1 : oddB11mV4TailMinor X C a x c * ((v4 - 1 / 250) / 2) ≤
      (829628041 / 250000000000 : ℝ) * ((v4 - 1 / 250) / 2) :=
    mul_le_mul_of_nonpos_right ht2 hvbar0
  have hTail2 :
      (829628041 / 250000000000 : ℝ) * ((v4 - 1 / 250) / 2) ≤
        (829628041 / 250000000000 : ℝ) * (-3 / 1000) :=
    mul_le_mul_of_nonneg_left hvbarU (by norm_num)
  have hbracket : oddB11mV4Bracket X R C D a x r c d dv v4 ≤
      (-96152230209 / 6250000000000000 : ℝ) := by
    unfold oddB11mV4Bracket
    nlinarith only [hLead, hTail1, hTail2]
  rw [oddB11mLowerSlopeV4_eq]
  nlinarith only [hbracket]

private def oddB11mXGeometrySlope
    (X R D F x r d f dv : ℝ) : ℝ :=
  -(27150000000 * D * R - 16575000000 * D * r + 53836000 * D +
      13575000000 * F * X - 13459000000 * F * dv -
      16575000000 * F * x + 539877750 * F - 16575000000 * R * d -
      100000000 * R * dv - 8287500000 * X * f - 200000 * X +
      6000000000 * d * r - 53836000 * d + 13459000000 * dv * f +
      100000000 * dv * r + 6000000000 * f * x - 329593875 * f +
      400000 * x - 7954) / 50000000000

set_option maxHeartbeats 3000000 in
private theorem oddB11mLowerSlopeX_eq
    (X R C D F a x r c d f dv : ℝ) :
    oddB11mSlopeX oddB11mLowerEndpoint X R C D F a x r c d f dv =
      oddB11mXGeometrySlope X R D F x r d f dv := by
  unfold oddB11mSlopeX oddB11mLowerEndpoint quadraticSecant
    oddB11mCore oddB11m oddGm oddGx oddP11 oddB11mXGeometrySlope
    alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
    alignedEntry00 alignedEntry02 alignedEntry04 alignedEntry22
    alignedEntry24 mixedDeterminantOne
  dsimp only
  ring

private theorem oddB11mLowerSlopeX_upper
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    oddB11mSlopeX oddB11mLowerEndpoint X R C D F a x r c d f dv ≤
      (-19 / 10000 : ℝ) := by
  rcases hbox.X_mem with ⟨hXL, hXU⟩
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.F_mem with ⟨hFL, hFU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  have hSX : (-135750 * F + 82875 * f + 2) / 500000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 500000)).2
    nlinarith only [hFL, hfU]
  have hSR : (-1086 * D + 663 * d + 4 * dv) / 2000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2000)).2
    nlinarith only [hDL, hdU, hdvU]
  have hSD : (331500000 * r - 132926351) / 1000000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1000000000)).2
    nlinarith only [hrU]
  have hSF : (0 : ℝ) ≤
      (53836000 * dv + 66300000 * x - 4310877) / 200000000 := by
    apply div_nonneg
    · nlinarith only [hdvL, hxL]
    · norm_num
  have hSx : (0 : ℝ) ≤ -(240000 * f - 208829) / 2000000 := by
    apply div_nonneg
    · nlinarith only [hfU]
    · norm_num
  have hSr : (0 : ℝ) ≤
      -(240000000 * d + 4000000 * dv - 28387671) / 2000000000 := by
    apply div_nonneg
    · nlinarith only [hdU, hdvU]
    · norm_num
  have hSd : (0 : ℝ) ≤ (149417191 / 2000000000 : ℝ) := by norm_num
  have hSf : -(107672000 * dv - 3355029) / 400000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 400000000)).2
    nlinarith only [hdvL]
  have hSdv : (0 : ℝ) ≤ (47086061 / 1250000000 : ℝ) := by norm_num
  have htel :
      oddB11mXGeometrySlope X R D F x r d f dv -
          (-952460724727 / 500000000000000 : ℝ) =
        (X - 1981 / 50000) * ((-135750 * F + 82875 * f + 2) / 500000) +
        (R - 242817 / 1000000) * ((-1086 * D + 663 * d + 4 * dv) / 2000) +
        (D - 42817 / 1000000) *
          ((331500000 * r - 132926351) / 1000000000) +
        (F - 63 / 200) *
          ((53836000 * dv + 66300000 * x - 4310877) / 200000000) +
        (x - 39761 / 1000000) * (-(240000 * f - 208829) / 2000000) +
        (r - 57183 / 1000000) *
          (-(240000000 * d + 4000000 * dv - 28387671) / 2000000000) +
        (d - 27183 / 1000000) * (149417191 / 2000000000) +
        (f - 4411 / 25000) *
          (-(107672000 * dv - 3355029) / 400000000) +
        (dv - 279 / 5000) * (47086061 / 1250000000) := by
    unfold oddB11mXGeometrySlope
    ring
  have hPX : (X - 1981 / 50000) *
      ((-135750 * F + 82875 * f + 2) / 500000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hXL]) hSX
  have hPR : (R - 242817 / 1000000) *
      ((-1086 * D + 663 * d + 4 * dv) / 2000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hRL]) hSR
  have hPD : (D - 42817 / 1000000) *
      ((331500000 * r - 132926351) / 1000000000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hDL]) hSD
  have hPF : (F - 63 / 200) *
      ((53836000 * dv + 66300000 * x - 4310877) / 200000000) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hFU]) hSF
  have hPx : (x - 39761 / 1000000) *
      (-(240000 * f - 208829) / 2000000) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hxU]) hSx
  have hPr : (r - 57183 / 1000000) *
      (-(240000000 * d + 4000000 * dv - 28387671) / 2000000000) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hrU]) hSr
  have hPd :
      (d - 27183 / 1000000) * (149417191 / 2000000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hdU]) hSd
  have hPf : (f - 4411 / 25000) *
      (-(107672000 * dv - 3355029) / 400000000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hfL]) hSf
  have hPdv :
      (dv - 279 / 5000) * (47086061 / 1250000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hdvU]) hSdv
  rw [oddB11mLowerSlopeX_eq]
  nlinarith only [htel, hPX, hPR, hPD, hPF, hPx, hPr, hPd, hPf, hPdv]

private def oddB11mRGeometrySlope
    (R C D x r c d dv : ℝ) : ℝ :=
  -(543000000 * C * R - 663000000 * C * r + 134047054 * C -
      538360000 * D * dv - 663000000 * D * x + 43190220 * D -
      331500000 * R * c - 500000000 * R * dv ^ 2 +
      240000000 * c * r - 82674127 * c + 538360000 * d * dv +
      240000000 * d * x - 26367510 * d + 1000000000 * dv ^ 2 * r -
      121449000 * dv ^ 2 + 4000000 * dv * x - 159080 * dv) /
    2000000000

set_option maxHeartbeats 3000000 in
private theorem oddB11mLowerSlopeR_eq
    (R C D F a x r c d f dv : ℝ) :
    oddB11mSlopeR oddB11mLowerEndpoint R C D F a x r c d f dv =
      oddB11mRGeometrySlope R C D x r c d dv := by
  unfold oddB11mSlopeR oddB11mLowerEndpoint quadraticSecant
    oddB11mCore oddB11m oddGm oddGx oddP11 oddB11mRGeometrySlope
    alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
    alignedEntry00 alignedEntry02 alignedEntry04 alignedEntry22
    alignedEntry24 mixedDeterminantOne
  dsimp only
  ring

private theorem oddB11mLowerSlopeR_upper
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    oddB11mSlopeR oddB11mLowerEndpoint R C D F a x r c d f dv ≤
      (-11 / 20000 : ℝ) := by
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.C_mem with ⟨hCL, hCU⟩
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  have hdv0 : 0 ≤ dv := by nlinarith only [hdvL]
  have hdvSq : dv * dv ≤ (558 / 10000 : ℝ) * (558 / 10000) :=
    mul_le_mul hdvU hdvU hdv0 (by norm_num)
  have hSR : (-1086 * C + 663 * c + 1000 * dv ^ 2) / 4000 ≤
      (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 4000)).2
    nlinarith only [hCL, hcU, hdvSq]
  have hSC : (132600000 * r - 53179337) / 400000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 400000000)).2
    nlinarith only [hrU]
  have hSD : (0 : ℝ) ≤
      (26918000 * dv + 33150000 * x - 2159511) / 100000000 := by
    apply div_nonneg
    · nlinarith only [hdvL, hxL]
    · norm_num
  have hSx : (0 : ℝ) ≤
      -(120000000 * d + 2000000 * dv - 14220687) / 1000000000 := by
    apply div_nonneg
    · nlinarith only [hdU, hdvU]
    · norm_num
  have hSr : (0 : ℝ) ≤
      -(24000000 * c + 100000000 * dv ^ 2 - 877149) / 200000000 := by
    apply div_nonneg
    · nlinarith only [hcU, hdvSq]
    · norm_num
  have hSc : (0 : ℝ) ≤ (59777617 / 800000000 : ℝ) := by norm_num
  have hSd : -(53836000 * dv - 1682487) / 200000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 200000000)).2
    nlinarith only [hdvL]
  have hSdv : (0 : ℝ) ≤
      3 * (3094575000 * dv + 348371671) / 100000000000 := by
    apply div_nonneg
    · nlinarith only [hdvL]
    · norm_num
  have htel :
      oddB11mRGeometrySlope R C D x r c d dv -
          (-2217458406031 / 4000000000000000 : ℝ) =
        (R - 242817 / 1000000) *
          ((-1086 * C + 663 * c + 1000 * dv ^ 2) / 4000) +
        (C - 1323 / 100000) *
          ((132600000 * r - 53179337) / 400000000) +
        (D - 42898 / 1000000) *
          ((26918000 * dv + 33150000 * x - 2159511) / 100000000) +
        (x - 39761 / 1000000) *
          (-(120000000 * d + 2000000 * dv - 14220687) / 1000000000) +
        (r - 57183 / 1000000) *
          (-(24000000 * c + 100000000 * dv ^ 2 - 877149) / 200000000) +
        (c - 1433 / 200000) * (59777617 / 800000000) +
        (d - 23317 / 1000000) *
          (-(53836000 * dv - 1682487) / 200000000) +
        (dv - 279 / 5000) *
          (3 * (3094575000 * dv + 348371671) / 100000000000) := by
    unfold oddB11mRGeometrySlope
    ring
  have hPR : (R - 242817 / 1000000) *
      ((-1086 * C + 663 * c + 1000 * dv ^ 2) / 4000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hRL]) hSR
  have hPC : (C - 1323 / 100000) *
      ((132600000 * r - 53179337) / 400000000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hCL]) hSC
  have hPD : (D - 42898 / 1000000) *
      ((26918000 * dv + 33150000 * x - 2159511) / 100000000) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hDU]) hSD
  have hPx : (x - 39761 / 1000000) *
      (-(120000000 * d + 2000000 * dv - 14220687) / 1000000000) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hxU]) hSx
  have hPr : (r - 57183 / 1000000) *
      (-(24000000 * c + 100000000 * dv ^ 2 - 877149) / 200000000) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hrU]) hSr
  have hPc :
      (c - 1433 / 200000) * (59777617 / 800000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hcU]) hSc
  have hPd : (d - 23317 / 1000000) *
      (-(53836000 * dv - 1682487) / 200000000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hdL]) hSd
  have hPdv : (dv - 279 / 5000) *
      (3 * (3094575000 * dv + 348371671) / 100000000000) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hdvU]) hSdv
  rw [oddB11mLowerSlopeR_eq]
  nlinarith only [htel, hPR, hPC, hPD, hPx, hPr, hPc, hPd, hPdv]

private def oddB11mCGeometrySlope (F a r f : ℝ) : ℝ :=
  -(82875000000000 * F * a - 150322786300000 * F -
      30000000000000 * a * f - 2000000000 * a +
      77660375050000 * f + 30000000000000 * r ^ 2 -
      40798703500000 * r + 8142688790623) / 500000000000000

set_option maxHeartbeats 3000000 in
private theorem oddB11mLowerSlopeC_eq
    (C D F a x r c d f dv : ℝ) :
    oddB11mSlopeC oddB11mLowerEndpoint C D F a x r c d f dv =
      oddB11mCGeometrySlope F a r f := by
  unfold oddB11mSlopeC oddB11mLowerEndpoint quadraticSecant
    oddB11mCore oddB11m oddGm oddGx oddP11 oddB11mCGeometrySlope
    alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
    alignedEntry00 alignedEntry02 alignedEntry04 alignedEntry22
    alignedEntry24 mixedDeterminantOne
  dsimp only
  ring

private theorem oddB11mLowerSlopeC_lower
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (1 / 50 : ℝ) ≤
      oddB11mSlopeC oddB11mLowerEndpoint C D F a x r c d f dv := by
  rcases hbox.F_mem with ⟨hFL, hFU⟩
  rcases hbox.a_mem with ⟨haL, haU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  have hSF : (0 : ℝ) ≤
      -(828750000 * a - 1503227863) / 5000000000 := by
    apply div_nonneg
    · nlinarith only [haU]
    · norm_num
  have hSa : (1200000 * f - 1041493) / 20000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 20000000)).2
    nlinarith only [hfU]
  have hSr : (0 : ℝ) ≤
      -(60000000 * r - 78608387) / 1000000000 := by
    apply div_nonneg
    · nlinarith only [hrU]
    · norm_num
  have hSf : (-1057328501 / 10000000000 : ℝ) ≤ 0 := by norm_num
  have htel :
      oddB11mCGeometrySlope F a r f -
          (20378969090939 / 1000000000000000 : ℝ) =
        (F - 1571 / 5000) *
          (-(828750000 * a - 1503227863) / 5000000000) +
        (a - 165293 / 200000) *
          ((1200000 * f - 1041493) / 20000000) +
        (r - 49817 / 1000000) *
          (-(60000000 * r - 78608387) / 1000000000) +
        (f - 552 / 3125) * (-1057328501 / 10000000000) := by
    unfold oddB11mCGeometrySlope
    ring
  have hPF : (0 : ℝ) ≤
      (F - 1571 / 5000) *
        (-(828750000 * a - 1503227863) / 5000000000) :=
    mul_nonneg (by nlinarith only [hFL]) hSF
  have hPa : (0 : ℝ) ≤
      (a - 165293 / 200000) *
        ((1200000 * f - 1041493) / 20000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [haU]) hSa
  have hPr : (0 : ℝ) ≤
      (r - 49817 / 1000000) *
        (-(60000000 * r - 78608387) / 1000000000) :=
    mul_nonneg (by nlinarith only [hrL]) hSr
  have hPf : (0 : ℝ) ≤
      (f - 552 / 3125) * (-1057328501 / 10000000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hfU]) hSf
  rw [oddB11mLowerSlopeC_eq]
  nlinarith only [htel, hPF, hPa, hPr, hPf]

private def oddB11mDGeometrySlope
    (D a x r d dv : ℝ) : ℝ :=
  -(-414375000000000 * D * a + 751613931500000 * D +
      300000000000000 * a * d + 5000000000000 * a * dv -
      17775858750000 * a - 776603750500000 * d +
      672950000000000 * dv * r - 170329359100000 * dv +
      300000000000000 * r * x - 32959387500000 * r -
      203993517500000 * x + 45463309891437) / 2500000000000000

set_option maxHeartbeats 3000000 in
private theorem oddB11mLowerSlopeD_eq
    (D F a x r c d f dv : ℝ) :
    oddB11mSlopeD oddB11mLowerEndpoint D F a x r c d f dv =
      oddB11mDGeometrySlope D a x r d dv := by
  unfold oddB11mSlopeD oddB11mLowerEndpoint quadraticSecant
    oddB11mCore oddB11m oddGm oddGx oddP11 oddB11mDGeometrySlope
    alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
    alignedEntry00 alignedEntry02 alignedEntry04 alignedEntry22
    alignedEntry24 mixedDeterminantOne
  dsimp only
  ring

private theorem oddB11mLowerSlopeD_upper
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    oddB11mSlopeD oddB11mLowerEndpoint D F a x r c d f dv ≤
      (-3 / 500 : ℝ) := by
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.a_mem with ⟨haL, haU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  have hSD : (828750000 * a - 1503227863) / 5000000000 ≤
      (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 5000000000)).2
    nlinarith only [haU]
  have hSa : (0 : ℝ) ≤
      -(96000000 * d + 1600000 * dv - 11365809) / 800000000 := by
    apply div_nonneg
    · nlinarith only [hdU, hdvU]
    · norm_num
  have hSx : (0 : ℝ) ≤
      -(120000000 * r - 81597407) / 1000000000 := by
    apply div_nonneg
    · nlinarith only [hrU]
    · norm_num
  have hSr : -(53836000 * dv - 1682487) / 200000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 200000000)).2
    nlinarith only [hdvL]
  have hSd : (0 : ℝ) ≤ (1057328501 / 5000000000 : ℝ) := by norm_num
  have hSdv : (0 : ℝ) ≤ (2653453679 / 50000000000 : ℝ) := by norm_num
  have htel :
      oddB11mDGeometrySlope D a x r d dv -
          (-138865161223703 / 20000000000000000 : ℝ) =
        (D - 42817 / 1000000) *
          ((828750000 * a - 1503227863) / 5000000000) +
        (a - 165293 / 200000) *
          (-(96000000 * d + 1600000 * dv - 11365809) / 800000000) +
        (x - 39761 / 1000000) *
          (-(120000000 * r - 81597407) / 1000000000) +
        (r - 49817 / 1000000) *
          (-(53836000 * dv - 1682487) / 200000000) +
        (d - 27183 / 1000000) * (1057328501 / 5000000000) +
        (dv - 279 / 5000) * (2653453679 / 50000000000) := by
    unfold oddB11mDGeometrySlope
    ring
  have hPD : (D - 42817 / 1000000) *
      ((828750000 * a - 1503227863) / 5000000000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hDL]) hSD
  have hPa : (a - 165293 / 200000) *
      (-(96000000 * d + 1600000 * dv - 11365809) / 800000000) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [haU]) hSa
  have hPx : (x - 39761 / 1000000) *
      (-(120000000 * r - 81597407) / 1000000000) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hxU]) hSx
  have hPr : (r - 49817 / 1000000) *
      (-(53836000 * dv - 1682487) / 200000000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hrL]) hSr
  have hPd :
      (d - 27183 / 1000000) * (1057328501 / 5000000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hdU]) hSd
  have hPdv :
      (dv - 279 / 5000) * (2653453679 / 50000000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hdvU]) hSdv
  rw [oddB11mLowerSlopeD_eq]
  nlinarith only [htel, hPD, hPa, hPx, hPr, hPd, hPdv]

private def oddB11mFGeometrySlope (a c x dv : ℝ) : ℝ :=
  -(-15000000000000 * a * c - 62500000000000 * a * dv ^ 2 +
      548218125000 * a + 38830187525000 * c +
      85889375000000 * dv ^ 2 + 67295000000000 * dv * x -
      2676322150000 * dv + 15000000000000 * x ^ 2 -
      3295938750000 * x - 887030540787) / 250000000000000

set_option maxHeartbeats 3000000 in
private theorem oddB11mLowerSlopeF_eq
    (F a x r c d f dv : ℝ) :
    oddB11mSlopeF oddB11mLowerEndpoint F a x r c d f dv =
      oddB11mFGeometrySlope a c x dv := by
  unfold oddB11mSlopeF oddB11mLowerEndpoint quadraticSecant
    oddB11mCore oddB11m oddGm oddGx oddP11 oddB11mFGeometrySlope
    alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
    alignedEntry00 alignedEntry02 alignedEntry04 alignedEntry22
    alignedEntry24 mixedDeterminantOne
  dsimp only
  ring

private theorem oddB11mLowerSlopeF_lower
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (49 / 50000 : ℝ) ≤
      oddB11mSlopeF oddB11mLowerEndpoint F a x r c d f dv := by
  rcases hbox.a_mem with ⟨haL, haU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  have hdv0 : 0 ≤ dv := by nlinarith only [hdvL]
  have hdvSq : dv * dv ≤ (558 / 10000 : ℝ) * (558 / 10000) :=
    mul_le_mul hdvU hdvU hdv0 (by norm_num)
  have hSa : (24000000 * c + 100000000 * dv ^ 2 - 877149) /
      400000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 400000000)).2
    nlinarith only [hcU, hdvSq]
  have hSc : (-1057328501 / 10000000000 : ℝ) ≤ 0 := by norm_num
  have hSx : -(53836000 * dv + 12000000 * x - 2159619) /
      200000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 200000000)).2
    nlinarith only [hdvL, hxL]
  have hSdv : -(13694125000 * dv + 763889913) / 100000000000 ≤
      (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 100000000000)).2
    nlinarith only [hdvL]
  have htel :
      oddB11mFGeometrySlope a c x dv -
          (98130640531 / 100000000000000 : ℝ) =
        (a - 165293 / 200000) *
          ((24000000 * c + 100000000 * dv ^ 2 - 877149) / 400000000) +
        (c - 1433 / 200000) * (-1057328501 / 10000000000) +
        (x - 39761 / 1000000) *
          (-(53836000 * dv + 12000000 * x - 2159619) / 200000000) +
        (dv - 279 / 5000) *
          (-(13694125000 * dv + 763889913) / 100000000000) := by
    unfold oddB11mFGeometrySlope
    ring
  have hPa : (0 : ℝ) ≤ (a - 165293 / 200000) *
      ((24000000 * c + 100000000 * dv ^ 2 - 877149) / 400000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [haU]) hSa
  have hPc : (0 : ℝ) ≤
      (c - 1433 / 200000) * (-1057328501 / 10000000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hcU]) hSc
  have hPx : (0 : ℝ) ≤ (x - 39761 / 1000000) *
      (-(53836000 * dv + 12000000 * x - 2159619) / 200000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hxU]) hSx
  have hPdv : (0 : ℝ) ≤ (dv - 279 / 5000) *
      (-(13694125000 * dv + 763889913) / 100000000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hdvU]) hSdv
  rw [oddB11mLowerSlopeF_eq]
  nlinarith only [htel, hPa, hPc, hPx, hPdv]

private def oddB11mAGeometrySlope (c d f dv : ℝ) : ℝ :=
  (45750000000000 * c * f + 18848000000000 * c -
      45750000000000 * d ^ 2 + 2000000000000 * d * dv -
      5147760000000 * d - 250000000000000 * dv ^ 2 * f +
      78550000000000 * dv ^ 2 - 85796000000 * dv +
      793800000000 * f - 383928104037) / 1000000000000000

set_option maxHeartbeats 3000000 in
private theorem oddB11mLowerSlopeA_eq
    (a x r c d f dv : ℝ) :
    oddB11mSlopeA oddB11mLowerEndpoint a x r c d f dv =
      oddB11mAGeometrySlope c d f dv := by
  unfold oddB11mSlopeA oddB11mLowerEndpoint quadraticSecant
    oddB11mCore oddB11m oddGm oddGx oddP11 oddB11mAGeometrySlope
    alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
    alignedEntry00 alignedEntry02 alignedEntry04 alignedEntry22
    alignedEntry24 mixedDeterminantOne
  dsimp only
  ring

private theorem oddB11mLowerSlopeA_upper
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    oddB11mSlopeA oddB11mLowerEndpoint a x r c d f dv ≤
      (-9 / 100000 : ℝ) := by
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  have hdv0 : 0 ≤ dv := by nlinarith only [hdvL]
  have hdvSq : dv * dv ≤ (558 / 10000 : ℝ) * (558 / 10000) :=
    mul_le_mul hdvU hdvU hdv0 (by norm_num)
  have hSc : (0 : ℝ) ≤ (22875 * f + 9424) / 500000 := by
    apply div_nonneg
    · nlinarith only [hfL]
    · norm_num
  have hSd : -(183000000 * d - 8000000 * dv + 24858051) /
      4000000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 4000000000)).2
    nlinarith only [hdL, hdvU]
  have hSf : (0 : ℝ) ≤
      -(200000000 * dv ^ 2 - 897279) / 800000000 := by
    apply div_nonneg
    · nlinarith only [hdvSq]
    · norm_num
  have hSdv : (0 : ℝ) ≤ (171950 * dv + 9399) / 5000000 := by
    apply div_nonneg
    · nlinarith only [hdvL]
    · norm_num
  have htel :
      oddB11mAGeometrySlope c d f dv -
          (-72619147703 / 800000000000000 : ℝ) =
        (c - 1433 / 200000) * ((22875 * f + 9424) / 500000) +
        (d - 23317 / 1000000) *
          (-(183000000 * d - 8000000 * dv + 24858051) / 4000000000) +
        (f - 552 / 3125) *
          (-(200000000 * dv ^ 2 - 897279) / 800000000) +
        (dv - 279 / 5000) * ((171950 * dv + 9399) / 5000000) := by
    unfold oddB11mAGeometrySlope
    ring
  have hPc :
      (c - 1433 / 200000) * ((22875 * f + 9424) / 500000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hcU]) hSc
  have hPd : (d - 23317 / 1000000) *
      (-(183000000 * d - 8000000 * dv + 24858051) / 4000000000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hdL]) hSd
  have hPf : (f - 552 / 3125) *
      (-(200000000 * dv ^ 2 - 897279) / 800000000) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hfU]) hSf
  have hPdv :
      (dv - 279 / 5000) * ((171950 * dv + 9399) / 5000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hdvU]) hSdv
  rw [oddB11mLowerSlopeA_eq]
  nlinarith only [htel, hPc, hPd, hPf, hPdv]

private def oddB11mLittleXGeometrySlope
    (x r d f dv : ℝ) : ℝ :=
  -(45750000000000 * d * r + 15112240000000 * d -
      134590000000000 * dv * f - 1000000000000 * dv * r +
      42531076000000 * dv + 22875000000000 * f * x +
      3252041625000 * f + 2573880000000 * r +
      9424000000000 * x - 3464483789243) / 500000000000000

set_option maxHeartbeats 3000000 in
private theorem oddB11mLowerSlopeLittleX_eq
    (x r c d f dv : ℝ) :
    oddB11mSlopeLittleX oddB11mLowerEndpoint x r c d f dv =
      oddB11mLittleXGeometrySlope x r d f dv := by
  unfold oddB11mSlopeLittleX oddB11mLowerEndpoint quadraticSecant
    oddB11mCore oddB11m oddGm oddGx oddP11 oddB11mLittleXGeometrySlope
    alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
    alignedEntry00 alignedEntry02 alignedEntry04 alignedEntry22
    alignedEntry24 mixedDeterminantOne
  dsimp only
  ring

private theorem oddB11mLowerSlopeLittleX_lower
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (17 / 12500 : ℝ) ≤
      oddB11mSlopeLittleX oddB11mLowerEndpoint x r c d f dv := by
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  have hSx : -(22875 * f + 9424) / 500000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 500000)).2
    nlinarith only [hfL]
  have hSr : -(1143750 * d - 25000 * dv + 64347) / 12500000 ≤
      (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 12500000)).2
    nlinarith only [hdL, hdvU]
  have hSd : (-70913449 / 2000000000 : ℝ) ≤ 0 := by norm_num
  have hSf : (0 : ℝ) ≤ (269180000 * dv - 8323149) / 1000000000 := by
    apply div_nonneg
    · nlinarith only [hdvL]
    · norm_num
  have hSdv : (-93634167 / 2500000000 : ℝ) ≤ 0 := by norm_num
  have htel :
      oddB11mLittleXGeometrySlope x r d f dv -
          (545166692529 / 400000000000000 : ℝ) =
        (x - 39761 / 1000000) * (-(22875 * f + 9424) / 500000) +
        (r - 57183 / 1000000) *
          (-(1143750 * d - 25000 * dv + 64347) / 12500000) +
        (d - 27183 / 1000000) * (-70913449 / 2000000000) +
        (f - 4411 / 25000) *
          ((269180000 * dv - 8323149) / 1000000000) +
        (dv - 279 / 5000) * (-93634167 / 2500000000) := by
    unfold oddB11mLittleXGeometrySlope
    ring
  have hPx : (0 : ℝ) ≤
      (x - 39761 / 1000000) * (-(22875 * f + 9424) / 500000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hxU]) hSx
  have hPr : (0 : ℝ) ≤ (r - 57183 / 1000000) *
      (-(1143750 * d - 25000 * dv + 64347) / 12500000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hrU]) hSr
  have hPd : (0 : ℝ) ≤
      (d - 27183 / 1000000) * (-70913449 / 2000000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hdU]) hSd
  have hPf : (0 : ℝ) ≤ (f - 4411 / 25000) *
      ((269180000 * dv - 8323149) / 1000000000) :=
    mul_nonneg (by nlinarith only [hfL]) hSf
  have hPdv : (0 : ℝ) ≤
      (dv - 279 / 5000) * (-93634167 / 2500000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hdvU]) hSdv
  rw [oddB11mLowerSlopeLittleX_eq]
  nlinarith only [htel, hPx, hPr, hPd, hPf, hPdv]

private def oddB11mLittleRGeometrySlope
    (r c d dv : ℝ) : ℝ :=
  -(571875000000 * c * r + 406295096875 * c -
      3364750000000 * d * dv + 102947081250 * d -
      3125000000000 * dv ^ 2 * r + 1362434375000 * dv ^ 2 +
      144389020500 * dv + 9922500000 * r - 17633722728) /
    12500000000000

set_option maxHeartbeats 3000000 in
private theorem oddB11mLowerSlopeLittleR_eq
    (r c d f dv : ℝ) :
    oddB11mSlopeLittleR oddB11mLowerEndpoint r c d f dv =
      oddB11mLittleRGeometrySlope r c d dv := by
  unfold oddB11mSlopeLittleR oddB11mLowerEndpoint quadraticSecant
    oddB11mCore oddB11m oddGm oddGx oddP11 oddB11mLittleRGeometrySlope
    alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
    alignedEntry00 alignedEntry02 alignedEntry04 alignedEntry22
    alignedEntry24 mixedDeterminantOne
  dsimp only
  ring

private theorem oddB11mLowerSlopeLittleR_lower
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (33 / 100000 : ℝ) ≤
      oddB11mSlopeLittleR oddB11mLowerEndpoint r c d f dv := by
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  have hdv0 : 0 ≤ dv := by nlinarith only [hdvL]
  have hdvSq : dv * dv ≤ (558 / 10000 : ℝ) * (558 / 10000) :=
    mul_le_mul hdvU hdvU hdv0 (by norm_num)
  have hSr : -(228750 * c - 1250000 * dv ^ 2 + 3969) / 5000000 ≤
      (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 5000000)).2
    nlinarith only [hcL, hdvSq]
  have hSc : (-3511973 / 100000000 : ℝ) ≤ 0 := by norm_num
  have hSd : (0 : ℝ) ≤
      (538360000 * dv - 16471533) / 2000000000 := by
    apply div_nonneg
    · nlinarith only [hdvL]
    · norm_num
  have hSdv : -11 * (430450000 * dv + 47994799) / 50000000000 ≤
      (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 50000000000)).2
    nlinarith only [hdvL]
  have htel :
      oddB11mLittleRGeometrySlope r c d dv -
          (664911134771 / 2000000000000000 : ℝ) =
        (r - 57183 / 1000000) *
          (-(228750 * c - 1250000 * dv ^ 2 + 3969) / 5000000) +
        (c - 1433 / 200000) * (-3511973 / 100000000) +
        (d - 23317 / 1000000) *
          ((538360000 * dv - 16471533) / 2000000000) +
        (dv - 279 / 5000) *
          (-11 * (430450000 * dv + 47994799) / 50000000000) := by
    unfold oddB11mLittleRGeometrySlope
    ring
  have hPr : (0 : ℝ) ≤ (r - 57183 / 1000000) *
      (-(228750 * c - 1250000 * dv ^ 2 + 3969) / 5000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hrU]) hSr
  have hPc : (0 : ℝ) ≤
      (c - 1433 / 200000) * (-3511973 / 100000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hcU]) hSc
  have hPd : (0 : ℝ) ≤ (d - 23317 / 1000000) *
      ((538360000 * dv - 16471533) / 2000000000) :=
    mul_nonneg (by nlinarith only [hdL]) hSd
  have hPdv : (0 : ℝ) ≤ (dv - 279 / 5000) *
      (-11 * (430450000 * dv + 47994799) / 50000000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hdvU]) hSdv
  rw [oddB11mLowerSlopeLittleR_eq]
  nlinarith only [htel, hPr, hPc, hPd, hPdv]

private def oddB11mLittleCGeometrySlope (f : ℝ) : ℝ :=
  (38245361080000 * f - 19838090094943) / 800000000000000

set_option maxHeartbeats 3000000 in
private theorem oddB11mLowerSlopeLittleC_eq
    (c d f dv : ℝ) :
    oddB11mSlopeLittleC oddB11mLowerEndpoint c d f dv =
      oddB11mLittleCGeometrySlope f := by
  unfold oddB11mSlopeLittleC oddB11mLowerEndpoint quadraticSecant
    oddB11mCore oddB11m oddGm oddGx oddP11 oddB11mLittleCGeometrySlope
    alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
    alignedEntry00 alignedEntry02 alignedEntry04 alignedEntry22
    alignedEntry24 mixedDeterminantOne
  dsimp only
  ring

private theorem oddB11mLowerSlopeLittleC_upper
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    oddB11mSlopeLittleC oddB11mLowerEndpoint c d f dv ≤
      (-163 / 10000 : ℝ) := by
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  have hSlope : (0 : ℝ) ≤ (956134027 / 20000000000 : ℝ) := by
    norm_num
  have htel :
      oddB11mLittleCGeometrySlope f -
          (-65412147568859 / 4000000000000000 : ℝ) =
        (f - 552 / 3125) * (956134027 / 20000000000) := by
    unfold oddB11mLittleCGeometrySlope
    ring
  have hstep :
      (f - 552 / 3125) * (956134027 / 20000000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hfU]) hSlope
  rw [oddB11mLowerSlopeLittleC_eq]
  nlinarith only [htel, hstep]

private def oddB11mLittleDGeometrySlope (d dv : ℝ) : ℝ :=
  -(956134027000000 * d + 1061381471600000 * dv - 192951353119623) /
    20000000000000000

set_option maxHeartbeats 3000000 in
private theorem oddB11mLowerSlopeLittleD_eq
    (d f dv : ℝ) :
    oddB11mSlopeLittleD oddB11mLowerEndpoint d f dv =
      oddB11mLittleDGeometrySlope d dv := by
  unfold oddB11mSlopeLittleD oddB11mLowerEndpoint quadraticSecant
    oddB11mCore oddB11m oddGm oddGx oddP11 oddB11mLittleDGeometrySlope
    alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
    alignedEntry00 alignedEntry02 alignedEntry04 alignedEntry22
    alignedEntry24 mixedDeterminantOne
  dsimp only
  ring

private theorem oddB11mLowerSlopeLittleD_lower
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (53 / 10000 : ℝ) ≤
      oddB11mSlopeLittleD oddB11mLowerEndpoint d f dv := by
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  have hSd : (-956134027 / 20000000000 : ℝ) ≤ 0 := by norm_num
  have hSdv : (-2653453679 / 50000000000 : ℝ) ≤ 0 := by norm_num
  have htel :
      oddB11mLittleDGeometrySlope d dv -
          (53867837874201 / 10000000000000000 : ℝ) =
        (d - 27183 / 1000000) * (-956134027 / 20000000000) +
        (dv - 279 / 5000) * (-2653453679 / 50000000000) := by
    unfold oddB11mLittleDGeometrySlope
    ring
  have hPd : (0 : ℝ) ≤
      (d - 27183 / 1000000) * (-956134027 / 20000000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hdU]) hSd
  have hPdv : (0 : ℝ) ≤
      (dv - 279 / 5000) * (-2653453679 / 50000000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hdvU]) hSdv
  rw [oddB11mLowerSlopeLittleD_eq]
  nlinarith only [htel, hPd, hPdv]

private def oddB11mLittleFGeometrySlope (dv : ℝ) : ℝ :=
  (136941250000000 * dv ^ 2 - 516556420000 * dv - 1040337678571) /
    1000000000000000

set_option maxHeartbeats 3000000 in
private theorem oddB11mLowerSlopeLittleF_eq
    (f dv : ℝ) :
    oddB11mSlopeLittleF oddB11mLowerEndpoint f dv =
      oddB11mLittleFGeometrySlope dv := by
  unfold oddB11mSlopeLittleF oddB11mLowerEndpoint quadraticSecant
    oddB11mCore oddB11m oddGm oddGx oddP11 oddB11mLittleFGeometrySlope
    alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
    alignedEntry00 alignedEntry02 alignedEntry04 alignedEntry22
    alignedEntry24 mixedDeterminantOne
  dsimp only
  ring

private theorem oddB11mLowerSlopeLittleF_upper
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    oddB11mSlopeLittleF oddB11mLowerEndpoint f dv ≤
      (-2 / 3125 : ℝ) := by
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  have hSlope : (0 : ℝ) ≤
      (13694125000 * dv + 712476533) / 100000000000 := by
    apply div_nonneg
    · nlinarith only [hdvL]
    · norm_num
  have htel :
      oddB11mLittleFGeometrySlope dv -
          (-642775773157 / 1000000000000000 : ℝ) =
        (dv - 279 / 5000) *
          ((13694125000 * dv + 712476533) / 100000000000) := by
    unfold oddB11mLittleFGeometrySlope
    ring
  have hstep : (dv - 279 / 5000) *
      ((13694125000 * dv + 712476533) / 100000000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hdvU]) hSlope
  rw [oddB11mLowerSlopeLittleF_eq]
  nlinarith only [htel, hstep]

private def oddB11mDvGeometrySlope (dv : ℝ) : ℝ :=
  -(1903514041950000 * dv - 116543785828411) / 200000000000000000

set_option maxHeartbeats 3000000 in
private theorem oddB11mLowerSlopeDv_eq (dv : ℝ) :
    oddB11mSlopeDv oddB11mLowerEndpoint dv =
      oddB11mDvGeometrySlope dv := by
  unfold oddB11mSlopeDv oddB11mLowerEndpoint quadraticSecant
    oddB11mCore oddB11m oddGm oddGx oddP11 oddB11mDvGeometrySlope
    alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
    alignedEntry00 alignedEntry02 alignedEntry04 alignedEntry22
    alignedEntry24 mixedDeterminantOne
  dsimp only
  ring

private theorem oddB11mLowerSlopeDv_lower
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (1 / 20000 : ℝ) ≤ oddB11mSlopeDv oddB11mLowerEndpoint dv := by
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  have hSlope : (-38070280839 / 4000000000000 : ℝ) ≤ 0 := by norm_num
  have htel :
      oddB11mDvGeometrySlope dv -
          (10327702287601 / 200000000000000000 : ℝ) =
        (dv - 279 / 5000) * (-38070280839 / 4000000000000) := by
    unfold oddB11mDvGeometrySlope
    ring
  have hstep : (0 : ℝ) ≤
      (dv - 279 / 5000) * (-38070280839 / 4000000000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hdvU]) hSlope
  rw [oddB11mLowerSlopeDv_eq]
  nlinarith only [htel, hstep]

private theorem oddB11mLowerEndpointValue_exact :
    oddB11mEndpointValue oddB11mLowerEndpoint =
      (303517759515495539 / 10000000000000000000000 : ℝ) := by
  norm_num [oddB11mEndpointValue, oddB11mLowerEndpoint, oddB11mCore,
    oddB11m, oddGm, oddGx, oddP11, alignedDeterminant,
    alignedMixedDeterminant, alignedAdjugatePair, alignedEntry00,
    alignedEntry02, alignedEntry04, alignedEntry22, alignedEntry24,
    mixedDeterminantOne]

private theorem oddB11mLowerEndpointValue_lower :
    (28 / 1000000 : ℝ) ≤ oddB11mEndpointValue oddB11mLowerEndpoint := by
  rw [oddB11mLowerEndpointValue_exact]
  norm_num

private theorem oddB11m_lower_bound
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (28 / 1000000 : ℝ) ≤
      oddB11mCore X R C D F a x r c d f sv dv v4 q33 h33 := by
  rcases hbox.X_mem with ⟨hXL, hXU⟩
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.C_mem with ⟨hCL, hCU⟩
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.F_mem with ⟨hFL, hFU⟩
  rcases hbox.a_mem with ⟨haL, haU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  rcases hbox.sv_mem with ⟨hsvL, hsvU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  rcases hbox.v4_mem with ⟨hv4L, hv4U⟩
  rcases hbox.q33_mem with ⟨hq33L, hq33U⟩
  rcases hbox.h33_mem with ⟨hh33L, hh33U⟩
  have hsQ33 := oddB11mLowerSlopeQ33_lower
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hsH33 := oddB11mLowerSlopeH33_lower
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hsSv := oddB11mLowerSlopeSv_upper
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hsV4 := oddB11mLowerSlopeV4_lower
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hsX := oddB11mLowerSlopeX_upper
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hsR := oddB11mLowerSlopeR_upper
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hsC := oddB11mLowerSlopeC_lower
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hsD := oddB11mLowerSlopeD_upper
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hsF := oddB11mLowerSlopeF_lower
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hsA := oddB11mLowerSlopeA_upper
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hsx := oddB11mLowerSlopeLittleX_lower
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hsr := oddB11mLowerSlopeLittleR_lower
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hsc := oddB11mLowerSlopeLittleC_upper
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hsd := oddB11mLowerSlopeLittleD_lower
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hsf := oddB11mLowerSlopeLittleF_upper
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hsDv := oddB11mLowerSlopeDv_lower
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hq33Step : (0 : ℝ) ≤
      (q33 - oddB11mLowerEndpoint.q33Value) *
        oddB11mSlopeQ33 oddB11mLowerEndpoint
          X R C D F a x r c d f sv dv v4 q33 h33 := by
    apply mul_nonneg
    · dsimp [oddB11mLowerEndpoint]
      nlinarith only [hq33L]
    · nlinarith only [hsQ33]
  have hh33Step : (0 : ℝ) ≤
      (h33 - oddB11mLowerEndpoint.h33Value) *
        oddB11mSlopeH33 oddB11mLowerEndpoint
          X R C D F a x r c d f sv dv v4 h33 := by
    apply mul_nonneg
    · dsimp [oddB11mLowerEndpoint]
      nlinarith only [hh33L]
    · nlinarith only [hsH33]
  have hsvStep : (0 : ℝ) ≤
      (sv - oddB11mLowerEndpoint.svValue) *
        oddB11mSlopeSv oddB11mLowerEndpoint
          X R C D F a x r c d f sv dv v4 := by
    apply mul_nonneg_of_nonpos_of_nonpos
    · dsimp [oddB11mLowerEndpoint]
      nlinarith only [hsvU]
    · nlinarith only [hsSv]
  have hv4Step : (0 : ℝ) ≤
      (v4 - oddB11mLowerEndpoint.v4Value) *
        oddB11mSlopeV4 oddB11mLowerEndpoint
          X R C D F a x r c d f dv v4 := by
    apply mul_nonneg
    · dsimp [oddB11mLowerEndpoint]
      nlinarith only [hv4L]
    · nlinarith only [hsV4]
  have hXStep : (0 : ℝ) ≤
      (X - oddB11mLowerEndpoint.bigX) *
        oddB11mSlopeX oddB11mLowerEndpoint X R C D F a x r c d f dv := by
    apply mul_nonneg_of_nonpos_of_nonpos
    · dsimp [oddB11mLowerEndpoint]
      nlinarith only [hXU]
    · nlinarith only [hsX]
  have hRStep : (0 : ℝ) ≤
      (R - oddB11mLowerEndpoint.bigR) *
        oddB11mSlopeR oddB11mLowerEndpoint R C D F a x r c d f dv := by
    apply mul_nonneg_of_nonpos_of_nonpos
    · dsimp [oddB11mLowerEndpoint]
      nlinarith only [hRU]
    · nlinarith only [hsR]
  have hCStep : (0 : ℝ) ≤
      (C - oddB11mLowerEndpoint.bigC) *
        oddB11mSlopeC oddB11mLowerEndpoint C D F a x r c d f dv := by
    apply mul_nonneg
    · dsimp [oddB11mLowerEndpoint]
      nlinarith only [hCL]
    · nlinarith only [hsC]
  have hDStep : (0 : ℝ) ≤
      (D - oddB11mLowerEndpoint.bigD) *
        oddB11mSlopeD oddB11mLowerEndpoint D F a x r c d f dv := by
    apply mul_nonneg_of_nonpos_of_nonpos
    · dsimp [oddB11mLowerEndpoint]
      nlinarith only [hDU]
    · nlinarith only [hsD]
  have hFStep : (0 : ℝ) ≤
      (F - oddB11mLowerEndpoint.bigF) *
        oddB11mSlopeF oddB11mLowerEndpoint F a x r c d f dv := by
    apply mul_nonneg
    · dsimp [oddB11mLowerEndpoint]
      nlinarith only [hFL]
    · nlinarith only [hsF]
  have haStep : (0 : ℝ) ≤
      (a - oddB11mLowerEndpoint.littleA) *
        oddB11mSlopeA oddB11mLowerEndpoint a x r c d f dv := by
    apply mul_nonneg_of_nonpos_of_nonpos
    · dsimp [oddB11mLowerEndpoint]
      nlinarith only [haU]
    · nlinarith only [hsA]
  have hxStep : (0 : ℝ) ≤
      (x - oddB11mLowerEndpoint.littleX) *
        oddB11mSlopeLittleX oddB11mLowerEndpoint x r c d f dv := by
    apply mul_nonneg
    · dsimp [oddB11mLowerEndpoint]
      nlinarith only [hxL]
    · nlinarith only [hsx]
  have hrStep : (0 : ℝ) ≤
      (r - oddB11mLowerEndpoint.littleR) *
        oddB11mSlopeLittleR oddB11mLowerEndpoint r c d f dv := by
    apply mul_nonneg
    · dsimp [oddB11mLowerEndpoint]
      nlinarith only [hrL]
    · nlinarith only [hsr]
  have hcStep : (0 : ℝ) ≤
      (c - oddB11mLowerEndpoint.littleC) *
        oddB11mSlopeLittleC oddB11mLowerEndpoint c d f dv := by
    apply mul_nonneg_of_nonpos_of_nonpos
    · dsimp [oddB11mLowerEndpoint]
      nlinarith only [hcU]
    · nlinarith only [hsc]
  have hdStep : (0 : ℝ) ≤
      (d - oddB11mLowerEndpoint.littleD) *
        oddB11mSlopeLittleD oddB11mLowerEndpoint d f dv := by
    apply mul_nonneg
    · dsimp [oddB11mLowerEndpoint]
      nlinarith only [hdL]
    · nlinarith only [hsd]
  have hfStep : (0 : ℝ) ≤
      (f - oddB11mLowerEndpoint.littleF) *
        oddB11mSlopeLittleF oddB11mLowerEndpoint f dv := by
    apply mul_nonneg_of_nonpos_of_nonpos
    · dsimp [oddB11mLowerEndpoint]
      nlinarith only [hfU]
    · nlinarith only [hsf]
  have hdvStep : (0 : ℝ) ≤
      (dv - oddB11mLowerEndpoint.dvValue) *
        oddB11mSlopeDv oddB11mLowerEndpoint dv := by
    apply mul_nonneg
    · dsimp [oddB11mLowerEndpoint]
      nlinarith only [hdvL]
    · nlinarith only [hsDv]
  have htel := oddB11m_lower_telescope
    X R C D F a x r c d f sv dv v4 q33 h33
  have hend := oddB11mLowerEndpointValue_lower
  nlinarith only [htel, hend, hq33Step, hh33Step, hsvStep, hv4Step,
    hXStep, hRStep, hCStep, hDStep, hFStep, haStep, hxStep, hrStep,
    hcStep, hdStep, hfStep, hdvStep]

set_option maxHeartbeats 3000000 in
private theorem oddB11mUpperSlopeQ33_eq_lower
    (X R C D F a x r c d f sv dv v4 q33 h33 : ℝ) :
    oddB11mSlopeQ33 oddB11mUpperEndpoint
        X R C D F a x r c d f sv dv v4 q33 h33 =
      oddB11mSlopeQ33 oddB11mLowerEndpoint
        X R C D F a x r c d f sv dv v4 q33 h33 := by
  unfold oddB11mSlopeQ33 oddB11mUpperEndpoint oddB11mLowerEndpoint
    quadraticSecant oddB11mCore oddB11m
  dsimp only
  ring

private theorem oddB11mUpperSlopeQ33_lower
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (1 / 10000 : ℝ) ≤
      oddB11mSlopeQ33 oddB11mUpperEndpoint
        X R C D F a x r c d f sv dv v4 q33 h33 := by
  rw [oddB11mUpperSlopeQ33_eq_lower]
  exact oddB11mLowerSlopeQ33_lower
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox

set_option maxHeartbeats 3000000 in
private theorem oddB11mUpperSlopeH33_eq_lower
    (X R C D F a x r c d f sv dv v4 h33 : ℝ) :
    oddB11mSlopeH33 oddB11mUpperEndpoint
        X R C D F a x r c d f sv dv v4 h33 =
      oddB11mSlopeH33 oddB11mLowerEndpoint
        X R C D F a x r c d f sv dv v4 h33 := by
  unfold oddB11mSlopeH33 oddB11mUpperEndpoint oddB11mLowerEndpoint
    quadraticSecant oddB11mCore oddB11m
  dsimp only
  ring

private theorem oddB11mUpperSlopeH33_lower
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (1 / 10000 : ℝ) ≤
      oddB11mSlopeH33 oddB11mUpperEndpoint
        X R C D F a x r c d f sv dv v4 h33 := by
  rw [oddB11mUpperSlopeH33_eq_lower]
  exact oddB11mLowerSlopeH33_lower
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox

private def oddB11mUpperSvBracket
    (X R C D F x r c d f sv dv v4 : ℝ) : ℝ :=
  oddB11mSvMinorZero C D F c d f * ((sv + 10763 / 20000) / 2) -
    oddB11mSvMinorOne X R D F x r d f * dv -
      oddB11mSvMinorTwo X R C D x r c d * v4

set_option maxHeartbeats 3000000 in
private theorem oddB11mUpperSlopeSv_eq
    (X R C D F a x r c d f sv dv v4 : ℝ) :
    oddB11mSlopeSv oddB11mUpperEndpoint
        X R C D F a x r c d f sv dv v4 =
      -oddB11mUpperSvBracket X R C D F x r c d f sv dv v4 / 2 := by
  unfold oddB11mSlopeSv oddB11mUpperEndpoint quadraticSecant
    oddB11mCore oddB11m oddP11 oddB11mUpperSvBracket
    oddB11mSvMinorZero oddB11mSvMinorOne oddB11mSvMinorTwo
    alignedAdjugatePair
  dsimp only
  ring

private theorem oddB11mUpperSlopeSv_upper
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    oddB11mSlopeSv oddB11mUpperEndpoint
        X R C D F a x r c d f sv dv v4 ≤
      (-9 / 1000000 : ℝ) := by
  rcases hbox.X_mem with ⟨hXL, hXU⟩
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.C_mem with ⟨hCL, hCU⟩
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.F_mem with ⟨hFL, hFU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  rcases hbox.sv_mem with ⟨hsvL, hsvU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  rcases hbox.v4_mem with ⟨hv4L, hv4U⟩
  have hCpL : (1213 / 200000 : ℝ) ≤ C - c := by
    nlinarith only [hCL, hcU]
  have hCp0 : 0 ≤ C - c := by nlinarith only [hCpL]
  have hFpL : (3439 / 25000 : ℝ) ≤ F - f := by
    nlinarith only [hFL, hfU]
  have hFp0 : 0 ≤ F - f := by nlinarith only [hFpL]
  have hFpU : F - f ≤ (433 / 3125 : ℝ) := by
    nlinarith only [hFU, hfL]
  have hDp0 : 0 ≤ D - d := by nlinarith only [hDL, hdU]
  have hDpU : D - d ≤ (19581 / 1000000 : ℝ) := by
    nlinarith only [hDU, hdL]
  have hRpL : (92817 / 500000 : ℝ) ≤ R - r := by
    nlinarith only [hRL, hrU]
  have hRp0 : 0 ≤ R - r := by nlinarith only [hRpL]
  have hRpU : R - r ≤ (193081 / 1000000 : ℝ) := by
    nlinarith only [hRU, hrL]
  have hXpL : (-141 / 1000000 : ℝ) ≤ X - x := by
    nlinarith only [hXL, hxU]
  have hXpU : X - x ≤ (1919 / 1000000 : ℝ) := by
    nlinarith only [hXU, hxL]
  have hCpFp : (1213 / 200000 : ℝ) * (3439 / 25000) ≤
      (C - c) * (F - f) :=
    mul_le_mul hCpL hFpL (by norm_num) hCp0
  have hDpSq : (D - d) * (D - d) ≤
      (19581 / 1000000 : ℝ) * (19581 / 1000000) :=
    mul_le_mul hDpU hDpU hDp0 (by norm_num)
  have hs0 : (450885839 / 1000000000000 : ℝ) ≤
      oddB11mSvMinorZero C D F c d f := by
    unfold oddB11mSvMinorZero
    nlinarith only [hCpFp, hDpSq]
  have hs00 : 0 ≤ oddB11mSvMinorZero C D F c d f := by
    nlinarith only [hs0]
  have hDpRp : (D - d) * (R - r) ≤
      (19581 / 1000000 : ℝ) * (193081 / 1000000) :=
    mul_le_mul hDpU hRpU hRp0 (by norm_num)
  have hFpXp1 : (F - f) * (X - x) ≤
      (F - f) * (1919 / 1000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hXpU hFp0
  have hFpXp2 : (F - f) * (1919 / 1000000 : ℝ) ≤
      (433 / 3125 : ℝ) * (1919 / 1000000) :=
    mul_le_mul_of_nonneg_right hFpU (by norm_num)
  have hs1 : oddB11mSvMinorOne X R D F x r d f ≤
      (4046615701 / 1000000000000 : ℝ) := by
    unfold oddB11mSvMinorOne
    nlinarith only [hDpRp, hFpXp1, hFpXp2]
  have hCpRp : (1213 / 200000 : ℝ) * (92817 / 500000) ≤
      (C - c) * (R - r) :=
    mul_le_mul hCpL hRpL (by norm_num) hCp0
  have hXpDp1 : (-141 / 1000000 : ℝ) * (19581 / 1000000) ≤
      (-141 / 1000000 : ℝ) * (D - d) :=
    mul_le_mul_of_nonpos_left hDpU (by norm_num)
  have hXpDp2 : (-141 / 1000000 : ℝ) * (D - d) ≤
      (X - x) * (D - d) :=
    mul_le_mul_of_nonneg_right hXpL hDp0
  have hs2 : (1123109289 / 1000000000000 : ℝ) ≤
      oddB11mSvMinorTwo X R C D x r c d := by
    unfold oddB11mSvMinorTwo
    nlinarith only [hCpRp, hXpDp1, hXpDp2]
  have hs20 : 0 ≤ oddB11mSvMinorTwo X R C D x r c d := by
    nlinarith only [hs2]
  have hsvBar : (10763 / 20000 : ℝ) ≤
      (sv + 10763 / 20000) / 2 := by
    nlinarith only [hsvL]
  have hs0Product :
      (450885839 / 1000000000000 : ℝ) * (10763 / 20000) ≤
        oddB11mSvMinorZero C D F c d f * ((sv + 10763 / 20000) / 2) :=
    mul_le_mul hs0 hsvBar (by norm_num) hs00
  have hdv0 : 0 ≤ dv := by nlinarith only [hdvL]
  have hs1Product : oddB11mSvMinorOne X R D F x r d f * dv ≤
      (4046615701 / 1000000000000 : ℝ) * (558 / 10000) :=
    mul_le_mul hs1 hdvU hdv0 (by norm_num)
  have hv4Neg : (2 / 1000 : ℝ) ≤ -v4 := by
    nlinarith only [hv4U]
  have hs2Product :
      (1123109289 / 1000000000000 : ℝ) * (2 / 1000) ≤
        oddB11mSvMinorTwo X R C D x r c d * (-v4) :=
    mul_le_mul hs2 hv4Neg (by norm_num) hs20
  have hbracket : (18 / 1000000 : ℝ) ≤
      oddB11mUpperSvBracket X R C D F x r c d f sv dv v4 := by
    unfold oddB11mUpperSvBracket
    nlinarith only [hs0Product, hs1Product, hs2Product]
  rw [oddB11mUpperSlopeSv_eq]
  nlinarith only [hbracket]

private def oddB11mUpperV4Lead
    (X R C D a x r c d dv : ℝ) : ℝ :=
  -oddB11mSvMinorTwo X R C D x r c d * (10763 / 20000) +
    ((X - x) * (R - r) + ((137423 / 100000) - a) * (D - d)) * dv

private def oddB11mUpperV4Bracket
    (X R C D a x r c d dv v4 : ℝ) : ℝ :=
  oddB11mUpperV4Lead X R C D a x r c d dv +
    oddB11mV4TailMinor X C a x c * ((v4 - 1 / 500) / 2)

set_option maxHeartbeats 3000000 in
private theorem oddB11mUpperSlopeV4_eq
    (X R C D F a x r c d f dv v4 : ℝ) :
    oddB11mSlopeV4 oddB11mUpperEndpoint
        X R C D F a x r c d f dv v4 =
      -oddB11mUpperV4Bracket X R C D a x r c d dv v4 / 2 := by
  unfold oddB11mSlopeV4 oddB11mUpperEndpoint quadraticSecant
    oddB11mCore oddB11m oddP11 oddB11mUpperV4Bracket
    oddB11mUpperV4Lead oddB11mV4TailMinor oddB11mSvMinorTwo
    alignedAdjugatePair
  dsimp only
  ring

private theorem oddB11mUpperSlopeV4_lower
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (2 / 1000000 : ℝ) ≤
      oddB11mSlopeV4 oddB11mUpperEndpoint
        X R C D F a x r c d f dv v4 := by
  rcases hbox.X_mem with ⟨hXL, hXU⟩
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.C_mem with ⟨hCL, hCU⟩
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.a_mem with ⟨haL, haU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  rcases hbox.v4_mem with ⟨hv4L, hv4U⟩
  have hRp0 : 0 ≤ R - r := by nlinarith only [hRL, hrU]
  have hDp0 : 0 ≤ D - d := by nlinarith only [hDL, hdU]
  have hdv0 : 0 ≤ dv := by nlinarith only [hdvL]
  have hXpL : (-141 / 1000000 : ℝ) ≤ X - x := by
    nlinarith only [hXL, hxU]
  have hXpU : X - x ≤ (1919 / 1000000 : ℝ) := by
    nlinarith only [hXU, hxL]
  have hSC : (10763 * (-R + r) / 20000 : ℝ) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · nlinarith only [hRp0]
    · norm_num
  have hSc : 0 ≤ (-10763 * (-R + r) / 20000 : ℝ) := by
    apply div_nonneg
    · nlinarith only [hRp0]
    · norm_num
  have hSa : dv * (-D + d) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hdv0 (by nlinarith only [hDp0])
  have hDvXp1 : dv * (X - x) ≤ dv * (1919 / 1000000 : ℝ) :=
    mul_le_mul_of_nonneg_left hXpU hdv0
  have hDvXp2 : dv * (1919 / 1000000 : ℝ) ≤
      (558 / 10000 : ℝ) * (1919 / 1000000) :=
    mul_le_mul_of_nonneg_right hdvU (by norm_num)
  have hInnerR : 0 ≤
      -4000000000 * X * dv + 4000000000 * dv * x + 13055519 := by
    nlinarith only [hDvXp1, hDvXp2]
  have hSR :
      -(-4000000000 * X * dv + 4000000000 * dv * x + 13055519) /
          4000000000 ≤ (0 : ℝ) := by
    apply div_nonpos_of_nonpos_of_nonneg
    · nlinarith only [hInnerR]
    · norm_num
  have hSD : (0 : ℝ) ≤
      (-538150 * X + 549751 * dv + 538150 * x) / 1000000 := by
    apply div_nonneg
    · nlinarith only [hdvL, hXpU]
    · norm_num
  have hSr : (0 : ℝ) ≤
      (-4000000000 * X * dv + 4000000000 * dv * x + 13055519) /
          4000000000 :=
    div_nonneg hInnerR (by norm_num)
  have hSd :
      -(-538150 * X + 549751 * dv + 538150 * x) / 1000000 ≤
        (0 : ℝ) := by
    apply div_nonpos_of_nonpos_of_nonneg
    · nlinarith only [hSD]
    · norm_num
  have hSdv : (0 : ℝ) ≤
      -3 * (-61878000000 * X + 61878000000 * x - 3588224777) /
          1000000000000 := by
    apply div_nonneg
    · nlinarith only [hXpL]
    · norm_num
  have hSX : (-3582759 / 20000000000 : ℝ) ≤ 0 := by norm_num
  have hSx : (0 : ℝ) ≤ (3582759 / 20000000000 : ℝ) := by norm_num
  have htel :
      oddB11mUpperV4Lead X R C D a x r c d dv -
          (-20771869563 / 4000000000000000 : ℝ) =
        (C - 1323 / 100000) * (10763 * (-R + r) / 20000) +
        (c - 1433 / 200000) * (-10763 * (-R + r) / 20000) +
        (a - 824479 / 1000000) * (dv * (-D + d)) +
        (R - 242817 / 1000000) *
          (-(-4000000000 * X * dv + 4000000000 * dv * x + 13055519) /
            4000000000) +
        (D - 21449 / 500000) *
          ((-538150 * X + 549751 * dv + 538150 * x) / 1000000) +
        (r - 57183 / 1000000) *
          ((-4000000000 * X * dv + 4000000000 * dv * x + 13055519) /
            4000000000) +
        (d - 23317 / 1000000) *
          (-(-538150 * X + 549751 * dv + 538150 * x) / 1000000) +
        (dv - 279 / 5000) *
          (-3 * (-61878000000 * X + 61878000000 * x - 3588224777) /
            1000000000000) +
        (X - 1981 / 50000) * (-3582759 / 20000000000) +
        (x - 39761 / 1000000) * (3582759 / 20000000000) := by
    unfold oddB11mUpperV4Lead oddB11mSvMinorTwo
    ring
  have hPC :
      (C - 1323 / 100000) * (10763 * (-R + r) / 20000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hCL]) hSC
  have hPc :
      (c - 1433 / 200000) * (-10763 * (-R + r) / 20000) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hcU]) hSc
  have hPa : (a - 824479 / 1000000) * (dv * (-D + d)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [haL]) hSa
  have hPR : (R - 242817 / 1000000) *
      (-(-4000000000 * X * dv + 4000000000 * dv * x + 13055519) /
        4000000000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hRL]) hSR
  have hPD : (D - 21449 / 500000) *
      ((-538150 * X + 549751 * dv + 538150 * x) / 1000000) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hDU]) hSD
  have hPr : (r - 57183 / 1000000) *
      ((-4000000000 * X * dv + 4000000000 * dv * x + 13055519) /
        4000000000) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hrU]) hSr
  have hPd : (d - 23317 / 1000000) *
      (-(-538150 * X + 549751 * dv + 538150 * x) / 1000000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hdL]) hSd
  have hPdv : (dv - 279 / 5000) *
      (-3 * (-61878000000 * X + 61878000000 * x - 3588224777) /
        1000000000000) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hdvU]) hSdv
  have hPX :
      (X - 1981 / 50000) * (-3582759 / 20000000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hXL]) hSX
  have hPx :
      (x - 39761 / 1000000) * (3582759 / 20000000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hxU]) hSx
  have hLead : oddB11mUpperV4Lead X R C D a x r c d dv ≤
      (-20771869563 / 4000000000000000 : ℝ) := by
    nlinarith only [htel, hPC, hPc, hPa, hPR, hPD, hPr, hPd, hPdv, hPX, hPx]
  have hApL : (109553 / 200000 : ℝ) ≤ (137423 / 100000) - a := by
    nlinarith only [haU]
  have hCpL : (1213 / 200000 : ℝ) ≤ C - c := by
    nlinarith only [hCL, hcU]
  have hApCp : (109553 / 200000 : ℝ) * (1213 / 200000) ≤
      ((137423 / 100000) - a) * (C - c) :=
    mul_le_mul hApL hCpL (by norm_num) (by nlinarith only [hApL])
  have hAbsLeft : -(1919 / 1000000 : ℝ) ≤ X - x := by
    nlinarith only [hXpL]
  have hSqProduct : 0 ≤
      ((1919 / 1000000 : ℝ) - (X - x)) *
        ((1919 / 1000000 : ℝ) + (X - x)) :=
    mul_nonneg (by nlinarith only [hXpU]) (by nlinarith only [hAbsLeft])
  have hXpSq : (X - x) ^ 2 ≤ (1919 / 1000000 : ℝ) ^ 2 := by
    nlinarith only [hSqProduct]
  have ht2 : (829628041 / 250000000000 : ℝ) ≤
      oddB11mV4TailMinor X C a x c := by
    unfold oddB11mV4TailMinor
    nlinarith only [hApCp, hXpSq]
  have hvbarU : (v4 - 1 / 500) / 2 ≤ (-2 / 1000 : ℝ) := by
    nlinarith only [hv4U]
  have hvbar0 : (v4 - 1 / 500) / 2 ≤ (0 : ℝ) := by
    nlinarith only [hvbarU]
  have hTail1 :
      oddB11mV4TailMinor X C a x c * ((v4 - 1 / 500) / 2) ≤
        (829628041 / 250000000000 : ℝ) * ((v4 - 1 / 500) / 2) :=
    mul_le_mul_of_nonpos_right ht2 hvbar0
  have hTail2 :
      (829628041 / 250000000000 : ℝ) * ((v4 - 1 / 500) / 2) ≤
        (829628041 / 250000000000 : ℝ) * (-2 / 1000) :=
    mul_le_mul_of_nonneg_left hvbarU (by norm_num)
  have hbracket : oddB11mUpperV4Bracket X R C D a x r c d dv v4 ≤
      (-75711947 / 6400000000000 : ℝ) := by
    unfold oddB11mUpperV4Bracket
    nlinarith only [hLead, hTail1, hTail2]
  rw [oddB11mUpperSlopeV4_eq]
  nlinarith only [hbracket]

private def oddB11mUpperXGeometrySlope
    (X R D F x r d f dv : ℝ) : ℝ :=
  -(27450000000 * D * R - 16650000000 * D * r + 26907500 * D +
      13725000000 * F * X - 13453750000 * F * dv -
      16650000000 * F * x + 543784500 * F - 16650000000 * R * d -
      50000000 * R * dv - 8325000000 * X * f - 50000 * X +
      5850000000 * d * r - 26907500 * d + 13453750000 * dv * f +
      50000000 * dv * r + 5850000000 * f * x - 329836500 * f +
      100000 * x - 1981) / 50000000000

set_option maxHeartbeats 3000000 in
private theorem oddB11mUpperSlopeX_eq
    (X R C D F a x r c d f dv : ℝ) :
    oddB11mSlopeX oddB11mUpperEndpoint X R C D F a x r c d f dv =
      oddB11mUpperXGeometrySlope X R D F x r d f dv := by
  unfold oddB11mSlopeX oddB11mUpperEndpoint quadraticSecant
    oddB11mCore oddB11m oddGm oddGx oddP11 oddB11mUpperXGeometrySlope
    alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
    alignedEntry00 alignedEntry02 alignedEntry04 alignedEntry22
    alignedEntry24 mixedDeterminantOne
  dsimp only
  ring

private theorem oddB11mUpperSlopeX_upper
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    oddB11mSlopeX oddB11mUpperEndpoint X R C D F a x r c d f dv ≤
      (-19 / 10000 : ℝ) := by
  rcases hbox.X_mem with ⟨hXL, hXU⟩
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.F_mem with ⟨hFL, hFU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  have hSX : (-274500 * F + 166500 * f + 1) / 1000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1000000)).2
    nlinarith only [hFL, hfU]
  have hSR : (-549 * D + 333 * d + dv) / 1000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1000)).2
    nlinarith only [hDL, hdU, hdvU]
  have hSD : (333000000 * r - 133844683) / 1000000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1000000000)).2
    nlinarith only [hrU]
  have hSF : (0 : ℝ) ≤
      (13453750 * dv + 16650000 * x - 1087569) / 50000000 := by
    apply div_nonneg
    · nlinarith only [hdvL, hxL]
    · norm_num
  have hSx : (0 : ℝ) ≤ -(117000 * f - 104893) / 1000000 := by
    apply div_nonneg
    · nlinarith only [hfU]
    · norm_num
  have hSr : (0 : ℝ) ≤
      -(117000000 * d + 1000000 * dv - 14258061) / 1000000000 := by
    apply div_nonneg
    · nlinarith only [hdU, hdvU]
    · norm_num
  have hSd : (0 : ℝ) ≤ (373529 / 5000000 : ℝ) := by norm_num
  have hSf : -(269075000 * dv - 8541423) / 1000000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1000000000)).2
    nlinarith only [hdvL]
  have hSdv : (0 : ℝ) ≤ (18734333 / 500000000 : ℝ) := by norm_num
  have htel :
      oddB11mUpperXGeometrySlope X R D F x r d f dv -
          (-61497999329 / 31250000000000 : ℝ) =
        (X - 1981 / 50000) * ((-274500 * F + 166500 * f + 1) / 1000000) +
        (R - 242817 / 1000000) * ((-549 * D + 333 * d + dv) / 1000) +
        (D - 42817 / 1000000) *
          ((333000000 * r - 133844683) / 1000000000) +
        (F - 63 / 200) *
          ((13453750 * dv + 16650000 * x - 1087569) / 50000000) +
        (x - 39761 / 1000000) * (-(117000 * f - 104893) / 1000000) +
        (r - 57183 / 1000000) *
          (-(117000000 * d + 1000000 * dv - 14258061) / 1000000000) +
        (d - 27183 / 1000000) * (373529 / 5000000) +
        (f - 4411 / 25000) *
          (-(269075000 * dv - 8541423) / 1000000000) +
        (dv - 279 / 5000) * (18734333 / 500000000) := by
    unfold oddB11mUpperXGeometrySlope
    ring
  have hPX : (X - 1981 / 50000) *
      ((-274500 * F + 166500 * f + 1) / 1000000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hXL]) hSX
  have hPR : (R - 242817 / 1000000) *
      ((-549 * D + 333 * d + dv) / 1000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hRL]) hSR
  have hPD : (D - 42817 / 1000000) *
      ((333000000 * r - 133844683) / 1000000000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hDL]) hSD
  have hPF : (F - 63 / 200) *
      ((13453750 * dv + 16650000 * x - 1087569) / 50000000) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hFU]) hSF
  have hPx : (x - 39761 / 1000000) *
      (-(117000 * f - 104893) / 1000000) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hxU]) hSx
  have hPr : (r - 57183 / 1000000) *
      (-(117000000 * d + 1000000 * dv - 14258061) / 1000000000) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hrU]) hSr
  have hPd :
      (d - 27183 / 1000000) * (373529 / 5000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hdU]) hSd
  have hPf : (f - 4411 / 25000) *
      (-(269075000 * dv - 8541423) / 1000000000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hfL]) hSf
  have hPdv :
      (dv - 279 / 5000) * (18734333 / 500000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hdvU]) hSdv
  rw [oddB11mUpperSlopeX_eq]
  nlinarith only [htel, hPX, hPR, hPD, hPF, hPx, hPr, hPd, hPf, hPdv]

private def oddB11mUpperRGeometrySlope
    (R C D x r c d dv : ℝ) : ℝ :=
  -(549000000 * C * R - 666000000 * C * r + 134382833 * C -
      538150000 * D * dv - 666000000 * D * x + 43502760 * D -
      333000000 * R * c - 500000000 * R * dv ^ 2 +
      234000000 * c * r - 81934361 * c + 538150000 * d * dv +
      234000000 * d * x - 26386920 * d + 1000000000 * dv ^ 2 * r -
      121408500 * dv ^ 2 + 2000000 * dv * x - 79240 * dv) /
    2000000000

set_option maxHeartbeats 3000000 in
private theorem oddB11mUpperSlopeR_eq
    (R C D F a x r c d f dv : ℝ) :
    oddB11mSlopeR oddB11mUpperEndpoint R C D F a x r c d f dv =
      oddB11mUpperRGeometrySlope R C D x r c d dv := by
  unfold oddB11mSlopeR oddB11mUpperEndpoint quadraticSecant
    oddB11mCore oddB11m oddGm oddGx oddP11 oddB11mUpperRGeometrySlope
    alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
    alignedEntry00 alignedEntry02 alignedEntry04 alignedEntry22
    alignedEntry24 mixedDeterminantOne
  dsimp only
  ring

private theorem oddB11mUpperSlopeR_upper
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    oddB11mSlopeR oddB11mUpperEndpoint R C D F a x r c d f dv ≤
      (-11 / 20000 : ℝ) := by
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.C_mem with ⟨hCL, hCU⟩
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  have hdv0 : 0 ≤ dv := by nlinarith only [hdvL]
  have hdvSq : dv * dv ≤ (558 / 10000 : ℝ) * (558 / 10000) :=
    mul_le_mul hdvU hdvU hdv0 (by norm_num)
  have hSR : (-549 * C + 333 * c + 500 * dv ^ 2) / 2000 ≤
      (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2000)).2
    nlinarith only [hCL, hcU, hdvSq]
  have hSC : (333000000 * r - 133844683) / 1000000000 ≤
      (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1000000000)).2
    nlinarith only [hrU]
  have hSD : (0 : ℝ) ≤
      (13453750 * dv + 16650000 * x - 1087569) / 50000000 := by
    apply div_nonneg
    · nlinarith only [hdvL, hxL]
    · norm_num
  have hSx : (0 : ℝ) ≤
      -(58500000 * d + 500000 * dv - 7142517) / 500000000 := by
    apply div_nonneg
    · nlinarith only [hdU, hdvU]
    · norm_num
  have hSr : (0 : ℝ) ≤
      -(11700000 * c + 50000000 * dv ^ 2 - 440559) / 100000000 := by
    apply div_nonneg
    · nlinarith only [hcU, hdvSq]
    · norm_num
  have hSc : (0 : ℝ) ≤ (373529 / 5000000 : ℝ) := by norm_num
  have hSd : -(269075000 * dv - 8541423) / 1000000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1000000000)).2
    nlinarith only [hdvL]
  have hSdv : (0 : ℝ) ≤
      3 * (1237560000 * dv + 139304069) / 40000000000 := by
    apply div_nonneg
    · nlinarith only [hdvL]
    · norm_num
  have htel :
      oddB11mUpperRGeometrySlope R C D x r c d dv -
          (-56652881963 / 100000000000000 : ℝ) =
        (R - 242817 / 1000000) *
          ((-549 * C + 333 * c + 500 * dv ^ 2) / 2000) +
        (C - 1323 / 100000) *
          ((333000000 * r - 133844683) / 1000000000) +
        (D - 42898 / 1000000) *
          ((13453750 * dv + 16650000 * x - 1087569) / 50000000) +
        (x - 39761 / 1000000) *
          (-(58500000 * d + 500000 * dv - 7142517) / 500000000) +
        (r - 57183 / 1000000) *
          (-(11700000 * c + 50000000 * dv ^ 2 - 440559) / 100000000) +
        (c - 1433 / 200000) * (373529 / 5000000) +
        (d - 23317 / 1000000) *
          (-(269075000 * dv - 8541423) / 1000000000) +
        (dv - 279 / 5000) *
          (3 * (1237560000 * dv + 139304069) / 40000000000) := by
    unfold oddB11mUpperRGeometrySlope
    ring
  have hPR : (R - 242817 / 1000000) *
      ((-549 * C + 333 * c + 500 * dv ^ 2) / 2000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hRL]) hSR
  have hPC : (C - 1323 / 100000) *
      ((333000000 * r - 133844683) / 1000000000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hCL]) hSC
  have hPD : (D - 42898 / 1000000) *
      ((13453750 * dv + 16650000 * x - 1087569) / 50000000) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hDU]) hSD
  have hPx : (x - 39761 / 1000000) *
      (-(58500000 * d + 500000 * dv - 7142517) / 500000000) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hxU]) hSx
  have hPr : (r - 57183 / 1000000) *
      (-(11700000 * c + 50000000 * dv ^ 2 - 440559) / 100000000) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hrU]) hSr
  have hPc :
      (c - 1433 / 200000) * (373529 / 5000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hcU]) hSc
  have hPd : (d - 23317 / 1000000) *
      (-(269075000 * dv - 8541423) / 1000000000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hdL]) hSd
  have hPdv : (dv - 279 / 5000) *
      (3 * (1237560000 * dv + 139304069) / 40000000000) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hdvU]) hSdv
  rw [oddB11mUpperSlopeR_eq]
  nlinarith only [htel, hPR, hPC, hPD, hPx, hPr, hPc, hPd, hPdv]

private def oddB11mUpperCGeometrySlope (F a r f : ℝ) : ℝ :=
  -(333000000000000 * F * a - 609649558750000 * F -
      117000000000000 * a * f - 2000000000 * a +
      312815878750000 * f + 117000000000000 * r ^ 2 -
      162792422000000 * r + 32633184820561) / 2000000000000000

set_option maxHeartbeats 3000000 in
private theorem oddB11mUpperSlopeC_eq
    (C D F a x r c d f dv : ℝ) :
    oddB11mSlopeC oddB11mUpperEndpoint C D F a x r c d f dv =
      oddB11mUpperCGeometrySlope F a r f := by
  unfold oddB11mSlopeC oddB11mUpperEndpoint quadraticSecant
    oddB11mCore oddB11m oddGm oddGx oddP11 oddB11mUpperCGeometrySlope
    alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
    alignedEntry00 alignedEntry02 alignedEntry04 alignedEntry22
    alignedEntry24 mixedDeterminantOne
  dsimp only
  ring

private theorem oddB11mUpperSlopeC_lower
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (21 / 1000 : ℝ) ≤
      oddB11mSlopeC oddB11mUpperEndpoint C D F a x r c d f dv := by
  rcases hbox.F_mem with ⟨hFL, hFU⟩
  rcases hbox.a_mem with ⟨haL, haU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  have hSF : (0 : ℝ) ≤
      -(266400000 * a - 487719647) / 1600000000 := by
    apply div_nonneg
    · nlinarith only [haU]
    · norm_num
  have hSa : 13 * (45000 * f - 40241) / 10000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 10000000)).2
    nlinarith only [hfU]
  have hSr : (0 : ℝ) ≤
      -13 * (9000000 * r - 12074141) / 2000000000 := by
    apply div_nonneg
    · nlinarith only [hrU]
    · norm_num
  have hSf : (-172895579 / 1600000000 : ℝ) ≤ 0 := by norm_num
  have htel :
      oddB11mUpperCGeometrySlope F a r f -
          (841852139901 / 40000000000000 : ℝ) =
        (F - 1571 / 5000) *
          (-(266400000 * a - 487719647) / 1600000000) +
        (a - 165293 / 200000) *
          (13 * (45000 * f - 40241) / 10000000) +
        (r - 49817 / 1000000) *
          (-13 * (9000000 * r - 12074141) / 2000000000) +
        (f - 552 / 3125) * (-172895579 / 1600000000) := by
    unfold oddB11mUpperCGeometrySlope
    ring
  have hPF : (0 : ℝ) ≤ (F - 1571 / 5000) *
      (-(266400000 * a - 487719647) / 1600000000) :=
    mul_nonneg (by nlinarith only [hFL]) hSF
  have hPa : (0 : ℝ) ≤ (a - 165293 / 200000) *
      (13 * (45000 * f - 40241) / 10000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [haU]) hSa
  have hPr : (0 : ℝ) ≤ (r - 49817 / 1000000) *
      (-13 * (9000000 * r - 12074141) / 2000000000) :=
    mul_nonneg (by nlinarith only [hrL]) hSr
  have hPf : (0 : ℝ) ≤
      (f - 552 / 3125) * (-172895579 / 1600000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hfU]) hSf
  rw [oddB11mUpperSlopeC_eq]
  nlinarith only [htel, hPF, hPa, hPr, hPf]

private def oddB11mUpperDGeometrySlope
    (D a x r d dv : ℝ) : ℝ :=
  -(-53280000000000 * D * a + 97543929400000 * D +
      37440000000000 * a * d + 320000000000 * a * dv -
      2281289760000 * a - 100101081200000 * d +
      86104000000000 * dv * r - 21347268568000 * dv +
      37440000000000 * r * x - 4221907200000 * r -
      26046787520000 * x + 5873474854067) / 320000000000000

set_option maxHeartbeats 3000000 in
private theorem oddB11mUpperSlopeD_eq
    (D F a x r c d f dv : ℝ) :
    oddB11mSlopeD oddB11mUpperEndpoint D F a x r c d f dv =
      oddB11mUpperDGeometrySlope D a x r d dv := by
  unfold oddB11mSlopeD oddB11mUpperEndpoint quadraticSecant
    oddB11mCore oddB11m oddGm oddGx oddP11 oddB11mUpperDGeometrySlope
    alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
    alignedEntry00 alignedEntry02 alignedEntry04 alignedEntry22
    alignedEntry24 mixedDeterminantOne
  dsimp only
  ring

private theorem oddB11mUpperSlopeD_upper
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    oddB11mSlopeD oddB11mUpperEndpoint D F a x r c d f dv ≤
      (-7 / 1000 : ℝ) := by
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.a_mem with ⟨haL, haU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  have hSD : (266400000 * a - 487719647) / 1600000000 ≤
      (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1600000000)).2
    nlinarith only [haU]
  have hSa : (0 : ℝ) ≤
      -(117000000 * d + 1000000 * dv - 14258061) / 1000000000 := by
    apply div_nonneg
    · nlinarith only [hdU, hdvU]
    · norm_num
  have hSx : (0 : ℝ) ≤
      -13 * (9000000 * r - 6261247) / 1000000000 := by
    apply div_nonneg
    · nlinarith only [hrU]
    · norm_num
  have hSr : -(269075000 * dv - 8541423) / 1000000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1000000000)).2
    nlinarith only [hdvL]
  have hSd : (0 : ℝ) ≤ (172895579 / 800000000 : ℝ) := by norm_num
  have hSdv : (0 : ℝ) ≤ (1311981 / 25000000 : ℝ) := by norm_num
  have htel :
      oddB11mUpperDGeometrySlope D a x r d dv -
          (-14314966101971 / 2000000000000000 : ℝ) =
        (D - 42817 / 1000000) *
          ((266400000 * a - 487719647) / 1600000000) +
        (a - 165293 / 200000) *
          (-(117000000 * d + 1000000 * dv - 14258061) / 1000000000) +
        (x - 39761 / 1000000) *
          (-13 * (9000000 * r - 6261247) / 1000000000) +
        (r - 49817 / 1000000) *
          (-(269075000 * dv - 8541423) / 1000000000) +
        (d - 27183 / 1000000) * (172895579 / 800000000) +
        (dv - 279 / 5000) * (1311981 / 25000000) := by
    unfold oddB11mUpperDGeometrySlope
    ring
  have hPD : (D - 42817 / 1000000) *
      ((266400000 * a - 487719647) / 1600000000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hDL]) hSD
  have hPa : (a - 165293 / 200000) *
      (-(117000000 * d + 1000000 * dv - 14258061) / 1000000000) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [haU]) hSa
  have hPx : (x - 39761 / 1000000) *
      (-13 * (9000000 * r - 6261247) / 1000000000) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hxU]) hSx
  have hPr : (r - 49817 / 1000000) *
      (-(269075000 * dv - 8541423) / 1000000000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hrL]) hSr
  have hPd :
      (d - 27183 / 1000000) * (172895579 / 800000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hdU]) hSd
  have hPdv :
      (dv - 279 / 5000) * (1311981 / 25000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hdvU]) hSdv
  rw [oddB11mUpperSlopeD_eq]
  nlinarith only [htel, hPD, hPa, hPx, hPr, hPd, hPdv]

private def oddB11mUpperFGeometrySlope (a c x dv : ℝ) : ℝ :=
  -(-4680000000000 * a * c - 20000000000000 * a * dv ^ 2 +
      178754400000 * a + 12512635150000 * c +
      27484600000000 * dv ^ 2 + 21526000000000 * dv * x -
      852860120000 * dv + 4680000000000 * x ^ 2 -
      1055476800000 * x - 292788296113) / 80000000000000

set_option maxHeartbeats 3000000 in
private theorem oddB11mUpperSlopeF_eq
    (F a x r c d f dv : ℝ) :
    oddB11mSlopeF oddB11mUpperEndpoint F a x r c d f dv =
      oddB11mUpperFGeometrySlope a c x dv := by
  unfold oddB11mSlopeF oddB11mUpperEndpoint quadraticSecant
    oddB11mCore oddB11m oddGm oddGx oddP11 oddB11mUpperFGeometrySlope
    alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
    alignedEntry00 alignedEntry02 alignedEntry04 alignedEntry22
    alignedEntry24 mixedDeterminantOne
  dsimp only
  ring

private theorem oddB11mUpperSlopeF_lower
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (1 / 1000 : ℝ) ≤
      oddB11mSlopeF oddB11mUpperEndpoint F a x r c d f dv := by
  rcases hbox.a_mem with ⟨haL, haU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  have hdv0 : 0 ≤ dv := by nlinarith only [hdvL]
  have hdvSq : dv * dv ≤ (558 / 10000 : ℝ) * (558 / 10000) :=
    mul_le_mul hdvU hdvU hdv0 (by norm_num)
  have hSa : (5850000 * c + 25000000 * dv ^ 2 - 223443) /
      100000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 100000000)).2
    nlinarith only [hcU, hdvSq]
  have hSc : (-172895579 / 1600000000 : ℝ) ≤ 0 := by norm_num
  have hSx : -(538150000 * dv + 117000000 * x - 21734883) /
      2000000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2000000000)).2
    nlinarith only [hdvL, hxL]
  have hSdv : -(5477650000 * dv + 307170453) / 40000000000 ≤
      (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 40000000000)).2
    nlinarith only [hdvL]
  have htel :
      oddB11mUpperFGeometrySlope a c x dv -
          (8340200450397 / 8000000000000000 : ℝ) =
        (a - 165293 / 200000) *
          ((5850000 * c + 25000000 * dv ^ 2 - 223443) / 100000000) +
        (c - 1433 / 200000) * (-172895579 / 1600000000) +
        (x - 39761 / 1000000) *
          (-(538150000 * dv + 117000000 * x - 21734883) / 2000000000) +
        (dv - 279 / 5000) *
          (-(5477650000 * dv + 307170453) / 40000000000) := by
    unfold oddB11mUpperFGeometrySlope
    ring
  have hPa : (0 : ℝ) ≤ (a - 165293 / 200000) *
      ((5850000 * c + 25000000 * dv ^ 2 - 223443) / 100000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [haU]) hSa
  have hPc : (0 : ℝ) ≤
      (c - 1433 / 200000) * (-172895579 / 1600000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hcU]) hSc
  have hPx : (0 : ℝ) ≤ (x - 39761 / 1000000) *
      (-(538150000 * dv + 117000000 * x - 21734883) / 2000000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hxU]) hSx
  have hPdv : (0 : ℝ) ≤ (dv - 279 / 5000) *
      (-(5477650000 * dv + 307170453) / 40000000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hdvU]) hSdv
  rw [oddB11mUpperSlopeF_eq]
  nlinarith only [htel, hPa, hPc, hPx, hPdv]

private def oddB11mUpperAGeometrySlope (c d f dv : ℝ) : ℝ :=
  (99000000000000 * c * f + 36853000000000 * c -
      99000000000000 * d ^ 2 + 2000000000000 * d * dv -
      10019178000000 * d - 500000000000000 * dv ^ 2 * f +
      157500000000000 * dv ^ 2 - 85634000000 * dv +
      1570140000000 * f - 797176662163) / 2000000000000000

set_option maxHeartbeats 3000000 in
private theorem oddB11mUpperSlopeA_eq
    (a x r c d f dv : ℝ) :
    oddB11mSlopeA oddB11mUpperEndpoint a x r c d f dv =
      oddB11mUpperAGeometrySlope c d f dv := by
  unfold oddB11mSlopeA oddB11mUpperEndpoint quadraticSecant
    oddB11mCore oddB11m oddGm oddGx oddP11 oddB11mUpperAGeometrySlope
    alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
    alignedEntry00 alignedEntry02 alignedEntry04 alignedEntry22
    alignedEntry24 mixedDeterminantOne
  dsimp only
  ring

private theorem oddB11mUpperSlopeA_upper
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    oddB11mSlopeA oddB11mUpperEndpoint a x r c d f dv ≤
      (-1 / 10000 : ℝ) := by
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  have hdv0 : 0 ≤ dv := by nlinarith only [hdvL]
  have hdvSq : dv * dv ≤ (558 / 10000 : ℝ) * (558 / 10000) :=
    mul_le_mul hdvU hdvU hdv0 (by norm_num)
  have hSc : (0 : ℝ) ≤ (99000 * f + 36853) / 2000000 := by
    apply div_nonneg
    · nlinarith only [hfL]
    · norm_num
  have hSd : -(99000000 * d - 2000000 * dv + 12327561) /
      2000000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2000000000)).2
    nlinarith only [hdL, hdvU]
  have hSf : (0 : ℝ) ≤
      -(20000000 * dv ^ 2 - 91179) / 80000000 := by
    apply div_nonneg
    · nlinarith only [hdvSq]
    · norm_num
  have hSdv : (0 : ℝ) ≤
      3 * (5765000 * dv + 318437) / 500000000 := by
    apply div_nonneg
    · nlinarith only [hdvL]
    · norm_num
  have htel :
      oddB11mUpperAGeometrySlope c d f dv -
          (-1023473889 / 10000000000000 : ℝ) =
        (c - 1433 / 200000) * ((99000 * f + 36853) / 2000000) +
        (d - 23317 / 1000000) *
          (-(99000000 * d - 2000000 * dv + 12327561) / 2000000000) +
        (f - 552 / 3125) *
          (-(20000000 * dv ^ 2 - 91179) / 80000000) +
        (dv - 279 / 5000) *
          (3 * (5765000 * dv + 318437) / 500000000) := by
    unfold oddB11mUpperAGeometrySlope
    ring
  have hPc :
      (c - 1433 / 200000) * ((99000 * f + 36853) / 2000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hcU]) hSc
  have hPd : (d - 23317 / 1000000) *
      (-(99000000 * d - 2000000 * dv + 12327561) / 2000000000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hdL]) hSd
  have hPf : (f - 552 / 3125) *
      (-(20000000 * dv ^ 2 - 91179) / 80000000) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hfU]) hSf
  have hPdv : (dv - 279 / 5000) *
      (3 * (5765000 * dv + 318437) / 500000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hdvU]) hSdv
  rw [oddB11mUpperSlopeA_eq]
  nlinarith only [htel, hPc, hPd, hPf, hPdv]

private def oddB11mUpperLittleXGeometrySlope
    (x r d f dv : ℝ) : ℝ :=
  -(99000000000000 * d * r + 28947739000000 * d -
      269075000000000 * dv * f - 1000000000000 * dv * r +
      85001442000000 * dv + 49500000000000 * f * x +
      6603709500000 * f + 5009589000000 * r + 18426500000000 * x -
      6908346159887) / 1000000000000000

set_option maxHeartbeats 3000000 in
private theorem oddB11mUpperSlopeLittleX_eq
    (x r c d f dv : ℝ) :
    oddB11mSlopeLittleX oddB11mUpperEndpoint x r c d f dv =
      oddB11mUpperLittleXGeometrySlope x r d f dv := by
  unfold oddB11mSlopeLittleX oddB11mUpperEndpoint quadraticSecant
    oddB11mCore oddB11m oddGm oddGx oddP11 oddB11mUpperLittleXGeometrySlope
    alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
    alignedEntry00 alignedEntry02 alignedEntry04 alignedEntry22
    alignedEntry24 mixedDeterminantOne
  dsimp only
  ring

private theorem oddB11mUpperSlopeLittleX_lower
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (13 / 10000 : ℝ) ≤
      oddB11mSlopeLittleX oddB11mUpperEndpoint x r c d f dv := by
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  have hSx : -(99000 * f + 36853) / 2000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2000000)).2
    nlinarith only [hfL]
  have hSr : -(99000000 * d - 1000000 * dv + 5009589) /
      1000000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1000000000)).2
    nlinarith only [hdL, hdvU]
  have hSd : (-4326107 / 125000000 : ℝ) ≤ 0 := by norm_num
  have hSf : (0 : ℝ) ≤
      (269075000 * dv - 8571879) / 1000000000 := by
    apply div_nonneg
    · nlinarith only [hdvL]
    · norm_num
  have hSdv : (-18734333 / 500000000 : ℝ) ≤ 0 := by norm_num
  have htel :
      oddB11mUpperLittleXGeometrySlope x r d f dv -
          (21020005303 / 15625000000000 : ℝ) =
        (x - 39761 / 1000000) * (-(99000 * f + 36853) / 2000000) +
        (r - 57183 / 1000000) *
          (-(99000000 * d - 1000000 * dv + 5009589) / 1000000000) +
        (d - 27183 / 1000000) * (-4326107 / 125000000) +
        (f - 4411 / 25000) *
          ((269075000 * dv - 8571879) / 1000000000) +
        (dv - 279 / 5000) * (-18734333 / 500000000) := by
    unfold oddB11mUpperLittleXGeometrySlope
    ring
  have hPx : (0 : ℝ) ≤ (x - 39761 / 1000000) *
      (-(99000 * f + 36853) / 2000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hxU]) hSx
  have hPr : (0 : ℝ) ≤ (r - 57183 / 1000000) *
      (-(99000000 * d - 1000000 * dv + 5009589) / 1000000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hrU]) hSr
  have hPd : (0 : ℝ) ≤
      (d - 27183 / 1000000) * (-4326107 / 125000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hdU]) hSd
  have hPf : (0 : ℝ) ≤ (f - 4411 / 25000) *
      ((269075000 * dv - 8571879) / 1000000000) :=
    mul_nonneg (by nlinarith only [hfL]) hSf
  have hPdv : (0 : ℝ) ≤
      (dv - 279 / 5000) * (-18734333 / 500000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hdvU]) hSdv
  rw [oddB11mUpperSlopeLittleX_eq]
  nlinarith only [htel, hPx, hPr, hPd, hPf, hPdv]

private def oddB11mUpperLittleRGeometrySlope
    (r c d dv : ℝ) : ℝ :=
  -(49500000000000 * c * r + 31778297500000 * c -
      269075000000000 * d * dv + 8571879000000 * d -
      250000000000000 * dv ^ 2 * r + 107112750000000 * dv ^ 2 +
      11520843275000 * dv + 785070000000 * r - 1413162602401) /
    1000000000000000

set_option maxHeartbeats 3000000 in
private theorem oddB11mUpperSlopeLittleR_eq
    (r c d f dv : ℝ) :
    oddB11mSlopeLittleR oddB11mUpperEndpoint r c d f dv =
      oddB11mUpperLittleRGeometrySlope r c d dv := by
  unfold oddB11mSlopeLittleR oddB11mUpperEndpoint quadraticSecant
    oddB11mCore oddB11m oddGm oddGx oddP11 oddB11mUpperLittleRGeometrySlope
    alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
    alignedEntry00 alignedEntry02 alignedEntry04 alignedEntry22
    alignedEntry24 mixedDeterminantOne
  dsimp only
  ring

private theorem oddB11mUpperSlopeLittleR_lower
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (33 / 100000 : ℝ) ≤
      oddB11mSlopeLittleR oddB11mUpperEndpoint r c d f dv := by
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  have hdv0 : 0 ≤ dv := by nlinarith only [hdvL]
  have hdvSq : dv * dv ≤ (558 / 10000 : ℝ) * (558 / 10000) :=
    mul_le_mul hdvU hdvU hdv0 (by norm_num)
  have hSr : -(4950000 * c - 25000000 * dv ^ 2 + 78507) /
      100000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 100000000)).2
    nlinarith only [hcL, hdvSq]
  have hSc : (-4326107 / 125000000 : ℝ) ≤ 0 := by norm_num
  have hSd : (0 : ℝ) ≤
      (269075000 * dv - 8571879) / 1000000000 := by
    apply div_nonneg
    · nlinarith only [hdvL]
    · norm_num
  have hSdv : -3 * (309390000 * dv + 34753367) / 10000000000 ≤
      (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 10000000000)).2
    nlinarith only [hdvL]
  have htel :
      oddB11mUpperLittleRGeometrySlope r c d dv -
          (42331953141 / 125000000000000 : ℝ) =
        (r - 57183 / 1000000) *
          (-(4950000 * c - 25000000 * dv ^ 2 + 78507) / 100000000) +
        (c - 1433 / 200000) * (-4326107 / 125000000) +
        (d - 23317 / 1000000) *
          ((269075000 * dv - 8571879) / 1000000000) +
        (dv - 279 / 5000) *
          (-3 * (309390000 * dv + 34753367) / 10000000000) := by
    unfold oddB11mUpperLittleRGeometrySlope
    ring
  have hPr : (0 : ℝ) ≤ (r - 57183 / 1000000) *
      (-(4950000 * c - 25000000 * dv ^ 2 + 78507) / 100000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hrU]) hSr
  have hPc : (0 : ℝ) ≤
      (c - 1433 / 200000) * (-4326107 / 125000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hcU]) hSc
  have hPd : (0 : ℝ) ≤ (d - 23317 / 1000000) *
      ((269075000 * dv - 8571879) / 1000000000) :=
    mul_nonneg (by nlinarith only [hdL]) hSd
  have hPdv : (0 : ℝ) ≤ (dv - 279 / 5000) *
      (-3 * (309390000 * dv + 34753367) / 10000000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hdvU]) hSdv
  rw [oddB11mUpperSlopeLittleR_eq]
  nlinarith only [htel, hPr, hPc, hPd, hPdv]

private def oddB11mUpperLittleCGeometrySlope (f : ℝ) : ℝ :=
  (48802809875000 * f - 25944514898099) / 1000000000000000

set_option maxHeartbeats 3000000 in
private theorem oddB11mUpperSlopeLittleC_eq
    (c d f dv : ℝ) :
    oddB11mSlopeLittleC oddB11mUpperEndpoint c d f dv =
      oddB11mUpperLittleCGeometrySlope f := by
  unfold oddB11mSlopeLittleC oddB11mUpperEndpoint quadraticSecant
    oddB11mCore oddB11m oddGm oddGx oddP11 oddB11mUpperLittleCGeometrySlope
    alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
    alignedEntry00 alignedEntry02 alignedEntry04 alignedEntry22
    alignedEntry24 mixedDeterminantOne
  dsimp only
  ring

private theorem oddB11mUpperSlopeLittleC_upper
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    oddB11mSlopeLittleC oddB11mUpperEndpoint c d f dv ≤
      (-17 / 1000 : ℝ) := by
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  have hSlope : (0 : ℝ) ≤ (390422479 / 8000000000 : ℝ) := by norm_num
  have htel :
      oddB11mUpperLittleCGeometrySlope f -
          (-17323986561779 / 1000000000000000 : ℝ) =
        (f - 552 / 3125) * (390422479 / 8000000000) := by
    unfold oddB11mUpperLittleCGeometrySlope
    ring
  have hstep :
      (f - 552 / 3125) * (390422479 / 8000000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hfU]) hSlope
  rw [oddB11mUpperSlopeLittleC_eq]
  nlinarith only [htel, hstep]

private def oddB11mUpperLittleDGeometrySlope (d dv : ℝ) : ℝ :=
  -(390422479000000 * d + 403993756400000 * dv - 76165526744477) /
    8000000000000000

set_option maxHeartbeats 3000000 in
private theorem oddB11mUpperSlopeLittleD_eq
    (d f dv : ℝ) :
    oddB11mSlopeLittleD oddB11mUpperEndpoint d f dv =
      oddB11mUpperLittleDGeometrySlope d dv := by
  unfold oddB11mSlopeLittleD oddB11mUpperEndpoint quadraticSecant
    oddB11mCore oddB11m oddGm oddGx oddP11 oddB11mUpperLittleDGeometrySlope
    alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
    alignedEntry00 alignedEntry02 alignedEntry04 alignedEntry22
    alignedEntry24 mixedDeterminantOne
  dsimp only
  ring

private theorem oddB11mUpperSlopeLittleD_lower
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (53 / 10000 : ℝ) ≤
      oddB11mSlopeLittleD oddB11mUpperEndpoint d f dv := by
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  have hSd : (-390422479 / 8000000000 : ℝ) ≤ 0 := by norm_num
  have hSdv : (-1009984391 / 20000000000 : ℝ) ≤ 0 := by norm_num
  have htel :
      oddB11mUpperLittleDGeometrySlope d dv -
          (430098208907 / 80000000000000 : ℝ) =
        (d - 27183 / 1000000) * (-390422479 / 8000000000) +
        (dv - 279 / 5000) * (-1009984391 / 20000000000) := by
    unfold oddB11mUpperLittleDGeometrySlope
    ring
  have hPd : (0 : ℝ) ≤
      (d - 27183 / 1000000) * (-390422479 / 8000000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hdU]) hSd
  have hPdv : (0 : ℝ) ≤
      (dv - 279 / 5000) * (-1009984391 / 20000000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hdvU]) hSdv
  rw [oddB11mUpperSlopeLittleD_eq]
  nlinarith only [htel, hPd, hPdv]

private def oddB11mUpperLittleFGeometrySlope (dv : ℝ) : ℝ :=
  (219900400000000 * dv ^ 2 + 60703320000 * dv - 1920285946191) /
    1600000000000000

set_option maxHeartbeats 3000000 in
private theorem oddB11mUpperSlopeLittleF_eq
    (f dv : ℝ) :
    oddB11mSlopeLittleF oddB11mUpperEndpoint f dv =
      oddB11mUpperLittleFGeometrySlope dv := by
  unfold oddB11mSlopeLittleF oddB11mUpperEndpoint quadraticSecant
    oddB11mCore oddB11m oddGm oddGx oddP11 oddB11mUpperLittleFGeometrySlope
    alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
    alignedEntry00 alignedEntry02 alignedEntry04 alignedEntry22
    alignedEntry24 mixedDeterminantOne
  dsimp only
  ring

private theorem oddB11mUpperSlopeLittleF_upper
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    oddB11mSlopeLittleF oddB11mUpperEndpoint f dv ≤
      (-3 / 4000 : ℝ) := by
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  have hSlope : (0 : ℝ) ≤
      (5497510000 * dv + 308278641) / 40000000000 := by
    apply div_nonneg
    · nlinarith only [hdvL]
    · norm_num
  have htel :
      oddB11mUpperLittleFGeometrySlope dv -
          (-1232208019479 / 1600000000000000 : ℝ) =
        (dv - 279 / 5000) *
          ((5497510000 * dv + 308278641) / 40000000000) := by
    unfold oddB11mUpperLittleFGeometrySlope
    ring
  have hstep : (dv - 279 / 5000) *
      ((5497510000 * dv + 308278641) / 40000000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hdvU]) hSlope
  rw [oddB11mUpperSlopeLittleF_eq]
  nlinarith only [htel, hstep]

private def oddB11mUpperDvGeometrySlope (dv : ℝ) : ℝ :=
  -(52141895755000 * dv - 1027233368291) / 5000000000000000

set_option maxHeartbeats 3000000 in
private theorem oddB11mUpperSlopeDv_eq (dv : ℝ) :
    oddB11mSlopeDv oddB11mUpperEndpoint dv =
      oddB11mUpperDvGeometrySlope dv := by
  unfold oddB11mSlopeDv oddB11mUpperEndpoint quadraticSecant
    oddB11mCore oddB11m oddGm oddGx oddP11 oddB11mUpperDvGeometrySlope
    alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
    alignedEntry00 alignedEntry02 alignedEntry04 alignedEntry22
    alignedEntry24 mixedDeterminantOne
  dsimp only
  ring

private theorem oddB11mUpperSlopeDv_upper
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    oddB11mSlopeDv oddB11mUpperEndpoint dv ≤
      (-37 / 100000 : ℝ) := by
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  have hSlope : (-10428379151 / 1000000000000 : ℝ) ≤ 0 := by norm_num
  have htel :
      oddB11mUpperDvGeometrySlope dv -
          (-3733283692223 / 10000000000000000 : ℝ) =
        (dv - 111 / 2000) * (-10428379151 / 1000000000000) := by
    unfold oddB11mUpperDvGeometrySlope
    ring
  have hstep :
      (dv - 111 / 2000) * (-10428379151 / 1000000000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hdvL]) hSlope
  rw [oddB11mUpperSlopeDv_eq]
  nlinarith only [htel, hstep]

private theorem oddB11mUpperEndpointValue_exact :
    oddB11mEndpointValue oddB11mUpperEndpoint =
      (39575399918544649 / 400000000000000000000 : ℝ) := by
  norm_num [oddB11mEndpointValue, oddB11mUpperEndpoint, oddB11mCore,
    oddB11m, oddGm, oddGx, oddP11, alignedDeterminant,
    alignedMixedDeterminant, alignedAdjugatePair, alignedEntry00,
    alignedEntry02, alignedEntry04, alignedEntry22, alignedEntry24,
    mixedDeterminantOne]

private theorem oddB11mUpperEndpointValue_upper :
    oddB11mEndpointValue oddB11mUpperEndpoint ≤ (100 / 1000000 : ℝ) := by
  rw [oddB11mUpperEndpointValue_exact]
  norm_num

private theorem oddB11m_upper_bound
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    oddB11mCore X R C D F a x r c d f sv dv v4 q33 h33 ≤
      (100 / 1000000 : ℝ) := by
  rcases hbox.X_mem with ⟨hXL, hXU⟩
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.C_mem with ⟨hCL, hCU⟩
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.F_mem with ⟨hFL, hFU⟩
  rcases hbox.a_mem with ⟨haL, haU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  rcases hbox.sv_mem with ⟨hsvL, hsvU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  rcases hbox.v4_mem with ⟨hv4L, hv4U⟩
  rcases hbox.q33_mem with ⟨hq33L, hq33U⟩
  rcases hbox.h33_mem with ⟨hh33L, hh33U⟩
  have hsQ33 := oddB11mUpperSlopeQ33_lower
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hsH33 := oddB11mUpperSlopeH33_lower
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hsSv := oddB11mUpperSlopeSv_upper
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hsV4 := oddB11mUpperSlopeV4_lower
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hsX := oddB11mUpperSlopeX_upper
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hsR := oddB11mUpperSlopeR_upper
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hsC := oddB11mUpperSlopeC_lower
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hsD := oddB11mUpperSlopeD_upper
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hsF := oddB11mUpperSlopeF_lower
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hsA := oddB11mUpperSlopeA_upper
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hsx := oddB11mUpperSlopeLittleX_lower
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hsr := oddB11mUpperSlopeLittleR_lower
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hsc := oddB11mUpperSlopeLittleC_upper
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hsd := oddB11mUpperSlopeLittleD_lower
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hsf := oddB11mUpperSlopeLittleF_upper
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hsDv := oddB11mUpperSlopeDv_upper
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hq33Step :
      (q33 - oddB11mUpperEndpoint.q33Value) *
          oddB11mSlopeQ33 oddB11mUpperEndpoint
            X R C D F a x r c d f sv dv v4 q33 h33 ≤ (0 : ℝ) := by
    apply mul_nonpos_of_nonpos_of_nonneg
    · dsimp [oddB11mUpperEndpoint]
      nlinarith only [hq33U]
    · nlinarith only [hsQ33]
  have hh33Step :
      (h33 - oddB11mUpperEndpoint.h33Value) *
          oddB11mSlopeH33 oddB11mUpperEndpoint
            X R C D F a x r c d f sv dv v4 h33 ≤ (0 : ℝ) := by
    apply mul_nonpos_of_nonpos_of_nonneg
    · dsimp [oddB11mUpperEndpoint]
      nlinarith only [hh33U]
    · nlinarith only [hsH33]
  have hsvStep :
      (sv - oddB11mUpperEndpoint.svValue) *
          oddB11mSlopeSv oddB11mUpperEndpoint
            X R C D F a x r c d f sv dv v4 ≤ (0 : ℝ) := by
    apply mul_nonpos_of_nonneg_of_nonpos
    · dsimp [oddB11mUpperEndpoint]
      nlinarith only [hsvL]
    · nlinarith only [hsSv]
  have hv4Step :
      (v4 - oddB11mUpperEndpoint.v4Value) *
          oddB11mSlopeV4 oddB11mUpperEndpoint
            X R C D F a x r c d f dv v4 ≤ (0 : ℝ) := by
    apply mul_nonpos_of_nonpos_of_nonneg
    · dsimp [oddB11mUpperEndpoint]
      nlinarith only [hv4U]
    · nlinarith only [hsV4]
  have hXStep :
      (X - oddB11mUpperEndpoint.bigX) *
          oddB11mSlopeX oddB11mUpperEndpoint
            X R C D F a x r c d f dv ≤ (0 : ℝ) := by
    apply mul_nonpos_of_nonneg_of_nonpos
    · dsimp [oddB11mUpperEndpoint]
      nlinarith only [hXL]
    · nlinarith only [hsX]
  have hRStep :
      (R - oddB11mUpperEndpoint.bigR) *
          oddB11mSlopeR oddB11mUpperEndpoint
            R C D F a x r c d f dv ≤ (0 : ℝ) := by
    apply mul_nonpos_of_nonneg_of_nonpos
    · dsimp [oddB11mUpperEndpoint]
      nlinarith only [hRL]
    · nlinarith only [hsR]
  have hCStep :
      (C - oddB11mUpperEndpoint.bigC) *
          oddB11mSlopeC oddB11mUpperEndpoint
            C D F a x r c d f dv ≤ (0 : ℝ) := by
    apply mul_nonpos_of_nonpos_of_nonneg
    · dsimp [oddB11mUpperEndpoint]
      nlinarith only [hCU]
    · nlinarith only [hsC]
  have hDStep :
      (D - oddB11mUpperEndpoint.bigD) *
          oddB11mSlopeD oddB11mUpperEndpoint
            D F a x r c d f dv ≤ (0 : ℝ) := by
    apply mul_nonpos_of_nonneg_of_nonpos
    · dsimp [oddB11mUpperEndpoint]
      nlinarith only [hDL]
    · nlinarith only [hsD]
  have hFStep :
      (F - oddB11mUpperEndpoint.bigF) *
          oddB11mSlopeF oddB11mUpperEndpoint
            F a x r c d f dv ≤ (0 : ℝ) := by
    apply mul_nonpos_of_nonpos_of_nonneg
    · dsimp [oddB11mUpperEndpoint]
      nlinarith only [hFU]
    · nlinarith only [hsF]
  have haStep :
      (a - oddB11mUpperEndpoint.littleA) *
          oddB11mSlopeA oddB11mUpperEndpoint
            a x r c d f dv ≤ (0 : ℝ) := by
    apply mul_nonpos_of_nonneg_of_nonpos
    · dsimp [oddB11mUpperEndpoint]
      nlinarith only [haL]
    · nlinarith only [hsA]
  have hxStep :
      (x - oddB11mUpperEndpoint.littleX) *
          oddB11mSlopeLittleX oddB11mUpperEndpoint
            x r c d f dv ≤ (0 : ℝ) := by
    apply mul_nonpos_of_nonpos_of_nonneg
    · dsimp [oddB11mUpperEndpoint]
      nlinarith only [hxU]
    · nlinarith only [hsx]
  have hrStep :
      (r - oddB11mUpperEndpoint.littleR) *
          oddB11mSlopeLittleR oddB11mUpperEndpoint
            r c d f dv ≤ (0 : ℝ) := by
    apply mul_nonpos_of_nonpos_of_nonneg
    · dsimp [oddB11mUpperEndpoint]
      nlinarith only [hrU]
    · nlinarith only [hsr]
  have hcStep :
      (c - oddB11mUpperEndpoint.littleC) *
          oddB11mSlopeLittleC oddB11mUpperEndpoint
            c d f dv ≤ (0 : ℝ) := by
    apply mul_nonpos_of_nonneg_of_nonpos
    · dsimp [oddB11mUpperEndpoint]
      nlinarith only [hcL]
    · nlinarith only [hsc]
  have hdStep :
      (d - oddB11mUpperEndpoint.littleD) *
          oddB11mSlopeLittleD oddB11mUpperEndpoint
            d f dv ≤ (0 : ℝ) := by
    apply mul_nonpos_of_nonpos_of_nonneg
    · dsimp [oddB11mUpperEndpoint]
      nlinarith only [hdU]
    · nlinarith only [hsd]
  have hfStep :
      (f - oddB11mUpperEndpoint.littleF) *
          oddB11mSlopeLittleF oddB11mUpperEndpoint
            f dv ≤ (0 : ℝ) := by
    apply mul_nonpos_of_nonneg_of_nonpos
    · dsimp [oddB11mUpperEndpoint]
      nlinarith only [hfL]
    · nlinarith only [hsf]
  have hdvStep :
      (dv - oddB11mUpperEndpoint.dvValue) *
          oddB11mSlopeDv oddB11mUpperEndpoint dv ≤ (0 : ℝ) := by
    apply mul_nonpos_of_nonneg_of_nonpos
    · dsimp [oddB11mUpperEndpoint]
      nlinarith only [hdvL]
    · nlinarith only [hsDv]
  have htel := oddB11m_upper_telescope
    X R C D F a x r c d f sv dv v4 q33 h33
  have hend := oddB11mUpperEndpointValue_upper
  nlinarith only [htel, hend, hq33Step, hh33Step, hsvStep, hv4Step,
    hXStep, hRStep, hCStep, hDStep, hFStep, haStep, hxStep, hrStep,
    hcStep, hdStep, hfStep, hdvStep]


private def oddB11pLowerQ33GeometrySlope (X R C D F a x r c d f : ℝ) : ℝ :=
  (412269 * C * F - 300000 * C * R ^ 2 - 100000 * C * a * f +
      100000 * C * r ^ 2 - 412269 * D ^ 2 - 600000 * D * R * X +
      200000 * D * a * d + 200000 * D * r * x - 300000 * F * X ^ 2 -
      100000 * F * a * c + 100000 * F * x ^ 2 + 200000 * R * c * r +
      200000 * R * d * x + 200000 * X * d * r + 200000 * X * f * x -
      137423 * c * f + 137423 * d ^ 2) / 200000

private theorem oddB11pLowerQ33Geometry_lower_raw
    (X R C D F a x r c d f : ℝ)
    (hXL : (1981 / 50000 : ℝ) ≤ X) (hXU : X ≤ 3977 / 100000)
    (hRL : (242817 / 1000000 : ℝ) ≤ R) (hRU : R ≤ 121449 / 500000)
    (hCL : (1323 / 100000 : ℝ) ≤ C)
    (hDL : (42817 / 1000000 : ℝ) ≤ D) (hDU : D ≤ 21449 / 500000)
    (hFL : (1571 / 5000 : ℝ) ≤ F)
    (haL : (824479 / 1000000 : ℝ) ≤ a) (haU : a ≤ 165293 / 200000)
    (hxL : (37851 / 1000000 : ℝ) ≤ x) (hxU : x ≤ 39761 / 1000000)
    (hrL : (49817 / 1000000 : ℝ) ≤ r) (hrU : r ≤ 57183 / 1000000)
    (hcL : (5179 / 1000000 : ℝ) ≤ c) (hcU : c ≤ 1433 / 200000)
    (hdL : (23317 / 1000000 : ℝ) ≤ d) (hdU : d ≤ 27183 / 1000000)
    (hfL : (4411 / 25000 : ℝ) ≤ f) (hfU : f ≤ 552 / 3125) :
    (9 / 10000 : ℝ) ≤ oddB11pLowerQ33GeometrySlope X R C D F a x r c d f := by
  have hX0 : 0 ≤ X := by nlinarith only [hXL]
  have hR0 : 0 ≤ R := by nlinarith only [hRL]
  have hC0 : 0 ≤ C := by nlinarith only [hCL]
  have hD0 : 0 ≤ D := by nlinarith only [hDL]
  have hF0 : 0 ≤ F := by nlinarith only [hFL]
  have ha0 : 0 ≤ a := by nlinarith only [haL]
  have hx0 : 0 ≤ x := by nlinarith only [hxL]
  have hr0 : 0 ≤ r := by nlinarith only [hrL]
  have hc0 : 0 ≤ c := by nlinarith only [hcL]
  have hd0 : 0 ≤ d := by nlinarith only [hdL]
  have hf0 : 0 ≤ f := by nlinarith only [hfL]
  have hDRL : (42817 / 1000000 : ℝ) * (242817 / 1000000) ≤ D * R :=
    mul_le_mul hDL hRL (by norm_num) hD0
  have hFXL : (1571 / 5000 : ℝ) * (1981 / 50000) ≤ F * X :=
    mul_le_mul hFL hXL (by norm_num) hF0
  have hdrU : d * r ≤ (27183 / 1000000 : ℝ) * (57183 / 1000000) :=
    mul_le_mul hdU hrU hr0 (by norm_num)
  have hfxU : f * x ≤ (552 / 3125 : ℝ) * (39761 / 1000000) :=
    mul_le_mul hfU hxU hx0 (by norm_num)
  have sX :
      (-600000 * D * R - 300000 * F * X - 11931 * F +
          200000 * d * r + 200000 * f * x) / 200000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 200000)).2
    nlinarith only [hDRL, hFXL, hdrU, hfxU, hFL]
  have hCRL : (1323 / 100000 : ℝ) * (242817 / 1000000) ≤ C * R :=
    mul_le_mul hCL hRL (by norm_num) hC0
  have hcrU : c * r ≤ (1433 / 200000 : ℝ) * (57183 / 1000000) :=
    mul_le_mul hcU hrU hr0 (by norm_num)
  have hdxU : d * x ≤ (27183 / 1000000 : ℝ) * (39761 / 1000000) :=
    mul_le_mul hdU hxU hx0 (by norm_num)
  have sR :
      (-1500000 * C * R - 364347 * C - 119310 * D +
          1000000 * c * r + 1000000 * d * x) / 1000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1000000)).2
    nlinarith only [hCRL, hCL, hDL, hcrU, hdxU]
  have hafU : a * f ≤ (165293 / 200000 : ℝ) * (552 / 3125) :=
    mul_le_mul haU hfU hf0 (by norm_num)
  have sC : (0 : ℝ) ≤
      (1030672500000 * F - 250000000000 * a * f +
          250000000000 * r ^ 2 - 44249578803) / 500000000000 := by
    apply div_nonneg
    · nlinarith only [hFL, hafU, sq_nonneg r]
    · norm_num
  have hadU : a * d ≤ (165293 / 200000 : ℝ) * (27183 / 1000000) :=
    mul_le_mul haU hdU hd0 (by norm_num)
  have hrxU : r * x ≤ (57183 / 1000000 : ℝ) * (39761 / 1000000) :=
    mul_le_mul hrU hxU hx0 (by norm_num)
  have sD :
      (-206134500000 * D + 100000000000 * a * d +
          100000000000 * r * x - 11740773819) / 100000000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 100000000000)).2
    nlinarith only [hDL, hadU, hrxU]
  have hacU : a * c ≤ (165293 / 200000 : ℝ) * (1433 / 200000) :=
    mul_le_mul haU hcU hc0 (by norm_num)
  have sF : (0 : ℝ) ≤
      (-100000000 * a * c + 100000000 * x ^ 2 + 4979823) / 200000000 := by
    apply div_nonneg
    · nlinarith only [hacU, sq_nonneg x]
    · norm_num
  have sa : -(157100 * c - 42898 * d + 6615 * f) / 1000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1000000)).2
    nlinarith only [hcL, hdU, hfL]
  have sx : (0 : ℝ) ≤
      (2428980000 * d + 397700000 * f + 428980000 * r +
          1571000000 * x + 59463921) / 10000000000 := by
    apply div_nonneg <;> nlinarith only [hdL, hfL, hrL, hxL]
  have sr : (0 : ℝ) ≤
      (242898000000 * c + 39770000000 * d + 6615000000 * r +
          1953271653) / 1000000000000 := by
    apply div_nonneg <;> nlinarith only [hcL, hdL, hrL]
  have sc : -(343557500000 * f + 58868600917) / 500000000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 500000000000)).2
    nlinarith only [hfL]
  have sd : (0 : ℝ) ≤ (687115000000 * d + 62650310313) / 1000000000000 := by
    apply div_nonneg <;> nlinarith only [hdL]
  have sf : (-222122767 / 25000000000 : ℝ) ≤ 0 := by norm_num
  have tel :
      oddB11pLowerQ33GeometrySlope X R C D F a x r c d f -
          (246520889556253 / 250000000000000000 : ℝ) =
        (X - 3977 / 100000) *
          ((-600000 * D * R - 300000 * F * X - 11931 * F +
              200000 * d * r + 200000 * f * x) / 200000) +
        (R - 121449 / 500000) *
          ((-1500000 * C * R - 364347 * C - 119310 * D +
              1000000 * c * r + 1000000 * d * x) / 1000000) +
        (C - 1323 / 100000) *
          ((1030672500000 * F - 250000000000 * a * f +
              250000000000 * r ^ 2 - 44249578803) / 500000000000) +
        (D - 21449 / 500000) *
          ((-206134500000 * D + 100000000000 * a * d +
              100000000000 * r * x - 11740773819) / 100000000000) +
        (F - 1571 / 5000) *
          ((-100000000 * a * c + 100000000 * x ^ 2 + 4979823) / 200000000) +
        (a - 165293 / 200000) * (-(157100 * c - 42898 * d + 6615 * f) / 1000000) +
        (x - 37851 / 1000000) *
          ((2428980000 * d + 397700000 * f + 428980000 * r +
              1571000000 * x + 59463921) / 10000000000) +
        (r - 49817 / 1000000) *
          ((242898000000 * c + 39770000000 * d + 6615000000 * r +
              1953271653) / 1000000000000) +
        (c - 1433 / 200000) * (-(343557500000 * f + 58868600917) / 500000000000) +
        (d - 23317 / 1000000) * ((687115000000 * d + 62650310313) / 1000000000000) +
        (f - 552 / 3125) * (-222122767 / 25000000000) := by
    unfold oddB11pLowerQ33GeometrySlope
    ring
  have pX : (0 : ℝ) ≤ (X - 3977 / 100000) *
      ((-600000 * D * R - 300000 * F * X - 11931 * F +
          200000 * d * r + 200000 * f * x) / 200000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hXU]) sX
  have pR : (0 : ℝ) ≤ (R - 121449 / 500000) *
      ((-1500000 * C * R - 364347 * C - 119310 * D +
          1000000 * c * r + 1000000 * d * x) / 1000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hRU]) sR
  have pC : (0 : ℝ) ≤ (C - 1323 / 100000) *
      ((1030672500000 * F - 250000000000 * a * f +
          250000000000 * r ^ 2 - 44249578803) / 500000000000) :=
    mul_nonneg (by nlinarith only [hCL]) sC
  have pD : (0 : ℝ) ≤ (D - 21449 / 500000) *
      ((-206134500000 * D + 100000000000 * a * d +
          100000000000 * r * x - 11740773819) / 100000000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hDU]) sD
  have pF : (0 : ℝ) ≤ (F - 1571 / 5000) *
      ((-100000000 * a * c + 100000000 * x ^ 2 + 4979823) / 200000000) :=
    mul_nonneg (by nlinarith only [hFL]) sF
  have pa : (0 : ℝ) ≤ (a - 165293 / 200000) *
      (-(157100 * c - 42898 * d + 6615 * f) / 1000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [haU]) sa
  have px : (0 : ℝ) ≤ (x - 37851 / 1000000) *
      ((2428980000 * d + 397700000 * f + 428980000 * r +
          1571000000 * x + 59463921) / 10000000000) :=
    mul_nonneg (by nlinarith only [hxL]) sx
  have pr : (0 : ℝ) ≤ (r - 49817 / 1000000) *
      ((242898000000 * c + 39770000000 * d + 6615000000 * r +
          1953271653) / 1000000000000) :=
    mul_nonneg (by nlinarith only [hrL]) sr
  have pc : (0 : ℝ) ≤ (c - 1433 / 200000) *
      (-(343557500000 * f + 58868600917) / 500000000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hcU]) sc
  have pd : (0 : ℝ) ≤ (d - 23317 / 1000000) *
      ((687115000000 * d + 62650310313) / 1000000000000) :=
    mul_nonneg (by nlinarith only [hdL]) sd
  have pf : (0 : ℝ) ≤ (f - 552 / 3125) * (-222122767 / 25000000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hfU]) sf
  nlinarith only [tel, pX, pR, pC, pD, pF, pa, px, pr, pc, pd, pf]

private def oddB11pLowerH33GeometrySlope (X R C D F a x r c d f : ℝ) : ℝ :=
  (100000 * C * F * a - 200000 * C * R * r + 137423 * C * f -
      100000 * D ^ 2 * a - 200000 * D * R * x - 200000 * D * X * r -
      274846 * D * d - 200000 * F * X * x + 137423 * F * c -
      100000 * R ^ 2 * c - 200000 * R * X * d - 100000 * X ^ 2 * f -
      300000 * a * c * f + 300000 * a * d ^ 2 + 300000 * c * r ^ 2 +
      600000 * d * r * x + 300000 * f * x ^ 2) / 200000

private theorem oddB11pLowerH33Geometry_lower_raw
    (X R C D F a x r c d f : ℝ)
    (hXL : (1981 / 50000 : ℝ) ≤ X) (hXU : X ≤ 3977 / 100000)
    (hRL : (242817 / 1000000 : ℝ) ≤ R) (hRU : R ≤ 121449 / 500000)
    (hCL : (1323 / 100000 : ℝ) ≤ C)
    (hDL : (42817 / 1000000 : ℝ) ≤ D) (hDU : D ≤ 21449 / 500000)
    (hFL : (1571 / 5000 : ℝ) ≤ F)
    (haL : (824479 / 1000000 : ℝ) ≤ a) (haU : a ≤ 165293 / 200000)
    (hxL : (37851 / 1000000 : ℝ) ≤ x) (hXsmallU : x ≤ 39761 / 1000000)
    (hrL : (49817 / 1000000 : ℝ) ≤ r) (hrU : r ≤ 57183 / 1000000)
    (hcL : (5179 / 1000000 : ℝ) ≤ c) (hcU : c ≤ 1433 / 200000)
    (hdL : (23317 / 1000000 : ℝ) ≤ d) (hdU : d ≤ 27183 / 1000000)
    (hfL : (4411 / 25000 : ℝ) ≤ f) (hfU : f ≤ 552 / 3125) :
    (3 / 5000 : ℝ) ≤ oddB11pLowerH33GeometrySlope X R C D F a x r c d f := by
  have hF0 : 0 ≤ F := by nlinarith only [hFL]
  have ha0 : 0 ≤ a := by nlinarith only [haL]
  have hf0 : 0 ≤ f := by nlinarith only [hfL]
  have hc0 : 0 ≤ c := by nlinarith only [hcL]
  have hd0 : 0 ≤ d := by nlinarith only [hdL]
  have hr0 : 0 ≤ r := by nlinarith only [hrL]
  have hx0 : 0 ≤ x := by nlinarith only [hxL]
  have sX : -(200000 * D * r + 200000 * F * x + 200000 * R * d +
      100000 * X * f + 3977 * f) / 200000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 200000)).2
    nlinarith only [hDL, hrL, hFL, hxL, hRL, hdL, hXL, hfL]
  have sR : -(1000000 * C * r + 1000000 * D * x + 500000 * R * c +
      121449 * c + 39770 * d) / 1000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1000000)).2
    nlinarith only [hCL, hrL, hDL, hxL, hRL, hcL, hdL]
  have hFaL : (1571 / 5000 : ℝ) * (824479 / 1000000) ≤ F * a :=
    mul_le_mul hFL haL (by norm_num) hF0
  have sC : (0 : ℝ) ≤ -(-500000 * F * a - 687115 * f + 242898 * r) / 1000000 := by
    apply div_nonneg
    · nlinarith only [hFaL, hfL, hrU]
    · norm_num
  have sD : -(500000 * D * a + 21449 * a + 1374230 * d +
      39770 * r + 242898 * x) / 1000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1000000)).2
    nlinarith only [hDL, haL, hdL, hrL, hxL]
  have sF : (0 : ℝ) ≤ -(-1323 * a - 137423 * c + 7954 * x) / 200000 := by
    apply div_nonneg
    · nlinarith only [haL, hcL, hXsmallU]
    · norm_num
  have hcfU : c * f ≤ (1433 / 200000 : ℝ) * (552 / 3125) :=
    mul_le_mul hcU hfU hf0 (by norm_num)
  have hddL : (23317 / 1000000 : ℝ) * (23317 / 1000000) ≤ d * d :=
    mul_le_mul hdL hdL (by norm_num) hd0
  have sa : (0 : ℝ) ≤
      -(750000000000 * c * f - 750000000000 * d ^ 2 - 579156899) /
        500000000000 := by
    apply div_nonneg
    · nlinarith only [hcfU, hddL]
    · norm_num
  have hdrL : (23317 / 1000000 : ℝ) * (49817 / 1000000) ≤ d * r :=
    mul_le_mul hdL hrL (by norm_num) hd0
  have hfxL : (4411 / 25000 : ℝ) * (37851 / 1000000) ≤ f * x :=
    mul_le_mul hfL hxL (by norm_num) hf0
  have sx : (0 : ℝ) ≤
      (750000000000 * d * r + 375000000000 * f * x +
          14194125000 * f - 5728893101) / 250000000000 := by
    apply div_nonneg
    · nlinarith only [hdrL, hfxL, hfL]
    · norm_num
  have hcrU : c * r ≤ (1433 / 200000 : ℝ) * (57183 / 1000000) :=
    mul_le_mul hcU hrU hr0 (by norm_num)
  have sr :
      (750000000 * c * r + 42887250 * c + 56776500 * d - 2459797) /
          500000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 500000000)).2
    nlinarith only [hcrU, hcU, hdU]
  have sc : -(2473437000000 * f - 382593314063) / 2000000000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2000000000000)).2
    nlinarith only [hfL]
  have sf : (0 : ℝ) ≤ (1587664249 / 1000000000000 : ℝ) := by norm_num
  have tel :
      oddB11pLowerH33GeometrySlope X R C D F a x r c d f -
          (5448358107401 / 8000000000000000 : ℝ) =
        (X - 3977 / 100000) *
          (-(200000 * D * r + 200000 * F * x + 200000 * R * d +
              100000 * X * f + 3977 * f) / 200000) +
        (R - 121449 / 500000) *
          (-(1000000 * C * r + 1000000 * D * x + 500000 * R * c +
              121449 * c + 39770 * d) / 1000000) +
        (C - 1323 / 100000) *
          (-(-500000 * F * a - 687115 * f + 242898 * r) / 1000000) +
        (D - 21449 / 500000) *
          (-(500000 * D * a + 21449 * a + 1374230 * d +
              39770 * r + 242898 * x) / 1000000) +
        (F - 1571 / 5000) * (-(-1323 * a - 137423 * c + 7954 * x) / 200000) +
        (a - 824479 / 1000000) *
          (-(750000000000 * c * f - 750000000000 * d ^ 2 - 579156899) /
            500000000000) +
        (x - 37851 / 1000000) *
          ((750000000000 * d * r + 375000000000 * f * x +
              14194125000 * f - 5728893101) / 250000000000) +
        (r - 57183 / 1000000) *
          ((750000000 * c * r + 42887250 * c + 56776500 * d - 2459797) /
            500000000) +
        (c - 1433 / 200000) *
          (-(2473437000000 * f - 382593314063) / 2000000000000) +
        (f - 4411 / 25000) * (1587664249 / 1000000000000) +
        (d - 23317 / 1000000) *
          ((2473437000000 * d - 66563811073) / 2000000000000) := by
    unfold oddB11pLowerH33GeometrySlope
    ring
  have pX : (0 : ℝ) ≤ (X - 3977 / 100000) *
      (-(200000 * D * r + 200000 * F * x + 200000 * R * d +
          100000 * X * f + 3977 * f) / 200000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hXU]) sX
  have pR : (0 : ℝ) ≤ (R - 121449 / 500000) *
      (-(1000000 * C * r + 1000000 * D * x + 500000 * R * c +
          121449 * c + 39770 * d) / 1000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hRU]) sR
  have pC : (0 : ℝ) ≤ (C - 1323 / 100000) *
      (-(-500000 * F * a - 687115 * f + 242898 * r) / 1000000) :=
    mul_nonneg (by nlinarith only [hCL]) sC
  have pD : (0 : ℝ) ≤ (D - 21449 / 500000) *
      (-(500000 * D * a + 21449 * a + 1374230 * d +
          39770 * r + 242898 * x) / 1000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hDU]) sD
  have pF : (0 : ℝ) ≤ (F - 1571 / 5000) *
      (-(-1323 * a - 137423 * c + 7954 * x) / 200000) :=
    mul_nonneg (by nlinarith only [hFL]) sF
  have pa : (0 : ℝ) ≤ (a - 824479 / 1000000) *
      (-(750000000000 * c * f - 750000000000 * d ^ 2 - 579156899) /
        500000000000) := mul_nonneg (by nlinarith only [haL]) sa
  have px : (0 : ℝ) ≤ (x - 37851 / 1000000) *
      ((750000000000 * d * r + 375000000000 * f * x +
          14194125000 * f - 5728893101) / 250000000000) :=
    mul_nonneg (by nlinarith only [hxL]) sx
  have pr : (0 : ℝ) ≤ (r - 57183 / 1000000) *
      ((750000000 * c * r + 42887250 * c + 56776500 * d - 2459797) /
        500000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hrU]) sr
  have pc : (0 : ℝ) ≤ (c - 1433 / 200000) *
      (-(2473437000000 * f - 382593314063) / 2000000000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hcU]) sc
  have pf : (0 : ℝ) ≤ (f - 4411 / 25000) * (1587664249 / 1000000000000) :=
    mul_nonneg (by nlinarith only [hfL]) sf
  have hdDiff0 : (0 : ℝ) ≤ d - 23317 / 1000000 := by nlinarith only [hdL]
  have hdDiffU : d - 23317 / 1000000 ≤ (3866 / 1000000 : ℝ) := by
    nlinarith only [hdU]
  have sdLower : (-277833767 / 62500000000 : ℝ) ≤
      (2473437000000 * d - 66563811073) / 2000000000000 := by
    nlinarith only [hdL]
  have sdLowerNeg : (-277833767 / 62500000000 : ℝ) ≤ 0 := by norm_num
  have pd1 : (d - 23317 / 1000000) * (-277833767 / 62500000000) ≤
      (d - 23317 / 1000000) *
        ((2473437000000 * d - 66563811073) / 2000000000000) :=
    mul_le_mul_of_nonneg_left sdLower hdDiff0
  have pd0 : (3866 / 1000000 : ℝ) * (-277833767 / 62500000000) ≤
      (d - 23317 / 1000000) * (-277833767 / 62500000000) :=
    mul_le_mul_of_nonpos_right hdDiffU sdLowerNeg
  nlinarith only [tel, pX, pR, pC, pD, pF, pa, px, pr, pc, pf, pd0, pd1]


private def oddB11pLowerSvGeometrySlope (X R C D F x r c d f sv dv v4 : ℝ) : ℝ :=
  -(25000 * C * F * sv + 13459 * C * F - 50000 * C * R * v4 -
      25000 * D ^ 2 * sv - 13459 * D ^ 2 - 50000 * D * R * dv -
      50000 * D * X * v4 - 50000 * F * X * dv - 25000 * c * f * sv -
      13459 * c * f + 50000 * c * r * v4 + 25000 * d ^ 2 * sv +
      13459 * d ^ 2 + 50000 * d * dv * r + 50000 * d * v4 * x +
      50000 * dv * f * x) / 50000

private theorem oddB11pLowerSvGeometry_upper_raw
    (X R C D F x r c d f sv dv v4 : ℝ)
    (hXU : X ≤ (3977 / 100000 : ℝ))
    (hRU : R ≤ (121449 / 500000 : ℝ))
    (hCL : (1323 / 100000 : ℝ) ≤ C) (hCU : C ≤ 671 / 50000)
    (hDL : (42817 / 1000000 : ℝ) ≤ D) (hDU : D ≤ 21449 / 500000)
    (hFL : (1571 / 5000 : ℝ) ≤ F)
    (hxL : (37851 / 1000000 : ℝ) ≤ x) (hxU : x ≤ 39761 / 1000000)
    (hrL : (49817 / 1000000 : ℝ) ≤ r)
    (hcL : (5179 / 1000000 : ℝ) ≤ c) (hcU : c ≤ 1433 / 200000)
    (hdL : (23317 / 1000000 : ℝ) ≤ d) (hdU : d ≤ 27183 / 1000000)
    (hfL : (4411 / 25000 : ℝ) ≤ f) (hfU : f ≤ 552 / 3125)
    (hsvL : (10763 / 20000 : ℝ) ≤ sv) (hsvU : sv ≤ 13459 / 25000)
    (hdvL : (111 / 2000 : ℝ) ≤ dv) (hdvU : dv ≤ 279 / 5000)
    (hv4L : (-1 / 250 : ℝ) ≤ v4) (hv4U : v4 ≤ -1 / 500) :
    oddB11pLowerSvGeometrySlope X R C D F x r c d f sv dv v4 ≤ (-19 / 1000000 : ℝ) := by
  have hD0 : 0 ≤ D := by nlinarith only [hDL]
  have hF0 : 0 ≤ F := by nlinarith only [hFL]
  have hC0 : 0 ≤ C := by nlinarith only [hCL]
  have hx0 : 0 ≤ x := by nlinarith only [hxL]
  have hr0 : 0 ≤ r := by nlinarith only [hrL]
  have hd0 : 0 ≤ d := by nlinarith only [hdL]
  have hf0 : 0 ≤ f := by nlinarith only [hfL]
  have hsv0 : 0 ≤ sv := by nlinarith only [hsvL]
  have hdv0 : 0 ≤ dv := by nlinarith only [hdvL]
  have hnv40 : 0 ≤ -v4 := by nlinarith only [hv4U]
  have hnv4U : -v4 ≤ (1 / 250 : ℝ) := by nlinarith only [hv4L]
  have hDnv4U : D * (-v4) ≤ (21449 / 500000 : ℝ) * (1 / 250) :=
    mul_le_mul hDU hnv4U hnv40 (by norm_num)
  have hFdvL : (1571 / 5000 : ℝ) * (111 / 2000) ≤ F * dv :=
    mul_le_mul hFL hdvL (by norm_num) hF0
  have sX : (0 : ℝ) ≤ D * v4 + F * dv := by nlinarith only [hDnv4U, hFdvL]
  have hCnv4U : C * (-v4) ≤ (671 / 50000 : ℝ) * (1 / 250) :=
    mul_le_mul hCU hnv4U hnv40 (by norm_num)
  have hDdvL : (42817 / 1000000 : ℝ) * (111 / 2000) ≤ D * dv :=
    mul_le_mul hDL hdvL (by norm_num) hD0
  have sR : (0 : ℝ) ≤ C * v4 + D * dv := by nlinarith only [hCnv4U, hDdvL]
  have sC : (-250000 * F * sv - 134590 * F + 121449 * v4) / 500000 ≤
      (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 500000)).2
    nlinarith only [hFL, hsvL, hv4U, mul_nonneg hF0 hsv0]
  have hDsv0 : 0 ≤ D * sv := mul_nonneg hD0 hsv0
  have sD : (0 : ℝ) ≤
      (12500000000 * D * sv + 6729500000 * D + 6072450000 * dv +
          536225000 * sv + 994250000 * v4 + 288682091) / 25000000000 := by
    apply div_nonneg
    · nlinarith only [hDsv0, hDL, hdvL, hsvL, hv4L]
    · norm_num
  have sF : (198850000 * dv - 33075000 * sv - 17806257) / 5000000000 ≤
      (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 5000000000)).2
    nlinarith only [hdvU, hsvL]
  have hdnv4U : d * (-v4) ≤ (27183 / 1000000 : ℝ) * (1 / 250) :=
    mul_le_mul hdU hnv4U hnv40 (by norm_num)
  have hdvfL : (111 / 2000 : ℝ) * (4411 / 25000) ≤ dv * f :=
    mul_le_mul hdvL hfL (by norm_num) hdv0
  have sx : -d * v4 - dv * f ≤ (0 : ℝ) := by nlinarith only [hdnv4U, hdvfL]
  have hcnv4U : c * (-v4) ≤ (1433 / 200000 : ℝ) * (1 / 250) := by
    have hc0 : 0 ≤ c := by
      nlinarith only [hcL]
    exact mul_le_mul hcU hnv4U hnv40 (by norm_num)
  have hddvL : (23317 / 1000000 : ℝ) * (111 / 2000) ≤ d * dv :=
    mul_le_mul hdL hdvL (by norm_num) hd0
  have sr : -c * v4 - d * dv ≤ (0 : ℝ) := by nlinarith only [hcnv4U, hddvL]
  have sc : (0 : ℝ) ≤
      -(-500000 * f * sv - 269180 * f + 49817 * v4) / 1000000 := by
    apply div_nonneg
    · nlinarith only [hfL, hsvL, hv4U, mul_nonneg hf0 hsv0]
    · norm_num
  have hdsv0 : 0 ≤ d * sv := mul_nonneg hd0 hsv0
  have sd :
      -(25000000000 * d * sv + 13459000000 * d + 2490850000 * dv +
          582925000 * sv + 1892550000 * v4 + 313823503) / 50000000000 ≤
        (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 50000000000)).2
    nlinarith only [hdsv0, hdL, hdvL, hsvL, hv4L]
  have sf : (0 : ℝ) ≤
      -(378510000 * dv - 35825000 * sv - 19286747) / 10000000000 := by
    apply div_nonneg
    · nlinarith only [hdvU, hsvL]
    · norm_num
  have ssv : (-318936897 / 400000000000 : ℝ) ≤ 0 := by norm_num
  have sdv : (0 : ℝ) ≤ (602719551 / 40000000000 : ℝ) := by norm_num
  have sv4 : (0 : ℝ) ≤ (920020857 / 250000000000 : ℝ) := by norm_num
  have tel :
      oddB11pLowerSvGeometrySlope X R C D F x r c d f sv dv v4 -
          (-996531627387 / 40000000000000000 : ℝ) =
        (X - 3977 / 100000) * (D * v4 + F * dv) +
        (R - 121449 / 500000) * (C * v4 + D * dv) +
        (C - 1323 / 100000) *
          ((-250000 * F * sv - 134590 * F + 121449 * v4) / 500000) +
        (D - 21449 / 500000) *
          ((12500000000 * D * sv + 6729500000 * D + 6072450000 * dv +
              536225000 * sv + 994250000 * v4 + 288682091) / 25000000000) +
        (F - 1571 / 5000) *
          ((198850000 * dv - 33075000 * sv - 17806257) / 5000000000) +
        (x - 37851 / 1000000) * (-d * v4 - dv * f) +
        (r - 49817 / 1000000) * (-c * v4 - d * dv) +
        (c - 1433 / 200000) *
          (-(-500000 * f * sv - 269180 * f + 49817 * v4) / 1000000) +
        (d - 23317 / 1000000) *
          (-(25000000000 * d * sv + 13459000000 * d + 2490850000 * dv +
              582925000 * sv + 1892550000 * v4 + 313823503) / 50000000000) +
        (f - 552 / 3125) *
          (-(378510000 * dv - 35825000 * sv - 19286747) / 10000000000) +
        (sv - 10763 / 20000) * (-318936897 / 400000000000) +
        (dv - 279 / 5000) * (602719551 / 40000000000) +
        (v4 - (-1 / 500)) * (920020857 / 250000000000) := by
    unfold oddB11pLowerSvGeometrySlope
    ring
  have pX : (X - 3977 / 100000) * (D * v4 + F * dv) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hXU]) sX
  have pR : (R - 121449 / 500000) * (C * v4 + D * dv) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hRU]) sR
  have pC : (C - 1323 / 100000) *
      ((-250000 * F * sv - 134590 * F + 121449 * v4) / 500000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hCL]) sC
  have pD : (D - 21449 / 500000) *
      ((12500000000 * D * sv + 6729500000 * D + 6072450000 * dv +
          536225000 * sv + 994250000 * v4 + 288682091) / 25000000000) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hDU]) sD
  have pF : (F - 1571 / 5000) *
      ((198850000 * dv - 33075000 * sv - 17806257) / 5000000000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hFL]) sF
  have px : (x - 37851 / 1000000) * (-d * v4 - dv * f) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hxL]) sx
  have pr : (r - 49817 / 1000000) * (-c * v4 - d * dv) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hrL]) sr
  have pc : (c - 1433 / 200000) *
      (-(-500000 * f * sv - 269180 * f + 49817 * v4) / 1000000) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hcU]) sc
  have pd : (d - 23317 / 1000000) *
      (-(25000000000 * d * sv + 13459000000 * d + 2490850000 * dv +
          582925000 * sv + 1892550000 * v4 + 313823503) / 50000000000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hdL]) sd
  have pf : (f - 552 / 3125) *
      (-(378510000 * dv - 35825000 * sv - 19286747) / 10000000000) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hfU]) sf
  have psv : (sv - 10763 / 20000) * (-318936897 / 400000000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hsvL]) ssv
  have pdv : (dv - 279 / 5000) * (602719551 / 40000000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hdvU]) sdv
  have pv4 : (v4 - (-1 / 500)) * (920020857 / 250000000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hv4U]) sv4
  nlinarith only [tel, pX, pR, pC, pD, pF, px, pr, pc, pd, pf, psv, pdv, pv4]

private def oddB11pLowerV4GeometrySlope (X R C D a x r c d dv v4 : ℝ) : ℝ :=
  -(-53836000 * C * R + 68711500 * C * v4 - 137423 * C -
      53836000 * D * X + 137423000 * D * dv + 100000000 * R * X * dv -
      50000000 * X ^ 2 * v4 + 100000 * X ^ 2 - 50000000 * a * c * v4 +
      100000 * a * c - 100000000 * a * d * dv + 53836000 * c * r +
      53836000 * d * x - 100000000 * dv * r * x + 50000000 * v4 * x ^ 2 -
      100000 * x ^ 2) / 100000000

private theorem oddB11pLowerV4Geometry_upper_raw
    (X R C D a x r c d dv v4 : ℝ)
    (hXL : (1981 / 50000 : ℝ) ≤ X) (hXU : X ≤ 3977 / 100000)
    (hRL : (242817 / 1000000 : ℝ) ≤ R) (hRU : R ≤ 121449 / 500000)
    (hCL : (1323 / 100000 : ℝ) ≤ C) (hCU : C ≤ 671 / 50000)
    (hDL : (42817 / 1000000 : ℝ) ≤ D)
    (haL : (824479 / 1000000 : ℝ) ≤ a) (haU : a ≤ 165293 / 200000)
    (hxL : (37851 / 1000000 : ℝ) ≤ x) (hxU : x ≤ 39761 / 1000000)
    (hrL : (49817 / 1000000 : ℝ) ≤ r) (hrU : r ≤ 57183 / 1000000)
    (hcL : (5179 / 1000000 : ℝ) ≤ c) (hcU : c ≤ 1433 / 200000)
    (hdL : (23317 / 1000000 : ℝ) ≤ d) (hdU : d ≤ 27183 / 1000000)
    (hdvL : (111 / 2000 : ℝ) ≤ dv) (hdvU : dv ≤ 279 / 5000)
    (hv4L : (-1 / 250 : ℝ) ≤ v4) (hv4U : v4 ≤ -1 / 500) :
    oddB11pLowerV4GeometrySlope X R C D a x r c d dv v4 ≤ (-21 / 50000 : ℝ) := by
  have hX0 : 0 ≤ X := by nlinarith only [hXL]
  have hR0 : 0 ≤ R := by nlinarith only [hRL]
  have hC0 : 0 ≤ C := by nlinarith only [hCL]
  have hD0 : 0 ≤ D := by nlinarith only [hDL]
  have ha0 : 0 ≤ a := by nlinarith only [haL]
  have hx0 : 0 ≤ x := by nlinarith only [hxL]
  have hr0 : 0 ≤ r := by nlinarith only [hrL]
  have hc0 : 0 ≤ c := by nlinarith only [hcL]
  have hd0 : 0 ≤ d := by nlinarith only [hdL]
  have hdv0 : 0 ≤ dv := by nlinarith only [hdvL]
  have hnv40 : 0 ≤ -v4 := by nlinarith only [hv4U]
  have hnv4U : -v4 ≤ (1 / 250 : ℝ) := by nlinarith only [hv4L]
  have hv4L' : -(1 / 250 : ℝ) ≤ v4 := by nlinarith only [hv4L]
  have hRdvU : R * dv ≤ (121449 / 500000 : ℝ) * (279 / 5000) :=
    mul_le_mul hRU hdvU hdv0 (by norm_num)
  have hXnv4U : X * (-v4) ≤ (3977 / 100000 : ℝ) * (1 / 250) :=
    mul_le_mul hXU hnv4U hnv40 (by norm_num)
  have sX : (0 : ℝ) ≤
      (53836000 * D - 100000000 * R * dv + 50000000 * X * v4 -
          100000 * X + 1988500 * v4 - 3977) / 100000000 := by
    apply div_nonneg
    · nlinarith only [hDL, hRdvU, hXnv4U, hXU, hv4L]
    · norm_num
  have sR : (0 : ℝ) ≤ (53836 * C - 3977 * dv) / 100000 := by
    apply div_nonneg
    · nlinarith only [hCL, hdvU]
    · norm_num
  have sC : (0 : ℝ) ≤ -(4294468750 * v4 - 825879983) / 6250000000 := by
    apply div_nonneg
    · nlinarith only [hv4U]
    · norm_num
  have sD : -(3435575000 * dv - 53526443) / 2500000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2500000000)).2
    nlinarith only [hdvL]
  have hcnv4U : c * (-v4) ≤ (1433 / 200000 : ℝ) * (1 / 250) :=
    mul_le_mul hcU hnv4U hnv40 (by norm_num)
  have hddvL : (23317 / 1000000 : ℝ) * (111 / 2000) ≤ d * dv :=
    mul_le_mul hdL hdvL (by norm_num) hd0
  have sa : (0 : ℝ) ≤ (500 * c * v4 - c + 1000 * d * dv) / 1000 := by
    apply div_nonneg
    · nlinarith only [hcnv4U, hcU, hddvL]
    · norm_num
  have hdLterm : (538360000 : ℝ) * (23317 / 1000000) ≤ 538360000 * d := by
    nlinarith only [hdL]
  have hdvrU : dv * r ≤ (279 / 5000 : ℝ) * (57183 / 1000000) :=
    mul_le_mul hdvU hrU hr0 (by norm_num)
  have hv4xLower : -(1 / 250 : ℝ) * (39761 / 1000000) ≤ v4 * x := by
    have h1 : -(1 / 250 : ℝ) * x ≤ v4 * x :=
      mul_le_mul_of_nonneg_right hv4L' hx0
    have h2 : -(1 / 250 : ℝ) * (39761 / 1000000) ≤ -(1 / 250 : ℝ) * x :=
      mul_le_mul_of_nonpos_left hxU (by norm_num)
    exact h2.trans h1
  have sx :
      -(538360000 * d - 1000000000 * dv * r + 500000000 * v4 * x +
          18925500 * v4 - 1000000 * x - 37851) / 1000000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1000000000)).2
    nlinarith only [hdLterm, hdvrU, hv4xLower, hv4L, hxU]
  have sr : -(538360 * c - 37851 * dv) / 1000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1000000)).2
    nlinarith only [hcL, hdvU]
  have sc : (2582703125 * v4 - 172787157) / 6250000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 6250000000)).2
    nlinarith only [hv4U]
  have sd : (0 : ℝ) ≤ (20661625000 * dv - 509436609) / 25000000000 := by
    apply div_nonneg
    · nlinarith only [hdvL]
    · norm_num
  have sdv : (-5518629751 / 125000000000 : ℝ) ≤ 0 := by norm_num
  have sv4 : (-7006474833 / 1000000000000 : ℝ) ≤ 0 := by norm_num
  have tel :
      oddB11pLowerV4GeometrySlope X R C D a x r c d dv v4 -
          (-167745095631 / 390625000000000 : ℝ) =
        (X - 3977 / 100000) *
          ((53836000 * D - 100000000 * R * dv + 50000000 * X * v4 -
              100000 * X + 1988500 * v4 - 3977) / 100000000) +
        (R - 121449 / 500000) * ((53836 * C - 3977 * dv) / 100000) +
        (C - 671 / 50000) * (-(4294468750 * v4 - 825879983) / 6250000000) +
        (D - 42817 / 1000000) * (-(3435575000 * dv - 53526443) / 2500000000) +
        (a - 165293 / 200000) * ((500 * c * v4 - c + 1000 * d * dv) / 1000) +
        (x - 37851 / 1000000) *
          (-(538360000 * d - 1000000000 * dv * r + 500000000 * v4 * x +
              18925500 * v4 - 1000000 * x - 37851) / 1000000000) +
        (r - 49817 / 1000000) * (-(538360 * c - 37851 * dv) / 1000000) +
        (c - 5179 / 1000000) * ((2582703125 * v4 - 172787157) / 6250000000) +
        (d - 27183 / 1000000) * ((20661625000 * dv - 509436609) / 25000000000) +
        (dv - 111 / 2000) * (-5518629751 / 125000000000) +
        (v4 - (-1 / 250)) * (-7006474833 / 1000000000000) := by
    unfold oddB11pLowerV4GeometrySlope
    ring
  have pX : (X - 3977 / 100000) *
      ((53836000 * D - 100000000 * R * dv + 50000000 * X * v4 -
          100000 * X + 1988500 * v4 - 3977) / 100000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hXU]) sX
  have pR : (R - 121449 / 500000) * ((53836 * C - 3977 * dv) / 100000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hRU]) sR
  have pC : (C - 671 / 50000) *
      (-(4294468750 * v4 - 825879983) / 6250000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hCU]) sC
  have pD : (D - 42817 / 1000000) *
      (-(3435575000 * dv - 53526443) / 2500000000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hDL]) sD
  have pa : (a - 165293 / 200000) *
      ((500 * c * v4 - c + 1000 * d * dv) / 1000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [haU]) sa
  have px : (x - 37851 / 1000000) *
      (-(538360000 * d - 1000000000 * dv * r + 500000000 * v4 * x +
          18925500 * v4 - 1000000 * x - 37851) / 1000000000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hxL]) sx
  have pr : (r - 49817 / 1000000) *
      (-(538360 * c - 37851 * dv) / 1000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hrL]) sr
  have pc : (c - 5179 / 1000000) *
      ((2582703125 * v4 - 172787157) / 6250000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hcL]) sc
  have pd : (d - 27183 / 1000000) *
      ((20661625000 * dv - 509436609) / 25000000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hdU]) sd
  have pdv : (dv - 111 / 2000) * (-5518629751 / 125000000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hdvL]) sdv
  have pv4 : (v4 - (-1 / 250)) * (-7006474833 / 1000000000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hv4L]) sv4
  nlinarith only [tel, pX, pR, pC, pD, pa, px, pr, pc, pd, pdv, pv4]


private def oddB11pLowerXGeometrySlope (X R D F x r d f dv : ℝ) : ℝ :=
  (-49725000000 * D * R + 6000000000 * D * r - 53836000 * D -
      24862500000 * F * X + 26918000000 * F * dv + 6000000000 * F * x -
      988781625 * F + 6000000000 * R * d + 100000000 * R * dv +
      3000000000 * X * f + 100000 * X + 16575000000 * d * r +
      16575000000 * f * x + 119310000 * f + 3977) / 50000000000

private theorem oddB11pLowerXGeometry_upper_raw
    (X R D F x r d f dv : ℝ)
    (hXL : (1981 / 50000 : ℝ) ≤ X)
    (hRL : (242817 / 1000000 : ℝ) ≤ R)
    (hDL : (42817 / 1000000 : ℝ) ≤ D)
    (hFL : (1571 / 5000 : ℝ) ≤ F)
    (hxU : x ≤ (39761 / 1000000 : ℝ))
    (hrU : r ≤ (57183 / 1000000 : ℝ))
    (hdLittleL : (23317 / 1000000 : ℝ) ≤ d) (hdU : d ≤ 27183 / 1000000)
    (hfL : (4411 / 25000 : ℝ) ≤ f) (hfU : f ≤ 552 / 3125)
    (hdvU : dv ≤ (279 / 5000 : ℝ)) :
    oddB11pLowerXGeometrySlope X R D F x r d f dv ≤ (-7 / 1000 : ℝ) := by
  have sX : (-248625 * F + 30000 * f + 1) / 500000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 500000)).2
    nlinarith only [hFL, hfU]
  have sR : (-1989 * D + 240 * d + 4 * dv) / 2000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2000)).2
    nlinarith only [hDL, hdU, hdvU]
  have sD : (240000000 * r - 485116453) / 2000000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2000000000)).2
    nlinarith only [hrU]
  have sF : (215344000 * dv + 48000000 * x - 15790671) / 400000000 ≤
      (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 400000000)).2
    nlinarith only [hdvU, hxU]
  have sx : (0 : ℝ) ≤ 3 * (27625 * f + 3142) / 250000 := by
    apply div_nonneg
    · nlinarith only [hfL]
    · norm_num
  have sr : (0 : ℝ) ≤ 3 * (2762500 * d + 42817) / 25000000 := by
    apply div_nonneg
    · nlinarith only [hdLittleL]
    · norm_num
  have sd : (0 : ℝ) ≤ (96188409 / 2000000000 : ℝ) := by norm_num
  have sf : (0 : ℝ) ≤ (35888343 / 2000000000 : ℝ) := by norm_num
  have sdv : (0 : ℝ) ≤ (84819173 / 500000000 : ℝ) := by norm_num
  have tel :
      oddB11pLowerXGeometrySlope X R D F x r d f dv -
          (-7053248667747 / 1000000000000000 : ℝ) =
        (X - 1981 / 50000) * ((-248625 * F + 30000 * f + 1) / 500000) +
        (R - 242817 / 1000000) * ((-1989 * D + 240 * d + 4 * dv) / 2000) +
        (D - 42817 / 1000000) * ((240000000 * r - 485116453) / 2000000000) +
        (F - 1571 / 5000) *
          ((215344000 * dv + 48000000 * x - 15790671) / 400000000) +
        (x - 39761 / 1000000) * (3 * (27625 * f + 3142) / 250000) +
        (r - 57183 / 1000000) * (3 * (2762500 * d + 42817) / 25000000) +
        (d - 27183 / 1000000) * (96188409 / 2000000000) +
        (f - 552 / 3125) * (35888343 / 2000000000) +
        (dv - 279 / 5000) * (84819173 / 500000000) := by
    unfold oddB11pLowerXGeometrySlope
    ring
  have pX : (X - 1981 / 50000) * ((-248625 * F + 30000 * f + 1) / 500000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hXL]) sX
  have pR : (R - 242817 / 1000000) * ((-1989 * D + 240 * d + 4 * dv) / 2000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hRL]) sR
  have pD : (D - 42817 / 1000000) *
      ((240000000 * r - 485116453) / 2000000000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hDL]) sD
  have pF : (F - 1571 / 5000) *
      ((215344000 * dv + 48000000 * x - 15790671) / 400000000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hFL]) sF
  have px : (x - 39761 / 1000000) * (3 * (27625 * f + 3142) / 250000) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hxU]) sx
  have pr : (r - 57183 / 1000000) *
      (3 * (2762500 * d + 42817) / 25000000) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hrU]) sr
  have pd : (d - 27183 / 1000000) * (96188409 / 2000000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hdU]) sd
  have pf : (f - 552 / 3125) * (35888343 / 2000000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hfU]) sf
  have pdv : (dv - 279 / 5000) * (84819173 / 500000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hdvU]) sdv
  nlinarith only [tel, pX, pR, pD, pF, px, pr, pd, pf, pdv]

private def oddB11pLowerRGeometrySlope (R C D x r c d dv : ℝ) : ℝ :=
  (-994500000 * C * R + 240000000 * C * r - 243715501 * C +
      1076720000 * D * dv + 240000000 * D * x - 79102530 * D +
      120000000 * R * c + 1000000000 * R * dv ^ 2 + 663000000 * c * r +
      29147760 * c + 663000000 * d * x + 9544800 * d +
      242898000 * dv ^ 2 + 159080 * dv) / 2000000000

private theorem oddB11pLowerRGeometry_upper_raw
    (R C D x r c d dv : ℝ)
    (hRL : (242817 / 1000000 : ℝ) ≤ R)
    (hCL : (1323 / 100000 : ℝ) ≤ C)
    (hDL : (42817 / 1000000 : ℝ) ≤ D)
    (hxU : x ≤ (39761 / 1000000 : ℝ))
    (hrU : r ≤ (57183 / 1000000 : ℝ))
    (hcLittleL : (5179 / 1000000 : ℝ) ≤ c) (hcU : c ≤ 1433 / 200000)
    (hdLittleL : (23317 / 1000000 : ℝ) ≤ d) (hdU : d ≤ 27183 / 1000000)
    (hdvL : (111 / 2000 : ℝ) ≤ dv) (hdvU : dv ≤ 279 / 5000) :
    oddB11pLowerRGeometrySlope R C D x r c d dv ≤ (-17 / 10000 : ℝ) := by
  have hdv0 : 0 ≤ dv := by nlinarith only [hdvL]
  have hdvSq : dv * dv ≤ (279 / 5000 : ℝ) * (279 / 5000) :=
    mul_le_mul hdvU hdvU hdv0 (by norm_num)
  have sR : (-1989 * C + 240 * c + 2000 * dv ^ 2) / 4000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 4000)).2
    nlinarith only [hCL, hcU, hdvSq]
  have sC : (96000000 * r - 194078803) / 800000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 800000000)).2
    nlinarith only [hrU]
  have sD : (107672000 * dv + 24000000 * x - 7910253) / 200000000 ≤
      (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 200000000)).2
    nlinarith only [hdvU, hxU]
  have sx : (0 : ℝ) ≤ 3 * (2762500 * d + 42817) / 25000000 := by
    apply div_nonneg
    · nlinarith only [hdLittleL]
    · norm_num
  have sr : (0 : ℝ) ≤ 3 * (276250 * c + 1323) / 2500000 := by
    apply div_nonneg
    · nlinarith only [hcLittleL]
    · norm_num
  have sc : (0 : ℝ) ≤ (96198129 / 2000000000 : ℝ) := by norm_num
  have sd : (0 : ℝ) ≤ (35906343 / 2000000000 : ℝ) := by norm_num
  have sdv : (0 : ℝ) ≤ (12142875000 * dv + 1834097431) / 50000000000 := by
    apply div_nonneg
    · nlinarith only [hdvL]
    · norm_num
  have tel :
      oddB11pLowerRGeometrySlope R C D x r c d dv -
          (-3456927575709 / 2000000000000000 : ℝ) =
        (R - 242817 / 1000000) * ((-1989 * C + 240 * c + 2000 * dv ^ 2) / 4000) +
        (C - 1323 / 100000) * ((96000000 * r - 194078803) / 800000000) +
        (D - 42817 / 1000000) *
          ((107672000 * dv + 24000000 * x - 7910253) / 200000000) +
        (x - 39761 / 1000000) * (3 * (2762500 * d + 42817) / 25000000) +
        (r - 57183 / 1000000) * (3 * (276250 * c + 1323) / 2500000) +
        (c - 1433 / 200000) * (96198129 / 2000000000) +
        (d - 27183 / 1000000) * (35906343 / 2000000000) +
        (dv - 279 / 5000) * ((12142875000 * dv + 1834097431) / 50000000000) := by
    unfold oddB11pLowerRGeometrySlope
    ring
  have pR : (R - 242817 / 1000000) *
      ((-1989 * C + 240 * c + 2000 * dv ^ 2) / 4000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hRL]) sR
  have pC : (C - 1323 / 100000) * ((96000000 * r - 194078803) / 800000000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hCL]) sC
  have pD : (D - 42817 / 1000000) *
      ((107672000 * dv + 24000000 * x - 7910253) / 200000000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hDL]) sD
  have px : (x - 39761 / 1000000) *
      (3 * (2762500 * d + 42817) / 25000000) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hxU]) sx
  have pr : (r - 57183 / 1000000) *
      (3 * (276250 * c + 1323) / 2500000) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hrU]) sr
  have pc : (c - 1433 / 200000) * (96198129 / 2000000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hcU]) sc
  have pd : (d - 27183 / 1000000) * (35906343 / 2000000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hdU]) sd
  have pdv : (dv - 279 / 5000) *
      ((12142875000 * dv + 1834097431) / 50000000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hdvU]) sdv
  nlinarith only [tel, pR, pC, pD, px, pr, pc, pd, pdv]


private def oddB11pLowerCGeometrySlope (F a r f : ℝ) : ℝ :=
  (-60000000000000 * F * a + 538420122700000 * F -
      165750000000000 * a * f - 82453800000000 * f +
      165750000000000 * r ^ 2 + 29147760000000 * r -
      29601752340949) / 1000000000000000

private theorem oddB11pLowerCGeometry_lower_raw
    (F a r f : ℝ)
    (hFL : (1571 / 5000 : ℝ) ≤ F)
    (haU : a ≤ (165293 / 200000 : ℝ))
    (hrL : (49817 / 1000000 : ℝ) ≤ r)
    (hfL : (4411 / 25000 : ℝ) ≤ f) (hfU : f ≤ 552 / 3125) :
    (87 / 1000 : ℝ) ≤ oddB11pLowerCGeometrySlope F a r f := by
  have sF : (0 : ℝ) ≤ -(600000000 * a - 5384201227) / 10000000000 := by
    apply div_nonneg
    · nlinarith only [haU]
    · norm_num
  have sa : -3 * (27625 * f + 3142) / 500000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 500000)).2
    nlinarith only [hfL]
  have sr : (0 : ℝ) ≤ 3 * (221000000 * r + 49873237) / 4000000000 := by
    apply div_nonneg
    · nlinarith only [hrL]
    · norm_num
  have sf : (-175552299 / 800000000 : ℝ) ≤ 0 := by norm_num
  have tel :
      oddB11pLowerCGeometrySlope F a r f - (348363142791651 / 4000000000000000 : ℝ) =
        (F - 1571 / 5000) * (-(600000000 * a - 5384201227) / 10000000000) +
        (a - 165293 / 200000) * (-3 * (27625 * f + 3142) / 500000) +
        (r - 49817 / 1000000) *
          (3 * (221000000 * r + 49873237) / 4000000000) +
        (f - 552 / 3125) * (-175552299 / 800000000) := by
    unfold oddB11pLowerCGeometrySlope
    ring
  have pF : (0 : ℝ) ≤ (F - 1571 / 5000) *
      (-(600000000 * a - 5384201227) / 10000000000) :=
    mul_nonneg (by nlinarith only [hFL]) sF
  have pa : (0 : ℝ) ≤ (a - 165293 / 200000) *
      (-3 * (27625 * f + 3142) / 500000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [haU]) sa
  have pr : (0 : ℝ) ≤ (r - 49817 / 1000000) *
      (3 * (221000000 * r + 49873237) / 4000000000) :=
    mul_nonneg (by nlinarith only [hrL]) sr
  have pf : (0 : ℝ) ≤ (f - 552 / 3125) * (-175552299 / 800000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hfU]) sf
  nlinarith only [tel, pF, pa, pr, pf]

private def oddB11pLowerDGeometrySlope (D a x r d dv : ℝ) : ℝ :=
  (300000000000000 * D * a - 2692100613500000 * D +
      1657500000000000 * a * d + 12869400000000 * a +
      824538000000000 * d + 667575136400000 * dv +
      1657500000000000 * r * x + 23862000000000 * r +
      145738800000000 * x - 163734453719773) / 5000000000000000

private theorem oddB11pLowerDGeometry_upper_raw
    (D a x r d dv : ℝ)
    (hDL : (42817 / 1000000 : ℝ) ≤ D)
    (haU : a ≤ (165293 / 200000 : ℝ))
    (hxU : x ≤ (39761 / 1000000 : ℝ))
    (hrL : (49817 / 1000000 : ℝ) ≤ r) (hrU : r ≤ 57183 / 1000000)
    (hdL : (23317 / 1000000 : ℝ) ≤ d) (hdU : d ≤ 27183 / 1000000)
    (hdvU : dv ≤ (279 / 5000 : ℝ)) :
    oddB11pLowerDGeometrySlope D a x r d dv ≤ (-29 / 1000 : ℝ) := by
  have sD : (600000000 * a - 5384201227) / 10000000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 10000000000)).2
    nlinarith only [haU]
  have sa : (0 : ℝ) ≤ 3 * (1105000 * d + 17143) / 10000000 := by
    apply div_nonneg
    · nlinarith only [hdL]
    · norm_num
  have sx : (0 : ℝ) ≤ 3 * (1381250 * r + 121449) / 12500000 := by
    apply div_nonneg
    · nlinarith only [hrL]
    · norm_num
  have sr : (0 : ℝ) ≤ (35906343 / 2000000000 : ℝ) := by norm_num
  have sd : (0 : ℝ) ≤ (175552299 / 400000000 : ℝ) := by norm_num
  have sdv : (0 : ℝ) ≤ (1668937841 / 12500000000 : ℝ) := by norm_num
  have tel :
      oddB11pLowerDGeometrySlope D a x r d dv - (-59968408232679 / 2000000000000000 : ℝ) =
        (D - 42817 / 1000000) * ((600000000 * a - 5384201227) / 10000000000) +
        (a - 165293 / 200000) * (3 * (1105000 * d + 17143) / 10000000) +
        (x - 39761 / 1000000) *
          (3 * (1381250 * r + 121449) / 12500000) +
        (r - 57183 / 1000000) * (35906343 / 2000000000) +
        (d - 27183 / 1000000) * (175552299 / 400000000) +
        (dv - 279 / 5000) * (1668937841 / 12500000000) := by
    unfold oddB11pLowerDGeometrySlope
    ring
  have pD : (D - 42817 / 1000000) *
      ((600000000 * a - 5384201227) / 10000000000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hDL]) sD
  have pa : (a - 165293 / 200000) *
      (3 * (1105000 * d + 17143) / 10000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [haU]) sa
  have px : (x - 39761 / 1000000) *
      (3 * (1381250 * r + 121449) / 12500000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hxU]) sx
  have pr : (r - 57183 / 1000000) * (35906343 / 2000000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hrU]) sr
  have pd : (d - 27183 / 1000000) * (175552299 / 400000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hdU]) sd
  have pdv : (dv - 279 / 5000) * (1668937841 / 12500000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hdvU]) sdv
  nlinarith only [tel, pD, pa, px, pr, pd, pdv]

private def oddB11pLowerFGeometrySlope (a x c dv : ℝ) : ℝ :=
  (-41437500000000 * a * c - 198450000000 * a - 20613450000000 * c -
      171778750000000 * dv ^ 2 + 5352644300000 * dv +
      41437500000000 * x ^ 2 + 1193100000000 * x + 1584205329699) /
    250000000000000

private theorem oddB11pLowerFGeometry_lower_raw
    (a x c dv : ℝ)
    (haU : a ≤ (165293 / 200000 : ℝ))
    (hxL : (37851 / 1000000 : ℝ) ≤ x)
    (hcL : (5179 / 1000000 : ℝ) ≤ c) (hcU : c ≤ 1433 / 200000)
    (hdvL : (111 / 2000 : ℝ) ≤ dv) (hdvU : dv ≤ 279 / 5000) :
    (7 / 2000 : ℝ) ≤ oddB11pLowerFGeometrySlope a x c dv := by
  have sa : -3 * (276250 * c + 1323) / 5000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 5000000)).2
    nlinarith only [hcL]
  have sx : (0 : ℝ) ≤ 3 * (221000000 * x + 14728271) / 4000000000 := by
    apply div_nonneg
    · nlinarith only [hxL]
    · norm_num
  have sc : (-175552299 / 800000000 : ℝ) ≤ 0 := by norm_num
  have sdv : -(3435575000 * dv + 84652199) / 5000000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 5000000000)).2
    nlinarith only [hdvL]
  have tel :
      oddB11pLowerFGeometrySlope a x c dv - (3581874422253 / 1000000000000000 : ℝ) =
        (a - 165293 / 200000) * (-3 * (276250 * c + 1323) / 5000000) +
        (x - 37851 / 1000000) *
          (3 * (221000000 * x + 14728271) / 4000000000) +
        (c - 1433 / 200000) * (-175552299 / 800000000) +
        (dv - 279 / 5000) * (-(3435575000 * dv + 84652199) / 5000000000) := by
    unfold oddB11pLowerFGeometrySlope
    ring
  have pa : (0 : ℝ) ≤ (a - 165293 / 200000) *
      (-3 * (276250 * c + 1323) / 5000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [haU]) sa
  have px : (0 : ℝ) ≤ (x - 37851 / 1000000) *
      (3 * (221000000 * x + 14728271) / 4000000000) :=
    mul_nonneg (by nlinarith only [hxL]) sx
  have pc : (0 : ℝ) ≤ (c - 1433 / 200000) * (-175552299 / 800000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hcU]) sc
  have pdv : (0 : ℝ) ≤ (dv - 279 / 5000) *
      (-(3435575000 * dv + 84652199) / 5000000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hdvU]) sdv
  nlinarith only [tel, pa, px, pc, pdv]

private def oddB11pLowerAGeometrySlope (c d f dv : ℝ) : ℝ :=
  (2250000000000 * c * f - 650958125000 * c - 2250000000000 * d ^ 2 -
      25000000000 * d * dv + 177758587500 * d + 6250000000000 * dv ^ 2 * f -
      27410906250 * f - 1737470697) / 12500000000000

private theorem oddB11pLowerAGeometry_upper_raw
    (c d f dv : ℝ)
    (hcL : (5179 / 1000000 : ℝ) ≤ c)
    (hdL : (23317 / 1000000 : ℝ) ≤ d) (hdU : d ≤ 27183 / 1000000)
    (hfL : (4411 / 25000 : ℝ) ≤ f) (hfU : f ≤ 552 / 3125)
    (hdvL : (111 / 2000 : ℝ) ≤ dv) (hdvU : dv ≤ 279 / 5000) :
    oddB11pLowerAGeometrySlope c d f dv ≤ (-1 / 10000 : ℝ) := by
  have sc : (3600000 * f - 1041533) / 20000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 20000000)).2
    nlinarith only [hfU]
  have sd : (0 : ℝ) ≤
      -(180000000 * d + 2000000 * dv - 9327747) / 1000000000 := by
    apply div_nonneg
    · nlinarith only [hdU, hdvU]
    · norm_num
  have hdv0 : 0 ≤ dv := by nlinarith only [hdvL]
  have hdvSqL : (111 / 2000 : ℝ) * (111 / 2000) ≤ dv * dv :=
    mul_le_mul hdvL hdvL (by norm_num) hdv0
  have sf : (0 : ℝ) ≤ (200000000 * dv ^ 2 - 504261) / 400000000 := by
    apply div_nonneg
    · nlinarith only [hdvSqL]
    · norm_num
  have sdv : (0 : ℝ) ≤ 3 * (2944000 * dv + 162463) / 100000000 := by
    apply div_nonneg
    · nlinarith only [hdvL]
    · norm_num
  have tel :
      oddB11pLowerAGeometrySlope c d f dv - (-105865075009 / 1000000000000000 : ℝ) =
        (c - 5179 / 1000000) * ((3600000 * f - 1041533) / 20000000) +
        (d - 27183 / 1000000) *
          (-(180000000 * d + 2000000 * dv - 9327747) / 1000000000) +
        (f - 552 / 3125) * ((200000000 * dv ^ 2 - 504261) / 400000000) +
        (dv - 279 / 5000) * (3 * (2944000 * dv + 162463) / 100000000) := by
    unfold oddB11pLowerAGeometrySlope
    ring
  have pc : (c - 5179 / 1000000) * ((3600000 * f - 1041533) / 20000000) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hcL]) sc
  have pd : (d - 27183 / 1000000) *
      (-(180000000 * d + 2000000 * dv - 9327747) / 1000000000) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hdU]) sd
  have pf : (f - 552 / 3125) *
      ((200000000 * dv ^ 2 - 504261) / 400000000) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hfU]) sf
  have pdv : (dv - 279 / 5000) *
      (3 * (2944000 * dv + 162463) / 100000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hdvU]) sdv
  nlinarith only [tel, pc, pd, pf, pdv]


private def oddB11pLowerLittleXGeometrySlope (x r d f dv : ℝ) : ℝ :=
  -(36000000000000 * d * r - 8159740700000 * d + 53836000000000 * dv * f +
      200000000000 * dv * r + 18000000000000 * f * x - 637057500000 * f -
      1422068700000 * r - 5207665000000 * x - 472102196763) /
    100000000000000

private theorem oddB11pLowerLittleXGeometry_lower_raw
    (x r d f dv : ℝ)
    (hxL : (37851 / 1000000 : ℝ) ≤ x)
    (hrL : (49817 / 1000000 : ℝ) ≤ r)
    (hdL : (23317 / 1000000 : ℝ) ≤ d) (hdU : d ≤ 27183 / 1000000)
    (hfL : (4411 / 25000 : ℝ) ≤ f) (hfU : f ≤ 552 / 3125)
    (hdvL : (111 / 2000 : ℝ) ≤ dv) (hdvU : dv ≤ 279 / 5000) :
    (17 / 5000 : ℝ) ≤ oddB11pLowerLittleXGeometrySlope x r d f dv := by
  have sx : (0 : ℝ) ≤ -(3600000 * f - 1041533) / 20000000 := by
    apply div_nonneg
    · nlinarith only [hfU]
    · norm_num
  have sr : (0 : ℝ) ≤
      -(360000000 * d + 2000000 * dv - 14220687) / 1000000000 := by
    apply div_nonneg
    · nlinarith only [hdU, hdvU]
    · norm_num
  have sd : (0 : ℝ) ≤ (63663287 / 1000000000 : ℝ) := by norm_num
  have sf : -(107672000 * dv + 88521) / 200000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 200000000)).2
    nlinarith only [hdvL]
  have sdv : (-237988861 / 2500000000 : ℝ) ≤ 0 := by norm_num
  have tel :
      oddB11pLowerLittleXGeometrySlope x r d f dv - (1747475474659 / 500000000000000 : ℝ) =
        (x - 37851 / 1000000) * (-(3600000 * f - 1041533) / 20000000) +
        (r - 49817 / 1000000) *
          (-(360000000 * d + 2000000 * dv - 14220687) / 1000000000) +
        (d - 23317 / 1000000) * (63663287 / 1000000000) +
        (f - 552 / 3125) * (-(107672000 * dv + 88521) / 200000000) +
        (dv - 279 / 5000) * (-237988861 / 2500000000) := by
    unfold oddB11pLowerLittleXGeometrySlope
    ring
  have px : (0 : ℝ) ≤ (x - 37851 / 1000000) *
      (-(3600000 * f - 1041533) / 20000000) :=
    mul_nonneg (by nlinarith only [hxL]) sx
  have pr : (0 : ℝ) ≤ (r - 49817 / 1000000) *
      (-(360000000 * d + 2000000 * dv - 14220687) / 1000000000) :=
    mul_nonneg (by nlinarith only [hrL]) sr
  have pd : (0 : ℝ) ≤ (d - 23317 / 1000000) * (63663287 / 1000000000) :=
    mul_nonneg (by nlinarith only [hdL]) sd
  have pf : (0 : ℝ) ≤ (f - 552 / 3125) *
      (-(107672000 * dv + 88521) / 200000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hfU]) sf
  have pdv : (0 : ℝ) ≤ (dv - 279 / 5000) * (-237988861 / 2500000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hdvU]) sdv
  nlinarith only [tel, px, pr, pd, pf, pdv]

private def oddB11pLowerLittleRGeometrySlope (r c d dv : ℝ) : ℝ :=
  -(360000000000000 * c * r - 145260694000000 * c +
      1076720000000000 * d * dv + 885210000000 * d +
      1000000000000000 * dv ^ 2 * r + 49817000000000 * dv ^ 2 +
      151404000000 * dv - 4385745000000 * r - 2475721665939) /
    2000000000000000

private theorem oddB11pLowerLittleRGeometry_lower_raw
    (r c d dv : ℝ)
    (hrU : r ≤ (57183 / 1000000 : ℝ))
    (hcL : (5179 / 1000000 : ℝ) ≤ c)
    (hdU : d ≤ (27183 / 1000000 : ℝ))
    (hdvL : (111 / 2000 : ℝ) ≤ dv) (hdvU : dv ≤ 279 / 5000) :
    (3 / 5000 : ℝ) ≤ oddB11pLowerLittleRGeometrySlope r c d dv := by
  have hdv0 : 0 ≤ dv := by nlinarith only [hdvL]
  have hdvSqL : (111 / 2000 : ℝ) * (111 / 2000) ≤ dv * dv :=
    mul_le_mul hdvL hdvL (by norm_num) hdv0
  have sr : -(72000000 * c + 200000000 * dv ^ 2 - 877149) / 400000000 ≤
      (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 400000000)).2
    nlinarith only [hcL, hdvSqL]
  have sc : (0 : ℝ) ≤ (62337407 / 1000000000 : ℝ) := by norm_num
  have sd : -(107672000 * dv + 88521) / 200000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 200000000)).2
    nlinarith only [hdvL]
  have sdv : -(1337500000 * dv + 442381047) / 25000000000 ≤ (0 : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 25000000000)).2
    nlinarith only [hdvL]
  have tel :
      oddB11pLowerLittleRGeometrySlope r c d dv - (686675463371 / 1000000000000000 : ℝ) =
        (r - 57183 / 1000000) *
          (-(72000000 * c + 200000000 * dv ^ 2 - 877149) / 400000000) +
        (c - 5179 / 1000000) * (62337407 / 1000000000) +
        (d - 27183 / 1000000) * (-(107672000 * dv + 88521) / 200000000) +
        (dv - 279 / 5000) *
          (-(1337500000 * dv + 442381047) / 25000000000) := by
    unfold oddB11pLowerLittleRGeometrySlope
    ring
  have pr : (0 : ℝ) ≤ (r - 57183 / 1000000) *
      (-(72000000 * c + 200000000 * dv ^ 2 - 877149) / 400000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hrU]) sr
  have pc : (0 : ℝ) ≤ (c - 5179 / 1000000) * (62337407 / 1000000000) :=
    mul_nonneg (by nlinarith only [hcL]) sc
  have pd : (0 : ℝ) ≤ (d - 27183 / 1000000) *
      (-(107672000 * dv + 88521) / 200000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hdU]) sd
  have pdv : (0 : ℝ) ≤ (dv - 279 / 5000) *
      (-(1337500000 * dv + 442381047) / 25000000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hdvU]) sdv
  nlinarith only [tel, pr, pc, pd, pdv]

private def oddB11pLowerLittleCGeometrySlope (f : ℝ) : ℝ :=
  (65900822300000 * f - 61788320201511) / 1000000000000000

private theorem oddB11pLowerLittleCGeometry_upper_raw
    (f : ℝ) (hfU : f ≤ (552 / 3125 : ℝ)) :
    oddB11pLowerLittleCGeometrySlope f ≤ (-1 / 20 : ℝ) := by
  have slope : (0 : ℝ) ≤ (659008223 / 10000000000 : ℝ) := by norm_num
  have tel :
      oddB11pLowerLittleCGeometrySlope f - (-50147598950439 / 1000000000000000 : ℝ) =
        (f - 552 / 3125) * (659008223 / 10000000000) := by
    unfold oddB11pLowerLittleCGeometrySlope
    ring
  have step : (f - 552 / 3125) * (659008223 / 10000000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hfU]) slope
  nlinarith only [tel, step]

private def oddB11pLowerLittleDGeometrySlope (d dv : ℝ) : ℝ :=
  -(659008223000000 * d + 284724101200000 * dv - 215161974469579) /
    10000000000000000

private theorem oddB11pLowerLittleDGeometry_lower_raw
    (d dv : ℝ)
    (hdU : d ≤ (27183 / 1000000 : ℝ))
    (hdvU : dv ≤ (279 / 5000 : ℝ)) :
    (9 / 500 : ℝ) ≤ oddB11pLowerLittleDGeometrySlope d dv := by
  have sd : (-659008223 / 10000000000 : ℝ) ≤ 0 := by norm_num
  have sdv : (-711810253 / 25000000000 : ℝ) ≤ 0 := by norm_num
  have tel :
      oddB11pLowerLittleDGeometrySlope d dv - (18136054909681 / 1000000000000000 : ℝ) =
        (d - 27183 / 1000000) * (-659008223 / 10000000000) +
        (dv - 279 / 5000) * (-711810253 / 25000000000) := by
    unfold oddB11pLowerLittleDGeometrySlope
    ring
  have pd : (0 : ℝ) ≤ (d - 27183 / 1000000) * (-659008223 / 10000000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hdU]) sd
  have pdv : (0 : ℝ) ≤ (dv - 279 / 5000) * (-711810253 / 25000000000) :=
    mul_nonneg_of_nonpos_of_nonpos (by nlinarith only [hdvU]) sdv
  nlinarith only [tel, pd, pdv]

private def oddB11pLowerLittleFGeometrySlope (dv : ℝ) : ℝ :=
  (12913515625000 * dv ^ 2 - 636795761250 * dv - 65468279519) /
    31250000000000

private theorem oddB11pLowerLittleFGeometry_upper_raw
    (dv : ℝ)
    (hdvL : (111 / 2000 : ℝ) ≤ dv) (hdvU : dv ≤ 279 / 5000) :
    oddB11pLowerLittleFGeometrySlope dv ≤ (-19 / 10000 : ℝ) := by
  have slope : (0 : ℝ) ≤ (20661625000 * dv + 134045457) / 50000000000 := by
    apply div_nonneg
    · nlinarith only [hdvL]
    · norm_num
  have tel :
      oddB11pLowerLittleFGeometrySlope dv - (-486347553649 / 250000000000000 : ℝ) =
        (dv - 279 / 5000) * ((20661625000 * dv + 134045457) / 50000000000) := by
    unfold oddB11pLowerLittleFGeometrySlope
    ring
  have step : (dv - 279 / 5000) *
      ((20661625000 * dv + 134045457) / 50000000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hdvU]) slope
  nlinarith only [tel, step]

private def oddB11pLowerDvGeometrySlope (dv : ℝ) : ℝ :=
  -(229278583485000 * dv - 3620081772667) / 2000000000000000

private theorem oddB11pLowerDvGeometry_upper_raw
    (dv : ℝ) (hdvL : (111 / 2000 : ℝ) ≤ dv) :
    oddB11pLowerDvGeometrySlope dv ≤ (-9 / 2000 : ℝ) := by
  have slope : (-45855716697 / 400000000000 : ℝ) ≤ 0 := by norm_num
  have tel :
      oddB11pLowerDvGeometrySlope dv - (-18209759221501 / 4000000000000000 : ℝ) =
        (dv - 111 / 2000) * (-45855716697 / 400000000000) := by
    unfold oddB11pLowerDvGeometrySlope
    ring
  have step : (dv - 111 / 2000) * (-45855716697 / 400000000000) ≤ (0 : ℝ) :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith only [hdvL]) slope
  nlinarith only [tel, step]


set_option maxHeartbeats 3000000 in
private theorem oddB11p_lower_geometry_telescope
    (X R C D F a x r c d f sv dv v4 q33 h33 : ℝ) :
    oddB11pCore X R C D F a x r c d f sv dv v4 q33 h33 -
        oddB11pEndpointValue oddB11pLowerEndpoint =
      (q33 - oddB11pLowerEndpoint.q33Value) *
          oddB11pLowerQ33GeometrySlope X R C D F a x r c d f +
        (h33 - oddB11pLowerEndpoint.h33Value) *
          oddB11pLowerH33GeometrySlope X R C D F a x r c d f +
        (sv - oddB11pLowerEndpoint.svValue) *
          oddB11pLowerSvGeometrySlope X R C D F x r c d f sv dv v4 +
        (v4 - oddB11pLowerEndpoint.v4Value) *
          oddB11pLowerV4GeometrySlope X R C D a x r c d dv v4 +
        (X - oddB11pLowerEndpoint.bigX) *
          oddB11pLowerXGeometrySlope X R D F x r d f dv +
        (R - oddB11pLowerEndpoint.bigR) *
          oddB11pLowerRGeometrySlope R C D x r c d dv +
        (C - oddB11pLowerEndpoint.bigC) *
          oddB11pLowerCGeometrySlope F a r f +
        (D - oddB11pLowerEndpoint.bigD) *
          oddB11pLowerDGeometrySlope D a x r d dv +
        (F - oddB11pLowerEndpoint.bigF) *
          oddB11pLowerFGeometrySlope a x c dv +
        (a - oddB11pLowerEndpoint.littleA) *
          oddB11pLowerAGeometrySlope c d f dv +
        (x - oddB11pLowerEndpoint.littleX) *
          oddB11pLowerLittleXGeometrySlope x r d f dv +
        (r - oddB11pLowerEndpoint.littleR) *
          oddB11pLowerLittleRGeometrySlope r c d dv +
        (c - oddB11pLowerEndpoint.littleC) *
          oddB11pLowerLittleCGeometrySlope f +
        (d - oddB11pLowerEndpoint.littleD) *
          oddB11pLowerLittleDGeometrySlope d dv +
        (f - oddB11pLowerEndpoint.littleF) *
          oddB11pLowerLittleFGeometrySlope dv +
        (dv - oddB11pLowerEndpoint.dvValue) *
          oddB11pLowerDvGeometrySlope dv := by
  unfold oddB11pEndpointValue oddB11pLowerEndpoint oddB11pCore oddB11p
    oddGx oddGp oddM11 oddB11pLowerQ33GeometrySlope
    oddB11pLowerH33GeometrySlope oddB11pLowerSvGeometrySlope
    oddB11pLowerV4GeometrySlope oddB11pLowerXGeometrySlope
    oddB11pLowerRGeometrySlope oddB11pLowerCGeometrySlope
    oddB11pLowerDGeometrySlope oddB11pLowerFGeometrySlope
    oddB11pLowerAGeometrySlope oddB11pLowerLittleXGeometrySlope
    oddB11pLowerLittleRGeometrySlope oddB11pLowerLittleCGeometrySlope
    oddB11pLowerLittleDGeometrySlope oddB11pLowerLittleFGeometrySlope
    oddB11pLowerDvGeometrySlope alignedMixedDeterminant
    alignedMixedAdjugatePair alignedEntry00 alignedEntry02 alignedEntry04
    alignedEntry22 alignedEntry24 mixedDeterminantOne
  dsimp only
  ring
private theorem oddB11pLowerEndpointValue_exact :
    oddB11pEndpointValue oddB11pLowerEndpoint =
      (11003233958044303 / 100000000000000000000 : ℝ) := by
  norm_num [oddB11pEndpointValue, oddB11pLowerEndpoint, oddB11pCore,
    oddB11p, oddGx, oddGp, oddM11, alignedDeterminant,
    alignedMixedDeterminant, alignedAdjugatePair, alignedMixedAdjugatePair,
    alignedEntry00, alignedEntry02, alignedEntry04, alignedEntry22,
    alignedEntry24, mixedDeterminantOne]

private theorem oddB11pLowerEndpointValue_lower :
    (108 / 1000000 : ℝ) ≤
      oddB11pEndpointValue oddB11pLowerEndpoint := by
  rw [oddB11pLowerEndpointValue_exact]
  norm_num

set_option maxHeartbeats 3000000 in
private theorem oddB11p_lower_bound
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (108 / 1000000 : ℝ) ≤
      oddB11pCore X R C D F a x r c d f sv dv v4 q33 h33 := by
  rcases hbox.X_mem with ⟨hXL, hXU⟩
  rcases hbox.R_mem with ⟨hRL, hRU⟩
  rcases hbox.C_mem with ⟨hCL, hCU⟩
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.F_mem with ⟨hFL, hFU⟩
  rcases hbox.a_mem with ⟨haL, haU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  rcases hbox.sv_mem with ⟨hsvL, hsvU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  rcases hbox.v4_mem with ⟨hv4L, hv4U⟩
  rcases hbox.q33_mem with ⟨hq33L, hq33U⟩
  rcases hbox.h33_mem with ⟨hh33L, hh33U⟩
  norm_num at hXL hXU hRL hRU hCL hCU hDL hDU hFL hFU
  norm_num at haL haU hxL hxU hrL hrU hcL hcU hdL hdU hfL hfU
  norm_num at hsvL hsvU hdvL hdvU hv4L hv4U hq33L hq33U hh33L hh33U
  have hsQ33 : (9 / 10000 : ℝ) ≤
      oddB11pLowerQ33GeometrySlope X R C D F a x r c d f := by
    apply oddB11pLowerQ33Geometry_lower_raw <;> norm_num <;> assumption
  have hsH33 : (3 / 5000 : ℝ) ≤
      oddB11pLowerH33GeometrySlope X R C D F a x r c d f := by
    apply oddB11pLowerH33Geometry_lower_raw <;> norm_num <;> assumption
  have hsSv :
      oddB11pLowerSvGeometrySlope X R C D F x r c d f sv dv v4 ≤
        (-19 / 1000000 : ℝ) := by
    apply oddB11pLowerSvGeometry_upper_raw <;> norm_num <;> assumption
  have hsV4 :
      oddB11pLowerV4GeometrySlope X R C D a x r c d dv v4 ≤
        (-21 / 50000 : ℝ) := by
    apply oddB11pLowerV4Geometry_upper_raw <;> norm_num <;> assumption
  have hsX :
      oddB11pLowerXGeometrySlope X R D F x r d f dv ≤
        (-7 / 1000 : ℝ) := by
    apply oddB11pLowerXGeometry_upper_raw <;> norm_num <;> assumption
  have hsR :
      oddB11pLowerRGeometrySlope R C D x r c d dv ≤
        (-17 / 10000 : ℝ) := by
    apply oddB11pLowerRGeometry_upper_raw <;> norm_num <;> assumption
  have hsC : (87 / 1000 : ℝ) ≤ oddB11pLowerCGeometrySlope F a r f := by
    apply oddB11pLowerCGeometry_lower_raw <;> norm_num <;> assumption
  have hsD :
      oddB11pLowerDGeometrySlope D a x r d dv ≤ (-29 / 1000 : ℝ) := by
    apply oddB11pLowerDGeometry_upper_raw <;> norm_num <;> assumption
  have hsF : (7 / 2000 : ℝ) ≤ oddB11pLowerFGeometrySlope a x c dv := by
    apply oddB11pLowerFGeometry_lower_raw <;> norm_num <;> assumption
  have hsA :
      oddB11pLowerAGeometrySlope c d f dv ≤ (-1 / 10000 : ℝ) := by
    apply oddB11pLowerAGeometry_upper_raw <;> norm_num <;> assumption
  have hsx : (17 / 5000 : ℝ) ≤
      oddB11pLowerLittleXGeometrySlope x r d f dv := by
    apply oddB11pLowerLittleXGeometry_lower_raw <;> norm_num <;> assumption
  have hsr : (3 / 5000 : ℝ) ≤
      oddB11pLowerLittleRGeometrySlope r c d dv := by
    apply oddB11pLowerLittleRGeometry_lower_raw <;> norm_num <;> assumption
  have hsc :
      oddB11pLowerLittleCGeometrySlope f ≤ (-1 / 20 : ℝ) := by
    apply oddB11pLowerLittleCGeometry_upper_raw <;> norm_num <;> assumption
  have hsd : (9 / 500 : ℝ) ≤
      oddB11pLowerLittleDGeometrySlope d dv := by
    apply oddB11pLowerLittleDGeometry_lower_raw <;> norm_num <;> assumption
  have hsf :
      oddB11pLowerLittleFGeometrySlope dv ≤ (-19 / 10000 : ℝ) := by
    apply oddB11pLowerLittleFGeometry_upper_raw <;> norm_num <;> assumption
  have hsDv :
      oddB11pLowerDvGeometrySlope dv ≤ (-9 / 2000 : ℝ) := by
    apply oddB11pLowerDvGeometry_upper_raw <;> norm_num <;> assumption
  have hq33Step : (0 : ℝ) ≤
      (q33 - oddB11pLowerEndpoint.q33Value) *
        oddB11pLowerQ33GeometrySlope X R C D F a x r c d f := by
    exact mul_nonneg (by dsimp [oddB11pLowerEndpoint]; nlinarith only [hq33L])
      (by nlinarith only [hsQ33])
  have hh33Step : (0 : ℝ) ≤
      (h33 - oddB11pLowerEndpoint.h33Value) *
        oddB11pLowerH33GeometrySlope X R C D F a x r c d f := by
    exact mul_nonneg (by dsimp [oddB11pLowerEndpoint]; nlinarith only [hh33L])
      (by nlinarith only [hsH33])
  have hsvStep : (0 : ℝ) ≤
      (sv - oddB11pLowerEndpoint.svValue) *
        oddB11pLowerSvGeometrySlope X R C D F x r c d f sv dv v4 := by
    exact mul_nonneg_of_nonpos_of_nonpos
      (by dsimp [oddB11pLowerEndpoint]; nlinarith only [hsvU])
      (by nlinarith only [hsSv])
  have hv4Step : (0 : ℝ) ≤
      (v4 - oddB11pLowerEndpoint.v4Value) *
        oddB11pLowerV4GeometrySlope X R C D a x r c d dv v4 := by
    exact mul_nonneg_of_nonpos_of_nonpos
      (by dsimp [oddB11pLowerEndpoint]; nlinarith only [hv4U])
      (by nlinarith only [hsV4])
  have hXStep : (0 : ℝ) ≤
      (X - oddB11pLowerEndpoint.bigX) *
        oddB11pLowerXGeometrySlope X R D F x r d f dv := by
    exact mul_nonneg_of_nonpos_of_nonpos
      (by dsimp [oddB11pLowerEndpoint]; nlinarith only [hXU])
      (by nlinarith only [hsX])
  have hRStep : (0 : ℝ) ≤
      (R - oddB11pLowerEndpoint.bigR) *
        oddB11pLowerRGeometrySlope R C D x r c d dv := by
    exact mul_nonneg_of_nonpos_of_nonpos
      (by dsimp [oddB11pLowerEndpoint]; nlinarith only [hRU])
      (by nlinarith only [hsR])
  have hCStep : (0 : ℝ) ≤
      (C - oddB11pLowerEndpoint.bigC) *
        oddB11pLowerCGeometrySlope F a r f := by
    exact mul_nonneg
      (by dsimp [oddB11pLowerEndpoint]; nlinarith only [hCL])
      (by nlinarith only [hsC])
  have hDStep : (0 : ℝ) ≤
      (D - oddB11pLowerEndpoint.bigD) *
        oddB11pLowerDGeometrySlope D a x r d dv := by
    exact mul_nonneg_of_nonpos_of_nonpos
      (by dsimp [oddB11pLowerEndpoint]; nlinarith only [hDU])
      (by nlinarith only [hsD])
  have hFStep : (0 : ℝ) ≤
      (F - oddB11pLowerEndpoint.bigF) *
        oddB11pLowerFGeometrySlope a x c dv := by
    exact mul_nonneg
      (by dsimp [oddB11pLowerEndpoint]; nlinarith only [hFL])
      (by nlinarith only [hsF])
  have haStep : (0 : ℝ) ≤
      (a - oddB11pLowerEndpoint.littleA) *
        oddB11pLowerAGeometrySlope c d f dv := by
    exact mul_nonneg_of_nonpos_of_nonpos
      (by dsimp [oddB11pLowerEndpoint]; nlinarith only [haU])
      (by nlinarith only [hsA])
  have hxStep : (0 : ℝ) ≤
      (x - oddB11pLowerEndpoint.littleX) *
        oddB11pLowerLittleXGeometrySlope x r d f dv := by
    exact mul_nonneg
      (by dsimp [oddB11pLowerEndpoint]; nlinarith only [hxL])
      (by nlinarith only [hsx])
  have hrStep : (0 : ℝ) ≤
      (r - oddB11pLowerEndpoint.littleR) *
        oddB11pLowerLittleRGeometrySlope r c d dv := by
    exact mul_nonneg
      (by dsimp [oddB11pLowerEndpoint]; nlinarith only [hrL])
      (by nlinarith only [hsr])
  have hcStep : (0 : ℝ) ≤
      (c - oddB11pLowerEndpoint.littleC) *
        oddB11pLowerLittleCGeometrySlope f := by
    exact mul_nonneg_of_nonpos_of_nonpos
      (by dsimp [oddB11pLowerEndpoint]; nlinarith only [hcU])
      (by nlinarith only [hsc])
  have hdStep : (0 : ℝ) ≤
      (d - oddB11pLowerEndpoint.littleD) *
        oddB11pLowerLittleDGeometrySlope d dv := by
    exact mul_nonneg
      (by dsimp [oddB11pLowerEndpoint]; nlinarith only [hdL])
      (by nlinarith only [hsd])
  have hfStep : (0 : ℝ) ≤
      (f - oddB11pLowerEndpoint.littleF) *
        oddB11pLowerLittleFGeometrySlope dv := by
    exact mul_nonneg_of_nonpos_of_nonpos
      (by dsimp [oddB11pLowerEndpoint]; nlinarith only [hfU])
      (by nlinarith only [hsf])
  have hdvStep : (0 : ℝ) ≤
      (dv - oddB11pLowerEndpoint.dvValue) *
        oddB11pLowerDvGeometrySlope dv := by
    exact mul_nonneg_of_nonpos_of_nonpos
      (by dsimp [oddB11pLowerEndpoint]; nlinarith only [hdvU])
      (by nlinarith only [hsDv])
  have htel := oddB11p_lower_geometry_telescope
    X R C D F a x r c d f sv dv v4 q33 h33
  have hend := oddB11pLowerEndpointValue_lower
  nlinarith only [htel, hend, hq33Step, hh33Step, hsvStep, hv4Step,
    hXStep, hRStep, hCStep, hDStep, hFStep, haStep, hxStep, hrStep,
    hcStep, hdStep, hfStep, hdvStep]





/-! ### Centered structural norm certificates for the remaining odd faces

The four remaining face slopes are polynomial laws on the correlated box.
Rather than inspect points of that box, we translate every coordinate to its
midpoint and evaluate the resulting polynomial in the following elementary
center-radius algebra.  Its multiplication law is just the identity
`(c + e) (d + f) - cd = cf + de + ef` followed by the triangle inequality.
Thus each certificate below is a structural weighted-l1 enclosure, not a
finite search. -/

private structure StructuralBall where
  value : ℝ
  center : ℝ
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  sound : |value - center| ≤ radius

private def StructuralBall.const (q : ℝ) : StructuralBall where
  value := q
  center := q
  radius := 0
  radius_nonneg := le_rfl
  sound := by simp

private def StructuralBall.deviation
    (value lower upper : ℝ)
    (hlower : lower ≤ value) (hupper : value ≤ upper) : StructuralBall where
  value := value - (lower + upper) / 2
  center := 0
  radius := (upper - lower) / 2
  radius_nonneg := by linarith
  sound := by
    rw [sub_zero, abs_le]
    constructor <;> linarith

private def StructuralBall.deviationOfMem
    {value lower upper : ℝ}
    (hmem : lower ≤ value ∧ value ≤ upper) : StructuralBall :=
  StructuralBall.deviation value lower upper hmem.1 hmem.2

private def StructuralBall.add (p q : StructuralBall) : StructuralBall where
  value := p.value + q.value
  center := p.center + q.center
  radius := p.radius + q.radius
  radius_nonneg := add_nonneg p.radius_nonneg q.radius_nonneg
  sound := by
    rw [show p.value + q.value - (p.center + q.center) =
      (p.value - p.center) + (q.value - q.center) by ring]
    exact le_trans (abs_add_le _ _) (add_le_add p.sound q.sound)

private def StructuralBall.mul (p q : StructuralBall) : StructuralBall where
  value := p.value * q.value
  center := p.center * q.center
  radius := |p.center| * q.radius + |q.center| * p.radius +
    p.radius * q.radius
  radius_nonneg := add_nonneg
    (add_nonneg
      (mul_nonneg (abs_nonneg _) q.radius_nonneg)
      (mul_nonneg (abs_nonneg _) p.radius_nonneg))
    (mul_nonneg p.radius_nonneg q.radius_nonneg)
  sound := by
    have hp0 : 0 ≤ |p.value - p.center| := abs_nonneg _
    have hq0 : 0 ≤ |q.value - q.center| := abs_nonneg _
    have hpc0 : 0 ≤ |p.center| := abs_nonneg _
    have hqc0 : 0 ≤ |q.center| := abs_nonneg _
    have h1 : |p.center| * |q.value - q.center| ≤
        |p.center| * q.radius :=
      mul_le_mul_of_nonneg_left q.sound hpc0
    have h2 : |q.center| * |p.value - p.center| ≤
        |q.center| * p.radius :=
      mul_le_mul_of_nonneg_left p.sound hqc0
    have h3 : |p.value - p.center| * |q.value - q.center| ≤
        p.radius * q.radius :=
      mul_le_mul p.sound q.sound hq0 p.radius_nonneg
    rw [show p.value * q.value - p.center * q.center =
      p.center * (q.value - q.center) +
        q.center * (p.value - p.center) +
          (p.value - p.center) * (q.value - q.center) by ring]
    calc
      |p.center * (q.value - q.center) +
          q.center * (p.value - p.center) +
            (p.value - p.center) * (q.value - q.center)| ≤
          |p.center * (q.value - q.center)| +
            |q.center * (p.value - p.center)| +
              |(p.value - p.center) * (q.value - q.center)| := by
                exact abs_add_three _ _ _
      _ = |p.center| * |q.value - q.center| +
            |q.center| * |p.value - p.center| +
              |p.value - p.center| * |q.value - q.center| := by
            rw [abs_mul, abs_mul, abs_mul]
      _ ≤ |p.center| * q.radius + |q.center| * p.radius +
            p.radius * q.radius := by linarith

private instance structuralBallAdd : Add StructuralBall :=
  ⟨StructuralBall.add⟩
private instance structuralBallMul : Mul StructuralBall :=
  ⟨StructuralBall.mul⟩
private abbrev structuralBallConst := StructuralBall.const

@[simp] private theorem structuralBallConst_value (q : ℝ) :
    (structuralBallConst q).value = q := rfl
@[simp] private theorem structuralBallConst_center (q : ℝ) :
    (structuralBallConst q).center = q := rfl
@[simp] private theorem structuralBallConst_radius (q : ℝ) :
    (structuralBallConst q).radius = 0 := rfl
@[simp] private theorem structuralBallAdd_value (p q : StructuralBall) :
    (p + q).value = p.value + q.value := rfl
@[simp] private theorem structuralBallAdd_center (p q : StructuralBall) :
    (p + q).center = p.center + q.center := rfl
@[simp] private theorem structuralBallAdd_radius (p q : StructuralBall) :
    (p + q).radius = p.radius + q.radius := rfl
@[simp] private theorem structuralBallMul_value (p q : StructuralBall) :
    (p * q).value = p.value * q.value := rfl
@[simp] private theorem structuralBallMul_center (p q : StructuralBall) :
    (p * q).center = p.center * q.center := rfl
@[simp] private theorem structuralBallMul_radius (p q : StructuralBall) :
    (p * q).radius = |p.center| * q.radius + |q.center| * p.radius +
      p.radius * q.radius := rfl

private def oddH33CenteredCertificate (bX bR bC bD bF ba bx br bc bd bf bsu bdu bu4 : StructuralBall) : StructuralBall :=
  ((((structuralBallConst ((138665565705399543 : ℝ) / 2000000000000000000000) + (bX * ((((structuralBallConst ((-8848176585739 : ℝ) / 4000000000000000) + (bX * ((structuralBallConst ((-75238727 : ℝ) / 2000000000) + (structuralBallConst ((-959 : ℝ) / 10000) * bf)) + ((structuralBallConst ((-819 : ℝ) / 10000) * bF) + (bu4 * (structuralBallConst ((57 : ℝ) / 800) + (structuralBallConst ((1 : ℝ) / 4) * bu4))))))) + ((bR * (((structuralBallConst ((-52267109 : ℝ) / 4000000000) + (structuralBallConst ((-3379 : ℝ) / 400000) * bu4)) + ((structuralBallConst ((-959 : ℝ) / 5000) * bd) + (structuralBallConst ((-819 : ℝ) / 5000) * bD))) + (bdu * (structuralBallConst ((-57 : ℝ) / 800) + (structuralBallConst ((-1 : ℝ) / 2) * bu4))))) + (bf * ((structuralBallConst ((279033983 : ℝ) / 80000000000) + (structuralBallConst ((112341 : ℝ) / 400000) * bdu)) + (bsu * (structuralBallConst ((3379 : ℝ) / 400000) + (structuralBallConst ((1 : ℝ) / 2) * bdu))))))) + (((bsu * ((structuralBallConst ((360062581 : ℝ) / 40000000000) + (structuralBallConst ((24557 : ℝ) / 100000) * bdu)) + (structuralBallConst ((27243 : ℝ) / 800000) * bu4))) + (bdu * (structuralBallConst ((4672896999 : ℝ) / 40000000000) + (structuralBallConst ((-118543 : ℝ) / 800000) * bu4)))) + ((bu4 * (structuralBallConst ((2224885933 : ℝ) / 80000000000) + (structuralBallConst ((78501 : ℝ) / 2000000) * bu4))) + (bD * ((structuralBallConst ((-40079509 : ℝ) / 4000000000) + (structuralBallConst ((-959 : ℝ) / 5000) * br)) + ((structuralBallConst ((112341 : ℝ) / 400000) * bu4) + (bsu * (structuralBallConst ((57 : ℝ) / 800) + (structuralBallConst ((1 : ℝ) / 2) * bu4))))))))) + (((bF * ((structuralBallConst ((-147200461 : ℝ) / 16000000000) + (structuralBallConst ((-959 : ℝ) / 5000) * bx)) + ((structuralBallConst ((112341 : ℝ) / 400000) * bdu) + (bsu * (structuralBallConst ((3379 : ℝ) / 400000) + (structuralBallConst ((1 : ℝ) / 2) * bdu)))))) + (bx * ((structuralBallConst ((-21269903 : ℝ) / 1000000000) + (structuralBallConst ((819 : ℝ) / 5000) * bf)) + (bu4 * (structuralBallConst ((57 : ℝ) / 400) + (structuralBallConst ((1 : ℝ) / 2) * bu4)))))) + ((br * ((structuralBallConst ((-21151549 : ℝ) / 4000000000) + (structuralBallConst ((-3379 : ℝ) / 400000) * bu4)) + ((structuralBallConst ((819 : ℝ) / 5000) * bd) + (bdu * (structuralBallConst ((-57 : ℝ) / 800) + (structuralBallConst ((-1 : ℝ) / 2) * bu4)))))) + (bd * ((structuralBallConst ((8818851 : ℝ) / 4000000000) + (structuralBallConst ((112341 : ℝ) / 400000) * bu4)) + (bsu * (structuralBallConst ((57 : ℝ) / 800) + (structuralBallConst ((1 : ℝ) / 2) * bu4)))))))))) + ((bR * ((((structuralBallConst ((-3826626140569 : ℝ) / 8000000000000000) + (structuralBallConst ((962528799 : ℝ) / 200000000000) * bu4)) + ((bR * ((structuralBallConst ((-257896327 : ℝ) / 160000000000) + (structuralBallConst ((-959 : ℝ) / 10000) * bc)) + ((structuralBallConst ((-819 : ℝ) / 10000) * bC) + (bdu * (structuralBallConst ((3379 : ℝ) / 400000) + (structuralBallConst ((1 : ℝ) / 4) * bdu)))))) + (bsu * ((structuralBallConst ((314319897 : ℝ) / 160000000000) + (structuralBallConst ((19497 : ℝ) / 2000000) * bu4)) + (structuralBallConst ((27243 : ℝ) / 800000) * bdu))))) + (((bdu * ((structuralBallConst ((2966708057 : ℝ) / 160000000000) + (structuralBallConst ((-78501 : ℝ) / 2000000) * bu4)) + (structuralBallConst ((118543 : ℝ) / 800000) * bdu))) + (bC * ((structuralBallConst ((-40079509 : ℝ) / 4000000000) + (structuralBallConst ((-959 : ℝ) / 5000) * br)) + ((structuralBallConst ((112341 : ℝ) / 400000) * bu4) + (bsu * (structuralBallConst ((57 : ℝ) / 800) + (structuralBallConst ((1 : ℝ) / 2) * bu4))))))) + ((bD * ((structuralBallConst ((-147200461 : ℝ) / 16000000000) + (structuralBallConst ((-959 : ℝ) / 5000) * bx)) + ((structuralBallConst ((112341 : ℝ) / 400000) * bdu) + (bsu * (structuralBallConst ((3379 : ℝ) / 400000) + (structuralBallConst ((1 : ℝ) / 2) * bdu)))))) + (bx * ((structuralBallConst ((-21151549 : ℝ) / 4000000000) + (structuralBallConst ((-3379 : ℝ) / 400000) * bu4)) + ((structuralBallConst ((819 : ℝ) / 5000) * bd) + (bdu * (structuralBallConst ((-57 : ℝ) / 800) + (structuralBallConst ((-1 : ℝ) / 2) * bu4))))))))) + (((br * ((structuralBallConst ((-112163271 : ℝ) / 80000000000) + (structuralBallConst ((819 : ℝ) / 5000) * bc)) + (bdu * (structuralBallConst ((3379 : ℝ) / 200000) + (structuralBallConst ((1 : ℝ) / 2) * bdu))))) + (bc * ((structuralBallConst ((8818851 : ℝ) / 4000000000) + (structuralBallConst ((112341 : ℝ) / 400000) * bu4)) + (bsu * (structuralBallConst ((57 : ℝ) / 800) + (structuralBallConst ((1 : ℝ) / 2) * bu4)))))) + (bd * ((structuralBallConst ((279033983 : ℝ) / 80000000000) + (structuralBallConst ((112341 : ℝ) / 400000) * bdu)) + (bsu * (structuralBallConst ((3379 : ℝ) / 400000) + (structuralBallConst ((1 : ℝ) / 2) * bdu)))))))) + (bf * ((structuralBallConst ((-9411511371329 : ℝ) / 160000000000000000) + (bsu * ((structuralBallConst ((161957557 : ℝ) / 200000000000) + (structuralBallConst ((-76723 : ℝ) / 2000000) * bdu)) + (structuralBallConst ((5191 : ℝ) / 4000000) * bsu)))) + (bdu * (structuralBallConst ((-4894852049 : ℝ) / 400000000000) + (structuralBallConst ((551093 : ℝ) / 2000000) * bdu))))))) + (((bsu * ((structuralBallConst ((-19235941313573 : ℝ) / 80000000000000000) + (structuralBallConst ((-2503164403 : ℝ) / 3200000000000) * bsu)) + ((structuralBallConst ((1176875007 : ℝ) / 400000000000) * bu4) + (structuralBallConst ((20745923689 : ℝ) / 1600000000000) * bdu)))) + (bdu * ((structuralBallConst ((-165902433122507 : ℝ) / 80000000000000000) + (structuralBallConst ((-336854051963 : ℝ) / 3200000000000) * bdu)) + (structuralBallConst ((-32561363229 : ℝ) / 800000000000) * bu4)))) + ((bu4 * (structuralBallConst ((-100615116819417 : ℝ) / 160000000000000000) + (structuralBallConst ((-22369552701 : ℝ) / 4000000000000) * bu4))) + (bC * (((structuralBallConst ((212071338986907 : ℝ) / 8000000000000000) + (bf * (structuralBallConst ((-2351300249 : ℝ) / 160000000000) + (bsu * (structuralBallConst ((-112341 : ℝ) / 400000) + (structuralBallConst ((-1 : ℝ) / 4) * bsu)))))) + ((bsu * ((structuralBallConst ((-4672896999 : ℝ) / 40000000000) + (structuralBallConst ((-24557 : ℝ) / 200000) * bsu)) + (structuralBallConst ((118543 : ℝ) / 800000) * bu4))) + (bu4 * (structuralBallConst ((-11759363637 : ℝ) / 160000000000) + (structuralBallConst ((-1099851 : ℝ) / 2000000) * bu4))))) + (((bF * ((structuralBallConst ((18053452007 : ℝ) / 160000000000) + (structuralBallConst ((959 : ℝ) / 10000) * ba)) + (bsu * (structuralBallConst ((-112341 : ℝ) / 400000) + (structuralBallConst ((-1 : ℝ) / 4) * bsu))))) + (ba * ((structuralBallConst ((21269903 : ℝ) / 2000000000) + (structuralBallConst ((-819 : ℝ) / 10000) * bf)) + (bu4 * (structuralBallConst ((-57 : ℝ) / 800) + (structuralBallConst ((-1 : ℝ) / 4) * bu4)))))) + (br * ((structuralBallConst ((8818851 : ℝ) / 4000000000) + (structuralBallConst ((819 : ℝ) / 10000) * br)) + ((structuralBallConst ((112341 : ℝ) / 400000) * bu4) + (bsu * (structuralBallConst ((57 : ℝ) / 800) + (structuralBallConst ((1 : ℝ) / 2) * bu4)))))))))))) + ((((bD * ((((structuralBallConst ((-83866734798329 : ℝ) / 8000000000000000) + (structuralBallConst ((1386087783 : ℝ) / 400000000000) * bu4)) + ((bsu * ((structuralBallConst ((7416479923 : ℝ) / 160000000000) + (structuralBallConst ((27243 : ℝ) / 800000) * bsu)) + ((structuralBallConst ((78501 : ℝ) / 2000000) * bu4) + (structuralBallConst ((118543 : ℝ) / 800000) * bdu)))) + (bdu * (structuralBallConst ((-11759363637 : ℝ) / 160000000000) + (structuralBallConst ((-1099851 : ℝ) / 1000000) * bu4))))) + (((bD * ((structuralBallConst ((-18053452007 : ℝ) / 160000000000) + (structuralBallConst ((-959 : ℝ) / 10000) * ba)) + (bsu * (structuralBallConst ((112341 : ℝ) / 400000) + (structuralBallConst ((1 : ℝ) / 4) * bsu))))) + (ba * ((structuralBallConst ((-21151549 : ℝ) / 4000000000) + (structuralBallConst ((-3379 : ℝ) / 400000) * bu4)) + ((structuralBallConst ((819 : ℝ) / 5000) * bd) + (bdu * (structuralBallConst ((-57 : ℝ) / 800) + (structuralBallConst ((-1 : ℝ) / 2) * bu4))))))) + ((bx * ((structuralBallConst ((8818851 : ℝ) / 4000000000) + (structuralBallConst ((819 : ℝ) / 5000) * br)) + ((structuralBallConst ((112341 : ℝ) / 400000) * bu4) + (bsu * (structuralBallConst ((57 : ℝ) / 800) + (structuralBallConst ((1 : ℝ) / 2) * bu4)))))) + (br * ((structuralBallConst ((279033983 : ℝ) / 80000000000) + (structuralBallConst ((112341 : ℝ) / 400000) * bdu)) + (bsu * (structuralBallConst ((3379 : ℝ) / 400000) + (structuralBallConst ((1 : ℝ) / 2) * bdu)))))))) + (bd * (structuralBallConst ((2351300249 : ℝ) / 80000000000) + (bsu * (structuralBallConst ((112341 : ℝ) / 200000) + (structuralBallConst ((1 : ℝ) / 2) * bsu))))))) + (bF * (((structuralBallConst ((212346194722527 : ℝ) / 160000000000000000) + (bsu * ((structuralBallConst ((-962528799 : ℝ) / 200000000000) + (structuralBallConst ((-19497 : ℝ) / 4000000) * bsu)) + (structuralBallConst ((78501 : ℝ) / 2000000) * bdu)))) + ((bdu * (structuralBallConst ((1386087783 : ℝ) / 400000000000) + (structuralBallConst ((-1099851 : ℝ) / 2000000) * bdu))) + (ba * ((structuralBallConst ((112163271 : ℝ) / 160000000000) + (structuralBallConst ((-819 : ℝ) / 10000) * bc)) + (bdu * (structuralBallConst ((-3379 : ℝ) / 400000) + (structuralBallConst ((-1 : ℝ) / 4) * bdu))))))) + ((bx * ((structuralBallConst ((279033983 : ℝ) / 80000000000) + (structuralBallConst ((819 : ℝ) / 10000) * bx)) + ((structuralBallConst ((112341 : ℝ) / 400000) * bdu) + (bsu * (structuralBallConst ((3379 : ℝ) / 400000) + (structuralBallConst ((1 : ℝ) / 2) * bdu)))))) + (bc * (structuralBallConst ((-2351300249 : ℝ) / 160000000000) + (bsu * (structuralBallConst ((-112341 : ℝ) / 400000) + (structuralBallConst ((-1 : ℝ) / 4) * bsu))))))))) + ((ba * (((structuralBallConst ((122757907183 : ℝ) / 1600000000000000) + (bf * (structuralBallConst ((-52542321 : ℝ) / 32000000000) + (bdu * (structuralBallConst ((10137 : ℝ) / 400000) + (structuralBallConst ((3 : ℝ) / 4) * bdu)))))) + ((bdu * ((structuralBallConst ((166398883 : ℝ) / 40000000000) + (structuralBallConst ((10751 : ℝ) / 200000) * bdu)) + (structuralBallConst ((13157 : ℝ) / 800000) * bu4))) + (bu4 * (structuralBallConst ((103634903 : ℝ) / 160000000000) + (structuralBallConst ((5191 : ℝ) / 4000000) * bu4))))) + ((bc * ((structuralBallConst ((-64818717 : ℝ) / 2000000000) + (structuralBallConst ((-1239 : ℝ) / 10000) * bf)) + (bu4 * (structuralBallConst ((171 : ℝ) / 800) + (structuralBallConst ((3 : ℝ) / 4) * bu4))))) + (bd * ((structuralBallConst ((67553259 : ℝ) / 4000000000) + (structuralBallConst ((1239 : ℝ) / 10000) * bd)) + ((structuralBallConst ((10137 : ℝ) / 400000) * bu4) + (bdu * (structuralBallConst ((171 : ℝ) / 800) + (structuralBallConst ((3 : ℝ) / 2) * bu4))))))))) + (bx * (((structuralBallConst ((-4185236083051 : ℝ) / 4000000000000000) + (bf * ((structuralBallConst ((150652707 : ℝ) / 80000000000) + (structuralBallConst ((-337023 : ℝ) / 400000) * bdu)) + (bsu * (structuralBallConst ((-10137 : ℝ) / 400000) + (structuralBallConst ((-3 : ℝ) / 2) * bdu)))))) + ((bsu * ((structuralBallConst ((-166398883 : ℝ) / 40000000000) + (structuralBallConst ((-13157 : ℝ) / 800000) * bu4)) + (structuralBallConst ((-10751 : ℝ) / 100000) * bdu))) + (bdu * (structuralBallConst ((-2650275057 : ℝ) / 40000000000) + (structuralBallConst ((-32943 : ℝ) / 800000) * bu4))))) + (((bu4 * (structuralBallConst ((-1669334667 : ℝ) / 80000000000) + (structuralBallConst ((-76723 : ℝ) / 2000000) * bu4))) + (bx * ((structuralBallConst ((64818717 : ℝ) / 2000000000) + (structuralBallConst ((1239 : ℝ) / 10000) * bf)) + (bu4 * (structuralBallConst ((-171 : ℝ) / 800) + (structuralBallConst ((-3 : ℝ) / 4) * bu4)))))) + ((br * ((structuralBallConst ((67553259 : ℝ) / 4000000000) + (structuralBallConst ((1239 : ℝ) / 5000) * bd)) + ((structuralBallConst ((10137 : ℝ) / 400000) * bu4) + (bdu * (structuralBallConst ((171 : ℝ) / 800) + (structuralBallConst ((3 : ℝ) / 2) * bu4)))))) + (bd * ((structuralBallConst ((-268108341 : ℝ) / 4000000000) + (structuralBallConst ((-337023 : ℝ) / 400000) * bu4)) + (bsu * (structuralBallConst ((-171 : ℝ) / 800) + (structuralBallConst ((-3 : ℝ) / 2) * bu4))))))))))) + (((br * (((structuralBallConst ((-665352169021 : ℝ) / 8000000000000000) + (structuralBallConst ((-161957557 : ℝ) / 200000000000) * bu4)) + ((bsu * ((structuralBallConst ((-103634903 : ℝ) / 160000000000) + (structuralBallConst ((-13157 : ℝ) / 800000) * bdu)) + (structuralBallConst ((-5191 : ℝ) / 2000000) * bu4))) + (bdu * ((structuralBallConst ((-380799543 : ℝ) / 160000000000) + (structuralBallConst ((32943 : ℝ) / 800000) * bdu)) + (structuralBallConst ((76723 : ℝ) / 2000000) * bu4))))) + (((br * ((structuralBallConst ((52542321 : ℝ) / 32000000000) + (structuralBallConst ((1239 : ℝ) / 10000) * bc)) + (bdu * (structuralBallConst ((-10137 : ℝ) / 400000) + (structuralBallConst ((-3 : ℝ) / 4) * bdu))))) + (bc * ((structuralBallConst ((-268108341 : ℝ) / 4000000000) + (structuralBallConst ((-337023 : ℝ) / 400000) * bu4)) + (bsu * (structuralBallConst ((-171 : ℝ) / 800) + (structuralBallConst ((-3 : ℝ) / 2) * bu4)))))) + (bd * ((structuralBallConst ((150652707 : ℝ) / 80000000000) + (structuralBallConst ((-337023 : ℝ) / 400000) * bdu)) + (bsu * (structuralBallConst ((-10137 : ℝ) / 400000) + (structuralBallConst ((-3 : ℝ) / 2) * bdu)))))))) + (bc * ((structuralBallConst ((7912002862703 : ℝ) / 1600000000000000) + (bf * (structuralBallConst ((697886799 : ℝ) / 32000000000) + (bsu * (structuralBallConst ((337023 : ℝ) / 400000) + (structuralBallConst ((3 : ℝ) / 4) * bsu)))))) + ((bsu * ((structuralBallConst ((2650275057 : ℝ) / 40000000000) + (structuralBallConst ((10751 : ℝ) / 200000) * bsu)) + (structuralBallConst ((32943 : ℝ) / 800000) * bu4))) + (bu4 * (structuralBallConst ((16265769963 : ℝ) / 160000000000) + (structuralBallConst ((551093 : ℝ) / 2000000) * bu4))))))) + (bd * (((structuralBallConst ((-5101522599781 : ℝ) / 8000000000000000) + (structuralBallConst ((-4894852049 : ℝ) / 400000000000) * bu4)) + ((bsu * ((structuralBallConst ((-3719468877 : ℝ) / 160000000000) + (structuralBallConst ((-76723 : ℝ) / 2000000) * bu4)) + ((structuralBallConst ((-13157 : ℝ) / 800000) * bsu) + (structuralBallConst ((32943 : ℝ) / 800000) * bdu)))) + (bdu * (structuralBallConst ((16265769963 : ℝ) / 160000000000) + (structuralBallConst ((551093 : ℝ) / 1000000) * bu4))))) + (bd * (structuralBallConst ((-697886799 : ℝ) / 32000000000) + (bsu * (structuralBallConst ((-337023 : ℝ) / 400000) + (structuralBallConst ((-3 : ℝ) / 4) * bsu))))))))))

private def oddQ33CenteredCertificate (bX bR bC bD bF ba bx br bc bd bf bsu bdu bu4 bh11 : StructuralBall) : StructuralBall :=
  ((((structuralBallConst ((1535757288518297531 : ℝ) / 8000000000000000000000) + (structuralBallConst ((1742945742948939 : ℝ) / 1600000000000000000) * bh11)) + ((bX * ((((structuralBallConst ((-2769380541623 : ℝ) / 400000000000000) + (structuralBallConst ((-33868621673 : ℝ) / 800000000000) * bh11)) + ((bX * (((structuralBallConst ((-226180593 : ℝ) / 2000000000) + (structuralBallConst ((-24557 : ℝ) / 100000) * bh11)) + ((bf * (structuralBallConst ((201 : ℝ) / 2500) + (structuralBallConst ((-1 : ℝ) / 2) * bh11))) + (bu4 * (structuralBallConst ((171 : ℝ) / 800) + (structuralBallConst ((3 : ℝ) / 4) * bu4))))) + (bF * (structuralBallConst ((-453 : ℝ) / 1000) + (structuralBallConst ((-1 : ℝ) / 2) * bh11))))) + (bR * (((structuralBallConst ((-30704001 : ℝ) / 800000000) + (structuralBallConst ((-27243 : ℝ) / 400000) * bh11)) + ((structuralBallConst ((-10137 : ℝ) / 400000) * bu4) + (bdu * (structuralBallConst ((-171 : ℝ) / 800) + (structuralBallConst ((-3 : ℝ) / 2) * bu4))))) + ((bD * (structuralBallConst ((-453 : ℝ) / 500) + (structuralBallConst (-1 : ℝ) * bh11))) + (bd * (structuralBallConst ((201 : ℝ) / 1250) + (structuralBallConst (-1 : ℝ) * bh11)))))))) + (((bf * ((structuralBallConst ((147157789 : ℝ) / 16000000000) + (structuralBallConst ((-112341 : ℝ) / 400000) * bdu)) + ((structuralBallConst ((-889 : ℝ) / 1000000) * bh11) + (bsu * (structuralBallConst ((-3379 : ℝ) / 400000) + (structuralBallConst ((-1 : ℝ) / 2) * bdu)))))) + (bsu * ((structuralBallConst ((553726279 : ℝ) / 40000000000) + (structuralBallConst ((38363 : ℝ) / 100000) * bdu)) + (structuralBallConst ((41329 : ℝ) / 800000) * bu4)))) + ((bdu * (structuralBallConst ((6695518941 : ℝ) / 40000000000) + (structuralBallConst ((-270029 : ℝ) / 800000) * bu4))) + (bu4 * (structuralBallConst ((2780437199 : ℝ) / 80000000000) + (structuralBallConst ((80279 : ℝ) / 2000000) * bu4)))))) + ((((bD * (((structuralBallConst ((-73089321 : ℝ) / 800000000) + (structuralBallConst ((-118543 : ℝ) / 400000) * bh11)) + ((structuralBallConst ((337023 : ℝ) / 400000) * bu4) + (bsu * (structuralBallConst ((171 : ℝ) / 800) + (structuralBallConst ((3 : ℝ) / 2) * bu4))))) + (br * (structuralBallConst ((201 : ℝ) / 1250) + (structuralBallConst (-1 : ℝ) * bh11))))) + (bF * (((structuralBallConst ((-1239092499 : ℝ) / 80000000000) + (structuralBallConst ((-78501 : ℝ) / 1000000) * bh11)) + ((structuralBallConst ((337023 : ℝ) / 400000) * bdu) + (bsu * (structuralBallConst ((10137 : ℝ) / 400000) + (structuralBallConst ((3 : ℝ) / 2) * bdu))))) + (bx * (structuralBallConst ((201 : ℝ) / 1250) + (structuralBallConst (-1 : ℝ) * bh11)))))) + ((bx * ((structuralBallConst ((74824547 : ℝ) / 1000000000) + (structuralBallConst ((-6903 : ℝ) / 50000) * bh11)) + ((bf * (structuralBallConst ((487 : ℝ) / 2500) + bh11)) + (bu4 * (structuralBallConst ((-57 : ℝ) / 400) + (structuralBallConst ((-1 : ℝ) / 2) * bu4)))))) + (br * (((structuralBallConst ((52055819 : ℝ) / 4000000000) + (structuralBallConst ((-7043 : ℝ) / 400000) * bh11)) + ((structuralBallConst ((3379 : ℝ) / 400000) * bu4) + (bdu * (structuralBallConst ((57 : ℝ) / 800) + (structuralBallConst ((1 : ℝ) / 2) * bu4))))) + (bd * (structuralBallConst ((487 : ℝ) / 2500) + bh11)))))) + (bd * ((structuralBallConst ((37807219 : ℝ) / 4000000000) + (structuralBallConst ((-112341 : ℝ) / 400000) * bu4)) + ((structuralBallConst ((-75743 : ℝ) / 400000) * bh11) + (bsu * (structuralBallConst ((-57 : ℝ) / 800) + (structuralBallConst ((-1 : ℝ) / 2) * bu4))))))))) + (bR * ((((structuralBallConst ((-12727358569831 : ℝ) / 8000000000000000) + (structuralBallConst ((-1700896407 : ℝ) / 200000000000) * bh11)) + ((structuralBallConst ((1763100041 : ℝ) / 200000000000) * bu4) + (bR * (((structuralBallConst ((-852146469 : ℝ) / 160000000000) + (structuralBallConst ((-19497 : ℝ) / 2000000) * bh11)) + ((bdu * (structuralBallConst ((10137 : ℝ) / 400000) + (structuralBallConst ((3 : ℝ) / 4) * bdu))) + (bC * (structuralBallConst ((-453 : ℝ) / 1000) + (structuralBallConst ((-1 : ℝ) / 2) * bh11))))) + (bc * (structuralBallConst ((201 : ℝ) / 2500) + (structuralBallConst ((-1 : ℝ) / 2) * bh11))))))) + (((bsu * ((structuralBallConst ((525004891 : ℝ) / 160000000000) + (structuralBallConst ((33803 : ℝ) / 2000000) * bu4)) + (structuralBallConst ((41329 : ℝ) / 800000) * bdu))) + (bdu * ((structuralBallConst ((5552616571 : ℝ) / 160000000000) + (structuralBallConst ((-80279 : ℝ) / 2000000) * bu4)) + (structuralBallConst ((270029 : ℝ) / 800000) * bdu)))) + ((bC * (((structuralBallConst ((-73089321 : ℝ) / 800000000) + (structuralBallConst ((-118543 : ℝ) / 400000) * bh11)) + ((structuralBallConst ((337023 : ℝ) / 400000) * bu4) + (bsu * (structuralBallConst ((171 : ℝ) / 800) + (structuralBallConst ((3 : ℝ) / 2) * bu4))))) + (br * (structuralBallConst ((201 : ℝ) / 1250) + (structuralBallConst (-1 : ℝ) * bh11))))) + (bD * (((structuralBallConst ((-1239092499 : ℝ) / 80000000000) + (structuralBallConst ((-78501 : ℝ) / 1000000) * bh11)) + ((structuralBallConst ((337023 : ℝ) / 400000) * bdu) + (bsu * (structuralBallConst ((10137 : ℝ) / 400000) + (structuralBallConst ((3 : ℝ) / 2) * bdu))))) + (bx * (structuralBallConst ((201 : ℝ) / 1250) + (structuralBallConst (-1 : ℝ) * bh11)))))))) + (((bx * (((structuralBallConst ((52055819 : ℝ) / 4000000000) + (structuralBallConst ((-7043 : ℝ) / 400000) * bh11)) + ((structuralBallConst ((3379 : ℝ) / 400000) * bu4) + (bdu * (structuralBallConst ((57 : ℝ) / 800) + (structuralBallConst ((1 : ℝ) / 2) * bu4))))) + (bd * (structuralBallConst ((487 : ℝ) / 2500) + bh11)))) + (br * ((structuralBallConst ((256179607 : ℝ) / 80000000000) + (structuralBallConst ((-7153 : ℝ) / 1000000) * bh11)) + ((bdu * (structuralBallConst ((-3379 : ℝ) / 200000) + (structuralBallConst ((-1 : ℝ) / 2) * bdu))) + (bc * (structuralBallConst ((487 : ℝ) / 2500) + bh11)))))) + ((bc * ((structuralBallConst ((37807219 : ℝ) / 4000000000) + (structuralBallConst ((-112341 : ℝ) / 400000) * bu4)) + ((structuralBallConst ((-75743 : ℝ) / 400000) * bh11) + (bsu * (structuralBallConst ((-57 : ℝ) / 800) + (structuralBallConst ((-1 : ℝ) / 2) * bu4)))))) + (bd * ((structuralBallConst ((147157789 : ℝ) / 16000000000) + (structuralBallConst ((-112341 : ℝ) / 400000) * bdu)) + ((structuralBallConst ((-889 : ℝ) / 1000000) * bh11) + (bsu * (structuralBallConst ((-3379 : ℝ) / 400000) + (structuralBallConst ((-1 : ℝ) / 2) * bdu)))))))))))) + (((bf * ((structuralBallConst ((-213126996188847 : ℝ) / 160000000000000000) + (structuralBallConst ((-3253339443 : ℝ) / 2000000000000) * bh11)) + ((bsu * ((structuralBallConst ((962528799 : ℝ) / 200000000000) + (structuralBallConst ((-78501 : ℝ) / 2000000) * bdu)) + (structuralBallConst ((19497 : ℝ) / 4000000) * bsu))) + (bdu * (structuralBallConst ((-1386087783 : ℝ) / 400000000000) + (structuralBallConst ((1099851 : ℝ) / 2000000) * bdu)))))) + (bsu * ((structuralBallConst ((-29389485735331 : ℝ) / 80000000000000000) + (structuralBallConst ((-3587195001 : ℝ) / 3200000000000) * bsu)) + ((structuralBallConst ((1724925913 : ℝ) / 400000000000) * bu4) + (structuralBallConst ((26276879723 : ℝ) / 1600000000000) * bdu))))) + ((bdu * ((structuralBallConst ((-176568895053349 : ℝ) / 80000000000000000) + (structuralBallConst ((-400702478641 : ℝ) / 3200000000000) * bdu)) + (structuralBallConst ((-40425839471 : ℝ) / 800000000000) * bu4))) + (bu4 * (structuralBallConst ((-93530053267643 : ℝ) / 160000000000000000) + (structuralBallConst ((-30218504007 : ℝ) / 4000000000000) * bu4)))))) + ((((bC * (((structuralBallConst ((16669216940503 : ℝ) / 250000000000000) + (structuralBallConst ((565440574971 : ℝ) / 1600000000000) * bh11)) + ((bf * ((structuralBallConst ((-17921750087 : ℝ) / 160000000000) + (structuralBallConst ((274379 : ℝ) / 1000000) * bh11)) + (bsu * (structuralBallConst ((112341 : ℝ) / 400000) + (structuralBallConst ((1 : ℝ) / 4) * bsu))))) + (bsu * ((structuralBallConst ((-6695518941 : ℝ) / 40000000000) + (structuralBallConst ((-38363 : ℝ) / 200000) * bsu)) + (structuralBallConst ((270029 : ℝ) / 800000) * bu4))))) + (((bu4 * (structuralBallConst ((-7252957311 : ℝ) / 160000000000) + (structuralBallConst ((-1648609 : ℝ) / 2000000) * bu4))) + (bF * ((structuralBallConst ((51123817749 : ℝ) / 160000000000) + (structuralBallConst ((1099851 : ℝ) / 1000000) * bh11)) + ((bsu * (structuralBallConst ((-337023 : ℝ) / 400000) + (structuralBallConst ((-3 : ℝ) / 4) * bsu))) + (ba * (structuralBallConst ((-201 : ℝ) / 2500) + (structuralBallConst ((1 : ℝ) / 2) * bh11))))))) + ((ba * ((structuralBallConst ((-74824547 : ℝ) / 2000000000) + (structuralBallConst ((6903 : ℝ) / 100000) * bh11)) + ((bf * (structuralBallConst ((-487 : ℝ) / 5000) + (structuralBallConst ((-1 : ℝ) / 2) * bh11))) + (bu4 * (structuralBallConst ((57 : ℝ) / 800) + (structuralBallConst ((1 : ℝ) / 4) * bu4)))))) + (br * (((structuralBallConst ((37807219 : ℝ) / 4000000000) + (structuralBallConst ((-112341 : ℝ) / 400000) * bu4)) + ((structuralBallConst ((-75743 : ℝ) / 400000) * bh11) + (bsu * (structuralBallConst ((-57 : ℝ) / 800) + (structuralBallConst ((-1 : ℝ) / 2) * bu4))))) + (br * (structuralBallConst ((487 : ℝ) / 5000) + (structuralBallConst ((1 : ℝ) / 2) * bh11))))))))) + (bD * ((((structuralBallConst ((-206056930726491 : ℝ) / 8000000000000000) + (structuralBallConst ((-50896794429 : ℝ) / 400000000000) * bh11)) + ((structuralBallConst ((-2122676483 : ℝ) / 400000000000) * bu4) + (bsu * ((structuralBallConst ((11113490969 : ℝ) / 160000000000) + (structuralBallConst ((41329 : ℝ) / 800000) * bsu)) + ((structuralBallConst ((80279 : ℝ) / 2000000) * bu4) + (structuralBallConst ((270029 : ℝ) / 800000) * bdu)))))) + (((bdu * (structuralBallConst ((-7252957311 : ℝ) / 160000000000) + (structuralBallConst ((-1648609 : ℝ) / 1000000) * bu4))) + (bD * ((structuralBallConst ((-51123817749 : ℝ) / 160000000000) + (structuralBallConst ((-1099851 : ℝ) / 1000000) * bh11)) + ((bsu * (structuralBallConst ((337023 : ℝ) / 400000) + (structuralBallConst ((3 : ℝ) / 4) * bsu))) + (ba * (structuralBallConst ((201 : ℝ) / 2500) + (structuralBallConst ((-1 : ℝ) / 2) * bh11))))))) + ((ba * (((structuralBallConst ((52055819 : ℝ) / 4000000000) + (structuralBallConst ((-7043 : ℝ) / 400000) * bh11)) + ((structuralBallConst ((3379 : ℝ) / 400000) * bu4) + (bdu * (structuralBallConst ((57 : ℝ) / 800) + (structuralBallConst ((1 : ℝ) / 2) * bu4))))) + (bd * (structuralBallConst ((487 : ℝ) / 2500) + bh11)))) + (bx * (((structuralBallConst ((37807219 : ℝ) / 4000000000) + (structuralBallConst ((-112341 : ℝ) / 400000) * bu4)) + ((structuralBallConst ((-75743 : ℝ) / 400000) * bh11) + (bsu * (structuralBallConst ((-57 : ℝ) / 800) + (structuralBallConst ((-1 : ℝ) / 2) * bu4))))) + (br * (structuralBallConst ((487 : ℝ) / 2500) + bh11))))))) + ((br * ((structuralBallConst ((147157789 : ℝ) / 16000000000) + (structuralBallConst ((-112341 : ℝ) / 400000) * bdu)) + ((structuralBallConst ((-889 : ℝ) / 1000000) * bh11) + (bsu * (structuralBallConst ((-3379 : ℝ) / 400000) + (structuralBallConst ((-1 : ℝ) / 2) * bdu)))))) + (bd * ((structuralBallConst ((17921750087 : ℝ) / 80000000000) + (structuralBallConst ((-274379 : ℝ) / 500000) * bh11)) + (bsu * (structuralBallConst ((-112341 : ℝ) / 200000) + (structuralBallConst ((-1 : ℝ) / 2) * bsu))))))))) + ((bF * (((structuralBallConst ((542806555184269 : ℝ) / 160000000000000000) + (structuralBallConst ((29547367797 : ℝ) / 2000000000000) * bh11)) + ((bsu * ((structuralBallConst ((-1763100041 : ℝ) / 200000000000) + (structuralBallConst ((-33803 : ℝ) / 4000000) * bsu)) + (structuralBallConst ((80279 : ℝ) / 2000000) * bdu))) + (bdu * (structuralBallConst ((-2122676483 : ℝ) / 400000000000) + (structuralBallConst ((-1648609 : ℝ) / 2000000) * bdu))))) + (((ba * ((structuralBallConst ((-256179607 : ℝ) / 160000000000) + (structuralBallConst ((7153 : ℝ) / 2000000) * bh11)) + ((bdu * (structuralBallConst ((3379 : ℝ) / 400000) + (structuralBallConst ((1 : ℝ) / 4) * bdu))) + (bc * (structuralBallConst ((-487 : ℝ) / 5000) + (structuralBallConst ((-1 : ℝ) / 2) * bh11)))))) + (bx * (((structuralBallConst ((147157789 : ℝ) / 16000000000) + (structuralBallConst ((-112341 : ℝ) / 400000) * bdu)) + ((structuralBallConst ((-889 : ℝ) / 1000000) * bh11) + (bsu * (structuralBallConst ((-3379 : ℝ) / 400000) + (structuralBallConst ((-1 : ℝ) / 2) * bdu))))) + (bx * (structuralBallConst ((487 : ℝ) / 5000) + (structuralBallConst ((1 : ℝ) / 2) * bh11)))))) + (bc * ((structuralBallConst ((-17921750087 : ℝ) / 160000000000) + (structuralBallConst ((274379 : ℝ) / 1000000) * bh11)) + (bsu * (structuralBallConst ((112341 : ℝ) / 400000) + (structuralBallConst ((1 : ℝ) / 4) * bsu)))))))) + (ba * (((structuralBallConst ((-577807167591 : ℝ) / 4000000000000000) + (structuralBallConst ((-181252509 : ℝ) / 1600000000000) * bh11)) + ((bf * ((structuralBallConst ((-116842551 : ℝ) / 160000000000) + (structuralBallConst ((-19497 : ℝ) / 2000000) * bh11)) + (bdu * (structuralBallConst ((3379 : ℝ) / 400000) + (structuralBallConst ((1 : ℝ) / 4) * bdu))))) + (bdu * ((structuralBallConst ((360062581 : ℝ) / 40000000000) + (structuralBallConst ((24557 : ℝ) / 200000) * bdu)) + (structuralBallConst ((27243 : ℝ) / 800000) * bu4))))) + (((bu4 * (structuralBallConst ((314319897 : ℝ) / 160000000000) + (structuralBallConst ((19497 : ℝ) / 4000000) * bu4))) + (bc * ((structuralBallConst ((-22743323 : ℝ) / 2000000000) + (structuralBallConst ((-24557 : ℝ) / 100000) * bh11)) + ((bf * (structuralBallConst ((201 : ℝ) / 2500) + (structuralBallConst ((-1 : ℝ) / 2) * bh11))) + (bu4 * (structuralBallConst ((57 : ℝ) / 800) + (structuralBallConst ((1 : ℝ) / 4) * bu4))))))) + (bd * (((structuralBallConst ((21968839 : ℝ) / 4000000000) + (structuralBallConst ((3379 : ℝ) / 400000) * bu4)) + ((structuralBallConst ((27243 : ℝ) / 400000) * bh11) + (bdu * (structuralBallConst ((57 : ℝ) / 800) + (structuralBallConst ((1 : ℝ) / 2) * bu4))))) + (bd * (structuralBallConst ((-201 : ℝ) / 2500) + (structuralBallConst ((1 : ℝ) / 2) * bh11)))))))))) + (((bx * ((((structuralBallConst ((2250883721311 : ℝ) / 1000000000000000) + (structuralBallConst ((10357219967 : ℝ) / 800000000000) * bh11)) + ((bf * ((structuralBallConst ((-260193743 : ℝ) / 80000000000) + (structuralBallConst ((-112341 : ℝ) / 400000) * bdu)) + ((structuralBallConst ((78501 : ℝ) / 1000000) * bh11) + (bsu * (structuralBallConst ((-3379 : ℝ) / 400000) + (structuralBallConst ((-1 : ℝ) / 2) * bdu)))))) + (bsu * ((structuralBallConst ((-360062581 : ℝ) / 40000000000) + (structuralBallConst ((-27243 : ℝ) / 800000) * bu4)) + (structuralBallConst ((-24557 : ℝ) / 100000) * bdu))))) + (((bdu * (structuralBallConst ((-4672896999 : ℝ) / 40000000000) + (structuralBallConst ((118543 : ℝ) / 800000) * bu4))) + (bu4 * (structuralBallConst ((-2224885933 : ℝ) / 80000000000) + (structuralBallConst ((-78501 : ℝ) / 2000000) * bu4)))) + ((bx * ((structuralBallConst ((22743323 : ℝ) / 2000000000) + (structuralBallConst ((24557 : ℝ) / 100000) * bh11)) + ((bf * (structuralBallConst ((-201 : ℝ) / 2500) + (structuralBallConst ((1 : ℝ) / 2) * bh11))) + (bu4 * (structuralBallConst ((-57 : ℝ) / 800) + (structuralBallConst ((-1 : ℝ) / 4) * bu4)))))) + (br * (((structuralBallConst ((21968839 : ℝ) / 4000000000) + (structuralBallConst ((3379 : ℝ) / 400000) * bu4)) + ((structuralBallConst ((27243 : ℝ) / 400000) * bh11) + (bdu * (structuralBallConst ((57 : ℝ) / 800) + (structuralBallConst ((1 : ℝ) / 2) * bu4))))) + (bd * (structuralBallConst ((-201 : ℝ) / 1250) + bh11))))))) + (bd * ((structuralBallConst ((-5262561 : ℝ) / 4000000000) + (structuralBallConst ((-112341 : ℝ) / 400000) * bu4)) + ((structuralBallConst ((118543 : ℝ) / 400000) * bh11) + (bsu * (structuralBallConst ((-57 : ℝ) / 800) + (structuralBallConst ((-1 : ℝ) / 2) * bu4)))))))) + (br * (((structuralBallConst ((3856625654209 : ℝ) / 8000000000000000) + (structuralBallConst ((-962528799 : ℝ) / 200000000000) * bu4)) + ((structuralBallConst ((249995947 : ℝ) / 200000000000) * bh11) + (bsu * ((structuralBallConst ((-314319897 : ℝ) / 160000000000) + (structuralBallConst ((-27243 : ℝ) / 800000) * bdu)) + (structuralBallConst ((-19497 : ℝ) / 2000000) * bu4))))) + (((bdu * ((structuralBallConst ((-2966708057 : ℝ) / 160000000000) + (structuralBallConst ((-118543 : ℝ) / 800000) * bdu)) + (structuralBallConst ((78501 : ℝ) / 2000000) * bu4))) + (br * ((structuralBallConst ((116842551 : ℝ) / 160000000000) + (structuralBallConst ((19497 : ℝ) / 2000000) * bh11)) + ((bdu * (structuralBallConst ((-3379 : ℝ) / 400000) + (structuralBallConst ((-1 : ℝ) / 4) * bdu))) + (bc * (structuralBallConst ((-201 : ℝ) / 2500) + (structuralBallConst ((1 : ℝ) / 2) * bh11))))))) + ((bc * ((structuralBallConst ((-5262561 : ℝ) / 4000000000) + (structuralBallConst ((-112341 : ℝ) / 400000) * bu4)) + ((structuralBallConst ((118543 : ℝ) / 400000) * bh11) + (bsu * (structuralBallConst ((-57 : ℝ) / 800) + (structuralBallConst ((-1 : ℝ) / 2) * bu4)))))) + (bd * ((structuralBallConst ((-260193743 : ℝ) / 80000000000) + (structuralBallConst ((-112341 : ℝ) / 400000) * bdu)) + ((structuralBallConst ((78501 : ℝ) / 1000000) * bh11) + (bsu * (structuralBallConst ((-3379 : ℝ) / 400000) + (structuralBallConst ((-1 : ℝ) / 2) * bdu))))))))))) + ((bc * (((structuralBallConst ((-107510636815971 : ℝ) / 4000000000000000) + (structuralBallConst ((-196662309669 : ℝ) / 1600000000000) * bh11)) + ((bf * ((structuralBallConst ((1823371769 : ℝ) / 160000000000) + (structuralBallConst ((-1099851 : ℝ) / 1000000) * bh11)) + (bsu * (structuralBallConst ((112341 : ℝ) / 400000) + (structuralBallConst ((1 : ℝ) / 4) * bsu))))) + (bsu * ((structuralBallConst ((4672896999 : ℝ) / 40000000000) + (structuralBallConst ((-118543 : ℝ) / 800000) * bu4)) + (structuralBallConst ((24557 : ℝ) / 200000) * bsu))))) + (bu4 * (structuralBallConst ((11759363637 : ℝ) / 160000000000) + (structuralBallConst ((1099851 : ℝ) / 2000000) * bu4))))) + (bd * (((structuralBallConst ((84730926383069 : ℝ) / 8000000000000000) + (structuralBallConst ((-1386087783 : ℝ) / 400000000000) * bu4)) + ((structuralBallConst ((14403193079 : ℝ) / 400000000000) * bh11) + (bsu * ((structuralBallConst ((-7416479923 : ℝ) / 160000000000) + (structuralBallConst ((-118543 : ℝ) / 800000) * bdu)) + ((structuralBallConst ((-78501 : ℝ) / 2000000) * bu4) + (structuralBallConst ((-27243 : ℝ) / 800000) * bsu)))))) + ((bdu * (structuralBallConst ((11759363637 : ℝ) / 160000000000) + (structuralBallConst ((1099851 : ℝ) / 1000000) * bu4))) + (bd * ((structuralBallConst ((-1823371769 : ℝ) / 160000000000) + (structuralBallConst ((1099851 : ℝ) / 1000000) * bh11)) + (bsu * (structuralBallConst ((-112341 : ℝ) / 400000) + (structuralBallConst ((-1 : ℝ) / 4) * bsu))))))))))))

private def oddH13CenteredCertificate (bX bR bC bD bF ba bx br bc bd bf bsu bdu bu4 bsv bdv bv4 bh13 : StructuralBall) : StructuralBall :=
  (((((structuralBallConst ((-2972201763503549973 : ℝ) / 16000000000000000000000) + (structuralBallConst ((-125763291904081 : ℝ) / 320000000000000000) * bh13)) + ((structuralBallConst ((19235941313573 : ℝ) / 80000000000000000) * bsv) + (structuralBallConst ((100615116819417 : ℝ) / 160000000000000000) * bv4))) + (((structuralBallConst ((165902433122507 : ℝ) / 80000000000000000) * bdv) + (bX * ((((structuralBallConst ((43539114658761 : ℝ) / 8000000000000000) + (structuralBallConst ((-4672896999 : ℝ) / 40000000000) * bdv)) + ((structuralBallConst ((-2224885933 : ℝ) / 80000000000) * bv4) + (structuralBallConst ((-360062581 : ℝ) / 40000000000) * bsv))) + (((structuralBallConst ((10357219967 : ℝ) / 800000000000) * bh13) + (bX * (((structuralBallConst ((24962887 : ℝ) / 250000000) + (structuralBallConst ((-6903 : ℝ) / 100000) * bh13)) + ((structuralBallConst ((-57 : ℝ) / 800) * bv4) + (bf * (structuralBallConst ((1907 : ℝ) / 10000) + (structuralBallConst ((1 : ℝ) / 2) * bh13))))) + ((bu4 * (structuralBallConst ((3 : ℝ) / 2000) + (structuralBallConst ((-1 : ℝ) / 2) * bv4))) + (bF * (structuralBallConst ((2097 : ℝ) / 10000) + (structuralBallConst ((-1 : ℝ) / 2) * bh13))))))) + ((bR * (((structuralBallConst ((63089011 : ℝ) / 2000000000) + (structuralBallConst ((-7043 : ℝ) / 400000) * bh13)) + ((structuralBallConst ((57 : ℝ) / 800) * bdv) + (structuralBallConst ((3379 : ℝ) / 400000) * bv4))) + (((bdu * (structuralBallConst ((-3 : ℝ) / 2000) + (structuralBallConst ((1 : ℝ) / 2) * bv4))) + (bu4 * (structuralBallConst ((1113 : ℝ) / 40000) + (structuralBallConst ((1 : ℝ) / 2) * bdv)))) + ((bD * (structuralBallConst ((2097 : ℝ) / 5000) + (structuralBallConst (-1 : ℝ) * bh13))) + (bd * (structuralBallConst ((1907 : ℝ) / 5000) + bh13)))))) + (bf * (((structuralBallConst ((-1704953131 : ℝ) / 80000000000) + (structuralBallConst ((-112341 : ℝ) / 400000) * bdv)) + ((structuralBallConst ((-3379 : ℝ) / 400000) * bsv) + (structuralBallConst ((78501 : ℝ) / 1000000) * bh13))) + ((bsu * (structuralBallConst ((-1113 : ℝ) / 40000) + (structuralBallConst ((-1 : ℝ) / 2) * bdv))) + (bdu * (structuralBallConst ((-107651 : ℝ) / 400000) + (structuralBallConst ((-1 : ℝ) / 2) * bsv))))))))) + ((((bsu * ((structuralBallConst ((-54255237 : ℝ) / 4000000000) + (structuralBallConst ((-27243 : ℝ) / 800000) * bv4)) + (structuralBallConst ((-24557 : ℝ) / 100000) * bdv))) + (bdu * ((structuralBallConst ((-663119083 : ℝ) / 5000000000) + (structuralBallConst ((-24557 : ℝ) / 100000) * bsv)) + (structuralBallConst ((118543 : ℝ) / 800000) * bv4)))) + ((bu4 * ((structuralBallConst ((-1575672123 : ℝ) / 160000000000) + (structuralBallConst ((-78501 : ℝ) / 1000000) * bv4)) + ((structuralBallConst ((-27243 : ℝ) / 800000) * bsv) + (structuralBallConst ((118543 : ℝ) / 800000) * bdv)))) + (bD * (((structuralBallConst ((339004897 : ℝ) / 4000000000) + (structuralBallConst ((-112341 : ℝ) / 400000) * bv4)) + ((structuralBallConst ((-75743 : ℝ) / 400000) * bh13) + (structuralBallConst ((-57 : ℝ) / 800) * bsv))) + (((bsu * (structuralBallConst ((3 : ℝ) / 2000) + (structuralBallConst ((-1 : ℝ) / 2) * bv4))) + (bu4 * (structuralBallConst ((-107651 : ℝ) / 400000) + (structuralBallConst ((-1 : ℝ) / 2) * bsv)))) + (br * (structuralBallConst ((1907 : ℝ) / 5000) + bh13))))))) + (((bF * (((structuralBallConst ((901787253 : ℝ) / 80000000000) + (structuralBallConst ((-112341 : ℝ) / 400000) * bdv)) + ((structuralBallConst ((-3379 : ℝ) / 400000) * bsv) + (structuralBallConst ((-889 : ℝ) / 1000000) * bh13))) + (((bsu * (structuralBallConst ((-1113 : ℝ) / 40000) + (structuralBallConst ((-1 : ℝ) / 2) * bdv))) + (bdu * (structuralBallConst ((-107651 : ℝ) / 400000) + (structuralBallConst ((-1 : ℝ) / 2) * bsv)))) + (bx * (structuralBallConst ((1907 : ℝ) / 5000) + bh13))))) + (bx * (((structuralBallConst ((5796883 : ℝ) / 125000000) + (structuralBallConst ((-57 : ℝ) / 400) * bv4)) + ((structuralBallConst ((24557 : ℝ) / 50000) * bh13) + (bf * (structuralBallConst ((-2097 : ℝ) / 5000) + bh13)))) + (bu4 * (structuralBallConst ((3 : ℝ) / 1000) + (structuralBallConst (-1 : ℝ) * bv4)))))) + ((br * (((structuralBallConst ((19391441 : ℝ) / 2000000000) + (structuralBallConst ((57 : ℝ) / 800) * bdv)) + ((structuralBallConst ((3379 : ℝ) / 400000) * bv4) + (structuralBallConst ((27243 : ℝ) / 400000) * bh13))) + (((bdu * (structuralBallConst ((-3 : ℝ) / 2000) + (structuralBallConst ((1 : ℝ) / 2) * bv4))) + (bu4 * (structuralBallConst ((1113 : ℝ) / 40000) + (structuralBallConst ((1 : ℝ) / 2) * bdv)))) + (bd * (structuralBallConst ((-2097 : ℝ) / 5000) + bh13))))) + (bd * (((structuralBallConst ((130719357 : ℝ) / 4000000000) + (structuralBallConst ((-112341 : ℝ) / 400000) * bv4)) + ((structuralBallConst ((-57 : ℝ) / 800) * bsv) + (structuralBallConst ((118543 : ℝ) / 400000) * bh13))) + ((bsu * (structuralBallConst ((3 : ℝ) / 2000) + (structuralBallConst ((-1 : ℝ) / 2) * bv4))) + (bu4 * (structuralBallConst ((-107651 : ℝ) / 400000) + (structuralBallConst ((-1 : ℝ) / 2) * bsv)))))))))))) + ((bR * ((((structuralBallConst ((41811941656331 : ℝ) / 32000000000000000) + (structuralBallConst ((-2966708057 : ℝ) / 160000000000) * bdv)) + ((structuralBallConst ((-962528799 : ℝ) / 200000000000) * bv4) + (structuralBallConst ((-314319897 : ℝ) / 160000000000) * bsv))) + (((structuralBallConst ((249995947 : ℝ) / 200000000000) * bh13) + (bR * (((structuralBallConst ((140045981 : ℝ) / 40000000000) + (structuralBallConst ((-7153 : ℝ) / 2000000) * bh13)) + ((structuralBallConst ((-3379 : ℝ) / 400000) * bdv) + (bdu * (structuralBallConst ((-1113 : ℝ) / 40000) + (structuralBallConst ((-1 : ℝ) / 2) * bdv))))) + ((bC * (structuralBallConst ((2097 : ℝ) / 10000) + (structuralBallConst ((-1 : ℝ) / 2) * bh13))) + (bc * (structuralBallConst ((1907 : ℝ) / 10000) + (structuralBallConst ((1 : ℝ) / 2) * bh13))))))) + ((bsu * ((structuralBallConst ((-29853531 : ℝ) / 16000000000) + (structuralBallConst ((-27243 : ℝ) / 800000) * bdv)) + (structuralBallConst ((-19497 : ℝ) / 2000000) * bv4))) + (bdu * ((structuralBallConst ((-5590343613 : ℝ) / 160000000000) + (structuralBallConst ((-118543 : ℝ) / 400000) * bdv)) + ((structuralBallConst ((-27243 : ℝ) / 800000) * bsv) + (structuralBallConst ((78501 : ℝ) / 2000000) * bv4))))))) + ((((bu4 * ((structuralBallConst ((-1225155417 : ℝ) / 400000000000) + (structuralBallConst ((-19497 : ℝ) / 2000000) * bsv)) + (structuralBallConst ((78501 : ℝ) / 2000000) * bdv))) + (bC * (((structuralBallConst ((339004897 : ℝ) / 4000000000) + (structuralBallConst ((-112341 : ℝ) / 400000) * bv4)) + ((structuralBallConst ((-75743 : ℝ) / 400000) * bh13) + (structuralBallConst ((-57 : ℝ) / 800) * bsv))) + (((bsu * (structuralBallConst ((3 : ℝ) / 2000) + (structuralBallConst ((-1 : ℝ) / 2) * bv4))) + (bu4 * (structuralBallConst ((-107651 : ℝ) / 400000) + (structuralBallConst ((-1 : ℝ) / 2) * bsv)))) + (br * (structuralBallConst ((1907 : ℝ) / 5000) + bh13)))))) + ((bD * (((structuralBallConst ((901787253 : ℝ) / 80000000000) + (structuralBallConst ((-112341 : ℝ) / 400000) * bdv)) + ((structuralBallConst ((-3379 : ℝ) / 400000) * bsv) + (structuralBallConst ((-889 : ℝ) / 1000000) * bh13))) + (((bsu * (structuralBallConst ((-1113 : ℝ) / 40000) + (structuralBallConst ((-1 : ℝ) / 2) * bdv))) + (bdu * (structuralBallConst ((-107651 : ℝ) / 400000) + (structuralBallConst ((-1 : ℝ) / 2) * bsv)))) + (bx * (structuralBallConst ((1907 : ℝ) / 5000) + bh13))))) + (bx * (((structuralBallConst ((19391441 : ℝ) / 2000000000) + (structuralBallConst ((57 : ℝ) / 800) * bdv)) + ((structuralBallConst ((3379 : ℝ) / 400000) * bv4) + (structuralBallConst ((27243 : ℝ) / 400000) * bh13))) + (((bdu * (structuralBallConst ((-3 : ℝ) / 2000) + (structuralBallConst ((1 : ℝ) / 2) * bv4))) + (bu4 * (structuralBallConst ((1113 : ℝ) / 40000) + (structuralBallConst ((1 : ℝ) / 2) * bdv)))) + (bd * (structuralBallConst ((-2097 : ℝ) / 5000) + bh13))))))) + (((br * (((structuralBallConst ((31068229 : ℝ) / 20000000000) + (structuralBallConst ((-3379 : ℝ) / 200000) * bdv)) + ((structuralBallConst ((19497 : ℝ) / 1000000) * bh13) + (bdu * (structuralBallConst ((-1113 : ℝ) / 20000) + (structuralBallConst (-1 : ℝ) * bdv))))) + (bc * (structuralBallConst ((-2097 : ℝ) / 5000) + bh13)))) + (bc * (((structuralBallConst ((130719357 : ℝ) / 4000000000) + (structuralBallConst ((-112341 : ℝ) / 400000) * bv4)) + ((structuralBallConst ((-57 : ℝ) / 800) * bsv) + (structuralBallConst ((118543 : ℝ) / 400000) * bh13))) + ((bsu * (structuralBallConst ((3 : ℝ) / 2000) + (structuralBallConst ((-1 : ℝ) / 2) * bv4))) + (bu4 * (structuralBallConst ((-107651 : ℝ) / 400000) + (structuralBallConst ((-1 : ℝ) / 2) * bsv))))))) + (bd * (((structuralBallConst ((-1704953131 : ℝ) / 80000000000) + (structuralBallConst ((-112341 : ℝ) / 400000) * bdv)) + ((structuralBallConst ((-3379 : ℝ) / 400000) * bsv) + (structuralBallConst ((78501 : ℝ) / 1000000) * bh13))) + ((bsu * (structuralBallConst ((-1113 : ℝ) / 40000) + (structuralBallConst ((-1 : ℝ) / 2) * bdv))) + (bdu * (structuralBallConst ((-107651 : ℝ) / 400000) + (structuralBallConst ((-1 : ℝ) / 2) * bsv)))))))))) + (bf * (((structuralBallConst ((20815280616761 : ℝ) / 20000000000000000) + (structuralBallConst ((-3038347521 : ℝ) / 400000000000) * bh13)) + ((structuralBallConst ((-161957557 : ℝ) / 200000000000) * bsv) + (structuralBallConst ((4894852049 : ℝ) / 400000000000) * bdv))) + ((bsu * ((structuralBallConst ((295110649 : ℝ) / 400000000000) + (structuralBallConst ((-5191 : ℝ) / 2000000) * bsv)) + (structuralBallConst ((76723 : ℝ) / 2000000) * bdv))) + (bdu * ((structuralBallConst ((-4008022507 : ℝ) / 400000000000) + (structuralBallConst ((-551093 : ℝ) / 1000000) * bdv)) + (structuralBallConst ((76723 : ℝ) / 2000000) * bsv))))))))) + ((((bsu * ((structuralBallConst ((41390520505583 : ℝ) / 320000000000000000) + (structuralBallConst ((-20745923689 : ℝ) / 1600000000000) * bdv)) + ((structuralBallConst ((-1176875007 : ℝ) / 400000000000) * bv4) + (structuralBallConst ((2503164403 : ℝ) / 1600000000000) * bsv)))) + (bdu * ((structuralBallConst ((1476792531428851 : ℝ) / 320000000000000000) + (structuralBallConst ((-20745923689 : ℝ) / 1600000000000) * bsv)) + ((structuralBallConst ((32561363229 : ℝ) / 800000000000) * bv4) + (structuralBallConst ((336854051963 : ℝ) / 1600000000000) * bdv))))) + ((bu4 * ((structuralBallConst ((12956967166677 : ℝ) / 20000000000000000) + (structuralBallConst ((-1176875007 : ℝ) / 400000000000) * bsv)) + ((structuralBallConst ((22369552701 : ℝ) / 2000000000000) * bv4) + (structuralBallConst ((32561363229 : ℝ) / 800000000000) * bdv)))) + (bC * ((((structuralBallConst ((-153012745344897 : ℝ) / 2000000000000000) + (structuralBallConst ((-196662309669 : ℝ) / 1600000000000) * bh13)) + ((structuralBallConst ((4672896999 : ℝ) / 40000000000) * bsv) + (structuralBallConst ((11759363637 : ℝ) / 160000000000) * bv4))) + (((bf * ((structuralBallConst ((4976486383 : ℝ) / 80000000000) + (structuralBallConst ((-1099851 : ℝ) / 1000000) * bh13)) + ((structuralBallConst ((112341 : ℝ) / 400000) * bsv) + (bsu * (structuralBallConst ((107651 : ℝ) / 400000) + (structuralBallConst ((1 : ℝ) / 2) * bsv)))))) + (bsu * ((structuralBallConst ((663119083 : ℝ) / 5000000000) + (structuralBallConst ((-118543 : ℝ) / 800000) * bv4)) + (structuralBallConst ((24557 : ℝ) / 100000) * bsv)))) + ((bu4 * ((structuralBallConst ((-13289200973 : ℝ) / 160000000000) + (structuralBallConst ((-118543 : ℝ) / 800000) * bsv)) + (structuralBallConst ((1099851 : ℝ) / 1000000) * bv4))) + (bF * (((structuralBallConst ((-23553862321 : ℝ) / 80000000000) + (structuralBallConst ((112341 : ℝ) / 400000) * bsv)) + ((structuralBallConst ((274379 : ℝ) / 1000000) * bh13) + (bsu * (structuralBallConst ((107651 : ℝ) / 400000) + (structuralBallConst ((1 : ℝ) / 2) * bsv))))) + (ba * (structuralBallConst ((-1907 : ℝ) / 10000) + (structuralBallConst ((-1 : ℝ) / 2) * bh13)))))))) + ((ba * (((structuralBallConst ((-5796883 : ℝ) / 250000000) + (structuralBallConst ((-24557 : ℝ) / 100000) * bh13)) + ((structuralBallConst ((57 : ℝ) / 800) * bv4) + (bf * (structuralBallConst ((2097 : ℝ) / 10000) + (structuralBallConst ((-1 : ℝ) / 2) * bh13))))) + (bu4 * (structuralBallConst ((-3 : ℝ) / 2000) + (structuralBallConst ((1 : ℝ) / 2) * bv4))))) + (br * (((structuralBallConst ((130719357 : ℝ) / 4000000000) + (structuralBallConst ((-112341 : ℝ) / 400000) * bv4)) + ((structuralBallConst ((-57 : ℝ) / 800) * bsv) + (structuralBallConst ((118543 : ℝ) / 400000) * bh13))) + (((bsu * (structuralBallConst ((3 : ℝ) / 2000) + (structuralBallConst ((-1 : ℝ) / 2) * bv4))) + (bu4 * (structuralBallConst ((-107651 : ℝ) / 400000) + (structuralBallConst ((-1 : ℝ) / 2) * bsv)))) + (br * (structuralBallConst ((-2097 : ℝ) / 10000) + (structuralBallConst ((1 : ℝ) / 2) * bh13))))))))))) + (((bD * ((((structuralBallConst ((188251232765301 : ℝ) / 6400000000000000) + (structuralBallConst ((-7416479923 : ℝ) / 160000000000) * bsv)) + ((structuralBallConst ((-1386087783 : ℝ) / 400000000000) * bv4) + (structuralBallConst ((11759363637 : ℝ) / 160000000000) * bdv))) + (((structuralBallConst ((14403193079 : ℝ) / 400000000000) * bh13) + (bsu * ((structuralBallConst ((-895751967 : ℝ) / 20000000000) + (structuralBallConst ((-118543 : ℝ) / 800000) * bdv)) + ((structuralBallConst ((-78501 : ℝ) / 2000000) * bv4) + (structuralBallConst ((-27243 : ℝ) / 400000) * bsv))))) + ((bdu * ((structuralBallConst ((-13289200973 : ℝ) / 160000000000) + (structuralBallConst ((-118543 : ℝ) / 800000) * bsv)) + (structuralBallConst ((1099851 : ℝ) / 1000000) * bv4))) + (bu4 * ((structuralBallConst ((16031972109 : ℝ) / 400000000000) + (structuralBallConst ((-78501 : ℝ) / 2000000) * bsv)) + (structuralBallConst ((1099851 : ℝ) / 1000000) * bdv)))))) + ((((bD * (((structuralBallConst ((23553862321 : ℝ) / 80000000000) + (structuralBallConst ((-274379 : ℝ) / 1000000) * bh13)) + ((structuralBallConst ((-112341 : ℝ) / 400000) * bsv) + (bsu * (structuralBallConst ((-107651 : ℝ) / 400000) + (structuralBallConst ((-1 : ℝ) / 2) * bsv))))) + (ba * (structuralBallConst ((1907 : ℝ) / 10000) + (structuralBallConst ((1 : ℝ) / 2) * bh13))))) + (ba * (((structuralBallConst ((19391441 : ℝ) / 2000000000) + (structuralBallConst ((57 : ℝ) / 800) * bdv)) + ((structuralBallConst ((3379 : ℝ) / 400000) * bv4) + (structuralBallConst ((27243 : ℝ) / 400000) * bh13))) + (((bdu * (structuralBallConst ((-3 : ℝ) / 2000) + (structuralBallConst ((1 : ℝ) / 2) * bv4))) + (bu4 * (structuralBallConst ((1113 : ℝ) / 40000) + (structuralBallConst ((1 : ℝ) / 2) * bdv)))) + (bd * (structuralBallConst ((-2097 : ℝ) / 5000) + bh13)))))) + ((bx * (((structuralBallConst ((130719357 : ℝ) / 4000000000) + (structuralBallConst ((-112341 : ℝ) / 400000) * bv4)) + ((structuralBallConst ((-57 : ℝ) / 800) * bsv) + (structuralBallConst ((118543 : ℝ) / 400000) * bh13))) + (((bsu * (structuralBallConst ((3 : ℝ) / 2000) + (structuralBallConst ((-1 : ℝ) / 2) * bv4))) + (bu4 * (structuralBallConst ((-107651 : ℝ) / 400000) + (structuralBallConst ((-1 : ℝ) / 2) * bsv)))) + (br * (structuralBallConst ((-2097 : ℝ) / 5000) + bh13))))) + (br * (((structuralBallConst ((-1704953131 : ℝ) / 80000000000) + (structuralBallConst ((-112341 : ℝ) / 400000) * bdv)) + ((structuralBallConst ((-3379 : ℝ) / 400000) * bsv) + (structuralBallConst ((78501 : ℝ) / 1000000) * bh13))) + ((bsu * (structuralBallConst ((-1113 : ℝ) / 40000) + (structuralBallConst ((-1 : ℝ) / 2) * bdv))) + (bdu * (structuralBallConst ((-107651 : ℝ) / 400000) + (structuralBallConst ((-1 : ℝ) / 2) * bsv)))))))) + (bd * ((structuralBallConst ((-4976486383 : ℝ) / 40000000000) + (structuralBallConst ((-112341 : ℝ) / 200000) * bsv)) + ((structuralBallConst ((1099851 : ℝ) / 500000) * bh13) + (bsu * (structuralBallConst ((-107651 : ℝ) / 200000) + (structuralBallConst (-1 : ℝ) * bsv))))))))) + (bF * ((((structuralBallConst ((-69737721550641 : ℝ) / 20000000000000000) + (structuralBallConst ((-3253339443 : ℝ) / 2000000000000) * bh13)) + ((structuralBallConst ((-1386087783 : ℝ) / 400000000000) * bdv) + (structuralBallConst ((962528799 : ℝ) / 200000000000) * bsv))) + (((bsu * ((structuralBallConst ((1225155417 : ℝ) / 400000000000) + (structuralBallConst ((-78501 : ℝ) / 2000000) * bdv)) + (structuralBallConst ((19497 : ℝ) / 2000000) * bsv))) + (bdu * ((structuralBallConst ((16031972109 : ℝ) / 400000000000) + (structuralBallConst ((-78501 : ℝ) / 2000000) * bsv)) + (structuralBallConst ((1099851 : ℝ) / 1000000) * bdv)))) + ((ba * (((structuralBallConst ((-31068229 : ℝ) / 40000000000) + (structuralBallConst ((-19497 : ℝ) / 2000000) * bh13)) + ((structuralBallConst ((3379 : ℝ) / 400000) * bdv) + (bdu * (structuralBallConst ((1113 : ℝ) / 40000) + (structuralBallConst ((1 : ℝ) / 2) * bdv))))) + (bc * (structuralBallConst ((2097 : ℝ) / 10000) + (structuralBallConst ((-1 : ℝ) / 2) * bh13))))) + (bx * (((structuralBallConst ((-1704953131 : ℝ) / 80000000000) + (structuralBallConst ((-112341 : ℝ) / 400000) * bdv)) + ((structuralBallConst ((-3379 : ℝ) / 400000) * bsv) + (structuralBallConst ((78501 : ℝ) / 1000000) * bh13))) + (((bsu * (structuralBallConst ((-1113 : ℝ) / 40000) + (structuralBallConst ((-1 : ℝ) / 2) * bdv))) + (bdu * (structuralBallConst ((-107651 : ℝ) / 400000) + (structuralBallConst ((-1 : ℝ) / 2) * bsv)))) + (bx * (structuralBallConst ((-2097 : ℝ) / 10000) + (structuralBallConst ((1 : ℝ) / 2) * bh13))))))))) + (bc * ((structuralBallConst ((4976486383 : ℝ) / 80000000000) + (structuralBallConst ((-1099851 : ℝ) / 1000000) * bh13)) + ((structuralBallConst ((112341 : ℝ) / 400000) * bsv) + (bsu * (structuralBallConst ((107651 : ℝ) / 400000) + (structuralBallConst ((1 : ℝ) / 2) * bsv))))))))) + ((ba * ((((structuralBallConst ((-1304516632797 : ℝ) / 8000000000000000) + (structuralBallConst ((-355979319 : ℝ) / 320000000000) * bh13)) + ((structuralBallConst ((-166398883 : ℝ) / 40000000000) * bdv) + (structuralBallConst ((-103634903 : ℝ) / 160000000000) * bv4))) + (((bf * ((structuralBallConst ((93056271 : ℝ) / 40000000000) + (structuralBallConst ((-10137 : ℝ) / 400000) * bdv)) + ((structuralBallConst ((3507 : ℝ) / 400000) * bh13) + (bdu * (structuralBallConst ((-3339 : ℝ) / 40000) + (structuralBallConst ((-3 : ℝ) / 2) * bdv)))))) + (bdu * ((structuralBallConst ((-23734371 : ℝ) / 4000000000) + (structuralBallConst ((-13157 : ℝ) / 800000) * bv4)) + (structuralBallConst ((-10751 : ℝ) / 100000) * bdv)))) + ((bu4 * ((structuralBallConst ((-14519157 : ℝ) / 16000000000) + (structuralBallConst ((-13157 : ℝ) / 800000) * bdv)) + (structuralBallConst ((-5191 : ℝ) / 2000000) * bv4))) + (bc * (((structuralBallConst ((2924079 : ℝ) / 31250000) + (structuralBallConst ((-171 : ℝ) / 800) * bv4)) + ((structuralBallConst ((5681 : ℝ) / 20000) * bh13) + (bf * (structuralBallConst ((1527 : ℝ) / 10000) + (structuralBallConst ((5 : ℝ) / 2) * bh13))))) + (bu4 * (structuralBallConst ((9 : ℝ) / 2000) + (structuralBallConst ((-3 : ℝ) / 2) * bv4)))))))) + (bd * (((structuralBallConst ((-75009891 : ℝ) / 2000000000) + (structuralBallConst ((-33357 : ℝ) / 400000) * bh13)) + ((structuralBallConst ((-10137 : ℝ) / 400000) * bv4) + (structuralBallConst ((-171 : ℝ) / 800) * bdv))) + (((bdu * (structuralBallConst ((9 : ℝ) / 2000) + (structuralBallConst ((-3 : ℝ) / 2) * bv4))) + (bu4 * (structuralBallConst ((-3339 : ℝ) / 40000) + (structuralBallConst ((-3 : ℝ) / 2) * bdv)))) + (bd * (structuralBallConst ((-1527 : ℝ) / 10000) + (structuralBallConst ((-5 : ℝ) / 2) * bh13)))))))) + (bx * ((((structuralBallConst ((159641820253 : ℝ) / 320000000000000) + (structuralBallConst ((166398883 : ℝ) / 40000000000) * bsv)) + ((structuralBallConst ((1524645141 : ℝ) / 160000000000) * bh13) + (structuralBallConst ((1669334667 : ℝ) / 80000000000) * bv4))) + (((structuralBallConst ((2650275057 : ℝ) / 40000000000) * bdv) + (bf * (((structuralBallConst ((512473869 : ℝ) / 16000000000) + (structuralBallConst ((-30867 : ℝ) / 200000) * bh13)) + ((structuralBallConst ((10137 : ℝ) / 400000) * bsv) + (structuralBallConst ((337023 : ℝ) / 400000) * bdv))) + ((bsu * (structuralBallConst ((3339 : ℝ) / 40000) + (structuralBallConst ((3 : ℝ) / 2) * bdv))) + (bdu * (structuralBallConst ((322953 : ℝ) / 400000) + (structuralBallConst ((3 : ℝ) / 2) * bsv))))))) + ((bsu * ((structuralBallConst ((23734371 : ℝ) / 4000000000) + (structuralBallConst ((10751 : ℝ) / 100000) * bdv)) + (structuralBallConst ((13157 : ℝ) / 800000) * bv4))) + (bdu * ((structuralBallConst ((144360647 : ℝ) / 2500000000) + (structuralBallConst ((10751 : ℝ) / 100000) * bsv)) + (structuralBallConst ((32943 : ℝ) / 800000) * bv4)))))) + (((bu4 * ((structuralBallConst ((1746192757 : ℝ) / 160000000000) + (structuralBallConst ((13157 : ℝ) / 800000) * bsv)) + ((structuralBallConst ((32943 : ℝ) / 800000) * bdv) + (structuralBallConst ((76723 : ℝ) / 1000000) * bv4)))) + (bx * (((structuralBallConst ((-2924079 : ℝ) / 31250000) + (structuralBallConst ((-5681 : ℝ) / 20000) * bh13)) + ((structuralBallConst ((171 : ℝ) / 800) * bv4) + (bf * (structuralBallConst ((-1527 : ℝ) / 10000) + (structuralBallConst ((-5 : ℝ) / 2) * bh13))))) + (bu4 * (structuralBallConst ((-9 : ℝ) / 2000) + (structuralBallConst ((3 : ℝ) / 2) * bv4)))))) + ((br * (((structuralBallConst ((-75009891 : ℝ) / 2000000000) + (structuralBallConst ((-33357 : ℝ) / 400000) * bh13)) + ((structuralBallConst ((-10137 : ℝ) / 400000) * bv4) + (structuralBallConst ((-171 : ℝ) / 800) * bdv))) + (((bdu * (structuralBallConst ((9 : ℝ) / 2000) + (structuralBallConst ((-3 : ℝ) / 2) * bv4))) + (bu4 * (structuralBallConst ((-3339 : ℝ) / 40000) + (structuralBallConst ((-3 : ℝ) / 2) * bdv)))) + (bd * (structuralBallConst ((-1527 : ℝ) / 5000) + (structuralBallConst (-5 : ℝ) * bh13)))))) + (bd * (((structuralBallConst ((-22676007 : ℝ) / 4000000000) + (structuralBallConst ((-9857 : ℝ) / 400000) * bh13)) + ((structuralBallConst ((171 : ℝ) / 800) * bsv) + (structuralBallConst ((337023 : ℝ) / 400000) * bv4))) + ((bsu * (structuralBallConst ((-9 : ℝ) / 2000) + (structuralBallConst ((3 : ℝ) / 2) * bv4))) + (bu4 * (structuralBallConst ((322953 : ℝ) / 400000) + (structuralBallConst ((3 : ℝ) / 2) * bsv)))))))))))))) + (((br * ((((structuralBallConst ((-536691016961 : ℝ) / 6400000000000000) + (structuralBallConst ((103634903 : ℝ) / 160000000000) * bsv)) + ((structuralBallConst ((161957557 : ℝ) / 200000000000) * bv4) + (structuralBallConst ((380799543 : ℝ) / 160000000000) * bdv))) + (((structuralBallConst ((652853607 : ℝ) / 200000000000) * bh13) + (bsu * ((structuralBallConst ((14519157 : ℝ) / 16000000000) + (structuralBallConst ((5191 : ℝ) / 2000000) * bv4)) + (structuralBallConst ((13157 : ℝ) / 800000) * bdv)))) + ((bdu * ((structuralBallConst ((701466547 : ℝ) / 160000000000) + (structuralBallConst ((-76723 : ℝ) / 2000000) * bv4)) + ((structuralBallConst ((-32943 : ℝ) / 400000) * bdv) + (structuralBallConst ((13157 : ℝ) / 800000) * bsv)))) + (bu4 * ((structuralBallConst ((-295110649 : ℝ) / 400000000000) + (structuralBallConst ((-76723 : ℝ) / 2000000) * bdv)) + (structuralBallConst ((5191 : ℝ) / 2000000) * bsv)))))) + (((br * (((structuralBallConst ((-93056271 : ℝ) / 40000000000) + (structuralBallConst ((-3507 : ℝ) / 400000) * bh13)) + ((structuralBallConst ((10137 : ℝ) / 400000) * bdv) + (bdu * (structuralBallConst ((3339 : ℝ) / 40000) + (structuralBallConst ((3 : ℝ) / 2) * bdv))))) + (bc * (structuralBallConst ((-1527 : ℝ) / 10000) + (structuralBallConst ((-5 : ℝ) / 2) * bh13))))) + (bc * (((structuralBallConst ((-22676007 : ℝ) / 4000000000) + (structuralBallConst ((-9857 : ℝ) / 400000) * bh13)) + ((structuralBallConst ((171 : ℝ) / 800) * bsv) + (structuralBallConst ((337023 : ℝ) / 400000) * bv4))) + ((bsu * (structuralBallConst ((-9 : ℝ) / 2000) + (structuralBallConst ((3 : ℝ) / 2) * bv4))) + (bu4 * (structuralBallConst ((322953 : ℝ) / 400000) + (structuralBallConst ((3 : ℝ) / 2) * bsv))))))) + (bd * (((structuralBallConst ((512473869 : ℝ) / 16000000000) + (structuralBallConst ((-30867 : ℝ) / 200000) * bh13)) + ((structuralBallConst ((10137 : ℝ) / 400000) * bsv) + (structuralBallConst ((337023 : ℝ) / 400000) * bdv))) + ((bsu * (structuralBallConst ((3339 : ℝ) / 40000) + (structuralBallConst ((3 : ℝ) / 2) * bdv))) + (bdu * (structuralBallConst ((322953 : ℝ) / 400000) + (structuralBallConst ((3 : ℝ) / 2) * bsv))))))))) + (bc * (((structuralBallConst ((60569232270703 : ℝ) / 4000000000000000) + (structuralBallConst ((-21653505791 : ℝ) / 320000000000) * bh13)) + ((structuralBallConst ((-16265769963 : ℝ) / 160000000000) * bv4) + (structuralBallConst ((-2650275057 : ℝ) / 40000000000) * bsv))) + (((bf * ((structuralBallConst ((-3142814541 : ℝ) / 80000000000) + (structuralBallConst ((-337023 : ℝ) / 400000) * bsv)) + ((structuralBallConst ((275313 : ℝ) / 200000) * bh13) + (bsu * (structuralBallConst ((-322953 : ℝ) / 400000) + (structuralBallConst ((-3 : ℝ) / 2) * bsv)))))) + (bsu * ((structuralBallConst ((-144360647 : ℝ) / 2500000000) + (structuralBallConst ((-32943 : ℝ) / 800000) * bv4)) + (structuralBallConst ((-10751 : ℝ) / 100000) * bsv)))) + (bu4 * ((structuralBallConst ((-3281822253 : ℝ) / 160000000000) + (structuralBallConst ((-551093 : ℝ) / 1000000) * bv4)) + (structuralBallConst ((-32943 : ℝ) / 800000) * bsv))))))) + (bd * ((((structuralBallConst ((-264794737492631 : ℝ) / 32000000000000000) + (structuralBallConst ((-16265769963 : ℝ) / 160000000000) * bdv)) + ((structuralBallConst ((3719468877 : ℝ) / 160000000000) * bsv) + (structuralBallConst ((4894852049 : ℝ) / 400000000000) * bv4))) + (((structuralBallConst ((14225932029 : ℝ) / 400000000000) * bh13) + (bsu * ((structuralBallConst ((305957413 : ℝ) / 20000000000) + (structuralBallConst ((-32943 : ℝ) / 800000) * bdv)) + ((structuralBallConst ((13157 : ℝ) / 400000) * bsv) + (structuralBallConst ((76723 : ℝ) / 2000000) * bv4))))) + ((bdu * ((structuralBallConst ((-3281822253 : ℝ) / 160000000000) + (structuralBallConst ((-551093 : ℝ) / 1000000) * bv4)) + (structuralBallConst ((-32943 : ℝ) / 800000) * bsv))) + (bu4 * ((structuralBallConst ((-4008022507 : ℝ) / 400000000000) + (structuralBallConst ((-551093 : ℝ) / 1000000) * bdv)) + (structuralBallConst ((76723 : ℝ) / 2000000) * bsv)))))) + (bd * ((structuralBallConst ((3142814541 : ℝ) / 80000000000) + (structuralBallConst ((-275313 : ℝ) / 200000) * bh13)) + ((structuralBallConst ((337023 : ℝ) / 400000) * bsv) + (bsu * (structuralBallConst ((322953 : ℝ) / 400000) + (structuralBallConst ((3 : ℝ) / 2) * bsv))))))))))

private def oddQ13CenteredCertificate (bX bR bC bD bF ba bx br bc bd bf bsu bdu bu4 bsv bdv bv4 bq13 bh13 : StructuralBall) : StructuralBall :=
  (((((structuralBallConst ((-3343609688941652051 : ℝ) / 8000000000000000000000) + (structuralBallConst ((-3031918271628951 : ℝ) / 1600000000000000000) * bq13)) + ((structuralBallConst ((-1742945742948939 : ℝ) / 800000000000000000) * bh13) + (structuralBallConst ((29389485735331 : ℝ) / 80000000000000000) * bsv))) + (((structuralBallConst ((93530053267643 : ℝ) / 160000000000000000) * bv4) + (structuralBallConst ((176568895053349 : ℝ) / 80000000000000000) * bdv)) + ((bX * (((((structuralBallConst ((5588137197069 : ℝ) / 400000000000000) + (structuralBallConst ((-6695518941 : ℝ) / 40000000000) * bdv)) + ((structuralBallConst ((-2780437199 : ℝ) / 80000000000) * bv4) + (structuralBallConst ((-553726279 : ℝ) / 40000000000) * bsv))) + (((structuralBallConst ((33868621673 : ℝ) / 400000000000) * bh13) + (structuralBallConst ((62910979413 : ℝ) / 800000000000) * bq13)) + ((bX * (((structuralBallConst ((275231319 : ℝ) / 1000000000) + (structuralBallConst ((-171 : ℝ) / 800) * bv4)) + ((structuralBallConst ((24557 : ℝ) / 50000) * bh13) + (structuralBallConst ((69823 : ℝ) / 100000) * bq13))) + (((bf * ((structuralBallConst ((-4203 : ℝ) / 20000) + bh13) + (structuralBallConst ((-1 : ℝ) / 2) * bq13))) + (bu4 * (structuralBallConst ((9 : ℝ) / 2000) + (structuralBallConst ((-3 : ℝ) / 2) * bv4)))) + (bF * ((structuralBallConst ((3963 : ℝ) / 4000) + bh13) + (structuralBallConst ((5 : ℝ) / 2) * bq13)))))) + (bR * ((((structuralBallConst ((68902977 : ℝ) / 800000000) + (structuralBallConst ((171 : ℝ) / 800) * bdv)) + ((structuralBallConst ((10137 : ℝ) / 400000) * bv4) + (structuralBallConst ((15123 : ℝ) / 80000) * bq13))) + (((structuralBallConst ((27243 : ℝ) / 200000) * bh13) + (bdu * (structuralBallConst ((-9 : ℝ) / 2000) + (structuralBallConst ((3 : ℝ) / 2) * bv4)))) + ((bu4 * (structuralBallConst ((3339 : ℝ) / 40000) + (structuralBallConst ((3 : ℝ) / 2) * bdv))) + (bD * ((structuralBallConst ((3963 : ℝ) / 2000) + (structuralBallConst (2 : ℝ) * bh13)) + (structuralBallConst (5 : ℝ) * bq13)))))) + (bd * ((structuralBallConst ((-4203 : ℝ) / 10000) + (structuralBallConst (-1 : ℝ) * bq13)) + (structuralBallConst (2 : ℝ) * bh13)))))))) + ((((bf * (((structuralBallConst ((-180246073 : ℝ) / 16000000000) + (structuralBallConst ((-78501 : ℝ) / 1000000) * bq13)) + ((structuralBallConst ((889 : ℝ) / 500000) * bh13) + (structuralBallConst ((3379 : ℝ) / 400000) * bsv))) + (((structuralBallConst ((112341 : ℝ) / 400000) * bdv) + (bsu * (structuralBallConst ((1113 : ℝ) / 40000) + (structuralBallConst ((1 : ℝ) / 2) * bdv)))) + (bdu * (structuralBallConst ((107651 : ℝ) / 400000) + (structuralBallConst ((1 : ℝ) / 2) * bsv)))))) + (bsu * ((structuralBallConst ((-84776103 : ℝ) / 4000000000) + (structuralBallConst ((-41329 : ℝ) / 800000) * bv4)) + (structuralBallConst ((-38363 : ℝ) / 100000) * bdv)))) + ((bdu * ((structuralBallConst ((-129689609 : ℝ) / 625000000) + (structuralBallConst ((-38363 : ℝ) / 100000) * bsv)) + (structuralBallConst ((270029 : ℝ) / 800000) * bv4))) + (bu4 * ((structuralBallConst ((-1405151489 : ℝ) / 160000000000) + (structuralBallConst ((-80279 : ℝ) / 1000000) * bv4)) + ((structuralBallConst ((-41329 : ℝ) / 800000) * bsv) + (structuralBallConst ((270029 : ℝ) / 800000) * bdv)))))) + (((bD * (((structuralBallConst ((138484701 : ℝ) / 400000000) + (structuralBallConst ((-337023 : ℝ) / 400000) * bv4)) + ((structuralBallConst ((-171 : ℝ) / 800) * bsv) + (structuralBallConst ((92863 : ℝ) / 80000) * bq13))) + (((structuralBallConst ((118543 : ℝ) / 200000) * bh13) + (bsu * (structuralBallConst ((9 : ℝ) / 2000) + (structuralBallConst ((-3 : ℝ) / 2) * bv4)))) + ((bu4 * (structuralBallConst ((-322953 : ℝ) / 400000) + (structuralBallConst ((-3 : ℝ) / 2) * bsv))) + (br * ((structuralBallConst ((-4203 : ℝ) / 10000) + (structuralBallConst (-1 : ℝ) * bq13)) + (structuralBallConst (2 : ℝ) * bh13))))))) + (bF * (((structuralBallConst ((145314279 : ℝ) / 80000000000) + (structuralBallConst ((-337023 : ℝ) / 400000) * bdv)) + ((structuralBallConst ((-10137 : ℝ) / 400000) * bsv) + (structuralBallConst ((78501 : ℝ) / 500000) * bh13))) + (((structuralBallConst ((159669 : ℝ) / 1000000) * bq13) + (bsu * (structuralBallConst ((-3339 : ℝ) / 40000) + (structuralBallConst ((-3 : ℝ) / 2) * bdv)))) + ((bdu * (structuralBallConst ((-322953 : ℝ) / 400000) + (structuralBallConst ((-3 : ℝ) / 2) * bsv))) + (bx * ((structuralBallConst ((-4203 : ℝ) / 10000) + (structuralBallConst (-1 : ℝ) * bq13)) + (structuralBallConst (2 : ℝ) * bh13)))))))) + ((bx * (((structuralBallConst ((-99896021 : ℝ) / 500000000) + (structuralBallConst ((-24557 : ℝ) / 50000) * bq13)) + ((structuralBallConst ((57 : ℝ) / 400) * bv4) + (structuralBallConst ((6903 : ℝ) / 25000) * bh13))) + ((bf * ((structuralBallConst ((-3803 : ℝ) / 10000) + (structuralBallConst (-1 : ℝ) * bq13)) + (structuralBallConst (-2 : ℝ) * bh13))) + (bu4 * (structuralBallConst ((-3 : ℝ) / 1000) + bv4))))) + (br * (((structuralBallConst ((-126221209 : ℝ) / 4000000000) + (structuralBallConst ((-27243 : ℝ) / 400000) * bq13)) + ((structuralBallConst ((-3379 : ℝ) / 400000) * bv4) + (structuralBallConst ((-57 : ℝ) / 800) * bdv))) + (((structuralBallConst ((7043 : ℝ) / 200000) * bh13) + (bdu * (structuralBallConst ((3 : ℝ) / 2000) + (structuralBallConst ((-1 : ℝ) / 2) * bv4)))) + ((bu4 * (structuralBallConst ((-1113 : ℝ) / 40000) + (structuralBallConst ((-1 : ℝ) / 2) * bdv))) + (bd * ((structuralBallConst ((-3803 : ℝ) / 10000) + (structuralBallConst (-1 : ℝ) * bq13)) + (structuralBallConst (-2 : ℝ) * bh13))))))))))) + (bd * (((structuralBallConst ((-42455473 : ℝ) / 500000000) + (structuralBallConst ((-118543 : ℝ) / 400000) * bq13)) + ((structuralBallConst ((57 : ℝ) / 800) * bsv) + (structuralBallConst ((75743 : ℝ) / 200000) * bh13))) + (((structuralBallConst ((112341 : ℝ) / 400000) * bv4) + (bsu * (structuralBallConst ((-3 : ℝ) / 2000) + (structuralBallConst ((1 : ℝ) / 2) * bv4)))) + (bu4 * (structuralBallConst ((107651 : ℝ) / 400000) + (structuralBallConst ((1 : ℝ) / 2) * bsv)))))))) + (bR * ((((structuralBallConst ((114053345726113 : ℝ) / 32000000000000000) + (structuralBallConst ((-5552616571 : ℝ) / 160000000000) * bdv)) + ((structuralBallConst ((-1763100041 : ℝ) / 200000000000) * bv4) + (structuralBallConst ((-525004891 : ℝ) / 160000000000) * bsv))) + (((structuralBallConst ((1700896407 : ℝ) / 100000000000) * bh13) + (structuralBallConst ((3699847773 : ℝ) / 200000000000) * bq13)) + ((bR * (((structuralBallConst ((419775513 : ℝ) / 40000000000) + (structuralBallConst ((-10137 : ℝ) / 400000) * bdv)) + ((structuralBallConst ((19497 : ℝ) / 1000000) * bh13) + (structuralBallConst ((60453 : ℝ) / 2000000) * bq13))) + (((bdu * (structuralBallConst ((-3339 : ℝ) / 40000) + (structuralBallConst ((-3 : ℝ) / 2) * bdv))) + (bC * ((structuralBallConst ((3963 : ℝ) / 4000) + bh13) + (structuralBallConst ((5 : ℝ) / 2) * bq13)))) + (bc * ((structuralBallConst ((-4203 : ℝ) / 20000) + bh13) + (structuralBallConst ((-1 : ℝ) / 2) * bq13)))))) + (bsu * ((structuralBallConst ((-9037581 : ℝ) / 3200000000) + (structuralBallConst ((-41329 : ℝ) / 800000) * bdv)) + (structuralBallConst ((-33803 : ℝ) / 2000000) * bv4)))))) + ((((bdu * ((structuralBallConst ((-10479220679 : ℝ) / 160000000000) + (structuralBallConst ((-270029 : ℝ) / 400000) * bdv)) + ((structuralBallConst ((-41329 : ℝ) / 800000) * bsv) + (structuralBallConst ((80279 : ℝ) / 2000000) * bv4)))) + (bu4 * ((structuralBallConst ((-2745421483 : ℝ) / 400000000000) + (structuralBallConst ((-33803 : ℝ) / 2000000) * bsv)) + (structuralBallConst ((80279 : ℝ) / 2000000) * bdv)))) + ((bC * (((structuralBallConst ((138484701 : ℝ) / 400000000) + (structuralBallConst ((-337023 : ℝ) / 400000) * bv4)) + ((structuralBallConst ((-171 : ℝ) / 800) * bsv) + (structuralBallConst ((92863 : ℝ) / 80000) * bq13))) + (((structuralBallConst ((118543 : ℝ) / 200000) * bh13) + (bsu * (structuralBallConst ((9 : ℝ) / 2000) + (structuralBallConst ((-3 : ℝ) / 2) * bv4)))) + ((bu4 * (structuralBallConst ((-322953 : ℝ) / 400000) + (structuralBallConst ((-3 : ℝ) / 2) * bsv))) + (br * ((structuralBallConst ((-4203 : ℝ) / 10000) + (structuralBallConst (-1 : ℝ) * bq13)) + (structuralBallConst (2 : ℝ) * bh13))))))) + (bD * (((structuralBallConst ((145314279 : ℝ) / 80000000000) + (structuralBallConst ((-337023 : ℝ) / 400000) * bdv)) + ((structuralBallConst ((-10137 : ℝ) / 400000) * bsv) + (structuralBallConst ((78501 : ℝ) / 500000) * bh13))) + (((structuralBallConst ((159669 : ℝ) / 1000000) * bq13) + (bsu * (structuralBallConst ((-3339 : ℝ) / 40000) + (structuralBallConst ((-3 : ℝ) / 2) * bdv)))) + ((bdu * (structuralBallConst ((-322953 : ℝ) / 400000) + (structuralBallConst ((-3 : ℝ) / 2) * bsv))) + (bx * ((structuralBallConst ((-4203 : ℝ) / 10000) + (structuralBallConst (-1 : ℝ) * bq13)) + (structuralBallConst (2 : ℝ) * bh13))))))))) + (((bx * (((structuralBallConst ((-126221209 : ℝ) / 4000000000) + (structuralBallConst ((-27243 : ℝ) / 400000) * bq13)) + ((structuralBallConst ((-3379 : ℝ) / 400000) * bv4) + (structuralBallConst ((-57 : ℝ) / 800) * bdv))) + (((structuralBallConst ((7043 : ℝ) / 200000) * bh13) + (bdu * (structuralBallConst ((3 : ℝ) / 2000) + (structuralBallConst ((-1 : ℝ) / 2) * bv4)))) + ((bu4 * (structuralBallConst ((-1113 : ℝ) / 40000) + (structuralBallConst ((-1 : ℝ) / 2) * bdv))) + (bd * ((structuralBallConst ((-3803 : ℝ) / 10000) + (structuralBallConst (-1 : ℝ) * bq13)) + (structuralBallConst (-2 : ℝ) * bh13))))))) + (br * (((structuralBallConst ((-140150047 : ℝ) / 20000000000) + (structuralBallConst ((-19497 : ℝ) / 1000000) * bq13)) + ((structuralBallConst ((3379 : ℝ) / 200000) * bdv) + (structuralBallConst ((7153 : ℝ) / 500000) * bh13))) + ((bdu * (structuralBallConst ((1113 : ℝ) / 20000) + bdv)) + (bc * ((structuralBallConst ((-3803 : ℝ) / 10000) + (structuralBallConst (-1 : ℝ) * bq13)) + (structuralBallConst (-2 : ℝ) * bh13))))))) + ((bc * (((structuralBallConst ((-42455473 : ℝ) / 500000000) + (structuralBallConst ((-118543 : ℝ) / 400000) * bq13)) + ((structuralBallConst ((57 : ℝ) / 800) * bsv) + (structuralBallConst ((75743 : ℝ) / 200000) * bh13))) + (((structuralBallConst ((112341 : ℝ) / 400000) * bv4) + (bsu * (structuralBallConst ((-3 : ℝ) / 2000) + (structuralBallConst ((1 : ℝ) / 2) * bv4)))) + (bu4 * (structuralBallConst ((107651 : ℝ) / 400000) + (structuralBallConst ((1 : ℝ) / 2) * bsv)))))) + (bd * (((structuralBallConst ((-180246073 : ℝ) / 16000000000) + (structuralBallConst ((-78501 : ℝ) / 1000000) * bq13)) + ((structuralBallConst ((889 : ℝ) / 500000) * bh13) + (structuralBallConst ((3379 : ℝ) / 400000) * bsv))) + (((structuralBallConst ((112341 : ℝ) / 400000) * bdv) + (bsu * (structuralBallConst ((1113 : ℝ) / 40000) + (structuralBallConst ((1 : ℝ) / 2) * bdv)))) + (bdu * (structuralBallConst ((107651 : ℝ) / 400000) + (structuralBallConst ((1 : ℝ) / 2) * bsv)))))))))))))) + ((((bf * (((structuralBallConst ((34837820394207 : ℝ) / 10000000000000000) + (structuralBallConst ((-962528799 : ℝ) / 200000000000) * bsv)) + ((structuralBallConst ((1386087783 : ℝ) / 400000000000) * bdv) + (structuralBallConst ((3253339443 : ℝ) / 1000000000000) * bh13))) + (((structuralBallConst ((29547367797 : ℝ) / 2000000000000) * bq13) + (bsu * ((structuralBallConst ((-1225155417 : ℝ) / 400000000000) + (structuralBallConst ((-19497 : ℝ) / 2000000) * bsv)) + (structuralBallConst ((78501 : ℝ) / 2000000) * bdv)))) + (bdu * ((structuralBallConst ((-16031972109 : ℝ) / 400000000000) + (structuralBallConst ((-1099851 : ℝ) / 1000000) * bdv)) + (structuralBallConst ((78501 : ℝ) / 2000000) * bsv)))))) + (bsu * ((structuralBallConst ((97843279926861 : ℝ) / 320000000000000000) + (structuralBallConst ((-26276879723 : ℝ) / 1600000000000) * bdv)) + ((structuralBallConst ((-1724925913 : ℝ) / 400000000000) * bv4) + (structuralBallConst ((3587195001 : ℝ) / 1600000000000) * bsv))))) + ((bdu * ((structuralBallConst ((1582575200848457 : ℝ) / 320000000000000000) + (structuralBallConst ((-26276879723 : ℝ) / 1600000000000) * bsv)) + ((structuralBallConst ((40425839471 : ℝ) / 800000000000) * bv4) + (structuralBallConst ((400702478641 : ℝ) / 1600000000000) * bdv)))) + (bu4 * ((structuralBallConst ((1114174272341 : ℝ) / 2500000000000000) + (structuralBallConst ((-1724925913 : ℝ) / 400000000000) * bsv)) + ((structuralBallConst ((30218504007 : ℝ) / 2000000000000) * bv4) + (structuralBallConst ((40425839471 : ℝ) / 800000000000) * bdv)))))) + (((bC * ((((structuralBallConst ((-2442792422768771 : ℝ) / 16000000000000000) + (structuralBallConst ((-998067266951 : ℝ) / 1600000000000) * bq13)) + ((structuralBallConst ((-565440574971 : ℝ) / 800000000000) * bh13) + (structuralBallConst ((6695518941 : ℝ) / 40000000000) * bsv))) + (((structuralBallConst ((7252957311 : ℝ) / 160000000000) * bv4) + (bf * (((structuralBallConst ((23567013833 : ℝ) / 80000000000) + (structuralBallConst ((-274379 : ℝ) / 500000) * bh13)) + ((structuralBallConst ((-112341 : ℝ) / 400000) * bsv) + (structuralBallConst ((1099851 : ℝ) / 1000000) * bq13))) + (bsu * (structuralBallConst ((-107651 : ℝ) / 400000) + (structuralBallConst ((-1 : ℝ) / 2) * bsv)))))) + ((bsu * ((structuralBallConst ((129689609 : ℝ) / 625000000) + (structuralBallConst ((-270029 : ℝ) / 800000) * bv4)) + (structuralBallConst ((38363 : ℝ) / 100000) * bsv))) + (bu4 * ((structuralBallConst ((-29860224199 : ℝ) / 160000000000) + (structuralBallConst ((-270029 : ℝ) / 800000) * bsv)) + (structuralBallConst ((1648609 : ℝ) / 1000000) * bv4)))))) + (((bF * (((structuralBallConst ((-58762771563 : ℝ) / 80000000000) + (structuralBallConst ((-3022839 : ℝ) / 1000000) * bq13)) + ((structuralBallConst ((-1099851 : ℝ) / 500000) * bh13) + (structuralBallConst ((337023 : ℝ) / 400000) * bsv))) + ((bsu * (structuralBallConst ((322953 : ℝ) / 400000) + (structuralBallConst ((3 : ℝ) / 2) * bsv))) + (ba * ((structuralBallConst ((4203 : ℝ) / 20000) + (structuralBallConst ((1 : ℝ) / 2) * bq13)) + (structuralBallConst (-1 : ℝ) * bh13)))))) + (ba * (((structuralBallConst ((99896021 : ℝ) / 1000000000) + (structuralBallConst ((-6903 : ℝ) / 50000) * bh13)) + ((structuralBallConst ((-57 : ℝ) / 800) * bv4) + (structuralBallConst ((24557 : ℝ) / 100000) * bq13))) + ((bf * ((structuralBallConst ((3803 : ℝ) / 20000) + bh13) + (structuralBallConst ((1 : ℝ) / 2) * bq13))) + (bu4 * (structuralBallConst ((3 : ℝ) / 2000) + (structuralBallConst ((-1 : ℝ) / 2) * bv4))))))) + (br * (((structuralBallConst ((-42455473 : ℝ) / 500000000) + (structuralBallConst ((-118543 : ℝ) / 400000) * bq13)) + ((structuralBallConst ((57 : ℝ) / 800) * bsv) + (structuralBallConst ((75743 : ℝ) / 200000) * bh13))) + (((structuralBallConst ((112341 : ℝ) / 400000) * bv4) + (bsu * (structuralBallConst ((-3 : ℝ) / 2000) + (structuralBallConst ((1 : ℝ) / 2) * bv4)))) + ((bu4 * (structuralBallConst ((107651 : ℝ) / 400000) + (structuralBallConst ((1 : ℝ) / 2) * bsv))) + (br * ((structuralBallConst ((-3803 : ℝ) / 20000) + (structuralBallConst (-1 : ℝ) * bh13)) + (structuralBallConst ((-1 : ℝ) / 2) * bq13)))))))))) + (bD * ((((structuralBallConst ((370568941345159 : ℝ) / 6400000000000000) + (structuralBallConst ((-11113490969 : ℝ) / 160000000000) * bsv)) + ((structuralBallConst ((2122676483 : ℝ) / 400000000000) * bv4) + (structuralBallConst ((7252957311 : ℝ) / 160000000000) * bdv))) + (((structuralBallConst ((50896794429 : ℝ) / 200000000000) * bh13) + (structuralBallConst ((95254872021 : ℝ) / 400000000000) * bq13)) + ((bsu * ((structuralBallConst ((-1485546521 : ℝ) / 20000000000) + (structuralBallConst ((-270029 : ℝ) / 800000) * bdv)) + ((structuralBallConst ((-80279 : ℝ) / 2000000) * bv4) + (structuralBallConst ((-41329 : ℝ) / 400000) * bsv)))) + (bdu * ((structuralBallConst ((-29860224199 : ℝ) / 160000000000) + (structuralBallConst ((-270029 : ℝ) / 800000) * bsv)) + (structuralBallConst ((1648609 : ℝ) / 1000000) * bv4)))))) + ((((bu4 * ((structuralBallConst ((28055921711 : ℝ) / 400000000000) + (structuralBallConst ((-80279 : ℝ) / 2000000) * bsv)) + (structuralBallConst ((1648609 : ℝ) / 1000000) * bdv))) + (bD * (((structuralBallConst ((58762771563 : ℝ) / 80000000000) + (structuralBallConst ((-337023 : ℝ) / 400000) * bsv)) + ((structuralBallConst ((1099851 : ℝ) / 500000) * bh13) + (structuralBallConst ((3022839 : ℝ) / 1000000) * bq13))) + ((bsu * (structuralBallConst ((-322953 : ℝ) / 400000) + (structuralBallConst ((-3 : ℝ) / 2) * bsv))) + (ba * ((structuralBallConst ((-4203 : ℝ) / 20000) + bh13) + (structuralBallConst ((-1 : ℝ) / 2) * bq13))))))) + ((ba * (((structuralBallConst ((-126221209 : ℝ) / 4000000000) + (structuralBallConst ((-27243 : ℝ) / 400000) * bq13)) + ((structuralBallConst ((-3379 : ℝ) / 400000) * bv4) + (structuralBallConst ((-57 : ℝ) / 800) * bdv))) + (((structuralBallConst ((7043 : ℝ) / 200000) * bh13) + (bdu * (structuralBallConst ((3 : ℝ) / 2000) + (structuralBallConst ((-1 : ℝ) / 2) * bv4)))) + ((bu4 * (structuralBallConst ((-1113 : ℝ) / 40000) + (structuralBallConst ((-1 : ℝ) / 2) * bdv))) + (bd * ((structuralBallConst ((-3803 : ℝ) / 10000) + (structuralBallConst (-1 : ℝ) * bq13)) + (structuralBallConst (-2 : ℝ) * bh13))))))) + (bx * (((structuralBallConst ((-42455473 : ℝ) / 500000000) + (structuralBallConst ((-118543 : ℝ) / 400000) * bq13)) + ((structuralBallConst ((57 : ℝ) / 800) * bsv) + (structuralBallConst ((75743 : ℝ) / 200000) * bh13))) + (((structuralBallConst ((112341 : ℝ) / 400000) * bv4) + (bsu * (structuralBallConst ((-3 : ℝ) / 2000) + (structuralBallConst ((1 : ℝ) / 2) * bv4)))) + ((bu4 * (structuralBallConst ((107651 : ℝ) / 400000) + (structuralBallConst ((1 : ℝ) / 2) * bsv))) + (br * ((structuralBallConst ((-3803 : ℝ) / 10000) + (structuralBallConst (-1 : ℝ) * bq13)) + (structuralBallConst (-2 : ℝ) * bh13))))))))) + ((br * (((structuralBallConst ((-180246073 : ℝ) / 16000000000) + (structuralBallConst ((-78501 : ℝ) / 1000000) * bq13)) + ((structuralBallConst ((889 : ℝ) / 500000) * bh13) + (structuralBallConst ((3379 : ℝ) / 400000) * bsv))) + (((structuralBallConst ((112341 : ℝ) / 400000) * bdv) + (bsu * (structuralBallConst ((1113 : ℝ) / 40000) + (structuralBallConst ((1 : ℝ) / 2) * bdv)))) + (bdu * (structuralBallConst ((107651 : ℝ) / 400000) + (structuralBallConst ((1 : ℝ) / 2) * bsv)))))) + (bd * (((structuralBallConst ((-23567013833 : ℝ) / 40000000000) + (structuralBallConst ((-1099851 : ℝ) / 500000) * bq13)) + ((structuralBallConst ((112341 : ℝ) / 200000) * bsv) + (structuralBallConst ((274379 : ℝ) / 250000) * bh13))) + (bsu * (structuralBallConst ((107651 : ℝ) / 200000) + bsv))))))))) + ((bF * ((((structuralBallConst ((-74118449370089 : ℝ) / 10000000000000000) + (structuralBallConst ((-63690347457 : ℝ) / 2000000000000) * bq13)) + ((structuralBallConst ((-29547367797 : ℝ) / 1000000000000) * bh13) + (structuralBallConst ((1763100041 : ℝ) / 200000000000) * bsv))) + (((structuralBallConst ((2122676483 : ℝ) / 400000000000) * bdv) + (bsu * ((structuralBallConst ((2745421483 : ℝ) / 400000000000) + (structuralBallConst ((-80279 : ℝ) / 2000000) * bdv)) + (structuralBallConst ((33803 : ℝ) / 2000000) * bsv)))) + ((bdu * ((structuralBallConst ((28055921711 : ℝ) / 400000000000) + (structuralBallConst ((-80279 : ℝ) / 2000000) * bsv)) + (structuralBallConst ((1648609 : ℝ) / 1000000) * bdv))) + (ba * (((structuralBallConst ((140150047 : ℝ) / 40000000000) + (structuralBallConst ((-7153 : ℝ) / 1000000) * bh13)) + ((structuralBallConst ((-3379 : ℝ) / 400000) * bdv) + (structuralBallConst ((19497 : ℝ) / 2000000) * bq13))) + ((bdu * (structuralBallConst ((-1113 : ℝ) / 40000) + (structuralBallConst ((-1 : ℝ) / 2) * bdv))) + (bc * ((structuralBallConst ((3803 : ℝ) / 20000) + bh13) + (structuralBallConst ((1 : ℝ) / 2) * bq13))))))))) + ((bx * (((structuralBallConst ((-180246073 : ℝ) / 16000000000) + (structuralBallConst ((-78501 : ℝ) / 1000000) * bq13)) + ((structuralBallConst ((889 : ℝ) / 500000) * bh13) + (structuralBallConst ((3379 : ℝ) / 400000) * bsv))) + (((structuralBallConst ((112341 : ℝ) / 400000) * bdv) + (bsu * (structuralBallConst ((1113 : ℝ) / 40000) + (structuralBallConst ((1 : ℝ) / 2) * bdv)))) + ((bdu * (structuralBallConst ((107651 : ℝ) / 400000) + (structuralBallConst ((1 : ℝ) / 2) * bsv))) + (bx * ((structuralBallConst ((-3803 : ℝ) / 20000) + (structuralBallConst (-1 : ℝ) * bh13)) + (structuralBallConst ((-1 : ℝ) / 2) * bq13))))))) + (bc * (((structuralBallConst ((23567013833 : ℝ) / 80000000000) + (structuralBallConst ((-274379 : ℝ) / 500000) * bh13)) + ((structuralBallConst ((-112341 : ℝ) / 400000) * bsv) + (structuralBallConst ((1099851 : ℝ) / 1000000) * bq13))) + (bsu * (structuralBallConst ((-107651 : ℝ) / 400000) + (structuralBallConst ((-1 : ℝ) / 2) * bsv)))))))) + (ba * ((((structuralBallConst ((4958460554873 : ℝ) / 16000000000000000) + (structuralBallConst ((-360062581 : ℝ) / 40000000000) * bdv)) + ((structuralBallConst ((-314319897 : ℝ) / 160000000000) * bv4) + (structuralBallConst ((181252509 : ℝ) / 800000000000) * bh13))) + (((structuralBallConst ((3226432211 : ℝ) / 1600000000000) * bq13) + (bf * (((structuralBallConst ((30663983 : ℝ) / 40000000000) + (structuralBallConst ((-3379 : ℝ) / 400000) * bdv)) + ((structuralBallConst ((7153 : ℝ) / 2000000) * bq13) + (structuralBallConst ((19497 : ℝ) / 1000000) * bh13))) + (bdu * (structuralBallConst ((-1113 : ℝ) / 40000) + (structuralBallConst ((-1 : ℝ) / 2) * bdv)))))) + ((bdu * ((structuralBallConst ((-54255237 : ℝ) / 4000000000) + (structuralBallConst ((-27243 : ℝ) / 800000) * bv4)) + (structuralBallConst ((-24557 : ℝ) / 100000) * bdv))) + (bu4 * ((structuralBallConst ((-29853531 : ℝ) / 16000000000) + (structuralBallConst ((-27243 : ℝ) / 800000) * bdv)) + (structuralBallConst ((-19497 : ℝ) / 2000000) * bv4)))))) + ((bc * (((structuralBallConst ((22935059 : ℝ) / 1000000000) + (structuralBallConst ((-57 : ℝ) / 800) * bv4)) + ((structuralBallConst ((6903 : ℝ) / 100000) * bq13) + (structuralBallConst ((24557 : ℝ) / 50000) * bh13))) + ((bf * ((structuralBallConst ((-4203 : ℝ) / 20000) + bh13) + (structuralBallConst ((-1 : ℝ) / 2) * bq13))) + (bu4 * (structuralBallConst ((3 : ℝ) / 2000) + (structuralBallConst ((-1 : ℝ) / 2) * bv4)))))) + (bd * (((structuralBallConst ((-38503409 : ℝ) / 4000000000) + (structuralBallConst ((-27243 : ℝ) / 200000) * bh13)) + ((structuralBallConst ((-7043 : ℝ) / 400000) * bq13) + (structuralBallConst ((-3379 : ℝ) / 400000) * bv4))) + (((structuralBallConst ((-57 : ℝ) / 800) * bdv) + (bdu * (structuralBallConst ((3 : ℝ) / 2000) + (structuralBallConst ((-1 : ℝ) / 2) * bv4)))) + ((bu4 * (structuralBallConst ((-1113 : ℝ) / 40000) + (structuralBallConst ((-1 : ℝ) / 2) * bdv))) + (bd * ((structuralBallConst ((4203 : ℝ) / 20000) + (structuralBallConst ((1 : ℝ) / 2) * bq13)) + (structuralBallConst (-1 : ℝ) * bh13)))))))))))))) + (((bx * ((((structuralBallConst ((-21700836918709 : ℝ) / 4000000000000000) + (structuralBallConst ((-33868621673 : ℝ) / 800000000000) * bq13)) + ((structuralBallConst ((-10357219967 : ℝ) / 400000000000) * bh13) + (structuralBallConst ((360062581 : ℝ) / 40000000000) * bsv))) + (((structuralBallConst ((2224885933 : ℝ) / 80000000000) * bv4) + (structuralBallConst ((4672896999 : ℝ) / 40000000000) * bdv)) + ((bf * (((structuralBallConst ((1711240323 : ℝ) / 80000000000) + (structuralBallConst ((-78501 : ℝ) / 500000) * bh13)) + ((structuralBallConst ((-889 : ℝ) / 1000000) * bq13) + (structuralBallConst ((3379 : ℝ) / 400000) * bsv))) + (((structuralBallConst ((112341 : ℝ) / 400000) * bdv) + (bsu * (structuralBallConst ((1113 : ℝ) / 40000) + (structuralBallConst ((1 : ℝ) / 2) * bdv)))) + (bdu * (structuralBallConst ((107651 : ℝ) / 400000) + (structuralBallConst ((1 : ℝ) / 2) * bsv)))))) + (bsu * ((structuralBallConst ((54255237 : ℝ) / 4000000000) + (structuralBallConst ((24557 : ℝ) / 100000) * bdv)) + (structuralBallConst ((27243 : ℝ) / 800000) * bv4)))))) + ((((bdu * ((structuralBallConst ((663119083 : ℝ) / 5000000000) + (structuralBallConst ((-118543 : ℝ) / 800000) * bv4)) + (structuralBallConst ((24557 : ℝ) / 100000) * bsv))) + (bu4 * ((structuralBallConst ((1575672123 : ℝ) / 160000000000) + (structuralBallConst ((-118543 : ℝ) / 800000) * bdv)) + ((structuralBallConst ((27243 : ℝ) / 800000) * bsv) + (structuralBallConst ((78501 : ℝ) / 1000000) * bv4))))) + ((bx * (((structuralBallConst ((-22935059 : ℝ) / 1000000000) + (structuralBallConst ((-24557 : ℝ) / 50000) * bh13)) + ((structuralBallConst ((-6903 : ℝ) / 100000) * bq13) + (structuralBallConst ((57 : ℝ) / 800) * bv4))) + ((bf * ((structuralBallConst ((4203 : ℝ) / 20000) + (structuralBallConst ((1 : ℝ) / 2) * bq13)) + (structuralBallConst (-1 : ℝ) * bh13))) + (bu4 * (structuralBallConst ((-3 : ℝ) / 2000) + (structuralBallConst ((1 : ℝ) / 2) * bv4)))))) + (br * (((structuralBallConst ((-38503409 : ℝ) / 4000000000) + (structuralBallConst ((-27243 : ℝ) / 200000) * bh13)) + ((structuralBallConst ((-7043 : ℝ) / 400000) * bq13) + (structuralBallConst ((-3379 : ℝ) / 400000) * bv4))) + (((structuralBallConst ((-57 : ℝ) / 800) * bdv) + (bdu * (structuralBallConst ((3 : ℝ) / 2000) + (structuralBallConst ((-1 : ℝ) / 2) * bv4)))) + ((bu4 * (structuralBallConst ((-1113 : ℝ) / 40000) + (structuralBallConst ((-1 : ℝ) / 2) * bdv))) + (bd * ((structuralBallConst ((4203 : ℝ) / 10000) + bq13) + (structuralBallConst (-2 : ℝ) * bh13))))))))) + (bd * (((structuralBallConst ((-16182273 : ℝ) / 500000000) + (structuralBallConst ((-118543 : ℝ) / 200000) * bh13)) + ((structuralBallConst ((-75743 : ℝ) / 400000) * bq13) + (structuralBallConst ((57 : ℝ) / 800) * bsv))) + (((structuralBallConst ((112341 : ℝ) / 400000) * bv4) + (bsu * (structuralBallConst ((-3 : ℝ) / 2000) + (structuralBallConst ((1 : ℝ) / 2) * bv4)))) + (bu4 * (structuralBallConst ((107651 : ℝ) / 400000) + (structuralBallConst ((1 : ℝ) / 2) * bsv))))))))) + (br * ((((structuralBallConst ((-41744727962299 : ℝ) / 32000000000000000) + (structuralBallConst ((-1700896407 : ℝ) / 200000000000) * bq13)) + ((structuralBallConst ((-249995947 : ℝ) / 100000000000) * bh13) + (structuralBallConst ((314319897 : ℝ) / 160000000000) * bsv))) + (((structuralBallConst ((962528799 : ℝ) / 200000000000) * bv4) + (structuralBallConst ((2966708057 : ℝ) / 160000000000) * bdv)) + ((bsu * ((structuralBallConst ((29853531 : ℝ) / 16000000000) + (structuralBallConst ((19497 : ℝ) / 2000000) * bv4)) + (structuralBallConst ((27243 : ℝ) / 800000) * bdv))) + (bdu * ((structuralBallConst ((5590343613 : ℝ) / 160000000000) + (structuralBallConst ((-78501 : ℝ) / 2000000) * bv4)) + ((structuralBallConst ((27243 : ℝ) / 800000) * bsv) + (structuralBallConst ((118543 : ℝ) / 400000) * bdv))))))) + (((bu4 * ((structuralBallConst ((1225155417 : ℝ) / 400000000000) + (structuralBallConst ((-78501 : ℝ) / 2000000) * bdv)) + (structuralBallConst ((19497 : ℝ) / 2000000) * bsv))) + (br * (((structuralBallConst ((-30663983 : ℝ) / 40000000000) + (structuralBallConst ((-19497 : ℝ) / 1000000) * bh13)) + ((structuralBallConst ((-7153 : ℝ) / 2000000) * bq13) + (structuralBallConst ((3379 : ℝ) / 400000) * bdv))) + ((bdu * (structuralBallConst ((1113 : ℝ) / 40000) + (structuralBallConst ((1 : ℝ) / 2) * bdv))) + (bc * ((structuralBallConst ((4203 : ℝ) / 20000) + (structuralBallConst ((1 : ℝ) / 2) * bq13)) + (structuralBallConst (-1 : ℝ) * bh13))))))) + ((bc * (((structuralBallConst ((-16182273 : ℝ) / 500000000) + (structuralBallConst ((-118543 : ℝ) / 200000) * bh13)) + ((structuralBallConst ((-75743 : ℝ) / 400000) * bq13) + (structuralBallConst ((57 : ℝ) / 800) * bsv))) + (((structuralBallConst ((112341 : ℝ) / 400000) * bv4) + (bsu * (structuralBallConst ((-3 : ℝ) / 2000) + (structuralBallConst ((1 : ℝ) / 2) * bv4)))) + (bu4 * (structuralBallConst ((107651 : ℝ) / 400000) + (structuralBallConst ((1 : ℝ) / 2) * bsv)))))) + (bd * (((structuralBallConst ((1711240323 : ℝ) / 80000000000) + (structuralBallConst ((-78501 : ℝ) / 500000) * bh13)) + ((structuralBallConst ((-889 : ℝ) / 1000000) * bq13) + (structuralBallConst ((3379 : ℝ) / 400000) * bsv))) + (((structuralBallConst ((112341 : ℝ) / 400000) * bdv) + (bsu * (structuralBallConst ((1113 : ℝ) / 40000) + (structuralBallConst ((1 : ℝ) / 2) * bdv)))) + (bdu * (structuralBallConst ((107651 : ℝ) / 400000) + (structuralBallConst ((1 : ℝ) / 2) * bsv))))))))))) + ((bc * (((structuralBallConst ((244313979817503 : ℝ) / 3200000000000000) + (structuralBallConst ((-11759363637 : ℝ) / 160000000000) * bv4)) + ((structuralBallConst ((-4672896999 : ℝ) / 40000000000) * bsv) + (structuralBallConst ((196662309669 : ℝ) / 800000000000) * bh13))) + (((structuralBallConst ((565440574971 : ℝ) / 1600000000000) * bq13) + (bf * (((structuralBallConst ((-1013333899 : ℝ) / 16000000000) + (structuralBallConst ((-112341 : ℝ) / 400000) * bsv)) + ((structuralBallConst ((274379 : ℝ) / 1000000) * bq13) + (structuralBallConst ((1099851 : ℝ) / 500000) * bh13))) + (bsu * (structuralBallConst ((-107651 : ℝ) / 400000) + (structuralBallConst ((-1 : ℝ) / 2) * bsv)))))) + ((bsu * ((structuralBallConst ((-663119083 : ℝ) / 5000000000) + (structuralBallConst ((-24557 : ℝ) / 100000) * bsv)) + (structuralBallConst ((118543 : ℝ) / 800000) * bv4))) + (bu4 * ((structuralBallConst ((13289200973 : ℝ) / 160000000000) + (structuralBallConst ((-1099851 : ℝ) / 1000000) * bv4)) + (structuralBallConst ((118543 : ℝ) / 800000) * bsv))))))) + (bd * ((((structuralBallConst ((-939696734024753 : ℝ) / 32000000000000000) + (structuralBallConst ((-50896794429 : ℝ) / 400000000000) * bq13)) + ((structuralBallConst ((-14403193079 : ℝ) / 200000000000) * bh13) + (structuralBallConst ((-11759363637 : ℝ) / 160000000000) * bdv))) + (((structuralBallConst ((1386087783 : ℝ) / 400000000000) * bv4) + (structuralBallConst ((7416479923 : ℝ) / 160000000000) * bsv)) + ((bsu * ((structuralBallConst ((895751967 : ℝ) / 20000000000) + (structuralBallConst ((27243 : ℝ) / 400000) * bsv)) + ((structuralBallConst ((78501 : ℝ) / 2000000) * bv4) + (structuralBallConst ((118543 : ℝ) / 800000) * bdv)))) + (bdu * ((structuralBallConst ((13289200973 : ℝ) / 160000000000) + (structuralBallConst ((-1099851 : ℝ) / 1000000) * bv4)) + (structuralBallConst ((118543 : ℝ) / 800000) * bsv)))))) + ((bu4 * ((structuralBallConst ((-16031972109 : ℝ) / 400000000000) + (structuralBallConst ((-1099851 : ℝ) / 1000000) * bdv)) + (structuralBallConst ((78501 : ℝ) / 2000000) * bsv))) + (bd * (((structuralBallConst ((1013333899 : ℝ) / 16000000000) + (structuralBallConst ((-1099851 : ℝ) / 500000) * bh13)) + ((structuralBallConst ((-274379 : ℝ) / 1000000) * bq13) + (structuralBallConst ((112341 : ℝ) / 400000) * bsv))) + (bsu * (structuralBallConst ((107651 : ℝ) / 400000) + (structuralBallConst ((1 : ℝ) / 2) * bsv)))))))))))

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
private theorem oddH33Slope_nonneg
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (0 : ℝ) ≤ oddH33Slope X R C D F a x r c d f su du u4 sv dv v4  := by
  let bX := StructuralBall.deviationOfMem hbox.X_mem
  let bR := StructuralBall.deviationOfMem hbox.R_mem
  let bC := StructuralBall.deviationOfMem hbox.C_mem
  let bD := StructuralBall.deviationOfMem hbox.D_mem
  let bF := StructuralBall.deviationOfMem hbox.F_mem
  let ba := StructuralBall.deviationOfMem hbox.a_mem
  let bx := StructuralBall.deviationOfMem hbox.x_mem
  let br := StructuralBall.deviationOfMem hbox.r_mem
  let bc := StructuralBall.deviationOfMem hbox.c_mem
  let bd := StructuralBall.deviationOfMem hbox.d_mem
  let bf := StructuralBall.deviationOfMem hbox.f_mem
  let bsu := StructuralBall.deviationOfMem hbox.su_mem
  let bdu := StructuralBall.deviationOfMem hbox.du_mem
  let bu4 := StructuralBall.deviationOfMem hbox.u4_mem
  let cert := oddH33CenteredCertificate bX bR bC bD bF ba bx br bc bd bf bsu bdu bu4
  have hs := cert.sound
  have hv : cert.value = oddH33Slope X R C D F a x r c d f su du u4 sv dv v4 := by
    simp only [cert, oddH33CenteredCertificate, structuralBallAdd_value,
      structuralBallMul_value, structuralBallConst_value]
    dsimp only [bX, bR, bC, bD, bF, ba, bx, br, bc, bd, bf, bsu, bdu, bu4, StructuralBall.deviationOfMem,
      StructuralBall.deviation]
    unfold oddH33Slope oddB33m oddB33p oddGm oddGx oddGp oddP33 oddM33 oddQ11Corner oddH11Corner alignedDeterminant alignedMixedDeterminant
      alignedAdjugatePair alignedMixedAdjugatePair alignedEntry00
      alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
      mixedDeterminantOne
    ring
  have hc : cert.center = ((138665565705399543 : ℝ) / 2000000000000000000000) := by
    norm_num [cert, oddH33CenteredCertificate, structuralBallAdd_center,
      structuralBallMul_center, structuralBallConst_center,
      bX, bR, bC, bD, bF, ba, bx, br, bc, bd, bf, bsu, bdu, bu4, StructuralBall.deviationOfMem, StructuralBall.deviation]
  have hr : cert.radius = ((1050316772510615697 : ℝ) / 80000000000000000000000) := by
    norm_num [cert, oddH33CenteredCertificate, structuralBallAdd_radius,
      structuralBallMul_radius, structuralBallAdd_center,
      structuralBallMul_center, structuralBallConst_radius,
      structuralBallConst_center, bX, bR, bC, bD, bF, ba, bx, br, bc, bd, bf, bsu, bdu, bu4, StructuralBall.deviationOfMem,
      StructuralBall.deviation]
  have hside := (abs_le.mp hs).1
  rw [hv, hc, hr] at hside
  have hmargin : (0 : ℝ) ≤ ((138665565705399543 : ℝ) / 2000000000000000000000) - ((1050316772510615697 : ℝ) / 80000000000000000000000) := by norm_num
  nlinarith only [hside, hmargin]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
private theorem oddQ33Slope_nonneg
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (0 : ℝ) ≤ oddQ33Slope X R C D F a x r c d f su du u4 sv dv v4 h11  := by
  let bX := StructuralBall.deviationOfMem hbox.X_mem
  let bR := StructuralBall.deviationOfMem hbox.R_mem
  let bC := StructuralBall.deviationOfMem hbox.C_mem
  let bD := StructuralBall.deviationOfMem hbox.D_mem
  let bF := StructuralBall.deviationOfMem hbox.F_mem
  let ba := StructuralBall.deviationOfMem hbox.a_mem
  let bx := StructuralBall.deviationOfMem hbox.x_mem
  let br := StructuralBall.deviationOfMem hbox.r_mem
  let bc := StructuralBall.deviationOfMem hbox.c_mem
  let bd := StructuralBall.deviationOfMem hbox.d_mem
  let bf := StructuralBall.deviationOfMem hbox.f_mem
  let bsu := StructuralBall.deviationOfMem hbox.su_mem
  let bdu := StructuralBall.deviationOfMem hbox.du_mem
  let bu4 := StructuralBall.deviationOfMem hbox.u4_mem
  let bh11 := StructuralBall.deviationOfMem hbox.h11_mem
  let cert := oddQ33CenteredCertificate bX bR bC bD bF ba bx br bc bd bf bsu bdu bu4 bh11
  have hs := cert.sound
  have hv : cert.value = oddQ33Slope X R C D F a x r c d f su du u4 sv dv v4 h11 := by
    simp only [cert, oddQ33CenteredCertificate, structuralBallAdd_value,
      structuralBallMul_value, structuralBallConst_value]
    dsimp only [bX, bR, bC, bD, bF, ba, bx, br, bc, bd, bf, bsu, bdu, bu4, bh11, StructuralBall.deviationOfMem,
      StructuralBall.deviation]
    unfold oddQ33Slope oddB33m oddB33p oddGm oddGx oddGp oddP33 oddM33 oddQ11Corner alignedDeterminant alignedMixedDeterminant
      alignedAdjugatePair alignedMixedAdjugatePair alignedEntry00
      alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
      mixedDeterminantOne
    ring
  have hc : cert.center = ((1535757288518297531 : ℝ) / 8000000000000000000000) := by
    norm_num [cert, oddQ33CenteredCertificate, structuralBallAdd_center,
      structuralBallMul_center, structuralBallConst_center,
      bX, bR, bC, bD, bF, ba, bx, br, bc, bd, bf, bsu, bdu, bu4, bh11, StructuralBall.deviationOfMem, StructuralBall.deviation]
  have hr : cert.radius = ((82708697513035383 : ℝ) / 1250000000000000000000) := by
    norm_num [cert, oddQ33CenteredCertificate, structuralBallAdd_radius,
      structuralBallMul_radius, structuralBallAdd_center,
      structuralBallMul_center, structuralBallConst_radius,
      structuralBallConst_center, bX, bR, bC, bD, bF, ba, bx, br, bc, bd, bf, bsu, bdu, bu4, bh11, StructuralBall.deviationOfMem,
      StructuralBall.deviation]
  have hside := (abs_le.mp hs).1
  rw [hv, hc, hr] at hside
  have hmargin : (0 : ℝ) ≤ ((1535757288518297531 : ℝ) / 8000000000000000000000) - ((82708697513035383 : ℝ) / 1250000000000000000000) := by norm_num
  nlinarith only [hside, hmargin]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
private theorem oddH13Slope_nonpos
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
     oddH13Slope X R C D F a x r c d f su du u4 sv dv v4 h13 ≤ (0 : ℝ) := by
  let bX := StructuralBall.deviationOfMem hbox.X_mem
  let bR := StructuralBall.deviationOfMem hbox.R_mem
  let bC := StructuralBall.deviationOfMem hbox.C_mem
  let bD := StructuralBall.deviationOfMem hbox.D_mem
  let bF := StructuralBall.deviationOfMem hbox.F_mem
  let ba := StructuralBall.deviationOfMem hbox.a_mem
  let bx := StructuralBall.deviationOfMem hbox.x_mem
  let br := StructuralBall.deviationOfMem hbox.r_mem
  let bc := StructuralBall.deviationOfMem hbox.c_mem
  let bd := StructuralBall.deviationOfMem hbox.d_mem
  let bf := StructuralBall.deviationOfMem hbox.f_mem
  let bsu := StructuralBall.deviationOfMem hbox.su_mem
  let bdu := StructuralBall.deviationOfMem hbox.du_mem
  let bu4 := StructuralBall.deviationOfMem hbox.u4_mem
  let bsv := StructuralBall.deviationOfMem hbox.sv_mem
  let bdv := StructuralBall.deviationOfMem hbox.dv_mem
  let bv4 := StructuralBall.deviationOfMem hbox.v4_mem
  let bh13 := StructuralBall.deviationOfMem hbox.h13_mem
  let cert := oddH13CenteredCertificate bX bR bC bD bF ba bx br bc bd bf bsu bdu bu4 bsv bdv bv4 bh13
  have hs := cert.sound
  have hv : cert.value = oddH13Slope X R C D F a x r c d f su du u4 sv dv v4 h13 := by
    simp only [cert, oddH13CenteredCertificate, structuralBallAdd_value,
      structuralBallMul_value, structuralBallConst_value]
    dsimp only [bX, bR, bC, bD, bF, ba, bx, br, bc, bd, bf, bsu, bdu, bu4, bsv, bdv, bv4, bh13, StructuralBall.deviationOfMem,
      StructuralBall.deviation]
    unfold oddH13Slope oddB13m oddB13p oddGm oddGx oddGp oddP13 oddM13 oddQ13Corner oddH13Corner alignedDeterminant alignedMixedDeterminant
      alignedAdjugatePair alignedMixedAdjugatePair alignedEntry00
      alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
      mixedDeterminantOne
    ring
  have hc : cert.center = ((-2972201763503549973 : ℝ) / 16000000000000000000000) := by
    norm_num [cert, oddH13CenteredCertificate, structuralBallAdd_center,
      structuralBallMul_center, structuralBallConst_center,
      bX, bR, bC, bD, bF, ba, bx, br, bc, bd, bf, bsu, bdu, bu4, bsv, bdv, bv4, bh13, StructuralBall.deviationOfMem, StructuralBall.deviation]
  have hr : cert.radius = ((7410049085747068211 : ℝ) / 160000000000000000000000) := by
    norm_num [cert, oddH13CenteredCertificate, structuralBallAdd_radius,
      structuralBallMul_radius, structuralBallAdd_center,
      structuralBallMul_center, structuralBallConst_radius,
      structuralBallConst_center, bX, bR, bC, bD, bF, ba, bx, br, bc, bd, bf, bsu, bdu, bu4, bsv, bdv, bv4, bh13, StructuralBall.deviationOfMem,
      StructuralBall.deviation]
  have hside := (abs_le.mp hs).2
  rw [hv, hc, hr] at hside
  have hmargin : ((-2972201763503549973 : ℝ) / 16000000000000000000000) + ((7410049085747068211 : ℝ) / 160000000000000000000000) ≤ (0 : ℝ) := by norm_num
  nlinarith only [hside, hmargin]

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
private theorem oddQ13Slope_nonpos
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
     oddQ13Slope X R C D F a x r c d f su du u4 sv dv v4 q13 h13 ≤ (0 : ℝ) := by
  let bX := StructuralBall.deviationOfMem hbox.X_mem
  let bR := StructuralBall.deviationOfMem hbox.R_mem
  let bC := StructuralBall.deviationOfMem hbox.C_mem
  let bD := StructuralBall.deviationOfMem hbox.D_mem
  let bF := StructuralBall.deviationOfMem hbox.F_mem
  let ba := StructuralBall.deviationOfMem hbox.a_mem
  let bx := StructuralBall.deviationOfMem hbox.x_mem
  let br := StructuralBall.deviationOfMem hbox.r_mem
  let bc := StructuralBall.deviationOfMem hbox.c_mem
  let bd := StructuralBall.deviationOfMem hbox.d_mem
  let bf := StructuralBall.deviationOfMem hbox.f_mem
  let bsu := StructuralBall.deviationOfMem hbox.su_mem
  let bdu := StructuralBall.deviationOfMem hbox.du_mem
  let bu4 := StructuralBall.deviationOfMem hbox.u4_mem
  let bsv := StructuralBall.deviationOfMem hbox.sv_mem
  let bdv := StructuralBall.deviationOfMem hbox.dv_mem
  let bv4 := StructuralBall.deviationOfMem hbox.v4_mem
  let bq13 := StructuralBall.deviationOfMem hbox.q13_mem
  let bh13 := StructuralBall.deviationOfMem hbox.h13_mem
  let cert := oddQ13CenteredCertificate bX bR bC bD bF ba bx br bc bd bf bsu bdu bu4 bsv bdv bv4 bq13 bh13
  have hs := cert.sound
  have hv : cert.value = oddQ13Slope X R C D F a x r c d f su du u4 sv dv v4 q13 h13 := by
    simp only [cert, oddQ13CenteredCertificate, structuralBallAdd_value,
      structuralBallMul_value, structuralBallConst_value]
    dsimp only [bX, bR, bC, bD, bF, ba, bx, br, bc, bd, bf, bsu, bdu, bu4, bsv, bdv, bv4, bq13, bh13, StructuralBall.deviationOfMem,
      StructuralBall.deviation]
    unfold oddQ13Slope oddB13m oddB13p oddGm oddGx oddGp oddP13 oddM13 oddQ13Corner alignedDeterminant alignedMixedDeterminant
      alignedAdjugatePair alignedMixedAdjugatePair alignedEntry00
      alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
      mixedDeterminantOne
    ring
  have hc : cert.center = ((-3343609688941652051 : ℝ) / 8000000000000000000000) := by
    norm_num [cert, oddQ13CenteredCertificate, structuralBallAdd_center,
      structuralBallMul_center, structuralBallConst_center,
      bX, bR, bC, bD, bF, ba, bx, br, bc, bd, bf, bsu, bdu, bu4, bsv, bdv, bv4, bq13, bh13, StructuralBall.deviationOfMem, StructuralBall.deviation]
  have hr : cert.radius = ((5456511453685090039 : ℝ) / 32000000000000000000000) := by
    norm_num [cert, oddQ13CenteredCertificate, structuralBallAdd_radius,
      structuralBallMul_radius, structuralBallAdd_center,
      structuralBallMul_center, structuralBallConst_radius,
      structuralBallConst_center, bX, bR, bC, bD, bF, ba, bx, br, bc, bd, bf, bsu, bdu, bu4, bsv, bdv, bv4, bq13, bh13, StructuralBall.deviationOfMem,
      StructuralBall.deviation]
  have hside := (abs_le.mp hs).2
  rw [hv, hc, hr] at hside
  have hmargin : ((-3343609688941652051 : ℝ) / 8000000000000000000000) + ((5456511453685090039 : ℝ) / 32000000000000000000000) ≤ (0 : ℝ) := by norm_num
  nlinarith only [hside, hmargin]

set_option maxHeartbeats 3000000 in
/-- The second mixed coefficient of the raw five-mode determinant is
nonnegative. -/
theorem factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient_two_nonneg :
    0 ≤ factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient 2 := by
  rw [coefficient_two_eq_correlated]
  let A := cleanStrong
  let X := cleanSkew
  let R := cleanCrossSum
  let C := cleanWeak
  let D := cleanCrossDifference
  let F := cleanP4
  let a := perturbStrong
  let x := perturbSkew
  let r := perturbCrossSum
  let c := perturbWeak
  let d := perturbCrossDifference
  let f := perturbP4
  let su := u0 + u2
  let du := u0 - u2
  let sv := v0 + v2
  let dv := v0 - v2
  let q11 := yoshidaEndpointOddLowGram11
  let q13 := yoshidaEndpointOddLowGram13
  let q33 := yoshidaEndpointOddLowGram33
  let h11 := factorTwoCenteredSymmetricPerturbation centeredP1
  let h13 := factorTwoCenteredSymmetricPerturbationBilinear centeredP1 centeredP3
  let h33 := factorTwoCenteredSymmetricPerturbation centeredP3
  have hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 := by
    simpa only [A, X, R, C, D, F, a, x, r, c, d, f, su, du, sv, dv,
      q11, q13, q33, h11, h13, h33] using actual_correlated_box
  rcases hbox with
    ⟨hA, hX, hR, hC, hD, hF, ha, hx, hr, hc, hd, hf,
      hsu, hdu, hu4, hsv, hdv, hv4, hq11, hq13, hq33,
      hh11, hh13, hh33⟩
  have hbox' : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 :=
    ⟨hA, hX, hR, hC, hD, hF, ha, hx, hr, hc, hd, hf,
      hsu, hdu, hu4, hsv, hdv, hv4, hq11, hq13, hq33,
      hh11, hh13, hh33⟩
  have hboxQ33Corner : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 oddQ33Corner h11 h13 h33 :=
    { hbox' with q33_mem := by norm_num [oddQ33Corner] }
  have hH33Slope := oddH33Slope_nonneg A X R C D F a x r c d f
    su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox'
  have hH13Slope := oddH13Slope_nonpos A X R C D F a x r c d f
    su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox'
  have hB11mL := oddB11m_lower_bound A X R C D F a x r c d f
    su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox'
  have hB11pL := oddB11p_lower_bound A X R C D F a x r c d f
    su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox'
  have hB11mCornerU := oddB11m_upper_bound A X R C D F a x r c d f
    su du u4 sv dv v4 q11 q13 oddQ33Corner h11 h13 h33 hboxQ33Corner
  have hB11pCornerL := oddB11p_lower_bound A X R C D F a x r c d f
    su du u4 sv dv v4 q11 q13 oddQ33Corner h11 h13 h33 hboxQ33Corner
  have hH11Slope : 0 ≤ oddH11Slope X R C D F a x r c d f
      su du u4 sv dv v4 h33 := by
    unfold oddH11Slope
    rw [oddB11m_eq_core, oddB11p_eq_core]
    nlinarith only [hB11mCornerU, hB11pCornerL]
  have hQ33Slope := oddQ33Slope_nonneg A X R C D F a x r c d f
    su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox'
  have hQ13Slope := oddQ13Slope_nonpos A X R C D F a x r c d f
    su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox'
  have hQ11Slope : 0 ≤ oddQ11Slope X R C D F a x r c d f
      su du u4 sv dv v4 q33 h33 := by
    unfold oddQ11Slope
    rw [oddB11m_eq_core, oddB11p_eq_core]
    nlinarith only [hB11mL, hB11pL]
  have hoddH33 := odd_h33_lower_of_slope
    X R C D F a x r c d f su du u4 sv dv v4 h33
      hh33.1 hH33Slope
  have hoddH13 := odd_h13_lower_of_slope
    X R C D F a x r c d f su du u4 sv dv v4 h13 h33
      hh13.2 hH13Slope
  have hoddH11 := odd_h11_lower_of_slope
    X R C D F a x r c d f su du u4 sv dv v4 h11 h13 h33
      hh11.1 hH11Slope
  have hoddQ33 := odd_q33_lower_of_slope
    X R C D F a x r c d f su du u4 sv dv v4 q33 h11 h13 h33
      hq33.1 hQ33Slope
  have hoddQ13 := odd_q13_lower_of_slope
    X R C D F a x r c d f su du u4 sv dv v4 q13 q33 h11 h13 h33
      hq13.2 hQ13Slope
  have hoddQ11 := odd_q11_lower_of_slope
    X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hq11.1 hQ11Slope
  have hAstep := correlated_A_lower_endpoint
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox'
  have hterminal := terminal_corner_pos
  have hu4step := u4_corner_lower A X R C D F a x r c d f
    su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox'
  have hevenOne := evenBlockOneFace_lower A X R C D F a x r c d f
    su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox'
  have hevenTwo := evenBlockTwoFace_lower A X R C D F a x r c d f
    su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox'
  have halt := alternatingFace_lower A X R C D F a x r c d f
    su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox'
  have hcorner : (0 : ℝ) <
      oddFace X R C D F a x r c d f su du u4 sv dv v4
        oddQ11Corner oddQ13Corner oddQ33Corner
        oddH11Corner oddH13Corner oddH33Corner := by
    calc
      0 < evenBlockOneFace
          (3977 / 100000) (242898 / 1000000) (1323 / 100000)
          (42898 / 1000000) (1571 / 5000) (826465 / 1000000)
          (141 / 1000) := lt_trans (by norm_num) hterminal
      _ ≤ evenBlockOneFace
          (3977 / 100000) (242898 / 1000000) (1323 / 100000)
          (42898 / 1000000) (1571 / 5000) (826465 / 1000000) u4 := hu4step
      _ ≤ evenBlockOneFace X R C D F a u4 := hevenOne
      _ = evenBlockTwoFace X R C D F a
          (37851 / 1000000) (49817 / 1000000) (7165 / 1000000)
          (23317 / 1000000) (4416 / 25000) u4 := rfl
      _ ≤ evenBlockTwoFace X R C D F a x r c d f u4 := hevenTwo
      _ ≤ alternatingFace X R C D F a x r c d f su du u4 sv dv v4 := halt
      _ = oddFace X R C D F a x r c d f su du u4 sv dv v4
          oddQ11Corner oddQ13Corner oddQ33Corner
          oddH11Corner oddH13Corner oddH33Corner :=
        alternatingFace_eq_oddFace_corner X R C D F a x r c d f
          su du u4 sv dv v4
  have hodd : (0 : ℝ) ≤ oddFace X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 := by
    calc
      0 ≤ oddFace X R C D F a x r c d f su du u4 sv dv v4
          oddQ11Corner oddQ13Corner oddQ33Corner
          oddH11Corner oddH13Corner oddH33Corner := hcorner.le
      _ ≤ oddFace X R C D F a x r c d f su du u4 sv dv v4
          oddQ11Corner oddQ13Corner oddQ33Corner
          oddH11Corner oddH13Corner h33 := hoddH33
      _ ≤ oddFace X R C D F a x r c d f su du u4 sv dv v4
          oddQ11Corner oddQ13Corner oddQ33Corner
          oddH11Corner h13 h33 := hoddH13
      _ ≤ oddFace X R C D F a x r c d f su du u4 sv dv v4
          oddQ11Corner oddQ13Corner oddQ33Corner h11 h13 h33 := hoddH11
      _ ≤ oddFace X R C D F a x r c d f su du u4 sv dv v4
          oddQ11Corner oddQ13Corner q33 h11 h13 h33 := hoddQ33
      _ ≤ oddFace X R C D F a x r c d f su du u4 sv dv v4
          oddQ11Corner q13 q33 h11 h13 h33 := hoddQ13
      _ ≤ oddFace X R C D F a x r c d f su du u4 sv dv v4
          q11 q13 q33 h11 h13 h33 := hoddQ11
  exact hodd.trans hAstep

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveC2Structural
