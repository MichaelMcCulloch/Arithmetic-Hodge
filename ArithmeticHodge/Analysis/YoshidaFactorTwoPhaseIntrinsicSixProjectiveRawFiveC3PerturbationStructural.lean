import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveOddMinorStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourC2Structural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourC3Structural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4P3AlternatingSharpStructural

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveC3Structural

noncomputable section

open Polynomial
open CenteredOddOneThreeEnergy
open ThreeByThreePositiveMixedDeterminant
open ThreeByThreeRankOneSchur
open YoshidaEndpointOddFullPolarization
open YoshidaEndpointOcticPotential
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseDiskSchur
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelSharp
open YoshidaFactorTwoPhaseIntrinsicLowStaticMinusRationalSchur
open YoshidaFactorTwoPhaseIntrinsicLowControlStep23EvenSlopeStructural
open YoshidaFactorTwoPhaseIntrinsicOddCleanSharp
open YoshidaFactorTwoPhaseIntrinsicOddPerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicSixP4P1AlternatingStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4PlusEndpointExactSchur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4P3AlternatingSharpStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotSecondSharpStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourC2Structural
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveCoefficientsStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveOddMinorStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateCoefficientsStructural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLowSchur

/-!
# Structural positivity of the third raw five-mode coefficient

This coefficient is the endpoint reversal of the second convolution layer.
The proof keeps that reversal at the level of the even adjugate pencil and
the odd endpoint pencil; it does not enumerate values of the projective
parameter.
-/

def e00p : ℝ := factorTwoStructuralPhaseLow00 1
def e02p : ℝ := factorTwoStructuralPhaseLow02 1
def e04p : ℝ := factorTwoIntrinsicFourP45Cross04 1
def e22p : ℝ := factorTwoStructuralPhaseLow22 1
def e24p : ℝ := factorTwoIntrinsicFourP45Cross24 1
def e44p : ℝ := factorTwoIntrinsicSixP4Diagonal 1

def e00m : ℝ := factorTwoStructuralPhaseLow00 (-1)
def e02m : ℝ := factorTwoStructuralPhaseLow02 (-1)
def e04m : ℝ := factorTwoIntrinsicFourP45Cross04 (-1)
def e22m : ℝ := factorTwoStructuralPhaseLow22 (-1)
def e24m : ℝ := factorTwoIntrinsicFourP45Cross24 (-1)
def e44m : ℝ := factorTwoIntrinsicSixP4Diagonal (-1)

def o11p : ℝ := factorTwoIntrinsicOddPhaseLow11 1
def o13p : ℝ := factorTwoIntrinsicOddPhaseLow13 1
def o33p : ℝ := factorTwoIntrinsicOddPhaseLow33 1
def o11m : ℝ := factorTwoIntrinsicOddPhaseLow11 (-1)
def o13m : ℝ := factorTwoIntrinsicOddPhaseLow13 (-1)
def o33m : ℝ := factorTwoIntrinsicOddPhaseLow33 (-1)

def u0 : ℝ := factorTwoIntrinsicAlternating01
def u2 : ℝ := factorTwoIntrinsicAlternating21
def u4 : ℝ := factorTwoIntrinsicFourP45Cross41
def v0 : ℝ := factorTwoIntrinsicAlternating03
def v2 : ℝ := factorTwoIntrinsicAlternating23
def v4 : ℝ := factorTwoIntrinsicFourP45Cross43

def plusAdjugatePair
    (x0 x2 x4 y0 y2 y4 : ℝ) : ℝ :=
  (e22p * e44p - e24p ^ 2) * x0 * y0 +
    (e04p * e24p - e02p * e44p) * (x0 * y2 + x2 * y0) +
    (e02p * e24p - e04p * e22p) * (x0 * y4 + x4 * y0) +
    (e00p * e44p - e04p ^ 2) * x2 * y2 +
    (e02p * e04p - e00p * e24p) * (x2 * y4 + x4 * y2) +
    (e00p * e22p - e02p ^ 2) * x4 * y4

def minusAdjugatePair
    (x0 x2 x4 y0 y2 y4 : ℝ) : ℝ :=
  (e22m * e44m - e24m ^ 2) * x0 * y0 +
    (e04m * e24m - e02m * e44m) * (x0 * y2 + x2 * y0) +
    (e02m * e24m - e04m * e22m) * (x0 * y4 + x4 * y0) +
    (e00m * e44m - e04m ^ 2) * x2 * y2 +
    (e02m * e04m - e00m * e24m) * (x2 * y4 + x4 * y2) +
    (e00m * e22m - e02m ^ 2) * x4 * y4

def mixedAdjugatePair
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

theorem rawAdjugatePairPolynomial_expansion
    (x0 x2 x4 y0 y2 y4 : ℝ) :
    coefficientRawAdjugatePairPolynomial x0 x2 x4 y0 y2 y4 =
      C (plusAdjugatePair x0 x2 x4 y0 y2 y4) +
        C (mixedAdjugatePair x0 x2 x4 y0 y2 y4) * X +
        C (minusAdjugatePair x0 x2 x4 y0 y2 y4) * X ^ 2 := by
  unfold coefficientRawAdjugatePairPolynomial coefficientLowDetPolynomial
    coefficientLow00Polynomial coefficientLow02Polynomial
    coefficientLow22Polynomial coefficientCross04Polynomial
    coefficientCross24Polynomial coefficientP4DiagonalPolynomial
    endpointAffinePolynomial plusAdjugatePair mixedAdjugatePair minusAdjugatePair
    e00p e02p e04p e22p e24p e44p e00m e02m e04m e22m e24m e44m
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  ring

theorem rawFiveOddMinorCoeff_zero_eq :
    rawFiveOddMinorCoeff 0 = o11p * o33p - o13p ^ 2 := by
  change factorTwoIntrinsicSixProjectiveOddMinorTwoCoefficientPolynomial.coeff 0 = _
  rw [Polynomial.coeff_zero_eq_eval_zero]
  unfold factorTwoIntrinsicSixProjectiveOddMinorTwoCoefficientPolynomial
    coefficientOdd11Polynomial coefficientOdd13Polynomial
    coefficientOdd33Polynomial endpointAffinePolynomial o11p o13p o33p
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X]
  ring

theorem rawFiveOddMinorCoeff_two_eq :
    rawFiveOddMinorCoeff 2 = o11m * o33m - o13m ^ 2 := by
  change factorTwoIntrinsicSixProjectiveOddMinorTwoCoefficientPolynomial.coeff 2 = _
  have hpoly :
      factorTwoIntrinsicSixProjectiveOddMinorTwoCoefficientPolynomial =
        C (o11p * o33p - o13p ^ 2) +
          C (o11p * o33m + o11m * o33p - 2 * o13p * o13m) * X +
          C (o11m * o33m - o13m ^ 2) * X ^ 2 := by
    unfold factorTwoIntrinsicSixProjectiveOddMinorTwoCoefficientPolynomial
      coefficientOdd11Polynomial coefficientOdd13Polynomial
      coefficientOdd33Polynomial endpointAffinePolynomial
      o11p o13p o33p o11m o13m o33m
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    ring
  rw [hpoly]
  simp only [coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow]
  norm_num

theorem coeff_two_affine_mul_quadratic
    (a b p q r : ℝ) :
    ((C a + C b * X) * (C p + C q * X + C r * X ^ 2)).coeff 2 =
      a * r + b * q := by
  rw [show
      (C a + C b * X) * (C p + C q * X + C r * X ^ 2) =
        C (a * p) + C (a * q + b * p) * X +
          C (a * r + b * q) * X ^ 2 + C (b * r) * X ^ 3 by
    simp only [map_add, map_mul]
    ring]
  norm_num
  simp only [← map_mul, ← map_add, coeff_C_mul_X_pow]
  norm_num

theorem coeff_two_two_mul_affine_mul_quadratic
    (a b p q r : ℝ) :
    (2 * (C a + C b * X) *
        (C p + C q * X + C r * X ^ 2)).coeff 2 =
      2 * (a * r + b * q) := by
  rw [show
      2 * (C a + C b * X) * (C p + C q * X + C r * X ^ 2) =
        C (2 * a * p) + C (2 * (a * q + b * p)) * X +
          C (2 * (a * r + b * q)) * X ^ 2 + C (2 * b * r) * X ^ 3 by
    simp only [map_add, map_mul, map_ofNat]
    ring]
  norm_num
  simp only [← map_mul, ← map_add, coeff_C_mul_X_pow]
  norm_num

theorem rawFiveCouplingCoeff_two_eq :
    rawFiveCouplingCoeff 2 =
      o33p * minusAdjugatePair u0 u2 u4 u0 u2 u4 +
        o33m * mixedAdjugatePair u0 u2 u4 u0 u2 u4 -
        2 * (o13p * minusAdjugatePair u0 u2 u4 v0 v2 v4 +
          o13m * mixedAdjugatePair u0 u2 u4 v0 v2 v4) +
        o11p * minusAdjugatePair v0 v2 v4 v0 v2 v4 +
        o11m * mixedAdjugatePair v0 v2 v4 v0 v2 v4 := by
  change
    factorTwoIntrinsicSixProjectiveRawMinorFiveCouplingCoefficientPolynomial.coeff 2 = _
  unfold factorTwoIntrinsicSixProjectiveRawMinorFiveCouplingCoefficientPolynomial
  rw [rawAdjugatePairPolynomial_expansion,
    rawAdjugatePairPolynomial_expansion,
    rawAdjugatePairPolynomial_expansion]
  unfold coefficientOdd11Polynomial coefficientOdd13Polynomial
    coefficientOdd33Polynomial endpointAffinePolynomial
    o11p o13p o33p o11m o13m o33m
  simp only [coeff_add, coeff_sub, coeff_two_affine_mul_quadratic,
    coeff_two_two_mul_affine_mul_quadratic]
  unfold u0 u2 u4 v0 v2 v4
  ring

def minusCrossEnergy : ℝ :=
  let z0 := u2 * v4 - u4 * v2
  let z2 := u4 * v0 - u0 * v4
  let z4 := u0 * v2 - u2 * v0
  e00m * z0 ^ 2 + 2 * e02m * z0 * z2 + 2 * e04m * z0 * z4 +
    e22m * z2 ^ 2 + 2 * e24m * z2 * z4 + e44m * z4 ^ 2

theorem rawFiveCrossEnergyCoeff_one_eq :
    rawFiveCrossEnergyCoeff 1 = minusCrossEnergy := by
  change
    factorTwoIntrinsicSixProjectiveRawMinorFiveCrossEnergyCoefficientPolynomial.coeff 1 = _
  let plusCrossEnergy : ℝ :=
    let z0 := u2 * v4 - u4 * v2
    let z2 := u4 * v0 - u0 * v4
    let z4 := u0 * v2 - u2 * v0
    e00p * z0 ^ 2 + 2 * e02p * z0 * z2 + 2 * e04p * z0 * z4 +
      e22p * z2 ^ 2 + 2 * e24p * z2 * z4 + e44p * z4 ^ 2
  have hpoly :
      factorTwoIntrinsicSixProjectiveRawMinorFiveCrossEnergyCoefficientPolynomial =
        C plusCrossEnergy + C minusCrossEnergy * X := by
    unfold factorTwoIntrinsicSixProjectiveRawMinorFiveCrossEnergyCoefficientPolynomial
      factorTwoIntrinsicSixProjectiveRawMinorFiveCross0Polynomial
      factorTwoIntrinsicSixProjectiveRawMinorFiveCross2Polynomial
      factorTwoIntrinsicSixProjectiveRawMinorFiveCross4Polynomial
      coefficientLow00Polynomial coefficientLow02Polynomial
      coefficientLow22Polynomial coefficientCross04Polynomial
      coefficientCross24Polynomial coefficientP4DiagonalPolynomial
      endpointAffinePolynomial plusCrossEnergy minusCrossEnergy
      e00p e02p e04p e22p e24p e44p e00m e02m e04m e22m e24m e44m
      u0 u2 u4 v0 v2 v4
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    ring
  rw [hpoly]
  simp

theorem coefficient_three_eq_endpoint_reversal :
    factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient 3 =
      pivotCoeff 1 * (o11m * o33m - o13m ^ 2) +
        pivotCoeff 2 *
          (o11p * o33m + o11m * o33p - 2 * o13p * o13m) +
        pivotCoeff 3 * (o11p * o33p - o13p ^ 2) -
        (o33p * minusAdjugatePair u0 u2 u4 u0 u2 u4 +
          o33m * mixedAdjugatePair u0 u2 u4 u0 u2 u4 -
          2 * (o13p * minusAdjugatePair u0 u2 u4 v0 v2 v4 +
            o13m * mixedAdjugatePair u0 u2 u4 v0 v2 v4) +
          o11p * minusAdjugatePair v0 v2 v4 v0 v2 v4 +
          o11m * mixedAdjugatePair v0 v2 v4 v0 v2 v4) +
        minusCrossEnergy := by
  simp only [factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient]
  rw [rawFiveOddMinorCoeff_zero_eq, rawFiveOddMinorCoeff_one_eq,
    rawFiveOddMinorCoeff_two_eq, rawFiveCouplingCoeff_two_eq,
    rawFiveCrossEnergyCoeff_one_eq]
  unfold o11p o13p o33p o11m o13m o33m
  ring

/-! ## Centered aligned realization

The endpoint reversal is encoded by changing the sign of the perturbation
inside one common clean midpoint.  This retains the correlations discarded
by independent endpoint intervals.
-/

def alignedEntry00 (A X C : ℝ) : ℝ := (A + C + 2 * X) / 4
def alignedEntry02 (A C : ℝ) : ℝ := (A - C) / 4
def alignedEntry22 (A X C : ℝ) : ℝ := (A + C - 2 * X) / 4
def alignedEntry04 (R D : ℝ) : ℝ := (R - D) / 2
def alignedEntry24 (R D : ℝ) : ℝ := (R + D) / 2

def alignedDeterminant (A X R C D F : ℝ) : ℝ :=
  (F * (A * C - X ^ 2) - A * D ^ 2 - C * R ^ 2 - 2 * X * R * D) / 4

def alignedMixedDeterminant
    (A X R C D F a x r c d f : ℝ) : ℝ :=
  mixedDeterminantOne
    (alignedEntry00 A X C) (alignedEntry02 A C) (alignedEntry04 R D)
    (alignedEntry22 A X C) (alignedEntry24 R D) F
    (alignedEntry00 a x c) (alignedEntry02 a c) (alignedEntry04 r d)
    (alignedEntry22 a x c) (alignedEntry24 r d) f

def alignedAdjugatePair
    (A X R C D F sx dx zx sy dy zy : ℝ) : ℝ :=
  ((F * C - D ^ 2) * sx * sy +
      (F * A - R ^ 2) * dx * dy -
      (F * X + R * D) * (sx * dy + dx * sy) -
      (C * R + X * D) * (sx * zy + zx * sy) +
      (X * R + A * D) * (dx * zy + zx * dy) +
      (A * C - X ^ 2) * zx * zy) / 4

def alignedMixedAdjugatePair
    (A X R C D F a x r c d f sx dx zx sy dy zy : ℝ) : ℝ :=
  ((F * c + f * C - 2 * D * d) * sx * sy +
      (F * a + f * A - 2 * R * r) * dx * dy -
      (F * x + f * X + R * d + r * D) * (sx * dy + dx * sy) -
      (C * r + c * R + X * d + x * D) * (sx * zy + zx * sy) +
      (X * r + x * R + A * d + a * D) * (dx * zy + zx * dy) +
      (A * c + a * C - 2 * X * x) * zx * zy) / 4

def alignedCrossEnergy
    (A X R C D F su du u4 sv dv v4 : ℝ) : ℝ :=
  let zs := u4 * dv - v4 * du
  let zd := v4 * su - u4 * sv
  let z4 := (du * sv - su * dv) / 2
  (A * zs ^ 2 + 2 * X * zs * zd + C * zd ^ 2 +
      4 * R * zs * z4 - 4 * D * zd * z4 + 4 * F * z4 ^ 2) / 4

def correlatedCoefficientThree
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
  let minusCoupling :=
    o33p * alignedAdjugatePair Am Xm Rm Cm Dm Fm su du u4 su du u4 -
      2 * o13p * alignedAdjugatePair Am Xm Rm Cm Dm Fm su du u4 sv dv v4 +
      o11p * alignedAdjugatePair Am Xm Rm Cm Dm Fm sv dv v4 sv dv v4
  let mixedCoupling :=
    o33m * alignedMixedAdjugatePair Ap Xp Rp Cp Dp Fp
        Am Xm Rm Cm Dm Fm su du u4 su du u4 -
      2 * o13m * alignedMixedAdjugatePair Ap Xp Rp Cp Dp Fp
        Am Xm Rm Cm Dm Fm su du u4 sv dv v4 +
      o11m * alignedMixedAdjugatePair Ap Xp Rp Cp Dp Fp
        Am Xm Rm Cm Dm Fm sv dv v4 sv dv v4
  alignedMixedDeterminant Ap Xp Rp Cp Dp Fp Am Xm Rm Cm Dm Fm * oddMinus +
    alignedMixedDeterminant Am Xm Rm Cm Dm Fm Ap Xp Rp Cp Dp Fp * oddMixed +
    alignedDeterminant Am Xm Rm Cm Dm Fm * oddPlus -
    minusCoupling - mixedCoupling +
    alignedCrossEnergy Am Xm Rm Cm Dm Fm su du u4 sv dv v4

theorem alignedDeterminant_eq
    (q00 q02 q04 q22 q24 q44 : ℝ) :
    alignedDeterminant
        (q00 + 2 * q02 + q22) (q00 - q22) (q04 + q24)
        (q00 - 2 * q02 + q22) (q24 - q04) q44 =
      symmetricDeterminant q00 q02 q04 q22 q24 q44 := by
  unfold alignedDeterminant symmetricDeterminant
  ring

theorem alignedMixedDeterminant_eq
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
  ring_nf

theorem alignedAdjugatePair_eq
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

theorem alignedMixedAdjugatePair_eq
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

theorem alignedCrossEnergy_eq
    (q00 q02 q04 q22 q24 q44 x0 x2 x4 y0 y2 y4 : ℝ) :
    alignedCrossEnergy
        (q00 + 2 * q02 + q22) (q00 - q22) (q04 + q24)
        (q00 - 2 * q02 + q22) (q24 - q04) q44
        (x0 + x2) (x0 - x2) x4 (y0 + y2) (y0 - y2) y4 =
      let z0 := x2 * y4 - x4 * y2
      let z2 := x4 * y0 - x0 * y4
      let z4 := x0 * y2 - x2 * y0
      q00 * z0 ^ 2 + 2 * q02 * z0 * z2 + 2 * q04 * z0 * z4 +
        q22 * z2 ^ 2 + 2 * q24 * z2 * z4 + q44 * z4 ^ 2 := by
  unfold alignedCrossEnergy
  dsimp only
  ring

theorem endpoint_aligned_coordinates :
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
  unfold YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotSecondSharpStructural.cleanCrossSum
    YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotSecondSharpStructural.cleanCrossDifference
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

theorem pivot_polynomial_expansion :
    factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial =
      C (symmetricDeterminant e00p e02p e04p e22p e24p e44p) +
        C (mixedDeterminantOne
          e00p e02p e04p e22p e24p e44p
          e00m e02m e04m e22m e24m e44m) * X +
        C (mixedDeterminantOne
          e00m e02m e04m e22m e24m e44m
          e00p e02p e04p e22p e24p e44p) * X ^ 2 +
        C (symmetricDeterminant e00m e02m e04m e22m e24m e44m) * X ^ 3 := by
  unfold factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial
    coefficientAdjugateTwoPolynomial coefficientLowDetPolynomial
    coefficientLow00Polynomial coefficientLow02Polynomial
    coefficientLow22Polynomial coefficientCross04Polynomial
    coefficientCross24Polynomial coefficientP4DiagonalPolynomial
    endpointAffinePolynomial symmetricDeterminant mixedDeterminantOne
    e00p e02p e04p e22p e24p e44p e00m e02m e04m e22m e24m e44m
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  ring

theorem pivot_coefficients_eq_correlated :
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
        (cleanCrossDifference - perturbCrossDifference) (cleanP4 - perturbP4) ∧
      pivotCoeff 3 = alignedDeterminant
        (cleanStrong + perturbStrong) (cleanSkew + perturbSkew)
        (cleanCrossSum + perturbCrossSum) (cleanWeak + perturbWeak)
        (cleanCrossDifference + perturbCrossDifference) (cleanP4 + perturbP4) := by
  rcases endpoint_aligned_coordinates with
    ⟨hAp, hXp, hRp, hCp, hDp, hFp, hAm, hXm, hRm, hCm, hDm, hFm⟩
  constructor
  · change factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial.coeff 1 = _
    rw [hAp, hXp, hRp, hCp, hDp, hFp, hAm, hXm, hRm, hCm, hDm, hFm,
      alignedMixedDeterminant_eq, pivot_polynomial_expansion]
    simp
  constructor
  · change factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial.coeff 2 = _
    rw [hAm, hXm, hRm, hCm, hDm, hFm, hAp, hXp, hRp, hCp, hDp, hFp,
      alignedMixedDeterminant_eq, pivot_polynomial_expansion]
    simp
  · change factorTwoIntrinsicSixProjectiveP4PivotCoefficientPolynomial.coeff 3 = _
    rw [hAm, hXm, hRm, hCm, hDm, hFm, alignedDeterminant_eq,
      pivot_polynomial_expansion]
    simp

theorem adjugate_pairs_eq_correlated
    (x0 x2 x4 y0 y2 y4 : ℝ) :
    minusAdjugatePair x0 x2 x4 y0 y2 y4 =
        alignedAdjugatePair
          (cleanStrong + perturbStrong) (cleanSkew + perturbSkew)
          (cleanCrossSum + perturbCrossSum) (cleanWeak + perturbWeak)
          (cleanCrossDifference + perturbCrossDifference) (cleanP4 + perturbP4)
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
  · rw [hAm, hXm, hRm, hCm, hDm, hFm, alignedAdjugatePair_eq]
    rfl
  · rw [hAp, hXp, hRp, hCp, hDp, hFp, hAm, hXm, hRm, hCm, hDm, hFm,
      alignedMixedAdjugatePair_eq]
    rfl

theorem minusCrossEnergy_eq_correlated :
    minusCrossEnergy = alignedCrossEnergy
      (cleanStrong + perturbStrong) (cleanSkew + perturbSkew)
      (cleanCrossSum + perturbCrossSum) (cleanWeak + perturbWeak)
      (cleanCrossDifference + perturbCrossDifference) (cleanP4 + perturbP4)
      (u0 + u2) (u0 - u2) u4 (v0 + v2) (v0 - v2) v4 := by
  rcases endpoint_aligned_coordinates with
    ⟨_, _, _, _, _, _, hAm, hXm, hRm, hCm, hDm, hFm⟩
  rw [hAm, hXm, hRm, hCm, hDm, hFm, alignedCrossEnergy_eq]
  rfl

set_option maxHeartbeats 1200000 in
theorem coefficient_three_eq_correlated :
    factorTwoIntrinsicSixProjectiveRawMinorFiveCoefficient 3 =
      correlatedCoefficientThree
        cleanStrong cleanSkew cleanCrossSum cleanWeak cleanCrossDifference cleanP4
        perturbStrong perturbSkew perturbCrossSum perturbWeak
        perturbCrossDifference perturbP4
        (u0 + u2) (u0 - u2) u4 (v0 + v2) (v0 - v2) v4
        yoshidaEndpointOddLowGram11 yoshidaEndpointOddLowGram13
        yoshidaEndpointOddLowGram33
        (factorTwoCenteredSymmetricPerturbation centeredP1)
        (factorTwoCenteredSymmetricPerturbationBilinear centeredP1 centeredP3)
        (factorTwoCenteredSymmetricPerturbation centeredP3) := by
  rw [coefficient_three_eq_endpoint_reversal]
  unfold correlatedCoefficientThree
  dsimp only
  rw [pivot_coefficients_eq_correlated.1,
    pivot_coefficients_eq_correlated.2.1,
    pivot_coefficients_eq_correlated.2.2,
    (adjugate_pairs_eq_correlated u0 u2 u4 u0 u2 u4).1,
    (adjugate_pairs_eq_correlated u0 u2 u4 u0 u2 u4).2,
    (adjugate_pairs_eq_correlated u0 u2 u4 v0 v2 v4).1,
    (adjugate_pairs_eq_correlated u0 u2 u4 v0 v2 v4).2,
    (adjugate_pairs_eq_correlated v0 v2 v4 v0 v2 v4).1,
    (adjugate_pairs_eq_correlated v0 v2 v4 v0 v2 v4).2,
    minusCrossEnergy_eq_correlated]
  unfold o11p o13p o33p o11m o13m o33m
    factorTwoIntrinsicOddPhaseLow11 factorTwoIntrinsicOddPhaseLow13
    factorTwoIntrinsicOddPhaseLow33
  ring

structure CorrelatedBox
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

theorem actual_correlated_box :
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

def quadraticSecant (g : ℝ → ℝ) (s t : ℝ) : ℝ :=
  ((g 1 + g (-1) - 2 * g 0) / 2) * (s + t) + (g 1 - g (-1)) / 2

theorem quadraticSecant_lower_endpoint
    (g : ℝ → ℝ) (x lo : ℝ) (hx : lo ≤ x)
    (hsec : 0 ≤ quadraticSecant g x lo)
    (hid : g x - g lo = (x - lo) * quadraticSecant g x lo) :
    g lo ≤ g x := by
  rw [← sub_nonneg, hid]
  exact mul_nonneg (sub_nonneg.mpr hx) hsec

theorem quadraticSecant_upper_endpoint
    (g : ℝ → ℝ) (x hi : ℝ) (hx : x ≤ hi)
    (hsec : quadraticSecant g x hi ≤ 0)
    (hid : g x - g hi = (x - hi) * quadraticSecant g x hi) :
    g hi ≤ g x := by
  rw [← sub_nonneg, hid]
  exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hx) hsec

theorem nonnegative_product_lower
    (a b aL bL : ℝ) (ha : aL ≤ a) (hb : bL ≤ b)
    (haL : 0 ≤ aL) (hb0 : 0 ≤ b) :
    aL * bL ≤ a * b := by
  have h1 := mul_nonneg (sub_nonneg.mpr ha) hb0
  have h2 := mul_nonneg haL (sub_nonneg.mpr hb)
  nlinarith only [h1, h2]

theorem nonnegative_product_upper
    (a b aU bU : ℝ) (ha : a ≤ aU) (hb : b ≤ bU)
    (haU : 0 ≤ aU) (hb0 : 0 ≤ b) :
    a * b ≤ aU * bU := by
  have h1 := mul_nonneg (sub_nonneg.mpr ha) hb0
  have h2 := mul_nonneg haU (sub_nonneg.mpr hb)
  nlinarith only [h1, h2]

theorem nonnegative_triple_lower
    (a b c aL bL cL : ℝ)
    (ha : aL ≤ a) (hb : bL ≤ b) (hc : cL ≤ c)
    (haL0 : 0 ≤ aL) (hbL0 : 0 ≤ bL)
    (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) :
    aL * bL * cL ≤ a * b * c := by
  have hab := nonnegative_product_lower a b aL bL ha hb haL0 hb0
  exact nonnegative_product_lower (a * b) c (aL * bL) cL
    hab hc (mul_nonneg haL0 hbL0) hc0

theorem nonnegative_triple_upper
    (a b c aU bU cU : ℝ)
    (ha : a ≤ aU) (hb : b ≤ bU) (hc : c ≤ cU)
    (haU0 : 0 ≤ aU) (hbU0 : 0 ≤ bU)
    (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) :
    a * b * c ≤ aU * bU * cU := by
  have hab := nonnegative_product_upper a b aU bU ha hb haU0 hb0
  exact nonnegative_product_upper (a * b) c (aU * bU) cU
    hab hc (mul_nonneg haU0 hbU0) hc0

theorem positive_negative_product_lower
    (a b aU bL : ℝ) (ha0 : 0 ≤ a) (hb : bL ≤ b)
    (hbL : bL ≤ 0) (ha : a ≤ aU) :
    aU * bL ≤ a * b := by
  have h1 := mul_nonneg ha0 (sub_nonneg.mpr hb)
  have h2 := mul_nonneg_of_nonpos_of_nonpos hbL (sub_nonpos.mpr ha)
  nlinarith only [h1, h2]

theorem positive_negative_product_upper
    (a b aL bU : ℝ) (ha : aL ≤ a) (hb0 : b ≤ 0)
    (haL : 0 ≤ aL) (hb : b ≤ bU) :
    a * b ≤ aL * bU := by
  have h1 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ha) hb0
  have h2 := mul_nonpos_of_nonneg_of_nonpos haL (sub_nonpos.mpr hb)
  nlinarith only [h1, h2]

theorem nonnegative_negative_triple_lower
    (a b c aU bU cL : ℝ)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc : cL ≤ c)
    (ha : a ≤ aU) (hb : b ≤ bU)
    (haU0 : 0 ≤ aU) (hcL0 : cL ≤ 0) :
    aU * bU * cL ≤ a * b * c := by
  have hab := nonnegative_product_upper a b aU bU ha hb haU0 hb0
  exact positive_negative_product_lower (a * b) c (aU * bU) cL
    (mul_nonneg ha0 hb0) hc hcL0 hab

theorem nonnegative_negative_triple_upper
    (a b c aL bL cU : ℝ)
    (ha : aL ≤ a) (hb : bL ≤ b) (hc0 : c ≤ 0)
    (hc : c ≤ cU) (haL0 : 0 ≤ aL) (hbL0 : 0 ≤ bL) :
    a * b * c ≤ aL * bL * cU := by
  have hab := nonnegative_product_lower a b aL bL ha hb haL0
    (le_trans hbL0 hb)
  exact positive_negative_product_upper (a * b) c (aL * bL) cU
    hab hc0 (mul_nonneg haL0 hbL0) hc

def alignedAdjugateASlope
    (F C D dx zx dy zy : ℝ) : ℝ :=
  (F * dx * dy + D * (dx * zy + zx * dy) + C * zx * zy) / 4

def alignedMixedAdjugateBothASlope
    (F C D dx zx dy zy : ℝ) : ℝ :=
  (F * dx * dy + D * (dx * zy + zx * dy) + C * zx * zy) / 2

def oddCouplingD
    (du dv o11 o13 o33 : ℝ) : ℝ :=
  o33 * du ^ 2 - 2 * o13 * du * dv + o11 * dv ^ 2

def oddCouplingCross
    (du u4 dv v4 o11 o13 o33 : ℝ) : ℝ :=
  o33 * du * u4 - o13 * (du * v4 + u4 * dv) + o11 * dv * v4

def oddCouplingFour
    (u4 v4 o11 o13 o33 : ℝ) : ℝ :=
  o33 * u4 ^ 2 - 2 * o13 * u4 * v4 + o11 * v4 ^ 2

def oddCouplingCore
    (F C D du u4 dv v4 o11 o13 o33 : ℝ) : ℝ :=
  F * oddCouplingD du dv o11 o13 o33 +
    2 * D * oddCouplingCross du u4 dv v4 o11 o13 o33 +
      C * oddCouplingFour u4 v4 o11 o13 o33

theorem oddCouplingCore_du_step
    (F C D du du0 u4 dv v4 o11 o13 o33 : ℝ) :
    oddCouplingCore F C D du u4 dv v4 o11 o13 o33 -
        oddCouplingCore F C D du0 u4 dv v4 o11 o13 o33 =
      (du - du0) *
        (F * (o33 * (du + du0) - 2 * o13 * dv) +
          2 * D * (o33 * u4 - o13 * v4)) := by
  unfold oddCouplingCore oddCouplingD oddCouplingCross oddCouplingFour
  ring

theorem oddCouplingCore_u4_step
    (F C D du u4 u40 dv v4 o11 o13 o33 : ℝ) :
    oddCouplingCore F C D du u4 dv v4 o11 o13 o33 -
        oddCouplingCore F C D du u40 dv v4 o11 o13 o33 =
      (u4 - u40) *
        (2 * D * (o33 * du - o13 * dv) +
          C * (o33 * (u4 + u40) - 2 * o13 * v4)) := by
  unfold oddCouplingCore oddCouplingD oddCouplingCross oddCouplingFour
  ring

theorem oddCouplingCore_dv_step
    (F C D du u4 dv dv0 v4 o11 o13 o33 : ℝ) :
    oddCouplingCore F C D du u4 dv v4 o11 o13 o33 -
        oddCouplingCore F C D du u4 dv0 v4 o11 o13 o33 =
      (dv - dv0) *
        (F * (o11 * (dv + dv0) - 2 * o13 * du) +
          2 * D * (o11 * v4 - o13 * u4)) := by
  unfold oddCouplingCore oddCouplingD oddCouplingCross oddCouplingFour
  ring

theorem oddCouplingCore_v4_step
    (F C D du u4 dv v4 v40 o11 o13 o33 : ℝ) :
    oddCouplingCore F C D du u4 dv v4 o11 o13 o33 -
        oddCouplingCore F C D du u4 dv v40 o11 o13 o33 =
      (v4 - v40) *
        (2 * D * (o11 * dv - o13 * du) +
          C * (o11 * (v4 + v40) - 2 * o13 * u4)) := by
  unfold oddCouplingCore oddCouplingD oddCouplingCross oddCouplingFour
  ring

def correlatedThreeASlope
    (C D F c d f du u4 dv v4 q11 q13 q33 h11 h13 h33 : ℝ) : ℝ :=
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
  let minusCouplingSlope :=
    o33p * alignedAdjugateASlope Fm Cm Dm du u4 du u4 -
      2 * o13p * alignedAdjugateASlope Fm Cm Dm du u4 dv v4 +
      o11p * alignedAdjugateASlope Fm Cm Dm dv v4 dv v4
  let mixedCouplingSlope :=
    o33m * alignedMixedAdjugateBothASlope F C D du u4 du u4 -
      2 * o13m * alignedMixedAdjugateBothASlope F C D du u4 dv v4 +
      o11m * alignedMixedAdjugateBothASlope F C D dv v4 dv v4
  ((Fm * Cp + Fp * Cm - 2 * Dp * Dm + Fp * Cp - Dp ^ 2) / 4) *
      oddMinus +
    ((Fp * Cm + Fm * Cp - 2 * Dp * Dm + Fm * Cm - Dm ^ 2) / 4) *
      oddMixed +
    ((Fm * Cm - Dm ^ 2) / 4) * oddPlus -
    minusCouplingSlope - mixedCouplingSlope + (u4 * dv - v4 * du) ^ 2 / 4

theorem correlated_A_secant_eq
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ) :
    quadraticSecant
      (fun z ↦ correlatedCoefficientThree z X R C D F a x r c d f
        su du u4 sv dv v4 q11 q13 q33 h11 h13 h33)
      A (137423 / 100000) =
        correlatedThreeASlope C D F c d f du u4 dv v4
          q11 q13 q33 h11 h13 h33 := by
  unfold quadraticSecant correlatedCoefficientThree correlatedThreeASlope
    alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
    alignedMixedAdjugatePair alignedCrossEnergy alignedAdjugateASlope
    alignedMixedAdjugateBothASlope alignedEntry00 alignedEntry02 alignedEntry04
    alignedEntry22 alignedEntry24 mixedDeterminantOne
  dsimp only
  ring

set_option maxHeartbeats 500000 in
theorem oddASlope_bounds
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
    have hqProd : (1778 / 10000 : ℝ) * (3315 / 10000) ≤
        q11 * q33 := by bound
    have hq13Nonneg : 0 ≤ q13 := by linarith
    have hqSq : q13 ^ 2 ≤ (2002 / 10000 : ℝ) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hq13U)
        (by norm_num; linarith : 0 ≤ q13 + 2002 / 10000)]
    have hhProd : (14 / 1000 : ℝ) * (117 / 1000) ≤
        h11 * (-h33) := by bound
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
theorem evenASlopeDeterminant_bounds
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (91 / 100000 : ℝ) ≤
        ((F + f) * (C - c) + (F - f) * (C + c) -
          2 * (D - d) * (D + d) +
          (F - f) * (C - c) - (D - d) ^ 2) / 4 ∧
      (21 / 10000 : ℝ) ≤
        ((F - f) * (C + c) + (F + f) * (C - c) -
          2 * (D - d) * (D + d) +
          (F + f) * (C + c) - (D + d) ^ 2) / 4 ∧
      (1 / 1000 : ℝ) ≤ ((F + f) * (C + c) - (D + d) ^ 2) / 4 := by
  rcases hbox.C_mem with ⟨hCL, hCU⟩
  rcases hbox.D_mem with ⟨hDL, hDU⟩
  rcases hbox.F_mem with ⟨hFL, hFU⟩
  rcases hbox.c_mem with ⟨hcL, hcU⟩
  rcases hbox.d_mem with ⟨hdL, hdU⟩
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  have hDetOne : (91 / 100000 : ℝ) ≤
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
  have hDetTwo : (21 / 10000 : ℝ) ≤
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
  have hDetThree : (1 / 1000 : ℝ) ≤
      ((F + f) * (C + c) - (D + d) ^ 2) / 4 := by
    have hFC :
        ((1571 / 5000 + 4411 / 25000) *
          (1323 / 100000 + 5179 / 1000000) : ℝ) ≤
            (F + f) * (C + c) := by
      have h1 := mul_nonneg
        (by linarith : 0 ≤ (F + f) - (1571 / 5000 + 4411 / 25000))
        (by linarith : 0 ≤ C + c)
      have h2 := mul_nonneg
        (by norm_num : (0 : ℝ) ≤ 1571 / 5000 + 4411 / 25000)
        (by linarith : 0 ≤ (C + c) - (1323 / 100000 + 5179 / 1000000))
      nlinarith
    have hDs : (D + d) ^ 2 ≤
        (42898 / 1000000 + 27183 / 1000000 : ℝ) ^ 2 := by
      nlinarith [mul_nonneg
        (by linarith : 0 ≤ (42898 / 1000000 + 27183 / 1000000) - (D + d))
        (by linarith : 0 ≤ (42898 / 1000000 + 27183 / 1000000) + (D + d))]
    have hc : (1 / 1000 : ℝ) ≤
        (((1571 / 5000 + 4411 / 25000) *
          (1323 / 100000 + 5179 / 1000000) -
            (42898 / 1000000 + 27183 / 1000000) ^ 2) / 4) := by
      norm_num
    nlinarith only [hFC, hDs, hc]
  exact ⟨hDetOne, hDetTwo, hDetThree⟩

set_option maxHeartbeats 1000000 in
theorem plusEndASlopeCoupling_upper
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
      (q33 + h33) *
            (((F + f) * du * du + (D + d) * (du * u4 + u4 * du) +
              (C + c) * u4 * u4) / 4) -
          2 * (q13 + h13) *
            (((F + f) * du * dv + (D + d) * (du * v4 + u4 * dv) +
              (C + c) * u4 * v4) / 4) +
          (q11 + h11) *
              (((F + f) * dv * dv + (D + d) * (dv * v4 + v4 * dv) +
                (C + c) * v4 * v4) / 4) ≤
        (32 / 1000000 : ℝ) := by
  have hOddPlus := (oddASlope_bounds
    A X R C D F a x r c d f
    su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox).2.2
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
    (q33 + h33) *
          (((F + f) * du * du + (D + d) * (du * u4 + u4 * du) +
            (C + c) * u4 * u4) / 4) -
        2 * (q13 + h13) *
          (((F + f) * du * dv + (D + d) * (du * v4 + u4 * dv) +
            (C + c) * u4 * v4) / 4) +
        (q11 + h11) *
            (((F + f) * dv * dv + (D + d) * (dv * v4 + v4 * dv) +
              (C + c) * v4 * v4) / 4) =
      oddCouplingCore (F + f) (C + c) (D + d) du u4 dv v4
        (q11 + h11) (q13 + h13) (q33 + h33) / 4 by
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
      (12291 / 25000 : ℝ) * du ^ 2 +
        2 * (33067 / 500000) * du * u4 +
          (4117 / 200000) * u4 ^ 2 := by positivity
  have hQvPos : 0 ≤
      (12291 / 25000 : ℝ) * dv ^ 2 +
        2 * (33067 / 500000) * dv * v4 +
          (4117 / 200000) * v4 ^ 2 := by
    have hfirst : (12291 / 25000 : ℝ) * (555 / 10000) ^ 2 ≤
        (12291 / 25000) * dv ^ 2 := by bound
    have hcross : 2 * (33067 / 500000 : ℝ) * dv * v4 ≥
        2 * (33067 / 500000) * (558 / 10000) * (-4 / 1000) := by
      have hmag : dv * (-v4) ≤ (558 / 10000 : ℝ) * (4 / 1000) := by
        bound
      calc
        2 * (33067 / 500000 : ℝ) * dv * v4 =
            -(2 * (33067 / 500000) * (dv * (-v4))) := by ring
        _ ≥ -(2 * (33067 / 500000) * ((558 / 10000) * (4 / 1000))) :=
          neg_le_neg (mul_le_mul_of_nonneg_left hmag (by norm_num))
        _ = 2 * (33067 / 500000) * (558 / 10000) * (-4 / 1000) := by ring
    nlinarith [sq_nonneg v4]
  have hQuvPos : 0 ≤
      (12291 / 25000 : ℝ) * du * dv +
        (33067 / 500000) * (du * v4 + u4 * dv) +
          (4117 / 200000) * u4 * v4 := by
    have hfirst : (12291 / 25000 : ℝ) * (1687 / 100000) *
        (555 / 10000) ≤ (12291 / 25000) * du * dv := by bound
    have hmiddle : (33067 / 500000 : ℝ) *
        ((1692 / 100000) * (-4 / 1000) +
          (141 / 1000) * (555 / 10000)) ≤
        (33067 / 500000) * (du * v4 + u4 * dv) := by linarith
    have hlast : (4117 / 200000 : ℝ) * u4 * v4 ≥
        (4117 / 200000) * (144 / 1000) * (-4 / 1000) := by
      have hmag : u4 * (-v4) ≤ (144 / 1000 : ℝ) * (4 / 1000) := by
        bound
      calc
        (4117 / 200000 : ℝ) * u4 * v4 =
            -((4117 / 200000) * (u4 * (-v4))) := by ring
        _ ≥ -((4117 / 200000) * ((144 / 1000) * (4 / 1000))) :=
          neg_le_neg (mul_le_mul_of_nonneg_left hmag (by norm_num))
        _ = (4117 / 200000) * (144 / 1000) * (-4 / 1000) := by ring
    norm_num at hfirst hmiddle hlast ⊢
    linarith only [hfirst, hmiddle, hlast]
  have hcore :
      oddCouplingCore (F + f) (C + c) (D + d) du u4 dv v4
          (q11 + h11) (q13 + h13) (q33 + h33) ≤
        oddCouplingCore (12291 / 25000) (4117 / 200000) (33067 / 500000)
          (1687 / 100000) (144 / 1000) (558 / 10000) (-4 / 1000)
          (199 / 1000) (189 / 1000) (216 / 1000) := by
    calc
      oddCouplingCore (F + f) (C + c) (D + d) du u4 dv v4
          (q11 + h11) (q13 + h13) (q33 + h33) ≤
          oddCouplingCore (12291 / 25000) (C + c) (D + d) du u4 dv v4
            (q11 + h11) (q13 + h13) (q33 + h33) := by
              rw [← sub_nonneg]
              convert mul_nonneg
                  (by linarith : 0 ≤ (12291 / 25000 : ℝ) - (F + f))
                  hEDpos using 1 <;> unfold oddCouplingCore <;> ring
      _ ≤ oddCouplingCore (12291 / 25000) (4117 / 200000) (D + d)
            du u4 dv v4 (q11 + h11) (q13 + h13) (q33 + h33) := by
              rw [← sub_nonneg]
              convert mul_nonneg
                  (by linarith : 0 ≤ (4117 / 200000 : ℝ) - (C + c))
                  hEFpos using 1 <;> unfold oddCouplingCore <;> ring
      _ ≤ oddCouplingCore (12291 / 25000) (4117 / 200000) (33067 / 500000)
            du u4 dv v4 (q11 + h11) (q13 + h13) (q33 + h33) := by
              rw [← sub_nonneg]
              convert mul_nonneg_of_nonpos_of_nonpos
                  (by linarith : (2 : ℝ) * (33067 / 500000 - (D + d)) ≤ 0)
                  hEXneg using 1 <;> unfold oddCouplingCore <;> ring
      _ ≤ oddCouplingCore (12291 / 25000) (4117 / 200000) (33067 / 500000)
            du u4 dv v4 (q11 + h11) (q13 + h13) (216 / 1000) := by
              rw [← sub_nonneg]
              convert mul_nonneg
                  (by linarith : 0 ≤ (216 / 1000 : ℝ) - (q33 + h33))
                  hQuPos using 1 <;>
                unfold oddCouplingCore oddCouplingD oddCouplingCross
                  oddCouplingFour <;> ring
      _ ≤ oddCouplingCore (12291 / 25000) (4117 / 200000) (33067 / 500000)
            du u4 dv v4 (q11 + h11) (189 / 1000) (216 / 1000) := by
              rw [← sub_nonneg]
              convert mul_nonneg
                  (by linarith : 0 ≤ 2 * ((q13 + h13) - 189 / 1000))
                  hQuvPos using 1 <;>
                unfold oddCouplingCore oddCouplingD oddCouplingCross
                  oddCouplingFour <;> ring
      _ ≤ oddCouplingCore (12291 / 25000) (4117 / 200000) (33067 / 500000)
            du u4 dv v4 (199 / 1000) (189 / 1000) (216 / 1000) := by
              rw [← sub_nonneg]
              convert mul_nonneg
                  (by linarith : 0 ≤ (199 / 1000 : ℝ) - (q11 + h11))
                  hQvPos using 1 <;>
                unfold oddCouplingCore oddCouplingD oddCouplingCross
                  oddCouplingFour <;> ring
      _ ≤ oddCouplingCore (12291 / 25000) (4117 / 200000) (33067 / 500000)
            (1687 / 100000) u4 dv v4
            (199 / 1000) (189 / 1000) (216 / 1000) := by
              rw [← sub_nonpos, oddCouplingCore_du_step]
              have hslope :
                  (12291 / 25000 : ℝ) *
                      ((216 / 1000) * (du + 1687 / 100000) -
                        2 * (189 / 1000) * dv) +
                    2 * (33067 / 500000) *
                      ((216 / 1000) * u4 - (189 / 1000) * v4) ≤ 0 := by
                norm_num at ⊢
                linarith
              exact mul_nonpos_of_nonneg_of_nonpos (by linarith) hslope
      _ ≤ oddCouplingCore (12291 / 25000) (4117 / 200000) (33067 / 500000)
            (1687 / 100000) (144 / 1000) dv v4
            (199 / 1000) (189 / 1000) (216 / 1000) := by
              rw [← sub_nonneg, oddCouplingCore_u4_step]
              have hslope : 0 ≤
                  2 * (33067 / 500000 : ℝ) *
                      ((216 / 1000) * (1687 / 100000) -
                        (189 / 1000) * dv) +
                    (4117 / 200000) *
                      ((216 / 1000) * (u4 + 144 / 1000) -
                        2 * (189 / 1000) * v4) := by
                norm_num at ⊢
                linarith
              simpa [add_comm] using mul_nonneg (by linarith) hslope
      _ ≤ oddCouplingCore (12291 / 25000) (4117 / 200000) (33067 / 500000)
            (1687 / 100000) (144 / 1000) (558 / 10000) v4
            (199 / 1000) (189 / 1000) (216 / 1000) := by
              rw [← sub_nonneg, oddCouplingCore_dv_step]
              have hslope : 0 ≤
                  (12291 / 25000 : ℝ) *
                      ((199 / 1000) * (dv + 558 / 10000) -
                        2 * (189 / 1000) * (1687 / 100000)) +
                    2 * (33067 / 500000) *
                      ((199 / 1000) * v4 -
                        (189 / 1000) * (144 / 1000)) := by
                norm_num at ⊢
                linarith
              simpa [add_comm] using mul_nonneg (by linarith) hslope
      _ ≤ oddCouplingCore (12291 / 25000) (4117 / 200000) (33067 / 500000)
            (1687 / 100000) (144 / 1000) (558 / 10000) (-4 / 1000)
            (199 / 1000) (189 / 1000) (216 / 1000) := by
              rw [← sub_nonpos, oddCouplingCore_v4_step]
              have hslope :
                  2 * (33067 / 500000 : ℝ) *
                      ((199 / 1000) * (558 / 10000) -
                        (189 / 1000) * (1687 / 100000)) +
                    (4117 / 200000) *
                      ((199 / 1000) * (v4 + (-4 / 1000)) -
                        2 * (189 / 1000) * (144 / 1000)) ≤ 0 := by
                norm_num at ⊢
                linarith
              exact mul_nonpos_of_nonneg_of_nonpos (by linarith) hslope
  calc
    oddCouplingCore (F + f) (C + c) (D + d) du u4 dv v4
        (q11 + h11) (q13 + h13) (q33 + h33) / 4 ≤
        oddCouplingCore (12291 / 25000) (4117 / 200000) (33067 / 500000)
          (1687 / 100000) (144 / 1000) (558 / 10000) (-4 / 1000)
          (199 / 1000) (189 / 1000) (216 / 1000) / 4 := by
            nlinarith only [hcore]
    _ ≤ (32 / 1000000 : ℝ) := by
      norm_num [oddCouplingCore, oddCouplingD, oddCouplingCross,
        oddCouplingFour]

set_option maxHeartbeats 500000 in
theorem crossASlopeSquare_lower
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
  have hsum : 0 ≤ (785 / 100000 : ℝ) + (u4 * dv - v4 * du) := by
    linarith
  have hprod := mul_nonneg
    (by linarith : 0 ≤ (u4 * dv - v4 * du) - 785 / 100000) hsum
  nlinarith

set_option maxHeartbeats 1000000 in
theorem minusOddASlopeCoupling_upper
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
      (q33 - h33) *
            ((F * du * du + D * (du * u4 + u4 * du) + C * u4 * u4) / 2) -
          2 * (q13 - h13) *
            ((F * du * dv + D * (du * v4 + u4 * dv) + C * u4 * v4) / 2) +
          (q11 - h11) *
              ((F * dv * dv + D * (dv * v4 + v4 * dv) + C * v4 * v4) / 2) ≤
        (82 / 1000000 : ℝ) := by
  have hOddMinus := (oddASlope_bounds
    A X R C D F a x r c d f
    su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox).1
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
    (q33 - h33) *
          ((F * du * du + D * (du * u4 + u4 * du) + C * u4 * u4) / 2) -
        2 * (q13 - h13) *
          ((F * du * dv + D * (du * v4 + u4 * dv) + C * u4 * v4) / 2) +
        (q11 - h11) *
            ((F * dv * dv + D * (dv * v4 + v4 * dv) + C * v4 * v4) / 2) =
      oddCouplingCore F C D du u4 dv v4
        (q11 - h11) (q13 - h13) (q33 - h33) / 2 by
    unfold oddCouplingCore oddCouplingD oddCouplingCross oddCouplingFour
    ring]
  have hom11L : (1578 / 10000 : ℝ) ≤ q11 - h11 := by linarith
  have hom11U : q11 - h11 ≤ (165 / 1000 : ℝ) := by linarith
  have hom13L : (209 / 1000 : ℝ) ≤ q13 - h13 := by linarith
  have hom13U : q13 - h13 ≤ (2112 / 10000 : ℝ) := by linarith
  have hom33L : (4485 / 10000 : ℝ) ≤ q33 - h33 := by linarith
  have hom33U : q33 - h33 ≤ (453 / 1000 : ℝ) := by linarith
  have hEDpos : 0 ≤ oddCouplingD du dv
      (q11 - h11) (q13 - h13) (q33 - h33) := by
    have hscaled : 0 ≤ (q33 - h33) *
        oddCouplingD du dv (q11 - h11) (q13 - h13) (q33 - h33) := by
      rw [show
        (q33 - h33) *
            oddCouplingD du dv (q11 - h11) (q13 - h13) (q33 - h33) =
          ((q33 - h33) * du - (q13 - h13) * dv) ^ 2 +
            ((q11 - h11) * (q33 - h33) - (q13 - h13) ^ 2) * dv ^ 2 by
        unfold oddCouplingD; ring]
      exact add_nonneg (sq_nonneg _)
        (mul_nonneg (by linarith) (sq_nonneg dv))
    exact nonneg_of_mul_nonneg_right hscaled (by linarith)
  have hEFpos : 0 ≤ oddCouplingFour u4 v4
      (q11 - h11) (q13 - h13) (q33 - h33) := by
    have hscaled : 0 ≤ (q33 - h33) *
        oddCouplingFour u4 v4 (q11 - h11) (q13 - h13) (q33 - h33) := by
      rw [show
        (q33 - h33) *
            oddCouplingFour u4 v4 (q11 - h11) (q13 - h13) (q33 - h33) =
          ((q33 - h33) * u4 - (q13 - h13) * v4) ^ 2 +
            ((q11 - h11) * (q33 - h33) - (q13 - h13) ^ 2) * v4 ^ 2 by
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
          (q11 - h11) (q13 - h13) (q33 - h33) ≤
        oddCouplingCore (63 / 200) (1342 / 100000) (42817 / 1000000)
          (1692 / 100000) (144 / 1000) (558 / 10000) (-4 / 1000)
          (165 / 1000) (209 / 1000) (453 / 1000) := by
    calc
      oddCouplingCore F C D du u4 dv v4
          (q11 - h11) (q13 - h13) (q33 - h33) ≤
          oddCouplingCore (63 / 200) C D du u4 dv v4
            (q11 - h11) (q13 - h13) (q33 - h33) := by
              rw [← sub_nonneg]
              convert mul_nonneg (by linarith : 0 ≤ (63 / 200 : ℝ) - F)
                hEDpos using 1 <;> unfold oddCouplingCore <;> ring
      _ ≤ oddCouplingCore (63 / 200) (1342 / 100000) D du u4 dv v4
            (q11 - h11) (q13 - h13) (q33 - h33) := by
              rw [← sub_nonneg]
              convert mul_nonneg (by linarith : 0 ≤ (1342 / 100000 : ℝ) - C)
                hEFpos using 1 <;> unfold oddCouplingCore <;> ring
      _ ≤ oddCouplingCore (63 / 200) (1342 / 100000) (42817 / 1000000)
            du u4 dv v4 (q11 - h11) (q13 - h13) (q33 - h33) := by
              rw [← sub_nonneg]
              convert mul_nonneg_of_nonpos_of_nonpos
                  (by linarith : (2 : ℝ) * (42817 / 1000000 - D) ≤ 0)
                  hEXneg using 1 <;> unfold oddCouplingCore <;> ring
      _ ≤ oddCouplingCore (63 / 200) (1342 / 100000) (42817 / 1000000)
            du u4 dv v4 (q11 - h11) (q13 - h13) (453 / 1000) := by
              rw [← sub_nonneg]
              convert mul_nonneg
                  (by linarith : 0 ≤ (453 / 1000 : ℝ) - (q33 - h33))
                  hQuPos using 1 <;>
                unfold oddCouplingCore oddCouplingD oddCouplingCross
                  oddCouplingFour <;> ring
      _ ≤ oddCouplingCore (63 / 200) (1342 / 100000) (42817 / 1000000)
            du u4 dv v4 (q11 - h11) (209 / 1000) (453 / 1000) := by
              rw [← sub_nonneg]
              convert mul_nonneg
                  (by linarith : 0 ≤ 2 * ((q13 - h13) - 209 / 1000))
                  hQuvPos using 1 <;>
                unfold oddCouplingCore oddCouplingD oddCouplingCross
                  oddCouplingFour <;> ring
      _ ≤ oddCouplingCore (63 / 200) (1342 / 100000) (42817 / 1000000)
            du u4 dv v4 (165 / 1000) (209 / 1000) (453 / 1000) := by
              rw [← sub_nonneg]
              convert mul_nonneg
                  (by linarith : 0 ≤ (165 / 1000 : ℝ) - (q11 - h11))
                  hQvPos using 1 <;>
                unfold oddCouplingCore oddCouplingD oddCouplingCross
                  oddCouplingFour <;> ring
      _ ≤ oddCouplingCore (63 / 200) (1342 / 100000) (42817 / 1000000)
            (1692 / 100000) u4 dv v4
            (165 / 1000) (209 / 1000) (453 / 1000) := by
              rw [← sub_nonneg, oddCouplingCore_du_step]
              have hslope : 0 ≤
                  (63 / 200 : ℝ) *
                      ((453 / 1000) * (du + 1692 / 100000) -
                        2 * (209 / 1000) * dv) +
                    2 * (42817 / 1000000) *
                      ((453 / 1000) * u4 - (209 / 1000) * v4) := by
                norm_num at ⊢
                linarith
              simpa [add_comm] using mul_nonneg (by linarith) hslope
      _ ≤ oddCouplingCore (63 / 200) (1342 / 100000) (42817 / 1000000)
            (1692 / 100000) (144 / 1000) dv v4
            (165 / 1000) (209 / 1000) (453 / 1000) := by
              rw [← sub_nonneg, oddCouplingCore_u4_step]
              have hslope : 0 ≤
                  2 * (42817 / 1000000 : ℝ) *
                      ((453 / 1000) * (1692 / 100000) -
                        (209 / 1000) * dv) +
                    (1342 / 100000) *
                      ((453 / 1000) * (u4 + 144 / 1000) -
                        2 * (209 / 1000) * v4) := by
                norm_num at ⊢
                linarith
              simpa [add_comm] using mul_nonneg (by linarith) hslope
      _ ≤ oddCouplingCore (63 / 200) (1342 / 100000) (42817 / 1000000)
            (1692 / 100000) (144 / 1000) (558 / 10000) v4
            (165 / 1000) (209 / 1000) (453 / 1000) := by
              rw [← sub_nonneg, oddCouplingCore_dv_step]
              have hslope : 0 ≤
                  (63 / 200 : ℝ) *
                      ((165 / 1000) * (dv + 558 / 10000) -
                        2 * (209 / 1000) * (1692 / 100000)) +
                    2 * (42817 / 1000000) *
                      ((165 / 1000) * v4 -
                        (209 / 1000) * (144 / 1000)) := by
                norm_num at ⊢
                linarith
              simpa [add_comm] using mul_nonneg (by linarith) hslope
      _ ≤ oddCouplingCore (63 / 200) (1342 / 100000) (42817 / 1000000)
            (1692 / 100000) (144 / 1000) (558 / 10000) (-4 / 1000)
            (165 / 1000) (209 / 1000) (453 / 1000) := by
              rw [← sub_nonpos, oddCouplingCore_v4_step]
              have hslope :
                  2 * (42817 / 1000000 : ℝ) *
                      ((165 / 1000) * (558 / 10000) -
                        (209 / 1000) * (1692 / 100000)) +
                    (1342 / 100000) *
                      ((165 / 1000) * (v4 + (-4 / 1000)) -
                        2 * (209 / 1000) * (144 / 1000)) ≤ 0 := by
                norm_num at ⊢
                linarith
              exact mul_nonpos_of_nonneg_of_nonpos (by linarith) hslope
  calc
    oddCouplingCore F C D du u4 dv v4
        (q11 - h11) (q13 - h13) (q33 - h33) / 2 ≤
        oddCouplingCore (63 / 200) (1342 / 100000) (42817 / 1000000)
          (1692 / 100000) (144 / 1000) (558 / 10000) (-4 / 1000)
          (165 / 1000) (209 / 1000) (453 / 1000) / 2 := by
            nlinarith only [hcore]
    _ ≤ (82 / 1000000 : ℝ) := by
      norm_num [oddCouplingCore, oddCouplingD, oddCouplingCross,
        oddCouplingFour]

set_option maxHeartbeats 5000000 in
theorem correlated_A_lower_endpoint
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    correlatedCoefficientThree
        (137423 / 100000) X R C D F a x r c d f
        su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 ≤
      correlatedCoefficientThree A X R C D F a x r c d f
        su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 := by
  have hsec : 0 ≤ quadraticSecant
      (fun z ↦ correlatedCoefficientThree z X R C D F a x r c d f
        su du u4 sv dv v4 q11 q13 q33 h11 h13 h33)
      A (137423 / 100000) := by
    rw [correlated_A_secant_eq]
    unfold correlatedThreeASlope alignedAdjugateASlope
      alignedMixedAdjugateBothASlope
    dsimp only
    rcases oddASlope_bounds
      A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox with
        ⟨hOddMinus, hOddMixed, hOddPlus⟩
    rcases evenASlopeDeterminant_bounds
      A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox with
        ⟨hDetOne, hDetTwo, hDetThree⟩
    have hMinusCoupling := plusEndASlopeCoupling_upper
      A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox
    have hMixedCoupling := minusOddASlopeCoupling_upper
      A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox
    have hCross := crossASlopeSquare_lower
      A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox
    have hTermOne : (91 / 100000 : ℝ) * (26 / 1000) ≤
        (((F + f) * (C - c) + (F - f) * (C + c) -
          2 * (D - d) * (D + d) + (F - f) * (C - c) -
            (D - d) ^ 2) / 4) *
          ((q11 - h11) * (q33 - h33) - (q13 - h13) ^ 2) := by
      have hprod := mul_nonneg (sub_nonneg.mpr hDetOne)
        (by linarith : 0 ≤
          (q11 - h11) * (q33 - h33) - (q13 - h13) ^ 2 + 26 / 1000)
      nlinarith
    have hTermTwo : (21 / 10000 : ℝ) * (41 / 1000) ≤
        (((F - f) * (C + c) + (F + f) * (C - c) -
          2 * (D - d) * (D + d) + (F + f) * (C + c) -
            (D + d) ^ 2) / 4) *
          ((q11 + h11) * (q33 - h33) +
            (q11 - h11) * (q33 + h33) -
              2 * (q13 + h13) * (q13 - h13)) := by
      have hprod := mul_nonneg (sub_nonneg.mpr hDetTwo)
        (by linarith : 0 ≤
          (q11 + h11) * (q33 - h33) +
            (q11 - h11) * (q33 + h33) -
              2 * (q13 + h13) * (q13 - h13) + 41 / 1000)
      nlinarith
    have hTermThree : (1 / 1000 : ℝ) * (4 / 1000) ≤
        (((F + f) * (C + c) - (D + d) ^ 2) / 4) *
          ((q11 + h11) * (q33 + h33) - (q13 + h13) ^ 2) := by
      have hprod := mul_nonneg (sub_nonneg.mpr hDetThree)
        (by linarith : 0 ≤
          (q11 + h11) * (q33 + h33) - (q13 + h13) ^ 2 + 4 / 1000)
      nlinarith
    nlinarith only [hTermOne, hTermTwo, hTermThree,
      hMinusCoupling, hMixedCoupling, hCross]
  have hid :
      correlatedCoefficientThree A X R C D F a x r c d f
          su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 -
        correlatedCoefficientThree (137423 / 100000) X R C D F a x r c d f
          su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 =
        (A - 137423 / 100000) * quadraticSecant
          (fun z ↦ correlatedCoefficientThree z X R C D F a x r c d f
            su du u4 sv dv v4 q11 q13 q33 h11 h13 h33)
          A (137423 / 100000) := by
    unfold quadraticSecant correlatedCoefficientThree alignedDeterminant
      alignedMixedDeterminant alignedAdjugatePair alignedMixedAdjugatePair
      alignedCrossEnergy alignedEntry00 alignedEntry02 alignedEntry04
      alignedEntry22 alignedEntry24 mixedDeterminantOne
    dsimp only
    ring
  nlinarith only [hid, mul_nonneg (sub_nonneg.mpr hbox.A_mem.1) hsec]

/-! ## The terminal correlated corner

The remaining coordinate telescope is staged backwards from this one exact
corner.  Each wrapper reintroduces one interval variable, so every secant has
an exact numeric head rather than an independently boxed endpoint pencil. -/

abbrev cornerA : ℝ := 137423 / 100000
abbrev cornerX : ℝ := 3977 / 100000
abbrev cornerR : ℝ := 242898 / 1000000
abbrev cornerC : ℝ := 1323 / 100000
abbrev cornerD : ℝ := 42898 / 1000000
abbrev cornerF : ℝ := 1571 / 5000
abbrev corner_a : ℝ := 826465 / 1000000
abbrev corner_x : ℝ := 39761 / 1000000
abbrev corner_r : ℝ := 57183 / 1000000
abbrev corner_c : ℝ := 7165 / 1000000
abbrev corner_d : ℝ := 23317 / 1000000
abbrev corner_f : ℝ := 4416 / 25000
abbrev cornerSu : ℝ := 56173 / 100000
abbrev cornerDu : ℝ := 1687 / 100000
abbrev cornerU4 : ℝ := 144 / 1000
abbrev lowerU4 : ℝ := 141 / 1000
abbrev cornerSv : ℝ := 53815 / 100000
abbrev cornerDv : ℝ := 558 / 10000
abbrev cornerV4 : ℝ := -2 / 1000
abbrev cornerQ11 : ℝ := 1778 / 10000
abbrev cornerQ13 : ℝ := 2002 / 10000
abbrev cornerQ33 : ℝ := 3315 / 10000
abbrev cornerH11 : ℝ := 14 / 1000
abbrev cornerH13 : ℝ := -9 / 1000
abbrev cornerH33 : ℝ := -120 / 1000

theorem correlated_corner_gt_fifteen_millionths :
    (15 / 1000000 : ℝ) <
      correlatedCoefficientThree
        cornerA cornerX cornerR cornerC cornerD cornerF
        corner_a corner_x corner_r corner_c corner_d corner_f
        cornerSu cornerDu cornerU4 cornerSv cornerDv cornerV4
        cornerQ11 cornerQ13 cornerQ33 cornerH11 cornerH13 cornerH33 := by
  norm_num [correlatedCoefficientThree, alignedDeterminant,
    alignedMixedDeterminant, alignedAdjugatePair, alignedMixedAdjugatePair,
    alignedCrossEnergy, alignedEntry00, alignedEntry02, alignedEntry04,
    alignedEntry22, alignedEntry24, mixedDeterminantOne]

set_option maxHeartbeats 1000000 in
theorem correlated_corner_unfix_u4
    (u4 : ℝ) (hu4L : lowerU4 ≤ u4) (hu4U : u4 ≤ cornerU4) :
    correlatedCoefficientThree
        cornerA cornerX cornerR cornerC cornerD cornerF
        corner_a corner_x corner_r corner_c corner_d corner_f
        cornerSu cornerDu cornerU4 cornerSv cornerDv cornerV4
        cornerQ11 cornerQ13 cornerQ33 cornerH11 cornerH13 cornerH33 ≤
      correlatedCoefficientThree
        cornerA cornerX cornerR cornerC cornerD cornerF
        corner_a corner_x corner_r corner_c corner_d corner_f
        cornerSu cornerDu u4 cornerSv cornerDv cornerV4
        cornerQ11 cornerQ13 cornerQ33 cornerH11 cornerH13 cornerH33 := by
  have hfactor :
      correlatedCoefficientThree
          cornerA cornerX cornerR cornerC cornerD cornerF
          corner_a corner_x corner_r corner_c corner_d corner_f
          cornerSu cornerDu u4 cornerSv cornerDv cornerV4
          cornerQ11 cornerQ13 cornerQ33 cornerH11 cornerH13 cornerH33 -
        correlatedCoefficientThree
          cornerA cornerX cornerR cornerC cornerD cornerF
          corner_a corner_x corner_r corner_c corner_d corner_f
          cornerSu cornerDu cornerU4 cornerSv cornerDv cornerV4
          cornerQ11 cornerQ13 cornerQ33 cornerH11 cornerH13 cornerH33 =
        (cornerU4 - u4) *
          ((22484813049853 / 8000000000000000 : ℝ) * u4 -
            157443992136563073 / 400000000000000000000) := by
    unfold correlatedCoefficientThree alignedDeterminant
      alignedMixedDeterminant alignedAdjugatePair alignedMixedAdjugatePair
      alignedCrossEnergy alignedEntry00 alignedEntry02 alignedEntry04
      alignedEntry22 alignedEntry24 mixedDeterminantOne
    dsimp only
    ring
  have hbracketLower : (0 : ℝ) <
      (22484813049853 / 8000000000000000) * lowerU4 -
        157443992136563073 / 400000000000000000000 := by
    norm_num
  have hbracketStep : 0 ≤
      (22484813049853 / 8000000000000000 : ℝ) * (u4 - lowerU4) :=
    mul_nonneg (by norm_num) (sub_nonneg.mpr hu4L)
  have hbracket : 0 ≤
      (22484813049853 / 8000000000000000 : ℝ) * u4 -
        157443992136563073 / 400000000000000000000 := by
    nlinarith only [hbracketLower, hbracketStep]
  rw [← sub_nonneg, hfactor]
  exact mul_nonneg (sub_nonneg.mpr hu4U) hbracket

set_option maxHeartbeats 1000000 in
theorem correlated_corner_unfix_v4
    (u4 v4 : ℝ)
    (hu4U : u4 ≤ cornerU4)
    (hv4L : (-4 / 1000 : ℝ) ≤ v4) (hv4U : v4 ≤ cornerV4) :
    correlatedCoefficientThree
        cornerA cornerX cornerR cornerC cornerD cornerF
        corner_a corner_x corner_r corner_c corner_d corner_f
        cornerSu cornerDu u4 cornerSv cornerDv cornerV4
        cornerQ11 cornerQ13 cornerQ33 cornerH11 cornerH13 cornerH33 ≤
      correlatedCoefficientThree
        cornerA cornerX cornerR cornerC cornerD cornerF
        corner_a corner_x corner_r corner_c corner_d corner_f
        cornerSu cornerDu u4 cornerSv cornerDv v4
        cornerQ11 cornerQ13 cornerQ33 cornerH11 cornerH13 cornerH33 := by
  let g : ℝ → ℝ := fun z ↦ correlatedCoefficientThree
    cornerA cornerX cornerR cornerC cornerD cornerF
    corner_a corner_x corner_r corner_c corner_d corner_f
    cornerSu cornerDu u4 cornerSv cornerDv z
    cornerQ11 cornerQ13 cornerQ33 cornerH11 cornerH13 cornerH33
  have hsec : quadraticSecant g v4 cornerV4 ≤ (-6 / 1000000 : ℝ) := by
    unfold g quadraticSecant correlatedCoefficientThree alignedDeterminant
      alignedMixedDeterminant alignedAdjugatePair alignedMixedAdjugatePair
      alignedCrossEnergy alignedEntry00 alignedEntry02 alignedEntry04
      alignedEntry22 alignedEntry24 mixedDeterminantOne
    dsimp only
    simp only [cornerA, cornerX, cornerR, cornerC, cornerD, cornerF,
      corner_a, corner_x, corner_r, corner_c, corner_d, corner_f,
      cornerSu, cornerDu, cornerSv, cornerDv, cornerV4,
      cornerQ11, cornerQ13, cornerQ33, cornerH11, cornerH13, cornerH33]
    ring_nf
    norm_num [cornerU4, cornerV4] at hu4U hv4L hv4U
    nlinarith
  have hid : g v4 - g cornerV4 =
      (v4 - cornerV4) * quadraticSecant g v4 cornerV4 := by
    unfold g quadraticSecant correlatedCoefficientThree alignedDeterminant
      alignedMixedDeterminant alignedAdjugatePair alignedMixedAdjugatePair
      alignedCrossEnergy alignedEntry00 alignedEntry02 alignedEntry04
      alignedEntry22 alignedEntry24 mixedDeterminantOne
    dsimp only
    ring
  have hsecNonpos : quadraticSecant g v4 cornerV4 ≤ 0 :=
    hsec.trans (by norm_num)
  rw [← sub_nonneg]
  simpa only [g] using
    (show 0 ≤ g v4 - g cornerV4 by
      rw [hid]
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hv4U) hsecNonpos)

set_option maxHeartbeats 1000000 in
theorem correlated_corner_unfix_r
    (r u4 v4 : ℝ)
    (hrL : (49817 / 1000000 : ℝ) ≤ r) (hrU : r ≤ corner_r)
    (hu4L : lowerU4 ≤ u4) (hu4U : u4 ≤ cornerU4)
    (hv4L : (-4 / 1000 : ℝ) ≤ v4) (hv4U : v4 ≤ cornerV4) :
    correlatedCoefficientThree
        cornerA cornerX cornerR cornerC cornerD cornerF
        corner_a corner_x corner_r corner_c corner_d corner_f
        cornerSu cornerDu u4 cornerSv cornerDv v4
        cornerQ11 cornerQ13 cornerQ33 cornerH11 cornerH13 cornerH33 ≤
      correlatedCoefficientThree
        cornerA cornerX cornerR cornerC cornerD cornerF
        corner_a corner_x r corner_c corner_d corner_f
        cornerSu cornerDu u4 cornerSv cornerDv v4
        cornerQ11 cornerQ13 cornerQ33 cornerH11 cornerH13 cornerH33 := by
  let g : ℝ → ℝ := fun z ↦ correlatedCoefficientThree
    cornerA cornerX cornerR cornerC cornerD cornerF
    corner_a corner_x z corner_c corner_d corner_f
    cornerSu cornerDu u4 cornerSv cornerDv v4
    cornerQ11 cornerQ13 cornerQ33 cornerH11 cornerH13 cornerH33
  have hsec : quadraticSecant g r corner_r ≤ (-20 / 1000000 : ℝ) := by
    unfold g quadraticSecant correlatedCoefficientThree alignedDeterminant
      alignedMixedDeterminant alignedAdjugatePair alignedMixedAdjugatePair
      alignedCrossEnergy alignedEntry00 alignedEntry02 alignedEntry04
      alignedEntry22 alignedEntry24 mixedDeterminantOne
    dsimp only
    simp only [cornerA, cornerX, cornerR, cornerC, cornerD, cornerF,
      corner_a, corner_x, corner_r, corner_c, corner_d, corner_f,
      cornerSu, cornerDu, cornerSv, cornerDv,
      cornerQ11, cornerQ13, cornerQ33, cornerH11, cornerH13, cornerH33]
    ring_nf
    norm_num [corner_r, lowerU4, cornerU4, cornerV4] at hrL hrU hu4L hu4U hv4L hv4U
    bound
  have hid : g r - g corner_r =
      (r - corner_r) * quadraticSecant g r corner_r := by
    unfold g quadraticSecant correlatedCoefficientThree alignedDeterminant
      alignedMixedDeterminant alignedAdjugatePair alignedMixedAdjugatePair
      alignedCrossEnergy alignedEntry00 alignedEntry02 alignedEntry04
      alignedEntry22 alignedEntry24 mixedDeterminantOne
    dsimp only
    ring
  have hsecNonpos : quadraticSecant g r corner_r ≤ 0 :=
    hsec.trans (by norm_num)
  rw [← sub_nonneg]
  simpa only [g] using
    (show 0 ≤ g r - g corner_r by
      rw [hid]
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hrU) hsecNonpos)

set_option maxHeartbeats 1000000 in
theorem correlated_corner_unfix_x
    (x r u4 v4 : ℝ)
    (hxL : (37851 / 1000000 : ℝ) ≤ x) (hxU : x ≤ corner_x)
    (hrL : (49817 / 1000000 : ℝ) ≤ r) (hrU : r ≤ corner_r)
    (hu4L : lowerU4 ≤ u4) (hu4U : u4 ≤ cornerU4)
    (hv4L : (-4 / 1000 : ℝ) ≤ v4) (hv4U : v4 ≤ cornerV4) :
    correlatedCoefficientThree
        cornerA cornerX cornerR cornerC cornerD cornerF
        corner_a corner_x r corner_c corner_d corner_f
        cornerSu cornerDu u4 cornerSv cornerDv v4
        cornerQ11 cornerQ13 cornerQ33 cornerH11 cornerH13 cornerH33 ≤
      correlatedCoefficientThree
        cornerA cornerX cornerR cornerC cornerD cornerF
        corner_a x r corner_c corner_d corner_f
        cornerSu cornerDu u4 cornerSv cornerDv v4
        cornerQ11 cornerQ13 cornerQ33 cornerH11 cornerH13 cornerH33 := by
  let g : ℝ → ℝ := fun z ↦ correlatedCoefficientThree
    cornerA cornerX cornerR cornerC cornerD cornerF
    corner_a z r corner_c corner_d corner_f
    cornerSu cornerDu u4 cornerSv cornerDv v4
    cornerQ11 cornerQ13 cornerQ33 cornerH11 cornerH13 cornerH33
  have hsec : quadraticSecant g x corner_x ≤ (-6 / 1000000 : ℝ) := by
    unfold g quadraticSecant correlatedCoefficientThree alignedDeterminant
      alignedMixedDeterminant alignedAdjugatePair alignedMixedAdjugatePair
      alignedCrossEnergy alignedEntry00 alignedEntry02 alignedEntry04
      alignedEntry22 alignedEntry24 mixedDeterminantOne
    dsimp only
    simp only [cornerA, cornerX, cornerR, cornerC, cornerD, cornerF,
      corner_a, corner_x, corner_c, corner_d, corner_f,
      cornerSu, cornerDu, cornerSv, cornerDv,
      cornerQ11, cornerQ13, cornerQ33, cornerH11, cornerH13, cornerH33]
    ring_nf
    norm_num [corner_x, corner_r, lowerU4, cornerU4, cornerV4] at hxL hxU hrL hrU hu4L hu4U hv4L hv4U
    have hrSlope : 0 ≤
        (17860508683 / 10000000000000 : ℝ) -
          (202431 / 400000000) * u4 + (468097 / 250000000) * v4 := by
      norm_num at ⊢
      linarith
    have hxSlope : 0 ≤
        (71 / 625 : ℝ) * u4 * v4 -
          (1383 / 8000) * u4 ^ 2 - (679 / 20000) * v4 ^ 2 +
            16458800923 / 2500000000000 := by
      have huvL : (144 / 1000 : ℝ) * (-4 / 1000) ≤ u4 * v4 := by
        have h1 : 0 ≤ u4 * (v4 - (-4 / 1000 : ℝ)) :=
          mul_nonneg (by linarith) (by linarith)
        have h2 : 0 ≤ (-4 / 1000 : ℝ) * (u4 - 144 / 1000) :=
          mul_nonneg_of_nonpos_of_nonpos (by norm_num) (by linarith)
        nlinarith only [h1, h2]
      have huSqU : u4 ^ 2 ≤ (144 / 1000 : ℝ) ^ 2 := by
        nlinarith [mul_nonneg
          (by linarith : 0 ≤ (144 / 1000 : ℝ) - u4)
          (by linarith : 0 ≤ (144 / 1000 : ℝ) + u4)]
      have hvSqU : v4 ^ 2 ≤ (-4 / 1000 : ℝ) ^ 2 := by
        nlinarith [mul_nonpos_of_nonneg_of_nonpos
          (by linarith : 0 ≤ v4 - (-4 / 1000 : ℝ))
          (by linarith : v4 + (-4 / 1000 : ℝ) ≤ 0)]
      nlinarith only [huvL, huSqU, hvSqU]
    have huSlope :
        (57183 / 1000000 : ℝ) * (-202431 / 400000000) -
              759773873619 / 400000000000000 +
            v4 * (342487757 / 20000000000) +
          v4 * (39761 / 1000000) * (71 / 625) +
      (u4 + 141 / 1000) * (-141459123 / 8000000000) +
      (u4 + 141 / 1000) * (39761 / 1000000) * (-1383 / 8000) ≤ 0 := by
      norm_num at ⊢
      linarith
    have hvSlope : 0 ≤
        (57183 / 1000000 : ℝ) * (468097 / 250000000) +
              (141 / 1000) * (342487757 / 20000000000) +
            (141 / 1000) * (39761 / 1000000) * (71 / 625) -
          361934047067 / 1000000000000000 +
        (v4 + (-2 / 1000)) * (-4548271 / 2000000000) +
      (v4 + (-2 / 1000)) * (39761 / 1000000) * (-679 / 20000) := by
      norm_num at ⊢
      linarith
    have hrStep := mul_nonneg
      (by linarith : 0 ≤ (57183 / 1000000 : ℝ) - r) hrSlope
    have hxStep := mul_nonneg
      (by linarith : 0 ≤ (39761 / 1000000 : ℝ) - x) hxSlope
    have huStep := mul_nonpos_of_nonneg_of_nonpos
      (by linarith : 0 ≤ u4 - 141 / 1000) huSlope
    have hvStep := mul_nonneg
      (by linarith : 0 ≤ (-2 / 1000 : ℝ) - v4) hvSlope
    nlinarith only [hrStep, hxStep, huStep, hvStep]
  have hid : g x - g corner_x =
      (x - corner_x) * quadraticSecant g x corner_x := by
    unfold g quadraticSecant correlatedCoefficientThree alignedDeterminant
      alignedMixedDeterminant alignedAdjugatePair alignedMixedAdjugatePair
      alignedCrossEnergy alignedEntry00 alignedEntry02 alignedEntry04
      alignedEntry22 alignedEntry24 mixedDeterminantOne
    dsimp only
    ring
  have hsecNonpos : quadraticSecant g x corner_x ≤ 0 :=
    hsec.trans (by norm_num)
  rw [← sub_nonneg]
  simpa only [g] using
    (show 0 ≤ g x - g corner_x by
      rw [hid]
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hxU) hsecNonpos)

set_option maxHeartbeats 1000000 in
theorem correlated_corner_unfix_a
    (a x r u4 v4 : ℝ)
    (haL : (824479 / 1000000 : ℝ) ≤ a) (haU : a ≤ corner_a)
    (hxL : (37851 / 1000000 : ℝ) ≤ x) (hxU : x ≤ corner_x)
    (hrL : (49817 / 1000000 : ℝ) ≤ r) (hrU : r ≤ corner_r)
    (hu4L : lowerU4 ≤ u4) (hu4U : u4 ≤ cornerU4)
    (hv4L : (-4 / 1000 : ℝ) ≤ v4) (hv4U : v4 ≤ cornerV4) :
    correlatedCoefficientThree
        cornerA cornerX cornerR cornerC cornerD cornerF
        corner_a x r corner_c corner_d corner_f
        cornerSu cornerDu u4 cornerSv cornerDv v4
        cornerQ11 cornerQ13 cornerQ33 cornerH11 cornerH13 cornerH33 ≤
      correlatedCoefficientThree
        cornerA cornerX cornerR cornerC cornerD cornerF
        a x r corner_c corner_d corner_f
        cornerSu cornerDu u4 cornerSv cornerDv v4
        cornerQ11 cornerQ13 cornerQ33 cornerH11 cornerH13 cornerH33 := by
  let g : ℝ → ℝ := fun z ↦ correlatedCoefficientThree
    cornerA cornerX cornerR cornerC cornerD cornerF
    z x r corner_c corner_d corner_f
    cornerSu cornerDu u4 cornerSv cornerDv v4
    cornerQ11 cornerQ13 cornerQ33 cornerH11 cornerH13 cornerH33
  have hsec : quadraticSecant g a corner_a ≤ (-7 / 1000000 : ℝ) := by
    unfold g quadraticSecant correlatedCoefficientThree alignedDeterminant
      alignedMixedDeterminant alignedAdjugatePair alignedMixedAdjugatePair
      alignedCrossEnergy alignedEntry00 alignedEntry02 alignedEntry04
      alignedEntry22 alignedEntry24 mixedDeterminantOne
    dsimp only
    simp only [cornerA, cornerX, cornerR, cornerC, cornerD, cornerF,
      corner_a, corner_c, corner_d, corner_f,
      cornerSu, cornerDu, cornerSv, cornerDv,
      cornerQ11, cornerQ13, cornerQ33, cornerH11, cornerH13, cornerH33]
    ring_nf
    norm_num [corner_a, corner_x, corner_r, lowerU4, cornerU4, cornerV4] at haL haU hxL hxU hrL hrU hu4L hu4U hv4L hv4U
    have hu : u4 * (56203269891 / 400000000000000 : ℝ) ≤
        (144 / 1000) * (56203269891 / 400000000000000) := by
      bound
    have huv : (144 / 1000 : ℝ) * (-4 / 1000) ≤ u4 * v4 := by
      have h1 : 0 ≤ u4 * (v4 - (-4 / 1000 : ℝ)) :=
        mul_nonneg (by linarith) (by linarith)
      have h2 : 0 ≤ (-4 / 1000 : ℝ) * (u4 - 144 / 1000) :=
        mul_nonneg_of_nonpos_of_nonpos (by norm_num) (by linarith)
      nlinarith only [h1, h2]
    have huvTerm : u4 * v4 * (-19829 / 1000000000 : ℝ) ≤
        (144 / 1000) * (-4 / 1000) * (-19829 / 1000000000) := by
      nlinarith only [huv]
    have huSq : u4 ^ 2 * (2108037 / 1600000000 : ℝ) ≤
        (144 / 1000) ^ 2 * (2108037 / 1600000000) := by
      bound
    have hv : v4 * (-29178367827 / 250000000000000 : ℝ) ≤
        (-4 / 1000) * (-29178367827 / 250000000000000) := by
      nlinarith
    have hvSq : (-2 / 1000 : ℝ) ^ 2 ≤ v4 ^ 2 := by
      nlinarith [mul_nonneg_of_nonpos_of_nonpos
        (by linarith : v4 - (-2 / 1000 : ℝ) ≤ 0)
        (by linarith : v4 + (-2 / 1000 : ℝ) ≤ 0)]
    have hvSqTerm : v4 ^ 2 * (-12799101 / 40000000000 : ℝ) ≤
        (-2 / 1000) ^ 2 * (-12799101 / 40000000000) := by
      nlinarith only [hvSq]
    nlinarith only [hu, huvTerm, huSq, hv, hvSqTerm]
  have hid : g a - g corner_a =
      (a - corner_a) * quadraticSecant g a corner_a := by
    unfold g quadraticSecant correlatedCoefficientThree alignedDeterminant
      alignedMixedDeterminant alignedAdjugatePair alignedMixedAdjugatePair
      alignedCrossEnergy alignedEntry00 alignedEntry02 alignedEntry04
      alignedEntry22 alignedEntry24 mixedDeterminantOne
    dsimp only
    ring
  have hsecNonpos : quadraticSecant g a corner_a ≤ 0 :=
    hsec.trans (by norm_num)
  rw [← sub_nonneg]
  simpa only [g] using
    (show 0 ≤ g a - g corner_a by
      rw [hid]
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr haU) hsecNonpos)

def tailOddFace
    (a x r u4 v4 q11 q13 q33 h11 h13 h33 : ℝ) : ℝ :=
  correlatedCoefficientThree
    cornerA cornerX cornerR cornerC cornerD cornerF
    a x r corner_c corner_d corner_f
    cornerSu cornerDu u4 cornerSv cornerDv v4
    q11 q13 q33 h11 h13 h33

theorem correlated_tail_five_lower
    (a x r u4 v4 : ℝ)
    (haL : (824479 / 1000000 : ℝ) ≤ a) (haU : a ≤ corner_a)
    (hxL : (37851 / 1000000 : ℝ) ≤ x) (hxU : x ≤ corner_x)
    (hrL : (49817 / 1000000 : ℝ) ≤ r) (hrU : r ≤ corner_r)
    (hu4L : lowerU4 ≤ u4) (hu4U : u4 ≤ cornerU4)
    (hv4L : (-4 / 1000 : ℝ) ≤ v4) (hv4U : v4 ≤ cornerV4) :
    tailOddFace corner_a corner_x corner_r cornerU4 cornerV4
        cornerQ11 cornerQ13 cornerQ33 cornerH11 cornerH13 cornerH33 ≤
      tailOddFace a x r u4 v4
        cornerQ11 cornerQ13 cornerQ33 cornerH11 cornerH13 cornerH33 := by
  unfold tailOddFace
  calc
    correlatedCoefficientThree
        cornerA cornerX cornerR cornerC cornerD cornerF
        corner_a corner_x corner_r corner_c corner_d corner_f
        cornerSu cornerDu cornerU4 cornerSv cornerDv cornerV4
        cornerQ11 cornerQ13 cornerQ33 cornerH11 cornerH13 cornerH33 ≤
      correlatedCoefficientThree
        cornerA cornerX cornerR cornerC cornerD cornerF
        corner_a corner_x corner_r corner_c corner_d corner_f
        cornerSu cornerDu u4 cornerSv cornerDv cornerV4
        cornerQ11 cornerQ13 cornerQ33 cornerH11 cornerH13 cornerH33 :=
      correlated_corner_unfix_u4 u4 hu4L hu4U
    _ ≤ correlatedCoefficientThree
        cornerA cornerX cornerR cornerC cornerD cornerF
        corner_a corner_x corner_r corner_c corner_d corner_f
        cornerSu cornerDu u4 cornerSv cornerDv v4
        cornerQ11 cornerQ13 cornerQ33 cornerH11 cornerH13 cornerH33 :=
      correlated_corner_unfix_v4 u4 v4 hu4U hv4L hv4U
    _ ≤ correlatedCoefficientThree
        cornerA cornerX cornerR cornerC cornerD cornerF
        corner_a corner_x r corner_c corner_d corner_f
        cornerSu cornerDu u4 cornerSv cornerDv v4
        cornerQ11 cornerQ13 cornerQ33 cornerH11 cornerH13 cornerH33 :=
      correlated_corner_unfix_r r u4 v4 hrL hrU hu4L hu4U hv4L hv4U
    _ ≤ correlatedCoefficientThree
        cornerA cornerX cornerR cornerC cornerD cornerF
        corner_a x r corner_c corner_d corner_f
        cornerSu cornerDu u4 cornerSv cornerDv v4
        cornerQ11 cornerQ13 cornerQ33 cornerH11 cornerH13 cornerH33 :=
      correlated_corner_unfix_x x r u4 v4
        hxL hxU hrL hrU hu4L hu4U hv4L hv4U
    _ ≤ correlatedCoefficientThree
        cornerA cornerX cornerR cornerC cornerD cornerF
        a x r corner_c corner_d corner_f
        cornerSu cornerDu u4 cornerSv cornerDv v4
        cornerQ11 cornerQ13 cornerQ33 cornerH11 cornerH13 cornerH33 :=
      correlated_corner_unfix_a a x r u4 v4
        haL haU hxL hxU hrL hrU hu4L hu4U hv4L hv4U

set_option maxHeartbeats 3000000 in
theorem correlated_odd_lower
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    tailOddFace a x r u4 v4
        cornerQ11 cornerQ13 cornerQ33 cornerH11 cornerH13 cornerH33 ≤
      tailOddFace a x r u4 v4 q11 q13 q33 h11 h13 h33 := by
  rcases hbox.a_mem with ⟨haL, haU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  rcases hbox.v4_mem with ⟨hv4L, hv4U⟩
  rcases hbox.q11_mem with ⟨hq11L, hq11U⟩
  rcases hbox.q13_mem with ⟨hq13L, hq13U⟩
  rcases hbox.q33_mem with ⟨hq33L, hq33U⟩
  rcases hbox.h11_mem with ⟨hh11L, hh11U⟩
  rcases hbox.h13_mem with ⟨hh13L, hh13U⟩
  rcases hbox.h33_mem with ⟨hh33L, hh33U⟩
  norm_num [corner_a, corner_x, corner_r, lowerU4, cornerU4, cornerV4,
    cornerQ11, cornerQ13, cornerQ33, cornerH11, cornerH13, cornerH33] at haL haU hxL hxU hrL hrU hu4L hu4U hv4L hv4U hq11L hq11U hq13L hq13U hq33L hq33U hh11L hh11U hh13L hh13U hh33L hh33U
  calc
    tailOddFace a x r u4 v4
        cornerQ11 cornerQ13 cornerQ33 cornerH11 cornerH13 cornerH33 ≤
      tailOddFace a x r u4 v4
        cornerQ11 cornerQ13 cornerQ33 cornerH11 cornerH13 h33 := by
      let g : ℝ → ℝ := fun z ↦ tailOddFace a x r u4 v4
        cornerQ11 cornerQ13 cornerQ33 cornerH11 cornerH13 z
      have hsecCap : (4 / 100000 : ℝ) ≤
          quadraticSecant g h33 cornerH33 := by
        unfold g tailOddFace quadraticSecant correlatedCoefficientThree
          alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
          alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
          alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
          mixedDeterminantOne
        dsimp only
        simp only [cornerA, cornerX, cornerR, cornerC, cornerD, cornerF,
          corner_c, corner_d, corner_f, cornerSu, cornerDu, cornerSv,
          cornerDv, cornerQ11, cornerQ13, cornerQ33, cornerH11,
          cornerH13, cornerH33]
        ring_nf
        have haSlope : 0 ≤
            (-1389 / 160000 : ℝ) * u4 ^ 2 -
              (190376263 / 200000000000) * u4 +
                3389195614637 / 10000000000000000 := by
          have huSqU : u4 ^ 2 ≤ (144 / 1000 : ℝ) ^ 2 := by
            nlinarith [mul_nonneg
              (by linarith : 0 ≤ (144 / 1000 : ℝ) - u4)
              (by linarith : 0 ≤ (144 / 1000 : ℝ) + u4)]
          nlinarith only [hu4U, huSqU]
        have hxSlope : 0 ≤
            (-5061 / 200000 : ℝ) * r * u4 -
                (28571319 / 5000000000) * r +
              (3 / 4) * u4 ^ 2 * (x + 37851 / 1000000) +
            (3977 / 200000) * u4 ^ 2 +
                (5929297951 / 200000000000) * u4 -
              (5152721 / 250000000) * (x + 37851 / 1000000) -
            136727876803 / 62500000000000 := by
          have hruU : r * u4 ≤
              (57183 / 1000000 : ℝ) * (144 / 1000) := by
            have h1 := mul_nonneg
              (by linarith : 0 ≤ (57183 / 1000000 : ℝ) - r)
              (by linarith : 0 ≤ u4)
            have h2 := mul_nonneg
              (by norm_num : 0 ≤ (57183 / 1000000 : ℝ))
              (by linarith : 0 ≤ (144 / 1000 : ℝ) - u4)
            nlinarith only [h1, h2]
          have huSqL : (141 / 1000 : ℝ) ^ 2 ≤ u4 ^ 2 := by
            nlinarith [mul_nonneg
              (by linarith : 0 ≤ u4 - (141 / 1000 : ℝ))
              (by linarith : 0 ≤ u4 + (141 / 1000 : ℝ))]
          have hxuSqL :
              (2 * (37851 / 1000000 : ℝ)) * (141 / 1000) ^ 2 ≤
                (x + 37851 / 1000000) * u4 ^ 2 := by
            have h1 := mul_nonneg
              (by linarith : 0 ≤ x - (37851 / 1000000 : ℝ))
              (sq_nonneg u4)
            have h2 := mul_nonneg
              (by norm_num : 0 ≤ 2 * (37851 / 1000000 : ℝ))
              (by linarith : 0 ≤ u4 ^ 2 - (141 / 1000 : ℝ) ^ 2)
            nlinarith only [h1, h2]
          nlinarith only [hruU, hrU, hu4L, huSqL, hxU, hxuSqL]
        have hrSlope : 0 ≤
            (-26764633 / 40000000000 : ℝ) * (r + 49817 / 1000000) -
                (5061 / 200000) * u4 * (37851 / 1000000) +
              (376703087 / 40000000000) * u4 -
            (28571319 / 5000000000) * (37851 / 1000000) -
              14964529257699 / 20000000000000000 := by
          nlinarith only [hrU, hu4L, hu4U]
        have huSlope :
            ((-1389 / 160000 : ℝ) * (824479 / 1000000) +
                  (3 / 4) * (37851 / 1000000) ^ 2 +
                (3977 / 200000) * (37851 / 1000000) +
              135061041 / 80000000000) * (u4 + 144 / 1000) -
                (190376263 / 200000000000) * (824479 / 1000000) -
              (5061 / 200000) * (49817 / 1000000) * (37851 / 1000000) +
            (376703087 / 40000000000) * (49817 / 1000000) +
                (5929297951 / 200000000000) * (37851 / 1000000) -
              6480504255519 / 20000000000000000 ≤ 0 := by
          norm_num at ⊢
          linarith
        have haStep := mul_nonneg
          (by linarith : 0 ≤ a - 824479 / 1000000) haSlope
        have hxStep := mul_nonneg
          (by linarith : 0 ≤ x - 37851 / 1000000) hxSlope
        have hrStep := mul_nonneg
          (by linarith : 0 ≤ r - 49817 / 1000000) hrSlope
        have huStep := mul_nonneg_of_nonpos_of_nonpos
          (by linarith : u4 - 144 / 1000 ≤ 0) huSlope
        nlinarith only [haStep, hxStep, hrStep, huStep]
      have hsec : 0 ≤ quadraticSecant g h33 cornerH33 :=
        le_trans (by norm_num) hsecCap
      have hid : g h33 - g cornerH33 =
          (h33 - cornerH33) * quadraticSecant g h33 cornerH33 := by
        unfold g tailOddFace quadraticSecant correlatedCoefficientThree
          alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
          alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
          alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
          mixedDeterminantOne
        dsimp only
        ring
      exact quadraticSecant_lower_endpoint g h33 cornerH33
        (by norm_num [cornerH33] at ⊢; exact hh33L) hsec hid
    _ ≤ tailOddFace a x r u4 v4
        cornerQ11 cornerQ13 cornerQ33 cornerH11 h13 h33 := by
      let g : ℝ → ℝ := fun z ↦ tailOddFace a x r u4 v4
        cornerQ11 cornerQ13 cornerQ33 cornerH11 z h33
      have hsecCap : quadraticSecant g h13 cornerH13 ≤
          (-9 / 100000 : ℝ) := by
        unfold g tailOddFace quadraticSecant correlatedCoefficientThree
          alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
          alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
          alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
          mixedDeterminantOne
        dsimp only
        simp only [cornerA, cornerX, cornerR, cornerC, cornerD, cornerF,
          corner_c, corner_d, corner_f, cornerSu, cornerDu, cornerSv,
          cornerDv, cornerQ11, cornerQ13, cornerQ33, cornerH11,
          cornerH13]
        ring_nf
        have huvL : (18 / 125 : ℝ) * (-(1 / 250)) ≤ u4 * v4 :=
          positive_negative_product_lower u4 v4
            (18 / 125) (-(1 / 250))
            (by linarith) hv4L (by norm_num) hu4U
        have haSlope : 0 ≤
            (-3880772827 / 2000000000000 : ℝ) * h13 +
                (1389 / 80000) * u4 * v4 +
              (31484871 / 10000000000) * u4 +
            (190376263 / 200000000000) * v4 -
              4225423739891 / 10000000000000000 := by
          nlinarith only [hh13U, huvL, hu4L, hv4L]
        have hruU : r * u4 ≤
            (57183 / 1000000 : ℝ) * (18 / 125) :=
          nonnegative_product_upper r u4
            (57183 / 1000000) (18 / 125)
            hrU hu4U (by norm_num) (by linarith)
        have hrvU : r * v4 ≤
            (49817 / 1000000 : ℝ) * (-(1 / 500)) :=
          positive_negative_product_upper r v4
            (49817 / 1000000) (-(1 / 500))
            hrL (by linarith) (by norm_num) hv4U
        have hrhU : r * h13 ≤
            (49817 / 1000000 : ℝ) * (-(9 / 1000)) :=
          positive_negative_product_upper r h13
            (49817 / 1000000) (-(9 / 1000))
            hrL (by linarith) (by norm_num) hh13U
        have hxhU : x * h13 ≤
            (37851 / 1000000 : ℝ) * (-(9 / 1000)) :=
          positive_negative_product_upper x h13
            (37851 / 1000000) (-(9 / 1000))
            hxL (by linarith) (by norm_num) hh13U
        have hxuU : x * u4 ≤
            (39761 / 1000000 : ℝ) * (18 / 125) :=
          nonnegative_product_upper x u4
            (39761 / 1000000) (18 / 125)
            hxU hu4U (by norm_num) (by linarith)
        have hxuvL :
            ((39761 / 1000000 : ℝ) * (18 / 125)) * (-(1 / 250)) ≤
              (x * u4) * v4 :=
          positive_negative_product_lower (x * u4) v4
            ((39761 / 1000000) * (18 / 125)) (-(1 / 250))
            (mul_nonneg (by linarith) (by linarith)) hv4L
            (by norm_num) hxuU
        have hxSlope :
            (159483 / 1000000 : ℝ) * h13 * r +
                  (5987 / 10000) * h13 * x +
                (6217223381 / 500000000000) * h13 +
              (837 / 10000) * r * u4 +
            (5061 / 200000) * r * v4 +
                  (32024427 / 5000000000) * r -
                (3 / 2) * u4 * v4 * x -
              (193093 / 2000000) * u4 * v4 -
            (943519619 / 40000000000) * u4 -
                  (5929297951 / 200000000000) * v4 +
                (5537803 / 250000000) * x -
              468643762867 / 250000000000000 ≤ 0 := by
          nlinarith only [hrhU, hxhU, hh13U, hruU, hrvU, hrU,
            hxuvL, huvL, hu4L, hv4L, hxU]
        have huSlope : 0 ≤
            (-202636707 / 40000000000 : ℝ) * r +
                (3659295483 / 500000000000) * v4 +
              51797913549471 / 40000000000000000 := by
          nlinarith only [hrU, hv4L]
        have hvSlope : 0 ≤
            (26061240479123 / 25000000000000000 : ℝ) -
              (422987881 / 50000000000) * r := by
          nlinarith only [hrU]
        have hhSlope : 0 ≤
            (9811 / 400000 : ℝ) * r ^ 2 +
                (3784678293 / 1000000000000) * r +
              222614074890179 / 2000000000000000000 := by
          positivity
        have hrSlope :
            (253102089343 / 20000000000000000 : ℝ) -
              (639301 / 1000000000) * r ≤ 0 := by
          nlinarith only [hrL]
        have haStep := mul_nonpos_of_nonpos_of_nonneg
          (by linarith : a - 165293 / 200000 ≤ 0) haSlope
        have hxStep := mul_nonpos_of_nonneg_of_nonpos
          (by linarith : 0 ≤ x - 37851 / 1000000) hxSlope
        have huStep := mul_nonpos_of_nonpos_of_nonneg
          (by linarith : u4 - 144 / 1000 ≤ 0) huSlope
        have hvStep := mul_nonpos_of_nonpos_of_nonneg
          (by linarith : v4 - (-2 / 1000) ≤ 0) hvSlope
        have hhStep := mul_nonpos_of_nonpos_of_nonneg
          (by linarith : h13 - (-9 / 1000) ≤ 0) hhSlope
        have hrStep := mul_nonpos_of_nonneg_of_nonpos
          (by linarith : 0 ≤ r - 49817 / 1000000) hrSlope
        nlinarith only [haStep, hxStep, huStep, hvStep, hhStep, hrStep]
      have hsec : quadraticSecant g h13 cornerH13 ≤ 0 :=
        le_trans hsecCap (by norm_num)
      have hid : g h13 - g cornerH13 =
          (h13 - cornerH13) * quadraticSecant g h13 cornerH13 := by
        unfold g tailOddFace quadraticSecant correlatedCoefficientThree
          alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
          alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
          alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
          mixedDeterminantOne
        dsimp only
        ring
      exact quadraticSecant_upper_endpoint g h13 cornerH13
        (by norm_num [cornerH13] at ⊢; exact hh13U) hsec hid
    _ ≤ tailOddFace a x r u4 v4
        cornerQ11 cornerQ13 cornerQ33 h11 h13 h33 := by
      let g : ℝ → ℝ := fun z ↦ tailOddFace a x r u4 v4
        cornerQ11 cornerQ13 cornerQ33 z h13 h33
      have hsecCap : (16 / 100000 : ℝ) ≤
          quadraticSecant g h11 cornerH11 := by
        unfold g tailOddFace quadraticSecant correlatedCoefficientThree
          alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
          alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
          alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
          mixedDeterminantOne
        dsimp only
        simp only [cornerA, cornerX, cornerR, cornerC, cornerD, cornerF,
          corner_c, corner_d, corner_f, cornerSu, cornerDu, cornerSv,
          cornerDv, cornerQ11, cornerQ13, cornerQ33, cornerH11]
        ring_nf
        have hvSqL : (-(1 / 500 : ℝ)) ^ 2 ≤ v4 ^ 2 := by
          nlinarith [mul_nonneg_of_nonpos_of_nonpos
            (by linarith : v4 - (-(1 / 500 : ℝ)) ≤ 0)
            (by linarith : v4 + (-(1 / 500 : ℝ)) ≤ 0)]
        have haSlope :
            (3880772827 / 2000000000000 : ℝ) * h33 -
                  (1389 / 160000) * v4 ^ 2 -
                (31484871 / 10000000000) * v4 +
              144625084239 / 4000000000000000 ≤ 0 := by
          nlinarith only [hh33U, hvSqL, hv4L]
        have hrhU : r * h33 ≤
            (49817 / 1000000 : ℝ) * (-(117 / 1000)) :=
          positive_negative_product_upper r h33
            (49817 / 1000000) (-(117 / 1000))
            hrL (by linarith) (by norm_num) hh33U
        have hxhU : x * h33 ≤
            (37851 / 1000000 : ℝ) * (-(117 / 1000)) :=
          positive_negative_product_upper x h33
            (37851 / 1000000) (-(117 / 1000))
            hxL (by linarith) (by norm_num) hh33U
        have hrvU : r * v4 ≤
            (49817 / 1000000 : ℝ) * (-(1 / 500)) :=
          positive_negative_product_upper r v4
            (49817 / 1000000) (-(1 / 500))
            hrL (by linarith) (by norm_num) hv4U
        have hvSqxL :
            (37851 / 1000000 : ℝ) * (-(1 / 500)) ^ 2 ≤
              x * v4 ^ 2 :=
          nonnegative_product_lower x (v4 ^ 2)
            (37851 / 1000000) ((-(1 / 500)) ^ 2)
            hxL hvSqL (by norm_num) (sq_nonneg v4)
        have hxSlope : 0 ≤
            (-159483 / 1000000 : ℝ) * h33 * r -
                  (5987 / 10000) * h33 * x -
                (6217223381 / 500000000000) * h33 -
              (837 / 10000) * r * v4 -
            (12982203 / 2000000000) * r +
                  (3 / 4) * v4 ^ 2 * x +
                (193093 / 4000000) * v4 ^ 2 +
              (943519619 / 40000000000) * v4 -
            (2280057 / 100000000) * x +
              325067889 / 40000000000000 := by
          nlinarith only [hrhU, hxhU, hh33U, hrvU, hrU,
            hvSqxL, hvSqL, hv4L, hxU]
        have hrSlope : 0 ≤
            (-9811 / 400000 : ℝ) * h33 * r -
                  (10013129521 / 2000000000000) * h33 +
                (212793 / 160000000) * r +
              (202636707 / 40000000000) * v4 -
            2488460815341 / 4000000000000000 := by
          nlinarith only [hrhU, hh33U, hrL, hv4L]
        have hvSlope :
            (-3659295483 / 1000000000000 : ℝ) * v4 -
              10352604269553 / 10000000000000000 ≤ 0 := by
          nlinarith only [hv4L]
        have hhSlope :
            (-180359537059459 / 500000000000000000 : ℝ) ≤ 0 := by
          norm_num
        have haStep := mul_nonneg_of_nonpos_of_nonpos
          (by linarith : a - 165293 / 200000 ≤ 0) haSlope
        have hxStep := mul_nonneg
          (by linarith : 0 ≤ x - 37851 / 1000000) hxSlope
        have hrStep := mul_nonneg
          (by linarith : 0 ≤ r - 49817 / 1000000) hrSlope
        have hvStep := mul_nonneg_of_nonpos_of_nonpos
          (by linarith : v4 - (-2 / 1000) ≤ 0) hvSlope
        have hhStep := mul_nonneg_of_nonpos_of_nonpos
          (by linarith : h33 - (-117 / 1000) ≤ 0) hhSlope
        nlinarith only [haStep, hxStep, hrStep, hvStep, hhStep]
      have hsec : 0 ≤ quadraticSecant g h11 cornerH11 :=
        le_trans (by norm_num) hsecCap
      have hid : g h11 - g cornerH11 =
          (h11 - cornerH11) * quadraticSecant g h11 cornerH11 := by
        unfold g tailOddFace quadraticSecant correlatedCoefficientThree
          alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
          alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
          alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
          mixedDeterminantOne
        dsimp only
        ring
      exact quadraticSecant_lower_endpoint g h11 cornerH11
        (by norm_num [cornerH11] at ⊢; exact hh11L) hsec hid
    _ ≤ tailOddFace a x r u4 v4
        cornerQ11 cornerQ13 q33 h11 h13 h33 := by
      let g : ℝ → ℝ := fun z ↦ tailOddFace a x r u4 v4
        cornerQ11 cornerQ13 z h11 h13 h33
      have hsecCap : (26 / 100000 : ℝ) ≤
          quadraticSecant g q33 cornerQ33 := by
        unfold g tailOddFace quadraticSecant correlatedCoefficientThree
          alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
          alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
          alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
          mixedDeterminantOne
        dsimp only
        simp only [cornerA, cornerX, cornerR, cornerC, cornerD, cornerF,
          corner_c, corner_d, corner_f, cornerSu, cornerDu, cornerSv,
          cornerDv, cornerQ11, cornerQ13, cornerQ33]
        ring_nf
        have huSqL : (141 / 1000 : ℝ) ^ 2 ≤ u4 ^ 2 := by
          nlinarith [mul_nonneg
            (by linarith : 0 ≤ u4 - (141 / 1000 : ℝ))
            (by linarith : 0 ≤ u4 + (141 / 1000 : ℝ))]
        have huSqU : u4 ^ 2 ≤ (18 / 125 : ℝ) ^ 2 := by
          nlinarith [mul_nonneg
            (by linarith : 0 ≤ (18 / 125 : ℝ) - u4)
            (by linarith : 0 ≤ (18 / 125 : ℝ) + u4)]
        have haSlope :
            (-1213 / 800000 : ℝ) * u4 ^ 2 +
                  (4182369353 / 2000000000000) * h11 -
                (33033147 / 200000000000) * u4 -
              980650214397 / 10000000000000000 ≤ 0 := by
          nlinarith only [huSqL, hh11U, hu4L]
        have huSqxU : x * u4 ^ 2 ≤
            (39761 / 1000000 : ℝ) * (18 / 125) ^ 2 :=
          nonnegative_product_upper x (u4 ^ 2)
            (39761 / 1000000) ((18 / 125) ^ 2)
            hxU huSqU (by norm_num) (sq_nonneg u4)
        have hhrU : h11 * r ≤
            (1 / 50 : ℝ) * (57183 / 1000000) :=
          nonnegative_product_upper h11 r
            (1 / 50) (57183 / 1000000)
            hh11U hrU (by norm_num) (by linarith)
        have hhxU : h11 * x ≤
            (1 / 50 : ℝ) * (39761 / 1000000) :=
          nonnegative_product_upper h11 x
            (1 / 50) (39761 / 1000000)
            hh11U hxU (by norm_num) (by linarith)
        have hruL : (49817 / 1000000 : ℝ) * (141 / 1000) ≤ r * u4 :=
          nonnegative_product_lower r u4
            (49817 / 1000000) (141 / 1000)
            hrL hu4L (by norm_num) (by linarith)
        have hxSlope : 0 ≤
            (-1 / 4 : ℝ) * u4 ^ 2 * x -
                  (19581 / 1000000) * h11 * r -
                (3439 / 50000) * h11 * x +
              (1687 / 200000) * r * u4 +
            (41689 / 4000000) * u4 ^ 2 -
                  (764151793 / 20000000000) * h11 +
                (11773027 / 1000000000) * r +
              (690154587 / 200000000000) * u4 +
            (10908919 / 250000000) * x +
              606360717347 / 1250000000000000 := by
          nlinarith only [huSqxU, hhrU, hhxU, hruL, huSqL,
            hh11U, hrL, hu4L, hxL]
        have hrSlope : 0 ≤
            (-1213 / 400000 : ℝ) * h11 * r -
                  (16959011487 / 2000000000000) * h11 +
                (69678651 / 40000000000) * r +
              (84362973 / 50000000000) * u4 +
            10374114038253 / 40000000000000000 := by
          nlinarith only [hhrU, hh11U, hrL, hu4L]
        have huSlope :
            (-15769781959 / 1000000000000 : ℝ) * u4 +
              34764889239639 / 50000000000000000 ≤ 0 := by
          nlinarith only [hu4L]
        have hhSlope : 0 ≤
            (509416389292459 / 500000000000000000 : ℝ) := by
          norm_num
        have haStep := mul_nonneg_of_nonpos_of_nonpos
          (by linarith : a - 165293 / 200000 ≤ 0) haSlope
        have hxStep := mul_nonneg
          (by linarith : 0 ≤ x - 37851 / 1000000) hxSlope
        have hrStep := mul_nonneg
          (by linarith : 0 ≤ r - 49817 / 1000000) hrSlope
        have huStep := mul_nonneg_of_nonpos_of_nonpos
          (by linarith : u4 - 144 / 1000 ≤ 0) huSlope
        have hhStep := mul_nonneg
          (by linarith : 0 ≤ h11 - 14 / 1000) hhSlope
        nlinarith only [haStep, hxStep, hrStep, huStep, hhStep]
      have hsec : 0 ≤ quadraticSecant g q33 cornerQ33 :=
        le_trans (by norm_num) hsecCap
      have hid : g q33 - g cornerQ33 =
          (q33 - cornerQ33) * quadraticSecant g q33 cornerQ33 := by
        unfold g tailOddFace quadraticSecant correlatedCoefficientThree
          alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
          alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
          alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
          mixedDeterminantOne
        dsimp only
        ring
      exact quadraticSecant_lower_endpoint g q33 cornerQ33
        (by norm_num [cornerQ33] at ⊢; exact hq33L) hsec hid
    _ ≤ tailOddFace a x r u4 v4
        cornerQ11 q13 q33 h11 h13 h33 := by
      let g : ℝ → ℝ := fun z ↦ tailOddFace a x r u4 v4
        cornerQ11 z q33 h11 h13 h33
      have hsecCap : quadraticSecant g q13 cornerQ13 ≤
          (-58 / 100000 : ℝ) := by
        unfold g tailOddFace quadraticSecant correlatedCoefficientThree
          alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
          alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
          alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
          mixedDeterminantOne
        dsimp only
        simp only [cornerA, cornerX, cornerR, cornerC, cornerD, cornerF,
          corner_c, corner_d, corner_f, cornerSu, cornerDu, cornerSv,
          cornerDv, cornerQ11, cornerQ13]
        ring_nf
        have huvL : (18 / 125 : ℝ) * (-(1 / 250)) ≤ u4 * v4 :=
          positive_negative_product_lower u4 v4
            (18 / 125) (-(1 / 250))
            (by linarith) hv4L (by norm_num) hu4U
        have huvU : u4 * v4 ≤
            (141 / 1000 : ℝ) * (-(1 / 500)) :=
          positive_negative_product_upper u4 v4
            (141 / 1000) (-(1 / 500))
            hu4L (by linarith) (by norm_num) hv4U
        have haSlope : 0 ≤
            (1213 / 400000 : ℝ) * u4 * v4 -
                  (4182369353 / 1000000000000) * h13 +
                (993000383 / 2000000000000) * q13 +
              (5463099 / 10000000000) * u4 +
            (33033147 / 200000000000) * v4 +
              1641451162183 / 10000000000000000 := by
          nlinarith only [huvL, hh13U, hq13L, hu4L, hv4L]
        have hxuL : (37851 / 1000000 : ℝ) * (141 / 1000) ≤ x * u4 :=
          nonnegative_product_lower x u4
            (37851 / 1000000) (141 / 1000)
            hxL hu4L (by norm_num) (by linarith)
        have hxuvU : (x * u4) * v4 ≤
            ((37851 / 1000000 : ℝ) * (141 / 1000)) * (-(1 / 500)) :=
          positive_negative_product_upper (x * u4) v4
            ((37851 / 1000000) * (141 / 1000)) (-(1 / 500))
            hxuL (by linarith) (by norm_num) hv4U
        have hrhU : r * h13 ≤
            (49817 / 1000000 : ℝ) * (-(9 / 1000)) :=
          positive_negative_product_upper r h13
            (49817 / 1000000) (-(9 / 1000))
            hrL (by linarith) (by norm_num) hh13U
        have hxhU : x * h13 ≤
            (37851 / 1000000 : ℝ) * (-(9 / 1000)) :=
          positive_negative_product_upper x h13
            (37851 / 1000000) (-(9 / 1000))
            hxL (by linarith) (by norm_num) hh13U
        have hqrL : (1 / 5 : ℝ) * (49817 / 1000000) ≤ q13 * r :=
          nonnegative_product_lower q13 r
            (1 / 5) (49817 / 1000000)
            hq13L hrL (by norm_num) (by linarith)
        have hqxL : (1 / 5 : ℝ) * (37851 / 1000000) ≤ q13 * x :=
          nonnegative_product_lower q13 x
            (1 / 5) (37851 / 1000000)
            hq13L hxL (by norm_num) (by linarith)
        have hruL : (49817 / 1000000 : ℝ) * (141 / 1000) ≤ r * u4 :=
          nonnegative_product_lower r u4
            (49817 / 1000000) (141 / 1000)
            hrL hu4L (by norm_num) (by linarith)
        have hrvL : (57183 / 1000000 : ℝ) * (-(1 / 250)) ≤ r * v4 :=
          positive_negative_product_lower r v4
            (57183 / 1000000) (-(1 / 250))
            (by linarith) hv4L (by norm_num) hrU
        have hxSlope :
            (1 / 2 : ℝ) * u4 * v4 * x +
                  (19581 / 500000) * h13 * r +
                (3439 / 25000) * h13 * x -
              (13243 / 200000) * q13 * r -
            (12271 / 50000) * q13 * x -
                  (279 / 10000) * r * u4 -
                (1687 / 200000) * r * v4 -
              (41689 / 2000000) * u4 * v4 +
            (764151793 / 10000000000) * h13 +
                  (468777259 / 500000000000) * q13 -
                (13256243 / 1000000000) * r +
              (12064773 / 8000000000) * u4 -
            (690154587 / 200000000000) * v4 -
                  (12283271 / 250000000) * x -
                1620377555379 / 625000000000000 ≤ 0 := by
          nlinarith only [hxuvU, hrhU, hxhU, hqrL, hqxL,
            hruL, hrvL, huvL, hh13U, hq13U, hrL, hu4U, hv4L, hxL]
        have hrSlope :
            (1213 / 200000 : ℝ) * h13 * r -
                  (4079 / 400000) * q13 * r +
                (16959011487 / 1000000000000) * h13 -
              (304960033 / 400000000000) * q13 -
            (3141733 / 2000000000) * r -
                  (63135991 / 40000000000) * u4 -
                (84362973 / 50000000000) * v4 -
              3014394563203 / 4000000000000000 ≤ 0 := by
          nlinarith only [hrhU, hqrL, hh13U, hq13L,
            hrL, hu4L, hv4L]
        have huSlope : 0 ≤
            (15769781959 / 500000000000 : ℝ) * v4 +
              23777350433697 / 10000000000000000 := by
          nlinarith only [hv4L]
        have hvSlope : 0 ≤
            (78777540865161 / 50000000000000000 : ℝ) := by
          norm_num
        have hhSlope :
            (-509416389292459 / 250000000000000000 : ℝ) ≤ 0 := by
          norm_num
        have hqSlope :
            (-1495499947517471 / 500000000000000000 : ℝ) ≤ 0 := by
          norm_num
        have haStep := mul_nonpos_of_nonpos_of_nonneg
          (by linarith : a - 165293 / 200000 ≤ 0) haSlope
        have hxStep := mul_nonpos_of_nonneg_of_nonpos
          (by linarith : 0 ≤ x - 37851 / 1000000) hxSlope
        have hrStep := mul_nonpos_of_nonneg_of_nonpos
          (by linarith : 0 ≤ r - 49817 / 1000000) hrSlope
        have huStep := mul_nonpos_of_nonpos_of_nonneg
          (by linarith : u4 - 144 / 1000 ≤ 0) huSlope
        have hvStep := mul_nonpos_of_nonpos_of_nonneg
          (by linarith : v4 - (-2 / 1000) ≤ 0) hvSlope
        have hhStep := mul_nonpos_of_nonneg_of_nonpos
          (by linarith : 0 ≤ h13 - (-11 / 1000)) hhSlope
        have hqStep := mul_nonpos_of_nonneg_of_nonpos
          (by linarith : 0 ≤ q13 - 1 / 5) hqSlope
        nlinarith only [haStep, hxStep, hrStep, huStep, hvStep, hhStep, hqStep]
      have hsec : quadraticSecant g q13 cornerQ13 ≤ 0 :=
        le_trans hsecCap (by norm_num)
      have hid : g q13 - g cornerQ13 =
          (q13 - cornerQ13) * quadraticSecant g q13 cornerQ13 := by
        unfold g tailOddFace quadraticSecant correlatedCoefficientThree
          alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
          alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
          alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
          mixedDeterminantOne
        dsimp only
        ring
      exact quadraticSecant_upper_endpoint g q13 cornerQ13
        (by norm_num [cornerQ13] at ⊢; exact hq13U) hsec hid
    _ ≤ tailOddFace a x r u4 v4 q11 q13 q33 h11 h13 h33 := by
      let g : ℝ → ℝ := fun z ↦ tailOddFace a x r u4 v4
        z q13 q33 h11 h13 h33
      have hsecCap : (4 / 10000 : ℝ) ≤
          quadraticSecant g q11 cornerQ11 := by
        unfold g tailOddFace quadraticSecant correlatedCoefficientThree
          alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
          alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
          alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
          mixedDeterminantOne
        dsimp only
        simp only [cornerA, cornerX, cornerR, cornerC, cornerD, cornerF,
          corner_c, corner_d, corner_f, cornerSu, cornerDu, cornerSv,
          cornerDv, cornerQ11]
        ring_nf
        have hvSqL : (1 / 500 : ℝ) ^ 2 ≤ v4 ^ 2 := by
          nlinarith [mul_nonneg_of_nonpos_of_nonpos
            (by linarith : v4 + (1 / 500 : ℝ) ≤ 0)
            (by linarith : v4 - (1 / 500 : ℝ) ≤ 0)]
        have hvSqU : v4 ^ 2 ≤ (1 / 250 : ℝ) ^ 2 := by
          nlinarith [mul_nonneg_of_nonpos_of_nonpos
            (by linarith : (-(1 / 250 : ℝ)) - v4 ≤ 0)
            (by linarith : (-(1 / 250 : ℝ)) + v4 ≤ 0)]
        have haSlope :
            (4182369353 / 2000000000000 : ℝ) * h33 -
                  (993000383 / 2000000000000) * q33 -
                (1213 / 800000) * v4 ^ 2 -
              (5463099 / 10000000000) * v4 -
            267695199 / 2500000000000 ≤ 0 := by
          nlinarith only [hvSqL, hh33U, hq33L, hv4L]
        have hhrU : r * h33 ≤
            (49817 / 1000000 : ℝ) * (-(117 / 1000)) :=
          positive_negative_product_upper r h33
            (49817 / 1000000) (-(117 / 1000))
            hrL (by linarith) (by norm_num) hh33U
        have hxhU : x * h33 ≤
            (37851 / 1000000 : ℝ) * (-(117 / 1000)) :=
          positive_negative_product_upper x h33
            (37851 / 1000000) (-(117 / 1000))
            hxL (by linarith) (by norm_num) hh33U
        have hqrL : (663 / 2000 : ℝ) * (49817 / 1000000) ≤ q33 * r :=
          nonnegative_product_lower q33 r
            (663 / 2000) (49817 / 1000000)
            hq33L hrL (by norm_num) (by linarith)
        have hqxL : (663 / 2000 : ℝ) * (37851 / 1000000) ≤ q33 * x :=
          nonnegative_product_lower q33 x
            (663 / 2000) (37851 / 1000000)
            hq33L hxL (by norm_num) (by linarith)
        have hrvL : (57183 / 1000000 : ℝ) * (-(1 / 250)) ≤ r * v4 :=
          positive_negative_product_lower r v4
            (57183 / 1000000) (-(1 / 250))
            (by linarith) hv4L (by norm_num) hrU
        have hxvSqU : x * v4 ^ 2 ≤
            (39761 / 1000000 : ℝ) * (1 / 250) ^ 2 :=
          nonnegative_product_upper x (v4 ^ 2)
            (39761 / 1000000) ((1 / 250) ^ 2)
            hxU hvSqU (by norm_num) (sq_nonneg v4)
        have hxSlope : 0 ≤
            (-19581 / 1000000 : ℝ) * h33 * r -
                  (3439 / 50000) * h33 * x -
                (764151793 / 20000000000) * h33 +
              (13243 / 200000) * q33 * r +
            (12271 / 50000) * q33 * x -
                  (468777259 / 500000000000) * q33 +
                (279 / 10000) * r * v4 -
              (1 / 4) * v4 ^ 2 * x +
            (41689 / 4000000) * v4 ^ 2 -
                  (12064773 / 8000000000) * v4 +
                10326894003 / 5000000000000 := by
          nlinarith only [hhrU, hxhU, hqrL, hqxL, hrvL,
            hxvSqU, hvSqL, hh33U, hq33U, hv4U]
        have hrSlope : 0 ≤
            (-1213 / 400000 : ℝ) * h33 * r -
                  (16959011487 / 2000000000000) * h33 +
                (4079 / 400000) * q33 * r +
              (304960033 / 400000000000) * q33 -
            (77841 / 100000000) * r +
                  (63135991 / 40000000000) * v4 +
                25334683443 / 40000000000000 := by
          nlinarith only [hhrU, hh33U, hqrL, hq33L, hrU, hv4L]
        have hvSlope :
            (-15769781959 / 1000000000000 : ℝ) * v4 -
              23461954794517 / 10000000000000000 ≤ 0 := by
          nlinarith only [hv4L]
        have hhSlope : 0 ≤
            (509416389292459 / 500000000000000000 : ℝ) := by
          norm_num
        have hqSlope : 0 ≤
            (1495499947517471 / 500000000000000000 : ℝ) := by
          norm_num
        have haStep := mul_nonneg_of_nonpos_of_nonpos
          (by linarith : a - 165293 / 200000 ≤ 0) haSlope
        have hxStep := mul_nonneg
          (by linarith : 0 ≤ x - 37851 / 1000000) hxSlope
        have hrStep := mul_nonneg
          (by linarith : 0 ≤ r - 49817 / 1000000) hrSlope
        have hvStep := mul_nonneg_of_nonpos_of_nonpos
          (by linarith : v4 - (-(1 / 500)) ≤ 0) hvSlope
        have hhStep := mul_nonneg
          (by linarith : 0 ≤ h33 - (-(3 / 25))) hhSlope
        have hqStep := mul_nonneg
          (by linarith : 0 ≤ q33 - 663 / 2000) hqSlope
        nlinarith only [haStep, hxStep, hrStep, hvStep, hhStep, hqStep]
      have hsec : 0 ≤ quadraticSecant g q11 cornerQ11 :=
        le_trans (by norm_num) hsecCap
      have hid : g q11 - g cornerQ11 =
          (q11 - cornerQ11) * quadraticSecant g q11 cornerQ11 := by
        unfold g tailOddFace quadraticSecant correlatedCoefficientThree
          alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
          alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00
          alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
          mixedDeterminantOne
        dsimp only
        ring
      exact quadraticSecant_lower_endpoint g q11 cornerQ11
        (by norm_num [cornerQ11] at ⊢; exact hq11L) hsec hid

/-! ## The alternating block

The alternating-coordinate secants are kept as cofactor-row pairings.  For
the first reverse move only `dv` varies; `su`, `du`, and `sv` remain at the
terminal correlated corner.
-/

def alternatingAdjugateRowD
    (A X R D F ws wd w4 : ℝ) : ℝ :=
  (-(F * X + R * D) * ws + (F * A - R ^ 2) * wd +
      (X * R + A * D) * w4) / 4

def alternatingMixedAdjugateRowD
    (A X R D F a x r d f ws wd w4 : ℝ) : ℝ :=
  (-(F * x + f * X + R * d + r * D) * ws +
      (F * a + f * A - 2 * R * r) * wd +
      (X * r + x * R + A * d + a * D) * w4) / 4

def alternatingCrossGradientS
    (A X R zs zd z4 : ℝ) : ℝ :=
  (A * zs + X * zd + 2 * R * z4) / 2

def alternatingCrossGradientFour
    (R D F zs zd z4 : ℝ) : ℝ :=
  R * zs - D * zd + 2 * F * z4

def alternatingFace
    (a x r su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ) : ℝ :=
  correlatedCoefficientThree
    cornerA cornerX cornerR cornerC cornerD cornerF
    a x r corner_c corner_d corner_f
    su du u4 sv dv v4 q11 q13 q33 h11 h13 h33

def alternatingDvCoupling
    (a x r u4 v4 q11 q13 h11 h13 dv dv0 : ℝ) : ℝ :=
  let Ap := cornerA - a
  let Xp := cornerX - x
  let Rp := cornerR - r
  let Dp := cornerD - corner_d
  let Fp := cornerF - corner_f
  let Am := cornerA + a
  let Xm := cornerX + x
  let Rm := cornerR + r
  let Dm := cornerD + corner_d
  let Fm := cornerF + corner_f
  let o11p := q11 + h11
  let o13p := q13 + h13
  let o11m := q11 - h11
  let o13m := q13 - h13
  let dvbar := (dv + dv0) / 2
  let wpS := o13p * cornerSu - o11p * cornerSv
  let wpD := o13p * cornerDu - o11p * dvbar
  let wp4 := o13p * u4 - o11p * v4
  let wmS := o13m * cornerSu - o11m * cornerSv
  let wmD := o13m * cornerDu - o11m * dvbar
  let wm4 := o13m * u4 - o11m * v4
  2 * (alternatingAdjugateRowD Am Xm Rm Dm Fm wpS wpD wp4 +
    alternatingMixedAdjugateRowD Ap Xp Rp Dp Fp
      Am Xm Rm Dm Fm wmS wmD wm4)

def alternatingDvCross
    (a x r u4 v4 dv dv0 : ℝ) : ℝ :=
  let Am := cornerA + a
  let Xm := cornerX + x
  let Rm := cornerR + r
  let Dm := cornerD + corner_d
  let Fm := cornerF + corner_f
  let dvbar := (dv + dv0) / 2
  let zs := u4 * dvbar - v4 * cornerDu
  let zd := v4 * cornerSu - u4 * cornerSv
  let z4 := (cornerDu * cornerSv - cornerSu * dvbar) / 2
  u4 * alternatingCrossGradientS Am Xm Rm zs zd z4 -
    (cornerSu / 2) * alternatingCrossGradientFour Rm Dm Fm zs zd z4

def alternatingDvSlope
    (a x r u4 v4 q11 q13 h11 h13 dv dv0 : ℝ) : ℝ :=
  alternatingDvCoupling a x r u4 v4 q11 q13 h11 h13 dv dv0 +
    alternatingDvCross a x r u4 v4 dv dv0

set_option maxHeartbeats 3000000 in
theorem alternating_dv_secant_eq
    (a x r u4 v4 q11 q13 q33 h11 h13 h33 dv dv0 : ℝ) :
    quadraticSecant
        (fun z ↦ alternatingFace a x r cornerSu cornerDu u4 cornerSv z v4
          q11 q13 q33 h11 h13 h33)
        dv dv0 =
      alternatingDvSlope a x r u4 v4 q11 q13 h11 h13 dv dv0 := by
  unfold quadraticSecant alternatingFace alternatingDvSlope
    alternatingDvCoupling alternatingDvCross alternatingAdjugateRowD
    alternatingMixedAdjugateRowD alternatingCrossGradientS
    alternatingCrossGradientFour correlatedCoefficientThree
    alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
    alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00 alignedEntry02
    alignedEntry04 alignedEntry22 alignedEntry24 mixedDeterminantOne
  dsimp only
  ring

def alternatingDvCouplingSlopeA
    (u4 v4 q11 q13 h11 h13 dv : ℝ) : ℝ :=
  19581 / 2000000 * u4 * q13 + 112849 / 2000000 * u4 * h13 -
    19581 / 2000000 * v4 * q11 - 112849 / 2000000 * v4 * h11 -
    3439 / 100000 * q11 * dv - 21103 / 100000 * h11 * dv -
    959481 / 500000000 * q11 + 5801593 / 5000000000 * q13 -
    5887737 / 500000000 * h11 + 35600761 / 5000000000 * h13

def alternatingDvCouplingSlopeX
    (r u4 v4 q11 q13 h11 h13 : ℝ) : ℝ :=
  -(1 / 2) * r * u4 * q13 + 3 / 2 * r * u4 * h13 +
    1 / 2 * r * v4 * q11 - 3 / 2 * r * v4 * h11 +
    121449 / 1000000 * u4 * q13 + 121449 / 1000000 * u4 * h13 -
    121449 / 1000000 * v4 * q11 - 121449 / 1000000 * v4 * h11 +
    37013957 / 1000000000 * q11 - 193178947 / 5000000000 * q13 +
    227131589 / 1000000000 * h11 - 1185418819 / 5000000000 * h13

def alternatingDvCouplingSlopeR
    (r u4 v4 q11 q13 h11 h13 dv : ℝ) : ℝ :=
  -(1 / 4) * r * q11 * dv + 3 / 4 * r * h11 * dv -
    279 / 20000 * r * q11 + 1687 / 200000 * r * q13 +
    837 / 20000 * r * h11 - 5061 / 200000 * r * h13 +
    9 / 2000000 * u4 * q13 + 159053 / 2000000 * u4 * h13 -
    9 / 2000000 * v4 * q11 - 159053 / 2000000 * v4 * h11 +
    428613 / 4000000 * q11 * dv + 131469 / 800000 * h11 * dv +
    449916357 / 40000000000 * q11 - 455748411 / 50000000000 * q13 +
    1581392297 / 40000000000 * h11 -
    1862001973 / 50000000000 * h13

def alternatingDvCouplingSlopeU (q13 h13 : ℝ) : ℝ :=
  131840371117 / 1000000000000 * q13 +
    37612887329 / 1000000000000 * h13

def alternatingDvCouplingSlopeV (q11 h11 : ℝ) : ℝ :=
  -(131840371117 / 1000000000000) * q11 -
    37612887329 / 1000000000000 * h11

def alternatingDvCouplingSlopeQ11 (dv : ℝ) : ℝ :=
  -(1450000824049 / 4000000000000) * dv +
    159402405150221 / 40000000000000000

def alternatingDvCouplingSlopeQ13 : ℝ :=
  129855012337841 / 20000000000000000

def alternatingDvCouplingSlopeH11 (dv : ℝ) : ℝ :=
  -(528330613949 / 4000000000000) * dv +
    6366046085317 / 8000000000000000

def alternatingDvCouplingSlopeH13 : ℝ :=
  150599411718793 / 100000000000000000

def alternatingDvCouplingSlopeDv : ℝ :=
  -(1326033875555991 / 20000000000000000)

set_option maxHeartbeats 3000000 in
theorem alternatingDvCoupling_telescope
    (a x r u4 v4 q11 q13 h11 h13 dv : ℝ) :
    alternatingDvCoupling a x r u4 v4 q11 q13 h11 h13 dv cornerDv -
        alternatingDvCoupling
          (824479 / 1000000) (39761 / 1000000) (57183 / 1000000)
          (18 / 125) (-(1 / 250)) (889 / 5000) (1001 / 5000)
          (7 / 500) (-(9 / 1000)) (111 / 2000) cornerDv =
      (a - 824479 / 1000000) *
          alternatingDvCouplingSlopeA u4 v4 q11 q13 h11 h13 dv +
        (x - 39761 / 1000000) *
          alternatingDvCouplingSlopeX r u4 v4 q11 q13 h11 h13 +
        (r - 57183 / 1000000) *
          alternatingDvCouplingSlopeR r u4 v4 q11 q13 h11 h13 dv +
        (u4 - 18 / 125) * alternatingDvCouplingSlopeU q13 h13 +
        (v4 - (-(1 / 250))) * alternatingDvCouplingSlopeV q11 h11 +
        (q11 - 889 / 5000) * alternatingDvCouplingSlopeQ11 dv +
        (q13 - 1001 / 5000) * alternatingDvCouplingSlopeQ13 +
        (h11 - 7 / 500) * alternatingDvCouplingSlopeH11 dv +
        (h13 - (-(9 / 1000))) * alternatingDvCouplingSlopeH13 +
        (dv - 111 / 2000) * alternatingDvCouplingSlopeDv := by
  unfold alternatingDvCoupling alternatingAdjugateRowD
    alternatingMixedAdjugateRowD alternatingDvCouplingSlopeA
    alternatingDvCouplingSlopeX alternatingDvCouplingSlopeR
    alternatingDvCouplingSlopeU alternatingDvCouplingSlopeV
    alternatingDvCouplingSlopeQ11 alternatingDvCouplingSlopeQ13
    alternatingDvCouplingSlopeH11 alternatingDvCouplingSlopeH13
    alternatingDvCouplingSlopeDv
  dsimp only
  ring

def alternatingDvCrossSlopeA (u4 v4 dv : ℝ) : ℝ :=
  1 / 4 * u4 ^ 2 * dv + 279 / 20000 * u4 ^ 2 -
    1687 / 200000 * u4 * v4

def alternatingDvCrossSlopeX (u4 v4 : ℝ) : ℝ :=
  -(10763 / 40000) * u4 ^ 2 + 56173 / 200000 * u4 * v4

def alternatingDvCrossSlopeR (u4 v4 dv : ℝ) : ℝ :=
  -(56173 / 200000) * u4 * dv - 44531887 / 4000000000 * u4 +
    94763851 / 20000000000 * v4

def alternatingDvCrossSlopeU (u4 v4 dv : ℝ) : ℝ :=
  440139 / 800000 * u4 * dv + 392552987 / 40000000000 * u4 +
    20238499 / 6250000000 * v4 - 185555989 / 40000000000 * dv -
    4753308097029 / 400000000000000

def alternatingDvCrossSlopeV : ℝ :=
  245805614983 / 20000000000000

def alternatingDvCrossSlopeDv : ℝ :=
  19032950646767 / 500000000000000

set_option maxHeartbeats 3000000 in
theorem alternatingDvCross_telescope
    (a x r u4 v4 dv : ℝ) :
    alternatingDvCross a x r u4 v4 dv cornerDv -
        alternatingDvCross
          (826465 / 1000000) (37851 / 1000000) (49817 / 1000000)
          (141 / 1000) (-(1 / 500)) (558 / 10000) cornerDv =
      (a - 826465 / 1000000) * alternatingDvCrossSlopeA u4 v4 dv +
        (x - 37851 / 1000000) * alternatingDvCrossSlopeX u4 v4 +
        (r - 49817 / 1000000) * alternatingDvCrossSlopeR u4 v4 dv +
        (u4 - 141 / 1000) * alternatingDvCrossSlopeU u4 v4 dv +
        (v4 - (-(1 / 500))) * alternatingDvCrossSlopeV +
        (dv - 558 / 10000) * alternatingDvCrossSlopeDv := by
  unfold alternatingDvCross alternatingCrossGradientS
    alternatingCrossGradientFour alternatingDvCrossSlopeA
    alternatingDvCrossSlopeX alternatingDvCrossSlopeR
    alternatingDvCrossSlopeU alternatingDvCrossSlopeV
    alternatingDvCrossSlopeDv
  dsimp only
  ring

set_option maxHeartbeats 3000000 in
theorem alternatingDvCoupling_upper
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    alternatingDvCoupling a x r u4 v4 q11 q13 h11 h13 dv cornerDv ≤
      (-16 / 10000 : ℝ) := by
  rcases hbox.a_mem with ⟨haL, haU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  rcases hbox.v4_mem with ⟨hv4L, hv4U⟩
  rcases hbox.q11_mem with ⟨hq11L, hq11U⟩
  rcases hbox.q13_mem with ⟨hq13L, hq13U⟩
  rcases hbox.h11_mem with ⟨hh11L, hh11U⟩
  rcases hbox.h13_mem with ⟨hh13L, hh13U⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  norm_num at hu4U hv4L hv4U hq11L hq13U hh11L hh11U
  norm_num at hh13L hh13U hdvL hdvU
  have huqU : u4 * q13 ≤ (18 / 125 : ℝ) * (1001 / 5000) :=
    nonnegative_product_upper u4 q13 (18 / 125) (1001 / 5000)
      hu4U hq13U (by norm_num) (by linarith)
  have huhU : u4 * h13 ≤ (141 / 1000 : ℝ) * (-(9 / 1000)) :=
    positive_negative_product_upper u4 h13
      (141 / 1000) (-(9 / 1000))
      hu4L (by linarith) (by norm_num) hh13U
  have hqvL : (179 / 1000 : ℝ) * (-(1 / 250)) ≤ q11 * v4 :=
    positive_negative_product_lower q11 v4
      (179 / 1000) (-(1 / 250))
      (by linarith) hv4L (by norm_num) hq11U
  have hhvL : (1 / 50 : ℝ) * (-(1 / 250)) ≤ h11 * v4 :=
    positive_negative_product_lower h11 v4
      (1 / 50) (-(1 / 250))
      (by linarith) hv4L (by norm_num) hh11U
  have hqdvL : (889 / 5000 : ℝ) * (111 / 2000) ≤ q11 * dv :=
    nonnegative_product_lower q11 dv
      (889 / 5000) (111 / 2000)
      hq11L hdvL (by norm_num) (by linarith)
  have hhdvL : (7 / 500 : ℝ) * (111 / 2000) ≤ h11 * dv :=
    nonnegative_product_lower h11 dv
      (7 / 500) (111 / 2000)
      hh11L hdvL (by norm_num) (by linarith)
  have haSlope : alternatingDvCouplingSlopeA
      u4 v4 q11 q13 h11 h13 dv ≤ 0 := by
    unfold alternatingDvCouplingSlopeA
    nlinarith only [huqU, huhU, hqvL, hhvL, hqdvL, hhdvL,
      hq11L, hq13U, hh11L, hh13U]
  have hruU : r * u4 ≤
      (57183 / 1000000 : ℝ) * (18 / 125) :=
    nonnegative_product_upper r u4
      (57183 / 1000000) (18 / 125)
      hrU hu4U (by norm_num) (by linarith)
  have hruqU : (r * u4) * q13 ≤
      ((57183 / 1000000 : ℝ) * (18 / 125)) * (1001 / 5000) :=
    nonnegative_product_upper (r * u4) q13
      ((57183 / 1000000) * (18 / 125)) (1001 / 5000)
      hruU hq13U (by norm_num) (by linarith)
  have hruhL :
      ((57183 / 1000000 : ℝ) * (18 / 125)) * (-(11 / 1000)) ≤
        (r * u4) * h13 :=
    positive_negative_product_lower (r * u4) h13
      ((57183 / 1000000) * (18 / 125)) (-(11 / 1000))
      (mul_nonneg (by linarith) (by linarith)) hh13L
      (by norm_num) hruU
  have hrvL : (57183 / 1000000 : ℝ) * (-(1 / 250)) ≤ r * v4 :=
    positive_negative_product_lower r v4
      (57183 / 1000000) (-(1 / 250))
      (by linarith) hv4L (by norm_num) hrU
  have hrvqL :
      (179 / 1000 : ℝ) * ((57183 / 1000000) * (-(1 / 250))) ≤
        q11 * (r * v4) :=
    positive_negative_product_lower q11 (r * v4)
      (179 / 1000) ((57183 / 1000000) * (-(1 / 250)))
      (by linarith) hrvL (by norm_num) hq11U
  have hrvU : r * v4 ≤
      (49817 / 1000000 : ℝ) * (-(1 / 500)) :=
    positive_negative_product_upper r v4
      (49817 / 1000000) (-(1 / 500))
      hrL (by linarith) (by norm_num) hv4U
  have hrvhU : h11 * (r * v4) ≤
      (7 / 500 : ℝ) * ((49817 / 1000000) * (-(1 / 500))) :=
    positive_negative_product_upper h11 (r * v4)
      (7 / 500) ((49817 / 1000000) * (-(1 / 500)))
      hh11L (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith))
      (by norm_num) hrvU
  have huqL : (141 / 1000 : ℝ) * (1 / 5) ≤ u4 * q13 :=
    nonnegative_product_lower u4 q13
      (141 / 1000) (1 / 5)
      hu4L hq13L (by norm_num) (by linarith)
  have huhL : (18 / 125 : ℝ) * (-(11 / 1000)) ≤ u4 * h13 :=
    positive_negative_product_lower u4 h13
      (18 / 125) (-(11 / 1000))
      (by linarith) hh13L (by norm_num) hu4U
  have hvqU : q11 * v4 ≤
      (889 / 5000 : ℝ) * (-(1 / 500)) :=
    positive_negative_product_upper q11 v4
      (889 / 5000) (-(1 / 500))
      hq11L (by linarith) (by norm_num) hv4U
  have hvhU : h11 * v4 ≤
      (7 / 500 : ℝ) * (-(1 / 500)) :=
    positive_negative_product_upper h11 v4
      (7 / 500) (-(1 / 500))
      hh11L (by linarith) (by norm_num) hv4U
  have hxSlope : 0 ≤ alternatingDvCouplingSlopeX
      r u4 v4 q11 q13 h11 h13 := by
    unfold alternatingDvCouplingSlopeX
    nlinarith only [hruqU, hruhL, hrvqL, hrvhU, huqL, huhL,
      hvqU, hvhU, hq11L, hq13U, hh11L, hh13U]
  have hrqU : r * q11 ≤
      (57183 / 1000000 : ℝ) * (179 / 1000) :=
    nonnegative_product_upper r q11
      (57183 / 1000000) (179 / 1000)
      hrU hq11U (by norm_num) (by linarith)
  have hrqdvU : (r * q11) * dv ≤
      ((57183 / 1000000 : ℝ) * (179 / 1000)) * (279 / 5000) :=
    nonnegative_product_upper (r * q11) dv
      ((57183 / 1000000) * (179 / 1000)) (279 / 5000)
      hrqU hdvU (by norm_num) (by linarith)
  have hrhL : (49817 / 1000000 : ℝ) * (7 / 500) ≤ r * h11 :=
    nonnegative_product_lower r h11
      (49817 / 1000000) (7 / 500)
      hrL hh11L (by norm_num) (by linarith)
  have hrhdvL :
      ((49817 / 1000000 : ℝ) * (7 / 500)) * (111 / 2000) ≤
        (r * h11) * dv :=
    nonnegative_product_lower (r * h11) dv
      ((49817 / 1000000) * (7 / 500)) (111 / 2000)
      hrhL hdvL (by norm_num) (by linarith)
  have hrqL : (49817 / 1000000 : ℝ) * (1 / 5) ≤ r * q13 :=
    nonnegative_product_lower r q13
      (49817 / 1000000) (1 / 5)
      hrL hq13L (by norm_num) (by linarith)
  have hrhU : r * h13 ≤
      (49817 / 1000000 : ℝ) * (-(9 / 1000)) :=
    positive_negative_product_upper r h13
      (49817 / 1000000) (-(9 / 1000))
      hrL (by linarith) (by norm_num) hh13U
  have hrSlope : 0 ≤ alternatingDvCouplingSlopeR
      r u4 v4 q11 q13 h11 h13 dv := by
    unfold alternatingDvCouplingSlopeR
    nlinarith only [hrqdvU, hrhdvL, hrqU, hrqL, hrhL, hrhU,
      huqL, huhL, hvqU, hvhU, hqdvL, hhdvL,
      hq11L, hq13U, hh11L, hh13U]
  have huSlope : 0 ≤ alternatingDvCouplingSlopeU q13 h13 := by
    unfold alternatingDvCouplingSlopeU
    nlinarith only [hq13L, hh13L]
  have hvSlope : alternatingDvCouplingSlopeV q11 h11 ≤ 0 := by
    unfold alternatingDvCouplingSlopeV
    nlinarith only [hq11L, hh11L]
  have hq11Slope : alternatingDvCouplingSlopeQ11 dv ≤ 0 := by
    unfold alternatingDvCouplingSlopeQ11
    nlinarith only [hdvL]
  have hq13Slope : 0 ≤ alternatingDvCouplingSlopeQ13 := by
    norm_num [alternatingDvCouplingSlopeQ13]
  have hh11Slope : alternatingDvCouplingSlopeH11 dv ≤ 0 := by
    unfold alternatingDvCouplingSlopeH11
    nlinarith only [hdvL]
  have hh13Slope : 0 ≤ alternatingDvCouplingSlopeH13 := by
    norm_num [alternatingDvCouplingSlopeH13]
  have hdvSlope : alternatingDvCouplingSlopeDv ≤ 0 := by
    norm_num [alternatingDvCouplingSlopeDv]
  have haStep := mul_nonpos_of_nonneg_of_nonpos
    (by linarith : 0 ≤ a - 824479 / 1000000) haSlope
  have hxStep := mul_nonpos_of_nonpos_of_nonneg
    (by linarith : x - 39761 / 1000000 ≤ 0) hxSlope
  have hrStep := mul_nonpos_of_nonpos_of_nonneg
    (by linarith : r - 57183 / 1000000 ≤ 0) hrSlope
  have huStep := mul_nonpos_of_nonpos_of_nonneg
    (by linarith : u4 - 18 / 125 ≤ 0) huSlope
  have hvStep := mul_nonpos_of_nonneg_of_nonpos
    (by linarith : 0 ≤ v4 - (-(1 / 250))) hvSlope
  have hq11Step := mul_nonpos_of_nonneg_of_nonpos
    (by linarith : 0 ≤ q11 - 889 / 5000) hq11Slope
  have hq13Step := mul_nonpos_of_nonpos_of_nonneg
    (by linarith : q13 - 1001 / 5000 ≤ 0) hq13Slope
  have hh11Step := mul_nonpos_of_nonneg_of_nonpos
    (by linarith : 0 ≤ h11 - 7 / 500) hh11Slope
  have hh13Step := mul_nonpos_of_nonpos_of_nonneg
    (by linarith : h13 - (-(9 / 1000)) ≤ 0) hh13Slope
  have hdvStep := mul_nonpos_of_nonneg_of_nonpos
    (by linarith : 0 ≤ dv - 111 / 2000) hdvSlope
  have htel := alternatingDvCoupling_telescope
    a x r u4 v4 q11 q13 h11 h13 dv
  have hcorner : alternatingDvCoupling
      (824479 / 1000000) (39761 / 1000000) (57183 / 1000000)
      (18 / 125) (-(1 / 250)) (889 / 5000) (1001 / 5000)
      (7 / 500) (-(9 / 1000)) (111 / 2000) cornerDv ≤
        (-16 / 10000 : ℝ) := by
    norm_num [alternatingDvCoupling, alternatingAdjugateRowD,
      alternatingMixedAdjugateRowD, cornerA, cornerX, cornerR, cornerD,
      cornerF, corner_d, corner_f, cornerSu, cornerDu, cornerSv, cornerDv]
  nlinarith only [htel, hcorner, haStep, hxStep, hrStep, huStep,
    hvStep, hq11Step, hq13Step, hh11Step, hh13Step, hdvStep]

set_option maxHeartbeats 1000000 in
theorem alternatingDvCross_upper
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    alternatingDvCross a x r u4 v4 dv cornerDv ≤ (14 / 10000 : ℝ) := by
  rcases hbox.a_mem with ⟨haL, haU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  rcases hbox.v4_mem with ⟨hv4L, hv4U⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  norm_num at hu4U hv4L hv4U hdvL hdvU
  have huvNonpos : u4 * v4 ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have hudvNonneg : 0 ≤ u4 * dv :=
    mul_nonneg (by linarith) (by linarith)
  have huSqDvNonneg : 0 ≤ u4 ^ 2 * dv :=
    mul_nonneg (sq_nonneg u4) (by linarith)
  have haSlope : 0 ≤ alternatingDvCrossSlopeA u4 v4 dv := by
    unfold alternatingDvCrossSlopeA
    nlinarith only [sq_nonneg u4, huvNonpos, huSqDvNonneg]
  have hxSlope : alternatingDvCrossSlopeX u4 v4 ≤ 0 := by
    unfold alternatingDvCrossSlopeX
    nlinarith only [sq_nonneg u4, huvNonpos]
  have hrSlope : alternatingDvCrossSlopeR u4 v4 dv ≤ 0 := by
    unfold alternatingDvCrossSlopeR
    nlinarith only [hudvNonneg, hu4L, hv4U]
  have hudvU : u4 * dv ≤ (18 / 125 : ℝ) * (279 / 5000) :=
    nonnegative_product_upper u4 dv
      (18 / 125) (279 / 5000)
      hu4U hdvU (by norm_num) (by linarith)
  have huSlope : alternatingDvCrossSlopeU u4 v4 dv ≤ 0 := by
    unfold alternatingDvCrossSlopeU
    nlinarith only [hudvU, hu4U, hv4U, hdvL]
  have hvSlope : 0 ≤ alternatingDvCrossSlopeV := by
    norm_num [alternatingDvCrossSlopeV]
  have hdvSlope : 0 ≤ alternatingDvCrossSlopeDv := by
    norm_num [alternatingDvCrossSlopeDv]
  have haStep := mul_nonpos_of_nonpos_of_nonneg
    (by linarith : a - 826465 / 1000000 ≤ 0) haSlope
  have hxStep := mul_nonpos_of_nonneg_of_nonpos
    (by linarith : 0 ≤ x - 37851 / 1000000) hxSlope
  have hrStep := mul_nonpos_of_nonneg_of_nonpos
    (by linarith : 0 ≤ r - 49817 / 1000000) hrSlope
  have huStep := mul_nonpos_of_nonneg_of_nonpos
    (by linarith : 0 ≤ u4 - 141 / 1000) huSlope
  have hvStep := mul_nonpos_of_nonpos_of_nonneg
    (by linarith : v4 - (-(1 / 500)) ≤ 0) hvSlope
  have hdvStep := mul_nonpos_of_nonpos_of_nonneg
    (by linarith : dv - 558 / 10000 ≤ 0) hdvSlope
  have htel := alternatingDvCross_telescope a x r u4 v4 dv
  have hcorner : alternatingDvCross
      (826465 / 1000000) (37851 / 1000000) (49817 / 1000000)
      (141 / 1000) (-(1 / 500)) (558 / 10000) cornerDv ≤
        (14 / 10000 : ℝ) := by
    norm_num [alternatingDvCross, alternatingCrossGradientS,
      alternatingCrossGradientFour, cornerA, cornerX, cornerR, cornerD,
      cornerF, corner_d, corner_f, cornerSu, cornerDu, cornerSv, cornerDv]
  nlinarith only [htel, hcorner, haStep, hxStep, hrStep, huStep,
    hvStep, hdvStep]

set_option maxHeartbeats 3000000 in
theorem correlated_alternating_unfix_dv
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    alternatingFace a x r cornerSu cornerDu u4 cornerSv cornerDv v4
        q11 q13 q33 h11 h13 h33 ≤
      alternatingFace a x r cornerSu cornerDu u4 cornerSv dv v4
        q11 q13 q33 h11 h13 h33 := by
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  norm_num at hdvU
  let g : ℝ → ℝ := fun z ↦
    alternatingFace a x r cornerSu cornerDu u4 cornerSv z v4
      q11 q13 q33 h11 h13 h33
  have hcoupling := alternatingDvCoupling_upper
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hcross := alternatingDvCross_upper
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hsecCap : quadraticSecant g dv cornerDv ≤ (-2 / 10000 : ℝ) := by
    rw [show quadraticSecant g dv cornerDv =
        alternatingDvSlope a x r u4 v4 q11 q13 h11 h13 dv cornerDv by
      simpa only [g] using alternating_dv_secant_eq
        a x r u4 v4 q11 q13 q33 h11 h13 h33 dv cornerDv]
    unfold alternatingDvSlope
    nlinarith only [hcoupling, hcross]
  have hsec : quadraticSecant g dv cornerDv ≤ 0 :=
    hsecCap.trans (by norm_num)
  have hid : g dv - g cornerDv =
      (dv - cornerDv) * quadraticSecant g dv cornerDv := by
    unfold g alternatingFace quadraticSecant correlatedCoefficientThree
      alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
      alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00 alignedEntry02
      alignedEntry04 alignedEntry22 alignedEntry24 mixedDeterminantOne
    dsimp only
    ring
  exact quadraticSecant_upper_endpoint g dv cornerDv
    (by norm_num [cornerDv] at ⊢; exact hdvU) hsec hid

def alternatingAdjugateRowS
    (X R C D F ws wd w4 : ℝ) : ℝ :=
  ((F * C - D ^ 2) * ws - (F * X + R * D) * wd -
      (C * R + X * D) * w4) / 4

def alternatingMixedAdjugateRowS
    (X R C D F x r c d f ws wd w4 : ℝ) : ℝ :=
  ((F * c + f * C - 2 * D * d) * ws -
      (F * x + f * X + R * d + r * D) * wd -
      (C * r + c * R + X * d + x * D) * w4) / 4

def alternatingCrossGradientD
    (X C D zs zd z4 : ℝ) : ℝ :=
  (X * zs + C * zd - 2 * D * z4) / 2

def alternatingSvCoupling
    (x r u4 v4 q11 q13 h11 h13 dv sv sv0 : ℝ) : ℝ :=
  let Xp := cornerX - x
  let Rp := cornerR - r
  let Cp := cornerC - corner_c
  let Dp := cornerD - corner_d
  let Fp := cornerF - corner_f
  let Xm := cornerX + x
  let Rm := cornerR + r
  let Cm := cornerC + corner_c
  let Dm := cornerD + corner_d
  let Fm := cornerF + corner_f
  let o11p := q11 + h11
  let o13p := q13 + h13
  let o11m := q11 - h11
  let o13m := q13 - h13
  let svbar := (sv + sv0) / 2
  let wpS := o13p * cornerSu - o11p * svbar
  let wpD := o13p * cornerDu - o11p * dv
  let wp4 := o13p * u4 - o11p * v4
  let wmS := o13m * cornerSu - o11m * svbar
  let wmD := o13m * cornerDu - o11m * dv
  let wm4 := o13m * u4 - o11m * v4
  2 * (alternatingAdjugateRowS Xm Rm Cm Dm Fm wpS wpD wp4 +
    alternatingMixedAdjugateRowS Xp Rp Cp Dp Fp
      Xm Rm Cm Dm Fm wmS wmD wm4)

def alternatingSvCross
    (x r u4 v4 dv sv sv0 : ℝ) : ℝ :=
  let Xm := cornerX + x
  let Rm := cornerR + r
  let Cm := cornerC + corner_c
  let Dm := cornerD + corner_d
  let Fm := cornerF + corner_f
  let svbar := (sv + sv0) / 2
  let zs := u4 * dv - v4 * cornerDu
  let zd := v4 * cornerSu - u4 * svbar
  let z4 := (cornerDu * svbar - cornerSu * dv) / 2
  (-(u4 * alternatingCrossGradientD Xm Cm Dm zs zd z4)) +
    ((cornerDu / 2) * alternatingCrossGradientFour Rm Dm Fm zs zd z4)

def alternatingSvSlope
    (x r u4 v4 q11 q13 h11 h13 dv sv sv0 : ℝ) : ℝ :=
  alternatingSvCoupling x r u4 v4 q11 q13 h11 h13 dv sv sv0 +
    alternatingSvCross x r u4 v4 dv sv sv0

set_option maxHeartbeats 3000000 in
theorem alternating_sv_secant_eq
    (a x r u4 v4 q11 q13 q33 h11 h13 h33 dv sv sv0 : ℝ) :
    quadraticSecant
        (fun z ↦ alternatingFace a x r cornerSu cornerDu u4 z dv v4
          q11 q13 q33 h11 h13 h33)
        sv sv0 =
      alternatingSvSlope x r u4 v4 q11 q13 h11 h13 dv sv sv0 := by
  unfold quadraticSecant alternatingFace alternatingSvSlope
    alternatingSvCoupling alternatingSvCross alternatingAdjugateRowS
    alternatingMixedAdjugateRowS alternatingCrossGradientD
    alternatingCrossGradientFour correlatedCoefficientThree
    alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
    alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00 alignedEntry02
    alignedEntry04 alignedEntry22 alignedEntry24 mixedDeterminantOne
  dsimp only
  ring

def alternatingSvCouplingSlopeX
    (u4 v4 q11 q13 h11 h13 dv : ℝ) : ℝ :=
  -(19581 / 2000000) * u4 * q13 - 112849 / 2000000 * u4 * h13 +
    19581 / 2000000 * v4 * q11 + 112849 / 2000000 * v4 * h11 +
    3439 / 50000 * q11 * dv + 21103 / 50000 * h11 * dv -
    5801593 / 5000000000 * q13 - 35600761 / 5000000000 * h13

def alternatingSvCouplingSlopeR
    (u4 v4 q11 q13 h11 h13 dv : ℝ) : ℝ :=
  -(1213 / 400000) * u4 * q13 - 1389 / 80000 * u4 * h13 +
    1213 / 400000 * v4 * q11 + 1389 / 80000 * v4 * h11 +
    19581 / 2000000 * q11 * dv + 112849 / 2000000 * h11 * dv -
    33033147 / 200000000000 * q13 -
    190376263 / 200000000000 * h13

def alternatingSvCouplingSlopeU (q13 h13 : ℝ) : ℝ :=
  -(4617440949 / 500000000000) * q13 -
    937357521 / 500000000000 * h13

def alternatingSvCouplingSlopeV (q11 h11 : ℝ) : ℝ :=
  4617440949 / 500000000000 * q11 +
    937357521 / 500000000000 * h11

def alternatingSvCouplingSlopeQ11 (dv sv : ℝ) : ℝ :=
  17523518583 / 400000000000 * dv - 1763124909 / 800000000000 * sv -
    19567545837039 / 16000000000000000

def alternatingSvCouplingSlopeQ13 : ℝ :=
  2035614991407 / 5000000000000000

def alternatingSvCouplingSlopeH11 (dv sv : ℝ) : ℝ :=
  5469127563 / 400000000000 * dv - 487377321 / 800000000000 * sv -
    5365623868611 / 16000000000000000

def alternatingSvCouplingSlopeH13 : ℝ :=
  919083676479 / 5000000000000000

def alternatingSvCouplingSlopeDv : ℝ :=
  15961246949697 / 2000000000000000

def alternatingSvCouplingSlopeSv : ℝ :=
  -(1601534456571 / 4000000000000000)

set_option maxHeartbeats 3000000 in
theorem alternatingSvCoupling_telescope
    (x r u4 v4 q11 q13 h11 h13 dv sv : ℝ) :
    alternatingSvCoupling x r u4 v4 q11 q13 h11 h13 dv sv cornerSv -
        alternatingSvCoupling
          (37851 / 1000000) (49817 / 1000000) (18 / 125)
          (-(1 / 250)) (889 / 5000) (1 / 5) (7 / 500)
          (-(11 / 1000)) (111 / 2000) (53836 / 100000) cornerSv =
      (x - 37851 / 1000000) *
          alternatingSvCouplingSlopeX u4 v4 q11 q13 h11 h13 dv +
        (r - 49817 / 1000000) *
          alternatingSvCouplingSlopeR u4 v4 q11 q13 h11 h13 dv +
        (u4 - 18 / 125) * alternatingSvCouplingSlopeU q13 h13 +
        (v4 - (-(1 / 250))) * alternatingSvCouplingSlopeV q11 h11 +
        (q11 - 889 / 5000) * alternatingSvCouplingSlopeQ11 dv sv +
        (q13 - 1 / 5) * alternatingSvCouplingSlopeQ13 +
        (h11 - 7 / 500) * alternatingSvCouplingSlopeH11 dv sv +
        (h13 - (-(11 / 1000))) * alternatingSvCouplingSlopeH13 +
        (dv - 111 / 2000) * alternatingSvCouplingSlopeDv +
        (sv - 53836 / 100000) * alternatingSvCouplingSlopeSv := by
  unfold alternatingSvCoupling alternatingAdjugateRowS
    alternatingMixedAdjugateRowS alternatingSvCouplingSlopeX
    alternatingSvCouplingSlopeR alternatingSvCouplingSlopeU
    alternatingSvCouplingSlopeV alternatingSvCouplingSlopeQ11
    alternatingSvCouplingSlopeQ13 alternatingSvCouplingSlopeH11
    alternatingSvCouplingSlopeH13 alternatingSvCouplingSlopeDv
    alternatingSvCouplingSlopeSv
  dsimp only
  ring

def alternatingSvCrossSlopeX (u4 v4 dv : ℝ) : ℝ :=
  -(1 / 2) * u4 ^ 2 * dv + 1687 / 200000 * u4 * v4

def alternatingSvCrossSlopeR (u4 v4 dv : ℝ) : ℝ :=
  1687 / 200000 * u4 * dv - 2845969 / 20000000000 * v4

def alternatingSvCrossSlopeU (u4 v4 dv sv : ℝ) : ℝ :=
  -(79531 / 2000000) * u4 * dv + 4079 / 800000 * u4 * sv +
    43902277 / 16000000000 * u4 - 505739769 / 100000000000 * v4 -
    434707209 / 20000000000 * dv + 51097891 / 40000000000 * sv +
    549966600833 / 800000000000000

def alternatingSvCrossSlopeV : ℝ :=
  -(53424269239 / 50000000000000)

def alternatingSvCrossSlopeDv : ℝ :=
  -(1347595063673 / 250000000000000)

def alternatingSvCrossSlopeSv : ℝ :=
  107521475687 / 500000000000000

set_option maxHeartbeats 3000000 in
theorem alternatingSvCross_telescope
    (x r u4 v4 dv sv : ℝ) :
    alternatingSvCross x r u4 v4 dv sv cornerSv -
        alternatingSvCross
          (39761 / 1000000) (49817 / 1000000) (141 / 1000)
          (-(1 / 500)) (558 / 10000) (53815 / 100000) cornerSv =
      (x - 39761 / 1000000) * alternatingSvCrossSlopeX u4 v4 dv +
        (r - 49817 / 1000000) * alternatingSvCrossSlopeR u4 v4 dv +
        (u4 - 141 / 1000) * alternatingSvCrossSlopeU u4 v4 dv sv +
        (v4 - (-(1 / 500))) * alternatingSvCrossSlopeV +
        (dv - 558 / 10000) * alternatingSvCrossSlopeDv +
        (sv - 53815 / 100000) * alternatingSvCrossSlopeSv := by
  unfold alternatingSvCross alternatingCrossGradientD
    alternatingCrossGradientFour alternatingSvCrossSlopeX
    alternatingSvCrossSlopeR alternatingSvCrossSlopeU
    alternatingSvCrossSlopeV alternatingSvCrossSlopeDv
    alternatingSvCrossSlopeSv
  dsimp only
  ring

set_option maxHeartbeats 2000000 in
theorem alternatingSvCoupling_lower
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (8 / 100000 : ℝ) ≤
      alternatingSvCoupling x r u4 v4 q11 q13 h11 h13 dv sv cornerSv := by
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  rcases hbox.v4_mem with ⟨hv4L, hv4U⟩
  rcases hbox.q11_mem with ⟨hq11L, hq11U⟩
  rcases hbox.q13_mem with ⟨hq13L, hq13U⟩
  rcases hbox.h11_mem with ⟨hh11L, hh11U⟩
  rcases hbox.h13_mem with ⟨hh13L, hh13U⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  rcases hbox.sv_mem with ⟨hsvL, hsvU⟩
  norm_num at hu4U hv4L hv4U hq11L hq13U hh11L hh11U
  norm_num at hh13L hh13U hdvL hdvU hsvL hsvU
  have huqU : u4 * q13 ≤ (18 / 125 : ℝ) * (1001 / 5000) :=
    nonnegative_product_upper u4 q13 (18 / 125) (1001 / 5000)
      hu4U hq13U (by norm_num) (by linarith)
  have huhU : u4 * h13 ≤ (141 / 1000 : ℝ) * (-(9 / 1000)) :=
    positive_negative_product_upper u4 h13
      (141 / 1000) (-(9 / 1000))
      hu4L (by linarith) (by norm_num) hh13U
  have hvqL : (179 / 1000 : ℝ) * (-(1 / 250)) ≤ q11 * v4 :=
    positive_negative_product_lower q11 v4
      (179 / 1000) (-(1 / 250))
      (by linarith) hv4L (by norm_num) hq11U
  have hvhL : (1 / 50 : ℝ) * (-(1 / 250)) ≤ h11 * v4 :=
    positive_negative_product_lower h11 v4
      (1 / 50) (-(1 / 250))
      (by linarith) hv4L (by norm_num) hh11U
  have hqdvL : (889 / 5000 : ℝ) * (111 / 2000) ≤ q11 * dv :=
    nonnegative_product_lower q11 dv
      (889 / 5000) (111 / 2000)
      hq11L hdvL (by norm_num) (by linarith)
  have hhdvL : (7 / 500 : ℝ) * (111 / 2000) ≤ h11 * dv :=
    nonnegative_product_lower h11 dv
      (7 / 500) (111 / 2000)
      hh11L hdvL (by norm_num) (by linarith)
  have hxSlope : 0 ≤ alternatingSvCouplingSlopeX
      u4 v4 q11 q13 h11 h13 dv := by
    unfold alternatingSvCouplingSlopeX
    nlinarith only [huqU, huhU, hvqL, hvhL, hqdvL, hhdvL,
      hq13U, hh13U]
  have hrSlope : 0 ≤ alternatingSvCouplingSlopeR
      u4 v4 q11 q13 h11 h13 dv := by
    unfold alternatingSvCouplingSlopeR
    nlinarith only [huqU, huhU, hvqL, hvhL, hqdvL, hhdvL,
      hq13U, hh13U]
  have huSlope : alternatingSvCouplingSlopeU q13 h13 ≤ 0 := by
    unfold alternatingSvCouplingSlopeU
    nlinarith only [hq13L, hh13L]
  have hvSlope : 0 ≤ alternatingSvCouplingSlopeV q11 h11 := by
    unfold alternatingSvCouplingSlopeV
    nlinarith only [hq11L, hh11L]
  have hq11Slope : 0 ≤ alternatingSvCouplingSlopeQ11 dv sv := by
    unfold alternatingSvCouplingSlopeQ11
    nlinarith only [hdvL, hsvU]
  have hq13Slope : 0 ≤ alternatingSvCouplingSlopeQ13 := by
    norm_num [alternatingSvCouplingSlopeQ13]
  have hh11Slope : 0 ≤ alternatingSvCouplingSlopeH11 dv sv := by
    unfold alternatingSvCouplingSlopeH11
    nlinarith only [hdvL, hsvU]
  have hh13Slope : 0 ≤ alternatingSvCouplingSlopeH13 := by
    norm_num [alternatingSvCouplingSlopeH13]
  have hdvSlope : 0 ≤ alternatingSvCouplingSlopeDv := by
    norm_num [alternatingSvCouplingSlopeDv]
  have hsvSlope : alternatingSvCouplingSlopeSv ≤ 0 := by
    norm_num [alternatingSvCouplingSlopeSv]
  have hxStep := mul_nonneg
    (by linarith : 0 ≤ x - 37851 / 1000000) hxSlope
  have hrStep := mul_nonneg
    (by linarith : 0 ≤ r - 49817 / 1000000) hrSlope
  have huStep := mul_nonneg_of_nonpos_of_nonpos
    (by linarith : u4 - 18 / 125 ≤ 0) huSlope
  have hvStep := mul_nonneg
    (by linarith : 0 ≤ v4 - (-(1 / 250))) hvSlope
  have hq11Step := mul_nonneg
    (by linarith : 0 ≤ q11 - 889 / 5000) hq11Slope
  have hq13Step := mul_nonneg
    (by linarith : 0 ≤ q13 - 1 / 5) hq13Slope
  have hh11Step := mul_nonneg
    (by linarith : 0 ≤ h11 - 7 / 500) hh11Slope
  have hh13Step := mul_nonneg
    (by linarith : 0 ≤ h13 - (-(11 / 1000))) hh13Slope
  have hdvStep := mul_nonneg
    (by linarith : 0 ≤ dv - 111 / 2000) hdvSlope
  have hsvStep := mul_nonneg_of_nonpos_of_nonpos
    (by linarith : sv - 53836 / 100000 ≤ 0) hsvSlope
  have htel := alternatingSvCoupling_telescope
    x r u4 v4 q11 q13 h11 h13 dv sv
  have hcorner : (8 / 100000 : ℝ) ≤ alternatingSvCoupling
      (37851 / 1000000) (49817 / 1000000) (18 / 125)
      (-(1 / 250)) (889 / 5000) (1 / 5) (7 / 500)
      (-(11 / 1000)) (111 / 2000) (53836 / 100000) cornerSv := by
    norm_num [alternatingSvCoupling, alternatingAdjugateRowS,
      alternatingMixedAdjugateRowS, cornerX, cornerR, cornerC, cornerD,
      cornerF, corner_c, corner_d, corner_f, cornerSu, cornerDu,
      cornerSv]
  nlinarith only [htel, hcorner, hxStep, hrStep, huStep, hvStep,
    hq11Step, hq13Step, hh11Step, hh13Step, hdvStep, hsvStep]

set_option maxHeartbeats 1000000 in
theorem alternatingSvCross_lower
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (-7 / 100000 : ℝ) ≤ alternatingSvCross x r u4 v4 dv sv cornerSv := by
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  rcases hbox.v4_mem with ⟨hv4L, hv4U⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  rcases hbox.sv_mem with ⟨hsvL, hsvU⟩
  norm_num at hu4U hv4L hv4U hdvL hdvU hsvL hsvU
  have huvNonpos : u4 * v4 ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have huSqDvNonneg : 0 ≤ u4 ^ 2 * dv :=
    mul_nonneg (sq_nonneg u4) (by linarith)
  have hxSlope : alternatingSvCrossSlopeX u4 v4 dv ≤ 0 := by
    unfold alternatingSvCrossSlopeX
    nlinarith only [huvNonpos, huSqDvNonneg]
  have hudvNonneg : 0 ≤ u4 * dv :=
    mul_nonneg (by linarith) (by linarith)
  have hrSlope : 0 ≤ alternatingSvCrossSlopeR u4 v4 dv := by
    unfold alternatingSvCrossSlopeR
    nlinarith only [hudvNonneg, hv4U]
  have hudvU : u4 * dv ≤ (18 / 125 : ℝ) * (279 / 5000) :=
    nonnegative_product_upper u4 dv
      (18 / 125) (279 / 5000)
      hu4U hdvU (by norm_num) (by linarith)
  have husvL : (141 / 1000 : ℝ) * (10763 / 20000) ≤ u4 * sv :=
    nonnegative_product_lower u4 sv
      (141 / 1000) (10763 / 20000)
      hu4L hsvL (by norm_num) (by linarith)
  have huSlope : 0 ≤ alternatingSvCrossSlopeU u4 v4 dv sv := by
    unfold alternatingSvCrossSlopeU
    nlinarith only [hudvU, husvL, hu4L, hv4U, hdvU, hsvL]
  have hvSlope : alternatingSvCrossSlopeV ≤ 0 := by
    norm_num [alternatingSvCrossSlopeV]
  have hdvSlope : alternatingSvCrossSlopeDv ≤ 0 := by
    norm_num [alternatingSvCrossSlopeDv]
  have hsvSlope : 0 ≤ alternatingSvCrossSlopeSv := by
    norm_num [alternatingSvCrossSlopeSv]
  have hxStep := mul_nonneg_of_nonpos_of_nonpos
    (by linarith : x - 39761 / 1000000 ≤ 0) hxSlope
  have hrStep := mul_nonneg
    (by linarith : 0 ≤ r - 49817 / 1000000) hrSlope
  have huStep := mul_nonneg
    (by linarith : 0 ≤ u4 - 141 / 1000) huSlope
  have hvStep := mul_nonneg_of_nonpos_of_nonpos
    (by linarith : v4 - (-(1 / 500)) ≤ 0) hvSlope
  have hdvStep := mul_nonneg_of_nonpos_of_nonpos
    (by linarith : dv - 558 / 10000 ≤ 0) hdvSlope
  have hsvStep := mul_nonneg
    (by linarith : 0 ≤ sv - 53815 / 100000) hsvSlope
  have htel := alternatingSvCross_telescope x r u4 v4 dv sv
  have hcorner : (-7 / 100000 : ℝ) ≤ alternatingSvCross
      (39761 / 1000000) (49817 / 1000000) (141 / 1000)
      (-(1 / 500)) (558 / 10000) (53815 / 100000) cornerSv := by
    norm_num [alternatingSvCross, alternatingCrossGradientD,
      alternatingCrossGradientFour, cornerX, cornerR, cornerC, cornerD,
      cornerF, corner_c, corner_d, corner_f, cornerSu, cornerDu,
      cornerSv]
  nlinarith only [htel, hcorner, hxStep, hrStep, huStep, hvStep,
    hdvStep, hsvStep]

set_option maxHeartbeats 3000000 in
theorem correlated_alternating_unfix_sv
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    alternatingFace a x r cornerSu cornerDu u4 cornerSv dv v4
        q11 q13 q33 h11 h13 h33 ≤
      alternatingFace a x r cornerSu cornerDu u4 sv dv v4
        q11 q13 q33 h11 h13 h33 := by
  rcases hbox.sv_mem with ⟨hsvL, hsvU⟩
  norm_num at hsvL
  let g : ℝ → ℝ := fun z ↦
    alternatingFace a x r cornerSu cornerDu u4 z dv v4
      q11 q13 q33 h11 h13 h33
  have hcoupling := alternatingSvCoupling_lower
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hcross := alternatingSvCross_lower
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hsecCap : (1 / 100000 : ℝ) ≤ quadraticSecant g sv cornerSv := by
    rw [show quadraticSecant g sv cornerSv =
        alternatingSvSlope x r u4 v4 q11 q13 h11 h13 dv sv cornerSv by
      simpa only [g] using alternating_sv_secant_eq
        a x r u4 v4 q11 q13 q33 h11 h13 h33 dv sv cornerSv]
    unfold alternatingSvSlope
    nlinarith only [hcoupling, hcross]
  have hsec : 0 ≤ quadraticSecant g sv cornerSv :=
    le_trans (by norm_num) hsecCap
  have hid : g sv - g cornerSv =
      (sv - cornerSv) * quadraticSecant g sv cornerSv := by
    unfold g alternatingFace quadraticSecant correlatedCoefficientThree
      alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
      alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00 alignedEntry02
      alignedEntry04 alignedEntry22 alignedEntry24 mixedDeterminantOne
    dsimp only
    ring
  exact quadraticSecant_lower_endpoint g sv cornerSv
    (by norm_num [cornerSv] at ⊢; exact hsvL) hsec hid

def alternatingDuCoupling
    (a x r u4 sv dv v4 q13 q33 h13 h33 du du0 : ℝ) : ℝ :=
  let Ap := cornerA - a
  let Xp := cornerX - x
  let Rp := cornerR - r
  let Dp := cornerD - corner_d
  let Fp := cornerF - corner_f
  let Am := cornerA + a
  let Xm := cornerX + x
  let Rm := cornerR + r
  let Dm := cornerD + corner_d
  let Fm := cornerF + corner_f
  let o13p := q13 + h13
  let o33p := q33 + h33
  let o13m := q13 - h13
  let o33m := q33 - h33
  let dubar := (du + du0) / 2
  let wpS := o33p * cornerSu - o13p * sv
  let wpD := o33p * dubar - o13p * dv
  let wp4 := o33p * u4 - o13p * v4
  let wmS := o33m * cornerSu - o13m * sv
  let wmD := o33m * dubar - o13m * dv
  let wm4 := o33m * u4 - o13m * v4
  (-2 : ℝ) * (alternatingAdjugateRowD Am Xm Rm Dm Fm wpS wpD wp4 +
    alternatingMixedAdjugateRowD Ap Xp Rp Dp Fp
      Am Xm Rm Dm Fm wmS wmD wm4)

def alternatingDuCross
    (a x r u4 sv dv v4 du du0 : ℝ) : ℝ :=
  let Am := cornerA + a
  let Xm := cornerX + x
  let Rm := cornerR + r
  let Dm := cornerD + corner_d
  let Fm := cornerF + corner_f
  let dubar := (du + du0) / 2
  let zs := u4 * dv - v4 * dubar
  let zd := v4 * cornerSu - u4 * sv
  let z4 := (dubar * sv - cornerSu * dv) / 2
  ((-v4) * alternatingCrossGradientS Am Xm Rm zs zd z4) +
    ((sv / 2) * alternatingCrossGradientFour Rm Dm Fm zs zd z4)

def alternatingDuSlope
    (a x r u4 sv dv v4 q13 q33 h13 h33 du du0 : ℝ) : ℝ :=
  alternatingDuCoupling a x r u4 sv dv v4 q13 q33 h13 h33 du du0 +
    alternatingDuCross a x r u4 sv dv v4 du du0

set_option maxHeartbeats 3000000 in
theorem alternating_du_secant_eq
    (a x r u4 sv dv v4 q11 q13 q33 h11 h13 h33 du du0 : ℝ) :
    quadraticSecant
        (fun z ↦ alternatingFace a x r cornerSu z u4 sv dv v4
          q11 q13 q33 h11 h13 h33)
        du du0 =
      alternatingDuSlope a x r u4 sv dv v4 q13 q33 h13 h33 du du0 := by
  unfold quadraticSecant alternatingFace alternatingDuSlope
    alternatingDuCoupling alternatingDuCross alternatingAdjugateRowD
    alternatingMixedAdjugateRowD alternatingCrossGradientS
    alternatingCrossGradientFour correlatedCoefficientThree
    alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
    alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00 alignedEntry02
    alignedEntry04 alignedEntry22 alignedEntry24 mixedDeterminantOne
  dsimp only
  ring

def alternatingDuCouplingSlopeA
    (u4 dv v4 q13 q33 h13 h33 du : ℝ) : ℝ :=
  -(19581 / 2000000) * u4 * q33 - 112849 / 2000000 * u4 * h33 +
    19581 / 2000000 * v4 * q13 + 112849 / 2000000 * v4 * h13 +
    3439 / 50000 * q13 * dv - 3439 / 100000 * q33 * du +
    21103 / 50000 * h13 * dv - 21103 / 100000 * h33 * du -
    5801593 / 10000000000 * q33 - 35600761 / 10000000000 * h33

def alternatingDuCouplingSlopeX
    (r u4 sv v4 q13 q33 h13 h33 : ℝ) : ℝ :=
  1 / 2 * r * u4 * q33 - 3 / 2 * r * u4 * h33 -
    1 / 2 * r * v4 * q13 + 3 / 2 * r * v4 * h13 -
    121449 / 1000000 * u4 * q33 - 121449 / 1000000 * u4 * h33 +
    121449 / 1000000 * v4 * q13 + 121449 / 1000000 * v4 * h13 -
    3439 / 50000 * q13 * sv - 21103 / 50000 * h13 * sv +
    193178947 / 5000000000 * q33 + 1185418819 / 5000000000 * h33

def alternatingDuCouplingSlopeR
    (r u4 sv dv v4 q13 q33 h13 h33 du : ℝ) : ℝ :=
  1 / 2 * r * q13 * dv - 1 / 4 * r * q33 * du -
    3 / 2 * r * h13 * dv + 3 / 4 * r * h33 * du -
    1687 / 400000 * r * q33 + 5061 / 400000 * r * h33 -
    9 / 2000000 * u4 * q33 - 159053 / 2000000 * u4 * h33 +
    9 / 2000000 * v4 * q13 + 159053 / 2000000 * v4 * h13 -
    428613 / 2000000 * q13 * dv - 19581 / 2000000 * q13 * sv +
    428613 / 4000000 * q33 * du - 131469 / 400000 * h13 * dv -
    112849 / 2000000 * h13 * sv + 131469 / 800000 * h33 * du +
    2922917157 / 400000000000 * q33 +
    13787074769 / 400000000000 * h33

def alternatingDuCouplingSlopeU (q33 h33 : ℝ) : ℝ :=
  -(131840371117 / 1000000000000) * q33 -
    37612887329 / 1000000000000 * h33

def alternatingDuCouplingSlopeV (q13 h13 : ℝ) : ℝ :=
  131840371117 / 1000000000000 * q13 +
    37612887329 / 1000000000000 * h13

def alternatingDuCouplingSlopeQ13 (dv sv : ℝ) : ℝ :=
  1450000824049 / 2000000000000 * dv -
    88024566161 / 2000000000000 * sv -
    131840371117 / 250000000000000

def alternatingDuCouplingSlopeQ33 (du : ℝ) : ℝ :=
  -(1450000824049 / 4000000000000) * du -
    150948856586157 / 400000000000000000

def alternatingDuCouplingSlopeH13 (dv sv : ℝ) : ℝ :=
  528330613949 / 2000000000000 * dv -
    29789152749 / 2000000000000 * sv -
    37612887329 / 250000000000000

def alternatingDuCouplingSlopeH33 (du : ℝ) : ℝ :=
  -(528330613949 / 4000000000000) * du +
    288896098856791 / 400000000000000000

def alternatingDuCouplingSlopeDv : ℝ :=
  284188528056361 / 2000000000000000

def alternatingDuCouplingSlopeSv : ℝ :=
  -(17277232551961 / 2000000000000000)

def alternatingDuCouplingSlopeDu : ℝ :=
  -(105258898144071 / 1000000000000000)

set_option maxHeartbeats 3000000 in
theorem alternatingDuCoupling_telescope
    (a x r u4 sv dv v4 q13 q33 h13 h33 du : ℝ) :
    alternatingDuCoupling a x r u4 sv dv v4 q13 q33 h13 h33 du cornerDu -
        alternatingDuCoupling
          (824479 / 1000000) (39761 / 1000000) (57183 / 1000000)
          (18 / 125) (13459 / 25000) (111 / 2000) (-(1 / 250))
          (1 / 5) (333 / 1000) (-(11 / 1000)) (-(117 / 1000))
          (423 / 25000) cornerDu =
      (a - 824479 / 1000000) *
          alternatingDuCouplingSlopeA u4 dv v4 q13 q33 h13 h33 du +
        (x - 39761 / 1000000) *
          alternatingDuCouplingSlopeX r u4 sv v4 q13 q33 h13 h33 +
        (r - 57183 / 1000000) *
          alternatingDuCouplingSlopeR r u4 sv dv v4 q13 q33 h13 h33 du +
        (u4 - 18 / 125) * alternatingDuCouplingSlopeU q33 h33 +
        (v4 - (-(1 / 250))) * alternatingDuCouplingSlopeV q13 h13 +
        (q13 - 1 / 5) * alternatingDuCouplingSlopeQ13 dv sv +
        (q33 - 333 / 1000) * alternatingDuCouplingSlopeQ33 du +
        (h13 - (-(11 / 1000))) * alternatingDuCouplingSlopeH13 dv sv +
        (h33 - (-(117 / 1000))) * alternatingDuCouplingSlopeH33 du +
        (dv - 111 / 2000) * alternatingDuCouplingSlopeDv +
        (sv - 13459 / 25000) * alternatingDuCouplingSlopeSv +
        (du - 423 / 25000) * alternatingDuCouplingSlopeDu := by
  unfold alternatingDuCoupling alternatingAdjugateRowD
    alternatingMixedAdjugateRowD alternatingDuCouplingSlopeA
    alternatingDuCouplingSlopeX alternatingDuCouplingSlopeR
    alternatingDuCouplingSlopeU alternatingDuCouplingSlopeV
    alternatingDuCouplingSlopeQ13 alternatingDuCouplingSlopeQ33
    alternatingDuCouplingSlopeH13 alternatingDuCouplingSlopeH33
    alternatingDuCouplingSlopeDv alternatingDuCouplingSlopeSv
    alternatingDuCouplingSlopeDu
  dsimp only
  ring

def alternatingDuCrossSlopeA (u4 dv v4 du : ℝ) : ℝ :=
  -(1 / 2) * u4 * v4 * dv + 1 / 4 * v4 ^ 2 * du +
    1687 / 400000 * v4 ^ 2

def alternatingDuCrossSlopeX (u4 sv v4 : ℝ) : ℝ :=
  1 / 2 * u4 * v4 * sv - 56173 / 200000 * v4 ^ 2

def alternatingDuCrossSlopeR (u4 sv dv v4 du : ℝ) : ℝ :=
  1 / 2 * u4 * dv * sv - 1 / 2 * v4 * sv * du +
    56173 / 200000 * v4 * dv - 1687 / 200000 * v4 * sv

def alternatingDuCrossSlopeU (sv dv v4 : ℝ) : ℝ :=
  -(2198709 / 2000000) * v4 * dv + 77621 / 2000000 * v4 * sv +
    58543 / 400000 * dv * sv + 13243 / 400000 * sv ^ 2

def alternatingDuCrossSlopeV (sv dv v4 du : ℝ) : ℝ :=
  2198709 / 4000000 * v4 * du - 58543 / 400000 * sv * du -
    5011186783 / 400000000000 * v4 - 2911823441 / 40000000000 * dv -
    31188493 / 2000000000 * sv - 2198709 / 2000000000 * du +
    5011186783 / 200000000000000

def alternatingDuCrossSlopeDv (sv : ℝ) : ℝ :=
  -(1172233691 / 10000000000) * sv +
    2911823441 / 20000000000000

def alternatingDuCrossSlopeSv (sv du : ℝ) : ℝ :=
  12271 / 100000 * sv * du + 2105711 / 312500000 * sv +
    132658203 / 2000000000 * du - 28836727039 / 10000000000000

def alternatingDuCrossSlopeDu : ℝ :=
  1427888187249 / 40000000000000

set_option maxHeartbeats 3000000 in
theorem alternatingDuCross_telescope
    (a x r u4 sv dv v4 du : ℝ) :
    alternatingDuCross a x r u4 sv dv v4 du cornerDu -
        alternatingDuCross
          (824479 / 1000000) (37851 / 1000000) (49817 / 1000000)
          (141 / 1000) (10763 / 20000) (558 / 10000) (-(1 / 500))
          (1687 / 100000) cornerDu =
      (a - 824479 / 1000000) * alternatingDuCrossSlopeA u4 dv v4 du +
        (x - 37851 / 1000000) * alternatingDuCrossSlopeX u4 sv v4 +
        (r - 49817 / 1000000) * alternatingDuCrossSlopeR u4 sv dv v4 du +
        (u4 - 141 / 1000) * alternatingDuCrossSlopeU sv dv v4 +
        (v4 - (-(1 / 500))) * alternatingDuCrossSlopeV sv dv v4 du +
        (dv - 558 / 10000) * alternatingDuCrossSlopeDv sv +
        (sv - 10763 / 20000) * alternatingDuCrossSlopeSv sv du +
        (du - 1687 / 100000) * alternatingDuCrossSlopeDu := by
  unfold alternatingDuCross alternatingCrossGradientS
    alternatingCrossGradientFour alternatingDuCrossSlopeA
    alternatingDuCrossSlopeX alternatingDuCrossSlopeR
    alternatingDuCrossSlopeU alternatingDuCrossSlopeV
    alternatingDuCrossSlopeDv alternatingDuCrossSlopeSv
    alternatingDuCrossSlopeDu
  dsimp only
  ring

set_option maxHeartbeats 3000000 in
theorem alternatingDuCoupling_lower
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (11 / 10000 : ℝ) ≤
      alternatingDuCoupling a x r u4 sv dv v4 q13 q33 h13 h33 du cornerDu := by
  rcases hbox.a_mem with ⟨haL, haU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  rcases hbox.sv_mem with ⟨hsvL, hsvU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  rcases hbox.v4_mem with ⟨hv4L, hv4U⟩
  rcases hbox.q13_mem with ⟨hq13L, hq13U⟩
  rcases hbox.q33_mem with ⟨hq33L, hq33U⟩
  rcases hbox.h13_mem with ⟨hh13L, hh13U⟩
  rcases hbox.h33_mem with ⟨hh33L, hh33U⟩
  rcases hbox.du_mem with ⟨hduL, hduU⟩
  norm_num at haL haU hxL hxU hrL hrU hu4L hu4U hsvL hsvU
  norm_num at hdvL hdvU hv4L hv4U hq13L hq13U hq33L hq33U
  norm_num at hh13L hh13U hh33L hh33U hduL hduU
  have hnvL : (1 / 500 : ℝ) ≤ -v4 := by linarith
  have hnvU : -v4 ≤ (1 / 250 : ℝ) := by linarith
  have hnh13L : (9 / 1000 : ℝ) ≤ -h13 := by linarith
  have hnh13U : -h13 ≤ (11 / 1000 : ℝ) := by linarith
  have hnh33L : (117 / 1000 : ℝ) ≤ -h33 := by linarith
  have hnh33U : -h33 ≤ (3 / 25 : ℝ) := by linarith
  have huq33L : (141 / 1000 : ℝ) * (663 / 2000) ≤ u4 * q33 :=
    nonnegative_product_lower u4 q33 (141 / 1000) (663 / 2000)
      hu4L hq33L (by norm_num) (by linarith)
  have huq33U : u4 * q33 ≤ (18 / 125 : ℝ) * (333 / 1000) :=
    nonnegative_product_upper u4 q33 (18 / 125) (333 / 1000)
      hu4U hq33U (by norm_num) (by linarith)
  have hunh33L : (141 / 1000 : ℝ) * (117 / 1000) ≤ u4 * (-h33) :=
    nonnegative_product_lower u4 (-h33) (141 / 1000) (117 / 1000)
      hu4L hnh33L (by norm_num) (by linarith)
  have hunh33U : u4 * (-h33) ≤ (18 / 125 : ℝ) * (3 / 25) :=
    nonnegative_product_upper u4 (-h33) (18 / 125) (3 / 25)
      hu4U hnh33U (by norm_num) (by linarith)
  have hnvq13L : (1 / 500 : ℝ) * (1 / 5) ≤ (-v4) * q13 :=
    nonnegative_product_lower (-v4) q13 (1 / 500) (1 / 5)
      hnvL hq13L (by norm_num) (by linarith)
  have hnvq13U : (-v4) * q13 ≤ (1 / 250 : ℝ) * (1001 / 5000) :=
    nonnegative_product_upper (-v4) q13 (1 / 250) (1001 / 5000)
      hnvU hq13U (by norm_num) (by linarith)
  have hnvnh13L : (1 / 500 : ℝ) * (9 / 1000) ≤ (-v4) * (-h13) :=
    nonnegative_product_lower (-v4) (-h13) (1 / 500) (9 / 1000)
      hnvL hnh13L (by norm_num) (by linarith)
  have hnvnh13U : (-v4) * (-h13) ≤ (1 / 250 : ℝ) * (11 / 1000) :=
    nonnegative_product_upper (-v4) (-h13) (1 / 250) (11 / 1000)
      hnvU hnh13U (by norm_num) (by linarith)
  have hq13dvL : (1 / 5 : ℝ) * (111 / 2000) ≤ q13 * dv :=
    nonnegative_product_lower q13 dv (1 / 5) (111 / 2000)
      hq13L hdvL (by norm_num) (by linarith)
  have hq13dvU : q13 * dv ≤ (1001 / 5000 : ℝ) * (279 / 5000) :=
    nonnegative_product_upper q13 dv (1001 / 5000) (279 / 5000)
      hq13U hdvU (by norm_num) (by linarith)
  have hq33duL : (663 / 2000 : ℝ) * (1687 / 100000) ≤ q33 * du :=
    nonnegative_product_lower q33 du (663 / 2000) (1687 / 100000)
      hq33L hduL (by norm_num) (by linarith)
  have hq33duU : q33 * du ≤ (333 / 1000 : ℝ) * (423 / 25000) :=
    nonnegative_product_upper q33 du (333 / 1000) (423 / 25000)
      hq33U hduU (by norm_num) (by linarith)
  have hnh13dvL : (9 / 1000 : ℝ) * (111 / 2000) ≤ (-h13) * dv :=
    nonnegative_product_lower (-h13) dv (9 / 1000) (111 / 2000)
      hnh13L hdvL (by norm_num) (by linarith)
  have hnh13dvU : (-h13) * dv ≤ (11 / 1000 : ℝ) * (279 / 5000) :=
    nonnegative_product_upper (-h13) dv (11 / 1000) (279 / 5000)
      hnh13U hdvU (by norm_num) (by linarith)
  have hnh33duL : (117 / 1000 : ℝ) * (1687 / 100000) ≤ (-h33) * du :=
    nonnegative_product_lower (-h33) du (117 / 1000) (1687 / 100000)
      hnh33L hduL (by norm_num) (by linarith)
  have hnh33duU : (-h33) * du ≤ (3 / 25 : ℝ) * (423 / 25000) :=
    nonnegative_product_upper (-h33) du (3 / 25) (423 / 25000)
      hnh33U hduU (by norm_num) (by linarith)
  have hq13svL : (1 / 5 : ℝ) * (10763 / 20000) ≤ q13 * sv :=
    nonnegative_product_lower q13 sv (1 / 5) (10763 / 20000)
      hq13L hsvL (by norm_num) (by linarith)
  have hnh13svU : (-h13) * sv ≤ (11 / 1000 : ℝ) * (13459 / 25000) :=
    nonnegative_product_upper (-h13) sv (11 / 1000) (13459 / 25000)
      hnh13U hsvU (by norm_num) (by linarith)
  have hruq33U : r * (u4 * q33) ≤
      (57183 / 1000000 : ℝ) * ((18 / 125) * (333 / 1000)) :=
    nonnegative_product_upper r (u4 * q33)
      (57183 / 1000000) ((18 / 125) * (333 / 1000))
      hrU huq33U (by norm_num) (mul_nonneg (by linarith) (by linarith))
  have hrunh33U : r * (u4 * (-h33)) ≤
      (57183 / 1000000 : ℝ) * ((18 / 125) * (3 / 25)) :=
    nonnegative_product_upper r (u4 * (-h33))
      (57183 / 1000000) ((18 / 125) * (3 / 25))
      hrU hunh33U (by norm_num) (mul_nonneg (by linarith) (by linarith))
  have hrnvq13U : r * ((-v4) * q13) ≤
      (57183 / 1000000 : ℝ) * ((1 / 250) * (1001 / 5000)) :=
    nonnegative_product_upper r ((-v4) * q13)
      (57183 / 1000000) ((1 / 250) * (1001 / 5000))
      hrU hnvq13U (by norm_num) (mul_nonneg (by linarith) (by linarith))
  have hrnvnh13U : r * ((-v4) * (-h13)) ≤
      (57183 / 1000000 : ℝ) * ((1 / 250) * (11 / 1000)) :=
    nonnegative_product_upper r ((-v4) * (-h13))
      (57183 / 1000000) ((1 / 250) * (11 / 1000))
      hrU hnvnh13U (by norm_num) (mul_nonneg (by linarith) (by linarith))
  have hrq13dvU : r * (q13 * dv) ≤
      (57183 / 1000000 : ℝ) * ((1001 / 5000) * (279 / 5000)) :=
    nonnegative_product_upper r (q13 * dv)
      (57183 / 1000000) ((1001 / 5000) * (279 / 5000))
      hrU hq13dvU (by norm_num) (mul_nonneg (by linarith) (by linarith))
  have hrnh13dvU : r * ((-h13) * dv) ≤
      (57183 / 1000000 : ℝ) * ((11 / 1000) * (279 / 5000)) :=
    nonnegative_product_upper r ((-h13) * dv)
      (57183 / 1000000) ((11 / 1000) * (279 / 5000))
      hrU hnh13dvU (by norm_num) (mul_nonneg (by linarith) (by linarith))
  have hrq33duL :
      (49817 / 1000000 : ℝ) * ((663 / 2000) * (1687 / 100000)) ≤
        r * (q33 * du) :=
    nonnegative_product_lower r (q33 * du)
      (49817 / 1000000) ((663 / 2000) * (1687 / 100000))
      hrL hq33duL (by norm_num) (mul_nonneg (by linarith) (by linarith))
  have hrnh33duL :
      (49817 / 1000000 : ℝ) * ((117 / 1000) * (1687 / 100000)) ≤
        r * ((-h33) * du) :=
    nonnegative_product_lower r ((-h33) * du)
      (49817 / 1000000) ((117 / 1000) * (1687 / 100000))
      hrL hnh33duL (by norm_num) (mul_nonneg (by linarith) (by linarith))
  have hrq33L : (49817 / 1000000 : ℝ) * (663 / 2000) ≤ r * q33 :=
    nonnegative_product_lower r q33 (49817 / 1000000) (663 / 2000)
      hrL hq33L (by norm_num) (by linarith)
  have hrnh33L : (49817 / 1000000 : ℝ) * (117 / 1000) ≤ r * (-h33) :=
    nonnegative_product_lower r (-h33) (49817 / 1000000) (117 / 1000)
      hrL hnh33L (by norm_num) (by linarith)
  have haSlope : 0 ≤ alternatingDuCouplingSlopeA
      u4 dv v4 q13 q33 h13 h33 du := by
    unfold alternatingDuCouplingSlopeA
    nlinarith only [hunh33L, hnvnh13L, hq13dvL, hnh33duL, hnh33L,
      huq33U, hnvq13U, hq33duU, hnh13dvU, hq33U]
  have hxSlope : alternatingDuCouplingSlopeX
      r u4 sv v4 q13 q33 h13 h33 ≤ 0 := by
    unfold alternatingDuCouplingSlopeX
    nlinarith only [hruq33U, hrunh33U, hrnvq13U, hrnvnh13U,
      huq33L, hunh33U, hnvq13L, hnvnh13U, hq13svL, hnh13svU,
      hq33U, hnh33L]
  have hrSlope : alternatingDuCouplingSlopeR
      r u4 sv dv v4 q13 q33 h13 h33 du ≤ 0 := by
    unfold alternatingDuCouplingSlopeR
    nlinarith only [hrq13dvU, hrnh13dvU, hunh33U, hnvnh13U,
      hq33duU, hnh13dvU, hnh13svU, hq33U, hrq33duL,
      hrnh33duL, hrq33L, hrnh33L, huq33L, hnvq13L,
      hq13dvL, hq13svL, hnh33duL, hnh33L]
  have huSlope : alternatingDuCouplingSlopeU q33 h33 ≤ 0 := by
    unfold alternatingDuCouplingSlopeU
    bound
  have hvSlope : 0 ≤ alternatingDuCouplingSlopeV q13 h13 := by
    unfold alternatingDuCouplingSlopeV
    nlinarith only [hq13L, hh13L]
  have hq13Slope : 0 ≤ alternatingDuCouplingSlopeQ13 dv sv := by
    unfold alternatingDuCouplingSlopeQ13
    bound
  have hq33Slope : alternatingDuCouplingSlopeQ33 du ≤ 0 := by
    unfold alternatingDuCouplingSlopeQ33
    bound
  have hh13Slope : 0 ≤ alternatingDuCouplingSlopeH13 dv sv := by
    unfold alternatingDuCouplingSlopeH13
    bound
  have hh33Slope : alternatingDuCouplingSlopeH33 du ≤ 0 := by
    unfold alternatingDuCouplingSlopeH33
    bound
  have hdvSlope : 0 ≤ alternatingDuCouplingSlopeDv := by
    norm_num [alternatingDuCouplingSlopeDv]
  have hsvSlope : alternatingDuCouplingSlopeSv ≤ 0 := by
    norm_num [alternatingDuCouplingSlopeSv]
  have hduSlope : alternatingDuCouplingSlopeDu ≤ 0 := by
    norm_num [alternatingDuCouplingSlopeDu]
  have haStep := mul_nonneg
    (by linarith : 0 ≤ a - 824479 / 1000000) haSlope
  have hxStep := mul_nonneg_of_nonpos_of_nonpos
    (by linarith : x - 39761 / 1000000 ≤ 0) hxSlope
  have hrStep := mul_nonneg_of_nonpos_of_nonpos
    (by linarith : r - 57183 / 1000000 ≤ 0) hrSlope
  have huStep := mul_nonneg_of_nonpos_of_nonpos
    (by linarith : u4 - 18 / 125 ≤ 0) huSlope
  have hvStep := mul_nonneg
    (by linarith : 0 ≤ v4 - (-(1 / 250))) hvSlope
  have hq13Step := mul_nonneg
    (by linarith : 0 ≤ q13 - 1 / 5) hq13Slope
  have hq33Step := mul_nonneg_of_nonpos_of_nonpos
    (by linarith : q33 - 333 / 1000 ≤ 0) hq33Slope
  have hh13Step := mul_nonneg
    (by linarith : 0 ≤ h13 - (-(11 / 1000))) hh13Slope
  have hh33Step := mul_nonneg_of_nonpos_of_nonpos
    (by linarith : h33 - (-(117 / 1000)) ≤ 0) hh33Slope
  have hdvStep := mul_nonneg
    (by linarith : 0 ≤ dv - 111 / 2000) hdvSlope
  have hsvStep := mul_nonneg_of_nonpos_of_nonpos
    (by linarith : sv - 13459 / 25000 ≤ 0) hsvSlope
  have hduStep := mul_nonneg_of_nonpos_of_nonpos
    (by linarith : du - 423 / 25000 ≤ 0) hduSlope
  have htel := alternatingDuCoupling_telescope
    a x r u4 sv dv v4 q13 q33 h13 h33 du
  have hcorner : (11 / 10000 : ℝ) ≤ alternatingDuCoupling
      (824479 / 1000000) (39761 / 1000000) (57183 / 1000000)
      (18 / 125) (13459 / 25000) (111 / 2000) (-(1 / 250))
      (1 / 5) (333 / 1000) (-(11 / 1000)) (-(117 / 1000))
      (423 / 25000) cornerDu := by
    norm_num [alternatingDuCoupling, alternatingAdjugateRowD,
      alternatingMixedAdjugateRowD, cornerA, cornerX, cornerR, cornerD,
      cornerF, corner_d, corner_f, cornerSu, cornerDu]
  nlinarith only [htel, hcorner, haStep, hxStep, hrStep, huStep,
    hvStep, hq13Step, hq33Step, hh13Step, hh33Step, hdvStep, hsvStep,
    hduStep]

set_option maxHeartbeats 1000000 in
theorem alternatingDuCross_lower
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (-10 / 10000 : ℝ) ≤ alternatingDuCross a x r u4 sv dv v4 du cornerDu := by
  rcases hbox.a_mem with ⟨haL, haU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  rcases hbox.sv_mem with ⟨hsvL, hsvU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  rcases hbox.v4_mem with ⟨hv4L, hv4U⟩
  rcases hbox.du_mem with ⟨hduL, hduU⟩
  norm_num at haL haU hxL hxU hrL hrU hu4L hu4U hsvL hsvU
  norm_num at hdvL hdvU hv4L hv4U hduL hduU
  let Am := cornerA + a
  let Xm := cornerX + x
  let Rm := cornerR + r
  let Dm := cornerD + corner_d
  let Fm := cornerF + corner_f
  let dubar := (du + cornerDu) / 2
  let zs := u4 * dv - v4 * dubar
  let zd := v4 * cornerSu - u4 * sv
  let z4 := (dubar * sv - cornerSu * dv) / 2
  have hnvL : (1 / 500 : ℝ) ≤ -v4 := by linarith
  have hnvU : -v4 ≤ (1 / 250 : ℝ) := by linarith
  have hdubarL : (1687 / 100000 : ℝ) ≤ dubar := by
    dsimp [dubar, cornerDu]
    linarith
  have hdubarU : dubar ≤ (3379 / 200000 : ℝ) := by
    dsimp [dubar, cornerDu]
    linarith
  have hAmL : (2198709 / 1000000 : ℝ) ≤ Am := by
    dsimp [Am, cornerA]
    linarith
  have hXmU : Xm ≤ (79531 / 1000000 : ℝ) := by
    dsimp [Xm, cornerX]
    linarith
  have hXm0 : 0 ≤ Xm := by
    dsimp [Xm, cornerX]
    linarith
  have hRmL : (58543 / 200000 : ℝ) ≤ Rm := by
    dsimp [Rm, cornerR]
    linarith
  have hRmU : Rm ≤ (300081 / 1000000 : ℝ) := by
    dsimp [Rm, cornerR]
    linarith
  have hDmL : (13243 / 200000 : ℝ) ≤ Dm := by
    norm_num [Dm, cornerD, corner_d]
  have hFmU : Fm ≤ (12271 / 25000 : ℝ) := by
    norm_num [Fm, cornerF, corner_f]
  have hu4dvL : (141 / 1000 : ℝ) * (111 / 2000) ≤ u4 * dv :=
    nonnegative_product_lower u4 dv (141 / 1000) (111 / 2000)
      hu4L hdvL (by norm_num) (by linarith)
  have hu4dvU : u4 * dv ≤ (18 / 125 : ℝ) * (279 / 5000) :=
    nonnegative_product_upper u4 dv (18 / 125) (279 / 5000)
      hu4U hdvU (by norm_num) (by linarith)
  have hnvdbL : (1 / 500 : ℝ) * (1687 / 100000) ≤ (-v4) * dubar :=
    nonnegative_product_lower (-v4) dubar (1 / 500) (1687 / 100000)
      hnvL hdubarL (by norm_num) (by linarith)
  have hnvdbU : (-v4) * dubar ≤ (1 / 250 : ℝ) * (3379 / 200000) :=
    nonnegative_product_upper (-v4) dubar (1 / 250) (3379 / 200000)
      hnvU hdubarU (by norm_num) (by linarith)
  have hzsL : (196481 / 25000000 : ℝ) ≤ zs := by
    dsimp [zs]
    nlinarith only [hu4dvL, hnvdbL]
  have hzsU : zs ≤ (405139 / 50000000 : ℝ) := by
    dsimp [zs]
    nlinarith only [hu4dvU, hnvdbU]
  have hnvSuL : (1 / 500 : ℝ) * (56173 / 100000) ≤
      (-v4) * cornerSu := by
    dsimp [cornerSu]
    nlinarith only [hnvL]
  have hnvSuU : (-v4) * cornerSu ≤
      (1 / 250 : ℝ) * (56173 / 100000) := by
    dsimp [cornerSu]
    nlinarith only [hnvU]
  have hu4svL : (141 / 1000 : ℝ) * (10763 / 20000) ≤ u4 * sv :=
    nonnegative_product_lower u4 sv (141 / 1000) (10763 / 20000)
      hu4L hsvL (by norm_num) (by linarith)
  have hu4svU : u4 * sv ≤ (18 / 125 : ℝ) * (13459 / 25000) :=
    nonnegative_product_upper u4 sv (18 / 125) (13459 / 25000)
      hu4U hsvU (by norm_num) (by linarith)
  have hzdL : (-1994269 / 25000000 : ℝ) ≤ zd := by
    dsimp [zd]
    nlinarith only [hnvSuU, hu4svU]
  have hzdU : zd ≤ (-7700261 / 100000000 : ℝ) := by
    dsimp [zd]
    nlinarith only [hnvSuL, hu4svL]
  have hdubarsvL :
      (1687 / 100000 : ℝ) * (10763 / 20000) ≤ dubar * sv :=
    nonnegative_product_lower dubar sv (1687 / 100000) (10763 / 20000)
      hdubarL hsvL (by norm_num) (by linarith)
  have hdubarsvU : dubar * sv ≤
      (3379 / 200000 : ℝ) * (13459 / 25000) :=
    nonnegative_product_upper dubar sv (3379 / 200000) (13459 / 25000)
      hdubarU hsvU (by norm_num) (by linarith)
  have hSudvL : (56173 / 100000 : ℝ) * (111 / 2000) ≤ cornerSu * dv := by
    dsimp [cornerSu]
    nlinarith only [hdvL]
  have hSudvU : cornerSu * dv ≤ (56173 / 100000 : ℝ) * (279 / 5000) := by
    dsimp [cornerSu]
    nlinarith only [hdvU]
  have hz4L : (-44531887 / 4000000000 : ℝ) ≤ z4 := by
    dsimp [z4]
    nlinarith only [hdubarsvL, hSudvU]
  have hz4U : z4 ≤ (-55201057 / 5000000000 : ℝ) := by
    dsimp [z4]
    nlinarith only [hdubarsvU, hSudvL]
  have hAmzs :
      (2198709 / 1000000 : ℝ) * (196481 / 25000000) ≤ Am * zs :=
    nonnegative_product_lower Am zs
      (2198709 / 1000000) (196481 / 25000000)
      hAmL hzsL (by norm_num) (by linarith)
  have hXmzd :
      (79531 / 1000000 : ℝ) * (-1994269 / 25000000) ≤ Xm * zd :=
    positive_negative_product_lower Xm zd
      (79531 / 1000000) (-1994269 / 25000000)
      hXm0 hzdL (by norm_num) hXmU
  have hRmz4 :
      (300081 / 1000000 : ℝ) * (-44531887 / 4000000000) ≤ Rm * z4 :=
    positive_negative_product_lower Rm z4
      (300081 / 1000000) (-44531887 / 4000000000)
      (by linarith) hz4L (by norm_num) hRmU
  have hgS : (8508693632353 / 4000000000000000 : ℝ) ≤
      alternatingCrossGradientS Am Xm Rm zs zd z4 := by
    unfold alternatingCrossGradientS
    nlinarith only [hAmzs, hXmzd, hRmz4]
  have hRmzs :
      (58543 / 200000 : ℝ) * (196481 / 25000000) ≤ Rm * zs :=
    nonnegative_product_lower Rm zs
      (58543 / 200000) (196481 / 25000000)
      hRmL hzsL (by norm_num) (by linarith)
  have hDmzd :
      (13243 / 200000 : ℝ) * (7700261 / 100000000) ≤ -Dm * zd := by
    have hprod := nonnegative_product_lower Dm (-zd)
      (13243 / 200000) (7700261 / 100000000)
      hDmL (by linarith : (7700261 / 100000000 : ℝ) ≤ -zd)
      (by norm_num) (by linarith : 0 ≤ -zd)
    nlinarith only [hprod]
  have hFmz4 :
      (12271 / 25000 : ℝ) * (-44531887 / 4000000000) ≤ Fm * z4 :=
    positive_negative_product_lower Fm z4
      (12271 / 25000) (-44531887 / 4000000000)
      (by norm_num [Fm, cornerF, corner_f]) hz4L (by norm_num) hFmU
  have hg4 : (-36 / 10000 : ℝ) ≤
      alternatingCrossGradientFour Rm Dm Fm zs zd z4 := by
    unfold alternatingCrossGradientFour
    nlinarith only [hRmzs, hDmzd, hFmz4]
  have hfirst : 0 ≤
      (-v4) * alternatingCrossGradientS Am Xm Rm zs zd z4 :=
    mul_nonneg (by linarith) (by nlinarith only [hgS])
  have hsecond :
      ((13459 / 25000 : ℝ) / 2) * (-36 / 10000) ≤
        (sv / 2) * alternatingCrossGradientFour Rm Dm Fm zs zd z4 :=
    positive_negative_product_lower (sv / 2)
      (alternatingCrossGradientFour Rm Dm Fm zs zd z4)
      ((13459 / 25000) / 2) (-36 / 10000)
      (by linarith) hg4 (by norm_num) (by linarith)
  change (-10 / 10000 : ℝ) ≤
    (-v4) * alternatingCrossGradientS Am Xm Rm zs zd z4 +
      (sv / 2) * alternatingCrossGradientFour Rm Dm Fm zs zd z4
  nlinarith only [hfirst, hsecond]

set_option maxHeartbeats 3000000 in
theorem correlated_alternating_unfix_du
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    alternatingFace a x r cornerSu cornerDu u4 sv dv v4
        q11 q13 q33 h11 h13 h33 ≤
      alternatingFace a x r cornerSu du u4 sv dv v4
        q11 q13 q33 h11 h13 h33 := by
  rcases hbox.du_mem with ⟨hduL, hduU⟩
  norm_num at hduL
  let g : ℝ → ℝ := fun z ↦
    alternatingFace a x r cornerSu z u4 sv dv v4
      q11 q13 q33 h11 h13 h33
  have hcoupling := alternatingDuCoupling_lower
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hcross := alternatingDuCross_lower
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hsecCap : (1 / 10000 : ℝ) ≤ quadraticSecant g du cornerDu := by
    rw [show quadraticSecant g du cornerDu =
        alternatingDuSlope a x r u4 sv dv v4 q13 q33 h13 h33 du cornerDu by
      simpa only [g] using alternating_du_secant_eq
        a x r u4 sv dv v4 q11 q13 q33 h11 h13 h33 du cornerDu]
    unfold alternatingDuSlope
    nlinarith only [hcoupling, hcross]
  have hsec : 0 ≤ quadraticSecant g du cornerDu :=
    le_trans (by norm_num) hsecCap
  have hid : g du - g cornerDu =
      (du - cornerDu) * quadraticSecant g du cornerDu := by
    unfold g alternatingFace quadraticSecant correlatedCoefficientThree
      alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
      alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00 alignedEntry02
      alignedEntry04 alignedEntry22 alignedEntry24 mixedDeterminantOne
    dsimp only
    ring
  exact quadraticSecant_lower_endpoint g du cornerDu
    (by norm_num [cornerDu] at ⊢; exact hduL) hsec hid

def alternatingSuCoupling
    (x r u4 sv dv v4 q13 q33 h13 h33 su su0 du : ℝ) : ℝ :=
  let Xp := cornerX - x
  let Rp := cornerR - r
  let Cp := cornerC - corner_c
  let Dp := cornerD - corner_d
  let Fp := cornerF - corner_f
  let Xm := cornerX + x
  let Rm := cornerR + r
  let Cm := cornerC + corner_c
  let Dm := cornerD + corner_d
  let Fm := cornerF + corner_f
  let o13m := q13 - h13
  let o33m := q33 - h33
  let o13p := q13 + h13
  let o33p := q33 + h33
  let subar := (su + su0) / 2
  let wmS := o33m * subar - o13m * sv
  let wmD := o33m * du - o13m * dv
  let wm4 := o33m * u4 - o13m * v4
  let wpS := o33p * subar - o13p * sv
  let wpD := o33p * du - o13p * dv
  let wp4 := o33p * u4 - o13p * v4
  (-2 : ℝ) * (alternatingAdjugateRowS Xm Rm Cm Dm Fm wpS wpD wp4 +
    alternatingMixedAdjugateRowS Xp Rp Cp Dp Fp
      Xm Rm Cm Dm Fm wmS wmD wm4)

def alternatingSuCross
    (x r u4 sv dv v4 su su0 du : ℝ) : ℝ :=
  let Xm := cornerX + x
  let Rm := cornerR + r
  let Cm := cornerC + corner_c
  let Dm := cornerD + corner_d
  let Fm := cornerF + corner_f
  let subar := (su + su0) / 2
  let zs := u4 * dv - v4 * du
  let zd := v4 * subar - u4 * sv
  let z4 := (du * sv - subar * dv) / 2
  (v4 * alternatingCrossGradientD Xm Cm Dm zs zd z4) -
    ((dv / 2) * alternatingCrossGradientFour Rm Dm Fm zs zd z4)

def alternatingSuSlope
    (x r u4 sv dv v4 q13 q33 h13 h33 su su0 du : ℝ) : ℝ :=
  alternatingSuCoupling x r u4 sv dv v4 q13 q33 h13 h33 su su0 du +
    alternatingSuCross x r u4 sv dv v4 su su0 du

set_option maxHeartbeats 3000000 in
theorem alternating_su_secant_eq
    (a x r u4 sv dv v4 q11 q13 q33 h11 h13 h33 su su0 du : ℝ) :
    quadraticSecant
        (fun z ↦ alternatingFace a x r z du u4 sv dv v4
          q11 q13 q33 h11 h13 h33)
        su su0 =
      alternatingSuSlope x r u4 sv dv v4 q13 q33 h13 h33 su su0 du := by
  unfold quadraticSecant alternatingFace alternatingSuSlope
    alternatingSuCoupling alternatingSuCross alternatingAdjugateRowS
    alternatingMixedAdjugateRowS alternatingCrossGradientD
    alternatingCrossGradientFour correlatedCoefficientThree
    alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
    alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00 alignedEntry02
    alignedEntry04 alignedEntry22 alignedEntry24 mixedDeterminantOne
  dsimp only
  ring

set_option maxHeartbeats 3000000 in
def alternatingSuCouplingSlopeDu
    (x r q33 h33 : ℝ) : ℝ :=
  (56424500000 * h33 * r + 422060000000 * h33 * x -
      5113473469 * h33 + 9790500000 * q33 * r +
      68780000000 * q33 * x + 40717671339 * q33) /
    1000000000000

def alternatingSuCouplingSlopeSv (q13 h13 : ℝ) : ℝ :=
  3 * (162459107 * h13 + 587708303 * q13) /
    (4 * 100000000000)

def alternatingSuCouplingSlopeDv
    (x r q13 h13 : ℝ) : ℝ :=
  -(56424500000 * h13 * r + 422060000000 * h13 * x -
      5113473469 * h13 + 9790500000 * q13 * r +
      68780000000 * q13 * x + 40717671339 * q13) /
    1000000000000

def alternatingSuCouplingSlopeX
    (u4 v4 q13 q33 h13 h33 : ℝ) : ℝ :=
  -(141061250 * h13 * v4 + 58560825 * h13 -
      141061250 * h33 * u4 - 17853138 * h33 +
      24476250 * q13 * v4 + 9543225 * q13 -
      24476250 * q33 * u4 - 2909394 * q33) /
    2500000000

def alternatingSuCouplingSlopeR
    (u4 v4 q13 q33 h13 h33 : ℝ) : ℝ :=
  -(1736250000 * h13 * v4 + 313155975 * h13 -
      1736250000 * h33 * u4 - 95470254 * h33 +
      303250000 * q13 * v4 + 54337275 * q13 -
      303250000 * q33 * u4 - 16565526 * q33) /
    100000000000

def alternatingSuCouplingSlopeU4 (q33 h33 : ℝ) : ℝ :=
  3 * (312452507 * h33 + 1539146983 * q33) /
    (5 * 100000000000)

def alternatingSuCouplingSlopeV4 (q13 h13 : ℝ) : ℝ :=
  -(3 * (312452507 * h13 + 1539146983 * q13)) /
    (5 * 100000000000)

def alternatingSuCouplingSlopeQ13 : ℝ :=
  -(429177215523 / (2 * 10000000000000000))

def alternatingSuCouplingSlopeQ33 (su : ℝ) : ℝ :=
  -(3 * (2350833212000 * su - 888605477821)) /
    (32 * 100000000000000)

def alternatingSuCouplingSlopeH13 : ℝ :=
  -(1907629057287 / (2 * 10000000000000000))

def alternatingSuCouplingSlopeH33 (su : ℝ) : ℝ :=
  -(3 * (16245910700000 * su - 4242266234833)) /
    (8 * 10000000000000000)

def alternatingSuCouplingSlopeSu : ℝ :=
  -(1051981257627 / (16 * 100000000000000))

set_option maxHeartbeats 3000000 in
theorem alternatingSuCoupling_telescope
    (x r u4 sv dv v4 q13 q33 h13 h33 su du : ℝ) :
    alternatingSuCoupling x r u4 sv dv v4 q13 q33 h13 h33
          su cornerSu du -
        alternatingSuCoupling
          (37851 / 1000000) (49817 / 1000000) (18 / 125)
          (13459 / 25000) (111 / 2000) (-(1 / 250))
          (1 / 5) (663 / 2000) (-(11 / 1000)) (-(3 / 25))
          (7021 / 12500) cornerSu (423 / 25000) =
      (du - 423 / 25000) *
          alternatingSuCouplingSlopeDu x r q33 h33 +
        (sv - 13459 / 25000) *
          alternatingSuCouplingSlopeSv q13 h13 +
        (dv - 111 / 2000) *
          alternatingSuCouplingSlopeDv x r q13 h13 +
        (x - 37851 / 1000000) *
          alternatingSuCouplingSlopeX u4 v4 q13 q33 h13 h33 +
        (r - 49817 / 1000000) *
          alternatingSuCouplingSlopeR u4 v4 q13 q33 h13 h33 +
        (u4 - 18 / 125) * alternatingSuCouplingSlopeU4 q33 h33 +
        (v4 - (-(1 / 250))) * alternatingSuCouplingSlopeV4 q13 h13 +
        (q13 - 1 / 5) * alternatingSuCouplingSlopeQ13 +
        (q33 - 663 / 2000) * alternatingSuCouplingSlopeQ33 su +
        (h13 - (-(11 / 1000))) * alternatingSuCouplingSlopeH13 +
        (h33 - (-(3 / 25))) * alternatingSuCouplingSlopeH33 su +
        (su - 7021 / 12500) * alternatingSuCouplingSlopeSu := by
  unfold alternatingSuCoupling alternatingAdjugateRowS
    alternatingMixedAdjugateRowS alternatingSuCouplingSlopeDu
    alternatingSuCouplingSlopeSv alternatingSuCouplingSlopeDv
    alternatingSuCouplingSlopeX alternatingSuCouplingSlopeR
    alternatingSuCouplingSlopeU4 alternatingSuCouplingSlopeV4
    alternatingSuCouplingSlopeQ13 alternatingSuCouplingSlopeQ33
    alternatingSuCouplingSlopeH13 alternatingSuCouplingSlopeH33
    alternatingSuCouplingSlopeSu
  dsimp only
  ring

set_option maxHeartbeats 3000000 in
theorem alternatingSuCoupling_upper
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    alternatingSuCoupling x r u4 sv dv v4 q13 q33 h13 h33
        su cornerSu du ≤ (-11 / 100000 : ℝ) := by
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.su_mem with ⟨hsuL, hsuU⟩
  rcases hbox.du_mem with ⟨hduL, hduU⟩
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  rcases hbox.sv_mem with ⟨hsvL, hsvU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  rcases hbox.v4_mem with ⟨hv4L, hv4U⟩
  rcases hbox.q13_mem with ⟨hq13L, hq13U⟩
  rcases hbox.q33_mem with ⟨hq33L, hq33U⟩
  rcases hbox.h13_mem with ⟨hh13L, hh13U⟩
  rcases hbox.h33_mem with ⟨hh33L, hh33U⟩
  norm_num at hxL hxU hrL hrU hsuL hsuU hduL hduU hu4L hu4U
  norm_num at hsvL hsvU hdvL hdvU hv4L hv4U hq13L hq13U
  norm_num at hq33L hq33U hh13L hh13U hh33L hh33U
  have hnv4L : (1 / 500 : ℝ) ≤ -v4 := by linarith
  have hnv4U : -v4 ≤ (1 / 250 : ℝ) := by linarith
  have hnh13L : (9 / 1000 : ℝ) ≤ -h13 := by linarith
  have hnh13U : -h13 ≤ (11 / 1000 : ℝ) := by linarith
  have hnh33L : (117 / 1000 : ℝ) ≤ -h33 := by linarith
  have hnh33U : -h33 ≤ (3 / 25 : ℝ) := by linarith
  have hnh33rU : (-h33) * r ≤
      (3 / 25 : ℝ) * (57183 / 1000000) :=
    nonnegative_product_upper (-h33) r (3 / 25) (57183 / 1000000)
      hnh33U hrU (by norm_num) (by linarith)
  have hnh33xU : (-h33) * x ≤
      (3 / 25 : ℝ) * (39761 / 1000000) :=
    nonnegative_product_upper (-h33) x (3 / 25) (39761 / 1000000)
      hnh33U hxU (by norm_num) (by linarith)
  have hq33rL : (663 / 2000 : ℝ) * (49817 / 1000000) ≤ q33 * r :=
    nonnegative_product_lower q33 r (663 / 2000) (49817 / 1000000)
      hq33L hrL (by norm_num) (by linarith)
  have hq33xL : (663 / 2000 : ℝ) * (37851 / 1000000) ≤ q33 * x :=
    nonnegative_product_lower q33 x (663 / 2000) (37851 / 1000000)
      hq33L hxL (by norm_num) (by linarith)
  have hnh13rU : (-h13) * r ≤
      (11 / 1000 : ℝ) * (57183 / 1000000) :=
    nonnegative_product_upper (-h13) r (11 / 1000) (57183 / 1000000)
      hnh13U hrU (by norm_num) (by linarith)
  have hnh13xU : (-h13) * x ≤
      (11 / 1000 : ℝ) * (39761 / 1000000) :=
    nonnegative_product_upper (-h13) x (11 / 1000) (39761 / 1000000)
      hnh13U hxU (by norm_num) (by linarith)
  have hq13rL : (1 / 5 : ℝ) * (49817 / 1000000) ≤ q13 * r :=
    nonnegative_product_lower q13 r (1 / 5) (49817 / 1000000)
      hq13L hrL (by norm_num) (by linarith)
  have hq13xL : (1 / 5 : ℝ) * (37851 / 1000000) ≤ q13 * x :=
    nonnegative_product_lower q13 x (1 / 5) (37851 / 1000000)
      hq13L hxL (by norm_num) (by linarith)
  have hnh13nv4L : (9 / 1000 : ℝ) * (1 / 500) ≤ (-h13) * (-v4) :=
    nonnegative_product_lower (-h13) (-v4) (9 / 1000) (1 / 500)
      hnh13L hnv4L (by norm_num) (by linarith)
  have hnh33u4L : (117 / 1000 : ℝ) * (141 / 1000) ≤ (-h33) * u4 :=
    nonnegative_product_lower (-h33) u4 (117 / 1000) (141 / 1000)
      hnh33L hu4L (by norm_num) (by linarith)
  have hq13nv4U : q13 * (-v4) ≤ (1001 / 5000 : ℝ) * (1 / 250) :=
    nonnegative_product_upper q13 (-v4) (1001 / 5000) (1 / 250)
      hq13U hnv4U (by norm_num) (by linarith)
  have hq33u4U : q33 * u4 ≤ (333 / 1000 : ℝ) * (18 / 125) :=
    nonnegative_product_upper q33 u4 (333 / 1000) (18 / 125)
      hq33U hu4U (by norm_num) (by linarith)
  have hduSlope : (12 / 1000 : ℝ) ≤
      alternatingSuCouplingSlopeDu x r q33 h33 := by
    unfold alternatingSuCouplingSlopeDu
    nlinarith only [hnh33rU, hnh33xU, hq33rL, hq33xL,
      hnh33L, hq33L]
  have hsvSlope : (8 / 10000 : ℝ) ≤
      alternatingSuCouplingSlopeSv q13 h13 := by
    unfold alternatingSuCouplingSlopeSv
    nlinarith only [hh13L, hq13L]
  have hdvSlope : alternatingSuCouplingSlopeDv x r q13 h13 ≤
      (-8 / 1000 : ℝ) := by
    unfold alternatingSuCouplingSlopeDv
    nlinarith only [hnh13rU, hnh13xU, hq13rL, hq13xL,
      hnh13L, hq13L]
  have hxSlope : alternatingSuCouplingSlopeX u4 v4 q13 q33 h13 h33 ≤
      (-14 / 10000 : ℝ) := by
    unfold alternatingSuCouplingSlopeX
    nlinarith only [hnh13nv4L, hh13L, hnh33u4L, hnh33L,
      hq13nv4U, hq13L, hq33u4U, hq33U]
  have hrSlope : alternatingSuCouplingSlopeR u4 v4 q13 q33 h13 h33 ≤
      (-26 / 100000 : ℝ) := by
    unfold alternatingSuCouplingSlopeR
    nlinarith only [hnh13nv4L, hh13L, hnh33u4L, hnh33L,
      hq13nv4U, hq13L, hq33u4U, hq33U]
  have hu4Slope : (28 / 10000 : ℝ) ≤
      alternatingSuCouplingSlopeU4 q33 h33 := by
    unfold alternatingSuCouplingSlopeU4
    nlinarith only [hh33L, hq33L]
  have hv4Slope : alternatingSuCouplingSlopeV4 q13 h13 ≤
      (-18 / 10000 : ℝ) := by
    unfold alternatingSuCouplingSlopeV4
    nlinarith only [hh13L, hq13L]
  have hq13Slope : alternatingSuCouplingSlopeQ13 ≤
      (-2 / 100000 : ℝ) := by
    norm_num [alternatingSuCouplingSlopeQ13]
  have hq33Slope : alternatingSuCouplingSlopeQ33 su ≤
      (-40 / 100000 : ℝ) := by
    unfold alternatingSuCouplingSlopeQ33
    nlinarith only [hsuL]
  have hh13Slope : alternatingSuCouplingSlopeH13 ≤
      (-9 / 100000 : ℝ) := by
    norm_num [alternatingSuCouplingSlopeH13]
  have hh33Slope : alternatingSuCouplingSlopeH33 su ≤
      (-18 / 100000 : ℝ) := by
    unfold alternatingSuCouplingSlopeH33
    nlinarith only [hsuL]
  have hsuSlope : alternatingSuCouplingSlopeSu ≤
      (-6 / 10000 : ℝ) := by
    norm_num [alternatingSuCouplingSlopeSu]
  have hduStep := mul_nonpos_of_nonpos_of_nonneg
    (by linarith : du - 423 / 25000 ≤ 0) (by linarith : 0 ≤
      alternatingSuCouplingSlopeDu x r q33 h33)
  have hsvStep := mul_nonpos_of_nonpos_of_nonneg
    (by linarith : sv - 13459 / 25000 ≤ 0) (by linarith : 0 ≤
      alternatingSuCouplingSlopeSv q13 h13)
  have hdvStep := mul_nonpos_of_nonneg_of_nonpos
    (by linarith : 0 ≤ dv - 111 / 2000) (by linarith :
      alternatingSuCouplingSlopeDv x r q13 h13 ≤ 0)
  have hxStep := mul_nonpos_of_nonneg_of_nonpos
    (by linarith : 0 ≤ x - 37851 / 1000000) (by linarith :
      alternatingSuCouplingSlopeX u4 v4 q13 q33 h13 h33 ≤ 0)
  have hrStep := mul_nonpos_of_nonneg_of_nonpos
    (by linarith : 0 ≤ r - 49817 / 1000000) (by linarith :
      alternatingSuCouplingSlopeR u4 v4 q13 q33 h13 h33 ≤ 0)
  have hu4Step := mul_nonpos_of_nonpos_of_nonneg
    (by linarith : u4 - 18 / 125 ≤ 0) (by linarith : 0 ≤
      alternatingSuCouplingSlopeU4 q33 h33)
  have hv4Step := mul_nonpos_of_nonneg_of_nonpos
    (by linarith : 0 ≤ v4 - (-(1 / 250))) (by linarith :
      alternatingSuCouplingSlopeV4 q13 h13 ≤ 0)
  have hq13Step := mul_nonpos_of_nonneg_of_nonpos
    (by linarith : 0 ≤ q13 - 1 / 5) (by linarith :
      alternatingSuCouplingSlopeQ13 ≤ 0)
  have hq33Step := mul_nonpos_of_nonneg_of_nonpos
    (by linarith : 0 ≤ q33 - 663 / 2000) (by linarith :
      alternatingSuCouplingSlopeQ33 su ≤ 0)
  have hh13Step := mul_nonpos_of_nonneg_of_nonpos
    (by linarith : 0 ≤ h13 - (-(11 / 1000))) (by linarith :
      alternatingSuCouplingSlopeH13 ≤ 0)
  have hh33Step := mul_nonpos_of_nonneg_of_nonpos
    (by linarith : 0 ≤ h33 - (-(3 / 25))) (by linarith :
      alternatingSuCouplingSlopeH33 su ≤ 0)
  have hsuStep := mul_nonpos_of_nonneg_of_nonpos
    (by linarith : 0 ≤ su - 7021 / 12500) (by linarith :
      alternatingSuCouplingSlopeSu ≤ 0)
  have htel := alternatingSuCoupling_telescope
    x r u4 sv dv v4 q13 q33 h13 h33 su du
  have hcorner : alternatingSuCoupling
      (37851 / 1000000) (49817 / 1000000) (18 / 125)
      (13459 / 25000) (111 / 2000) (-(1 / 250))
      (1 / 5) (663 / 2000) (-(11 / 1000)) (-(3 / 25))
      (7021 / 12500) cornerSu (423 / 25000) <
        (-11 / 100000 : ℝ) := by
    norm_num [alternatingSuCoupling, alternatingAdjugateRowS,
      alternatingMixedAdjugateRowS, cornerX, cornerR, cornerC, cornerD,
      cornerF, corner_c, corner_d, corner_f, cornerSu]
  nlinarith only [htel, hcorner, hduStep, hsvStep, hdvStep, hxStep,
    hrStep, hu4Step, hv4Step, hq13Step, hq33Step, hh13Step,
    hh33Step, hsuStep]

set_option maxHeartbeats 1000000 in
theorem alternatingSuCross_upper
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    alternatingSuCross x r u4 sv dv v4 su cornerSu du ≤
      (10 / 100000 : ℝ) := by
  have hxL := hbox.x_mem.1
  have hrL := hbox.r_mem.1
  rcases hbox.su_mem with ⟨hsuL, hsuU⟩
  rcases hbox.du_mem with ⟨hduL, hduU⟩
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  rcases hbox.sv_mem with ⟨hsvL, hsvU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  rcases hbox.v4_mem with ⟨hv4L, hv4U⟩
  norm_num at hxL hrL hsuL hsuU hduL hduU hu4L hu4U hsvL hsvU
  norm_num at hdvL hdvU hv4L hv4U
  let Xm := cornerX + x
  let Rm := cornerR + r
  let Cm := cornerC + corner_c
  let Dm := cornerD + corner_d
  let Fm := cornerF + corner_f
  let subar := (su + cornerSu) / 2
  let zs := u4 * dv - v4 * du
  let zd := v4 * subar - u4 * sv
  let z4 := (du * sv - subar * dv) / 2
  have hnv4L : (1 / 500 : ℝ) ≤ -v4 := by linarith
  have hnv4U : -v4 ≤ (1 / 250 : ℝ) := by linarith
  have hsubarL : (112341 / 200000 : ℝ) ≤ subar := by
    dsimp [subar, cornerSu]
    linarith
  have hsubarU : subar ≤ (56173 / 100000 : ℝ) := by
    dsimp [subar, cornerSu]
    linarith
  have hu4dvL : (141 / 1000 : ℝ) * (111 / 2000) ≤ u4 * dv :=
    nonnegative_product_lower u4 dv (141 / 1000) (111 / 2000)
      hu4L hdvL (by norm_num) (by linarith)
  have hu4dvU : u4 * dv ≤ (18 / 125 : ℝ) * (279 / 5000) :=
    nonnegative_product_upper u4 dv (18 / 125) (279 / 5000)
      hu4U hdvU (by norm_num) (by linarith)
  have hnv4duL : (1 / 500 : ℝ) * (1687 / 100000) ≤ (-v4) * du :=
    nonnegative_product_lower (-v4) du (1 / 500) (1687 / 100000)
      hnv4L hduL (by norm_num) (by linarith)
  have hnv4duU : (-v4) * du ≤ (1 / 250 : ℝ) * (423 / 25000) :=
    nonnegative_product_upper (-v4) du (1 / 250) (423 / 25000)
      hnv4U hduU (by norm_num) (by linarith)
  have hzsL : (196481 / 25000000 : ℝ) ≤ zs := by
    dsimp [zs]
    nlinarith only [hu4dvL, hnv4duL]
  have hzsU : zs ≤ (50643 / 6250000 : ℝ) := by
    dsimp [zs]
    nlinarith only [hu4dvU, hnv4duU]
  have hnv4subarL : (1 / 500 : ℝ) * (112341 / 200000) ≤
      (-v4) * subar :=
    nonnegative_product_lower (-v4) subar (1 / 500) (112341 / 200000)
      hnv4L hsubarL (by norm_num) (by linarith)
  have hnv4subarU : (-v4) * subar ≤
      (1 / 250 : ℝ) * (56173 / 100000) :=
    nonnegative_product_upper (-v4) subar (1 / 250) (56173 / 100000)
      hnv4U hsubarU (by norm_num) (by linarith)
  have hu4svL : (141 / 1000 : ℝ) * (10763 / 20000) ≤ u4 * sv :=
    nonnegative_product_lower u4 sv (141 / 1000) (10763 / 20000)
      hu4L hsvL (by norm_num) (by linarith)
  have hu4svU : u4 * sv ≤ (18 / 125 : ℝ) * (13459 / 25000) :=
    nonnegative_product_upper u4 sv (18 / 125) (13459 / 25000)
      hu4U hsvU (by norm_num) (by linarith)
  have hzdL : (-1994269 / 25000000 : ℝ) ≤ zd := by
    dsimp [zd]
    nlinarith only [hnv4subarU, hu4svU]
  have hzdU : zd ≤ (-240633 / 3125000 : ℝ) := by
    dsimp [zd]
    nlinarith only [hnv4subarL, hu4svL]
  have hdusvL : (1687 / 100000 : ℝ) * (10763 / 20000) ≤ du * sv :=
    nonnegative_product_lower du sv (1687 / 100000) (10763 / 20000)
      hduL hsvL (by norm_num) (by linarith)
  have hdusvU : du * sv ≤ (423 / 25000 : ℝ) * (13459 / 25000) :=
    nonnegative_product_upper du sv (423 / 25000) (13459 / 25000)
      hduU hsvU (by norm_num) (by linarith)
  have hsubardvL : (112341 / 200000 : ℝ) * (111 / 2000) ≤ subar * dv :=
    nonnegative_product_lower subar dv (112341 / 200000) (111 / 2000)
      hsubarL hdvL (by norm_num) (by linarith)
  have hsubardvU : subar * dv ≤
      (56173 / 100000 : ℝ) * (279 / 5000) :=
    nonnegative_product_upper subar dv (56173 / 100000) (279 / 5000)
      hsubarU hdvU (by norm_num) (by linarith)
  have hz4L : (-44531887 / 4000000000 : ℝ) ≤ z4 := by
    dsimp [z4]
    nlinarith only [hdusvL, hsubardvU]
  have hz4U : z4 ≤ (-220655763 / 20000000000 : ℝ) := by
    dsimp [z4]
    nlinarith only [hdusvU, hsubardvL]
  have hXmL : (77621 / 1000000 : ℝ) ≤ Xm := by
    dsimp [Xm, cornerX]
    linarith
  have hRmL : (58543 / 200000 : ℝ) ≤ Rm := by
    dsimp [Rm, cornerR]
    linarith
  have hXmzs : (77621 / 1000000 : ℝ) * (196481 / 25000000) ≤ Xm * zs :=
    nonnegative_product_lower Xm zs (77621 / 1000000) (196481 / 25000000)
      hXmL hzsL (by norm_num) (by linarith)
  have hRmzs : (58543 / 200000 : ℝ) * (196481 / 25000000) ≤ Rm * zs :=
    nonnegative_product_lower Rm zs (58543 / 200000) (196481 / 25000000)
      hRmL hzsL (by norm_num) (by linarith)
  have hGD : (888379105089 / 4000000000000000 : ℝ) ≤
      alternatingCrossGradientD Xm Cm Dm zs zd z4 := by
    unfold alternatingCrossGradientD
    dsimp [Cm, Dm, cornerC, cornerD, corner_c, corner_d]
    nlinarith only [hXmzs, hzdL, hz4U]
  have hG4 : (-176488688027 / 50000000000000 : ℝ) ≤
      alternatingCrossGradientFour Rm Dm Fm zs zd z4 := by
    unfold alternatingCrossGradientFour
    dsimp [Dm, Fm, cornerD, cornerF, corner_d, corner_f]
    nlinarith only [hRmzs, hzdU, hz4L]
  have hGD0 : 0 ≤ alternatingCrossGradientD Xm Cm Dm zs zd z4 := by
    exact le_trans (by norm_num) hGD
  have hG4cap : (-353 / 100000 : ℝ) <
      alternatingCrossGradientFour Rm Dm Fm zs zd z4 := by
    nlinarith only [hG4]
  have hfirst : v4 * alternatingCrossGradientD Xm Cm Dm zs zd z4 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hGD0
  have hnegG4 : -alternatingCrossGradientFour Rm Dm Fm zs zd z4 ≤
      (353 / 100000 : ℝ) := by
    linarith
  have hsecondVar := mul_le_mul_of_nonneg_left hnegG4
    (by linarith : 0 ≤ dv / 2)
  have hsecondEndpoint := mul_le_mul_of_nonneg_right
    (by linarith : dv / 2 ≤ (279 / 5000 : ℝ) / 2)
    (by norm_num : (0 : ℝ) ≤ 353 / 100000)
  have hsecond : -(dv / 2) *
        alternatingCrossGradientFour Rm Dm Fm zs zd z4 ≤
      ((279 / 5000 : ℝ) / 2) * (353 / 100000) := by
    nlinarith only [hsecondVar, hsecondEndpoint]
  have hcap : ((279 / 5000 : ℝ) / 2) * (353 / 100000) <
      10 / 100000 := by
    norm_num
  change v4 * alternatingCrossGradientD Xm Cm Dm zs zd z4 -
      (dv / 2) * alternatingCrossGradientFour Rm Dm Fm zs zd z4 ≤
    10 / 100000
  apply le_of_lt
  calc
    v4 * alternatingCrossGradientD Xm Cm Dm zs zd z4 -
          (dv / 2) * alternatingCrossGradientFour Rm Dm Fm zs zd z4 =
        v4 * alternatingCrossGradientD Xm Cm Dm zs zd z4 +
          (-(dv / 2)) *
            alternatingCrossGradientFour Rm Dm Fm zs zd z4 := by ring
    _ ≤ 0 + ((279 / 5000 : ℝ) / 2) * (353 / 100000) :=
      add_le_add hfirst hsecond
    _ < 0 + 10 / 100000 := by simpa only [zero_add] using hcap
    _ = 10 / 100000 := zero_add _

set_option maxHeartbeats 3000000 in
theorem correlated_alternating_unfix_su
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    alternatingFace a x r cornerSu du u4 sv dv v4
        q11 q13 q33 h11 h13 h33 ≤
      alternatingFace a x r su du u4 sv dv v4
        q11 q13 q33 h11 h13 h33 := by
  have hsuU := hbox.su_mem.2
  norm_num at hsuU
  let g : ℝ → ℝ := fun z ↦
    alternatingFace a x r z du u4 sv dv v4
      q11 q13 q33 h11 h13 h33
  have hcoupling := alternatingSuCoupling_upper
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hcross := alternatingSuCross_upper
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hsecCap : quadraticSecant g su cornerSu ≤ (-1 / 100000 : ℝ) := by
    rw [show quadraticSecant g su cornerSu =
        alternatingSuSlope x r u4 sv dv v4 q13 q33 h13 h33
          su cornerSu du by
      simpa only [g] using alternating_su_secant_eq
        a x r u4 sv dv v4 q11 q13 q33 h11 h13 h33 su cornerSu du]
    unfold alternatingSuSlope
    nlinarith only [hcoupling, hcross]
  have hsec : quadraticSecant g su cornerSu ≤ 0 :=
    le_trans hsecCap (by norm_num)
  have hid : g su - g cornerSu =
      (su - cornerSu) * quadraticSecant g su cornerSu := by
    unfold g alternatingFace quadraticSecant correlatedCoefficientThree
      alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
      alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00 alignedEntry02
      alignedEntry04 alignedEntry22 alignedEntry24 mixedDeterminantOne
    dsimp only
    ring
  exact quadraticSecant_upper_endpoint g su cornerSu
    (by norm_num [cornerSu] at ⊢; exact hsuU) hsec hid

/-! ## The even block

The perturbation-`f` secant splits into three determinant/odd-minor
pairings, two coupling derivatives, and the alternating cross square.
-/

def perturbFDetMinusSlope
    (A X C a x c : ℝ) : ℝ :=
  let Ap := A - a
  let Xp := X - x
  let Cp := C - c
  let Am := A + a
  let Xm := X + x
  let Cm := C + c
  (Ap * Cp - Xp ^ 2 -
    (Am * Cp + Ap * Cm - 2 * Xp * Xm)) / 4

def perturbFDetMixedSlope
    (A X C a x c : ℝ) : ℝ :=
  let Ap := A - a
  let Xp := X - x
  let Cp := C - c
  let Am := A + a
  let Xm := X + x
  let Cm := C + c
  (Ap * Cm + Am * Cp - 2 * Xm * Xp -
    (Am * Cm - Xm ^ 2)) / 4

def perturbFDetPlusSlope
    (A X C a x c : ℝ) : ℝ :=
  let Am := A + a
  let Xm := X + x
  let Cm := C + c
  (Am * Cm - Xm ^ 2) / 4

def perturbFOddMinor (o11 o13 o33 : ℝ) : ℝ :=
  o11 * o33 - o13 ^ 2

def perturbFOddMixed
    (o11p o13p o33p o11m o13m o33m : ℝ) : ℝ :=
  o11p * o33m + o11m * o33p - 2 * o13p * o13m

def perturbFOddS
    (su sv o11 o13 o33 : ℝ) : ℝ :=
  o33 * su ^ 2 - 2 * o13 * su * sv + o11 * sv ^ 2

def perturbFOddD
    (du dv o11 o13 o33 : ℝ) : ℝ :=
  o33 * du ^ 2 - 2 * o13 * du * dv + o11 * dv ^ 2

def perturbFOddSD
    (su du sv dv o11 o13 o33 : ℝ) : ℝ :=
  o33 * su * du - o13 * (su * dv + du * sv) + o11 * sv * dv

def perturbFSecant
    (a x su du sv dv q11 q13 q33 h11 h13 h33 : ℝ) : ℝ :=
  let o11p := q11 + h11
  let o13p := q13 + h13
  let o33p := q33 + h33
  let o11m := q11 - h11
  let o13m := q13 - h13
  let o33m := q33 - h33
  let oddPlus := perturbFOddMinor o11p o13p o33p
  let oddMixed := perturbFOddMixed o11p o13p o33p o11m o13m o33m
  let oddMinus := perturbFOddMinor o11m o13m o33m
  let ssPlus := perturbFOddS su sv o11p o13p o33p
  let ddPlus := perturbFOddD du dv o11p o13p o33p
  let sdPlus := perturbFOddSD su du sv dv o11p o13p o33p
  let ssMinus := perturbFOddS su sv o11m o13m o33m
  let ddMinus := perturbFOddD du dv o11m o13m o33m
  let sdMinus := perturbFOddSD su du sv dv o11m o13m o33m
  perturbFDetMinusSlope cornerA cornerX cornerC a x corner_c * oddMinus +
    perturbFDetMixedSlope cornerA cornerX cornerC a x corner_c * oddMixed +
    perturbFDetPlusSlope cornerA cornerX cornerC a x corner_c * oddPlus +
    (-(cornerC + corner_c) * ssPlus -
      (cornerA + a) * ddPlus + 2 * (cornerX + x) * sdPlus) / 4 +
    (corner_c * ssMinus + a * ddMinus) / 2 - x * sdMinus +
    (du * sv - su * dv) ^ 2 / 4

def perturbFFace
    (a x r f su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ) : ℝ :=
  correlatedCoefficientThree
    cornerA cornerX cornerR cornerC cornerD cornerF
    a x r corner_c corner_d f
    su du u4 sv dv v4 q11 q13 q33 h11 h13 h33

set_option maxHeartbeats 3000000 in
theorem perturb_f_secant_eq
    (a x r f f0 su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ) :
    quadraticSecant
        (fun z ↦ perturbFFace a x r z su du u4 sv dv v4
          q11 q13 q33 h11 h13 h33)
        f f0 =
      perturbFSecant a x su du sv dv q11 q13 q33 h11 h13 h33 := by
  unfold quadraticSecant perturbFFace perturbFSecant
    perturbFDetMinusSlope perturbFDetMixedSlope perturbFDetPlusSlope
    perturbFOddMinor perturbFOddMixed perturbFOddS perturbFOddD perturbFOddSD
    correlatedCoefficientThree alignedDeterminant alignedMixedDeterminant
    alignedAdjugatePair alignedMixedAdjugatePair alignedCrossEnergy
    alignedEntry00 alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
    mixedDeterminantOne
  dsimp only
  ring

def perturbFSlopeA
    (du dv q11 q13 q33 h11 h13 h33 : ℝ) : ℝ :=
  -(300000 * du ^ 2 * h33 - 100000 * du ^ 2 * q33 -
      600000 * du * dv * h13 + 200000 * du * dv * q13 +
      300000 * dv ^ 2 * h11 - 100000 * dv ^ 2 * q11 -
      9811 * h11 * h33 - 1213 * h11 * q33 + 9811 * h13 ^ 2 +
      2426 * h13 * q13 - 1213 * h33 * q11 + 4079 * q11 * q33 -
      4079 * q13 ^ 2) / 400000

def perturbFSlopeX
    (x su du sv dv q11 q13 q33 h11 h13 h33 : ℝ) : ℝ :=
  (-3000000 * du * h13 * sv + 3000000 * du * h33 * su +
      1000000 * du * q13 * sv - 1000000 * du * q33 * su +
      3000000 * dv * h11 * sv - 3000000 * dv * h13 * su -
      1000000 * dv * q11 * sv + 1000000 * dv * q13 * su -
      5000000 * h11 * h33 * x - 278345 * h11 * h33 +
      1000000 * h11 * q33 * x - 39779 * h11 * q33 +
      5000000 * h13 ^ 2 * x + 278345 * h13 ^ 2 -
      2000000 * h13 * q13 * x + 79558 * h13 * q13 +
      1000000 * h33 * q11 * x - 39779 * h33 * q11 +
      1000000 * q11 * q33 * x + 119301 * q11 * q33 -
      1000000 * q13 ^ 2 * x - 119301 * q13 ^ 2) / 2000000

def perturbFSlopeSu
    (su du sv dv q13 q33 h13 h33 : ℝ) : ℝ :=
  -(40000000000 * du * dv * sv - 6362120000 * du * h33 -
      360000 * du * q33 - 20000000000 * dv ^ 2 * su -
      11234600000 * dv ^ 2 + 6362120000 * dv * h13 +
      360000 * dv * q13 - 1389000000 * h13 * sv +
      694500000 * h33 * su + 390121485 * h33 -
      242600000 * q13 * sv + 121300000 * q33 * su +
      68137849 * q33) / 80000000000

def perturbFSlopeDu
    (du sv dv q13 q33 h13 h33 : ℝ) : ℝ :=
  (-384766700000 * du * h33 - 54975100000 * du * q33 +
      100000000000 * du * sv ^ 2 + 769533400000 * dv * h13 +
      109950200000 * dv * q13 - 112346000000 * dv * sv -
      31810600000 * h13 * sv + 11377954109 * h33 -
      1800000 * q13 * sv - 926418823 * q33 +
      1687000000 * sv ^ 2) / 400000000000

def perturbFSlopeSv
    (sv dv q11 q13 h11 h13 : ℝ) : ℝ :=
  (63621200000000 * dv * h11 + 3600000000 * dv * q11 -
      3790554040000 * dv - 6945000000000 * h11 * sv -
      3737451750000 * h11 + 6729140056000 * h13 -
      1213000000000 * q11 * sv - 652775950000 * q11 +
      1362696248000 * q13 + 56919380000 * sv +
      30631164347) / 800000000000000

def perturbFSlopeDv
    (dv q11 q13 h11 h13 : ℝ) : ℝ :=
  -(384766700000000 * dv * h11 + 54975100000000 * dv * q11 -
      31554059290000 * dv + 4351107470000 * h11 +
      4886939880000 * h13 + 3066641910000 * q11 -
      1853848760000 * q13 - 740773180069) / 400000000000000

def perturbFSlopeQ11 (q33 h33 : ℝ) : ℝ :=
  -(-23891664212800 * h33 + 4254936075200 * q33 +
      1387057229297) / 1600000000000000

def perturbFSlopeQ13 (q13 h13 : ℝ) : ℝ :=
  (-298645802660000 * h13 + 26593350470000 * q13 +
      17076795107559) / 10000000000000000

def perturbFSlopeQ33 (h11 : ℝ) : ℝ :=
  (11945832106400 * h11 - 792271927361) / 800000000000000

def perturbFSlopeH11 (h33 : ℝ) : ℝ :=
  (90497959000000 * h33 + 14631500903571) / 8000000000000000

def perturbFSlopeH13 (h13 : ℝ) : ℝ :=
  -(113122448750000 * h13 + 20095739874677) / 10000000000000000

def perturbFSlopeH33 : ℝ :=
  12435690511627 / 20000000000000000

set_option maxHeartbeats 3000000 in
theorem perturbFSecant_telescope
    (a x su du sv dv q11 q13 q33 h11 h13 h33 : ℝ) :
    perturbFSecant a x su du sv dv q11 q13 q33 h11 h13 h33 -
        perturbFSecant
          (824479 / 1000000) (39761 / 1000000) (56173 / 100000)
          (1687 / 100000) (10763 / 20000) (279 / 5000)
          (889 / 5000) (1001 / 5000) (663 / 2000)
          (1 / 50) (-(11 / 1000)) (-(117 / 1000)) =
      (a - 824479 / 1000000) *
          perturbFSlopeA du dv q11 q13 q33 h11 h13 h33 +
        (x - 39761 / 1000000) *
          perturbFSlopeX x su du sv dv q11 q13 q33 h11 h13 h33 +
        (su - 56173 / 100000) *
          perturbFSlopeSu su du sv dv q13 q33 h13 h33 +
        (du - 1687 / 100000) *
          perturbFSlopeDu du sv dv q13 q33 h13 h33 +
        (sv - 10763 / 20000) *
          perturbFSlopeSv sv dv q11 q13 h11 h13 +
        (dv - 279 / 5000) *
          perturbFSlopeDv dv q11 q13 h11 h13 +
        (q11 - 889 / 5000) * perturbFSlopeQ11 q33 h33 +
        (q13 - 1001 / 5000) * perturbFSlopeQ13 q13 h13 +
        (q33 - 663 / 2000) * perturbFSlopeQ33 h11 +
        (h11 - 1 / 50) * perturbFSlopeH11 h33 +
        (h13 - (-(11 / 1000))) * perturbFSlopeH13 h13 +
        (h33 - (-(117 / 1000))) * perturbFSlopeH33 := by
  unfold perturbFSecant perturbFDetMinusSlope perturbFDetMixedSlope
    perturbFDetPlusSlope perturbFOddMinor perturbFOddMixed perturbFOddS
    perturbFOddD perturbFOddSD perturbFSlopeA perturbFSlopeX
    perturbFSlopeSu perturbFSlopeDu perturbFSlopeSv perturbFSlopeDv
    perturbFSlopeQ11 perturbFSlopeQ13 perturbFSlopeQ33 perturbFSlopeH11
    perturbFSlopeH13 perturbFSlopeH33
  dsimp only
  ring

def perturbFSlopeAGram
    (q11 q13 q33 h11 h13 h33 : ℝ) : ℝ :=
  -(-9811 * h11 * h33 - 1213 * h11 * q33 + 9811 * h13 ^ 2 +
      2426 * h13 * q13 - 1213 * h33 * q11 + 4079 * q11 * q33 -
      4079 * q13 ^ 2) / 400000

def perturbFSlopeACoupling
    (du dv q11 q13 q33 h11 h13 h33 : ℝ) : ℝ :=
  (-3 * du ^ 2 * h33 + du ^ 2 * q33 + 6 * du * dv * h13 -
      2 * du * dv * q13 - 3 * dv ^ 2 * h11 + dv ^ 2 * q11) / 4

theorem perturbFSlopeA_eq_blocks
    (du dv q11 q13 q33 h11 h13 h33 : ℝ) :
    perturbFSlopeA du dv q11 q13 q33 h11 h13 h33 =
      perturbFSlopeAGram q11 q13 q33 h11 h13 h33 +
        perturbFSlopeACoupling du dv q11 q13 q33 h11 h13 h33 := by
  unfold perturbFSlopeA perturbFSlopeAGram perturbFSlopeACoupling
  ring

def perturbFAGramSlopeQ11
    (q11 q13 q33 h11 h13 h33 : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ perturbFSlopeAGram z q13 q33 h11 h13 h33)
    q11 (889 / 5000)

def perturbFAGramSlopeQ13
    (q13 q33 h11 h13 h33 : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ perturbFSlopeAGram (889 / 5000) z q33 h11 h13 h33)
    q13 (1001 / 5000)

def perturbFAGramSlopeQ33
    (q33 h11 h13 h33 : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ perturbFSlopeAGram
      (889 / 5000) (1001 / 5000) z h11 h13 h33)
    q33 (663 / 2000)

def perturbFAGramSlopeH11 (h11 h13 h33 : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ perturbFSlopeAGram
      (889 / 5000) (1001 / 5000) (663 / 2000) z h13 h33)
    h11 (7 / 500)

def perturbFAGramSlopeH13 (h13 h33 : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ perturbFSlopeAGram
      (889 / 5000) (1001 / 5000) (663 / 2000) (7 / 500) z h33)
    h13 (-(11 / 1000))

def perturbFAGramSlopeH33 (h33 : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ perturbFSlopeAGram
      (889 / 5000) (1001 / 5000) (663 / 2000)
      (7 / 500) (-(11 / 1000)) z)
    h33 (-(117 / 1000))

theorem perturbFSlopeAGram_telescope
    (q11 q13 q33 h11 h13 h33 : ℝ) :
    perturbFSlopeAGram q11 q13 q33 h11 h13 h33 -
        perturbFSlopeAGram
          (889 / 5000) (1001 / 5000) (663 / 2000)
          (7 / 500) (-(11 / 1000)) (-(117 / 1000)) =
      (q11 - 889 / 5000) *
          perturbFAGramSlopeQ11 q11 q13 q33 h11 h13 h33 +
        (q13 - 1001 / 5000) *
          perturbFAGramSlopeQ13 q13 q33 h11 h13 h33 +
        (q33 - 663 / 2000) *
          perturbFAGramSlopeQ33 q33 h11 h13 h33 +
        (h11 - 7 / 500) * perturbFAGramSlopeH11 h11 h13 h33 +
        (h13 - (-(11 / 1000))) * perturbFAGramSlopeH13 h13 h33 +
        (h33 - (-(117 / 1000))) * perturbFAGramSlopeH33 h33 := by
  unfold perturbFAGramSlopeQ11 perturbFAGramSlopeQ13
    perturbFAGramSlopeQ33 perturbFAGramSlopeH11 perturbFAGramSlopeH13
    perturbFAGramSlopeH33 quadraticSecant perturbFSlopeAGram
  ring

def perturbFACouplingSlopeDu
    (du dv q11 q13 q33 h11 h13 h33 : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ perturbFSlopeACoupling z dv q11 q13 q33 h11 h13 h33)
    du (1687 / 100000)

def perturbFACouplingSlopeDv
    (dv q11 q13 q33 h11 h13 h33 : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ perturbFSlopeACoupling
      (1687 / 100000) z q11 q13 q33 h11 h13 h33)
    dv (279 / 5000)

def perturbFACouplingSlopeQ11
    (q11 q13 q33 h11 h13 h33 : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ perturbFSlopeACoupling
      (1687 / 100000) (279 / 5000) z q13 q33 h11 h13 h33)
    q11 (179 / 1000)

def perturbFACouplingSlopeQ13
    (q13 q33 h11 h13 h33 : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ perturbFSlopeACoupling
      (1687 / 100000) (279 / 5000) (179 / 1000) z
      q33 h11 h13 h33)
    q13 (1 / 5)

def perturbFACouplingSlopeQ33
    (q33 h11 h13 h33 : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ perturbFSlopeACoupling
      (1687 / 100000) (279 / 5000) (179 / 1000) (1 / 5)
      z h11 h13 h33)
    q33 (333 / 1000)

def perturbFACouplingSlopeH11 (h11 h13 h33 : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ perturbFSlopeACoupling
      (1687 / 100000) (279 / 5000) (179 / 1000) (1 / 5)
      (333 / 1000) z h13 h33)
    h11 (7 / 500)

def perturbFACouplingSlopeH13 (h13 h33 : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ perturbFSlopeACoupling
      (1687 / 100000) (279 / 5000) (179 / 1000) (1 / 5)
      (333 / 1000) (7 / 500) z h33)
    h13 (-(9 / 1000))

def perturbFACouplingSlopeH33 (h33 : ℝ) : ℝ :=
  quadraticSecant
    (fun z ↦ perturbFSlopeACoupling
      (1687 / 100000) (279 / 5000) (179 / 1000) (1 / 5)
      (333 / 1000) (7 / 500) (-(9 / 1000)) z)
    h33 (-(3 / 25))

theorem perturbFSlopeACoupling_telescope
    (du dv q11 q13 q33 h11 h13 h33 : ℝ) :
    perturbFSlopeACoupling du dv q11 q13 q33 h11 h13 h33 -
        perturbFSlopeACoupling
          (1687 / 100000) (279 / 5000) (179 / 1000) (1 / 5)
          (333 / 1000) (7 / 500) (-(9 / 1000)) (-(3 / 25)) =
      (du - 1687 / 100000) *
          perturbFACouplingSlopeDu du dv q11 q13 q33 h11 h13 h33 +
        (dv - 279 / 5000) *
          perturbFACouplingSlopeDv dv q11 q13 q33 h11 h13 h33 +
        (q11 - 179 / 1000) *
          perturbFACouplingSlopeQ11 q11 q13 q33 h11 h13 h33 +
        (q13 - 1 / 5) *
          perturbFACouplingSlopeQ13 q13 q33 h11 h13 h33 +
        (q33 - 333 / 1000) *
          perturbFACouplingSlopeQ33 q33 h11 h13 h33 +
        (h11 - 7 / 500) * perturbFACouplingSlopeH11 h11 h13 h33 +
        (h13 - (-(9 / 1000))) * perturbFACouplingSlopeH13 h13 h33 +
        (h33 - (-(3 / 25))) * perturbFACouplingSlopeH33 h33 := by
  unfold perturbFACouplingSlopeDu perturbFACouplingSlopeDv
    perturbFACouplingSlopeQ11 perturbFACouplingSlopeQ13
    perturbFACouplingSlopeQ33 perturbFACouplingSlopeH11
    perturbFACouplingSlopeH13 perturbFACouplingSlopeH33 quadraticSecant
    perturbFSlopeACoupling
  ring

set_option maxHeartbeats 1000000 in
theorem perturbFSlopeA_upper
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    perturbFSlopeA du dv q11 q13 q33 h11 h13 h33 ≤
      (-22 / 100000 : ℝ) := by
  rcases hbox.du_mem with ⟨hduL, hduU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  rcases hbox.q11_mem with ⟨hq11L, hq11U⟩
  rcases hbox.q13_mem with ⟨hq13L, hq13U⟩
  rcases hbox.q33_mem with ⟨hq33L, hq33U⟩
  rcases hbox.h11_mem with ⟨hh11L, hh11U⟩
  rcases hbox.h13_mem with ⟨hh13L, hh13U⟩
  rcases hbox.h33_mem with ⟨hh33L, hh33U⟩
  norm_num at hduL hduU hdvL hdvU hq11L hq11U hq13L hq13U
  norm_num at hq33L hq33U hh11L hh11U hh13L hh13U hh33L hh33U
  have hgQ11 : perturbFAGramSlopeQ11 q11 q13 q33 h11 h13 h33 ≤
      (-2988219 / 800000000 : ℝ) := by
    unfold perturbFAGramSlopeQ11 quadraticSecant perturbFSlopeAGram
    ring_nf
    nlinarith only [hq33L, hh33U]
  have hgQ13 : (826717 / 200000000 : ℝ) ≤
      perturbFAGramSlopeQ13 q13 q33 h11 h13 h33 := by
    unfold perturbFAGramSlopeQ13 quadraticSecant perturbFSlopeAGram
    ring_nf
    nlinarith only [hq13L, hh13U]
  have hgQ33 : perturbFAGramSlopeQ33 q33 h11 h13 h33 ≤
      (-3504931 / 2000000000 : ℝ) := by
    unfold perturbFAGramSlopeQ33 quadraticSecant perturbFSlopeAGram
    ring_nf
    nlinarith only [hh11U]
  have hgH11 : perturbFAGramSlopeH11 h11 h13 h33 ≤
      (-371979 / 200000000 : ℝ) := by
    unfold perturbFAGramSlopeH11 quadraticSecant perturbFSlopeAGram
    ring_nf
    nlinarith only [hh33U]
  have hgH13 : perturbFAGramSlopeH13 h13 h33 ≤
      (-134679 / 200000000 : ℝ) := by
    unfold perturbFAGramSlopeH13 quadraticSecant perturbFSlopeAGram
    ring_nf
    nlinarith only [hh13L, hh13U]
  have hgH33 : (1765127 / 2000000000 : ℝ) ≤
      perturbFAGramSlopeH33 h33 := by
    norm_num [perturbFAGramSlopeH33, quadraticSecant, perturbFSlopeAGram]
  have hgQ11Step := mul_nonpos_of_nonneg_of_nonpos
    (by linarith : 0 ≤ q11 - 889 / 5000)
    (by linarith : perturbFAGramSlopeQ11 q11 q13 q33 h11 h13 h33 ≤ 0)
  have hgQ13Step := mul_nonpos_of_nonpos_of_nonneg
    (by linarith : q13 - 1001 / 5000 ≤ 0)
    (by linarith : 0 ≤ perturbFAGramSlopeQ13 q13 q33 h11 h13 h33)
  have hgQ33Step := mul_nonpos_of_nonneg_of_nonpos
    (by linarith : 0 ≤ q33 - 663 / 2000)
    (by linarith : perturbFAGramSlopeQ33 q33 h11 h13 h33 ≤ 0)
  have hgH11Step := mul_nonpos_of_nonneg_of_nonpos
    (by linarith : 0 ≤ h11 - 7 / 500)
    (by linarith : perturbFAGramSlopeH11 h11 h13 h33 ≤ 0)
  have hgH13Step := mul_nonpos_of_nonneg_of_nonpos
    (by linarith : 0 ≤ h13 - (-(11 / 1000)))
    (by linarith : perturbFAGramSlopeH13 h13 h33 ≤ 0)
  have hgH33Step := mul_nonpos_of_nonpos_of_nonneg
    (by linarith : h33 - (-(117 / 1000)) ≤ 0)
    (by linarith : 0 ≤ perturbFAGramSlopeH33 h33)
  have hgTel := perturbFSlopeAGram_telescope q11 q13 q33 h11 h13 h33
  have hgCorner : perturbFSlopeAGram
      (889 / 5000) (1001 / 5000) (663 / 2000)
      (7 / 500) (-(11 / 1000)) (-(117 / 1000)) ≤
        (-27 / 100000 : ℝ) := by
    norm_num [perturbFSlopeAGram]
  have hgUpper : perturbFSlopeAGram q11 q13 q33 h11 h13 h33 ≤
      (-27 / 100000 : ℝ) := by
    nlinarith only [hgTel, hgCorner, hgQ11Step, hgQ13Step, hgQ33Step,
      hgH11Step, hgH13Step, hgH33Step]
  have hcDuCoeffNonneg : 0 ≤ -3 * h33 + q33 := by linarith
  have hcDuCoeffU : -3 * h33 + q33 ≤ (693 / 1000 : ℝ) := by linarith
  have hcDuSumNonneg : 0 ≤ du + 1687 / 100000 := by linarith
  have hcDuSumU : du + 1687 / 100000 ≤ (3379 / 100000 : ℝ) := by linarith
  have hcDuPositive : (-3 * h33 + q33) * (du + 1687 / 100000) ≤
      (693 / 1000 : ℝ) * (3379 / 100000) :=
    nonnegative_product_upper (-3 * h33 + q33) (du + 1687 / 100000)
      (693 / 1000) (3379 / 100000) hcDuCoeffU hcDuSumU
      (by norm_num) hcDuSumNonneg
  have hcDuNegative : (6 * h13 - 2 * q13) * dv ≤
      (-454 / 1000 : ℝ) * (111 / 2000) := by
    have hcoef : 6 * h13 - 2 * q13 ≤ (-454 / 1000 : ℝ) := by linarith
    have := positive_negative_product_upper dv (6 * h13 - 2 * q13)
      (111 / 2000) (-454 / 1000) hdvL (by linarith)
      (by norm_num) hcoef
    nlinarith only [this]
  have hcDu : perturbFACouplingSlopeDu du dv q11 q13 q33 h11 h13 h33 ≤
      (-87201 / 200000000 : ℝ) := by
    unfold perturbFACouplingSlopeDu quadraticSecant perturbFSlopeACoupling
    ring_nf
    nlinarith only [hcDuPositive, hcDuNegative]
  have hcDvCoeffL : (589 / 5000 : ℝ) ≤ q11 - 3 * h11 := by linarith
  have hcDvCoeff0 : 0 ≤ q11 - 3 * h11 := by linarith
  have hcDvSumL : (1113 / 10000 : ℝ) ≤ dv + 279 / 5000 := by linarith
  have hcDvPositive : (589 / 5000 : ℝ) * (1113 / 10000) ≤
      (q11 - 3 * h11) * (dv + 279 / 5000) :=
    nonnegative_product_lower (q11 - 3 * h11) (dv + 279 / 5000)
      (589 / 5000) (1113 / 10000) hcDvCoeffL hcDvSumL
      (by norm_num) (by linarith)
  have hcDvNegative : (1687 / 100000 : ℝ) * (-(2332 / 5000)) ≤
      (1687 / 100000) * (6 * h13 - 2 * q13) := by
    nlinarith only [hh13L, hq13U]
  have hcDv : (647319 / 500000000 : ℝ) ≤
      perturbFACouplingSlopeDv dv q11 q13 q33 h11 h13 h33 := by
    unfold perturbFACouplingSlopeDv quadraticSecant perturbFSlopeACoupling
    ring_nf
    nlinarith only [hcDvPositive, hcDvNegative]
  have hcQ11 : (616041 / 800000000 : ℝ) ≤
      perturbFACouplingSlopeQ11 q11 q13 q33 h11 h13 h33 := by
    unfold perturbFACouplingSlopeQ11 quadraticSecant perturbFSlopeACoupling
    ring_nf
    norm_num
  have hcQ13 : perturbFACouplingSlopeQ13 q13 q33 h11 h13 h33 ≤
      (-374511 / 800000000 : ℝ) := by
    unfold perturbFACouplingSlopeQ13 quadraticSecant perturbFSlopeACoupling
    ring_nf
    norm_num
  have hcQ33 : (5691913 / 80000000000 : ℝ) ≤
      perturbFACouplingSlopeQ33 q33 h11 h13 h33 := by
    unfold perturbFACouplingSlopeQ33 quadraticSecant perturbFSlopeACoupling
    ring_nf
    norm_num
  have hcH11 : perturbFACouplingSlopeH11 h11 h13 h33 ≤
      (-1848123 / 800000000 : ℝ) := by
    unfold perturbFACouplingSlopeH11 quadraticSecant perturbFSlopeACoupling
    ring_nf
    norm_num
  have hcH13 : (1123533 / 800000000 : ℝ) ≤
      perturbFACouplingSlopeH13 h13 h33 := by
    unfold perturbFACouplingSlopeH13 quadraticSecant perturbFSlopeACoupling
    ring_nf
    norm_num
  have hcH33 : perturbFACouplingSlopeH33 h33 ≤
      (-17075739 / 80000000000 : ℝ) := by
    unfold perturbFACouplingSlopeH33 quadraticSecant perturbFSlopeACoupling
    ring_nf
    norm_num
  have hcDuStep := mul_nonpos_of_nonneg_of_nonpos
    (by linarith : 0 ≤ du - 1687 / 100000)
    (by linarith : perturbFACouplingSlopeDu du dv q11 q13 q33 h11 h13 h33 ≤ 0)
  have hcDvStep := mul_nonpos_of_nonpos_of_nonneg
    (by linarith : dv - 279 / 5000 ≤ 0)
    (by linarith : 0 ≤ perturbFACouplingSlopeDv dv q11 q13 q33 h11 h13 h33)
  have hcQ11Step := mul_nonpos_of_nonpos_of_nonneg
    (by linarith : q11 - 179 / 1000 ≤ 0)
    (by linarith : 0 ≤
      perturbFACouplingSlopeQ11 q11 q13 q33 h11 h13 h33)
  have hcQ13Step := mul_nonpos_of_nonneg_of_nonpos
    (by linarith : 0 ≤ q13 - 1 / 5)
    (by linarith : perturbFACouplingSlopeQ13 q13 q33 h11 h13 h33 ≤ 0)
  have hcQ33Step := mul_nonpos_of_nonpos_of_nonneg
    (by linarith : q33 - 333 / 1000 ≤ 0)
    (by linarith : 0 ≤ perturbFACouplingSlopeQ33 q33 h11 h13 h33)
  have hcH11Step := mul_nonpos_of_nonneg_of_nonpos
    (by linarith : 0 ≤ h11 - 7 / 500)
    (by linarith : perturbFACouplingSlopeH11 h11 h13 h33 ≤ 0)
  have hcH13Step := mul_nonpos_of_nonpos_of_nonneg
    (by linarith : h13 - (-(9 / 1000)) ≤ 0)
    (by linarith : 0 ≤ perturbFACouplingSlopeH13 h13 h33)
  have hcH33Step := mul_nonpos_of_nonneg_of_nonpos
    (by linarith : 0 ≤ h33 - (-(3 / 25)))
    (by linarith : perturbFACouplingSlopeH33 h33 ≤ 0)
  have hcTel := perturbFSlopeACoupling_telescope
    du dv q11 q13 q33 h11 h13 h33
  have hcCorner : perturbFSlopeACoupling
      (1687 / 100000) (279 / 5000) (179 / 1000) (1 / 5)
      (333 / 1000) (7 / 500) (-(9 / 1000)) (-(3 / 25)) ≤
        (5 / 100000 : ℝ) := by
    norm_num [perturbFSlopeACoupling]
  have hcUpper : perturbFSlopeACoupling
      du dv q11 q13 q33 h11 h13 h33 ≤ (5 / 100000 : ℝ) := by
    nlinarith only [hcTel, hcCorner, hcDuStep, hcDvStep, hcQ11Step,
      hcQ13Step, hcQ33Step, hcH11Step, hcH13Step, hcH33Step]
  rw [perturbFSlopeA_eq_blocks]
  linarith

set_option maxHeartbeats 3000000 in
theorem perturbFSecant_upper
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    perturbFSecant a x su du sv dv q11 q13 q33 h11 h13 h33 ≤
      (-3 / 100000 : ℝ) := by
  rcases hbox.a_mem with ⟨haL, haU⟩
  rcases hbox.x_mem with ⟨hxL, hxU⟩
  rcases hbox.su_mem with ⟨hsuL, hsuU⟩
  rcases hbox.du_mem with ⟨hduL, hduU⟩
  rcases hbox.sv_mem with ⟨hsvL, hsvU⟩
  rcases hbox.dv_mem with ⟨hdvL, hdvU⟩
  rcases hbox.q11_mem with ⟨hq11L, hq11U⟩
  rcases hbox.q13_mem with ⟨hq13L, hq13U⟩
  rcases hbox.q33_mem with ⟨hq33L, hq33U⟩
  rcases hbox.h11_mem with ⟨hh11L, hh11U⟩
  rcases hbox.h13_mem with ⟨hh13L, hh13U⟩
  rcases hbox.h33_mem with ⟨hh33L, hh33U⟩
  norm_num at haL haU hxL hxU hsuL hsuU hduL hduU hsvL hsvU
  norm_num at hdvL hdvU hq11L hq11U hq13L hq13U hq33L hq33U
  norm_num at hh11L hh11U hh13L hh13U hh33L hh33U
  have hnh13L : (9 / 1000 : ℝ) ≤ -h13 := by linarith
  have hnh13U : -h13 ≤ (11 / 1000 : ℝ) := by linarith
  have hnh33L : (117 / 1000 : ℝ) ≤ -h33 := by linarith
  have hnh33U : -h33 ≤ (3 / 25 : ℝ) := by linarith
  have haSlope : perturbFSlopeA du dv q11 q13 q33 h11 h13 h33 ≤
      (-22 / 100000 : ℝ) := by
    exact perturbFSlopeA_upper
      A X R C D F a x r c d f su du u4 sv dv v4
        q11 q13 q33 h11 h13 h33 hbox
  have hxSlope : (0 : ℝ) ≤
      perturbFSlopeX x su du sv dv q11 q13 q33 h11 h13 h33 := by
    have h1 : (1687 / 100000 : ℝ) * (9 / 1000) * (10763 / 20000) ≤
        du * (-h13) * sv := by bound
    have h2 : du * (-h33) * su ≤
        (423 / 25000 : ℝ) * (3 / 25) * (56173 / 100000) := by bound
    have h3 : (1687 / 100000 : ℝ) * (1 / 5) * (10763 / 20000) ≤
        du * q13 * sv := by bound
    have h4 : du * q33 * su ≤
        (423 / 25000 : ℝ) * (333 / 1000) * (56173 / 100000) := by bound
    have h5 : (111 / 2000 : ℝ) * (7 / 500) * (10763 / 20000) ≤
        dv * h11 * sv := by bound
    have h6 : (111 / 2000 : ℝ) * (9 / 1000) * (7021 / 12500) ≤
        dv * (-h13) * su := by bound
    have h7 : dv * q11 * sv ≤
        (279 / 5000 : ℝ) * (179 / 1000) * (13459 / 25000) := by bound
    have h8 : (111 / 2000 : ℝ) * (1 / 5) * (7021 / 12500) ≤
        dv * q13 * su := by bound
    have h9 : (7 / 500 : ℝ) * (117 / 1000) * (37851 / 1000000) ≤
        h11 * (-h33) * x := by bound
    have h10 : (7 / 500 : ℝ) * (117 / 1000) ≤ h11 * (-h33) := by bound
    have h11x : (7 / 500 : ℝ) * (663 / 2000) * (37851 / 1000000) ≤
        h11 * q33 * x := by bound
    have h12 : h11 * q33 ≤ (1 / 50 : ℝ) * (333 / 1000) := by bound
    have h13x : (9 / 1000 : ℝ) ^ 2 * (37851 / 1000000) ≤
        (-h13) ^ 2 * x := by bound
    have h14 : (9 / 1000 : ℝ) ^ 2 ≤ (-h13) ^ 2 := by bound
    have h15 : (9 / 1000 : ℝ) * (1 / 5) * (37851 / 1000000) ≤
        (-h13) * q13 * x := by bound
    have h16 : (-h13) * q13 ≤ (11 / 1000 : ℝ) * (1001 / 5000) := by bound
    have h17 : (-h33) * q11 * x ≤
        (3 / 25 : ℝ) * (179 / 1000) * (39761 / 1000000) := by bound
    have h18 : (117 / 1000 : ℝ) * (889 / 5000) ≤ (-h33) * q11 := by bound
    have h19 : (889 / 5000 : ℝ) * (663 / 2000) * (37851 / 1000000) ≤
        q11 * q33 * x := by bound
    have h20 : (889 / 5000 : ℝ) * (663 / 2000) ≤ q11 * q33 := by bound
    have h21 : q13 ^ 2 * x ≤
        (1001 / 5000 : ℝ) ^ 2 * (39761 / 1000000) := by bound
    have h22 : q13 ^ 2 ≤ (1001 / 5000 : ℝ) ^ 2 := by bound
    unfold perturbFSlopeX
    nlinarith only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
      h11x, h12, h13x, h14, h15, h16, h17, h18, h19, h20, h21, h22]
  have hsuSlope : (0 : ℝ) ≤
      perturbFSlopeSu su du sv dv q13 q33 h13 h33 := by
    have h1 : du * dv * sv ≤
        (423 / 25000 : ℝ) * (279 / 5000) * (13459 / 25000) := by bound
    have h2 : du * (-h33) ≤ (423 / 25000 : ℝ) * (3 / 25) := by bound
    have h3 : (1687 / 100000 : ℝ) * (663 / 2000) ≤ du * q33 := by bound
    have h4 : (111 / 2000 : ℝ) ^ 2 * (7021 / 12500) ≤ dv ^ 2 * su := by bound
    have h5 : (111 / 2000 : ℝ) ^ 2 ≤ dv ^ 2 := by bound
    have h6 : (111 / 2000 : ℝ) * (9 / 1000) ≤ dv * (-h13) := by bound
    have h7 : dv * q13 ≤ (279 / 5000 : ℝ) * (1001 / 5000) := by bound
    have h8 : (-h13) * sv ≤ (11 / 1000 : ℝ) * (13459 / 25000) := by bound
    have h9 : (117 / 1000 : ℝ) * (7021 / 12500) ≤ (-h33) * su := by bound
    have h10 : (1 / 5 : ℝ) * (10763 / 20000) ≤ q13 * sv := by bound
    have h11s : q33 * su ≤ (333 / 1000 : ℝ) * (56173 / 100000) := by bound
    unfold perturbFSlopeSu
    nlinarith only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
      h11s, hnh33L, hq33U]
  have hduSlope : perturbFSlopeDu du sv dv q13 q33 h13 h33 ≤ 0 := by
    have h1 : du * (-h33) ≤ (423 / 25000 : ℝ) * (3 / 25) := by bound
    have h2 : (1687 / 100000 : ℝ) * (663 / 2000) ≤ du * q33 := by bound
    have h3 : du * sv ^ 2 ≤ (423 / 25000 : ℝ) * (13459 / 25000) ^ 2 := by bound
    have h4 : (111 / 2000 : ℝ) * (9 / 1000) ≤ dv * (-h13) := by bound
    have h5 : dv * q13 ≤ (279 / 5000 : ℝ) * (1001 / 5000) := by bound
    have h6 : (111 / 2000 : ℝ) * (10763 / 20000) ≤ dv * sv := by bound
    have h7 : (-h13) * sv ≤ (11 / 1000 : ℝ) * (13459 / 25000) := by bound
    have h8 : (1 / 5 : ℝ) * (10763 / 20000) ≤ q13 * sv := by bound
    have h9 : sv ^ 2 ≤ (13459 / 25000 : ℝ) ^ 2 := by bound
    unfold perturbFSlopeDu
    nlinarith only [h1, h2, h3, h4, h5, h6, h7, h8, h9,
      hnh33L, hq33L]
  have hsvSlope : perturbFSlopeSv sv dv q11 q13 h11 h13 ≤ 0 := by
    have h1 : dv * h11 ≤ (279 / 5000 : ℝ) * (1 / 50) := by bound
    have h2 : dv * q11 ≤ (279 / 5000 : ℝ) * (179 / 1000) := by bound
    have h3 : (7 / 500 : ℝ) * (10763 / 20000) ≤ h11 * sv := by bound
    have h4 : (889 / 5000 : ℝ) * (10763 / 20000) ≤ q11 * sv := by bound
    unfold perturbFSlopeSv
    nlinarith only [h1, h2, h3, h4, hdvL, hh11L, hnh13L,
      hq11L, hq13U, hsvU]
  have hdvSlope : (0 : ℝ) ≤
      perturbFSlopeDv dv q11 q13 h11 h13 := by
    have h1 : dv * h11 ≤ (279 / 5000 : ℝ) * (1 / 50) := by bound
    have h2 : dv * q11 ≤ (279 / 5000 : ℝ) * (179 / 1000) := by bound
    unfold perturbFSlopeDv
    nlinarith only [h1, h2, hdvL, hh11U, hnh13L, hq11U, hq13L]
  have hq11Slope : perturbFSlopeQ11 q33 h33 ≤
      (-34 / 10000 : ℝ) := by
    unfold perturbFSlopeQ11
    nlinarith only [hq33L, hh33U]
  have hq13Slope : (25 / 10000 : ℝ) ≤ perturbFSlopeQ13 q13 h13 := by
    unfold perturbFSlopeQ13
    nlinarith only [hq13L, hh13U]
  have hq33Slope : perturbFSlopeQ33 h11 ≤ (-69 / 100000 : ℝ) := by
    unfold perturbFSlopeQ33
    nlinarith only [hh11U]
  have hh11Slope : (47 / 100000 : ℝ) ≤ perturbFSlopeH11 h33 := by
    unfold perturbFSlopeH11
    nlinarith only [hh33L]
  have hh13Slope : perturbFSlopeH13 h13 ≤ (-18 / 10000 : ℝ) := by
    unfold perturbFSlopeH13
    nlinarith only [hh13L]
  have hh33Slope : (62 / 100000 : ℝ) ≤ perturbFSlopeH33 := by
    norm_num [perturbFSlopeH33]
  have haStep := mul_nonpos_of_nonneg_of_nonpos
    (by linarith : 0 ≤ a - 824479 / 1000000)
    (by linarith : perturbFSlopeA du dv q11 q13 q33 h11 h13 h33 ≤ 0)
  have hxStep := mul_nonpos_of_nonpos_of_nonneg
    (by linarith : x - 39761 / 1000000 ≤ 0)
    (by linarith : 0 ≤
      perturbFSlopeX x su du sv dv q11 q13 q33 h11 h13 h33)
  have hsuStep := mul_nonpos_of_nonpos_of_nonneg
    (by linarith : su - 56173 / 100000 ≤ 0)
    (by linarith : 0 ≤ perturbFSlopeSu su du sv dv q13 q33 h13 h33)
  have hduStep := mul_nonpos_of_nonneg_of_nonpos
    (by linarith : 0 ≤ du - 1687 / 100000)
    (by linarith : perturbFSlopeDu du sv dv q13 q33 h13 h33 ≤ 0)
  have hsvStep := mul_nonpos_of_nonneg_of_nonpos
    (by linarith : 0 ≤ sv - 10763 / 20000)
    (by linarith : perturbFSlopeSv sv dv q11 q13 h11 h13 ≤ 0)
  have hdvStep := mul_nonpos_of_nonpos_of_nonneg
    (by linarith : dv - 279 / 5000 ≤ 0)
    (by linarith : 0 ≤ perturbFSlopeDv dv q11 q13 h11 h13)
  have hq11Step := mul_nonpos_of_nonneg_of_nonpos
    (by linarith : 0 ≤ q11 - 889 / 5000)
    (by linarith : perturbFSlopeQ11 q33 h33 ≤ 0)
  have hq13Step := mul_nonpos_of_nonpos_of_nonneg
    (by linarith : q13 - 1001 / 5000 ≤ 0)
    (by linarith : 0 ≤ perturbFSlopeQ13 q13 h13)
  have hq33Step := mul_nonpos_of_nonneg_of_nonpos
    (by linarith : 0 ≤ q33 - 663 / 2000)
    (by linarith : perturbFSlopeQ33 h11 ≤ 0)
  have hh11Step := mul_nonpos_of_nonpos_of_nonneg
    (by linarith : h11 - 1 / 50 ≤ 0)
    (by linarith : 0 ≤ perturbFSlopeH11 h33)
  have hh13Step := mul_nonpos_of_nonneg_of_nonpos
    (by linarith : 0 ≤ h13 - (-(11 / 1000)))
    (by linarith : perturbFSlopeH13 h13 ≤ 0)
  have hh33Step := mul_nonpos_of_nonpos_of_nonneg
    (by linarith : h33 - (-(117 / 1000)) ≤ 0)
    (by linarith : 0 ≤ perturbFSlopeH33)
  have htel := perturbFSecant_telescope
    a x su du sv dv q11 q13 q33 h11 h13 h33
  have hcorner : perturbFSecant
      (824479 / 1000000) (39761 / 1000000) (56173 / 100000)
      (1687 / 100000) (10763 / 20000) (279 / 5000)
      (889 / 5000) (1001 / 5000) (663 / 2000)
      (1 / 50) (-(11 / 1000)) (-(117 / 1000)) <
        (-3 / 100000 : ℝ) := by
    norm_num [perturbFSecant, perturbFDetMinusSlope,
      perturbFDetMixedSlope, perturbFDetPlusSlope, perturbFOddMinor,
      perturbFOddMixed, perturbFOddS, perturbFOddD, perturbFOddSD,
      cornerA, cornerX, cornerC, corner_c]
  nlinarith only [htel, hcorner, haStep, hxStep, hsuStep, hduStep,
    hsvStep, hdvStep, hq11Step, hq13Step, hq33Step, hh11Step,
    hh13Step, hh33Step]

set_option maxHeartbeats 3000000 in
theorem correlated_even_unfix_f
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    perturbFFace a x r corner_f su du u4 sv dv v4
        q11 q13 q33 h11 h13 h33 ≤
      perturbFFace a x r f su du u4 sv dv v4
        q11 q13 q33 h11 h13 h33 := by
  have hfU := hbox.f_mem.2
  norm_num at hfU
  let g : ℝ → ℝ := fun z ↦
    perturbFFace a x r z su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33
  have hslope := perturbFSecant_upper
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hsecCap : quadraticSecant g f corner_f ≤ (-3 / 100000 : ℝ) := by
    rw [show quadraticSecant g f corner_f =
        perturbFSecant a x su du sv dv q11 q13 q33 h11 h13 h33 by
      simpa only [g] using perturb_f_secant_eq
        a x r f corner_f su du u4 sv dv v4
          q11 q13 q33 h11 h13 h33]
    exact hslope
  have hsec : quadraticSecant g f corner_f ≤ 0 :=
    le_trans hsecCap (by norm_num)
  have hid : g f - g corner_f =
      (f - corner_f) * quadraticSecant g f corner_f := by
    unfold g perturbFFace quadraticSecant correlatedCoefficientThree
      alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
      alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00 alignedEntry02
      alignedEntry04 alignedEntry22 alignedEntry24 mixedDeterminantOne
    dsimp only
    ring
  exact quadraticSecant_upper_endpoint g f corner_f
    (by norm_num [corner_f] at ⊢; exact hfU) hsec hid

/-! ### The perturbation-`d` secant

The second even move keeps the already-unfixed `f` coordinate and splits its
`d`-secant into the three determinant/odd-minor pairings, the plus and minus
coupling derivatives, and the alternating cross term.
-/

def perturbDDetMinusSlope
    (a x r d : ℝ) : ℝ :=
  -(300000000000 * a * d - 1584500000 * a - 137423000000 * d +
      600000000000 * r * x - 7954000000 * r - 48579600000 * x -
      16926646491) / 400000000000

def perturbDDetMixedSlope
    (a x r d : ℝ) : ℝ :=
  (300000000000 * a * d + 15574700000 * a + 137423000000 * d +
      600000000000 * r * x + 7954000000 * r + 48579600000 * x -
      10518062309) / 400000000000

def perturbDDetPlusSlope
    (a x r d : ℝ) : ℝ :=
  -(100000000000 * a * d + 10911300000 * a + 137423000000 * d +
      200000000000 * r * x + 7954000000 * r + 48579600000 * x +
      16926646491) / 400000000000

def perturbDOddSFour
    (su u4 sv v4 o11 o13 o33 : ℝ) : ℝ :=
  o33 * su * u4 - o13 * (su * v4 + u4 * sv) + o11 * sv * v4

def perturbDOddDFour
    (du u4 dv v4 o11 o13 o33 : ℝ) : ℝ :=
  o33 * du * u4 - o13 * (du * v4 + u4 * dv) + o11 * dv * v4

def perturbDSecant
    (a x r su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 d : ℝ) : ℝ :=
  let o11p := q11 + h11
  let o13p := q13 + h13
  let o33p := q33 + h33
  let o11m := q11 - h11
  let o13m := q13 - h13
  let o33m := q33 - h33
  let oddPlus := perturbFOddMinor o11p o13p o33p
  let oddMixed := perturbFOddMixed o11p o13p o33p o11m o13m o33m
  let oddMinus := perturbFOddMinor o11m o13m o33m
  let ssPlus := perturbFOddS su sv o11p o13p o33p
  let sdPlus := perturbFOddSD su du sv dv o11p o13p o33p
  let s4Plus := perturbDOddSFour su u4 sv v4 o11p o13p o33p
  let d4Plus := perturbDOddDFour du u4 dv v4 o11p o13p o33p
  let ssMinus := perturbFOddS su sv o11m o13m o33m
  let sdMinus := perturbFOddSD su du sv dv o11m o13m o33m
  let s4Minus := perturbDOddSFour su u4 sv v4 o11m o13m o33m
  let d4Minus := perturbDOddDFour du u4 dv v4 o11m o13m o33m
  perturbDDetMinusSlope a x r d * oddMinus +
    perturbDDetMixedSlope a x r d * oddMixed +
    perturbDDetPlusSlope a x r d * oddPlus +
    ((cornerD + (d + corner_d) / 2) * ssPlus +
      (cornerR + r) * sdPlus + (cornerX + x) * s4Plus -
      (cornerA + a) * d4Plus) / 2 +
    (-(d + corner_d) * ssMinus / 2 - r * sdMinus - x * s4Minus +
      a * d4Minus) +
    (du * sv - dv * su) * (-su * v4 + sv * u4) / 2

def perturbDFace
    (a x r d f su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ) : ℝ :=
  correlatedCoefficientThree
    cornerA cornerX cornerR cornerC cornerD cornerF
    a x r corner_c d f
    su du u4 sv dv v4 q11 q13 q33 h11 h13 h33

set_option maxHeartbeats 3000000 in
theorem perturb_d_secant_eq
    (a x r d f su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ) :
    quadraticSecant
        (fun z ↦ perturbDFace a x r z f su du u4 sv dv v4
          q11 q13 q33 h11 h13 h33)
        d corner_d =
      perturbDSecant
        a x r su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 d := by
  unfold quadraticSecant perturbDFace perturbDSecant
    perturbDDetMinusSlope perturbDDetMixedSlope perturbDDetPlusSlope
    perturbDOddSFour perturbDOddDFour perturbFOddMinor perturbFOddMixed
    perturbFOddS perturbFOddSD correlatedCoefficientThree alignedDeterminant
    alignedMixedDeterminant alignedAdjugatePair alignedMixedAdjugatePair
    alignedCrossEnergy alignedEntry00 alignedEntry02 alignedEntry04
    alignedEntry22 alignedEntry24 mixedDeterminantOne
  dsimp only
  ring

def perturbDSlopeA
    (d du u4 dv v4 q11 q13 q33 h11 h13 h33 : ℝ) : ℝ :=
  (-5000000 * d * h11 * h33 + 1000000 * d * h11 * q33 +
      5000000 * d * h13 ^ 2 - 2000000 * d * h13 * q13 +
      1000000 * d * h33 * q11 + 1000000 * d * q11 * q33 -
      1000000 * d * q13 ^ 2 + 3000000 * du * h13 * v4 -
      3000000 * du * h33 * u4 - 1000000 * du * q13 * v4 +
      1000000 * du * q33 * u4 - 3000000 * dv * h11 * v4 +
      3000000 * dv * h13 * u4 + 1000000 * dv * q11 * v4 -
      1000000 * dv * q13 * u4 - 202381 * h11 * h33 -
      62479 * h11 * q33 + 202381 * h13 ^ 2 + 124958 * h13 * q13 -
      62479 * h33 * q11 + 109113 * q11 * q33 - 109113 * q13 ^ 2) /
    2000000

def perturbDSlopeX
    (r su u4 sv v4 q11 q13 q33 h11 h13 h33 : ℝ) : ℝ :=
  (-2500000 * h11 * h33 * r - 121449 * h11 * h33 +
      500000 * h11 * q33 * r - 121449 * h11 * q33 +
      750000 * h11 * sv * v4 + 2500000 * h13 ^ 2 * r +
      121449 * h13 ^ 2 - 1000000 * h13 * q13 * r +
      242898 * h13 * q13 - 750000 * h13 * su * v4 -
      750000 * h13 * sv * u4 + 500000 * h33 * q11 * r -
      121449 * h33 * q11 + 750000 * h33 * su * u4 +
      500000 * q11 * q33 * r + 121449 * q11 * q33 -
      250000 * q11 * sv * v4 - 500000 * q13 ^ 2 * r -
      121449 * q13 ^ 2 + 250000 * q13 * su * v4 +
      250000 * q13 * sv * u4 - 250000 * q33 * su * u4) / 500000

def perturbDSlopeR
    (su du sv dv q11 q13 q33 h11 h13 h33 : ℝ) : ℝ :=
  (-1500000 * du * h13 * sv + 1500000 * du * h33 * su +
      500000 * du * q13 * sv - 500000 * du * q33 * su +
      1500000 * dv * h11 * sv - 1500000 * dv * h13 * su -
      500000 * dv * q11 * sv + 500000 * dv * q13 * su -
      238575 * h11 * h33 - 9 * h11 * q33 + 238575 * h13 ^ 2 +
      18 * h13 * q13 - 9 * h33 * q11 + 79531 * q11 * q33 -
      79531 * q13 ^ 2) / 1000000

def perturbDSlopeSu
    (d su du u4 sv dv v4 q13 q33 h13 h33 : ℝ) : ℝ :=
  -(600000000000 * d * h13 * sv - 300000000000 * d * h33 * su -
      168519000000 * d * h33 - 200000000000 * d * q13 * sv +
      100000000000 * d * q33 * su + 56173000000 * d * q33 -
      78469800000 * du * h33 - 38616200000 * du * q33 +
      200000000000 * du * sv * v4 + 78469800000 * dv * h13 +
      38616200000 * dv * q13 - 200000000000 * dv * su * v4 +
      200000000000 * dv * sv * u4 - 112346000000 * dv * v4 +
      31149400000 * h13 * sv + 31810600000 * h13 * v4 -
      15574700000 * h33 * su - 31810600000 * h33 * u4 -
      8748776231 * h33 + 12495800000 * q13 * sv +
      1800000 * q13 * v4 - 6247900000 * q33 * su -
      1800000 * q33 * u4 - 3509632867 * q33) / 400000000000

def perturbDSlopeDu
    (u4 sv v4 q13 q33 h13 h33 : ℝ) : ℝ :=
  (-39234900000 * h13 * sv + 384766700000 * h13 * v4 -
      384766700000 * h33 * u4 + 22039420377 * h33 -
      19308100000 * q13 * sv + 54975100000 * q13 * v4 -
      54975100000 * q33 * u4 + 10845939013 * q33 +
      100000000000 * sv ^ 2 * u4 - 56173000000 * sv * v4) /
    200000000000

def perturbDSlopeU4
    (sv dv q13 q33 h13 h33 : ℝ) : ℝ :=
  (19238335000 * dv * h13 + 2748755000 * dv * q13 -
      2808650000 * dv * sv - 795265000 * h13 * sv +
      122173497 * h33 - 45000 * q13 * sv - 46346219 * q33 +
      84350000 * sv ^ 2) / 10000000000

def perturbDSlopeSv
    (d sv dv v4 q11 q13 h11 h13 : ℝ) : ℝ :=
  (1500000000000 * d * h11 * sv + 807225000000 * d * h11 -
      1685190000000 * d * h13 - 500000000000 * d * q11 * sv -
      269075000000 * d * q11 + 561730000000 * d * q13 +
      392349000000 * dv * h11 + 193081000000 * dv * q11 -
      80889120000 * dv + 77873500000 * h11 * sv +
      159053000000 * h11 * v4 + 41907624025 * h11 -
      117010321940 * h13 + 31239500000 * q11 * sv +
      9000000 * q11 * v4 + 16811536925 * q11 -
      38354901140 * q13 + 2429280000 * sv - 9476385100 * v4 +
      1307317032) / 2000000000000

def perturbDSlopeDv
    (v4 q11 q13 h11 h13 : ℝ) : ℝ :=
  -(1923833500000 * h11 * v4 - 105571307175 * h11 -
      166834922115 * h13 + 274875500000 * q11 * v4 -
      51953270075 * q11 + 14647623065 * q13 -
      157770296450 * v4 + 21765239964) / 1000000000000

def perturbDSlopeV4
    (q11 q13 h11 h13 : ℝ) : ℝ :=
  -(25821089330000 * h11 + 4886939880000 * h13 +
      6134252490000 * q11 - 1853848760000 * q13 -
      2501489688451) / 400000000000000

def perturbDSlopeQ11
    (d q33 h33 : ℝ) : ℝ :=
  (-439800800000000 * d * h33 + 1758967200000000 * d * q33 -
      115842169000000 * d - 192076575850400 * h33 +
      9616384357600 * q33 + 11974238869087) / 1600000000000000

def perturbDSlopeQ13
    (d q13 h13 : ℝ) : ℝ :=
  -(-1374377500000000 * d * h13 + 2748386250000000 * d * q13 +
      172358177875000 * d - 600239299532500 * h13 +
      15025600558750 * q13 + 30898677429043) / 2500000000000000

def perturbDSlopeQ33
    (d h11 : ℝ) : ℝ :=
  -(2199004000000000 * d * h11 - 932640655000000 * d +
      960382879252000 * h11 - 49958042318677) / 8000000000000000

def perturbDSlopeH11
    (d h33 : ℝ) : ℝ :=
  -(21986500000000000 * d * h33 - 1008662709000000 * d +
      419056710860000 * h33 + 178963854326503) / 8000000000000000

def perturbDSlopeH13
    (d h13 : ℝ) : ℝ :=
  (3435390625000000 * d * h13 - 467017233187500 * d +
      65477611071875 * h13 + 31705832257427) / 1250000000000000

def perturbDSlopeH33
    (d : ℝ) : ℝ :=
  (5312653231000000 * d - 259508104893067) / 40000000000000000

def perturbDSlopeD : ℝ :=
  1225116380433 / 400000000000000

/-! The two broadest `d`-secant slopes retain their correlated cancellation by
moving coordinatewise to a single exact corner. -/

def perturbDXStageR
    (q11 q13 q33 h11 h13 h33 : ℝ) : ℝ :=
  (2500000 * h13 ^ 2 - 2500000 * h11 * h33 +
      500000 * q33 * h11 - 1000000 * q13 * h13 -
      500000 * q13 ^ 2 + 500000 * q11 * h33 +
      500000 * q11 * q33) / 500000

def perturbDXStageSu
    (u4 v4 q13 q33 h13 h33 : ℝ) : ℝ :=
  (-750000 * v4 * h13 + 250000 * v4 * q13 +
      750000 * u4 * h33 - 250000 * u4 * q33) / 500000

def perturbDXStageU4
    (sv q13 q33 h13 h33 : ℝ) : ℝ :=
  (-750000 * sv * h13 + 250000 * sv * q13 +
      421260 * h33 - 140420 * q33) / 500000

def perturbDXStageSv
    (v4 q11 q13 h11 h13 : ℝ) : ℝ :=
  (750000 * v4 * h11 - 250000 * v4 * q11 -
      105750 * h13 + 35250 * q13) / 500000

def perturbDXStageV4
    (q11 q13 h11 h13 : ℝ) : ℝ :=
  (-421260 * h13 + 403770 * h11 + 140420 * q13 -
      134590 * q11) / 500000

def perturbDXStageQ11 (q33 h33 : ℝ) : ℝ :=
  (-(185715 / 2) * h33 + (300081 / 2) * q33 + 13459 / 50) / 500000

def perturbDXStageQ13 (q13 h13 : ℝ) : ℝ :=
  (185715 * h13 - (300081 / 2) * q13 - 45247 / 4) / 500000

def perturbDXStageQ33 (h11 : ℝ) : ℝ :=
  (-(185715 / 2) * h11 + 14116059 / 2000) / 500000

def perturbDXStageH11 (h33 : ℝ) : ℝ :=
  (-(528813 / 2) * h33 - 2538327 / 80) / 500000

def perturbDXStageH13 (h13 : ℝ) : ℝ :=
  ((528813 / 2) * h13 - 43709043 / 2000) / 500000

def perturbDXStageH33 : ℝ :=
  (78148953 / 2000) / 500000

theorem perturbDX_telescope
    (r su u4 sv v4 q11 q13 q33 h11 h13 h33 : ℝ) :
    perturbDSlopeX r su u4 sv v4 q11 q13 q33 h11 h13 h33 -
        perturbDSlopeX
          (57183 / 1000000) (56168 / 100000) (141 / 1000)
          (53836 / 100000) (-(2 / 1000)) (179 / 1000)
          (1 / 5) (333 / 1000) (14 / 1000)
          (-(11 / 1000)) (-(117 / 1000)) =
      (r - 57183 / 1000000) *
          perturbDXStageR q11 q13 q33 h11 h13 h33 +
        (su - 56168 / 100000) *
          perturbDXStageSu u4 v4 q13 q33 h13 h33 +
        (u4 - 141 / 1000) *
          perturbDXStageU4 sv q13 q33 h13 h33 +
        (sv - 53836 / 100000) *
          perturbDXStageSv v4 q11 q13 h11 h13 +
        (v4 - (-(2 / 1000))) *
          perturbDXStageV4 q11 q13 h11 h13 +
        (q11 - 179 / 1000) * perturbDXStageQ11 q33 h33 +
        (q13 - 1 / 5) * perturbDXStageQ13 q13 h13 +
        (q33 - 333 / 1000) * perturbDXStageQ33 h11 +
        (h11 - 14 / 1000) * perturbDXStageH11 h33 +
        (h13 - (-(11 / 1000))) * perturbDXStageH13 h13 +
        (h33 - (-(117 / 1000))) * perturbDXStageH33 := by
  unfold perturbDSlopeX perturbDXStageR perturbDXStageSu
    perturbDXStageU4 perturbDXStageSv perturbDXStageV4
    perturbDXStageQ11 perturbDXStageQ13 perturbDXStageQ33
    perturbDXStageH11 perturbDXStageH13 perturbDXStageH33
  ring

def perturbDAStageD
    (q11 q13 q33 h11 h13 h33 : ℝ) : ℝ :=
  (5000000 * h13 ^ 2 - 5000000 * h11 * h33 +
      1000000 * q33 * h11 - 2000000 * q13 * h13 -
      1000000 * q13 ^ 2 + 1000000 * q11 * h33 +
      1000000 * q11 * q33) / 2000000

def perturbDAStageDu
    (u4 v4 q13 q33 h13 h33 : ℝ) : ℝ :=
  (3000000 * v4 * h13 - 1000000 * v4 * q13 -
      3000000 * u4 * h33 + 1000000 * u4 * q33) / 2000000

def perturbDAStageU4
    (dv q13 q33 h13 h33 : ℝ) : ℝ :=
  (3000000 * dv * h13 - 1000000 * dv * q13 -
      50610 * h33 + 16870 * q33) / 2000000

def perturbDAStageDv
    (v4 q11 q13 h11 h13 : ℝ) : ℝ :=
  (-3000000 * v4 * h11 + 1000000 * v4 * q11 +
      432000 * h13 - 144000 * q13) / 2000000

def perturbDAStageV4
    (q11 q13 h11 h13 : ℝ) : ℝ :=
  (50610 * h13 - 167400 * h11 - 16870 * q13 +
      55800 * q11) / 2000000

def perturbDAStageQ11 (q33 h33 : ℝ) : ℝ :=
  (-39162 * h33 + 132430 * q33 - 1116 / 5) / 2000000

def perturbDAStageQ13 (q13 h13 : ℝ) : ℝ :=
  (78324 * h13 - 132430 * q13 - 17240103 / 500) / 2000000

def perturbDAStageQ33 (h11 : ℝ) : ℝ :=
  (-39162 * h11 + 12987667 / 500) / 2000000

def perturbDAStageH11 (h33 : ℝ) : ℝ :=
  (-318966 * h33 - 12312603 / 1000) / 2000000

def perturbDAStageH13 (h13 : ℝ) : ℝ :=
  (318966 * h13 + 90187497 / 2500) / 2000000

def perturbDAStageH33 : ℝ :=
  (-(46790919 / 2500)) / 2000000

theorem perturbDA_telescope
    (d du u4 dv v4 q11 q13 q33 h11 h13 h33 : ℝ) :
    perturbDSlopeA d du u4 dv v4 q11 q13 q33 h11 h13 h33 -
        perturbDSlopeA
          (23317 / 1000000) (1687 / 100000) (144 / 1000)
          (558 / 10000) (-(4 / 1000)) (1778 / 10000)
          (2002 / 10000) (3315 / 10000) (14 / 1000)
          (-(11 / 1000)) (-(117 / 1000)) =
      (d - 23317 / 1000000) *
          perturbDAStageD q11 q13 q33 h11 h13 h33 +
        (du - 1687 / 100000) *
          perturbDAStageDu u4 v4 q13 q33 h13 h33 +
        (u4 - 144 / 1000) *
          perturbDAStageU4 dv q13 q33 h13 h33 +
        (dv - 558 / 10000) *
          perturbDAStageDv v4 q11 q13 h11 h13 +
        (v4 - (-(4 / 1000))) *
          perturbDAStageV4 q11 q13 h11 h13 +
        (q11 - 1778 / 10000) * perturbDAStageQ11 q33 h33 +
        (q13 - 2002 / 10000) * perturbDAStageQ13 q13 h13 +
        (q33 - 3315 / 10000) * perturbDAStageQ33 h11 +
        (h11 - 14 / 1000) * perturbDAStageH11 h33 +
        (h13 - (-(11 / 1000))) * perturbDAStageH13 h13 +
        (h33 - (-(117 / 1000))) * perturbDAStageH33 := by
  unfold perturbDSlopeA perturbDAStageD perturbDAStageDu perturbDAStageU4
    perturbDAStageDv perturbDAStageV4 perturbDAStageQ11
    perturbDAStageQ13 perturbDAStageQ33 perturbDAStageH11
    perturbDAStageH13 perturbDAStageH33
  ring

set_option maxHeartbeats 3000000 in
theorem perturbDSecant_telescope
    (a x r su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 d : ℝ) :
    perturbDSecant
          a x r su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 d -
        perturbDSecant
          (824479 / 1000000) (39761 / 1000000) (49817 / 1000000)
          (56173 / 100000) (1687 / 100000) (18 / 125)
          (10763 / 20000) (279 / 5000) (-(1 / 250))
          (889 / 5000) (1001 / 5000) (663 / 2000)
          (1 / 50) (-(11 / 1000)) (-(117 / 1000))
          (23317 / 1000000) =
      (a - 824479 / 1000000) *
          perturbDSlopeA d du u4 dv v4 q11 q13 q33 h11 h13 h33 +
        (x - 39761 / 1000000) *
          perturbDSlopeX r su u4 sv v4 q11 q13 q33 h11 h13 h33 +
        (r - 49817 / 1000000) *
          perturbDSlopeR su du sv dv q11 q13 q33 h11 h13 h33 +
        (su - 56173 / 100000) *
          perturbDSlopeSu d su du u4 sv dv v4 q13 q33 h13 h33 +
        (du - 1687 / 100000) *
          perturbDSlopeDu u4 sv v4 q13 q33 h13 h33 +
        (u4 - 18 / 125) *
          perturbDSlopeU4 sv dv q13 q33 h13 h33 +
        (sv - 10763 / 20000) *
          perturbDSlopeSv d sv dv v4 q11 q13 h11 h13 +
        (dv - 279 / 5000) *
          perturbDSlopeDv v4 q11 q13 h11 h13 +
        (v4 - (-(1 / 250))) * perturbDSlopeV4 q11 q13 h11 h13 +
        (q11 - 889 / 5000) * perturbDSlopeQ11 d q33 h33 +
        (q13 - 1001 / 5000) * perturbDSlopeQ13 d q13 h13 +
        (q33 - 663 / 2000) * perturbDSlopeQ33 d h11 +
        (h11 - 1 / 50) * perturbDSlopeH11 d h33 +
        (h13 - (-(11 / 1000))) * perturbDSlopeH13 d h13 +
        (h33 - (-(117 / 1000))) * perturbDSlopeH33 d +
        (d - 23317 / 1000000) * perturbDSlopeD := by
  unfold perturbDSecant perturbDDetMinusSlope perturbDDetMixedSlope
    perturbDDetPlusSlope perturbDOddSFour perturbDOddDFour
    perturbFOddMinor perturbFOddMixed perturbFOddS perturbFOddSD
    perturbDSlopeA perturbDSlopeX perturbDSlopeR perturbDSlopeSu
    perturbDSlopeDu perturbDSlopeU4 perturbDSlopeSv perturbDSlopeDv
    perturbDSlopeV4 perturbDSlopeQ11 perturbDSlopeQ13 perturbDSlopeQ33
    perturbDSlopeH11 perturbDSlopeH13 perturbDSlopeH33 perturbDSlopeD
  dsimp only
  ring

set_option maxHeartbeats 3000000 in
theorem perturbDSecant_lower
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (14 / 100000 : ℝ) ≤
      perturbDSecant
        a x r su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 d := by
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
  rcases hbox.q11_mem with ⟨hq11L, hq11U⟩
  rcases hbox.q13_mem with ⟨hq13L, hq13U⟩
  rcases hbox.q33_mem with ⟨hq33L, hq33U⟩
  rcases hbox.h11_mem with ⟨hh11L, hh11U⟩
  rcases hbox.h13_mem with ⟨hh13L, hh13U⟩
  rcases hbox.h33_mem with ⟨hh33L, hh33U⟩
  have haSlope : (16 / 10000 : ℝ) ≤
      perturbDSlopeA d du u4 dv v4 q11 q13 q33 h11 h13 h33 := by
    have hq110 : (0 : ℝ) ≤ q11 := by linarith
    have hq130 : (0 : ℝ) ≤ q13 := by linarith
    have hq330 : (0 : ℝ) ≤ q33 := by linarith
    have hh110 : (0 : ℝ) ≤ h11 := by linarith
    have hnh13L : (9 / 1000 : ℝ) ≤ -h13 := by linarith
    have hnh33L : (117 / 1000 : ℝ) ≤ -h33 := by linarith
    have hnh33U : -h33 ≤ (120 / 1000 : ℝ) := by linarith
    have hnv4L : (2 / 1000 : ℝ) ≤ -v4 := by linarith
    have hnv4U : -v4 ≤ (4 / 1000 : ℝ) := by linarith
    have hh13sqL : (9 / 1000 : ℝ) ^ 2 ≤ h13 ^ 2 := by
      nlinarith only [hnh13L]
    have hh11Nh33 : (14 / 1000 : ℝ) * (117 / 1000) ≤ h11 * (-h33) :=
      nonnegative_product_lower h11 (-h33)
        (14 / 1000) (117 / 1000) hh11L hnh33L (by norm_num) (by linarith)
    have hh11q33 : (14 / 1000 : ℝ) * (3315 / 10000) ≤ h11 * q33 :=
      nonnegative_product_lower h11 q33
        (14 / 1000) (3315 / 10000) hh11L hq33L (by norm_num) hq330
    have hnh13q13 : (9 / 1000 : ℝ) * (1 / 5) ≤ (-h13) * q13 :=
      nonnegative_product_lower (-h13) q13
        (9 / 1000) (1 / 5) hnh13L hq13L (by norm_num) hq130
    have hq13sqU : q13 ^ 2 ≤ (2002 / 10000 : ℝ) ^ 2 := by
      nlinarith only [hq13L, hq13U]
    have hq11Nh33 : q11 * (-h33) ≤
        (179 / 1000 : ℝ) * (120 / 1000) :=
      nonnegative_product_upper q11 (-h33)
        (179 / 1000) (120 / 1000) hq11U hnh33U (by norm_num) (by linarith)
    have hq11q33 : (1778 / 10000 : ℝ) * (3315 / 10000) ≤ q11 * q33 :=
      nonnegative_product_lower q11 q33
        (1778 / 10000) (3315 / 10000) hq11L hq33L (by norm_num) hq330
    have hdSlope : (0 : ℝ) ≤ perturbDAStageD q11 q13 q33 h11 h13 h33 := by
      unfold perturbDAStageD
      nlinarith only [hh13sqL, hh11Nh33, hh11q33, hnh13q13,
        hq13sqU, hq11Nh33, hq11q33]
    have hduSlope : (0 : ℝ) ≤ perturbDAStageDu u4 v4 q13 q33 h13 h33 := by
      have h1 : 0 ≤ (-v4) * (-h13) := mul_nonneg (by linarith) (by linarith)
      have h2 : 0 ≤ (-v4) * q13 := mul_nonneg (by linarith) hq130
      have h3 : 0 ≤ u4 * (-h33) := mul_nonneg (by linarith) (by linarith)
      have h4 : 0 ≤ u4 * q33 := mul_nonneg (by linarith) hq330
      unfold perturbDAStageDu
      nlinarith only [h1, h2, h3, h4]
    have hdvNh13 : (555 / 10000 : ℝ) * (9 / 1000) ≤ dv * (-h13) :=
      nonnegative_product_lower dv (-h13)
        (555 / 10000) (9 / 1000) hdvL hnh13L (by norm_num) (by linarith)
    have hdvq13 : (555 / 10000 : ℝ) * (1 / 5) ≤ dv * q13 :=
      nonnegative_product_lower dv q13
        (555 / 10000) (1 / 5) hdvL hq13L (by norm_num) hq130
    have hu4Slope : perturbDAStageU4 dv q13 q33 h13 h33 ≤ 0 := by
      unfold perturbDAStageU4
      nlinarith only [hdvNh13, hdvq13, hnh33U, hq33U]
    have hnv4h11 : (-v4) * h11 ≤
        (4 / 1000 : ℝ) * (20 / 1000) :=
      nonnegative_product_upper (-v4) h11
        (4 / 1000) (20 / 1000) hnv4U hh11U (by norm_num) hh110
    have hnv4q11 : (2 / 1000 : ℝ) * (1778 / 10000) ≤ (-v4) * q11 :=
      nonnegative_product_lower (-v4) q11
        (2 / 1000) (1778 / 10000) hnv4L hq11L (by norm_num) hq110
    have hdvSlope : perturbDAStageDv v4 q11 q13 h11 h13 ≤ 0 := by
      unfold perturbDAStageDv
      nlinarith only [hnv4h11, hnv4q11, hnh13L, hq13L]
    have hv4Slope : (0 : ℝ) ≤ perturbDAStageV4 q11 q13 h11 h13 := by
      unfold perturbDAStageV4
      linarith only [hh13L, hh11U, hq13U, hq11L]
    have hq11Slope : (0 : ℝ) ≤ perturbDAStageQ11 q33 h33 := by
      unfold perturbDAStageQ11
      linarith only [hh33U, hq33L]
    have hq13Slope : perturbDAStageQ13 q13 h13 ≤ 0 := by
      unfold perturbDAStageQ13
      linarith only [hh13U, hq13L]
    have hq33Slope : (0 : ℝ) ≤ perturbDAStageQ33 h11 := by
      unfold perturbDAStageQ33
      linarith only [hh11U]
    have hh11Slope : (0 : ℝ) ≤ perturbDAStageH11 h33 := by
      unfold perturbDAStageH11
      linarith only [hh33U]
    have hh13Slope : (0 : ℝ) ≤ perturbDAStageH13 h13 := by
      unfold perturbDAStageH13
      linarith only [hh13L]
    have hh33Slope : perturbDAStageH33 ≤ 0 := by
      norm_num [perturbDAStageH33]
    have hdStep := mul_nonneg (by linarith : 0 ≤ d - 23317 / 1000000) hdSlope
    have hduStep := mul_nonneg (by linarith : 0 ≤ du - 1687 / 100000) hduSlope
    have hu4Step := mul_nonneg_of_nonpos_of_nonpos
      (by linarith : u4 - 144 / 1000 ≤ 0) hu4Slope
    have hdvStep := mul_nonneg_of_nonpos_of_nonpos
      (by linarith : dv - 558 / 10000 ≤ 0) hdvSlope
    have hv4Step := mul_nonneg
      (by linarith : 0 ≤ v4 - (-(4 / 1000))) hv4Slope
    have hq11Step := mul_nonneg
      (by linarith : 0 ≤ q11 - 1778 / 10000) hq11Slope
    have hq13Step := mul_nonneg_of_nonpos_of_nonpos
      (by linarith : q13 - 2002 / 10000 ≤ 0) hq13Slope
    have hq33Step := mul_nonneg
      (by linarith : 0 ≤ q33 - 3315 / 10000) hq33Slope
    have hh11Step := mul_nonneg
      (by linarith : 0 ≤ h11 - 14 / 1000) hh11Slope
    have hh13Step := mul_nonneg
      (by linarith : 0 ≤ h13 - (-(11 / 1000))) hh13Slope
    have hh33Step := mul_nonneg_of_nonpos_of_nonpos
      (by linarith : h33 - (-(117 / 1000)) ≤ 0) hh33Slope
    have htel := perturbDA_telescope d du u4 dv v4 q11 q13 q33 h11 h13 h33
    have hcorner : (16 / 10000 : ℝ) < perturbDSlopeA
        (23317 / 1000000) (1687 / 100000) (144 / 1000)
        (558 / 10000) (-(4 / 1000)) (1778 / 10000)
        (2002 / 10000) (3315 / 10000) (14 / 1000)
        (-(11 / 1000)) (-(117 / 1000)) := by
      norm_num [perturbDSlopeA]
    linarith only [htel, hcorner, hdStep, hduStep, hu4Step, hdvStep,
      hv4Step, hq11Step, hq13Step, hq33Step, hh11Step, hh13Step,
      hh33Step]
  have hxSlope :
      perturbDSlopeX r su u4 sv v4 q11 q13 q33 h11 h13 h33 ≤
        (-9 / 1000 : ℝ) := by
    have hq110 : (0 : ℝ) ≤ q11 := by linarith
    have hq130 : (0 : ℝ) ≤ q13 := by linarith
    have hq330 : (0 : ℝ) ≤ q33 := by linarith
    have hh110 : (0 : ℝ) ≤ h11 := by linarith
    have hnh13L : (9 / 1000 : ℝ) ≤ -h13 := by linarith
    have hnh13U : -h13 ≤ (11 / 1000 : ℝ) := by linarith
    have hnh33L : (117 / 1000 : ℝ) ≤ -h33 := by linarith
    have hnh33U : -h33 ≤ (120 / 1000 : ℝ) := by linarith
    have hnv4L : (2 / 1000 : ℝ) ≤ -v4 := by linarith
    have hnv4U : -v4 ≤ (4 / 1000 : ℝ) := by linarith
    have hh13sqL : (9 / 1000 : ℝ) ^ 2 ≤ h13 ^ 2 := by
      nlinarith only [hnh13L]
    have hh11Nh33 : (14 / 1000 : ℝ) * (117 / 1000) ≤ h11 * (-h33) :=
      nonnegative_product_lower h11 (-h33)
        (14 / 1000) (117 / 1000) hh11L hnh33L (by norm_num) (by linarith)
    have hh11q33 : (14 / 1000 : ℝ) * (3315 / 10000) ≤ h11 * q33 :=
      nonnegative_product_lower h11 q33
        (14 / 1000) (3315 / 10000) hh11L hq33L (by norm_num) hq330
    have hnh13q13 : (9 / 1000 : ℝ) * (1 / 5) ≤ (-h13) * q13 :=
      nonnegative_product_lower (-h13) q13
        (9 / 1000) (1 / 5) hnh13L hq13L (by norm_num) hq130
    have hq13sqU : q13 ^ 2 ≤ (2002 / 10000 : ℝ) ^ 2 := by
      nlinarith only [hq13L, hq13U]
    have hq11Nh33 : q11 * (-h33) ≤
        (179 / 1000 : ℝ) * (120 / 1000) :=
      nonnegative_product_upper q11 (-h33)
        (179 / 1000) (120 / 1000) hq11U hnh33U (by norm_num) (by linarith)
    have hq11q33 : (1778 / 10000 : ℝ) * (3315 / 10000) ≤ q11 * q33 :=
      nonnegative_product_lower q11 q33
        (1778 / 10000) (3315 / 10000) hq11L hq33L (by norm_num) hq330
    have hrSlope : (0 : ℝ) ≤ perturbDXStageR q11 q13 q33 h11 h13 h33 := by
      unfold perturbDXStageR
      nlinarith only [hh13sqL, hh11Nh33, hh11q33, hnh13q13,
        hq13sqU, hq11Nh33, hq11q33]
    have hsuSlope : perturbDXStageSu u4 v4 q13 q33 h13 h33 ≤ 0 := by
      have h1 : 0 ≤ (-v4) * (-h13) := mul_nonneg (by linarith) (by linarith)
      have h2 : 0 ≤ (-v4) * q13 := mul_nonneg (by linarith) hq130
      have h3 : 0 ≤ u4 * (-h33) := mul_nonneg (by linarith) (by linarith)
      have h4 : 0 ≤ u4 * q33 := mul_nonneg (by linarith) hq330
      unfold perturbDXStageSu
      nlinarith only [h1, h2, h3, h4]
    have hnh13sv : (-h13) * sv ≤
        (11 / 1000 : ℝ) * (53836 / 100000) :=
      nonnegative_product_upper (-h13) sv
        (11 / 1000) (53836 / 100000) hnh13U hsvU (by norm_num) (by linarith)
    have hq13sv : q13 * sv ≤
        (2002 / 10000 : ℝ) * (53836 / 100000) :=
      nonnegative_product_upper q13 sv
        (2002 / 10000) (53836 / 100000) hq13U hsvU (by norm_num) (by linarith)
    have hu4Slope : perturbDXStageU4 sv q13 q33 h13 h33 ≤ 0 := by
      unfold perturbDXStageU4
      nlinarith only [hnh13sv, hq13sv, hnh33L, hq33L]
    have hnv4h11 : (-v4) * h11 ≤
        (4 / 1000 : ℝ) * (20 / 1000) :=
      nonnegative_product_upper (-v4) h11
        (4 / 1000) (20 / 1000) hnv4U hh11U (by norm_num) hh110
    have hnv4q11 : (2 / 1000 : ℝ) * (1778 / 10000) ≤ (-v4) * q11 :=
      nonnegative_product_lower (-v4) q11
        (2 / 1000) (1778 / 10000) hnv4L hq11L (by norm_num) hq110
    have hsvSlope : (0 : ℝ) ≤ perturbDXStageSv v4 q11 q13 h11 h13 := by
      unfold perturbDXStageSv
      nlinarith only [hnv4h11, hnv4q11, hnh13L, hq13L]
    have hv4Slope : (0 : ℝ) ≤ perturbDXStageV4 q11 q13 h11 h13 := by
      unfold perturbDXStageV4
      linarith only [hh13U, hh11L, hq13L, hq11U]
    have hq11Slope : (0 : ℝ) ≤ perturbDXStageQ11 q33 h33 := by
      unfold perturbDXStageQ11
      linarith only [hh33U, hq33L]
    have hq13Slope : perturbDXStageQ13 q13 h13 ≤ 0 := by
      unfold perturbDXStageQ13
      linarith only [hh13U, hq13L]
    have hq33Slope : (0 : ℝ) ≤ perturbDXStageQ33 h11 := by
      unfold perturbDXStageQ33
      linarith only [hh11U]
    have hh11Slope : perturbDXStageH11 h33 ≤ 0 := by
      unfold perturbDXStageH11
      linarith only [hh33L]
    have hh13Slope : perturbDXStageH13 h13 ≤ 0 := by
      unfold perturbDXStageH13
      linarith only [hh13U]
    have hh33Slope : (0 : ℝ) ≤ perturbDXStageH33 := by
      norm_num [perturbDXStageH33]
    have hrStep := mul_nonpos_of_nonpos_of_nonneg
      (by linarith : r - 57183 / 1000000 ≤ 0) hrSlope
    have hsuStep := mul_nonpos_of_nonneg_of_nonpos
      (by linarith : 0 ≤ su - 56168 / 100000) hsuSlope
    have hu4Step := mul_nonpos_of_nonneg_of_nonpos
      (by linarith : 0 ≤ u4 - 141 / 1000) hu4Slope
    have hsvStep := mul_nonpos_of_nonpos_of_nonneg
      (by linarith : sv - 53836 / 100000 ≤ 0) hsvSlope
    have hv4Step := mul_nonpos_of_nonpos_of_nonneg
      (by linarith : v4 - (-(2 / 1000)) ≤ 0) hv4Slope
    have hq11Step := mul_nonpos_of_nonpos_of_nonneg
      (by linarith : q11 - 179 / 1000 ≤ 0) hq11Slope
    have hq13Step := mul_nonpos_of_nonneg_of_nonpos
      (by linarith : 0 ≤ q13 - 1 / 5) hq13Slope
    have hq33Step := mul_nonpos_of_nonpos_of_nonneg
      (by linarith : q33 - 333 / 1000 ≤ 0) hq33Slope
    have hh11Step := mul_nonpos_of_nonneg_of_nonpos
      (by linarith : 0 ≤ h11 - 14 / 1000) hh11Slope
    have hh13Step := mul_nonpos_of_nonneg_of_nonpos
      (by linarith : 0 ≤ h13 - (-(11 / 1000))) hh13Slope
    have hh33Step := mul_nonpos_of_nonpos_of_nonneg
      (by linarith : h33 - (-(117 / 1000)) ≤ 0) hh33Slope
    have htel := perturbDX_telescope
      r su u4 sv v4 q11 q13 q33 h11 h13 h33
    have hcorner : perturbDSlopeX
        (57183 / 1000000) (56168 / 100000) (141 / 1000)
        (53836 / 100000) (-(2 / 1000)) (179 / 1000)
        (1 / 5) (333 / 1000) (14 / 1000)
        (-(11 / 1000)) (-(117 / 1000)) < (-9 / 1000 : ℝ) := by
      norm_num [perturbDSlopeX]
    linarith only [htel, hcorner, hrStep, hsuStep, hu4Step, hsvStep,
      hv4Step, hq11Step, hq13Step, hq33Step, hh11Step, hh13Step,
      hh33Step]
  have hrSlope : (1 / 1000 : ℝ) ≤
      perturbDSlopeR su du sv dv q11 q13 q33 h11 h13 h33 := by
    have hsu0 : (0 : ℝ) ≤ su := by linarith
    have hsv0 : (0 : ℝ) ≤ sv := by linarith
    have hq110 : (0 : ℝ) ≤ q11 := by linarith
    have hq130 : (0 : ℝ) ≤ q13 := by linarith
    have hq330 : (0 : ℝ) ≤ q33 := by linarith
    have hnh13L : (9 / 1000 : ℝ) ≤ -h13 := by linarith
    have hnh13U : -h13 ≤ (11 / 1000 : ℝ) := by linarith
    have hnh33L : (117 / 1000 : ℝ) ≤ -h33 := by linarith
    have hnh33U : -h33 ≤ (120 / 1000 : ℝ) := by linarith
    have hnh13svL : (9 / 1000 : ℝ) * (53815 / 100000) ≤ (-h13) * sv :=
      nonnegative_product_lower (-h13) sv
        (9 / 1000) (53815 / 100000)
        hnh13L hsvL (by norm_num) hsv0
    have hduNh13sv : (1687 / 100000 : ℝ) *
        ((9 / 1000) * (53815 / 100000)) ≤ du * ((-h13) * sv) :=
      nonnegative_product_lower du ((-h13) * sv)
        (1687 / 100000) ((9 / 1000) * (53815 / 100000))
        hduL hnh13svL (by norm_num) (by positivity)
    have hnh33suU : (-h33) * su ≤
        (120 / 1000 : ℝ) * (56173 / 100000) :=
      nonnegative_product_upper (-h33) su
        (120 / 1000) (56173 / 100000)
        hnh33U hsuU (by norm_num) hsu0
    have hduNh33su : du * ((-h33) * su) ≤
        (1692 / 100000 : ℝ) * ((120 / 1000) * (56173 / 100000)) :=
      nonnegative_product_upper du ((-h33) * su)
        (1692 / 100000) ((120 / 1000) * (56173 / 100000))
        hduU hnh33suU (by norm_num) (by positivity)
    have hq13svL : (1 / 5 : ℝ) * (53815 / 100000) ≤ q13 * sv :=
      nonnegative_product_lower q13 sv
        (1 / 5) (53815 / 100000)
        hq13L hsvL (by norm_num) hsv0
    have hduQ13sv : (1687 / 100000 : ℝ) *
        ((1 / 5) * (53815 / 100000)) ≤ du * (q13 * sv) :=
      nonnegative_product_lower du (q13 * sv)
        (1687 / 100000) ((1 / 5) * (53815 / 100000))
        hduL hq13svL (by norm_num) (by positivity)
    have hq33suU : q33 * su ≤
        (333 / 1000 : ℝ) * (56173 / 100000) :=
      nonnegative_product_upper q33 su
        (333 / 1000) (56173 / 100000)
        hq33U hsuU (by norm_num) hsu0
    have hduQ33su : du * (q33 * su) ≤
        (1692 / 100000 : ℝ) * ((333 / 1000) * (56173 / 100000)) :=
      nonnegative_product_upper du (q33 * su)
        (1692 / 100000) ((333 / 1000) * (56173 / 100000))
        hduU hq33suU (by norm_num) (by positivity)
    have hh11svL : (14 / 1000 : ℝ) * (53815 / 100000) ≤ h11 * sv :=
      nonnegative_product_lower h11 sv
        (14 / 1000) (53815 / 100000)
        hh11L hsvL (by norm_num) hsv0
    have hdvH11sv : (555 / 10000 : ℝ) *
        ((14 / 1000) * (53815 / 100000)) ≤ dv * (h11 * sv) :=
      nonnegative_product_lower dv (h11 * sv)
        (555 / 10000) ((14 / 1000) * (53815 / 100000))
        hdvL hh11svL (by norm_num) (by positivity)
    have hnh13suL : (9 / 1000 : ℝ) * (56168 / 100000) ≤ (-h13) * su :=
      nonnegative_product_lower (-h13) su
        (9 / 1000) (56168 / 100000)
        hnh13L hsuL (by norm_num) hsu0
    have hdvNh13su : (555 / 10000 : ℝ) *
        ((9 / 1000) * (56168 / 100000)) ≤ dv * ((-h13) * su) :=
      nonnegative_product_lower dv ((-h13) * su)
        (555 / 10000) ((9 / 1000) * (56168 / 100000))
        hdvL hnh13suL (by norm_num) (by positivity)
    have hq11svU : q11 * sv ≤
        (179 / 1000 : ℝ) * (53836 / 100000) :=
      nonnegative_product_upper q11 sv
        (179 / 1000) (53836 / 100000)
        hq11U hsvU (by norm_num) hsv0
    have hdvQ11sv : dv * (q11 * sv) ≤
        (558 / 10000 : ℝ) * ((179 / 1000) * (53836 / 100000)) :=
      nonnegative_product_upper dv (q11 * sv)
        (558 / 10000) ((179 / 1000) * (53836 / 100000))
        hdvU hq11svU (by norm_num) (by positivity)
    have hq13suL : (1 / 5 : ℝ) * (56168 / 100000) ≤ q13 * su :=
      nonnegative_product_lower q13 su
        (1 / 5) (56168 / 100000)
        hq13L hsuL (by norm_num) hsu0
    have hdvQ13su : (555 / 10000 : ℝ) *
        ((1 / 5) * (56168 / 100000)) ≤ dv * (q13 * su) :=
      nonnegative_product_lower dv (q13 * su)
        (555 / 10000) ((1 / 5) * (56168 / 100000))
        hdvL hq13suL (by norm_num) (by positivity)
    have hh11Nh33 : (14 / 1000 : ℝ) * (117 / 1000) ≤ h11 * (-h33) :=
      nonnegative_product_lower h11 (-h33)
        (14 / 1000) (117 / 1000)
        hh11L hnh33L (by norm_num) (by linarith)
    have hh11q33 : h11 * q33 ≤
        (20 / 1000 : ℝ) * (333 / 1000) :=
      nonnegative_product_upper h11 q33
        (20 / 1000) (333 / 1000)
        hh11U hq33U (by norm_num) hq330
    have hnh13sqL : (9 / 1000 : ℝ) ^ 2 ≤ (-h13) ^ 2 := by
      nlinarith only [hnh13L]
    have hnh13q13 : (-h13) * q13 ≤
        (11 / 1000 : ℝ) * (2002 / 10000) :=
      nonnegative_product_upper (-h13) q13
        (11 / 1000) (2002 / 10000)
        hnh13U hq13U (by norm_num) hq130
    have hnh33q11 : (117 / 1000 : ℝ) * (1778 / 10000) ≤ (-h33) * q11 :=
      nonnegative_product_lower (-h33) q11
        (117 / 1000) (1778 / 10000)
        hnh33L hq11L (by norm_num) hq110
    have hq11q33 : (1778 / 10000 : ℝ) * (3315 / 10000) ≤ q11 * q33 :=
      nonnegative_product_lower q11 q33
        (1778 / 10000) (3315 / 10000)
        hq11L hq33L (by norm_num) hq330
    have hq13sqU : q13 ^ 2 ≤ (2002 / 10000 : ℝ) ^ 2 := by
      nlinarith only [hq13L, hq13U]
    unfold perturbDSlopeR
    nlinarith only [hduNh13sv, hduNh33su, hduQ13sv, hduQ33su,
      hdvH11sv, hdvNh13su, hdvQ11sv, hdvQ13su, hh11Nh33,
      hh11q33, hnh13sqL, hnh13q13, hnh33q11, hq11q33, hq13sqU]
  have hsuSlope :
      perturbDSlopeSu d su du u4 sv dv v4 q13 q33 h13 h33 ≤
        (-9 / 1000 : ℝ) := by
    have hsu0 : (0 : ℝ) ≤ su := by linarith
    have hdu0 : (0 : ℝ) ≤ du := by linarith
    have hu40 : (0 : ℝ) ≤ u4 := by linarith
    have hsv0 : (0 : ℝ) ≤ sv := by linarith
    have hdv0 : (0 : ℝ) ≤ dv := by linarith
    have hq130 : (0 : ℝ) ≤ q13 := by linarith
    have hq330 : (0 : ℝ) ≤ q33 := by linarith
    have hnh13L : (9 / 1000 : ℝ) ≤ -h13 := by linarith
    have hnh13U : -h13 ≤ (11 / 1000 : ℝ) := by linarith
    have hnh33L : (117 / 1000 : ℝ) ≤ -h33 := by linarith
    have hnh33U : -h33 ≤ (120 / 1000 : ℝ) := by linarith
    have hnv4L : (2 / 1000 : ℝ) ≤ -v4 := by linarith
    have hnv4U : -v4 ≤ (4 / 1000 : ℝ) := by linarith
    have h1 : d * (-h13) * sv ≤
        (27183 / 1000000 : ℝ) * (11 / 1000) * (53836 / 100000) :=
      nonnegative_triple_upper d (-h13) sv
        (27183 / 1000000) (11 / 1000) (53836 / 100000)
        hdU hnh13U hsvU (by norm_num) (by norm_num) (by linarith) hsv0
    have h2 : (23317 / 1000000 : ℝ) * (117 / 1000) *
        (56168 / 100000) ≤ d * (-h33) * su :=
      nonnegative_triple_lower d (-h33) su
        (23317 / 1000000) (117 / 1000) (56168 / 100000)
        hdL hnh33L hsuL (by norm_num) (by norm_num) (by linarith) hsu0
    have h3 : (23317 / 1000000 : ℝ) * (117 / 1000) ≤ d * (-h33) :=
      nonnegative_product_lower d (-h33)
        (23317 / 1000000) (117 / 1000)
        hdL hnh33L (by norm_num) (by linarith)
    have h4 : d * q13 * sv ≤
        (27183 / 1000000 : ℝ) * (2002 / 10000) * (53836 / 100000) :=
      nonnegative_triple_upper d q13 sv
        (27183 / 1000000) (2002 / 10000) (53836 / 100000)
        hdU hq13U hsvU (by norm_num) (by norm_num) hq130 hsv0
    have h5 : (23317 / 1000000 : ℝ) * (3315 / 10000) *
        (56168 / 100000) ≤ d * q33 * su :=
      nonnegative_triple_lower d q33 su
        (23317 / 1000000) (3315 / 10000) (56168 / 100000)
        hdL hq33L hsuL (by norm_num) (by norm_num) hq330 hsu0
    have h6 : (23317 / 1000000 : ℝ) * (3315 / 10000) ≤ d * q33 :=
      nonnegative_product_lower d q33
        (23317 / 1000000) (3315 / 10000)
        hdL hq33L (by norm_num) hq330
    have h7 : (1687 / 100000 : ℝ) * (117 / 1000) ≤ du * (-h33) :=
      nonnegative_product_lower du (-h33)
        (1687 / 100000) (117 / 1000)
        hduL hnh33L (by norm_num) (by linarith)
    have h8 : du * q33 ≤ (1692 / 100000 : ℝ) * (333 / 1000) :=
      nonnegative_product_upper du q33
        (1692 / 100000) (333 / 1000)
        hduU hq33U (by norm_num) hq330
    have h9 : du * sv * (-v4) ≤
        (1692 / 100000 : ℝ) * (53836 / 100000) * (4 / 1000) :=
      nonnegative_triple_upper du sv (-v4)
        (1692 / 100000) (53836 / 100000) (4 / 1000)
        hduU hsvU hnv4U (by norm_num) (by norm_num) hsv0 (by linarith)
    have h10 : dv * (-h13) ≤ (558 / 10000 : ℝ) * (11 / 1000) :=
      nonnegative_product_upper dv (-h13)
        (558 / 10000) (11 / 1000)
        hdvU hnh13U (by norm_num) (by linarith)
    have h11 : (555 / 10000 : ℝ) * (1 / 5) ≤ dv * q13 :=
      nonnegative_product_lower dv q13
        (555 / 10000) (1 / 5) hdvL hq13L (by norm_num) hq130
    have h12 : (555 / 10000 : ℝ) * (56168 / 100000) *
        (2 / 1000) ≤ dv * su * (-v4) :=
      nonnegative_triple_lower dv su (-v4)
        (555 / 10000) (56168 / 100000) (2 / 1000)
        hdvL hsuL hnv4L (by norm_num) (by norm_num) hsu0 (by linarith)
    have h13c : (555 / 10000 : ℝ) * (53815 / 100000) *
        (141 / 1000) ≤ dv * sv * u4 :=
      nonnegative_triple_lower dv sv u4
        (555 / 10000) (53815 / 100000) (141 / 1000)
        hdvL hsvL hu4L (by norm_num) (by norm_num) hsv0 hu40
    have h14 : (555 / 10000 : ℝ) * (2 / 1000) ≤ dv * (-v4) :=
      nonnegative_product_lower dv (-v4)
        (555 / 10000) (2 / 1000)
        hdvL hnv4L (by norm_num) (by linarith)
    have h15 : (-h13) * sv ≤ (11 / 1000 : ℝ) * (53836 / 100000) :=
      nonnegative_product_upper (-h13) sv
        (11 / 1000) (53836 / 100000)
        hnh13U hsvU (by norm_num) hsv0
    have h16 : (9 / 1000 : ℝ) * (2 / 1000) ≤ (-h13) * (-v4) :=
      nonnegative_product_lower (-h13) (-v4)
        (9 / 1000) (2 / 1000)
        hnh13L hnv4L (by norm_num) (by linarith)
    have h17 : (117 / 1000 : ℝ) * (56168 / 100000) ≤ (-h33) * su :=
      nonnegative_product_lower (-h33) su
        (117 / 1000) (56168 / 100000)
        hnh33L hsuL (by norm_num) hsu0
    have h18 : (117 / 1000 : ℝ) * (141 / 1000) ≤ (-h33) * u4 :=
      nonnegative_product_lower (-h33) u4
        (117 / 1000) (141 / 1000)
        hnh33L hu4L (by norm_num) hu40
    have h20 : (1 / 5 : ℝ) * (53815 / 100000) ≤ q13 * sv :=
      nonnegative_product_lower q13 sv
        (1 / 5) (53815 / 100000) hq13L hsvL (by norm_num) hsv0
    have h21 : q13 * (-v4) ≤ (2002 / 10000 : ℝ) * (4 / 1000) :=
      nonnegative_product_upper q13 (-v4)
        (2002 / 10000) (4 / 1000)
        hq13U hnv4U (by norm_num) (by linarith)
    have h22 : q33 * su ≤ (333 / 1000 : ℝ) * (56173 / 100000) :=
      nonnegative_product_upper q33 su
        (333 / 1000) (56173 / 100000)
        hq33U hsuU (by norm_num) hsu0
    have h23 : q33 * u4 ≤ (333 / 1000 : ℝ) * (144 / 1000) :=
      nonnegative_product_upper q33 u4
        (333 / 1000) (144 / 1000)
        hq33U hu4U (by norm_num) hu40
    unfold perturbDSlopeSu
    linarith only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
      h11, h12, h13c, h14, h15, h16, h17, h18, hnh33L, h20, h21,
      h22, h23, hq33U]
  have hduSlope : (34 / 1000 : ℝ) ≤
      perturbDSlopeDu u4 sv v4 q13 q33 h13 h33 := by
    have hu40 : (0 : ℝ) ≤ u4 := by linarith
    have hsv0 : (0 : ℝ) ≤ sv := by linarith
    have hq130 : (0 : ℝ) ≤ q13 := by linarith
    have hh130 : h13 ≤ 0 := by linarith
    have hh330 : h33 ≤ 0 := by linarith
    have hsvh13 : sv * h13 ≤
        (53815 / 100000 : ℝ) * (-9 / 1000) :=
      positive_negative_product_upper sv h13
        (53815 / 100000) (-9 / 1000)
        hsvL hh130 (by norm_num) hh13U
    have hnh13v4 : (9 / 1000 : ℝ) * (2 / 1000) ≤ (-h13) * (-v4) :=
      nonnegative_product_lower (-h13) (-v4)
        (9 / 1000) (2 / 1000)
        (by linarith) (by linarith) (by norm_num) (by linarith)
    have hu4h33 : u4 * h33 ≤
        (141 / 1000 : ℝ) * (-117 / 1000) :=
      positive_negative_product_upper u4 h33
        (141 / 1000) (-117 / 1000)
        hu4L hh330 (by norm_num) hh33U
    have hq13sv : q13 * sv ≤
        (2002 / 10000 : ℝ) * (53836 / 100000) :=
      nonnegative_product_upper q13 sv
        (2002 / 10000) (53836 / 100000)
        hq13U hsvU (by norm_num) hsv0
    have hq13v4 : (2002 / 10000 : ℝ) * (-4 / 1000) ≤ q13 * v4 :=
      positive_negative_product_lower q13 v4
        (2002 / 10000) (-4 / 1000)
        hq130 hv4L (by norm_num) hq13U
    have hq33u4 : q33 * u4 ≤
        (333 / 1000 : ℝ) * (144 / 1000) :=
      nonnegative_product_upper q33 u4
        (333 / 1000) (144 / 1000)
        hq33U hu4U (by norm_num) hu40
    have hsvsqL : (53815 / 100000 : ℝ) ^ 2 ≤ sv ^ 2 := by
      nlinarith only [hsv0, hsvL]
    have hsvsqu4 : (53815 / 100000 : ℝ) ^ 2 * (141 / 1000) ≤
        sv ^ 2 * u4 :=
      nonnegative_product_lower (sv ^ 2) u4
        ((53815 / 100000) ^ 2) (141 / 1000)
        hsvsqL hu4L (by norm_num) hu40
    have hsvv4 : sv * v4 ≤
        (53815 / 100000 : ℝ) * (-2 / 1000) :=
      positive_negative_product_upper sv v4
        (53815 / 100000) (-2 / 1000)
        hsvL (by linarith) (by norm_num) hv4U
    unfold perturbDSlopeDu
    nlinarith only [hsvh13, hnh13v4, hu4h33, hh33L, hq13sv,
      hq13v4, hq33u4, hq33L, hsvsqu4, hsvv4]
  have hu4Slope : perturbDSlopeU4 sv dv q13 q33 h13 h33 ≤
      (-6 / 1000 : ℝ) := by
    have hdv0 : (0 : ℝ) ≤ dv := by linarith
    have hsv0 : (0 : ℝ) ≤ sv := by linarith
    have hdvh13 : dv * h13 ≤
        (555 / 10000 : ℝ) * (-9 / 1000) :=
      positive_negative_product_upper dv h13
        (555 / 10000) (-9 / 1000)
        hdvL (by linarith) (by norm_num) hh13U
    have hdvq13 : dv * q13 ≤
        (558 / 10000 : ℝ) * (2002 / 10000) :=
      nonnegative_product_upper dv q13
        (558 / 10000) (2002 / 10000)
        hdvU hq13U (by norm_num) (by linarith)
    have hdvsv : (555 / 10000 : ℝ) * (53815 / 100000) ≤ dv * sv :=
      nonnegative_product_lower dv sv
        (555 / 10000) (53815 / 100000)
        hdvL hsvL (by norm_num) hsv0
    have hsvh13 : (53836 / 100000 : ℝ) * (-11 / 1000) ≤ sv * h13 :=
      positive_negative_product_lower sv h13
        (53836 / 100000) (-11 / 1000)
        hsv0 hh13L (by norm_num) hsvU
    have hq13sv : (1 / 5 : ℝ) * (53815 / 100000) ≤ q13 * sv :=
      nonnegative_product_lower q13 sv
        (1 / 5) (53815 / 100000)
        hq13L hsvL (by norm_num) hsv0
    have hsvsq : sv ^ 2 ≤ (53836 / 100000 : ℝ) ^ 2 := by
      nlinarith only [hsv0, hsvU]
    unfold perturbDSlopeU4
    nlinarith only [hdvh13, hdvq13, hdvsv, hsvh13, hh33U,
      hq13sv, hq33L, hsvsq]
  have hsvSlope : (1 / 1000 : ℝ) ≤
      perturbDSlopeSv d sv dv v4 q11 q13 h11 h13 := by
    have hd0 : (0 : ℝ) ≤ d := by linarith
    have hsv0 : (0 : ℝ) ≤ sv := by linarith
    have hq110 : (0 : ℝ) ≤ q11 := by linarith
    have hh110 : (0 : ℝ) ≤ h11 := by linarith
    have hh11svL : (14 / 1000 : ℝ) * (53815 / 100000) ≤ h11 * sv :=
      nonnegative_product_lower h11 sv
        (14 / 1000) (53815 / 100000)
        hh11L hsvL (by norm_num) hsv0
    have hh11svU : h11 * sv ≤
        (20 / 1000 : ℝ) * (53836 / 100000) :=
      nonnegative_product_upper h11 sv
        (20 / 1000) (53836 / 100000)
        hh11U hsvU (by norm_num) hsv0
    have hdh11sv : (23317 / 1000000 : ℝ) *
        ((14 / 1000) * (53815 / 100000)) ≤ d * (h11 * sv) :=
      nonnegative_product_lower d (h11 * sv)
        (23317 / 1000000) ((14 / 1000) * (53815 / 100000))
        hdL hh11svL (by norm_num) (by positivity)
    have hq11svU : q11 * sv ≤
        (179 / 1000 : ℝ) * (53836 / 100000) :=
      nonnegative_product_upper q11 sv
        (179 / 1000) (53836 / 100000)
        hq11U hsvU (by norm_num) hsv0
    have hdq11sv : d * (q11 * sv) ≤
        (27183 / 1000000 : ℝ) *
          ((179 / 1000) * (53836 / 100000)) :=
      nonnegative_product_upper d (q11 * sv)
        (27183 / 1000000) ((179 / 1000) * (53836 / 100000))
        hdU hq11svU (by norm_num) (by positivity)
    have hdh11 : (23317 / 1000000 : ℝ) * (14 / 1000) ≤ d * h11 :=
      nonnegative_product_lower d h11
        (23317 / 1000000) (14 / 1000)
        hdL hh11L (by norm_num) hh110
    have hdh13 : d * h13 ≤
        (23317 / 1000000 : ℝ) * (-9 / 1000) :=
      positive_negative_product_upper d h13
        (23317 / 1000000) (-9 / 1000)
        hdL (by linarith) (by norm_num) hh13U
    have hdq11 : d * q11 ≤
        (27183 / 1000000 : ℝ) * (179 / 1000) :=
      nonnegative_product_upper d q11
        (27183 / 1000000) (179 / 1000)
        hdU hq11U (by norm_num) hq110
    have hdq13 : (23317 / 1000000 : ℝ) * (1 / 5) ≤ d * q13 :=
      nonnegative_product_lower d q13
        (23317 / 1000000) (1 / 5)
        hdL hq13L (by norm_num) (by linarith)
    have hdvh11 : (555 / 10000 : ℝ) * (14 / 1000) ≤ dv * h11 :=
      nonnegative_product_lower dv h11
        (555 / 10000) (14 / 1000)
        hdvL hh11L (by norm_num) hh110
    have hdvq11 : (555 / 10000 : ℝ) * (1778 / 10000) ≤ dv * q11 :=
      nonnegative_product_lower dv q11
        (555 / 10000) (1778 / 10000)
        hdvL hq11L (by norm_num) hq110
    have hh11v4 : (20 / 1000 : ℝ) * (-4 / 1000) ≤ h11 * v4 :=
      positive_negative_product_lower h11 v4
        (20 / 1000) (-4 / 1000)
        hh110 hv4L (by norm_num) hh11U
    have hq11svL : (1778 / 10000 : ℝ) * (53815 / 100000) ≤ q11 * sv :=
      nonnegative_product_lower q11 sv
        (1778 / 10000) (53815 / 100000)
        hq11L hsvL (by norm_num) hsv0
    have hq11v4 : (179 / 1000 : ℝ) * (-4 / 1000) ≤ q11 * v4 :=
      positive_negative_product_lower q11 v4
        (179 / 1000) (-4 / 1000)
        hq110 hv4L (by norm_num) hq11U
    unfold perturbDSlopeSv
    nlinarith only [hdh11sv, hdh11, hdh13, hdq11sv, hdq11, hdq13,
      hdvh11, hdvq11, hdvU, hh11svL, hh11v4, hh11L, hh13U,
      hq11svL, hq11v4, hq11L, hq13U, hsvL, hv4U]
  have hdvSlope : perturbDSlopeDv v4 q11 q13 h11 h13 ≤
      (-14 / 1000 : ℝ) := by
    have hh110 : (0 : ℝ) ≤ h11 := by linarith
    have hq110 : (0 : ℝ) ≤ q11 := by linarith
    have hh11v4 : (20 / 1000 : ℝ) * (-4 / 1000) ≤ h11 * v4 :=
      positive_negative_product_lower h11 v4
        (20 / 1000) (-4 / 1000)
        hh110 hv4L (by norm_num) hh11U
    have hq11v4 : (179 / 1000 : ℝ) * (-4 / 1000) ≤ q11 * v4 :=
      positive_negative_product_lower q11 v4
        (179 / 1000) (-4 / 1000)
        hq110 hv4L (by norm_num) hq11U
    unfold perturbDSlopeDv
    nlinarith only [hv4U, hq11U, hq13L, hh11U, hh13U,
      hh11v4, hq11v4]
  have hv4Slope : (3 / 1000 : ℝ) ≤
      perturbDSlopeV4 q11 q13 h11 h13 := by
    unfold perturbDSlopeV4
    linarith only [hq11U, hq13L, hh11U, hh13U]
  have hq11Slope : (3 / 100 : ℝ) ≤ perturbDSlopeQ11 d q33 h33 := by
    have hd0 : (0 : ℝ) ≤ d := by linarith
    have hh330 : h33 ≤ 0 := by linarith
    have hdh33 : d * h33 ≤
        (23317 / 1000000 : ℝ) * (-117 / 1000) :=
      positive_negative_product_upper d h33
        (23317 / 1000000) (-117 / 1000)
        hdL hh330 (by norm_num) hh33U
    have hdq33 : (23317 / 1000000 : ℝ) * (3315 / 10000) ≤ d * q33 :=
      nonnegative_product_lower d q33
        (23317 / 1000000) (3315 / 10000)
        hdL hq33L (by norm_num) (by linarith)
    unfold perturbDSlopeQ11
    nlinarith only [hdL, hq33L, hh33U, hdh33, hdq33]
  have hq13Slope : perturbDSlopeQ13 d q13 h13 ≤
      (-22 / 1000 : ℝ) := by
    have hd0 : (0 : ℝ) ≤ d := by linarith
    have hdh13 : (27183 / 1000000 : ℝ) * (-11 / 1000) ≤ d * h13 :=
      positive_negative_product_lower d h13
        (27183 / 1000000) (-11 / 1000)
        hd0 hh13L (by norm_num) hdU
    have hdq13 : (23317 / 1000000 : ℝ) * (1 / 5) ≤ d * q13 :=
      nonnegative_product_lower d q13
        (23317 / 1000000) (1 / 5)
        hdL hq13L (by norm_num) (by linarith)
    unfold perturbDSlopeQ13
    nlinarith only [hdL, hdU, hq13L, hh13L, hh13U, hdh13, hdq13]
  have hq33Slope : (6 / 1000 : ℝ) ≤ perturbDSlopeQ33 d h11 := by
    have hprod : d * h11 ≤
        (27183 / 1000000 : ℝ) * (20 / 1000) :=
      nonnegative_product_upper d h11
        (27183 / 1000000) (20 / 1000)
        hdU hh11U (by norm_num) (by linarith)
    unfold perturbDSlopeQ33
    nlinarith only [hdL, hdU, hh11L, hh11U, hprod]
  have hh11Slope : perturbDSlopeH11 d h33 ≤ (-3 / 1000 : ℝ) := by
    have hd0 : (0 : ℝ) ≤ d := by linarith
    have hprod : (27183 / 1000000 : ℝ) * (-120 / 1000) ≤ d * h33 :=
      positive_negative_product_lower d h33
        (27183 / 1000000) (-120 / 1000)
        hd0 hh33L (by norm_num) hdU
    unfold perturbDSlopeH11
    nlinarith only [hdL, hdU, hh33L, hh33U, hprod]
  have hh13Slope : (12 / 1000 : ℝ) ≤ perturbDSlopeH13 d h13 := by
    have hd0 : (0 : ℝ) ≤ d := by linarith
    have hprod : (27183 / 1000000 : ℝ) * (-11 / 1000) ≤ d * h13 :=
      positive_negative_product_lower d h13
        (27183 / 1000000) (-11 / 1000)
        hd0 hh13L (by norm_num) hdU
    unfold perturbDSlopeH13
    nlinarith only [hdL, hdU, hh13L, hprod]
  have hh33Slope : perturbDSlopeH33 d ≤ (-2 / 1000 : ℝ) := by
    unfold perturbDSlopeH33
    linarith only [hdU]
  have hdSlope : (3 / 1000 : ℝ) ≤ perturbDSlopeD := by
    norm_num [perturbDSlopeD]
  have haStep : 0 ≤ (a - 824479 / 1000000) *
      perturbDSlopeA d du u4 dv v4 q11 q13 q33 h11 h13 h33 :=
    mul_nonneg (by linarith) (by linarith)
  have hxStep : 0 ≤ (x - 39761 / 1000000) *
      perturbDSlopeX r su u4 sv v4 q11 q13 q33 h11 h13 h33 :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  have hrStep : 0 ≤ (r - 49817 / 1000000) *
      perturbDSlopeR su du sv dv q11 q13 q33 h11 h13 h33 :=
    mul_nonneg (by linarith) (by linarith)
  have hsuStep : 0 ≤ (su - 56173 / 100000) *
      perturbDSlopeSu d su du u4 sv dv v4 q13 q33 h13 h33 :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  have hduStep : 0 ≤ (du - 1687 / 100000) *
      perturbDSlopeDu u4 sv v4 q13 q33 h13 h33 :=
    mul_nonneg (by linarith) (by linarith)
  have hu4Step : 0 ≤ (u4 - 18 / 125) *
      perturbDSlopeU4 sv dv q13 q33 h13 h33 :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  have hsvStep : 0 ≤ (sv - 10763 / 20000) *
      perturbDSlopeSv d sv dv v4 q11 q13 h11 h13 :=
    mul_nonneg (by linarith) (by linarith)
  have hdvStep : 0 ≤ (dv - 279 / 5000) *
      perturbDSlopeDv v4 q11 q13 h11 h13 :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  have hv4Step : 0 ≤ (v4 - (-(1 / 250))) *
      perturbDSlopeV4 q11 q13 h11 h13 :=
    mul_nonneg (by linarith) (by linarith)
  have hq11Step : 0 ≤ (q11 - 889 / 5000) * perturbDSlopeQ11 d q33 h33 :=
    mul_nonneg (by linarith) (by linarith)
  have hq13Step : 0 ≤
      (q13 - 1001 / 5000) * perturbDSlopeQ13 d q13 h13 :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  have hq33Step : 0 ≤ (q33 - 663 / 2000) * perturbDSlopeQ33 d h11 :=
    mul_nonneg (by linarith) (by linarith)
  have hh11Step : 0 ≤ (h11 - 1 / 50) * perturbDSlopeH11 d h33 :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  have hh13Step : 0 ≤
      (h13 - (-(11 / 1000))) * perturbDSlopeH13 d h13 :=
    mul_nonneg (by linarith) (by linarith)
  have hh33Step : 0 ≤
      (h33 - (-(117 / 1000))) * perturbDSlopeH33 d :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  have hdStep : 0 ≤ (d - 23317 / 1000000) * perturbDSlopeD :=
    mul_nonneg (by linarith) (by linarith)
  have htel := perturbDSecant_telescope
    a x r su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 d
  have hcorner : (14 / 100000 : ℝ) <
      perturbDSecant
        (824479 / 1000000) (39761 / 1000000) (49817 / 1000000)
        (56173 / 100000) (1687 / 100000) (18 / 125)
        (10763 / 20000) (279 / 5000) (-(1 / 250))
        (889 / 5000) (1001 / 5000) (663 / 2000)
        (1 / 50) (-(11 / 1000)) (-(117 / 1000))
        (23317 / 1000000) := by
    norm_num [perturbDSecant, perturbDDetMinusSlope,
      perturbDDetMixedSlope, perturbDDetPlusSlope, perturbDOddSFour,
      perturbDOddDFour, perturbFOddMinor, perturbFOddMixed,
      perturbFOddS, perturbFOddSD, cornerA, cornerX, cornerR,
      cornerD, corner_d]
  nlinarith only [htel, hcorner, haStep, hxStep, hrStep, hsuStep,
    hduStep, hu4Step, hsvStep, hdvStep, hv4Step, hq11Step, hq13Step,
    hq33Step, hh11Step, hh13Step, hh33Step, hdStep]

set_option maxHeartbeats 3000000 in
theorem correlated_even_unfix_d
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    perturbDFace a x r corner_d f su du u4 sv dv v4
        q11 q13 q33 h11 h13 h33 ≤
      perturbDFace a x r d f su du u4 sv dv v4
        q11 q13 q33 h11 h13 h33 := by
  have hdL := hbox.d_mem.1
  let g : ℝ → ℝ := fun z ↦
    perturbDFace a x r z f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33
  have hslope := perturbDSecant_lower
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hsecFloor : (14 / 100000 : ℝ) ≤ quadraticSecant g d corner_d := by
    rw [show quadraticSecant g d corner_d =
        perturbDSecant a x r su du u4 sv dv v4
          q11 q13 q33 h11 h13 h33 d by
      simpa only [g] using perturb_d_secant_eq
        a x r d f su du u4 sv dv v4 q11 q13 q33 h11 h13 h33]
    exact hslope
  have hsec : (0 : ℝ) ≤ quadraticSecant g d corner_d :=
    le_trans (by norm_num) hsecFloor
  have hid : g d - g corner_d =
      (d - corner_d) * quadraticSecant g d corner_d := by
    unfold g perturbDFace quadraticSecant correlatedCoefficientThree
      alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
      alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00 alignedEntry02
      alignedEntry04 alignedEntry22 alignedEntry24 mixedDeterminantOne
    dsimp only
    ring
  exact quadraticSecant_lower_endpoint g d corner_d
    (by simpa only [corner_d] using hdL) hsec hid

/-! ### The perturbation-`c` secant

The third even move is affine in `c`.  Its slope separates into the same
three determinant/odd-minor pairings as the preceding moves, the `C`-part of
the two adjugate couplings, and the `C`-component of the cross square.
-/

def perturbCDetMinusSlope
    (a r f : ℝ) : ℝ :=
  -(-750000000000 * a * f + 78550000000 * a + 343557500000 * f +
      750000000000 * r ^ 2 - 121449000000 * r + 93195906899) /
    1000000000000

def perturbCDetMixedSlope
    (a r f : ℝ) : ℝ :=
  (-750000000000 * a * f - 78550000000 * a - 343557500000 * f +
      750000000000 * r ^ 2 + 121449000000 * r + 93195906899) /
    1000000000000

def perturbCDetPlusSlope
    (a r f : ℝ) : ℝ :=
  -(-250000000000 * a * f - 78550000000 * a - 343557500000 * f +
      250000000000 * r ^ 2 + 121449000000 * r - 93195906899) /
    1000000000000

def perturbCSecant
    (a r f su u4 sv v4 q11 q13 q33 h11 h13 h33 : ℝ) : ℝ :=
  let o11p := q11 + h11
  let o13p := q13 + h13
  let o33p := q33 + h33
  let o11m := q11 - h11
  let o13m := q13 - h13
  let o33m := q33 - h33
  let oddPlus := perturbFOddMinor o11p o13p o33p
  let oddMixed := perturbFOddMixed o11p o13p o33p o11m o13m o33m
  let oddMinus := perturbFOddMinor o11m o13m o33m
  let ssPlus := perturbFOddS su sv o11p o13p o33p
  let s4Plus := perturbDOddSFour su u4 sv v4 o11p o13p o33p
  let ffPlus := perturbFOddS u4 v4 o11p o13p o33p
  let ssMinus := perturbFOddS su sv o11m o13m o33m
  let s4Minus := perturbDOddSFour su u4 sv v4 o11m o13m o33m
  let ffMinus := perturbFOddS u4 v4 o11m o13m o33m
  perturbCDetMinusSlope a r f * oddMinus +
    perturbCDetMixedSlope a r f * oddMixed +
    perturbCDetPlusSlope a r f * oddPlus -
    ((cornerF + f) * ssPlus - 2 * (cornerR + r) * s4Plus +
      (cornerA + a) * ffPlus) / 4 +
    (f * ssMinus - 2 * r * s4Minus + a * ffMinus) / 2 +
    (v4 * su - u4 * sv) ^ 2 / 4

def perturbCFace
    (a x r c d f su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ) : ℝ :=
  correlatedCoefficientThree
    cornerA cornerX cornerR cornerC cornerD cornerF
    a x r c d f su du u4 sv dv v4 q11 q13 q33 h11 h13 h33

set_option maxHeartbeats 3000000 in
theorem perturb_c_secant_eq
    (a x r c d f su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ) :
    quadraticSecant
        (fun z ↦ perturbCFace a x r z d f su du u4 sv dv v4
          q11 q13 q33 h11 h13 h33)
        c corner_c =
      perturbCSecant a r f su u4 sv v4 q11 q13 q33 h11 h13 h33 := by
  unfold quadraticSecant perturbCFace perturbCSecant
    perturbCDetMinusSlope perturbCDetMixedSlope perturbCDetPlusSlope
    perturbDOddSFour perturbFOddMinor perturbFOddMixed perturbFOddS
    correlatedCoefficientThree alignedDeterminant alignedMixedDeterminant
    alignedAdjugatePair alignedMixedAdjugatePair alignedCrossEnergy
    alignedEntry00 alignedEntry02 alignedEntry04 alignedEntry22 alignedEntry24
    mixedDeterminantOne
  dsimp only
  ring

def perturbCSlopeA
    (f u4 v4 q11 q13 q33 h11 h13 h33 : ℝ) : ℝ :=
  5 * f * h11 * h33 / 2 - f * h11 * q33 / 2 - 5 * f * h13 ^ 2 / 2 +
    f * h13 * q13 - f * h33 * q11 / 2 - f * q11 * q33 / 2 +
    f * q13 ^ 2 / 2 + 1571 * h11 * h33 / 10000 +
    1571 * h11 * q33 / 10000 - 3 * h11 * v4 ^ 2 / 4 -
    1571 * h13 ^ 2 / 10000 - 1571 * h13 * q13 / 5000 +
    3 * h13 * u4 * v4 / 2 + 1571 * h33 * q11 / 10000 -
    3 * h33 * u4 ^ 2 / 4 - 1571 * q11 * q33 / 10000 +
    q11 * v4 ^ 2 / 4 + 1571 * q13 ^ 2 / 10000 -
    q13 * u4 * v4 / 2 + q33 * u4 ^ 2 / 4

def perturbCSlopeR
    (r su u4 sv v4 q11 q13 q33 h11 h13 h33 : ℝ) : ℝ :=
  -5 * h11 * h33 * r / 2 - 734881 * h11 * h33 / 2000000 +
    h11 * q33 * r / 2 - 435979 * h11 * q33 / 2000000 +
    3 * h11 * sv * v4 / 2 + 5 * h13 ^ 2 * r / 2 +
    734881 * h13 ^ 2 / 2000000 - h13 * q13 * r +
    435979 * h13 * q13 / 1000000 - 3 * h13 * su * v4 / 2 -
    3 * h13 * sv * u4 / 2 + h33 * q11 * r / 2 -
    435979 * h33 * q11 / 2000000 + 3 * h33 * su * u4 / 2 +
    q11 * q33 * r / 2 + 535613 * q11 * q33 / 2000000 -
    q11 * sv * v4 / 2 - q13 ^ 2 * r / 2 -
    535613 * q13 ^ 2 / 2000000 + q13 * su * v4 / 2 +
    q13 * sv * u4 / 2 - q33 * su * u4 / 2

def perturbCSlopeSu
    (f su u4 sv v4 q13 q33 h13 h33 : ℝ) : ℝ :=
  3 * f * h13 * sv / 2 - 3 * f * h33 * su / 4 -
    168519 * f * h33 / 400000 - f * q13 * sv / 2 +
    f * q33 * su / 4 + 56173 * f * q33 / 400000 +
    1571 * h13 * sv / 10000 - 392349 * h13 * v4 / 2000000 -
    1571 * h33 * su / 20000 + 392349 * h33 * u4 / 2000000 -
    88247783 * h33 / 2000000000 + 1571 * q13 * sv / 10000 -
    193081 * q13 * v4 / 2000000 - 1571 * q33 * su / 20000 +
    193081 * q33 * u4 / 2000000 - 88247783 * q33 / 2000000000 +
    su * v4 ^ 2 / 4 - sv * u4 * v4 / 2 + 56173 * v4 ^ 2 / 400000

def perturbCSlopeU4
    (u4 sv v4 q13 q33 h13 h33 : ℝ) : ℝ :=
  -392349 * h13 * sv / 2000000 + 3847667 * h13 * v4 / 2000000 -
    3847667 * h33 * u4 / 4000000 - 5663782023 * h33 / 200000000000 -
    193081 * q13 * sv / 2000000 + 549751 * q13 * v4 / 2000000 -
    549751 * q33 * u4 / 4000000 + 6887731813 * q33 / 200000000000 +
    sv ^ 2 * u4 / 4 + 9 * sv ^ 2 / 250 - 56173 * sv * v4 / 200000

def perturbCSlopeSv
    (f sv v4 q11 q13 h11 h13 : ℝ) : ℝ :=
  -3 * f * h11 * sv / 4 - 32289 * f * h11 / 80000 +
    168519 * f * h13 / 200000 + f * q11 * sv / 4 +
    10763 * f * q11 / 80000 - 56173 * f * q13 / 200000 -
    1571 * h11 * sv / 20000 + 392349 * h11 * v4 / 2000000 -
    16908673 * h11 / 400000000 + 11999731 * h13 / 200000000 -
    1571 * q11 * sv / 20000 + 193081 * q11 * v4 / 2000000 -
    16908673 * q11 / 400000000 + 74345951 * q13 / 1000000000 +
    81 * sv / 15625 - 505557 * v4 / 12500000 + 871803 / 312500000

def perturbCSlopeV4
    (v4 q11 q13 h11 h13 : ℝ) : ℝ :=
  -3847667 * h11 * v4 / 4000000 + 4376758967 * h11 / 40000000000 +
    33366984423 * h13 / 200000000000 -
    549751 * q11 * v4 / 4000000 + 2100120843 * q11 / 40000000000 -
    2929524613 * q13 / 200000000000 +
    3155405929 * v4 / 40000000000 - 220807805569 / 10000000000000

def perturbCSlopeQ11 (f q33 h33 : ℝ) : ℝ :=
  549751 * f * h33 / 2000000 - 2198709 * f * q33 / 2000000 +
    115842169 * f / 1600000000 + 610115763553 * h33 / 2000000000000 +
    140414958617 * q33 / 2000000000000 -
    918340720867 / 40000000000000

def perturbCSlopeQ13 (f q13 h13 : ℝ) : ℝ :=
  -549751 * f * h13 / 1000000 + 2198709 * f * q13 / 2000000 +
    1378865423 * f / 20000000000 - 610115763553 * h13 / 1000000000000 -
    140414958617 * q13 / 2000000000000 +
    260123266653483 / 10000000000000000

def perturbCSlopeQ33 (f h11 : ℝ) : ℝ :=
  549751 * f * h11 / 2000000 - 186528131 * f / 1600000000 +
    610115763553 * h11 / 2000000000000 -
    73436568458837 / 10000000000000000

def perturbCSlopeH11 (f h33 : ℝ) : ℝ :=
  43973 * f * h33 / 16000 - 1008662709 * f / 8000000000 -
    150341892573 * h33 / 2000000000000 +
    311762023899339 / 4000000000000000

def perturbCSlopeH13 (f h13 : ℝ) : ℝ :=
  -43973 * f * h13 / 16000 + 7472275731 * f / 20000000000 +
    150341892573 * h13 / 2000000000000 -
    913511197726721 / 10000000000000000

def perturbCSlopeF (h33 : ℝ) : ℝ :=
  -5312653231 * h33 / 40000000000 -
    7440920660703 / 400000000000000

def perturbCSlopeH33 : ℝ :=
  4381224233357 / 10000000000000000

set_option maxHeartbeats 3000000 in
theorem perturbCSecant_telescope
    (a r f su u4 sv v4 q11 q13 q33 h11 h13 h33 : ℝ) :
    perturbCSecant a r f su u4 sv v4 q11 q13 q33 h11 h13 h33 -
        perturbCSecant
          (824479 / 1000000) (49817 / 1000000) (4411 / 25000)
          (56173 / 100000) (18 / 125) (10763 / 20000) (-(1 / 250))
          (889 / 5000) (1001 / 5000) (663 / 2000)
          (1 / 50) (-(11 / 1000)) (-(117 / 1000)) =
      (a - 824479 / 1000000) *
          perturbCSlopeA f u4 v4 q11 q13 q33 h11 h13 h33 +
      (r - 49817 / 1000000) *
          perturbCSlopeR r su u4 sv v4 q11 q13 q33 h11 h13 h33 +
      (su - 56173 / 100000) *
          perturbCSlopeSu f su u4 sv v4 q13 q33 h13 h33 +
      (u4 - 18 / 125) *
          perturbCSlopeU4 u4 sv v4 q13 q33 h13 h33 +
      (sv - 10763 / 20000) *
          perturbCSlopeSv f sv v4 q11 q13 h11 h13 +
      (v4 - (-(1 / 250))) *
          perturbCSlopeV4 v4 q11 q13 h11 h13 +
      (q11 - 889 / 5000) * perturbCSlopeQ11 f q33 h33 +
      (q13 - 1001 / 5000) * perturbCSlopeQ13 f q13 h13 +
      (q33 - 663 / 2000) * perturbCSlopeQ33 f h11 +
      (h11 - 1 / 50) * perturbCSlopeH11 f h33 +
      (h13 - (-(11 / 1000))) * perturbCSlopeH13 f h13 +
      (f - 4411 / 25000) * perturbCSlopeF h33 +
      (h33 - (-(117 / 1000))) * perturbCSlopeH33 := by
  unfold perturbCSecant perturbCDetMinusSlope perturbCDetMixedSlope
    perturbCDetPlusSlope perturbFOddMinor perturbFOddMixed perturbFOddS
    perturbDOddSFour perturbCSlopeA perturbCSlopeR perturbCSlopeSu
    perturbCSlopeU4 perturbCSlopeSv perturbCSlopeV4 perturbCSlopeQ11
    perturbCSlopeQ13 perturbCSlopeQ33 perturbCSlopeH11 perturbCSlopeH13
    perturbCSlopeF perturbCSlopeH33
  dsimp only
  ring

theorem perturbCA_telescope
    (f u4 v4 q11 q13 q33 h11 h13 h33 : ℝ) :
    perturbCSlopeA f u4 v4 q11 q13 q33 h11 h13 h33 -
        perturbCSlopeA
          (4411 / 25000) (18 / 125) (-(1 / 250))
          (889 / 5000) (1001 / 5000) (663 / 2000)
          (7 / 500) (-(11 / 1000)) (-(117 / 1000)) =
      (f - 4411 / 25000) *
          (-(-5 * h11 * h33 + h11 * q33 + 5 * h13 ^ 2 -
            2 * h13 * q13 + h33 * q11 + q11 * q33 - q13 ^ 2) / 2) +
      (u4 - 18 / 125) *
          (-(-750 * h13 * v4 + 375 * h33 * u4 + 54 * h33 +
            250 * q13 * v4 - 125 * q33 * u4 - 18 * q33) / 500) +
      (v4 - (-(1 / 250))) *
          ((-750 * h11 * v4 + 3 * h11 + 216 * h13 +
            250 * q11 * v4 - q11 - 72 * q13) / 1000) +
      (q11 - 889 / 5000) *
          (-(-17220 * h33 + 61330 * q33 - 1) / 250000) +
      (q13 - 1001 / 5000) *
          ((-17220000 * h13 + 30665000 * q13 + 6175133) / 125000000) +
      (q33 - 663 / 2000) * ((8610000 * h11 - 4804237) / 125000000) +
      (h11 - 7 / 500) * (3 * (4985000 * h33 + 190181) / 25000000) +
      (h13 - (-(11 / 1000))) *
          (-3 * (24925000 * h13 + 910973) / 125000000) +
      (h33 - (-(117 / 1000))) * (158427 / 31250000) := by
  unfold perturbCSlopeA
  ring

theorem perturbCR_telescope
    (r su u4 sv v4 q11 q13 q33 h11 h13 h33 : ℝ) :
    perturbCSlopeR r su u4 sv v4 q11 q13 q33 h11 h13 h33 -
        perturbCSlopeR
          (57183 / 1000000) (56168 / 100000) (141 / 1000)
          (53836 / 100000) (-(1 / 500)) (179 / 1000)
          (1 / 5) (333 / 1000) (7 / 500)
          (-(11 / 1000)) (-(117 / 1000)) =
      (r - 57183 / 1000000) *
          ((-5 * h11 * h33 + h11 * q33 + 5 * h13 ^ 2 -
            2 * h13 * q13 + h33 * q11 + q11 * q33 - q13 ^ 2) / 2) +
      (su - 56168 / 100000) *
          ((-3 * h13 * v4 + 3 * h33 * u4 + q13 * v4 - q33 * u4) / 2) +
      (u4 - 141 / 1000) *
          ((-37500 * h13 * sv + 21063 * h33 + 12500 * q13 * sv -
            7021 * q33) / 25000) +
      (sv - 53836 / 100000) *
          (-(-3000 * h11 * v4 + 423 * h13 + 1000 * q11 * v4 -
            141 * q13) / 2000) +
      (v4 - (-(1 / 500))) *
          (-(-40377 * h11 + 42126 * h13 + 13459 * q11 -
            14042 * q13) / 50000) +
      (q11 - 179 / 1000) *
          ((-4734950 * h33 + 7409950 * q33 + 13459) / 25000000) +
      (q13 - 1 / 5) *
          (-(-3787960 * h13 + 2963980 * q13 + 218869) / 10000000) +
      (q33 - 333 / 1000) *
          (-(94699000 * h11 - 6728401) / 500000000) +
      (h11 - 7 / 500) *
          (-(255199000 * h33 + 32342307) / 500000000) +
      (h13 - (-(11 / 1000))) *
          (7 * (36457000 * h13 - 3002377) / 500000000) +
      (h33 - (-(117 / 1000))) * (38873753 / 500000000) := by
  unfold perturbCSlopeR
  ring

theorem perturbCSu_telescope
    (f su u4 sv v4 q13 q33 h13 h33 : ℝ) :
    perturbCSlopeSu f su u4 sv v4 q13 q33 h13 h33 -
        perturbCSlopeSu
          (4411 / 25000) (56168 / 100000) (141 / 1000)
          (10763 / 20000) (-(1 / 500)) (1 / 5) (333 / 1000)
          (-(11 / 1000)) (-(117 / 1000)) =
      (f - 4411 / 25000) *
          (-(-600000 * h13 * sv + 300000 * h33 * su + 168519 * h33 +
            200000 * q13 * sv - 100000 * q33 * su - 56173 * q33) / 400000) +
      (su - 56168 / 100000) *
          (-(5272 * h33 + 861 * q33 - 6250 * v4 ^ 2) / 25000) +
      (u4 - 141 / 1000) *
          ((392349 * h33 + 193081 * q33 - 1000000 * sv * v4) / 2000000) +
      (sv - 10763 / 20000) *
          ((21088 * h13 + 3444 * q13 - 3525 * v4) / 50000) +
      (v4 - (-(1 / 500))) *
          (-(9808725 * h13 + 4827025 * q13 - 14042625 * v4 +
            1925064) / 50000000) +
      (q13 - 1 / 5) * (37260853 / 1000000000) +
      (q33 - 333 / 1000) * (-(250780299 / 10000000000)) +
      (h13 - (-(11 / 1000))) * (227362493 / 1000000000) +
      (h33 - (-(117 / 1000))) * (-(2092440963 / 10000000000)) := by
  unfold perturbCSlopeSu
  ring

theorem perturbCU4_telescope
    (u4 sv v4 q13 q33 h13 h33 : ℝ) :
    perturbCSlopeU4 u4 sv v4 q13 q33 h13 h33 -
        perturbCSlopeU4
          (141 / 1000) (10763 / 20000) (-(1 / 500))
          (1001 / 5000) (663 / 2000) (-(9 / 1000)) (-(117 / 1000)) =
      (u4 - 141 / 1000) *
          (-(3847667 * h33 + 549751 * q33 - 1000000 * sv ^ 2) / 4000000) +
      (sv - 10763 / 20000) *
          (-(3138792 * h13 + 1544648 * q13 - 1140000 * sv +
            4493840 * v4 - 613491) / 16000000) +
      (v4 - (-(1 / 500))) *
          ((7695334000 * h13 + 1099502000 * q13 - 604589999) / 4000000000) +
      (q13 - 1001 / 5000) * (-(2100120843 / 40000000000)) +
      (q33 - 663 / 2000) * (3011987263 / 200000000000) +
      (h13 - (-(9 / 1000))) * (-(4376758967 / 40000000000)) +
      (h33 - (-(117 / 1000))) * (-(32789834373 / 200000000000)) := by
  unfold perturbCSlopeU4
  ring

theorem perturbCSv_telescope
    (f sv v4 q11 q13 h11 h13 : ℝ) :
    perturbCSlopeSv f sv v4 q11 q13 h11 h13 -
        perturbCSlopeSv
          (4411 / 25000) (10763 / 20000) (-(1 / 250))
          (889 / 5000) (1001 / 5000) (7 / 500) (-(9 / 1000)) =
      (f - 4411 / 25000) *
          ((-300000 * h11 * sv - 161445 * h11 + 337038 * h13 +
            100000 * q11 * sv + 53815 * q11 - 112346 * q13) / 400000) +
      (sv - 10763 / 20000) *
          (-(26360 * h11 + 4305 * q11 - 648) / 125000) +
      (v4 - (-(1 / 250))) *
          ((9808725 * h11 + 4827025 * q11 - 2022228) / 50000000) +
      (q11 - 889 / 5000) * (-(18726967 / 500000000)) +
      (q13 - 1001 / 5000) * (30987663 / 1250000000) +
      (h11 - 7 / 500) * (-(113877421 / 500000000)) +
      (h13 - (-(9 / 1000))) * (130416323 / 625000000) := by
  unfold perturbCSlopeSv
  ring

theorem perturbCV4_telescope
    (v4 q11 q13 h11 h13 : ℝ) :
    perturbCSlopeV4 v4 q11 q13 h11 h13 -
        perturbCSlopeV4
          (-(1 / 500)) (179 / 1000) (1 / 5) (1 / 50) (-(9 / 1000)) =
      (v4 - (-(1 / 500))) *
          (-(38476670000 * h11 + 5497510000 * q11 - 3155405929) /
            40000000000) +
      (q11 - 179 / 1000) * (2111115863 / 40000000000) +
      (q13 - 1 / 5) * (-(2929524613 / 200000000000)) +
      (h11 - 1 / 50) * (4453712307 / 40000000000) +
      (h13 - (-(9 / 1000))) * (33366984423 / 200000000000) := by
  unfold perturbCSlopeV4
  ring

set_option maxHeartbeats 3000000 in
theorem perturbCSlopeA_upper_box
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    perturbCSlopeA f u4 v4 q11 q13 q33 h11 h13 h33 ≤
      (-2 / 1000 : ℝ) := by
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  rcases hbox.v4_mem with ⟨hv4L, hv4U⟩
  rcases hbox.q11_mem with ⟨hq11L, hq11U⟩
  rcases hbox.q13_mem with ⟨hq13L, hq13U⟩
  rcases hbox.q33_mem with ⟨hq33L, hq33U⟩
  rcases hbox.h11_mem with ⟨hh11L, hh11U⟩
  rcases hbox.h13_mem with ⟨hh13L, hh13U⟩
  rcases hbox.h33_mem with ⟨hh33L, hh33U⟩
  norm_num at hfL hfU hu4L hu4U hv4L hv4U hq11L hq11U hq13L hq13U hq33L hq33U hh11L hh11U hh13L hh13U hh33L hh33U
  have hf0 : (0 : ℝ) ≤ f := by linarith
  have hu40 : (0 : ℝ) ≤ u4 := by linarith
  have hq110 : (0 : ℝ) ≤ q11 := by linarith
  have hq130 : (0 : ℝ) ≤ q13 := by linarith
  have hq330 : (0 : ℝ) ≤ q33 := by linarith
  have hh110 : (0 : ℝ) ≤ h11 := by linarith
  have hh130 : h13 ≤ (0 : ℝ) := by linarith
  have hh330 : h33 ≤ (0 : ℝ) := by linarith
  have hnh13U : -h13 ≤ (11 / 1000 : ℝ) := by linarith
  have hnv4U : -v4 ≤ (1 / 250 : ℝ) := by linarith
  have h13SqL : (81 / 1000000 : ℝ) ≤ h13 ^ 2 := by
    nlinarith only [mul_nonneg_of_nonpos_of_nonpos
      (by linarith : h13 + 9 / 1000 ≤ 0)
      (by linarith : h13 - 9 / 1000 ≤ 0)]
  have hv4SqL : (1 / 250000 : ℝ) ≤ v4 ^ 2 := by
    nlinarith only [mul_nonneg_of_nonpos_of_nonpos
      (by linarith : v4 + 1 / 500 ≤ 0)
      (by linarith : v4 - 1 / 500 ≤ 0)]
  have hv4SqU : v4 ^ 2 ≤ (1 / 62500 : ℝ) := by
    nlinarith only [mul_nonneg
      (by linarith : 0 ≤ v4 + 1 / 250)
      (by linarith : 0 ≤ 1 / 250 - v4)]
  have hu4SqU : u4 ^ 2 ≤ (18 / 125 : ℝ) ^ 2 := by
    nlinarith only [mul_nonneg
      (by linarith : 0 ≤ 18 / 125 - u4)
      (by linarith : 0 ≤ 18 / 125 + u4)]
  have hq13SqU : q13 ^ 2 ≤ (1001 / 5000 : ℝ) ^ 2 := by
    nlinarith only [mul_nonneg
      (by linarith : 0 ≤ 1001 / 5000 - q13)
      (by linarith : 0 ≤ 1001 / 5000 + q13)]
  have hA1 : (81 / 1000000 : ℝ) ≤ h13 ^ 2 := h13SqL
  have hA2 : (-(11011 / 5000000) : ℝ) ≤ q13 * h13 := by
    have h := positive_negative_product_lower q13 h13
      (1001 / 5000) (-(11 / 1000)) hq130 hh13L (by norm_num) hq13U
    norm_num at h
    exact h
  have hA3 : (589407 / 10000000 : ℝ) ≤ q11 * q33 := by
    have h := nonnegative_product_lower q11 q33
      (889 / 5000) (663 / 2000) hq11L hq33L (by norm_num) hq330
    norm_num at h
    exact h
  have hA4 : (7 / 125000000 : ℝ) ≤ v4 ^ 2 * h11 := by
    have h := nonnegative_product_lower (v4 ^ 2) h11
      (1 / 250000) (7 / 500) hv4SqL hh11L (by norm_num) hh110
    norm_num at h
    exact h
  have hA5 : (-(972 / 390625) : ℝ) ≤ u4 ^ 2 * h33 := by
    have h := positive_negative_product_lower (u4 ^ 2) h33
      ((18 / 125) ^ 2) (-(3 / 25)) (sq_nonneg u4) hh33L
      (by norm_num) hu4SqU
    norm_num at h
    exact h
  have hA6 : (357291 / 25000000000 : ℝ) ≤ f * h13 ^ 2 := by
    have h := nonnegative_product_lower f (h13 ^ 2)
      (4411 / 25000) (81 / 1000000) hfL h13SqL (by norm_num)
      (sq_nonneg h13)
    norm_num at h
    exact h
  have hA7 : (20471451 / 25000000000 : ℝ) ≤ f * q33 * h11 := by
    have h := nonnegative_triple_lower f q33 h11
      (4411 / 25000) (663 / 2000) (7 / 500)
      hfL hq33L hh11L (by norm_num) (by norm_num) hq330 hh110
    norm_num at h
    exact h
  have hA8 : (-(37053 / 9765625) : ℝ) ≤ f * q11 * h33 := by
    have h := nonnegative_negative_triple_lower f q11 h33
      (552 / 3125) (179 / 1000) (-(3 / 25))
      hf0 hq110 hh33L hfU hq11U (by norm_num) (by norm_num)
    norm_num at h
    exact h
  have hA9 : (2599874277 / 250000000000 : ℝ) ≤ f * q11 * q33 := by
    have h := nonnegative_triple_lower f q11 q33
      (4411 / 25000) (889 / 5000) (663 / 2000)
      hfL hq11L hq33L (by norm_num) (by norm_num) hq110 hq330
    norm_num at h
    exact h
  have hA10 : (-(9009 / 78125000) : ℝ) ≤ u4 * v4 * q13 := by
    have h := nonnegative_negative_triple_lower u4 q13 v4
      (18 / 125) (1001 / 5000) (-(1 / 250))
      hu40 hq130 hv4L hu4U hq13U (by norm_num) (by norm_num)
    norm_num at h
    simpa only [mul_assoc, mul_left_comm, mul_comm] using h
  have hA11 : h11 * h33 ≤ (-(819 / 500000) : ℝ) := by
    have h := positive_negative_product_upper h11 h33
      (7 / 500) (-(117 / 1000)) hh11L hh330 (by norm_num) hh33U
    norm_num at h
    exact h
  have hA12 : q33 * h11 ≤ (333 / 50000 : ℝ) := by
    have h := nonnegative_product_upper q33 h11
      (333 / 1000) (1 / 50) hq33U hh11U (by norm_num) hh110
    norm_num at h
    exact h
  have hA13 : q11 * h33 ≤ (-(104013 / 5000000) : ℝ) := by
    have h := positive_negative_product_upper q11 h33
      (889 / 5000) (-(117 / 1000)) hq11L hh330 (by norm_num) hh33U
    norm_num at h
    exact h
  have hA14 : q13 ^ 2 ≤ (1002001 / 25000000 : ℝ) := by
    norm_num at hq13SqU ⊢
    exact hq13SqU
  have hA15 : u4 * v4 * h13 ≤ (99 / 15625000 : ℝ) := by
    have h := nonnegative_triple_upper u4 (-v4) (-h13)
      (18 / 125) (1 / 250) (11 / 1000)
      hu4U hnv4U hnh13U (by norm_num) (by norm_num)
      (by linarith) (by linarith)
    norm_num at h
    nlinarith only [h]
  have hA16 : f * h11 * h33 ≤ (-(3612609 / 12500000000) : ℝ) := by
    have h := nonnegative_negative_triple_upper f h11 h33
      (4411 / 25000) (7 / 500) (-(117 / 1000))
      hfL hh11L hh330 hh33U (by norm_num) (by norm_num)
    norm_num at h
    exact h
  have hA17 : f * q13 * h13 ≤ (-(39699 / 125000000) : ℝ) := by
    have h := nonnegative_negative_triple_upper f q13 h13
      (4411 / 25000) (1 / 5) (-(9 / 1000))
      hfL hq13L hh130 hh13U (by norm_num) (by norm_num)
    norm_num at h
    exact h
  have hA18 : f * q13 ^ 2 ≤ (69138069 / 9765625000 : ℝ) := by
    have h := nonnegative_product_upper f (q13 ^ 2)
      (552 / 3125) ((1001 / 5000) ^ 2) hfU hq13SqU
      (by norm_num) (sq_nonneg q13)
    norm_num at h
    exact h
  have hA19 : v4 ^ 2 * q11 ≤ (179 / 62500000 : ℝ) := by
    have h := nonnegative_product_upper (v4 ^ 2) q11
      (1 / 62500) (179 / 1000) hv4SqU hq11U (by norm_num) hq110
    norm_num at h
    exact h
  have hA20 : u4 ^ 2 * q33 ≤ (26973 / 3906250 : ℝ) := by
    have h := nonnegative_product_upper (u4 ^ 2) q33
      ((18 / 125) ^ 2) (333 / 1000) hu4SqU hq33U
      (by norm_num) hq330
    norm_num at h
    exact h
  unfold perturbCSlopeA
  nlinarith only [hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9,
    hA10, hA11, hA12, hA13, hA14, hA15, hA16, hA17, hA18, hA19, hA20]

set_option maxHeartbeats 3000000 in
theorem perturbCSlopeR_upper_box
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    perturbCSlopeR r su u4 sv v4 q11 q13 q33 h11 h13 h33 ≤
      (-8 / 1000 : ℝ) := by
  rcases hbox.a_mem with ⟨haL, haU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  rcases hbox.su_mem with ⟨hsuL, hsuU⟩
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  rcases hbox.sv_mem with ⟨hsvL, hsvU⟩
  rcases hbox.v4_mem with ⟨hv4L, hv4U⟩
  rcases hbox.q11_mem with ⟨hq11L, hq11U⟩
  rcases hbox.q13_mem with ⟨hq13L, hq13U⟩
  rcases hbox.q33_mem with ⟨hq33L, hq33U⟩
  rcases hbox.h11_mem with ⟨hh11L, hh11U⟩
  rcases hbox.h13_mem with ⟨hh13L, hh13U⟩
  rcases hbox.h33_mem with ⟨hh33L, hh33U⟩
  norm_num at hfL hfU hsuL hsuU hu4L hu4U hsvL hsvU hv4L hv4U hq11L hq11U hq13L hq13U hq33L hq33U hh11L hh11U hh13L hh13U hh33L hh33U
  have hf0 : (0 : ℝ) ≤ f := by linarith
  have hsu0 : (0 : ℝ) ≤ su := by linarith
  have hu40 : (0 : ℝ) ≤ u4 := by linarith
  have hsv0 : (0 : ℝ) ≤ sv := by linarith
  have hq110 : (0 : ℝ) ≤ q11 := by linarith
  have hq130 : (0 : ℝ) ≤ q13 := by linarith
  have hq330 : (0 : ℝ) ≤ q33 := by linarith
  have hh110 : (0 : ℝ) ≤ h11 := by linarith
  have hh130 : h13 ≤ (0 : ℝ) := by linarith
  have hh330 : h33 ≤ (0 : ℝ) := by linarith
  have hv40 : v4 ≤ (0 : ℝ) := by linarith
  have hnh13L : (9 / 1000 : ℝ) ≤ -h13 := by linarith
  have hnv4L : (1 / 500 : ℝ) ≤ -v4 := by linarith
  have h13SqU : h13 ^ 2 ≤ (121 / 1000000 : ℝ) := by
    nlinarith only [mul_nonneg
      (by linarith : 0 ≤ h13 + 11 / 1000)
      (by linarith : 0 ≤ 11 / 1000 - h13)]
  have hq13SqL : (1 / 5 : ℝ) ^ 2 ≤ q13 ^ 2 := by
    nlinarith only [mul_nonneg
      (by linarith : 0 ≤ q13 - 1 / 5)
      (by linarith : 0 ≤ q13 + 1 / 5)]
  have hrSlope :
      perturbCSlopeR r su u4 sv v4 q11 q13 q33 h11 h13 h33 ≤
        (-8 / 1000 : ℝ) := by
    have hR1 : (63189 / 6250000000 : ℝ) ≤ su * v4 * h13 := by
      have h := nonnegative_triple_lower su (-v4) (-h13)
        (7021 / 12500) (1 / 500) (9 / 1000)
        hsuL hnv4L hnh13L (by norm_num) (by norm_num)
        (by linarith) (by linarith)
      norm_num at h
      nlinarith only [h]
    have hR2 : (-(1332441 / 1562500000) : ℝ) ≤ u4 * sv * h13 := by
      have h := nonnegative_negative_triple_lower u4 sv h13
        (18 / 125) (13459 / 25000) (-(11 / 1000))
        hu40 hsv0 hh13L hu4U hsvU (by norm_num) (by norm_num)
      norm_num at h
      exact h
    have hR3 : (4641 / 1000000 : ℝ) ≤ q33 * h11 := by
      have h := nonnegative_product_lower q33 h11
        (663 / 2000) (7 / 500) hq33L hh11L (by norm_num) hh110
      norm_num at h
      exact h
    have hR4 : (-(537 / 25000) : ℝ) ≤ q11 * h33 := by
      have h := positive_negative_product_lower q11 h33
        (179 / 1000) (-(3 / 25)) hq110 hh33L (by norm_num) hq11U
      norm_num at h
      exact h
    have hR5 : (-(171549 / 1250000000) : ℝ) ≤ r * h11 * h33 := by
      have hr0 : (0 : ℝ) ≤ r := by linarith
      have h := nonnegative_negative_triple_lower r h11 h33
        (57183 / 1000000) (1 / 50) (-(3 / 25))
        hr0 hh110 hh33L hrU hh11U (by norm_num) (by norm_num)
      norm_num at h
      exact h
    have hR6 : (1 / 25 : ℝ) ≤ q13 ^ 2 := by
      norm_num at hq13SqL ⊢
      exact hq13SqL
    have hR7 : (-(3 / 1250) : ℝ) ≤ h11 * h33 := by
      have h := positive_negative_product_lower h11 h33
        (1 / 50) (-(3 / 25)) hh110 hh33L (by norm_num) hh11U
      norm_num at h
      exact h
    have hR8 : (-(629642013 / 5000000000000) : ℝ) ≤
        r * q13 * h13 := by
      have hr0 : (0 : ℝ) ≤ r := by linarith
      have h := nonnegative_negative_triple_lower r q13 h13
        (57183 / 1000000) (1001 / 5000) (-(11 / 1000))
        hr0 hq130 hh13L hrU hq13U (by norm_num) (by norm_num)
      norm_num at h
      exact h
    have hR9 : (-(2409161 / 6250000000) : ℝ) ≤ sv * v4 * q11 := by
      have h := nonnegative_negative_triple_lower sv q11 v4
        (13459 / 25000) (179 / 1000) (-(1 / 250))
        hsv0 hq110 hv4L hsvU hq11U (by norm_num) (by norm_num)
      norm_num at h
      simpa only [mul_assoc, mul_left_comm, mul_comm] using h
    have hR10 : (49817 / 25000000 : ℝ) ≤ r * q13 ^ 2 := by
      have h := nonnegative_product_lower r (q13 ^ 2)
        (49817 / 1000000) (1 / 25) hrL (by nlinarith only [hq13SqL])
        (by norm_num) (sq_nonneg q13)
      norm_num at h
      exact h
    have hR11 : (656344143 / 25000000000 : ℝ) ≤ su * u4 * q33 := by
      have h := nonnegative_triple_lower su u4 q33
        (7021 / 12500) (141 / 1000) (663 / 2000)
        hsuL hu4L hq33L (by norm_num) (by norm_num) hu40 hq330
      norm_num at h
      exact h
    have hR12 : sv * v4 * h11 ≤ (-(75341 / 5000000000) : ℝ) := by
      have h := nonnegative_negative_triple_upper sv h11 v4
        (10763 / 20000) (7 / 500) (-(1 / 500))
        hsvL hh11L hv40 hv4U (by norm_num) (by norm_num)
      norm_num at h
      simpa only [mul_assoc, mul_left_comm, mul_comm] using h
    have hR13 : su * u4 * h33 ≤
        (-(115825437 / 12500000000) : ℝ) := by
      have h := nonnegative_negative_triple_upper su u4 h33
        (7021 / 12500) (141 / 1000) (-(117 / 1000))
        hsuL hu4L hh330 hh33U (by norm_num) (by norm_num)
      norm_num at h
      exact h
    have hR14 : q13 * h13 ≤ (-(9 / 5000) : ℝ) := by
      have h := positive_negative_product_upper q13 h13
        (1 / 5) (-(9 / 1000)) hq13L hh130 (by norm_num) hh13U
      norm_num at h
      exact h
    have hR15 : r * h13 ^ 2 ≤ (6919143 / 1000000000000 : ℝ) := by
      have h := nonnegative_product_upper r (h13 ^ 2)
        (57183 / 1000000) (121 / 1000000) hrU h13SqU
        (by norm_num) (sq_nonneg h13)
      norm_num at h
      exact h
    have hR16 : q11 * q33 ≤ (59607 / 1000000 : ℝ) := by
      have h := nonnegative_product_upper q11 q33
        (179 / 1000) (333 / 1000) hq11U hq33U (by norm_num) hq330
      norm_num at h
      exact h
    have hR17 : h13 ^ 2 ≤ (121 / 1000000 : ℝ) := h13SqU
    have hR18 : r * q33 * h11 ≤
        (19041939 / 50000000000 : ℝ) := by
      have h := nonnegative_triple_upper r q33 h11
        (57183 / 1000000) (333 / 1000) (1 / 50)
        hrU hq33U hh11U (by norm_num) (by norm_num) hq330 hh110
      norm_num at h
      exact h
    have hR19 : r * q11 * h33 ≤
        (-(5181615621 / 5000000000000) : ℝ) := by
      have h := nonnegative_negative_triple_upper r q11 h33
        (49817 / 1000000) (889 / 5000) (-(117 / 1000))
        hrL hq11L hh330 hh33U (by norm_num) (by norm_num)
      norm_num at h
      exact h
    have hR20 : r * q11 * q33 ≤
        (3408507081 / 1000000000000 : ℝ) := by
      have h := nonnegative_triple_upper r q11 q33
        (57183 / 1000000) (179 / 1000) (333 / 1000)
        hrU hq11U hq33U (by norm_num) (by norm_num) hq110 hq330
      norm_num at h
      exact h
    have hR21 : su * v4 * q13 ≤ (-(7021 / 31250000) : ℝ) := by
      have h := nonnegative_negative_triple_upper su q13 v4
        (7021 / 12500) (1 / 5) (-(1 / 500))
        hsuL hq13L hv40 hv4U (by norm_num) (by norm_num)
      norm_num at h
      simpa only [mul_assoc, mul_left_comm, mul_comm] using h
    have hR22 : u4 * sv * q13 ≤ (121252131 / 7812500000 : ℝ) := by
      have h := nonnegative_triple_upper u4 sv q13
        (18 / 125) (13459 / 25000) (1001 / 5000)
        hu4U hsvU hq13U (by norm_num) (by norm_num) hsv0 hq130
      norm_num at h
      exact h
    unfold perturbCSlopeR
    nlinarith only [hR1, hR2, hR3, hR4, hR5, hR6, hR7, hR8, hR9,
      hR10, hR11, hR12, hR13, hR14, hR15, hR16, hR17, hR18, hR19,
      hR20, hR21, hR22]
  exact hrSlope

set_option maxHeartbeats 3000000 in
theorem perturbCSlopeSu_lower_box
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (20 / 1000 : ℝ) ≤
      perturbCSlopeSu f su u4 sv v4 q13 q33 h13 h33 := by
  rcases hbox.a_mem with ⟨haL, haU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  rcases hbox.su_mem with ⟨hsuL, hsuU⟩
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  rcases hbox.sv_mem with ⟨hsvL, hsvU⟩
  rcases hbox.v4_mem with ⟨hv4L, hv4U⟩
  rcases hbox.q11_mem with ⟨hq11L, hq11U⟩
  rcases hbox.q13_mem with ⟨hq13L, hq13U⟩
  rcases hbox.q33_mem with ⟨hq33L, hq33U⟩
  rcases hbox.h11_mem with ⟨hh11L, hh11U⟩
  rcases hbox.h13_mem with ⟨hh13L, hh13U⟩
  rcases hbox.h33_mem with ⟨hh33L, hh33U⟩
  norm_num at hfL hfU hsuL hsuU hu4L hu4U hsvL hsvU hv4L hv4U hq11L hq11U hq13L hq13U hq33L hq33U hh11L hh11U hh13L hh13U hh33L hh33U
  have hf0 : (0 : ℝ) ≤ f := by linarith
  have hsu0 : (0 : ℝ) ≤ su := by linarith
  have hu40 : (0 : ℝ) ≤ u4 := by linarith
  have hsv0 : (0 : ℝ) ≤ sv := by linarith
  have hq110 : (0 : ℝ) ≤ q11 := by linarith
  have hq130 : (0 : ℝ) ≤ q13 := by linarith
  have hq330 : (0 : ℝ) ≤ q33 := by linarith
  have hh110 : (0 : ℝ) ≤ h11 := by linarith
  have hnh13L : (9 / 1000 : ℝ) ≤ -h13 := by linarith
  have hnh13U : -h13 ≤ (11 / 1000 : ℝ) := by linarith
  have hnh33L : (117 / 1000 : ℝ) ≤ -h33 := by linarith
  have hnh33U : -h33 ≤ (120 / 1000 : ℝ) := by linarith
  have hnv4L : (2 / 1000 : ℝ) ≤ -v4 := by linarith
  have hnv4U : -v4 ≤ (4 / 1000 : ℝ) := by linarith
  norm_num at hnh13L hnh13U hnh33L hnh33U hnv4L hnv4U
  have hh130 : h13 ≤ (0 : ℝ) := by linarith
  have hh330 : h33 ≤ (0 : ℝ) := by linarith
  have hv40 : v4 ≤ (0 : ℝ) := by linarith
  have h13SqL : (81 / 1000000 : ℝ) ≤ h13 ^ 2 := by
    nlinarith only [mul_nonneg_of_nonpos_of_nonpos
      (by linarith : h13 + 9 / 1000 ≤ 0)
      (by linarith : h13 - 9 / 1000 ≤ 0)]
  have h13SqU : h13 ^ 2 ≤ (121 / 1000000 : ℝ) := by
    nlinarith only [mul_nonneg
      (by linarith : 0 ≤ h13 + 11 / 1000)
      (by linarith : 0 ≤ 11 / 1000 - h13)]
  have hv4SqL : (1 / 250000 : ℝ) ≤ v4 ^ 2 := by
    nlinarith only [mul_nonneg_of_nonpos_of_nonpos
      (by linarith : v4 + 1 / 500 ≤ 0)
      (by linarith : v4 - 1 / 500 ≤ 0)]
  have hv4SqU : v4 ^ 2 ≤ (1 / 62500 : ℝ) := by
    nlinarith only [mul_nonneg
      (by linarith : 0 ≤ v4 + 1 / 250)
      (by linarith : 0 ≤ 1 / 250 - v4)]
  have hu4SqU : u4 ^ 2 ≤ (18 / 125 : ℝ) ^ 2 := by
    nlinarith only [mul_nonneg
      (by linarith : 0 ≤ 18 / 125 - u4)
      (by linarith : 0 ≤ 18 / 125 + u4)]
  have hsvSqL : (10763 / 20000 : ℝ) ^ 2 ≤ sv ^ 2 := by
    nlinarith only [mul_nonneg
      (by linarith : 0 ≤ sv - 10763 / 20000)
      (by linarith : 0 ≤ sv + 10763 / 20000)]
  have hq13SqL : (1 / 5 : ℝ) ^ 2 ≤ q13 ^ 2 := by
    nlinarith only [mul_nonneg
      (by linarith : 0 ≤ q13 - 1 / 5)
      (by linarith : 0 ≤ q13 + 1 / 5)]
  have hq13SqU : q13 ^ 2 ≤ (1001 / 5000 : ℝ) ^ 2 := by
    nlinarith only [mul_nonneg
      (by linarith : 0 ≤ 1001 / 5000 - q13)
      (by linarith : 0 ≤ 1001 / 5000 + q13)]
  have hsuSlope : (20 / 1000 : ℝ) ≤
      perturbCSlopeSu f su u4 sv v4 q13 q33 h13 h33 := by
    have hSu1 : su * h33 ≤ (-(821457 / 12500000) : ℝ) := by
      have h := positive_negative_product_upper su h33
        (7021 / 12500) (-(117 / 1000)) hsuL hh330 (by norm_num) hh33U
      norm_num at h
      exact h
    have hSu2 : su * q33 ≤ (18705609 / 100000000 : ℝ) := by
      have h := nonnegative_product_upper su q33
        (56173 / 100000) (333 / 1000) hsuU hq33U (by norm_num) hq330
      norm_num at h
      exact h
    have hSu3 : f * h33 ≤ (-(516087 / 25000000) : ℝ) := by
      have h := positive_negative_product_upper f h33
        (4411 / 25000) (-(117 / 1000)) hfL hh330 (by norm_num) hh33U
      norm_num at h
      exact h
    have hSu4 : v4 * q13 ≤ (-(1 / 2500) : ℝ) := by
      have h := positive_negative_product_upper q13 v4
        (1 / 5) (-(1 / 500)) hq13L hv40 (by norm_num) hv4U
      norm_num at h
      nlinarith only [h]
    have hSu5 : f * su * h33 ≤
        (-(3623446827 / 312500000000) : ℝ) := by
      have h := nonnegative_negative_triple_upper f su h33
        (4411 / 25000) (7021 / 12500) (-(117 / 1000))
        hfL hsuL hh330 hh33U (by norm_num) (by norm_num)
      norm_num at h
      exact h
    have hSu6 : v4 * h13 ≤ (11 / 250000 : ℝ) := by
      have h := nonnegative_product_upper (-v4) (-h13)
        (1 / 250) (11 / 1000) hnv4U hnh13U (by norm_num) (by linarith)
      norm_num at h
      nlinarith only [h]
    have hSu7 : h33 ≤ (-(117 / 1000) : ℝ) := hh33U
    have hSu8 : q33 ≤ (333 / 1000 : ℝ) := hq33U
    have hSu9 : f * sv * q13 ≤ (929599671 / 48828125000 : ℝ) := by
      have h := nonnegative_triple_upper f sv q13
        (552 / 3125) (13459 / 25000) (1001 / 5000)
        hfU hsvU hq13U (by norm_num) (by norm_num) hsv0 hq130
      norm_num at h
      exact h
    have hSu10 : u4 * sv * v4 ≤
        (-(1517583 / 10000000000) : ℝ) := by
      have h := nonnegative_negative_triple_upper u4 sv v4
        (141 / 1000) (10763 / 20000) (-(1 / 500))
        hu4L hsvL hv40 hv4U (by norm_num) (by norm_num)
      norm_num at h
      exact h
    have hSu11 : (-(148049 / 25000000) : ℝ) ≤ sv * h13 := by
      have h := positive_negative_product_lower sv h13
        (13459 / 25000) (-(11 / 1000)) hsv0 hh13L (by norm_num) hsvU
      norm_num at h
      exact h
    have hSu12 : (10763 / 100000 : ℝ) ≤ sv * q13 := by
      have h := nonnegative_product_lower sv q13
        (10763 / 20000) (1 / 5) hsvL hq13L (by norm_num) hq130
      norm_num at h
      exact h
    have hSu13 : (93483 / 2000000 : ℝ) ≤ u4 * q33 := by
      have h := nonnegative_product_lower u4 q33
        (141 / 1000) (663 / 2000) hu4L hq33L (by norm_num) hq330
      norm_num at h
      exact h
    have hSu14 : (-(10215381 / 9765625000) : ℝ) ≤
        f * sv * h13 := by
      have h := nonnegative_negative_triple_lower f sv h13
        (552 / 3125) (13459 / 25000) (-(11 / 1000))
        hf0 hsv0 hh13L hfU hsvU (by norm_num) (by norm_num)
      norm_num at h
      exact h
    have hSu15 : (-(54 / 3125) : ℝ) ≤ u4 * h33 := by
      have h := positive_negative_product_lower u4 h33
        (18 / 125) (-(3 / 25)) hu40 hh33L (by norm_num) hu4U
      norm_num at h
      exact h
    have hSu16 : (2924493 / 50000000 : ℝ) ≤ f * q33 := by
      have h := nonnegative_product_lower f q33
        (4411 / 25000) (663 / 2000) hfL hq33L (by norm_num) hq330
      norm_num at h
      exact h
    have hSu17 : (1 / 250000 : ℝ) ≤ v4 ^ 2 := hv4SqL
    have hSu18 : (20532865353 / 625000000000 : ℝ) ≤
        f * su * q33 := by
      have h := nonnegative_triple_lower f su q33
        (4411 / 25000) (7021 / 12500) (663 / 2000)
        hfL hsuL hq33L (by norm_num) (by norm_num) hsu0 hq330
      norm_num at h
      exact h
    have hSu19 : (7021 / 3125000000 : ℝ) ≤ su * v4 ^ 2 := by
      have h := nonnegative_product_lower su (v4 ^ 2)
        (7021 / 12500) (1 / 250000) hsuL hv4SqL
        (by norm_num) (sq_nonneg v4)
      norm_num at h
      exact h
    unfold perturbCSlopeSu
    nlinarith only [hSu1, hSu2, hSu3, hSu4, hSu5, hSu6, hSu7,
      hSu8, hSu9, hSu10, hSu11, hSu12, hSu13, hSu14, hSu15,
      hSu16, hSu17, hSu18, hSu19]
  exact hsuSlope

set_option maxHeartbeats 3000000 in
theorem perturbCSlopeU4_lower_box
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    (35 / 1000 : ℝ) ≤
      perturbCSlopeU4 u4 sv v4 q13 q33 h13 h33 := by
  rcases hbox.a_mem with ⟨haL, haU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  rcases hbox.su_mem with ⟨hsuL, hsuU⟩
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  rcases hbox.sv_mem with ⟨hsvL, hsvU⟩
  rcases hbox.v4_mem with ⟨hv4L, hv4U⟩
  rcases hbox.q11_mem with ⟨hq11L, hq11U⟩
  rcases hbox.q13_mem with ⟨hq13L, hq13U⟩
  rcases hbox.q33_mem with ⟨hq33L, hq33U⟩
  rcases hbox.h11_mem with ⟨hh11L, hh11U⟩
  rcases hbox.h13_mem with ⟨hh13L, hh13U⟩
  rcases hbox.h33_mem with ⟨hh33L, hh33U⟩
  norm_num at hfL hfU hsuL hsuU hu4L hu4U hsvL hsvU hv4L hv4U hq11L hq11U hq13L hq13U hq33L hq33U hh11L hh11U hh13L hh13U hh33L hh33U
  have hf0 : (0 : ℝ) ≤ f := by linarith
  have hsu0 : (0 : ℝ) ≤ su := by linarith
  have hu40 : (0 : ℝ) ≤ u4 := by linarith
  have hsv0 : (0 : ℝ) ≤ sv := by linarith
  have hq110 : (0 : ℝ) ≤ q11 := by linarith
  have hq130 : (0 : ℝ) ≤ q13 := by linarith
  have hq330 : (0 : ℝ) ≤ q33 := by linarith
  have hh110 : (0 : ℝ) ≤ h11 := by linarith
  have hnh13L : (9 / 1000 : ℝ) ≤ -h13 := by linarith
  have hnh13U : -h13 ≤ (11 / 1000 : ℝ) := by linarith
  have hnh33L : (117 / 1000 : ℝ) ≤ -h33 := by linarith
  have hnh33U : -h33 ≤ (120 / 1000 : ℝ) := by linarith
  have hnv4L : (2 / 1000 : ℝ) ≤ -v4 := by linarith
  have hnv4U : -v4 ≤ (4 / 1000 : ℝ) := by linarith
  norm_num at hnh13L hnh13U hnh33L hnh33U hnv4L hnv4U
  have hh130 : h13 ≤ (0 : ℝ) := by linarith
  have hh330 : h33 ≤ (0 : ℝ) := by linarith
  have hv40 : v4 ≤ (0 : ℝ) := by linarith
  have h13SqL : (81 / 1000000 : ℝ) ≤ h13 ^ 2 := by
    nlinarith only [mul_nonneg_of_nonpos_of_nonpos
      (by linarith : h13 + 9 / 1000 ≤ 0)
      (by linarith : h13 - 9 / 1000 ≤ 0)]
  have h13SqU : h13 ^ 2 ≤ (121 / 1000000 : ℝ) := by
    nlinarith only [mul_nonneg
      (by linarith : 0 ≤ h13 + 11 / 1000)
      (by linarith : 0 ≤ 11 / 1000 - h13)]
  have hv4SqL : (1 / 250000 : ℝ) ≤ v4 ^ 2 := by
    nlinarith only [mul_nonneg_of_nonpos_of_nonpos
      (by linarith : v4 + 1 / 500 ≤ 0)
      (by linarith : v4 - 1 / 500 ≤ 0)]
  have hv4SqU : v4 ^ 2 ≤ (1 / 62500 : ℝ) := by
    nlinarith only [mul_nonneg
      (by linarith : 0 ≤ v4 + 1 / 250)
      (by linarith : 0 ≤ 1 / 250 - v4)]
  have hu4SqU : u4 ^ 2 ≤ (18 / 125 : ℝ) ^ 2 := by
    nlinarith only [mul_nonneg
      (by linarith : 0 ≤ 18 / 125 - u4)
      (by linarith : 0 ≤ 18 / 125 + u4)]
  have hsvSqL : (10763 / 20000 : ℝ) ^ 2 ≤ sv ^ 2 := by
    nlinarith only [mul_nonneg
      (by linarith : 0 ≤ sv - 10763 / 20000)
      (by linarith : 0 ≤ sv + 10763 / 20000)]
  have hq13SqL : (1 / 5 : ℝ) ^ 2 ≤ q13 ^ 2 := by
    nlinarith only [mul_nonneg
      (by linarith : 0 ≤ q13 - 1 / 5)
      (by linarith : 0 ≤ q13 + 1 / 5)]
  have hq13SqU : q13 ^ 2 ≤ (1001 / 5000 : ℝ) ^ 2 := by
    nlinarith only [mul_nonneg
      (by linarith : 0 ≤ 1001 / 5000 - q13)
      (by linarith : 0 ≤ 1001 / 5000 + q13)]
  have hu4Slope : (35 / 1000 : ℝ) ≤
      perturbCSlopeU4 u4 sv v4 q13 q33 h13 h33 := by
    have hU41 : sv * q13 ≤ (13472459 / 125000000 : ℝ) := by
      have h := nonnegative_product_upper sv q13
        (13459 / 25000) (1001 / 5000) hsvU hq13U (by norm_num) hq130
      norm_num at h
      exact h
    have hU42 : u4 * h33 ≤ (-(16497 / 1000000) : ℝ) := by
      have h := positive_negative_product_upper u4 h33
        (141 / 1000) (-(117 / 1000)) hu4L hh330 (by norm_num) hh33U
      norm_num at h
      exact h
    have hU43 : sv * h13 ≤ (-(96867 / 20000000) : ℝ) := by
      have h := positive_negative_product_upper sv h13
        (10763 / 20000) (-(9 / 1000)) hsvL hh130 (by norm_num) hh13U
      norm_num at h
      exact h
    have hU44 : u4 * q33 ≤ (2997 / 62500 : ℝ) := by
      have h := nonnegative_product_upper u4 q33
        (18 / 125) (333 / 1000) hu4U hq33U (by norm_num) hq330
      norm_num at h
      exact h
    have hU45 : sv * v4 ≤ (-(10763 / 10000000) : ℝ) := by
      have h := positive_negative_product_upper sv v4
        (10763 / 20000) (-(1 / 500)) hsvL hv40 (by norm_num) hv4U
      norm_num at h
      exact h
    have hU46 : h33 ≤ (-(117 / 1000) : ℝ) := hh33U
    have hU47 : (9 / 500000 : ℝ) ≤ v4 * h13 := by
      have h := nonnegative_product_lower (-v4) (-h13)
        (1 / 500) (9 / 1000) hnv4L hnh13L (by norm_num) (by linarith)
      norm_num at h
      nlinarith only [h]
    have hU48 : (-(1001 / 1250000) : ℝ) ≤ v4 * q13 := by
      have h := positive_negative_product_lower q13 v4
        (1001 / 5000) (-(1 / 250)) hq130 hv4L (by norm_num) hq13U
      norm_num at h
      nlinarith only [h]
    have hU49 : (663 / 2000 : ℝ) ≤ q33 := hq33L
    have hU410 : (115842169 / 400000000 : ℝ) ≤ sv ^ 2 := by
      norm_num at hsvSqL ⊢
      exact hsvSqL
    have hU411 : (16333745829 / 400000000000 : ℝ) ≤
        u4 * sv ^ 2 := by
      have h := nonnegative_product_lower u4 (sv ^ 2)
        (141 / 1000) ((10763 / 20000) ^ 2) hu4L hsvSqL
        (by norm_num) (sq_nonneg sv)
      norm_num at h
      exact h
    unfold perturbCSlopeU4
    nlinarith only [hU41, hU42, hU43, hU44, hU45, hU46, hU47,
      hU48, hU49, hU410, hU411]
  exact hu4Slope

set_option maxHeartbeats 3000000 in
theorem perturbCSlopeSv_upper_box
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    perturbCSlopeSv f sv v4 q11 q13 h11 h13 ≤ (-9 / 10000 : ℝ) := by
  rcases hbox.a_mem with ⟨haL, haU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  rcases hbox.su_mem with ⟨hsuL, hsuU⟩
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  rcases hbox.sv_mem with ⟨hsvL, hsvU⟩
  rcases hbox.v4_mem with ⟨hv4L, hv4U⟩
  rcases hbox.q11_mem with ⟨hq11L, hq11U⟩
  rcases hbox.q13_mem with ⟨hq13L, hq13U⟩
  rcases hbox.q33_mem with ⟨hq33L, hq33U⟩
  rcases hbox.h11_mem with ⟨hh11L, hh11U⟩
  rcases hbox.h13_mem with ⟨hh13L, hh13U⟩
  rcases hbox.h33_mem with ⟨hh33L, hh33U⟩
  norm_num at hfL hfU hsuL hsuU hu4L hu4U hsvL hsvU hv4L hv4U hq11L hq11U hq13L hq13U hq33L hq33U hh11L hh11U hh13L hh13U hh33L hh33U
  have hf0 : (0 : ℝ) ≤ f := by linarith
  have hsu0 : (0 : ℝ) ≤ su := by linarith
  have hu40 : (0 : ℝ) ≤ u4 := by linarith
  have hsv0 : (0 : ℝ) ≤ sv := by linarith
  have hq110 : (0 : ℝ) ≤ q11 := by linarith
  have hq130 : (0 : ℝ) ≤ q13 := by linarith
  have hq330 : (0 : ℝ) ≤ q33 := by linarith
  have hh110 : (0 : ℝ) ≤ h11 := by linarith
  have hnh13L : (9 / 1000 : ℝ) ≤ -h13 := by linarith
  have hnh13U : -h13 ≤ (11 / 1000 : ℝ) := by linarith
  have hnh33L : (117 / 1000 : ℝ) ≤ -h33 := by linarith
  have hnh33U : -h33 ≤ (120 / 1000 : ℝ) := by linarith
  have hnv4L : (2 / 1000 : ℝ) ≤ -v4 := by linarith
  have hnv4U : -v4 ≤ (4 / 1000 : ℝ) := by linarith
  norm_num at hnh13L hnh13U hnh33L hnh33U hnv4L hnv4U
  have hh130 : h13 ≤ (0 : ℝ) := by linarith
  have hh330 : h33 ≤ (0 : ℝ) := by linarith
  have hv40 : v4 ≤ (0 : ℝ) := by linarith
  have h13SqL : (81 / 1000000 : ℝ) ≤ h13 ^ 2 := by
    nlinarith only [mul_nonneg_of_nonpos_of_nonpos
      (by linarith : h13 + 9 / 1000 ≤ 0)
      (by linarith : h13 - 9 / 1000 ≤ 0)]
  have h13SqU : h13 ^ 2 ≤ (121 / 1000000 : ℝ) := by
    nlinarith only [mul_nonneg
      (by linarith : 0 ≤ h13 + 11 / 1000)
      (by linarith : 0 ≤ 11 / 1000 - h13)]
  have hv4SqL : (1 / 250000 : ℝ) ≤ v4 ^ 2 := by
    nlinarith only [mul_nonneg_of_nonpos_of_nonpos
      (by linarith : v4 + 1 / 500 ≤ 0)
      (by linarith : v4 - 1 / 500 ≤ 0)]
  have hv4SqU : v4 ^ 2 ≤ (1 / 62500 : ℝ) := by
    nlinarith only [mul_nonneg
      (by linarith : 0 ≤ v4 + 1 / 250)
      (by linarith : 0 ≤ 1 / 250 - v4)]
  have hu4SqU : u4 ^ 2 ≤ (18 / 125 : ℝ) ^ 2 := by
    nlinarith only [mul_nonneg
      (by linarith : 0 ≤ 18 / 125 - u4)
      (by linarith : 0 ≤ 18 / 125 + u4)]
  have hsvSqL : (10763 / 20000 : ℝ) ^ 2 ≤ sv ^ 2 := by
    nlinarith only [mul_nonneg
      (by linarith : 0 ≤ sv - 10763 / 20000)
      (by linarith : 0 ≤ sv + 10763 / 20000)]
  have hq13SqL : (1 / 5 : ℝ) ^ 2 ≤ q13 ^ 2 := by
    nlinarith only [mul_nonneg
      (by linarith : 0 ≤ q13 - 1 / 5)
      (by linarith : 0 ≤ q13 + 1 / 5)]
  have hq13SqU : q13 ^ 2 ≤ (1001 / 5000 : ℝ) ^ 2 := by
    nlinarith only [mul_nonneg
      (by linarith : 0 ≤ 1001 / 5000 - q13)
      (by linarith : 0 ≤ 1001 / 5000 + q13)]
  have hsvSlope :
      perturbCSlopeSv f sv v4 q11 q13 h11 h13 ≤ (-9 / 10000 : ℝ) := by
    have hSv1 : (75341 / 10000000 : ℝ) ≤ sv * h11 := by
      have h := nonnegative_product_lower sv h11
        (10763 / 20000) (7 / 500) hsvL hh11L (by norm_num) hh110
      norm_num at h
      exact h
    have hSv2 : (9568307 / 100000000 : ℝ) ≤ sv * q11 := by
      have h := nonnegative_product_lower sv q11
        (10763 / 20000) (889 / 5000) hsvL hq11L (by norm_num) hq110
      norm_num at h
      exact h
    have hSv3 : (7 / 500 : ℝ) ≤ h11 := hh11L
    have hSv4 : (889 / 5000 : ℝ) ≤ q11 := hq11L
    have hSv5 : (332329151 / 250000000000 : ℝ) ≤
        f * sv * h11 := by
      have h := nonnegative_triple_lower f sv h11
        (4411 / 25000) (10763 / 20000) (7 / 500)
        hfL hsvL hh11L (by norm_num) (by norm_num) hsv0 hh110
      norm_num at h
      exact h
    have hSv6 : (30877 / 12500000 : ℝ) ≤ f * h11 := by
      have h := nonnegative_product_lower f h11
        (4411 / 25000) (7 / 500) hfL hh11L (by norm_num) hh110
      norm_num at h
      exact h
    have hSv7 : (-(1 / 250) : ℝ) ≤ v4 := hv4L
    have hSv8 : (4411 / 125000 : ℝ) ≤ f * q13 := by
      have h := nonnegative_product_lower f q13
        (4411 / 25000) (1 / 5) hfL hq13L (by norm_num) hq130
      norm_num at h
      exact h
    have hSv9 : f * q11 ≤ (12351 / 390625 : ℝ) := by
      have h := nonnegative_product_upper f q11
        (552 / 3125) (179 / 1000) hfU hq11U (by norm_num) hq110
      norm_num at h
      exact h
    have hSv10 : h13 ≤ (-(9 / 1000) : ℝ) := hh13U
    have hSv11 : f * h13 ≤ (-(39699 / 25000000) : ℝ) := by
      have h := positive_negative_product_upper f h13
        (4411 / 25000) (-(9 / 1000)) hfL hh130 (by norm_num) hh13U
      norm_num at h
      exact h
    have hSv12 : v4 * q11 ≤ (-(889 / 2500000) : ℝ) := by
      have h := positive_negative_product_upper q11 v4
        (889 / 5000) (-(1 / 500)) hq11L hv40 (by norm_num) hv4U
      norm_num at h
      nlinarith only [h]
    have hSv13 : v4 * h11 ≤ (-(7 / 250000) : ℝ) := by
      have h := positive_negative_product_upper h11 v4
        (7 / 500) (-(1 / 500)) hh11L hv40 (by norm_num) hv4U
      norm_num at h
      nlinarith only [h]
    have hSv14 : q13 ≤ (1001 / 5000 : ℝ) := hq13U
    have hSv15 : sv ≤ (13459 / 25000 : ℝ) := hsvU
    have hSv16 : f * sv * q11 ≤
        (166232109 / 9765625000 : ℝ) := by
      have h := nonnegative_triple_upper f sv q11
        (552 / 3125) (13459 / 25000) (179 / 1000)
        hfU hsvU hq11U (by norm_num) (by norm_num) hsv0 hq110
      norm_num at h
      exact h
    unfold perturbCSlopeSv
    nlinarith only [hSv1, hSv2, hSv3, hSv4, hSv5, hSv6, hSv7,
      hSv8, hSv9, hSv10, hSv11, hSv12, hSv13, hSv14, hSv15, hSv16]
  exact hsvSlope

set_option maxHeartbeats 3000000 in
theorem perturbCSecant_upper
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    perturbCSecant a r f su u4 sv v4 q11 q13 q33 h11 h13 h33 ≤
      (-4 / 10000 : ℝ) := by
  rcases hbox.a_mem with ⟨haL, haU⟩
  rcases hbox.r_mem with ⟨hrL, hrU⟩
  rcases hbox.f_mem with ⟨hfL, hfU⟩
  rcases hbox.su_mem with ⟨hsuL, hsuU⟩
  rcases hbox.u4_mem with ⟨hu4L, hu4U⟩
  rcases hbox.sv_mem with ⟨hsvL, hsvU⟩
  rcases hbox.v4_mem with ⟨hv4L, hv4U⟩
  rcases hbox.q11_mem with ⟨hq11L, hq11U⟩
  rcases hbox.q13_mem with ⟨hq13L, hq13U⟩
  rcases hbox.q33_mem with ⟨hq33L, hq33U⟩
  rcases hbox.h11_mem with ⟨hh11L, hh11U⟩
  rcases hbox.h13_mem with ⟨hh13L, hh13U⟩
  rcases hbox.h33_mem with ⟨hh33L, hh33U⟩
  norm_num at hfL hfU hsuL hsuU hu4L hu4U hsvL hsvU hv4L hv4U hq11L hq11U hq13L hq13U hq33L hq33U hh11L hh11U hh13L hh13U hh33L hh33U
  have hf0 : (0 : ℝ) ≤ f := by linarith
  have hq110 : (0 : ℝ) ≤ q11 := by linarith
  have hq130 : (0 : ℝ) ≤ q13 := by linarith
  have hq330 : (0 : ℝ) ≤ q33 := by linarith
  have hh110 : (0 : ℝ) ≤ h11 := by linarith
  have hh130 : h13 ≤ (0 : ℝ) := by linarith
  have hh330 : h33 ≤ (0 : ℝ) := by linarith
  have hv40 : v4 ≤ (0 : ℝ) := by linarith
  have haSlope :
      perturbCSlopeA f u4 v4 q11 q13 q33 h11 h13 h33 ≤
        (-2 / 1000 : ℝ) := perturbCSlopeA_upper_box
          A X R C D F a x r c d f su du u4 sv dv v4
          q11 q13 q33 h11 h13 h33 hbox
  have hrSlope :
      perturbCSlopeR r su u4 sv v4 q11 q13 q33 h11 h13 h33 ≤
        (-8 / 1000 : ℝ) := perturbCSlopeR_upper_box
          A X R C D F a x r c d f su du u4 sv dv v4
          q11 q13 q33 h11 h13 h33 hbox
  have hsuSlope : (20 / 1000 : ℝ) ≤
      perturbCSlopeSu f su u4 sv v4 q13 q33 h13 h33 :=
        perturbCSlopeSu_lower_box A X R C D F a x r c d f
          su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox
  have hu4Slope : (35 / 1000 : ℝ) ≤
      perturbCSlopeU4 u4 sv v4 q13 q33 h13 h33 :=
        perturbCSlopeU4_lower_box A X R C D F a x r c d f
          su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox
  have hsvSlope :
      perturbCSlopeSv f sv v4 q11 q13 h11 h13 ≤ (-9 / 10000 : ℝ) :=
        perturbCSlopeSv_upper_box A X R C D F a x r c d f
          su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 hbox
  have hv4Slope :
      perturbCSlopeV4 v4 q11 q13 h11 h13 ≤ (-14 / 1000 : ℝ) := by
    have hV41 : (1 / 5 : ℝ) ≤ q13 := hq13L
    have hV42 : (-(1 / 12500) : ℝ) ≤ v4 * h11 := by
      have h := positive_negative_product_lower h11 v4
        (1 / 50) (-(1 / 250)) hh110 hv4L (by norm_num) hh11U
      norm_num at h
      nlinarith only [h]
    have hV43 : (-(179 / 250000) : ℝ) ≤ v4 * q11 := by
      have h := positive_negative_product_lower q11 v4
        (179 / 1000) (-(1 / 250)) hq110 hv4L (by norm_num) hq11U
      norm_num at h
      nlinarith only [h]
    have hV44 : q11 ≤ (179 / 1000 : ℝ) := hq11U
    have hV45 : v4 ≤ (-(1 / 500) : ℝ) := hv4U
    have hV46 : h13 ≤ (-(9 / 1000) : ℝ) := hh13U
    have hV47 : h11 ≤ (1 / 50 : ℝ) := hh11U
    unfold perturbCSlopeV4
    nlinarith only [hV41, hV42, hV43, hV44, hV45, hV46, hV47]
  have hq11Slope :
      perturbCSlopeQ11 f q33 h33 ≤ (-9 / 100 : ℝ) := by
    have hQ111 : (2924493 / 50000000 : ℝ) ≤ f * q33 := by
      have h := nonnegative_product_lower f q33
        (4411 / 25000) (663 / 2000) hfL hq33L (by norm_num) hq330
      norm_num at h
      exact h
    have hQ112 : f ≤ (552 / 3125 : ℝ) := hfU
    have hQ113 : q33 ≤ (333 / 1000 : ℝ) := hq33U
    have hQ114 : f * h33 ≤ (-(516087 / 25000000) : ℝ) := by
      have h := positive_negative_product_upper f h33
        (4411 / 25000) (-(117 / 1000)) hfL hh330 (by norm_num) hh33U
      norm_num at h
      exact h
    have hQ115 : h33 ≤ (-(117 / 1000) : ℝ) := hh33U
    unfold perturbCSlopeQ11
    nlinarith only [hQ111, hQ112, hQ113, hQ114, hQ115]
  have hq13Slope : (69 / 1000 : ℝ) ≤
      perturbCSlopeQ13 f q13 h13 := by
    have hQ131 : q13 ≤ (1001 / 5000 : ℝ) := hq13U
    have hQ132 : f * h13 ≤ (-(39699 / 25000000) : ℝ) := by
      have h := positive_negative_product_upper f h13
        (4411 / 25000) (-(9 / 1000)) hfL hh130 (by norm_num) hh13U
      norm_num at h
      exact h
    have hQ133 : h13 ≤ (-(9 / 1000) : ℝ) := hh13U
    have hQ134 : (4411 / 25000 : ℝ) ≤ f := hfL
    have hQ135 : (4411 / 125000 : ℝ) ≤ f * q13 := by
      have h := nonnegative_product_lower f q13
        (4411 / 25000) (1 / 5) hfL hq13L (by norm_num) hq130
      norm_num at h
      exact h
    unfold perturbCSlopeQ13
    nlinarith only [hQ131, hQ132, hQ133, hQ134, hQ135]
  have hq33Slope : perturbCSlopeQ33 f h11 ≤ (-20 / 1000 : ℝ) := by
    have hQ331 : (4411 / 25000 : ℝ) ≤ f := hfL
    have hQ332 : f * h11 ≤ (276 / 78125 : ℝ) := by
      have h := nonnegative_product_upper f h11
        (552 / 3125) (1 / 50) hfU hh11U (by norm_num) hh110
      norm_num at h
      exact h
    have hQ333 : h11 ≤ (1 / 50 : ℝ) := hh11U
    unfold perturbCSlopeQ33
    nlinarith only [hQ331, hQ332, hQ333]
  have hh11Slope : (6 / 1000 : ℝ) ≤ perturbCSlopeH11 f h33 := by
    have hH111 : f ≤ (552 / 3125 : ℝ) := hfU
    have hH112 : h33 ≤ (-(117 / 1000) : ℝ) := hh33U
    have hH113 : (-(1656 / 78125) : ℝ) ≤ f * h33 := by
      have h := positive_negative_product_lower f h33
        (552 / 3125) (-(3 / 25)) hf0 hh33L (by norm_num) hfU
      norm_num at h
      exact h
    unfold perturbCSlopeH11
    nlinarith only [hH111, hH112, hH113]
  have hh13Slope : perturbCSlopeH13 f h13 ≤ (-20 / 1000 : ℝ) := by
    have hH131 : (-(759 / 390625) : ℝ) ≤ f * h13 := by
      have h := positive_negative_product_lower f h13
        (552 / 3125) (-(11 / 1000)) hf0 hh13L (by norm_num) hfU
      norm_num at h
      exact h
    have hH132 : h13 ≤ (-(9 / 1000) : ℝ) := hh13U
    have hH133 : f ≤ (552 / 3125 : ℝ) := hfU
    unfold perturbCSlopeH13
    nlinarith only [hH131, hH132, hH133]
  have hfSlope : perturbCSlopeF h33 ≤ (-2 / 1000 : ℝ) := by
    unfold perturbCSlopeF
    linarith only [hh33L]
  have hh33Slope : (4 / 10000 : ℝ) ≤ perturbCSlopeH33 := by
    norm_num [perturbCSlopeH33]
  have haStep : (a - 824479 / 1000000) *
      perturbCSlopeA f u4 v4 q11 q13 q33 h11 h13 h33 ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have hrStep : (r - 49817 / 1000000) *
      perturbCSlopeR r su u4 sv v4 q11 q13 q33 h11 h13 h33 ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have hsuStep : (su - 56173 / 100000) *
      perturbCSlopeSu f su u4 sv v4 q13 q33 h13 h33 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  have hu4Step : (u4 - 18 / 125) *
      perturbCSlopeU4 u4 sv v4 q13 q33 h13 h33 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  have hsvStep : (sv - 10763 / 20000) *
      perturbCSlopeSv f sv v4 q11 q13 h11 h13 ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have hv4Step : (v4 - (-(1 / 250))) *
      perturbCSlopeV4 v4 q11 q13 h11 h13 ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have hq11Step :
      (q11 - 889 / 5000) * perturbCSlopeQ11 f q33 h33 ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have hq13Step :
      (q13 - 1001 / 5000) * perturbCSlopeQ13 f q13 h13 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  have hq33Step : (q33 - 663 / 2000) * perturbCSlopeQ33 f h11 ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have hh11Step : (h11 - 1 / 50) * perturbCSlopeH11 f h33 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  have hh13Step :
      (h13 - (-(11 / 1000))) * perturbCSlopeH13 f h13 ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have hfStep : (f - 4411 / 25000) * perturbCSlopeF h33 ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have hh33Step :
      (h33 - (-(117 / 1000))) * perturbCSlopeH33 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  have htel := perturbCSecant_telescope
    a r f su u4 sv v4 q11 q13 q33 h11 h13 h33
  have hcorner :
      perturbCSecant
          (824479 / 1000000) (49817 / 1000000) (4411 / 25000)
          (56173 / 100000) (18 / 125) (10763 / 20000) (-(1 / 250))
          (889 / 5000) (1001 / 5000) (663 / 2000)
          (1 / 50) (-(11 / 1000)) (-(117 / 1000)) <
        (-4 / 10000 : ℝ) := by
    norm_num [perturbCSecant, perturbCDetMinusSlope,
      perturbCDetMixedSlope, perturbCDetPlusSlope, perturbFOddMinor,
      perturbFOddMixed, perturbFOddS, perturbDOddSFour,
      cornerA, cornerR, cornerF]
  linarith only [htel, hcorner, haStep, hrStep, hsuStep, hu4Step,
    hsvStep, hv4Step, hq11Step, hq13Step, hq33Step, hh11Step,
    hh13Step, hfStep, hh33Step]

set_option maxHeartbeats 3000000 in
theorem correlated_even_unfix_c
    (A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33 : ℝ)
    (hbox : CorrelatedBox A X R C D F a x r c d f
      su du u4 sv dv v4 q11 q13 q33 h11 h13 h33) :
    perturbCFace a x r corner_c d f su du u4 sv dv v4
        q11 q13 q33 h11 h13 h33 ≤
      perturbCFace a x r c d f su du u4 sv dv v4
        q11 q13 q33 h11 h13 h33 := by
  have hcU := hbox.c_mem.2
  let g : ℝ → ℝ := fun z ↦
    perturbCFace a x r z d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33
  have hslope := perturbCSecant_upper
    A X R C D F a x r c d f su du u4 sv dv v4
      q11 q13 q33 h11 h13 h33 hbox
  have hsecCap : quadraticSecant g c corner_c ≤ (-4 / 10000 : ℝ) := by
    rw [show quadraticSecant g c corner_c =
        perturbCSecant a r f su u4 sv v4 q11 q13 q33 h11 h13 h33 by
      simpa only [g] using perturb_c_secant_eq
        a x r c d f su du u4 sv dv v4 q11 q13 q33 h11 h13 h33]
    exact hslope
  have hsec : quadraticSecant g c corner_c ≤ 0 :=
    le_trans hsecCap (by norm_num)
  have hid : g c - g corner_c =
      (c - corner_c) * quadraticSecant g c corner_c := by
    unfold g perturbCFace quadraticSecant correlatedCoefficientThree
      alignedDeterminant alignedMixedDeterminant alignedAdjugatePair
      alignedMixedAdjugatePair alignedCrossEnergy alignedEntry00 alignedEntry02
      alignedEntry04 alignedEntry22 alignedEntry24 mixedDeterminantOne
    dsimp only
    ring
  exact quadraticSecant_upper_endpoint g c corner_c
    (by simpa only [corner_c] using hcU) hsec hid

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveC3Structural
