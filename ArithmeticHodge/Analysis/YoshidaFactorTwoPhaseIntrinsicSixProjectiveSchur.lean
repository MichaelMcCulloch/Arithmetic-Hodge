import ArithmeticHodge.Analysis.ThreeByThreeRankOneSchur
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4Schur
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixSchurExpansion
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixSchurReduction

set_option autoImplicit false

open Real

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur

noncomputable section

open ThreeByThreeRankOneSchur
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointOddCleanPositive
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseDiskSchur
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixSchurExpansion
open YoshidaFactorTwoPhaseIntrinsicSixSchurReduction
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLowSchur

/-!
# Projective Schur form of the first six intrinsic modes

On the phase circle use the rational coordinate

`a = (1 - x) / (1 + x)`, `b = 2 t / (1 + x)`, `x = t^2`.

Multiplication by `1 + x` turns every same-parity affine pencil into the
sum of its two endpoint forms and turns every alternating entry into `t`
times a fixed entry.  After the existing `P₀/P₂` Schur elimination, the
remaining form on `(P₄,P₁,P₃,P₅)` is therefore an explicit symmetric
quadratic.  Its first three variables are handled by the structural `3 x 3`
adjugate Cauchy theorem and `P₅` is appended by one scalar Schur gate.

This module contains no estimate for the scalar entries.  It proves that the
three displayed pivots and the one final adjugate inequality are exactly
sufficient; those are the analytic frontier rather than a hidden finite
certificate.
-/

/-! ## Endpoint-homogenized scalar entries -/

/-- Polarized adjugate form of a symmetric `2 x 2` matrix. -/
def factorTwoIntrinsicSixAdjugateBilinear
    (q00 q02 q22 u0 u2 v0 v2 : ℝ) : ℝ :=
  q22 * u0 * v0 - q02 * (u0 * v2 + u2 * v0) + q00 * u2 * v2

def factorTwoIntrinsicSixProjectiveLow00 (x : ℝ) : ℝ :=
  factorTwoStructuralPhaseLow00 1 +
    x * factorTwoStructuralPhaseLow00 (-1)

def factorTwoIntrinsicSixProjectiveLow02 (x : ℝ) : ℝ :=
  factorTwoStructuralPhaseLow02 1 +
    x * factorTwoStructuralPhaseLow02 (-1)

def factorTwoIntrinsicSixProjectiveLow22 (x : ℝ) : ℝ :=
  factorTwoStructuralPhaseLow22 1 +
    x * factorTwoStructuralPhaseLow22 (-1)

def factorTwoIntrinsicSixProjectiveLowDet (x : ℝ) : ℝ :=
  factorTwoIntrinsicSixProjectiveLow00 x *
      factorTwoIntrinsicSixProjectiveLow22 x -
    factorTwoIntrinsicSixProjectiveLow02 x ^ 2

def factorTwoIntrinsicSixProjectiveCross04 (x : ℝ) : ℝ :=
  factorTwoIntrinsicFourP45Cross04 1 +
    x * factorTwoIntrinsicFourP45Cross04 (-1)

def factorTwoIntrinsicSixProjectiveCross24 (x : ℝ) : ℝ :=
  factorTwoIntrinsicFourP45Cross24 1 +
    x * factorTwoIntrinsicFourP45Cross24 (-1)

def factorTwoIntrinsicSixProjectiveOdd11 (x : ℝ) : ℝ :=
  factorTwoIntrinsicOddPhaseLow11 1 +
    x * factorTwoIntrinsicOddPhaseLow11 (-1)

def factorTwoIntrinsicSixProjectiveOdd13 (x : ℝ) : ℝ :=
  factorTwoIntrinsicOddPhaseLow13 1 +
    x * factorTwoIntrinsicOddPhaseLow13 (-1)

def factorTwoIntrinsicSixProjectiveOdd33 (x : ℝ) : ℝ :=
  factorTwoIntrinsicOddPhaseLow33 1 +
    x * factorTwoIntrinsicOddPhaseLow33 (-1)

def factorTwoIntrinsicSixProjectiveOdd15 (x : ℝ) : ℝ :=
  factorTwoIntrinsicFourP45Cross15 1 +
    x * factorTwoIntrinsicFourP45Cross15 (-1)

def factorTwoIntrinsicSixProjectiveOdd35 (x : ℝ) : ℝ :=
  factorTwoIntrinsicFourP45Cross35 1 +
    x * factorTwoIntrinsicFourP45Cross35 (-1)

def factorTwoIntrinsicSixP4Diagonal (a : ℝ) : ℝ :=
  factorTwoEndpointPhaseDiagonal factorTwoCenteredP4 a

def factorTwoIntrinsicSixP5Diagonal (a : ℝ) : ℝ :=
  factorTwoEndpointPhaseDiagonal factorTwoCenteredP5 a

def factorTwoIntrinsicSixProjectiveP4Diagonal (x : ℝ) : ℝ :=
  factorTwoIntrinsicSixP4Diagonal 1 +
    x * factorTwoIntrinsicSixP4Diagonal (-1)

def factorTwoIntrinsicSixProjectiveP5Diagonal (x : ℝ) : ℝ :=
  factorTwoIntrinsicSixP5Diagonal 1 +
    x * factorTwoIntrinsicSixP5Diagonal (-1)

def factorTwoIntrinsicSixAlternating45 : ℝ :=
  factorTwoCenteredAlternatingCoupling
    factorTwoCenteredP4 factorTwoCenteredP5

/-! ## The exact residual coefficients -/

private def projectiveAdj
    (x u0 u2 v0 v2 : ℝ) : ℝ :=
  factorTwoIntrinsicSixAdjugateBilinear
    (factorTwoIntrinsicSixProjectiveLow00 x)
    (factorTwoIntrinsicSixProjectiveLow02 x)
    (factorTwoIntrinsicSixProjectiveLow22 x)
    u0 u2 v0 v2

def factorTwoIntrinsicSixProjectiveP4Pivot (x : ℝ) : ℝ :=
  factorTwoIntrinsicSixProjectiveLowDet x *
      factorTwoIntrinsicSixProjectiveP4Diagonal x -
    projectiveAdj x
      (factorTwoIntrinsicSixProjectiveCross04 x)
      (factorTwoIntrinsicSixProjectiveCross24 x)
      (factorTwoIntrinsicSixProjectiveCross04 x)
      (factorTwoIntrinsicSixProjectiveCross24 x)

private def projectiveLowAlternating0 (i : Fin 3) : ℝ :=
  match i with
  | 0 => factorTwoIntrinsicAlternating01
  | 1 => factorTwoIntrinsicAlternating03
  | 2 => factorTwoIntrinsicFourP45Cross05

private def projectiveLowAlternating2 (i : Fin 3) : ℝ :=
  match i with
  | 0 => factorTwoIntrinsicAlternating21
  | 1 => factorTwoIntrinsicAlternating23
  | 2 => factorTwoIntrinsicFourP45Cross25

private def projectiveP4Alternating (i : Fin 3) : ℝ :=
  match i with
  | 0 => factorTwoIntrinsicFourP45Cross41
  | 1 => factorTwoIntrinsicFourP45Cross43
  | 2 => factorTwoIntrinsicSixAlternating45

private def projectiveOddEntry (x : ℝ) (i j : Fin 3) : ℝ :=
  match i, j with
  | 0, 0 => factorTwoIntrinsicSixProjectiveOdd11 x
  | 0, 1 => factorTwoIntrinsicSixProjectiveOdd13 x
  | 1, 0 => factorTwoIntrinsicSixProjectiveOdd13 x
  | 0, 2 => factorTwoIntrinsicSixProjectiveOdd15 x
  | 2, 0 => factorTwoIntrinsicSixProjectiveOdd15 x
  | 1, 1 => factorTwoIntrinsicSixProjectiveOdd33 x
  | 1, 2 => factorTwoIntrinsicSixProjectiveOdd35 x
  | 2, 1 => factorTwoIntrinsicSixProjectiveOdd35 x
  | 2, 2 => factorTwoIntrinsicSixProjectiveP5Diagonal x

def factorTwoIntrinsicSixProjectiveP4OddCross
    (x : ℝ) (i : Fin 3) : ℝ :=
  factorTwoIntrinsicSixProjectiveLowDet x * projectiveP4Alternating i -
    projectiveAdj x
      (factorTwoIntrinsicSixProjectiveCross04 x)
      (factorTwoIntrinsicSixProjectiveCross24 x)
      (projectiveLowAlternating0 i)
      (projectiveLowAlternating2 i)

def factorTwoIntrinsicSixProjectiveOddResidual
    (x : ℝ) (i j : Fin 3) : ℝ :=
  factorTwoIntrinsicSixProjectiveLowDet x * projectiveOddEntry x i j -
    x * projectiveAdj x
      (projectiveLowAlternating0 i)
      (projectiveLowAlternating2 i)
      (projectiveLowAlternating0 j)
      (projectiveLowAlternating2 j)

/-! ## Direct homogeneous coordinates -/

/-- Homogeneous `P₀`-to-tail coordinate before the low Schur elimination. -/
def factorTwoIntrinsicSixProjectiveLowTail0
    (t x c4 c1 c3 c5 : ℝ) : ℝ :=
  c4 * factorTwoIntrinsicSixProjectiveCross04 x +
    t * (factorTwoIntrinsicAlternating01 * c1 +
      factorTwoIntrinsicAlternating03 * c3 +
      c5 * factorTwoIntrinsicFourP45Cross05)

/-- Homogeneous `P₂`-to-tail coordinate before the low Schur elimination. -/
def factorTwoIntrinsicSixProjectiveLowTail2
    (t x c4 c1 c3 c5 : ℝ) : ℝ :=
  c4 * factorTwoIntrinsicSixProjectiveCross24 x +
    t * (factorTwoIntrinsicAlternating21 * c1 +
      factorTwoIntrinsicAlternating23 * c3 +
      c5 * factorTwoIntrinsicFourP45Cross25)

/-- Homogeneous tail quadratic before the low Schur elimination. -/
def factorTwoIntrinsicSixProjectiveTailQuadratic
    (t x c4 c1 c3 c5 : ℝ) : ℝ :=
  factorTwoIntrinsicSixProjectiveOdd11 x * c1 ^ 2 +
    2 * factorTwoIntrinsicSixProjectiveOdd13 x * c1 * c3 +
    factorTwoIntrinsicSixProjectiveOdd33 x * c3 ^ 2 +
    factorTwoIntrinsicSixProjectiveP4Diagonal x * c4 ^ 2 +
    2 * t * factorTwoIntrinsicSixAlternating45 * c4 * c5 +
    factorTwoIntrinsicSixProjectiveP5Diagonal x * c5 ^ 2 +
    2 * (c5 *
        (c1 * factorTwoIntrinsicSixProjectiveOdd15 x +
          c3 * factorTwoIntrinsicSixProjectiveOdd35 x) +
      t * c4 *
        (c1 * factorTwoIntrinsicFourP45Cross41 +
          c3 * factorTwoIntrinsicFourP45Cross43))

/-- The direct homogeneous low-Schur residual.  The sequential `3 + 1`
form below is an exact regrouping of this expression. -/
def factorTwoIntrinsicSixProjectiveRawResidual
    (t x c4 c1 c3 c5 : ℝ) : ℝ :=
  factorTwoIntrinsicSixProjectiveLowDet x *
      factorTwoIntrinsicSixProjectiveTailQuadratic t x c4 c1 c3 c5 -
    factorTwoIntrinsicSixAdjugateBilinear
      (factorTwoIntrinsicSixProjectiveLow00 x)
      (factorTwoIntrinsicSixProjectiveLow02 x)
      (factorTwoIntrinsicSixProjectiveLow22 x)
      (factorTwoIntrinsicSixProjectiveLowTail0 t x c4 c1 c3 c5)
      (factorTwoIntrinsicSixProjectiveLowTail2 t x c4 c1 c3 c5)
      (factorTwoIntrinsicSixProjectiveLowTail0 t x c4 c1 c3 c5)
      (factorTwoIntrinsicSixProjectiveLowTail2 t x c4 c1 c3 c5)

/-! ## The `3 + 1` sequential Schur data -/

def factorTwoIntrinsicSixProjectiveBaseQuadratic
    (t x c4 c1 c3 : ℝ) : ℝ :=
  symmetricQuadratic
    (factorTwoIntrinsicSixProjectiveP4Pivot x)
    (t * factorTwoIntrinsicSixProjectiveP4OddCross x 0)
    (t * factorTwoIntrinsicSixProjectiveP4OddCross x 1)
    (factorTwoIntrinsicSixProjectiveOddResidual x 0 0)
    (factorTwoIntrinsicSixProjectiveOddResidual x 0 1)
    (factorTwoIntrinsicSixProjectiveOddResidual x 1 1)
    c4 c1 c3

def factorTwoIntrinsicSixProjectiveP5Linear
    (t x c4 c1 c3 : ℝ) : ℝ :=
  t * factorTwoIntrinsicSixProjectiveP4OddCross x 2 * c4 +
    factorTwoIntrinsicSixProjectiveOddResidual x 0 2 * c1 +
    factorTwoIntrinsicSixProjectiveOddResidual x 1 2 * c3

def factorTwoIntrinsicSixProjectiveP5DiagonalResidual (x : ℝ) : ℝ :=
  factorTwoIntrinsicSixProjectiveOddResidual x 2 2

def factorTwoIntrinsicSixProjectiveResidual
    (t x c4 c1 c3 c5 : ℝ) : ℝ :=
  factorTwoIntrinsicSixProjectiveBaseQuadratic t x c4 c1 c3 +
    2 * c5 * factorTwoIntrinsicSixProjectiveP5Linear t x c4 c1 c3 +
    factorTwoIntrinsicSixProjectiveP5DiagonalResidual x * c5 ^ 2

def factorTwoIntrinsicSixProjectiveBaseMinorTwo (t x : ℝ) : ℝ :=
  leadingMinorTwo
    (factorTwoIntrinsicSixProjectiveP4Pivot x)
    (t * factorTwoIntrinsicSixProjectiveP4OddCross x 0)
    (factorTwoIntrinsicSixProjectiveOddResidual x 0 0)

def factorTwoIntrinsicSixProjectiveBaseDet (t x : ℝ) : ℝ :=
  symmetricDeterminant
    (factorTwoIntrinsicSixProjectiveP4Pivot x)
    (t * factorTwoIntrinsicSixProjectiveP4OddCross x 0)
    (t * factorTwoIntrinsicSixProjectiveP4OddCross x 1)
    (factorTwoIntrinsicSixProjectiveOddResidual x 0 0)
    (factorTwoIntrinsicSixProjectiveOddResidual x 0 1)
    (factorTwoIntrinsicSixProjectiveOddResidual x 1 1)

def factorTwoIntrinsicSixProjectiveP5Adjugate (t x : ℝ) : ℝ :=
  adjugateQuadratic
    (factorTwoIntrinsicSixProjectiveP4Pivot x)
    (t * factorTwoIntrinsicSixProjectiveP4OddCross x 0)
    (t * factorTwoIntrinsicSixProjectiveP4OddCross x 1)
    (factorTwoIntrinsicSixProjectiveOddResidual x 0 0)
    (factorTwoIntrinsicSixProjectiveOddResidual x 0 1)
    (factorTwoIntrinsicSixProjectiveOddResidual x 1 1)
    (t * factorTwoIntrinsicSixProjectiveP4OddCross x 2)
    (factorTwoIntrinsicSixProjectiveOddResidual x 0 2)
    (factorTwoIntrinsicSixProjectiveOddResidual x 1 2)

/-- The displayed sequential coefficients are exactly the coefficientwise
expansion of the homogeneous low-Schur residual. -/
theorem factorTwoIntrinsicSixProjectiveResidual_eq_raw
    (t x c4 c1 c3 c5 : ℝ) (hx : x = t ^ 2) :
    factorTwoIntrinsicSixProjectiveResidual t x c4 c1 c3 c5 =
      factorTwoIntrinsicSixProjectiveRawResidual t x c4 c1 c3 c5 := by
  subst x
  unfold factorTwoIntrinsicSixProjectiveResidual
    factorTwoIntrinsicSixProjectiveBaseQuadratic
    factorTwoIntrinsicSixProjectiveP5Linear
    factorTwoIntrinsicSixProjectiveP5DiagonalResidual
    factorTwoIntrinsicSixProjectiveP4Pivot
    factorTwoIntrinsicSixProjectiveP4OddCross
    factorTwoIntrinsicSixProjectiveOddResidual projectiveAdj
    factorTwoIntrinsicSixProjectiveRawResidual
    factorTwoIntrinsicSixProjectiveTailQuadratic
    factorTwoIntrinsicSixProjectiveLowTail0
    factorTwoIntrinsicSixProjectiveLowTail2
    factorTwoIntrinsicSixAdjugateBilinear symmetricQuadratic
  simp only [projectiveLowAlternating0, projectiveLowAlternating2,
    projectiveP4Alternating, projectiveOddEntry]
  ring

/-! ## Exact projective homogenization -/

/-- On the rational parametrization of the phase circle, the original
six-mode Schur residual is exactly the projective residual above.  The
factor `(1 + x)^3` is the common homogeneous denominator: one factor comes
from the tail pencil and two from the eliminated `P₀/P₂` determinant. -/
theorem factorTwoIntrinsicSixSchurResidual_projective
    (t x c4 c1 c3 c5 : ℝ) (hx : x = t ^ 2) :
    (1 + x) ^ 3 *
        factorTwoIntrinsicSixSchurResidual c4 c1 c3 c5
          ((1 - x) / (1 + x)) (2 * t / (1 + x)) =
      factorTwoIntrinsicSixProjectiveResidual t x c4 c1 c3 c5 := by
  subst x
  have hden : 1 + t ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg t]
  have h00 :
      (1 + t ^ 2) *
          factorTwoStructuralPhaseLow00
            ((1 - t ^ 2) / (1 + t ^ 2)) =
        factorTwoIntrinsicSixProjectiveLow00 (t ^ 2) := by
    unfold factorTwoIntrinsicSixProjectiveLow00
      factorTwoStructuralPhaseLow00
    field_simp [hden]
    ring
  have h02 :
      (1 + t ^ 2) *
          factorTwoStructuralPhaseLow02
            ((1 - t ^ 2) / (1 + t ^ 2)) =
        factorTwoIntrinsicSixProjectiveLow02 (t ^ 2) := by
    unfold factorTwoIntrinsicSixProjectiveLow02
      factorTwoStructuralPhaseLow02
    field_simp [hden]
    ring
  have h22 :
      (1 + t ^ 2) *
          factorTwoStructuralPhaseLow22
            ((1 - t ^ 2) / (1 + t ^ 2)) =
        factorTwoIntrinsicSixProjectiveLow22 (t ^ 2) := by
    unfold factorTwoIntrinsicSixProjectiveLow22
      factorTwoStructuralPhaseLow22
    field_simp [hden]
    ring
  have hLowTail0 :
      (1 + t ^ 2) *
          factorTwoIntrinsicSixLowTail0 c4 c1 c3 c5
            ((1 - t ^ 2) / (1 + t ^ 2))
            (2 * t / (1 + t ^ 2)) =
        factorTwoIntrinsicSixProjectiveLowTail0
          t (t ^ 2) c4 c1 c3 c5 := by
    unfold factorTwoIntrinsicSixLowTail0
      factorTwoIntrinsicSixProjectiveLowTail0
      factorTwoIntrinsicSixProjectiveCross04
      factorTwoIntrinsicFourP45Cross04
      factorTwoIntrinsicAlternatingRow0
    field_simp [hden]
    ring
  have hLowTail2 :
      (1 + t ^ 2) *
          factorTwoIntrinsicSixLowTail2 c4 c1 c3 c5
            ((1 - t ^ 2) / (1 + t ^ 2))
            (2 * t / (1 + t ^ 2)) =
        factorTwoIntrinsicSixProjectiveLowTail2
          t (t ^ 2) c4 c1 c3 c5 := by
    unfold factorTwoIntrinsicSixLowTail2
      factorTwoIntrinsicSixProjectiveLowTail2
      factorTwoIntrinsicSixProjectiveCross24
      factorTwoIntrinsicFourP45Cross24
      factorTwoIntrinsicAlternatingRow2
    field_simp [hden]
    ring
  have hTail :
      (1 + t ^ 2) *
          factorTwoIntrinsicSixTailQuadratic c4 c1 c3 c5
            ((1 - t ^ 2) / (1 + t ^ 2))
            (2 * t / (1 + t ^ 2)) =
        factorTwoIntrinsicSixProjectiveTailQuadratic
          t (t ^ 2) c4 c1 c3 c5 := by
    unfold factorTwoIntrinsicSixTailQuadratic
    rw [factorTwoEndpointChannelPhase_P4_P5_expansion]
    unfold factorTwoIntrinsicOddPhaseQuadratic
      factorTwoIntrinsicP4PhaseDiagonal factorTwoIntrinsicP5PhaseDiagonal
      factorTwoIntrinsicSixProjectiveTailQuadratic
      factorTwoIntrinsicSixProjectiveOdd11
      factorTwoIntrinsicSixProjectiveOdd13
      factorTwoIntrinsicSixProjectiveOdd33
      factorTwoIntrinsicSixProjectiveOdd15
      factorTwoIntrinsicSixProjectiveOdd35
      factorTwoIntrinsicSixProjectiveP4Diagonal
      factorTwoIntrinsicSixProjectiveP5Diagonal
      factorTwoIntrinsicSixP4Diagonal factorTwoIntrinsicSixP5Diagonal
      factorTwoIntrinsicSixAlternating45 factorTwoIntrinsicP45Alternating
      factorTwoIntrinsicOddPhaseLow11 factorTwoIntrinsicOddPhaseLow13
      factorTwoIntrinsicOddPhaseLow33 factorTwoIntrinsicFourP45Cross15
      factorTwoIntrinsicFourP45Cross35
      YoshidaFactorTwoPhaseDiskSchur.factorTwoEndpointPhaseDiagonal
    field_simp [hden]
    ring
  have h00' :
      factorTwoStructuralPhaseLow00
          ((1 - t ^ 2) / (1 + t ^ 2)) =
        factorTwoIntrinsicSixProjectiveLow00 (t ^ 2) / (1 + t ^ 2) := by
    apply (eq_div_iff hden).2
    simpa only [mul_comm] using h00
  have h02' :
      factorTwoStructuralPhaseLow02
          ((1 - t ^ 2) / (1 + t ^ 2)) =
        factorTwoIntrinsicSixProjectiveLow02 (t ^ 2) / (1 + t ^ 2) := by
    apply (eq_div_iff hden).2
    simpa only [mul_comm] using h02
  have h22' :
      factorTwoStructuralPhaseLow22
          ((1 - t ^ 2) / (1 + t ^ 2)) =
        factorTwoIntrinsicSixProjectiveLow22 (t ^ 2) / (1 + t ^ 2) := by
    apply (eq_div_iff hden).2
    simpa only [mul_comm] using h22
  have hLowTail0' :
      factorTwoIntrinsicSixLowTail0 c4 c1 c3 c5
          ((1 - t ^ 2) / (1 + t ^ 2))
          (2 * t / (1 + t ^ 2)) =
        factorTwoIntrinsicSixProjectiveLowTail0
            t (t ^ 2) c4 c1 c3 c5 /
          (1 + t ^ 2) := by
    apply (eq_div_iff hden).2
    simpa only [mul_comm] using hLowTail0
  have hLowTail2' :
      factorTwoIntrinsicSixLowTail2 c4 c1 c3 c5
          ((1 - t ^ 2) / (1 + t ^ 2))
          (2 * t / (1 + t ^ 2)) =
        factorTwoIntrinsicSixProjectiveLowTail2
            t (t ^ 2) c4 c1 c3 c5 /
          (1 + t ^ 2) := by
    apply (eq_div_iff hden).2
    simpa only [mul_comm] using hLowTail2
  have hTail' :
      factorTwoIntrinsicSixTailQuadratic c4 c1 c3 c5
          ((1 - t ^ 2) / (1 + t ^ 2))
          (2 * t / (1 + t ^ 2)) =
        factorTwoIntrinsicSixProjectiveTailQuadratic
            t (t ^ 2) c4 c1 c3 c5 /
          (1 + t ^ 2) := by
    apply (eq_div_iff hden).2
    simpa only [mul_comm] using hTail
  rw [factorTwoIntrinsicSixSchurResidual_eq_expansion,
    h00', h02', h22', hLowTail0', hLowTail2', hTail',
    factorTwoIntrinsicSixProjectiveResidual_eq_raw
      t (t ^ 2) c4 c1 c3 c5 rfl]
  unfold factorTwoIntrinsicSixProjectiveRawResidual
    factorTwoIntrinsicSixProjectiveLowDet
    factorTwoIntrinsicSixAdjugateBilinear
  field_simp [hden]
  ring

/-! ## Pure sequential closure -/

/-- Three strict pivots for the five-mode base and one adjugate gate for
`P₅` imply nonnegativity of the complete projective residual. -/
theorem factorTwoIntrinsicSixProjectiveResidual_nonneg_of_schur
    (t x c4 c1 c3 c5 : ℝ)
    (h00 : 0 < factorTwoIntrinsicSixProjectiveP4Pivot x)
    (hminor : 0 < factorTwoIntrinsicSixProjectiveBaseMinorTwo t x)
    (hdet : 0 < factorTwoIntrinsicSixProjectiveBaseDet t x)
    (hfinal : factorTwoIntrinsicSixProjectiveP5Adjugate t x ≤
      factorTwoIntrinsicSixProjectiveBaseDet t x *
        factorTwoIntrinsicSixProjectiveP5DiagonalResidual x) :
    0 ≤ factorTwoIntrinsicSixProjectiveResidual
      t x c4 c1 c3 c5 := by
  let Q := factorTwoIntrinsicSixProjectiveBaseQuadratic t x c4 c1 c3
  let L := factorTwoIntrinsicSixProjectiveP5Linear t x c4 c1 c3
  let T := factorTwoIntrinsicSixProjectiveBaseDet t x
  let A := factorTwoIntrinsicSixProjectiveP5Adjugate t x
  let C := factorTwoIntrinsicSixProjectiveP5DiagonalResidual x
  have hQ : 0 ≤ Q := by
    dsimp only [Q, factorTwoIntrinsicSixProjectiveBaseQuadratic]
    exact symmetricQuadratic_nonneg _ _ _ _ _ _ h00 hminor hdet _ _ _
  have hA : 0 ≤ A := by
    dsimp only [A, factorTwoIntrinsicSixProjectiveP5Adjugate]
    exact adjugateQuadratic_nonneg _ _ _ _ _ _ h00 hminor hdet _ _ _
  have hC : 0 ≤ C := by
    have hTC : 0 ≤ T * C := hA.trans (by
      simpa only [T, A, C] using hfinal)
    have hT : 0 < T := by simpa only [T] using hdet
    nlinarith
  have hCauchy : T * L ^ 2 ≤ Q * A := by
    dsimp only [T, L, Q, A,
      factorTwoIntrinsicSixProjectiveBaseDet,
      factorTwoIntrinsicSixProjectiveBaseQuadratic,
      factorTwoIntrinsicSixProjectiveP5Linear,
      factorTwoIntrinsicSixProjectiveP5Adjugate]
    exact adjugate_cauchy _ _ _ _ _ _ h00 hminor hdet _ _ _ _ _ _
  have hLC : L ^ 2 ≤ Q * C := by
    have hQA : Q * A ≤ Q * (T * C) :=
      mul_le_mul_of_nonneg_left (by
        simpa only [T, A, C] using hfinal) hQ
    have hscaled : T * L ^ 2 ≤ T * (Q * C) := by
      calc
        T * L ^ 2 ≤ Q * A := hCauchy
        _ ≤ Q * (T * C) := hQA
        _ = T * (Q * C) := by ring
    have hT : 0 < T := by simpa only [T] using hdet
    nlinarith
  have hmixed : (c5 * L) ^ 2 ≤ Q * (C * c5 ^ 2) := by
    have hs := mul_le_mul_of_nonneg_left hLC (sq_nonneg c5)
    nlinarith
  have hsum := ArithmeticHodge.Analysis.TwoByTwoSchur.scalar_low_tail_nonneg
    Q (C * c5 ^ 2) (c5 * L) hQ
    (mul_nonneg hC (sq_nonneg c5)) hmixed
  dsimp only [factorTwoIntrinsicSixProjectiveResidual, Q, L, C]
  nlinarith

/-- The four projective Schur gates imply nonnegativity of the original
six-mode residual at the corresponding point of the phase circle. -/
theorem factorTwoIntrinsicSixSchurResidual_nonneg_of_projective_schur
    (t x c4 c1 c3 c5 : ℝ) (hx : x = t ^ 2)
    (h00 : 0 < factorTwoIntrinsicSixProjectiveP4Pivot x)
    (hminor : 0 < factorTwoIntrinsicSixProjectiveBaseMinorTwo t x)
    (hdet : 0 < factorTwoIntrinsicSixProjectiveBaseDet t x)
    (hfinal : factorTwoIntrinsicSixProjectiveP5Adjugate t x ≤
      factorTwoIntrinsicSixProjectiveBaseDet t x *
        factorTwoIntrinsicSixProjectiveP5DiagonalResidual x) :
    0 ≤ factorTwoIntrinsicSixSchurResidual c4 c1 c3 c5
      ((1 - x) / (1 + x)) (2 * t / (1 + x)) := by
  have hprojective :=
    factorTwoIntrinsicSixProjectiveResidual_nonneg_of_schur
      t x c4 c1 c3 c5 h00 hminor hdet hfinal
  have hscaled :
      0 ≤ (1 + x) ^ 3 *
        factorTwoIntrinsicSixSchurResidual c4 c1 c3 c5
          ((1 - x) / (1 + x)) (2 * t / (1 + x)) := by
    rw [factorTwoIntrinsicSixSchurResidual_projective
      t x c4 c1 c3 c5 hx]
    exact hprojective
  have hfactor : 0 < (1 + x) ^ 3 := by
    have hx_nonneg : 0 ≤ x := by rw [hx]; exact sq_nonneg t
    exact pow_pos (by linarith) 3
  have hscaled' :
      0 ≤ factorTwoIntrinsicSixSchurResidual c4 c1 c3 c5
          ((1 - x) / (1 + x)) (2 * t / (1 + x)) *
        (1 + x) ^ 3 := by
    simpa only [mul_comm] using hscaled
  exact nonneg_of_mul_nonneg_left hscaled' hfactor

/-- Final structural six-mode phase closure on the rational phase-circle
chart.  Apart from the exact chart relation `x = t²`, the only assumptions
are the three Sylvester pivots and the final `P₅` adjugate gate. -/
theorem factorTwoEndpointChannelPhase_intrinsicSix_nonneg_of_projective_schur
    (c0 c2 c4 c1 c3 c5 t x : ℝ) (hx : x = t ^ 2)
    (h00 : 0 < factorTwoIntrinsicSixProjectiveP4Pivot x)
    (hminor : 0 < factorTwoIntrinsicSixProjectiveBaseMinorTwo t x)
    (hdet : 0 < factorTwoIntrinsicSixProjectiveBaseDet t x)
    (hfinal : factorTwoIntrinsicSixProjectiveP5Adjugate t x ≤
      factorTwoIntrinsicSixProjectiveBaseDet t x *
        factorTwoIntrinsicSixProjectiveP5DiagonalResidual x) :
    0 ≤ factorTwoEndpointChannelPhase
      (factorTwoEvenStructuralLowProfile c0 c2 +
        factorTwoIntrinsicSixEvenTail c4)
      (factorTwoIntrinsicSixOddTail c1 c3 c5)
      ((1 - x) / (1 + x)) (2 * t / (1 + x)) := by
  have hden : 1 + x ≠ 0 := by
    rw [hx]
    nlinarith [sq_nonneg t]
  have hcircle :
      ((1 - x) / (1 + x)) ^ 2 +
          (2 * t / (1 + x)) ^ 2 = 1 := by
    field_simp [hden]
    rw [hx]
    ring
  apply factorTwoEndpointChannelPhase_intrinsicSix_nonneg_of_schur
    c0 c2 c4 c1 c3 c5
      ((1 - x) / (1 + x)) (2 * t / (1 + x)) hcircle.le
  exact factorTwoIntrinsicSixSchurResidual_nonneg_of_projective_schur
    t x c4 c1 c3 c5 hx h00 hminor hdet hfinal

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur
