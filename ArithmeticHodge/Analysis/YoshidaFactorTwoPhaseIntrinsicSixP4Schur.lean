import ArithmeticHodge.Analysis.ThreeByThreeRankOneSchur
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixSchurExpansion

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4Schur

noncomputable section

open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddLowGramExpansion
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointChannelRadius
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicSixSchurExpansion
open YoshidaFactorTwoPhaseIntrinsicSixSchurReduction
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLowSchur

/-!
# Sequential `P₄` Schur form of the intrinsic six-mode residual

The residual left after eliminating `P₀/P₂` is quadratic in `c₄`.
Its leading coefficient is the even `P₀/P₂/P₄` determinant, its
constant coefficient is the odd `P₁/P₃/P₅` Schur form, and its mixed
coefficient is one linear row.  One scalar Cauchy gate therefore closes the
whole four-variable residual.
-/

def factorTwoIntrinsicP4PhaseDiagonal (a : ℝ) : ℝ :=
  yoshidaEndpointOddCleanQuadratic factorTwoCenteredP4 +
    a * factorTwoCenteredSymmetricPerturbation factorTwoCenteredP4

def factorTwoIntrinsicP5PhaseDiagonal (a : ℝ) : ℝ :=
  yoshidaEndpointOddCleanQuadratic factorTwoCenteredP5 +
    a * factorTwoCenteredSymmetricPerturbation factorTwoCenteredP5

def factorTwoIntrinsicP45Alternating : ℝ :=
  factorTwoCenteredAlternatingCoupling
    factorTwoCenteredP4 factorTwoCenteredP5

theorem factorTwoEndpointChannelPhase_P4_P5_expansion
    (c4 c5 a b : ℝ) :
    factorTwoEndpointChannelPhase
        (fun x ↦ c4 * factorTwoCenteredP4 x)
        (fun x ↦ c5 * factorTwoCenteredP5 x) a b =
      factorTwoIntrinsicP4PhaseDiagonal a * c4 ^ 2 +
        b * factorTwoIntrinsicP45Alternating * c4 * c5 +
        factorTwoIntrinsicP5PhaseDiagonal a * c5 ^ 2 := by
  have heSym :
      factorTwoCenteredSymmetricPerturbation
          (fun x ↦ c4 * factorTwoCenteredP4 x) =
        c4 ^ 2 *
          factorTwoCenteredSymmetricPerturbation factorTwoCenteredP4 := by
    simpa [smul_eq_mul] using
      factorTwoCenteredSymmetricPerturbation_smul
        c4 factorTwoCenteredP4
  have hoSym :
      factorTwoCenteredSymmetricPerturbation
          (fun x ↦ c5 * factorTwoCenteredP5 x) =
        c5 ^ 2 *
          factorTwoCenteredSymmetricPerturbation factorTwoCenteredP5 := by
    simpa [smul_eq_mul] using
      factorTwoCenteredSymmetricPerturbation_smul
        c5 factorTwoCenteredP5
  have hAlt :
      factorTwoCenteredAlternatingCoupling
          (fun x ↦ c4 * factorTwoCenteredP4 x)
          (fun x ↦ c5 * factorTwoCenteredP5 x) =
        c4 * c5 * factorTwoCenteredAlternatingCoupling
          factorTwoCenteredP4 factorTwoCenteredP5 := by
    change factorTwoCenteredAlternatingCoupling
        (c4 • factorTwoCenteredP4) (c5 • factorTwoCenteredP5) = _
    rw [factorTwoCenteredAlternatingCoupling_smul_left,
      factorTwoCenteredAlternatingCoupling_smul_right]
    ring
  unfold factorTwoEndpointChannelPhase factorTwoEndpointChannelCleanSum
    factorTwoEndpointChannelSymmetricSum
    factorTwoIntrinsicP4PhaseDiagonal
    factorTwoIntrinsicP5PhaseDiagonal factorTwoIntrinsicP45Alternating
  rw [yoshidaEndpointOddCleanQuadratic_const_mul,
    yoshidaEndpointOddCleanQuadratic_const_mul, heSym, hoSym, hAlt]
  ring

/-- Determinant of the already-eliminated `P₀/P₂` block. -/
def factorTwoIntrinsicSixLowDet (a : ℝ) : ℝ :=
  factorTwoStructuralPhaseLow00 a * factorTwoStructuralPhaseLow22 a -
    factorTwoStructuralPhaseLow02 a ^ 2

/-- The two `P₄` columns into the `P₀/P₂` block. -/
def factorTwoIntrinsicSixP4Low0 (a : ℝ) : ℝ :=
  factorTwoIntrinsicFourP45Cross04 a

def factorTwoIntrinsicSixP4Low2 (a : ℝ) : ℝ :=
  factorTwoIntrinsicFourP45Cross24 a

/-- The odd-side columns into `P₀/P₂`. -/
def factorTwoIntrinsicSixOddLow0
    (c1 c3 c5 b : ℝ) : ℝ :=
  (b / 2) *
    (factorTwoIntrinsicAlternatingRow0 c1 c3 +
      c5 * factorTwoIntrinsicFourP45Cross05)

def factorTwoIntrinsicSixOddLow2
    (c1 c3 c5 b : ℝ) : ℝ :=
  (b / 2) *
    (factorTwoIntrinsicAlternatingRow2 c1 c3 +
      c5 * factorTwoIntrinsicFourP45Cross25)

/-- The `c₄`-linear row of the tail phase. -/
def factorTwoIntrinsicSixP4TailRow
    (c1 c3 c5 b : ℝ) : ℝ :=
  (b / 2) *
    (c5 * factorTwoIntrinsicP45Alternating +
      c1 * factorTwoIntrinsicFourP45Cross41 +
      c3 * factorTwoIntrinsicFourP45Cross43)

/-- Tail phase restricted to the odd `P₁/P₃/P₅` plane. -/
def factorTwoIntrinsicSixOddTailQuadratic
    (c1 c3 c5 a : ℝ) : ℝ :=
  factorTwoIntrinsicOddPhaseQuadratic a c1 c3 +
    factorTwoIntrinsicP5PhaseDiagonal a * c5 ^ 2 +
    2 * c5 *
      (c1 * factorTwoIntrinsicFourP45Cross15 a +
        c3 * factorTwoIntrinsicFourP45Cross35 a)

/-- Leading `c₄²` coefficient: the even `P₀/P₂/P₄` Schur
determinant. -/
def factorTwoIntrinsicSixP4SchurLeading (a : ℝ) : ℝ :=
  factorTwoIntrinsicSixLowDet a * factorTwoIntrinsicP4PhaseDiagonal a -
    (factorTwoStructuralPhaseLow22 a *
          factorTwoIntrinsicSixP4Low0 a ^ 2 -
      2 * factorTwoStructuralPhaseLow02 a *
          factorTwoIntrinsicSixP4Low0 a *
          factorTwoIntrinsicSixP4Low2 a +
      factorTwoStructuralPhaseLow00 a *
          factorTwoIntrinsicSixP4Low2 a ^ 2)

/-- Linear `c₄` coefficient after the first Schur elimination. -/
def factorTwoIntrinsicSixP4SchurMixed
    (c1 c3 c5 a b : ℝ) : ℝ :=
  factorTwoIntrinsicSixLowDet a *
      factorTwoIntrinsicSixP4TailRow c1 c3 c5 b -
    (factorTwoStructuralPhaseLow22 a *
          factorTwoIntrinsicSixP4Low0 a *
          factorTwoIntrinsicSixOddLow0 c1 c3 c5 b -
      factorTwoStructuralPhaseLow02 a *
          (factorTwoIntrinsicSixP4Low0 a *
              factorTwoIntrinsicSixOddLow2 c1 c3 c5 b +
            factorTwoIntrinsicSixP4Low2 a *
              factorTwoIntrinsicSixOddLow0 c1 c3 c5 b) +
      factorTwoStructuralPhaseLow00 a *
          factorTwoIntrinsicSixP4Low2 a *
          factorTwoIntrinsicSixOddLow2 c1 c3 c5 b)

/-- Constant `c₄` coefficient: the odd `P₁/P₃/P₅` Schur form. -/
def factorTwoIntrinsicSixP4SchurConstant
    (c1 c3 c5 a b : ℝ) : ℝ :=
  factorTwoIntrinsicSixLowDet a *
      factorTwoIntrinsicSixOddTailQuadratic c1 c3 c5 a -
    (factorTwoStructuralPhaseLow22 a *
          factorTwoIntrinsicSixOddLow0 c1 c3 c5 b ^ 2 -
      2 * factorTwoStructuralPhaseLow02 a *
          factorTwoIntrinsicSixOddLow0 c1 c3 c5 b *
          factorTwoIntrinsicSixOddLow2 c1 c3 c5 b +
      factorTwoStructuralPhaseLow00 a *
          factorTwoIntrinsicSixOddLow2 c1 c3 c5 b ^ 2)

/-- Exact sequential Schur decomposition in the `P₄` coefficient. -/
theorem factorTwoIntrinsicSixSchurResidual_eq_P4_quadratic
    (c4 c1 c3 c5 a b : ℝ) :
    factorTwoIntrinsicSixSchurResidual c4 c1 c3 c5 a b =
      factorTwoIntrinsicSixP4SchurLeading a * c4 ^ 2 +
        2 * c4 *
          factorTwoIntrinsicSixP4SchurMixed c1 c3 c5 a b +
        factorTwoIntrinsicSixP4SchurConstant c1 c3 c5 a b := by
  rw [factorTwoIntrinsicSixSchurResidual_eq_expansion]
  unfold factorTwoIntrinsicSixTailQuadratic
  rw [factorTwoEndpointChannelPhase_P4_P5_expansion]
  unfold factorTwoIntrinsicSixLowTail0 factorTwoIntrinsicSixLowTail2
  unfold factorTwoIntrinsicSixP4SchurLeading
    factorTwoIntrinsicSixP4SchurMixed
    factorTwoIntrinsicSixP4SchurConstant
  unfold factorTwoIntrinsicSixLowDet factorTwoIntrinsicSixP4Low0
    factorTwoIntrinsicSixP4Low2 factorTwoIntrinsicSixOddLow0
    factorTwoIntrinsicSixOddLow2 factorTwoIntrinsicSixP4TailRow
    factorTwoIntrinsicSixOddTailQuadratic
  ring

/-- A positive even `P₀/P₂/P₄` determinant and one exact rank-one
Cauchy gate close the complete residual. -/
theorem factorTwoIntrinsicSixSchurResidual_nonneg_of_P4_schur
    (c4 c1 c3 c5 a b : ℝ)
    (hLeading : 0 < factorTwoIntrinsicSixP4SchurLeading a)
    (hCauchy :
      factorTwoIntrinsicSixP4SchurMixed c1 c3 c5 a b ^ 2 ≤
        factorTwoIntrinsicSixP4SchurLeading a *
          factorTwoIntrinsicSixP4SchurConstant c1 c3 c5 a b) :
    0 ≤ factorTwoIntrinsicSixSchurResidual c4 c1 c3 c5 a b := by
  rw [factorTwoIntrinsicSixSchurResidual_eq_P4_quadratic]
  let A := factorTwoIntrinsicSixP4SchurLeading a
  let B := factorTwoIntrinsicSixP4SchurMixed c1 c3 c5 a b
  let C := factorTwoIntrinsicSixP4SchurConstant c1 c3 c5 a b
  have hid :
      A * (A * c4 ^ 2 + 2 * c4 * B + C) =
        (A * c4 + B) ^ 2 + (A * C - B ^ 2) := by ring
  have hscaled : 0 ≤ A * (A * c4 ^ 2 + 2 * c4 * B + C) := by
    rw [hid]
    exact add_nonneg (sq_nonneg _) (sub_nonneg.mpr hCauchy)
  dsimp only [A, B, C] at hscaled ⊢
  have hscaled' :
      0 ≤ (factorTwoIntrinsicSixP4SchurLeading a * c4 ^ 2 +
            2 * c4 * factorTwoIntrinsicSixP4SchurMixed c1 c3 c5 a b +
            factorTwoIntrinsicSixP4SchurConstant c1 c3 c5 a b) *
          factorTwoIntrinsicSixP4SchurLeading a := by
    simpa only [mul_comm] using hscaled
  exact nonneg_of_mul_nonneg_left hscaled' hLeading

/-- Final six-mode closure from the two sequential structural gates. -/
theorem factorTwoEndpointChannelPhase_intrinsicSix_nonneg_of_P4_schur
    (c0 c2 c4 c1 c3 c5 a b : ℝ)
    (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hLeading : 0 < factorTwoIntrinsicSixP4SchurLeading a)
    (hCauchy :
      factorTwoIntrinsicSixP4SchurMixed c1 c3 c5 a b ^ 2 ≤
        factorTwoIntrinsicSixP4SchurLeading a *
          factorTwoIntrinsicSixP4SchurConstant c1 c3 c5 a b) :
    0 ≤ factorTwoEndpointChannelPhase
      (factorTwoEvenStructuralLowProfile c0 c2 +
        factorTwoIntrinsicSixEvenTail c4)
      (factorTwoIntrinsicSixOddTail c1 c3 c5) a b :=
  factorTwoEndpointChannelPhase_intrinsicSix_nonneg_of_schur
    c0 c2 c4 c1 c3 c5 a b hab
    (factorTwoIntrinsicSixSchurResidual_nonneg_of_P4_schur
      c4 c1 c3 c5 a b hLeading hCauchy)

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4Schur
