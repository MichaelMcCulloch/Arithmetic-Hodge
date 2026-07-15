import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixConeReductionStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixStaticPlusObstruction

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticSplitStructural

noncomputable section

open Polynomial
open ThreeByThreeRankOneSchur
open YoshidaEndpointOddResidualRegularity
open YoshidaFactorTwoPhaseDiskSchur
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicFourP45Reduction
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixP4UniformStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveGateReduction
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourConeStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveConeStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawSixConeReductionStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveXGateStructural
open YoshidaFactorTwoPhaseIntrinsicSixSchurReduction
open YoshidaFactorTwoPhaseIntrinsicSixStaticPlusObstruction
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLowSchur

/-!
# An unbalanced two-endpoint split of the intrinsic six-mode form

The alternating block need not be divided equally between the two endpoint
forms.  The fixed bilinear transfer below was selected to leave a visibly
larger reserve in both corrected endpoint blocks.  Its coefficients are
exact rationals; none of the results in this file use their numerical origin.

The two corrected forms are the only positivity inputs.  Their opposite
transfer terms cancel after the two projective congruence scalings, leaving
the complete six-mode projective quadratic.  The remaining argument is
inverse-free Schur algebra and the existing exact raw-determinant factor.
-/

/-! ## The fixed rational transfer and the two endpoint forms -/

/-- The bilinear transfer from the even coordinates `(P₀,P₂,P₄)` to the odd
coordinates `(P₁,P₃,P₅)`.  Written entrywise, this is directly usable by a
future rational LDL or Schur certificate for either corrected block. -/
def factorTwoIntrinsicSixUnbalancedTransfer
    (c0 c2 c4 c1 c3 c5 : ℝ) : ℝ :=
  (63 / 1000 : ℝ) * c0 * c1 +
    (337 / 10000 : ℝ) * c0 * c3 +
    (3 / 400 : ℝ) * c0 * c5 +
    (577 / 10000 : ℝ) * c2 * c1 +
    (7 / 200 : ℝ) * c2 * c3 +
    (13 / 625 : ℝ) * c2 * c5 +
    (169 / 5000 : ℝ) * c4 * c1 +
    (253 / 5000 : ℝ) * c4 * c3 +
    (457 / 5000 : ℝ) * c4 * c5

/-- The positive-endpoint block after moving twice the transfer out of its
alternating cross term. -/
def factorTwoIntrinsicSixUnbalancedStaticPlus
    (c0 c2 c4 c1 c3 c5 : ℝ) : ℝ :=
  factorTwoIntrinsicSixStaticEven 1 c0 c2 c4 +
    factorTwoIntrinsicSixStaticOdd 1 c1 c3 c5 +
    (factorTwoIntrinsicSixStaticAlternating c0 c2 c4 c1 c3 c5 -
      2 * factorTwoIntrinsicSixUnbalancedTransfer c0 c2 c4 c1 c3 c5)

/-- The negative-endpoint block with the same transfer added back. -/
def factorTwoIntrinsicSixUnbalancedStaticMinus
    (c0 c2 c4 c1 c3 c5 : ℝ) : ℝ :=
  factorTwoIntrinsicSixStaticEven (-1) c0 c2 c4 +
    factorTwoIntrinsicSixStaticOdd (-1) c1 c3 c5 +
    (factorTwoIntrinsicSixStaticAlternating c0 c2 c4 c1 c3 c5 +
      2 * factorTwoIntrinsicSixUnbalancedTransfer c0 c2 c4 c1 c3 c5)

/-- The first of the two substantive endpoint hypotheses. -/
def FactorTwoIntrinsicSixUnbalancedStaticPlusNonnegative : Prop :=
  ∀ c0 c2 c4 c1 c3 c5 : ℝ,
    0 ≤ factorTwoIntrinsicSixUnbalancedStaticPlus c0 c2 c4 c1 c3 c5

/-- The second of the two substantive endpoint hypotheses. -/
def FactorTwoIntrinsicSixUnbalancedStaticMinusNonnegative : Prop :=
  ∀ c0 c2 c4 c1 c3 c5 : ℝ,
    0 ≤ factorTwoIntrinsicSixUnbalancedStaticMinus c0 c2 c4 c1 c3 c5

/-! ## Exact cancellation and the full projective quadratic -/

/-- The complete homogeneous six-mode quadratic before eliminating the
`P₀/P₂` plane. -/
def factorTwoIntrinsicSixProjectiveFullQuadratic
    (t x c0 c2 c4 c1 c3 c5 : ℝ) : ℝ :=
  factorTwoIntrinsicSixProjectiveLow00 x * c0 ^ 2 +
    2 * factorTwoIntrinsicSixProjectiveLow02 x * c0 * c2 +
    factorTwoIntrinsicSixProjectiveLow22 x * c2 ^ 2 +
    2 * c0 *
      factorTwoIntrinsicSixProjectiveLowTail0 t x c4 c1 c3 c5 +
    2 * c2 *
      factorTwoIntrinsicSixProjectiveLowTail2 t x c4 c1 c3 c5 +
    factorTwoIntrinsicSixProjectiveTailQuadratic t x c4 c1 c3 c5

/-- The two opposite transfer corrections cancel under the projective
congruence scalings.  This is the exact unbalanced split identity. -/
theorem factorTwoIntrinsicSixUnbalancedStatic_scaled_sum
    (t x c0 c2 c4 c1 c3 c5 : ℝ) (hx : x = t ^ 2) :
    factorTwoIntrinsicSixUnbalancedStaticPlus
        c0 c2 c4 (t * c1) (t * c3) (t * c5) +
      factorTwoIntrinsicSixUnbalancedStaticMinus
        (t * c0) (t * c2) (t * c4) c1 c3 c5 =
      factorTwoIntrinsicSixProjectiveFullQuadratic
        t x c0 c2 c4 c1 c3 c5 := by
  subst x
  unfold factorTwoIntrinsicSixUnbalancedStaticPlus
    factorTwoIntrinsicSixUnbalancedStaticMinus
    factorTwoIntrinsicSixUnbalancedTransfer
    factorTwoIntrinsicSixProjectiveFullQuadratic
    factorTwoIntrinsicSixStaticEven
    factorTwoIntrinsicSixStaticOdd
    factorTwoIntrinsicSixStaticAlternating
    factorTwoIntrinsicSixProjectiveLow00
    factorTwoIntrinsicSixProjectiveLow02
    factorTwoIntrinsicSixProjectiveLow22
    factorTwoIntrinsicSixProjectiveLowTail0
    factorTwoIntrinsicSixProjectiveLowTail2
    factorTwoIntrinsicSixProjectiveTailQuadratic
    factorTwoIntrinsicSixProjectiveCross04
    factorTwoIntrinsicSixProjectiveCross24
    factorTwoIntrinsicSixProjectiveOdd11
    factorTwoIntrinsicSixProjectiveOdd13
    factorTwoIntrinsicSixProjectiveOdd33
    factorTwoIntrinsicSixProjectiveOdd15
    factorTwoIntrinsicSixProjectiveOdd35
    factorTwoIntrinsicSixProjectiveP4Diagonal
    factorTwoIntrinsicSixProjectiveP5Diagonal
    factorTwoIntrinsicSixP4Diagonal
    factorTwoIntrinsicSixP5Diagonal
    factorTwoIntrinsicSixAlternating45
    factorTwoIntrinsicOddPhaseQuadratic
    factorTwoIntrinsicP4PhaseDiagonal
    factorTwoIntrinsicP5PhaseDiagonal
    factorTwoIntrinsicP45Alternating
    factorTwoEndpointPhaseDiagonal
  ring

private theorem affine_endpoint_homogenization
    (q r t : ℝ) :
    (1 + t ^ 2) *
        (q + ((1 - t ^ 2) / (1 + t ^ 2)) * r) =
      (q + r) + t ^ 2 * (q - r) := by
  have hden : 1 + t ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg t]
  field_simp [hden]
  ring

/-- Equivalently, the projective quadratic is the one-factor homogenization
of the complete six-mode phase on the rational phase-circle chart. -/
theorem factorTwoIntrinsicSixProjectiveFullQuadratic_eq_phase
    (t x c0 c2 c4 c1 c3 c5 : ℝ) (hx : x = t ^ 2) :
    factorTwoIntrinsicSixProjectiveFullQuadratic
        t x c0 c2 c4 c1 c3 c5 =
      (1 + x) * factorTwoEndpointChannelPhase
        (factorTwoEvenStructuralLowProfile c0 c2 +
          factorTwoIntrinsicSixEvenTail c4)
        (factorTwoIntrinsicSixOddTail c1 c3 c5)
        ((1 - x) / (1 + x)) (2 * t / (1 + x)) := by
  subst x
  have hden : 1 + t ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg t]
  have hdecomp := factorTwoEndpointChannelPhase_add_add_eq_low_mixed_tail
    (factorTwoEvenStructuralLowProfile c0 c2)
    (fun y ↦ c4 * factorTwoCenteredP4 y)
    (factorTwoOddStructuralLowProfile c1 c3)
    (fun y ↦ c5 * factorTwoCenteredP5 y)
    (continuous_factorTwoEvenStructuralLowProfile c0 c2)
    (continuous_const.mul continuous_factorTwoCenteredP4)
    (continuous_factorTwoOddStructuralLowProfile c1 c3)
    (continuous_const.mul continuous_factorTwoCenteredP5)
    ((1 - t ^ 2) / (1 + t ^ 2)) (2 * t / (1 + t ^ 2))
  have hlow := factorTwoEndpointChannelPhase_intrinsicLow_expansion
    c0 c2 c1 c3
      ((1 - t ^ 2) / (1 + t ^ 2)) (2 * t / (1 + t ^ 2))
  have hmixed := factorTwoIntrinsicFourP45Mixed_eq_cross_entries
    c0 c2 c1 c3 c4 c5
      ((1 - t ^ 2) / (1 + t ^ 2)) (2 * t / (1 + t ^ 2))
  have htail := factorTwoEndpointChannelPhase_P4_P5_expansion
    c4 c5 ((1 - t ^ 2) / (1 + t ^ 2)) (2 * t / (1 + t ^ 2))
  have h00 :
      (1 + t ^ 2) * factorTwoStructuralPhaseLow00
          ((1 - t ^ 2) / (1 + t ^ 2)) =
        factorTwoIntrinsicSixProjectiveLow00 (t ^ 2) := by
    simpa [factorTwoStructuralPhaseLow00,
      factorTwoIntrinsicSixProjectiveLow00] using
      affine_endpoint_homogenization
        YoshidaEndpointEvenTailRepresenter.yoshidaEndpointEvenLowGram00
        (YoshidaFactorTwoEndpointClean.factorTwoCenteredSymmetricPerturbation
          YoshidaEndpointEvenStructuralReduction.centeredEvenP0) t
  have h02 :
      (1 + t ^ 2) * factorTwoStructuralPhaseLow02
          ((1 - t ^ 2) / (1 + t ^ 2)) =
        factorTwoIntrinsicSixProjectiveLow02 (t ^ 2) := by
    simpa [factorTwoStructuralPhaseLow02,
      factorTwoIntrinsicSixProjectiveLow02] using
      affine_endpoint_homogenization
        YoshidaEndpointEvenTailRepresenter.yoshidaEndpointEvenLowGram02
        (YoshidaFactorTwoEndpointParityPencil.factorTwoCenteredSymmetricPerturbationBilinear
          YoshidaEndpointEvenStructuralReduction.centeredEvenP0
          YoshidaEndpointEvenStructuralReduction.centeredEvenP2) t
  have h22 :
      (1 + t ^ 2) * factorTwoStructuralPhaseLow22
          ((1 - t ^ 2) / (1 + t ^ 2)) =
        factorTwoIntrinsicSixProjectiveLow22 (t ^ 2) := by
    simpa [factorTwoStructuralPhaseLow22,
      factorTwoIntrinsicSixProjectiveLow22] using
      affine_endpoint_homogenization
        YoshidaEndpointEvenTailRepresenter.yoshidaEndpointEvenLowGram22
        (YoshidaFactorTwoEndpointClean.factorTwoCenteredSymmetricPerturbation
          YoshidaEndpointEvenStructuralReduction.centeredEvenP2) t
  have h04 :
      (1 + t ^ 2) * factorTwoIntrinsicFourP45Cross04
          ((1 - t ^ 2) / (1 + t ^ 2)) =
        factorTwoIntrinsicSixProjectiveCross04 (t ^ 2) := by
    simpa [factorTwoIntrinsicFourP45Cross04,
      factorTwoIntrinsicSixProjectiveCross04] using
      affine_endpoint_homogenization
        (YoshidaEndpointEvenTailRepresenter.yoshidaEndpointEvenCleanBilinear
          YoshidaEndpointEvenStructuralReduction.centeredEvenP0
          factorTwoCenteredP4)
        (YoshidaFactorTwoEndpointParityPencil.factorTwoCenteredSymmetricPerturbationBilinear
          YoshidaEndpointEvenStructuralReduction.centeredEvenP0
          factorTwoCenteredP4) t
  have h24 :
      (1 + t ^ 2) * factorTwoIntrinsicFourP45Cross24
          ((1 - t ^ 2) / (1 + t ^ 2)) =
        factorTwoIntrinsicSixProjectiveCross24 (t ^ 2) := by
    simpa [factorTwoIntrinsicFourP45Cross24,
      factorTwoIntrinsicSixProjectiveCross24] using
      affine_endpoint_homogenization
        (YoshidaEndpointEvenTailRepresenter.yoshidaEndpointEvenCleanBilinear
          YoshidaEndpointEvenStructuralReduction.centeredEvenP2
          factorTwoCenteredP4)
        (YoshidaFactorTwoEndpointParityPencil.factorTwoCenteredSymmetricPerturbationBilinear
          YoshidaEndpointEvenStructuralReduction.centeredEvenP2
          factorTwoCenteredP4) t
  have h11 :
      (1 + t ^ 2) * factorTwoIntrinsicOddPhaseLow11
          ((1 - t ^ 2) / (1 + t ^ 2)) =
        factorTwoIntrinsicSixProjectiveOdd11 (t ^ 2) := by
    simpa [factorTwoIntrinsicOddPhaseLow11,
      factorTwoIntrinsicSixProjectiveOdd11] using
      affine_endpoint_homogenization
        YoshidaEndpointOddFullPolarization.yoshidaEndpointOddLowGram11
        (YoshidaFactorTwoEndpointClean.factorTwoCenteredSymmetricPerturbation
          YoshidaEndpointOcticPotential.centeredP1) t
  have h13 :
      (1 + t ^ 2) * factorTwoIntrinsicOddPhaseLow13
          ((1 - t ^ 2) / (1 + t ^ 2)) =
        factorTwoIntrinsicSixProjectiveOdd13 (t ^ 2) := by
    simpa [factorTwoIntrinsicOddPhaseLow13,
      factorTwoIntrinsicSixProjectiveOdd13] using
      affine_endpoint_homogenization
        YoshidaEndpointOddFullPolarization.yoshidaEndpointOddLowGram13
        (YoshidaFactorTwoEndpointParityPencil.factorTwoCenteredSymmetricPerturbationBilinear
          YoshidaEndpointOcticPotential.centeredP1
          YoshidaEndpointOcticPotential.centeredP3) t
  have h33 :
      (1 + t ^ 2) * factorTwoIntrinsicOddPhaseLow33
          ((1 - t ^ 2) / (1 + t ^ 2)) =
        factorTwoIntrinsicSixProjectiveOdd33 (t ^ 2) := by
    simpa [factorTwoIntrinsicOddPhaseLow33,
      factorTwoIntrinsicSixProjectiveOdd33] using
      affine_endpoint_homogenization
        YoshidaEndpointOddFullPolarization.yoshidaEndpointOddLowGram33
        (YoshidaFactorTwoEndpointClean.factorTwoCenteredSymmetricPerturbation
          YoshidaEndpointOcticPotential.centeredP3) t
  have h15 :
      (1 + t ^ 2) * factorTwoIntrinsicFourP45Cross15
          ((1 - t ^ 2) / (1 + t ^ 2)) =
        factorTwoIntrinsicSixProjectiveOdd15 (t ^ 2) := by
    simpa [factorTwoIntrinsicFourP45Cross15,
      factorTwoIntrinsicSixProjectiveOdd15] using
      affine_endpoint_homogenization
        (YoshidaEndpointEvenTailRepresenter.yoshidaEndpointEvenCleanBilinear
          YoshidaEndpointOcticPotential.centeredP1 factorTwoCenteredP5)
        (YoshidaFactorTwoEndpointParityPencil.factorTwoCenteredSymmetricPerturbationBilinear
          YoshidaEndpointOcticPotential.centeredP1 factorTwoCenteredP5) t
  have h35 :
      (1 + t ^ 2) * factorTwoIntrinsicFourP45Cross35
          ((1 - t ^ 2) / (1 + t ^ 2)) =
        factorTwoIntrinsicSixProjectiveOdd35 (t ^ 2) := by
    simpa [factorTwoIntrinsicFourP45Cross35,
      factorTwoIntrinsicSixProjectiveOdd35] using
      affine_endpoint_homogenization
        (YoshidaEndpointEvenTailRepresenter.yoshidaEndpointEvenCleanBilinear
          YoshidaEndpointOcticPotential.centeredP3 factorTwoCenteredP5)
        (YoshidaFactorTwoEndpointParityPencil.factorTwoCenteredSymmetricPerturbationBilinear
          YoshidaEndpointOcticPotential.centeredP3 factorTwoCenteredP5) t
  have h44 :
      (1 + t ^ 2) * factorTwoIntrinsicP4PhaseDiagonal
          ((1 - t ^ 2) / (1 + t ^ 2)) =
        factorTwoIntrinsicSixProjectiveP4Diagonal (t ^ 2) := by
    simpa [factorTwoIntrinsicP4PhaseDiagonal,
      factorTwoIntrinsicSixP4Diagonal,
      factorTwoIntrinsicSixProjectiveP4Diagonal,
      factorTwoEndpointPhaseDiagonal] using
      affine_endpoint_homogenization
        (YoshidaEndpointOddCleanPositive.yoshidaEndpointOddCleanQuadratic
          factorTwoCenteredP4)
        (YoshidaFactorTwoEndpointClean.factorTwoCenteredSymmetricPerturbation
          factorTwoCenteredP4) t
  have h55 :
      (1 + t ^ 2) * factorTwoIntrinsicP5PhaseDiagonal
          ((1 - t ^ 2) / (1 + t ^ 2)) =
        factorTwoIntrinsicSixProjectiveP5Diagonal (t ^ 2) := by
    simpa [factorTwoIntrinsicP5PhaseDiagonal,
      factorTwoIntrinsicSixP5Diagonal,
      factorTwoIntrinsicSixProjectiveP5Diagonal,
      factorTwoEndpointPhaseDiagonal] using
      affine_endpoint_homogenization
        (YoshidaEndpointOddCleanPositive.yoshidaEndpointOddCleanQuadratic
          factorTwoCenteredP5)
        (YoshidaFactorTwoEndpointClean.factorTwoCenteredSymmetricPerturbation
          factorTwoCenteredP5) t
  unfold factorTwoIntrinsicSixEvenTail factorTwoIntrinsicSixOddTail
  rw [hdecomp, hlow, htail]
  rw [show factorTwoEndpointLowTailMixed
      (factorTwoEvenStructuralLowProfile c0 c2)
      (fun y ↦ c4 * factorTwoCenteredP4 y)
      (factorTwoOddStructuralLowProfile c1 c3)
      (fun y ↦ c5 * factorTwoCenteredP5 y)
      ((1 - t ^ 2) / (1 + t ^ 2)) (2 * t / (1 + t ^ 2)) =
        factorTwoIntrinsicFourP45Mixed c0 c2 c1 c3 c4 c5
          ((1 - t ^ 2) / (1 + t ^ 2))
          (2 * t / (1 + t ^ 2)) by rfl,
    hmixed]
  unfold factorTwoIntrinsicSixProjectiveFullQuadratic
    factorTwoIntrinsicSixProjectiveLowTail0
    factorTwoIntrinsicSixProjectiveLowTail2
    factorTwoIntrinsicSixProjectiveTailQuadratic
    factorTwoIntrinsicSixAlternating45
    factorTwoIntrinsicOddPhaseQuadratic
    factorTwoIntrinsicAlternatingRow0
    factorTwoIntrinsicAlternatingRow2
    factorTwoIntrinsicP45Alternating
  rw [← h00, ← h02, ← h22, ← h04, ← h24,
    ← h11, ← h13, ← h33, ← h15, ← h35, ← h44, ← h55]
  field_simp [hden]
  ring

/-- The two corrected endpoint hypotheses make the complete projective
quadratic nonnegative in every coefficient direction. -/
theorem factorTwoIntrinsicSixProjectiveFullQuadratic_nonneg
    (hplus : FactorTwoIntrinsicSixUnbalancedStaticPlusNonnegative)
    (hminus : FactorTwoIntrinsicSixUnbalancedStaticMinusNonnegative)
    (t x c0 c2 c4 c1 c3 c5 : ℝ) (hx : x = t ^ 2) :
    0 ≤ factorTwoIntrinsicSixProjectiveFullQuadratic
      t x c0 c2 c4 c1 c3 c5 := by
  rw [← factorTwoIntrinsicSixUnbalancedStatic_scaled_sum
    t x c0 c2 c4 c1 c3 c5 hx]
  exact add_nonneg
    (hplus c0 c2 c4 (t * c1) (t * c3) (t * c5))
    (hminus (t * c0) (t * c2) (t * c4) c1 c3 c5)

/-! ## Inverse-free passage to the low-Schur residual -/

/-- Evaluating the full quadratic at the adjugate low-plane minimizer, after
scaling all four tail coordinates by the positive low determinant, gives the
low determinant times the direct projective Schur residual. -/
theorem factorTwoIntrinsicSixProjectiveFullQuadratic_adjugate_specialization
    (t x c4 c1 c3 c5 : ℝ) :
    let d := factorTwoIntrinsicSixProjectiveLowDet x
    let l0 := factorTwoIntrinsicSixProjectiveLowTail0 t x c4 c1 c3 c5
    let l2 := factorTwoIntrinsicSixProjectiveLowTail2 t x c4 c1 c3 c5
    factorTwoIntrinsicSixProjectiveFullQuadratic t x
        (-(factorTwoIntrinsicSixProjectiveLow22 x * l0 -
            factorTwoIntrinsicSixProjectiveLow02 x * l2))
        (factorTwoIntrinsicSixProjectiveLow02 x * l0 -
          factorTwoIntrinsicSixProjectiveLow00 x * l2)
        (d * c4) (d * c1) (d * c3) (d * c5) =
      d * factorTwoIntrinsicSixProjectiveRawResidual
        t x c4 c1 c3 c5 := by
  dsimp only
  unfold factorTwoIntrinsicSixProjectiveFullQuadratic
    factorTwoIntrinsicSixProjectiveRawResidual
    factorTwoIntrinsicSixProjectiveLowDet
    factorTwoIntrinsicSixProjectiveLowTail0
    factorTwoIntrinsicSixProjectiveLowTail2
    factorTwoIntrinsicSixProjectiveTailQuadratic
    factorTwoIntrinsicSixAdjugateBilinear
  ring

/-- The two corrected endpoint hypotheses imply nonnegativity of the direct
projective low-Schur residual at every point `x=t²`. -/
theorem factorTwoIntrinsicSixProjectiveRawResidual_nonneg_of_unbalanced_static
    (hplus : FactorTwoIntrinsicSixUnbalancedStaticPlusNonnegative)
    (hminus : FactorTwoIntrinsicSixUnbalancedStaticMinusNonnegative)
    (t x c4 c1 c3 c5 : ℝ) (hx : x = t ^ 2) :
    0 ≤ factorTwoIntrinsicSixProjectiveRawResidual
      t x c4 c1 c3 c5 := by
  let d := factorTwoIntrinsicSixProjectiveLowDet x
  let l0 := factorTwoIntrinsicSixProjectiveLowTail0 t x c4 c1 c3 c5
  let l2 := factorTwoIntrinsicSixProjectiveLowTail2 t x c4 c1 c3 c5
  have hfull := factorTwoIntrinsicSixProjectiveFullQuadratic_nonneg
    hplus hminus t x
      (-(factorTwoIntrinsicSixProjectiveLow22 x * l0 -
          factorTwoIntrinsicSixProjectiveLow02 x * l2))
      (factorTwoIntrinsicSixProjectiveLow02 x * l0 -
        factorTwoIntrinsicSixProjectiveLow00 x * l2)
      (d * c4) (d * c1) (d * c3) (d * c5) hx
  have hidentity :=
    factorTwoIntrinsicSixProjectiveFullQuadratic_adjugate_specialization
      t x c4 c1 c3 c5
  dsimp only [d, l0, l2] at hidentity hfull
  rw [hidentity] at hfull
  have hxNonneg : 0 ≤ x := by
    rw [hx]
    positivity
  have hd : 0 < factorTwoIntrinsicSixProjectiveLowDet x :=
    factorTwoIntrinsicSixProjectiveLowDet_pos x hxNonneg
  nlinarith

/-! ## The final adjugate gate and the raw six determinant -/

private theorem adjugateVector_linear_identity
    (q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 : ℝ) :
    ell0 * adjugateVector
          q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 0 +
        ell1 * adjugateVector
          q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 1 +
        ell2 * adjugateVector
          q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 2 =
      adjugateQuadratic
        q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 := by
  simp only [adjugateVector]
  unfold adjugateQuadratic
  ring

private theorem adjugateVector_quadratic_identity
    (q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 : ℝ) :
    symmetricQuadratic q00 q01 q02 q11 q12 q22
        (adjugateVector q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 0)
        (adjugateVector q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 1)
        (adjugateVector q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 2) =
      symmetricDeterminant q00 q01 q02 q11 q12 q22 *
        adjugateQuadratic
          q00 q01 q02 q11 q12 q22 ell0 ell1 ell2 := by
  simp only [adjugateVector]
  unfold symmetricQuadratic symmetricDeterminant adjugateQuadratic
  ring

/-- Universal nonnegativity of the full projective residual forces its final
`P₅` adjugate gate.  The proof evaluates at the adjugate vector and at the
negative base determinant, so it uses no matrix inverse or division. -/
theorem factorTwoIntrinsicSixProjectiveP5_gate_of_unbalanced_static
    (hplus : FactorTwoIntrinsicSixUnbalancedStaticPlusNonnegative)
    (hminus : FactorTwoIntrinsicSixUnbalancedStaticMinusNonnegative)
    (t x : ℝ) (hx : x = t ^ 2) :
    factorTwoIntrinsicSixProjectiveP5AdjugateX x ≤
      factorTwoIntrinsicSixProjectiveBaseDetX x *
        factorTwoIntrinsicSixProjectiveP5DiagonalResidual x := by
  let q00 := factorTwoIntrinsicSixProjectiveP4Pivot x
  let q01 := t * factorTwoIntrinsicSixProjectiveP4OddCross x 0
  let q02 := t * factorTwoIntrinsicSixProjectiveP4OddCross x 1
  let q11 := factorTwoIntrinsicSixProjectiveOddResidual x 0 0
  let q12 := factorTwoIntrinsicSixProjectiveOddResidual x 0 1
  let q22 := factorTwoIntrinsicSixProjectiveOddResidual x 1 1
  let ell0 := t * factorTwoIntrinsicSixProjectiveP4OddCross x 2
  let ell1 := factorTwoIntrinsicSixProjectiveOddResidual x 0 2
  let ell2 := factorTwoIntrinsicSixProjectiveOddResidual x 1 2
  let T := factorTwoIntrinsicSixProjectiveBaseDet t x
  let A := factorTwoIntrinsicSixProjectiveP5Adjugate t x
  let C := factorTwoIntrinsicSixProjectiveP5DiagonalResidual x
  let v := adjugateVector q00 q01 q02 q11 q12 q22 ell0 ell1 ell2
  have hQ :
      factorTwoIntrinsicSixProjectiveBaseQuadratic
          t x (v 0) (v 1) (v 2) = T * A := by
    simpa [factorTwoIntrinsicSixProjectiveBaseQuadratic,
      factorTwoIntrinsicSixProjectiveBaseDet,
      factorTwoIntrinsicSixProjectiveP5Adjugate,
      q00, q01, q02, q11, q12, q22,
      ell0, ell1, ell2, T, A, v] using
      adjugateVector_quadratic_identity
        q00 q01 q02 q11 q12 q22 ell0 ell1 ell2
  have hL :
      factorTwoIntrinsicSixProjectiveP5Linear
          t x (v 0) (v 1) (v 2) = A := by
    simpa [factorTwoIntrinsicSixProjectiveP5Linear,
      factorTwoIntrinsicSixProjectiveP5Adjugate,
      q00, q01, q02, q11, q12, q22,
      ell0, ell1, ell2, A, v] using
      adjugateVector_linear_identity
        q00 q01 q02 q11 q12 q22 ell0 ell1 ell2
  have hResidualRaw :=
    factorTwoIntrinsicSixProjectiveRawResidual_nonneg_of_unbalanced_static
      hplus hminus t x (v 0) (v 1) (v 2) (-T) hx
  have hResidual :
      0 ≤ factorTwoIntrinsicSixProjectiveResidual
        t x (v 0) (v 1) (v 2) (-T) := by
    rw [factorTwoIntrinsicSixProjectiveResidual_eq_raw
      t x (v 0) (v 1) (v 2) (-T) hx]
    exact hResidualRaw
  unfold factorTwoIntrinsicSixProjectiveResidual at hResidual
  rw [hQ, hL] at hResidual
  change 0 ≤ T * A + 2 * (-T) * A + C * (-T) ^ 2 at hResidual
  have hxNonneg : 0 ≤ x := by
    rw [hx]
    positivity
  have hTX : 0 < factorTwoIntrinsicSixProjectiveBaseDetX x :=
    factorTwoIntrinsicSixProjectiveBaseDetX_pos x hxNonneg
  have hT : 0 < T := by
    dsimp only [T]
    rwa [factorTwoIntrinsicSixProjectiveBaseDet_eq_x t x hx]
  have hgate : A ≤ T * C := by
    nlinarith
  simpa [A, T, C,
    factorTwoIntrinsicSixProjectiveP5Adjugate_eq_x t x hx,
    factorTwoIntrinsicSixProjectiveBaseDet_eq_x t x hx] using hgate

/-- Structural endpoint conclusion: the two corrected fixed-form positivity
statements imply pointwise nonnegativity of the raw six-mode determinant at
every projective point `x=t²`. -/
theorem factorTwoIntrinsicSixProjectiveRawDeterminant_eval_nonneg_of_unbalanced_static
    (hplus : FactorTwoIntrinsicSixUnbalancedStaticPlusNonnegative)
    (hminus : FactorTwoIntrinsicSixUnbalancedStaticMinusNonnegative)
    (t x : ℝ) (hx : x = t ^ 2) :
    0 ≤ factorTwoIntrinsicSixProjectiveRawDeterminantPolynomial.eval x := by
  have hxNonneg : 0 ≤ x := by
    rw [hx]
    positivity
  rw [← factorTwoIntrinsicSixProjectiveXGates_iff_rawSix_eval_nonneg
    x hxNonneg]
  exact ⟨factorTwoIntrinsicSixProjectiveP4Pivot_pos x hxNonneg,
    factorTwoIntrinsicSixProjectiveBaseMinorTwoX_pos x hxNonneg,
    factorTwoIntrinsicSixProjectiveBaseDetX_pos x hxNonneg,
    factorTwoIntrinsicSixProjectiveP5_gate_of_unbalanced_static
      hplus hminus t x hx⟩

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticSplitStructural
