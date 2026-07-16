import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedDiskStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseProfileStaticSquareAssemblyStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEightUnbalancedStaticDiskStructural

noncomputable section

open YoshidaFactorTwoEndpointBilinear
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddLowGramExpansion
open YoshidaEndpointOddResidualRegularity
open YoshidaFactorTwoPhaseDiskSchur
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicSixSchurReduction
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedDiskStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticSplitStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseProfileStaticSquareAssemblyStructural

/-!
# Closed-disk handoff for the first eight intrinsic modes

This file is purely algebraic.  It adjoins the centered Legendre modes
`P₆/P₇` to the already-certified intrinsic six-mode profiles and extends the
fixed unbalanced transfer by seven abstract bilinear coefficients.  No value
or estimate for those coefficients is assumed.

The two corrected static endpoint forms are the only hypotheses of the final
theorem.  Their opposite transfer corrections cancel in the same square-root
interpolation used for the intrinsic six-mode certificate.
-/

/-! ## The eight-mode profiles and abstract transfer -/

/-- The intrinsic even profile through centered Legendre degree six. -/
def factorTwoIntrinsicEightEvenProfile
    (c0 c2 c4 c6 : ℝ) : ℝ → ℝ :=
  factorTwoEvenStructuralLowProfile c0 c2 +
    factorTwoIntrinsicSixEvenTail c4 +
    fun x ↦ c6 * factorTwoCenteredP6 x

/-- The intrinsic odd profile through centered Legendre degree seven. -/
def factorTwoIntrinsicEightOddProfile
    (c1 c3 c5 c7 : ℝ) : ℝ → ℝ :=
  factorTwoIntrinsicSixOddTail c1 c3 c5 +
    fun x ↦ c7 * factorTwoCenteredP7 x

/-- The six-mode transfer extended by every new even--odd entry involving
`P₆` or `P₇`.  The seven parameters remain abstract: choosing and certifying
them is a separate endpoint-border problem. -/
def factorTwoIntrinsicEightUnbalancedTransfer
    (h07 h27 h47 h61 h63 h65 h67 : ℝ)
    (c0 c2 c4 c6 c1 c3 c5 c7 : ℝ) : ℝ :=
  factorTwoIntrinsicSixUnbalancedTransfer c0 c2 c4 c1 c3 c5 +
    h07 * c0 * c7 + h27 * c2 * c7 + h47 * c4 * c7 +
    h61 * c6 * c1 + h63 * c6 * c3 + h65 * c6 * c5 +
    h67 * c6 * c7

/-! ## Corrected static endpoint forms -/

/-- Positive static endpoint with twice the extended transfer removed. -/
def factorTwoIntrinsicEightUnbalancedStaticPlus
    (h07 h27 h47 h61 h63 h65 h67 : ℝ)
    (c0 c2 c4 c6 c1 c3 c5 c7 : ℝ) : ℝ :=
  factorTwoProfileStaticBranchForm
      (factorTwoIntrinsicEightEvenProfile c0 c2 c4 c6)
      (factorTwoIntrinsicEightOddProfile c1 c3 c5 c7) 1 -
    2 * factorTwoIntrinsicEightUnbalancedTransfer
      h07 h27 h47 h61 h63 h65 h67
      c0 c2 c4 c6 c1 c3 c5 c7

/-- Negative static endpoint with twice the extended transfer restored. -/
def factorTwoIntrinsicEightUnbalancedStaticMinus
    (h07 h27 h47 h61 h63 h65 h67 : ℝ)
    (c0 c2 c4 c6 c1 c3 c5 c7 : ℝ) : ℝ :=
  factorTwoProfileStaticBranchForm
      (factorTwoIntrinsicEightEvenProfile c0 c2 c4 c6)
      (factorTwoIntrinsicEightOddProfile c1 c3 c5 c7) (-1) +
    2 * factorTwoIntrinsicEightUnbalancedTransfer
      h07 h27 h47 h61 h63 h65 h67
      c0 c2 c4 c6 c1 c3 c5 c7

def FactorTwoIntrinsicEightUnbalancedStaticPlusNonnegative
    (h07 h27 h47 h61 h63 h65 h67 : ℝ) : Prop :=
  ∀ c0 c2 c4 c6 c1 c3 c5 c7 : ℝ,
    0 ≤ factorTwoIntrinsicEightUnbalancedStaticPlus
      h07 h27 h47 h61 h63 h65 h67
      c0 c2 c4 c6 c1 c3 c5 c7

def FactorTwoIntrinsicEightUnbalancedStaticMinusNonnegative
    (h07 h27 h47 h61 h63 h65 h67 : ℝ) : Prop :=
  ∀ c0 c2 c4 c6 c1 c3 c5 c7 : ℝ,
    0 ≤ factorTwoIntrinsicEightUnbalancedStaticMinus
      h07 h27 h47 h61 h63 h65 h67
      c0 c2 c4 c6 c1 c3 c5 c7

/-! ## Homogeneity identities -/

theorem factorTwoIntrinsicEightEvenProfile_scale
    (r c0 c2 c4 c6 : ℝ) :
    factorTwoIntrinsicEightEvenProfile
        (r * c0) (r * c2) (r * c4) (r * c6) =
      r • factorTwoIntrinsicEightEvenProfile c0 c2 c4 c6 := by
  funext x
  unfold factorTwoIntrinsicEightEvenProfile
    factorTwoEvenStructuralLowProfile factorTwoIntrinsicSixEvenTail
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring_nf

theorem factorTwoIntrinsicEightOddProfile_scale
    (s c1 c3 c5 c7 : ℝ) :
    factorTwoIntrinsicEightOddProfile
        (s * c1) (s * c3) (s * c5) (s * c7) =
      s • factorTwoIntrinsicEightOddProfile c1 c3 c5 c7 := by
  funext x
  unfold factorTwoIntrinsicEightOddProfile
    factorTwoIntrinsicSixOddTail factorTwoOddStructuralLowProfile
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring_nf

theorem factorTwoIntrinsicEightUnbalancedTransfer_scale
    (h07 h27 h47 h61 h63 h65 h67 : ℝ)
    (r s c0 c2 c4 c6 c1 c3 c5 c7 : ℝ) :
    factorTwoIntrinsicEightUnbalancedTransfer
        h07 h27 h47 h61 h63 h65 h67
        (r * c0) (r * c2) (r * c4) (r * c6)
        (s * c1) (s * c3) (s * c5) (s * c7) =
      r * s * factorTwoIntrinsicEightUnbalancedTransfer
        h07 h27 h47 h61 h63 h65 h67
        c0 c2 c4 c6 c1 c3 c5 c7 := by
  unfold factorTwoIntrinsicEightUnbalancedTransfer
    factorTwoIntrinsicSixUnbalancedTransfer
  ring_nf

private theorem factorTwoEndpointPhaseDiagonal_smul
    (w : ℝ → ℝ) (c a : ℝ) :
    factorTwoEndpointPhaseDiagonal (c • w) a =
      c ^ 2 * factorTwoEndpointPhaseDiagonal w a := by
  have hclean : yoshidaEndpointOddCleanQuadratic (c • w) =
      c ^ 2 * yoshidaEndpointOddCleanQuadratic w := by
    simpa only [Pi.smul_apply, smul_eq_mul] using
      yoshidaEndpointOddCleanQuadratic_const_mul w c
  unfold factorTwoEndpointPhaseDiagonal
  rw [hclean, factorTwoCenteredSymmetricPerturbation_smul]
  ring_nf

private theorem factorTwoProfileStaticBranchForm_smul_smul
    (e o : ℝ → ℝ) (r s sigma : ℝ) :
    factorTwoProfileStaticBranchForm (r • e) (s • o) sigma =
      r ^ 2 * factorTwoEndpointPhaseDiagonal e sigma +
        s ^ 2 * factorTwoEndpointPhaseDiagonal o (-sigma) +
        r * s * factorTwoCenteredAlternatingCoupling e o := by
  unfold factorTwoProfileStaticBranchForm
  rw [factorTwoEndpointPhaseDiagonal_smul,
    factorTwoEndpointPhaseDiagonal_smul,
    factorTwoCenteredAlternatingCoupling_smul_left,
    factorTwoCenteredAlternatingCoupling_smul_right]
  ring_nf

theorem factorTwoIntrinsicEightUnbalancedStaticPlus_scale
    (h07 h27 h47 h61 h63 h65 h67 : ℝ)
    (r s c0 c2 c4 c6 c1 c3 c5 c7 : ℝ) :
    factorTwoIntrinsicEightUnbalancedStaticPlus
        h07 h27 h47 h61 h63 h65 h67
        (r * c0) (r * c2) (r * c4) (r * c6)
        (s * c1) (s * c3) (s * c5) (s * c7) =
      r ^ 2 * factorTwoEndpointPhaseDiagonal
          (factorTwoIntrinsicEightEvenProfile c0 c2 c4 c6) 1 +
        s ^ 2 * factorTwoEndpointPhaseDiagonal
          (factorTwoIntrinsicEightOddProfile c1 c3 c5 c7) (-1) +
        r * s *
          (factorTwoCenteredAlternatingCoupling
              (factorTwoIntrinsicEightEvenProfile c0 c2 c4 c6)
              (factorTwoIntrinsicEightOddProfile c1 c3 c5 c7) -
            2 * factorTwoIntrinsicEightUnbalancedTransfer
              h07 h27 h47 h61 h63 h65 h67
              c0 c2 c4 c6 c1 c3 c5 c7) := by
  unfold factorTwoIntrinsicEightUnbalancedStaticPlus
  rw [factorTwoIntrinsicEightEvenProfile_scale,
    factorTwoIntrinsicEightOddProfile_scale,
    factorTwoProfileStaticBranchForm_smul_smul,
    factorTwoIntrinsicEightUnbalancedTransfer_scale]
  ring_nf

theorem factorTwoIntrinsicEightUnbalancedStaticMinus_scale
    (h07 h27 h47 h61 h63 h65 h67 : ℝ)
    (r s c0 c2 c4 c6 c1 c3 c5 c7 : ℝ) :
    factorTwoIntrinsicEightUnbalancedStaticMinus
        h07 h27 h47 h61 h63 h65 h67
        (r * c0) (r * c2) (r * c4) (r * c6)
        (s * c1) (s * c3) (s * c5) (s * c7) =
      r ^ 2 * factorTwoEndpointPhaseDiagonal
          (factorTwoIntrinsicEightEvenProfile c0 c2 c4 c6) (-1) +
        s ^ 2 * factorTwoEndpointPhaseDiagonal
          (factorTwoIntrinsicEightOddProfile c1 c3 c5 c7) 1 +
        r * s *
          (factorTwoCenteredAlternatingCoupling
              (factorTwoIntrinsicEightEvenProfile c0 c2 c4 c6)
              (factorTwoIntrinsicEightOddProfile c1 c3 c5 c7) +
            2 * factorTwoIntrinsicEightUnbalancedTransfer
              h07 h27 h47 h61 h63 h65 h67
              c0 c2 c4 c6 c1 c3 c5 c7) := by
  unfold factorTwoIntrinsicEightUnbalancedStaticMinus
  rw [factorTwoIntrinsicEightEvenProfile_scale,
    factorTwoIntrinsicEightOddProfile_scale,
    factorTwoProfileStaticBranchForm_smul_smul,
    factorTwoIntrinsicEightUnbalancedTransfer_scale]
  ring_nf

/-! ## Dimension-free unbalanced interpolation and the eight-mode handoff -/

/-- Profile-level form of the unbalanced endpoint interpolation.  This is
dimension-free; `H` is any scalar transfer that is bilinear under the two
independent profile rescalings supplied by the endpoint hypotheses. -/
theorem factorTwoEndpointChannelPhase_nonneg_of_unbalanced_profile_static_splits
    (e o : ℝ → ℝ) (H a b : ℝ)
    (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hPlus : ∀ r s : ℝ,
      0 ≤ r ^ 2 * factorTwoEndpointPhaseDiagonal e 1 +
        s ^ 2 * factorTwoEndpointPhaseDiagonal o (-1) +
        r * s * (factorTwoCenteredAlternatingCoupling e o - 2 * H))
    (hMinus : ∀ r s : ℝ,
      0 ≤ r ^ 2 * factorTwoEndpointPhaseDiagonal e (-1) +
        s ^ 2 * factorTwoEndpointPhaseDiagonal o 1 +
        r * s * (factorTwoCenteredAlternatingCoupling e o + 2 * H)) :
    0 ≤ factorTwoEndpointChannelPhase e o a b := by
  let EPlus := factorTwoEndpointPhaseDiagonal e 1
  let EMinus := factorTwoEndpointPhaseDiagonal e (-1)
  let OMinus := factorTwoEndpointPhaseDiagonal o (-1)
  let OPlus := factorTwoEndpointPhaseDiagonal o 1
  let QE := (EPlus + EMinus) / 2
  let PE := (EPlus - EMinus) / 2
  let QO := (OMinus + OPlus) / 2
  let PO := (OPlus - OMinus) / 2
  let J := factorTwoCenteredAlternatingCoupling e o
  have hScalar := scalar_phase_nonneg_of_unbalanced_static_splits
    QE PE QO PO J H a b hab
    (by
      intro r s
      have h := hPlus r s
      dsimp only [QE, PE, QO, PO, J, EPlus, EMinus, OMinus, OPlus]
      nlinarith)
    (by
      intro r s
      have h := hMinus r s
      dsimp only [QE, PE, QO, PO, J, EPlus, EMinus, OMinus, OPlus]
      nlinarith)
  have hEvenAffine :
      (EPlus + EMinus) / 2 + a * ((EPlus - EMinus) / 2) =
        factorTwoEndpointPhaseDiagonal e a := by
    dsimp only [EPlus, EMinus]
    unfold factorTwoEndpointPhaseDiagonal
    ring
  have hOddAffine :
      (OMinus + OPlus) / 2 + a * ((OPlus - OMinus) / 2) =
        factorTwoEndpointPhaseDiagonal o a := by
    dsimp only [OMinus, OPlus]
    unfold factorTwoEndpointPhaseDiagonal
    ring
  rw [factorTwoEndpointChannelPhase_eq_diagonals]
  dsimp only [QE, PE, QO, PO, J] at hScalar
  rw [show
      (EPlus + EMinus) / 2 + (OMinus + OPlus) / 2 +
          a * ((EPlus - EMinus) / 2 + (OPlus - OMinus) / 2) +
          b * factorTwoCenteredAlternatingCoupling e o =
        ((EPlus + EMinus) / 2 + a * ((EPlus - EMinus) / 2)) +
          ((OMinus + OPlus) / 2 + a * ((OPlus - OMinus) / 2)) +
          b * factorTwoCenteredAlternatingCoupling e o by ring_nf]
    at hScalar
  rw [hEvenAffine, hOddAffine] at hScalar
  exact hScalar

/-- Nonnegativity of the two corrected eight-mode static endpoints implies
nonnegativity of the complete eight-mode phase on the whole closed disk.
The seven transfer coefficients are arbitrary and remain visible only in the
two endpoint hypotheses. -/
theorem factorTwoEndpointChannelPhase_intrinsicEight_nonneg_of_unbalanced_static
    (h07 h27 h47 h61 h63 h65 h67 : ℝ)
    (hplus : FactorTwoIntrinsicEightUnbalancedStaticPlusNonnegative
      h07 h27 h47 h61 h63 h65 h67)
    (hminus : FactorTwoIntrinsicEightUnbalancedStaticMinusNonnegative
      h07 h27 h47 h61 h63 h65 h67)
    (c0 c2 c4 c6 c1 c3 c5 c7 a b : ℝ)
    (hab : a ^ 2 + b ^ 2 ≤ 1) :
    0 ≤ factorTwoEndpointChannelPhase
      (factorTwoIntrinsicEightEvenProfile c0 c2 c4 c6)
      (factorTwoIntrinsicEightOddProfile c1 c3 c5 c7) a b := by
  let H := factorTwoIntrinsicEightUnbalancedTransfer
    h07 h27 h47 h61 h63 h65 h67
    c0 c2 c4 c6 c1 c3 c5 c7
  apply factorTwoEndpointChannelPhase_nonneg_of_unbalanced_profile_static_splits
    (factorTwoIntrinsicEightEvenProfile c0 c2 c4 c6)
    (factorTwoIntrinsicEightOddProfile c1 c3 c5 c7) H a b hab
  · intro r s
    have h := hplus
      (r * c0) (r * c2) (r * c4) (r * c6)
      (s * c1) (s * c3) (s * c5) (s * c7)
    rw [factorTwoIntrinsicEightUnbalancedStaticPlus_scale] at h
    simpa only [H] using h
  · intro r s
    have h := hminus
      (r * c0) (r * c2) (r * c4) (r * c6)
      (s * c1) (s * c3) (s * c5) (s * c7)
    rw [factorTwoIntrinsicEightUnbalancedStaticMinus_scale] at h
    simpa only [H] using h

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEightUnbalancedStaticDiskStructural
