import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEightUnbalancedStaticDiskStructural

set_option autoImplicit false

open Polynomial

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineUnbalancedStaticDiskStructural

noncomputable section

open ShiftedLegendreOrthogonality
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddLowGramExpansion
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseDiskSchur
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicEightUnbalancedStaticDiskStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseProfileStaticSquareAssemblyStructural

/-!
# Closed-disk handoff after retaining centered Legendre `P₈`

This is a purely algebraic extension of the intrinsic eight-mode unbalanced
static handoff.  The new even mode contributes four abstract transfer entries
against the retained odd modes `P₁/P₃/P₅/P₇`.  No value or estimate for any
transfer coefficient is assumed.
-/

/-! ## The retained mode, profile, and abstract transfer -/

/-- Classical centered Legendre `P₈`, transported from the shifted basis. -/
def factorTwoCenteredP8 (x : ℝ) : ℝ :=
  (shiftedLegendreReal 8).eval ((x + 1) / 2)

/-- The intrinsic even profile through centered Legendre degree eight. -/
def factorTwoIntrinsicNineEvenProfile
    (c0 c2 c4 c6 c8 : ℝ) : ℝ → ℝ :=
  factorTwoIntrinsicEightEvenProfile c0 c2 c4 c6 +
    fun x ↦ c8 * factorTwoCenteredP8 x

/-- The intrinsic odd profile is unchanged from the eight-mode handoff. -/
def factorTwoIntrinsicNineOddProfile
    (c1 c3 c5 c7 : ℝ) : ℝ → ℝ :=
  factorTwoIntrinsicEightOddProfile c1 c3 c5 c7

/-- The eight-mode transfer extended by every new `P₈`--odd entry. -/
def factorTwoIntrinsicNineUnbalancedTransfer
    (h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 : ℝ)
    (c0 c2 c4 c6 c8 c1 c3 c5 c7 : ℝ) : ℝ :=
  factorTwoIntrinsicEightUnbalancedTransfer
      h07 h27 h47 h61 h63 h65 h67
      c0 c2 c4 c6 c1 c3 c5 c7 +
    h81 * c8 * c1 + h83 * c8 * c3 + h85 * c8 * c5 +
    h87 * c8 * c7

/-! ## Corrected static endpoint forms -/

def factorTwoIntrinsicNineUnbalancedStaticPlus
    (h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 : ℝ)
    (c0 c2 c4 c6 c8 c1 c3 c5 c7 : ℝ) : ℝ :=
  factorTwoProfileStaticBranchForm
      (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8)
      (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) 1 -
    2 * factorTwoIntrinsicNineUnbalancedTransfer
      h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
      c0 c2 c4 c6 c8 c1 c3 c5 c7

def factorTwoIntrinsicNineUnbalancedStaticMinus
    (h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 : ℝ)
    (c0 c2 c4 c6 c8 c1 c3 c5 c7 : ℝ) : ℝ :=
  factorTwoProfileStaticBranchForm
      (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8)
      (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) (-1) +
    2 * factorTwoIntrinsicNineUnbalancedTransfer
      h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
      c0 c2 c4 c6 c8 c1 c3 c5 c7

def FactorTwoIntrinsicNineUnbalancedStaticPlusNonnegative
    (h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 : ℝ) : Prop :=
  ∀ c0 c2 c4 c6 c8 c1 c3 c5 c7 : ℝ,
    0 ≤ factorTwoIntrinsicNineUnbalancedStaticPlus
      h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
      c0 c2 c4 c6 c8 c1 c3 c5 c7

def FactorTwoIntrinsicNineUnbalancedStaticMinusNonnegative
    (h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 : ℝ) : Prop :=
  ∀ c0 c2 c4 c6 c8 c1 c3 c5 c7 : ℝ,
    0 ≤ factorTwoIntrinsicNineUnbalancedStaticMinus
      h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
      c0 c2 c4 c6 c8 c1 c3 c5 c7

/-! ## Homogeneity identities -/

theorem factorTwoIntrinsicNineEvenProfile_scale
    (r c0 c2 c4 c6 c8 : ℝ) :
    factorTwoIntrinsicNineEvenProfile
        (r * c0) (r * c2) (r * c4) (r * c6) (r * c8) =
      r • factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8 := by
  funext x
  unfold factorTwoIntrinsicNineEvenProfile
  rw [factorTwoIntrinsicEightEvenProfile_scale]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem factorTwoIntrinsicNineOddProfile_scale
    (s c1 c3 c5 c7 : ℝ) :
    factorTwoIntrinsicNineOddProfile
        (s * c1) (s * c3) (s * c5) (s * c7) =
      s • factorTwoIntrinsicNineOddProfile c1 c3 c5 c7 := by
  unfold factorTwoIntrinsicNineOddProfile
  exact factorTwoIntrinsicEightOddProfile_scale s c1 c3 c5 c7

theorem factorTwoIntrinsicNineUnbalancedTransfer_scale
    (h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 : ℝ)
    (r s c0 c2 c4 c6 c8 c1 c3 c5 c7 : ℝ) :
    factorTwoIntrinsicNineUnbalancedTransfer
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
        (r * c0) (r * c2) (r * c4) (r * c6) (r * c8)
        (s * c1) (s * c3) (s * c5) (s * c7) =
      r * s * factorTwoIntrinsicNineUnbalancedTransfer
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
        c0 c2 c4 c6 c8 c1 c3 c5 c7 := by
  unfold factorTwoIntrinsicNineUnbalancedTransfer
  rw [factorTwoIntrinsicEightUnbalancedTransfer_scale]
  ring

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

theorem factorTwoIntrinsicNineUnbalancedStaticPlus_scale
    (h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 : ℝ)
    (r s c0 c2 c4 c6 c8 c1 c3 c5 c7 : ℝ) :
    factorTwoIntrinsicNineUnbalancedStaticPlus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
        (r * c0) (r * c2) (r * c4) (r * c6) (r * c8)
        (s * c1) (s * c3) (s * c5) (s * c7) =
      r ^ 2 * factorTwoEndpointPhaseDiagonal
          (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8) 1 +
        s ^ 2 * factorTwoEndpointPhaseDiagonal
          (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) (-1) +
        r * s *
          (factorTwoCenteredAlternatingCoupling
              (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8)
              (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) -
            2 * factorTwoIntrinsicNineUnbalancedTransfer
              h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
              c0 c2 c4 c6 c8 c1 c3 c5 c7) := by
  unfold factorTwoIntrinsicNineUnbalancedStaticPlus
  rw [factorTwoIntrinsicNineEvenProfile_scale,
    factorTwoIntrinsicNineOddProfile_scale,
    factorTwoProfileStaticBranchForm_smul_smul,
    factorTwoIntrinsicNineUnbalancedTransfer_scale]
  ring_nf

theorem factorTwoIntrinsicNineUnbalancedStaticMinus_scale
    (h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 : ℝ)
    (r s c0 c2 c4 c6 c8 c1 c3 c5 c7 : ℝ) :
    factorTwoIntrinsicNineUnbalancedStaticMinus
        h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
        (r * c0) (r * c2) (r * c4) (r * c6) (r * c8)
        (s * c1) (s * c3) (s * c5) (s * c7) =
      r ^ 2 * factorTwoEndpointPhaseDiagonal
          (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8) (-1) +
        s ^ 2 * factorTwoEndpointPhaseDiagonal
          (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) 1 +
        r * s *
          (factorTwoCenteredAlternatingCoupling
              (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8)
              (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) +
            2 * factorTwoIntrinsicNineUnbalancedTransfer
              h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
              c0 c2 c4 c6 c8 c1 c3 c5 c7) := by
  unfold factorTwoIntrinsicNineUnbalancedStaticMinus
  rw [factorTwoIntrinsicNineEvenProfile_scale,
    factorTwoIntrinsicNineOddProfile_scale,
    factorTwoProfileStaticBranchForm_smul_smul,
    factorTwoIntrinsicNineUnbalancedTransfer_scale]
  ring_nf

/-! ## Closed-disk handoff -/

/-- Nonnegativity of the two corrected static endpoints after retaining `P₈`
implies nonnegativity of the complete retained phase on the closed disk. -/
theorem factorTwoEndpointChannelPhase_intrinsicNine_nonneg_of_unbalanced_static
    (h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 : ℝ)
    (hplus : FactorTwoIntrinsicNineUnbalancedStaticPlusNonnegative
      h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87)
    (hminus : FactorTwoIntrinsicNineUnbalancedStaticMinusNonnegative
      h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87)
    (c0 c2 c4 c6 c8 c1 c3 c5 c7 a b : ℝ)
    (hab : a ^ 2 + b ^ 2 ≤ 1) :
    0 ≤ factorTwoEndpointChannelPhase
      (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8)
      (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) a b := by
  let H := factorTwoIntrinsicNineUnbalancedTransfer
    h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
    c0 c2 c4 c6 c8 c1 c3 c5 c7
  apply factorTwoEndpointChannelPhase_nonneg_of_unbalanced_profile_static_splits
    (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8)
    (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) H a b hab
  · intro r s
    have h := hplus
      (r * c0) (r * c2) (r * c4) (r * c6) (r * c8)
      (s * c1) (s * c3) (s * c5) (s * c7)
    rw [factorTwoIntrinsicNineUnbalancedStaticPlus_scale] at h
    simpa only [H] using h
  · intro r s
    have h := hminus
      (r * c0) (r * c2) (r * c4) (r * c6) (r * c8)
      (s * c1) (s * c3) (s * c5) (s * c7)
    rw [factorTwoIntrinsicNineUnbalancedStaticMinus_scale] at h
    simpa only [H] using h

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineUnbalancedStaticDiskStructural
