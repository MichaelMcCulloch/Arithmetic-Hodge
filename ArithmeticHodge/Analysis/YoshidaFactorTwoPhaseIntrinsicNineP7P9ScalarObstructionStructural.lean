import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineSemanticHandoffStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineStaticNestedSchurStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP7P9ScalarObstructionStructural

noncomputable section

open ShiftedLegendreBasis
open ShiftedLegendreOrthogonality
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddLowGramExpansion
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddResidualRegularity
open YoshidaEndpointPotentialBound
open YoshidaFactorTwoPhaseDiskSchur
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicEightUnbalancedStaticDiskStructural
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicNineComplementSchurStructural
open YoshidaFactorTwoPhaseIntrinsicNineEnhancedTailReserveStructural
open YoshidaFactorTwoPhaseIntrinsicNineStaticNestedSchurStructural
open YoshidaFactorTwoPhaseIntrinsicNineUnbalancedStaticDiskStructural
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseIntrinsicSixSchurReduction
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseP678CombinedResidualSchurStructural

/-!
# Exact `P7/P9` scalar obstruction at the positive symmetric endpoint

This file makes no numerical sign claim.  It reduces both the honest
low--tail determinant and the enhanced-reserve allocation proposed for the
cutoff-nine survivor to five named scalars.  The witness is the retained odd
mode `P7`, the first omitted odd mode `P9`, and phase `(a,b) = (1,0)`.
-/

/-! ## The first omitted odd mode -/

/-- Classical centered Legendre `P9`, with the sign converting the shifted
convention to `P9(1) = 1`. -/
def factorTwoCenteredP9 (x : ℝ) : ℝ :=
  -(shiftedLegendreReal 9).eval ((x + 1) / 2)

theorem factorTwoCenteredP9_eq (x : ℝ) :
    factorTwoCenteredP9 x =
      (12155 * x ^ 9 - 25740 * x ^ 7 + 18018 * x ^ 5 -
        4620 * x ^ 3 + 315 * x) / 128 := by
  unfold factorTwoCenteredP9 shiftedLegendreReal
  simp [Polynomial.shiftedLegendre, Finset.sum_range_succ, Nat.choose]
  ring

theorem continuous_factorTwoCenteredP9 : Continuous factorTwoCenteredP9 := by
  rw [show factorTwoCenteredP9 = fun x ↦
      (12155 * x ^ 9 - 25740 * x ^ 7 + 18018 * x ^ 5 -
        4620 * x ^ 3 + 315 * x) / 128 by
    funext x
    exact factorTwoCenteredP9_eq x]
  fun_prop

theorem odd_factorTwoCenteredP9 : Function.Odd factorTwoCenteredP9 := by
  intro x
  rw [factorTwoCenteredP9_eq, factorTwoCenteredP9_eq]
  ring

theorem locallyLipschitzOn_factorTwoCenteredP9 :
    LocallyLipschitzOn (Icc (-1 : ℝ) 1) factorTwoCenteredP9 := by
  have h : ContDiff ℝ 1 factorTwoCenteredP9 := by
    rw [show factorTwoCenteredP9 = fun x ↦
        (12155 * x ^ 9 - 25740 * x ^ 7 + 18018 * x ^ 5 -
          4620 * x ^ 3 + 315 * x) / 128 by
      funext x
      exact factorTwoCenteredP9_eq x]
    fun_prop
  exact h.locallyLipschitz.locallyLipschitzOn

theorem centeredPullback_factorTwoCenteredP9 (t : ℝ) :
    centeredPullback factorTwoCenteredP9 t =
      -(shiftedLegendreReal 9).eval t := by
  unfold centeredPullback factorTwoCenteredP9
  congr 2
  ring

theorem factorTwoCenteredP9_momentsVanishBelow :
    centeredLegendreMomentsVanishBelow factorTwoCenteredP9 9 := by
  intro n hn
  rw [show (fun t : unitInterval ↦
      centeredPullback factorTwoCenteredP9 (t : ℝ) *
        (shiftedLegendreReal n).eval (t : ℝ)) =
      fun t : unitInterval ↦
        -((shiftedLegendreReal 9).eval (t : ℝ) *
          (shiftedLegendreReal n).eval (t : ℝ)) by
    funext t
    rw [centeredPullback_factorTwoCenteredP9]
    ring]
  rw [integral_neg]
  change -(∫ t : unitInterval,
    (fun x : ℝ ↦ (shiftedLegendreReal 9).eval x *
      (shiftedLegendreReal n).eval x) (t : ℝ)) = 0
  rw [integral_unitInterval_eq_intervalIntegral
      (fun x : ℝ ↦ (shiftedLegendreReal 9).eval x *
        (shiftedLegendreReal n).eval x),
    integral_shiftedLegendreReal_mul_eq_zero (by omega), neg_zero]

theorem factorTwoCenteredP9_energy :
    factorTwoIntrinsicEnergy factorTwoCenteredP9 = 2 / 19 := by
  unfold factorTwoIntrinsicEnergy
  rw [show (fun x : ℝ ↦ factorTwoCenteredP9 x ^ 2) = fun x ↦
      ((12155 * x ^ 9 - 25740 * x ^ 7 + 18018 * x ^ 5 -
        4620 * x ^ 3 + 315 * x) / 128) ^ 2 by
    funext x
    rw [factorTwoCenteredP9_eq]]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [YoshidaEndpointOcticPotential.integral_pow_nat]
  norm_num

/-! ## Five exact witness scalars -/

/-- Honest low diagonal of the pure retained `P7` row. -/
def factorTwoP7P9LowDiagonal : ℝ :=
  factorTwoEndpointChannelPhase 0 factorTwoCenteredP7 1 0

/-- Honest tail diagonal of the pure omitted `P9` row. -/
def factorTwoP7P9TailDiagonal : ℝ :=
  factorTwoEndpointChannelPhase 0 factorTwoCenteredP9 1 0

/-- Complete low--tail half-cross between `P7` and `P9`. -/
def factorTwoP7P9Mixed : ℝ :=
  factorTwoEndpointLowTailMixed
    0 0 factorTwoCenteredP7 factorTwoCenteredP9 1 0

/-- The already-certified forward `P7` row charged by the `P678` split. -/
def factorTwoP7P9Forward : ℝ :=
  factorTwoP678ResidualCombinedForwardMixed
    0 factorTwoCenteredP9 0 1 0 1 0

/-- Endpoint-potential mass of the omitted `P9` row. -/
def factorTwoP9Potential : ℝ :=
  factorTwoIntrinsicPotentialEnergy factorTwoCenteredP9

/-- The honest two-by-two low--tail determinant. -/
def factorTwoP7P9FullDeterminant : ℝ :=
  factorTwoP7P9LowDiagonal * factorTwoP7P9TailDiagonal -
    factorTwoP7P9Mixed ^ 2

/-- The enhanced-reserve determinant demanded by the semantic survivor
handoff after the `P678` allocation. -/
def factorTwoP7P9AllocatedDeterminant : ℝ :=
  (factorTwoP7P9LowDiagonal - 1 / 800) *
      (1 / 23750 + (1 / 2 : ℝ) * factorTwoP9Potential) -
    15 * (factorTwoP7P9Mixed - factorTwoP7P9Forward) ^ 2

private theorem factorTwoEndpointPhaseDiagonal_zero (a : ℝ) :
    factorTwoEndpointPhaseDiagonal (0 : ℝ → ℝ) a = 0 := by
  have hclean : yoshidaEndpointOddCleanQuadratic (0 : ℝ → ℝ) = 0 := by
    have h := yoshidaEndpointOddCleanQuadratic_const_mul
      (fun _ : ℝ ↦ (1 : ℝ)) 0
    norm_num at h
    simpa using h
  have hsym := factorTwoCenteredSymmetricPerturbation_smul
    0 (fun _ : ℝ ↦ (1 : ℝ))
  norm_num at hsym
  unfold factorTwoEndpointPhaseDiagonal
  rw [hclean, hsym]
  ring

theorem factorTwoP7P9LowDiagonal_eq_phaseDiagonal :
    factorTwoP7P9LowDiagonal = factorTwoP7PhaseDiagonal 1 := by
  unfold factorTwoP7P9LowDiagonal factorTwoP7PhaseDiagonal
  rw [factorTwoEndpointChannelPhase_eq_diagonals,
    factorTwoEndpointPhaseDiagonal_zero]
  unfold factorTwoEndpointPhaseDiagonal
  ring

theorem factorTwoP7P9TailDiagonal_eq_phaseDiagonal :
    factorTwoP7P9TailDiagonal =
      factorTwoEndpointPhaseDiagonal factorTwoCenteredP9 1 := by
  unfold factorTwoP7P9TailDiagonal
  rw [factorTwoEndpointChannelPhase_eq_diagonals,
    factorTwoEndpointPhaseDiagonal_zero]
  ring

theorem factorTwoP7P9FullDeterminant_eq :
    factorTwoEndpointChannelPhase 0 factorTwoCenteredP7 1 0 *
          factorTwoEndpointChannelPhase 0 factorTwoCenteredP9 1 0 -
        factorTwoEndpointLowTailMixed
            0 0 factorTwoCenteredP7 factorTwoCenteredP9 1 0 ^ 2 =
      factorTwoP7P9FullDeterminant := by
  rfl

theorem factorTwoIntrinsicNineP678LowReserve_P7 :
    factorTwoIntrinsicNineP678LowReserve 0 1 0 = 1 / 750 := by
  unfold factorTwoIntrinsicNineP678LowReserve
  rw [factorTwoCenteredP7_energy]
  norm_num

theorem factorTwoIntrinsicNineSurvivorResidualReserve_P9 :
    factorTwoIntrinsicNineSurvivorResidualReserve 0 factorTwoCenteredP9 =
      1 / 23750 + (1 / 2 : ℝ) * factorTwoP9Potential := by
  have hzeroE : factorTwoIntrinsicEnergy (0 : ℝ → ℝ) = 0 := by
    simp [factorTwoIntrinsicEnergy]
  have hzeroV : factorTwoIntrinsicPotentialEnergy (0 : ℝ → ℝ) = 0 := by
    simp [factorTwoIntrinsicPotentialEnergy]
  unfold factorTwoIntrinsicNineSurvivorResidualReserve factorTwoP9Potential
  rw [hzeroE, hzeroV]
  rw [factorTwoCenteredP9_energy]
  norm_num

private theorem factorTwoIntrinsicNineEvenProfile_zero :
    factorTwoIntrinsicNineEvenProfile 0 0 0 0 0 = 0 := by
  funext x
  simp [factorTwoIntrinsicNineEvenProfile,
    factorTwoIntrinsicEightEvenProfile, factorTwoEvenStructuralLowProfile,
    factorTwoIntrinsicSixEvenTail]

private theorem factorTwoIntrinsicNineOddProfile_P7 :
    factorTwoIntrinsicNineOddProfile 0 0 0 1 = factorTwoCenteredP7 := by
  funext x
  simp [factorTwoIntrinsicNineOddProfile,
    factorTwoIntrinsicEightOddProfile, factorTwoIntrinsicSixOddTail,
    factorTwoOddStructuralLowProfile]

/-- For this witness the honest survivor is exactly the full mixed row minus
the certified forward row. -/
theorem factorTwoIntrinsicNineRemainingMixed_P7_P9 :
    factorTwoIntrinsicNineRemainingMixed
        0 factorTwoCenteredP9 0 0 0 0 0 0 0 0 1 1 0 =
      factorTwoP7P9Mixed - factorTwoP7P9Forward := by
  have hzeroGap : centeredLegendreMomentsVanishBelow (0 : ℝ → ℝ) 9 := by
    intro n hn
    simp [centeredPullback]
  have hzeroLocal :
      LocallyLipschitzOn (Icc (-1 : ℝ) 1) (0 : ℝ → ℝ) := by
    have hdiff : ContDiff ℝ 1 (fun _ : ℝ ↦ (0 : ℝ)) := contDiff_const
    change LocallyLipschitzOn (Icc (-1) 1) (fun _ : ℝ ↦ (0 : ℝ))
    exact hdiff.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  have hmix :=
    factorTwoEndpointLowTailMixed_intrinsicNine_eq_P678_add_remaining
      (0 : ℝ → ℝ) factorTwoCenteredP9
      continuous_zero continuous_factorTwoCenteredP9
      hzeroLocal locallyLipschitzOn_factorTwoCenteredP9
      odd_factorTwoCenteredP9 hzeroGap
      factorTwoCenteredP9_momentsVanishBelow
      0 0 0 0 0 0 0 0 1 1 0
  rw [factorTwoIntrinsicNineEvenProfile_zero,
    factorTwoIntrinsicNineOddProfile_P7] at hmix
  unfold factorTwoP7P9Mixed factorTwoP7P9Forward
  linarith

/-- Exact scalar reduction of the enhanced-reserve allocation.  A sign
certificate for the right side is deliberately a separate theorem. -/
theorem factorTwoP7P9AllocatedDeterminant_eq :
    (factorTwoEndpointChannelPhase 0 factorTwoCenteredP7 1 0 -
          (15 / 16 : ℝ) * factorTwoIntrinsicNineP678LowReserve 0 1 0) *
        factorTwoIntrinsicNineSurvivorResidualReserve 0 factorTwoCenteredP9 -
      15 * factorTwoIntrinsicNineRemainingMixed
          0 factorTwoCenteredP9 0 0 0 0 0 0 0 0 1 1 0 ^ 2 =
      factorTwoP7P9AllocatedDeterminant := by
  rw [factorTwoIntrinsicNineP678LowReserve_P7,
    factorTwoIntrinsicNineSurvivorResidualReserve_P9,
    factorTwoIntrinsicNineRemainingMixed_P7_P9]
  unfold factorTwoP7P9AllocatedDeterminant factorTwoP7P9LowDiagonal
  ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP7P9ScalarObstructionStructural
