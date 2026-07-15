import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreFourFiveRankStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCoupledCleanReduction

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP5EndpointStructural

noncomputable section

open MeasureTheory Real
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddLowGramExpansion
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointChannelRadius
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseArchRankDiskSchur
open YoshidaFactorTwoPhaseCoupledCleanReduction
open YoshidaFactorTwoPhaseCoupledRankLimit
open YoshidaFactorTwoPhaseDiskSchur
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveSchur
open YoshidaFactorTwoPhaseLegendreFourFiveRankStructural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseSymmetricCoercivity

/-!
# Structural endpoint reserve for the intrinsic `P5` mode

The clean `P5` reserve dominates the complete hyperbolic rank energy and
the two retained prime atoms with a strict rational margin.  Specializing
the profile-level coupled-rank lower bound therefore gives a common strict
lower bound at both symmetric phase endpoints, without evaluating either
endpoint diagonal.
-/

private theorem factorTwoEvenRankEnergy_zero :
    factorTwoEvenRankEnergy (0 : ℝ → ℝ) = 0 := by
  unfold factorTwoEvenRankEnergy centeredCoshMoment
  simp

private theorem factorTwoCoupledRankEnergy_zero_P5 :
    factorTwoCoupledRankEnergy (0 : ℝ → ℝ) factorTwoCenteredP5 =
      factorTwoOddRankEnergy factorTwoCenteredP5 := by
  rw [factorTwoCoupledRankEnergy_eq_even_add_odd
    (0 : ℝ → ℝ) factorTwoCenteredP5 continuous_zero
    continuous_factorTwoCenteredP5 (fun _ ↦ rfl) odd_factorTwoCenteredP5]
  rw [factorTwoEvenRankEnergy_zero, zero_add]

private theorem factorTwoCenteredP5_energy_eq :
    factorTwoIntrinsicEnergy factorTwoCenteredP5 = 2 / 11 := by
  simpa [factorTwoIntrinsicEnergy] using integral_factorTwoCenteredP5_sq

private theorem yoshidaEndpointOddCleanQuadratic_zero :
    yoshidaEndpointOddCleanQuadratic (0 : ℝ → ℝ) = 0 := by
  change yoshidaEndpointOddCleanQuadratic (fun _ : ℝ ↦ 0) = 0
  simpa using
    (yoshidaEndpointOddCleanQuadratic_const_mul factorTwoCenteredP5 0)

private theorem factorTwoCenteredSymmetricPerturbation_zero :
    factorTwoCenteredSymmetricPerturbation (0 : ℝ → ℝ) = 0 := by
  change factorTwoCenteredSymmetricPerturbation (fun _ : ℝ ↦ 0) = 0
  simpa [Pi.smul_apply] using
    (factorTwoCenteredSymmetricPerturbation_smul 0 factorTwoCenteredP5)

private theorem factorTwoEndpointChannelPhase_zero_P5
    (a : ℝ) :
    factorTwoEndpointChannelPhase (0 : ℝ → ℝ)
        factorTwoCenteredP5 a 0 =
      factorTwoIntrinsicSixP5Diagonal a := by
  rw [factorTwoEndpointChannelPhase_eq_diagonals]
  simp [factorTwoEndpointPhaseDiagonal, factorTwoIntrinsicSixP5Diagonal,
    yoshidaEndpointOddCleanQuadratic_zero,
    factorTwoCenteredSymmetricPerturbation_zero]

private theorem one_div_thirty_lt_factorTwoIntrinsicSixP5Diagonal_endpoint
    (a : ℝ) (ha : |a| = 1) (haSq : a ^ 2 ≤ 1) :
    (1 / 30 : ℝ) < factorTwoIntrinsicSixP5Diagonal a := by
  have hrank := factorTwoOddRankEnergy_P5_le_three_twentieths
  have hclean := four_thirds_energy_le_clean_P5
  have henergy := factorTwoCenteredP5_energy_eq
  have hprime := primeBlock_upperCoefficient_lt_one
  have hprimeProduct :
      (Real.log 2 / Real.sqrt 2 +
          (Real.log 3 / Real.sqrt 3) / 2) *
          factorTwoIntrinsicEnergy factorTwoCenteredP5 <
        factorTwoIntrinsicEnergy factorTwoCenteredP5 := by
    apply mul_lt_of_lt_one_left
    · rw [henergy]
      norm_num
    · exact hprime
  have hlower := factorTwoEndpointChannelPhase_lower_by_coupledRank
    (0 : ℝ → ℝ) factorTwoCenteredP5 continuous_zero
    continuous_factorTwoCenteredP5 (fun _ ↦ rfl)
    odd_factorTwoCenteredP5 a 0 (by simpa using haSq)
  rw [factorTwoEndpointChannelPhase_zero_P5,
    factorTwoCoupledRankEnergy_zero_P5] at hlower
  simp [factorTwoEndpointChannelCleanSum,
    yoshidaEndpointOddCleanQuadratic_zero, ha] at hlower
  nlinarith [hrank, hclean, hprimeProduct, henergy,
    integral_factorTwoCenteredP5_sq]

/-- The plus endpoint `P5` diagonal retains a rational `1/30` reserve. -/
theorem one_div_thirty_lt_factorTwoIntrinsicSixP5Diagonal_one :
    (1 / 30 : ℝ) < factorTwoIntrinsicSixP5Diagonal 1 := by
  apply one_div_thirty_lt_factorTwoIntrinsicSixP5Diagonal_endpoint
  · norm_num
  · norm_num

/-- The minus endpoint `P5` diagonal retains the same rational reserve. -/
theorem one_div_thirty_lt_factorTwoIntrinsicSixP5Diagonal_neg_one :
    (1 / 30 : ℝ) < factorTwoIntrinsicSixP5Diagonal (-1) := by
  apply one_div_thirty_lt_factorTwoIntrinsicSixP5Diagonal_endpoint
  · norm_num
  · norm_num

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP5EndpointStructural
