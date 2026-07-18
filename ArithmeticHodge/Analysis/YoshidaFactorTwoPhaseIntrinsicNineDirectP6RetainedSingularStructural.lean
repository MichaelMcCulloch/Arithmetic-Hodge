import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6BorderStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicRetainedSingularGapStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6RetainedSingularStructural

noncomputable section

open UnitIntervalLogEnergyAffine
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6BorderStructural
open YoshidaFactorTwoPhaseIntrinsicProjectedRemainder
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseIntrinsicRetainedSingularGapStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFactorTwoPhaseSingularWeightedCauchyStructural

/-!
# A retained singular reserve inside the charged `P6` diagonal

The `P6` diagonal can pay its exact share of the cutoff-nine reserve while
still retaining `1/128` of the positive singular operator.  This is the
tail-side fraction compatible with the existing `1/2048` low-side retention:
their product is `(1/512)^2`, so the corresponding pole row can later be
removed losslessly by singular Cauchy--Schwarz.
-/

/-- Uniformly on the phase disk, the charged `P6` diagonal retains
`1/128` of the half-singular energy and a strictly positive rational `L²`
complement. -/
theorem factorTwoIntrinsicNineDirectP6RetainedDiagonal_retain_one_div_128
    (a b : ℝ) (ha : a ^ 2 ≤ 1) :
    (1 / 128 : ℝ) * ((1 / 2 : ℝ) *
        factorTwoPhaseSingularWeightedEnergy
          factorTwoCenteredP6 (0 : ℝ → ℝ) a 0) +
      (741739 / 46126080 : ℝ) *
        factorTwoIntrinsicEnergy factorTwoCenteredP6 ≤
      factorTwoIntrinsicNineDirectP6RetainedDiagonal a b := by
  have hab : a ^ 2 + (0 : ℝ) ^ 2 ≤ 1 := by simpa using ha
  have hzeroLocal :
      LocallyLipschitzOn (Icc (-1 : ℝ) 1) (0 : ℝ → ℝ) := by
    have hdiff : ContDiff ℝ 1 (fun _ : ℝ ↦ (0 : ℝ)) := contDiff_const
    exact hdiff.locallyLipschitz.locallyLipschitzOn
  have hzeroGap :
      centeredLegendreMomentsVanishBelow (0 : ℝ → ℝ) 6 := by
    intro n hn
    simp [centeredPullback]
  have hbase := factorTwoEndpointChannelPhase_general_gap_retain_singular
    factorTwoCenteredP6 (0 : ℝ → ℝ)
    continuous_factorTwoCenteredP6 continuous_zero
    even_factorTwoCenteredP6 (by intro x; simp)
    factorTwoCenteredP6_p0_zero
    locallyLipschitzOn_factorTwoCenteredP6 hzeroLocal
    6 6 factorTwoCenteredP6_momentsVanishBelow hzeroGap
    a 0 (1 / 128 : ℝ) hab (by norm_num) (by norm_num)
  have hzeroPotential :
      factorTwoIntrinsicPotentialEnergy (0 : ℝ → ℝ) = 0 := by
    unfold factorTwoIntrinsicPotentialEnergy
    simp
  have hzeroEnergy :
      factorTwoIntrinsicEnergy (0 : ℝ → ℝ) = 0 := by
    unfold factorTwoIntrinsicEnergy
    simp
  rw [factorTwoCenteredP6_potential_ratio,
    hzeroPotential, hzeroEnergy] at hbase
  norm_num only [mul_zero, add_zero] at hbase
  have hbudget := P6_projected_loss_budget a ha
  have hmargin :
      (3 / 320 + 741739 / 46126080 : ℝ) ≤
        (1 - (1 / 128 : ℝ)) * (harmonic 6 : ℝ) -
          factorTwoIntrinsicProjectedEvenRemainderLoss a 0 -
          ((1 + (1 / 128 : ℝ)) / 2) * Real.log 2 +
          ((1 - (1 / 128 : ℝ)) / 2) *
            (249251 / 180180 - Real.log 2) := by
    norm_num [harmonic, Finset.sum_range_succ] at hbudget ⊢
    linarith
  have hscaled := mul_le_mul_of_nonneg_right hmargin
    (factorTwoIntrinsicEnergy_nonneg factorTwoCenteredP6)
  have hphase :
      (1 / 128 : ℝ) * ((1 / 2 : ℝ) *
          factorTwoPhaseSingularWeightedEnergy
            factorTwoCenteredP6 (0 : ℝ → ℝ) a 0) +
        (3 / 320 + 741739 / 46126080 : ℝ) *
          factorTwoIntrinsicEnergy factorTwoCenteredP6 ≤
        factorTwoP6PhaseDiagonal a := by
    rw [← phase_P6_zero_eq_diagonal a 0]
    nlinarith
  rw [factorTwoIntrinsicNineDirectP6RetainedDiagonal_eq]
  nlinarith

/-- Positive-endpoint specialization of the uniform retained-singular
reserve. -/
theorem factorTwoIntrinsicNineDirectP6RetainedDiagonal_plus_retain_one_div_128 :
    (1 / 128 : ℝ) * ((1 / 2 : ℝ) *
        factorTwoPhaseSingularWeightedEnergy
          factorTwoCenteredP6 (0 : ℝ → ℝ) 1 0) +
      (741739 / 46126080 : ℝ) *
        factorTwoIntrinsicEnergy factorTwoCenteredP6 ≤
      factorTwoIntrinsicNineDirectP6RetainedDiagonal 1 0 := by
  exact factorTwoIntrinsicNineDirectP6RetainedDiagonal_retain_one_div_128
    1 0 (by norm_num)

/-- Negative-endpoint specialization of the uniform retained-singular
reserve. -/
theorem factorTwoIntrinsicNineDirectP6RetainedDiagonal_minus_retain_one_div_128 :
    (1 / 128 : ℝ) * ((1 / 2 : ℝ) *
        factorTwoPhaseSingularWeightedEnergy
          factorTwoCenteredP6 (0 : ℝ → ℝ) (-1) 0) +
      (741739 / 46126080 : ℝ) *
        factorTwoIntrinsicEnergy factorTwoCenteredP6 ≤
      factorTwoIntrinsicNineDirectP6RetainedDiagonal (-1) 0 := by
  exact factorTwoIntrinsicNineDirectP6RetainedDiagonal_retain_one_div_128
    (-1) 0 (by norm_num)

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6RetainedSingularStructural
