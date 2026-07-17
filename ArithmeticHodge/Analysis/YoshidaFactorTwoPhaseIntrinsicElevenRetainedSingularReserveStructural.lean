import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenGapMarginsStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicRetainedSingularGapStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedSingularReserveStructural

open YoshidaEndpointEvenStructuralReduction
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicElevenGapMarginsStructural
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicProjectedRemainder
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseIntrinsicRetainedSingularGapStructural
open YoshidaFactorTwoPhaseSingularWeightedCauchyStructural

noncomputable section

/-!
# A retained singular reserve at the eleventh Legendre gap

The scalar cutoff-eleven reserve discards the positive reflected-pole Gram.
For low--tail completion it is useful to keep a small, uniform fraction of
that operator on both diagonal blocks.  The theorem below retains `1 / 64`
of the singular energy while preserving explicit positive multiplication
weights in both parity channels.  No Legendre row is enumerated.
-/

/-- The multiplication reserve left after retaining `1 / 64` of the
positive singular operator. -/
def factorTwoIntrinsicElevenRetainedWeightedReserve
    (e o : ℝ → ℝ) : ℝ :=
  (13 / 100 : ℝ) * factorTwoIntrinsicEnergy e +
    (1 / 30 : ℝ) * factorTwoIntrinsicEnergy o +
    (63 / 128 : ℝ) *
      (factorTwoIntrinsicPotentialEnergy e +
        factorTwoIntrinsicPotentialEnergy o)

theorem factorTwoIntrinsicElevenRetainedWeightedReserve_nonneg
    (e o : ℝ → ℝ) :
    0 ≤ factorTwoIntrinsicElevenRetainedWeightedReserve e o := by
  have he := factorTwoIntrinsicEnergy_nonneg e
  have ho := factorTwoIntrinsicEnergy_nonneg o
  have hVe := factorTwoIntrinsicPotentialEnergy_nonneg e
  have hVo := factorTwoIntrinsicPotentialEnergy_nonneg o
  unfold factorTwoIntrinsicElevenRetainedWeightedReserve
  positivity

/-- At moment gap eleven, the complete phase retains `1 / 64` of the
positive singular energy and the displayed positive multiplication
reserve, uniformly throughout the closed phase disk. -/
theorem factorTwoEndpointChannelPhase_gap_eleven_retain_one_div_sixty_four
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (he : Function.Even e) (ho : Function.Odd o)
    (he0 : centeredEvenP0Coefficient e = 0)
    (helocal : LocallyLipschitzOn (Icc (-1) 1) e)
    (holocal : LocallyLipschitzOn (Icc (-1) 1) o)
    (heLow : centeredLegendreMomentsVanishBelow e 11)
    (hoLow : centeredLegendreMomentsVanishBelow o 11)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    (1 / 64 : ℝ) * ((1 / 2 : ℝ) *
        factorTwoPhaseSingularWeightedEnergy e o a b) +
      factorTwoIntrinsicElevenRetainedWeightedReserve e o ≤
        factorTwoEndpointChannelPhase e o a b := by
  have hbase := factorTwoEndpointChannelPhase_general_gap_retain_singular
    e o hec hoc he ho he0 helocal holocal 11 11 heLow hoLow
      a b (1 / 64 : ℝ) hab (by norm_num) (by norm_num)
  have heBase := eleven_even_gap_margin_le a b hab
  have hoBase := eleven_odd_gap_margin_le a b hab
  have hlog := Real.log_two_lt_d9
  have heMargin :
      (13 / 100 : ℝ) ≤
        (1 - (1 / 64 : ℝ)) * (harmonic 11 : ℝ) -
          factorTwoIntrinsicProjectedEvenRemainderLoss a b -
          ((1 + (1 / 64 : ℝ)) / 2) * Real.log 2 := by
    norm_num [harmonic, Finset.sum_range_succ] at heBase ⊢
    linarith
  have hoMargin :
      (1 / 30 : ℝ) ≤
        (1 - (1 / 64 : ℝ)) * (harmonic 11 : ℝ) -
          factorTwoIntrinsicProjectedOddRemainderLoss a b -
          ((1 + (1 / 64 : ℝ)) / 2) * Real.log 2 := by
    norm_num [harmonic, Finset.sum_range_succ] at hoBase ⊢
    linarith
  have heScaled := mul_le_mul_of_nonneg_right heMargin
    (factorTwoIntrinsicEnergy_nonneg e)
  have hoScaled := mul_le_mul_of_nonneg_right hoMargin
    (factorTwoIntrinsicEnergy_nonneg o)
  unfold factorTwoIntrinsicElevenRetainedWeightedReserve
  norm_num [harmonic, Finset.sum_range_succ] at heScaled hoScaled
  norm_num at hbase ⊢
  linarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedSingularReserveStructural
