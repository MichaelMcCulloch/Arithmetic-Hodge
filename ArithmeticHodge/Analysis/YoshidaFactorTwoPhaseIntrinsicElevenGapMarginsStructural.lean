import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicGeneralGapReserveStructural

set_option autoImplicit false

open Real

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenGapMarginsStructural

open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicGeneralGapReserveStructural
open YoshidaFactorTwoPhaseIntrinsicProjectedRemainder
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseFullProfile
open YoshidaEndpointEvenStructuralReduction

noncomputable section

/-!
# Uniform scalar margins at the eleventh Legendre gap

Moving both parity tails above degree ten does more than make the projected
remainder coercive.  The two additional harmonic steps beyond the established
even cutoff, and the one additional step beyond the established odd cutoff,
leave explicit rational multiplication weights.  These are the denominators
used by the constrained weighted-dual low--tail estimate.
-/

/-- The even gap-eleven multiplication weight retains the exact two harmonic
steps `1/10 + 1/11`. -/
theorem eleven_even_gap_margin_le
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    (21 / 110 : ℝ) ≤
      (harmonic 11 : ℝ) -
        factorTwoIntrinsicProjectedEvenRemainderLoss a b -
        Real.log 2 / 2 := by
  have hloss := projectedEvenRemainderLoss_le_harmonic_nine a b hab
  norm_num [harmonic, Finset.sum_range_succ] at hloss ⊢
  linarith

/-- The odd gap-eleven multiplication weight retains the exact harmonic step
`1/11`. -/
theorem eleven_odd_gap_margin_le
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    (1 / 11 : ℝ) ≤
      (harmonic 11 : ℝ) -
        factorTwoIntrinsicProjectedOddRemainderLoss a b -
        Real.log 2 / 2 := by
  have hloss := projectedOddRemainderLoss_le_harmonic_ten a b hab
  norm_num [harmonic, Finset.sum_range_succ] at hloss ⊢
  linarith

/-- In particular, the even gap-eleven multiplication weight is strictly
positive throughout the closed phase disk. -/
theorem eleven_even_gap_margin_pos
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    0 < (harmonic 11 : ℝ) -
        factorTwoIntrinsicProjectedEvenRemainderLoss a b -
        Real.log 2 / 2 :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 21 / 110)
    (eleven_even_gap_margin_le a b hab)

/-- In particular, the odd gap-eleven multiplication weight is strictly
positive throughout the closed phase disk. -/
theorem eleven_odd_gap_margin_pos
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    0 < (harmonic 11 : ℝ) -
        factorTwoIntrinsicProjectedOddRemainderLoss a b -
        Real.log 2 / 2 :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 11)
    (eleven_odd_gap_margin_le a b hab)

/-- The arbitrary-gap reserve specialized at cutoff eleven, with its phase
dependent scalar coefficients replaced by the uniform rational margins.  The
potential term remains intact, so this is a genuine multiplication-weight
tail lower form rather than a bare `L²` estimate. -/
theorem factorTwoEndpointChannelPhase_gap_eleven_reserve
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (he : Function.Even e) (ho : Function.Odd o)
    (he0 : centeredEvenP0Coefficient e = 0)
    (helocal : LocallyLipschitzOn (Set.Icc (-1) 1) e)
    (holocal : LocallyLipschitzOn (Set.Icc (-1) 1) o)
    (heLow : centeredLegendreMomentsVanishBelow e 11)
    (hoLow : centeredLegendreMomentsVanishBelow o 11)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    (21 / 110 : ℝ) * factorTwoIntrinsicEnergy e +
        (1 / 11 : ℝ) * factorTwoIntrinsicEnergy o +
        (1 / 2 : ℝ) *
          (factorTwoIntrinsicPotentialEnergy e +
            factorTwoIntrinsicPotentialEnergy o) ≤
      factorTwoEndpointChannelPhase e o a b := by
  have hreserve := factorTwoEndpointChannelPhase_general_gap_reserve
    e o hec hoc he ho he0 helocal holocal 11 11 heLow hoLow a b hab
  have heMargin := eleven_even_gap_margin_le a b hab
  have hoMargin := eleven_odd_gap_margin_le a b hab
  have heEnergy := factorTwoIntrinsicEnergy_nonneg e
  have hoEnergy := factorTwoIntrinsicEnergy_nonneg o
  have heScaled := mul_le_mul_of_nonneg_right heMargin heEnergy
  have hoScaled := mul_le_mul_of_nonneg_right hoMargin hoEnergy
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenGapMarginsStructural
