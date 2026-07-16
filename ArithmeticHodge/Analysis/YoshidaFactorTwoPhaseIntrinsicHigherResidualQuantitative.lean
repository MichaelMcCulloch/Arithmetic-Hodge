import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicHigherResidual

set_option autoImplicit false

open Complex MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicHigherResidualQuantitative

open ShiftedLegendreL2Basis
open ShiftedLegendreL2HigherGap
open ShiftedLegendreCenteredParity
open ShiftedLegendreOrthogonality
open YoshidaEndpointHyperbolicBound
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine
open UnitIntervalLogEnergyLipschitz
open UnitIntervalLogEnergyProjection
open CenteredOddOneThreeEnergy
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointOddSharpMassLoss
open YoshidaEndpointPullbackLipschitz
open YoshidaEndpointScalarStructuralUpper
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicProjectedRemainder
open YoshidaFactorTwoPhaseIntrinsicResidual

noncomputable section

/-!
# Quantitative structural reserve on the higher Legendre residual

The cutoff-nine/cutoff-ten argument has strict rational slack after paying
the complete projected phase loss.  This module retains that slack, together
with the half-potential term already present in the singular-square estimate.
No retained Legendre mode is inspected.
-/

/-- The ninth even and tenth odd harmonic gaps retain explicit rational
`L²` reserves, as well as half of both endpoint-potential energies, uniformly
on the closed phase disk. -/
theorem factorTwoEndpointChannelPhase_quantitative_of_higher_residual
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (he : Function.Even e) (ho : Function.Odd o)
    (he0 : centeredEvenP0Coefficient e = 0)
    (helocal : LocallyLipschitzOn (Icc (-1) 1) e)
    (holocal : LocallyLipschitzOn (Icc (-1) 1) o)
    (heLow : centeredLegendreMomentsVanishBelow e 9)
    (hoLow : centeredLegendreMomentsVanishBelow o 10)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    (1 / 2000 : ℝ) * factorTwoIntrinsicEnergy e +
        (2 / 25 : ℝ) * factorTwoIntrinsicEnergy o +
        (1 / 2 : ℝ) *
          (factorTwoIntrinsicPotentialEnergy e +
            factorTwoIntrinsicPotentialEnergy o) ≤
      factorTwoEndpointChannelPhase e o a b := by
  have heRaw := harmonic_mul_intrinsicEnergy_le_raw_div_four
    e hec helocal 9 heLow
  have hoRaw := harmonic_mul_intrinsicEnergy_le_raw_div_four
    o hoc holocal 10 hoLow
  have hprotected := raw_add_half_potential_sub_half_logMass_le_protected
    e o hec hoc helocal holocal a b hab
  have heLoss := projectedEvenRemainderLoss_lt_structural_bound a b hab
  have hremainder := neg_factorTwoIntrinsicSignedRemainder_le_projected_energy
    e o hec hoc he ho he0 a b hab
  have heEnergy := factorTwoIntrinsicEnergy_nonneg e
  have hoEnergy := factorTwoIntrinsicEnergy_nonneg o
  have heBudget :
      factorTwoIntrinsicProjectedEvenRemainderLoss a b +
          Real.log 2 / 2 + (1 / 2000 : ℝ) ≤
        (harmonic 9 : ℝ) := by
    have hlog : Real.log 2 < (7 / 10 : ℝ) :=
      log_two_lt_one_thousand_seven_hundred_thirty_three_div_two_thousand_five_hundred.trans
        (by norm_num)
    norm_num [harmonic, Finset.sum_range_succ] at heLoss ⊢
    linarith
  have hoBudget :
      factorTwoIntrinsicProjectedOddRemainderLoss a b +
          Real.log 2 / 2 + (2 / 25 : ℝ) ≤
        (harmonic 10 : ℝ) := by
    have hsqrt :=
      inv_sqrt_two_lt_one_hundred_seventy_seven_div_two_hundred_fifty
    have hsqrt' : 1 / Real.sqrt 2 < (177 / 250 : ℝ) := by
      simpa only [one_div] using hsqrt
    have hlogLower := six_hundred_ninety_three_div_thousand_lt_log_two
    have heLossRational :
        factorTwoIntrinsicProjectedEvenRemainderLoss a b <
          (14868913 / 6000000 : ℝ) := by
      calc
        factorTwoIntrinsicProjectedEvenRemainderLoss a b <
            (19 / 24 + 8 / 25 + 338887 / 250000 + 7 / 640 : ℝ) := heLoss
        _ = 14868913 / 6000000 := by norm_num
    have hLossSqrt :
        factorTwoIntrinsicProjectedEvenRemainderLoss a b +
            1 / Real.sqrt 2 <
          (14868913 / 6000000 : ℝ) + 177 / 250 :=
      add_lt_add heLossRational hsqrt'
    have hNegLog :
        -Real.log 2 / 2 < -(693 / 1000 : ℝ) / 2 := by
      linarith
    have hTotal :
        factorTwoIntrinsicProjectedEvenRemainderLoss a b +
              1 / Real.sqrt 2 - Real.log 2 / 2 + 2 / 25 <
          (14868913 / 6000000 : ℝ) + 177 / 250 -
            (693 / 1000 : ℝ) / 2 + 2 / 25 := by
      linarith
    have hRational :
        (14868913 / 6000000 : ℝ) + 177 / 250 -
            (693 / 1000 : ℝ) / 2 + 2 / 25 <
          (harmonic 10 : ℝ) := by
      norm_num [harmonic, Finset.sum_range_succ]
    unfold factorTwoIntrinsicProjectedOddRemainderLoss
    linarith [hTotal, hRational]
  have heBudgetScaled := mul_le_mul_of_nonneg_right heBudget heEnergy
  have hoBudgetScaled := mul_le_mul_of_nonneg_right hoBudget hoEnergy
  rw [factorTwoEndpointChannelPhase_eq_protected_add_signedRemainder
    e o hec hoc a b]
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicHigherResidualQuantitative
