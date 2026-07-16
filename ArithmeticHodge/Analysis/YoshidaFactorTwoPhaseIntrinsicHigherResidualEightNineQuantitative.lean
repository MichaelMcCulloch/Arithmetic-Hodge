import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicHigherResidualEightNineStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicHigherResidualEightNineQuantitative

open ShiftedLegendreL2HigherGap
open YoshidaConstantBounds
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointOddSharpMassLoss
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicHigherResidualEightNineStructural
open YoshidaFactorTwoPhaseIntrinsicProjectedRemainder
open YoshidaFactorTwoPhaseIntrinsicResidual

noncomputable section

/-!
# Quantitative cutoff-eight/cutoff-nine residual reserve

The structural endpoint-potential gain at the first even residual mode and
the ninth odd harmonic gap both have strict slack after paying the complete
projected signed remainder.  We retain small rational shares of both `L²`
energies, together with the unused odd endpoint-potential half, for the
later low--residual Schur complement.
-/

private theorem projectedEvenRemainderLoss_add_reserve_le
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    factorTwoIntrinsicProjectedEvenRemainderLoss a b +
        Real.log 2 / 2 + (1 / 250 : ℝ) ≤
      (harmonic 8 : ℝ) + 1 / 10 := by
  have hloss := projectedEvenRemainderLoss_lt_4926971_div_2000000 a b hab
  have hlog : Real.log 2 < (7 / 10 : ℝ) :=
    log_two_lt_one_thousand_seven_hundred_thirty_three_div_two_thousand_five_hundred.trans
      (by norm_num)
  norm_num [harmonic, Finset.sum_range_succ] at hloss ⊢
  linarith

private theorem projectedOddRemainderLoss_add_reserve_le
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    factorTwoIntrinsicProjectedOddRemainderLoss a b +
        Real.log 2 / 2 + (1 / 2500 : ℝ) ≤
      (harmonic 9 : ℝ) := by
  have heven := projectedEvenRemainderLoss_lt_4926971_div_2000000 a b hab
  have hsqrt := inv_sqrt_two_lt_one_hundred_seventy_seven_div_two_hundred_fifty
  have hsqrt' : (Real.sqrt 2)⁻¹ < (177 / 250 : ℝ) := by
    simpa only [one_div] using hsqrt
  have hlogLower := six_hundred_ninety_three_div_thousand_lt_log_two
  unfold factorTwoIntrinsicProjectedOddRemainderLoss
  norm_num [harmonic, Finset.sum_range_succ] at heven ⊢
  linarith

/-- The cutoff-eight/cutoff-nine phase retains explicit even and odd `L²`
reserves and the full unused odd endpoint-potential half. -/
theorem factorTwoEndpointChannelPhase_quantitative_of_eight_nine_residual
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (he : Function.Even e) (ho : Function.Odd o)
    (he0 : centeredEvenP0Coefficient e = 0)
    (helocal : LocallyLipschitzOn (Icc (-1) 1) e)
    (holocal : LocallyLipschitzOn (Icc (-1) 1) o)
    (heLow : centeredLegendreMomentsVanishBelow e 8)
    (hoLow : centeredLegendreMomentsVanishBelow o 9)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    (1 / 250 : ℝ) * factorTwoIntrinsicEnergy e +
        (1 / 2500 : ℝ) * factorTwoIntrinsicEnergy o +
        (1 / 2 : ℝ) * factorTwoIntrinsicPotentialEnergy o ≤
      factorTwoEndpointChannelPhase e o a b := by
  have heReserve :=
    harmonic_eight_add_one_tenth_mul_intrinsicEnergy_le_raw_add_half_potential
      e hec he helocal heLow
  have hoRaw := harmonic_mul_intrinsicEnergy_le_raw_div_four
    o hoc holocal 9 hoLow
  have hprotected := raw_add_half_potential_sub_half_logMass_le_protected
    e o hec hoc helocal holocal a b hab
  have heBudget := projectedEvenRemainderLoss_add_reserve_le a b hab
  have hoBudget := projectedOddRemainderLoss_add_reserve_le a b hab
  have hremainder := neg_factorTwoIntrinsicSignedRemainder_le_projected_energy
    e o hec hoc he ho he0 a b hab
  have heEnergy := factorTwoIntrinsicEnergy_nonneg e
  have hoEnergy := factorTwoIntrinsicEnergy_nonneg o
  have heBudgetScaled := mul_le_mul_of_nonneg_right heBudget heEnergy
  have hoBudgetScaled := mul_le_mul_of_nonneg_right hoBudget hoEnergy
  rw [factorTwoEndpointChannelPhase_eq_protected_add_signedRemainder
    e o hec hoc a b]
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicHigherResidualEightNineQuantitative
