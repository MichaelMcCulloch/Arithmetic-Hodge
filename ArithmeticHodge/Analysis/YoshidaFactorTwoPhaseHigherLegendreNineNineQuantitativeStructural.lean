import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseHigherLegendreStructuralPositive
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicHigherResidualEightNineQuantitative

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseHigherLegendreNineNineQuantitativeStructural

open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseHigherLegendreDecomposition
open YoshidaFactorTwoPhaseHigherLegendreStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicHigherResidualEightNineQuantitative
open YoshidaFactorTwoPhaseIntrinsicResidual

noncomputable section

/-!
# Canonical cutoff-nine/cutoff-nine residual handoff

The even cutoff-nine residual has a stronger moment gap than the cutoff-eight
hypothesis required by the quantitative abstract residual theorem.  The odd
cutoff-nine residual supplies that theorem's exact odd gap.  This file records
the resulting reserve and the exact outer low/residual Schur handoff without
introducing any finite-mode estimate.
-/

/-- The canonical cutoff-nine/cutoff-nine residual retains the quantitative
energy and odd-potential reserve of the abstract cutoff-eight/cutoff-nine
theorem. -/
theorem factorTwoEndpointChannelPhase_nine_nine_higherResidual_quantitative
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (he : Function.Even e) (ho : Function.Odd o)
    (helocal : LocallyLipschitzOn (Icc (-1) 1) e)
    (holocal : LocallyLipschitzOn (Icc (-1) 1) o)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    (1 / 250 : ℝ) * factorTwoIntrinsicEnergy
          (centeredLegendreHigherResidual e hec 9) +
        (1 / 2500 : ℝ) * factorTwoIntrinsicEnergy
          (centeredLegendreHigherResidual o hoc 9) +
        (1 / 2 : ℝ) * factorTwoIntrinsicPotentialEnergy
          (centeredLegendreHigherResidual o hoc 9) ≤
      factorTwoEndpointChannelPhase
        (centeredLegendreHigherResidual e hec 9)
        (centeredLegendreHigherResidual o hoc 9) a b := by
  let eH := centeredLegendreHigherResidual e hec 9
  let oH := centeredLegendreHigherResidual o hoc 9
  have heLowNine := centeredLegendreHigherResidual_momentsVanishBelow e hec 9
  have heLowEight : centeredLegendreMomentsVanishBelow eH 8 := by
    intro n hn
    exact heLowNine n (by omega)
  have hoLow := centeredLegendreHigherResidual_momentsVanishBelow o hoc 9
  apply factorTwoEndpointChannelPhase_quantitative_of_eight_nine_residual
    eH oH
    (continuous_centeredLegendreHigherResidual e hec 9)
    (continuous_centeredLegendreHigherResidual o hoc 9)
    (centeredLegendreHigherResidual_even e hec he 9)
    (centeredLegendreHigherResidual_odd o hoc ho 9)
    (centeredEvenP0Coefficient_eq_zero_of_momentsVanishBelow
      eH (by norm_num) heLowNine)
    (locallyLipschitzOn_centeredLegendreHigherResidual e hec helocal 9)
    (locallyLipschitzOn_centeredLegendreHigherResidual o hoc holocal 9)
    heLowEight hoLow a b hab

/-- Once the cutoff-nine/cutoff-nine finite block and its exact mixed Schur
determinant are controlled, the quantitative residual theorem closes the
complete profile. -/
theorem factorTwoEndpointChannelPhase_nonneg_of_nine_nine_legendre_schur
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (he : Function.Even e) (ho : Function.Odd o)
    (helocal : LocallyLipschitzOn (Icc (-1) 1) e)
    (holocal : LocallyLipschitzOn (Icc (-1) 1) o)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hLow : 0 ≤ factorTwoEndpointChannelPhase
      (centeredLegendreLowProjection e hec 9)
      (centeredLegendreLowProjection o hoc 9) a b)
    (hSchur : factorTwoEndpointLowTailMixed
        (centeredLegendreLowProjection e hec 9)
        (centeredLegendreHigherResidual e hec 9)
        (centeredLegendreLowProjection o hoc 9)
        (centeredLegendreHigherResidual o hoc 9) a b ^ 2 ≤
      factorTwoEndpointChannelPhase
          (centeredLegendreLowProjection e hec 9)
          (centeredLegendreLowProjection o hoc 9) a b *
        factorTwoEndpointChannelPhase
          (centeredLegendreHigherResidual e hec 9)
          (centeredLegendreHigherResidual o hoc 9) a b) :
    0 ≤ factorTwoEndpointChannelPhase e o a b := by
  have hquant :=
    factorTwoEndpointChannelPhase_nine_nine_higherResidual_quantitative
      e o hec hoc he ho helocal holocal a b hab
  have htail : 0 ≤ factorTwoEndpointChannelPhase
      (centeredLegendreHigherResidual e hec 9)
      (centeredLegendreHigherResidual o hoc 9) a b := by
    have heEnergy := factorTwoIntrinsicEnergy_nonneg
      (centeredLegendreHigherResidual e hec 9)
    have hoEnergy := factorTwoIntrinsicEnergy_nonneg
      (centeredLegendreHigherResidual o hoc 9)
    have hoPotential := factorTwoIntrinsicPotentialEnergy_nonneg
      (centeredLegendreHigherResidual o hoc 9)
    exact (by positivity : 0 ≤
      (1 / 250 : ℝ) * factorTwoIntrinsicEnergy
          (centeredLegendreHigherResidual e hec 9) +
        (1 / 2500 : ℝ) * factorTwoIntrinsicEnergy
          (centeredLegendreHigherResidual o hoc 9) +
        (1 / 2 : ℝ) * factorTwoIntrinsicPotentialEnergy
          (centeredLegendreHigherResidual o hoc 9)).trans hquant
  have hfull := factorTwoEndpointChannelPhase_nonneg_of_low_tail_schur
    (centeredLegendreLowProjection e hec 9)
    (centeredLegendreHigherResidual e hec 9)
    (centeredLegendreLowProjection o hoc 9)
    (centeredLegendreHigherResidual o hoc 9)
    (continuous_centeredLegendreLowProjection e hec 9)
    (continuous_centeredLegendreHigherResidual e hec 9)
    (continuous_centeredLegendreLowProjection o hoc 9)
    (continuous_centeredLegendreHigherResidual o hoc 9)
    a b hLow htail hSchur
  simpa only [centeredLegendreLowProjection_add_higherResidual] using hfull

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseHigherLegendreNineNineQuantitativeStructural
