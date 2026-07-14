import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseHigherLegendreDecomposition

set_option autoImplicit false

open MeasureTheory Polynomial Real Set
open scoped unitInterval

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseHigherLegendreStructuralPositive

open ShiftedLegendreL2Basis
open ShiftedLegendreOrthogonality
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine
open YoshidaEndpointEvenStructuralReduction
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseHigherLegendreDecomposition
open YoshidaFactorTwoPhaseIntrinsicHigherResidual

noncomputable section

/-!
# Structural positivity of the canonical higher Legendre residual

The cutoff-nine/cutoff-ten residuals already carry the complete harmonic
moment gaps used by the infinite-dimensional phase estimate.  This module
discharges the remaining mean-zero premise directly from the degree-zero
moment, so the pure higher block is unconditional on the canonical split.
-/

/-- A nonempty shifted-Legendre moment gap includes the centered mean-zero
condition required by the projected phase estimate. -/
theorem centeredEvenP0Coefficient_eq_zero_of_momentsVanishBelow
    (w : ℝ → ℝ) {k : ℕ} (hk : 0 < k)
    (hlow : centeredLegendreMomentsVanishBelow w k) :
    centeredEvenP0Coefficient w = 0 := by
  have hzero := hlow 0 hk
  have hunit : (∫ t : unitInterval, centeredPullback w (t : ℝ)) = 0 := by
    simpa [shiftedLegendreReal, Polynomial.shiftedLegendre] using hzero
  have hinterval : (∫ x : ℝ in -1..1, w x) = 0 := by
    have hbridge :
        (∫ t : unitInterval, centeredPullback w (t : ℝ)) =
          (1 / 2 : ℝ) * ∫ x : ℝ in -1..1, w x := by
      calc
        _ = ∫ t : ℝ in 0..1, centeredPullback w t :=
          integral_unitInterval_eq_intervalIntegral (centeredPullback w)
        _ = (1 / 2 : ℝ) * ∫ x : ℝ in -1..1, w x :=
          integral_comp_two_mul_sub_one w
    rw [hunit] at hbridge
    linarith
  unfold centeredEvenP0Coefficient
  rw [hinterval, mul_zero]

/-- The complete phase is nonnegative on the canonical infinite block above
even degree eight and odd degree nine.  No retained mode or phase point is
enumerated. -/
theorem factorTwoEndpointChannelPhase_nine_ten_higherResidual_nonneg
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (he : Function.Even e) (ho : Function.Odd o)
    (helocal : LocallyLipschitzOn (Icc (-1) 1) e)
    (holocal : LocallyLipschitzOn (Icc (-1) 1) o)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    0 ≤ factorTwoEndpointChannelPhase
      (centeredLegendreHigherResidual e hec 9)
      (centeredLegendreHigherResidual o hoc 10) a b := by
  let eH := centeredLegendreHigherResidual e hec 9
  let oH := centeredLegendreHigherResidual o hoc 10
  have hgap := nine_ten_higherResidual_moment_gaps e o hec hoc
  apply factorTwoEndpointChannelPhase_nonneg_of_higher_residual
    eH oH
    (continuous_centeredLegendreHigherResidual e hec 9)
    (continuous_centeredLegendreHigherResidual o hoc 10)
    (centeredLegendreHigherResidual_even e hec he 9)
    (centeredLegendreHigherResidual_odd o hoc ho 10)
    (centeredEvenP0Coefficient_eq_zero_of_momentsVanishBelow
      eH (by norm_num) hgap.1)
    (locallyLipschitzOn_centeredLegendreHigherResidual e hec helocal 9)
    (locallyLipschitzOn_centeredLegendreHigherResidual o hoc holocal 10)
    hgap.1 hgap.2 a b hab

/-- Once the canonical finite block and its exact mixed determinant are
controlled, the structural higher-residual theorem closes the full profile.
This statement exposes only the two genuine low-side obligations. -/
theorem factorTwoEndpointChannelPhase_nonneg_of_nine_ten_legendre_schur
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (he : Function.Even e) (ho : Function.Odd o)
    (helocal : LocallyLipschitzOn (Icc (-1) 1) e)
    (holocal : LocallyLipschitzOn (Icc (-1) 1) o)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hLow : 0 ≤ factorTwoEndpointChannelPhase
      (centeredLegendreLowProjection e hec 9)
      (centeredLegendreLowProjection o hoc 10) a b)
    (hSchur : factorTwoEndpointLowTailMixed
        (centeredLegendreLowProjection e hec 9)
        (centeredLegendreHigherResidual e hec 9)
        (centeredLegendreLowProjection o hoc 10)
        (centeredLegendreHigherResidual o hoc 10) a b ^ 2 ≤
      factorTwoEndpointChannelPhase
          (centeredLegendreLowProjection e hec 9)
          (centeredLegendreLowProjection o hoc 10) a b *
        factorTwoEndpointChannelPhase
          (centeredLegendreHigherResidual e hec 9)
          (centeredLegendreHigherResidual o hoc 10) a b) :
    0 ≤ factorTwoEndpointChannelPhase e o a b := by
  have h := factorTwoEndpointChannelPhase_nonneg_of_low_tail_schur
    (centeredLegendreLowProjection e hec 9)
    (centeredLegendreHigherResidual e hec 9)
    (centeredLegendreLowProjection o hoc 10)
    (centeredLegendreHigherResidual o hoc 10)
    (continuous_centeredLegendreLowProjection e hec 9)
    (continuous_centeredLegendreHigherResidual e hec 9)
    (continuous_centeredLegendreLowProjection o hoc 10)
    (continuous_centeredLegendreHigherResidual o hoc 10)
    a b hLow
    (factorTwoEndpointChannelPhase_nine_ten_higherResidual_nonneg
      e o hec hoc he ho helocal holocal a b hab)
    hSchur
  simpa only [centeredLegendreLowProjection_add_higherResidual] using h

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseHigherLegendreStructuralPositive
