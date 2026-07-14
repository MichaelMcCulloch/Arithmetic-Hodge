import ArithmeticHodge.Analysis.YoshidaEndpointEvenMeanZeroLocallyLipschitz
import ArithmeticHodge.Analysis.YoshidaEndpointOddCleanLipschitz
import ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointChannelRadius

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseStructuralReserve

noncomputable section

open UnitIntervalLogEnergyProjection
open YoshidaEndpointEvenMeanZeroLocallyLipschitz
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointOddCleanLipschitz
open YoshidaFactorTwoEndpointChannelRadius

/-!
# Structural clean reserve for an opposite-parity phase channel

The even zero-two residual and the complete odd profile carry different exact
coercive reserves.  Keeping those coefficients separate is the useful form
for a subsequent weighted low--tail Schur estimate.
-/

/-- A zero-`P₀/P₂` even profile paired with an arbitrary odd profile retains
`41/60` of the even energy and `1/100` of the odd energy in the clean channel. -/
theorem endpointChannelCleanSum_structural_reserve
    (e o : ℝ → ℝ)
    (hec : Continuous e) (hoc : Continuous o)
    (heven : Function.Even e) (hodd : Function.Odd o)
    (heZero : centeredEvenP0Coefficient e = 0)
    (heTwo : centeredEvenP2Coefficient e = 0)
    (heLocal : LocallyLipschitzOn (Icc (-1) 1) e)
    (hoLocal : LocallyLipschitzOn (Icc (-1) 1) o) :
    (41 / 60 : ℝ) * (∫ x : ℝ in -1..1, e x ^ 2) +
        (1 / 100 : ℝ) * (∫ x : ℝ in -1..1, o x ^ 2) ≤
      factorTwoEndpointChannelCleanSum e o := by
  have heReserve :=
    yoshidaEndpointOddCleanQuadratic_reserve_of_even_of_mean_zero_of_locallyLipschitzOn
      e hec heven heZero heLocal
  have heResidual : centeredEvenZeroTwoResidual e = e := by
    funext x
    unfold centeredEvenZeroTwoResidual
    rw [heZero, heTwo]
    ring
  rw [heResidual, heTwo] at heReserve
  norm_num at heReserve
  have hoReserve :=
    one_hundredth_energy_le_yoshidaEndpointOddCleanQuadratic_of_locallyLipschitzOn
      o hoc hodd hoLocal
  unfold factorTwoEndpointChannelCleanSum
  linarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseStructuralReserve
