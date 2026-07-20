import ArithmeticHodge.Analysis.YoshidaFourCellOddP11TailConcentrationClosureStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11TailHardySpectralStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointPotentialBound
open YoshidaFourCellOddP11TailConcentrationClosureStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellParityHalfFoldStructural

/-!
# A global spectral probe for the proposed odd tail Hardy inequality

The remaining Hardy residual was stated with the endpoint potential only on
`[3/5,1]`.  For an odd profile the potential on `[0,1]` is one half of the
global even potential, whose matrix is already available in exact centered
Legendre coordinates.  On `[0,3/5]` the potential is at most `1/4`.

Consequently a negative value of the quadratic form below is an exact
counterexample to `FourCellOddP11TailHardyConcentration`.  This bridge is
useful for adversarial work because it replaces the truncated singular
integral by a global spectral form; it introduces no finite-mode assumption.
-/

/-- Legendre-friendly upper majorant of the retained Hardy residual.  The
lower-mass coefficient is `73077/20000 - (93/100)(1/4) = 68427/20000`.
The global potential has coefficient `93/200` because odd parity folds it
into twice its positive-half value. -/
def fourCellOddP11GlobalHardyProbe (r : ℝ → ℝ) : ℝ :=
  fourCellOddRawStripCancellationReserve r -
    (68427 / 20000 : ℝ) * (∫ x : ℝ in 0..3 / 5, r x ^ 2) -
    (6 / 5 : ℝ) * (∫ x : ℝ in 3 / 5..1, r x ^ 2 / x) +
    (2813 / 20000 : ℝ) * (∫ x : ℝ in 3 / 5..1, r x ^ 2) -
    (93 / 200 : ℝ) *
      (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * r x ^ 2)

/-- The actual upper-strip potential is bounded below by the global odd
potential minus the certified lower-strip loss. -/
theorem globalPotential_sub_quarterLowerMass_le_upperPotential
    (r : ℝ → ℝ) (hr : Continuous r) (hodd : Function.Odd r) :
    (1 / 2 : ℝ) *
          (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * r x ^ 2) -
        (1 / 4 : ℝ) * (∫ x : ℝ in 0..3 / 5, r x ^ 2) ≤
      ∫ x : ℝ in 3 / 5..1,
        yoshidaEndpointPotential x * r x ^ 2 := by
  have hfold := endpointPotential_eq_two_mul_positiveHalf r hr (Or.inr hodd)
  have hsplit := positiveHalfPotential_eq_lower_add_upper r hr
  have hlower := lowerPotential_le_oneQuarter_lowerMass r hr
  linarith

/-- The global spectral probe really is an upper bound for the proposed
Hardy residual.  Thus negativity of the probe is stronger than negativity
of the original residual. -/
theorem tailHardyResidual_le_globalHardyProbe
    (r : ℝ → ℝ) (hr : Continuous r) (hodd : Function.Odd r) :
    fourCellOddP11TailHardyResidual r ≤
      fourCellOddP11GlobalHardyProbe r := by
  have hpotential :=
    globalPotential_sub_quarterLowerMass_le_upperPotential r hr hodd
  unfold fourCellOddP11TailHardyResidual
    fourCellOddP11RetainedHardySurplus
    fourCellOddP11GlobalHardyProbe
  linarith

/-- A single genuine `P₁₁+` profile with negative global probe refutes
the remaining Hardy premise.  This is the exact adversarial target for a
structural Legendre or endpoint-concentration construction. -/
theorem not_tailHardyConcentration_of_globalProbe_neg
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (h1 : centeredOddP1Coefficient r = 0)
    (h3 : centeredOddP3Coefficient r = 0)
    (h5 : centeredOddP5Coefficient r = 0)
    (h7 : centeredOddP7Coefficient r = 0)
    (h9 : centeredOddP9Coefficient r = 0)
    (hneg : fourCellOddP11GlobalHardyProbe r < 0) :
    ¬ FourCellOddP11TailHardyConcentration := by
  intro hHardy
  have hresidual := hHardy r hr hodd h1 h3 h5 h7 h9
  have hprobe := tailHardyResidual_le_globalHardyProbe r hr.continuous hodd
  linarith

/-- Conversely, the proposed universal Hardy statement forces the global
probe to be nonnegative on every profile in the exact `P₁₁+` sector.
This convenient contrapositive-free form lets a spectral calculation target
one named scalar. -/
theorem globalHardyProbe_nonneg_of_tailHardyConcentration
    (hHardy : FourCellOddP11TailHardyConcentration)
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (h1 : centeredOddP1Coefficient r = 0)
    (h3 : centeredOddP3Coefficient r = 0)
    (h5 : centeredOddP5Coefficient r = 0)
    (h7 : centeredOddP7Coefficient r = 0)
    (h9 : centeredOddP9Coefficient r = 0) :
    0 ≤ fourCellOddP11GlobalHardyProbe r := by
  have hresidual := hHardy r hr hodd h1 h3 h5 h7 h9
  exact hresidual.trans
    (tailHardyResidual_le_globalHardyProbe r hr.continuous hodd)

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11TailHardySpectralStructural
