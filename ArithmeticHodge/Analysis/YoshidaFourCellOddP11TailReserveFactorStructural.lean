import ArithmeticHodge.Analysis.YoshidaFourCellOddP11TailReserveThreeHalvesStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11TailReserveFactorStructural

noncomputable section

open CenteredEndpointCorrelation
open CenteredOddOneThreeEnergy
open UnitIntervalLogEnergyAffine
open YoshidaConstantBounds
open YoshidaEndpointPotentialBound
open YoshidaEndpointOcticPotential
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFourCellOddEndpointStripCoercivityStructural
open YoshidaFourCellOddP11TailReserveThreeHalvesStructural
open YoshidaFourCellOddP11ThreeHalvesClosureStructural
open YoshidaFourCellOddP1OrthogonalFormDualClosureStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaFourCellRawParityFoldStructural
open YoshidaRegularKernelBound

/-!
# The structural `3/2` tail-reserve obstruction

This file does not replace the genuine `P₁₁+` tail by a finite mode list.
Instead it folds the exact core and exact scalar weight against the global
harmonic-eleven gap.  The result is an exact endpoint-concentration
condition equivalent to the proposed factor `3/2` reserve, followed by a
slightly stronger rational certificate that absorbs the regular row.

Thus the remaining analytic work is explicit: it must compare the unused
global raw excess with the endpoint-strip raw energy and the adverse
potential/lower/weighted-upper masses.  The harmonic gap alone, after its
raw excess is discarded, does not establish the requested reserve.
-/

/-- After inserting the harmonic-eleven global reserve, this is exactly the
difference between the complete odd core and `3/2` times its exact scalar
tail weight.  The first line is the unused global harmonic excess. -/
def fourCellOddP11ThreeHalvesConcentrationGap (r : ℝ → ℝ) : ℝ :=
  centeredRawLogEnergy r / 4 -
      (harmonic 11 : ℝ) * factorTwoIntrinsicEnergy r +
    (2 * (harmonic 11 : ℝ) -
        (2 * (Real.log (2 * fourCellOperatorHalfWidth) +
          Real.eulerMascheroniConstant + Real.log Real.pi) + 3 / 200)) *
      (∫ x : ℝ in 0..1, r x ^ 2) +
    Real.sqrt 2 * Real.log 2 * fourCellOddEndpointStripEvenMass r +
    (2 - Real.sqrt 2 * Real.log 2) *
      fourCellOddEndpointStripOddMass r +
    (171 / 50 : ℝ) * (∫ x : ℝ in 3 / 5..1, r x ^ 2) -
    ((1 / 2 : ℝ) * fourCellOddEndpointStripOddRawEnergy r +
      (93 / 100 : ℝ) *
        (∫ x : ℝ in 0..1, yoshidaEndpointPotential x * r x ^ 2) +
      (81 / 500 : ℝ) * (∫ x : ℝ in 0..3 / 5, r x ^ 2) +
      (9 / 5 : ℝ) * (∫ x : ℝ in 3 / 5..1, r x ^ 2 / x)) -
    2 * fourCellOperatorHalfWidth *
      (∫ t : ℝ in 0..2,
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          centeredEndpointCorrelation r t)

/-- Exact core/weight identity on every regular odd profile.  The equality
uses only parity folding and the definitions; there is no spectral cutoff or
inequality in this step. -/
theorem core_sub_threeHalves_weight_eq_concentrationGap
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r) :
    fourCellOddCoreLocalQuadratic r -
        (3 / 2 : ℝ) * fourCellOddP1ExactTailWeight r =
      fourCellOddP11ThreeHalvesConcentrationGap r := by
  have hraw := centeredRawLogEnergy_div_four_eq_positiveHalf_odd
    r (hr.contDiffOn.locallyLipschitzOn (convex_Icc (-1 : ℝ) 1)) hodd
  have hmass := integral_sq_eq_two_mul_positiveHalf
    r hr.continuous (Or.inr hodd)
  unfold fourCellOddCoreLocalQuadratic
  rw [fourCellOddHalfCoreReserve_add_localWidthDefect_eq_raw_add_reduced]
  unfold fourCellOddP11ThreeHalvesConcentrationGap
    fourCellOddP1ExactTailWeight fourCellOddRawStripCancellationReserve
    fourCellOddStripReducedRemainder factorTwoIntrinsicEnergy
  rw [hraw, hmass]
  ring

/-- The named endpoint-concentration statement for all genuine `P₁₁+`
tails.  By the next theorem this is not a surrogate: it is exactly the
factor-`3/2` reserve in harmonic-gap normal form. -/
def FourCellOddP11ThreeHalvesEndpointConcentration : Prop :=
  ∀ (r : ℝ → ℝ),
    ContDiff ℝ 1 r → Function.Odd r →
    centeredOddP1Coefficient r = 0 →
    centeredOddP3Coefficient r = 0 →
    centeredOddP5Coefficient r = 0 →
    centeredOddP7Coefficient r = 0 →
    centeredOddP9Coefficient r = 0 →
    0 ≤ fourCellOddP11ThreeHalvesConcentrationGap r

/-- The exact structural reduction: the proposed `3/2` reserve is equivalent
to one endpoint-concentration inequality on the infinite `P₁₁+` tail. -/
theorem tailReserveAtFactor_threeHalves_iff_endpointConcentration :
    FourCellOddP11TailReserveAtFactor (3 / 2 : ℝ) ↔
      FourCellOddP11ThreeHalvesEndpointConcentration := by
  constructor
  · intro hreserve r hr hodd h1 h3 h5 h7 h9
    have h := hreserve r hr hodd h1 h3 h5 h7 h9
    have hid := core_sub_threeHalves_weight_eq_concentrationGap r hr hodd
    linarith
  · intro hconcentration r hr hodd h1 h3 h5 h7 h9
    have h := hconcentration r hr hodd h1 h3 h5 h7 h9
    have hid := core_sub_threeHalves_weight_eq_concentrationGap r hr hodd
    linarith

/-- The genuinely infinite-dimensional harmonic input makes the first line
of the concentration gap nonnegative on every `P₁₁+` tail. -/
theorem harmonicElevenExcess_nonneg_of_P11Plus
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (h1 : centeredOddP1Coefficient r = 0)
    (h3 : centeredOddP3Coefficient r = 0)
    (h5 : centeredOddP5Coefficient r = 0)
    (h7 : centeredOddP7Coefficient r = 0)
    (h9 : centeredOddP9Coefficient r = 0) :
    0 ≤ centeredRawLogEnergy r / 4 -
      (harmonic 11 : ℝ) * factorTwoIntrinsicEnergy r := by
  have hgap := harmonic_eleven_mul_intrinsicEnergy_le_raw_div_four_of_P11Plus
    r hr hodd h1 h3 h5 h7 h9
  linarith

/-! ## A concrete rational concentration certificate -/

/-- After paying the shared scalar and the worst possible regular-row charge,
the harmonic-eleven mass coefficient leaves this exact positive reserve. -/
def fourCellOddP11ThreeHalvesHalfMassReserve : ℝ :=
  38536409 / 13860000

theorem fourCellOddP11ThreeHalvesHalfMassReserve_eq :
    fourCellOddP11ThreeHalvesHalfMassReserve =
      2 * (harmonic 11 : ℝ) - 65187 / 20000 := by
  norm_num [fourCellOddP11ThreeHalvesHalfMassReserve, harmonic,
    Finset.sum_range_succ]

theorem fourCellOddP11ThreeHalvesHalfMassReserve_pos :
    0 < fourCellOddP11ThreeHalvesHalfMassReserve := by
  norm_num [fourCellOddP11ThreeHalvesHalfMassReserve]

/-- A slightly stronger, regular-row-free concentration budget.  Its raw
term is the *unused* harmonic-eleven excess, so this is still a structural
infinite-tail condition rather than a scalar mass estimate or a finite mode
calculation. -/
def fourCellOddP11ThreeHalvesRationalConcentrationBudget
    (r : ℝ → ℝ) : ℝ :=
  centeredRawLogEnergy r / 4 -
      (harmonic 11 : ℝ) * factorTwoIntrinsicEnergy r +
    fourCellOddP11ThreeHalvesHalfMassReserve *
      (∫ x : ℝ in 0..1, r x ^ 2) +
    Real.sqrt 2 * Real.log 2 * fourCellOddEndpointStripEvenMass r +
    (2 - Real.sqrt 2 * Real.log 2) *
      fourCellOddEndpointStripOddMass r +
    (171 / 50 : ℝ) * (∫ x : ℝ in 3 / 5..1, r x ^ 2) -
    ((1 / 2 : ℝ) * fourCellOddEndpointStripOddRawEnergy r +
      (93 / 100 : ℝ) *
        (∫ x : ℝ in 0..1, yoshidaEndpointPotential x * r x ^ 2) +
      (81 / 500 : ℝ) * (∫ x : ℝ in 0..3 / 5, r x ^ 2) +
      (9 / 5 : ℝ) * (∫ x : ℝ in 3 / 5..1, r x ^ 2 / x))

/-- The exact regular correlation and the shared transcendental scalar cost
at most `65187/20000` copies of positive-half mass.  This public proof is
included here because the older bound with the same constant is local to its
source module. -/
theorem fourCellOddP11_scalar_add_regularCharge_le
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r) :
    (2 * (Real.log (2 * fourCellOperatorHalfWidth) +
          Real.eulerMascheroniConstant + Real.log Real.pi) + 3 / 200) *
          (∫ x : ℝ in 0..1, r x ^ 2) +
        2 * fourCellOperatorHalfWidth *
          (∫ t : ℝ in 0..2,
            yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
              centeredEndpointCorrelation r t) ≤
      (65187 / 20000 : ℝ) * (∫ x : ℝ in 0..1, r x ^ 2) := by
  let H : ℝ := ∫ x : ℝ in 0..1, r x ^ 2
  let R : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      centeredEndpointCorrelation r t
  let C : ℝ := 2 * (Real.log (2 * fourCellOperatorHalfWidth) +
      Real.eulerMascheroniConstant + Real.log Real.pi) + 3 / 200
  have hmass := integral_sq_eq_two_mul_positiveHalf
    r hr.continuous (Or.inr hodd)
  have hRabs : |R| ≤ (1 / 20 : ℝ) * (2 * H) := by
    have h := abs_fourCellRegularCorrelation_le_one_twentieth_centeredMass
      r hr.continuous hodd
    simpa only [R, H, hmass] using h
  have hwidth0 : 0 ≤ 2 * fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have hRle : R ≤ (1 / 20 : ℝ) * (2 * H) :=
    (le_abs_self R).trans hRabs
  have hregular :
      2 * fourCellOperatorHalfWidth * R ≤
        fourCellOperatorHalfWidth / 5 * H := by
    calc
      2 * fourCellOperatorHalfWidth * R ≤
          2 * fourCellOperatorHalfWidth * ((1 / 20 : ℝ) * (2 * H)) :=
        mul_le_mul_of_nonneg_left hRle hwidth0
      _ = fourCellOperatorHalfWidth / 5 * H := by ring
  have hH0 : 0 ≤ H := by
    dsimp only [H]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg _)
  have hscalar := fourCellScalar_fine_bounds.2
  have hlog := strict_log_two_bounds.2
  have hwidth :
      fourCellOperatorHalfWidth / 5 ≤ (1733 / 20000 : ℝ) := by
    unfold fourCellOperatorHalfWidth
    nlinarith
  have hcoefficient :
      C + fourCellOperatorHalfWidth / 5 ≤ (65187 / 20000 : ℝ) := by
    dsimp only [C]
    nlinarith [hscalar, hwidth]
  have hbudget :
      C * H + fourCellOperatorHalfWidth / 5 * H ≤
        (65187 / 20000 : ℝ) * H := by
    calc
      C * H + fourCellOperatorHalfWidth / 5 * H =
          (C + fourCellOperatorHalfWidth / 5) * H := by ring
      _ ≤ (65187 / 20000 : ℝ) * H :=
        mul_le_mul_of_nonneg_right hcoefficient hH0
  dsimp only [C, H, R] at hregular hbudget ⊢
  linarith

/-- The rational budget is bounded above by the exact concentration gap.
The sole loss is the certified worst-case scalar/regular charge. -/
theorem rationalConcentrationBudget_le_concentrationGap
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r) :
    fourCellOddP11ThreeHalvesRationalConcentrationBudget r ≤
      fourCellOddP11ThreeHalvesConcentrationGap r := by
  have hcharge := fourCellOddP11_scalar_add_regularCharge_le r hr hodd
  unfold fourCellOddP11ThreeHalvesRationalConcentrationBudget
    fourCellOddP11ThreeHalvesConcentrationGap
  rw [fourCellOddP11ThreeHalvesHalfMassReserve_eq]
  ring_nf at hcharge ⊢
  linarith

/-- The one concrete structural premise still sufficient for the factor
`3/2` theorem.  It retains the harmonic raw excess and requires no mode
enumeration. -/
def FourCellOddP11ThreeHalvesRationalConcentration : Prop :=
  ∀ (r : ℝ → ℝ),
    ContDiff ℝ 1 r → Function.Odd r →
    centeredOddP1Coefficient r = 0 →
    centeredOddP3Coefficient r = 0 →
    centeredOddP5Coefficient r = 0 →
    centeredOddP7Coefficient r = 0 →
    centeredOddP9Coefficient r = 0 →
    0 ≤ fourCellOddP11ThreeHalvesRationalConcentrationBudget r

theorem tailReserveAtFactor_threeHalves_of_rationalConcentration
    (hconcentration : FourCellOddP11ThreeHalvesRationalConcentration) :
    FourCellOddP11TailReserveAtFactor (3 / 2 : ℝ) := by
  rw [tailReserveAtFactor_threeHalves_iff_endpointConcentration]
  intro r hr hodd h1 h3 h5 h7 h9
  exact (hconcentration r hr hodd h1 h3 h5 h7 h9).trans
    (rationalConcentrationBudget_le_concentrationGap r hr hodd)

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11TailReserveFactorStructural
