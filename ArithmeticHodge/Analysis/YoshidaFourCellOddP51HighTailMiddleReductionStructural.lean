import ArithmeticHodge.Analysis.YoshidaFourCellOddP51HighTailGalerkinRieszStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP51HighTailRawGapStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddCoreIntegratedRegularAbsorptionStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP51HighTailMiddleReductionStructural

noncomputable section

open CenteredOddOneThreeEnergy
open UnitIntervalLogEnergyAffine
open YoshidaFourCellOddCoreIntegratedRegularAbsorptionStructural
open YoshidaFourCellOddCoreNineteenTwentiethsCoercivityStructural
open YoshidaFourCellOddFiniteLegendreSolveStructural
open YoshidaFourCellOddP11CorrectedDeterminantAuditStructural
open YoshidaFourCellOddP11CoupledRieszClosureStructural
open YoshidaFourCellOddP51GalerkinRieszStructural
open YoshidaFourCellOddP51HighTailGalerkinRieszStructural
open YoshidaFourCellOddP51HighTailRawGapStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# Reduction of the `P51` high-tail middle coercivity

The `P53+` raw gap supplies eight positive-half masses.  Therefore retaining
only one sixty-fourth of that raw reserve is enough for the desired `1/8`
middle constant.  The already proved nineteen-twentieths raw-strip
absorption pays the complete signed regular correlation.  What remains is
one explicit surplus inequality involving only

* nineteen twentieths of the raw-strip cancellation reserve,
* the retained prime/potential diagonal,
* the scalar mass row, and
* one sixty-fourth of the `P53+` raw reserve.

This file proves that exact reduction.  It does not assume or rename the
middle-coercivity target itself.
-/

private theorem odd_const_mul
    {v : ℝ → ℝ} (hv : Function.Odd v) (t : ℝ) :
    Function.Odd (fun x ↦ t * v x) := by
  intro x
  change t * v (-x) = -(t * v x)
  rw [hv]
  ring

/-- An arbitrary retained `P3,...,P51` vector plus a scaled genuine tail. -/
def fourCellOddP51HighTailMiddleProfile
    (a : FourCellOddP51RetainedIndex → ℝ) (t : ℝ) (r : ℝ → ℝ) :
    ℝ → ℝ :=
  fourCellOddP51RetainedProfile a + fun x ↦ t * r x

theorem contDiff_fourCellOddP51HighTailMiddleProfile
    (a : FourCellOddP51RetainedIndex → ℝ) (t : ℝ) (r : ℝ → ℝ)
    (hr : ContDiff ℝ 1 r) :
    ContDiff ℝ 1 (fourCellOddP51HighTailMiddleProfile a t r) := by
  unfold fourCellOddP51HighTailMiddleProfile fourCellOddP51RetainedProfile
  exact (contDiff_fourCellOddFiniteRetainedProfile 24 a).add
    (contDiff_const.mul hr)

theorem odd_fourCellOddP51HighTailMiddleProfile
    (a : FourCellOddP51RetainedIndex → ℝ) (t : ℝ) (r : ℝ → ℝ)
    (hodd : Function.Odd r) :
    Function.Odd (fourCellOddP51HighTailMiddleProfile a t r) := by
  unfold fourCellOddP51HighTailMiddleProfile fourCellOddP51RetainedProfile
  exact (odd_fourCellOddFiniteRetainedProfile 24 a).add
    (odd_const_mul hodd t)

/-! ## The single remaining raw-strip surplus -/

/-- After the signed regular row has been paid, this is the exact surplus
whose nonnegativity retains one sixty-fourth of the `P53+` raw gap. -/
def fourCellOddP51OneEighthRawStripSurplus
    (a : FourCellOddP51RetainedIndex → ℝ) (t : ℝ) (r : ℝ → ℝ) :
    ℝ :=
  let w := fourCellOddP51HighTailMiddleProfile a t r
  (19 / 20 : ℝ) * fourCellOddRawStripCancellationReserve w +
      fourCellOddRetainedPrimePotentialQuadratic w -
    (fourCellOddLocalScalarMassCoefficient *
        (∫ x : ℝ in 0..1, w x ^ 2) +
      t ^ 2 * (centeredRawLogEnergy r / 256))

/-- The sole analytic inequality left by the `1/8` high-tail reduction. -/
def FourCellOddP51OneEighthRawStripSurplusNonnegative : Prop :=
  ∀ (a : FourCellOddP51RetainedIndex → ℝ) (t : ℝ) (r : ℝ → ℝ),
    ContDiff ℝ 1 r → Function.Odd r →
    FourCellOddP53PlusMomentConditions r →
      0 ≤ fourCellOddP51OneEighthRawStripSurplus a t r

/-- Exact bookkeeping identity: the displayed surplus is precisely the
nineteen-twentieths retained quadratic after reserving one sixty-fourth of
the tail raw gap. -/
theorem fourCellOddNineteenTwentiethsRetainedQuadratic_sub_scaledRaw_eq_surplus
    (a : FourCellOddP51RetainedIndex → ℝ) (t : ℝ) (r : ℝ → ℝ) :
    fourCellOddNineteenTwentiethsRetainedQuadratic
        (fourCellOddP51HighTailMiddleProfile a t r) -
      t ^ 2 * (centeredRawLogEnergy r / 256) =
        fourCellOddP51OneEighthRawStripSurplus a t r := by
  unfold fourCellOddP51OneEighthRawStripSurplus
    fourCellOddNineteenTwentiethsRetainedQuadratic
  dsimp only
  ring

/-- The retained block by itself already has nonnegative surplus.  Thus the
new analytic content is confined to the nonzero high-tail scale and its
mixed raw-strip rows. -/
theorem fourCellOddP51OneEighthRawStripSurplus_zero_scale_nonneg
    (a : FourCellOddP51RetainedIndex → ℝ) (r : ℝ → ℝ) :
    0 ≤ fourCellOddP51OneEighthRawStripSurplus a 0 r := by
  let u := fourCellOddP51RetainedProfile a
  have hu : ContDiff ℝ 1 u := by
    dsimp only [u, fourCellOddP51RetainedProfile]
    exact contDiff_fourCellOddFiniteRetainedProfile 24 a
  have huodd : Function.Odd u := by
    dsimp only [u, fourCellOddP51RetainedProfile]
    exact odd_fourCellOddFiniteRetainedProfile 24 a
  have hu1 : centeredOddP1Coefficient u = 0 := by
    dsimp only [u, fourCellOddP51RetainedProfile]
    exact centeredOddP1Coefficient_fourCellOddFiniteRetainedProfile_eq_zero
      24 a
  have hcoercive :=
    coercivityConstant_mul_positiveHalfMass_le_retainedQuadratic_of_P1
      u hu huodd hu1
  have hmass : 0 ≤ ∫ x : ℝ in 0..1, u x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg (u x))
  have hbase : 0 ≤
      fourCellOddNineteenTwentiethsCoercivityConstant *
        (∫ x : ℝ in 0..1, u x ^ 2) :=
    mul_nonneg fourCellOddNineteenTwentiethsCoercivityConstant_pos.le hmass
  have hretained :
      0 ≤ fourCellOddNineteenTwentiethsRetainedQuadratic u :=
    hbase.trans hcoercive
  have hprofile : fourCellOddP51HighTailMiddleProfile a 0 r = u := by
    funext x
    unfold fourCellOddP51HighTailMiddleProfile
    dsimp only [u]
    simp only [Pi.add_apply, zero_mul, add_zero]
  rw [←
    fourCellOddNineteenTwentiethsRetainedQuadratic_sub_scaledRaw_eq_surplus
      a 0 r, hprofile]
  norm_num
  exact hretained

/-- One sixty-fourth of the P53 raw reserve dominates one eighth of the
scaled positive-half tail mass. -/
theorem oneEighth_scaledTailMass_le_oneSixtyFourth_scaledRawGap
    (t : ℝ) (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r)
    (hodd : Function.Odd r) (htail : FourCellOddP53PlusMomentConditions r) :
    t ^ 2 * ((1 / 8 : ℝ) * (∫ x : ℝ in 0..1, r x ^ 2)) ≤
      t ^ 2 * (centeredRawLogEnergy r / 256) := by
  have hraw := eight_mul_positiveHalfMass_le_raw_div_four_of_P53Plus
    r hr hodd htail
  have hscaled := mul_le_mul_of_nonneg_left hraw (sq_nonneg t)
  calc
    t ^ 2 * ((1 / 8 : ℝ) * (∫ x : ℝ in 0..1, r x ^ 2)) =
        (1 / 64 : ℝ) *
          (t ^ 2 * (8 * (∫ x : ℝ in 0..1, r x ^ 2))) := by ring
    _ ≤ (1 / 64 : ℝ) *
        (t ^ 2 * (centeredRawLogEnergy r / 4)) :=
      mul_le_mul_of_nonneg_left hscaled (by norm_num)
    _ = t ^ 2 * (centeredRawLogEnergy r / 256) := by ring

/-- The single raw-strip surplus inequality proves genuine `P53+` middle
coercivity with constant `1/8`.  The regular correlation is absent from the
remaining premise because it was already absorbed structurally. -/
theorem fourCellOddP51P53PlusMiddleCoerciveAt_oneEighth_of_rawStripSurplus
    (hsurplus : FourCellOddP51OneEighthRawStripSurplusNonnegative) :
    FourCellOddP51P53PlusMiddleCoerciveAt (1 / 8) := by
  intro a t r hr hodd htail
  let w := fourCellOddP51HighTailMiddleProfile a t r
  have hw : ContDiff ℝ 1 w := by
    dsimp only [w]
    exact contDiff_fourCellOddP51HighTailMiddleProfile a t r hr
  have hwodd : Function.Odd w := by
    dsimp only [w]
    exact odd_fourCellOddP51HighTailMiddleProfile a t r hodd
  have hraw := oneEighth_scaledTailMass_le_oneSixtyFourth_scaledRawGap
    t r hr hodd htail
  have hs := hsurplus a t r hr hodd htail
  have hid :=
    fourCellOddNineteenTwentiethsRetainedQuadratic_sub_scaledRaw_eq_surplus
      a t r
  have hrawRetained :
      t ^ 2 * (centeredRawLogEnergy r / 256) ≤
        fourCellOddNineteenTwentiethsRetainedQuadratic w := by
    rw [← hid] at hs
    change t ^ 2 * (centeredRawLogEnergy r / 256) ≤
      fourCellOddNineteenTwentiethsRetainedQuadratic
        (fourCellOddP51HighTailMiddleProfile a t r)
    linarith
  have hretainedCore :=
    fourCellOddNineteenTwentiethsRetainedQuadratic_le_coreLocalQuadratic
      w hw hwodd
  exact hraw.trans (hrawRetained.trans hretainedCore)

/-- End-to-end algebraic handoff at the stronger high-tail constant. -/
theorem fourCellOddP11CoupledRieszDefectNonnegative_of_oneEighthRawStripSurplus
    (hsurplus : FourCellOddP51OneEighthRawStripSurplusNonnegative)
    (hpivot : FourCellOddP51GalerkinPivotNonnegative)
    (hdual : FourCellOddP51GalerkinP53PlusResidualDual (1 / 8)) :
    FourCellOddP11CoupledRieszDefectNonnegative := by
  apply
    fourCellOddP11CoupledRieszDefectNonnegative_of_P51HighTailGalerkinRiesz
      (1 / 8) (by norm_num)
  · exact
      fourCellOddP51P53PlusMiddleCoerciveAt_oneEighth_of_rawStripSurplus
        hsurplus
  · exact hpivot
  · exact hdual

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP51HighTailMiddleReductionStructural
