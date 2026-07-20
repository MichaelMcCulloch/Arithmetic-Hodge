import ArithmeticHodge.Analysis.YoshidaFourCellOddP51HighTailRawStripSchurStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP51TailDiagonalDecisionStructural

noncomputable section

open UnitIntervalLogEnergyAffine
open YoshidaFourCellOddCoreNineteenTwentiethsCoercivityStructural
open YoshidaFourCellOddP51GalerkinRieszStructural
open YoshidaFourCellOddP51HighTailMiddleReductionStructural
open YoshidaFourCellOddP51HighTailRawStripSchurStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# Decision criterion for the `P51` tail diagonal

The `1 / 256` reservation is qualitatively different from the already
proved `P53+` raw gap: it subtracts the unbounded raw form from a diagonal
whose currently available coercive floor is only an `L²` floor.  This file
isolates a concrete counterwitness regime.  It uses no additional retained
mode family.

If a genuine tail has raw-strip reserve and prime/potential diagonal each at
most three times its positive-half mass, but raw energy more than 768 times
that mass, then its reserved tail diagonal is strictly negative.  The
existing zero-retained transport then refutes the complete one-eighth
raw-strip surplus certificate.
-/

/-- Positive-half mass, named locally to keep the decision inequalities
readable. -/
def fourCellOddP51TailPositiveHalfMass (r : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ in 0..1, r x ^ 2

/-- The signed scalar coefficient is comfortably larger than three.  This
is the only transcendental estimate used by the counterwitness criterion. -/
theorem three_lt_fourCellOddLocalScalarMassCoefficient :
    (3 : ℝ) < fourCellOddLocalScalarMassCoefficient := by
  have hscalar := fourCellScalar_fine_bounds.1
  unfold fourCellOddLocalScalarMassCoefficient
  linarith

/-- Concrete diagonal decision.  The constants deliberately leave a strict
`3 / 20` mass margin, so no equality case is hidden in the transport. -/
theorem fourCellOddP51OneEighthTailDiagonal_neg_of_highRaw_saturation
    (r : ℝ → ℝ)
    (hreserve :
      fourCellOddRawStripCancellationReserve r ≤
        3 * fourCellOddP51TailPositiveHalfMass r)
    (hprime :
      fourCellOddRetainedPrimePotentialQuadratic r ≤
        3 * fourCellOddP51TailPositiveHalfMass r)
    (hraw :
      768 * fourCellOddP51TailPositiveHalfMass r <
        centeredRawLogEnergy r) :
    fourCellOddP51OneEighthTailDiagonal r < 0 := by
  have hmass : 0 ≤ fourCellOddP51TailPositiveHalfMass r := by
    unfold fourCellOddP51TailPositiveHalfMass
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg (r x))
  have hreserveScaled :
      (19 / 20 : ℝ) * fourCellOddRawStripCancellationReserve r ≤
        (57 / 20 : ℝ) * fourCellOddP51TailPositiveHalfMass r := by
    have := mul_le_mul_of_nonneg_left hreserve (by norm_num : (0 : ℝ) ≤ 19 / 20)
    nlinarith
  have hscalarMass :
      3 * fourCellOddP51TailPositiveHalfMass r ≤
        fourCellOddLocalScalarMassCoefficient *
          fourCellOddP51TailPositiveHalfMass r :=
    mul_le_mul_of_nonneg_right
      three_lt_fourCellOddLocalScalarMassCoefficient.le hmass
  have hrawReserved :
      3 * fourCellOddP51TailPositiveHalfMass r <
        centeredRawLogEnergy r / 256 := by
    linarith
  unfold fourCellOddP51TailPositiveHalfMass at hreserve hprime hraw hmass
  unfold fourCellOddP51TailPositiveHalfMass at hreserveScaled hscalarMass
  unfold fourCellOddP51TailPositiveHalfMass at hrawReserved
  unfold fourCellOddP51OneEighthTailDiagonal
    fourCellOddNineteenTwentiethsRetainedQuadratic
  linarith

/-- A genuine `P53+` high-raw saturation packet is therefore a closed
counterwitness to the entire proposed one-eighth surplus, not merely to an
auxiliary diagonal estimate. -/
theorem not_fourCellOddP51OneEighthRawStripSurplusNonnegative_of_highRaw_saturation
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (htail : FourCellOddP53PlusMomentConditions r)
    (hreserve :
      fourCellOddRawStripCancellationReserve r ≤
        3 * fourCellOddP51TailPositiveHalfMass r)
    (hprime :
      fourCellOddRetainedPrimePotentialQuadratic r ≤
        3 * fourCellOddP51TailPositiveHalfMass r)
    (hraw :
      768 * fourCellOddP51TailPositiveHalfMass r <
        centeredRawLogEnergy r) :
    ¬ FourCellOddP51OneEighthRawStripSurplusNonnegative := by
  have hneg : fourCellOddP51OneEighthTailDiagonal r < 0 :=
    fourCellOddP51OneEighthTailDiagonal_neg_of_highRaw_saturation
      r hreserve hprime hraw
  apply
    not_fourCellOddP51OneEighthRawStripSurplusNonnegative_of_tailDiagonal_neg
      1 r hr hodd htail
  simpa using hneg

/-- Contrapositive decision form: if the one-eighth certificate were true,
every genuine tail whose two lower-order diagonals obey the displayed caps
would satisfy an upper raw-energy bound.  This is precisely the reverse
spectral estimate that remains to be justified (or contradicted by a smooth
strip-localized high-frequency packet). -/
theorem raw_le_768_mul_mass_of_oneEighthCertificate_and_saturation_caps
    (hcertificate : FourCellOddP51OneEighthRawStripSurplusNonnegative)
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (hodd : Function.Odd r)
    (htail : FourCellOddP53PlusMomentConditions r)
    (hreserve :
      fourCellOddRawStripCancellationReserve r ≤
        3 * fourCellOddP51TailPositiveHalfMass r)
    (hprime :
      fourCellOddRetainedPrimePotentialQuadratic r ≤
        3 * fourCellOddP51TailPositiveHalfMass r) :
    centeredRawLogEnergy r ≤
      768 * fourCellOddP51TailPositiveHalfMass r := by
  by_contra hnot
  have hraw :
      768 * fourCellOddP51TailPositiveHalfMass r <
        centeredRawLogEnergy r := lt_of_not_ge hnot
  exact
    (not_fourCellOddP51OneEighthRawStripSurplusNonnegative_of_highRaw_saturation
      r hr hodd htail hreserve hprime hraw) hcertificate

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP51TailDiagonalDecisionStructural
