import ArithmeticHodge.Analysis.YoshidaFourCellOddP11CoreEntryBoundsStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddCoreIntegratedRegularAbsorptionStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11CoreDiagonalBoundsStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaFourCellOddCoreIntegratedRegularAbsorptionStructural
open YoshidaFourCellOddP11GalerkinResidualDualDirectStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellParityOperatorStructural

/-!
# Structural diagonal bound for the first augmented odd mode

The augmented six-mode Galerkin block needs one new diagonal entry, the core
quadratic of the genuine `P₁₁` tail direction.  Its positivity does not
require a sampled kernel estimate: the already proved infinite-dimensional
odd coercivity theorem applies directly, because `P₁₁` is exactly
orthogonal to `P₁` and has positive-half mass `1 / 23`.
-/

/-- Rational, assumption-free lower bound for the new `P₁₁` diagonal.
This is the normalized coercivity floor `(343 / 12500) * (1 / 23)`. -/
theorem threeHundredFortyThree_div_twoHundredEightySevenThousandFiveHundred_le_fourCellOddCoreLocalQuadratic_P11 :
    (343 / 287500 : ℝ) ≤
      fourCellOddCoreLocalQuadratic fourCellOddP11DirectTail := by
  have hP1 : centeredOddP1Coefficient fourCellOddP11DirectTail = 0 :=
    fourCellOddP11DirectTail_moments.1
  have h :=
    threeHundredFortyThree_div_twelveThousandFiveHundred_mul_mass_le_coreLocalQuadratic_of_P1
      fourCellOddP11DirectTail contDiff_fourCellOddP11DirectTail
      odd_fourCellOddP11DirectTail hP1
  rw [integral_zero_one_fourCellOddP11DirectTail_sq] at h
  norm_num at h ⊢
  exact h

/-- In particular, the augmented diagonal is strictly positive. -/
theorem fourCellOddCoreLocalQuadratic_P11_pos :
    0 < fourCellOddCoreLocalQuadratic fourCellOddP11DirectTail := by
  have h :=
    threeHundredFortyThree_div_twoHundredEightySevenThousandFiveHundred_le_fourCellOddCoreLocalQuadratic_P11
  norm_num at h ⊢
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 343 / 287500) h

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11CoreDiagonalBoundsStructural
