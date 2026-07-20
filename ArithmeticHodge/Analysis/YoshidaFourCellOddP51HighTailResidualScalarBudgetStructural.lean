import ArithmeticHodge.Analysis.YoshidaFourCellOddP51HighTailResidualRepresenterStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP51HighTailResidualScalarBudgetStructural

noncomputable section

open YoshidaFourCellOddP51GalerkinRieszStructural
open YoshidaFourCellOddP51HighTailResidualRepresenterStructural
open YoshidaFourCellOddP51Kernel18ErrorBudgetStructural

/-!
# Loose scalar budget for the P51 high-tail residual

The exact `P53+` main representer can use a deliberately loose norm cap.
The rational bound `3 / 40000` still lies strictly below the budget forced
by the existing `7 / 10000` pivot floor at the high-tail constant `1 / 8`.
This leaves the analytic norm estimate well separated from the final scalar
arithmetic.
-/

/-- A loose closed norm cap for the complete projected main row. -/
def FourCellOddP51MainP53PlusThreeFortyThousandCap : Prop :=
  ‖fourCellOddP51Kernel18MainP53PlusL2‖ ^ 2 ≤ (3 / 40000 : ℝ)

/-- The loose norm cap and the existing pivot floor imply the exact main-row
budget at the high-tail constant `1 / 8`. -/
theorem fourCellOddP51Kernel18MainP53PlusNormCertificate_oneEighth_of_cap
    (hpivot : FourCellOddP51GalerkinPivotSevenTenThousandFloor)
    (hmain : FourCellOddP51MainP53PlusThreeFortyThousandCap) :
    FourCellOddP51Kernel18MainP53PlusNormCertificate (9 / 10) (1 / 8) := by
  unfold FourCellOddP51Kernel18MainP53PlusNormCertificate
  calc
    ‖fourCellOddP51Kernel18MainP53PlusL2‖ ^ 2 ≤ (3 / 40000 : ℝ) :=
      hmain
    _ ≤ (9 / 10 : ℝ) * ((7 / 10000 : ℝ) * (1 / 8 : ℝ)) := by
      norm_num
    _ ≤ (9 / 10 : ℝ) *
        (fourCellOddP51GalerkinPivot * (1 / 8 : ℝ)) := by
      gcongr
      simpa only [FourCellOddP51GalerkinPivotSevenTenThousandFloor] using hpivot

/-- Consequently only three transparent scalar facts remain on the residual
side: the pivot floor, a harmless mass normalization, and the loose norm cap.
-/
theorem fourCellOddP51GalerkinP53PlusResidualDual_oneEighth_of_scalarCaps
    (hpivot : FourCellOddP51GalerkinPivotSevenTenThousandFloor)
    (hmass : FourCellOddQ51PositiveHalfMassAtMostOne)
    (hmain : FourCellOddP51MainP53PlusThreeFortyThousandCap) :
    FourCellOddP51GalerkinP53PlusResidualDual (1 / 8) := by
  apply
    fourCellOddP51GalerkinP53PlusResidualDual_oneEighth_of_certificate
  refine ⟨?_,
    fourCellOddP51Kernel18MainP53PlusNormCertificate_oneEighth_of_cap
      hpivot hmain,
    ?_⟩
  · exact (by norm_num : (0 : ℝ) ≤ 7 / 10000).trans
      (by
        simpa only [FourCellOddP51GalerkinPivotSevenTenThousandFloor]
          using hpivot)
  · exact
      integral_zero_one_fourCellOddP51Kernel18ErrorRepresenter_sq_le_budget_of_kappa_floor
        (1 / 8) (by norm_num) hpivot hmass

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP51HighTailResidualScalarBudgetStructural
