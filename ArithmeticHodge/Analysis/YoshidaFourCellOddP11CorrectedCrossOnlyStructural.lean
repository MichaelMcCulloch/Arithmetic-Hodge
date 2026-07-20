import ArithmeticHodge.Analysis.YoshidaFourCellOddP11CorrectedDeterminantAuditStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP11DirectCorrectedCauchyStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP11P1TailSchurStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11CorrectedCrossOnlyStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaFourCellOddP11ConcreteWeightedDualClosureStructural
open YoshidaFourCellOddP11CorrectedDeterminantAuditStructural
open YoshidaFourCellOddP11CoupledRieszClosureStructural
open YoshidaFourCellOddP11CoupledRieszDefectClosureStructural
open YoshidaFourCellOddP11DirectCorrectedCauchyStructural
open YoshidaFourCellOddP11FormDualProbeStructural
open YoshidaFourCellOddP11P1TailSchurStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# The sole remaining corrected cross at the odd `P₁₁+` frontier

The pure `P₁`--tail Schur diagonal is now unconditional.  Consequently the
complete odd length-four frontier is exactly the one correlation-preserving
Cauchy inequality below.  Its right-hand side retains the *actual* tail Schur
reserve; replacing that reserve by an independently allocated scalar lower
bound is strictly stronger and is not used here.
-/

/-- Cauchy--Schwarz between the finite and tail inverse-free `P₁` Schur
residuals, written in their scalar corrected-reserve coordinates. -/
def FourCellOddP11CorrectedCrossCauchyOnly : Prop :=
  ∀ (d e f g : ℝ) (r : ℝ → ℝ),
    ContDiff ℝ 1 r → Function.Odd r →
    centeredOddP1Coefficient r = 0 →
    centeredOddP3Coefficient r = 0 →
    centeredOddP5Coefficient r = 0 →
    centeredOddP7Coefficient r = 0 →
    centeredOddP9Coefficient r = 0 →
    fourCellOddP11FiniteTailCorrectedCross d e f g r ^ 2 ≤
      fourCellOddP11FiniteCorrectedReserve d e f g *
        fourCellOddP11TailCorrectedReserve r

/-- The proved pure-tail diagonal turns the single corrected cross into the
full direct corrected Cauchy certificate. -/
theorem fourCellOddP11DirectCorrectedCauchy_of_correctedCrossOnly
    (hcross : FourCellOddP11CorrectedCrossCauchyOnly) :
    FourCellOddP11DirectCorrectedCauchy := by
  intro d e f g r hr hodd h1 h3 h5 h7 h9
  exact ⟨
    fourCellOddP11P1TailSchurNonnegative_proved
      r hr hodd h1 h3 h5 h7 h9,
    hcross d e f g r hr hodd h1 h3 h5 h7 h9⟩

/-- Conversely, the direct corrected certificate contains precisely this
cross inequality as its second conjunct. -/
theorem correctedCrossOnly_of_fourCellOddP11DirectCorrectedCauchy
    (hcauchy : FourCellOddP11DirectCorrectedCauchy) :
    FourCellOddP11CorrectedCrossCauchyOnly := by
  intro d e f g r hr hodd h1 h3 h5 h7 h9
  exact (hcauchy d e f g r hr hodd h1 h3 h5 h7 h9).2

/-- Exact sharpened odd frontier: after the unconditional pure-tail Schur
theorem, the one corrected finite--tail cross inequality is equivalent to
the original complete `P₁`-orthogonal form-dual bound. -/
theorem fourCellOddP11CorrectedCrossCauchyOnly_iff_P1OrthogonalFormDual :
    FourCellOddP11CorrectedCrossCauchyOnly ↔
      FourCellOddP1OrthogonalFormDualBound := by
  constructor
  · intro hcross
    apply
      (fourCellOddP11CoupledRieszDefectNonnegative_iff_P1OrthogonalFormDual).1
    exact fourCellOddP11CoupledRieszDefectNonnegative_of_directCorrectedCauchy
      (fourCellOddP11DirectCorrectedCauchy_of_correctedCrossOnly hcross)
  · intro hdual
    have hdefect : FourCellOddP11CoupledRieszDefectNonnegative :=
      (fourCellOddP11CoupledRieszDefectNonnegative_iff_P1OrthogonalFormDual).2
        hdual
    exact correctedCrossOnly_of_fourCellOddP11DirectCorrectedCauchy
      (fourCellOddP11DirectCorrectedCauchy_of_coupledRieszDefectNonnegative
        hdefect)

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11CorrectedCrossOnlyStructural
