import ArithmeticHodge.Analysis.YoshidaFourCellOddP51Kernel18MainSelectorStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP51SparseP11AnchorMassStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP51Kernel18CertificateAssemblyStructural

noncomputable section

open YoshidaFourCellOddCoreNineteenTwentiethsCoercivityStructural
open YoshidaFourCellOddFiniteLegendreSolveStructural
open YoshidaFourCellOddP11CoupledRieszClosureStructural
open YoshidaFourCellOddP11GalerkinSolutionBoxStructural
open YoshidaFourCellOddP51GalerkinRieszStructural
open YoshidaFourCellOddP51Kernel18ErrorBudgetStructural
open YoshidaFourCellOddP51Kernel18MainSelectorStructural
open YoshidaFourCellOddP51Kernel18RowDecompositionStructural
open YoshidaFourCellOddP51SparseP11AnchorMassStructural
open YoshidaFourCellOddP51TailBudgetAssemblyStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# Final structural assembly of the P51 odd four-cell certificate

The exact row decomposition, the complete low-mode selector, and the sparse
`P11` anchor reduce the full odd four-cell production proposition to two
scalar estimates:

* one high-normal-residual energy inequality for the sparse anchor;
* one positive-half `L²` norm inequality for a main-row selector residual.

No matrix inverse, list of twenty-five rows, or infinite-dimensional test
function remains in this assembly.
-/

/-- The two scalar structural certificates left by the degree-eighteen P51
route. -/
def FourCellOddP51Kernel18StructuralCertificate
    (c : ℝ) (a : FourCellOddP51RetainedIndex → ℝ) : Prop :=
  fourCellOddP51SparseP11HighNormalResidualEnergy ≤
      fourCellOddNineteenTwentiethsCoercivityConstant *
        (fourCellOddCoreLocalQuadratic
            fourCellOddP11GalerkinRetainedResidualProfile -
          (7 / 10000 : ℝ)) ∧
    FourCellOddP51Kernel18MainSelectorCertificate
      fourCellOddNineteenTwentiethsCoercivityConstant c a

/-- The two scalar certificates give the exact finite-plus-tail P51
Galerkin--Riesz certificate. -/
theorem fourCellOddP51GalerkinRieszCertificate_of_kernel18StructuralCertificate
    (c : ℝ) (a : FourCellOddP51RetainedIndex → ℝ)
    (hcert : FourCellOddP51Kernel18StructuralCertificate c a) :
    FourCellOddP51GalerkinRieszCertificate
      fourCellOddNineteenTwentiethsCoercivityConstant := by
  rcases hcert with ⟨hhigh, hmainCertificate⟩
  rcases fourCellOddP51SparseP11HighCertificate_closes_floor_and_mass hhigh with
    ⟨hpivotFloor, hmass⟩
  have hpivot : FourCellOddP51GalerkinPivotNonnegative := by
    change 0 ≤ fourCellOddP51GalerkinPivot
    exact (by norm_num : (0 : ℝ) ≤ 7 / 10000).trans hpivotFloor
  have hmain : FourCellOddP51TailPairBudget (9 / 10)
      fourCellOddNineteenTwentiethsCoercivityConstant
      fourCellOddP51Kernel18MainRepresenter :=
    fourCellOddP51Kernel18MainTailPairBudget_of_selectorCertificate
      fourCellOddNineteenTwentiethsCoercivityConstant c a hmainCertificate
  have herrorL2 :
      (∫ x : ℝ in 0..1,
          fourCellOddP51Kernel18ErrorRepresenter x ^ 2) ≤
        (1 / 1000 : ℝ) *
          (fourCellOddP51GalerkinPivot *
            fourCellOddNineteenTwentiethsCoercivityConstant) :=
    integral_zero_one_fourCellOddP51Kernel18ErrorRepresenter_sq_le_budget
      hpivotFloor hmass
  have herror : FourCellOddP51TailPairBudget (1 / 1000)
      fourCellOddNineteenTwentiethsCoercivityConstant
      fourCellOddP51Kernel18ErrorRepresenter :=
    fourCellOddP51TailPairBudget_one_thousandth_of_memLp_l2
      fourCellOddNineteenTwentiethsCoercivityConstant
      fourCellOddP51Kernel18ErrorRepresenter
      memLp_fourCellOddP51Kernel18ErrorRepresenter_two_restrict herrorL2
  refine ⟨hpivot, ?_⟩
  exact fourCellOddP51GalerkinP53PlusResidualDual_of_tailBudgets
    fourCellOddNineteenTwentiethsCoercivityConstant
    fourCellOddNineteenTwentiethsCoercivityConstant_pos.le hpivot
    fourCellOddP51Kernel18MainRepresenter
    fourCellOddP51Kernel18ErrorRepresenter
    fourCellOddP51Kernel18TailRowDecomposition hmain herror

/-- Production handoff: the same two scalar certificates close the complete
odd four-cell Riesz defect required by the structural RH bridge. -/
theorem fourCellOddP11CoupledRieszDefectNonnegative_of_kernel18StructuralCertificate
    (c : ℝ) (a : FourCellOddP51RetainedIndex → ℝ)
    (hcert : FourCellOddP51Kernel18StructuralCertificate c a) :
    FourCellOddP11CoupledRieszDefectNonnegative := by
  apply
    fourCellOddP11CoupledRieszDefectNonnegative_of_nineteenTwentieths_P51Certificate
  exact
    fourCellOddP51GalerkinRieszCertificate_of_kernel18StructuralCertificate
      c a hcert

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP51Kernel18CertificateAssemblyStructural
