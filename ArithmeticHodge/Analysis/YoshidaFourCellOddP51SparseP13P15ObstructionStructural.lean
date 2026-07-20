import ArithmeticHodge.Analysis.YoshidaFourCellOddP15RetentionStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP51SparseP13AnchorStructural

set_option autoImplicit false

open MeasureTheory Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP51SparseP13P15ObstructionStructural

noncomputable section

open YoshidaFourCellOddFiniteLegendreSolveStructural
open YoshidaFourCellOddP15RetentionStructural
open YoshidaFourCellOddCoreNineteenTwentiethsCoercivityStructural
open YoshidaFourCellOddP51SparseP13AnchorStructural
open YoshidaFourCellOddStripCapacityClosureStructural

/-!
# The first-row obstruction to the sparse P13 pivot certificate

The sparse `P13` anchor leaves the block `P15,P17,...,P51`.  Before trying
to estimate all nineteen rows, any proposed normal-residual certificate
must pay its first `P15` row.  This file isolates that necessary condition
by one application of positivity of the remaining summands.  No row is
expanded and no finite list is enumerated.
-/

/-- The first omitted normal row of the exact retained-`P13` residual. -/
def fourCellOddP51SparseP13P15NormalRow : ℝ :=
  fourCellOddCoreLocalBilinear
    fourCellOddP13RetainedSolvedResidual fourCellOddP15DirectTail

private theorem first_high_basis_eq_P15 :
    fourCellOddFiniteRetainedBasis
        (Fin.natAdd 6 (0 : Fin 19) : Fin 25) =
      fourCellOddP15DirectTail := by
  funext x
  rfl

/-- The single `P15` Bessel payment is a lower bound for the complete
nineteen-row sparse-`P13` normal energy. -/
theorem thirtyOne_mul_sparseP13P15NormalRow_sq_le_highEnergy :
    (31 : ℝ) * fourCellOddP51SparseP13P15NormalRow ^ 2 ≤
      fourCellOddP51SparseP13HighNormalResidualEnergy := by
  have hterm_nonneg (i : Fin 19) : 0 ≤
      (2 * (@fourCellOddFiniteRetainedDegree 24
          (Fin.natAdd 6 i : Fin 25) : ℝ) + 1) *
        fourCellOddCoreLocalBilinear
          fourCellOddP13RetainedSolvedResidual
          (fourCellOddFiniteRetainedBasis
            (Fin.natAdd 6 i : Fin 25)) ^ 2 := by
    positivity
  have hfirst := Finset.single_le_sum
    (fun i _hi ↦ hterm_nonneg i) (Finset.mem_univ (0 : Fin 19))
  change
    (2 * (@fourCellOddFiniteRetainedDegree 24
        (Fin.natAdd 6 (0 : Fin 19) : Fin 25) : ℝ) + 1) *
      fourCellOddCoreLocalBilinear
        fourCellOddP13RetainedSolvedResidual
        (fourCellOddFiniteRetainedBasis
          (Fin.natAdd 6 (0 : Fin 19) : Fin 25)) ^ 2 ≤
      fourCellOddP51SparseP13HighNormalResidualEnergy at hfirst
  rw [first_high_basis_eq_P15] at hfirst
  norm_num [fourCellOddFiniteRetainedDegree,
    fourCellOddP51SparseP13P15NormalRow] at hfirst ⊢
  exact hfirst

/-- Every proposed sparse-`P13` floor certificate must already dominate
the exact first omitted row. -/
theorem sparseP13P15NormalRow_le_budget_of_high_certificate
    (tau : ℝ)
    (hcertificate :
      fourCellOddP51SparseP13HighNormalResidualEnergy ≤
        fourCellOddNineteenTwentiethsCoercivityConstant *
          (fourCellOddCoreLocalQuadratic
              fourCellOddP13RetainedSolvedResidual - tau)) :
    (31 : ℝ) * fourCellOddP51SparseP13P15NormalRow ^ 2 ≤
      fourCellOddNineteenTwentiethsCoercivityConstant *
        (fourCellOddCoreLocalQuadratic
            fourCellOddP13RetainedSolvedResidual - tau) :=
  thirtyOne_mul_sparseP13P15NormalRow_sq_le_highEnergy.trans hcertificate

/-- Exact contrapositive obstruction: reversing the single `P15` payment
refutes the complete nineteen-row certificate. -/
theorem not_sparseP13High_certificate_of_budget_lt_P15_row
    (tau : ℝ)
    (hobstruction :
      fourCellOddNineteenTwentiethsCoercivityConstant *
          (fourCellOddCoreLocalQuadratic
              fourCellOddP13RetainedSolvedResidual - tau) <
        (31 : ℝ) * fourCellOddP51SparseP13P15NormalRow ^ 2) :
    ¬ fourCellOddP51SparseP13HighNormalResidualEnergy ≤
        fourCellOddNineteenTwentiethsCoercivityConstant *
          (fourCellOddCoreLocalQuadratic
              fourCellOddP13RetainedSolvedResidual - tau) := by
  intro hcertificate
  exact (not_lt_of_ge
    (sparseP13P15NormalRow_le_budget_of_high_certificate
      tau hcertificate)) hobstruction

/-- In particular, a common `L²` representer certificate cannot evade the
first omitted row: its norm must dominate the same `P15` payment. -/
theorem sparseP13P15NormalRow_le_l2_of_representer
    (F : ℝ → ℝ)
    (hF : MemLp F 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hrow : ∀ i : Fin 21,
      fourCellOddCoreLocalBilinear
          fourCellOddP13RetainedSolvedResidual
          (fourCellOddFiniteRetainedBasis
            (Fin.natAdd 4 i : Fin 25)) =
        ∫ x : ℝ in 0..1,
          F x * fourCellOddFiniteRetainedBasis
            (Fin.natAdd 4 i : Fin 25) x) :
    (31 : ℝ) * fourCellOddP51SparseP13P15NormalRow ^ 2 ≤
      ∫ x : ℝ in 0..1, F x ^ 2 := by
  exact thirtyOne_mul_sparseP13P15NormalRow_sq_le_highEnergy.trans
    (fourCellOddP51SparseP13HighNormalResidualEnergy_le_l2_of_representer
      F hF hrow)

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP51SparseP13P15ObstructionStructural
