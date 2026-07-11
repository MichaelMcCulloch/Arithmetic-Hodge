import ArithmeticHodge.Analysis.MultiplicativeWeilFunctional
import ArithmeticHodge.Analysis.MultiplicativeWeilZeroFiberSum

/-!
# Distinct-zero form of the Bombieri formula

The exact-multiplicity enumeration can be eliminated from the remaining
explicit-formula target.  It suffices to prove one sum over distinct
nontrivial zeros, weighted by their analytic multiplicities.
-/

set_option autoImplicit false

open Complex

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- The concrete Bombieri functional equals the analytic-multiplicity-weighted
sum over distinct nontrivial zeta zeros. -/
def BombieriDistinctZeroSumFormula : Prop :=
  ∀ f : BombieriTest,
    bombieriFunctional f =
      ∑' rho : NontrivialZetaZero,
        (analyticOrderNatAt riemannZeta rho.val : ℂ) *
          mellin (f : ℝ → ℂ) rho.val

/-- For any exhaustive exact-multiplicity enumeration, the enumerated
Bombieri zero-sum formula is equivalent to its distinct-zero form. -/
theorem bombieriZeroSumFormula_iff_distinct
    (zeros : ZetaZeroEnumeration) :
    BombieriZeroSumFormula zeros ↔ BombieriDistinctZeroSumFormula := by
  constructor
  · intro hformula f
    rw [hformula f]
    exact zeros.tsum_comp_zero_eq_tsum_distinct_multiplicity
      (fun rho => mellin (f : ℝ → ℂ) rho.val)
      (zeros.mellin_summable f)
  · intro hformula f
    rw [hformula f]
    exact (zeros.tsum_comp_zero_eq_tsum_distinct_multiplicity
      (fun rho => mellin (f : ℝ → ℂ) rho.val)
      (zeros.mellin_summable f)).symm

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
