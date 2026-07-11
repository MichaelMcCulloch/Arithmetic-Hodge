import ArithmeticHodge.Analysis.MultiplicativeWeilFunctional
import ArithmeticHodge.Analysis.MultiplicativeWeilZeroFiberSum

set_option autoImplicit false

open Complex

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

def BombieriDistinctZeroSumFormula : Prop :=
  ∀ f : BombieriTest,
    bombieriFunctional f =
      ∑' rho : NontrivialZetaZero,
        (analyticOrderNatAt riemannZeta rho.val : ℂ) *
          mellin (f : ℝ → ℂ) rho.val

theorem bombieriZeroSumFormula_iff_distinct_scratch
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

#print axioms bombieriZeroSumFormula_iff_distinct_scratch

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
