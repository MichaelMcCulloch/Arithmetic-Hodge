import ArithmeticHodge.Analysis.MultiplicativeWeilArchPolarLimit

/-!
# The unconditional Bombieri explicit formula

The archimedean-polar right-line limit closes the contour assembly.  Hence the
concrete Bombieri functional equals both the distinct analytic-multiplicity
zero sum and every exact-multiplicity enumerated zero sum.
-/

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- The concrete Bombieri functional equals the distinct nontrivial-zero sum,
with every zero weighted by its analytic multiplicity. -/
theorem bombieriDistinctZeroSumFormula :
    BombieriDistinctZeroSumFormula :=
  bombieriDistinctZeroSumFormula_of_archPolarRightLineLimit
    bombieriArchPolarRightLineLimit

/-- Every exhaustive exact-multiplicity enumeration satisfies Bombieri's
zero-sum formula. -/
theorem bombieriZeroSumFormula (zeros : ZetaZeroEnumeration) :
    BombieriZeroSumFormula zeros :=
  bombieriZeroSumFormula_of_archPolarRightLineLimit
    bombieriArchPolarRightLineLimit zeros

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
