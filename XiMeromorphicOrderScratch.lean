import ArithmeticHodge.Analysis.XiZeroMultiplicity

set_option autoImplicit false

open Complex

namespace ArithmeticHodge.Analysis

theorem meromorphicOrderAt_xiFunction_eq_xiZeroMultiplicity_scratch (z : ℂ) :
    meromorphicOrderAt xiFunction z =
      ((xiZeroMultiplicity z : ℤ) : WithTop ℤ) := by
  have htop : analyticOrderAt xiFunction z ≠ ⊤ :=
    (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z
      (fun w => differentiable_xiFunction.analyticAt w)).not.mpr
        xiFunction_ne_const_zero
  rw [(differentiable_xiFunction.analyticAt z).meromorphicOrderAt_eq]
  rw [← Nat.cast_analyticOrderNatAt htop]
  rw [xiZeroMultiplicity_eq_analyticOrderNatAt]
  rw [ENat.map_coe]

#print axioms meromorphicOrderAt_xiFunction_eq_xiZeroMultiplicity_scratch

end ArithmeticHodge.Analysis
