import ArithmeticHodge.Analysis.ZetaZeroCount

set_option autoImplicit false

open Complex

namespace ArithmeticHodge.Analysis

theorem xiZeroMultiplicity_eq_analyticOrderNatAt_scratch (z : ℂ) :
    xiZeroMultiplicity z = analyticOrderNatAt xiFunction z := by
  have hdiv : xiDivisor z = (analyticOrderNatAt xiFunction z : ℤ) := by
    have hxi_an : AnalyticOnNhd ℂ xiFunction Set.univ :=
      analyticOnNhd_univ_iff_differentiable.mpr differentiable_xiFunction
    have hxi_mer : MeromorphicOn xiFunction Set.univ := hxi_an.meromorphicOn
    rw [xiDivisor, MeromorphicOn.divisor_apply hxi_mer (Set.mem_univ z)]
    have htop_a : analyticOrderAt xiFunction z ≠ ⊤ :=
      (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z
        (fun w => differentiable_xiFunction.analyticAt w)).not.mpr
          xiFunction_ne_const_zero
    have htop_m : meromorphicOrderAt xiFunction z ≠ ⊤ := by
      rw [(differentiable_xiFunction.analyticAt z).meromorphicOrderAt_eq]
      simp [htop_a]
    apply WithTop.coe_eq_coe.mp
    rw [WithTop.coe_untop₀_of_ne_top htop_m]
    rw [(differentiable_xiFunction.analyticAt z).meromorphicOrderAt_eq]
    rw [← Nat.cast_analyticOrderNatAt htop_a]
    simp
  simp [xiZeroMultiplicity, hdiv]

#print axioms xiZeroMultiplicity_eq_analyticOrderNatAt_scratch

end ArithmeticHodge.Analysis
