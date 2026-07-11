import ArithmeticHodge.Analysis.XiZeroMultiplicity
import ArithmeticHodge.Analysis.MultiplicativeWeilZeroSummability

/-!
# Xi and zeta zero multiplicities

At a nontrivial zeta zero, the zero multiplicity of the completed xi function
is exactly the analytic multiplicity of the Riemann zeta function.
-/

set_option autoImplicit false

open Complex

namespace ArithmeticHodge.Analysis

/-- Completion by the nonvanishing gamma and polynomial factors preserves the
analytic multiplicity of every nontrivial zeta zero. -/
theorem xiZeroMultiplicity_eq_analyticOrderNatAt_riemannZeta
    (rho : NontrivialZetaZero) :
    xiZeroMultiplicity rho.val = analyticOrderNatAt riemannZeta rho.val := by
  rw [xiZeroMultiplicity_eq_analyticOrderNatAt,
    MultiplicativeWeil.analyticOrderNatAt_xiFunction_eq_riemannZeta]

/-- A finite sum weighted by xi multiplicities can be rewritten using the
analytic zeta multiplicities, in any additive target. -/
theorem finset_sum_xiZeroMultiplicity_nsmul_eq_analyticOrderNatAt_riemannZeta
    {M : Type*} [AddCommMonoid M]
    (S : Finset NontrivialZetaZero) (F : NontrivialZetaZero → M) :
    ∑ rho ∈ S, xiZeroMultiplicity rho.val • F rho =
      ∑ rho ∈ S, analyticOrderNatAt riemannZeta rho.val • F rho := by
  refine Finset.sum_congr rfl fun rho _ ↦ ?_
  rw [xiZeroMultiplicity_eq_analyticOrderNatAt_riemannZeta]

end ArithmeticHodge.Analysis
