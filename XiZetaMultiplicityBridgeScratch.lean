import ArithmeticHodge.Analysis.XiZeroMultiplicity
import ArithmeticHodge.Analysis.MultiplicativeWeilZeroSummability

set_option autoImplicit false

open Complex

namespace ArithmeticHodge.Analysis

theorem xiZeroMultiplicity_eq_analyticOrderNatAt_riemannZeta_scratch
    (rho : NontrivialZetaZero) :
    xiZeroMultiplicity rho.val = analyticOrderNatAt riemannZeta rho.val := by
  rw [xiZeroMultiplicity_eq_analyticOrderNatAt,
    MultiplicativeWeil.analyticOrderNatAt_xiFunction_eq_riemannZeta]

theorem finset_sum_xiZeroMultiplicity_nsmul_eq_analyticOrderNatAt_riemannZeta_scratch
    {M : Type*} [AddCommMonoid M]
    (S : Finset NontrivialZetaZero) (F : NontrivialZetaZero → M) :
    ∑ rho ∈ S, xiZeroMultiplicity rho.val • F rho =
      ∑ rho ∈ S, analyticOrderNatAt riemannZeta rho.val • F rho := by
  refine Finset.sum_congr rfl fun rho _ ↦ ?_
  rw [xiZeroMultiplicity_eq_analyticOrderNatAt_riemannZeta_scratch]

end ArithmeticHodge.Analysis

#check ArithmeticHodge.Analysis.xiZeroMultiplicity_eq_analyticOrderNatAt_riemannZeta_scratch
#check ArithmeticHodge.Analysis.finset_sum_xiZeroMultiplicity_nsmul_eq_analyticOrderNatAt_riemannZeta_scratch
#print axioms ArithmeticHodge.Analysis.xiZeroMultiplicity_eq_analyticOrderNatAt_riemannZeta_scratch
#print axioms ArithmeticHodge.Analysis.finset_sum_xiZeroMultiplicity_nsmul_eq_analyticOrderNatAt_riemannZeta_scratch
