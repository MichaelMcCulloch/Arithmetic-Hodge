import ArithmeticHodge.Analysis.YoshidaEndpointOddCleanPositive

set_option autoImplicit false

open Real

namespace ArithmeticHodge.Analysis.YoshidaEndpointScalarCancellation

open YoshidaEndpointOddCleanPositive

noncomputable section

/-- The boundary `log 2` created by the singular correlation cancels the
separate renormalization `log 2`, leaving the clean endpoint scalar. -/
theorem endpoint_scalar_cancellation :
    Real.log 2 -
        (Real.log (Real.log 2) + Real.eulerMascheroniConstant +
          Real.log 2 + Real.log Real.pi) =
      -yoshidaEndpointScalarMassLoss := by
  have hlogTwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hlogMul :
      Real.log (Real.pi * Real.log 2) =
        Real.log Real.pi + Real.log (Real.log 2) := by
    exact Real.log_mul Real.pi_ne_zero hlogTwo
  unfold yoshidaEndpointScalarMassLoss
  rw [hlogMul]
  ring

end

end ArithmeticHodge.Analysis.YoshidaEndpointScalarCancellation
