import ArithmeticHodge.Analysis.YoshidaEndpointEvenTailRepresenter

set_option autoImplicit false

open Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeKernel

noncomputable section

/-- Sixth-order Taylor envelope for the regular Yoshida kernel on
`[0, log 2]`.  The odd powers come from the regularized cosecant term. -/
def yoshidaRegularKernelPolynomial6 (t : ℝ) : ℝ :=
  (1 / 4 : ℝ) - t / 48 - t ^ 2 / 32 + 7 * t ^ 3 / 11520 +
    5 * t ^ 4 / 1536 - 31 * t ^ 5 / 1935360 -
      61 * t ^ 6 / 184320

/-- The degree-six regular-kernel envelope is normalized at the removable
singularity. -/
theorem yoshidaRegularKernelPolynomial6_zero :
    yoshidaRegularKernelPolynomial6 0 = (1 / 4 : ℝ) := by
  norm_num [yoshidaRegularKernelPolynomial6]

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
