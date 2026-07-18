import ArithmeticHodge.Analysis.YoshidaEndpointPotentialPolynomialPrefixStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoReflectedPoleEntropyStructural
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaReflectedEndpointSignedEntropyPrefixStructural

open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialPolynomialPrefixStructural
open YoshidaFactorTwoReflectedPoleEntropyStructural

noncomputable section

/-!
# Polynomial prefix integrals of signed endpoint entropy

The signed entropy derivative is the endpoint potential plus the constant
`log 2 - 1`.  One integration by parts therefore reduces every entropy times
polynomial prefix to the existing affine endpoint-potential prefix functional.
-/

/-- Interior derivative of the continuous signed endpoint entropy. -/
theorem hasDerivAt_reflectedEndpointSignedEntropy
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt reflectedEndpointSignedEntropy
      (yoshidaEndpointPotential x + Real.log 2 - 1) x := by
  have hplus : (x + 1) / 2 ≠ 0 := by
    have : 0 < (x + 1) / 2 := by linarith [hx.1]
    exact ne_of_gt this
  have hminus : (1 - x) / 2 ≠ 0 := by
    have : 0 < (1 - x) / 2 := by linarith [hx.2]
    exact ne_of_gt this
  have hplusAffine : HasDerivAt (fun y : ℝ ↦ (y + 1) / 2) (1 / 2) x := by
    simpa using ((hasDerivAt_id x).add_const 1).div_const 2
  have hminusAffine : HasDerivAt (fun y : ℝ ↦ (1 - y) / 2) (-1 / 2) x := by
    convert ((hasDerivAt_const x (1 : ℝ)).sub
      (hasDerivAt_id x)).div_const 2 using 1
    all_goals ring
  have h :=
    ((Real.hasDerivAt_negMulLog hplus).comp x hplusAffine).sub
      ((Real.hasDerivAt_negMulLog hminus).comp x hminusAffine)
  have hlogs := reflectedEndpointLogs_sum_eq_potential hx
  convert h using 1
  dsimp only [Function.comp_apply]
  nlinarith

/-- Signed entropy times a polynomial derivative is evaluated by one boundary
term and the affine endpoint-potential prefix functional.  Endpoint
differentiability is not required: continuity on the closed interval and the
derivative identity on its interior suffice. -/
theorem integral_reflectedEndpointSignedEntropy_mul_derivative_eval_eq
    (q : ℝ[X]) {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) :
    (∫ x : ℝ in -1..u,
      reflectedEndpointSignedEntropy x * q.derivative.eval x) =
      reflectedEndpointSignedEntropy u * q.eval u -
        affineEndpointPotentialPolynomialPrefixIntegral
          (Real.log 2 - 1) 1 q u := by
  have hEntropyDerivativeIntegrable : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x + Real.log 2 - 1)
      volume (-1) u := by
    have h := intervalIntegrable_affineEndpointPotential_mul_eval
      (Real.log 2 - 1) 1 (1 : ℝ[X]) hu
    convert h using 1
    funext x
    simp
    ring
  have hPolynomialDerivativeIntegrable : IntervalIntegrable
      (fun x : ℝ ↦ q.derivative.eval x) volume (-1) u :=
    q.derivative.continuous.intervalIntegrable (-1) u
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := reflectedEndpointSignedEntropy)
    (v := fun x : ℝ ↦ q.eval x)
    (u' := fun x : ℝ ↦ yoshidaEndpointPotential x + Real.log 2 - 1)
    (v' := fun x : ℝ ↦ q.derivative.eval x)
    continuous_reflectedEndpointSignedEntropy.continuousOn
    q.continuous.continuousOn
    (fun x hx ↦ by
      apply hasDerivAt_reflectedEndpointSignedEntropy
      have hx' : x ∈ Ioo (-1 : ℝ) u := by
        simpa [min_eq_left hu.1, max_eq_right hu.1] using hx
      exact ⟨hx'.1, hx'.2.trans_le hu.2⟩)
    (fun x _hx ↦ q.hasDerivAt x)
    hEntropyDerivativeIntegrable hPolynomialDerivativeIntegrable
  rw [show (fun x : ℝ ↦
      (yoshidaEndpointPotential x + Real.log 2 - 1) * q.eval x) =
      fun x ↦ ((Real.log 2 - 1) + 1 * yoshidaEndpointPotential x) *
        q.eval x by
      funext x
      ring,
    integral_affineEndpointPotential_mul_eval_eq_prefixIntegral
      (Real.log 2 - 1) 1 q hu] at hIBP
  simpa using hIBP

end

end ArithmeticHodge.Analysis.YoshidaReflectedEndpointSignedEntropyPrefixStructural
