import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option autoImplicit false

open Polynomial Set

namespace ArithmeticHodge.Analysis.PolynomialIteratedIntegrationByParts

noncomputable section

/-!
# Iterated integration by parts for polynomials

This packages the uniform `n`-fold argument needed for shifted-Legendre
orthogonality.  Endpoint vanishing is stated explicitly, so no degree or mode
is checked separately.
-/

/-- Move `n` derivatives from the right polynomial to the left polynomial.
All boundary terms vanish under the stated uniform endpoint hypothesis. -/
theorem integral_eval_mul_iterate_derivative_eq
    (p q : ℝ[X]) (n : ℕ)
    (hboundary : ∀ m < n,
      (derivative^[m] q).eval 0 = 0 ∧
        (derivative^[m] q).eval 1 = 0) :
    (∫ x : ℝ in 0..1, p.eval x * (derivative^[n] q).eval x) =
      (-1 : ℝ) ^ n *
        ∫ x : ℝ in 0..1, (derivative^[n] p).eval x * q.eval x := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
      have hboundary' : ∀ m < n,
          (derivative^[m] q).eval 0 = 0 ∧
            (derivative^[m] q).eval 1 = 0 := by
        intro m hm
        exact hboundary m (hm.trans (Nat.lt_succ_self n))
      have hqDeriv (x : ℝ) :
          HasDerivAt (fun y : ℝ ↦ (derivative^[n] q).eval y)
            ((derivative^[n.succ] q).eval x) x := by
        rw [Function.iterate_succ_apply']
        exact (derivative^[n] q).hasDerivAt x
      have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
        (u := fun x : ℝ ↦ p.eval x)
        (u' := fun x : ℝ ↦ p.derivative.eval x)
        (v := fun x : ℝ ↦ (derivative^[n] q).eval x)
        (v' := fun x : ℝ ↦ (derivative^[n.succ] q).eval x)
        (fun x _ ↦ p.hasDerivAt x) (fun x _ ↦ hqDeriv x)
        (Continuous.intervalIntegrable (by
          rw [continuous_iff_continuousAt]
          intro x
          exact p.derivative.hasDerivAt x |>.continuousAt) 0 1)
        (Continuous.intervalIntegrable (by
          rw [continuous_iff_continuousAt]
          intro x
          exact (derivative^[n.succ] q).hasDerivAt x |>.continuousAt) 0 1)
      have hb := hboundary n (Nat.lt_succ_self n)
      have hibp' :
          (∫ x : ℝ in 0..1,
              p.eval x * (derivative^[n.succ] q).eval x) =
            -(∫ x : ℝ in 0..1,
              p.derivative.eval x * (derivative^[n] q).eval x) := by
        simpa only [hb.1, hb.2, mul_zero, sub_zero, zero_sub] using hibp
      rw [hibp', ih p.derivative hboundary']
      rw [← Function.iterate_succ_apply]
      rw [pow_succ]
      ring

/-- Orthogonality consequence: after moving more derivatives than the left
polynomial's degree, the integral vanishes. -/
theorem integral_eval_mul_iterate_derivative_eq_zero
    (p q : ℝ[X]) (n : ℕ) (hp : p.natDegree < n)
    (hboundary : ∀ m < n,
      (derivative^[m] q).eval 0 = 0 ∧
        (derivative^[m] q).eval 1 = 0) :
    (∫ x : ℝ in 0..1, p.eval x * (derivative^[n] q).eval x) = 0 := by
  rw [integral_eval_mul_iterate_derivative_eq p q n hboundary,
    iterate_derivative_eq_zero hp]
  simp

end

end ArithmeticHodge.Analysis.PolynomialIteratedIntegrationByParts
