import ArithmeticHodge.Analysis.YoshidaEndpointPotentialPrefixMomentStructural
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Algebra.Polynomial

set_option autoImplicit false

open Finset MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointPotentialPolynomialPrefixStructural

open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialPrefixMomentStructural

noncomputable section

/-!
# Exact prefix functionals on polynomials

The ordinary and endpoint-potential integrals of an arbitrary polynomial on
`[-1,u]` are finite coefficient sums.  This packages every clipped
polynomial calculation behind two linear functionals, with the logarithmic
part supplied uniformly by the all-degree prefix-moment recurrence.
-/

/-- Exact ordinary integral of a polynomial on `[-1,u]`, expressed through
its coefficients. -/
def polynomialPrefixIntegral (p : ℝ[X]) (u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (p.natDegree + 1),
    p.coeff k *
      (u ^ (k + 1) - (-1 : ℝ) ^ (k + 1)) / (k + 1 : ℝ)

/-- Exact endpoint-potential integral of a polynomial on `[-1,u]`. -/
def endpointPotentialPolynomialPrefixIntegral (p : ℝ[X]) (u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (p.natDegree + 1),
    p.coeff k * endpointPotentialPrefixMoment k u

/-- Affine endpoint-potential prefix functional. -/
def affineEndpointPotentialPolynomialPrefixIntegral
    (a b : ℝ) (p : ℝ[X]) (u : ℝ) : ℝ :=
  a * polynomialPrefixIntegral p u +
    b * endpointPotentialPolynomialPrefixIntegral p u

/-- Ordinary polynomial integration is exactly the coefficient prefix
functional. -/
theorem integral_eval_eq_polynomialPrefixIntegral
    (p : ℝ[X]) (u : ℝ) :
    (∫ x : ℝ in -1..u, p.eval x) = polynomialPrefixIntegral p u := by
  rw [show (fun x : ℝ ↦ p.eval x) =
      fun x ↦ ∑ k ∈ Finset.range (p.natDegree + 1),
        p.coeff k * x ^ k by
    funext x
    exact Polynomial.eval_eq_sum_range x]
  rw [intervalIntegral.integral_finset_sum]
  · unfold polynomialPrefixIntegral
    apply Finset.sum_congr rfl
    intro k hk
    rw [intervalIntegral.integral_const_mul, integral_pow]
    ring
  · intro k hk
    exact Continuous.intervalIntegrable (by fun_prop) (-1) u

/-- Endpoint-potential polynomial integration is exactly the corresponding
coefficient prefix functional. -/
theorem integral_endpointPotential_mul_eval_eq_prefixIntegral
    (p : ℝ[X]) {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) :
    (∫ x : ℝ in -1..u, yoshidaEndpointPotential x * p.eval x) =
      endpointPotentialPolynomialPrefixIntegral p u := by
  rw [show (fun x : ℝ ↦ yoshidaEndpointPotential x * p.eval x) =
      fun x ↦ ∑ k ∈ Finset.range (p.natDegree + 1),
        p.coeff k * (yoshidaEndpointPotential x * x ^ k) by
    funext x
    rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring]
  rw [intervalIntegral.integral_finset_sum]
  · unfold endpointPotentialPolynomialPrefixIntegral
    apply Finset.sum_congr rfl
    intro k hk
    rw [intervalIntegral.integral_const_mul]
    rfl
  · intro k hk
    exact (intervalIntegrable_endpointPotentialPrefixMoment k hu).const_mul _

/-- An affine endpoint-potential weight times any polynomial is integrable
on every endpoint prefix. -/
theorem intervalIntegrable_affineEndpointPotential_mul_eval
    (a b : ℝ) (p : ℝ[X]) {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) :
    IntervalIntegrable
      (fun x : ℝ ↦ (a + b * yoshidaEndpointPotential x) * p.eval x)
      volume (-1) u := by
  have hp : IntervalIntegrable (fun x : ℝ ↦ p.eval x) volume (-1) u :=
    p.continuous.intervalIntegrable (-1) u
  have hVp : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * p.eval x)
      volume (-1) u := by
    simpa only [pow_zero, mul_one] using
      (intervalIntegrable_endpointPotentialPrefixMoment 0 hu).mul_continuousOn
        p.continuous.continuousOn
  have h := (hp.const_mul a).add (hVp.const_mul b)
  apply h.congr
  intro x _hx
  ring

/-- A polynomial against any affine endpoint-potential weight is evaluated
by the affine coefficient prefix functional. -/
theorem integral_affineEndpointPotential_mul_eval_eq_prefixIntegral
    (a b : ℝ) (p : ℝ[X]) {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) :
    (∫ x : ℝ in -1..u,
      (a + b * yoshidaEndpointPotential x) * p.eval x) =
      affineEndpointPotentialPolynomialPrefixIntegral a b p u := by
  have hp : IntervalIntegrable (fun x : ℝ ↦ p.eval x) volume (-1) u :=
    p.continuous.intervalIntegrable (-1) u
  have hVp : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * p.eval x)
      volume (-1) u := by
    simpa only [pow_zero, mul_one] using
      (intervalIntegrable_endpointPotentialPrefixMoment 0 hu).mul_continuousOn
        p.continuous.continuousOn
  rw [show (fun x : ℝ ↦
      (a + b * yoshidaEndpointPotential x) * p.eval x) =
      fun x ↦ a * p.eval x +
        b * (yoshidaEndpointPotential x * p.eval x) by
    funext x
    ring,
    intervalIntegral.integral_add (hp.const_mul a) (hVp.const_mul b),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_eval_eq_polynomialPrefixIntegral,
    integral_endpointPotential_mul_eval_eq_prefixIntegral p hu]
  rfl

end

end ArithmeticHodge.Analysis.YoshidaEndpointPotentialPolynomialPrefixStructural
