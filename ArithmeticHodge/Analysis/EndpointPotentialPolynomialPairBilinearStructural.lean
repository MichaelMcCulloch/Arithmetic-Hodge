import ArithmeticHodge.Analysis.YoshidaEndpointPotentialLegendreDiagonalStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddP1OrthogonalFormDualClosureStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.EndpointPotentialPolynomialPairBilinearStructural

noncomputable section

open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialIntegrable
open YoshidaEndpointPotentialLegendreDiagonalStructural
open YoshidaFourCellOddP1OrthogonalFormDualClosureStructural
open YoshidaFourCellParityHalfFoldStructural

/-!
# The endpoint-potential form as a public symmetric bilinear form

The all-degree Legendre recurrence already uses bilinearity internally.  This
file exposes that structure for arbitrary polynomial profiles and folds an odd
polynomial's positive-half potential mass into the global polynomial pair.
The final theorem rewrites the exact odd `P₁` tail weight without expanding
the polynomial or approximating any integral.
-/

theorem continuous_polynomialEval (p : ℝ[X]) :
    Continuous (fun x : ℝ ↦ p.eval x) :=
  p.continuous

theorem intervalIntegrable_endpointPotentialPolynomialPair
    (p q : ℝ[X]) :
    IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * p.eval x * q.eval x)
      volume (-1) 1 := by
  simpa only [mul_assoc] using
    intervalIntegrable_endpointPotential_mul
      (fun x : ℝ ↦ p.eval x * q.eval x)
      (p.continuous.mul q.continuous)

theorem endpointPotentialPolynomialPair_add_left
    (p q r : ℝ[X]) :
    endpointPotentialPolynomialPair (p + q) r =
      endpointPotentialPolynomialPair p r +
        endpointPotentialPolynomialPair q r := by
  unfold endpointPotentialPolynomialPair
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x * (p + q).eval x * r.eval x) =
    fun x : ℝ ↦
      yoshidaEndpointPotential x * p.eval x * r.eval x +
        yoshidaEndpointPotential x * q.eval x * r.eval x by
    funext x
    simp only [Polynomial.eval_add]
    ring,
    intervalIntegral.integral_add
      (intervalIntegrable_endpointPotentialPolynomialPair p r)
      (intervalIntegrable_endpointPotentialPolynomialPair q r)]

theorem endpointPotentialPolynomialPair_sub_left
    (p q r : ℝ[X]) :
    endpointPotentialPolynomialPair (p - q) r =
      endpointPotentialPolynomialPair p r -
        endpointPotentialPolynomialPair q r := by
  unfold endpointPotentialPolynomialPair
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x * (p - q).eval x * r.eval x) =
    fun x : ℝ ↦
      yoshidaEndpointPotential x * p.eval x * r.eval x -
        yoshidaEndpointPotential x * q.eval x * r.eval x by
    funext x
    simp only [Polynomial.eval_sub]
    ring,
    intervalIntegral.integral_sub
      (intervalIntegrable_endpointPotentialPolynomialPair p r)
      (intervalIntegrable_endpointPotentialPolynomialPair q r)]

theorem endpointPotentialPolynomialPair_smul_left
    (a : ℝ) (p q : ℝ[X]) :
    endpointPotentialPolynomialPair (a • p) q =
      a * endpointPotentialPolynomialPair p q := by
  unfold endpointPotentialPolynomialPair
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x * (a • p).eval x * q.eval x) =
    fun x : ℝ ↦
      a * (yoshidaEndpointPotential x * p.eval x * q.eval x) by
    funext x
    simp only [Polynomial.eval_smul, smul_eq_mul]
    ring,
    intervalIntegral.integral_const_mul]

theorem endpointPotentialPolynomialPair_neg_left
    (p q : ℝ[X]) :
    endpointPotentialPolynomialPair (-p) q =
      -endpointPotentialPolynomialPair p q := by
  unfold endpointPotentialPolynomialPair
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x * (-p).eval x * q.eval x) =
    fun x : ℝ ↦
      -(yoshidaEndpointPotential x * p.eval x * q.eval x) by
    funext x
    simp only [Polynomial.eval_neg]
    ring,
    intervalIntegral.integral_neg]

theorem endpointPotentialPolynomialPair_comm (p q : ℝ[X]) :
    endpointPotentialPolynomialPair p q =
      endpointPotentialPolynomialPair q p := by
  unfold endpointPotentialPolynomialPair
  apply intervalIntegral.integral_congr
  intro x _hx
  ring

theorem endpointPotentialPolynomialPair_add_right
    (p q r : ℝ[X]) :
    endpointPotentialPolynomialPair p (q + r) =
      endpointPotentialPolynomialPair p q +
        endpointPotentialPolynomialPair p r := by
  rw [endpointPotentialPolynomialPair_comm p (q + r),
    endpointPotentialPolynomialPair_add_left,
    endpointPotentialPolynomialPair_comm q p,
    endpointPotentialPolynomialPair_comm r p]

theorem endpointPotentialPolynomialPair_sub_right
    (p q r : ℝ[X]) :
    endpointPotentialPolynomialPair p (q - r) =
      endpointPotentialPolynomialPair p q -
        endpointPotentialPolynomialPair p r := by
  rw [endpointPotentialPolynomialPair_comm p (q - r),
    endpointPotentialPolynomialPair_sub_left,
    endpointPotentialPolynomialPair_comm q p,
    endpointPotentialPolynomialPair_comm r p]

theorem endpointPotentialPolynomialPair_smul_right
    (a : ℝ) (p q : ℝ[X]) :
    endpointPotentialPolynomialPair p (a • q) =
      a * endpointPotentialPolynomialPair p q := by
  rw [endpointPotentialPolynomialPair_comm p (a • q),
    endpointPotentialPolynomialPair_smul_left,
    endpointPotentialPolynomialPair_comm q p]

theorem endpointPotentialPolynomialPair_neg_right
    (p q : ℝ[X]) :
    endpointPotentialPolynomialPair p (-q) =
      -endpointPotentialPolynomialPair p q := by
  rw [endpointPotentialPolynomialPair_comm p (-q),
    endpointPotentialPolynomialPair_neg_left,
    endpointPotentialPolynomialPair_comm q p]

/-- For an odd polynomial, its global endpoint-potential pair is exactly
twice its positive-half weighted square mass. -/
theorem endpointPotentialPolynomialPair_self_eq_two_mul_positiveHalf
    (p : ℝ[X]) (hodd : Function.Odd fun x : ℝ ↦ p.eval x) :
    endpointPotentialPolynomialPair p p =
      2 * ∫ x : ℝ in 0..1,
        yoshidaEndpointPotential x * (p.eval x) ^ 2 := by
  have hfold := endpointPotential_eq_two_mul_positiveHalf
    (fun x : ℝ ↦ p.eval x) p.continuous (Or.inr hodd)
  simpa only [endpointPotentialPolynomialPair, pow_two, mul_assoc] using hfold

/-- Positive-half form of the preceding parity fold. -/
theorem integral_zero_one_endpointPotential_polynomial_sq_eq_half_pair
    (p : ℝ[X]) (hodd : Function.Odd fun x : ℝ ↦ p.eval x) :
    (∫ x : ℝ in 0..1,
        yoshidaEndpointPotential x * (p.eval x) ^ 2) =
      (1 / 2 : ℝ) * endpointPotentialPolynomialPair p p := by
  have h := endpointPotentialPolynomialPair_self_eq_two_mul_positiveHalf
    p hodd
  linarith

/-- Exact polynomial evaluation bridge for the odd `P₁` tail weight.
The only non-global term which is not an ordinary polynomial square integral
is the displayed reciprocal-strip integral. -/
theorem fourCellOddP1ExactTailWeight_polynomial_eq
    (p : ℝ[X]) (hodd : Function.Odd fun x : ℝ ↦ p.eval x) :
    fourCellOddP1ExactTailWeight (fun x : ℝ ↦ p.eval x) =
      (27 / 250 : ℝ) * (∫ x : ℝ in 0..3 / 5, (p.eval x) ^ 2) +
        (93 / 100 : ℝ) * endpointPotentialPolynomialPair p p +
        (6 / 5 : ℝ) *
          (∫ x : ℝ in 3 / 5..1, (p.eval x) ^ 2 / x) -
        (57 / 25 : ℝ) *
          (∫ x : ℝ in 3 / 5..1, (p.eval x) ^ 2) := by
  rw [fourCellOddP1ExactTailWeight,
    integral_zero_one_endpointPotential_polynomial_sq_eq_half_pair p hodd]
  ring

end

end ArithmeticHodge.Analysis.EndpointPotentialPolynomialPairBilinearStructural
