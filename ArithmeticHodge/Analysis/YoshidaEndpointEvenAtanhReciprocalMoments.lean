import ArithmeticHodge.Analysis.YoshidaEndpointEvenAtanhReciprocalMajorant

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenAtanhReciprocalMoments

open YoshidaEndpointEvenAtanhReciprocalMajorant
open YoshidaEndpointEvenStructuralReduction

noncomputable section

/-!
# Exact moments of the reciprocal transformed tail-weight majorant

The reciprocal majorant has a positive Bernstein presentation on `0 ≤ y ≤ 1`.
Its even moments therefore reduce structurally to the elementary interval
integrals of monomials.
-/

/-- Exact degree-three Bernstein presentation of the reciprocal majorant. -/
theorem atanhTailWeightReciprocalMajorantPolynomial_eq_bernstein (y : ℝ) :
    atanhTailWeightReciprocalMajorantPolynomial y =
      (60 / 41 : ℝ) * (1 - y) ^ 3 +
        (5580 / 1681 : ℝ) * y * (1 - y) ^ 2 +
        (172080 / 68921 : ℝ) * y ^ 2 * (1 - y) +
        (4279422 / 8615125 : ℝ) * y ^ 3 := by
  unfold atanhTailWeightReciprocalMajorantPolynomial
  ring

/-- The reciprocal majorant is manifestly nonnegative on the centered
interval from its positive Bernstein presentation. -/
theorem atanhTailWeightReciprocalMajorant_nonneg_on_Icc
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    0 ≤ atanhTailWeightReciprocalMajorant x := by
  have hxAbs : |x| ≤ 1 := abs_le.mpr hx
  have hxSq : x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one x).2 hxAbs
  have hxSqNonneg : 0 ≤ x ^ 2 := sq_nonneg x
  unfold atanhTailWeightReciprocalMajorant
  rw [atanhTailWeightReciprocalMajorantPolynomial_eq_bernstein]
  have hone : 0 ≤ 1 - x ^ 2 := by linarith
  positivity

private theorem continuous_atanhTailWeightReciprocalMajorant :
    Continuous atanhTailWeightReciprocalMajorant := by
  unfold atanhTailWeightReciprocalMajorant
    atanhTailWeightReciprocalMajorantPolynomial
  fun_prop

private theorem integral_even_pow (n : ℕ) :
    (∫ x : ℝ in -1..1, x ^ (2 * n)) =
      2 / (2 * (n : ℝ) + 1) := by
  rw [integral_pow]
  norm_num [pow_succ, pow_mul]

/-- Every even moment of the reciprocal majorant is an explicit rational
combination of four elementary monomial moments. -/
theorem integral_pow_mul_atanhTailWeightReciprocalMajorant (n : ℕ) :
    (∫ x : ℝ in -1..1,
      x ^ (2 * n) * atanhTailWeightReciprocalMajorant x) =
        2 * ((60 / 41 : ℝ) / (2 * (n : ℝ) + 1) -
          (1800 / 1681 : ℝ) / (2 * (n : ℝ) + 3) +
          (17100 / 68921 : ℝ) / (2 * (n : ℝ) + 5) -
          (18 / 125 : ℝ) / (2 * (n : ℝ) + 7)) := by
  have h0 : IntervalIntegrable
      (fun x : ℝ ↦ (60 / 41 : ℝ) * x ^ (2 * n)) volume (-1) 1 := by
    exact (by fun_prop : Continuous
      (fun x : ℝ ↦ (60 / 41 : ℝ) * x ^ (2 * n))).intervalIntegrable (-1) 1
  have h1 : IntervalIntegrable
      (fun x : ℝ ↦ (1800 / 1681 : ℝ) * x ^ (2 * (n + 1)))
        volume (-1) 1 := by
    exact (by fun_prop : Continuous
      (fun x : ℝ ↦
        (1800 / 1681 : ℝ) * x ^ (2 * (n + 1)))).intervalIntegrable (-1) 1
  have h2 : IntervalIntegrable
      (fun x : ℝ ↦ (17100 / 68921 : ℝ) * x ^ (2 * (n + 2)))
        volume (-1) 1 := by
    exact (by fun_prop : Continuous
      (fun x : ℝ ↦
        (17100 / 68921 : ℝ) * x ^ (2 * (n + 2)))).intervalIntegrable (-1) 1
  have h3 : IntervalIntegrable
      (fun x : ℝ ↦ (18 / 125 : ℝ) * x ^ (2 * (n + 3)))
        volume (-1) 1 := by
    exact (by fun_prop : Continuous
      (fun x : ℝ ↦
        (18 / 125 : ℝ) * x ^ (2 * (n + 3)))).intervalIntegrable (-1) 1
  rw [show (fun x : ℝ ↦
      x ^ (2 * n) * atanhTailWeightReciprocalMajorant x) =
      fun x ↦
        ((60 / 41 : ℝ) * x ^ (2 * n) -
          (1800 / 1681 : ℝ) * x ^ (2 * (n + 1)) +
          (17100 / 68921 : ℝ) * x ^ (2 * (n + 2))) -
          (18 / 125 : ℝ) * x ^ (2 * (n + 3)) by
    funext x
    unfold atanhTailWeightReciprocalMajorant
      atanhTailWeightReciprocalMajorantPolynomial
    simp only [Nat.mul_add, pow_add]
    ring]
  rw [intervalIntegral.integral_sub ((h0.sub h1).add h2) h3,
    intervalIntegral.integral_add (h0.sub h1) h2,
    intervalIntegral.integral_sub h0 h1,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_even_pow n, integral_even_pow (n + 1),
    integral_even_pow (n + 2), integral_even_pow (n + 3)]
  push_cast
  ring

/-- Zeroth moment `J₀` of the reciprocal majorant. -/
theorem integral_atanhTailWeightReciprocalMajorant :
    (∫ x : ℝ in -1..1, atanhTailWeightReciprocalMajorant x) =
      136958844 / 60305875 := by
  have h := integral_pow_mul_atanhTailWeightReciprocalMajorant 0
  norm_num at h ⊢
  exact h

/-- Second moment `J₁` of the reciprocal majorant. -/
theorem integral_sq_mul_atanhTailWeightReciprocalMajorant :
    (∫ x : ℝ in -1..1,
      x ^ 2 * atanhTailWeightReciprocalMajorant x) =
        35350212 / 60305875 := by
  have h := integral_pow_mul_atanhTailWeightReciprocalMajorant 1
  norm_num at h ⊢
  exact h

/-- Fourth moment `J₂` of the reciprocal majorant. -/
theorem integral_pow_four_mul_atanhTailWeightReciprocalMajorant :
    (∫ x : ℝ in -1..1,
      x ^ 4 * atanhTailWeightReciprocalMajorant x) =
        204567908 / 663364625 := by
  have h := integral_pow_mul_atanhTailWeightReciprocalMajorant 2
  norm_num at h ⊢
  exact h

/-- Exact mixed moment against the centered degree-two Legendre mode. -/
theorem integral_atanhTailWeightReciprocalMajorant_mul_centeredEvenP2 :
    (∫ x : ℝ in -1..1,
      atanhTailWeightReciprocalMajorant x * centeredEvenP2 x) =
        -(15454104 / 60305875 : ℝ) := by
  rw [show (fun x : ℝ ↦
      atanhTailWeightReciprocalMajorant x * centeredEvenP2 x) =
      fun x ↦ (3 / 2 : ℝ) *
          (x ^ 2 * atanhTailWeightReciprocalMajorant x) -
        (1 / 2 : ℝ) * atanhTailWeightReciprocalMajorant x by
    funext x
    unfold centeredEvenP2
    ring]
  have h2 : IntervalIntegrable
      (fun x : ℝ ↦ (3 / 2 : ℝ) *
        (x ^ 2 * atanhTailWeightReciprocalMajorant x)) volume (-1) 1 :=
    (((continuous_id.pow 2).mul
      continuous_atanhTailWeightReciprocalMajorant).const_mul (3 / 2 : ℝ))
        |>.intervalIntegrable (-1) 1
  have h0 : IntervalIntegrable
      (fun x : ℝ ↦ (1 / 2 : ℝ) *
        atanhTailWeightReciprocalMajorant x) volume (-1) 1 :=
    (continuous_atanhTailWeightReciprocalMajorant.const_mul (1 / 2 : ℝ))
      |>.intervalIntegrable (-1) 1
  rw [intervalIntegral.integral_sub h2 h0,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_sq_mul_atanhTailWeightReciprocalMajorant,
    integral_atanhTailWeightReciprocalMajorant]
  norm_num

/-- Exact quadratic moment against the centered degree-two Legendre mode. -/
theorem integral_atanhTailWeightReciprocalMajorant_mul_centeredEvenP2_sq :
    (∫ x : ℝ in -1..1,
      atanhTailWeightReciprocalMajorant x * centeredEvenP2 x ^ 2) =
        253636116 / 663364625 := by
  rw [show (fun x : ℝ ↦
      atanhTailWeightReciprocalMajorant x * centeredEvenP2 x ^ 2) =
      fun x ↦ (9 / 4 : ℝ) *
          (x ^ 4 * atanhTailWeightReciprocalMajorant x) -
        (3 / 2 : ℝ) *
          (x ^ 2 * atanhTailWeightReciprocalMajorant x) +
        (1 / 4 : ℝ) * atanhTailWeightReciprocalMajorant x by
    funext x
    unfold centeredEvenP2
    ring]
  have h4 : IntervalIntegrable
      (fun x : ℝ ↦ (9 / 4 : ℝ) *
        (x ^ 4 * atanhTailWeightReciprocalMajorant x)) volume (-1) 1 := by
    exact ((((continuous_id.pow 4).mul
      continuous_atanhTailWeightReciprocalMajorant).const_mul (9 / 4 : ℝ)))
        |>.intervalIntegrable (-1) 1
  have h2 : IntervalIntegrable
      (fun x : ℝ ↦ (3 / 2 : ℝ) *
        (x ^ 2 * atanhTailWeightReciprocalMajorant x)) volume (-1) 1 := by
    exact ((((continuous_id.pow 2).mul
      continuous_atanhTailWeightReciprocalMajorant).const_mul (3 / 2 : ℝ)))
        |>.intervalIntegrable (-1) 1
  have h0 : IntervalIntegrable
      (fun x : ℝ ↦ (1 / 4 : ℝ) *
        atanhTailWeightReciprocalMajorant x) volume (-1) 1 := by
    exact ((continuous_atanhTailWeightReciprocalMajorant.const_mul (1 / 4 : ℝ))
      |>.intervalIntegrable (-1) 1)
  rw [intervalIntegral.integral_add (h4.sub h2) h0,
    intervalIntegral.integral_sub h4 h2,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_pow_four_mul_atanhTailWeightReciprocalMajorant,
    integral_sq_mul_atanhTailWeightReciprocalMajorant,
    integral_atanhTailWeightReciprocalMajorant]
  norm_num

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenAtanhReciprocalMoments
