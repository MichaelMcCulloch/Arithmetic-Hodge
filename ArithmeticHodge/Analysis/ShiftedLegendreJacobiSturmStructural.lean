import ArithmeticHodge.Analysis.ShiftedLegendreCenteredLowModes

set_option autoImplicit false

open Polynomial

namespace ArithmeticHodge.Analysis.ShiftedLegendreJacobiSturmStructural

open ShiftedLegendreOrthogonality
open ShiftedLegendreCenteredLowModes

noncomputable section

/-!
# All-degree Jacobi and Sturm identities for shifted Legendre polynomials

The identities in this file are proved uniformly in the degree from the
closed coefficient formula.  They are the algebraic input for structural
endpoint-potential Gram formulas; no finite list of modes is expanded.
-/

/-- The closed coefficient formula after transport from `ℤ[X]` to
`ℝ[X]`. -/
theorem coeff_shiftedLegendreReal (n k : ℕ) :
    (shiftedLegendreReal n).coeff k =
      (-1 : ℝ) ^ k * (n.choose k : ℝ) * ((n + k).choose n : ℝ) := by
  simp [shiftedLegendreReal, Polynomial.coeff_shiftedLegendre]

/-- Multiplication by `X` after differentiation has coefficient `k pₖ` in
degree `k`, including the constant-coefficient boundary case. -/
theorem coeff_X_mul_derivative (p : ℝ[X]) (k : ℕ) :
    (X * derivative p).coeff k = (k : ℝ) * p.coeff k := by
  cases k with
  | zero => simp
  | succ k =>
      rw [show k + 1 = k.succ by omega, coeff_X_mul, coeff_derivative]
      push_cast
      ring

/-- Coefficient formula for the shifted Sturm operator. -/
theorem coeff_derivative_X_mul_one_sub_X_mul_derivative
    (p : ℝ[X]) (k : ℕ) :
    (derivative (X * (1 - X) * derivative p)).coeff k =
      (k + 1 : ℝ) ^ 2 * p.coeff (k + 1) -
        (k : ℝ) * (k + 1 : ℝ) * p.coeff k := by
  have hpoly : X * (1 - X) * derivative p =
      X * derivative p - X * (X * derivative p) := by
    ring
  rw [hpoly, coeff_derivative, coeff_sub, coeff_X_mul,
    coeff_derivative, coeff_X_mul, coeff_X_mul_derivative]
  ring

/-- Adjacent coefficients of a shifted Legendre polynomial satisfy the
uniform first-order relation underlying its Sturm equation. -/
theorem shiftedLegendreReal_coeff_succ (n k : ℕ) :
    (k + 1 : ℝ) ^ 2 * (shiftedLegendreReal n).coeff (k + 1) =
      -(((n : ℝ) * (n + 1 : ℝ) - (k : ℝ) * (k + 1 : ℝ)) *
        (shiftedLegendreReal n).coeff k) := by
  by_cases hkn : k ≤ n
  · have hleft := Nat.choose_succ_right_eq n k
    have hright := Nat.choose_mul_succ_eq (n + k) n
    have hsub : n + k + 1 - n = k + 1 := by omega
    rw [hsub] at hright
    have hnat :
        (k + 1) ^ 2 * (n.choose (k + 1) * (n + k + 1).choose n) =
          (n - k) * (n + k + 1) *
            (n.choose k * (n + k).choose n) := by
      calc
        (k + 1) ^ 2 * (n.choose (k + 1) * (n + k + 1).choose n) =
            (n.choose (k + 1) * (k + 1)) *
              ((n + k + 1).choose n * (k + 1)) := by ring
        _ = (n.choose k * (n - k)) *
              ((n + k).choose n * (n + k + 1)) := by
            rw [hleft, hright]
        _ = (n - k) * (n + k + 1) *
              (n.choose k * (n + k).choose n) := by ring
    have hreal := congrArg (fun z : ℕ ↦ (z : ℝ)) hnat
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add,
      Nat.cast_one] at hreal
    have hfactor :
        ((n - k : ℕ) : ℝ) * ((n : ℝ) + (k : ℝ) + 1) =
          (n : ℝ) * (n + 1 : ℝ) -
            (k : ℝ) * (k + 1 : ℝ) := by
      rw [Nat.cast_sub hkn]
      ring
    rw [coeff_shiftedLegendreReal, coeff_shiftedLegendreReal, pow_succ]
    calc
      (k + 1 : ℝ) ^ 2 *
          ((-1 : ℝ) ^ k * -1 * (n.choose (k + 1) : ℝ) *
            ((n + (k + 1)).choose n : ℝ)) =
          -((-1 : ℝ) ^ k) *
            ((k + 1 : ℝ) ^ 2 *
              ((n.choose (k + 1) : ℝ) *
                ((n + k + 1).choose n : ℝ))) := by
            rw [show n + (k + 1) = n + k + 1 by omega]
            ring
      _ = -((-1 : ℝ) ^ k) *
            (((n - k : ℕ) : ℝ) * ((n : ℝ) + (k : ℝ) + 1) *
              ((n.choose k : ℝ) * ((n + k).choose n : ℝ))) := by
            rw [hreal]
      _ = -(((n : ℝ) * (n + 1 : ℝ) -
              (k : ℝ) * (k + 1 : ℝ)) *
            ((-1 : ℝ) ^ k * (n.choose k : ℝ) *
              ((n + k).choose n : ℝ))) := by
            rw [hfactor]
            ring
  · have hnk : n < k := Nat.lt_of_not_ge hkn
    have hnk1 : n < k + 1 := hnk.trans (Nat.lt_succ_self k)
    rw [coeff_shiftedLegendreReal, coeff_shiftedLegendreReal,
      Nat.choose_eq_zero_of_lt hnk, Nat.choose_eq_zero_of_lt hnk1]
    ring

/-- Every shifted Legendre polynomial is an eigenvector of the shifted
Sturm operator, uniformly in its degree. -/
theorem derivative_X_mul_one_sub_X_mul_derivative_shiftedLegendreReal
    (n : ℕ) :
    derivative (X * (1 - X) * derivative (shiftedLegendreReal n)) =
      -(((n : ℝ) * (n + 1 : ℝ)) • shiftedLegendreReal n) := by
  ext k
  rw [coeff_derivative_X_mul_one_sub_X_mul_derivative,
    shiftedLegendreReal_coeff_succ]
  simp only [coeff_neg, coeff_smul, smul_eq_mul]
  ring

/-- The centered Legendre Sturm operator on `[-1,1]`. -/
def centeredLegendreSturm (p : ℝ[X]) : ℝ[X] :=
  -derivative ((1 - X ^ 2) * derivative p)

/-- Affine transport conjugates the shifted and centered Sturm operators. -/
theorem centeredLegendreSturm_comp_centering (p : ℝ[X]) :
    centeredLegendreSturm
        (p.comp ((2 : ℝ)⁻¹ • (X + 1))) =
      -(derivative (X * (1 - X) * derivative p)).comp
        ((2 : ℝ)⁻¹ • (X + 1)) := by
  apply Polynomial.funext
  intro x
  simp [centeredLegendreSturm, Polynomial.derivative_comp,
    Polynomial.smul_eq_C_mul]
  ring

/-- Every centered shifted-Legendre polynomial is an eigenvector of the
centered Sturm operator, uniformly in its degree. -/
theorem centeredLegendreSturm_centeredShiftedLegendreReal (n : ℕ) :
    centeredLegendreSturm (centeredShiftedLegendreReal n) =
      ((n : ℝ) * (n + 1 : ℝ)) • centeredShiftedLegendreReal n := by
  rw [centeredShiftedLegendreReal,
    centeredLegendreSturm_comp_centering,
    derivative_X_mul_one_sub_X_mul_derivative_shiftedLegendreReal]
  apply Polynomial.funext
  intro x
  simp [Polynomial.smul_eq_C_mul]

end

end ArithmeticHodge.Analysis.ShiftedLegendreJacobiSturmStructural
