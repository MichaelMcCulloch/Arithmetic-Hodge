import ArithmeticHodge.Analysis.ShiftedLegendreBasis

set_option autoImplicit false

open Polynomial

namespace ArithmeticHodge.Analysis.ShiftedLegendreCenteredLowModes

noncomputable section

open ShiftedLegendreOrthogonality

/-!
# Centered shifted-Legendre low modes

The affine change of variables `t = (x + 1) / 2` carries the first three
shifted-Legendre polynomials on `[0,1]` to the corresponding centered
polynomials on `[-1,1]`.  These identities are exact polynomial identities;
they are closed symbolic identities, not precomputed numeric data.
-/

/-- The shifted-Legendre polynomial transported from `[0,1]` to `[-1,1]`
by `t = (x + 1) / 2`. -/
def centeredShiftedLegendreReal (n : ℕ) : ℝ[X] :=
  (shiftedLegendreReal n).comp ((2 : ℝ)⁻¹ • (X + 1))

@[simp]
theorem centeredShiftedLegendreReal_zero :
    centeredShiftedLegendreReal 0 = 1 := by
  simp [centeredShiftedLegendreReal, shiftedLegendreReal,
    Polynomial.shiftedLegendre]

@[simp]
theorem centeredShiftedLegendreReal_one :
    centeredShiftedLegendreReal 1 = -X := by
  apply Polynomial.funext
  intro x
  simp [centeredShiftedLegendreReal, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Finset.sum_range_succ,
    Polynomial.smul_eq_C_mul]
  ring

@[simp]
theorem centeredShiftedLegendreReal_two :
    centeredShiftedLegendreReal 2 =
      (2 : ℝ)⁻¹ • ((3 : ℝ) • X ^ 2 - 1) := by
  apply Polynomial.funext
  intro x
  simp [centeredShiftedLegendreReal, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Finset.sum_range_succ,
    Polynomial.smul_eq_C_mul]
  norm_num [Nat.choose]
  ring

theorem eval_centeredShiftedLegendreReal (n : ℕ) (x : ℝ) :
    (centeredShiftedLegendreReal n).eval x =
      (shiftedLegendreReal n).eval ((x + 1) / 2) := by
  simp [centeredShiftedLegendreReal, Polynomial.eval_comp,
    Polynomial.smul_eq_C_mul]
  congr 1
  ring

/-- Centered reflection acts on degree `n` by the exact Legendre parity
sign. -/
theorem eval_centeredShiftedLegendreReal_neg (n : ℕ) (x : ℝ) :
    (centeredShiftedLegendreReal n).eval (-x) =
      (-1 : ℝ) ^ n * (centeredShiftedLegendreReal n).eval x := by
  rw [eval_centeredShiftedLegendreReal,
    eval_centeredShiftedLegendreReal]
  simp only [shiftedLegendreReal, Polynomial.eval_map]
  change Polynomial.aeval ((-x + 1) / 2)
      (Polynomial.shiftedLegendre n) =
    (-1 : ℝ) ^ n *
      Polynomial.aeval ((x + 1) / 2) (Polynomial.shiftedLegendre n)
  convert Polynomial.shiftedLegendre_eval_symm n ((-x + 1) / 2) using 1;
    ring

/-- Every centered shifted-Legendre mode of even degree is an even
function. -/
theorem even_eval_centeredShiftedLegendreReal (n : ℕ) :
    Function.Even (fun x : ℝ ↦
      (centeredShiftedLegendreReal (2 * n)).eval x) := by
  intro x
  change (centeredShiftedLegendreReal (2 * n)).eval (-x) =
    (centeredShiftedLegendreReal (2 * n)).eval x
  rw [eval_centeredShiftedLegendreReal_neg]
  simp

@[simp]
theorem eval_centeredShiftedLegendreReal_zero (x : ℝ) :
    (centeredShiftedLegendreReal 0).eval x = 1 := by
  rw [centeredShiftedLegendreReal_zero]
  simp

@[simp]
theorem eval_centeredShiftedLegendreReal_one (x : ℝ) :
    (centeredShiftedLegendreReal 1).eval x = -x := by
  rw [centeredShiftedLegendreReal_one]
  simp

@[simp]
theorem eval_centeredShiftedLegendreReal_two (x : ℝ) :
    (centeredShiftedLegendreReal 2).eval x =
      (3 * x ^ 2 - 1) / 2 := by
  rw [centeredShiftedLegendreReal_two]
  simp [Polynomial.smul_eq_C_mul]
  ring

end

end ArithmeticHodge.Analysis.ShiftedLegendreCenteredLowModes
