import ArithmeticHodge.Analysis.ShiftedLegendreJacobiRecurrenceStructural
import ArithmeticHodge.Analysis.YoshidaEndpointPotentialLegendreOffDiagonalStructural
import Mathlib.Topology.Algebra.Polynomial

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.ShiftedLegendreCenteredL2Structural

open ShiftedLegendreCenteredLowModes
open ShiftedLegendreJacobiRecurrenceStructural
open YoshidaEndpointPotentialLegendreOffDiagonalStructural

noncomputable section

/-!
# All-degree centered Legendre L2 Gram

The centered Jacobi recurrence and off-diagonal orthogonality determine the
ordinary `L²([-1,1])` norm in every degree.  This gives the full centered
Legendre Gram matrix without expanding any mode.
-/

/-- Ordinary polynomial pairing on the centered interval. -/
def centeredPolynomialPair (p q : ℝ[X]) : ℝ :=
  ∫ x : ℝ in -1..1, p.eval x * q.eval x

/-- Ordinary centered Legendre diagonal entry. -/
def centeredLegendreL2Diagonal (n : ℕ) : ℝ :=
  centeredPolynomialPair
    (centeredShiftedLegendreReal n)
    (centeredShiftedLegendreReal n)

private theorem intervalIntegrable_centeredPolynomialPair
    (p q : ℝ[X]) :
    IntervalIntegrable (fun x : ℝ ↦ p.eval x * q.eval x)
      volume (-1) 1 :=
  (p.continuous.mul q.continuous).intervalIntegrable (-1) 1

private theorem centeredPolynomialPair_smul_left
    (c : ℝ) (p q : ℝ[X]) :
    centeredPolynomialPair (c • p) q =
      c * centeredPolynomialPair p q := by
  unfold centeredPolynomialPair
  rw [show (fun x : ℝ ↦ (c • p).eval x * q.eval x) =
      fun x ↦ c * (p.eval x * q.eval x) by
    funext x
    simp only [Polynomial.eval_smul, smul_eq_mul]
    ring,
    intervalIntegral.integral_const_mul]

private theorem centeredPolynomialPair_sub_left
    (p r q : ℝ[X]) :
    centeredPolynomialPair (p - r) q =
      centeredPolynomialPair p q - centeredPolynomialPair r q := by
  unfold centeredPolynomialPair
  rw [show (fun x : ℝ ↦ (p - r).eval x * q.eval x) =
      fun x ↦ p.eval x * q.eval x - r.eval x * q.eval x by
    funext x
    simp only [Polynomial.eval_sub]
    ring,
    intervalIntegral.integral_sub
      (intervalIntegrable_centeredPolynomialPair p q)
      (intervalIntegrable_centeredPolynomialPair r q)]

private theorem centeredPolynomialPair_neg_left
    (p q : ℝ[X]) :
    centeredPolynomialPair (-p) q = -centeredPolynomialPair p q := by
  unfold centeredPolynomialPair
  rw [show (fun x : ℝ ↦ (-p).eval x * q.eval x) =
      fun x ↦ -(p.eval x * q.eval x) by
    funext x
    simp only [Polynomial.eval_neg]
    ring,
    intervalIntegral.integral_neg]

theorem centeredPolynomialPair_comm (p q : ℝ[X]) :
    centeredPolynomialPair p q = centeredPolynomialPair q p := by
  unfold centeredPolynomialPair
  apply intervalIntegral.integral_congr
  intro x _hx
  ring

private theorem centeredPolynomialPair_smul_right
    (c : ℝ) (p q : ℝ[X]) :
    centeredPolynomialPair p (c • q) =
      c * centeredPolynomialPair p q := by
  calc
    _ = centeredPolynomialPair (c • q) p := centeredPolynomialPair_comm _ _
    _ = c * centeredPolynomialPair q p :=
      centeredPolynomialPair_smul_left _ _ _
    _ = _ := by rw [centeredPolynomialPair_comm q p]

private theorem centeredPolynomialPair_sub_right
    (p q r : ℝ[X]) :
    centeredPolynomialPair p (q - r) =
      centeredPolynomialPair p q - centeredPolynomialPair p r := by
  calc
    _ = centeredPolynomialPair (q - r) p := centeredPolynomialPair_comm _ _
    _ = centeredPolynomialPair q p - centeredPolynomialPair r p :=
      centeredPolynomialPair_sub_left _ _ _
    _ = _ := by
      rw [centeredPolynomialPair_comm q p,
        centeredPolynomialPair_comm r p]

private theorem centeredPolynomialPair_neg_right
    (p q : ℝ[X]) :
    centeredPolynomialPair p (-q) = -centeredPolynomialPair p q := by
  calc
    _ = centeredPolynomialPair (-q) p := centeredPolynomialPair_comm _ _
    _ = -centeredPolynomialPair q p := centeredPolynomialPair_neg_left _ _
    _ = _ := by rw [centeredPolynomialPair_comm q p]

/-- Multiplication by the centered coordinate is self-adjoint for the
ordinary polynomial pairing. -/
theorem centeredPolynomialPair_X (p q : ℝ[X]) :
    centeredPolynomialPair (X * p) q =
      centeredPolynomialPair p (X * q) := by
  unfold centeredPolynomialPair
  apply intervalIntegral.integral_congr
  intro x _hx
  simp only [Polynomial.eval_mul, Polynomial.eval_X]
  ring

/-- Distinct centered shifted-Legendre modes are orthogonal. -/
theorem centeredPolynomialPair_legendre_eq_zero
    {m n : ℕ} (hmn : m ≠ n) :
    centeredPolynomialPair
      (centeredShiftedLegendreReal m)
      (centeredShiftedLegendreReal n) = 0 := by
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · exact integral_eval_mul_centeredShiftedLegendreReal_eq_zero
      n (centeredShiftedLegendreReal m)
      ((natDegree_centeredShiftedLegendreReal_le m).trans_lt hlt)
  · rw [centeredPolynomialPair_comm]
    exact integral_eval_mul_centeredShiftedLegendreReal_eq_zero
      m (centeredShiftedLegendreReal n)
      ((natDegree_centeredShiftedLegendreReal_le n).trans_lt hgt)

/-- The centered Legendre diagonal starts at total interval mass two. -/
theorem centeredLegendreL2Diagonal_zero :
    centeredLegendreL2Diagonal 0 = 2 := by
  norm_num [centeredLegendreL2Diagonal, centeredPolynomialPair]

/-- Uniform recurrence for the ordinary centered Legendre diagonal. -/
theorem centeredLegendreL2Diagonal_succ (n : ℕ) :
    (2 * (n : ℝ) + 3) * centeredLegendreL2Diagonal (n + 1) =
      (2 * (n : ℝ) + 1) * centeredLegendreL2Diagonal n := by
  let Q : ℕ → ℝ[X] := centeredShiftedLegendreReal
  let P : ℝ[X] → ℝ[X] → ℝ := centeredPolynomialPair
  let D : ℕ → ℝ := fun k ↦ P (Q k) (Q k)
  let M : ℕ → ℕ → ℝ := fun i j ↦ P (Q i) (Q j)
  let K : ℝ := P (X * Q n) (Q (n + 1))
  have hN :
      (((n + 1 : ℕ) : ℝ) * D (n + 1)) =
        -(((2 * n + 1 : ℕ) : ℝ) * K) -
          (n : ℝ) * M (n - 1) (n + 1) := by
    have h := congrArg
      (fun p : ℝ[X] ↦ centeredPolynomialPair p
        (centeredShiftedLegendreReal (n + 1)))
      (centeredShiftedLegendreReal_recurrence n)
    simp only [centeredPolynomialPair_smul_left,
      centeredPolynomialPair_sub_left,
      centeredPolynomialPair_neg_left] at h
    simpa only [Q, P, D, M, K] using h
  have hNext :
      (((n + 2 : ℕ) : ℝ) * M n (n + 2)) =
        -(((2 * n + 3 : ℕ) : ℝ) * K) -
          (((n + 1 : ℕ) : ℝ) * D n) := by
    have h := congrArg
      (fun p : ℝ[X] ↦ centeredPolynomialPair
        (centeredShiftedLegendreReal n) p)
      (centeredShiftedLegendreReal_recurrence (n + 1))
    simp only [centeredPolynomialPair_smul_right,
      centeredPolynomialPair_sub_right,
      centeredPolynomialPair_neg_right] at h
    rw [← centeredPolynomialPair_X
      (centeredShiftedLegendreReal n)
      (centeredShiftedLegendreReal (n + 1))] at h
    simpa only [Q, P, D, M, K, Nat.add_sub_cancel,
      show n + 1 + 1 = n + 2 by omega,
      show 2 * (n + 1) + 1 = 2 * n + 3 by omega] using h
  have hprev : M (n - 1) (n + 1) = 0 := by
    apply centeredPolynomialPair_legendre_eq_zero
    omega
  have hnext : M n (n + 2) = 0 := by
    apply centeredPolynomialPair_legendre_eq_zero
    omega
  rw [hprev] at hN
  rw [hnext] at hNext
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hN hNext
  have helim :
      (2 * (n : ℝ) + 3) * (n + 1 : ℝ) * D (n + 1) =
        (2 * (n : ℝ) + 1) * (n + 1 : ℝ) * D n := by
    linear_combination
      (2 * (n : ℝ) + 3) * hN -
        (2 * (n : ℝ) + 1) * hNext
  have hscaled :
      (n + 1 : ℝ) *
        ((2 * (n : ℝ) + 3) * D (n + 1) -
          (2 * (n : ℝ) + 1) * D n) = 0 := by
    calc
      _ = (2 * (n : ℝ) + 3) * (n + 1 : ℝ) * D (n + 1) -
          (2 * (n : ℝ) + 1) * (n + 1 : ℝ) * D n := by ring
      _ = 0 := by rw [helim, sub_self]
  have hdiff :
      (2 * (n : ℝ) + 3) * D (n + 1) -
        (2 * (n : ℝ) + 1) * D n = 0 :=
    (mul_eq_zero.mp hscaled).resolve_left (by positivity)
  change (2 * (n : ℝ) + 3) * D (n + 1) =
    (2 * (n : ℝ) + 1) * D n
  linarith

/-- Closed all-degree squared norm of a centered shifted-Legendre mode. -/
theorem centeredLegendreL2Diagonal_closed (n : ℕ) :
    centeredLegendreL2Diagonal n = 2 / (2 * (n : ℝ) + 1) := by
  induction n with
  | zero => simpa using centeredLegendreL2Diagonal_zero
  | succ n ih =>
      have hrec := centeredLegendreL2Diagonal_succ n
      rw [ih] at hrec
      have hden : 2 * (n : ℝ) + 3 ≠ 0 := by positivity
      norm_num only [Nat.cast_add, Nat.cast_one] at ⊢
      rw [show 2 * ((n : ℝ) + 1) + 1 =
        2 * (n : ℝ) + 3 by ring]
      apply (eq_div_iff hden).2
      have hprevden : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
      have hcancel :
          (2 * (n : ℝ) + 1) * (2 / (2 * (n : ℝ) + 1)) = 2 := by
        field_simp [hprevden]
      rw [hcancel] at hrec
      simpa only [mul_comm] using hrec

/-- Full ordinary centered Legendre Gram matrix. -/
theorem centeredLegendreL2Gram (m n : ℕ) :
    centeredPolynomialPair
        (centeredShiftedLegendreReal m)
        (centeredShiftedLegendreReal n) =
      if m = n then 2 / (2 * (n : ℝ) + 1) else 0 := by
  by_cases hmn : m = n
  · subst m
    rw [if_pos rfl]
    exact centeredLegendreL2Diagonal_closed n
  · rw [if_neg hmn]
    exact centeredPolynomialPair_legendre_eq_zero hmn

end

end ArithmeticHodge.Analysis.ShiftedLegendreCenteredL2Structural
