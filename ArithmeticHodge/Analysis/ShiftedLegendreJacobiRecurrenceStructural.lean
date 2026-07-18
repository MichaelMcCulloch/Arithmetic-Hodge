import ArithmeticHodge.Analysis.ShiftedLegendreJacobiSturmStructural
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.Polynomial.Eval.SMul

set_option autoImplicit false

open Polynomial

namespace ArithmeticHodge.Analysis.ShiftedLegendreJacobiRecurrenceStructural

open ShiftedLegendreCenteredLowModes
open ShiftedLegendreJacobiSturmStructural
open ShiftedLegendreOrthogonality

noncomputable section

/-!
# All-degree Jacobi recurrence for shifted Legendre polynomials

The coefficient magnitudes satisfy one binomial identity.  This proves the
three-term recurrence uniformly in the degree, without expanding any mode.
-/

/-- The unsigned magnitude of coefficient `k` in shifted Legendre degree
`d`. -/
def shiftedLegendreMagnitude (d k : ℕ) : ℕ :=
  d.choose k * (d + k).choose d

private theorem magnitude_degree_succ (n k : ℕ) :
    shiftedLegendreMagnitude (n + 2) k * (n + 2 - k) =
      shiftedLegendreMagnitude (n + 1) k * (n + k + 2) := by
  have hchoose := Nat.choose_mul_succ_eq (n + 1) k
  have hadd := Nat.add_one_mul_choose_eq (n + k + 1) (n + 1)
  have hadd' :
      (n + k + 2) * (n + k + 1).choose (n + 1) =
        (n + k + 2).choose (n + 2) * (n + 2) := by
    simpa only [show n + k + 1 + 1 = n + k + 2 by omega,
      show n + 1 + 1 = n + 2 by omega] using hadd
  unfold shiftedLegendreMagnitude
  calc
    (n + 2).choose k * (n + 2 + k).choose (n + 2) * (n + 2 - k) =
        ((n + 2).choose k * (n + 2 - k)) *
          (n + k + 2).choose (n + 2) := by
      rw [show n + 2 + k = n + k + 2 by omega]
      ring
    _ = ((n + 1).choose k * (n + 2)) *
          (n + k + 2).choose (n + 2) := by rw [← hchoose]
    _ = (n + 1).choose k *
          ((n + k + 2).choose (n + 2) * (n + 2)) := by ring
    _ = (n + 1).choose k *
          ((n + k + 2) * (n + k + 1).choose (n + 1)) := by
      rw [← hadd']
    _ = (n + 1).choose k * (n + 1 + k).choose (n + 1) *
          (n + k + 2) := by
      rw [show n + 1 + k = n + k + 1 by omega]
      ring

private theorem magnitude_degree_pred (n k : ℕ) :
    shiftedLegendreMagnitude n k * (n + k + 1) =
      shiftedLegendreMagnitude (n + 1) k * (n + 1 - k) := by
  have hchoose := Nat.choose_mul_succ_eq n k
  have hadd := Nat.add_one_mul_choose_eq (n + k) n
  unfold shiftedLegendreMagnitude
  calc
    n.choose k * (n + k).choose n * (n + k + 1) =
        n.choose k * ((n + k + 1) * (n + k).choose n) := by ring
    _ = n.choose k * ((n + k + 1).choose (n + 1) * (n + 1)) := by
      rw [hadd]
    _ = (n.choose k * (n + 1)) *
          (n + k + 1).choose (n + 1) := by ring
    _ = ((n + 1).choose k * (n + 1 - k)) *
          (n + k + 1).choose (n + 1) := by rw [hchoose]
    _ = (n + 1).choose k * (n + 1 + k).choose (n + 1) *
          (n + 1 - k) := by
      rw [show n + 1 + k = n + k + 1 by omega]
      ring

private theorem magnitude_index_pred
    (n k : ℕ) (hk : 0 < k) :
    shiftedLegendreMagnitude (n + 1) (k - 1) * (n + 2 - k) *
        (n + k + 1) =
      shiftedLegendreMagnitude (n + 1) k * k ^ 2 := by
  have hchoose := Nat.choose_succ_right_eq (n + 1) (k - 1)
  have hsecond := Nat.choose_mul_succ_eq (n + k) (n + 1)
  have hkm : k - 1 + 1 = k := by omega
  have hsub : n + k + 1 - (n + 1) = k := by omega
  have hsubChoose : n + 1 - (k - 1) = n + 2 - k := by omega
  rw [hkm] at hchoose
  rw [hsubChoose] at hchoose
  rw [hsub] at hsecond
  unfold shiftedLegendreMagnitude
  calc
    (n + 1).choose (k - 1) * (n + 1 + (k - 1)).choose (n + 1) *
          (n + 2 - k) * (n + k + 1) =
        ((n + 1).choose (k - 1) * (n + 2 - k)) *
          ((n + k).choose (n + 1) * (n + k + 1)) := by
      rw [show n + 1 + (k - 1) = n + k by omega]
      ring
    _ = ((n + 1).choose k * k) *
          ((n + k + 1).choose (n + 1) * k) := by
      rw [← hchoose, hsecond]
    _ = (n + 1).choose k * (n + 1 + k).choose (n + 1) * k ^ 2 := by
      ring

/-- The unsigned coefficients satisfy the three-term recurrence away from
the constant-coefficient boundary. -/
theorem shiftedLegendreMagnitude_threeTerm
    (n k : ℕ) (hk : 0 < k) :
    (n + 2) * shiftedLegendreMagnitude (n + 2) k +
        (n + 1) * shiftedLegendreMagnitude n k =
      (2 * n + 3) *
        (shiftedLegendreMagnitude (n + 1) k +
          2 * shiftedLegendreMagnitude (n + 1) (k - 1)) := by
  by_cases hkn : k ≤ n + 1
  · have ha : 0 < n + 2 - k := by omega
    have hb : 0 < n + k + 1 := by omega
    have hsucc := magnitude_degree_succ n k
    have hpred := magnitude_degree_pred n k
    have hindex := magnitude_index_pred n k hk
    have hscalar :
        (n + 2) * (n + k + 2) * (n + k + 1) +
            (n + 1) * (n + 1 - k) * (n + 2 - k) =
          (2 * n + 3) *
            ((n + 2 - k) * (n + k + 1) + 2 * k ^ 2) := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := Nat.exists_eq_add_of_le' hk
      have hjn : j ≤ n := by omega
      obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hjn
      have hsubOne : j + q + 1 - (j + 1) = q := by omega
      have hsubTwo : j + q + 2 - (j + 1) = q + 1 := by omega
      rw [hsubOne, hsubTwo]
      ring
    apply Nat.mul_right_cancel (Nat.mul_pos ha hb)
    calc
      ((n + 2) * shiftedLegendreMagnitude (n + 2) k +
            (n + 1) * shiftedLegendreMagnitude n k) *
          ((n + 2 - k) * (n + k + 1)) =
          (n + 2) *
              (shiftedLegendreMagnitude (n + 2) k * (n + 2 - k)) *
              (n + k + 1) +
            (n + 1) *
              (shiftedLegendreMagnitude n k * (n + k + 1)) *
              (n + 2 - k) := by ring
      _ = (n + 2) *
              (shiftedLegendreMagnitude (n + 1) k * (n + k + 2)) *
              (n + k + 1) +
            (n + 1) *
              (shiftedLegendreMagnitude (n + 1) k * (n + 1 - k)) *
              (n + 2 - k) := by rw [hsucc, hpred]
      _ = shiftedLegendreMagnitude (n + 1) k *
          ((2 * n + 3) *
            ((n + 2 - k) * (n + k + 1) + 2 * k ^ 2)) := by
        rw [← hscalar]
        ring
      _ = (2 * n + 3) *
            (shiftedLegendreMagnitude (n + 1) k *
                ((n + 2 - k) * (n + k + 1)) +
              2 * (shiftedLegendreMagnitude (n + 1) k * k ^ 2)) := by
        ring
      _ = (2 * n + 3) *
            (shiftedLegendreMagnitude (n + 1) k *
                ((n + 2 - k) * (n + k + 1)) +
              2 * (shiftedLegendreMagnitude (n + 1) (k - 1) *
                (n + 2 - k) * (n + k + 1))) := by
        rw [hindex]
      _ = (2 * n + 3) *
            (shiftedLegendreMagnitude (n + 1) k +
              2 * shiftedLegendreMagnitude (n + 1) (k - 1)) *
            ((n + 2 - k) * (n + k + 1)) := by
        ring
  · by_cases hkeq : k = n + 2
    · subst k
      have hc := Nat.succ_mul_centralBinom_succ (n + 1)
      simp only [Nat.centralBinom] at hc
      simp only [show n + 1 + 1 = n + 2 by omega] at hc
      simp [shiftedLegendreMagnitude, Nat.choose_eq_zero_of_lt]
      rw [show n + 2 + (n + 2) = 2 * (n + 2) by omega,
        show n + 1 + (n + 1) = 2 * (n + 1) by omega]
      calc
        (n + 2) * (2 * (n + 2)).choose (n + 2) =
            2 * (2 * (n + 1) + 1) *
              (2 * (n + 1)).choose (n + 1) := hc
        _ = (2 * n + 3) *
            (2 * (2 * (n + 1)).choose (n + 1)) := by
          ring
    · have hgt : n + 2 < k := by omega
      have hgt1 : n + 1 < k := by omega
      have hgt0 : n < k := by omega
      have hgtPred : n + 1 < k - 1 := by omega
      simp [shiftedLegendreMagnitude,
        Nat.choose_eq_zero_of_lt hgt,
        Nat.choose_eq_zero_of_lt hgt1,
        Nat.choose_eq_zero_of_lt hgt0,
        Nat.choose_eq_zero_of_lt hgtPred]

/-- The coefficient formula factored into its sign and unsigned magnitude. -/
theorem coeff_shiftedLegendreReal_eq_sign_mul_magnitude (n k : ℕ) :
    (shiftedLegendreReal n).coeff k =
      (-1 : ℝ) ^ k * (shiftedLegendreMagnitude n k : ℝ) := by
  rw [coeff_shiftedLegendreReal]
  simp only [shiftedLegendreMagnitude, Nat.cast_mul]
  ring

private theorem coeff_one_sub_two_X_mul_zero (p : ℝ[X]) :
    ((1 - 2 * X) * p).coeff 0 = p.coeff 0 := by
  have hpoly :
      (1 - 2 * X) * p = p - (2 : ℝ) • (X * p) := by
    apply Polynomial.funext
    intro x
    simp [Polynomial.eval_smul]
    ring
  rw [hpoly, Polynomial.coeff_sub, Polynomial.coeff_smul,
    Polynomial.coeff_X_mul_zero]
  simp

private theorem coeff_one_sub_two_X_mul_succ (p : ℝ[X]) (k : ℕ) :
    ((1 - 2 * X) * p).coeff (k + 1) =
      p.coeff (k + 1) - 2 * p.coeff k := by
  have hpoly :
      (1 - 2 * X) * p = p - (2 : ℝ) • (X * p) := by
    apply Polynomial.funext
    intro x
    simp [Polynomial.eval_smul]
    ring
  rw [hpoly, Polynomial.coeff_sub, Polynomial.coeff_smul,
    Polynomial.coeff_X_mul]
  simp

/-- The all-degree Jacobi three-term recurrence for the shifted Legendre
polynomials. -/
theorem shiftedLegendreReal_threeTerm (n : ℕ) :
    (((n + 2 : ℕ) : ℝ) • shiftedLegendreReal (n + 2)) =
      (((2 * n + 3 : ℕ) : ℝ) •
          ((1 - 2 * X) * shiftedLegendreReal (n + 1))) -
        (((n + 1 : ℕ) : ℝ) • shiftedLegendreReal n) := by
  ext k
  cases k with
  | zero =>
      rw [Polynomial.coeff_smul, Polynomial.coeff_sub,
        Polynomial.coeff_smul, coeff_one_sub_two_X_mul_zero]
      simp [coeff_shiftedLegendreReal]
      ring
  | succ k =>
      rw [Polynomial.coeff_smul, Polynomial.coeff_sub,
        Polynomial.coeff_smul, Polynomial.coeff_smul,
        coeff_one_sub_two_X_mul_succ]
      simp only [smul_eq_mul]
      rw [coeff_shiftedLegendreReal_eq_sign_mul_magnitude,
        coeff_shiftedLegendreReal_eq_sign_mul_magnitude,
        coeff_shiftedLegendreReal_eq_sign_mul_magnitude,
        coeff_shiftedLegendreReal_eq_sign_mul_magnitude,
        pow_succ]
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      have hnat := shiftedLegendreMagnitude_threeTerm n (k + 1) (by omega)
      simp only [Nat.add_sub_cancel] at hnat
      have hreal := congrArg (fun z : ℕ ↦ (z : ℝ)) hnat
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hreal
      linear_combination -((-1 : ℝ) ^ k) * hreal

/-- Affine transport turns the shifted Jacobi factor `1 - 2t` into the
centered coordinate `-x`. -/
theorem centeredShiftedLegendreReal_threeTerm (n : ℕ) :
    (((n + 2 : ℕ) : ℝ) • centeredShiftedLegendreReal (n + 2)) =
      -(((2 * n + 3 : ℕ) : ℝ) •
          (X * centeredShiftedLegendreReal (n + 1))) -
        (((n + 1 : ℕ) : ℝ) • centeredShiftedLegendreReal n) := by
  apply Polynomial.funext
  intro x
  have h := congrArg
    (fun p : ℝ[X] ↦ p.eval ((x + 1) / 2))
    (shiftedLegendreReal_threeTerm n)
  simp only [Polynomial.eval_smul, Polynomial.eval_sub,
    Polynomial.eval_neg, Polynomial.eval_mul, Polynomial.eval_one,
    Polynomial.eval_ofNat, Polynomial.eval_X, smul_eq_mul] at h ⊢
  rw [eval_centeredShiftedLegendreReal,
    eval_centeredShiftedLegendreReal,
    eval_centeredShiftedLegendreReal] at ⊢
  linear_combination h

end

end ArithmeticHodge.Analysis.ShiftedLegendreJacobiRecurrenceStructural
