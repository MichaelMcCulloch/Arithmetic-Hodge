import ArithmeticHodge.Analysis.ShiftedLegendreLogKernel
import Mathlib.Topology.Algebra.Polynomial

set_option autoImplicit false

open Finset Polynomial

namespace ArithmeticHodge.Analysis.ShiftedLogKernelSelfAdjoint

noncomputable section

open ShiftedLegendreLogKernel

/-!
# Self-adjointness of the shifted logarithmic kernel

The proof is entirely symbolic.  On monomials the pairing reduces to a
finite reciprocal sum, whose partial fractions give the symmetric value

`(H_m + H_n - H_{m+n}) / (m+n+1)`.

Polynomial bilinearity then extends the identity without any degree cutoff.
-/

/-- The real polynomial pairing on the unit interval. -/
def unitIntervalPolynomialPairing (p q : ℝ[X]) : ℝ :=
  ∫ x in 0..1, p.eval x * q.eval x

private theorem sum_range_inv_add_one (m n : ℕ) :
    (∑ j ∈ Finset.range n, ((((m + j + 1 : ℕ) : ℝ))⁻¹)) =
      (harmonic (m + n) : ℝ) - (harmonic m : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      rw [show m + (n + 1) = (m + n) + 1 by omega, harmonic_succ]
      push_cast
      ring

private theorem sum_range_reciprocal_rectangle (m n : ℕ) :
    (∑ j ∈ Finset.range n,
      ((((n - j : ℕ) : ℝ))⁻¹) * ((((m + j + 1 : ℕ) : ℝ))⁻¹)) =
      ((harmonic n : ℝ) + (harmonic (m + n) : ℝ) -
        (harmonic m : ℝ)) / (m + n + 1 : ℕ) := by
  calc
    _ = ∑ j ∈ Finset.range n,
        (((((n - j : ℕ) : ℝ))⁻¹) +
          ((((m + j + 1 : ℕ) : ℝ))⁻¹)) / (m + n + 1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      have ha : (↑(n - j) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.sub_pos_of_lt hj).ne'
      have hb : (↑(m + j + 1) : ℝ) ≠ 0 := by positivity
      have hM : (↑(m + n + 1) : ℝ) ≠ 0 := by positivity
      have hadd : m + n + 1 = m + j + 1 + (n - j) := by omega
      field_simp [ha, hb, hM]
      exact_mod_cast hadd
    _ = ((∑ j ∈ Finset.range n, ((((n - j : ℕ) : ℝ))⁻¹)) +
          ∑ j ∈ Finset.range n,
            ((((m + j + 1 : ℕ) : ℝ))⁻¹)) / (m + n + 1 : ℕ) := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ = _ := by
      rw [sum_range_inv_nat_sub, sum_range_inv_add_one]
      ring

private theorem unitIntervalPolynomialPairing_add_left
    (p q r : ℝ[X]) :
    unitIntervalPolynomialPairing (p + q) r =
      unitIntervalPolynomialPairing p r +
        unitIntervalPolynomialPairing q r := by
  rw [unitIntervalPolynomialPairing]
  simp only [Polynomial.eval_add]
  rw [show (fun x : ℝ ↦ (p.eval x + q.eval x) * r.eval x) =
      fun x ↦ p.eval x * r.eval x + q.eval x * r.eval x by
    funext x
    ring]
  exact intervalIntegral.integral_add
    ((p.continuous.mul r.continuous).intervalIntegrable 0 1)
    ((q.continuous.mul r.continuous).intervalIntegrable 0 1)

private theorem unitIntervalPolynomialPairing_add_right
    (p q r : ℝ[X]) :
    unitIntervalPolynomialPairing p (q + r) =
      unitIntervalPolynomialPairing p q +
        unitIntervalPolynomialPairing p r := by
  rw [unitIntervalPolynomialPairing]
  simp only [Polynomial.eval_add]
  rw [show (fun x : ℝ ↦ p.eval x * (q.eval x + r.eval x)) =
      fun x ↦ p.eval x * q.eval x + p.eval x * r.eval x by
    funext x
    ring]
  exact intervalIntegral.integral_add
    ((p.continuous.mul q.continuous).intervalIntegrable 0 1)
    ((p.continuous.mul r.continuous).intervalIntegrable 0 1)

private theorem unitIntervalPolynomialPairing_sub_right
    (p q r : ℝ[X]) :
    unitIntervalPolynomialPairing p (q - r) =
      unitIntervalPolynomialPairing p q -
        unitIntervalPolynomialPairing p r := by
  rw [unitIntervalPolynomialPairing]
  simp only [Polynomial.eval_sub]
  rw [show (fun x : ℝ ↦ p.eval x * (q.eval x - r.eval x)) =
      fun x ↦ p.eval x * q.eval x - p.eval x * r.eval x by
    funext x
    ring]
  exact intervalIntegral.integral_sub
    ((p.continuous.mul q.continuous).intervalIntegrable 0 1)
    ((p.continuous.mul r.continuous).intervalIntegrable 0 1)

private theorem unitIntervalPolynomialPairing_smul_left
    (a : ℝ) (p q : ℝ[X]) :
    unitIntervalPolynomialPairing (a • p) q =
      a * unitIntervalPolynomialPairing p q := by
  rw [unitIntervalPolynomialPairing, Polynomial.smul_eq_C_mul]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  rw [show (fun x : ℝ ↦ a * p.eval x * q.eval x) =
      fun x ↦ a * (p.eval x * q.eval x) by
    funext x
    ring,
    intervalIntegral.integral_const_mul]
  rfl

private theorem unitIntervalPolynomialPairing_smul_right
    (a : ℝ) (p q : ℝ[X]) :
    unitIntervalPolynomialPairing p (a • q) =
      a * unitIntervalPolynomialPairing p q := by
  rw [unitIntervalPolynomialPairing, Polynomial.smul_eq_C_mul]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  rw [show (fun x : ℝ ↦ p.eval x * (a * q.eval x)) =
      fun x ↦ a * (p.eval x * q.eval x) by
    funext x
    ring,
    intervalIntegral.integral_const_mul]
  rfl

private theorem unitIntervalPolynomialPairing_sum_right
    {ι : Type*} (s : Finset ι) (p : ℝ[X]) (f : ι → ℝ[X]) :
    unitIntervalPolynomialPairing p (∑ i ∈ s, f i) =
      ∑ i ∈ s, unitIntervalPolynomialPairing p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [unitIntervalPolynomialPairing]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        unitIntervalPolynomialPairing_add_right, ih]

private theorem unitIntervalPolynomialPairing_comm (p q : ℝ[X]) :
    unitIntervalPolynomialPairing p q = unitIntervalPolynomialPairing q p := by
  rw [unitIntervalPolynomialPairing]
  apply intervalIntegral.integral_congr
  intro x _hx
  ring

private theorem unitIntervalPolynomialPairing_X_pow_X_pow (m n : ℕ) :
    unitIntervalPolynomialPairing (Polynomial.X ^ m) (Polynomial.X ^ n) =
      1 / (m + n + 1 : ℕ) := by
  rw [unitIntervalPolynomialPairing]
  simp only [Polynomial.eval_X_pow]
  rw [show (fun x : ℝ ↦ x ^ m * x ^ n) = fun x ↦ x ^ (m + n) by
    funext x
    rw [pow_add], integral_pow]
  have hpos : 0 < m + n + 1 := by omega
  rw [one_pow, zero_pow hpos.ne']
  push_cast
  ring

private theorem unitIntervalPolynomialPairing_X_pow_C_mul_X_pow
    (m n : ℕ) (a : ℝ) :
    unitIntervalPolynomialPairing (Polynomial.X ^ m)
        (Polynomial.C a * Polynomial.X ^ n) =
      a / (m + n + 1 : ℕ) := by
  rw [← Polynomial.smul_eq_C_mul,
    unitIntervalPolynomialPairing_smul_right,
    unitIntervalPolynomialPairing_X_pow_X_pow]
  ring

/-- Exact closed form of the monomial pairing with the logarithmic kernel. -/
theorem unitIntervalPolynomialPairing_X_pow_shiftedLogKernel_X_pow
    (m n : ℕ) :
    unitIntervalPolynomialPairing (Polynomial.X ^ m)
        (shiftedLogKernel (Polynomial.X ^ n)) =
      ((harmonic m : ℝ) + (harmonic n : ℝ) -
        (harmonic (m + n) : ℝ)) / (m + n + 1 : ℕ) := by
  rw [shiftedLogKernel_X_pow, shiftedLogKernelMonomial,
    unitIntervalPolynomialPairing_sub_right,
    unitIntervalPolynomialPairing_X_pow_C_mul_X_pow,
    shiftedLogKernelLower,
    unitIntervalPolynomialPairing_sum_right]
  simp_rw [unitIntervalPolynomialPairing_X_pow_C_mul_X_pow]
  rw [Finset.sum_fin_eq_sum_range]
  have hsum :
      (∑ i ∈ Finset.range n,
        if h : i < n then
          (↑(n - (⟨i, h⟩ : Fin n)) : ℝ)⁻¹ /
            (m + (⟨i, h⟩ : Fin n) + 1 : ℕ)
        else 0) =
      ∑ i ∈ Finset.range n,
        (↑(n - i) : ℝ)⁻¹ * (↑(m + i + 1) : ℝ)⁻¹ := by
    apply Finset.sum_congr rfl
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    simp [hin, div_eq_mul_inv]
  rw [hsum, sum_range_reciprocal_rectangle]
  push_cast
  ring

/-- The logarithmic-kernel pairing is symmetric on monomials. -/
theorem unitIntervalPolynomialPairing_shiftedLogKernel_X_pow_comm
    (m n : ℕ) :
    unitIntervalPolynomialPairing (Polynomial.X ^ m)
        (shiftedLogKernel (Polynomial.X ^ n)) =
      unitIntervalPolynomialPairing
        (shiftedLogKernel (Polynomial.X ^ m)) (Polynomial.X ^ n) := by
  rw [unitIntervalPolynomialPairing_comm
      (shiftedLogKernel (Polynomial.X ^ m)) (Polynomial.X ^ n),
    unitIntervalPolynomialPairing_X_pow_shiftedLogKernel_X_pow,
    unitIntervalPolynomialPairing_X_pow_shiftedLogKernel_X_pow]
  rw [Nat.add_comm n m]
  ring

private theorem unitIntervalPolynomialPairing_monomial_selfAdjoint
    (m n : ℕ) (a b : ℝ) :
    unitIntervalPolynomialPairing (Polynomial.C a * Polynomial.X ^ m)
        (shiftedLogKernel (Polynomial.C b * Polynomial.X ^ n)) =
      unitIntervalPolynomialPairing
        (shiftedLogKernel (Polynomial.C a * Polynomial.X ^ m))
        (Polynomial.C b * Polynomial.X ^ n) := by
  have hp : Polynomial.C a * Polynomial.X ^ m =
      a • Polynomial.X ^ m := (Polynomial.smul_eq_C_mul a).symm
  have hq : Polynomial.C b * Polynomial.X ^ n =
      b • Polynomial.X ^ n := (Polynomial.smul_eq_C_mul b).symm
  rw [hp, hq, map_smul, map_smul,
    unitIntervalPolynomialPairing_smul_left,
    unitIntervalPolynomialPairing_smul_right,
    unitIntervalPolynomialPairing_smul_left,
    unitIntervalPolynomialPairing_smul_right,
    unitIntervalPolynomialPairing_shiftedLogKernel_X_pow_comm]

/-- The shifted logarithmic-difference operator is self-adjoint for the
`L²([0,1])` polynomial pairing. -/
theorem shiftedLogKernel_selfAdjoint (p q : ℝ[X]) :
    (∫ x in 0..1, p.eval x * (shiftedLogKernel q).eval x) =
      ∫ x in 0..1, (shiftedLogKernel p).eval x * q.eval x := by
  change unitIntervalPolynomialPairing p (shiftedLogKernel q) =
    unitIntervalPolynomialPairing (shiftedLogKernel p) q
  induction p using Polynomial.induction_on' generalizing q with
  | add p r hp hr =>
      rw [unitIntervalPolynomialPairing_add_left, map_add,
        unitIntervalPolynomialPairing_add_left, hp, hr]
  | monomial m a =>
      induction q using Polynomial.induction_on' with
      | add q r hq hr =>
          rw [map_add, unitIntervalPolynomialPairing_add_right,
            unitIntervalPolynomialPairing_add_right, hq, hr]
      | monomial n b =>
          simpa only [Polynomial.C_mul_X_pow_eq_monomial] using
            unitIntervalPolynomialPairing_monomial_selfAdjoint m n a b

end

end ArithmeticHodge.Analysis.ShiftedLogKernelSelfAdjoint
