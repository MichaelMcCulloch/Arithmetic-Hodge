import ArithmeticHodge.Analysis.ShiftedLegendreBasis
import ArithmeticHodge.Analysis.ShiftedLegendreLogEigen
import Mathlib.LinearAlgebra.Basis.Bilinear

set_option autoImplicit false

open Polynomial

namespace ArithmeticHodge.Analysis.ShiftedLegendrePolynomialGap

open ShiftedLegendreBasis
open ShiftedLegendreLogEigen
open ShiftedLegendreLogKernel
open ShiftedLegendreOrthogonality

noncomputable section

/-!
# The structural polynomial spectral gap

The shifted Legendre basis diagonalizes the logarithmic-difference operator.
The zero-mean condition removes its constant zero mode, and every remaining
harmonic eigenvalue is at least `2`.  The result is uniform in polynomial
degree and contains no finite spectral certificate.
-/

/-- The unit-interval polynomial pairing as a bilinear map. -/
def unitIntervalPolynomialPairingBilinear :
    ℝ[X] →ₗ[ℝ] ℝ[X] →ₗ[ℝ] ℝ where
  toFun p :=
    { toFun := fun q ↦ ∫ x : ℝ in 0..1, p.eval x * q.eval x
      map_add' := by
        intro q r
        simp only [Polynomial.eval_add]
        rw [show (fun x : ℝ ↦ p.eval x * (q.eval x + r.eval x)) =
            fun x ↦ p.eval x * q.eval x + p.eval x * r.eval x by
          funext x
          ring]
        exact intervalIntegral.integral_add
          ((p.continuous.mul q.continuous).intervalIntegrable 0 1)
          ((p.continuous.mul r.continuous).intervalIntegrable 0 1)
      map_smul' := by
        intro a q
        rw [Polynomial.smul_eq_C_mul]
        simp only [Polynomial.eval_mul, Polynomial.eval_C, RingHom.id_apply]
        rw [show (fun x : ℝ ↦ p.eval x * (a * q.eval x)) =
            fun x ↦ a * (p.eval x * q.eval x) by
          funext x
          ring,
          intervalIntegral.integral_const_mul]
        rfl }
  map_add' p q := by
    apply LinearMap.ext
    intro r
    change (∫ x : ℝ in 0..1, (p + q).eval x * r.eval x) =
      (∫ x : ℝ in 0..1, p.eval x * r.eval x) +
        ∫ x : ℝ in 0..1, q.eval x * r.eval x
    simp only [Polynomial.eval_add]
    rw [show (fun x : ℝ ↦ (p.eval x + q.eval x) * r.eval x) =
        fun x ↦ p.eval x * r.eval x + q.eval x * r.eval x by
      funext x
      ring]
    exact intervalIntegral.integral_add
      ((p.continuous.mul r.continuous).intervalIntegrable 0 1)
      ((q.continuous.mul r.continuous).intervalIntegrable 0 1)
  map_smul' a p := by
    apply LinearMap.ext
    intro q
    change (∫ x : ℝ in 0..1, (a • p).eval x * q.eval x) =
      a • ∫ x : ℝ in 0..1, p.eval x * q.eval x
    simp only [Polynomial.smul_eq_C_mul, Polynomial.eval_mul,
      Polynomial.eval_C, smul_eq_mul]
    rw [show (fun x : ℝ ↦ a * p.eval x * q.eval x) =
        fun x ↦ a * (p.eval x * q.eval x) by
      funext x
      ring,
      intervalIntegral.integral_const_mul]

@[simp]
theorem unitIntervalPolynomialPairingBilinear_apply (p q : ℝ[X]) :
    unitIntervalPolynomialPairingBilinear p q =
      ∫ x : ℝ in 0..1, p.eval x * q.eval x := rfl

/-- The logarithmic-difference energy polarized as a bilinear map. -/
def shiftedLogEnergyBilinear : ℝ[X] →ₗ[ℝ] ℝ[X] →ₗ[ℝ] ℝ where
  toFun p := (unitIntervalPolynomialPairingBilinear p).comp shiftedLogKernel
  map_add' p q := by
    ext r
    simp
  map_smul' a p := by
    ext q
    simp

@[simp]
theorem shiftedLogEnergyBilinear_apply (p q : ℝ[X]) :
    shiftedLogEnergyBilinear p q =
      ∫ x : ℝ in 0..1,
        p.eval x * (shiftedLogKernel q).eval x := rfl

private theorem bilinear_self_eq_repr_diagonal
    (B : ℝ[X] →ₗ[ℝ] ℝ[X] →ₗ[ℝ] ℝ)
    (horth : ∀ m n : ℕ, m ≠ n →
      B (shiftedLegendreRealBasis m) (shiftedLegendreRealBasis n) = 0)
    (p : ℝ[X]) :
    B p p =
      (shiftedLegendreRealBasis.repr p).sum fun n c ↦
        c ^ 2 * B (shiftedLegendreRealBasis n)
          (shiftedLegendreRealBasis n) := by
  classical
  rw [← LinearMap.sum_repr_mul_repr_mul shiftedLegendreRealBasis
    shiftedLegendreRealBasis p p]
  apply Finsupp.sum_congr
  intro n hn
  rw [Finsupp.sum_eq_single n]
  · simp only [smul_eq_mul]
    ring
  · intro m _hm hmn
    rw [horth n m (Ne.symm hmn)]
    simp
  · intro hnzero
    simp [hnzero]

private theorem shiftedLegendre_pairing_orthogonal
    {m n : ℕ} (hmn : m ≠ n) :
    unitIntervalPolynomialPairingBilinear
      (shiftedLegendreRealBasis m) (shiftedLegendreRealBasis n) = 0 := by
  simp only [unitIntervalPolynomialPairingBilinear_apply,
    shiftedLegendreRealBasis_apply]
  exact integral_shiftedLegendreReal_mul_eq_zero hmn

private theorem shiftedLegendre_energy_orthogonal
    {m n : ℕ} (hmn : m ≠ n) :
    shiftedLogEnergyBilinear
      (shiftedLegendreRealBasis m) (shiftedLegendreRealBasis n) = 0 := by
  rw [shiftedLogEnergyBilinear_apply, shiftedLegendreRealBasis_apply,
    shiftedLegendreRealBasis_apply,
    shiftedLogKernel_shiftedLegendreReal]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  rw [show (fun x : ℝ ↦
      (shiftedLegendreReal m).eval x *
        (2 * (harmonic n : ℝ) * (shiftedLegendreReal n).eval x)) =
      fun x ↦ (2 * (harmonic n : ℝ)) *
        ((shiftedLegendreReal m).eval x *
          (shiftedLegendreReal n).eval x) by
    funext x
    ring,
    intervalIntegral.integral_const_mul,
    integral_shiftedLegendreReal_mul_eq_zero hmn]
  ring

private theorem shiftedLegendre_energy_self (n : ℕ) :
    shiftedLogEnergyBilinear
      (shiftedLegendreRealBasis n) (shiftedLegendreRealBasis n) =
        (2 * (harmonic n : ℝ)) *
          unitIntervalPolynomialPairingBilinear
            (shiftedLegendreRealBasis n)
            (shiftedLegendreRealBasis n) := by
  rw [shiftedLogEnergyBilinear_apply, shiftedLegendreRealBasis_apply,
    shiftedLogKernel_shiftedLegendreReal]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  rw [show (fun x : ℝ ↦
      (shiftedLegendreReal n).eval x *
        (2 * (harmonic n : ℝ) * (shiftedLegendreReal n).eval x)) =
      fun x ↦ (2 * (harmonic n : ℝ)) *
        ((shiftedLegendreReal n).eval x *
          (shiftedLegendreReal n).eval x) by
    funext x
    ring,
    intervalIntegral.integral_const_mul]
  rfl

private theorem shiftedLegendreRealBasis_repr_zero_eq_mean (p : ℝ[X]) :
    shiftedLegendreRealBasis.repr p 0 =
      ∫ x : ℝ in 0..1, p.eval x := by
  classical
  have hexpand := LinearMap.sum_repr_mul_repr_mul
    shiftedLegendreRealBasis shiftedLegendreRealBasis
    (B := unitIntervalPolynomialPairingBilinear) p
      (shiftedLegendreRealBasis 0)
  have hsingle :
      (shiftedLegendreRealBasis.repr p).sum (fun n c ↦
        c * unitIntervalPolynomialPairingBilinear
          (shiftedLegendreRealBasis n) (shiftedLegendreRealBasis 0)) =
        unitIntervalPolynomialPairingBilinear p
          (shiftedLegendreRealBasis 0) := by
    rw [Module.Basis.repr_self] at hexpand
    simpa [smul_eq_mul] using hexpand
  have hcollapse :
      (shiftedLegendreRealBasis.repr p).sum (fun n c ↦
        c * unitIntervalPolynomialPairingBilinear
          (shiftedLegendreRealBasis n) (shiftedLegendreRealBasis 0)) =
        shiftedLegendreRealBasis.repr p 0 *
          unitIntervalPolynomialPairingBilinear
            (shiftedLegendreRealBasis 0) (shiftedLegendreRealBasis 0) := by
    rw [Finsupp.sum_eq_single 0]
    · intro n _hn hnzero
      rw [shiftedLegendre_pairing_orthogonal hnzero]
      ring
    · intro hzero
      simp
  rw [hcollapse] at hsingle
  have hLzero : shiftedLegendreReal 0 = 1 := by
    simp [shiftedLegendreReal, Polynomial.shiftedLegendre]
  simpa [unitIntervalPolynomialPairingBilinear_apply,
    shiftedLegendreRealBasis_apply, hLzero] using hsingle

private theorem one_le_harmonic_cast_of_pos
    {n : ℕ} (hn : 0 < n) :
    (1 : ℝ) ≤ (harmonic n : ℝ) := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hnzero : n = 0
      · subst n
        norm_num [harmonic]
      · have hprev : (1 : ℝ) ≤ (harmonic n : ℝ) :=
          ih (Nat.pos_of_ne_zero hnzero)
        rw [harmonic_succ]
        push_cast
        exact hprev.trans (le_add_of_nonneg_right (by positivity))

/-- Every zero-mean real polynomial satisfies the sharp first-positive-mode
spectral gap for the logarithmic-difference operator on `[0,1]`. -/
theorem shiftedLogKernel_polynomial_spectral_gap
    (p : ℝ[X])
    (hmean : (∫ x : ℝ in 0..1, p.eval x) = 0) :
    2 * (∫ x : ℝ in 0..1, p.eval x ^ 2) ≤
      ∫ x : ℝ in 0..1,
        p.eval x * (shiftedLogKernel p).eval x := by
  classical
  let c := shiftedLegendreRealBasis.repr p
  have hc_zero : c 0 = 0 := by
    dsimp only [c]
    rw [shiftedLegendreRealBasis_repr_zero_eq_mean]
    exact hmean
  have hnorm_diagonal := bilinear_self_eq_repr_diagonal
    unitIntervalPolynomialPairingBilinear
      (fun m n hmn ↦ shiftedLegendre_pairing_orthogonal hmn) p
  have henergy_diagonal := bilinear_self_eq_repr_diagonal
    shiftedLogEnergyBilinear
      (fun m n hmn ↦ shiftedLegendre_energy_orthogonal hmn) p
  have hsq :
      (∫ x : ℝ in 0..1, p.eval x ^ 2) =
        unitIntervalPolynomialPairingBilinear p p := by
    rw [unitIntervalPolynomialPairingBilinear_apply]
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  rw [hsq]
  change 2 * unitIntervalPolynomialPairingBilinear p p ≤
    shiftedLogEnergyBilinear p p
  rw [hnorm_diagonal, henergy_diagonal]
  simp_rw [shiftedLegendre_energy_self]
  change 2 * c.sum (fun n a ↦
      a ^ 2 * unitIntervalPolynomialPairingBilinear
        (shiftedLegendreRealBasis n) (shiftedLegendreRealBasis n)) ≤
    c.sum (fun n a ↦
      a ^ 2 * ((2 * (harmonic n : ℝ)) *
        unitIntervalPolynomialPairingBilinear
          (shiftedLegendreRealBasis n) (shiftedLegendreRealBasis n)))
  calc
    2 * c.sum (fun n a ↦
        a ^ 2 * unitIntervalPolynomialPairingBilinear
          (shiftedLegendreRealBasis n) (shiftedLegendreRealBasis n)) =
        c.sum (fun n a ↦
          2 * (a ^ 2 * unitIntervalPolynomialPairingBilinear
            (shiftedLegendreRealBasis n)
            (shiftedLegendreRealBasis n))) := by
          simp [Finsupp.sum, Finset.mul_sum]
    _ ≤ c.sum (fun n a ↦
        a ^ 2 * ((2 * (harmonic n : ℝ)) *
          unitIntervalPolynomialPairingBilinear
            (shiftedLegendreRealBasis n)
            (shiftedLegendreRealBasis n))) := by
      apply Finsupp.sum_le_sum
      intro n hn
      by_cases hnzero : n = 0
      · subst n
        simp [hc_zero]
      · have hH : (1 : ℝ) ≤ (harmonic n : ℝ) :=
          one_le_harmonic_cast_of_pos (Nat.pos_of_ne_zero hnzero)
        have hnorm : 0 ≤ unitIntervalPolynomialPairingBilinear
            (shiftedLegendreRealBasis n) (shiftedLegendreRealBasis n) := by
          rw [unitIntervalPolynomialPairingBilinear_apply]
          exact intervalIntegral.integral_nonneg (by norm_num)
            (fun x _hx ↦ mul_self_nonneg
              ((shiftedLegendreRealBasis n).eval x))
        have hfactor : 0 ≤
            (shiftedLegendreRealBasis.repr p n) ^ 2 *
              unitIntervalPolynomialPairingBilinear
                (shiftedLegendreRealBasis n)
                (shiftedLegendreRealBasis n) :=
          mul_nonneg (sq_nonneg _) hnorm
        have hlambda : (2 : ℝ) ≤ 2 * (harmonic n : ℝ) := by
          linarith
        calc
          2 * ((shiftedLegendreRealBasis.repr p n) ^ 2 *
              unitIntervalPolynomialPairingBilinear
                (shiftedLegendreRealBasis n)
                (shiftedLegendreRealBasis n)) ≤
              (2 * (harmonic n : ℝ)) *
                ((shiftedLegendreRealBasis.repr p n) ^ 2 *
                  unitIntervalPolynomialPairingBilinear
                    (shiftedLegendreRealBasis n)
                    (shiftedLegendreRealBasis n)) :=
            mul_le_mul_of_nonneg_right hlambda hfactor
          _ = (shiftedLegendreRealBasis.repr p n) ^ 2 *
              ((2 * (harmonic n : ℝ)) *
                unitIntervalPolynomialPairingBilinear
                  (shiftedLegendreRealBasis n)
                  (shiftedLegendreRealBasis n)) := by ring

end

end ArithmeticHodge.Analysis.ShiftedLegendrePolynomialGap
