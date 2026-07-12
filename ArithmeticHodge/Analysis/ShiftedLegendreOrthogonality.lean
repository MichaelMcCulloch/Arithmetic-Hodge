import ArithmeticHodge.Analysis.PolynomialIteratedIntegrationByParts
import Mathlib.RingTheory.Polynomial.ShiftedLegendre

set_option autoImplicit false

open Polynomial Set

namespace ArithmeticHodge.Analysis.ShiftedLegendreOrthogonality

open PolynomialIteratedIntegrationByParts

noncomputable section

/-!
# Structural shifted-Legendre orthogonality

Rodrigues' formula and uniform iterated integration by parts give
orthogonality against every lower-degree polynomial at once.
-/

/-- The shifted Legendre polynomial over `ℝ`. -/
def shiftedLegendreReal (n : ℕ) : ℝ[X] :=
  (Polynomial.shiftedLegendre n).map (Int.castRingHom ℝ)

/-- The polynomial differentiated in Rodrigues' formula. -/
def shiftedLegendreRodriguesBase (n : ℕ) : ℝ[X] :=
  Polynomial.X ^ n * (1 - Polynomial.X) ^ n

/-- Every derivative below order `n` of the Rodrigues base vanishes at both
endpoints.  This is a multiplicity argument, uniform in the degree. -/
theorem shiftedLegendreRodriguesBase_boundary
    (n m : ℕ) (hm : m < n) :
    (derivative^[m] (shiftedLegendreRodriguesBase n)).eval 0 = 0 ∧
      (derivative^[m] (shiftedLegendreRodriguesBase n)).eval 1 = 0 := by
  have hnm : n - m ≠ 0 := Nat.sub_ne_zero_of_lt hm
  constructor
  · have hpow : (Polynomial.X : ℝ[X]) ^ n ∣
        shiftedLegendreRodriguesBase n := by
      unfold shiftedLegendreRodriguesBase
      exact dvd_mul_right _ _
    have hdvd := pow_sub_dvd_iterate_derivative_of_pow_dvd m hpow
    rcases hdvd with ⟨r, hr⟩
    rw [hr, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      zero_pow hnm, zero_mul]
  · let Z : ℝ[X] := Polynomial.X - Polynomial.C 1
    have hlin : Z ∣ (1 - Polynomial.X : ℝ[X]) := by
      refine ⟨-1, ?_⟩
      dsimp only [Z]
      simp
    have hpowRight : Z ^ n ∣ (1 - Polynomial.X : ℝ[X]) ^ n :=
      pow_dvd_pow_of_dvd hlin n
    have hpow : Z ^ n ∣ shiftedLegendreRodriguesBase n := by
      unfold shiftedLegendreRodriguesBase
      exact dvd_mul_of_dvd_right hpowRight _
    have hdvd := pow_sub_dvd_iterate_derivative_of_pow_dvd m hpow
    rcases hdvd with ⟨r, hr⟩
    rw [hr, Polynomial.eval_mul, Polynomial.eval_pow]
    have hZ : Z.eval 1 = 0 := by simp [Z]
    rw [hZ, zero_pow hnm, zero_mul]

/-- Rodrigues' formula transported from integer coefficients to `ℝ`. -/
theorem factorial_mul_shiftedLegendreReal_eq (n : ℕ) :
    Polynomial.C (n.factorial : ℝ) * shiftedLegendreReal n =
      derivative^[n] (shiftedLegendreRodriguesBase n) := by
  have h := congrArg (Polynomial.map (Int.castRingHom ℝ))
    (Polynomial.factorial_mul_shiftedLegendre_eq n)
  change (n.factorial : ℝ[X]) * shiftedLegendreReal n = _
  rw [show derivative^[n] (shiftedLegendreRodriguesBase n) =
      (derivative^[n]
        ((Polynomial.X : ℤ[X]) ^ n * (1 - Polynomial.X) ^ n)).map
          (Int.castRingHom ℝ) by
    rw [← Polynomial.iterate_derivative_map]
    simp only [shiftedLegendreRodriguesBase, Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sub,
      Polynomial.map_one]]
  simpa only [Polynomial.map_mul, shiftedLegendreReal,
    Polynomial.map_natCast] using h

/-- Shifted Legendre degree `n` is orthogonal on `[0,1]` to every real
polynomial of degree strictly below `n`. -/
theorem integral_eval_mul_shiftedLegendreReal_eq_zero
    (n : ℕ) (p : ℝ[X]) (hp : p.natDegree < n) :
    (∫ x : ℝ in 0..1, p.eval x * (shiftedLegendreReal n).eval x) = 0 := by
  have hzero := integral_eval_mul_iterate_derivative_eq_zero
    p (shiftedLegendreRodriguesBase n) n hp
      (fun m hm ↦ shiftedLegendreRodriguesBase_boundary n m hm)
  rw [← factorial_mul_shiftedLegendreReal_eq n] at hzero
  simp only [Polynomial.eval_mul, Polynomial.eval_C] at hzero
  have hscale : (n.factorial : ℝ) *
      (∫ x : ℝ in 0..1,
        p.eval x * (shiftedLegendreReal n).eval x) = 0 := by
    calc
      (n.factorial : ℝ) *
          (∫ x : ℝ in 0..1,
            p.eval x * (shiftedLegendreReal n).eval x) =
          ∫ x : ℝ in 0..1,
            p.eval x * ((n.factorial : ℝ) *
              (shiftedLegendreReal n).eval x) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro x _
        ring
      _ = 0 := hzero
  exact (mul_eq_zero.mp hscale).resolve_left (by positivity)

end

end ArithmeticHodge.Analysis.ShiftedLegendreOrthogonality
