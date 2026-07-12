import ArithmeticHodge.Analysis.PolynomialIntervalNorm
import ArithmeticHodge.Analysis.ShiftedLegendreOrthogonality
import ArithmeticHodge.Analysis.ShiftedLogKernelSelfAdjoint
import ArithmeticHodge.Analysis.ShiftedLogKernelTriangular

set_option autoImplicit false

open Polynomial

namespace ArithmeticHodge.Analysis.ShiftedLegendreLogEigen

open PolynomialIntervalNorm
open ShiftedLegendreLogKernel
open ShiftedLegendreOrthogonality
open ShiftedLogKernelSelfAdjoint
open ShiftedLogKernelTriangular

noncomputable section

/-!
# Shifted Legendre eigenvectors of the logarithmic-difference operator

Triangularity supplies the harmonic diagonal, self-adjointness and Rodrigues
orthogonality kill the lower-degree remainder, and definiteness of the
polynomial interval norm makes the conclusion exact.
-/

/-- Exact all-degree shifted-Legendre eigenidentity. -/
theorem shiftedLogKernel_shiftedLegendreReal (n : ℕ) :
    shiftedLogKernel (shiftedLegendreReal n) =
      Polynomial.C (2 * (harmonic n : ℝ)) * shiftedLegendreReal n := by
  let L : ℝ[X] := shiftedLegendreReal n
  let lambda : ℝ := 2 * (harmonic n : ℝ)
  let R : ℝ[X] := shiftedLogKernel L - Polynomial.C lambda * L
  have hLnat : L.natDegree = n := by
    dsimp only [L, shiftedLegendreReal]
    rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective,
      Polynomial.natDegree_shiftedLegendre]
  have hLne : L ≠ 0 := by
    rw [← Polynomial.degree_ne_bot]
    dsimp only [L, shiftedLegendreReal]
    rw [Polynomial.degree_map_eq_of_injective Int.cast_injective,
      Polynomial.degree_shiftedLegendre]
    exact WithBot.coe_ne_bot
  have hRdegree : R.degree < n := by
    have h := degree_shiftedLogKernel_sub_diagonal_lt hLne
    rw [hLnat] at h
    simpa only [R, lambda] using h
  by_cases hRzero : R = 0
  · have hEq : shiftedLogKernel L = Polynomial.C lambda * L :=
      sub_eq_zero.mp hRzero
    simpa only [L, lambda] using hEq
  have hRnat : R.natDegree < n :=
    (Polynomial.natDegree_lt_iff_degree_lt hRzero).2 hRdegree
  have hnpos : 0 < n := (Nat.zero_le R.natDegree).trans_lt hRnat
  have hTRdegree : (shiftedLogKernel R).degree < n :=
    (degree_shiftedLogKernel_le R).trans_lt hRdegree
  have hTRnat : (shiftedLogKernel R).natDegree < n := by
    by_cases hTRzero : shiftedLogKernel R = 0
    · simpa only [hTRzero, Polynomial.natDegree_zero] using hnpos
    · exact (Polynomial.natDegree_lt_iff_degree_lt hTRzero).2 hTRdegree
  have hRL :
      (∫ x : ℝ in 0..1, R.eval x * L.eval x) = 0 := by
    simpa only [L] using
      integral_eval_mul_shiftedLegendreReal_eq_zero n R hRnat
  have hTRL :
      (∫ x : ℝ in 0..1, (shiftedLogKernel R).eval x * L.eval x) = 0 := by
    simpa only [L] using integral_eval_mul_shiftedLegendreReal_eq_zero
      n (shiftedLogKernel R) hTRnat
  have hRTL :
      (∫ x : ℝ in 0..1, R.eval x * (shiftedLogKernel L).eval x) = 0 := by
    rw [shiftedLogKernel_selfAdjoint R L]
    exact hTRL
  have hEvalContinuous (p : ℝ[X]) : Continuous (fun x : ℝ ↦ p.eval x) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (p.hasDerivAt x).continuousAt
  have hRTLInt : IntervalIntegrable
      (fun x : ℝ ↦ R.eval x * (shiftedLogKernel L).eval x)
      MeasureTheory.volume 0 1 :=
    ((hEvalContinuous R).mul (hEvalContinuous (shiftedLogKernel L)))
      |>.intervalIntegrable 0 1
  have hRLInt : IntervalIntegrable
      (fun x : ℝ ↦ R.eval x * L.eval x)
      MeasureTheory.volume 0 1 :=
    ((hEvalContinuous R).mul (hEvalContinuous L)).intervalIntegrable 0 1
  have hRR : (∫ x : ℝ in 0..1, R.eval x ^ 2) = 0 := by
    calc
      (∫ x : ℝ in 0..1, R.eval x ^ 2) =
          ∫ x : ℝ in 0..1,
            (R.eval x * (shiftedLogKernel L).eval x) -
              lambda * (R.eval x * L.eval x) := by
        apply intervalIntegral.integral_congr
        intro x _
        dsimp only [R]
        rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
        ring
      _ = (∫ x : ℝ in 0..1,
            R.eval x * (shiftedLogKernel L).eval x) -
          ∫ x : ℝ in 0..1, lambda * (R.eval x * L.eval x) := by
        rw [intervalIntegral.integral_sub hRTLInt (hRLInt.const_mul lambda)]
      _ = 0 := by
        rw [hRTL, intervalIntegral.integral_const_mul, hRL]
        ring
  have hReq : R = 0 := eq_zero_of_integral_eval_sq_eq_zero R hRR
  exact (hRzero hReq).elim

end

end ArithmeticHodge.Analysis.ShiftedLegendreLogEigen
