import ArithmeticHodge.Analysis.ShiftedLegendreLogKernel
import Mathlib.Algebra.Polynomial.Degree.Support

set_option autoImplicit false

open Finset Polynomial

namespace ArithmeticHodge.Analysis.ShiftedLogKernelTriangular

open ShiftedLegendreLogKernel

noncomputable section

/-! # Uniform triangularity of the shifted logarithmic kernel -/

theorem degree_shiftedLogKernelMonomial_le (n : ℕ) :
    (shiftedLogKernelMonomial n).degree ≤ n := by
  rw [shiftedLogKernelMonomial]
  apply (Polynomial.degree_sub_le _ _).trans
  apply max_le
  · exact Polynomial.degree_C_mul_X_pow_le _ _
  · exact (degree_shiftedLogKernelLower_lt n).le

/-- The logarithmic kernel preserves the polynomial degree filtration. -/
theorem degree_shiftedLogKernel_le (p : ℝ[X]) :
    (shiftedLogKernel p).degree ≤ p.degree := by
  by_cases hp : p = 0
  · simp [hp]
  rw [Polynomial.degree_eq_natDegree hp]
  rw [shiftedLogKernel, Polynomial.lsum_apply, Polynomial.sum_def]
  calc
    (∑ n ∈ p.support,
        (shiftedLogKernelMonomialLinear n) (p.coeff n)).degree ≤
        p.support.sup fun n ↦
          ((shiftedLogKernelMonomialLinear n) (p.coeff n)).degree :=
      Polynomial.degree_sum_le _ _
    _ ≤ (p.natDegree : WithBot ℕ) := by
      apply Finset.sup_le
      intro n hn
      dsimp only [shiftedLogKernelMonomialLinear]
      exact (Polynomial.degree_smul_le _ _).trans
        ((degree_shiftedLogKernelMonomial_le n).trans
          (WithBot.coe_le_coe.mpr (Polynomial.le_natDegree_of_mem_supp n hn)))

/-- The top coefficient is multiplied by the harmonic diagonal entry. -/
theorem coeff_shiftedLogKernel_natDegree
    {p : ℝ[X]} (hp : p ≠ 0) :
    (shiftedLogKernel p).coeff p.natDegree =
      2 * (harmonic p.natDegree : ℝ) * p.leadingCoeff := by
  rw [shiftedLogKernel, Polynomial.lsum_apply, Polynomial.coeff_sum,
    Polynomial.sum_def]
  rw [Finset.sum_eq_single p.natDegree]
  · change (p.coeff p.natDegree •
        shiftedLogKernelMonomial p.natDegree).coeff p.natDegree = _
    rw [Polynomial.coeff_smul, coeff_shiftedLogKernelMonomial]
    rw [Polynomial.leadingCoeff]
    simp only [smul_eq_mul]
    ring
  · intro k hk hkn
    change (p.coeff k • shiftedLogKernelMonomial k).coeff p.natDegree = 0
    rw [Polynomial.coeff_smul]
    have hklt : k < p.natDegree :=
      (Polynomial.le_natDegree_of_mem_supp k hk).lt_of_ne hkn
    have hdegree : (shiftedLogKernelMonomial k).degree < p.natDegree :=
      (degree_shiftedLogKernelMonomial_le k).trans_lt
        (WithBot.coe_lt_coe.mpr hklt)
    rw [Polynomial.coeff_eq_zero_of_degree_lt hdegree]
    simp
  · intro hnot
    exact (hnot (Polynomial.natDegree_mem_support_of_nonzero hp)).elim

/-- Removing the harmonic diagonal term strictly lowers degree. -/
theorem degree_shiftedLogKernel_sub_diagonal_lt
    {p : ℝ[X]} (hp : p ≠ 0) :
    (shiftedLogKernel p -
      Polynomial.C (2 * (harmonic p.natDegree : ℝ)) * p).degree <
        p.natDegree := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro m hm
  rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  by_cases hmn : m = p.natDegree
  · subst m
    rw [coeff_shiftedLogKernel_natDegree hp, Polynomial.leadingCoeff]
    ring
  · have hlt : p.natDegree < m := lt_of_le_of_ne hm (Ne.symm hmn)
    have hpdeg : p.degree = (p.natDegree : WithBot ℕ) :=
      Polynomial.degree_eq_natDegree hp
    have hTlt : (shiftedLogKernel p).degree < m :=
      (degree_shiftedLogKernel_le p).trans_lt (hpdeg.trans_lt
        (WithBot.coe_lt_coe.mpr hlt))
    have hplt : p.degree < m := hpdeg.trans_lt (WithBot.coe_lt_coe.mpr hlt)
    rw [Polynomial.coeff_eq_zero_of_degree_lt hTlt,
      Polynomial.coeff_eq_zero_of_degree_lt hplt, mul_zero, sub_zero]

end

end ArithmeticHodge.Analysis.ShiftedLogKernelTriangular
