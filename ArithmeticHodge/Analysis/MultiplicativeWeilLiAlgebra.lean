import ArithmeticHodge.Analysis.WeilDefs

/-!
# Algebra of the Bombieri--Li witness

This module defines Li's rational functions and proves the two elementary
identities used in the off-critical-line negativity argument: the reflected
product identity and the exact squared-modulus formula that detects zeros to
the left of the critical line.
-/

set_option autoImplicit false

open Complex Real

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- Li's rational test function. -/
def liFunction (n : ℕ) (s : ℂ) : ℂ :=
  1 - (1 - 1 / s) ^ n

private theorem li_bases_mul (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    (1 - 1 / s) * (1 - 1 / (1 - s)) = 1 := by
  have h1s : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  field_simp [hs0, h1s]
  ring

/-- The elementary product identity behind Bombieri's Li witness. -/
theorem liFunction_mul_one_sub (n : ℕ) (s : ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    liFunction n s * liFunction n (1 - s) =
      liFunction n s + liFunction n (1 - s) := by
  have hbase := li_bases_mul s hs0 hs1
  have hp : (1 - 1 / s) ^ n * (1 - 1 / (1 - s)) ^ n = 1 := by
    rw [← mul_pow, hbase, one_pow]
  simp only [liFunction]
  linear_combination hp

/-- Exact squared-modulus identity detecting which side of the critical line a
zero lies on. -/
theorem normSq_one_sub_inv (rho : ℂ) (hrho : rho ≠ 0) :
    Complex.normSq (1 - 1 / rho) =
      1 + (1 - 2 * rho.re) / Complex.normSq rho := by
  rw [Complex.normSq_sub, Complex.normSq_one, Complex.normSq_div,
    Complex.normSq_one]
  have hnorm : Complex.normSq rho ≠ 0 :=
    mt Complex.normSq_eq_zero.mp hrho
  have hre : ((1 : ℂ) * starRingEnd ℂ (1 / rho)).re =
      rho.re / Complex.normSq rho := by
    simp
  rw [hre]
  field_simp
  ring

/-- A point left of the critical line gives a Li base of modulus greater than
one. -/
theorem one_lt_norm_one_sub_inv (rho : ℂ) (hrho : rho ≠ 0)
    (hre : rho.re < 1 / 2) :
    1 < ‖1 - 1 / rho‖ := by
  rw [← sq_lt_sq₀ (by positivity : (0 : ℝ) ≤ 1) (norm_nonneg _),
    Complex.sq_norm, normSq_one_sub_inv rho hrho]
  have hnorm : 0 < Complex.normSq rho := Complex.normSq_pos.mpr hrho
  have hnum : 0 < 1 - 2 * rho.re := by linarith
  have hquot : 0 < (1 - 2 * rho.re) / Complex.normSq rho :=
    div_pos hnum hnorm
  linarith

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
