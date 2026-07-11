import ArithmeticHodge.Analysis.ZetaProduct

open Complex Real

namespace ArithmeticHodge.Analysis

set_option autoImplicit false

/-- The local Stirling premise inside the legacy zero-density proof is false:
`Complex.log` uses the principal argument and hence has imaginary part at most
`pi`, while the proposed right-hand side is an unwrapped phase of size
`T log T`.  The concrete height `T = 100` already gives a contradiction. -/
theorem no_principal_log_Gamma_stirling_phase_at_100_scratch :
    ¬ ∃ ε : ℝ, |ε| ≤ 1 ∧
      (Complex.log (Complex.Gamma
        (↑(1 / 4 : ℝ) + ↑((100 : ℝ) / 2) * Complex.I))).im =
        (100 : ℝ) / 2 * Real.log ((100 : ℝ) / 2) -
          (100 : ℝ) / 2 - Real.pi / 4 + ε / 100 := by
  rintro ⟨ε, hε, heq⟩
  have hexp_three_lt_fifty : Real.exp 3 < 50 := by
    calc
      Real.exp 3 = Real.exp 1 ^ (3 : ℕ) := by
        rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
        ring
      _ < 3 ^ (3 : ℕ) := by
        exact pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos 1).le (by norm_num)
      _ < 50 := by norm_num
  have hlog_fifty : 3 < Real.log 50 := by
    exact (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 50)).mpr
      hexp_three_lt_fifty
  have hε_lower : -1 ≤ ε := neg_le_of_abs_le hε
  have hpi_upper : Real.pi < 4 := Real.pi_lt_four
  have hphase_gt_pi : Real.pi <
      (100 : ℝ) / 2 * Real.log ((100 : ℝ) / 2) -
        (100 : ℝ) / 2 - Real.pi / 4 + ε / 100 := by
    norm_num at hlog_fifty ⊢
    nlinarith
  have hprincipal := Complex.log_im_le_pi
    (Complex.Gamma
      (↑(1 / 4 : ℝ) + ↑((100 : ℝ) / 2) * Complex.I))
  rw [heq] at hprincipal
  exact (not_lt_of_ge hprincipal) hphase_gt_pi

#print axioms no_principal_log_Gamma_stirling_phase_at_100_scratch

end ArithmeticHodge.Analysis
