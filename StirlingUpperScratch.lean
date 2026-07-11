import ArithmeticHodge.Analysis.ComplexStirling

open Complex Real

namespace ArithmeticHodge.Analysis

theorem complex_Gamma_stirling_upper_bound
    (σ₁ σ₂ : ℝ) (hσ : σ₁ ≤ σ₂) :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 < C ∧
      ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → 2 ≤ |s.im| →
        ‖Complex.Gamma s‖ ≤
          C * |s.im| ^ A * Real.exp (-(Real.pi / 2) * |s.im|) := by
  obtain ⟨D, hD_pos, hD⟩ := complex_stirling_bound σ₁ σ₂ hσ
  let A : ℝ := max 0 (σ₂ - 1 / 2 + D)
  refine ⟨A, 1, le_max_left _ _, one_pos, fun s hs₁ hs₂ ht => ?_⟩
  rw [one_mul]
  let T : ℝ := |s.im|
  let L : ℝ := Real.log T
  have hT : 2 ≤ T := by simpa [T] using ht
  have hT_pos : 0 < T := by linarith
  have hL_pos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by linarith)
  have him_ne : s.im ≠ 0 := by
    intro him
    rw [him, abs_zero] at ht
    norm_num at ht
  have hGamma_ne : Complex.Gamma s ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m hsm
    have := congr_arg Complex.im hsm
    simp only [Complex.neg_im, Complex.natCast_im, neg_zero] at this
    exact him_ne this
  have hGamma_pos : 0 < ‖Complex.Gamma s‖ := norm_pos_iff.mpr hGamma_ne
  have hstirling := hD s hs₁ hs₂ ht
  have herror :
      Real.log ‖Complex.Gamma s‖ -
          ((s.re - 1 / 2) * L - T * (Real.pi / 2)) ≤ D * L := by
    simpa only [T, L] using (abs_le.mp hstirling).2
  have hcoeff : s.re - 1 / 2 + D ≤ A := by
    calc
      s.re - 1 / 2 + D ≤ σ₂ - 1 / 2 + D := by linarith
      _ ≤ A := by exact le_max_right _ _
  have hlog :
      Real.log ‖Complex.Gamma s‖ ≤
        A * L - (Real.pi / 2) * T := by
    calc
      Real.log ‖Complex.Gamma s‖
          ≤ (s.re - 1 / 2 + D) * L - (Real.pi / 2) * T := by
            linarith
      _ ≤ A * L - (Real.pi / 2) * T := by
            gcongr
  calc
    ‖Complex.Gamma s‖ = Real.exp (Real.log ‖Complex.Gamma s‖) :=
      (Real.exp_log hGamma_pos).symm
    _ ≤ Real.exp (A * L - (Real.pi / 2) * T) := Real.exp_le_exp.mpr hlog
    _ = T ^ A * Real.exp (-(Real.pi / 2) * T) := by
      rw [Real.rpow_def_of_pos hT_pos, ← Real.exp_add]
      congr 1
      dsimp [L]
      ring
    _ = |s.im| ^ A * Real.exp (-(Real.pi / 2) * |s.im|) := by rfl

theorem norm_cos_le_exp_abs_im (z : ℂ) :
    ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  have hnorm : 2 * ‖Complex.cos z‖ ≤ Real.exp (-z.im) + Real.exp z.im := by
    calc
      2 * ‖Complex.cos z‖ = ‖(2 : ℂ) * Complex.cos z‖ := by
        rw [Complex.norm_mul]
        norm_num
      _ = ‖Complex.exp (z * Complex.I) + Complex.exp (-z * Complex.I)‖ := by
        rw [Complex.two_cos]
      _ ≤ ‖Complex.exp (z * Complex.I)‖ + ‖Complex.exp (-z * Complex.I)‖ :=
        norm_add_le _ _
      _ = Real.exp (-z.im) + Real.exp z.im := by
        rw [Complex.norm_exp, Complex.norm_exp]
        simp
  have hneg : Real.exp (-z.im) ≤ Real.exp |z.im| :=
    Real.exp_le_exp.mpr (neg_le_abs z.im)
  have hpos : Real.exp z.im ≤ Real.exp |z.im| :=
    Real.exp_le_exp.mpr (le_abs_self z.im)
  linarith

theorem norm_Gamma_mul_cos_pi_half_le
    (σ₁ σ₂ : ℝ) (hσ : σ₁ ≤ σ₂) :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 < C ∧
      ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → 2 ≤ |s.im| →
        ‖Complex.Gamma s * Complex.cos ((Real.pi : ℂ) * s / 2)‖ ≤
          C * |s.im| ^ A := by
  obtain ⟨A, C, hA, hC, hGamma⟩ :=
    complex_Gamma_stirling_upper_bound σ₁ σ₂ hσ
  refine ⟨A, C, hA, hC, fun s hs₁ hs₂ ht => ?_⟩
  rw [Complex.norm_mul]
  have harg_im : (((Real.pi : ℂ) * s / 2).im) = (Real.pi / 2) * s.im := by
    rw [Complex.div_im, Complex.mul_im]
    norm_num
    ring
  have harg_abs : |(((Real.pi : ℂ) * s / 2).im)| =
      (Real.pi / 2) * |s.im| := by
    rw [harg_im, abs_mul, abs_of_pos (by positivity : 0 < Real.pi / 2)]
  have hcos := norm_cos_le_exp_abs_im ((Real.pi : ℂ) * s / 2)
  rw [harg_abs] at hcos
  calc
    ‖Complex.Gamma s‖ * ‖Complex.cos ((Real.pi : ℂ) * s / 2)‖
        ≤ (C * |s.im| ^ A * Real.exp (-(Real.pi / 2) * |s.im|)) *
            Real.exp ((Real.pi / 2) * |s.im|) := by
          gcongr
          exact hGamma s hs₁ hs₂ ht
    _ = C * |s.im| ^ A := by
      rw [mul_assoc, ← Real.exp_add]
      ring_nf
      simp

end ArithmeticHodge.Analysis
