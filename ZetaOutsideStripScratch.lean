import DirichletBoundScratch
import StirlingUpperScratch

open Complex Real

namespace ArithmeticHodge.Analysis

theorem riemannZeta_polynomial_bound_of_re_le_neg
    (σ₁ σ₂ : ℝ) (hσ : σ₁ ≤ σ₂) (hσ₂ : σ₂ < 0) :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 < C ∧
      ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → 2 ≤ |s.im| →
        ‖riemannZeta s‖ ≤ C * |s.im| ^ A := by
  have hqstrip : 1 - σ₂ ≤ 1 - σ₁ := by linarith
  obtain ⟨A, CΓ, hA, hCΓ, hΓcos⟩ :=
    norm_Gamma_mul_cos_pi_half_le (1 - σ₂) (1 - σ₁) hqstrip
  obtain ⟨Cζ, hCζ, hζ⟩ :=
    riemannZeta_dirichlet_uniform_bound (1 - σ₂) (by linarith)
  refine ⟨A, 2 * CΓ * Cζ, hA, by positivity, fun s hs₁ hs₂ ht => ?_⟩
  let q : ℂ := 1 - s
  have hq_re_lo : 1 - σ₂ ≤ q.re := by
    dsimp [q]
    linarith
  have hq_re_hi : q.re ≤ 1 - σ₁ := by
    dsimp [q]
    linarith
  have hq_im_abs : |q.im| = |s.im| := by
    simp [q]
  have hq_im : 2 ≤ |q.im| := by simpa [hq_im_abs] using ht
  have hΓcos_q := hΓcos q hq_re_lo hq_re_hi hq_im
  rw [hq_im_abs] at hΓcos_q
  have hζ_q := hζ q hq_re_lo
  have hq_ne_neg_nat : ∀ n : ℕ, q ≠ -n := by
    intro n hqn
    have hre := congr_arg Complex.re hqn
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    linarith
  have hq_ne_one : q ≠ 1 := by
    intro hq1
    have hre := congr_arg Complex.re hq1
    simp only [Complex.one_re] at hre
    linarith
  have hFE : riemannZeta s =
      2 * (2 * (Real.pi : ℂ)) ^ (-q) *
        (Complex.Gamma q * Complex.cos ((Real.pi : ℂ) * q / 2)) *
          riemannZeta q := by
    calc
      riemannZeta s = riemannZeta (1 - q) := by simp [q]
      _ = 2 * (2 * (Real.pi : ℂ)) ^ (-q) * Complex.Gamma q *
          Complex.cos ((Real.pi : ℂ) * q / 2) * riemannZeta q :=
        riemannZeta_one_sub hq_ne_neg_nat hq_ne_one
      _ = 2 * (2 * (Real.pi : ℂ)) ^ (-q) *
          (Complex.Gamma q * Complex.cos ((Real.pi : ℂ) * q / 2)) *
            riemannZeta q := by ring
  have hpow : ‖(2 * (Real.pi : ℂ)) ^ (-q)‖ ≤ 1 := by
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < 2 * Real.pi)]
    calc
      (2 * Real.pi) ^ (-q).re ≤ (2 * Real.pi) ^ (0 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le
        · nlinarith [Real.pi_gt_three]
        · simp only [Complex.neg_re]
          linarith
      _ = 1 := by simp
  rw [hFE]
  rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_mul, Complex.norm_ofNat]
  calc
    2 * ‖(2 * (Real.pi : ℂ)) ^ (-q)‖ *
          ‖Complex.Gamma q * Complex.cos ((Real.pi : ℂ) * q / 2)‖ *
            ‖riemannZeta q‖
        ≤ 2 * 1 * (CΓ * |s.im| ^ A) * Cζ := by gcongr
    _ = (2 * CΓ * Cζ) * |s.im| ^ A := by ring

theorem zeta_vertical_strip_bound_outside_critical_strip
    (σ₁ σ₂ : ℝ) (hσ : σ₁ ≤ σ₂)
    (hout : 1 < σ₁ ∨ σ₂ < 0) :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 < C ∧
      ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → 2 ≤ |s.im| →
        ‖riemannZeta s‖ ≤ C * |s.im| ^ A := by
  rcases hout with hright | hleft
  · obtain ⟨C, hC, hζ⟩ := riemannZeta_dirichlet_uniform_bound σ₁ hright
    refine ⟨0, C, le_rfl, hC, fun s hs₁ _hs₂ _ht => ?_⟩
    simpa using hζ s hs₁
  · exact riemannZeta_polynomial_bound_of_re_le_neg σ₁ σ₂ hσ hleft

end ArithmeticHodge.Analysis
