import ArithmeticHodge.Analysis.ComplexStirling

open Complex Real

namespace ArithmeticHodge.Analysis

theorem complex_Gamma_stirling_lower_bound_scratch
    (σ₁ σ₂ : ℝ) (hσ : σ₁ ≤ σ₂) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → 2 ≤ |s.im| →
        |s.im| ^ (-A) * Real.exp (-(Real.pi / 2) * |s.im|) ≤
          ‖Complex.Gamma s‖ := by
  obtain ⟨D, _hD_pos, hD⟩ := complex_stirling_bound σ₁ σ₂ hσ
  let A : ℝ := max 0 (1 / 2 + D - σ₁)
  refine ⟨A, le_max_left _ _, fun s hs₁ hs₂ ht => ?_⟩
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
    apply him_ne
    simpa using congr_arg Complex.im hsm
  have hGamma_pos : 0 < ‖Complex.Gamma s‖ := norm_pos_iff.mpr hGamma_ne
  have hstirling := hD s hs₁ hs₂ ht
  have herror₀ := (abs_le.mp hstirling).1
  have herror : -D * L ≤
      Real.log ‖Complex.Gamma s‖ -
        ((s.re - 1 / 2) * L - T * (Real.pi / 2)) := by
    dsimp [T, L]
    nlinarith
  have hcoeff : -A ≤ s.re - 1 / 2 - D := by
    have hA : 1 / 2 + D - σ₁ ≤ A := le_max_right _ _
    linarith
  have hlog :
      (-A) * L - (Real.pi / 2) * T ≤
        Real.log ‖Complex.Gamma s‖ := by
    calc
      (-A) * L - (Real.pi / 2) * T
          ≤ (s.re - 1 / 2 - D) * L - (Real.pi / 2) * T := by
            gcongr
      _ ≤ Real.log ‖Complex.Gamma s‖ := by linarith
  calc
    |s.im| ^ (-A) * Real.exp (-(Real.pi / 2) * |s.im|)
        = Real.exp ((-A) * L - (Real.pi / 2) * T) := by
          rw [Real.rpow_def_of_pos (by simpa [T] using hT_pos), ← Real.exp_add]
          dsimp [T, L]
          congr 1
          ring_nf
    _ ≤ Real.exp (Real.log ‖Complex.Gamma s‖) := Real.exp_le_exp.mpr hlog
    _ = ‖Complex.Gamma s‖ := Real.exp_log hGamma_pos

theorem Gammaℝ_stirling_lower_bound_scratch
    (σ₁ σ₂ : ℝ) (hσ : σ₁ ≤ σ₂) :
    ∃ A c : ℝ, 0 ≤ A ∧ 0 < c ∧
      ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → 4 ≤ |s.im| →
        c * |s.im| ^ (-A) * Real.exp (-(Real.pi / 4) * |s.im|) ≤
          ‖Complex.Gammaℝ s‖ := by
  have hhalf_strip : σ₁ / 2 ≤ σ₂ / 2 := by linarith
  obtain ⟨A, hA, hGamma⟩ :=
    complex_Gamma_stirling_lower_bound_scratch (σ₁ / 2) (σ₂ / 2) hhalf_strip
  let c : ℝ := Real.pi ^ (-σ₂ / 2)
  have hc : 0 < c := Real.rpow_pos_of_pos Real.pi_pos _
  refine ⟨A, c, hA, hc, fun s hs₁ hs₂ ht => ?_⟩
  let T : ℝ := |s.im|
  let q : ℂ := s / 2
  have hT : 4 ≤ T := by simpa [T] using ht
  have hT_pos : 0 < T := by linarith
  have hq_re_lo : σ₁ / 2 ≤ q.re := by
    dsimp [q]
    norm_num [Complex.div_re]
    linarith
  have hq_re_hi : q.re ≤ σ₂ / 2 := by
    dsimp [q]
    norm_num [Complex.div_re]
    linarith
  have hq_im_abs : |q.im| = T / 2 := by
    dsimp [q, T]
    norm_num [Complex.div_im, abs_div]
  have hq_im : 2 ≤ |q.im| := by rw [hq_im_abs]; linarith
  have hGamma_q := hGamma q hq_re_lo hq_re_hi hq_im
  rw [hq_im_abs] at hGamma_q
  have hGamma_q' :
      (T / 2) ^ (-A) * Real.exp (-(Real.pi / 4) * T) ≤
        ‖Complex.Gamma q‖ := by
    calc
      (T / 2) ^ (-A) * Real.exp (-(Real.pi / 4) * T) =
          (T / 2) ^ (-A) * Real.exp (-(Real.pi / 2) * (T / 2)) := by ring_nf
      _ ≤ ‖Complex.Gamma q‖ := hGamma_q
  have hfactor_norm :
      ‖(Real.pi : ℂ) ^ (-s / 2)‖ = Real.pi ^ (-s.re / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    norm_num [Complex.div_re]
  have hfactor : c ≤ ‖(Real.pi : ℂ) ^ (-s / 2)‖ := by
    rw [hfactor_norm]
    dsimp [c]
    apply Real.rpow_le_rpow_of_exponent_le
    · linarith [Real.pi_gt_three]
    · linarith
  have hpoly : T ^ (-A) ≤ (T / 2) ^ (-A) := by
    rw [Real.rpow_neg hT_pos.le, Real.rpow_neg (by positivity : 0 ≤ T / 2)]
    apply (inv_le_inv₀ (Real.rpow_pos_of_pos hT_pos A)
      (Real.rpow_pos_of_pos (by positivity : 0 < T / 2) A)).2
    exact Real.rpow_le_rpow (by positivity) (by linarith) hA
  rw [Complex.Gammaℝ_def, Complex.norm_mul]
  calc
    c * |s.im| ^ (-A) * Real.exp (-(Real.pi / 4) * |s.im|)
        = c * T ^ (-A) * Real.exp (-(Real.pi / 4) * T) := by rfl
    _ ≤ (‖(Real.pi : ℂ) ^ (-s / 2)‖ * (T / 2) ^ (-A)) *
          Real.exp (-(Real.pi / 4) * T) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            exact mul_le_mul hfactor hpoly (Real.rpow_nonneg (by positivity) _)
              (norm_nonneg _)
    _ = ‖(Real.pi : ℂ) ^ (-s / 2)‖ *
          ((T / 2) ^ (-A) * Real.exp (-(Real.pi / 4) * T)) := by ring_nf
    _ ≤ ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma q‖ := by
            gcongr
    _ = ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖ := by rfl

theorem norm_Gammaℝ_inv_stirling_upper_bound_scratch
    (σ₁ σ₂ : ℝ) (hσ : σ₁ ≤ σ₂) :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 < C ∧
      ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → 4 ≤ |s.im| →
        ‖(Complex.Gammaℝ s)⁻¹‖ ≤
          C * |s.im| ^ A * Real.exp ((Real.pi / 4) * |s.im|) := by
  obtain ⟨A, c, hA, hc, hlower⟩ := Gammaℝ_stirling_lower_bound_scratch σ₁ σ₂ hσ
  refine ⟨A, c⁻¹, hA, inv_pos.mpr hc, fun s hs₁ hs₂ ht => ?_⟩
  let T : ℝ := |s.im|
  have hT : 4 ≤ T := by simpa [T] using ht
  have hT_pos : 0 < T := by linarith
  have him_ne : s.im ≠ 0 := by
    intro him
    rw [him, abs_zero] at ht
    norm_num at ht
  have hGammaℝ_ne : Complex.Gammaℝ s ≠ 0 := by
    intro hΓ
    rw [Complex.Gammaℝ_eq_zero_iff] at hΓ
    obtain ⟨n, hsn⟩ := hΓ
    apply him_ne
    simpa using congr_arg Complex.im hsn
  have hnorm_pos : 0 < ‖Complex.Gammaℝ s‖ := norm_pos_iff.mpr hGammaℝ_ne
  have hlower_s := hlower s hs₁ hs₂ ht
  have hminor_pos : 0 < c * T ^ (-A) * Real.exp (-(Real.pi / 4) * T) := by
    positivity
  have hinv : ‖Complex.Gammaℝ s‖⁻¹ ≤
      (c * T ^ (-A) * Real.exp (-(Real.pi / 4) * T))⁻¹ := by
    exact (inv_le_inv₀ hnorm_pos hminor_pos).2 hlower_s
  rw [norm_inv]
  calc
    ‖Complex.Gammaℝ s‖⁻¹
        ≤ (c * T ^ (-A) * Real.exp (-(Real.pi / 4) * T))⁻¹ := hinv
    _ = c⁻¹ * T ^ A * Real.exp ((Real.pi / 4) * T) := by
      rw [Real.rpow_neg hT_pos.le]
      rw [show -(Real.pi / 4) * T = -((Real.pi / 4) * T) by ring_nf,
        Real.exp_neg]
      field_simp
    _ = c⁻¹ * |s.im| ^ A * Real.exp ((Real.pi / 4) * |s.im|) := by rfl

end ArithmeticHodge.Analysis
