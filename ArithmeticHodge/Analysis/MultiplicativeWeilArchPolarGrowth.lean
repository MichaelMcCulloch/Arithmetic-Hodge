import ArithmeticHodge.Analysis.MultiplicativeWeilVerticalBoundary

/-!
# Growth of the Bombieri archimedean-polar factor

This module supplies a deliberately coarse uniform quartic bound on horizontal
segments.  Combined with rapid Mellin decay, it makes the horizontal
archimedean-polar boundary terms vanish along the selected contour sequence.
-/

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- On a fixed horizontal strip, the archimedean/polar factor has a uniform
quartic bound along any sequence of heights at least four. -/
theorem bombieriArchPolar_quartic_bound
    (sigma : ℝ) (_hsigma : 1 < sigma) (T : ℕ → ℝ)
    (hT : ∀ n, 4 ≤ T n) :
    ∃ C : ℝ, 0 < C ∧ ∀ n x, x ∈ Set.Icc (1 / 2 : ℝ) sigma →
      (‖bombieriArchPolar ((x : ℂ) + T n * I)‖ ≤
          C * (1 + |T n|) ^ 4) ∧
        ‖bombieriArchPolar ((x : ℂ) - T n * I)‖ ≤
          C * (1 + |T n|) ^ 4 := by
  obtain ⟨D, hD, hdigamma⟩ :=
    digamma_growth_bound (1 / 4 : ℝ) (sigma / 2)
  let C : ℝ := D + |Real.log Real.pi| + 3
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro n x hx
  have hTpos : 0 < T n := by linarith [hT n]
  have hTabs : |T n| = T n := abs_of_pos hTpos
  have hedge (s : ℂ) (hsre : s.re = x) (hsim : |s.im| = T n) :
      ‖bombieriArchPolar s‖ ≤ C * (1 + |T n|) ^ 4 := by
    have hhalfRe : (s / 2).re = x / 2 := by
      rw [show (s / 2).re = s.re / 2 by norm_num [Complex.div_re], hsre]
    have hhalfIm : |(s / 2).im| = T n / 2 := by
      rw [show (s / 2).im = s.im / 2 by norm_num [Complex.div_im], abs_div,
        hsim]
      norm_num
    have hpsi := hdigamma (s / 2)
      (by rw [hhalfRe]; linarith [hx.1])
      (by rw [hhalfRe]; linarith [hx.2])
      (by rw [hhalfIm]; linarith [hT n])
    have hlogLe : Real.log |(s / 2).im| ≤ |T n| := by
      calc
        Real.log |(s / 2).im| ≤ |(s / 2).im| :=
          Real.log_le_self (abs_nonneg _)
        _ = T n / 2 := hhalfIm
        _ ≤ |T n| := by rw [hTabs]; linarith [hT n]
    have hpsiLinear : ‖Complex.digamma (s / 2)‖ ≤ D * |T n| := by
      exact hpsi.trans (mul_le_mul_of_nonneg_left hlogLe hD.le)
    have hsNorm : 4 ≤ ‖s‖ := by
      calc
        4 ≤ T n := hT n
        _ = |s.im| := hsim.symm
        _ ≤ ‖s‖ := Complex.abs_im_le_norm s
    have hsOneNorm : 4 ≤ ‖s - 1‖ := by
      calc
        4 ≤ T n := hT n
        _ = |(s - 1).im| := by simpa using hsim.symm
        _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm (s - 1)
    have hpole0 : ‖(1 : ℂ) / s‖ ≤ 1 := by
      rw [norm_div, norm_one]
      exact (div_le_one (by positivity)).2 (by linarith)
    have hpole1 : ‖(1 : ℂ) / (s - 1)‖ ≤ 1 := by
      rw [norm_div, norm_one]
      exact (div_le_one (by positivity)).2 (by linarith)
    have hlogpi : ‖(Real.log Real.pi : ℂ) / 2‖ ≤
        |Real.log Real.pi| := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat]
      linarith [abs_nonneg (Real.log Real.pi)]
    have htriangle :
        ‖bombieriArchPolar s‖ ≤
          ‖(1 : ℂ) / s‖ + ‖(1 : ℂ) / (s - 1)‖ +
            ‖(Real.log Real.pi : ℂ) / 2‖ +
              ‖Complex.digamma (s / 2)‖ / 2 := by
      rw [bombieriArchPolar]
      calc
        ‖1 / s + 1 / (s - 1) - (Real.log Real.pi : ℂ) / 2 +
            Complex.digamma (s / 2) / 2‖ ≤
            ‖1 / s + 1 / (s - 1) - (Real.log Real.pi : ℂ) / 2‖ +
              ‖Complex.digamma (s / 2) / 2‖ := norm_add_le _ _
        _ ≤ ‖1 / s + 1 / (s - 1)‖ +
              ‖(Real.log Real.pi : ℂ) / 2‖ +
                ‖Complex.digamma (s / 2) / 2‖ := by
          gcongr
          exact norm_sub_le _ _
        _ ≤ ‖(1 : ℂ) / s‖ + ‖(1 : ℂ) / (s - 1)‖ +
              ‖(Real.log Real.pi : ℂ) / 2‖ +
                ‖Complex.digamma (s / 2) / 2‖ := by
          gcongr
          exact norm_add_le _ _
        _ = _ := by simp only [norm_div, Complex.norm_ofNat]
    have hbase : 1 ≤ 1 + |T n| := by linarith [abs_nonneg (T n)]
    have hbasePow : 1 + |T n| ≤ (1 + |T n|) ^ 4 :=
      le_self_pow₀ hbase (by norm_num)
    have hPone : 1 ≤ (1 + |T n|) ^ 4 := hbase.trans hbasePow
    have hPt : |T n| ≤ (1 + |T n|) ^ 4 := by
      exact (by linarith [abs_nonneg (T n)] : |T n| ≤ 1 + |T n|).trans hbasePow
    calc
      ‖bombieriArchPolar s‖ ≤
          ‖(1 : ℂ) / s‖ + ‖(1 : ℂ) / (s - 1)‖ +
            ‖(Real.log Real.pi : ℂ) / 2‖ +
              ‖Complex.digamma (s / 2)‖ / 2 := htriangle
      _ ≤ 1 + 1 + |Real.log Real.pi| + (D * |T n|) / 2 := by
        gcongr
      _ ≤ C * (1 + |T n|) ^ 4 := by
        dsimp only [C]
        nlinarith [hD, abs_nonneg (Real.log Real.pi), hPone, hPt,
          mul_nonneg hD.le (abs_nonneg (T n))]
  constructor
  · apply hedge ((x : ℂ) + T n * I)
    · simp
    · simp [hTabs]
  · apply hedge ((x : ℂ) - T n * I)
    · simp
    · simp [hTabs]

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
