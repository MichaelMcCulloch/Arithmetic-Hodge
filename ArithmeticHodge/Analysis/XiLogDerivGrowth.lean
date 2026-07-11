import ArithmeticHodge.Analysis.ZetaProduct

/-!
# Quantitative xi logarithmic-derivative growth

A lower bound on the distance to every nearby Hadamard zero gives a coarse
polynomial bound for `xi'/xi` on fixed vertical strips.  This is the analytic
estimate needed to make rapidly decaying Mellin weights kill horizontal
contour edges.
-/

set_option autoImplicit false

open Complex

namespace ArithmeticHodge.Analysis

noncomputable section

private theorem riemannZeta_ne_zero_of_xi_ne_zero_and_large_im
    {s : ℂ} (him : 2 ≤ |s.im|) (hxi : xiFunction s ≠ 0) :
    riemannZeta s ≠ 0 := by
  intro hzeta
  have hs1 : s ≠ 1 := by
    intro hs
    rw [hs] at him
    norm_num at him
  have hnottrivial : ¬ ∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, hn⟩
    have himzero : s.im = 0 := by rw [hn]; simp
    rw [himzero, abs_zero] at him
    norm_num at him
  have hre := nontrivial_zeta_zero_re s hzeta hnottrivial hs1
  exact hxi ((xiFunction_zero_iff hre.1 hre.2).2 hzeta)

/-- A quantitative separation from the Hadamard zeros gives a polynomial
bound for the completed-xi logarithmic derivative on a fixed vertical strip.
The deliberately coarse exponent is the one needed for contour-edge decay. -/
theorem xi_logDeriv_growth_of_ne_zero
    (sigmaLower sigmaUpper : ℝ) (hsigma : sigmaLower < sigmaUpper) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℂ) (delta : ℝ),
      sigmaLower ≤ s.re → s.re ≤ sigmaUpper → 4 ≤ |s.im| →
      xiFunction s ≠ 0 →
      0 < delta → delta ≤ 1 →
      (∀ n, ‖s - hadamardZeros n‖ ≤ 1 →
        delta ≤ ‖s - hadamardZeros n‖) →
      ‖logDeriv xiFunction s‖ ≤
        C * (1 + |s.im|) ^ 2 * (1 + delta⁻¹) := by
  obtain ⟨Czeta, hCzeta, hzetaBound⟩ :=
    zeta_logDeriv_growth sigmaLower sigmaUpper hsigma
  obtain ⟨Cpsi, hCpsi, hpsiBound⟩ :=
    digamma_growth_bound (sigmaLower / 2) (sigmaUpper / 2)
  let C : ℝ := Czeta + Cpsi + |Real.log Real.pi| + 2
  refine ⟨C, by dsimp [C]; linarith [abs_nonneg (Real.log Real.pi)], ?_⟩
  intro s delta hsigmaLower hsigmaUpper him hxi hdelta hdeltaOne hsep
  have himTwo : 2 ≤ |s.im| := by linarith
  have hzeta : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_xi_ne_zero_and_large_im himTwo hxi
  have hs0 : s ≠ 0 := by
    intro hs
    rw [hs] at him
    norm_num at him
  have hs1 : s ≠ 1 := by
    intro hs
    rw [hs] at him
    norm_num at him
  have hzetaGrowth := hzetaBound s delta hsigmaLower hsigmaUpper himTwo
    hzeta hdelta hdeltaOne hsep
  have hdivRe : (s / 2).re = s.re / 2 := by
    norm_num [Complex.div_re]
  have hdivImAbs : |(s / 2).im| = |s.im| / 2 := by
    rw [show (s / 2).im = s.im / 2 by norm_num [Complex.div_im], abs_div]
    norm_num
  have hhalfLower : sigmaLower / 2 ≤ (s / 2).re := by
    rw [hdivRe]
    linarith
  have hhalfUpper : (s / 2).re ≤ sigmaUpper / 2 := by
    rw [hdivRe]
    linarith
  have hhalfIm : 2 ≤ |(s / 2).im| := by
    rw [hdivImAbs]
    linarith
  have hpsi := hpsiBound (s / 2) hhalfLower hhalfUpper hhalfIm
  have hlogNonneg : 0 ≤ Real.log |(s / 2).im| :=
    Real.log_nonneg (by linarith)
  have hlogLe : Real.log |(s / 2).im| ≤ |s.im| := by
    calc
      Real.log |(s / 2).im| ≤ |(s / 2).im| :=
        Real.log_le_self (abs_nonneg _)
      _ ≤ |s.im| := by
        rw [hdivImAbs]
        linarith [abs_nonneg s.im]
  have hpsiPolynomial : ‖Complex.digamma (s / 2)‖ ≤
      Cpsi * (1 + |s.im|) ^ 2 * (1 + delta⁻¹) := by
    have hP : |s.im| ≤ (1 + |s.im|) ^ 2 * (1 + delta⁻¹) := by
      have hdeltaInv : 0 < delta⁻¹ := inv_pos.mpr hdelta
      have hsquare : |s.im| ≤ (1 + |s.im|) ^ 2 := by
        nlinarith [abs_nonneg s.im, sq_nonneg (1 + |s.im|)]
      have hfactor : (1 + |s.im|) ^ 2 ≤
          (1 + |s.im|) ^ 2 * (1 + delta⁻¹) := by
        nlinarith [sq_nonneg (1 + |s.im|)]
      exact hsquare.trans hfactor
    calc
      ‖Complex.digamma (s / 2)‖ ≤
          Cpsi * Real.log |(s / 2).im| := hpsi
      _ ≤ Cpsi * |s.im| := mul_le_mul_of_nonneg_left hlogLe hCpsi.le
      _ ≤ Cpsi * ((1 + |s.im|) ^ 2 * (1 + delta⁻¹)) :=
        mul_le_mul_of_nonneg_left hP hCpsi.le
      _ = Cpsi * (1 + |s.im|) ^ 2 * (1 + delta⁻¹) := by ring
  have hPone : 1 ≤ (1 + |s.im|) ^ 2 * (1 + delta⁻¹) := by
    have hdeltaInv : 0 < delta⁻¹ := inv_pos.mpr hdelta
    have hsquare : 1 ≤ (1 + |s.im|) ^ 2 := by
      nlinarith [abs_nonneg s.im]
    nlinarith [mul_nonneg (sub_nonneg.mpr hsquare) hdeltaInv.le]
  have hsNorm : 4 ≤ ‖s‖ := him.trans (Complex.abs_im_le_norm s)
  have hsOneNorm : 4 ≤ ‖s - 1‖ := by
    calc
      4 ≤ |s.im| := him
      _ = |(s - 1).im| := by simp
      _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
  have hpole0 : ‖(1 : ℂ) / s‖ ≤ 1 := by
    rw [norm_div, norm_one]
    exact (div_le_one (by positivity)).2 (by linarith)
  have hpole1 : ‖(1 : ℂ) / (s - 1)‖ ≤ 1 := by
    rw [norm_div, norm_one]
    exact (div_le_one (by positivity)).2 (by linarith)
  have hlogpi : ‖(Real.log Real.pi : ℂ) / 2‖ ≤
      |Real.log Real.pi| := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, norm_ofNat]
    have := abs_nonneg (Real.log Real.pi)
    linarith
  have hidentity := zeta_logDeriv_from_xi_explicit s hs1 hs0 hzeta
  have hxiIdentity : logDeriv xiFunction s =
      deriv riemannZeta s / riemannZeta s + 1 / s + 1 / (s - 1) -
        (Real.log Real.pi : ℂ) / 2 + Complex.digamma (s / 2) / 2 := by
    rw [logDeriv_apply]
    linear_combination -hidentity
  rw [hxiIdentity]
  have htriangle :
      ‖deriv riemannZeta s / riemannZeta s + 1 / s + 1 / (s - 1) -
          (Real.log Real.pi : ℂ) / 2 + Complex.digamma (s / 2) / 2‖ ≤
        ‖deriv riemannZeta s / riemannZeta s‖ + ‖(1 : ℂ) / s‖ +
          ‖(1 : ℂ) / (s - 1)‖ + ‖(Real.log Real.pi : ℂ) / 2‖ +
            ‖Complex.digamma (s / 2)‖ / 2 := by
    calc
      _ ≤ ‖deriv riemannZeta s / riemannZeta s + 1 / s + 1 / (s - 1) -
          (Real.log Real.pi : ℂ) / 2‖ + ‖Complex.digamma (s / 2) / 2‖ :=
        norm_add_le _ _
      _ ≤ ‖deriv riemannZeta s / riemannZeta s + 1 / s + 1 / (s - 1)‖ +
          ‖(Real.log Real.pi : ℂ) / 2‖ + ‖Complex.digamma (s / 2) / 2‖ := by
        gcongr
        exact norm_sub_le _ _
      _ ≤ ‖deriv riemannZeta s / riemannZeta s + 1 / s‖ +
          ‖(1 : ℂ) / (s - 1)‖ + ‖(Real.log Real.pi : ℂ) / 2‖ +
            ‖Complex.digamma (s / 2) / 2‖ := by
        gcongr
        exact norm_add_le _ _
      _ ≤ ‖deriv riemannZeta s / riemannZeta s‖ + ‖(1 : ℂ) / s‖ +
          ‖(1 : ℂ) / (s - 1)‖ + ‖(Real.log Real.pi : ℂ) / 2‖ +
            ‖Complex.digamma (s / 2) / 2‖ := by
        gcongr
        exact norm_add_le _ _
      _ = _ := by simp only [norm_div, norm_ofNat]
  calc
    _ ≤ ‖deriv riemannZeta s / riemannZeta s‖ + ‖(1 : ℂ) / s‖ +
          ‖(1 : ℂ) / (s - 1)‖ + ‖(Real.log Real.pi : ℂ) / 2‖ +
            ‖Complex.digamma (s / 2)‖ / 2 := htriangle
    _ ≤ Czeta * (1 + |s.im|) ^ 2 * (1 + delta⁻¹) + 1 + 1 +
          |Real.log Real.pi| +
            (Cpsi * (1 + |s.im|) ^ 2 * (1 + delta⁻¹)) / 2 := by
      gcongr
    _ ≤ C * (1 + |s.im|) ^ 2 * (1 + delta⁻¹) := by
      dsimp [C]
      nlinarith [hCzeta, hCpsi,
        mul_nonneg (sq_nonneg (1 + |s.im|))
          (by linarith [inv_pos.mpr hdelta] : 0 ≤ 1 + delta⁻¹),
        mul_le_mul_of_nonneg_left hPone
          (by linarith [abs_nonneg (Real.log Real.pi)] :
            0 ≤ Cpsi / 2 + |Real.log Real.pi| + 2)]

end

end ArithmeticHodge.Analysis
