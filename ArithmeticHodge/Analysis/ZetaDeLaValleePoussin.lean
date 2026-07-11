import ArithmeticHodge.Analysis.ZetaHadamardZeroRepulsion
import ArithmeticHodge.Analysis.ZetaLogDerivRealBound
import ArithmeticHodge.Analysis.ZetaLogDerivRepulsionAlgebra
import ArithmeticHodge.Analysis.MultiplicativeWeilLiSeries

/-!
# A logarithmic de la Vallée-Poussin zero-free region

This module closes the analytic estimates left in the explicit
`3-4-1` chosen-zero inequality.  Constants are intentionally coarse: the
horizontal shift is chosen after the archimedean constants, so no numerical
optimization is needed.
-/

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- The zero-independent correction in the explicit Hadamard partial
fraction for `-zeta'/zeta`. -/
private def zetaHadamardCorrection (sigma t : ℝ) : ℂ :=
  -(hadamardM : ℂ) / ((sigma : ℂ) + t * I) - hadamardB +
    1 / ((sigma : ℂ) + t * I) +
    1 / (((sigma : ℂ) + t * I) - 1) -
    (Real.log Real.pi : ℂ) / 2 +
    Complex.digamma (((sigma : ℂ) + t * I) / 2) / 2

/-- To the right of the critical strip, dropping the Hadamard zero sum gives
an upper bound for the real part of `-zeta'/zeta`. -/
theorem negZetaLogDeriv_re_le_hadamardCorrection
    {sigma : ℝ} (hsigma : 1 < sigma) (t : ℝ) :
    (-(deriv riemannZeta ((sigma : ℂ) + t * I) /
      riemannZeta ((sigma : ℂ) + t * I))).re ≤
      (zetaHadamardCorrection sigma t).re := by
  let s : ℂ := (sigma : ℂ) + t * I
  let zeroSum : ℂ := ∑' n,
    (1 / (s - hadamardZeros n) + 1 / hadamardZeros n)
  have hsre : 1 < s.re := by simpa [s]
  have hs0 : s ≠ 0 := by
    intro hzero
    have hzre := congrArg Complex.re hzero
    simp [s] at hzre
    linarith
  have hs1 : s ≠ 1 := by
    intro hone
    have hzre := congrArg Complex.re hone
    simp [s] at hzre
    linarith
  have hzeta : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re hsre
  have hsep : ∀ n, s ≠ hadamardZeros n := by
    intro n heq
    have hreEq := congrArg Complex.re heq
    simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_self,
      add_zero] at hreEq
    linarith [(hadamardZeros_re n).2]
  obtain ⟨hsumm, hpf⟩ :=
    zeta_logDeriv_partial_fraction_explicit s hs1 hs0 hzeta hsep
  have hreSumm : Summable (fun n =>
      (1 / (s - hadamardZeros n) + 1 / hadamardZeros n).re) :=
    (Complex.hasSum_re hsumm.hasSum).summable
  have hsumNonneg : 0 ≤ zeroSum.re := by
    rw [show zeroSum.re = ∑' n,
        (1 / (s - hadamardZeros n) + 1 / hadamardZeros n).re by
      exact Complex.re_tsum hsumm]
    apply tsum_nonneg
    intro n
    simpa only [s] using
      hadamardPartialFractionTerm_re_nonneg hsigma n
  have heq :
      -(deriv riemannZeta s / riemannZeta s) =
        zetaHadamardCorrection sigma t - zeroSum := by
    rw [hpf]
    dsimp only [zetaHadamardCorrection, zeroSum, s]
    ring
  have hreEq := congrArg Complex.re heq
  simp only [Complex.sub_re] at hreEq
  change (-(deriv riemannZeta s / riemannZeta s)).re ≤
    (zetaHadamardCorrection sigma t).re
  linarith

/-- On `1 ≤ sigma ≤ 2` and above height four, the explicit correction is
bounded by a constant times the padded logarithm of the height. -/
theorem exists_hadamardCorrection_high_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ sigma t : ℝ,
      1 ≤ sigma → sigma ≤ 2 → 4 ≤ |t| →
      (zetaHadamardCorrection sigma t).re ≤
        C * Real.log (|t| + 2) := by
  obtain ⟨D, hDpos, hD⟩ := digamma_growth_bound (1 / 2 : ℝ) 1
  let C : ℝ :=
    (hadamardM : ℝ) + ‖hadamardB‖ + |Real.log Real.pi| + D + 4
  refine ⟨C, by
    dsimp only [C]
    positivity, ?_⟩
  intro sigma t hsigma1 hsigma2 ht
  let s : ℂ := (sigma : ℂ) + t * I
  let L : ℝ := Real.log (|t| + 2)
  have hLone : 1 ≤ L := by
    dsimp only [L]
    calc
      (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (|t| + 2) := by
        apply Real.log_le_log (Real.exp_pos 1)
        linarith [Real.exp_one_lt_three]
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hLone
  have hsNorm : 4 ≤ ‖s‖ := by
    calc
      4 ≤ |t| := ht
      _ = |s.im| := by simp [s]
      _ ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hsOneNorm : 4 ≤ ‖s - 1‖ := by
    calc
      4 ≤ |t| := ht
      _ = |(s - 1).im| := by simp [s]
      _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm (s - 1)
  have hMterm : ‖-(hadamardM : ℂ) / s‖ ≤ (hadamardM : ℝ) := by
    rw [norm_div, norm_neg, Complex.norm_natCast]
    exact div_le_self (Nat.cast_nonneg hadamardM) (by linarith)
  have hpole0 : ‖(1 : ℂ) / s‖ ≤ 1 := by
    rw [norm_div, norm_one]
    exact (div_le_one (by positivity)).2 (by linarith)
  have hpole1 : ‖(1 : ℂ) / (s - 1)‖ ≤ 1 := by
    rw [norm_div, norm_one]
    exact (div_le_one (by positivity)).2 (by linarith)
  have hlogpi : ‖(Real.log Real.pi : ℂ) / 2‖ ≤
      |Real.log Real.pi| := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_ofNat]
    linarith [abs_nonneg (Real.log Real.pi)]
  have hhalfRe : (s / 2).re = sigma / 2 := by
    dsimp only [s]
    norm_num [Complex.div_re]
  have hhalfIm : |(s / 2).im| = |t| / 2 := by
    dsimp only [s]
    rw [show (((sigma : ℂ) + t * I) / 2).im = t / 2 by
      norm_num [Complex.div_im], abs_div]
    norm_num
  have hpsi := hD (s / 2)
    (by rw [hhalfRe]; linarith)
    (by rw [hhalfRe]; linarith)
    (by rw [hhalfIm]; linarith)
  have hhalfImPos : 0 < |(s / 2).im| := by
    rw [hhalfIm]
    linarith
  have hhalfImLe : |(s / 2).im| ≤ |t| + 2 := by
    rw [hhalfIm]
    linarith [abs_nonneg t]
  have hlogLe : Real.log |(s / 2).im| ≤ L := by
    dsimp only [L]
    exact Real.log_le_log hhalfImPos hhalfImLe
  have hpsiL : ‖Complex.digamma (s / 2)‖ ≤ D * L :=
    hpsi.trans (mul_le_mul_of_nonneg_left hlogLe hDpos.le)
  have htriangle : ‖zetaHadamardCorrection sigma t‖ ≤
      ‖-(hadamardM : ℂ) / s‖ + ‖hadamardB‖ +
        ‖(1 : ℂ) / s‖ + ‖(1 : ℂ) / (s - 1)‖ +
          ‖(Real.log Real.pi : ℂ) / 2‖ +
            ‖Complex.digamma (s / 2)‖ / 2 := by
    change ‖-(hadamardM : ℂ) / s - hadamardB + 1 / s +
        1 / (s - 1) - (Real.log Real.pi : ℂ) / 2 +
          Complex.digamma (s / 2) / 2‖ ≤ _
    calc
      _ ≤ ‖-(hadamardM : ℂ) / s - hadamardB + 1 / s +
          1 / (s - 1) - (Real.log Real.pi : ℂ) / 2‖ +
            ‖Complex.digamma (s / 2) / 2‖ := norm_add_le _ _
      _ ≤ ‖-(hadamardM : ℂ) / s - hadamardB + 1 / s +
          1 / (s - 1)‖ + ‖(Real.log Real.pi : ℂ) / 2‖ +
            ‖Complex.digamma (s / 2) / 2‖ := by
        gcongr
        exact norm_sub_le _ _
      _ ≤ ‖-(hadamardM : ℂ) / s - hadamardB + 1 / s‖ +
          ‖(1 : ℂ) / (s - 1)‖ +
            ‖(Real.log Real.pi : ℂ) / 2‖ +
              ‖Complex.digamma (s / 2) / 2‖ := by
        gcongr
        exact norm_add_le _ _
      _ ≤ ‖-(hadamardM : ℂ) / s - hadamardB‖ +
          ‖(1 : ℂ) / s‖ + ‖(1 : ℂ) / (s - 1)‖ +
            ‖(Real.log Real.pi : ℂ) / 2‖ +
              ‖Complex.digamma (s / 2) / 2‖ := by
        gcongr
        exact norm_add_le _ _
      _ ≤ ‖-(hadamardM : ℂ) / s‖ + ‖hadamardB‖ +
          ‖(1 : ℂ) / s‖ + ‖(1 : ℂ) / (s - 1)‖ +
            ‖(Real.log Real.pi : ℂ) / 2‖ +
              ‖Complex.digamma (s / 2) / 2‖ := by
        gcongr
        exact norm_sub_le _ _
      _ = _ := by simp only [norm_div, Complex.norm_ofNat]
  have hbaseNonneg :
      0 ≤ (hadamardM : ℝ) + ‖hadamardB‖ +
        |Real.log Real.pi| + 2 := by positivity
  calc
    (zetaHadamardCorrection sigma t).re ≤
        ‖zetaHadamardCorrection sigma t‖ := Complex.re_le_norm _
    _ ≤ ‖-(hadamardM : ℂ) / s‖ + ‖hadamardB‖ +
        ‖(1 : ℂ) / s‖ + ‖(1 : ℂ) / (s - 1)‖ +
          ‖(Real.log Real.pi : ℂ) / 2‖ +
            ‖Complex.digamma (s / 2)‖ / 2 := htriangle
    _ ≤ (hadamardM : ℝ) + ‖hadamardB‖ + 1 + 1 +
          |Real.log Real.pi| + (D * L) / 2 := by gcongr
    _ ≤ ((hadamardM : ℝ) + ‖hadamardB‖ +
          |Real.log Real.pi| + 2) * L + (D * L) / 2 := by
      nlinarith [mul_nonneg hbaseNonneg (sub_nonneg.mpr hLone)]
    _ ≤ C * L := by
      dsimp only [C]
      nlinarith [mul_nonneg hDpos.le hLpos.le]
    _ = C * Real.log (|t| + 2) := rfl

/-- On the positive real axis immediately to the right of the pole, the
logarithmic derivative has its expected `1 / x + O(1)` upper bound. -/
theorem exists_negZetaLogDeriv_real_near_one_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 < x → x ≤ 1 →
      (-(deriv riemannZeta ((1 + x : ℝ) : ℂ) /
        riemannZeta ((1 + x : ℝ) : ℂ))).re ≤ 1 / x + C := by
  obtain ⟨D, hDpos, hD⟩ := exists_digamma_half_real_bound
  let C : ℝ :=
    (hadamardM : ℝ) + ‖hadamardB‖ + |Real.log Real.pi| + D + 3
  refine ⟨C, by
    dsimp only [C]
    positivity, ?_⟩
  intro x hx hx1
  let s : ℂ := ((1 + x : ℝ) : ℂ) + 0 * I
  have hsigma : 1 < 1 + x := by linarith
  have hdrop :=
    negZetaLogDeriv_re_le_hadamardCorrection hsigma 0
  have hsNorm : 1 ≤ ‖s‖ := by
    dsimp only [s]
    simp only [zero_mul, add_zero]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  have hMterm : ‖-(hadamardM : ℂ) / s‖ ≤ (hadamardM : ℝ) := by
    rw [norm_div, norm_neg, Complex.norm_natCast]
    exact div_le_self (Nat.cast_nonneg hadamardM) hsNorm
  have hpole0 : ‖(1 : ℂ) / s‖ ≤ 1 := by
    rw [norm_div, norm_one]
    exact (div_le_one (by positivity)).2 hsNorm
  have hsSubOne : s - 1 = (x : ℂ) := by
    apply Complex.ext <;> simp [s]
  have hpole1 : ‖(1 : ℂ) / (s - 1)‖ = 1 / x := by
    rw [hsSubOne, norm_div, norm_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hx]
  have hlogpi : ‖(Real.log Real.pi : ℂ) / 2‖ ≤
      |Real.log Real.pi| := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_ofNat]
    linarith [abs_nonneg (Real.log Real.pi)]
  have hpsi : ‖Complex.digamma (s / 2)‖ ≤ D := by
    have hbase := hD (1 + x) (by linarith) (by linarith)
    simpa only [s, Complex.ofReal_add, Complex.ofReal_one,
      Complex.ofReal_div, Complex.ofReal_ofNat, zero_mul, add_zero] using hbase
  have htriangle : ‖zetaHadamardCorrection (1 + x) 0‖ ≤
      ‖-(hadamardM : ℂ) / s‖ + ‖hadamardB‖ +
        ‖(1 : ℂ) / s‖ + ‖(1 : ℂ) / (s - 1)‖ +
          ‖(Real.log Real.pi : ℂ) / 2‖ +
            ‖Complex.digamma (s / 2)‖ / 2 := by
    change ‖-(hadamardM : ℂ) / s - hadamardB + 1 / s +
        1 / (s - 1) - (Real.log Real.pi : ℂ) / 2 +
          Complex.digamma (s / 2) / 2‖ ≤ _
    calc
      _ ≤ ‖-(hadamardM : ℂ) / s - hadamardB + 1 / s +
          1 / (s - 1) - (Real.log Real.pi : ℂ) / 2‖ +
            ‖Complex.digamma (s / 2) / 2‖ := norm_add_le _ _
      _ ≤ ‖-(hadamardM : ℂ) / s - hadamardB + 1 / s +
          1 / (s - 1)‖ + ‖(Real.log Real.pi : ℂ) / 2‖ +
            ‖Complex.digamma (s / 2) / 2‖ := by
        gcongr
        exact norm_sub_le _ _
      _ ≤ ‖-(hadamardM : ℂ) / s - hadamardB + 1 / s‖ +
          ‖(1 : ℂ) / (s - 1)‖ +
            ‖(Real.log Real.pi : ℂ) / 2‖ +
              ‖Complex.digamma (s / 2) / 2‖ := by
        gcongr
        exact norm_add_le _ _
      _ ≤ ‖-(hadamardM : ℂ) / s - hadamardB‖ +
          ‖(1 : ℂ) / s‖ + ‖(1 : ℂ) / (s - 1)‖ +
            ‖(Real.log Real.pi : ℂ) / 2‖ +
              ‖Complex.digamma (s / 2) / 2‖ := by
        gcongr
        exact norm_add_le _ _
      _ ≤ ‖-(hadamardM : ℂ) / s‖ + ‖hadamardB‖ +
          ‖(1 : ℂ) / s‖ + ‖(1 : ℂ) / (s - 1)‖ +
            ‖(Real.log Real.pi : ℂ) / 2‖ +
              ‖Complex.digamma (s / 2) / 2‖ := by
        gcongr
        exact norm_sub_le _ _
      _ = _ := by simp only [norm_div, Complex.norm_ofNat]
  calc
    (-(deriv riemannZeta ((1 + x : ℝ) : ℂ) /
        riemannZeta ((1 + x : ℝ) : ℂ))).re ≤
        (zetaHadamardCorrection (1 + x) 0).re := by
      simpa using hdrop
    _ ≤ ‖zetaHadamardCorrection (1 + x) 0‖ :=
      Complex.re_le_norm _
    _ ≤ ‖-(hadamardM : ℂ) / s‖ + ‖hadamardB‖ +
        ‖(1 : ℂ) / s‖ + ‖(1 : ℂ) / (s - 1)‖ +
          ‖(Real.log Real.pi : ℂ) / 2‖ +
            ‖Complex.digamma (s / 2)‖ / 2 := htriangle
    _ ≤ (hadamardM : ℝ) + ‖hadamardB‖ + 1 + 1 / x +
          |Real.log Real.pi| + D / 2 := by
      gcongr
      exact hpole1.le
    _ ≤ 1 / x + C := by
      dsimp only [C]
      linarith

/-- Quantitative de la Vallée-Poussin upper zero-free boundary.  The
horizontal displacement is chosen after the coarse analytic constants, which
leaves a positive reciprocal-logarithmic margin. -/
theorem exists_nontrivialZetaZero_upper_log_gap :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ rho : NontrivialZetaZero,
      T ≤ |rho.val.im| →
        C / Real.log (|rho.val.im| + 2) ≤ 1 - rho.val.re := by
  obtain ⟨Czero, hCzeroPos, hreal⟩ :=
    exists_negZetaLogDeriv_real_near_one_bound
  obtain ⟨Chigh, hChighPos, hhigh⟩ :=
    exists_hadamardCorrection_high_bound
  let Q : ℝ := 3 * Czero + 6 * Chigh
  have hQpos : 0 < Q := by
    dsimp only [Q]
    nlinarith
  let C : ℝ := 3 / ((4 * Q + 9) * (Q + 3))
  have hCpos : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨C, 4, hCpos, by norm_num, ?_⟩
  intro rho hrhoHeight
  let gamma : ℝ := rho.val.im
  let L : ℝ := Real.log (|gamma| + 2)
  have hheight : 4 ≤ |gamma| := by simpa only [gamma] using hrhoHeight
  have hLone : 1 ≤ L := by
    dsimp only [L]
    calc
      (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (|gamma| + 2) := by
        apply Real.log_le_log (Real.exp_pos 1)
        linarith [Real.exp_one_lt_three]
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hLone
  let a : ℝ := 1 / (Q + 3)
  have haPos : 0 < a := by
    dsimp only [a]
    positivity
  have haOne : a ≤ 1 := by
    dsimp only [a]
    apply (div_le_one (by positivity)).2
    linarith
  let x : ℝ := a / L
  have hxPos : 0 < x := div_pos haPos hLpos
  have hxOne : x ≤ 1 := by
    dsimp only [x]
    apply (div_le_one hLpos).2
    exact haOne.trans hLone
  let sigma : ℝ := 1 + x
  have hsigma : 1 < sigma := by dsimp only [sigma]; linarith
  have hsigmaOne : 1 ≤ sigma := hsigma.le
  have hsigmaTwo : sigma ≤ 2 := by dsimp only [sigma]; linarith
  let gap : ℝ := sigma - rho.val.re
  have hgapPos : 0 < gap := by
    dsimp only [gap]
    linarith [rho.re_lt_one]
  let Fzero : ℝ :=
    (-(deriv riemannZeta (sigma : ℂ) /
      riemannZeta (sigma : ℂ))).re
  let Fone : ℝ :=
    (-(deriv riemannZeta ((sigma : ℂ) + gamma * I) /
      riemannZeta ((sigma : ℂ) + gamma * I))).re
  let Ftwo : ℝ :=
    (-(deriv riemannZeta ((sigma : ℂ) + (2 * gamma) * I) /
      riemannZeta ((sigma : ℂ) + (2 * gamma) * I))).re
  have h341 : 0 ≤ 3 * Fzero + 4 * Fone + Ftwo := by
    dsimp only [Fzero, Fone, Ftwo]
    exact negZetaLogDeriv_trig_nonneg hsigma gamma
  have hCzeroL : Czero ≤ Czero * L := by
    nlinarith [mul_nonneg hCzeroPos.le (sub_nonneg.mpr hLone)]
  have hzero : Fzero ≤ 1 / x + Czero * L := by
    calc
      Fzero ≤ 1 / x + Czero := by
        dsimp only [Fzero, sigma]
        simpa only [Complex.ofReal_add, Complex.ofReal_one] using
          hreal x hxPos hxOne
      _ ≤ 1 / x + Czero * L := by linarith
  have hchosen := negZetaLogDeriv_re_le_chosenZero rho hsigma
  have hcorrOne := hhigh sigma gamma hsigmaOne hsigmaTwo hheight
  have hone : Fone ≤ Chigh * L - 1 / gap := by
    calc
      Fone ≤ (zetaHadamardCorrection sigma gamma).re -
          1 / gap := by
        simpa only [Fone, gamma, gap, zetaHadamardCorrection] using
          hchosen
      _ ≤ Chigh * L - 1 / gap := by
        linarith
  have htwoHeight : 4 ≤ |2 * gamma| := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hdropTwo :=
    negZetaLogDeriv_re_le_hadamardCorrection hsigma (2 * gamma)
  have hcorrTwo := hhigh sigma (2 * gamma)
    hsigmaOne hsigmaTwo htwoHeight
  have hargTwoPos : 0 < |2 * gamma| + 2 := by positivity
  have hargTwoLe : |2 * gamma| + 2 ≤ (|gamma| + 2) ^ 2 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [abs_nonneg gamma]
  have hlogTwo : Real.log (|2 * gamma| + 2) ≤ 2 * L := by
    calc
      Real.log (|2 * gamma| + 2) ≤
          Real.log ((|gamma| + 2) ^ 2) :=
        Real.log_le_log hargTwoPos hargTwoLe
      _ = 2 * L := by
        rw [Real.log_pow]
        norm_num [L]
  have htwo : Ftwo ≤ (2 * Chigh) * L := by
    calc
      Ftwo ≤ (zetaHadamardCorrection sigma (2 * gamma)).re := by
        simpa only [Ftwo, Complex.ofReal_mul,
          Complex.ofReal_ofNat] using hdropTwo
      _ ≤ Chigh * Real.log (|2 * gamma| + 2) := hcorrTwo
      _ ≤ (2 * Chigh) * L := by
        nlinarith [mul_nonneg hChighPos.le
          (sub_nonneg.mpr hlogTwo)]
  have hdenom :
      0 < 3 / x + (3 * Czero + 4 * Chigh + 2 * Chigh) * L := by
    have hxInvPos : 0 < 3 / x := div_pos (by norm_num) hxPos
    have hcoeffPos : 0 < 3 * Czero + 4 * Chigh + 2 * Chigh := by
      nlinarith
    nlinarith [mul_pos hcoeffPos hLpos]
  have hgapLower := gap_ge_of_logDeriv_341_bounds
    (gap := gap) (L := L) (Fzero := Fzero) (Fone := Fone)
    (Ftwo := Ftwo) (Czero := Czero) (Cone := Chigh)
    (Ctwo := 2 * Chigh) hgapPos h341 hzero hone htwo hdenom
  have hQthreePos : 0 < Q + 3 := by linarith
  have hFourQninePos : 0 < 4 * Q + 9 := by linarith
  have hdenomEq :
      3 / x + (3 * Czero + 4 * Chigh + 2 * Chigh) * L =
        (4 * Q + 9) * L := by
    dsimp only [x, a, Q]
    field_simp [hLpos.ne', hQthreePos.ne']
    ring
  rw [hdenomEq] at hgapLower
  have hmarginEq :
      C / L + x = 4 / ((4 * Q + 9) * L) := by
    dsimp only [C, x, a]
    field_simp [hLpos.ne', hQthreePos.ne', hFourQninePos.ne']
    ring
  rw [← hmarginEq] at hgapLower
  dsimp only [gap, sigma] at hgapLower
  change C / L ≤ 1 - rho.val.re
  linarith

/-- The functional-equation reflection turns the upper logarithmic boundary
into the matching lower boundary. -/
theorem exists_nontrivialZetaZero_lower_log_gap :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ rho : NontrivialZetaZero,
      T ≤ |rho.val.im| →
        C / Real.log (|rho.val.im| + 2) ≤ rho.val.re := by
  obtain ⟨C, T, hCpos, hTpos, hupper⟩ :=
    exists_nontrivialZetaZero_upper_log_gap
  refine ⟨C, T, hCpos, hTpos, ?_⟩
  intro rho hrhoHeight
  let reflected : NontrivialZetaZero := oneSubNontrivialZetaZero rho
  have hreflectedHeight : T ≤ |reflected.val.im| := by
    dsimp only [reflected]
    simpa only [oneSubNontrivialZetaZero_val, Complex.sub_im,
      Complex.one_im, zero_sub, abs_neg] using hrhoHeight
  have hreflected := hupper reflected hreflectedHeight
  dsimp only [reflected] at hreflected
  simpa only [oneSubNontrivialZetaZero_val, Complex.sub_im,
    Complex.one_im, zero_sub, abs_neg, Complex.sub_re,
    Complex.one_re, sub_sub_cancel] using hreflected

/-- A single pair of constants gives both sides of the classical
de la Vallée-Poussin logarithmic zero-free region. -/
theorem exists_nontrivialZetaZero_two_sided_log_gap :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ rho : NontrivialZetaZero,
      T ≤ |rho.val.im| →
        C / Real.log (|rho.val.im| + 2) ≤ rho.val.re ∧
        C / Real.log (|rho.val.im| + 2) ≤ 1 - rho.val.re := by
  obtain ⟨C, T, hCpos, hTpos, hupper⟩ :=
    exists_nontrivialZetaZero_upper_log_gap
  refine ⟨C, T, hCpos, hTpos, ?_⟩
  intro rho hrhoHeight
  have hright := hupper rho hrhoHeight
  let reflected : NontrivialZetaZero := oneSubNontrivialZetaZero rho
  have hreflectedHeight : T ≤ |reflected.val.im| := by
    dsimp only [reflected]
    simpa only [oneSubNontrivialZetaZero_val, Complex.sub_im,
      Complex.one_im, zero_sub, abs_neg] using hrhoHeight
  have hreflected := hupper reflected hreflectedHeight
  have hleft : C / Real.log (|rho.val.im| + 2) ≤ rho.val.re := by
    dsimp only [reflected] at hreflected
    simpa only [oneSubNontrivialZetaZero_val, Complex.sub_im,
      Complex.one_im, zero_sub, abs_neg, Complex.sub_re,
      Complex.one_re, sub_sub_cancel] using hreflected
  exact ⟨hleft, hright⟩

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
