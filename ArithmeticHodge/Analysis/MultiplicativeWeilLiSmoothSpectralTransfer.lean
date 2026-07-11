import ArithmeticHodge.Analysis.MultiplicativeWeilLiSmoothConvolution
import ArithmeticHodge.Analysis.MultiplicativeWeilLiCutoffFormula
import ArithmeticHodge.Analysis.MultiplicativeWeilLiCutoffSpectral
import ArithmeticHodge.Analysis.MultiplicativeWeilLiDominantSeries
import ArithmeticHodge.Analysis.MultiplicativeWeilCriterion
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Smooth spectral transfer for truncated Li kernels

Square-summable cutoff Mellin transforms and uniformly bounded Mellin bump
multipliers justify the second zero-sum exchange.  Consequently every
negative fixed-cutoff spectral sum yields a nonzero smooth Bombieri witness.
-/

set_option autoImplicit false

open Complex Filter MeasureTheory Real Set Topology
open scoped ContDiff Distributions

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-! ## Fixed-cutoff square summability -/

/-- Endpoint Laplace polynomials remain square-summable along every sequence
whose inverse squared norms are summable. -/
theorem summable_norm_liLaplaceTailPolynomial_sq
    (z : ℕ → ℂ)
    (hinv : Summable (fun k ↦ ‖z k‖⁻¹ ^ (2 : ℝ)))
    (m : ℕ) (L : ℝ) :
    Summable (fun k ↦ ‖liLaplaceTailPolynomial m (z k) L‖ ^ 2) := by
  have hinv' : Summable (fun k ↦ ‖z k‖⁻¹ ^ (2 : ℕ)) := by
    simpa only [Real.rpow_two] using hinv
  induction m with
  | zero =>
      simpa only [liLaplaceTailPolynomial, one_div, norm_inv]
        using hinv'
  | succ m ih =>
      let A : ℕ → ℂ := fun k ↦
        (L : ℂ) ^ (m + 1) / z k
      let B : ℕ → ℂ := fun k ↦
        ((((m + 1 : ℕ) : ℂ) / z k) *
          liLaplaceTailPolynomial m (z k) L)
      have hA : Summable (fun k ↦ ‖A k‖ ^ 2) := by
        have h := hinv'.mul_left (‖(L : ℂ) ^ (m + 1)‖ ^ 2)
        apply h.congr
        intro k
        dsimp only [A]
        rw [norm_div, div_eq_mul_inv, mul_pow]
      have hdiag : Summable (fun k ↦
          (‖z k‖⁻¹ ^ (2 : ℕ)) *
            ‖liLaplaceTailPolynomial m (z k) L‖ ^ 2) := by
        have hprod : Summable (fun p : ℕ × ℕ ↦
            (‖z p.1‖⁻¹ ^ (2 : ℕ)) *
              ‖liLaplaceTailPolynomial m (z p.2) L‖ ^ 2) :=
          hinv'.mul_of_nonneg ih
            (fun _k ↦ sq_nonneg _)
            (fun _k ↦ sq_nonneg _)
        have hinjective : Function.Injective (fun k : ℕ ↦ (k, k)) := by
          intro a b hab
          exact congrArg Prod.fst hab
        simpa only [Function.comp_apply] using
          hprod.comp_injective hinjective
      have hB : Summable (fun k ↦ ‖B k‖ ^ 2) := by
        have h := hdiag.mul_left
          (‖(((m + 1 : ℕ) : ℂ))‖ ^ 2)
        apply h.congr
        intro k
        dsimp only [B]
        rw [norm_mul, norm_div, div_eq_mul_inv, mul_pow, mul_pow]
        ring
      apply ((hA.add hB).mul_left 2).of_nonneg_of_le
      · intro k
        exact sq_nonneg _
      · intro k
        change ‖A k + B k‖ ^ 2 ≤
          2 * (‖A k‖ ^ 2 + ‖B k‖ ^ 2)
        have hnorm := norm_add_le (A k) (B k)
        have hsquare : (‖A k‖ + ‖B k‖) ^ 2 ≤
            2 * (‖A k‖ ^ 2 + ‖B k‖ ^ 2) := by
          nlinarith [sq_nonneg (‖A k‖ - ‖B k‖)]
        exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hnorm |>.trans hsquare

/-- Multiplying an endpoint polynomial by the cutoff power preserves square
summability throughout the closed critical strip. -/
theorem summable_norm_liCutoffLogMoment_sq
    (z : ℕ → ℂ)
    (hinv : Summable (fun k ↦ ‖z k‖⁻¹ ^ (2 : ℝ)))
    (hre : ∀ k, 0 ≤ (z k).re)
    (m : ℕ) (epsilon : ℝ)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    Summable (fun k ↦ ‖liCutoffLogMoment m epsilon (z k)‖ ^ 2) := by
  have hpoly := summable_norm_liLaplaceTailPolynomial_sq
    z hinv m (-Real.log epsilon)
  apply hpoly.of_nonneg_of_le
  · intro k
    exact sq_nonneg _
  · intro k
    rw [norm_liCutoffLogMoment_eq m epsilon (z k) hepsilon0,
      mul_pow]
    have hpow0 : 0 ≤ epsilon ^ (z k).re :=
      Real.rpow_nonneg hepsilon0.le _
    have hpow1 : epsilon ^ (z k).re ≤ 1 :=
      Real.rpow_le_one hepsilon0.le hepsilon1.le (hre k)
    have hpowSq : (epsilon ^ (z k).re) ^ 2 ≤ (1 : ℝ) := by
      have := pow_le_pow_left₀ hpow0 hpow1 2
      simpa only [one_pow] using this
    calc
      (epsilon ^ (z k).re) ^ 2 *
          ‖liLaplaceTailPolynomial m (z k) (-Real.log epsilon)‖ ^ 2 ≤
          1 * ‖liLaplaceTailPolynomial m (z k) (-Real.log epsilon)‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hpowSq (sq_nonneg _)
      _ = _ := one_mul _

/-- The complete finite endpoint correction is square-summable along the
critical strip. -/
theorem summable_norm_liKernelCutoffCorrection_sq
    (z : ℕ → ℂ)
    (hinv : Summable (fun k ↦ ‖z k‖⁻¹ ^ (2 : ℝ)))
    (hre : ∀ k, 0 ≤ (z k).re)
    (n : ℕ) (epsilon : ℝ)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    Summable (fun k ↦
      ‖liKernelCutoffCorrection n epsilon (z k)‖ ^ 2) := by
  let T : ℕ → ℕ → ℂ := fun m k ↦
    ((Nat.choose n (m + 1) : ℂ) / (Nat.factorial m : ℂ)) *
      liCutoffLogMoment m epsilon (z k)
  have hterm (m : ℕ) : Summable (fun k ↦ ‖T m k‖ ^ 2) := by
    have hm := summable_norm_liCutoffLogMoment_sq
      z hinv hre m epsilon hepsilon0 hepsilon1
    have h := hm.mul_left
      (‖(Nat.choose n (m + 1) : ℂ) / (Nat.factorial m : ℂ)‖ ^ 2)
    apply h.congr
    intro k
    dsimp only [T]
    rw [norm_mul, mul_pow]
  have hfinite : Summable (fun k ↦
      ∑ m ∈ Finset.range n, ‖T m k‖ ^ 2) := by
    exact summable_sum fun m _hm ↦ hterm m
  have hmajor : Summable (fun k ↦
      (n : ℝ) * ∑ m ∈ Finset.range n, ‖T m k‖ ^ 2) :=
    hfinite.mul_left (n : ℝ)
  apply hmajor.of_nonneg_of_le
  · intro k
    exact sq_nonneg _
  · intro k
    rw [liKernelCutoffCorrection]
    change ‖∑ m ∈ Finset.range n, T m k‖ ^ 2 ≤ _
    have hnorm : ‖∑ m ∈ Finset.range n, T m k‖ ≤
        ∑ m ∈ Finset.range n, ‖T m k‖ := norm_sum_le _ _
    have hsum0 : 0 ≤ ∑ m ∈ Finset.range n, ‖T m k‖ :=
      Finset.sum_nonneg fun _m _hm ↦ norm_nonneg _
    calc
      ‖∑ m ∈ Finset.range n, T m k‖ ^ 2 ≤
          (∑ m ∈ Finset.range n, ‖T m k‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) hsum0).2 hnorm
      _ ≤ ((Finset.range n).card : ℝ) *
          ∑ m ∈ Finset.range n, ‖T m k‖ ^ 2 :=
        sq_sum_le_card_mul_sum_sq
      _ = (n : ℝ) * ∑ m ∈ Finset.range n, ‖T m k‖ ^ 2 := by
        rw [Finset.card_range]

/-- The Mellin transform of a fixed Li cutoff is square-summable whenever
the underlying spectral parameters have summable inverse squared norms. -/
theorem summable_norm_mellin_liKernelCutoff_sq_of_inv_norm_sq
    (z : ℕ → ℂ)
    (hinv : Summable (fun k ↦ ‖z k‖⁻¹ ^ (2 : ℝ)))
    (hre : ∀ k, 0 < (z k).re)
    (n : ℕ) (epsilon : ℝ)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    Summable (fun k ↦ ‖mellin (liKernelCutoff n epsilon) (z k)‖ ^ 2) := by
  have hli := summable_norm_liFunction_sq_of_inv_norm_sq z hinv n
  have hcorrection := summable_norm_liKernelCutoffCorrection_sq
    z hinv (fun k ↦ (hre k).le) n epsilon hepsilon0 hepsilon1
  have hmajor := (hli.add hcorrection).mul_left 2
  apply hmajor.of_nonneg_of_le
  · intro k
    exact sq_nonneg _
  · intro k
    rw [mellin_liKernelCutoff_eq_liFunction_sub_correction
      n epsilon (z k) hepsilon0 hepsilon1 (hre k)]
    have hnorm := norm_sub_le
      (liFunction n (z k))
      (liKernelCutoffCorrection n epsilon (z k))
    have hsquare :
        (‖liFunction n (z k)‖ +
          ‖liKernelCutoffCorrection n epsilon (z k)‖) ^ 2 ≤
        2 * (‖liFunction n (z k)‖ ^ 2 +
          ‖liKernelCutoffCorrection n epsilon (z k)‖ ^ 2) := by
      nlinarith [sq_nonneg
        (‖liFunction n (z k)‖ -
          ‖liKernelCutoffCorrection n epsilon (z k)‖)]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hnorm |>.trans hsquare

/-- Fixed-cutoff quadratic spectral terms are absolutely summable over every
analytic-multiplicity enumeration of the nontrivial zeta zeros. -/
theorem ZetaZeroEnumeration.spectralTerm_liKernelCutoff_summable
    (zeros : ZetaZeroEnumeration) (n : ℕ) (epsilon : ℝ)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    Summable (fun k ↦
      spectralTerm (liKernelCutoff n epsilon) (zeros.zero k).val) := by
  have hdirect :=
    summable_norm_mellin_liKernelCutoff_sq_of_inv_norm_sq
      (fun k ↦ (zeros.zero k).val)
      zeros.summable_inv_norm_sq
      (fun k ↦ (zeros.zero k).re_pos)
      n epsilon hepsilon0 hepsilon1
  have hreflected :=
    summable_norm_mellin_liKernelCutoff_sq_of_inv_norm_sq
      (fun k ↦ 1 - (zeros.zero k).val)
      zeros.summable_one_sub_inv_norm_sq
      (fun k ↦ by
        simp only [Complex.sub_re, Complex.one_re]
        linarith [(zeros.zero k).re_lt_one])
      n epsilon hepsilon0 hepsilon1
  apply (hdirect.add hreflected).of_norm_bounded
  intro k
  rw [spectralTerm_liKernelCutoff, norm_mul]
  nlinarith [two_mul_le_add_sq
    ‖mellin (liKernelCutoff n epsilon) (zeros.zero k).val‖
    ‖mellin (liKernelCutoff n epsilon) (1 - (zeros.zero k).val)‖]

/-! ## Uniform strip control of the smoothing multipliers -/

/-- Every production bump Mellin transform is bounded uniformly in the
closed critical strip, independently of the imaginary part and bump index. -/
theorem norm_mellin_mellinBumpSequence_le_exp_one
    (k : ℕ) (s : ℂ) (hre0 : 0 ≤ s.re) (hre1 : s.re ≤ 1) :
    ‖mellin (mellinBumpSequence k : ℝ → ℂ) s‖ ≤ Real.exp 1 := by
  let eta : BombieriTest := mellinBumpSequence k
  have hetaInt : Integrable (eta : ℝ → ℂ) :=
    eta.contDiff.continuous.integrable_of_hasCompactSupport eta.hasCompactSupport
  have hzero_nonpos (x : ℝ) (hx : x ∉ Ioi (0 : ℝ)) : eta x = 0 := by
    by_contra hne
    apply hx
    have hsupport := eta.tsupport_subset
      (subset_tsupport eta (Function.mem_support.mpr hne))
    simpa only [positiveHalfLine] using hsupport
  have hmassIoi : (∫ x : ℝ in Ioi 0, (eta x).re) = 1 := by
    rw [← mellinBumpSequence_unit_mass k,
      ← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hzero_nonpos x hx]
      rfl
  have hpowInt : IntegrableOn (fun x : ℝ ↦
      (x : ℂ) ^ (s - 1) * eta x) (Ioi 0) := by
    simpa only [MellinConvergent, smul_eq_mul] using eta.mellinConvergent s
  have hradiusLe : mellinBumpRadius k ≤ 1 := by
    unfold mellinBumpRadius
    apply (div_le_one (by positivity)).2
    norm_num
  have hpoint (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
      ‖(x : ℂ) ^ (s - 1) * eta x‖ ≤ Real.exp 1 * (eta x).re := by
    by_cases hetaZero : eta x = 0
    · simp [hetaZero]
    have hxt := mellinBumpSequence_support k
      (subset_tsupport eta (Function.mem_support.mpr hetaZero))
    have hlog : |Real.log x| < mellinBumpRadius k := by
      rw [abs_lt]
      exact ⟨(Real.lt_log_iff_exp_lt hx).mpr hxt.1,
        (Real.log_lt_iff_lt_exp hx).mpr hxt.2⟩
    have habsexp : |s.re - 1| ≤ 1 := by
      rw [abs_of_nonpos (by linarith)]
      linarith
    have hlogmul : Real.log x * (s.re - 1) ≤ 1 := by
      calc
        Real.log x * (s.re - 1) ≤
            |Real.log x * (s.re - 1)| := le_abs_self _
        _ = |Real.log x| * |s.re - 1| := abs_mul _ _
        _ ≤ mellinBumpRadius k * 1 :=
          mul_le_mul hlog.le habsexp (abs_nonneg _) (mellinBumpRadius_pos k).le
        _ ≤ 1 := by simpa only [mul_one] using hradiusLe
    have hpow : ‖(x : ℂ) ^ (s - 1)‖ ≤ Real.exp 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx,
        Complex.sub_re, Complex.one_re, Real.rpow_def_of_pos hx]
      exact Real.exp_le_exp.mpr hlogmul
    have hetaNorm : ‖eta x‖ = (eta x).re := by
      change ‖mellinBumpSequence k x‖ =
        (mellinBumpSequence k x).re
      have hetaEq : mellinBumpSequence k x =
          ((mellinBumpSequence k x).re : ℂ) := by
        apply Complex.ext
        · simp
        · exact (mellinBumpSequence_real_nonnegative k x).2
      rw [hetaEq, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mellinBumpSequence_real_nonnegative k x).1]
      simp
    rw [norm_mul, hetaNorm]
    exact mul_le_mul_of_nonneg_right hpow
      (mellinBumpSequence_real_nonnegative k x).1
  change ‖∫ x : ℝ in Ioi 0,
      (x : ℂ) ^ (s - 1) * eta x‖ ≤ Real.exp 1
  calc
    ‖∫ x : ℝ in Ioi 0,
        (x : ℂ) ^ (s - 1) * eta x‖ ≤
        ∫ x : ℝ in Ioi 0, ‖(x : ℂ) ^ (s - 1) * eta x‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ in Ioi 0, Real.exp 1 * (eta x).re := by
      apply integral_mono_ae
      · exact hpowInt.norm
      · exact (hetaInt.re.const_mul (Real.exp 1)).integrableOn
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact hpoint x hx
    _ = Real.exp 1 * ∫ x : ℝ in Ioi 0, (eta x).re :=
      integral_const_mul (Real.exp 1) _
    _ = Real.exp 1 := by rw [hmassIoi, mul_one]

/-- Reality of the production bump fixes its Mellin transform under
coefficient conjugation. -/
theorem coefficientConjugate_mellin_mellinBumpSequence
    (k : ℕ) (s : ℂ) :
    coefficientConjugate
      (mellin (mellinBumpSequence k : ℝ → ℂ)) s =
        mellin (mellinBumpSequence k : ℝ → ℂ) s := by
  rw [← mellin_conjugate]
  apply congrArg (fun f : ℝ → ℂ ↦ mellin f s)
  funext x
  apply Complex.ext
  · simp
  · simp [(mellinBumpSequence_real_nonnegative k x).2]

/-- Smoothing multiplies the fixed-cutoff spectral term by the direct and
reflected bump Mellin multipliers. -/
theorem spectralTerm_bombieriLiMellinBumpConvolution_eq
    (n : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (k : ℕ) (s : ℂ) :
    spectralTerm
        (bombieriLiMellinBumpConvolution n epsilon hepsilon k : ℝ → ℂ) s =
      spectralTerm (liKernelCutoff n epsilon) s *
        mellin (mellinBumpSequence k : ℝ → ℂ) s *
        mellin (mellinBumpSequence k : ℝ → ℂ) (1 - s) := by
  have hcutoff := coefficientConjugate_mellin_liKernelCutoff
    n epsilon (1 - s)
  have hbump := coefficientConjugate_mellin_mellinBumpSequence
    k (1 - s)
  unfold coefficientConjugate at hcutoff hbump
  unfold spectralTerm coefficientConjugate
  rw [mellin_bombieriLiMellinBumpConvolution,
    mellin_bombieriLiMellinBumpConvolution]
  simp only [map_mul]
  rw [hcutoff, hbump]
  ring

/-! ## The second spectral exchange -/

/-- For a fixed positive cutoff, smoothing by the shrinking production bump
commutes with the full analytic-multiplicity zero sum. -/
theorem tendsto_tsum_spectralTerm_bombieriLiMellinBumpConvolution
    (zeros : ZetaZeroEnumeration) (n : ℕ)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    Tendsto (fun k : ℕ ↦ ∑' j : ℕ,
        spectralTerm
          (bombieriLiMellinBumpConvolution n epsilon hepsilon k : ℝ → ℂ)
          (zeros.zero j).val)
      atTop
      (nhds (∑' j : ℕ,
        spectralTerm (liKernelCutoff n epsilon) (zeros.zero j).val)) := by
  let bound : ℕ → ℝ := fun j ↦
    (Real.exp 1) ^ 2 *
      ‖spectralTerm (liKernelCutoff n epsilon) (zeros.zero j).val‖
  have hsum : Summable bound := by
    have hcutoff :=
      (zeros.spectralTerm_liKernelCutoff_summable
        n epsilon hepsilon hepsilon1).norm
    exact hcutoff.mul_left ((Real.exp 1) ^ 2)
  have hpoint (j : ℕ) : Tendsto (fun k : ℕ ↦
      spectralTerm
        (bombieriLiMellinBumpConvolution n epsilon hepsilon k : ℝ → ℂ)
        (zeros.zero j).val) atTop
      (nhds (spectralTerm
        (liKernelCutoff n epsilon) (zeros.zero j).val)) := by
    have hdirect := mellin_mellinBumpSequence_tendsto_one
      (zeros.zero j).val
    have hreflected := mellin_mellinBumpSequence_tendsto_one
      (1 - (zeros.zero j).val)
    have h := ((tendsto_const_nhds
      (x := spectralTerm
        (liKernelCutoff n epsilon) (zeros.zero j).val)).mul hdirect).mul
          hreflected
    simpa only [spectralTerm_bombieriLiMellinBumpConvolution_eq,
      mul_one] using h
  have hbound (k j : ℕ) :
      ‖spectralTerm
        (bombieriLiMellinBumpConvolution n epsilon hepsilon k : ℝ → ℂ)
        (zeros.zero j).val‖ ≤ bound j := by
    have hdirect := norm_mellin_mellinBumpSequence_le_exp_one
      k (zeros.zero j).val
      (zeros.zero j).re_pos.le
      (zeros.zero j).re_lt_one.le
    have hreflected := norm_mellin_mellinBumpSequence_le_exp_one
      k (1 - (zeros.zero j).val)
      (by
        simp only [Complex.sub_re, Complex.one_re]
        linarith [(zeros.zero j).re_lt_one])
      (by
        simp only [Complex.sub_re, Complex.one_re]
        linarith [(zeros.zero j).re_pos])
    rw [spectralTerm_bombieriLiMellinBumpConvolution_eq,
      norm_mul, norm_mul]
    change
      ‖spectralTerm (liKernelCutoff n epsilon) (zeros.zero j).val‖ *
          ‖mellin (mellinBumpSequence k : ℝ → ℂ) (zeros.zero j).val‖ *
          ‖mellin (mellinBumpSequence k : ℝ → ℂ)
            (1 - (zeros.zero j).val)‖ ≤ _
    calc
      ‖spectralTerm (liKernelCutoff n epsilon) (zeros.zero j).val‖ *
            ‖mellin (mellinBumpSequence k : ℝ → ℂ)
              (zeros.zero j).val‖ *
            ‖mellin (mellinBumpSequence k : ℝ → ℂ)
              (1 - (zeros.zero j).val)‖ ≤
          ‖spectralTerm (liKernelCutoff n epsilon) (zeros.zero j).val‖ *
            Real.exp 1 *
            ‖mellin (mellinBumpSequence k : ℝ → ℂ)
              (1 - (zeros.zero j).val)‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdirect (norm_nonneg _))
          (norm_nonneg _)
      _ ≤ ‖spectralTerm
            (liKernelCutoff n epsilon) (zeros.zero j).val‖ *
          Real.exp 1 * Real.exp 1 := by
        exact mul_le_mul_of_nonneg_left hreflected
          (mul_nonneg (norm_nonneg _) (Real.exp_nonneg _))
      _ = bound j := by
        dsimp only [bound]
        ring
  exact tendsto_tsum_of_dominated_convergence
    hsum hpoint (Eventually.of_forall hbound)

/-! ## Negative smooth witnesses -/

/-- A negative fixed-cutoff spectral sum survives sufficiently fine Mellin
smoothing and produces a nonzero Bombieri test. -/
theorem exists_nonzero_smooth_of_liKernelCutoff_tsum_re_negative
    (zeros : ZetaZeroEnumeration) (n : ℕ)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hnegative :
      (∑' j : ℕ,
        spectralTerm (liKernelCutoff n epsilon) (zeros.zero j).val).re < 0) :
    ∃ g : BombieriTest, g ≠ 0 ∧
      (∑' j : ℕ,
        spectralTerm (g : ℝ → ℂ) (zeros.zero j).val).re < 0 := by
  have hlimit :=
    tendsto_tsum_spectralTerm_bombieriLiMellinBumpConvolution
      zeros n epsilon hepsilon hepsilon1
  have hlimitRe : Tendsto (fun k : ℕ ↦ Complex.reCLM
      (∑' j : ℕ,
        spectralTerm
          (bombieriLiMellinBumpConvolution
            n epsilon hepsilon k : ℝ → ℂ)
          (zeros.zero j).val)) atTop
      (nhds (Complex.reCLM (∑' j : ℕ,
        spectralTerm (liKernelCutoff n epsilon)
          (zeros.zero j).val))) :=
    Complex.reCLM.continuous.continuousAt.tendsto.comp hlimit
  have hevent : ∀ᶠ k : ℕ in atTop, Complex.reCLM
      (∑' j : ℕ,
        spectralTerm
          (bombieriLiMellinBumpConvolution
            n epsilon hepsilon k : ℝ → ℂ)
          (zeros.zero j).val) < 0 :=
    hlimitRe.eventually (Iio_mem_nhds hnegative)
  obtain ⟨k, hk⟩ := hevent.exists
  let g : BombieriTest :=
    bombieriLiMellinBumpConvolution n epsilon hepsilon k
  have hgnegative :
      (∑' j : ℕ,
        spectralTerm (g : ℝ → ℂ) (zeros.zero j).val).re < 0 := by
    simpa only [g] using hk
  refine ⟨g, ?_, hgnegative⟩
  intro hgzero
  have hmellinZero (j : ℕ) :
      mellin (g : ℝ → ℂ) (zeros.zero j).val = 0 := by
    rw [hgzero]
    simp [mellin]
  have htermZero (j : ℕ) :
      spectralTerm (g : ℝ → ℂ) (zeros.zero j).val = 0 := by
    unfold spectralTerm
    rw [hmellinZero]
    exact zero_mul _
  simp_rw [htermZero] at hgnegative
  norm_num at hgnegative

/-- Any off-RH supply of a negative fixed Li cutoff discharges the genuine
smooth witness obligation in Bombieri's criterion. -/
theorem bombieriOffCriticalSpectralNegativity_of_liKernelCutoff
    (zeros : ZetaZeroEnumeration)
    (hcutoff : ¬ RiemannHypothesis →
      ∃ n : ℕ, ∃ epsilon : ℝ,
        0 < epsilon ∧ epsilon < 1 ∧
          (∑' j : ℕ,
            spectralTerm (liKernelCutoff n epsilon)
              (zeros.zero j).val).re < 0) :
    BombieriOffCriticalSpectralNegativity zeros := by
  unfold BombieriOffCriticalSpectralNegativity
  intro hnot
  obtain ⟨n, epsilon, hepsilon, hepsilon1, hnegative⟩ := hcutoff hnot
  exact exists_nonzero_smooth_of_liKernelCutoff_tsum_re_negative
    zeros n epsilon hepsilon hepsilon1 hnegative

end


end ArithmeticHodge.Analysis.MultiplicativeWeil
