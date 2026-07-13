import ArithmeticHodge.Analysis.YoshidaFactorTwoCoreObstruction
import ArithmeticHodge.Analysis.MultiplicativeWeilMellinBumpSequence
import Mathlib.MeasureTheory.Integral.MeanInequalities

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoCoreExplicitObstruction

noncomputable section

open MultiplicativeWeil
open YoshidaBombieriCrossDistribution
open YoshidaFactorTwoCoreObstruction
open YoshidaFactorTwoCoreReduction

/-!
# An explicit negative factor-two core diagonal

The unit-mass bump with logarithmic radius `1 / 1000` has very large
zero-lag `L²` mass.  Its two polar Mellin values remain close to one, so the
negative Euler--Mascheroni mass term alone dominates the polar contribution.
This gives a fully structural witness that the isolated factor-two core is
not positive.
-/

private theorem sq_setIntegral_norm_le_length_mul_setIntegral_normSq
    (F : SchwartzMap ℝ ℂ) {l r : ℝ} (hlr : l ≤ r) :
    (∫ u : ℝ in Set.Icc l r, ‖F u‖) ^ 2 ≤
      (r - l) * ∫ u : ℝ in Set.Icc l r, Complex.normSq (F u) := by
  let μ : Measure ℝ := volume.restrict (Set.Icc l r)
  have hconst : MemLp (fun _ : ℝ ↦ (1 : ℝ)) 2 μ := memLp_const 1
  have hF : MemLp (fun u : ℝ ↦ ‖F u‖) 2 μ :=
    MemLp.mono_measure Measure.restrict_le_self (F.memLp 2).norm
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (μ := μ) (p := 2) (q := 2) Real.HolderConjugate.two_two
      (by simpa using hconst) (by simpa using hF)
  simp at hholder
  have hlen : μ.real Set.univ = r - l := by
    simp [μ, hlr]
  have hsq : (∫ u : ℝ, ‖F u‖ ^ (2 : ℕ) ∂μ) =
      ∫ u : ℝ, Complex.normSq (F u) ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with u
    rw [Complex.normSq_eq_norm_sq]
  rw [hlen, hsq] at hholder
  have hA : 0 ≤ ∫ u : ℝ, ‖F u‖ ∂μ :=
    integral_nonneg fun _ ↦ norm_nonneg _
  have hB : 0 ≤ ∫ u : ℝ, Complex.normSq (F u) ∂μ :=
    integral_nonneg fun _ ↦ Complex.normSq_nonneg _
  have hlen0 : 0 ≤ r - l := sub_nonneg.mpr hlr
  have hsqrt : 0 ≤
      (r - l) ^ ((2 : ℝ)⁻¹) *
        (∫ u : ℝ, Complex.normSq (F u) ∂μ) ^ ((2 : ℝ)⁻¹) :=
    mul_nonneg (Real.rpow_nonneg hlen0 _) (Real.rpow_nonneg hB _)
  have hsqle : (∫ u : ℝ, ‖F u‖ ∂μ) ^ 2 ≤
      (((r - l) ^ ((2 : ℝ)⁻¹)) *
        ((∫ u : ℝ, Complex.normSq (F u) ∂μ) ^
          ((2 : ℝ)⁻¹))) ^ 2 := by
    exact (sq_le_sq₀ hA hsqrt).2 hholder
  calc
    (∫ u : ℝ in Set.Icc l r, ‖F u‖) ^ 2 =
        (∫ u : ℝ, ‖F u‖ ∂μ) ^ 2 := rfl
    _ ≤ _ := hsqle
    _ = (r - l) * ∫ u : ℝ, Complex.normSq (F u) ∂μ := by
      rw [mul_pow]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hlen0]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hB]
      norm_num
    _ = _ := rfl

/-- A real nonnegative Bombieri test supported in an interval has squared mass
bounded by the interval length times its zero-lag critical correlation. -/
theorem sq_integral_re_le_length_mul_critical_zero
    (g : BombieriTest) {l r : ℝ} (hlr : l ≤ r)
    (hsupport : tsupport (g : ℝ → ℂ) ⊆ Set.Icc l r)
    (hreal : ∀ x, 0 ≤ (g x).re ∧ (g x).im = 0) :
    (∫ x : ℝ, (g x).re) ^ 2 ≤
      (r - l) * (bombieriCriticalCrossCorrelation g g 0).re := by
  let F : SchwartzMap ℝ ℂ :=
    g.hasCompactSupport.toSchwartzMap g.contDiff
  have hzero (x : ℝ) (hx : x ∉ Set.Icc l r) : g x = 0 := by
    by_contra hne
    exact hx (hsupport
      (subset_tsupport g (Function.mem_support.mpr hne)))
  have hnorm (x : ℝ) : ‖F x‖ = (g x).re := by
    change ‖g x‖ = (g x).re
    have hgEq : g x = ((g x).re : ℂ) := by
      apply Complex.ext
      · simp
      · exact (hreal x).2
    calc
      ‖g x‖ = ‖((g x).re : ℂ)‖ := congrArg norm hgEq
      _ = |(g x).re| := Complex.norm_real _
      _ = (g x).re := abs_of_nonneg (hreal x).1
  have hL1 : (∫ x : ℝ in Set.Icc l r, ‖F x‖) =
      ∫ x : ℝ, (g x).re := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
      simp [F, hzero x hx])]
    apply integral_congr_ae
    filter_upwards [] with x
    exact hnorm x
  have hL2full : (∫ x : ℝ in Set.Icc l r,
      Complex.normSq (F x)) =
      ∫ x : ℝ, Complex.normSq (g x) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
      simp [F, hzero x hx])]
    rfl
  have hzeroNonpos (x : ℝ) (hx : x ∉ Set.Ioi (0 : ℝ)) : g x = 0 := by
    by_contra hne
    apply hx
    have hmem := g.tsupport_subset
      (subset_tsupport g (Function.mem_support.mpr hne))
    simpa only [positiveHalfLine] using hmem
  have hL2pos : (∫ x : ℝ in Set.Ioi 0,
      Complex.normSq (g x)) =
      ∫ x : ℝ, Complex.normSq (g x) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp [hzeroNonpos x hx]
  have hcorr : (bombieriCriticalCrossCorrelation g g 0).re =
      ∫ x : ℝ in Set.Ioi 0, Complex.normSq (g x) := by
    rw [bombieriCriticalCrossCorrelation_self_zero_eq_quadratic_one,
      bombieriQuadraticTest_apply_one, integral_complex_ofReal]
    rfl
  have hL2 : (∫ x : ℝ in Set.Icc l r,
      Complex.normSq (F x)) =
      (bombieriCriticalCrossCorrelation g g 0).re := by
    calc
      (∫ x : ℝ in Set.Icc l r, Complex.normSq (F x)) =
          ∫ x : ℝ, Complex.normSq (g x) := hL2full
      _ = ∫ x : ℝ in Set.Ioi 0, Complex.normSq (g x) := hL2pos.symm
      _ = (bombieriCriticalCrossCorrelation g g 0).re := hcorr.symm
  have hholder :=
    sq_setIntegral_norm_le_length_mul_setIntegral_normSq F hlr
  rw [hL1, hL2] at hholder
  exact hholder

/-- The radius-`1 / 1000` unit-mass bump has strictly negative isolated
factor-two core diagonal. -/
theorem bombieriCoreDiagonal_mellinBumpSequence_999_neg :
    bombieriCoreDiagonal (mellinBumpSequence 999) < 0 := by
  let g : BombieriTest := mellinBumpSequence 999
  let ε : ℝ := 1 / 1000
  change bombieriCoreDiagonal g < 0
  have hε : 0 < ε := by norm_num [ε]
  have hsupport : tsupport (g : ℝ → ℂ) ⊆
      Set.Ioo (Real.exp (-ε)) (Real.exp ε) := by
    have hradius : mellinBumpRadius 999 = ε := by
      norm_num [mellinBumpRadius, ε]
    simpa only [g, hradius] using mellinBumpSequence_support 999
  have hsupportClosed : tsupport (g : ℝ → ℂ) ⊆
      Set.Icc (Real.exp (-ε)) (Real.exp ε) :=
    hsupport.trans Set.Ioo_subset_Icc_self
  have hreal : ∀ x, 0 ≤ (g x).re ∧ (g x).im = 0 := by
    simpa only [g] using mellinBumpSequence_real_nonnegative 999
  have hmass : (∫ x : ℝ, (g x).re) = 1 := by
    simpa only [g] using mellinBumpSequence_unit_mass 999
  have hlr : Real.exp (-ε) ≤ Real.exp ε :=
    Real.exp_le_exp.mpr (by linarith)
  have hmassCorrelation : 1 ≤
      (Real.exp ε - Real.exp (-ε)) *
        (bombieriCriticalCrossCorrelation g g 0).re := by
    have hholder := sq_integral_re_le_length_mul_critical_zero
      g hlr hsupportClosed hreal
    simpa only [hmass, one_pow] using hholder
  have hexpUpper : Real.exp ε ≤ 1 / (1 - ε) :=
    Real.exp_bound_div_one_sub_of_interval hε.le (by norm_num [ε])
  have hexpNegLower : 1 - ε ≤ Real.exp (-ε) :=
    Real.one_sub_le_exp_neg ε
  have hwidth : Real.exp ε - Real.exp (-ε) ≤ (1 / 400 : ℝ) := by
    calc
      Real.exp ε - Real.exp (-ε) ≤
          1 / (1 - ε) - (1 - ε) :=
        sub_le_sub hexpUpper hexpNegLower
      _ ≤ (1 / 400 : ℝ) := by norm_num [ε]
  have hcorrelationNonneg :
      0 ≤ (bombieriCriticalCrossCorrelation g g 0).re := by
    rw [bombieriCriticalCrossCorrelation_self_zero_eq_quadratic_one,
      bombieriQuadraticTest_apply_one, integral_complex_ofReal]
    exact integral_nonneg fun x ↦ Complex.normSq_nonneg (g x)
  have hcorrelationLower :
      400 ≤ (bombieriCriticalCrossCorrelation g g 0).re := by
    have hproduct := mul_le_mul_of_nonneg_right hwidth hcorrelationNonneg
    have hscaled : 1 ≤
        (1 / 400 : ℝ) *
          (bombieriCriticalCrossCorrelation g g 0).re :=
      hmassCorrelation.trans hproduct
    nlinarith
  have hcorrelationPos :
      0 < (bombieriCriticalCrossCorrelation g g 0).re :=
    lt_of_lt_of_le (by norm_num) hcorrelationLower
  have hsmallZero : ‖((0 : ℂ) - 1)‖ * ε ≤ 1 := by
    norm_num [ε]
  have hMellinZeroError :
      ‖mellin (g : ℝ → ℂ) 0 - 1‖ ≤ (1 / 500 : ℝ) := by
    have h := norm_mellin_sub_one_le_of_unit_mass_log_support
      g ε hε hsupport hreal hmass 0 hsmallZero
    have hconstant :
        2 * ‖((0 : ℂ) - 1)‖ * ε = (1 / 500 : ℝ) := by
      norm_num [ε]
    rw [hconstant] at h
    exact h
  have hsmallOne : ‖((1 : ℂ) - 1)‖ * ε ≤ 1 := by
    norm_num
  have hMellinOneError :
      ‖mellin (g : ℝ → ℂ) 1 - 1‖ ≤ 0 := by
    have h := norm_mellin_sub_one_le_of_unit_mass_log_support
      g ε hε hsupport hreal hmass 1 hsmallOne
    simpa using h
  have hMellinOne : mellin (g : ℝ → ℂ) 1 = 1 := by
    have hnorm : ‖mellin (g : ℝ → ℂ) 1 - 1‖ = 0 :=
      le_antisymm hMellinOneError (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  have hMellinZeroNorm :
      ‖mellin (g : ℝ → ℂ) 0‖ ≤ (501 / 500 : ℝ) := by
    calc
      ‖mellin (g : ℝ → ℂ) 0‖ =
          ‖(mellin (g : ℝ → ℂ) 0 - 1) + 1‖ := by
        rw [sub_add_cancel]
      _ ≤ ‖mellin (g : ℝ → ℂ) 0 - 1‖ + ‖(1 : ℂ)‖ :=
        norm_add_le _ _
      _ = ‖mellin (g : ℝ → ℂ) 0 - 1‖ + 1 := by norm_num
      _ ≤ (1 / 500 : ℝ) + 1 := by
        linarith [hMellinZeroError]
      _ = (501 / 500 : ℝ) := by norm_num
  have hMellinZeroRe :
      (mellin (g : ℝ → ℂ) 0).re ≤ (501 / 500 : ℝ) :=
    (Complex.re_le_norm _).trans hMellinZeroNorm
  have hCauchy := bombieriInitialCauchyValue_re_nonneg g
  have hgammaMass : 200 < Real.eulerMascheroniConstant *
      (bombieriCriticalCrossCorrelation g g 0).re := by
    calc
      200 ≤ (1 / 2 : ℝ) *
          (bombieriCriticalCrossCorrelation g g 0).re := by
        nlinarith [hcorrelationLower]
      _ < Real.eulerMascheroniConstant *
          (bombieriCriticalCrossCorrelation g g 0).re :=
        mul_lt_mul_of_pos_right
          Real.one_half_lt_eulerMascheroniConstant hcorrelationPos
  have hlogPi : 0 < Real.log Real.pi :=
    Real.log_pos (by linarith [Real.pi_gt_three])
  have hlogPiMass : 0 < Real.log Real.pi *
      (bombieriCriticalCrossCorrelation g g 0).re :=
    mul_pos hlogPi hcorrelationPos
  unfold bombieriCoreDiagonal bombieriCoreDiagonalSymbol
  rw [hMellinOne]
  simp only [star_one, one_mul, mul_one, add_re, sub_re, mul_re,
    ofReal_re, ofReal_im, zero_mul, sub_zero, Complex.star_def,
    Complex.conj_re]
  nlinarith

/-- The explicit narrow bump violates the isolated-core norm bound. -/
theorem not_core_bound_mellinBumpSequence_999 :
    ¬ ‖factorTwoCoreCrossSymbol (mellinBumpSequence 999)‖ ≤
      bombieriCoreDiagonal (mellinBumpSequence 999) := by
  intro hbound
  have hnorm :=
    norm_nonneg (factorTwoCoreCrossSymbol (mellinBumpSequence 999))
  have hcore := bombieriCoreDiagonal_mellinBumpSequence_999_neg
  linarith

/-- The explicit core-bound counterexample belongs to the support-ratio-at-most
two seed class used by the factor-two determinant reduction. -/
theorem exists_factorTwo_support_not_core_bound :
    ∃ a b : ℝ,
      0 < a ∧ a ≤ b ∧
      tsupport (mellinBumpSequence 999 : ℝ → ℂ) ⊆ Set.Icc a b ∧
      b / a ≤ 2 ∧
      ¬ ‖factorTwoCoreCrossSymbol (mellinBumpSequence 999)‖ ≤
        bombieriCoreDiagonal (mellinBumpSequence 999) := by
  let ε : ℝ := 1 / 1000
  let a : ℝ := Real.exp (-ε)
  let b : ℝ := Real.exp ε
  have hε : 0 < ε := by norm_num [ε]
  have ha : 0 < a := Real.exp_pos _
  have hab : a ≤ b := Real.exp_le_exp.mpr (by
    linarith)
  have hsupport : tsupport (mellinBumpSequence 999 : ℝ → ℂ) ⊆
      Set.Icc a b := by
    have hradius : mellinBumpRadius 999 = ε := by
      norm_num [mellinBumpRadius, ε]
    have hopen := mellinBumpSequence_support 999
    simpa only [a, b, hradius] using
      hopen.trans Set.Ioo_subset_Icc_self
  have hexpUpper : Real.exp ε ≤ 1 / (1 - ε) :=
    Real.exp_bound_div_one_sub_of_interval hε.le (by norm_num [ε])
  have hexpNegLower : 1 - ε ≤ Real.exp (-ε) :=
    Real.one_sub_le_exp_neg ε
  have hratio : b / a ≤ 2 := by
    rw [div_le_iff₀ ha]
    calc
      b = Real.exp ε := rfl
      _ ≤ 1 / (1 - ε) := hexpUpper
      _ ≤ 2 * (1 - ε) := by norm_num [ε]
      _ ≤ 2 * Real.exp (-ε) := by linarith
      _ = 2 * a := rfl
  exact ⟨a, b, ha, hab, hsupport, hratio,
    not_core_bound_mellinBumpSequence_999⟩

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoCoreExplicitObstruction
