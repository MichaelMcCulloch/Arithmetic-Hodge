import ArithmeticHodge.Analysis.MultiplicativeWeilQuadraticCriticalLine

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ArithmeticFunction ContDiff Distributions

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

theorem bombieriQuadraticTest_apply_two_eq_zero_of_support_ratio_le_two
    (g : BombieriTest) {a b : ℝ} (ha : 0 < a)
    (hsupport : tsupport g ⊆ Set.Icc a b) (hratio : b / a ≤ 2) :
    bombieriQuadraticTest g 2 = 0 := by
  rw [bombieriQuadraticTest_apply, autocorrelation]
  apply integral_eq_zero_of_ae
  filter_upwards [(countable_singleton a).ae_notMem
      (volume.restrict (Ioi 0))] with y hy
  by_cases hgy : g y = 0
  · simp [hgy]
  by_cases hg2y : g (2 * y) = 0
  · simp [hg2y]
  exfalso
  apply hy
  have hymem := hsupport
    (subset_tsupport g (Function.mem_support.mpr hgy))
  have h2ymem := hsupport
    (subset_tsupport g (Function.mem_support.mpr hg2y))
  have hba : b ≤ 2 * a := (div_le_iff₀ ha).mp hratio
  simp only [mem_singleton_iff]
  nlinarith [hymem.1, h2ymem.2]

theorem bombieriQuadraticTest_apply_half_eq_zero_of_support_ratio_le_two
    (g : BombieriTest) {a b : ℝ} (ha : 0 < a)
    (hsupport : tsupport g ⊆ Set.Icc a b) (hratio : b / a ≤ 2) :
    bombieriQuadraticTest g (1 / 2 : ℝ) = 0 := by
  rw [bombieriQuadraticTest_apply, autocorrelation]
  apply integral_eq_zero_of_ae
  filter_upwards [(countable_singleton (2 * a)).ae_notMem
      (volume.restrict (Ioi 0))] with y hy
  by_cases hgy : g y = 0
  · simp [hgy]
  by_cases hghalfy : g ((1 / 2 : ℝ) * y) = 0
  · have hghalfy' : g ((2 : ℝ)⁻¹ * y) = 0 := by
      norm_num at hghalfy ⊢
      exact hghalfy
    simp [hghalfy']
  exfalso
  apply hy
  have hymem := hsupport
    (subset_tsupport g (Function.mem_support.mpr hgy))
  have hhalfymem := hsupport
    (subset_tsupport g (Function.mem_support.mpr hghalfy))
  have hba : b ≤ 2 * a := (div_le_iff₀ ha).mp hratio
  simp only [mem_singleton_iff]
  nlinarith [hymem.2, hhalfymem.1]

theorem primeSum_bombieriQuadraticTest_eq_zero_of_support_ratio_le_two
    (g : BombieriTest) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b) (hratio : b / a ≤ 2) :
    primeSum (bombieriQuadraticTest g) = 0 := by
  have htwo := bombieriQuadraticTest_apply_two_eq_zero_of_support_ratio_le_two
    g ha hsupport hratio
  have hhalf := bombieriQuadraticTest_apply_half_eq_zero_of_support_ratio_le_two
    g ha hsupport hratio
  rw [primeSum]
  have hterm (k : ℕ) :
      vonMangoldtPrimeSummand (bombieriQuadraticTest g) k = 0 := by
    cases k with
    | zero =>
        simp [vonMangoldtPrimeSummand]
    | succ k =>
        let n : ℝ := ((k + 1 + 1 : ℕ) : ℝ)
        have hn : 2 ≤ n := by
          dsimp only [n]
          exact_mod_cast (show 2 ≤ k + 1 + 1 by omega)
        have hnpos : 0 < n := zero_lt_two.trans_le hn
        have hdirect : bombieriQuadraticTest g n = 0 := by
          by_cases hn2 : n = 2
          · simpa only [hn2] using htwo
          · have hnlt : 2 < n := lt_of_le_of_ne hn (Ne.symm hn2)
            by_contra hne
            have hmem := bombieriQuadraticTest_tsupport_subset_Icc
              g ha hab hsupport
              (subset_tsupport (bombieriQuadraticTest g)
                (Function.mem_support.mpr hne))
            have : n ≤ b / a := hmem.2
            exact (not_lt_of_ge this) (hratio.trans_lt hnlt)
        have hinverse : bombieriQuadraticTest g n⁻¹ = 0 := by
          by_cases hn2 : n = 2
          · rw [hn2]
            rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
            exact hhalf
          · have hnlt : 2 < n := lt_of_le_of_ne hn (Ne.symm hn2)
            have hinvlt : n⁻¹ < (1 / 2 : ℝ) := by
              simpa only [one_div] using
                (inv_lt_inv₀ hnpos (by norm_num : (0 : ℝ) < 2)).2 hnlt
            by_contra hne
            have hmem := bombieriQuadraticTest_tsupport_subset_Icc
              g ha hab hsupport
              (subset_tsupport (bombieriQuadraticTest g)
                (Function.mem_support.mpr hne))
            have hlower : a / b ≤ n⁻¹ := hmem.1
            have hb : 0 < b := ha.trans_le hab
            have hhalfLe : (1 / 2 : ℝ) ≤ a / b := by
              rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hb]
              nlinarith [(div_le_iff₀ ha).mp hratio]
            exact (not_lt_of_ge (hhalfLe.trans hlower)) hinvlt
        have hreflected :
            transpose (bombieriQuadraticTest g : ℝ → ℂ) n = 0 := by
          rw [transpose_apply_of_pos _ hnpos, hinverse, zero_div]
        change (ArithmeticFunction.vonMangoldt (k + 1 + 1) : ℂ) *
          (bombieriQuadraticTest g n +
            transpose (bombieriQuadraticTest g : ℝ → ℂ) n) = 0
        rw [hdirect, hreflected, zero_add, mul_zero]
  simp only [hterm, tsum_zero]

theorem bombieriFunctional_quadratic_eq_polar_add_arch_of_support_ratio_le_two
    (g : BombieriTest) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b) (hratio : b / a ≤ 2) :
    bombieriFunctional (bombieriQuadraticTest g) =
      mellin (bombieriQuadraticTest g : ℝ → ℂ) 1 +
        mellin (bombieriQuadraticTest g : ℝ → ℂ) 0 +
          bombieriArchTerm (bombieriQuadraticTest g) := by
  rw [bombieriFunctional_apply,
    primeSum_bombieriQuadraticTest_eq_zero_of_support_ratio_le_two
      g ha hab hsupport hratio]
  ring

theorem bombieriFunctional_quadratic_eq_local_critical_form_le_two
    (g : BombieriTest) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b) (hratio : b / a ≤ 2) :
    bombieriFunctional (bombieriQuadraticTest g) =
      ((2 * (mellin (g : ℝ → ℂ) 1 *
        starRingEnd ℂ (mellin (g : ℝ → ℂ) 0)).re : ℝ) : ℂ) +
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ,
          (((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * Complex.I)).re -
            Real.log Real.pi : ℝ) : ℂ) *
              (Complex.normSq
                (mellin (g : ℝ → ℂ)
                  ((1 / 2 : ℝ) + v * Complex.I)) : ℂ) := by
  rw [bombieriFunctional_quadratic_eq_polar_add_arch_of_support_ratio_le_two
      g ha hab hsupport hratio,
    bombieriQuadratic_polar_eq_two_re,
    bombieriArchTerm_quadratic_eq_critical_normSq_integral]

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
