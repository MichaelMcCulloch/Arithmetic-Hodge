import ArithmeticHodge.Analysis.MultiplicativeWeilQuadraticCrossIntegral

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ContDiff Distributions

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-!
# A structural obstruction to additive support localization

A short-support test and a normalized dilation of it each lie in the proven
restricted class.  Their mixed quadratic test nevertheless contains an exact,
strictly positive long-range correlation.  Thus positivity cannot be summed
piecewise without a new cross-term estimate.
-/

/-- The value at one of a nonzero quadratic Bombieri test has strictly
positive real part. -/
theorem bombieriQuadraticTest_apply_one_re_pos
    (g : BombieriTest) (hg : g ≠ 0) :
    0 < (bombieriQuadraticTest g 1).re := by
  obtain ⟨x, hx⟩ : ∃ x : ℝ, g x ≠ 0 := by
    by_contra h
    push_neg at h
    apply hg
    ext y
    simpa using h y
  let h : ℝ → ℝ := fun y ↦ Complex.normSq (g y)
  have hcont : Continuous h :=
    Complex.continuous_normSq.comp g.contDiff.continuous
  have hcompact : HasCompactSupport h := by
    exact g.hasCompactSupport.comp_left (by simp)
  have hnonneg : 0 ≤ h := fun y ↦ Complex.normSq_nonneg (g y)
  have hxne : h x ≠ 0 := Complex.normSq_eq_zero.not.mpr hx
  have hpos : 0 < ∫ y : ℝ, h y :=
    hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero
      hcompact hnonneg hxne
  have hset : (∫ y : ℝ in Set.Ioi 0, h y) = ∫ y : ℝ, h y := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hynpos : ¬ 0 < y := by simpa using hy
    have hgy : g y = 0 := by
      by_contra hne
      have hmem := g.tsupport_subset
        (subset_tsupport g (Function.mem_support.mpr hne))
      exact hynpos (by simpa [positiveHalfLine] using hmem)
    simp [h, hgy]
  rw [bombieriQuadraticTest_apply_one, integral_complex_ofReal]
  change 0 < ∫ y : ℝ in Set.Ioi 0, h y
  rw [hset]
  exact hpos

/-- At the inverse dilation, the directed correlation from the original test
to its dilation vanishes when the two sampled arguments are separated beyond
the support ratio. -/
theorem bombieriDirectedCorrelation_inv_normalizedDilation_eq_zero
    (g : BombieriTest) {a b lambda : ℝ}
    (hlambda : 0 < lambda)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hsep : b < lambda ^ 2 * a) :
    bombieriDirectedCorrelation g
      (normalizedDilation lambda hlambda g) lambda⁻¹ = 0 := by
  unfold bombieriDirectedCorrelation
  apply integral_eq_zero_of_ae
  filter_upwards [] with y
  change g (lambda⁻¹ * y) *
      starRingEnd ℂ (normalizedDilation lambda hlambda g y) = 0
  rw [normalizedDilation_apply]
  simp only [map_mul, Complex.conj_ofReal]
  by_cases hleft : g (lambda⁻¹ * y) = 0
  · simp [hleft]
  by_cases hright : g (lambda * y) = 0
  · simp [hright]
  exfalso
  have hleftMem := hsupport
    (subset_tsupport g (Function.mem_support.mpr hleft))
  have hrightMem := hsupport
    (subset_tsupport g (Function.mem_support.mpr hright))
  have hy : lambda * a ≤ y := by
    calc
      lambda * a ≤ lambda * (lambda⁻¹ * y) :=
        mul_le_mul_of_nonneg_left hleftMem.1 hlambda.le
      _ = y := by field_simp [hlambda.ne']
  have hbad : lambda ^ 2 * a ≤ b := by
    calc
      lambda ^ 2 * a = lambda * (lambda * a) := by ring
      _ ≤ lambda * y := mul_le_mul_of_nonneg_left hy hlambda.le
      _ ≤ b := hrightMem.2
  exact (not_le_of_gt hsep) hbad

/-- The opposite directed correlation is exactly the positive diagonal mass. -/
theorem bombieriDirectedCorrelation_normalizedDilation_inv_eq
    (g : BombieriTest) (lambda : ℝ) (hlambda : 0 < lambda) :
    bombieriDirectedCorrelation
        (normalizedDilation lambda hlambda g) g lambda⁻¹ =
      ((Real.sqrt lambda : ℝ) : ℂ) * bombieriQuadraticTest g 1 := by
  rw [bombieriQuadraticTest_apply_one]
  unfold bombieriDirectedCorrelation
  calc
    (∫ y : ℝ in Set.Ioi 0,
        normalizedDilation lambda hlambda g (lambda⁻¹ * y) *
          starRingEnd ℂ (g y)) =
        ∫ y : ℝ in Set.Ioi 0,
          ((Real.sqrt lambda : ℝ) : ℂ) *
            (Complex.normSq (g y) : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y _hy
      change normalizedDilation lambda hlambda g (lambda⁻¹ * y) *
          starRingEnd ℂ (g y) =
        ((Real.sqrt lambda : ℝ) : ℂ) *
          (Complex.normSq (g y) : ℂ)
      rw [normalizedDilation_apply]
      have harg : lambda * (lambda⁻¹ * y) = y := by
        field_simp [hlambda.ne']
      rw [harg, Complex.normSq_eq_conj_mul_self]
      ring
    _ = ((Real.sqrt lambda : ℝ) : ℂ) *
        ∫ y : ℝ in Set.Ioi 0,
          (Complex.normSq (g y) : ℂ) := by
      exact MeasureTheory.integral_const_mul
        (μ := volume.restrict (Set.Ioi 0)) _ _

/-- Exact mixed-test value for a separated normalized dilation. -/
theorem bombieriQuadraticCrossTest_inv_dilation_eq
    (g : BombieriTest) {a b lambda : ℝ}
    (hlambda : 0 < lambda)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hsep : b < lambda ^ 2 * a) :
    bombieriQuadraticCrossTest g
        (normalizedDilation lambda hlambda g) lambda⁻¹ =
      ((Real.sqrt lambda : ℝ) : ℂ) * bombieriQuadraticTest g 1 := by
  rw [bombieriQuadraticCrossTest_apply,
    bombieriDirectedCorrelation_inv_normalizedDilation_eq_zero
      g hlambda hsupport hsep,
    bombieriDirectedCorrelation_normalizedDilation_inv_eq]
  exact zero_add _

/-- The mixed value is strictly positive for every nonzero separated test. -/
theorem bombieriQuadraticCrossTest_inv_dilation_re_pos
    (g : BombieriTest) {a b lambda : ℝ}
    (hg : g ≠ 0) (hlambda : 0 < lambda)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hsep : b < lambda ^ 2 * a) :
    0 < (bombieriQuadraticCrossTest g
      (normalizedDilation lambda hlambda g) lambda⁻¹).re := by
  rw [bombieriQuadraticCrossTest_inv_dilation_eq
    g hlambda hsupport hsep]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  exact mul_pos (Real.sqrt_pos.2 hlambda)
    (bombieriQuadraticTest_apply_one_re_pos g hg)

/-- Endpoint specialization: two ratio-at-most-two pieces separated by the
factor-two normalized dilation already have a nonzero mixed correlation. -/
theorem bombieriQuadraticCrossTest_half_dilation_re_pos_of_ratio_le_two
    (g : BombieriTest) {a b : ℝ}
    (hg : g ≠ 0) (ha : 0 < a)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    0 < (bombieriQuadraticCrossTest g
      (normalizedDilation 2 (by norm_num) g) (1 / 2 : ℝ)).re := by
  have hba : b ≤ 2 * a := (div_le_iff₀ ha).mp hratio
  have hsep : b < (2 : ℝ) ^ 2 * a := by
    nlinarith
  simpa only [one_div] using
    bombieriQuadraticCrossTest_inv_dilation_re_pos
      g hg (by norm_num : (0 : ℝ) < 2) hsupport hsep

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
