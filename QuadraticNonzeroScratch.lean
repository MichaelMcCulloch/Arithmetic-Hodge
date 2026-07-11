import ArithmeticHodge.Analysis.MultiplicativeWeilQuadratic

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ContDiff Distributions

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

theorem bombieriQuadraticTest_ne_zero (g : BombieriTest) (hg : g ≠ 0) :
    bombieriQuadraticTest g ≠ 0 := by
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
    exact g.hasCompactSupport.comp_left (by simp [h])
  have hnonneg : 0 ≤ h := fun y ↦ Complex.normSq_nonneg (g y)
  have hxne : h x ≠ 0 := by
    exact (Complex.normSq_eq_zero.not.mpr hx)
  have hpos : 0 < ∫ y : ℝ, h y :=
    hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero
      hcompact hnonneg hxne
  have hset : (∫ y : ℝ in Ioi 0, h y) = ∫ y : ℝ, h y := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hynpos : ¬ 0 < y := by simpa using hy
    have hgy : g y = 0 := by
      by_contra hne
      have hmem := g.tsupport_subset
        (subset_tsupport g (Function.mem_support.mpr hne))
      exact hynpos (by simpa [positiveHalfLine] using hmem)
    simp [h, hgy]
  intro hzero
  have hvalue : bombieriQuadraticTest g 1 = 0 := by
    rw [hzero]
    rfl
  rw [bombieriQuadraticTest_apply_one, integral_complex_ofReal] at hvalue
  change ((∫ y : ℝ in Ioi 0, h y : ℝ) : ℂ) = 0 at hvalue
  rw [hset] at hvalue
  exact hpos.ne' (Complex.ofReal_eq_zero.mp hvalue)

#print axioms bombieriQuadraticTest_ne_zero

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
