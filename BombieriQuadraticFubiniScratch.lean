import ArithmeticHodge.Analysis.MultiplicativeWeilQuadratic

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ContDiff Distributions SchwartzMap

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

private def quadraticFubiniSupport (g : BombieriTest) : Set (ℝ × ℝ) :=
  (fun q : ℝ × ℝ ↦ (q.1 / q.2, q.2⁻¹)) '' (tsupport g ×ˢ tsupport g)

private theorem quadraticFubiniSupport_isCompact (g : BombieriTest) :
    IsCompact (quadraticFubiniSupport g) := by
  apply (g.hasCompactSupport.isCompact.prod
    g.hasCompactSupport.isCompact).image_of_continuousOn
  exact (continuousOn_fst.div continuousOn_snd fun q hq ↦
      (g.tsupport_subset hq.2).ne').prodMk
    (ContinuousOn.inv₀ continuousOn_snd fun q hq ↦
      (g.tsupport_subset hq.2).ne')

private theorem quadraticFubiniSupport_subset_pos (g : BombieriTest) :
    quadraticFubiniSupport g ⊆ Ioi 0 ×ˢ Ioi 0 := by
  rintro p ⟨q, hq, rfl⟩
  have hq1 : 0 < q.1 := by
    simpa [positiveHalfLine] using g.tsupport_subset hq.1
  have hq2 : 0 < q.2 := by
    simpa [positiveHalfLine] using g.tsupport_subset hq.2
  exact ⟨div_pos hq1 hq2, inv_pos.mpr hq2⟩

private theorem convolutionMellinKernel_continuousOn_pos
    (g : BombieriTest) (s : ℂ) :
    ContinuousOn
      (convolutionMellinKernel (g : ℝ → ℂ)
        (transposeConjugate (g : ℝ → ℂ)) s)
      (Ioi 0 ×ˢ Ioi 0) := by
  let U : Set (ℝ × ℝ) := Ioi 0 ×ˢ Ioi 0
  let H : ℝ × ℝ → ℂ := fun p ↦
    ((p.1 : ℂ) ^ (s - 1) * g (p.1 / p.2)) *
      ((starRingEnd ℂ (g p.2⁻¹) / p.2) / p.2)
  have hpow : ContinuousOn (fun p : ℝ × ℝ ↦
      (p.1 : ℂ) ^ (s - 1)) U := by
    intro p hp
    exact (Complex.continuousAt_ofReal_cpow_const p.1 (s - 1)
      (Or.inr hp.1.ne')).comp_continuousWithinAt continuousWithinAt_fst
  have hratio : ContinuousOn (fun p : ℝ × ℝ ↦ p.1 / p.2) U :=
    continuousOn_fst.div continuousOn_snd fun p hp ↦ hp.2.ne'
  have hinv : ContinuousOn (fun p : ℝ × ℝ ↦ p.2⁻¹) U :=
    ContinuousOn.inv₀ continuousOn_snd fun p hp ↦ hp.2.ne'
  have hdenom : ContinuousOn (fun p : ℝ × ℝ ↦ (p.2 : ℂ)) U := by
    fun_prop
  have hdenom_ne : ∀ p ∈ U, (p.2 : ℂ) ≠ 0 := fun p hp ↦
    Complex.ofReal_ne_zero.mpr hp.2.ne'
  have hH : ContinuousOn H U := by
    exact (hpow.mul (g.contDiff.continuous.comp_continuousOn hratio)).mul
      (((Complex.conjCLE.continuous.comp_continuousOn
          (g.contDiff.continuous.comp_continuousOn hinv)).div
        hdenom hdenom_ne).div hdenom hdenom_ne)
  apply hH.congr
  intro p hp
  rw [show convolutionMellinKernel (g : ℝ → ℂ)
      (transposeConjugate (g : ℝ → ℂ)) s p =
      ((p.1 : ℂ) ^ (s - 1) * g (p.1 / p.2)) *
        (transposeConjugate (g : ℝ → ℂ) p.2 / p.2) by
    rfl]
  rw [transposeConjugate_apply_of_pos (g : ℝ → ℂ) hp.2]

private theorem convolutionMellinKernel_eq_zero_of_pos_notMem
    (g : BombieriTest) (s : ℂ) (p : ℝ × ℝ)
    (hp : p ∈ Ioi 0 ×ˢ Ioi 0) (hnot : p ∉ quadraticFubiniSupport g) :
    convolutionMellinKernel (g : ℝ → ℂ)
      (transposeConjugate (g : ℝ → ℂ)) s p = 0 := by
  by_cases hratio : g (p.1 / p.2) = 0
  · simp [convolutionMellinKernel, hratio]
  have hinv : g p.2⁻¹ = 0 := by
    by_contra hinv
    apply hnot
    have hp2 : 0 < p.2 := hp.2
    refine ⟨(p.1 / p.2, p.2⁻¹), ⟨subset_tsupport g ?_, subset_tsupport g ?_⟩, ?_⟩
    · exact Function.mem_support.mpr hratio
    · exact Function.mem_support.mpr hinv
    · apply Prod.ext
      · dsimp
        field_simp [hp2.ne']
      · simp
  unfold convolutionMellinKernel
  rw [transposeConjugate_apply_of_pos (g : ℝ → ℂ) hp.2]
  simp [hinv]

/-- Compact support away from zero makes the quadratic Mellin kernel
absolutely integrable at every complex argument. -/
theorem bombieri_quadratic_convolutionFubiniAt
    (g : BombieriTest) (s : ℂ) :
    ConvolutionFubiniAt (g : ℝ → ℂ)
      (transposeConjugate (g : ℝ → ℂ)) s := by
  unfold ConvolutionFubiniAt
  rw [Measure.prod_restrict]
  change IntegrableOn
    (convolutionMellinKernel (g : ℝ → ℂ)
      (transposeConjugate (g : ℝ → ℂ)) s)
    (Ioi 0 ×ˢ Ioi 0) (volume.prod volume)
  have hcompact := quadraticFubiniSupport_isCompact g
  have hcontinuous :=
    (convolutionMellinKernel_continuousOn_pos g s).mono
      (quadraticFubiniSupport_subset_pos g)
  exact (hcontinuous.integrableOn_compact hcompact).of_forall_diff_eq_zero
    (measurableSet_Ioi.prod measurableSet_Ioi) fun p hp ↦
      convolutionMellinKernel_eq_zero_of_pos_notMem g s p hp.1 hp.2

/-- The bundled quadratic Bombieri test has the expected Mellin factor at
every complex argument. -/
theorem bombieriQuadraticTestData_hasMellin
    (g : BombieriTest) (s : ℂ) :
    HasMellin ((bombieriQuadraticTestData g).test : ℝ → ℂ) s
      (spectralTerm (g : ℝ → ℂ) s) := by
  let gc : BombieriTest :=
    TestFunction.postcompCLM Complex.conjCLE.toContinuousLinearMap g
  have hgc : MellinConvergent (fun y : ℝ ↦ starRingEnd ℂ (g y)) (1 - s) := by
    simpa [gc] using gc.mellinConvergent (1 - s)
  have htgc : MellinConvergent
      (transposeConjugate (g : ℝ → ℂ)) s :=
    (mellinConvergent_transpose
      (fun y : ℝ ↦ starRingEnd ℂ (g y)) s).2 hgc
  rw [show ((bombieriQuadraticTestData g).test : ℝ → ℂ) =
      convolution (g : ℝ → ℂ)
        (transposeConjugate (g : ℝ → ℂ)) from
    funext (bombieriQuadraticTestData g).convolution_eq]
  simpa only [mellin_transposeConjugate, spectralTerm] using
    hasMellin_convolution (g : ℝ → ℂ)
      (transposeConjugate (g : ℝ → ℂ)) s
      ⟨g.mellinConvergent s, htgc,
        bombieri_quadratic_convolutionFubiniAt g s⟩

#print axioms bombieri_quadratic_convolutionFubiniAt
#print axioms bombieriQuadraticTestData_hasMellin

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
