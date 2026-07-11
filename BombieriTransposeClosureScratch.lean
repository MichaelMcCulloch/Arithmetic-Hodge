import ArithmeticHodge.Analysis.MultiplicativeWeil

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ContDiff Distributions

namespace ArithmeticHodge.Analysis.MultiplicativeWeil.TransposeClosureScratch

noncomputable section

private def transposeSupport (f : BombieriTest) : Set ℝ :=
  Inv.inv '' tsupport f

private theorem transposeSupport_isCompact (f : BombieriTest) :
    IsCompact (transposeSupport f) := by
  exact f.hasCompactSupport.image_of_continuousOn
    (continuousOn_inv₀.mono fun x hx ↦ (f.tsupport_subset hx).ne')

private theorem transposeSupport_subset_pos (f : BombieriTest) :
    transposeSupport f ⊆ Ioi 0 := by
  rintro x ⟨y, hy, rfl⟩
  have hypos := f.tsupport_subset hy
  change 0 < y at hypos
  exact inv_pos.mpr hypos

private theorem support_transpose_subset (f : BombieriTest) :
    Function.support (transpose (f : ℝ → ℂ)) ⊆ transposeSupport f := by
  intro x hx
  refine ⟨x⁻¹, subset_tsupport f ?_, inv_inv x⟩
  exact Function.mem_support.mpr (mul_ne_zero_iff.mp hx).2

private theorem transpose_hasCompactSupport (f : BombieriTest) :
    HasCompactSupport (transpose (f : ℝ → ℂ)) := by
  refine HasCompactSupport.intro (transposeSupport_isCompact f) ?_
  intro x hx
  apply not_ne_iff.mp
  intro hne
  exact hx (support_transpose_subset f (Function.mem_support.mpr hne))

private theorem transpose_tsupport_subset (f : BombieriTest) :
    tsupport (transpose (f : ℝ → ℂ)) ⊆ Ioi 0 := by
  exact (closure_minimal (support_transpose_subset f)
      (transposeSupport_isCompact f).isClosed).trans
    (transposeSupport_subset_pos f)

private theorem transpose_contDiff (f : BombieriTest) :
    ContDiff ℝ ∞ (transpose (f : ℝ → ℂ)) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have hzero : (0 : ℝ) ∉ transposeSupport f := by
      intro h
      have hpos := transposeSupport_subset_pos f h
      change 0 < (0 : ℝ) at hpos
      exact (lt_irrefl 0 hpos)
    have heq : transpose (f : ℝ → ℂ) =ᶠ[nhds (0 : ℝ)] fun _ ↦ 0 := by
      filter_upwards [(transposeSupport_isCompact f).isClosed.compl_mem_nhds hzero]
        with y hy
      apply not_ne_iff.mp
      intro hne
      exact hy (support_transpose_subset f (Function.mem_support.mpr hne))
    exact contDiffAt_const.congr_of_eventuallyEq heq
  · unfold transpose
    simp only [Complex.cpow_neg_one]
    have hofReal : ContDiffAt ℝ ∞ (fun y : ℝ ↦ (y : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt
    have hofRealInv : ContDiffAt ℝ ∞ (fun y : ℝ ↦ (y : ℂ)⁻¹) x :=
      hofReal.inv (Complex.ofReal_ne_zero.mpr hx)
    have hrealInv : ContDiffAt ℝ ∞ (fun y : ℝ ↦ y⁻¹) x :=
      contDiffAt_inv ℝ hx
    exact hofRealInv.mul (f.contDiff.contDiffAt.comp x hrealInv)

private def transposeTest (f : BombieriTest) : BombieriTest :=
  TestFunction.mk (transpose (f : ℝ → ℂ)) (transpose_contDiff f)
    (transpose_hasCompactSupport f) (transpose_tsupport_subset f)

@[simp]
private theorem transposeTest_apply (f : BombieriTest) (x : ℝ) :
    transposeTest f x = transpose (f : ℝ → ℂ) x := rfl

private def transposeLinearMap : BombieriTest →ₗ[ℂ] BombieriTest where
  toFun := transposeTest
  map_add' f g := by
    ext x
    simp only [transposeTest_apply, TestFunction.coe_add, Pi.add_apply]
    simp [transpose, mul_add]
  map_smul' c f := by
    ext x
    simp only [transposeTest_apply, TestFunction.coe_smul, Pi.smul_apply]
    simp [transpose, mul_left_comm]

private def transposeData : TransposeData where
  toLinearMap := transposeLinearMap
  apply_pos _ _ _ := rfl

example : Nonempty TransposeData := ⟨transposeData⟩

#print axioms transposeSupport_isCompact
#print axioms transpose_tsupport_subset
#print axioms transpose_contDiff
#print axioms transposeLinearMap
#print axioms transposeData

end

end ArithmeticHodge.Analysis.MultiplicativeWeil.TransposeClosureScratch
