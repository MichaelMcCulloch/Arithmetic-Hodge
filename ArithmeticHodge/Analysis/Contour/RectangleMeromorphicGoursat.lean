import ArithmeticHodge.Analysis.ResidueRectangle
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.MeasureTheory.Topology

/-!
# Meromorphic Cauchy--Goursat on rectangles

A meromorphic function with nonnegative order throughout a closed rectangle has
vanishing raw rectangular boundary integral.
-/

set_option autoImplicit false

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

namespace ArithmeticHodge.Analysis

noncomputable section

private theorem intervalIntegral_comp_congr_codiscreteWithin
    {A B : ℂ → ℂ} {U : Set ℂ}
    (hAB : A =ᶠ[codiscreteWithin U] B)
    {a b : ℝ} (edge : ℝ → ℂ) (hedge : Function.Injective edge)
    (hmap : MapsTo edge (Ι a b) U) :
    (∫ t : ℝ in a..b, A (edge t)) = ∫ t : ℝ in a..b, B (edge t) := by
  let D : Set ℂ := {s | A s ≠ B s} ∩ U
  have hDdiscrete : IsDiscrete D := by
    apply isDiscrete_of_codiscreteWithin
    have heq : {s : ℂ | A s ≠ B s}ᶜ = {s : ℂ | A s = B s} := by
      ext s
      simp
    rw [heq]
    exact hAB
  have hDcount : D.Countable := by
    haveI : DiscreteTopology D := isDiscrete_iff_discreteTopology.mp hDdiscrete
    exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hpre : (edge ⁻¹' D).Countable := hDcount.preimage hedge
  apply intervalIntegral.integral_congr_ae_restrict
  filter_upwards [hpre.ae_notMem (volume.restrict (Ι a b)),
    ae_restrict_mem measurableSet_uIoc] with t htD ht
  change edge t ∉ D at htD
  by_contra hne
  exact htD ⟨hne, hmap ht⟩

/-- The rectangular boundary integral is unchanged when two functions agree
away from a discrete subset of the closed rectangle. -/
theorem rectIntegral_congr_codiscreteWithin
    {A B : ℂ → ℂ} {z w : ℂ}
    (hAB : A =ᶠ[codiscreteWithin ([[z.re, w.re]] ×ℂ [[z.im, w.im]])] B) :
    rectIntegral A z w = rectIntegral B z w := by
  let U : Set ℂ := [[z.re, w.re]] ×ℂ [[z.im, w.im]]
  change A =ᶠ[codiscreteWithin U] B at hAB
  let bottom : ℝ → ℂ := fun t ↦ (t : ℂ) + (z.im : ℂ) * I
  let top : ℝ → ℂ := fun t ↦ (t : ℂ) + (w.im : ℂ) * I
  let right : ℝ → ℂ := fun t ↦ (w.re : ℂ) + (t : ℂ) * I
  let left : ℝ → ℂ := fun t ↦ (z.re : ℂ) + (t : ℂ) * I
  have hbottom_inj : Function.Injective bottom := by
    intro x y h
    have hre := congrArg Complex.re h
    simpa only [bottom, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero] using hre
  have htop_inj : Function.Injective top := by
    intro x y h
    have hre := congrArg Complex.re h
    simpa only [top, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero] using hre
  have hright_inj : Function.Injective right := by
    intro x y h
    have him := congrArg Complex.im h
    simpa only [right, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im,
      mul_one, zero_mul, add_zero, zero_add] using him
  have hleft_inj : Function.Injective left := by
    intro x y h
    have him := congrArg Complex.im h
    simpa only [left, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im,
      mul_one, zero_mul, add_zero, zero_add] using him
  have hbottom_map : MapsTo bottom (Ι z.re w.re) U := by
    intro t ht
    change bottom t ∈ ([[z.re, w.re]] ×ℂ [[z.im, w.im]])
    rw [mem_reProdIm]
    simpa only [bottom, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero, add_im, mul_im, mul_one,
      zero_add] using
        (show t ∈ [[z.re, w.re]] ∧ z.im ∈ [[z.im, w.im]] from
          ⟨uIoc_subset_uIcc ht, left_mem_uIcc⟩)
  have htop_map : MapsTo top (Ι z.re w.re) U := by
    intro t ht
    change top t ∈ ([[z.re, w.re]] ×ℂ [[z.im, w.im]])
    rw [mem_reProdIm]
    simpa only [top, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero, add_im, mul_im, mul_one,
      zero_add] using
        (show t ∈ [[z.re, w.re]] ∧ w.im ∈ [[z.im, w.im]] from
          ⟨uIoc_subset_uIcc ht, right_mem_uIcc⟩)
  have hright_map : MapsTo right (Ι z.im w.im) U := by
    intro t ht
    change right t ∈ ([[z.re, w.re]] ×ℂ [[z.im, w.im]])
    rw [mem_reProdIm]
    simpa only [right, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero, add_im, mul_im, mul_one,
      zero_add] using
        (show w.re ∈ [[z.re, w.re]] ∧ t ∈ [[z.im, w.im]] from
          ⟨right_mem_uIcc, uIoc_subset_uIcc ht⟩)
  have hleft_map : MapsTo left (Ι z.im w.im) U := by
    intro t ht
    change left t ∈ ([[z.re, w.re]] ×ℂ [[z.im, w.im]])
    rw [mem_reProdIm]
    simpa only [left, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero, add_im, mul_im, mul_one,
      zero_add] using
        (show z.re ∈ [[z.re, w.re]] ∧ t ∈ [[z.im, w.im]] from
          ⟨left_mem_uIcc, uIoc_subset_uIcc ht⟩)
  have hbottom := intervalIntegral_comp_congr_codiscreteWithin hAB bottom
    hbottom_inj hbottom_map
  have htop := intervalIntegral_comp_congr_codiscreteWithin hAB top
    htop_inj htop_map
  have hright := intervalIntegral_comp_congr_codiscreteWithin hAB right
    hright_inj hright_map
  have hleft := intervalIntegral_comp_congr_codiscreteWithin hAB left
    hleft_inj hleft_map
  have hrect : rectIntegral A z w = rectIntegral B z w := by
    unfold rectIntegral
    rw [show (∫ t : ℝ in z.re..w.re,
          A ((t : ℂ) + (z.im : ℂ) * I)) =
        ∫ t : ℝ in z.re..w.re,
          B ((t : ℂ) + (z.im : ℂ) * I) by
      simpa only [bottom] using hbottom]
    rw [show (∫ t : ℝ in z.re..w.re,
          A ((t : ℂ) + (w.im : ℂ) * I)) =
        ∫ t : ℝ in z.re..w.re,
          B ((t : ℂ) + (w.im : ℂ) * I) by
      simpa only [top] using htop]
    rw [show (∫ t : ℝ in z.im..w.im,
          A ((w.re : ℂ) + (t : ℂ) * I)) =
        ∫ t : ℝ in z.im..w.im,
          B ((w.re : ℂ) + (t : ℂ) * I) by
      simpa only [right] using hright]
    rw [show (∫ t : ℝ in z.im..w.im,
          A ((z.re : ℂ) + (t : ℂ) * I)) =
        ∫ t : ℝ in z.im..w.im,
          B ((z.re : ℂ) + (t : ℂ) * I) by
      simpa only [left] using hleft]
  exact hrect

/-- If a function is meromorphic on a closed rectangle and has no poles there,
then its raw rectangular boundary integral vanishes. -/
theorem rectIntegral_eq_zero_of_meromorphicOrderAt_nonneg
    {A : ℂ → ℂ} {z w : ℂ}
    (hA : MeromorphicOn A ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (hord : ∀ s ∈ ([[z.re, w.re]] ×ℂ [[z.im, w.im]]),
      0 ≤ meromorphicOrderAt A s) :
    rectIntegral A z w = 0 := by
  let U : Set ℂ := [[z.re, w.re]] ×ℂ [[z.im, w.im]]
  change MeromorphicOn A U at hA
  change ∀ s ∈ U, 0 ≤ meromorphicOrderAt A s at hord
  let B : ℂ → ℂ := toMeromorphicNFOn A U
  have hB_nf : MeromorphicNFOn B U := by
    simpa only [B] using meromorphicNFOn_toMeromorphicNFOn A U
  have hB_an : AnalyticOnNhd ℂ B U := by
    intro s hs
    refine (hB_nf hs).meromorphicOrderAt_nonneg_iff_analyticAt.1 ?_
    rw [show meromorphicOrderAt B s = meromorphicOrderAt A s by
      simpa only [B] using meromorphicOrderAt_toMeromorphicNFOn hA hs]
    exact hord s hs
  have hB_diff : DifferentiableOn ℂ B U := by
    intro s hs
    exact (hB_an s hs).differentiableAt.differentiableWithinAt
  have hB_zero : rectIntegral B z w = 0 :=
    rectIntegral_eq_zero_of_differentiableOn hB_diff
  have hAB : A =ᶠ[codiscreteWithin U] B := by
    simpa only [B] using toMeromorphicNFOn_eqOn_codiscrete hA
  have hrect : rectIntegral A z w = rectIntegral B z w :=
    rectIntegral_congr_codiscreteWithin (by simpa only [U] using hAB)
  exact hrect.trans hB_zero

end

end ArithmeticHodge.Analysis
