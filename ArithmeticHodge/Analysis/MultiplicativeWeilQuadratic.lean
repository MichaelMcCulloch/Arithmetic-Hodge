/-
  Closure of Bombieri's multiplicative test space under its quadratic
  autocorrelation.

  Smoothness is proved using a fixed-support parametric additive convolution.
  Compact support is contained in the ratio image of `tsupport g × tsupport g`,
  which is a compact subset of `(0,∞)`.
-/

import ArithmeticHodge.Analysis.MultiplicativeWeil
import Mathlib.Analysis.Calculus.ContDiff.Convolution

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ContDiff Distributions SchwartzMap Convolution

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

private def quadraticParametricKernel (g : BombieriTest) (p y : ℝ) : ℂ :=
  g (-p * y) * starRingEnd ℂ (g (-y))

private def quadraticRatioSet (g : BombieriTest) : Set ℝ :=
  (fun p : ℝ × ℝ ↦ p.1 / p.2) '' (tsupport g ×ˢ tsupport g)

private theorem quadraticRatioSet_isCompact (g : BombieriTest) :
    IsCompact (quadraticRatioSet g) := by
  apply (g.hasCompactSupport.isCompact.prod
    g.hasCompactSupport.isCompact).image_of_continuousOn
  exact continuousOn_fst.div continuousOn_snd fun p hp ↦
    (g.tsupport_subset hp.2).ne'

private theorem quadraticRatioSet_subset_pos (g : BombieriTest) :
    quadraticRatioSet g ⊆ Ioi 0 := by
  rintro x ⟨p, hp, rfl⟩
  have hp1 : 0 < p.1 := by
    simpa [positiveHalfLine] using g.tsupport_subset hp.1
  have hp2 : 0 < p.2 := by
    simpa [positiveHalfLine] using g.tsupport_subset hp.2
  exact div_pos hp1 hp2

private theorem autocorrelation_eq_zero_of_not_mem_ratio
    (g : BombieriTest) {x : ℝ} (hx : x ∉ quadraticRatioSet g) :
    autocorrelation (g : ℝ → ℂ) x = 0 := by
  unfold autocorrelation
  calc
    (∫ y : ℝ in Ioi 0, g (x * y) * starRingEnd ℂ (g y)) =
        ∫ _y : ℝ in Ioi 0, (0 : ℂ) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      by_cases hgy : g y = 0
      · simp [hgy]
      by_cases hgxy : g (x * y) = 0
      · simp [hgxy]
      exfalso
      apply hx
      have hypos : 0 < y := by simpa using hy
      refine ⟨(x * y, y), ⟨subset_tsupport g ?_, subset_tsupport g ?_⟩, ?_⟩
      · exact Function.mem_support.mpr hgxy
      · exact Function.mem_support.mpr hgy
      · exact (div_eq_iff hypos.ne').2 (by ring)
    _ = 0 := by simp

private theorem quadraticParametricKernel_contDiff (g : BombieriTest) :
    ContDiff ℝ ∞ (fun q : ℝ × ℝ ↦ quadraticParametricKernel g q.1 q.2) := by
  unfold quadraticParametricKernel
  have harg1 : ContDiff ℝ ∞ (fun q : ℝ × ℝ ↦ -q.1 * q.2) := by
    fun_prop
  have harg2 : ContDiff ℝ ∞ (fun q : ℝ × ℝ ↦ -q.2) := by
    fun_prop
  have hg1 : ContDiff ℝ ∞ (fun q : ℝ × ℝ ↦ g (-q.1 * q.2)) :=
    g.contDiff.comp harg1
  have hg2 : ContDiff ℝ ∞ (fun q : ℝ × ℝ ↦ g (-q.2)) :=
    g.contDiff.comp harg2
  exact hg1.mul (Complex.conjCLE.contDiff.comp hg2)

private theorem quadraticParametricKernel_eq_zero_outside
    (g : BombieriTest) (p y : ℝ) (_hp : p ∈ (univ : Set ℝ))
    (hy : y ∉ -(tsupport g)) :
    quadraticParametricKernel g p y = 0 := by
  have hneg : -y ∉ tsupport g := by
    intro h
    exact hy (Set.mem_neg.2 h)
  have hzero : g (-y) = 0 := by
    by_contra hne
    exact hneg (subset_tsupport g (Function.mem_support.mpr hne))
  simp [quadraticParametricKernel, hzero]

private def quadraticSmoothRepresentative (g : BombieriTest) (x : ℝ) : ℂ :=
  ((fun _y : ℝ ↦ (1 : ℂ)) ⋆[
      ContinuousLinearMap.mul ℝ ℂ, volume]
    quadraticParametricKernel g x) 0

private theorem quadraticSmoothRepresentative_contDiff (g : BombieriTest) :
    ContDiff ℝ ∞ (quadraticSmoothRepresentative g) := by
  rw [← contDiffOn_univ]
  exact contDiffOn_convolution_right_with_param_comp
    (ContinuousLinearMap.mul ℝ ℂ)
    (v := fun _x : ℝ ↦ (0 : ℝ)) contDiffOn_const isOpen_univ
    g.hasCompactSupport.isCompact.neg
    (quadraticParametricKernel_eq_zero_outside g)
    (locallyIntegrable_const (1 : ℂ))
    (quadraticParametricKernel_contDiff g).contDiffOn

private theorem quadraticSmoothRepresentative_eq_autocorrelation
    (g : BombieriTest) (x : ℝ) :
    quadraticSmoothRepresentative g x =
      autocorrelation (g : ℝ → ℂ) x := by
  unfold quadraticSmoothRepresentative autocorrelation
  simp only [MeasureTheory.convolution_def, quadraticParametricKernel,
    ContinuousLinearMap.mul_apply', one_mul, zero_sub, neg_neg, neg_mul_neg]
  apply (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
  intro y hy
  have hynpos : ¬0 < y := by simpa using hy
  have hnot : y ∉ tsupport g := by
    intro h
    exact hynpos (by simpa [positiveHalfLine] using g.tsupport_subset h)
  have hzero : g y = 0 := by
    by_contra hne
    exact hnot (subset_tsupport g (Function.mem_support.mpr hne))
  simp [hzero]

/-- The multiplicative autocorrelation of a Bombieri test is globally smooth. -/
theorem bombieri_autocorrelation_contDiff (g : BombieriTest) :
    ContDiff ℝ ∞ (autocorrelation (g : ℝ → ℂ)) := by
  rw [show autocorrelation (g : ℝ → ℂ) = quadraticSmoothRepresentative g by
    funext x
    exact (quadraticSmoothRepresentative_eq_autocorrelation g x).symm]
  exact quadraticSmoothRepresentative_contDiff g

/-- The multiplicative autocorrelation has compact support. -/
theorem bombieri_autocorrelation_hasCompactSupport (g : BombieriTest) :
    HasCompactSupport (autocorrelation (g : ℝ → ℂ)) :=
  HasCompactSupport.intro (quadraticRatioSet_isCompact g)
    fun _x hx ↦ autocorrelation_eq_zero_of_not_mem_ratio g hx

/-- The autocorrelation's topological support remains in `(0,∞)`. -/
theorem bombieri_autocorrelation_tsupport_subset (g : BombieriTest) :
    tsupport (autocorrelation (g : ℝ → ℂ)) ⊆ Ioi 0 := by
  have hsupp : Function.support (autocorrelation (g : ℝ → ℂ)) ⊆
      quadraticRatioSet g := by
    intro x hx
    by_contra hratio
    exact hx (autocorrelation_eq_zero_of_not_mem_ratio g hratio)
  have hclosure : closure (Function.support (autocorrelation (g : ℝ → ℂ))) ⊆
      quadraticRatioSet g :=
    (quadraticRatioSet_isCompact g).isClosed.closure_subset_iff.mpr hsupp
  exact hclosure.trans (quadraticRatioSet_subset_pos g)

/-- The autocorrelation of a Bombieri test bundled as another Bombieri test. -/
def bombieriQuadraticTest (g : BombieriTest) : BombieriTest :=
  TestFunction.mk
    (autocorrelation (g : ℝ → ℂ))
    (bombieri_autocorrelation_contDiff g)
    (bombieri_autocorrelation_hasCompactSupport g)
    (by simpa [positiveHalfLine] using
      bombieri_autocorrelation_tsupport_subset g)

@[simp]
theorem bombieriQuadraticTest_apply (g : BombieriTest) (x : ℝ) :
    bombieriQuadraticTest g x = autocorrelation (g : ℝ → ℂ) x := rfl

/-- At one, the quadratic test is the integral of the squared norm of `g`. -/
theorem bombieriQuadraticTest_apply_one (g : BombieriTest) :
    bombieriQuadraticTest g 1 =
      ∫ y : ℝ in Ioi 0, (Complex.normSq (g y) : ℂ) := by
  rw [bombieriQuadraticTest_apply, autocorrelation]
  apply integral_congr_ae
  filter_upwards with y
  simp only [one_mul, Complex.normSq_eq_conj_mul_self]
  ring

/-- A nonzero Bombieri test has a nonzero quadratic autocorrelation. -/
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
    exact g.hasCompactSupport.comp_left (by simp)
  have hnonneg : 0 ≤ h := fun y ↦ Complex.normSq_nonneg (g y)
  have hxne : h x ≠ 0 := Complex.normSq_eq_zero.not.mpr hx
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

/-- Unconditional closure of Bombieri tests under the quadratic convolution. -/
def bombieriQuadraticTestData (g : BombieriTest) : QuadraticTestData g where
  test := bombieriQuadraticTest g
  convolution_eq := fun x ↦ by
    rw [bombieriQuadraticTest_apply]
    exact (convolution_transposeConjugate_eq_autocorrelation
      (g : ℝ → ℂ) x).symm

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
