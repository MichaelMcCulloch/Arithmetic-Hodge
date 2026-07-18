import ArithmeticHodge.Analysis.MultiplicativeWeilDirectedCorrelationPhysicalStructural
import Mathlib.Analysis.Calculus.ContDiff.Convolution

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ComplexConjugate ContDiff Convolution Distributions SchwartzMap

namespace ArithmeticHodge.Analysis.MultiplicativeWeilDirectedCorrelationSmoothStructural

noncomputable section

open MultiplicativeWeil

/-!
# Smoothness of the directed multiplicative correlation

The directed correlation is represented as a fixed-support parametric additive
convolution.  This makes its global smoothness structural, rather than an
artifact of the logarithmic-coordinate formula valid only on the positive
half-line.  Its support is contained in the compact set of quotients of the
two input supports.
-/

/-- The compact set of possible quotients contributing to the directed
correlation. -/
def bombieriDirectedCorrelationRatioSet (f g : BombieriTest) : Set ℝ :=
  (fun p : ℝ × ℝ ↦ p.1 / p.2) '' (tsupport f ×ˢ tsupport g)

theorem bombieriDirectedCorrelationRatioSet_isCompact (f g : BombieriTest) :
    IsCompact (bombieriDirectedCorrelationRatioSet f g) := by
  apply (f.hasCompactSupport.isCompact.prod
    g.hasCompactSupport.isCompact).image_of_continuousOn
  exact continuousOn_fst.div continuousOn_snd fun p hp ↦
    (g.tsupport_subset hp.2).ne'

theorem bombieriDirectedCorrelationRatioSet_subset_pos (f g : BombieriTest) :
    bombieriDirectedCorrelationRatioSet f g ⊆ Ioi 0 := by
  rintro x ⟨p, hp, rfl⟩
  have hp1 : 0 < p.1 := by
    simpa [positiveHalfLine] using f.tsupport_subset hp.1
  have hp2 : 0 < p.2 := by
    simpa [positiveHalfLine] using g.tsupport_subset hp.2
  exact div_pos hp1 hp2

private theorem bombieriDirectedCorrelation_eq_zero_of_not_mem_ratioSet
    (f g : BombieriTest) {x : ℝ}
    (hx : x ∉ bombieriDirectedCorrelationRatioSet f g) :
    bombieriDirectedCorrelation f g x = 0 := by
  unfold bombieriDirectedCorrelation
  calc
    (∫ y : ℝ in Ioi 0, f (x * y) * starRingEnd ℂ (g y)) =
        ∫ _y : ℝ in Ioi 0, (0 : ℂ) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      by_cases hgy : g y = 0
      · simp [hgy]
      by_cases hfxy : f (x * y) = 0
      · simp [hfxy]
      exfalso
      apply hx
      have hypos : 0 < y := by simpa using hy
      refine ⟨(x * y, y),
        ⟨subset_tsupport f (Function.mem_support.mpr hfxy),
          subset_tsupport g (Function.mem_support.mpr hgy)⟩, ?_⟩
      exact (div_eq_iff hypos.ne').2 (by ring)
    _ = 0 := by simp

private def directedCorrelationParametricKernel
    (f g : BombieriTest) (p y : ℝ) : ℂ :=
  f (-p * y) * starRingEnd ℂ (g (-y))

private theorem directedCorrelationParametricKernel_contDiff
    (f g : BombieriTest) :
    ContDiff ℝ ∞
      (fun q : ℝ × ℝ ↦ directedCorrelationParametricKernel f g q.1 q.2) := by
  unfold directedCorrelationParametricKernel
  have harg1 : ContDiff ℝ ∞ (fun q : ℝ × ℝ ↦ -q.1 * q.2) := by
    fun_prop
  have harg2 : ContDiff ℝ ∞ (fun q : ℝ × ℝ ↦ -q.2) := by
    fun_prop
  have hf : ContDiff ℝ ∞ (fun q : ℝ × ℝ ↦ f (-q.1 * q.2)) :=
    f.contDiff.comp harg1
  have hg : ContDiff ℝ ∞ (fun q : ℝ × ℝ ↦ g (-q.2)) :=
    g.contDiff.comp harg2
  exact hf.mul (Complex.conjCLE.contDiff.comp hg)

private theorem directedCorrelationParametricKernel_eq_zero_outside
    (f g : BombieriTest) (p y : ℝ) (_hp : p ∈ (univ : Set ℝ))
    (hy : y ∉ -(tsupport g)) :
    directedCorrelationParametricKernel f g p y = 0 := by
  have hneg : -y ∉ tsupport g := by
    intro h
    exact hy (Set.mem_neg.2 h)
  have hzero : g (-y) = 0 := by
    by_contra hne
    exact hneg (subset_tsupport g (Function.mem_support.mpr hne))
  simp [directedCorrelationParametricKernel, hzero]

private def directedCorrelationSmoothRepresentative
    (f g : BombieriTest) (x : ℝ) : ℂ :=
  ((fun _y : ℝ ↦ (1 : ℂ)) ⋆[
      ContinuousLinearMap.mul ℝ ℂ, volume]
    directedCorrelationParametricKernel f g x) 0

private theorem directedCorrelationSmoothRepresentative_contDiff
    (f g : BombieriTest) :
    ContDiff ℝ ∞ (directedCorrelationSmoothRepresentative f g) := by
  rw [← contDiffOn_univ]
  exact contDiffOn_convolution_right_with_param_comp
    (ContinuousLinearMap.mul ℝ ℂ)
    (v := fun _x : ℝ ↦ (0 : ℝ)) contDiffOn_const isOpen_univ
    g.hasCompactSupport.isCompact.neg
    (directedCorrelationParametricKernel_eq_zero_outside f g)
    (locallyIntegrable_const (1 : ℂ))
    (directedCorrelationParametricKernel_contDiff f g).contDiffOn

private theorem directedCorrelationSmoothRepresentative_eq
    (f g : BombieriTest) (x : ℝ) :
    directedCorrelationSmoothRepresentative f g x =
      bombieriDirectedCorrelation f g x := by
  unfold directedCorrelationSmoothRepresentative bombieriDirectedCorrelation
  simp only [MeasureTheory.convolution_def,
    directedCorrelationParametricKernel,
    ContinuousLinearMap.mul_apply', one_mul, zero_sub, neg_neg, neg_mul_neg]
  apply (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
  intro y hy
  have hynpos : ¬ 0 < y := by simpa using hy
  have hnot : y ∉ tsupport g := by
    intro h
    exact hynpos (by simpa [positiveHalfLine] using g.tsupport_subset h)
  have hzero : g y = 0 := by
    by_contra hne
    exact hnot (subset_tsupport g (Function.mem_support.mpr hne))
  simp [hzero]

/-- The directed multiplicative correlation of two Bombieri tests is globally
smooth.  This is stronger than the first derivative needed for Abel
summation. -/
theorem bombieriDirectedCorrelation_contDiff (f g : BombieriTest) :
    ContDiff ℝ ∞ (bombieriDirectedCorrelation f g) := by
  rw [show bombieriDirectedCorrelation f g =
      directedCorrelationSmoothRepresentative f g by
    funext x
    exact (directedCorrelationSmoothRepresentative_eq f g x).symm]
  exact directedCorrelationSmoothRepresentative_contDiff f g

/-- The support of the directed correlation is contained in the compact
quotient image of the two input supports. -/
theorem bombieriDirectedCorrelation_tsupport_subset_ratioSet
    (f g : BombieriTest) :
    tsupport (bombieriDirectedCorrelation f g) ⊆
      bombieriDirectedCorrelationRatioSet f g := by
  have hsupp : Function.support (bombieriDirectedCorrelation f g) ⊆
      bombieriDirectedCorrelationRatioSet f g := by
    intro x hx
    by_contra hratio
    exact hx (bombieriDirectedCorrelation_eq_zero_of_not_mem_ratioSet
      f g hratio)
  exact (bombieriDirectedCorrelationRatioSet_isCompact f g).isClosed
    |>.closure_subset_iff.mpr hsupp

/-- The directed multiplicative correlation has compact support. -/
theorem bombieriDirectedCorrelation_hasCompactSupport (f g : BombieriTest) :
    HasCompactSupport (bombieriDirectedCorrelation f g) :=
  HasCompactSupport.intro
    (bombieriDirectedCorrelationRatioSet_isCompact f g)
    fun _x hx ↦ bombieriDirectedCorrelation_eq_zero_of_not_mem_ratioSet f g hx

/-- The conjugated physical directed correlation is globally smooth. -/
theorem star_bombieriDirectedCorrelation_contDiff (f g : BombieriTest) :
    ContDiff ℝ ∞
      (fun x : ℝ ↦ starRingEnd ℂ (bombieriDirectedCorrelation f g x)) := by
  exact Complex.conjCLE.contDiff.comp (bombieriDirectedCorrelation_contDiff f g)

/-- First-order regularity in the exact form used by Abel summation. -/
theorem star_bombieriDirectedCorrelation_contDiff_one (f g : BombieriTest) :
    ContDiff ℝ 1
      (fun x : ℝ ↦ starRingEnd ℂ (bombieriDirectedCorrelation f g x)) := by
  exact (star_bombieriDirectedCorrelation_contDiff f g).of_le (by simp)

/-- The conjugated physical directed correlation has compact support. -/
theorem star_bombieriDirectedCorrelation_hasCompactSupport
    (f g : BombieriTest) :
    HasCompactSupport
      (fun x : ℝ ↦ starRingEnd ℂ (bombieriDirectedCorrelation f g x)) := by
  exact (bombieriDirectedCorrelation_hasCompactSupport f g).comp_left (by simp)

/-- The derivative of the conjugated physical correlation is integrable. -/
theorem deriv_star_bombieriDirectedCorrelation_integrable
    (f g : BombieriTest) :
    Integrable
      (deriv fun x : ℝ ↦
        starRingEnd ℂ (bombieriDirectedCorrelation f g x)) := by
  exact (star_bombieriDirectedCorrelation_contDiff f g).continuous_deriv (by simp)
    |>.integrable_of_hasCompactSupport
      (star_bombieriDirectedCorrelation_hasCompactSupport f g).deriv

end

end ArithmeticHodge.Analysis.MultiplicativeWeilDirectedCorrelationSmoothStructural
