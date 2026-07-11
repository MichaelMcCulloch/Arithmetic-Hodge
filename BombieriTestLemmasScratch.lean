import ArithmeticHodge.Analysis.MultiplicativeWeil
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ContDiff Distributions SchwartzMap

namespace ArithmeticHodge.Analysis.MultiplicativeWeil.BombieriTestLemmasScratch

noncomputable section

/-- The natural domain for Bombieri's compactly supported multiplicative tests. -/
def positiveHalfLine : Opens ℝ := ⟨Ioi 0, isOpen_Ioi⟩

/-- Smooth complex-valued functions compactly supported in `(0, ∞)`. -/
abbrev BombieriTest := TestFunction positiveHalfLine ℂ ⊤

/-- Compact support inside `(0, ∞)` makes the Mellin integral converge at every parameter. -/
theorem BombieriTest.mellinConvergent (f : BombieriTest) (s : ℂ) :
    MellinConvergent (f : ℝ → ℂ) s := by
  let F : ℝ → ℂ := fun x ↦ (x : ℂ) ^ (s - 1) * f x
  have hF_cont : ContinuousOn F (tsupport f) := by
    intro x hx
    have hx_pos : 0 < x := f.tsupport_subset hx
    exact ((Complex.continuousAt_ofReal_cpow_const x (s - 1)
      (Or.inr hx_pos.ne')).mul f.contDiff.continuous.continuousAt).continuousWithinAt
  have hF_integrableOn : IntegrableOn F (tsupport f) :=
    hF_cont.integrableOn_compact f.hasCompactSupport
  have hF_support : Function.support F ⊆ tsupport f := by
    intro x hx
    apply subset_tsupport f
    apply Function.mem_support.mpr
    intro hfx
    apply hx
    simp [F, hfx]
  have hF_integrable : Integrable F :=
    (integrableOn_iff_integrable_of_support_subset hF_support).mp hF_integrableOn
  change IntegrableOn F (Ioi 0)
  exact hF_integrable.integrableOn

/-- Pull a multiplicative test to the additive real line with a Mellin weight. -/
def logarithmicPullback (σ : ℝ) (f : BombieriTest) (u : ℝ) : ℂ :=
  (Real.exp (-σ * u) : ℂ) * f (Real.exp (-u))

private theorem comp_exp_neg_hasCompactSupport (f : BombieriTest) :
    HasCompactSupport (fun u : ℝ ↦ f (Real.exp (-u))) := by
  let K : Set ℝ := (fun x : ℝ ↦ -Real.log x) '' tsupport f
  have hlog : ContinuousOn (fun x : ℝ ↦ -Real.log x) (tsupport f) := by
    exact Real.continuousOn_log.neg.mono fun x hx ↦ by
      exact (f.tsupport_subset hx).ne'
  have hK : IsCompact K := f.hasCompactSupport.image_of_continuousOn hlog
  refine HasCompactSupport.intro hK ?_
  intro u hu
  by_contra hne
  apply hu
  refine ⟨Real.exp (-u), ?_, ?_⟩
  · exact subset_tsupport f (Function.mem_support.mpr hne)
  · simp

/-- Every logarithmic pullback of a Bombieri test is compactly supported. -/
theorem BombieriTest.logarithmicPullback_hasCompactSupport
    (f : BombieriTest) (σ : ℝ) :
    HasCompactSupport (logarithmicPullback σ f) := by
  have hcore := comp_exp_neg_hasCompactSupport f
  simpa only [logarithmicPullback, Pi.mul_apply] using
    hcore.mul_left (f := fun u : ℝ ↦ (Real.exp (-σ * u) : ℂ))

/-- The logarithmic pullback remains smooth. -/
theorem BombieriTest.logarithmicPullback_contDiff
    (f : BombieriTest) (σ : ℝ) :
    ContDiff ℝ ∞ (logarithmicPullback σ f) := by
  unfold logarithmicPullback
  have hweightReal : ContDiff ℝ ∞ (fun u : ℝ ↦ Real.exp (-σ * u)) := by
    fun_prop
  have hweight : ContDiff ℝ ∞ (fun u : ℝ ↦ (Real.exp (-σ * u) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hweightReal
  have hargument : ContDiff ℝ ∞ (fun u : ℝ ↦ Real.exp (-u)) := by
    fun_prop
  exact hweight.mul (f.contDiff.comp hargument)

/-- The logarithmic pullback, bundled as a Schwartz function. -/
def BombieriTest.logarithmicPullbackSchwartz
    (f : BombieriTest) (σ : ℝ) : SchwartzMap ℝ ℂ :=
  (f.logarithmicPullback_hasCompactSupport σ).toSchwartzMap
    (f.logarithmicPullback_contDiff σ)

@[simp]
theorem BombieriTest.logarithmicPullbackSchwartz_apply
    (f : BombieriTest) (σ u : ℝ) :
    f.logarithmicPullbackSchwartz σ u = logarithmicPullback σ f u := rfl

#print axioms BombieriTest.mellinConvergent
#print axioms BombieriTest.logarithmicPullback_hasCompactSupport
#print axioms BombieriTest.logarithmicPullback_contDiff
#print axioms BombieriTest.logarithmicPullbackSchwartz_apply

end

end ArithmeticHodge.Analysis.MultiplicativeWeil.BombieriTestLemmasScratch
