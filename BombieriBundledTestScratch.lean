import ArithmeticHodge.Analysis.MultiplicativeWeil
import Mathlib.Analysis.Distribution.TestFunction

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped Distributions

namespace ArithmeticHodge.Analysis.MultiplicativeWeil.BundledScratch

def positiveHalfLine : Opens ℝ := ⟨Ioi 0, isOpen_Ioi⟩

abbrev BombieriTest := 𝓓(positiveHalfLine, ℂ)

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

structure TransposeData where
  toLinearMap : BombieriTest →ₗ[ℂ] BombieriTest
  apply_pos : ∀ (f : BombieriTest) {x : ℝ}, 0 < x →
    toLinearMap f x = transpose (f : ℝ → ℂ) x

structure QuadraticTestData (g : BombieriTest) where
  test : BombieriTest
  apply : ∀ x : ℝ, test x =
    convolution (g : ℝ → ℂ) (transposeConjugate (g : ℝ → ℂ)) x

#check BombieriTest.mellinConvergent
#check TransposeData.toLinearMap
#check QuadraticTestData.test
#print axioms BombieriTest.mellinConvergent

end ArithmeticHodge.Analysis.MultiplicativeWeil.BundledScratch
