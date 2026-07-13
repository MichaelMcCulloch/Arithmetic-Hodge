import ArithmeticHodge.Analysis.YoshidaClippedDomain
import Mathlib.Topology.Piecewise

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.YoshidaClippedEndpointContinuous

open ArithmeticHodge.Analysis

noncomputable section

/-- A clipped smooth profile whose two boundary traces vanish is globally
continuous after its built-in zero extension. -/
theorem continuous_yoshidaClippedSmooth_of_endpoints_zero
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a)
    (hneg : f (-a) = 0) (hpos : f a = 0) :
    Continuous (f : ℝ → ℂ) := by
  classical
  let s : Set ℝ := Icc (-a) a
  have hfrontier : ∀ x ∈ frontier s, (f : ℝ → ℂ) x = 0 := by
    intro x hx
    have hle : -a ≤ a := by linarith
    rw [show frontier s = {-a, a} by
      dsimp only [s]
      exact frontier_Icc hle] at hx
    rcases hx with hx | hx
    · simpa only [mem_singleton_iff] using hx ▸ hneg
    · simpa only [mem_singleton_iff] using hx ▸ hpos
  have hfOn : ContinuousOn (f : ℝ → ℂ) (closure s) := by
    rw [show closure s = s by
      exact (isClosed_Icc : IsClosed (Icc (-a) a)).closure_eq]
    exact f.property.1.continuousOn
  have hzeroOn : ContinuousOn (fun _ : ℝ ↦ (0 : ℂ)) (closure sᶜ) :=
    continuous_const.continuousOn
  have hpw : Continuous (s.piecewise (f : ℝ → ℂ) (fun _ ↦ 0)) :=
    continuous_piecewise hfrontier hfOn hzeroOn
  have heq : s.piecewise (f : ℝ → ℂ) (fun _ ↦ 0) = (f : ℝ → ℂ) := by
    funext x
    by_cases hx : x ∈ s
    · simp [Set.piecewise, hx]
    · simp only [Set.piecewise, hx, ↓reduceIte]
      exact (yoshidaClippedSmooth_eq_zero_outside f hx).symm
  rw [heq] at hpw
  exact hpw

end

end ArithmeticHodge.Analysis.YoshidaClippedEndpointContinuous
