import ArithmeticHodge.Analysis.MultiplicativeWeil
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Smooth multiplicative bumps near one

Every positive neighborhood of the multiplicative identity contains the
support of a real-valued nonnegative `BombieriTest` which equals one at the
identity.  These bumps are the starting point for the smooth approximate
identity used to regularize Li's cutoff kernels.
-/

set_option autoImplicit false

open Complex Filter Real Set TopologicalSpace Topology
open scoped ContDiff Distributions

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- A positive neighborhood of one contains a real-valued nonnegative smooth
Bombieri bump which is one at the identity. -/
theorem exists_bombieri_bump
    (U : Set ℝ) (hU : U ∈ 𝓝 (1 : ℝ)) (hUpos : U ⊆ Ioi 0) :
    ∃ eta : BombieriTest,
      eta 1 = 1 ∧ tsupport (eta : ℝ → ℂ) ⊆ U ∧
        ∀ x, 0 ≤ (eta x).re ∧ (eta x).re ≤ 1 ∧ (eta x).im = 0 := by
  obtain ⟨phi, hphiSupport, hphiCompact, hphiSmooth, hphiRange, hphiOne⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) hU
  have hsmooth : ContDiff ℝ ∞ (fun x : ℝ ↦ (phi x : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp hphiSmooth
  have hcompact : HasCompactSupport (fun x : ℝ ↦ (phi x : ℂ)) := by
    change HasCompactSupport (Complex.ofRealCLM ∘ phi)
    exact hphiCompact.comp_left rfl
  have htsupport : tsupport (fun x : ℝ ↦ (phi x : ℂ)) = tsupport phi := by
    have hsupport : Function.support (fun x : ℝ ↦ (phi x : ℂ)) =
        Function.support phi := by
      ext x
      simp only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero]
    unfold tsupport
    rw [hsupport]
  let eta : BombieriTest := TestFunction.mk
    (fun x : ℝ ↦ (phi x : ℂ)) hsmooth hcompact (by
      rw [htsupport]
      simpa only [positiveHalfLine] using hphiSupport.trans hUpos)
  refine ⟨eta, ?_, ?_, ?_⟩
  · change (phi 1 : ℂ) = 1
    rw [hphiOne]
    norm_num
  · change tsupport (fun x : ℝ ↦ (phi x : ℂ)) ⊆ U
    rw [htsupport]
    exact hphiSupport
  · intro x
    have hx := hphiRange (Set.mem_range_self x)
    change 0 ≤ ((phi x : ℂ).re) ∧ ((phi x : ℂ).re) ≤ 1 ∧
      (phi x : ℂ).im = 0
    simpa using hx

/-- For every positive logarithmic radius there is a smooth Bombieri bump
supported in the multiplicative interval around one. -/
theorem exists_bombieri_bump_log_near_one
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ eta : BombieriTest,
      eta 1 = 1 ∧
      tsupport (eta : ℝ → ℂ) ⊆ Ioo (Real.exp (-epsilon)) (Real.exp epsilon) ∧
      ∀ x, 0 ≤ (eta x).re ∧ (eta x).re ≤ 1 ∧ (eta x).im = 0 := by
  apply exists_bombieri_bump
  · exact Ioo_mem_nhds (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hepsilon))
      (Real.one_lt_exp_iff.mpr hepsilon)
  · intro x hx
    exact (Real.exp_pos (-epsilon)).trans hx.1

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
