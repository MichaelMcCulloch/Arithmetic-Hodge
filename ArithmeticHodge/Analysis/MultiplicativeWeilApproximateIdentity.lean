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

open Complex Filter MeasureTheory Real Set TopologicalSpace Topology
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

/-- Smooth nonnegative multiplicative bumps near one can be normalized to
have ordinary Lebesgue mass one. -/
theorem exists_bombieri_bump_unit_mass
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ eta : BombieriTest,
      tsupport (eta : ℝ → ℂ) ⊆ Ioo (Real.exp (-epsilon)) (Real.exp epsilon) ∧
      (∀ x, 0 ≤ (eta x).re ∧ (eta x).im = 0) ∧
      (∫ x : ℝ, (eta x).re) = 1 := by
  obtain ⟨eta0, hetaOne, hetaSupport, hetaReal⟩ :=
    exists_bombieri_bump_log_near_one epsilon hepsilon
  let mass : ℝ := ∫ x : ℝ, (eta0 x).re
  have hcont : Continuous (fun x : ℝ ↦ (eta0 x).re) := by
    exact Complex.continuous_re.comp eta0.contDiff.continuous
  have hcompact : HasCompactSupport (fun x : ℝ ↦ (eta0 x).re) := by
    change HasCompactSupport (Complex.reCLM ∘ (eta0 : ℝ → ℂ))
    exact eta0.hasCompactSupport.comp_left rfl
  have hnonneg : 0 ≤ fun x : ℝ ↦ (eta0 x).re :=
    fun x ↦ (hetaReal x).1
  have hmass : 0 < mass := by
    apply hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero
      hcompact hnonneg
    change (eta0 1).re ≠ 0
    rw [hetaOne]
    norm_num
  let eta : BombieriTest := (((mass⁻¹ : ℝ) : ℂ)) • eta0
  refine ⟨eta, ?_, ?_, ?_⟩
  · change tsupport (fun x : ℝ ↦ (((mass⁻¹ : ℝ) : ℂ)) * eta0 x) ⊆ _
    have hsupport := tsupport_smul_subset_right
      (fun _x : ℝ ↦ (((mass⁻¹ : ℝ) : ℂ))) (eta0 : ℝ → ℂ)
    simpa only [smul_eq_mul] using hsupport.trans hetaSupport
  · intro x
    have hx := hetaReal x
    constructor
    · change 0 ≤ ((((mass⁻¹ : ℝ) : ℂ) * eta0 x).re)
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      exact mul_nonneg (inv_nonneg.mpr hmass.le) hx.1
    · change ((((mass⁻¹ : ℝ) : ℂ) * eta0 x).im) = 0
      simp [hx.2.2]
  · change (∫ x : ℝ, ((((mass⁻¹ : ℝ) : ℂ) * eta0 x).re)) = 1
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, MeasureTheory.integral_const_mul]
    change mass⁻¹ * mass = 1
    exact inv_mul_cancel₀ hmass.ne'

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
