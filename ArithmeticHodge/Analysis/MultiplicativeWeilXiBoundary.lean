import ArithmeticHodge.Analysis.Contour.RectangleMeromorphicGoursat
import ArithmeticHodge.Analysis.ZetaProduct

/-!
# Rewriting the xi logarithmic derivative on rectangular contours

After removing zeta's pole at one, its exceptional zero set is codiscrete.
Thus the exact xi/zeta/gamma logarithmic-derivative identity transfers to raw
rectangle integrals even when the enclosed region contains zeros.
-/

set_option autoImplicit false

open Complex Filter Set Topology
open scoped Interval Real

namespace ArithmeticHodge.Analysis

noncomputable section

private noncomputable def zetaPoleRemoved (s : ℂ) : ℂ :=
  Function.update (fun z : ℂ ↦ (z - 1) * riemannZeta z) 1 1 s

private theorem zetaPoleRemoved_differentiableAt_of_ne
    {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ zetaPoleRemoved s := by
  apply DifferentiableAt.congr_of_eventuallyEq
  · exact (differentiableAt_id.sub_const 1).mul
      (differentiableAt_riemannZeta hs)
  · filter_upwards [eventually_ne_nhds hs] with t ht
    simp only [zetaPoleRemoved, Function.update_of_ne ht, Pi.mul_apply, id_eq]

private theorem zetaPoleRemoved_differentiable :
    Differentiable ℂ zetaPoleRemoved := by
  intro s
  rcases ne_or_eq s 1 with hs | rfl
  · exact zetaPoleRemoved_differentiableAt_of_ne hs
  · refine
      (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact zetaPoleRemoved_differentiableAt_of_ne ht
    · unfold zetaPoleRemoved
      simpa only [continuousAt_update_same] using riemannZeta_residue_one

private theorem zetaPoleRemoved_two_ne_zero :
    zetaPoleRemoved 2 ≠ 0 := by
  rw [zetaPoleRemoved, Function.update_of_ne (by norm_num : (2 : ℂ) ≠ 1)]
  norm_num only [sub_self, OfNat.ofNat_ne_zero, not_false_eq_true, one_mul]
  exact riemannZeta_ne_zero_of_one_le_re (by norm_num)

private theorem eventually_zeta_safe :
    ∀ᶠ s in codiscrete ℂ,
      s ≠ 0 ∧ s ≠ 1 ∧ riemannZeta s ≠ 0 := by
  have hGanalytic : AnalyticOnNhd ℂ zetaPoleRemoved Set.univ :=
    zetaPoleRemoved_differentiable.differentiableOn.analyticOnNhd isOpen_univ
  have hG : zetaPoleRemoved ⁻¹' {0}ᶜ ∈ codiscrete ℂ :=
    hGanalytic.preimage_zero_mem_codiscrete zetaPoleRemoved_two_ne_zero
  have hzero : (fun s : ℂ ↦ s) ⁻¹' {0}ᶜ ∈ codiscrete ℂ :=
    analyticOnNhd_id.preimage_zero_mem_codiscrete
      (x := (1 : ℂ)) (by norm_num)
  have hone : (fun s : ℂ ↦ s - 1) ⁻¹' {0}ᶜ ∈ codiscrete ℂ :=
    (analyticOnNhd_id.sub analyticOnNhd_const).preimage_zero_mem_codiscrete
      (x := (0 : ℂ)) (by norm_num)
  filter_upwards [hG, hzero, hone] with s hsG hs0 hs1
  have hsG' : zetaPoleRemoved s ≠ 0 := by simpa using hsG
  have hs0' : s ≠ 0 := by simpa using hs0
  have hs1' : s ≠ 1 := by simpa [sub_ne_zero] using hs1
  refine ⟨hs0', hs1', ?_⟩
  intro hzs
  apply hsG'
  simp [zetaPoleRemoved, hs1', hzs]

private theorem xi_logDeriv_eq_zeta_gamma_polar_codiscrete :
    (fun s : ℂ ↦ logDeriv xiFunction s) =ᶠ[codiscrete ℂ]
      (fun s : ℂ ↦
        deriv riemannZeta s / riemannZeta s +
          1 / s + 1 / (s - 1) - (Real.log Real.pi : ℂ) / 2 +
            Complex.digamma (s / 2) / 2) := by
  filter_upwards [eventually_zeta_safe] with s hs
  have h := zeta_logDeriv_from_xi_explicit s hs.2.1 hs.1 hs.2.2
  rw [logDeriv_apply, h]
  ring

/-- The weighted raw rectangle integral of `xi'/xi` equals the integral of
the exact zeta, polar, and real-gamma logarithmic-derivative decomposition. -/
theorem rectIntegral_weighted_xi_logDeriv_eq_zeta_gamma_polar
    (H : ℂ → ℂ) (z w : ℂ) :
    rectIntegral (fun s ↦ H s * logDeriv xiFunction s) z w =
      rectIntegral
        (fun s ↦ H s *
          (deriv riemannZeta s / riemannZeta s +
            1 / s + 1 / (s - 1) - (Real.log Real.pi : ℂ) / 2 +
              Complex.digamma (s / 2) / 2)) z w := by
  apply rectIntegral_congr_codiscreteWithin
  have hglobal :
      (fun s : ℂ ↦ H s * logDeriv xiFunction s) =ᶠ[codiscrete ℂ]
        (fun s ↦ H s *
          (deriv riemannZeta s / riemannZeta s +
            1 / s + 1 / (s - 1) - (Real.log Real.pi : ℂ) / 2 +
              Complex.digamma (s / 2) / 2)) := by
    filter_upwards [xi_logDeriv_eq_zeta_gamma_polar_codiscrete] with s hs
    rw [hs]
  exact hglobal.filter_mono (by
    simpa only [codiscrete] using
      (Filter.codiscreteWithin.mono
        (Set.subset_univ
          ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))))

end

end ArithmeticHodge.Analysis
