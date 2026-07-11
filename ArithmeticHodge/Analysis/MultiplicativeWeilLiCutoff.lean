import ArithmeticHodge.Analysis.MultiplicativeWeilLiKernel
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Truncated Bombieri--Li kernels

Cutting the Li kernel off at a positive lower endpoint makes it compactly
supported away from zero.  Dominated convergence shows that, as the endpoint
tends to zero, its Mellin transform recovers `liFunction` throughout the
right half-plane.
-/

set_option autoImplicit false

open Complex Filter MeasureTheory Real Set Topology

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- Bombieri's Li kernel with the singular endpoint truncated at `epsilon`. -/
def liKernelCutoff (n : ℕ) (epsilon x : ℝ) : ℂ :=
  if x ∈ Ioo epsilon 1 then liPolynomial n (Real.log x) else 0

private theorem liKernelCutoff_integrand_eq_indicator
    (n : ℕ) (s : ℂ) {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    (fun x : ℝ ↦ (x : ℂ) ^ (s - 1) * liKernelCutoff n epsilon x) =
      (Ioi epsilon).indicator
        (fun x : ℝ ↦ (x : ℂ) ^ (s - 1) * liKernel n x) := by
  funext x
  by_cases hx : x ∈ Ioi epsilon
  · rw [Set.indicator_of_mem hx]
    have hxpos : 0 < x := hepsilon.trans_lt hx
    by_cases hx1 : x < 1
    · have hcut : x ∈ Ioo epsilon 1 := ⟨hx, hx1⟩
      have hfull : x ∈ Ioo (0 : ℝ) 1 := ⟨hxpos, hx1⟩
      simp only [liKernelCutoff, liKernel, if_pos hcut, if_pos hfull]
    · have hx1' : ¬x ∈ Ioo epsilon 1 := fun h ↦ hx1 h.2
      have hx01 : ¬x ∈ Ioo (0 : ℝ) 1 := fun h ↦ hx1 h.2
      simp [liKernelCutoff, liKernel, hx1', hx01]
  · rw [Set.indicator_of_notMem hx]
    have hcut : ¬x ∈ Ioo epsilon 1 := fun h ↦ hx h.1
    simp [liKernelCutoff, hcut]

/-- For any positive cutoffs tending to zero, the truncated Li Mellin
transform converges pointwise to Li's rational function. -/
theorem mellin_liKernelCutoff_tendsto_liFunction
    (n : ℕ) (s : ℂ) (hs : 0 < s.re)
    (epsilon : ℕ → ℝ) (hepsilon : ∀ k, 0 ≤ epsilon k)
    (hepsilon0 : Tendsto epsilon atTop (𝓝 0)) :
    Tendsto (fun k ↦ mellin (liKernelCutoff n (epsilon k)) s)
      atTop (𝓝 (liFunction n s)) := by
  let f : ℝ → ℂ := fun x ↦ (x : ℂ) ^ (s - 1) * liKernel n x
  let F : ℕ → ℝ → ℂ := fun k ↦ (Ioi (epsilon k)).indicator f
  have hfInt : Integrable f (volume.restrict (Ioi 0)) := by
    simpa only [f, MellinConvergent, smul_eq_mul] using
      liKernel_mellinConvergent n s hs
  have hFmeas : ∀ k, AEStronglyMeasurable (F k)
      (volume.restrict (Ioi 0)) := by
    intro k
    exact hfInt.aestronglyMeasurable.indicator measurableSet_Ioi
  have hbound : ∀ k, ∀ᵐ x ∂(volume.restrict (Ioi 0)),
      ‖F k x‖ ≤ ‖f x‖ := by
    intro k
    filter_upwards [] with x
    by_cases hx : x ∈ Ioi (epsilon k)
    · simp [F, hx]
    · simp [F, hx, norm_nonneg]
  have hlim : ∀ᵐ x ∂(volume.restrict (Ioi 0)),
      Tendsto (fun k ↦ F k x) atTop (𝓝 (f x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hevent : ∀ᶠ k in atTop, epsilon k < x :=
      hepsilon0.eventually (Iio_mem_nhds hx)
    apply tendsto_const_nhds.congr'
    filter_upwards [hevent] with k hk
    simp [F, hk]
  have hdct : Tendsto
      (fun k ↦ ∫ x : ℝ, F k x ∂(volume.restrict (Ioi 0)))
      atTop (𝓝 (∫ x : ℝ, f x ∂(volume.restrict (Ioi 0)))) :=
    tendsto_integral_of_dominated_convergence
      (fun x ↦ ‖f x‖) hFmeas hfInt.norm hbound hlim
  have hrewrite (k : ℕ) :
      (∫ x : ℝ, F k x ∂(volume.restrict (Ioi 0))) =
        mellin (liKernelCutoff n (epsilon k)) s := by
    rw [show F k = fun x : ℝ ↦
        (x : ℂ) ^ (s - 1) * liKernelCutoff n (epsilon k) x by
      simpa only [F, f] using
        (liKernelCutoff_integrand_eq_indicator
          n s (hepsilon k)).symm]
    rfl
  have hfull : (∫ x : ℝ, f x ∂(volume.restrict (Ioi 0))) =
      liFunction n s := by
    change mellin (liKernel n) s = liFunction n s
    exact mellin_liKernel n s hs
  rw [hfull] at hdct
  exact hdct.congr' (Eventually.of_forall fun k ↦ hrewrite k)

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
