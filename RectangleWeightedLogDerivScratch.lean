import ArithmeticHodge.Analysis.Contour.ArgumentPrinciple
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.DSlope

set_option autoImplicit false

open Filter Topology Complex Set

namespace ArithmeticHodge.Analysis.Contour

noncomputable section

/-- The weighted logarithmic derivative with all prescribed simple principal
parts removed. -/
def weightedLogDerivRemainder
    (F H : ℂ → ℂ) (S : Finset ℂ) (ord : ℂ → ℤ) (s : ℂ) : ℂ :=
  H s * logDeriv F s -
    ∑ ρ ∈ S, (ord ρ : ℂ) * H ρ * (s - ρ)⁻¹

private theorem analyticAt_dslope
    {H : ℂ → ℂ} {s : ℂ} (hH : AnalyticAt ℂ H s) :
    AnalyticAt ℂ (dslope H s) s := by
  obtain ⟨p, hp⟩ := hH
  exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩

/-- On a closed axis-parallel rectangle, subtracting the weighted principal
parts from `H · F'/F` removes every pole. -/
theorem weightedLogDerivRemainder_meromorphicOn_order_nonneg
    {re₀ re₁ im₀ im₁ : ℝ} {F H : ℂ → ℂ}
    (S : Finset ℂ) (ord : ℂ → ℤ)
    (hF : MeromorphicOn F (Icc re₀ re₁ ×ℂ Icc im₀ im₁))
    (hH : AnalyticOnNhd ℂ H (Icc re₀ re₁ ×ℂ Icc im₀ im₁))
    (hsupp : ∀ s ∈ Icc re₀ re₁ ×ℂ Icc im₀ im₁,
      meromorphicOrderAt F s ≠ 0 → s ∈ S)
    (hord : ∀ ρ ∈ S, meromorphicOrderAt F ρ = (ord ρ : WithTop ℤ)) :
    MeromorphicOn (weightedLogDerivRemainder F H S ord)
        (Icc re₀ re₁ ×ℂ Icc im₀ im₁) ∧
      ∀ s ∈ Icc re₀ re₁ ×ℂ Icc im₀ im₁,
        0 ≤ meromorphicOrderAt (weightedLogDerivRemainder F H S ord) s := by
  let R : Set ℂ := Icc re₀ re₁ ×ℂ Icc im₀ im₁
  have hP : MeromorphicOn
      (fun z : ℂ ↦ ∑ ρ ∈ S, (ord ρ : ℂ) * H ρ * (z - ρ)⁻¹) R := by
    refine MeromorphicOn.fun_sum fun ρ z _ ↦ ?_
    exact (MeromorphicAt.const ((ord ρ : ℂ) * H ρ) z).mul
      (((MeromorphicAt.id z).sub (MeromorphicAt.const ρ z)).inv)
  have hAmero : MeromorphicOn (weightedLogDerivRemainder F H S ord) R := by
    exact (hH.meromorphicOn.mul hF.logDeriv).sub hP
  refine ⟨hAmero, ?_⟩
  intro s hs
  by_cases hsS : s ∈ S
  · obtain ⟨g, hg_an, hg_ne, hg_germ⟩ :=
      logDeriv_eventuallyEq_principalPart (hF s hs) (hord s hsS)
    have hrest_an : AnalyticAt ℂ
        (fun w : ℂ ↦ ∑ ρ ∈ S.erase s,
          (ord ρ : ℂ) * H ρ * (w - ρ)⁻¹) s :=
      Finset.analyticAt_fun_sum _ fun ρ hρ ↦
        analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).inv
          (sub_ne_zero.2 (Ne.symm (Finset.ne_of_mem_erase hρ))))
    have hregular_an : AnalyticAt ℂ
        (fun w : ℂ ↦
          (ord s : ℂ) * dslope H s w + H w * logDeriv g w -
            ∑ ρ ∈ S.erase s, (ord ρ : ℂ) * H ρ * (w - ρ)⁻¹) s := by
      exact ((analyticAt_const.mul (analyticAt_dslope (hH s hs))).add
        ((hH s hs).mul (analyticAt_logDeriv_of_analyticAt hg_an hg_ne))).sub
          hrest_an
    have hAeq : weightedLogDerivRemainder F H S ord =ᶠ[𝓝[≠] s]
        fun w : ℂ ↦
          (ord s : ℂ) * dslope H s w + H w * logDeriv g w -
            ∑ ρ ∈ S.erase s, (ord ρ : ℂ) * H ρ * (w - ρ)⁻¹ := by
      filter_upwards [hg_germ, self_mem_nhdsWithin] with w hw hws
      have hne : w ≠ s := by
        simpa only [mem_compl_iff, mem_singleton_iff] using hws
      have hdslope : dslope H s w = (w - s)⁻¹ * (H w - H s) := by
        rw [dslope_of_ne _ hne, slope_def_module, smul_eq_mul]
      simp only [weightedLogDerivRemainder,
        ← Finset.add_sum_erase S
          (fun ρ ↦ (ord ρ : ℂ) * H ρ * (w - ρ)⁻¹) hsS]
      rw [hw, hdslope]
      ring
    rw [meromorphicOrderAt_congr hAeq]
    exact hregular_an.meromorphicOrderAt_nonneg
  · have hzero : meromorphicOrderAt F s = 0 := by
      by_contra hne
      exact hsS (hsupp s hs hne)
    obtain ⟨g, hg_an, hg_ne, hg_germ⟩ :=
      logDeriv_eventuallyEq_principalPart (hF s hs)
        (n := 0) (by simpa using hzero)
    have hP_an : AnalyticAt ℂ
        (fun w : ℂ ↦ ∑ ρ ∈ S,
          (ord ρ : ℂ) * H ρ * (w - ρ)⁻¹) s :=
      Finset.analyticAt_fun_sum _ fun ρ hρ ↦
        analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).inv
          (sub_ne_zero.2 (by
            intro h
            change s = ρ at h
            subst ρ
            exact hsS hρ)))
    have hregular_an : AnalyticAt ℂ
        (fun w : ℂ ↦ H w * logDeriv g w -
          ∑ ρ ∈ S, (ord ρ : ℂ) * H ρ * (w - ρ)⁻¹) s :=
      ((hH s hs).mul (analyticAt_logDeriv_of_analyticAt hg_an hg_ne)).sub hP_an
    have hAeq : weightedLogDerivRemainder F H S ord =ᶠ[𝓝[≠] s]
        fun w : ℂ ↦ H w * logDeriv g w -
          ∑ ρ ∈ S, (ord ρ : ℂ) * H ρ * (w - ρ)⁻¹ := by
      filter_upwards [hg_germ] with w hw
      simp only [weightedLogDerivRemainder, hw, Int.cast_zero, zero_mul, zero_add]
    rw [meromorphicOrderAt_congr hAeq]
    exact hregular_an.meromorphicOrderAt_nonneg

#print axioms weightedLogDerivRemainder_meromorphicOn_order_nonneg

end

end ArithmeticHodge.Analysis.Contour
