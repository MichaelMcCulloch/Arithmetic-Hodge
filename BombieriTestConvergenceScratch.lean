import ArithmeticHodge.Analysis.MultiplicativeWeil

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

theorem mellinConvergent_of_contDiff_compact_tsupport_pos_scratch
    (f : ℝ → ℂ) (hf : ContDiff ℝ ⊤ f) (hcompact : HasCompactSupport f)
    (hpositive : tsupport f ⊆ Ioi 0) (s : ℂ) :
    MellinConvergent f s := by
  let F : ℝ → ℂ := fun x ↦ (x : ℂ) ^ (s - 1) * f x
  have hF_cont : ContinuousOn F (tsupport f) := by
    intro x hx
    have hx_pos : 0 < x := hpositive hx
    exact ((Complex.continuousAt_ofReal_cpow_const x (s - 1)
      (Or.inr hx_pos.ne')).mul hf.continuous.continuousAt).continuousWithinAt
  have hF_integrableOn : IntegrableOn F (tsupport f) :=
    hF_cont.integrableOn_compact hcompact
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

#print axioms mellinConvergent_of_contDiff_compact_tsupport_pos_scratch

end ArithmeticHodge.Analysis.MultiplicativeWeil
