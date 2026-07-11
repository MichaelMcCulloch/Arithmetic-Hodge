import ArithmeticHodge.Analysis.FourierTransform

open MeasureTheory Real Complex

namespace ArithmeticHodge.Analysis

/-- The transform-side explicit formula required by Weil's positivity
criterion in the additive logarithmic convention used by `fourierCos`. -/
def FourierSideWeilExplicit : Prop :=
  ∀ (h : ℝ → ℝ), Continuous h →
    (∀ x : ℝ, ‖h x‖ ≤ 1 / (1 + x ^ 2)) →
    RiemannHypothesis →
    ∃ zeros : ℕ → ℝ,
      (∀ n, ∃ ρ : NontrivialZetaZero, zeros n = ρ.val.im) ∧
      Summable (fun n ↦ fourierCos h (zeros n)) ∧
      ∑' n, fourierCos h (zeros n) =
        weilFunctionalFull h (fourierCos h)

/-- With the spectral transform on the correct side, Fourier positivity of
autocorrelations proves the RH-to-Weil-positivity implication directly. -/
theorem rh_implies_weil_positivity_from_fourier_side
    (hexplicit : FourierSideWeilExplicit) :
    RiemannHypothesis → WeilPositivity := by
  intro hRH f hf_auto hf_cont hf_decay
  obtain ⟨g, hg, hg_sq, hf⟩ := hf_auto
  obtain ⟨zeros, _hzeros, _hsumm, hexpl⟩ :=
    hexplicit f hf_cont hf_decay hRH
  rw [← hexpl]
  exact tsum_nonneg fun n ↦
    fourierCos_autocorrelation_nonneg g hg hg_sq f hf (zeros n)

#print axioms rh_implies_weil_positivity_from_fourier_side

end ArithmeticHodge.Analysis
