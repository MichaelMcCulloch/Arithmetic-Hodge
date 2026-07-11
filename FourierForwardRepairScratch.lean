import ArithmeticHodge.Analysis.WeilPositivity

open MeasureTheory Real

namespace ArithmeticHodge.Analysis

/-- A sound replacement for the legacy forward theorem.  The additional
assumption says exactly that the spectral side of the explicit formula is the
Fourier cosine transform, whose values are nonnegative on autocorrelations. -/
theorem rh_implies_weil_positivity_from_oriented_explicit_scratch
    (hexplicit : FourierOrientedWeilExplicit) :
    RiemannHypothesis → WeilPositivity := by
  intro hRH f hf hcont hdecay
  obtain ⟨zeros, _hsummable, hidentity⟩ :=
    hexplicit f hf hcont hdecay hRH
  rw [← hidentity]
  exact tsum_nonneg fun n => by
    obtain ⟨g, hg, hg_sq, hfg⟩ := hf
    exact fourierCos_autocorrelation_nonneg g hg hg_sq f hfg (zeros n)

/-- The missing bridge in the legacy proof is not merely absent from the API:
the claim that autocorrelations are pointwise nonnegative is false. -/
theorem not_all_autocorrelations_pointwise_nonnegative_scratch :
    ¬ ∀ (f : ℝ → ℝ), IsAutocorrelation f → ∀ x : ℝ, 0 ≤ f x := by
  intro hall
  obtain ⟨f, hf, hvalue⟩ := exists_autocorrelation_with_negative_value
  have hnonneg := hall f hf 1
  rw [hvalue] at hnonneg
  norm_num at hnonneg

#print axioms rh_implies_weil_positivity_from_oriented_explicit_scratch
#print axioms not_all_autocorrelations_pointwise_nonnegative_scratch
#print axioms rh_implies_weilPositivity_of_fourierOrientedExplicit
#print axioms fourierCos_autocorrelation_nonneg

-- These two audits isolate the unresolved legacy dependencies.
#print axioms rh_implies_weil_positivity_from_explicit
#print axioms weil_explicit_formula

end ArithmeticHodge.Analysis
