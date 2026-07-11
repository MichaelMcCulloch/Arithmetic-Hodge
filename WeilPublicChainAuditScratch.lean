import ArithmeticHodge.Analysis.WeilPositivity

set_option autoImplicit false

open Complex Filter Topology Real MeasureTheory Nat

namespace ArithmeticHodge.Analysis

/-! ## Sound local characterization of the forward-orientation gap -/

/-- Autocorrelation gives Fourier-side nonnegativity. -/
theorem autocorrelation_fourierCos_nonneg_public_audit_scratch
    (f : ℝ → ℝ) (hf : IsAutocorrelation f) (xi : ℝ) :
    0 ≤ fourierCos f xi := by
  obtain ⟨g, hg, hg_sq, hfg⟩ := hf
  exact fourierCos_autocorrelation_nonneg g hg hg_sq f hfg xi

/-- Autocorrelation does not give pointwise nonnegativity, so an explicit
formula summing `f(gamma)` cannot use the preceding Fourier theorem. -/
theorem autocorrelation_not_pointwise_nonnegative_public_audit_scratch :
    ¬ ∀ (f : ℝ → ℝ), IsAutocorrelation f → ∀ x, 0 ≤ f x := by
  intro hall
  obtain ⟨f, hf, hf_one⟩ := exists_autocorrelation_with_negative_value
  have hnonneg := hall f hf 1
  rw [hf_one] at hnonneg
  norm_num at hnonneg

/-- The actual logical core of `weil_criterion_forward_from_explicit` does
not use autocorrelation, zero provenance, or summability: equality to a
nonnegative `tsum` is already sufficient. -/
theorem forward_helper_minimal_public_audit_scratch
    (f fHat : ℝ → ℝ) (zeros : ℕ → ℝ)
    (hexpl : ∑' n, f (zeros n) = weilFunctionalFull f fHat)
    (hterms : ∀ n, 0 ≤ f (zeros n)) :
    0 ≤ weilFunctionalFull f fHat := by
  rw [← hexpl]
  exact tsum_nonneg hterms

/-- The existential conclusion used by `weil_explicit_unconditional` is
satisfied by every summable series: put the entire sum into one unnamed
component and set the other two to zero. -/
theorem unconditional_explicit_shape_vacuous_public_audit_scratch
    (a : ℕ → ℂ) (ha : Summable a) :
    ∃ polar prime arch : ℂ,
      Summable a ∧ ∑' n, a n = polar + prime + arch := by
  exact ⟨∑' n, a n, 0, 0, ha, by ring⟩

/-- The public zero-provenance field permits a constant repetition of one
zero and therefore does not encode exhaustivity or analytic multiplicity. -/
theorem constant_zero_sequence_satisfies_public_provenance_audit_scratch
    (rho : NontrivialZetaZero) :
    ∀ n, ∃ rho' : NontrivialZetaZero,
      (fun _ : ℕ => rho.val.im) n = rho'.val.im := by
  intro n
  exact ⟨rho, rfl⟩

/-- A correctly oriented conditional explicit-formula interface for the
current `WeilPositivity` definition.  Its spectral side is `fourierCos f`,
the quantity known to be nonnegative for autocorrelations. -/
def FourierOrientedWeilExplicit : Prop :=
  ∀ (f : ℝ → ℝ), IsAutocorrelation f → Continuous f →
    (∀ x : ℝ, ‖f x‖ ≤ 1 / (1 + x ^ 2)) → RiemannHypothesis →
      ∃ zeros : ℕ → ℝ,
        Summable (fun n => fourierCos f (zeros n)) ∧
        ∑' n, fourierCos f (zeros n) =
          weilFunctionalFull f (fourierCos f)

/-- With the spectral transform on the correct side, the forward implication
is immediate and uses no unproved mathematics beyond the explicit premise. -/
theorem rh_implies_weilPositivity_of_fourierOrientedExplicit_public_audit_scratch
    (hexplicit : FourierOrientedWeilExplicit) :
    RiemannHypothesis → WeilPositivity := by
  intro hRH f hf hcont hdecay
  obtain ⟨zeros, _hsumm, hexpl⟩ := hexplicit f hf hcont hdecay hRH
  rw [← hexpl]
  exact tsum_nonneg fun n =>
    autocorrelation_fourierCos_nonneg_public_audit_scratch f hf (zeros n)

/-! ## Axiom audit of the public chain -/

#print axioms xi_hadamard_product
#print axioms weil_contour_identity
#print axioms sum_over_zeros_eq_contour
#print axioms weil_explicit_formula
#print axioms weil_explicit_unconditional
#print axioms rh_zeros_on_critical_line
#print axioms contour_assembly_polar_sign

#print axioms rh_implies_weil_positivity_from_explicit
#print axioms bombieriAutocorrelation_weil_neg
#print axioms exists_negative_weil_autocorrelation
#print axioms weil_positivity_implies_rh_from_explicit
#print axioms weil_criterion_equiv_proved

#print axioms autocorrelation_nonneg_at_zero
#print axioms autocorrelation_even
#print axioms tsum_nonneg_of_nonneg
#print axioms weil_criterion_forward_from_explicit
#print axioms weil_criterion_equiv
#print axioms weil_criterion_forward
#print axioms weil_criterion_backward
#print axioms weil_criterion

#print axioms autocorrelation_fourierCos_nonneg_public_audit_scratch
#print axioms autocorrelation_not_pointwise_nonnegative_public_audit_scratch
#print axioms forward_helper_minimal_public_audit_scratch
#print axioms unconditional_explicit_shape_vacuous_public_audit_scratch
#print axioms constant_zero_sequence_satisfies_public_provenance_audit_scratch
#print axioms rh_implies_weilPositivity_of_fourierOrientedExplicit_public_audit_scratch

end ArithmeticHodge.Analysis
