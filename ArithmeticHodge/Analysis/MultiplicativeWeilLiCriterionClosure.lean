import ArithmeticHodge.Analysis.MultiplicativeWeilCriterion
import ArithmeticHodge.Analysis.MultiplicativeWeilExplicitFormula
import ArithmeticHodge.Analysis.MultiplicativeWeilLiDominantSeries
import ArithmeticHodge.Analysis.MultiplicativeWeilLiCutoffTsum

/-!
# Closing the Bombieri converse with Li cutoffs and smoothing

The earlier sequence-level approximation interface is retained below, while
the final section discharges it using the hard-cutoff and smoothing exchanges.
Full paired Li negativity therefore produces the concrete nonzero Bombieri
witness required by the criterion without any analytic hypothesis.
-/

set_option autoImplicit false

open Complex Filter Real Set Topology

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- Smooth Bombieri tests can approximate every fixed paired Li zero sum. -/
def BombieriLiSpectralApproximation
    (zeros : ZetaZeroEnumeration) : Prop :=
  ∀ n : ℕ, ∃ g : ℕ → BombieriTest,
    Tendsto
      (fun j ↦ ∑' k : ℕ,
        spectralTerm (g j : ℝ → ℂ) (zeros.zero k).val)
      atTop
      (𝓝 (∑' k : ℕ,
        (liFunction n (zeros.zero k).val +
          liFunction n (1 - (zeros.zero k).val))))

/-- The spectral approximation property plus the dominant-series theorem
discharges the entire off-critical witness obligation. -/
theorem bombieriOffCriticalSpectralNegativity_of_liApproximation
    (zeros : ZetaZeroEnumeration)
    (happrox : BombieriLiSpectralApproximation zeros) :
    BombieriOffCriticalSpectralNegativity zeros := by
  intro hnot
  obtain ⟨n, _hn, hnegative⟩ :=
    not_RH_exists_large_liFunction_paired_tsum_re_negative
      zeros hnot 0
  obtain ⟨g, hg⟩ := happrox n
  have hgre : Tendsto
      (fun j ↦ (∑' k : ℕ,
        spectralTerm (g j : ℝ → ℂ) (zeros.zero k).val).re)
      atTop
      (𝓝 ((∑' k : ℕ,
        (liFunction n (zeros.zero k).val +
          liFunction n (1 - (zeros.zero k).val))).re)) := by
    exact (Complex.reCLM.continuous.tendsto _).comp hg
  have hevent : ∀ᶠ j : ℕ in atTop,
      (∑' k : ℕ,
        spectralTerm (g j : ℝ → ℂ) (zeros.zero k).val).re < 0 :=
    hgre.eventually (Iio_mem_nhds hnegative)
  obtain ⟨j, hj⟩ := hevent.exists
  refine ⟨g j, ?_, hj⟩
  intro hzero
  have hcoe : (g j : ℝ → ℂ) = 0 := by
    rw [hzero]
    rfl
  simp [hcoe, spectralTerm, mellin, coefficientConjugate] at hj

/-- With the now-unconditional explicit formula, Li spectral approximation is
the sole remaining hypothesis in the concrete Bombieri nonnegativity
criterion. -/
theorem riemannHypothesis_iff_bombieriNonnegativity_of_liApproximation
    (zeros : ZetaZeroEnumeration)
    (happrox : BombieriLiSpectralApproximation zeros) :
    RiemannHypothesis ↔ BombieriNonnegativity :=
  riemannHypothesis_iff_bombieriNonnegativity zeros
    (bombieriZeroSumFormula zeros)
    (bombieriOffCriticalSpectralNegativity_of_liApproximation zeros happrox)

/-! ## Unconditional closure -/

/-- Bombieri's off-critical smooth witness construction, with both the hard
cutoff and smoothing exchanges now discharged. -/
theorem bombieriOffCriticalSpectralNegativity
    (zeros : ZetaZeroEnumeration) :
    BombieriOffCriticalSpectralNegativity zeros :=
  bombieriOffCriticalSpectralNegativity_of_liKernelCutoffTsum zeros

/-- The source-faithful Bombieri quadratic criterion is unconditional: its
only remaining direction toward an actual proof of RH is proving the concrete
quadratic functional nonnegative for every Bombieri test. -/
theorem riemannHypothesis_iff_bombieriNonnegativity_unconditional
    (zeros : ZetaZeroEnumeration) :
    RiemannHypothesis ↔ BombieriNonnegativity :=
  riemannHypothesis_iff_bombieriNonnegativity zeros
    (bombieriZeroSumFormula zeros)
    (bombieriOffCriticalSpectralNegativity zeros)

/-- Exact real-valued terminal target: RH is equivalent to nonnegativity of
the concrete Bombieri quadratic functional.  No separate imaginary-part
hypothesis is needed for the backward implication. -/
theorem riemannHypothesis_iff_bombieriQuadratic_re_nonnegative
    (zeros : ZetaZeroEnumeration) :
    RiemannHypothesis ↔
      ∀ g : BombieriTest,
        0 ≤ (bombieriFunctional (bombieriQuadraticTest g)).re := by
  constructor
  · intro hRH g
    exact (rh_implies_bombieriFunctional_quadratic_nonneg
      zeros (bombieriZeroSumFormula zeros) hRH g).2
  · intro hnonnegative
    by_contra hnot
    obtain ⟨g, _hg, hnegative⟩ :=
      bombieriOffCriticalNegativity_of_spectral zeros
        (bombieriZeroSumFormula zeros)
        (bombieriOffCriticalSpectralNegativity zeros) hnot
    exact (not_lt_of_ge (hnonnegative g)) hnegative

/-- Dual terminal target for falsification: RH fails exactly when a nonzero
Bombieri test has strictly negative concrete quadratic value. -/
theorem not_riemannHypothesis_iff_exists_bombieriQuadratic_re_negative
    (zeros : ZetaZeroEnumeration) :
    ¬ RiemannHypothesis ↔
      ∃ g : BombieriTest, g ≠ 0 ∧
        (bombieriFunctional (bombieriQuadraticTest g)).re < 0 := by
  constructor
  · intro hnot
    exact bombieriOffCriticalNegativity_of_spectral zeros
      (bombieriZeroSumFormula zeros)
      (bombieriOffCriticalSpectralNegativity zeros) hnot
  · rintro ⟨g, _hg, hnegative⟩ hRH
    have hnonnegative :=
      (rh_implies_bombieriFunctional_quadratic_nonneg
        zeros (bombieriZeroSumFormula zeros) hRH g).2
    exact (not_lt_of_ge hnonnegative) hnegative

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
