/-
  The source-oriented Bombieri criterion with all algebraic and test-space
  plumbing discharged.

  What remains visible in theorem types is the genuine analytic content:
  the explicit zero-sum identity and the off-critical negative-witness
  construction for the converse.  Spectral separation appears only in the
  optional upgrade from semidefinite to strict positivity.
-/

import ArithmeticHodge.Analysis.MultiplicativeWeilFunctional
import ArithmeticHodge.Analysis.MultiplicativeWeilQuadraticMellin
import ArithmeticHodge.Analysis.MultiplicativeWeilZeros

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ContDiff Distributions

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- Under RH, every entry of an analytic-multiplicity zero enumeration lies on
the critical line. -/
theorem ZetaZeroEnumeration.zero_re_eq_half_of_rh
    (zeros : ZetaZeroEnumeration) (hRH : RiemannHypothesis) (n : ℕ) :
    (zeros.zero n).val.re = 1 / 2 := by
  exact hRH (zeros.zero n).val (zeros.zero n).is_zero (by
    rintro ⟨k, hk⟩
    have hre := (zeros.zero n).re_pos
    rw [hk] at hre
    have hkpos : (0 : ℝ) < (k : ℝ) + 1 := Nat.cast_add_one_pos k
    norm_num at hre
    linarith) (by
      intro hone
      have : (zeros.zero n).val.re = 1 := by rw [hone]; simp
      linarith [(zeros.zero n).re_lt_one])

/-- With the explicit zero-sum identity, RH turns the concrete quadratic
functional into the sum of squared Mellin norms. -/
theorem rh_bombieriFunctional_quadratic_eq_tsum_normSq
    (zeros : ZetaZeroEnumeration)
    (hformula : BombieriZeroSumFormula zeros)
    (hRH : RiemannHypothesis) (g : BombieriTest) :
    bombieriFunctional (bombieriQuadraticTest g) =
      ∑' n, (Complex.normSq
        (mellin (g : ℝ → ℂ) (zeros.zero n).val) : ℂ) := by
  exact rh_bombieri_quadratic_eq_tsum_normSq
    bombieriFunctional canonicalTransposeData zeros
    (bombieriZeroSumFormula_to_explicitFormula zeros hformula)
    hRH g (bombieriQuadraticTestData g)
    (fun n ↦ bombieriQuadraticConvolutionFubiniAt g (zeros.zero n).val)

/-- RH-forward nonnegativity of the concrete Bombieri functional. -/
theorem rh_implies_bombieriFunctional_quadratic_nonneg
    (zeros : ZetaZeroEnumeration)
    (hformula : BombieriZeroSumFormula zeros)
    (hRH : RiemannHypothesis) (g : BombieriTest) :
    (bombieriFunctional (bombieriQuadraticTest g)).im = 0 ∧
      0 ≤ (bombieriFunctional (bombieriQuadraticTest g)).re := by
  exact rh_implies_bombieri_nonneg
    bombieriFunctional canonicalTransposeData zeros
    (bombieriZeroSumFormula_to_explicitFormula zeros hformula)
    hRH g (bombieriQuadraticTestData g)
    (fun n ↦ bombieriQuadraticConvolutionFubiniAt g (zeros.zero n).val)

/-- No nonzero Bombieri test has a Mellin transform vanishing at every
enumerated zeta zero.  This is the zero-density versus exponential-type input
needed to upgrade nonnegativity to strict positivity. -/
def BombieriSpectralSeparation (zeros : ZetaZeroEnumeration) : Prop :=
  ∀ g : BombieriTest, g ≠ 0 →
    ∃ n, mellin (g : ℝ → ℂ) (zeros.zero n).val ≠ 0

/-- Spectral separation is equivalently the uniqueness statement that
vanishing at every enumerated zeta zero forces the test itself to vanish. -/
theorem bombieriSpectralSeparation_iff
    (zeros : ZetaZeroEnumeration) :
    BombieriSpectralSeparation zeros ↔
      ∀ g : BombieriTest,
        (∀ n, mellin (g : ℝ → ℂ) (zeros.zero n).val = 0) → g = 0 := by
  constructor
  · intro h g hzero
    by_contra hg
    obtain ⟨n, hn⟩ := h g hg
    exact hn (hzero n)
  · intro h g hg
    by_contra hnone
    push_neg at hnone
    exact hg (h g hnone)

/-- RH-forward strict positivity, conditional exactly on spectral separation
and the explicit zero-sum identity. -/
theorem rh_implies_bombieriFunctional_quadratic_strictPos
    (zeros : ZetaZeroEnumeration)
    (hformula : BombieriZeroSumFormula zeros)
    (hseparate : BombieriSpectralSeparation zeros)
    (hRH : RiemannHypothesis) (g : BombieriTest) (hg : g ≠ 0) :
    (bombieriFunctional (bombieriQuadraticTest g)).im = 0 ∧
      0 < (bombieriFunctional (bombieriQuadraticTest g)).re := by
  let a : ℕ → ℂ := fun n ↦
    (Complex.normSq (mellin (g : ℝ → ℂ) (zeros.zero n).val) : ℂ)
  have hterm : ∀ n, mellin (bombieriQuadraticTest g : ℝ → ℂ)
      (zeros.zero n).val = a n := by
    intro n
    exact (bombieriQuadraticTestData_hasMellin g (zeros.zero n).val).2.trans
      (spectralTerm_eq_normSq_of_re_eq_half
        (g : ℝ → ℂ) (zeros.zero_re_eq_half_of_rh hRH n))
  have hsummC : Summable a :=
    (hformula (bombieriQuadraticTest g)).1.congr hterm
  have heq : bombieriFunctional (bombieriQuadraticTest g) = ∑' n, a n :=
    rh_bombieriFunctional_quadratic_eq_tsum_normSq zeros hformula hRH g
  obtain ⟨n, hn⟩ := hseparate g hg
  constructor
  · rw [heq]
    change Complex.imCLM (∑' n, a n) = 0
    rw [Complex.imCLM.map_tsum hsummC]
    simp [a]
  · rw [heq]
    change 0 < Complex.reCLM (∑' n, a n)
    rw [Complex.reCLM.map_tsum hsummC]
    have hsummR : Summable (fun n ↦ Complex.reCLM (a n)) := by
      simpa only [Function.comp_apply] using
        hsummC.map Complex.reCLM Complex.reCLM.continuous
    apply hsummR.tsum_pos
    · intro k
      simp only [a]
      exact Complex.normSq_nonneg _
    · simp only [a]
      exact Complex.normSq_pos.mpr hn

/-- Strict positivity of the concrete quadratic Bombieri functional. -/
def BombieriStrictPositivity : Prop :=
  ∀ g : BombieriTest, g ≠ 0 →
      (bombieriFunctional (bombieriQuadraticTest g)).im = 0 ∧
        0 < (bombieriFunctional (bombieriQuadraticTest g)).re

/-- Positive semidefiniteness of the concrete quadratic Bombieri functional.
This is the source-faithful Weil--Bombieri criterion. -/
def BombieriNonnegativity : Prop :=
  ∀ g : BombieriTest,
    (bombieriFunctional (bombieriQuadraticTest g)).im = 0 ∧
      0 ≤ (bombieriFunctional (bombieriQuadraticTest g)).re

/-- The source-side converse obligation: off RH, a nonzero test makes the
summable zero-side quadratic series negative.  This is the Li-function
truncation and smoothing step in Bombieri's argument. -/
def BombieriOffCriticalSpectralNegativity
    (zeros : ZetaZeroEnumeration) : Prop :=
  ¬ RiemannHypothesis →
    ∃ g : BombieriTest, g ≠ 0 ∧
      Summable (fun n ↦ spectralTerm (g : ℝ → ℂ) (zeros.zero n).val) ∧
      (∑' n, spectralTerm (g : ℝ → ℂ) (zeros.zero n).val).re < 0

/-- The explicit formula transports a negative spectral witness to the
concrete prime/archimedean functional. -/
theorem bombieriOffCriticalNegativity_of_spectral
    (zeros : ZetaZeroEnumeration)
    (hformula : BombieriZeroSumFormula zeros)
    (hnegative : BombieriOffCriticalSpectralNegativity zeros) :
    ¬ RiemannHypothesis →
      ∃ g : BombieriTest, g ≠ 0 ∧
        (bombieriFunctional (bombieriQuadraticTest g)).re < 0 := by
  intro hRH
  obtain ⟨g, hg, _hsumm, hneg⟩ := hnegative hRH
  refine ⟨g, hg, ?_⟩
  have hterm : ∀ n, mellin (bombieriQuadraticTest g : ℝ → ℂ)
      (zeros.zero n).val =
        spectralTerm (g : ℝ → ℂ) (zeros.zero n).val := fun n ↦
    (bombieriQuadraticTestData_hasMellin g (zeros.zero n).val).2
  have heq : bombieriFunctional (bombieriQuadraticTest g) =
      ∑' n, spectralTerm (g : ℝ → ℂ) (zeros.zero n).val := by
    rw [(hformula (bombieriQuadraticTest g)).2]
    exact tsum_congr hterm
  rw [heq]
  exact hneg

/-- Bombieri's positive-semidefinite criterion, conditional only on the
explicit zero-sum identity and the genuine off-critical witness theorem. -/
theorem riemannHypothesis_iff_bombieriNonnegativity
    (zeros : ZetaZeroEnumeration)
    (hformula : BombieriZeroSumFormula zeros)
    (hnegative : BombieriOffCriticalSpectralNegativity zeros) :
    RiemannHypothesis ↔ BombieriNonnegativity := by
  constructor
  · intro hRH g
    exact rh_implies_bombieriFunctional_quadratic_nonneg
      zeros hformula hRH g
  · intro hnonneg
    by_contra hRH
    obtain ⟨g, _hg, hneg⟩ :=
      bombieriOffCriticalNegativity_of_spectral zeros hformula hnegative hRH
    exact (not_lt_of_ge (hnonneg g).2) hneg

/-- The stronger strict-positivity refinement when spectral separation is
also available. -/
theorem riemannHypothesis_iff_bombieriStrictPositivity
    (zeros : ZetaZeroEnumeration)
    (hformula : BombieriZeroSumFormula zeros)
    (hseparate : BombieriSpectralSeparation zeros)
    (hnegative : BombieriOffCriticalSpectralNegativity zeros) :
    RiemannHypothesis ↔ BombieriStrictPositivity := by
  constructor
  · intro hRH g hg
    exact rh_implies_bombieriFunctional_quadratic_strictPos
      zeros hformula hseparate hRH g hg
  · intro hpos
    by_contra hRH
    obtain ⟨g, hg, hneg⟩ :=
      bombieriOffCriticalNegativity_of_spectral zeros hformula hnegative hRH
    exact (not_lt_of_ge (hpos g hg).2.le) hneg

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
