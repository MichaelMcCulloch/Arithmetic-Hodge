import ArithmeticHodge.Analysis.MultiplicativeWeilFunctional
import ArithmeticHodge.Analysis.MultiplicativeWeilQuadraticMellin
import ArithmeticHodge.Analysis.MultiplicativeWeilZeros

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ContDiff Distributions

namespace ArithmeticHodge.Analysis.MultiplicativeWeil.CriterionScratch

noncomputable section

theorem zero_re_eq_half (zeros : ZetaZeroEnumeration)
    (hRH : RiemannHypothesis) (n : ℕ) :
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

theorem rh_quadratic_eq_tsum (zeros : ZetaZeroEnumeration)
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

theorem rh_quadratic_nonneg (zeros : ZetaZeroEnumeration)
    (hformula : BombieriZeroSumFormula zeros)
    (hRH : RiemannHypothesis) (g : BombieriTest) :
    (bombieriFunctional (bombieriQuadraticTest g)).im = 0 ∧
      0 ≤ (bombieriFunctional (bombieriQuadraticTest g)).re := by
  exact rh_implies_bombieri_nonneg
    bombieriFunctional canonicalTransposeData zeros
    (bombieriZeroSumFormula_to_explicitFormula zeros hformula)
    hRH g (bombieriQuadraticTestData g)
    (fun n ↦ bombieriQuadraticConvolutionFubiniAt g (zeros.zero n).val)

def BombieriSpectralSeparation (zeros : ZetaZeroEnumeration) : Prop :=
  ∀ g : BombieriTest, g ≠ 0 →
    ∃ n, mellin (g : ℝ → ℂ) (zeros.zero n).val ≠ 0

theorem rh_quadratic_strictPos (zeros : ZetaZeroEnumeration)
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
        (g : ℝ → ℂ) (zero_re_eq_half zeros hRH n))
  have hsummC : Summable a :=
    (hformula (bombieriQuadraticTest g)).1.congr hterm
  have heq : bombieriFunctional (bombieriQuadraticTest g) = ∑' n, a n :=
    rh_quadratic_eq_tsum zeros hformula hRH g
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

def BombieriStrictPositivity : Prop :=
  ∀ g : BombieriTest, g ≠ 0 →
    0 < (bombieriFunctional (bombieriQuadraticTest g)).re

def BombieriOffCriticalNegativity : Prop :=
  ¬ RiemannHypothesis →
    ∃ g : BombieriTest, g ≠ 0 ∧
      (bombieriFunctional (bombieriQuadraticTest g)).re < 0

theorem rh_iff_bombieriStrictPositivity
    (zeros : ZetaZeroEnumeration)
    (hformula : BombieriZeroSumFormula zeros)
    (hseparate : BombieriSpectralSeparation zeros)
    (hnegative : BombieriOffCriticalNegativity) :
    RiemannHypothesis ↔ BombieriStrictPositivity := by
  constructor
  · intro hRH g hg
    exact (rh_quadratic_strictPos zeros hformula hseparate hRH g hg).2
  · intro hpos
    by_contra hRH
    obtain ⟨g, hg, hneg⟩ := hnegative hRH
    exact (not_lt_of_ge (hpos g hg).le) hneg

#print axioms rh_quadratic_strictPos
#print axioms rh_iff_bombieriStrictPositivity

end

end ArithmeticHodge.Analysis.MultiplicativeWeil.CriterionScratch
