import ArithmeticHodge.Analysis.MultiplicativeWeilQuadraticRealImagSplitStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneQuarterPartitionStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilLiCriterionClosure

set_option autoImplicit false

open Complex Real

namespace ArithmeticHodge.Analysis.MultiplicativeWeilRealCutPhaseReductionStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilMonotoneQuarterPartitionStructural

/-!
# Real-phase reduction for a conjugation-fixed Bombieri cut

The complete Bombieri cross of two real-valued tests is real.  Consequently,
once the suffix diagonal is nonnegative, allowing an arbitrary complex scalar
in a head--suffix pencil adds only the nonnegative term
`c.im ^ 2 * Q(suffix)`.  Thus the full complex phase disk reduces exactly to
the real scalar line for the real-valued partitions that suffice after the
real--imaginary splitting of an arbitrary Bombieri test.
-/

/-- It is enough to prove the concrete Bombieri inequality on tests fixed by
coefficient conjugation, i.e. on pointwise real-valued tests. -/
def BombieriRealQuadraticNonnegativity : Prop :=
  ∀ g : BombieriTest,
    bombieriConjugateTest g = g →
      0 ≤ (bombieriFunctional (bombieriQuadraticTest g)).re

/-- Exact reduction of global Bombieri positivity to the real-valued subspace.
The reverse direction uses the functional-level real--imaginary splitting,
not a pointwise assertion about the raw autocorrelation test. -/
theorem bombieriQuadratic_re_nonnegative_iff_real :
    (∀ g : BombieriTest,
        0 ≤ (bombieriFunctional (bombieriQuadraticTest g)).re) ↔
      BombieriRealQuadraticNonnegativity := by
  constructor
  · intro hall g _hg
    exact hall g
  · intro hreal g
    rw [bombieriFunctional_quadratic_eq_realPart_add_imagPart]
    simp only [Complex.add_re]
    exact add_nonneg
      (hreal (bombieriRealPartTest g)
        (bombieriConjugateTest_realPartTest g))
      (hreal (bombieriImagPartTest g)
        (bombieriConjugateTest_imagPartTest g))

/-- The unconditional Bombieri criterion may therefore be stated using only
pointwise real-valued smooth tests. -/
theorem riemannHypothesis_iff_bombieriRealQuadraticNonnegativity
    (zeros : ZetaZeroEnumeration) :
    RiemannHypothesis ↔ BombieriRealQuadraticNonnegativity := by
  rw [riemannHypothesis_iff_bombieriQuadratic_re_nonnegative zeros,
    bombieriQuadratic_re_nonnegative_iff_real]

/-- Exact phase decomposition for two coefficient-conjugation-fixed tests.
The imaginary part of the scalar contributes only its squared magnitude times
the suffix diagonal. -/
theorem bombieriFunctional_twoBlock_re_eq_realPhase_add_imagSq
    (f g : BombieriTest)
    (hf : bombieriConjugateTest f = f)
    (hg : bombieriConjugateTest g = g)
    (c : ℂ) :
    (bombieriFunctional
        (bombieriQuadraticTest (f + c • g))).re =
      (bombieriFunctional
          (bombieriQuadraticTest (f + (c.re : ℂ) • g))).re +
        c.im ^ 2 *
          (bombieriFunctional (bombieriQuadraticTest g)).re := by
  have hcross :=
    bombieriTwoBlockGlobalCrossSymbol_im_eq_zero_of_conjugate_fixed
      f g hf hg
  rw [bombieriFunctional_twoBlock_re,
    bombieriFunctional_twoBlock_re]
  simp only [Complex.normSq_apply, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, hcross, mul_zero, sub_zero]
  ring

/-- Provided the suffix diagonal is nonnegative, positivity in every complex
scalar direction is equivalent to positivity on the real scalar line. -/
theorem bombieriFunctional_twoBlock_all_complex_nonneg_iff_all_real
    (f g : BombieriTest)
    (hf : bombieriConjugateTest f = f)
    (hg : bombieriConjugateTest g = g)
    (hdiag : 0 ≤
      (bombieriFunctional (bombieriQuadraticTest g)).re) :
    (∀ c : ℂ,
        0 ≤ (bombieriFunctional
          (bombieriQuadraticTest (f + c • g))).re) ↔
      ∀ a : ℝ,
        0 ≤ (bombieriFunctional
          (bombieriQuadraticTest (f + (a : ℂ) • g))).re := by
  constructor
  · intro hall a
    exact hall (a : ℂ)
  · intro hreal c
    rw [bombieriFunctional_twoBlock_re_eq_realPhase_add_imagSq
      f g hf hg c]
    exact add_nonneg (hreal c.re) (mul_nonneg (sq_nonneg _) hdiag)

/-- A real-valued parent remains real-valued after a monotone cutoff. -/
theorem bombieriConjugateTest_monotoneQuarterCutoff
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent)
    (k : ℤ) :
    bombieriConjugateTest (monotoneQuarterCutoff parent k) =
      monotoneQuarterCutoff parent k := by
  apply TestFunction.ext
  intro x
  simp only [bombieriConjugateTest_apply, monotoneQuarterCutoff_apply,
    map_mul, Complex.conj_ofReal]
  have hp := congrArg (fun f : BombieriTest ↦ f x) hparent
  simpa only [bombieriConjugateTest_apply] using congrArg
    (fun z : ℂ ↦ (monotoneQuarterStep k x : ℂ) * z) hp

/-- The canonical monotone cell cut from a real-valued parent is real-valued. -/
theorem bombieriConjugateTest_monotoneQuarterCell
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent)
    (k : ℤ) :
    bombieriConjugateTest (monotoneQuarterCell parent k) =
      monotoneQuarterCell parent k := by
  apply TestFunction.ext
  intro x
  simp only [bombieriConjugateTest_apply, monotoneQuarterCell_apply,
    map_mul, Complex.conj_ofReal]
  have hp := congrArg (fun f : BombieriTest ↦ f x) hparent
  simpa only [bombieriConjugateTest_apply] using congrArg
    (fun z : ℂ ↦ (monotoneQuarterWeight k x : ℂ) * z) hp

/-- For nested monotone cutoffs of a real-valued parent, a nonnegative inner
cutoff reduces the entire complex pencil to its real phase line. -/
theorem monotoneQuarterCutoff_all_complex_nonneg_iff_all_real
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent)
    (k : ℤ)
    (hinner : 0 ≤
      (bombieriFunctional
        (bombieriQuadraticTest
          (monotoneQuarterCutoff parent (k + 1)))).re) :
    (∀ c : ℂ,
        0 ≤ (bombieriFunctional
          (bombieriQuadraticTest
            (monotoneQuarterCutoff parent k +
              c • monotoneQuarterCutoff parent (k + 1)))).re) ↔
      ∀ a : ℝ,
        0 ≤ (bombieriFunctional
          (bombieriQuadraticTest
            (monotoneQuarterCutoff parent k +
              (a : ℂ) • monotoneQuarterCutoff parent (k + 1)))).re := by
  exact bombieriFunctional_twoBlock_all_complex_nonneg_iff_all_real
    (monotoneQuarterCutoff parent k)
    (monotoneQuarterCutoff parent (k + 1))
    (bombieriConjugateTest_monotoneQuarterCutoff parent hparent k)
    (bombieriConjugateTest_monotoneQuarterCutoff parent hparent (k + 1))
    hinner

/-- The same reduction in the actual head-cell plus whole-suffix coordinates
used by finite assembly. -/
theorem monotoneQuarterCell_cutoff_all_complex_nonneg_iff_all_real
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent)
    (k : ℤ)
    (hinner : 0 ≤
      (bombieriFunctional
        (bombieriQuadraticTest
          (monotoneQuarterCutoff parent (k + 1)))).re) :
    (∀ c : ℂ,
        0 ≤ (bombieriFunctional
          (bombieriQuadraticTest
            (monotoneQuarterCell parent k +
              c • monotoneQuarterCutoff parent (k + 1)))).re) ↔
      ∀ a : ℝ,
        0 ≤ (bombieriFunctional
          (bombieriQuadraticTest
            (monotoneQuarterCell parent k +
              (a : ℂ) • monotoneQuarterCutoff parent (k + 1)))).re := by
  exact bombieriFunctional_twoBlock_all_complex_nonneg_iff_all_real
    (monotoneQuarterCell parent k)
    (monotoneQuarterCutoff parent (k + 1))
    (bombieriConjugateTest_monotoneQuarterCell parent hparent k)
    (bombieriConjugateTest_monotoneQuarterCutoff parent hparent (k + 1))
    hinner

end

end ArithmeticHodge.Analysis.MultiplicativeWeilRealCutPhaseReductionStructural
