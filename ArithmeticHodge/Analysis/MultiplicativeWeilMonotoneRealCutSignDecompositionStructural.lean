import ArithmeticHodge.Analysis.MultiplicativeWeilRealMonotoneTailConeCriterionStructural

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneRealCutSignDecompositionStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilRealMonotonePropagationCriterionStructural

/-!
# Smooth sign decomposition and the mixed-cut obstruction

The nonsmooth functions `max g 0` and `max (-g) 0` are not Bombieri tests at
general zeroes of `g`.  A genuine smooth replacement is available after
choosing a smooth pointwise majorant `rho >= |g|`: the two tests

`p = (rho + g) / 2`, `n = (rho - g) / 2`

are smooth, compactly supported, real, pointwise nonnegative, and satisfy
`g = p - n`.

This does not linearly reduce cutoff propagation to the nonnegative cone.
The Bombieri quadratic of every cutoff contains the complete mixed cross
`-2 Re B(C_k p, C_k n)`.  More sharply, the nonnegative tail assumptions for
`g` translate into mixed upper bounds at every later cutoff; they do not give
the separate tail nonnegativity assumptions needed to propagate `p` and `n`.
-/

/-- Intrinsic pointwise nonnegativity for a real-valued Bombieri test. -/
def BombieriPointwiseNonnegative (f : BombieriTest) : Prop :=
  bombieriConjugateTest f = f ∧ ∀ x : ℝ, 0 ≤ (f x).re

/-- Smooth positive piece associated to a real smooth majorant. -/
def bombieriSmoothPositivePiece
    (rho parent : BombieriTest) : BombieriTest :=
  ((1 / 2 : ℝ) : ℂ) • (rho + parent)

/-- Smooth negative piece associated to a real smooth majorant. -/
def bombieriSmoothNegativePiece
    (rho parent : BombieriTest) : BombieriTest :=
  ((1 / 2 : ℝ) : ℂ) • (rho - parent)

/-- The two smooth pieces recover the parent exactly. -/
theorem bombieriSmoothPositivePiece_sub_negativePiece
    (rho parent : BombieriTest) :
    bombieriSmoothPositivePiece rho parent -
        bombieriSmoothNegativePiece rho parent = parent := by
  apply TestFunction.ext
  intro x
  simp only [bombieriSmoothPositivePiece, bombieriSmoothNegativePiece,
    TestFunction.coe_sub, Pi.sub_apply, TestFunction.coe_smul,
    Pi.smul_apply, TestFunction.coe_add, Pi.add_apply, smul_eq_mul]
  push_cast
  ring

private theorem conjugate_fixed_sub
    (f g : BombieriTest)
    (hf : bombieriConjugateTest f = f)
    (hg : bombieriConjugateTest g = g) :
    bombieriConjugateTest (f - g) = f - g := by
  apply TestFunction.ext
  intro x
  have hfx := congrArg (fun q : BombieriTest ↦ q x) hf
  have hgx := congrArg (fun q : BombieriTest ↦ q x) hg
  simp only [bombieriConjugateTest_apply, TestFunction.coe_sub,
    Pi.sub_apply, map_sub] at hfx hgx ⊢
  rw [hfx, hgx]

/-- A real smooth majorant produces a real pointwise-nonnegative positive
piece. -/
theorem bombieriSmoothPositivePiece_pointwiseNonnegative
    (rho parent : BombieriTest)
    (hrho : bombieriConjugateTest rho = rho)
    (hparent : bombieriConjugateTest parent = parent)
    (hmajor : ∀ x : ℝ, |(parent x).re| ≤ (rho x).re) :
    BombieriPointwiseNonnegative
      (bombieriSmoothPositivePiece rho parent) := by
  constructor
  · apply TestFunction.ext
    intro x
    have hrx := congrArg (fun q : BombieriTest ↦ q x) hrho
    have hpx := congrArg (fun q : BombieriTest ↦ q x) hparent
    simp only [bombieriSmoothPositivePiece, bombieriConjugateTest_apply,
      TestFunction.coe_smul, Pi.smul_apply, TestFunction.coe_add,
      Pi.add_apply, smul_eq_mul, map_mul, map_add, Complex.conj_ofReal] at hrx hpx ⊢
    rw [hrx, hpx]
  · intro x
    unfold bombieriSmoothPositivePiece
    simp only [TestFunction.coe_smul, Pi.smul_apply, TestFunction.coe_add,
      Pi.add_apply, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.add_re]
    have h := (abs_le.mp (hmajor x)).1
    linarith

/-- The same majorant produces a real pointwise-nonnegative negative
piece. -/
theorem bombieriSmoothNegativePiece_pointwiseNonnegative
    (rho parent : BombieriTest)
    (hrho : bombieriConjugateTest rho = rho)
    (hparent : bombieriConjugateTest parent = parent)
    (hmajor : ∀ x : ℝ, |(parent x).re| ≤ (rho x).re) :
    BombieriPointwiseNonnegative
      (bombieriSmoothNegativePiece rho parent) := by
  constructor
  · apply TestFunction.ext
    intro x
    have hrx := congrArg (fun q : BombieriTest ↦ q x) hrho
    have hpx := congrArg (fun q : BombieriTest ↦ q x) hparent
    simp only [bombieriSmoothNegativePiece, bombieriConjugateTest_apply,
      TestFunction.coe_smul, Pi.smul_apply, TestFunction.coe_sub,
      Pi.sub_apply, smul_eq_mul, map_mul, map_sub, Complex.conj_ofReal] at hrx hpx ⊢
    rw [hrx, hpx]
  · intro x
    unfold bombieriSmoothNegativePiece
    simp only [TestFunction.coe_smul, Pi.smul_apply, TestFunction.coe_sub,
      Pi.sub_apply, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.sub_re]
    have h := (abs_le.mp (hmajor x)).2
    linarith

/-- Genuine smooth sign decomposition supplied by any smooth majorant. -/
theorem exists_smooth_pointwiseNonnegative_decomposition_of_majorant
    (rho parent : BombieriTest)
    (hrho : bombieriConjugateTest rho = rho)
    (hparent : bombieriConjugateTest parent = parent)
    (hmajor : ∀ x : ℝ, |(parent x).re| ≤ (rho x).re) :
    ∃ p n : BombieriTest,
      BombieriPointwiseNonnegative p ∧
        BombieriPointwiseNonnegative n ∧ parent = p - n := by
  refine ⟨bombieriSmoothPositivePiece rho parent,
    bombieriSmoothNegativePiece rho parent,
    bombieriSmoothPositivePiece_pointwiseNonnegative
      rho parent hrho hparent hmajor,
    bombieriSmoothNegativePiece_pointwiseNonnegative
      rho parent hrho hparent hmajor, ?_⟩
  exact (bombieriSmoothPositivePiece_sub_negativePiece rho parent).symm

/-! ## Exact cutoff expansion -/

/-- Monotone cutoff is linear under subtraction of parents. -/
theorem monotoneQuarterCutoff_sub
    (p n : BombieriTest) (k : ℤ) :
    monotoneQuarterCutoff (p - n) k =
      monotoneQuarterCutoff p k - monotoneQuarterCutoff n k := by
  apply TestFunction.ext
  intro x
  simp only [monotoneQuarterCutoff_apply, TestFunction.coe_sub, Pi.sub_apply]
  ring

/-- Exact quadratic expansion of a cutoff of a difference. -/
theorem bombieriRealQuadraticValue_cutoff_sub
    (p n : BombieriTest) (k : ℤ) :
    bombieriRealQuadraticValue
        (monotoneQuarterCutoff (p - n) k) =
      bombieriRealQuadraticValue (monotoneQuarterCutoff p k) +
        bombieriRealQuadraticValue (monotoneQuarterCutoff n k) -
        2 * (bombieriTwoBlockGlobalCrossSymbol
          (monotoneQuarterCutoff p k)
          (monotoneQuarterCutoff n k)).re := by
  rw [monotoneQuarterCutoff_sub]
  have h := bombieriFunctional_twoBlock_re
    (monotoneQuarterCutoff p k) (monotoneQuarterCutoff n k) (-1 : ℂ)
  unfold bombieriRealQuadraticValue
  simpa only [neg_one_smul, sub_eq_add_neg, Complex.normSq_neg,
    Complex.normSq_one, one_mul, neg_mul, mul_neg, Complex.neg_re] using h

/-- Pointwise cone membership does not make the quadratic additive: current
cutoff nonnegativity is exactly one mixed-cross upper bound. -/
theorem bombieriRealQuadraticValue_cutoff_sub_nonnegative_iff_mixedCross
    (p n : BombieriTest) (k : ℤ) :
    0 ≤ bombieriRealQuadraticValue
        (monotoneQuarterCutoff (p - n) k) ↔
      2 * (bombieriTwoBlockGlobalCrossSymbol
          (monotoneQuarterCutoff p k)
          (monotoneQuarterCutoff n k)).re ≤
        bombieriRealQuadraticValue (monotoneQuarterCutoff p k) +
          bombieriRealQuadraticValue (monotoneQuarterCutoff n k) := by
  rw [bombieriRealQuadraticValue_cutoff_sub]
  constructor <;> intro h <;> linarith

/-- The entire nonnegative cutoff tail of a difference is equivalent to a
family of mixed-cross bounds.  It does not project to separate nonnegative
tails for the two pointwise-nonnegative pieces. -/
theorem bombieriRealQuadraticValue_cutoff_sub_tail_nonnegative_iff_mixedCross
    (p n : BombieriTest) (k : ℤ) :
    (∀ j : ℕ,
      0 ≤ bombieriRealQuadraticValue
        (monotoneQuarterCutoff (p - n) (k + 1 + (j : ℤ)))) ↔
      ∀ j : ℕ,
        2 * (bombieriTwoBlockGlobalCrossSymbol
            (monotoneQuarterCutoff p (k + 1 + (j : ℤ)))
            (monotoneQuarterCutoff n (k + 1 + (j : ℤ)))).re ≤
          bombieriRealQuadraticValue
              (monotoneQuarterCutoff p (k + 1 + (j : ℤ))) +
            bombieriRealQuadraticValue
              (monotoneQuarterCutoff n (k + 1 + (j : ℤ))) := by
  constructor
  · intro h j
    exact
      (bombieriRealQuadraticValue_cutoff_sub_nonnegative_iff_mixedCross
        p n (k + 1 + (j : ℤ))).1 (h j)
  · intro h j
    exact
      (bombieriRealQuadraticValue_cutoff_sub_nonnegative_iff_mixedCross
        p n (k + 1 + (j : ℤ))).2 (h j)

/-- Specialization to the genuine smooth majorant decomposition.  The sole
failure of a linear cone reduction is the displayed complete mixed term. -/
theorem bombieriRealQuadraticValue_cutoff_eq_smoothPieces_sub_mixed
    (rho parent : BombieriTest) (k : ℤ) :
    bombieriRealQuadraticValue (monotoneQuarterCutoff parent k) =
      bombieriRealQuadraticValue
          (monotoneQuarterCutoff
            (bombieriSmoothPositivePiece rho parent) k) +
        bombieriRealQuadraticValue
          (monotoneQuarterCutoff
            (bombieriSmoothNegativePiece rho parent) k) -
        2 * (bombieriTwoBlockGlobalCrossSymbol
          (monotoneQuarterCutoff
            (bombieriSmoothPositivePiece rho parent) k)
          (monotoneQuarterCutoff
            (bombieriSmoothNegativePiece rho parent) k)).re := by
  calc
    bombieriRealQuadraticValue (monotoneQuarterCutoff parent k) =
        bombieriRealQuadraticValue
          (monotoneQuarterCutoff
            (bombieriSmoothPositivePiece rho parent -
              bombieriSmoothNegativePiece rho parent) k) := by
      rw [bombieriSmoothPositivePiece_sub_negativePiece]
    _ = _ := bombieriRealQuadraticValue_cutoff_sub
      (bombieriSmoothPositivePiece rho parent)
      (bombieriSmoothNegativePiece rho parent) k

/-- The mixed term cannot be omitted even algebraically: the decomposition
`0 = p - p` cancels two full diagonals through its cross. -/
theorem bombieriMixedCross_self_eq_diagonal
    (p : BombieriTest) (k : ℤ) :
    (bombieriTwoBlockGlobalCrossSymbol
      (monotoneQuarterCutoff p k)
      (monotoneQuarterCutoff p k)).re =
        bombieriRealQuadraticValue (monotoneQuarterCutoff p k) := by
  rw [bombieriTwoBlockGlobalCrossSymbol_self]
  rfl

end

end ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneRealCutSignDecompositionStructural
