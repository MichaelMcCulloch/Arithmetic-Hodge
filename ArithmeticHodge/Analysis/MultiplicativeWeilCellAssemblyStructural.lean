import ArithmeticHodge.Analysis.MultiplicativeWeilTwoSeedFactorTwo

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

open ArithmeticHodge.Analysis.MultiplicativeWeilRestrictedSupportEndpointPositive

noncomputable section

/-!
# Sound finite-cell assembly through whole-tail contractions

Pairwise two-cell positivity does not by itself imply positivity of a finite
cell matrix.  This module records the stronger condition that does assemble:
at every cut of an ordered cell list, the head must contract against the sum
of the entire remaining tail.

The generic two-block symbol below retains both the local Hermitian cross and
the polarized prime cross.  Its determinant criterion is support-free.  The
only support input in the finite assembly theorem is the already-proved
nonnegativity of each ratio-at-most-two diagonal cell.
-/

/-- A Bombieri test carried by some multiplicative cell of width at most two. -/
def BombieriRatioTwoCell (g : BombieriTest) : Prop :=
  ∃ a b : ℝ,
    0 < a ∧ a ≤ b ∧
      tsupport g ⊆ Set.Icc a b ∧ b / a ≤ 2

/-- The compiled restricted-support theorem supplies the diagonal sign for
every ratio-at-most-two cell. -/
theorem bombieriFunctional_quadratic_re_nonneg_of_ratioTwoCell
    (g : BombieriTest) (hg : BombieriRatioTwoCell g) :
    0 ≤ (bombieriFunctional (bombieriQuadraticTest g)).re := by
  obtain ⟨a, b, ha, hab, hsupport, hratio⟩ := hg
  exact bombieriFunctional_quadratic_re_nonneg_of_ratio_le_two
    g ha hab hsupport hratio

/-- The complete global cross of two arbitrary blocks.  The prime part is
polarized in both real scalar directions, so this is a genuinely complex
Hermitian cross coordinate. -/
def bombieriTwoBlockGlobalCrossSymbol (f g : BombieriTest) : ℂ :=
  bombieriLocalCriticalForm f g - bombieriPolarizedPrimeCross f g

/-- The generic symbol specializes definitionally to the existing adjacent
factor-two two-seed symbol. -/
theorem bombieriTwoBlockGlobalCrossSymbol_dilation_two
    (f g : BombieriTest) :
    bombieriTwoBlockGlobalCrossSymbol f
        (normalizedDilation 2 (by norm_num) g) =
      factorTwoTwoSeedGlobalCrossSymbol f g := by
  rfl

/-- Exact mixed functional for an arbitrary second block and complex scalar. -/
theorem bombieriFunctional_quadraticCross_twoBlock_re
    (f g : BombieriTest) (c : ℂ) :
    (bombieriFunctional
      (bombieriQuadraticCrossTest f (c • g))).re =
      2 * (c * bombieriTwoBlockGlobalCrossSymbol f g).re := by
  rw [bombieriFunctional_quadraticCross_eq_localCross_sub_prime]
  simp only [Complex.sub_re]
  rw [bombieriLocalCriticalForm_smul_cross_re,
    primeSum_bombieriQuadraticCrossTest_smul_re_eq_polarized]
  unfold bombieriTwoBlockGlobalCrossSymbol
  simp only [mul_sub, Complex.sub_re]

/-- Exact unequal-diagonal Hermitian expansion for two arbitrary blocks. -/
theorem bombieriFunctional_twoBlock_re
    (f g : BombieriTest) (c : ℂ) :
    (bombieriFunctional
      (bombieriQuadraticTest (f + c • g))).re =
      (bombieriFunctional (bombieriQuadraticTest f)).re +
        Complex.normSq c *
          (bombieriFunctional (bombieriQuadraticTest g)).re +
        2 * (c * bombieriTwoBlockGlobalCrossSymbol f g).re := by
  rw [bombieriFunctional_quadratic_add_eq_diagonal_add_cross,
    bombieriFunctional_quadratic_smul]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  rw [bombieriFunctional_quadraticCross_twoBlock_re]
  simp only [Complex.mul_re]

/-- Whole-block positivity in every complex scalar direction is exactly the
unequal-diagonal contraction.  This is the higher/operator condition used at
each cut of the finite-cell assembly below. -/
theorem bombieriFunctional_twoBlock_nonneg_iff
    (f g : BombieriTest)
    (hf : 0 ≤ (bombieriFunctional (bombieriQuadraticTest f)).re)
    (hg : 0 ≤ (bombieriFunctional (bombieriQuadraticTest g)).re) :
    (∀ c : ℂ,
      0 ≤ (bombieriFunctional
        (bombieriQuadraticTest (f + c • g))).re) ↔
      Complex.normSq (bombieriTwoBlockGlobalCrossSymbol f g) ≤
        (bombieriFunctional (bombieriQuadraticTest f)).re *
          (bombieriFunctional (bombieriQuadraticTest g)).re := by
  simpa only [bombieriFunctional_twoBlock_re, twoSeedHermitianValue] using
    twoSeedHermitian_nonneg_iff
      (bombieriFunctional (bombieriQuadraticTest f)).re
      (bombieriFunctional (bombieriQuadraticTest g)).re
      (bombieriTwoBlockGlobalCrossSymbol f g) hf hg

/-- Recursive whole-tail Schur condition.  Unlike pairwise two-cell
contractions, the cross at each step sees the sum of every later cell. -/
def BombieriCellChainContraction : List BombieriTest → Prop
  | [] => True
  | [_] => True
  | f :: g :: rest =>
      BombieriCellChainContraction (g :: rest) ∧
        Complex.normSq
            (bombieriTwoBlockGlobalCrossSymbol f (g :: rest).sum) ≤
          (bombieriFunctional (bombieriQuadraticTest f)).re *
            (bombieriFunctional
              (bombieriQuadraticTest (g :: rest).sum)).re

private theorem bombieriFunctional_quadratic_zero :
    bombieriFunctional (bombieriQuadraticTest (0 : BombieriTest)) = 0 := by
  simpa using bombieriFunctional_quadratic_smul (0 : ℂ) (0 : BombieriTest)

/-- Finite ratio-two cells assemble whenever every head contracts against its
whole remaining tail.  Pairwise principal-block information alone is not used. -/
theorem bombieriFunctional_quadratic_re_nonneg_of_cellChain
    (cells : List BombieriTest) :
    (∀ g ∈ cells, BombieriRatioTwoCell g) →
      BombieriCellChainContraction cells →
        0 ≤ (bombieriFunctional
          (bombieriQuadraticTest cells.sum)).re := by
  induction cells with
  | nil =>
      intro _hcells _hchain
      rw [List.sum_nil, bombieriFunctional_quadratic_zero]
      exact le_rfl
  | cons f tail ih =>
      intro hcells hchain
      cases tail with
      | nil =>
          simpa only [List.sum_singleton] using
            bombieriFunctional_quadratic_re_nonneg_of_ratioTwoCell f
              (hcells f (by simp))
      | cons g rest =>
          have hf :
              0 ≤ (bombieriFunctional (bombieriQuadraticTest f)).re :=
            bombieriFunctional_quadratic_re_nonneg_of_ratioTwoCell f
              (hcells f (by simp))
          have htailCells :
              ∀ h ∈ g :: rest, BombieriRatioTwoCell h := by
            intro h hh
            exact hcells h (List.mem_cons_of_mem f hh)
          change
            BombieriCellChainContraction (g :: rest) ∧
              Complex.normSq
                  (bombieriTwoBlockGlobalCrossSymbol f (g :: rest).sum) ≤
                (bombieriFunctional (bombieriQuadraticTest f)).re *
                  (bombieriFunctional
                    (bombieriQuadraticTest (g :: rest).sum)).re at hchain
          have htail :
              0 ≤ (bombieriFunctional
                (bombieriQuadraticTest (g :: rest).sum)).re :=
            ih htailCells hchain.1
          have hall :=
            (bombieriFunctional_twoBlock_nonneg_iff
              f (g :: rest).sum hf htail).2 hchain.2
          simpa only [List.sum_cons, one_smul] using hall 1

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
