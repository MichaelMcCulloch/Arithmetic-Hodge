import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowStaticSplitPositive
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4Schur

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixStaticPlusObstruction

noncomputable section

open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowStaticSplitPositive
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseLowSchur

/-!
# The inherited thin-plus obstruction in the six-mode static form

The six-mode static split extends the earlier four-mode split by adjoining
the `P₄/P₅` coordinates.  Restricting those new coordinates to zero recovers
the old split exactly.  Consequently, strict positivity of the positive
six-mode form would already prove the unresolved four-mode thin-plus Cauchy
gate, and hence its equivalent full-series domination statement.

This module records only that structural obstruction.  It makes no claim that
the six-mode form is positive and contains no projective-gate reduction.
-/

/-! ## The six-mode static extension -/

/-- The signed endpoint quadratic on the even `P₀/P₂/P₄` plane. -/
def factorTwoIntrinsicSixStaticEven
    (sigma c0 c2 c4 : ℝ) : ℝ :=
  factorTwoStructuralPhaseLow00 sigma * c0 ^ 2 +
    2 * factorTwoStructuralPhaseLow02 sigma * c0 * c2 +
    factorTwoStructuralPhaseLow22 sigma * c2 ^ 2 +
    2 * c4 *
      (c0 * factorTwoIntrinsicFourP45Cross04 sigma +
        c2 * factorTwoIntrinsicFourP45Cross24 sigma) +
    factorTwoIntrinsicP4PhaseDiagonal sigma * c4 ^ 2

/-- The oppositely signed endpoint quadratic on the odd `P₁/P₃/P₅` plane. -/
def factorTwoIntrinsicSixStaticOdd
    (sigma c1 c3 c5 : ℝ) : ℝ :=
  factorTwoIntrinsicOddPhaseQuadratic (-sigma) c1 c3 +
    2 * c5 *
      (c1 * factorTwoIntrinsicFourP45Cross15 (-sigma) +
        c3 * factorTwoIntrinsicFourP45Cross35 (-sigma)) +
    factorTwoIntrinsicP5PhaseDiagonal (-sigma) * c5 ^ 2

/-- The complete phase-free alternating row between the two parity planes. -/
def factorTwoIntrinsicSixStaticAlternating
    (c0 c2 c4 c1 c3 c5 : ℝ) : ℝ :=
  c0 * (factorTwoIntrinsicAlternating01 * c1 +
      factorTwoIntrinsicAlternating03 * c3 +
      factorTwoIntrinsicFourP45Cross05 * c5) +
    c2 * (factorTwoIntrinsicAlternating21 * c1 +
      factorTwoIntrinsicAlternating23 * c3 +
      factorTwoIntrinsicFourP45Cross25 * c5) +
    c4 * (factorTwoIntrinsicFourP45Cross41 * c1 +
      factorTwoIntrinsicFourP45Cross43 * c3 +
      factorTwoIntrinsicP45Alternating * c5)

/-- The static extension of the four-mode split to all six intrinsic modes. -/
def factorTwoIntrinsicSixStaticSplit
    (sigma c0 c2 c4 c1 c3 c5 : ℝ) : ℝ :=
  factorTwoIntrinsicSixStaticEven sigma c0 c2 c4 +
    factorTwoIntrinsicSixStaticOdd sigma c1 c3 c5 +
    factorTwoIntrinsicSixStaticAlternating c0 c2 c4 c1 c3 c5

/-- Strict positivity of a six-mode static split away from the origin. -/
def FactorTwoIntrinsicSixStaticPos (sigma : ℝ) : Prop :=
  ∀ c0 c2 c4 c1 c3 c5 : ℝ,
    c0 ≠ 0 ∨ c2 ≠ 0 ∨ c4 ≠ 0 ∨ c1 ≠ 0 ∨ c3 ≠ 0 ∨ c5 ≠ 0 →
      0 < factorTwoIntrinsicSixStaticSplit sigma c0 c2 c4 c1 c3 c5

/-! ## Exact inherited obstruction -/

/-- On the original four intrinsic modes, the six-mode static split is
literally the older thin static split. -/
theorem factorTwoIntrinsicSixStaticSplit_restrict_low
    (sigma c0 c2 c1 c3 : ℝ) :
    factorTwoIntrinsicSixStaticSplit sigma c0 c2 0 c1 c3 0 =
      factorTwoIntrinsicStaticSplit sigma c0 c2 c1 c3 := by
  unfold factorTwoIntrinsicSixStaticSplit
    factorTwoIntrinsicSixStaticEven
    factorTwoIntrinsicSixStaticOdd
    factorTwoIntrinsicSixStaticAlternating
    factorTwoIntrinsicStaticSplit
    factorTwoIntrinsicStaticEvenQuadratic
    factorTwoIntrinsicStaticOddQuadratic
    factorTwoIntrinsicStaticAlternating
    factorTwoIntrinsicAlternatingRow0
    factorTwoIntrinsicAlternatingRow2
  ring

/-- Strict positivity of the positive six-mode extension would discharge the
pre-existing four-mode thin-plus Cauchy gate. -/
theorem factorTwoIntrinsicStaticPlusCauchy_of_sixStaticPos
    (hplus : FactorTwoIntrinsicSixStaticPos 1) :
    FactorTwoIntrinsicStaticCauchy 1 := by
  rw [← factorTwoIntrinsicStaticPlus_nonneg_iff_cauchy]
  intro c0 c2 c1 c3
  by_cases hne : c0 ≠ 0 ∨ c2 ≠ 0 ∨ c1 ≠ 0 ∨ c3 ≠ 0
  · have hsix : c0 ≠ 0 ∨ c2 ≠ 0 ∨ (0 : ℝ) ≠ 0 ∨
        c1 ≠ 0 ∨ c3 ≠ 0 ∨ (0 : ℝ) ≠ 0 := by
      rcases hne with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    have h := hplus c0 c2 0 c1 c3 0 hsix
    rw [factorTwoIntrinsicSixStaticSplit_restrict_low] at h
    exact h.le
  · push_neg at hne
    rcases hne with ⟨rfl, rfl, rfl, rfl⟩
    simp [factorTwoIntrinsicStaticSplit,
      factorTwoIntrinsicStaticEvenQuadratic,
      factorTwoIntrinsicStaticOddQuadratic,
      factorTwoIntrinsicStaticAlternating,
      factorTwoIntrinsicOddPhaseQuadratic]

/-- The same inherited obstruction in the exact full-series normal form. -/
theorem factorTwoIntrinsicStaticPlusFullSeriesDomination_of_sixStaticPos
    (hplus : FactorTwoIntrinsicSixStaticPos 1) :
    FactorTwoIntrinsicStaticPlusFullSeriesDomination :=
  factorTwoIntrinsicStaticPlusCauchy_iff_fullSeriesDomination.mp
    (factorTwoIntrinsicStaticPlusCauchy_of_sixStaticPos hplus)

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixStaticPlusObstruction
