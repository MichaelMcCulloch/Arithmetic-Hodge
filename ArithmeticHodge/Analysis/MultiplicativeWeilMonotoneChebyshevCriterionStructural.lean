import ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneCutChebyshevFrontierStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilRealMonotoneTailConeCriterionStructural

set_option autoImplicit false

open Complex Real
open scoped BigOperators

namespace ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneChebyshevCriterionStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilMonotoneCutChebyshevFrontierStructural
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilRealMonotonePropagationCriterionStructural
open MultiplicativeWeilRealMonotoneTailConeCriterionStructural

/-!
# An exact corrected-Chebyshev criterion for RH

The monotone-cut criterion is now made completely explicit.  Its only
unproved assertion is a uniform lower bound for a finite row consisting of
two neighboring Gram entries and the corrected Chebyshev contributions of
all farther cells.  This file proves that assertion equivalent to the
one-step propagation property, and hence equivalent to RH.

This is a characterization, not an estimate: no sign is assigned to the
Chebyshev row below.
-/

/-- The full signed head--suffix row after the lag-three-and-beyond entries
have been rewritten through `psi(x) - x`. -/
def monotoneQuarterNearFarChebyshevRow
    (parent : BombieriTest) (k : ℤ) (n : ℕ) : ℝ :=
  (bombieriTwoBlockGlobalCrossSymbol
      (monotoneQuarterCell parent k)
      (monotoneQuarterCell parent (k + 1))).re +
    (bombieriTwoBlockGlobalCrossSymbol
      (monotoneQuarterCell parent k)
      (monotoneQuarterCell parent (k + 2))).re +
    ∑ i ∈ Finset.range n,
      monotoneQuarterFarChebyshevContribution
        parent k (3 + (i : ℤ))

/-- Compact support supplies a zero monotone cutoff beyond every prescribed
lattice index. -/
theorem exists_monotoneQuarterCutoff_terminal_from
    (parent : BombieriTest) (start : ℤ) :
    ∃ n : ℕ,
      monotoneQuarterCutoff parent (start + (n : ℤ)) = 0 := by
  obtain ⟨lo, N, _hleft, hterminal, _hsum, _hratio, _hsuffix⟩ :=
    exists_monotoneQuarterCell_decomposition parent
  let terminal : ℤ := lo + (N : ℤ)
  by_cases hstart : start ≤ terminal
  · let n : ℕ := Int.toNat (terminal - start)
    have hdiff : 0 ≤ terminal - start := sub_nonneg.mpr hstart
    have hn : (n : ℤ) = terminal - start := by
      exact Int.toNat_of_nonneg hdiff
    refine ⟨n, ?_⟩
    have hindex : start + (n : ℤ) = lo + (N : ℤ) := by
      rw [hn]
      dsimp only [terminal]
      ring
    rw [hindex]
    exact hterminal
  · refine ⟨0, ?_⟩
    simp only [Int.natCast_zero, add_zero]
    apply monotoneQuarterCutoff_eq_zero_of_zero_of_le parent hterminal
    dsimp only [terminal] at hstart
    exact le_of_lt (lt_of_not_ge hstart)

/-- The precise remaining lower bound.  It is required only when the inner
cutoff is already nonnegative and only through a genuinely terminal finite
suffix. -/
def BombieriRealMonotoneChebyshevRowBound : Prop :=
  ∀ parent : BombieriTest,
    bombieriConjugateTest parent = parent →
      ∀ (k : ℤ) (n : ℕ),
        monotoneQuarterCutoff parent (k + 3 + (n : ℤ)) = 0 →
        0 ≤ bombieriRealQuadraticValue
            (monotoneQuarterCutoff parent (k + 1)) →
        -(bombieriRealQuadraticValue (monotoneQuarterCell parent k) +
            bombieriRealQuadraticValue
              (monotoneQuarterCutoff parent (k + 1))) / 2 ≤
          monotoneQuarterNearFarChebyshevRow parent k n

/-- For a terminal suffix, the corrected-Chebyshev row bound is exactly
nonnegativity of the outer cutoff. -/
theorem bombieriRealQuadraticValue_cutoff_nonnegative_iff_chebyshevRowBound
    (parent : BombieriTest) (k : ℤ) (n : ℕ)
    (hterminal :
      monotoneQuarterCutoff parent (k + 3 + (n : ℤ)) = 0) :
    0 ≤ bombieriRealQuadraticValue (monotoneQuarterCutoff parent k) ↔
      -(bombieriRealQuadraticValue (monotoneQuarterCell parent k) +
          bombieriRealQuadraticValue
            (monotoneQuarterCutoff parent (k + 1))) / 2 ≤
        monotoneQuarterNearFarChebyshevRow parent k n := by
  simpa only [monotoneQuarterNearFarChebyshevRow] using
    bombieriRealQuadraticValue_cutoff_nonnegative_iff_twoNear_add_chebyshev
      parent k n hterminal

/-- The explicit Chebyshev-row assertion implies the abstract one-step
monotone propagation property. -/
theorem bombieriRealMonotoneCutPropagation_of_chebyshevRowBound
    (hrow : BombieriRealMonotoneChebyshevRowBound) :
    BombieriRealMonotoneCutPropagation := by
  intro parent hparent k hinner
  obtain ⟨n, hterminal⟩ :=
    exists_monotoneQuarterCutoff_terminal_from parent (k + 3)
  have hterminal' :
      monotoneQuarterCutoff parent (k + 3 + (n : ℤ)) = 0 := by
    simpa only [add_assoc] using hterminal
  exact
    (bombieriRealQuadraticValue_cutoff_nonnegative_iff_chebyshevRowBound
      parent k n hterminal').2
      (hrow parent hparent k n hterminal' hinner)

/-- Conversely, one-step propagation supplies every terminal
corrected-Chebyshev row bound. -/
theorem chebyshevRowBound_of_bombieriRealMonotoneCutPropagation
    (hprop : BombieriRealMonotoneCutPropagation) :
    BombieriRealMonotoneChebyshevRowBound := by
  intro parent hparent k n hterminal hinner
  exact
    (bombieriRealQuadraticValue_cutoff_nonnegative_iff_chebyshevRowBound
      parent k n hterminal).1
      (hprop parent hparent k hinner)

/-- The explicit corrected-Chebyshev row bound is neither stronger nor
weaker than the monotone propagation frontier. -/
theorem bombieriRealMonotoneCutPropagation_iff_chebyshevRowBound :
    BombieriRealMonotoneCutPropagation ↔
      BombieriRealMonotoneChebyshevRowBound := by
  exact ⟨chebyshevRowBound_of_bombieriRealMonotoneCutPropagation,
    bombieriRealMonotoneCutPropagation_of_chebyshevRowBound⟩

/-- Final closure statement: RH is equivalent to the uniform structural
lower bound for the two near entries plus the corrected Chebyshev far row. -/
theorem riemannHypothesis_iff_bombieriRealMonotoneChebyshevRowBound
    (zeros : ZetaZeroEnumeration) :
    RiemannHypothesis ↔ BombieriRealMonotoneChebyshevRowBound := by
  exact (riemannHypothesis_iff_bombieriRealMonotoneCutPropagation zeros).trans
    bombieriRealMonotoneCutPropagation_iff_chebyshevRowBound

end

end ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneChebyshevCriterionStructural
