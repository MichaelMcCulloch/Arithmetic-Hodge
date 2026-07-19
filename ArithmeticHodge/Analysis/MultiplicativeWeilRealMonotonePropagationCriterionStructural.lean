import ArithmeticHodge.Analysis.MultiplicativeWeilRealCutPhaseReductionStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneQuarterPartitionStructural

set_option autoImplicit false

open Complex Real

namespace ArithmeticHodge.Analysis.MultiplicativeWeilRealMonotonePropagationCriterionStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilRealCutPhaseReductionStructural

/-!
# Real monotone-cut propagation is the weakest direct assembly target

The recursive determinant/cut-pencil condition used by generic finite-cell
assembly is stronger than needed for the selected monotone partition.  After
reducing arbitrary Bombieri tests to their real and imaginary parts, it is
enough to propagate nonnegativity one boundary cutoff at a time:

`Q(C_(k+1)(g)) >= 0 -> Q(C_k(g)) >= 0`.

The terminal cutoff is zero and the initial cutoff is the original parent, so
this one-phase implication closes by finite backward induction.  Conversely,
failure of RH produces a real-valued parent with a first adjacent boundary at
which this propagation fails.  This is strictly a route simplification: it
removes the unnecessary demand for every complex scalar pencil, while not
claiming the remaining propagation inequality itself.
-/

/-- Real quadratic value of one Bombieri test. -/
def bombieriRealQuadraticValue (g : BombieriTest) : ℝ :=
  (bombieriFunctional (bombieriQuadraticTest g)).re

/-- The exact one-step property required by direct monotone-cut assembly. -/
def BombieriRealMonotoneCutPropagation : Prop :=
  ∀ parent : BombieriTest,
    bombieriConjugateTest parent = parent →
      ∀ k : ℤ,
        0 ≤ bombieriRealQuadraticValue
            (monotoneQuarterCutoff parent (k + 1)) →
          0 ≤ bombieriRealQuadraticValue
            (monotoneQuarterCutoff parent k)

private theorem bombieriRealQuadraticValue_zero :
    bombieriRealQuadraticValue (0 : BombieriTest) = 0 := by
  unfold bombieriRealQuadraticValue
  have h := bombieriFunctional_quadratic_smul
    (0 : ℂ) (0 : BombieriTest)
  simpa only [zero_smul, Complex.normSq_zero, Complex.ofReal_zero,
    zero_mul, Complex.zero_re] using congrArg Complex.re h

/-- Iterating the one-step property backwards from any later cutoff. -/
theorem bombieriRealQuadraticValue_monotoneCutoff_nonnegative_of_later
    (hprop : BombieriRealMonotoneCutPropagation)
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent)
    (lo : ℤ) :
    ∀ n : ℕ,
      0 ≤ bombieriRealQuadraticValue
        (monotoneQuarterCutoff parent (lo + (n : ℤ))) →
      0 ≤ bombieriRealQuadraticValue
        (monotoneQuarterCutoff parent lo) := by
  intro n
  induction n generalizing lo with
  | zero =>
      intro h
      have hindex : lo + ((0 : ℕ) : ℤ) = lo := by norm_num
      rw [hindex] at h
      exact h
  | succ n ih =>
      intro hlater
      have hindex : lo + ((n + 1 : ℕ) : ℤ) = (lo + 1) + (n : ℤ) := by
        norm_num
        ring
      rw [hindex] at hlater
      have hnext : 0 ≤ bombieriRealQuadraticValue
          (monotoneQuarterCutoff parent (lo + 1)) :=
        ih (lo + 1) hlater
      exact hprop parent hparent lo hnext

/-- The one-step real cutoff propagation property is sufficient for global
Bombieri positivity and hence RH. -/
theorem riemannHypothesis_of_bombieriRealMonotoneCutPropagation
    (zeros : ZetaZeroEnumeration)
    (hprop : BombieriRealMonotoneCutPropagation) :
    RiemannHypothesis := by
  apply
    (riemannHypothesis_iff_bombieriRealQuadraticNonnegativity zeros).2
  intro parent hparent
  obtain ⟨lo, n, hleft, hright, _hsum, _hratio, _hsuffix⟩ :=
    exists_monotoneQuarterCell_decomposition parent
  have hterminal : 0 ≤ bombieriRealQuadraticValue
      (monotoneQuarterCutoff parent (lo + (n : ℤ))) := by
    rw [hright, bombieriRealQuadraticValue_zero]
  have hinitial :=
    bombieriRealQuadraticValue_monotoneCutoff_nonnegative_of_later
      hprop parent hparent lo n hterminal
  simpa only [bombieriRealQuadraticValue, hleft] using hinitial

/-- Under RH every cutoff is already nonnegative, so the propagation property
also holds.  Hence this is the exact weakest universal one-step target exposed
by the canonical monotone partition. -/
theorem riemannHypothesis_iff_bombieriRealMonotoneCutPropagation
    (zeros : ZetaZeroEnumeration) :
    RiemannHypothesis ↔ BombieriRealMonotoneCutPropagation := by
  constructor
  · intro hRH parent _hparent k _hinner
    exact
      (riemannHypothesis_iff_bombieriQuadratic_re_nonnegative zeros).1 hRH
        (monotoneQuarterCutoff parent k)
  · exact riemannHypothesis_of_bombieriRealMonotoneCutPropagation zeros

/-- A concrete adjacent boundary where nonnegativity fails to propagate. -/
def BombieriRealMonotoneCutPropagationFailure : Prop :=
  ∃ (parent : BombieriTest) (k : ℤ),
    bombieriConjugateTest parent = parent ∧
      0 ≤ bombieriRealQuadraticValue
        (monotoneQuarterCutoff parent (k + 1)) ∧
      bombieriRealQuadraticValue
        (monotoneQuarterCutoff parent k) < 0

private theorem exists_adjacent_neg_to_nonnegative
    (q : ℕ → ℝ) :
    ∀ n : ℕ, q 0 < 0 → 0 ≤ q n →
      ∃ j : ℕ, j < n ∧ q j < 0 ∧ 0 ≤ q (j + 1) := by
  intro n
  induction n with
  | zero =>
      intro hneg hnonneg
      exact (not_lt_of_ge hnonneg hneg).elim
  | succ n ih =>
      intro hzero hlast
      by_cases hn : 0 ≤ q n
      · obtain ⟨j, hjn, hjneg, hjsucc⟩ := ih hzero hn
        exact ⟨j, hjn.trans (Nat.lt_succ_self n), hjneg, hjsucc⟩
      · refine ⟨n, Nat.lt_succ_self n, lt_of_not_ge hn, ?_⟩
        simpa only [Nat.succ_eq_add_one] using hlast

/-- Dual localization: if RH fails, some real-valued parent has a single
adjacent monotone boundary whose inner cutoff is nonnegative but whose outer
cutoff is negative.  Conversely, such a boundary is already a negative
Bombieri witness. -/
theorem not_riemannHypothesis_iff_realMonotoneCutPropagationFailure
    (zeros : ZetaZeroEnumeration) :
    ¬ RiemannHypothesis ↔ BombieriRealMonotoneCutPropagationFailure := by
  constructor
  · intro hnot
    have hnotReal : ¬ BombieriRealQuadraticNonnegativity := by
      intro hreal
      exact hnot
        ((riemannHypothesis_iff_bombieriRealQuadraticNonnegativity zeros).2
          hreal)
    unfold BombieriRealQuadraticNonnegativity at hnotReal
    push_neg at hnotReal
    obtain ⟨parent, hparent, hnegative⟩ := hnotReal
    obtain ⟨lo, n, hleft, hright, _hsum, _hratio, _hsuffix⟩ :=
      exists_monotoneQuarterCell_decomposition parent
    let q : ℕ → ℝ := fun j ↦ bombieriRealQuadraticValue
      (monotoneQuarterCutoff parent (lo + (j : ℤ)))
    have hqzero : q 0 < 0 := by
      dsimp only [q]
      simpa only [Int.natCast_zero, add_zero,
        bombieriRealQuadraticValue, hleft] using hnegative
    have hqn : 0 ≤ q n := by
      dsimp only [q]
      rw [hright, bombieriRealQuadraticValue_zero]
    obtain ⟨j, hjn, hjneg, hjsucc⟩ :=
      exists_adjacent_neg_to_nonnegative q n hqzero hqn
    refine ⟨parent, lo + (j : ℤ), hparent, ?_, hjneg⟩
    have hindex : lo + (j : ℤ) + 1 = lo + ((j + 1 : ℕ) : ℤ) := by
      norm_num
      ring
    rw [hindex]
    exact hjsucc
  · rintro ⟨parent, k, _hparent, _hinner, houter⟩ hRH
    have hnonnegative :=
      (riemannHypothesis_iff_bombieriQuadratic_re_nonnegative zeros).1 hRH
        (monotoneQuarterCutoff parent k)
    exact (not_lt_of_ge hnonnegative) houter

end

end ArithmeticHodge.Analysis.MultiplicativeWeilRealMonotonePropagationCriterionStructural
