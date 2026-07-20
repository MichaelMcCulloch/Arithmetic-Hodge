import ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellResidualDeterminantClosureStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilFiniteWindowAssemblyObstructionStructural

set_option autoImplicit false

open Complex Real

namespace ArithmeticHodge.Analysis.MultiplicativeWeilAllLengthResidualPropagationClosureStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilAllLengthResidualDeterminantSingularClosureStructural
open MultiplicativeWeilFiveCellResidualDeterminantClosureStructural
open MultiplicativeWeilFourCellResidualDeterminantStructural
open MultiplicativeWeilMonotonePrimeAtomAggregateObstructionStructural
open MultiplicativeWeilRealCutPhaseReductionStructural

/-!
# The exact residual propagation frontier beyond five cells

Once production positivity at lengths four and five is available, the
determinant-only induction has no further exceptional branch: its remaining
input is precisely the middle-orthogonal residual determinant at every length
at least six.  The first theorem below connects that tail family directly to
the compiled all-length induction and hence to the real Bombieri criterion.

The final scalar model records why the tail cannot be supplied merely by
formal overlap propagation.  At every length it has nonnegative adjacent
shorter windows and a positive middle pivot, while the middle-pivot residual
determinant is strictly reversed.  Thus any proof of the production tail must
use structure of the actual Bombieri kernel or common-parent masks beyond
shorter-window positivity.
-/

/-- Lengths four and five, followed by the genuine residual determinant at
every length at least six, supply the complete determinant-only induction.
No singular-pivot hypothesis remains: the positive interior perturbation
theorem discharges it uniformly at every length. -/
theorem inductiveResidualDeterminantOnlyClosure_of_four_five_and_tail
    (hfour : RealFiniteBlockProductionNonnegativeAtLength 4)
    (hfive : RealFiniteBlockProductionNonnegativeAtLength 5)
    (htail : ∀ n : ℕ, 6 ≤ n →
      RealFiniteBlockMiddleOrthogonalResidualDeterminantAtLength n) :
    RealFiniteBlockInductiveResidualDeterminantOnlyClosure := by
  intro n hn _hprev
  by_cases hn4 : n = 4
  · subst n
    exact fourCell_residualDeterminant_of_production hfour
  by_cases hn5 : n = 5
  · subst n
    exact fiveCell_residualDeterminant_of_production hfive
  exact htail n (by omega)

/-- After the two active low-length production problems are closed, the
tail residual determinant family is sufficient for complete real Bombieri
quadratic nonnegativity. -/
theorem bombieriRealQuadraticNonnegativity_of_four_five_and_tailResidualDeterminants
    (hfour : RealFiniteBlockProductionNonnegativeAtLength 4)
    (hfive : RealFiniteBlockProductionNonnegativeAtLength 5)
    (htail : ∀ n : ℕ, 6 ≤ n →
      RealFiniteBlockMiddleOrthogonalResidualDeterminantAtLength n) :
    BombieriRealQuadraticNonnegativity := by
  exact bombieriRealQuadraticNonnegativity_of_inductiveResidualDeterminantClosure
    ((inductiveResidualDeterminantOnlyClosure_iff_existingClosure).1
      (inductiveResidualDeterminantOnlyClosure_of_four_five_and_tail
        hfour hfive htail))

/-- Terminal form of the preceding bridge. -/
theorem riemannHypothesis_of_four_five_and_tailResidualDeterminants
    (zeros : ZetaZeroEnumeration)
    (hfour : RealFiniteBlockProductionNonnegativeAtLength 4)
    (hfive : RealFiniteBlockProductionNonnegativeAtLength 5)
    (htail : ∀ n : ℕ, 6 ≤ n →
      RealFiniteBlockMiddleOrthogonalResidualDeterminantAtLength n) :
    RiemannHypothesis := by
  exact (riemannHypothesis_iff_bombieriRealQuadraticNonnegativity zeros).2
    (bombieriRealQuadraticNonnegativity_of_four_five_and_tailResidualDeterminants
      hfour hfive htail)

/-- Under RH the residual determinant holds at every length, since the two
concrete residual tests are real and the global real Bombieri form satisfies
its ordinary two-vector Cauchy--Schwarz inequality. -/
theorem tailResidualDeterminants_of_riemannHypothesis
    (zeros : ZetaZeroEnumeration) (hRH : RiemannHypothesis) :
    ∀ n : ℕ, 6 ≤ n →
      RealFiniteBlockMiddleOrthogonalResidualDeterminantAtLength n := by
  have hglobal : BombieriRealQuadraticNonnegativity :=
    (riemannHypothesis_iff_bombieriRealQuadraticNonnegativity zeros).1 hRH
  intro n _hn parent hparent k _hMpos
  have hfixed :=
    bombieriConjugateTest_finiteBlockMiddleOrthogonalResiduals
      parent hparent k n
  exact
    bombieriTwoBlockGlobalCrossSymbol_re_sq_le_of_realQuadraticNonnegativity
      hglobal
      (finiteBlockLeftMiddleOrthogonalResidual parent k n)
      (finiteBlockRightMiddleOrthogonalResidual parent k n)
      hfixed.1 hfixed.2

/-- Consequently, conditional only on the two low production theorems now
being attacked separately, the entire `n ≥ 6` residual family is not an
extra assembly convenience: it is exactly RH. -/
theorem riemannHypothesis_iff_tailResidualDeterminants_of_four_five
    (zeros : ZetaZeroEnumeration)
    (hfour : RealFiniteBlockProductionNonnegativeAtLength 4)
    (hfive : RealFiniteBlockProductionNonnegativeAtLength 5) :
    RiemannHypothesis ↔
      ∀ n : ℕ, 6 ≤ n →
        RealFiniteBlockMiddleOrthogonalResidualDeterminantAtLength n := by
  exact ⟨tailResidualDeterminants_of_riemannHypothesis zeros,
    riemannHypothesis_of_four_five_and_tailResidualDeterminants
      zeros hfour hfive⟩

/-! ## A sharp abstract obstruction to overlap-only propagation -/

/-- The three-level slice of the width-`d+1` equicorrelation form on
`d+2` coordinates: one left endpoint, `d` equal interior coordinates, and
one right endpoint. -/
def fixedWidthThreeLevelResidualModel
    (d : ℕ) (a m e : ℝ) : ℝ :=
  (d + 1 : ℝ) * (a ^ 2 + (d : ℝ) * m ^ 2 + e ^ 2) -
    (a + (d : ℝ) * m + e) ^ 2

/-- The left shortened window is an exact square. -/
theorem fixedWidthThreeLevelResidualModel_left
    (d : ℕ) (a m : ℝ) :
    fixedWidthThreeLevelResidualModel d a m 0 =
      (d : ℝ) * (a - m) ^ 2 := by
  unfold fixedWidthThreeLevelResidualModel
  ring

/-- The right shortened window is an exact square. -/
theorem fixedWidthThreeLevelResidualModel_right
    (d : ℕ) (m e : ℝ) :
    fixedWidthThreeLevelResidualModel d 0 m e =
      (d : ℝ) * (m - e) ^ 2 := by
  unfold fixedWidthThreeLevelResidualModel
  ring

/-- Both adjacent windows of the scalar model are nonnegative. -/
theorem fixedWidthThreeLevelResidualModel_adjacent_nonnegative
    (d : ℕ) (a m e : ℝ) :
    0 ≤ fixedWidthThreeLevelResidualModel d a m 0 ∧
      0 ≤ fixedWidthThreeLevelResidualModel d 0 m e := by
  rw [fixedWidthThreeLevelResidualModel_left,
    fixedWidthThreeLevelResidualModel_right]
  exact ⟨mul_nonneg (Nat.cast_nonneg d) (sq_nonneg _),
    mul_nonneg (Nat.cast_nonneg d) (sq_nonneg _)⟩

/-- On the full all-ones vector, the first window beyond the controlled
width is strictly negative. -/
theorem fixedWidthThreeLevelResidualModel_one
    (d : ℕ) :
    fixedWidthThreeLevelResidualModel d 1 1 1 = -((d + 2 : ℕ) : ℝ) := by
  unfold fixedWidthThreeLevelResidualModel
  push_cast
  ring

/-- Exact endpoint--middle--endpoint coordinates of the model.  The two
adjacent principal minors are saturated, but the middle-pivot residual
determinant is strictly reversed by `d^2 (d+1)^2`.  This gives a structural
countermodel at every production-tail length (`d ≥ 4` corresponds to
length `d+2 ≥ 6`). -/
theorem fixedWidthThreeLevelResidualModel_strict_residualReversal
    (d : ℕ) (hd : 1 ≤ d) :
    let A : ℝ := d
    let M : ℝ := d
    let E : ℝ := d
    let U : ℝ := -d
    let V : ℝ := -d
    let X : ℝ := -1
    0 < M ∧ U ^ 2 ≤ A * M ∧ V ^ 2 ≤ M * E ∧
      (A * M - U ^ 2) * (M * E - V ^ 2) <
        (M * X - U * V) ^ 2 := by
  dsimp only
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (Nat.zero_lt_of_lt hd)
  constructor
  · exact hdpos
  constructor
  · nlinarith [sq_nonneg (d : ℝ)]
  constructor
  · nlinarith [sq_nonneg (d : ℝ)]
  · have hdp : 0 < (d : ℝ) * ((d : ℝ) + 1) := by positivity
    nlinarith [sq_pos_of_pos hdp]

/-- Uniform tail version: at every length at least six there is an abstract
three-block quadratic with positive middle pivot and nonnegative adjacent
shorter windows whose residual determinant fails strictly. -/
theorem exists_overlapPositive_residualDeterminantReversal_at_tailLength
    (n : ℕ) (hn : 6 ≤ n) :
    ∃ d : ℕ, d + 2 = n ∧ 1 ≤ d ∧
      (∀ a m : ℝ,
        0 ≤ fixedWidthThreeLevelResidualModel d a m 0) ∧
      (∀ m e : ℝ,
        0 ≤ fixedWidthThreeLevelResidualModel d 0 m e) ∧
      fixedWidthThreeLevelResidualModel d 1 1 1 < 0 ∧
      (let A : ℝ := d
       let M : ℝ := d
       let E : ℝ := d
       let U : ℝ := -d
       let V : ℝ := -d
       let X : ℝ := -1
       0 < M ∧ U ^ 2 ≤ A * M ∧ V ^ 2 ≤ M * E ∧
         (A * M - U ^ 2) * (M * E - V ^ 2) <
           (M * X - U * V) ^ 2) := by
  refine ⟨n - 2, by omega, by omega, ?_, ?_, ?_, ?_⟩
  · intro a m
    exact (fixedWidthThreeLevelResidualModel_adjacent_nonnegative
      (n - 2) a m 0).1
  · intro m e
    exact (fixedWidthThreeLevelResidualModel_adjacent_nonnegative
      (n - 2) 0 m e).2
  · rw [fixedWidthThreeLevelResidualModel_one]
    exact neg_lt_zero.mpr (by positivity)
  exact fixedWidthThreeLevelResidualModel_strict_residualReversal
    (n - 2) (by omega)

end

end ArithmeticHodge.Analysis.MultiplicativeWeilAllLengthResidualPropagationClosureStructural
