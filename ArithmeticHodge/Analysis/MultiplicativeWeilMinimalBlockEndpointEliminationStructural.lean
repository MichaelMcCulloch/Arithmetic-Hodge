import ArithmeticHodge.Analysis.MultiplicativeWeilMinimalNegativeBlockStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneCutChebyshevFrontierStructural

set_option autoImplicit false

open Complex Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.MultiplicativeWeilMinimalBlockEndpointEliminationStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilMinimalNegativeBlockStructural
open MultiplicativeWeilMonotoneCutChebyshevFrontierStructural
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural
open MultiplicativeWeilRealMonotonePropagationCriterionStructural

/-!
# Endpoint elimination for support-minimal negative blocks

Removing the first cell from a finite block leaves one signed row.  Its first
two entries are the neighboring Gram crosses, while every later entry has the
exact corrected-Chebyshev representation.  This gives an exact recurrence for
blocks of every length at least three and turns support-minimal negativity into
a strict failure of an explicit finite Schur row.

There is no positivity assumption on the corrected-Chebyshev terms here.  The
point is to identify, without a cutoff-to-infinity or a finite computation,
the all-length obstruction that any negative block must exhibit.
-/

/-- Physical lattice index of the first cell of a finite block. -/
def monotoneQuarterFiniteBlockBase (lo : ℤ) (start : ℕ) : ℤ :=
  lo + (start : ℤ)

private theorem monotoneQuarterFiniteBlock_eq_base_sum
    (parent : BombieriTest) (lo : ℤ) (start len : ℕ) :
    monotoneQuarterFiniteBlock parent lo start len =
      ∑ i ∈ Finset.range len,
        monotoneQuarterCell parent
          (monotoneQuarterFiniteBlockBase lo start + (i : ℤ)) := by
  classical
  unfold monotoneQuarterFiniteBlock monotoneQuarterFiniteBlockBase
  apply Finset.sum_congr rfl
  intro i _hi
  congr 1
  push_cast
  ring

@[simp] theorem monotoneQuarterFiniteBlock_one
    (parent : BombieriTest) (lo : ℤ) (start : ℕ) :
    monotoneQuarterFiniteBlock parent lo start 1 =
      monotoneQuarterCell parent
        (monotoneQuarterFiniteBlockBase lo start) := by
  rw [monotoneQuarterFiniteBlock_eq_base_sum]
  simp

/-- The block after its first endpoint consists of the two near cells and a
far tail of arbitrary finite length. -/
theorem monotoneQuarterFiniteBlock_endpointSuffix_eq_twoNear_add_farTail
    (parent : BombieriTest) (lo : ℤ) (start n : ℕ) :
    monotoneQuarterFiniteBlock parent lo (start + 1) (2 + n) =
      monotoneQuarterCell parent
          (monotoneQuarterFiniteBlockBase lo start + 1) +
        monotoneQuarterCell parent
          (monotoneQuarterFiniteBlockBase lo start + 2) +
        monotoneQuarterFarTail parent
          (monotoneQuarterFiniteBlockBase lo start) n := by
  classical
  let k : ℤ := monotoneQuarterFiniteBlockBase lo start
  let f : ℕ → BombieriTest := fun i ↦
    monotoneQuarterCell parent (k + 1 + (i : ℤ))
  have hblock : monotoneQuarterFiniteBlock parent lo (start + 1) (2 + n) =
      ∑ i ∈ Finset.range (2 + n), f i := by
    rw [monotoneQuarterFiniteBlock_eq_base_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    dsimp only [f, k, monotoneQuarterFiniteBlockBase]
    congr 1
    push_cast
    ring
  have hsum := Finset.sum_range_add f 2 n
  rw [hblock, hsum]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add]
  dsimp only [f, k]
  congr 1
  · congr 1 <;> ring_nf
  · unfold monotoneQuarterFarTail
    apply Finset.sum_congr rfl
    intro i _hi
    congr 1
    push_cast
    ring_nf

/-- The explicit endpoint row for a block of length `3 + n`. -/
def monotoneQuarterFiniteEndpointChebyshevRow
    (parent : BombieriTest) (lo : ℤ) (start n : ℕ) : ℝ :=
  (bombieriTwoBlockGlobalCrossSymbol
      (monotoneQuarterCell parent
        (monotoneQuarterFiniteBlockBase lo start))
      (monotoneQuarterCell parent
        (monotoneQuarterFiniteBlockBase lo start + 1))).re +
    (bombieriTwoBlockGlobalCrossSymbol
      (monotoneQuarterCell parent
        (monotoneQuarterFiniteBlockBase lo start))
      (monotoneQuarterCell parent
        (monotoneQuarterFiniteBlockBase lo start + 2))).re +
    ∑ i ∈ Finset.range n,
      monotoneQuarterFarChebyshevContribution parent
        (monotoneQuarterFiniteBlockBase lo start) (3 + (i : ℤ))

/-- The finite corrected-Chebyshev row is exactly the complete cross between
the removed endpoint and the remaining block. -/
theorem monotoneQuarterFiniteBlock_endpointCross_re_eq_chebyshevRow
    (parent : BombieriTest) (lo : ℤ) (start n : ℕ) :
    (bombieriTwoBlockGlobalCrossSymbol
      (monotoneQuarterFiniteBlock parent lo start 1)
      (monotoneQuarterFiniteBlock parent lo (start + 1) (2 + n))).re =
        monotoneQuarterFiniteEndpointChebyshevRow parent lo start n := by
  rw [monotoneQuarterFiniteBlock_one,
    monotoneQuarterFiniteBlock_endpointSuffix_eq_twoNear_add_farTail,
    bombieriTwoBlockGlobalCrossSymbol_add_right,
    bombieriTwoBlockGlobalCrossSymbol_add_right,
    Complex.add_re, Complex.add_re,
    monotoneQuarterCell_farTail_globalCross_re_eq_sum]
  rfl

/-- Exact endpoint-removal recurrence for every block of length at least
three. -/
theorem bombieriRealQuadraticValue_finiteBlock_three_add_eq_endpointRecurrence
    (parent : BombieriTest) (lo : ℤ) (start n : ℕ) :
    bombieriRealQuadraticValue
        (monotoneQuarterFiniteBlock parent lo start (3 + n)) =
      bombieriRealQuadraticValue
          (monotoneQuarterFiniteBlock parent lo start 1) +
        bombieriRealQuadraticValue
          (monotoneQuarterFiniteBlock parent lo (start + 1) (2 + n)) +
        2 * monotoneQuarterFiniteEndpointChebyshevRow parent lo start n := by
  have hsplit := monotoneQuarterFiniteBlock_eq_prefix_add_suffix
    parent lo start (3 + n) 1 (by omega)
  have hlen : 3 + n - 1 = 2 + n := by omega
  rw [hsplit, hlen, bombieriRealQuadraticValue_add,
    monotoneQuarterFiniteBlock_endpointCross_re_eq_chebyshevRow]

/-- Endpoint elimination is equivalent to the arithmetic-mean lower bound
for the explicit corrected-Chebyshev row. -/
theorem bombieriRealQuadraticValue_finiteBlock_three_add_nonnegative_iff
    (parent : BombieriTest) (lo : ℤ) (start n : ℕ) :
    0 ≤ bombieriRealQuadraticValue
        (monotoneQuarterFiniteBlock parent lo start (3 + n)) ↔
      -(bombieriRealQuadraticValue
            (monotoneQuarterFiniteBlock parent lo start 1) +
          bombieriRealQuadraticValue
            (monotoneQuarterFiniteBlock parent lo (start + 1) (2 + n))) / 2 ≤
        monotoneQuarterFiniteEndpointChebyshevRow parent lo start n := by
  rw [bombieriRealQuadraticValue_finiteBlock_three_add_eq_endpointRecurrence]
  constructor <;> intro h <;> linarith

private theorem nonnegative_of_schur
    {L R X : ℝ} (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hschur : X ^ 2 ≤ L * R) :
    0 ≤ L + R + 2 * X := by
  nlinarith [sq_nonneg (L - R), sq_nonneg (L + R + 2 * X)]

/-- A genuine Schur bound on the explicit finite endpoint row closes the
endpoint-removal step. -/
theorem bombieriRealQuadraticValue_finiteBlock_three_add_nonnegative_of_schur
    (parent : BombieriTest) (lo : ℤ) (start n : ℕ)
    (hhead : 0 ≤ bombieriRealQuadraticValue
      (monotoneQuarterFiniteBlock parent lo start 1))
    (htail : 0 ≤ bombieriRealQuadraticValue
      (monotoneQuarterFiniteBlock parent lo (start + 1) (2 + n)))
    (hschur :
      monotoneQuarterFiniteEndpointChebyshevRow parent lo start n ^ 2 ≤
        bombieriRealQuadraticValue
            (monotoneQuarterFiniteBlock parent lo start 1) *
          bombieriRealQuadraticValue
            (monotoneQuarterFiniteBlock parent lo (start + 1) (2 + n))) :
    0 ≤ bombieriRealQuadraticValue
      (monotoneQuarterFiniteBlock parent lo start (3 + n)) := by
  rw [bombieriRealQuadraticValue_finiteBlock_three_add_eq_endpointRecurrence]
  exact nonnegative_of_schur hhead htail hschur

/-- Every support-minimal negative block, at every possible length, forces a
strict arithmetic-mean failure in its exact finite corrected-Chebyshev
endpoint row. -/
theorem supportMinimalNegativeMonotoneBlock_endpointChebyshevRow_lt
    {parent : BombieriTest} {lo : ℤ} {N start len : ℕ}
    (hmin : IsSupportMinimalNegativeMonotoneBlock
      parent lo N start len) :
    monotoneQuarterFiniteEndpointChebyshevRow parent lo start (len - 3) <
      -(bombieriRealQuadraticValue
            (monotoneQuarterFiniteBlock parent lo start 1) +
          bombieriRealQuadraticValue
            (monotoneQuarterFiniteBlock parent lo (start + 1) (len - 1))) / 2 := by
  have hlen := four_le_length_of_supportMinimalNegativeMonotoneBlock hmin
  have hshape : 3 + (len - 3) = len := by omega
  have htailShape : 2 + (len - 3) = len - 1 := by omega
  have hrec := bombieriRealQuadraticValue_finiteBlock_three_add_eq_endpointRecurrence
    parent lo start (len - 3)
  rw [hshape, htailShape] at hrec
  have hnegative := hmin.negative
  rw [hrec] at hnegative
  linarith

/-- The same endpoint row also strictly reverses the Schur determinant. -/
theorem supportMinimalNegativeMonotoneBlock_endpointChebyshevRow_schur_reversed
    {parent : BombieriTest} {lo : ℤ} {N start len : ℕ}
    (hmin : IsSupportMinimalNegativeMonotoneBlock
      parent lo N start len) :
    bombieriRealQuadraticValue
          (monotoneQuarterFiniteBlock parent lo start 1) *
        bombieriRealQuadraticValue
          (monotoneQuarterFiniteBlock parent lo (start + 1) (len - 1)) <
      monotoneQuarterFiniteEndpointChebyshevRow parent lo start (len - 3) ^ 2 := by
  have hconstraints :=
    supportMinimalNegativeMonotoneBlock_leftEndpoint_constraints hmin
  have hcross :=
    monotoneQuarterFiniteBlock_endpointCross_re_eq_chebyshevRow
      parent lo start (len - 3)
  have hlen := four_le_length_of_supportMinimalNegativeMonotoneBlock hmin
  have htailShape : 2 + (len - 3) = len - 1 := by omega
  rw [htailShape] at hcross
  have hdet := hconstraints.determinant_strictly_reversed
  rw [hcross] at hdet
  exact hdet

/-! ## Simultaneous removal of both endpoints -/

private theorem bombieriRealQuadraticValue_threeTerm_overlap
    (left middle right : BombieriTest) :
    bombieriRealQuadraticValue ((left + middle) + right) =
      bombieriRealQuadraticValue (left + middle) +
        bombieriRealQuadraticValue (middle + right) -
          bombieriRealQuadraticValue middle +
        2 * (bombieriTwoBlockGlobalCrossSymbol left right).re := by
  rw [bombieriRealQuadraticValue_add,
    bombieriRealQuadraticValue_add middle right,
    bombieriTwoBlockGlobalCrossSymbol_add_left]
  simp only [Complex.add_re]
  ring

private theorem monotoneQuarterFiniteBlock_four_add_eq_endpoint_middle_endpoint
    (parent : BombieriTest) (lo : ℤ) (start n : ℕ) :
    monotoneQuarterFiniteBlock parent lo start (4 + n) =
      (monotoneQuarterFiniteBlock parent lo start 1 +
          monotoneQuarterFiniteBlock parent lo (start + 1) (2 + n)) +
        monotoneQuarterFiniteBlock parent lo (start + (3 + n)) 1 := by
  have houter := monotoneQuarterFiniteBlock_eq_prefix_add_suffix
    parent lo start (4 + n) (3 + n) (by omega)
  have hprefix := monotoneQuarterFiniteBlock_eq_prefix_add_suffix
    parent lo start (3 + n) 1 (by omega)
  have houterLen : 4 + n - (3 + n) = 1 := by omega
  have hprefixLen : 3 + n - 1 = 2 + n := by omega
  rw [houterLen] at houter
  rw [hprefixLen] at hprefix
  rw [houter, hprefix]

private theorem monotoneQuarterFiniteBlock_three_add_suffix_eq_middle_endpoint
    (parent : BombieriTest) (lo : ℤ) (start n : ℕ) :
    monotoneQuarterFiniteBlock parent lo (start + 1) (3 + n) =
      monotoneQuarterFiniteBlock parent lo (start + 1) (2 + n) +
        monotoneQuarterFiniteBlock parent lo (start + (3 + n)) 1 := by
  have hsplit := monotoneQuarterFiniteBlock_eq_prefix_add_suffix
    parent lo (start + 1) (3 + n) (2 + n) (by omega)
  have hlen : 3 + n - (2 + n) = 1 := by omega
  rw [hlen] at hsplit
  have hstart : (start + 1) + (2 + n) = start + (3 + n) := by omega
  rw [hstart] at hsplit
  exact hsplit

/-- The cross between the two removed endpoint cells is one exact far
corrected-Chebyshev contribution. -/
theorem monotoneQuarterFiniteBlock_remoteEndpointCross_re_eq_chebyshev
    (parent : BombieriTest) (lo : ℤ) (start n : ℕ) :
    (bombieriTwoBlockGlobalCrossSymbol
      (monotoneQuarterFiniteBlock parent lo start 1)
      (monotoneQuarterFiniteBlock parent lo (start + (3 + n)) 1)).re =
        monotoneQuarterFarChebyshevContribution parent
          (monotoneQuarterFiniteBlockBase lo start) (3 + (n : ℤ)) := by
  rw [monotoneQuarterFiniteBlock_one,
    monotoneQuarterFiniteBlock_one]
  have hright : monotoneQuarterFiniteBlockBase lo (start + (3 + n)) =
      monotoneQuarterFiniteBlockBase lo start + (3 + (n : ℤ)) := by
    unfold monotoneQuarterFiniteBlockBase
    push_cast
    ring
  rw [hright]
  exact monotoneQuarterCell_far_globalCross_re_eq_contribution
    parent (monotoneQuarterFiniteBlockBase lo start) (3 + (n : ℤ)) (by omega)

/-- Removing both endpoints gives an exact all-length overlap recurrence.
The only interaction absent from the two shortened blocks is the single far
corrected-Chebyshev corner. -/
theorem bombieriRealQuadraticValue_finiteBlock_four_add_eq_overlapChebyshev
    (parent : BombieriTest) (lo : ℤ) (start n : ℕ) :
    bombieriRealQuadraticValue
        (monotoneQuarterFiniteBlock parent lo start (4 + n)) =
      bombieriRealQuadraticValue
          (monotoneQuarterFiniteBlock parent lo start (3 + n)) +
        bombieriRealQuadraticValue
          (monotoneQuarterFiniteBlock parent lo (start + 1) (3 + n)) -
        bombieriRealQuadraticValue
          (monotoneQuarterFiniteBlock parent lo (start + 1) (2 + n)) +
        2 * monotoneQuarterFarChebyshevContribution parent
          (monotoneQuarterFiniteBlockBase lo start) (3 + (n : ℤ)) := by
  let left := monotoneQuarterFiniteBlock parent lo start 1
  let middle := monotoneQuarterFiniteBlock parent lo (start + 1) (2 + n)
  let right := monotoneQuarterFiniteBlock parent lo (start + (3 + n)) 1
  have hwhole : monotoneQuarterFiniteBlock parent lo start (4 + n) =
      (left + middle) + right := by
    simpa only [left, middle, right] using
      monotoneQuarterFiniteBlock_four_add_eq_endpoint_middle_endpoint
        parent lo start n
  have hprefix : left + middle =
      monotoneQuarterFiniteBlock parent lo start (3 + n) := by
    have hsplit := monotoneQuarterFiniteBlock_eq_prefix_add_suffix
      parent lo start (3 + n) 1 (by omega)
    have hlen : 3 + n - 1 = 2 + n := by omega
    rw [hlen] at hsplit
    exact hsplit.symm
  have hsuffix : middle + right =
      monotoneQuarterFiniteBlock parent lo (start + 1) (3 + n) := by
    exact (monotoneQuarterFiniteBlock_three_add_suffix_eq_middle_endpoint
      parent lo start n).symm
  rw [hwhole, bombieriRealQuadraticValue_threeTerm_overlap,
    hprefix, hsuffix]
  dsimp only [middle]
  rw [show (bombieriTwoBlockGlobalCrossSymbol left right).re =
      monotoneQuarterFarChebyshevContribution parent
        (monotoneQuarterFiniteBlockBase lo start) (3 + (n : ℤ)) by
    simpa only [left, right] using
      monotoneQuarterFiniteBlock_remoteEndpointCross_re_eq_chebyshev
        parent lo start n]

/-- Strong all-length endpoint obstruction: a support-minimal negative block
has nonnegative prefix, suffix, and middle, yet its two shortened blocks plus
the exact far Chebyshev corner fail to pay for their overlap. -/
theorem supportMinimalNegativeMonotoneBlock_overlapChebyshev_deficit
    {parent : BombieriTest} {lo : ℤ} {N start len : ℕ}
    (hmin : IsSupportMinimalNegativeMonotoneBlock
      parent lo N start len) :
    0 ≤ bombieriRealQuadraticValue
        (monotoneQuarterFiniteBlock parent lo start (len - 1)) ∧
      0 ≤ bombieriRealQuadraticValue
        (monotoneQuarterFiniteBlock parent lo (start + 1) (len - 1)) ∧
      0 ≤ bombieriRealQuadraticValue
        (monotoneQuarterFiniteBlock parent lo (start + 1) (len - 2)) ∧
      bombieriRealQuadraticValue
          (monotoneQuarterFiniteBlock parent lo start (len - 1)) +
        bombieriRealQuadraticValue
          (monotoneQuarterFiniteBlock parent lo (start + 1) (len - 1)) +
        2 * monotoneQuarterFarChebyshevContribution parent
          (monotoneQuarterFiniteBlockBase lo start) ((len - 1 : ℕ) : ℤ) <
        bombieriRealQuadraticValue
          (monotoneQuarterFiniteBlock parent lo (start + 1) (len - 2)) := by
  have hlen := four_le_length_of_supportMinimalNegativeMonotoneBlock hmin
  have hprefix :=
    supportMinimalNegativeMonotoneBlock_properSubblock_nonnegative
      hmin 0 (len - 1) (by omega) (by omega)
  have hsuffix :=
    supportMinimalNegativeMonotoneBlock_properSubblock_nonnegative
      hmin 1 (len - 1) (by omega) (by omega)
  have hmiddle :=
    supportMinimalNegativeMonotoneBlock_properSubblock_nonnegative
      hmin 1 (len - 2) (by omega) (by omega)
  refine ⟨?_, hsuffix, hmiddle, ?_⟩
  · simpa only [zero_add] using hprefix
  have hshape : 4 + (len - 4) = len := by omega
  have hthree : 3 + (len - 4) = len - 1 := by omega
  have htwo : 2 + (len - 4) = len - 2 := by omega
  have hlag : 3 + ((len - 4 : ℕ) : ℤ) = ((len - 1 : ℕ) : ℤ) := by
    omega
  have hrec := bombieriRealQuadraticValue_finiteBlock_four_add_eq_overlapChebyshev
    parent lo start (len - 4)
  rw [hshape, hthree, htwo, hlag] at hrec
  have hnegative := hmin.negative
  rw [hrec] at hnegative
  linarith

end

end ArithmeticHodge.Analysis.MultiplicativeWeilMinimalBlockEndpointEliminationStructural
