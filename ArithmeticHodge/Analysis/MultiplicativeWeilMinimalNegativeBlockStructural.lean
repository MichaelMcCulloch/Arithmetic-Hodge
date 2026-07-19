import ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneRatioTwoBlockPropagationStructural

set_option autoImplicit false

open Complex Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.MultiplicativeWeilMinimalNegativeBlockStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilMonotoneRatioTwoBlockPropagationStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural
open MultiplicativeWeilRealCutPhaseReductionStructural
open MultiplicativeWeilRealMonotonePropagationCriterionStructural

/-!
# Support-minimal negative monotone blocks

A negative real Bombieri parent has a finite consecutive monotone
quarter-cell decomposition.  Choosing a negative contiguous subblock of
shortest length imposes substantially more structure than selecting a single
failed one-sided cutoff:

* its length is at least four, because every block of at most three cells has
  support ratio at most two;
* every proper contiguous subblock is nonnegative; and
* at every internal cut, both sides are nonnegative while their complete
  global cross strictly violates the arithmetic-mean and determinant bounds.

The last conditions hold simultaneously for all cuts of the same negative
block.  This file performs the finite extraction and records those constraints
without assuming RH or its negation.
-/

/-- A finite contiguous block in the canonical monotone quarter-cell
decomposition. -/
def monotoneQuarterFiniteBlock
    (parent : BombieriTest) (lo : ℤ) (start len : ℕ) : BombieriTest :=
  ∑ i ∈ Finset.range len,
    monotoneQuarterCell parent (lo + ((start + i : ℕ) : ℤ))

/-- A negative block whose length is minimal among all negative contiguous
subblocks of a fixed finite decomposition. -/
structure IsSupportMinimalNegativeMonotoneBlock
    (parent : BombieriTest) (lo : ℤ) (n start len : ℕ) : Prop where
  within : start + len ≤ n
  negative :
    bombieriRealQuadraticValue
      (monotoneQuarterFiniteBlock parent lo start len) < 0
  shorter_nonnegative :
    ∀ start' len' : ℕ,
      start' + len' ≤ n → len' < len →
        0 ≤ bombieriRealQuadraticValue
          (monotoneQuarterFiniteBlock parent lo start' len')

/-! ## Blocks of at most three cells -/

private theorem tsupport_finset_sum_subset_Icc
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → BombieriTest) (a b : ℝ)
    (hf : ∀ i ∈ s, tsupport (f i) ⊆ Set.Icc a b) :
    tsupport (((∑ i ∈ s, f i) : BombieriTest) : ℝ → ℂ) ⊆
      Set.Icc a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (tsupport_add (f i : ℝ → ℂ)
          (∑ j ∈ s, f j : BombieriTest)).trans
        (union_subset (hf i (by simp))
          (ih (fun j hj ↦ hf j (by simp [hj]))))

/-- Any block containing at most three consecutive monotone cells fits in a
single ratio-two support interval. -/
theorem monotoneQuarterFiniteBlock_ratioTwo_of_le_three
    (parent : BombieriTest) (lo : ℤ) (start len : ℕ)
    (hlen : len ≤ 3) :
    BombieriRatioTwoCell
      (monotoneQuarterFiniteBlock parent lo start len) := by
  let k : ℤ := lo + (start : ℤ)
  have hsupport :
      tsupport (monotoneQuarterFiniteBlock parent lo start len) ⊆
        Set.Icc (quarterLogLatticePoint k)
          (quarterLogLatticePoint (k + 4)) := by
    unfold monotoneQuarterFiniteBlock
    apply tsupport_finset_sum_subset_Icc
    intro i hi
    have hiLen : i < len := Finset.mem_range.mp hi
    have hcell := monotoneQuarterCell_tsupport_subset parent
      (lo + ((start + i : ℕ) : ℤ))
    apply hcell.trans
    apply Set.Icc_subset_Icc
    · apply quarterLogLatticePoint_mono
      dsimp only [k]
      push_cast
      omega
    · apply quarterLogLatticePoint_mono
      dsimp only [k]
      push_cast
      omega
  refine ⟨quarterLogLatticePoint k, quarterLogLatticePoint (k + 4),
    quarterLogLatticePoint_pos k,
    quarterLogLatticePoint_mono (by omega), hsupport, ?_⟩
  rw [quarterLogLatticePoint_add_four]
  exact (mul_div_cancel_right₀ 2 (quarterLogLatticePoint_pos k).ne').le

/-- Consequently every block of at most three monotone cells has
nonnegative complete Bombieri quadratic value. -/
theorem bombieriRealQuadraticValue_monotoneQuarterFiniteBlock_nonnegative_of_le_three
    (parent : BombieriTest) (lo : ℤ) (start len : ℕ)
    (hlen : len ≤ 3) :
    0 ≤ bombieriRealQuadraticValue
      (monotoneQuarterFiniteBlock parent lo start len) := by
  unfold bombieriRealQuadraticValue
  exact bombieriFunctional_quadratic_re_nonneg_of_ratioTwoCell _
    (monotoneQuarterFiniteBlock_ratioTwo_of_le_three
      parent lo start len hlen)

/-! ## Finite minimization -/

/-- Every negative finite consecutive block contains a shortest negative
contiguous subblock. -/
theorem exists_supportMinimalNegativeMonotoneBlock
    (parent : BombieriTest) (lo : ℤ) (n : ℕ)
    (hnegative : bombieriRealQuadraticValue
      (monotoneQuarterFiniteBlock parent lo 0 n) < 0) :
    ∃ start len : ℕ,
      IsSupportMinimalNegativeMonotoneBlock
        parent lo n start len := by
  classical
  let P : ℕ → Prop := fun len ↦
    ∃ start : ℕ,
      start + len ≤ n ∧
        bombieriRealQuadraticValue
          (monotoneQuarterFiniteBlock parent lo start len) < 0
  have hex : ∃ len : ℕ, P len := by
    refine ⟨n, 0, by omega, ?_⟩
    exact hnegative
  let len : ℕ := Nat.find hex
  obtain ⟨start, hwithin, hneg⟩ := Nat.find_spec hex
  refine ⟨start, len, ⟨hwithin, hneg, ?_⟩⟩
  intro start' len' hwithin' hshort
  by_contra hnot
  have hneg' : bombieriRealQuadraticValue
      (monotoneQuarterFiniteBlock parent lo start' len') < 0 :=
    lt_of_not_ge hnot
  have hP : P len' := ⟨start', hwithin', hneg'⟩
  exact (Nat.find_min hex hshort) hP

/-- A shortest negative block necessarily contains at least four cells. -/
theorem four_le_length_of_supportMinimalNegativeMonotoneBlock
    {parent : BombieriTest} {lo : ℤ} {n start len : ℕ}
    (hmin : IsSupportMinimalNegativeMonotoneBlock
      parent lo n start len) :
    4 ≤ len := by
  by_contra hnot
  have hle : len ≤ 3 := by omega
  have hnonnegative :=
    bombieriRealQuadraticValue_monotoneQuarterFiniteBlock_nonnegative_of_le_three
      parent lo start len hle
  exact (not_lt_of_ge hnonnegative) hmin.negative

/-- Every proper contiguous subblock of a shortest negative block is
nonnegative. -/
theorem supportMinimalNegativeMonotoneBlock_properSubblock_nonnegative
    {parent : BombieriTest} {lo : ℤ} {n start len : ℕ}
    (hmin : IsSupportMinimalNegativeMonotoneBlock
      parent lo n start len)
    (offset sublen : ℕ) (hinside : offset + sublen ≤ len)
    (hproper : sublen < len) :
    0 ≤ bombieriRealQuadraticValue
      (monotoneQuarterFiniteBlock parent lo (start + offset) sublen) := by
  apply hmin.shorter_nonnegative (start + offset) sublen
  · calc
      (start + offset) + sublen = start + (offset + sublen) := by omega
      _ ≤ start + len := Nat.add_le_add_left hinside start
      _ ≤ n := hmin.within
  · exact hproper

/-! ## Simultaneous internal-cut constraints -/

/-- A finite block splits exactly at every internal index. -/
theorem monotoneQuarterFiniteBlock_eq_prefix_add_suffix
    (parent : BombieriTest) (lo : ℤ) (start len cut : ℕ)
    (hcut : cut ≤ len) :
    monotoneQuarterFiniteBlock parent lo start len =
      monotoneQuarterFiniteBlock parent lo start cut +
        monotoneQuarterFiniteBlock parent lo (start + cut) (len - cut) := by
  unfold monotoneQuarterFiniteBlock
  have hsum := Finset.sum_range_add
    (fun i : ℕ ↦
      monotoneQuarterCell parent (lo + ((start + i : ℕ) : ℤ)))
    cut (len - cut)
  have hlen : cut + (len - cut) = len := Nat.add_sub_of_le hcut
  rw [hlen] at hsum
  simpa only [Nat.cast_add, add_assoc] using hsum

/-- Exact real quadratic expansion across an arbitrary two-block cut. -/
theorem bombieriRealQuadraticValue_add
    (left right : BombieriTest) :
    bombieriRealQuadraticValue (left + right) =
      bombieriRealQuadraticValue left +
        bombieriRealQuadraticValue right +
          2 * (bombieriTwoBlockGlobalCrossSymbol left right).re := by
  unfold bombieriRealQuadraticValue
  simpa only [one_smul, Complex.normSq_one, one_mul] using
    bombieriFunctional_twoBlock_re left right (1 : ℂ)

/-- The four simultaneous consequences attached to one internal cut of a
minimal negative block. -/
structure BombieriMinimalNegativeCutConstraints
    (left right : BombieriTest) : Prop where
  left_nonnegative : 0 ≤ bombieriRealQuadraticValue left
  right_nonnegative : 0 ≤ bombieriRealQuadraticValue right
  cross_strictly_below_arithmeticMean :
    (bombieriTwoBlockGlobalCrossSymbol left right).re <
      -(bombieriRealQuadraticValue left +
          bombieriRealQuadraticValue right) / 2
  determinant_strictly_reversed :
    bombieriRealQuadraticValue left *
        bombieriRealQuadraticValue right <
      (bombieriTwoBlockGlobalCrossSymbol left right).re ^ 2

private theorem determinant_reversal_of_negative_twoBlock
    {L R X : ℝ} (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hnegative : L + R + 2 * X < 0) :
    L * R < X ^ 2 := by
  nlinarith [sq_nonneg (L - R), sq_nonneg (L + R + 2 * X)]

/-- Every internal cut of one shortest negative block simultaneously has two
nonnegative sides and a strictly excessive negative global cross. -/
theorem supportMinimalNegativeMonotoneBlock_internalCut_constraints
    {parent : BombieriTest} {lo : ℤ} {n start len : ℕ}
    (hmin : IsSupportMinimalNegativeMonotoneBlock
      parent lo n start len)
    (cut : ℕ) (hcutPos : 0 < cut) (hcutLt : cut < len) :
    BombieriMinimalNegativeCutConstraints
      (monotoneQuarterFiniteBlock parent lo start cut)
      (monotoneQuarterFiniteBlock parent lo
        (start + cut) (len - cut)) := by
  let left := monotoneQuarterFiniteBlock parent lo start cut
  let right := monotoneQuarterFiniteBlock parent lo
    (start + cut) (len - cut)
  have hleft : 0 ≤ bombieriRealQuadraticValue left := by
    dsimp only [left]
    exact supportMinimalNegativeMonotoneBlock_properSubblock_nonnegative
      hmin 0 cut (by omega) hcutLt
  have hright : 0 ≤ bombieriRealQuadraticValue right := by
    dsimp only [right]
    apply supportMinimalNegativeMonotoneBlock_properSubblock_nonnegative
      hmin cut (len - cut)
    · omega
    · omega
  have hsplit :
      monotoneQuarterFiniteBlock parent lo start len = left + right := by
    dsimp only [left, right]
    exact monotoneQuarterFiniteBlock_eq_prefix_add_suffix
      parent lo start len cut hcutLt.le
  have hnegative :
      bombieriRealQuadraticValue left +
          bombieriRealQuadraticValue right +
        2 * (bombieriTwoBlockGlobalCrossSymbol left right).re < 0 := by
    rw [← bombieriRealQuadraticValue_add, ← hsplit]
    exact hmin.negative
  refine ⟨hleft, hright, ?_, ?_⟩
  · linarith
  · exact determinant_reversal_of_negative_twoBlock
      hleft hright hnegative

/-- In particular, removing the left endpoint leaves a nonnegative suffix
which has a strictly excessive negative cross with that endpoint. -/
theorem supportMinimalNegativeMonotoneBlock_leftEndpoint_constraints
    {parent : BombieriTest} {lo : ℤ} {n start len : ℕ}
    (hmin : IsSupportMinimalNegativeMonotoneBlock
      parent lo n start len) :
    BombieriMinimalNegativeCutConstraints
      (monotoneQuarterFiniteBlock parent lo start 1)
      (monotoneQuarterFiniteBlock parent lo (start + 1) (len - 1)) := by
  apply supportMinimalNegativeMonotoneBlock_internalCut_constraints hmin 1
  · omega
  · have hlen := four_le_length_of_supportMinimalNegativeMonotoneBlock hmin
    omega

/-- Symmetrically, removing the right endpoint leaves a nonnegative prefix
with the same strict cross and determinant reversals. -/
theorem supportMinimalNegativeMonotoneBlock_rightEndpoint_constraints
    {parent : BombieriTest} {lo : ℤ} {n start len : ℕ}
    (hmin : IsSupportMinimalNegativeMonotoneBlock
      parent lo n start len) :
    BombieriMinimalNegativeCutConstraints
      (monotoneQuarterFiniteBlock parent lo start (len - 1))
      (monotoneQuarterFiniteBlock parent lo
        (start + (len - 1)) 1) := by
  have hlen := four_le_length_of_supportMinimalNegativeMonotoneBlock hmin
  have hcutPos : 0 < len - 1 := by omega
  have hcutLt : len - 1 < len := by omega
  simpa only [Nat.sub_sub_self (by omega : 1 ≤ len)] using
    supportMinimalNegativeMonotoneBlock_internalCut_constraints
      hmin (len - 1) hcutPos hcutLt

/-! ## Extraction from a real negative parent -/

/-- A finite monotone block cut from a conjugation-fixed parent remains
conjugation-fixed. -/
theorem bombieriConjugateTest_monotoneQuarterFiniteBlock
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent)
    (lo : ℤ) (start len : ℕ) :
    bombieriConjugateTest
        (monotoneQuarterFiniteBlock parent lo start len) =
      monotoneQuarterFiniteBlock parent lo start len := by
  induction len with
  | zero =>
      apply TestFunction.ext
      intro x
      simp only [monotoneQuarterFiniteBlock, Finset.range_zero,
        Finset.sum_empty, bombieriConjugateTest_apply,
        TestFunction.coe_zero, Pi.zero_apply, map_zero]
  | succ len ih =>
      rw [monotoneQuarterFiniteBlock, Finset.sum_range_succ,
        bombieriConjugateTest_add]
      have ih' :
          bombieriConjugateTest
              (monotoneQuarterFiniteBlock parent lo start len) =
            monotoneQuarterFiniteBlock parent lo start len := ih
      rw [show (∑ i ∈ Finset.range len,
          monotoneQuarterCell parent
            (lo + ((start + i : ℕ) : ℤ))) =
          monotoneQuarterFiniteBlock parent lo start len by rfl,
        ih',
        bombieriConjugateTest_monotoneQuarterCell parent hparent]

/-- Every conjugation-fixed negative parent therefore contains a
conjugation-fixed support-minimal negative block of length at least four. -/
theorem exists_supportMinimalNegativeMonotoneBlock_of_parent_negative
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent)
    (hnegative : bombieriRealQuadraticValue parent < 0) :
    ∃ (lo : ℤ) (n start len : ℕ),
      IsSupportMinimalNegativeMonotoneBlock
          parent lo n start len ∧
        4 ≤ len ∧
        bombieriConjugateTest
            (monotoneQuarterFiniteBlock parent lo start len) =
          monotoneQuarterFiniteBlock parent lo start len := by
  obtain ⟨lo, n, _hleft, _hright, hsum, _hratio, _hsuffix⟩ :=
    exists_monotoneQuarterCell_decomposition parent
  have hfull : bombieriRealQuadraticValue
      (monotoneQuarterFiniteBlock parent lo 0 n) < 0 := by
    have hblock : monotoneQuarterFiniteBlock parent lo 0 n = parent := by
      simpa only [monotoneQuarterFiniteBlock, zero_add] using hsum
    rw [hblock]
    exact hnegative
  obtain ⟨start, len, hmin⟩ :=
    exists_supportMinimalNegativeMonotoneBlock parent lo n hfull
  exact ⟨lo, n, start, len, hmin,
    four_le_length_of_supportMinimalNegativeMonotoneBlock hmin,
    bombieriConjugateTest_monotoneQuarterFiniteBlock
      parent hparent lo start len⟩

end

end ArithmeticHodge.Analysis.MultiplicativeWeilMinimalNegativeBlockStructural
