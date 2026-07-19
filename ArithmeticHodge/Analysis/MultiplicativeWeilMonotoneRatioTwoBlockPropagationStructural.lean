import ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneCutoffEnergyMonotonicityObstructionStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneCutPrimePhaseStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilQuarterLogLatticeFejerAssemblyStructural

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneRatioTwoBlockPropagationStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilFejerLocalizationStructural
open MultiplicativeWeilMonotoneCutoffEnergyMonotonicityObstructionStructural
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilQuarterLogLatticeFejerAssemblyStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural
open MultiplicativeWeilRealMonotonePropagationCriterionStructural

/-!
# Three-step propagation through the maximal ratio-two head block

The maximal consecutive block covered by the unconditional ratio-two theorem
is

`B_k(parent) = C_k(parent) - C_(k+3)(parent)`.

It is the sum of cells `k`, `k+1`, and `k+2`, with support from lattice point
`k` through `k+4`, whose endpoint ratio is exactly two.  Hence `Q(B_k) >= 0`.

The exact three-step propagation formula nevertheless retains the complete
global cross with the whole suffix `C_(k+3)`.  The ordered prime coefficients
have a useful triangular separation, but exactly the same separation threshold
already occurs for a one-cell head.  Thus the larger ratio-two reserve changes
the size of the missing cross bound without supplying its sign.
-/

/-! ## The maximal ratio-two block -/

/-- Three consecutive monotone cells, represented by their telescoped
boundary cutoffs. -/
def monotoneRatioTwoBlock (parent : BombieriTest) (k : ℤ) : BombieriTest :=
  monotoneQuarterCutoff parent k -
    monotoneQuarterCutoff parent (k + 3)

/-- Scalar multiplier of the three-cell block. -/
def monotoneRatioTwoBlockMultiplier (k : ℤ) (x : ℝ) : ℝ :=
  monotoneQuarterStep k x - monotoneQuarterStep (k + 3) x

@[simp] theorem monotoneRatioTwoBlock_apply
    (parent : BombieriTest) (k : ℤ) (x : ℝ) :
    monotoneRatioTwoBlock parent k x =
      (monotoneRatioTwoBlockMultiplier k x : ℂ) * parent x := by
  simp only [monotoneRatioTwoBlock, TestFunction.coe_sub, Pi.sub_apply,
    monotoneQuarterCutoff_apply, monotoneRatioTwoBlockMultiplier]
  push_cast
  ring

/-- The block is exactly the sum of its three consecutive physical cells. -/
theorem monotoneRatioTwoBlock_eq_threeCells
    (parent : BombieriTest) (k : ℤ) :
    monotoneRatioTwoBlock parent k =
      monotoneQuarterCell parent k +
        monotoneQuarterCell parent (k + 1) +
          monotoneQuarterCell parent (k + 2) := by
  rw [monotoneRatioTwoBlock]
  calc
    monotoneQuarterCutoff parent k -
        monotoneQuarterCutoff parent (k + 3) =
      ∑ i ∈ Finset.range 3,
        monotoneQuarterCell parent (k + (i : ℤ)) := by
          simpa using
            (sum_range_monotoneQuarterCell_eq_cutoff_sub parent k 3).symm
    _ = monotoneQuarterCell parent k +
        monotoneQuarterCell parent (k + 1) +
          monotoneQuarterCell parent (k + 2) := by
      norm_num [Finset.sum_range_succ]

/-- Explicit physical support enclosure for the telescoped block. -/
theorem monotoneRatioTwoBlock_tsupport_subset
    (parent : BombieriTest) (k : ℤ) :
    tsupport (monotoneRatioTwoBlock parent k) ⊆
      Set.Icc (quarterLogLatticePoint k)
        (quarterLogLatticePoint (k + 4)) := by
  have h₀ : tsupport (monotoneQuarterCell parent k) ⊆
      Set.Icc (quarterLogLatticePoint k)
        (quarterLogLatticePoint (k + 4)) :=
    (monotoneQuarterCell_tsupport_subset parent k).trans
      (Set.Icc_subset_Icc le_rfl
        (quarterLogLatticePoint_mono (by omega)))
  have h₁ : tsupport (monotoneQuarterCell parent (k + 1)) ⊆
      Set.Icc (quarterLogLatticePoint k)
        (quarterLogLatticePoint (k + 4)) :=
    (monotoneQuarterCell_tsupport_subset parent (k + 1)).trans
      (Set.Icc_subset_Icc
        (quarterLogLatticePoint_mono (by omega))
        (quarterLogLatticePoint_mono (by omega)))
  have h₂ : tsupport (monotoneQuarterCell parent (k + 2)) ⊆
      Set.Icc (quarterLogLatticePoint k)
        (quarterLogLatticePoint (k + 4)) :=
    (monotoneQuarterCell_tsupport_subset parent (k + 2)).trans
      (Set.Icc_subset_Icc
        (quarterLogLatticePoint_mono (by omega)) (by
          apply le_of_eq
          congr 1
          omega))
  rw [monotoneRatioTwoBlock_eq_threeCells]
  exact (tsupport_add
      (monotoneQuarterCell parent k +
        monotoneQuarterCell parent (k + 1) : ℝ → ℂ)
      (monotoneQuarterCell parent (k + 2) : ℝ → ℂ)).trans
    (Set.union_subset
      ((tsupport_add
        (monotoneQuarterCell parent k : ℝ → ℂ)
        (monotoneQuarterCell parent (k + 1) : ℝ → ℂ)).trans
          (Set.union_subset h₀ h₁))
      h₂)

/-- The physical support endpoints of the three-cell block have ratio exactly
two. -/
theorem monotoneRatioTwoBlock_endpoint_ratio (k : ℤ) :
    quarterLogLatticePoint (k + 4) / quarterLogLatticePoint k = 2 := by
  rw [quarterLogLatticePoint_add_four]
  exact mul_div_cancel_right₀ 2 (quarterLogLatticePoint_pos k).ne'

/-- The three-cell block is itself one ratio-two Bombieri cell. -/
theorem monotoneRatioTwoBlock_ratioTwo
    (parent : BombieriTest) (k : ℤ) :
    BombieriRatioTwoCell (monotoneRatioTwoBlock parent k) := by
  refine ⟨quarterLogLatticePoint k, quarterLogLatticePoint (k + 4),
    quarterLogLatticePoint_pos k,
    quarterLogLatticePoint_mono (by omega),
    monotoneRatioTwoBlock_tsupport_subset parent k, ?_⟩
  rw [monotoneRatioTwoBlock_endpoint_ratio]

/-- Consequently the complete quadratic value of the block is
unconditionally nonnegative. -/
theorem bombieriRealQuadraticValue_monotoneRatioTwoBlock_nonnegative
    (parent : BombieriTest) (k : ℤ) :
    0 ≤ bombieriRealQuadraticValue (monotoneRatioTwoBlock parent k) := by
  unfold bombieriRealQuadraticValue
  exact bombieriFunctional_quadratic_re_nonneg_of_ratioTwoCell _
    (monotoneRatioTwoBlock_ratioTwo parent k)

/-- The block reserve contains all three diagonal cells and all three internal
global crosses. -/
theorem bombieriRealQuadraticValue_monotoneRatioTwoBlock_eq_internal
    (parent : BombieriTest) (k : ℤ) :
    bombieriRealQuadraticValue (monotoneRatioTwoBlock parent k) =
      bombieriRealQuadraticValue (monotoneQuarterCell parent k) +
      bombieriRealQuadraticValue (monotoneQuarterCell parent (k + 1)) +
      bombieriRealQuadraticValue (monotoneQuarterCell parent (k + 2)) +
      2 * (bombieriTwoBlockGlobalCrossSymbol
        (monotoneQuarterCell parent k)
        (monotoneQuarterCell parent (k + 1))).re +
      2 * (bombieriTwoBlockGlobalCrossSymbol
        (monotoneQuarterCell parent k)
        (monotoneQuarterCell parent (k + 2))).re +
      2 * (bombieriTwoBlockGlobalCrossSymbol
        (monotoneQuarterCell parent (k + 1))
        (monotoneQuarterCell parent (k + 2))).re := by
  rw [monotoneRatioTwoBlock_eq_threeCells]
  exact bombieriQuadraticRealValue_add_add
    (monotoneQuarterCell parent k)
    (monotoneQuarterCell parent (k + 1))
    (monotoneQuarterCell parent (k + 2))

/-! ## Exact three-step defect and propagation threshold -/

/-- Outer cutoff equals the ratio-two block plus the cutoff three steps
later. -/
theorem monotoneQuarterCutoff_eq_ratioTwoBlock_add_three
    (parent : BombieriTest) (k : ℤ) :
    monotoneQuarterCutoff parent k =
      monotoneRatioTwoBlock parent k +
        monotoneQuarterCutoff parent (k + 3) := by
  unfold monotoneRatioTwoBlock
  abel

/-- Three-step energy drop from the outer cutoff to the remaining suffix. -/
def monotoneRatioTwoBlockEnergyDrop
    (parent : BombieriTest) (k : ℤ) : ℝ :=
  bombieriRealQuadraticValue (monotoneQuarterCutoff parent k) -
    bombieriRealQuadraticValue (monotoneQuarterCutoff parent (k + 3))

/-- Exact three-step defect: the suffix diagonal cancels, leaving the known
ratio-two block reserve plus twice the signed block--suffix global cross. -/
theorem monotoneRatioTwoBlockEnergyDrop_eq_reserve_add_two_cross
    (parent : BombieriTest) (k : ℤ) :
    monotoneRatioTwoBlockEnergyDrop parent k =
      bombieriRealQuadraticValue (monotoneRatioTwoBlock parent k) +
        2 * (bombieriTwoBlockGlobalCrossSymbol
          (monotoneRatioTwoBlock parent k)
          (monotoneQuarterCutoff parent (k + 3))).re := by
  unfold monotoneRatioTwoBlockEnergyDrop bombieriRealQuadraticValue
  rw [monotoneQuarterCutoff_eq_ratioTwoBlock_add_three]
  have hexpand := bombieriFunctional_twoBlock_re
    (monotoneRatioTwoBlock parent k)
    (monotoneQuarterCutoff parent (k + 3)) (1 : ℂ)
  have hexpand' :
      (bombieriFunctional
        (bombieriQuadraticTest
          (monotoneRatioTwoBlock parent k +
            monotoneQuarterCutoff parent (k + 3)))).re =
        (bombieriFunctional
          (bombieriQuadraticTest
            (monotoneRatioTwoBlock parent k))).re +
        (bombieriFunctional
          (bombieriQuadraticTest
            (monotoneQuarterCutoff parent (k + 3)))).re +
        2 * (bombieriTwoBlockGlobalCrossSymbol
          (monotoneRatioTwoBlock parent k)
          (monotoneQuarterCutoff parent (k + 3))).re := by
    simpa only [one_smul, Complex.normSq_one, one_mul] using hexpand
  rw [hexpand']
  ring

/-- The local-minus-prime content of the same defect remains explicit. -/
theorem monotoneRatioTwoBlockEnergyDrop_eq_reserve_add_local_sub_prime
    (parent : BombieriTest) (k : ℤ) :
    monotoneRatioTwoBlockEnergyDrop parent k =
      bombieriRealQuadraticValue (monotoneRatioTwoBlock parent k) +
      2 * (bombieriLocalCriticalForm
        (monotoneRatioTwoBlock parent k)
        (monotoneQuarterCutoff parent (k + 3))).re -
      2 * (bombieriPolarizedPrimeCross
        (monotoneRatioTwoBlock parent k)
        (monotoneQuarterCutoff parent (k + 3))).re := by
  rw [monotoneRatioTwoBlockEnergyDrop_eq_reserve_add_two_cross]
  unfold bombieriTwoBlockGlobalCrossSymbol
  simp only [Complex.sub_re]
  ring

/-- Energy dominance across three steps is exactly a lower bound on the
remaining whole-block cross. -/
theorem monotoneRatioTwoBlockEnergyDrop_nonnegative_iff_cross_bound
    (parent : BombieriTest) (k : ℤ) :
    0 ≤ monotoneRatioTwoBlockEnergyDrop parent k ↔
      -(bombieriRealQuadraticValue
          (monotoneRatioTwoBlock parent k)) / 2 ≤
        (bombieriTwoBlockGlobalCrossSymbol
          (monotoneRatioTwoBlock parent k)
          (monotoneQuarterCutoff parent (k + 3))).re := by
  rw [monotoneRatioTwoBlockEnergyDrop_eq_reserve_add_two_cross]
  constructor <;> intro h <;> linarith

/-- Exact three-step quadratic expansion without cancelling the suffix
reserve. -/
theorem bombieriRealQuadraticValue_cutoff_eq_threeStep
    (parent : BombieriTest) (k : ℤ) :
    bombieriRealQuadraticValue (monotoneQuarterCutoff parent k) =
      bombieriRealQuadraticValue (monotoneRatioTwoBlock parent k) +
      bombieriRealQuadraticValue (monotoneQuarterCutoff parent (k + 3)) +
      2 * (bombieriTwoBlockGlobalCrossSymbol
        (monotoneRatioTwoBlock parent k)
        (monotoneQuarterCutoff parent (k + 3))).re := by
  unfold bombieriRealQuadraticValue
  rw [monotoneQuarterCutoff_eq_ratioTwoBlock_add_three]
  simpa only [one_smul, Complex.normSq_one, one_mul] using
    bombieriFunctional_twoBlock_re
      (monotoneRatioTwoBlock parent k)
      (monotoneQuarterCutoff parent (k + 3)) (1 : ℂ)

/-- The actual sign-propagation threshold uses both the block and suffix
reserves.  This is weaker than demanding monotone energy drop, but it is still
an unproved signed global-cross inequality. -/
theorem bombieriRealQuadraticValue_cutoff_nonnegative_iff_threeStep_cross_bound
    (parent : BombieriTest) (k : ℤ) :
    0 ≤ bombieriRealQuadraticValue (monotoneQuarterCutoff parent k) ↔
      -(bombieriRealQuadraticValue (monotoneRatioTwoBlock parent k) +
          bombieriRealQuadraticValue
            (monotoneQuarterCutoff parent (k + 3))) / 2 ≤
        (bombieriTwoBlockGlobalCrossSymbol
          (monotoneRatioTwoBlock parent k)
          (monotoneQuarterCutoff parent (k + 3))).re := by
  rw [bombieriRealQuadraticValue_cutoff_eq_threeStep]
  constructor <;> intro h <;> linarith

/-- A three-step propagation theorem, conditional on exactly the missing
block--suffix row bound. -/
theorem bombieriRealQuadraticValue_cutoff_nonnegative_of_threeStep_cross_bound
    (parent : BombieriTest) (k : ℤ)
    (_htail : 0 ≤ bombieriRealQuadraticValue
      (monotoneQuarterCutoff parent (k + 3)))
    (hcross : -(bombieriRealQuadraticValue
        (monotoneRatioTwoBlock parent k) +
          bombieriRealQuadraticValue
            (monotoneQuarterCutoff parent (k + 3))) / 2 ≤
      (bombieriTwoBlockGlobalCrossSymbol
        (monotoneRatioTwoBlock parent k)
        (monotoneQuarterCutoff parent (k + 3))).re) :
    0 ≤ bombieriRealQuadraticValue (monotoneQuarterCutoff parent k) := by
  exact
    (bombieriRealQuadraticValue_cutoff_nonnegative_iff_threeStep_cross_bound
      parent k).2 hcross

/-- With a nonnegative suffix, the propagation threshold is no stronger than
the energy-dominance threshold. -/
theorem threeStepPropagationThreshold_le_energyDropThreshold
    (parent : BombieriTest) (k : ℤ)
    (htail : 0 ≤ bombieriRealQuadraticValue
      (monotoneQuarterCutoff parent (k + 3))) :
    -(bombieriRealQuadraticValue (monotoneRatioTwoBlock parent k) +
        bombieriRealQuadraticValue
          (monotoneQuarterCutoff parent (k + 3))) / 2 ≤
      -(bombieriRealQuadraticValue
          (monotoneRatioTwoBlock parent k)) / 2 := by
  linarith

/-! ## Ordered prime masks and comparison with a one-cell head -/

/-- The three-cell block multiplier is pointwise nonnegative. -/
theorem monotoneRatioTwoBlockMultiplier_nonnegative
    (k : ℤ) (x : ℝ) :
    0 ≤ monotoneRatioTwoBlockMultiplier k x := by
  by_cases hx : x ≤ quarterLogLatticePoint (k + 3)
  · rw [monotoneRatioTwoBlockMultiplier,
      monotoneQuarterStep_eq_zero_of_le (k + 3) hx, sub_zero]
    exact monotoneQuarterStep_nonneg k x
  · have hright : quarterLogLatticePoint (k + 3) ≤ x := le_of_not_ge hx
    have hkRight : quarterLogLatticePoint (k + 1) ≤ x :=
      (quarterLogLatticePoint_mono (by omega)).trans hright
    rw [monotoneRatioTwoBlockMultiplier,
      monotoneQuarterStep_eq_one_of_le k hkRight]
    exact sub_nonneg.mpr (monotoneQuarterStep_le_one (k + 3) x)

/-- Above the block support, both boundary steps equal one and the block
multiplier vanishes. -/
theorem monotoneRatioTwoBlockMultiplier_eq_zero_of_upper
    (k : ℤ) {x : ℝ} (hx : quarterLogLatticePoint (k + 4) ≤ x) :
    monotoneRatioTwoBlockMultiplier k x = 0 := by
  have hk : quarterLogLatticePoint (k + 1) ≤ x :=
    (quarterLogLatticePoint_mono (by omega)).trans hx
  have hk3 : quarterLogLatticePoint ((k + 3) + 1) ≤ x := by
    simpa only [add_assoc] using hx
  rw [monotoneRatioTwoBlockMultiplier,
    monotoneQuarterStep_eq_one_of_le k hk,
    monotoneQuarterStep_eq_one_of_le (k + 3) hk3]
  ring

/-- Directed coefficient with the block at the dilated point and the suffix
at the base point. -/
def monotoneRatioTwoBlockForwardPrimeMask
    (k : ℤ) (x y : ℝ) : ℝ :=
  monotoneRatioTwoBlockMultiplier k (x * y) *
    monotoneQuarterStep (k + 3) y

/-- Oppositely directed coefficient with the suffix at the dilated point. -/
def monotoneRatioTwoBlockReversePrimeMask
    (k : ℤ) (x y : ℝ) : ℝ :=
  monotoneQuarterStep (k + 3) (x * y) *
    monotoneRatioTwoBlockMultiplier k y

/-- Symmetric real coefficient of the block--suffix prime cross. -/
def monotoneRatioTwoBlockSymmetricPrimeMask
    (k : ℤ) (x y : ℝ) : ℝ :=
  monotoneRatioTwoBlockForwardPrimeMask k x y +
    monotoneRatioTwoBlockReversePrimeMask k x y

theorem monotoneRatioTwoBlockForwardPrimeMask_nonnegative
    (k : ℤ) (x y : ℝ) :
    0 ≤ monotoneRatioTwoBlockForwardPrimeMask k x y := by
  exact mul_nonneg (monotoneRatioTwoBlockMultiplier_nonnegative k (x * y))
    (monotoneQuarterStep_nonneg (k + 3) y)

theorem monotoneRatioTwoBlockReversePrimeMask_nonnegative
    (k : ℤ) (x y : ℝ) :
    0 ≤ monotoneRatioTwoBlockReversePrimeMask k x y := by
  exact mul_nonneg (monotoneQuarterStep_nonneg (k + 3) (x * y))
    (monotoneRatioTwoBlockMultiplier_nonnegative k y)

theorem monotoneRatioTwoBlockSymmetricPrimeMask_nonnegative
    (k : ℤ) (x y : ℝ) :
    0 ≤ monotoneRatioTwoBlockSymmetricPrimeMask k x y := by
  exact add_nonneg
    (monotoneRatioTwoBlockForwardPrimeMask_nonnegative k x y)
    (monotoneRatioTwoBlockReversePrimeMask_nonnegative k x y)

/-- At every actual prime dilation (`x ≥ 2`), the forward orientation is
support-separated and vanishes exactly. -/
theorem monotoneRatioTwoBlockForwardPrimeMask_eq_zero_of_two_le
    (k : ℤ) {x y : ℝ} (hx : 2 ≤ x) (hy : 0 ≤ y) :
    monotoneRatioTwoBlockForwardPrimeMask k x y = 0 := by
  by_cases hyCut : y ≤ quarterLogLatticePoint (k + 3)
  · rw [monotoneRatioTwoBlockForwardPrimeMask,
      monotoneQuarterStep_eq_zero_of_le (k + 3) hyCut, mul_zero]
  · have hCutY : quarterLogLatticePoint (k + 3) < y := lt_of_not_ge hyCut
    have htwiceY : 2 * y ≤ x * y :=
      mul_le_mul_of_nonneg_right hx hy
    have hupperTwice :
        quarterLogLatticePoint (k + 4) <
          2 * quarterLogLatticePoint (k + 3) := by
      calc
        quarterLogLatticePoint (k + 4) <
            quarterLogLatticePoint ((k + 3) + 4) :=
          quarterLogLatticePoint_strictMono (by omega)
        _ = 2 * quarterLogLatticePoint (k + 3) :=
          quarterLogLatticePoint_add_four (k + 3)
    have hupper : quarterLogLatticePoint (k + 4) ≤ x * y := by
      apply le_of_lt
      calc
        quarterLogLatticePoint (k + 4) <
            2 * quarterLogLatticePoint (k + 3) := hupperTwice
        _ < 2 * y := mul_lt_mul_of_pos_left hCutY (by norm_num)
        _ ≤ x * y := htwiceY
    rw [monotoneRatioTwoBlockForwardPrimeMask,
      monotoneRatioTwoBlockMultiplier_eq_zero_of_upper k hupper, zero_mul]

/-- Hence at prime ratios the whole symmetric coefficient is only the reverse
orientation. -/
theorem monotoneRatioTwoBlockSymmetricPrimeMask_eq_reverse_of_two_le
    (k : ℤ) {x y : ℝ} (hx : 2 ≤ x) (hy : 0 ≤ y) :
    monotoneRatioTwoBlockSymmetricPrimeMask k x y =
      monotoneRatioTwoBlockReversePrimeMask k x y := by
  rw [monotoneRatioTwoBlockSymmetricPrimeMask,
    monotoneRatioTwoBlockForwardPrimeMask_eq_zero_of_two_le k hx hy,
    zero_add]

/-- Exact coefficient factorization for the forward directed parent
correlation. -/
theorem monotoneRatioTwoBlock_mul_conj_suffix_eq_forwardMask
    (parent : BombieriTest) (k : ℤ) (x y : ℝ) :
    monotoneRatioTwoBlock parent k (x * y) *
        starRingEnd ℂ (monotoneQuarterCutoff parent (k + 3) y) =
      (monotoneRatioTwoBlockForwardPrimeMask k x y : ℂ) *
        MultiplicativeWeilMonotoneCutPrimePhaseStructural.monotoneCutParentProduct
          parent x y := by
  rw [monotoneRatioTwoBlock_apply, monotoneQuarterCutoff_apply,
    map_mul (starRingEnd ℂ)]
  simp only [Complex.conj_ofReal]
  unfold monotoneRatioTwoBlockForwardPrimeMask
    MultiplicativeWeilMonotoneCutPrimePhaseStructural.monotoneCutParentProduct
  push_cast
  ring

/-- Exact coefficient factorization for the reverse orientation. -/
theorem suffix_mul_conj_monotoneRatioTwoBlock_eq_reverseMask
    (parent : BombieriTest) (k : ℤ) (x y : ℝ) :
    monotoneQuarterCutoff parent (k + 3) (x * y) *
        starRingEnd ℂ (monotoneRatioTwoBlock parent k y) =
      (monotoneRatioTwoBlockReversePrimeMask k x y : ℂ) *
        MultiplicativeWeilMonotoneCutPrimePhaseStructural.monotoneCutParentProduct
          parent x y := by
  rw [monotoneRatioTwoBlock_apply, monotoneQuarterCutoff_apply,
    map_mul (starRingEnd ℂ)]
  simp only [Complex.conj_ofReal]
  unfold monotoneRatioTwoBlockReversePrimeMask
    MultiplicativeWeilMonotoneCutPrimePhaseStructural.monotoneCutParentProduct
  push_cast
  ring

/-- The complete mixed ordered correlation uses the symmetric mask. -/
theorem monotoneRatioTwoBlock_mixedProduct_eq_symmetricMask
    (parent : BombieriTest) (k : ℤ) (x y : ℝ) :
    monotoneRatioTwoBlock parent k (x * y) *
          starRingEnd ℂ (monotoneQuarterCutoff parent (k + 3) y) +
        monotoneQuarterCutoff parent (k + 3) (x * y) *
          starRingEnd ℂ (monotoneRatioTwoBlock parent k y) =
      (monotoneRatioTwoBlockSymmetricPrimeMask k x y : ℂ) *
        MultiplicativeWeilMonotoneCutPrimePhaseStructural.monotoneCutParentProduct
          parent x y := by
  rw [monotoneRatioTwoBlock_mul_conj_suffix_eq_forwardMask,
    suffix_mul_conj_monotoneRatioTwoBlock_eq_reverseMask]
  unfold monotoneRatioTwoBlockSymmetricPrimeMask
  push_cast
  ring

/-- Although the prime coefficient is nonnegative, the real mixed kernel
still carries the signed parent correlation. -/
theorem monotoneRatioTwoBlock_mixedProduct_re_eq_mask_mul_parentRe
    (parent : BombieriTest) (k : ℤ) (x y : ℝ) :
    (monotoneRatioTwoBlock parent k (x * y) *
          starRingEnd ℂ (monotoneQuarterCutoff parent (k + 3) y) +
        monotoneQuarterCutoff parent (k + 3) (x * y) *
          starRingEnd ℂ (monotoneRatioTwoBlock parent k y)).re =
      monotoneRatioTwoBlockSymmetricPrimeMask k x y *
        (MultiplicativeWeilMonotoneCutPrimePhaseStructural.monotoneCutParentProduct
          parent x y).re := by
  rw [monotoneRatioTwoBlock_mixedProduct_eq_symmetricMask]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

/-! ### The one-cell head has the same prime separation threshold -/

/-- Forward ordered mask for the ordinary one-cell head and its suffix. -/
def monotoneOneCellForwardPrimeMask (k : ℤ) (x y : ℝ) : ℝ :=
  monotoneQuarterWeight k (x * y) * monotoneQuarterStep (k + 1) y

/-- The one-cell forward orientation also vanishes at every prime dilation. -/
theorem monotoneOneCellForwardPrimeMask_eq_zero_of_two_le
    (k : ℤ) {x y : ℝ} (hx : 2 ≤ x) (hy : 0 ≤ y) :
    monotoneOneCellForwardPrimeMask k x y = 0 := by
  by_cases hyCut : y ≤ quarterLogLatticePoint (k + 1)
  · rw [monotoneOneCellForwardPrimeMask,
      monotoneQuarterStep_eq_zero_of_le (k + 1) hyCut, mul_zero]
  · have hCutY : quarterLogLatticePoint (k + 1) < y := lt_of_not_ge hyCut
    have htwiceY : 2 * y ≤ x * y :=
      mul_le_mul_of_nonneg_right hx hy
    have hupperTwice :
        quarterLogLatticePoint (k + 2) <
          2 * quarterLogLatticePoint (k + 1) := by
      calc
        quarterLogLatticePoint (k + 2) <
            quarterLogLatticePoint ((k + 1) + 4) :=
          quarterLogLatticePoint_strictMono (by omega)
        _ = 2 * quarterLogLatticePoint (k + 1) :=
          quarterLogLatticePoint_add_four (k + 1)
    have hupper : quarterLogLatticePoint (k + 2) ≤ x * y := by
      apply le_of_lt
      calc
        quarterLogLatticePoint (k + 2) <
            2 * quarterLogLatticePoint (k + 1) := hupperTwice
        _ < 2 * y := mul_lt_mul_of_pos_left hCutY (by norm_num)
        _ ≤ x * y := htwiceY
    rw [monotoneOneCellForwardPrimeMask,
      monotoneQuarterWeight_eq_zero_of_le_left k hupper, zero_mul]

/-- Consecutive quarter-lattice ratios are independent of the base index. -/
theorem quarterLogLatticePoint_consecutive_ratio (n : ℤ) :
    quarterLogLatticePoint (n + 1) / quarterLogLatticePoint n =
      quarterLogLatticePoint 1 := by
  rw [quarterLogLatticePoint_add,
    mul_div_cancel_right₀ _ (quarterLogLatticePoint_pos n).ne']

/-- The block--suffix and one-cell--suffix support-separation thresholds are
exactly equal.  The larger block therefore has no stronger crossing
localization at prime ratios. -/
theorem ratioTwoBlock_separationThreshold_eq_oneCell
    (k : ℤ) :
    quarterLogLatticePoint (k + 4) /
        quarterLogLatticePoint (k + 3) =
      quarterLogLatticePoint (k + 2) /
        quarterLogLatticePoint (k + 1) := by
  calc
    quarterLogLatticePoint (k + 4) /
        quarterLogLatticePoint (k + 3) =
      quarterLogLatticePoint ((k + 3) + 1) /
        quarterLogLatticePoint (k + 3) := by
          congr 1
          ring_nf
    _ = quarterLogLatticePoint 1 :=
      quarterLogLatticePoint_consecutive_ratio (k + 3)
    _ = quarterLogLatticePoint ((k + 1) + 1) /
        quarterLogLatticePoint (k + 1) :=
      (quarterLogLatticePoint_consecutive_ratio (k + 1)).symm
    _ = quarterLogLatticePoint (k + 2) /
        quarterLogLatticePoint (k + 1) := by
          congr 1
          ring_nf

/-! ## Exact comparison of the remaining global crosses -/

/-- The three-step missing cross is the sum of the three cell rows against
the far suffix. -/
theorem ratioTwoBlock_globalCross_eq_three_far_rows
    (parent : BombieriTest) (k : ℤ) :
    bombieriTwoBlockGlobalCrossSymbol
        (monotoneRatioTwoBlock parent k)
        (monotoneQuarterCutoff parent (k + 3)) =
      bombieriTwoBlockGlobalCrossSymbol
          (monotoneQuarterCell parent k)
          (monotoneQuarterCutoff parent (k + 3)) +
      bombieriTwoBlockGlobalCrossSymbol
          (monotoneQuarterCell parent (k + 1))
          (monotoneQuarterCutoff parent (k + 3)) +
      bombieriTwoBlockGlobalCrossSymbol
          (monotoneQuarterCell parent (k + 2))
          (monotoneQuarterCutoff parent (k + 3)) := by
  rw [monotoneRatioTwoBlock_eq_threeCells,
    bombieriTwoBlockGlobalCrossSymbol_add_left,
    bombieriTwoBlockGlobalCrossSymbol_add_left]

/-- For comparison, the ordinary one-step sign-propagation threshold has the
same form, with one cell reserve and the immediately following suffix. -/
theorem bombieriRealQuadraticValue_cutoff_nonnegative_iff_oneStep_cross_bound
    (parent : BombieriTest) (k : ℤ) :
    0 ≤ bombieriRealQuadraticValue (monotoneQuarterCutoff parent k) ↔
      -(bombieriRealQuadraticValue (monotoneQuarterCell parent k) +
          bombieriRealQuadraticValue
            (monotoneQuarterCutoff parent (k + 1))) / 2 ≤
        (bombieriTwoBlockGlobalCrossSymbol
          (monotoneQuarterCell parent k)
          (monotoneQuarterCutoff parent (k + 1))).re := by
  unfold bombieriRealQuadraticValue
  rw [monotoneQuarterCutoff_eq_cell_add_next]
  have hexpand := bombieriFunctional_twoBlock_re
    (monotoneQuarterCell parent k)
    (monotoneQuarterCutoff parent (k + 1)) (1 : ℂ)
  have hexpand' :
      (bombieriFunctional
        (bombieriQuadraticTest
          (monotoneQuarterCell parent k +
            monotoneQuarterCutoff parent (k + 1)))).re =
        (bombieriFunctional
          (bombieriQuadraticTest
            (monotoneQuarterCell parent k))).re +
        (bombieriFunctional
          (bombieriQuadraticTest
            (monotoneQuarterCutoff parent (k + 1)))).re +
        2 * (bombieriTwoBlockGlobalCrossSymbol
          (monotoneQuarterCell parent k)
          (monotoneQuarterCutoff parent (k + 1))).re := by
    simpa only [one_smul, Complex.normSq_one, one_mul] using hexpand
  rw [hexpand']
  constructor <;> intro h <;> linarith

end

end ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneRatioTwoBlockPropagationStructural
