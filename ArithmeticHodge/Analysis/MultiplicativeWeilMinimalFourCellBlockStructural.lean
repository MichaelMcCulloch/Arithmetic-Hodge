import ArithmeticHodge.Analysis.MultiplicativeWeilMinimalNegativeBlockStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilPrimeCorrelation

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ArithmeticFunction BigOperators

namespace ArithmeticHodge.Analysis.MultiplicativeWeilMinimalFourCellBlockStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilMinimalNegativeBlockStructural
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural
open MultiplicativeWeilRealMonotonePropagationCriterionStructural

/-!
# The first possible support-minimal monotone block

Every support-minimal negative block has at least four quarter cells.  This
file treats the first possible length exactly.  Four consecutive cells have
support ratio `2^(5/4) < 3`, so their complete prime sum consists of precisely
the `n = 2` Mangoldt atom.  Their sign is therefore equivalent to one explicit
local-energy domination inequality.

The two overlapping three-cell blocks and their two-cell intersection are
all unconditionally nonnegative by ratio-two positivity.  Their exact
inclusion-exclusion identity nevertheless retains the complete cross between
the two endpoint cells.  A final algebraic lemma records sharply that the
three reserve signs alone cannot bound this remote corner.  Thus a proof at
length four needs a genuinely common-parent factor-two estimate, rather than
another rearrangement of already-known proper-block positivity.
-/

/-! ## The four-cell block and its common-parent mask -/

/-- Four consecutive cells starting at offset `start` in a fixed monotone
quarter decomposition. -/
def monotoneQuarterFourCellBlock
    (parent : BombieriTest) (lo : ℤ) (start : ℕ) : BombieriTest :=
  monotoneQuarterFiniteBlock parent lo start 4

/-- The physical lattice index of the first cell. -/
def monotoneQuarterFourCellBase (lo : ℤ) (start : ℕ) : ℤ :=
  lo + (start : ℤ)

/-- The telescoped scalar mask of four consecutive cells. -/
def monotoneQuarterFourCellMultiplier
    (lo : ℤ) (start : ℕ) (x : ℝ) : ℝ :=
  monotoneQuarterStep (monotoneQuarterFourCellBase lo start) x -
    monotoneQuarterStep (monotoneQuarterFourCellBase lo start + 4) x

private theorem monotoneQuarterFiniteBlock_eq_shifted_sum
    (parent : BombieriTest) (lo : ℤ) (start len : ℕ) :
    monotoneQuarterFiniteBlock parent lo start len =
      ∑ i ∈ Finset.range len,
        monotoneQuarterCell parent
          (monotoneQuarterFourCellBase lo start + (i : ℤ)) := by
  classical
  unfold monotoneQuarterFiniteBlock monotoneQuarterFourCellBase
  apply Finset.sum_congr rfl
  intro i _hi
  have hindex : lo + ((start + i : ℕ) : ℤ) =
      lo + (start : ℤ) + (i : ℤ) := by
    push_cast
    ring
  rw [hindex]

/-- Four cells telescope to the difference of their two boundary cutoffs. -/
theorem monotoneQuarterFourCellBlock_eq_cutoff_sub
    (parent : BombieriTest) (lo : ℤ) (start : ℕ) :
    monotoneQuarterFourCellBlock parent lo start =
      monotoneQuarterCutoff parent
          (monotoneQuarterFourCellBase lo start) -
        monotoneQuarterCutoff parent
          (monotoneQuarterFourCellBase lo start + 4) := by
  rw [monotoneQuarterFourCellBlock,
    monotoneQuarterFiniteBlock_eq_shifted_sum]
  exact sum_range_monotoneQuarterCell_eq_cutoff_sub
    parent (monotoneQuarterFourCellBase lo start) 4

@[simp] theorem monotoneQuarterFourCellBlock_apply
    (parent : BombieriTest) (lo : ℤ) (start : ℕ) (x : ℝ) :
    monotoneQuarterFourCellBlock parent lo start x =
      (monotoneQuarterFourCellMultiplier lo start x : ℂ) * parent x := by
  rw [monotoneQuarterFourCellBlock_eq_cutoff_sub]
  simp only [TestFunction.coe_sub, Pi.sub_apply,
    monotoneQuarterCutoff_apply, monotoneQuarterFourCellMultiplier]
  push_cast
  ring

/-- The four-cell multiplier is still a pointwise nonnegative common-parent
mask. -/
theorem monotoneQuarterFourCellMultiplier_nonnegative
    (lo : ℤ) (start : ℕ) (x : ℝ) :
    0 ≤ monotoneQuarterFourCellMultiplier lo start x := by
  unfold monotoneQuarterFourCellMultiplier
  apply sub_nonneg.mpr
  let k := monotoneQuarterFourCellBase lo start
  calc
    monotoneQuarterStep (k + 4) x ≤ monotoneQuarterStep (k + 3) x := by
      convert monotoneQuarterStep_succ_le (k + 3) x using 1
      ring
    _ ≤ monotoneQuarterStep (k + 2) x := by
      convert monotoneQuarterStep_succ_le (k + 2) x using 1
      ring
    _ ≤ monotoneQuarterStep (k + 1) x := by
      convert monotoneQuarterStep_succ_le (k + 1) x using 1
      ring
    _ ≤ monotoneQuarterStep k x := monotoneQuarterStep_succ_le k x

/-- At factor two the surviving autocorrelation is the nonnegative mask
product paired against the still-signed common-parent correlation. -/
theorem bombieriQuadraticTest_fourCellBlock_two_eq_parentMask
    (parent : BombieriTest) (lo : ℤ) (start : ℕ) :
    bombieriQuadraticTest (monotoneQuarterFourCellBlock parent lo start) 2 =
      ∫ y : ℝ in Set.Ioi 0,
        ((monotoneQuarterFourCellMultiplier lo start (2 * y) *
            monotoneQuarterFourCellMultiplier lo start y : ℝ) : ℂ) *
          (parent (2 * y) * starRingEnd ℂ (parent y)) := by
  rw [bombieriQuadraticTest_apply]
  unfold autocorrelation
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y _hy
  change
    monotoneQuarterFourCellBlock parent lo start (2 * y) *
        starRingEnd ℂ (monotoneQuarterFourCellBlock parent lo start y) = _
  rw [monotoneQuarterFourCellBlock_apply,
    monotoneQuarterFourCellBlock_apply, map_mul (starRingEnd ℂ),
    Complex.conj_ofReal]
  push_cast
  ring

theorem fourCell_factorTwo_mask_nonnegative
    (lo : ℤ) (start : ℕ) (y : ℝ) :
    0 ≤ monotoneQuarterFourCellMultiplier lo start (2 * y) *
      monotoneQuarterFourCellMultiplier lo start y :=
  mul_nonneg
    (monotoneQuarterFourCellMultiplier_nonnegative lo start (2 * y))
    (monotoneQuarterFourCellMultiplier_nonnegative lo start y)

/-! ## Support width and exact single-atom reduction -/

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

/-- Four cells occupy five quarter-lattice gaps. -/
theorem monotoneQuarterFourCellBlock_tsupport_subset
    (parent : BombieriTest) (lo : ℤ) (start : ℕ) :
    tsupport (monotoneQuarterFourCellBlock parent lo start) ⊆
      Set.Icc
        (quarterLogLatticePoint (monotoneQuarterFourCellBase lo start))
        (quarterLogLatticePoint
          (monotoneQuarterFourCellBase lo start + 5)) := by
  rw [monotoneQuarterFourCellBlock,
    monotoneQuarterFiniteBlock_eq_shifted_sum]
  apply tsupport_finset_sum_subset_Icc
  intro i hi
  have hiFour : i < 4 := Finset.mem_range.mp hi
  have hcell := monotoneQuarterCell_tsupport_subset parent
    (monotoneQuarterFourCellBase lo start + (i : ℤ))
  apply hcell.trans
  apply Set.Icc_subset_Icc
  · apply quarterLogLatticePoint_mono
    omega
  · apply quarterLogLatticePoint_mono
    omega

private theorem quarterLogLatticePoint_one_pow_four :
    quarterLogLatticePoint 1 ^ 4 = 2 := by
  unfold quarterLogLatticePoint
  norm_num
  rw [← Real.exp_nat_mul]
  convert Real.exp_log (by norm_num : (0 : ℝ) < 2) using 1
  ring_nf

/-- Five quarter steps have fourth power `32`. -/
theorem quarterLogLatticePoint_five_pow_four :
    quarterLogLatticePoint 5 ^ 4 = 32 := by
  have hfive : quarterLogLatticePoint 5 =
      2 * quarterLogLatticePoint 1 := by
    calc
      quarterLogLatticePoint 5 = quarterLogLatticePoint (1 + 4) := by
        norm_num
      _ = quarterLogLatticePoint 4 * quarterLogLatticePoint 1 :=
        quarterLogLatticePoint_add 1 4
      _ = 2 * quarterLogLatticePoint 1 := by
        rw [quarterLogLatticePoint_four]
  rw [hfive, mul_pow, quarterLogLatticePoint_one_pow_four]
  norm_num

/-- In particular `2^(5/4) < 3`, proved without numerical approximation. -/
theorem quarterLogLatticePoint_five_lt_three :
    quarterLogLatticePoint 5 < 3 := by
  apply lt_of_pow_lt_pow_left₀ 4 (by norm_num : (0 : ℝ) ≤ 3)
  rw [quarterLogLatticePoint_five_pow_four]
  norm_num

/-- The physical endpoint ratio of a four-cell block is strictly below
three. -/
theorem monotoneQuarterFourCellBlock_endpoint_ratio_lt_three
    (lo : ℤ) (start : ℕ) :
    quarterLogLatticePoint
          (monotoneQuarterFourCellBase lo start + 5) /
        quarterLogLatticePoint (monotoneQuarterFourCellBase lo start) < 3 := by
  rw [quarterLogLatticePoint_add]
  rw [mul_div_cancel_right₀ _
    (quarterLogLatticePoint_pos
      (monotoneQuarterFourCellBase lo start)).ne']
  exact quarterLogLatticePoint_five_lt_three

/-- Above the integer ratio three the quadratic autocorrelation vanishes. -/
private theorem bombieriQuadraticTest_apply_eq_zero_of_three_le
    (g : BombieriTest) {a b x : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a < 3) (hx : 3 ≤ x) :
    bombieriQuadraticTest g x = 0 := by
  by_contra hne
  have hmem := bombieriQuadraticTest_tsupport_subset_Icc
    g ha hab hsupport
    (subset_tsupport (bombieriQuadraticTest g)
      (Function.mem_support.mpr hne))
  exact (not_lt_of_ge hmem.2) (hratio.trans_le hx)

private theorem vonMangoldtPrimeSummand_quadratic_eq_zero_of_two_le
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a < 3) {k : ℕ} (hk : 2 ≤ k) :
    vonMangoldtPrimeSummand (bombieriQuadraticTest g) k = 0 := by
  have hx : 3 ≤ (((k + 1 : ℕ) : ℝ)) := by
    exact_mod_cast (show 3 ≤ k + 1 by omega)
  have hzero := bombieriQuadraticTest_apply_eq_zero_of_three_le
    g ha hab hsupport hratio hx
  unfold vonMangoldtPrimeSummand
  rw [primeKernel_bombieriQuadraticTest_eq_two_re, hzero]
  norm_num

/-- Below ratio three the entire prime functional is exactly the `n = 2`
summand. -/
private theorem primeSum_quadratic_eq_n_two_of_support_ratio_lt_three
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a < 3) :
    primeSum (bombieriQuadraticTest g) =
      vonMangoldtPrimeSummand (bombieriQuadraticTest g) 1 := by
  rw [primeSum, tsum_eq_sum (s := Finset.range 2) (by
    intro k hk
    have hkTwo : 2 ≤ k := by
      simpa only [Finset.mem_range, not_lt] using hk
    exact vonMangoldtPrimeSummand_quadratic_eq_zero_of_two_le
      g ha hab hsupport hratio hkTwo)]
  norm_num [Finset.sum_range_succ, vonMangoldtPrimeSummand]

/-- Exact evaluation of the complete prime sum for the four-cell block. -/
theorem primeSum_fourCellBlock_eq_n_two
    (parent : BombieriTest) (lo : ℤ) (start : ℕ) :
    primeSum
        (bombieriQuadraticTest
          (monotoneQuarterFourCellBlock parent lo start)) =
      (Real.log 2 : ℂ) *
        ((2 * (bombieriQuadraticTest
          (monotoneQuarterFourCellBlock parent lo start) 2).re : ℝ) : ℂ) := by
  rw [primeSum_quadratic_eq_n_two_of_support_ratio_lt_three
    (monotoneQuarterFourCellBlock parent lo start)
    (quarterLogLatticePoint_pos (monotoneQuarterFourCellBase lo start))
    (quarterLogLatticePoint_mono (by omega))
    (monotoneQuarterFourCellBlock_tsupport_subset parent lo start)
    (monotoneQuarterFourCellBlock_endpoint_ratio_lt_three lo start)]
  unfold vonMangoldtPrimeSummand
  rw [ArithmeticFunction.vonMangoldt_apply_prime
      (by norm_num : Nat.Prime 2),
    primeKernel_bombieriQuadraticTest_eq_two_re]
  norm_num

/-! ## The sharp length-four inequality -/

/-- Exact local-minus-single-prime formula for four cells. -/
theorem bombieriRealQuadraticValue_fourCellBlock_eq_local_sub_n_two
    (parent : BombieriTest) (lo : ℤ) (start : ℕ) :
    bombieriRealQuadraticValue
        (monotoneQuarterFourCellBlock parent lo start) =
      (bombieriLocalCriticalForm
        (monotoneQuarterFourCellBlock parent lo start)
        (monotoneQuarterFourCellBlock parent lo start)).re -
      2 * Real.log 2 *
        (bombieriQuadraticTest
          (monotoneQuarterFourCellBlock parent lo start) 2).re := by
  unfold bombieriRealQuadraticValue
  rw [bombieriFunctional_quadratic_eq_localCritical_sub_prime,
    primeSum_fourCellBlock_eq_n_two]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring

/-- Four-cell positivity is exactly domination of the sole surviving
factor-two atom by the local critical form. -/
theorem bombieriRealQuadraticValue_fourCellBlock_nonnegative_iff
    (parent : BombieriTest) (lo : ℤ) (start : ℕ) :
    0 ≤ bombieriRealQuadraticValue
        (monotoneQuarterFourCellBlock parent lo start) ↔
      2 * Real.log 2 *
          (bombieriQuadraticTest
            (monotoneQuarterFourCellBlock parent lo start) 2).re ≤
        (bombieriLocalCriticalForm
          (monotoneQuarterFourCellBlock parent lo start)
          (monotoneQuarterFourCellBlock parent lo start)).re := by
  rw [bombieriRealQuadraticValue_fourCellBlock_eq_local_sub_n_two]
  exact sub_nonneg

/-- Hence a support-minimal negative block of the first possible length is
equivalently a strict failure of the displayed single-atom domination. -/
theorem supportMinimalNegativeMonotoneBlock_length_four_local_lt_n_two
    {parent : BombieriTest} {lo : ℤ} {n start len : ℕ}
    (hmin : IsSupportMinimalNegativeMonotoneBlock
      parent lo n start len) (hlen : len = 4) :
    (bombieriLocalCriticalForm
        (monotoneQuarterFourCellBlock parent lo start)
        (monotoneQuarterFourCellBlock parent lo start)).re <
      2 * Real.log 2 *
        (bombieriQuadraticTest
          (monotoneQuarterFourCellBlock parent lo start) 2).re := by
  have hnegative : bombieriRealQuadraticValue
      (monotoneQuarterFourCellBlock parent lo start) < 0 := by
    simpa only [monotoneQuarterFourCellBlock, hlen] using hmin.negative
  rw [bombieriRealQuadraticValue_fourCellBlock_eq_local_sub_n_two] at hnegative
  linarith

/-! ## The same obstruction between the two ratio-two halves -/

/-- The four-cell block is the sum of its two consecutive two-cell halves. -/
theorem monotoneQuarterFourCellBlock_eq_twoHalves
    (parent : BombieriTest) (lo : ℤ) (start : ℕ) :
    monotoneQuarterFourCellBlock parent lo start =
      monotoneQuarterFiniteBlock parent lo start 2 +
        monotoneQuarterFiniteBlock parent lo (start + 2) 2 := by
  unfold monotoneQuarterFourCellBlock
  simpa using
    (monotoneQuarterFiniteBlock_eq_prefix_add_suffix
      parent lo start 4 2 (by omega))

private theorem bombieriQuadraticTest_apply_two_eq_zero_of_ratioTwoCell
    (g : BombieriTest) (hcell : BombieriRatioTwoCell g) :
    bombieriQuadraticTest g 2 = 0 := by
  obtain ⟨a, b, ha, _hab, hsupport, hratio⟩ := hcell
  exact bombieriQuadraticTest_apply_two_eq_zero_of_support_ratio_le_two
    g ha hsupport hratio

/-- Endpoint cancellation in both ratio-two halves leaves exactly their
mixed factor-two quadratic cross. -/
theorem bombieriQuadraticTest_fourCellBlock_two_eq_halfCross
    (parent : BombieriTest) (lo : ℤ) (start : ℕ) :
    bombieriQuadraticTest
        (monotoneQuarterFourCellBlock parent lo start) 2 =
      bombieriQuadraticCrossTest
        (monotoneQuarterFiniteBlock parent lo start 2)
        (monotoneQuarterFiniteBlock parent lo (start + 2) 2) 2 := by
  rw [monotoneQuarterFourCellBlock_eq_twoHalves,
    bombieriQuadraticTest_add_eq_diagonal_add_cross]
  simp only [TestFunction.coe_add, Pi.add_apply]
  rw [bombieriQuadraticTest_apply_two_eq_zero_of_ratioTwoCell
      (monotoneQuarterFiniteBlock parent lo start 2)
      (monotoneQuarterFiniteBlock_ratioTwo_of_le_three
        parent lo start 2 (by omega)),
    bombieriQuadraticTest_apply_two_eq_zero_of_ratioTwoCell
      (monotoneQuarterFiniteBlock parent lo (start + 2) 2)
      (monotoneQuarterFiniteBlock_ratioTwo_of_le_three
        parent lo (start + 2) 2 (by omega))]
  ring

private theorem bombieriLocalCriticalForm_add_self_re
    (f g : BombieriTest) :
    (bombieriLocalCriticalForm (f + g) (f + g)).re =
      (bombieriLocalCriticalForm f f).re +
        (bombieriLocalCriticalForm g g).re +
        2 * (bombieriLocalCriticalForm f g).re := by
  have hconj := congrArg Complex.re
    (bombieriLocalCriticalForm_conj_apply f g)
  simp only [map_add, LinearMap.add_apply, Complex.add_re]
  simp only [Complex.star_def, Complex.conj_re] at hconj
  rw [hconj]
  ring

/-- Exact half-block form: the diagonal local reserves are nonnegative, and
the only new competition is local half-cross versus the mixed factor-two
prime cross. -/
theorem bombieriRealQuadraticValue_fourCellBlock_eq_halfLocalPrimeBalance
    (parent : BombieriTest) (lo : ℤ) (start : ℕ) :
    bombieriRealQuadraticValue
        (monotoneQuarterFourCellBlock parent lo start) =
      (bombieriLocalCriticalForm
        (monotoneQuarterFiniteBlock parent lo start 2)
        (monotoneQuarterFiniteBlock parent lo start 2)).re +
      (bombieriLocalCriticalForm
        (monotoneQuarterFiniteBlock parent lo (start + 2) 2)
        (monotoneQuarterFiniteBlock parent lo (start + 2) 2)).re +
      2 * ((bombieriLocalCriticalForm
          (monotoneQuarterFiniteBlock parent lo start 2)
          (monotoneQuarterFiniteBlock parent lo (start + 2) 2)).re -
        Real.log 2 *
          (bombieriQuadraticCrossTest
            (monotoneQuarterFiniteBlock parent lo start 2)
            (monotoneQuarterFiniteBlock parent lo (start + 2) 2) 2).re) := by
  rw [bombieriRealQuadraticValue_fourCellBlock_eq_local_sub_n_two,
    bombieriQuadraticTest_fourCellBlock_two_eq_halfCross,
    monotoneQuarterFourCellBlock_eq_twoHalves,
    bombieriLocalCriticalForm_add_self_re]
  ring

private theorem bombieriLocalCriticalForm_self_re_nonnegative_of_ratioTwoCell
    (g : BombieriTest) (hcell : BombieriRatioTwoCell g) :
    0 ≤ (bombieriLocalCriticalForm g g).re := by
  obtain ⟨a, b, ha, hab, hsupport, hratio⟩ := hcell
  have hvalue := bombieriFunctional_quadratic_re_nonneg_of_ratioTwoCell
    g ⟨a, b, ha, hab, hsupport, hratio⟩
  rw [bombieriFunctional_quadratic_eq_bombieriLocalCriticalForm_le_two
    g ha hab hsupport hratio] at hvalue
  exact hvalue

/-- The local diagonals of both two-cell halves are unconditional reserves. -/
theorem fourCellBlock_halfLocalDiagonals_nonnegative
    (parent : BombieriTest) (lo : ℤ) (start : ℕ) :
    0 ≤ (bombieriLocalCriticalForm
          (monotoneQuarterFiniteBlock parent lo start 2)
          (monotoneQuarterFiniteBlock parent lo start 2)).re ∧
      0 ≤ (bombieriLocalCriticalForm
          (monotoneQuarterFiniteBlock parent lo (start + 2) 2)
          (monotoneQuarterFiniteBlock parent lo (start + 2) 2)).re := by
  constructor
  · apply bombieriLocalCriticalForm_self_re_nonnegative_of_ratioTwoCell
    exact monotoneQuarterFiniteBlock_ratioTwo_of_le_three
      parent lo start 2 (by omega)
  · apply bombieriLocalCriticalForm_self_re_nonnegative_of_ratioTwoCell
    exact monotoneQuarterFiniteBlock_ratioTwo_of_le_three
      parent lo (start + 2) 2 (by omega)

/-- Sharp exact closure target after splitting into ratio-two halves.  Unlike
`Q(B) ≥ 0`, the right side displays the usable diagonal reserves and the one
new mixed structural estimate separately. -/
theorem bombieriRealQuadraticValue_fourCellBlock_nonnegative_iff_halfBalance
    (parent : BombieriTest) (lo : ℤ) (start : ℕ) :
    0 ≤ bombieriRealQuadraticValue
        (monotoneQuarterFourCellBlock parent lo start) ↔
      2 * Real.log 2 *
          (bombieriQuadraticCrossTest
            (monotoneQuarterFiniteBlock parent lo start 2)
            (monotoneQuarterFiniteBlock parent lo (start + 2) 2) 2).re ≤
        (bombieriLocalCriticalForm
          (monotoneQuarterFiniteBlock parent lo start 2)
          (monotoneQuarterFiniteBlock parent lo start 2)).re +
        (bombieriLocalCriticalForm
          (monotoneQuarterFiniteBlock parent lo (start + 2) 2)
          (monotoneQuarterFiniteBlock parent lo (start + 2) 2)).re +
        2 * (bombieriLocalCriticalForm
          (monotoneQuarterFiniteBlock parent lo start 2)
          (monotoneQuarterFiniteBlock parent lo (start + 2) 2)).re := by
  rw [bombieriRealQuadraticValue_fourCellBlock_eq_halfLocalPrimeBalance]
  constructor <;> intro h <;> linarith

/-- A clean non-circular sufficient condition: the local cross of the two
ratio-two halves absorbs their sole mixed factor-two prime correlation. -/
theorem bombieriRealQuadraticValue_fourCellBlock_nonnegative_of_halfLocal_dominates
    (parent : BombieriTest) (lo : ℤ) (start : ℕ)
    (hhalf :
      Real.log 2 *
          (bombieriQuadraticCrossTest
            (monotoneQuarterFiniteBlock parent lo start 2)
            (monotoneQuarterFiniteBlock parent lo (start + 2) 2) 2).re ≤
        (bombieriLocalCriticalForm
          (monotoneQuarterFiniteBlock parent lo start 2)
          (monotoneQuarterFiniteBlock parent lo (start + 2) 2)).re) :
    0 ≤ bombieriRealQuadraticValue
      (monotoneQuarterFourCellBlock parent lo start) := by
  have hdiag := fourCellBlock_halfLocalDiagonals_nonnegative
    parent lo start
  rw [bombieriRealQuadraticValue_fourCellBlock_eq_halfLocalPrimeBalance]
  linarith

/-! ## Overlapping ratio-two reserves and the remote corner -/

/-- Inclusion-exclusion for two overlapping blocks.  The only term not
contained in the two blocks or their overlap is the remote endpoint cross. -/
theorem bombieriRealQuadraticValue_threeTerm_overlap
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

private theorem fourCellBlock_eq_endpoint_middle_endpoint
    (parent : BombieriTest) (lo : ℤ) (start : ℕ) :
    monotoneQuarterFourCellBlock parent lo start =
      (monotoneQuarterFiniteBlock parent lo start 1 +
          monotoneQuarterFiniteBlock parent lo (start + 1) 2) +
        monotoneQuarterFiniteBlock parent lo (start + 3) 1 := by
  rw [monotoneQuarterFourCellBlock]
  have hfirst := monotoneQuarterFiniteBlock_eq_prefix_add_suffix
    parent lo start 4 1 (by omega)
  have hsecond := monotoneQuarterFiniteBlock_eq_prefix_add_suffix
    parent lo (start + 1) 3 2 (by omega)
  calc
    monotoneQuarterFiniteBlock parent lo start 4 =
        monotoneQuarterFiniteBlock parent lo start 1 +
          monotoneQuarterFiniteBlock parent lo (start + 1) 3 := hfirst
    _ = monotoneQuarterFiniteBlock parent lo start 1 +
        (monotoneQuarterFiniteBlock parent lo (start + 1) 2 +
          monotoneQuarterFiniteBlock parent lo (start + 3) 1) := by
      rw [hsecond]
    _ = (monotoneQuarterFiniteBlock parent lo start 1 +
          monotoneQuarterFiniteBlock parent lo (start + 1) 2) +
        monotoneQuarterFiniteBlock parent lo (start + 3) 1 := by
      abel

/-- Exact overlap formula for the four-cell block. -/
theorem bombieriRealQuadraticValue_fourCellBlock_eq_overlapping_reserves
    (parent : BombieriTest) (lo : ℤ) (start : ℕ) :
    bombieriRealQuadraticValue
        (monotoneQuarterFourCellBlock parent lo start) =
      bombieriRealQuadraticValue
          (monotoneQuarterFiniteBlock parent lo start 3) +
        bombieriRealQuadraticValue
          (monotoneQuarterFiniteBlock parent lo (start + 1) 3) -
        bombieriRealQuadraticValue
          (monotoneQuarterFiniteBlock parent lo (start + 1) 2) +
        2 * (bombieriTwoBlockGlobalCrossSymbol
          (monotoneQuarterFiniteBlock parent lo start 1)
          (monotoneQuarterFiniteBlock parent lo (start + 3) 1)).re := by
  let left := monotoneQuarterFiniteBlock parent lo start 1
  let middle := monotoneQuarterFiniteBlock parent lo (start + 1) 2
  let right := monotoneQuarterFiniteBlock parent lo (start + 3) 1
  have hwhole : monotoneQuarterFourCellBlock parent lo start =
      (left + middle) + right := by
    simpa only [left, middle, right] using
      fourCellBlock_eq_endpoint_middle_endpoint parent lo start
  have hleftMiddle : left + middle =
      monotoneQuarterFiniteBlock parent lo start 3 := by
    simpa only [left, middle, Nat.add_sub_cancel] using
      (monotoneQuarterFiniteBlock_eq_prefix_add_suffix
        parent lo start 3 1 (by omega)).symm
  have hmiddleRight : middle + right =
      monotoneQuarterFiniteBlock parent lo (start + 1) 3 := by
    simpa only [middle, right, Nat.add_assoc, Nat.add_sub_cancel] using
      (monotoneQuarterFiniteBlock_eq_prefix_add_suffix
        parent lo (start + 1) 3 2 (by omega)).symm
  rw [hwhole,
    bombieriRealQuadraticValue_threeTerm_overlap,
    hleftMiddle, hmiddleRight]

/-- Both overlapping three-cell blocks and their two-cell intersection are
unconditionally nonnegative. -/
theorem fourCellBlock_overlapping_reserves_nonnegative
    (parent : BombieriTest) (lo : ℤ) (start : ℕ) :
    0 ≤ bombieriRealQuadraticValue
        (monotoneQuarterFiniteBlock parent lo start 3) ∧
      0 ≤ bombieriRealQuadraticValue
        (monotoneQuarterFiniteBlock parent lo (start + 1) 3) ∧
      0 ≤ bombieriRealQuadraticValue
        (monotoneQuarterFiniteBlock parent lo (start + 1) 2) := by
  exact ⟨
    bombieriRealQuadraticValue_monotoneQuarterFiniteBlock_nonnegative_of_le_three
      parent lo start 3 (by omega),
    bombieriRealQuadraticValue_monotoneQuarterFiniteBlock_nonnegative_of_le_three
      parent lo (start + 1) 3 (by omega),
    bombieriRealQuadraticValue_monotoneQuarterFiniteBlock_nonnegative_of_le_three
      parent lo (start + 1) 2 (by omega)⟩

/-- The precise additional structural fact that would close the four-cell
case: the overlap reserve must be paid by the two three-cell reserves plus the
remote endpoint cross. -/
theorem bombieriRealQuadraticValue_fourCellBlock_nonnegative_iff_corner_bound
    (parent : BombieriTest) (lo : ℤ) (start : ℕ) :
    0 ≤ bombieriRealQuadraticValue
        (monotoneQuarterFourCellBlock parent lo start) ↔
      bombieriRealQuadraticValue
          (monotoneQuarterFiniteBlock parent lo (start + 1) 2) ≤
        bombieriRealQuadraticValue
            (monotoneQuarterFiniteBlock parent lo start 3) +
          bombieriRealQuadraticValue
            (monotoneQuarterFiniteBlock parent lo (start + 1) 3) +
          2 * (bombieriTwoBlockGlobalCrossSymbol
            (monotoneQuarterFiniteBlock parent lo start 1)
            (monotoneQuarterFiniteBlock parent lo (start + 3) 1)).re := by
  rw [bombieriRealQuadraticValue_fourCellBlock_eq_overlapping_reserves]
  constructor <;> intro h <;> linarith

/-- A minimal negative block of length four forces the strict reverse remote
corner inequality. -/
theorem supportMinimalNegativeMonotoneBlock_length_four_corner_deficit
    {parent : BombieriTest} {lo : ℤ} {n start len : ℕ}
    (hmin : IsSupportMinimalNegativeMonotoneBlock
      parent lo n start len) (hlen : len = 4) :
    bombieriRealQuadraticValue
        (monotoneQuarterFiniteBlock parent lo start 3) +
      bombieriRealQuadraticValue
        (monotoneQuarterFiniteBlock parent lo (start + 1) 3) +
      2 * (bombieriTwoBlockGlobalCrossSymbol
        (monotoneQuarterFiniteBlock parent lo start 1)
        (monotoneQuarterFiniteBlock parent lo (start + 3) 1)).re <
      bombieriRealQuadraticValue
        (monotoneQuarterFiniteBlock parent lo (start + 1) 2) := by
  have hnegative : bombieriRealQuadraticValue
      (monotoneQuarterFourCellBlock parent lo start) < 0 := by
    simpa only [monotoneQuarterFourCellBlock, hlen] using hmin.negative
  rw [bombieriRealQuadraticValue_fourCellBlock_eq_overlapping_reserves]
    at hnegative
  linarith

/-! ## Algebraic sharpness of the remaining corner -/

/-- Nonnegativity of the two overlapping blocks and their intersection does
not, by itself, sign the inclusion-exclusion expression. -/
theorem overlapping_reserve_signs_do_not_force_corner_expression :
    ¬ ∀ L R M X : ℝ,
      0 ≤ L → 0 ≤ R → 0 ≤ M →
        0 ≤ L + R - M + 2 * X := by
  intro h
  have hbad := h 0 0 0 (-1) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hbad

/-- In fact no constant multiple of the three nonnegative reserves can give
a lower bound for the remote corner using only those signs. -/
theorem no_constant_corner_bound_from_overlapping_reserve_signs
    (C : ℝ) :
    ¬ ∀ L R M X : ℝ,
      0 ≤ L → 0 ≤ R → 0 ≤ M →
        -(C * (L + R + M)) ≤ X := by
  intro h
  have hbad := h 0 0 0 (-1) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hbad

end

end ArithmeticHodge.Analysis.MultiplicativeWeilMinimalFourCellBlockStructural
