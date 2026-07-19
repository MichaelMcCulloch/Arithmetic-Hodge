import ArithmeticHodge.Analysis.MultiplicativeWeilMinimalNegativeBlockStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilPrimeCorrelation

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ArithmeticFunction BigOperators

namespace ArithmeticHodge.Analysis.MultiplicativeWeilBelowThreePrimeReductionStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilMinimalNegativeBlockStructural
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural
open MultiplicativeWeilRealMonotonePropagationCriterionStructural

/-!
# Exact prime reduction below support ratio three

If a Bombieri seed is supported in a positive interval of multiplicative
width strictly below three, its quadratic autocorrelation is supported below
the first integer `3`.  The `n = 1` Mangoldt coefficient is zero, every
integer `n >= 3` misses the support, and therefore the entire prime functional
is exactly its `n = 2` summand.

This is especially adapted to four consecutive quarter-lattice cells: their
support ratio is `2 * 2^(1/4) < 3`.  The resulting positivity condition is an
explicit domination of one normalized factor-two correlation by the local
critical energy, rather than a hypothesis involving the global Bombieri
quadratic itself.
-/

/-! ## The unique surviving Mangoldt atom -/

/-- At every real ratio at least three, the autocorrelation of a seed whose
support ratio is strictly below three vanishes. -/
theorem bombieriQuadraticTest_apply_eq_zero_of_three_le
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

/-- Hence every prime kernel with natural index at least two (`n = k+1 >= 3`)
vanishes. -/
theorem primeKernel_bombieriQuadraticTest_eq_zero_of_two_le
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a < 3) {k : ℕ} (hk : 2 ≤ k) :
    primeKernel (bombieriQuadraticTest g) k = 0 := by
  have hx : 3 ≤ (((k + 1 : ℕ) : ℝ)) := by
    exact_mod_cast (show 3 ≤ k + 1 by omega)
  have hzero := bombieriQuadraticTest_apply_eq_zero_of_three_le
    g ha hab hsupport hratio hx
  rw [primeKernel_bombieriQuadraticTest_eq_two_re, hzero]
  norm_num

/-- Weighted form of the preceding support vanishing. -/
theorem vonMangoldtPrimeSummand_bombieriQuadraticTest_eq_zero_of_two_le
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a < 3) {k : ℕ} (hk : 2 ≤ k) :
    vonMangoldtPrimeSummand (bombieriQuadraticTest g) k = 0 := by
  unfold vonMangoldtPrimeSummand
  rw [primeKernel_bombieriQuadraticTest_eq_zero_of_two_le
    g ha hab hsupport hratio hk, mul_zero]

/-- Below support ratio three, the infinite prime functional is exactly the
single summand at `k = 1`, i.e. the classical integer `n = 2`. -/
theorem primeSum_bombieriQuadraticTest_eq_n_two_of_support_ratio_lt_three
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
    exact vonMangoldtPrimeSummand_bombieriQuadraticTest_eq_zero_of_two_le
      g ha hab hsupport hratio hkTwo)]
  norm_num [Finset.sum_range_succ, vonMangoldtPrimeSummand]

/-- The surviving atom in its direct quadratic-correlation form. -/
theorem n_two_vonMangoldtPrimeSummand_quadratic_eq_log_two_mul_two_re
    (g : BombieriTest) :
    vonMangoldtPrimeSummand (bombieriQuadraticTest g) 1 =
      (Real.log 2 : ℂ) *
        ((2 * (bombieriQuadraticTest g 2).re : ℝ) : ℂ) := by
  unfold vonMangoldtPrimeSummand
  rw [ArithmeticFunction.vonMangoldt_apply_prime
      (by norm_num : Nat.Prime 2),
    primeKernel_bombieriQuadraticTest_eq_two_re]
  norm_num

/-- Sharp normalized-dilation form of the same atom. -/
theorem n_two_vonMangoldtPrimeSummand_quadratic_eq_dilationCorrelation
    (g : BombieriTest) :
    vonMangoldtPrimeSummand (bombieriQuadraticTest g) 1 =
      (((Real.sqrt 2 * Real.log 2 *
        (criticalDilationCorrelation g 2).re : ℝ) : ℂ)) := by
  have hcorr := congrArg Complex.re
    (criticalDilationCorrelation_eq_sqrt_mul_quadraticTest g 2)
  rw [n_two_vonMangoldtPrimeSummand_quadratic_eq_log_two_mul_two_re]
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_cast
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hcorr
  rw [hcorr]
  calc
    Real.log 2 * (2 * (bombieriQuadraticTest g 2).re) =
        (Real.sqrt 2 * Real.sqrt 2) * Real.log 2 *
          (bombieriQuadraticTest g 2).re := by rw [hsqrt]; ring
    _ = Real.sqrt 2 * Real.log 2 *
          (Real.sqrt 2 * (bombieriQuadraticTest g 2).re) := by ring

/-- Exact complete quadratic formula in the below-three regime. -/
theorem bombieriFunctional_quadratic_eq_localCritical_sub_n_two
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a < 3) :
    bombieriFunctional (bombieriQuadraticTest g) =
      bombieriLocalCriticalForm g g -
        vonMangoldtPrimeSummand (bombieriQuadraticTest g) 1 := by
  rw [bombieriFunctional_quadratic_eq_localCritical_sub_prime,
    primeSum_bombieriQuadraticTest_eq_n_two_of_support_ratio_lt_three
      g ha hab hsupport hratio]

/-- Exact real formula after rewriting the unique atom as a normalized
factor-two correlation. -/
theorem bombieriFunctional_quadratic_re_eq_localCritical_sub_dilationCorrelation
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a < 3) :
    (bombieriFunctional (bombieriQuadraticTest g)).re =
      (bombieriLocalCriticalForm g g).re -
        Real.sqrt 2 * Real.log 2 *
          (criticalDilationCorrelation g 2).re := by
  rw [bombieriFunctional_quadratic_eq_localCritical_sub_n_two
      g ha hab hsupport hratio,
    n_two_vonMangoldtPrimeSummand_quadratic_eq_dilationCorrelation]
  rfl

/-- Below support ratio three, nonnegativity is exactly one explicit local
critical domination inequality.  This condition contains no occurrence of
the global Bombieri quadratic and is therefore non-circular. -/
theorem bombieriFunctional_quadratic_re_nonnegative_iff_local_dominates_n_two
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a < 3) :
    0 ≤ (bombieriFunctional (bombieriQuadraticTest g)).re ↔
      Real.sqrt 2 * Real.log 2 *
          (criticalDilationCorrelation g 2).re ≤
        (bombieriLocalCriticalForm g g).re := by
  rw [bombieriFunctional_quadratic_re_eq_localCritical_sub_dilationCorrelation
    g ha hab hsupport hratio]
  constructor <;> intro h <;> linarith

/-- Direct sufficient form of the preceding exact criterion. -/
theorem bombieriFunctional_quadratic_re_nonnegative_of_local_dominates_n_two
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a < 3)
    (hdom : Real.sqrt 2 * Real.log 2 *
          (criticalDilationCorrelation g 2).re ≤
        (bombieriLocalCriticalForm g g).re) :
    0 ≤ (bombieriFunctional (bombieriQuadraticTest g)).re :=
  (bombieriFunctional_quadratic_re_nonnegative_iff_local_dominates_n_two
    g ha hab hsupport hratio).2 hdom

/-! ## Four coherent quarter cells -/

/-- Four consecutive cells of the canonical monotone partition. -/
def monotoneQuarterFourCellBlock
    (parent : BombieriTest) (lo : ℤ) (start : ℕ) : BombieriTest :=
  monotoneQuarterFiniteBlock parent lo start 4

private theorem tsupport_finset_sum_subset_Icc_belowThree
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

/-- The four-cell block is supported between the first boundary and the
fifth later quarter-lattice point. -/
theorem monotoneQuarterFourCellBlock_tsupport_subset
    (parent : BombieriTest) (lo : ℤ) (start : ℕ) :
    tsupport (monotoneQuarterFourCellBlock parent lo start) ⊆
      Set.Icc (quarterLogLatticePoint (lo + (start : ℤ)))
        (quarterLogLatticePoint (lo + (start : ℤ) + 5)) := by
  classical
  unfold monotoneQuarterFourCellBlock monotoneQuarterFiniteBlock
  apply tsupport_finset_sum_subset_Icc_belowThree
  intro i hi
  have hiFour : i < 4 := Finset.mem_range.mp hi
  have hcell := monotoneQuarterCell_tsupport_subset parent
    (lo + ((start + i : ℕ) : ℤ))
  apply hcell.trans
  apply Set.Icc_subset_Icc
  · apply quarterLogLatticePoint_mono
    push_cast
    omega
  · apply quarterLogLatticePoint_mono
    push_cast
    omega

/-- One quarter-lattice step is strictly below `6/5`; the proof uses its
exact fourth power rather than a floating-point approximation. -/
theorem quarterLogLatticePoint_one_lt_six_fifths_belowThree :
    quarterLogLatticePoint 1 < (6 / 5 : ℝ) := by
  have hpow : quarterLogLatticePoint 1 ^ 4 = 2 := by
    unfold quarterLogLatticePoint
    norm_num
    rw [← Real.exp_nat_mul]
    convert Real.exp_log (by norm_num : (0 : ℝ) < 2) using 1
    ring_nf
  apply lt_of_pow_lt_pow_left₀ 4 (by norm_num : (0 : ℝ) ≤ 6 / 5)
  rw [hpow]
  norm_num

/-- The support interval of four consecutive cells has ratio strictly below
three.  In fact its ratio is `2 * 2^(1/4) < 12/5`. -/
theorem monotoneQuarterFourCellBlock_endpoint_ratio_lt_three
    (lo : ℤ) (start : ℕ) :
    quarterLogLatticePoint (lo + (start : ℤ) + 5) /
        quarterLogLatticePoint (lo + (start : ℤ)) < 3 := by
  let k : ℤ := lo + (start : ℤ)
  have hkpos := quarterLogLatticePoint_pos k
  calc
    quarterLogLatticePoint (lo + (start : ℤ) + 5) /
          quarterLogLatticePoint (lo + (start : ℤ)) =
        quarterLogLatticePoint (k + 5) / quarterLogLatticePoint k := by
          rfl
    _ = (2 * quarterLogLatticePoint (k + 1)) /
          quarterLogLatticePoint k := by
          rw [show k + 5 = (k + 1) + 4 by ring,
            quarterLogLatticePoint_add_four]
    _ = 2 * quarterLogLatticePoint 1 := by
          rw [quarterLogLatticePoint_add]
          field_simp [hkpos.ne']
    _ < 3 := by
          nlinarith [quarterLogLatticePoint_one_lt_six_fifths_belowThree]

/-- Exact below-three formula specialized to four common-parent cells. -/
theorem bombieriFunctional_fourCell_re_eq_localCritical_sub_dilationCorrelation
    (parent : BombieriTest) (lo : ℤ) (start : ℕ) :
    (bombieriFunctional
      (bombieriQuadraticTest
        (monotoneQuarterFourCellBlock parent lo start))).re =
      (bombieriLocalCriticalForm
        (monotoneQuarterFourCellBlock parent lo start)
        (monotoneQuarterFourCellBlock parent lo start)).re -
      Real.sqrt 2 * Real.log 2 *
        (criticalDilationCorrelation
          (monotoneQuarterFourCellBlock parent lo start) 2).re := by
  exact bombieriFunctional_quadratic_re_eq_localCritical_sub_dilationCorrelation
    (monotoneQuarterFourCellBlock parent lo start)
    (a := quarterLogLatticePoint (lo + (start : ℤ)))
    (b := quarterLogLatticePoint (lo + (start : ℤ) + 5))
    (quarterLogLatticePoint_pos _)
    (quarterLogLatticePoint_mono (by omega))
    (monotoneQuarterFourCellBlock_tsupport_subset parent lo start)
    (monotoneQuarterFourCellBlock_endpoint_ratio_lt_three lo start)

/-- Real local energy of a sum, with its Hermitian cross combined. -/
theorem bombieriLocalCriticalForm_add_self_re
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

private theorem bombieriLocalCriticalForm_self_re_nonnegative_of_ratioTwoCell
    (g : BombieriTest) (hcell : BombieriRatioTwoCell g) :
    0 ≤ (bombieriLocalCriticalForm g g).re := by
  obtain ⟨a, b, ha, hab, hsupport, hratio⟩ := hcell
  have hvalue := bombieriFunctional_quadratic_re_nonneg_of_ratioTwoCell
    g ⟨a, b, ha, hab, hsupport, hratio⟩
  rw [bombieriFunctional_quadratic_eq_bombieriLocalCriticalForm_le_two
    g ha hab hsupport hratio] at hvalue
  exact hvalue

/-- A four-cell block splits into two consecutive two-cell ratio-two pieces. -/
theorem monotoneQuarterFourCellBlock_eq_twoHalves
    (parent : BombieriTest) (lo : ℤ) (start : ℕ) :
    monotoneQuarterFourCellBlock parent lo start =
      monotoneQuarterFiniteBlock parent lo start 2 +
        monotoneQuarterFiniteBlock parent lo (start + 2) 2 := by
  unfold monotoneQuarterFourCellBlock
  simpa using
    (monotoneQuarterFiniteBlock_eq_prefix_add_suffix
      parent lo start 4 2 (by omega))

/-- The two half-block local diagonals are unconditionally nonnegative. -/
theorem bombieriLocalCriticalForm_fourCellHalves_diagonal_nonnegative
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

private theorem bombieriQuadraticTest_apply_two_eq_zero_of_ratioTwoCell
    (g : BombieriTest) (hcell : BombieriRatioTwoCell g) :
    bombieriQuadraticTest g 2 = 0 := by
  obtain ⟨a, b, ha, _hab, hsupport, hratio⟩ := hcell
  exact bombieriQuadraticTest_apply_two_eq_zero_of_support_ratio_le_two
    g ha hsupport hratio

/-- If two blocks separately have support ratio at most two, the factor-two
correlation of their sum contains only their mixed quadratic test: both
diagonal factor-two autocorrelations vanish at the endpoint. -/
theorem criticalDilationCorrelation_add_eq_sqrt_two_mul_quadraticCross
    (f g : BombieriTest)
    (hf : BombieriRatioTwoCell f) (hg : BombieriRatioTwoCell g) :
    criticalDilationCorrelation (f + g) 2 =
      (Real.sqrt 2 : ℂ) * bombieriQuadraticCrossTest f g 2 := by
  rw [criticalDilationCorrelation_eq_sqrt_mul_quadraticTest,
    bombieriQuadraticTest_add_eq_diagonal_add_cross]
  simp only [TestFunction.coe_add, Pi.add_apply]
  rw [bombieriQuadraticTest_apply_two_eq_zero_of_ratioTwoCell f hf,
    bombieriQuadraticTest_apply_two_eq_zero_of_ratioTwoCell g hg]
  ring

/-- For four consecutive common-parent cells, the unique factor-two
correlation is exactly the mixed factor-two test between its two two-cell
halves. -/
theorem criticalDilationCorrelation_fourCell_eq_sqrt_two_mul_halfCross
    (parent : BombieriTest) (lo : ℤ) (start : ℕ) :
    criticalDilationCorrelation
        (monotoneQuarterFourCellBlock parent lo start) 2 =
      (Real.sqrt 2 : ℂ) *
        bombieriQuadraticCrossTest
          (monotoneQuarterFiniteBlock parent lo start 2)
          (monotoneQuarterFiniteBlock parent lo (start + 2) 2) 2 := by
  rw [monotoneQuarterFourCellBlock_eq_twoHalves]
  apply criticalDilationCorrelation_add_eq_sqrt_two_mul_quadraticCross
  · exact monotoneQuarterFiniteBlock_ratioTwo_of_le_three
      parent lo start 2 (by omega)
  · exact monotoneQuarterFiniteBlock_ratioTwo_of_le_three
      parent lo (start + 2) 2 (by omega)

/-- Consequently the sole Mangoldt term of four coherent cells is exactly
`2 log 2` times the real mixed factor-two correlation of the two halves. -/
theorem n_two_vonMangoldtPrimeSummand_fourCell_eq_halfCross
    (parent : BombieriTest) (lo : ℤ) (start : ℕ) :
    vonMangoldtPrimeSummand
        (bombieriQuadraticTest
          (monotoneQuarterFourCellBlock parent lo start)) 1 =
      (((2 * Real.log 2 *
        (bombieriQuadraticCrossTest
          (monotoneQuarterFiniteBlock parent lo start 2)
          (monotoneQuarterFiniteBlock parent lo (start + 2) 2) 2).re : ℝ) : ℂ)) := by
  rw [n_two_vonMangoldtPrimeSummand_quadratic_eq_dilationCorrelation,
    criticalDilationCorrelation_fourCell_eq_sqrt_two_mul_halfCross]
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_cast
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  calc
    Real.sqrt 2 * Real.log 2 *
          (Real.sqrt 2 *
            (bombieriQuadraticCrossTest
              (monotoneQuarterFiniteBlock parent lo start 2)
              (monotoneQuarterFiniteBlock parent lo (start + 2) 2) 2).re) =
        (Real.sqrt 2 * Real.sqrt 2) * Real.log 2 *
          (bombieriQuadraticCrossTest
            (monotoneQuarterFiniteBlock parent lo start 2)
            (monotoneQuarterFiniteBlock parent lo (start + 2) 2) 2).re := by ring
    _ = 2 * Real.log 2 *
          (bombieriQuadraticCrossTest
            (monotoneQuarterFiniteBlock parent lo start 2)
            (monotoneQuarterFiniteBlock parent lo (start + 2) 2) 2).re := by
      rw [hsqrt]

/-- Non-circular common-parent sufficient inequality for four cells.  Since
both half-block diagonals are already nonnegative, it is enough for twice
their local critical cross to absorb the unique `n = 2` atom of the whole
four-cell block. -/
theorem bombieriFunctional_fourCell_re_nonnegative_of_halfLocalCross_absorbs_n_two
    (parent : BombieriTest) (lo : ℤ) (start : ℕ)
    (habsorb :
      Real.sqrt 2 * Real.log 2 *
          (criticalDilationCorrelation
            (monotoneQuarterFourCellBlock parent lo start) 2).re ≤
        2 * (bombieriLocalCriticalForm
          (monotoneQuarterFiniteBlock parent lo start 2)
          (monotoneQuarterFiniteBlock parent lo (start + 2) 2)).re) :
    0 ≤ (bombieriFunctional
      (bombieriQuadraticTest
        (monotoneQuarterFourCellBlock parent lo start))).re := by
  have hdiagonal :=
    bombieriLocalCriticalForm_fourCellHalves_diagonal_nonnegative
      parent lo start
  have hsplit := monotoneQuarterFourCellBlock_eq_twoHalves parent lo start
  rw [hsplit] at habsorb
  have hlocal :
      Real.sqrt 2 * Real.log 2 *
          (criticalDilationCorrelation
            (monotoneQuarterFourCellBlock parent lo start) 2).re ≤
        (bombieriLocalCriticalForm
          (monotoneQuarterFourCellBlock parent lo start)
          (monotoneQuarterFourCellBlock parent lo start)).re := by
    rw [hsplit, bombieriLocalCriticalForm_add_self_re]
    linarith
  rw [bombieriFunctional_fourCell_re_eq_localCritical_sub_dilationCorrelation]
  linarith

/-- Sharper half-block form of the sufficient inequality.  After exact
endpoint cancellation, the factor `sqrt 2` disappears: it suffices that the
local cross of the two ratio-two halves dominate `log 2` times their mixed
quadratic value at the single ratio `2`. -/
theorem bombieriFunctional_fourCell_re_nonnegative_of_halfLocal_dominates_halfPrime
    (parent : BombieriTest) (lo : ℤ) (start : ℕ)
    (hhalf :
      Real.log 2 *
          (bombieriQuadraticCrossTest
            (monotoneQuarterFiniteBlock parent lo start 2)
            (monotoneQuarterFiniteBlock parent lo (start + 2) 2) 2).re ≤
        (bombieriLocalCriticalForm
          (monotoneQuarterFiniteBlock parent lo start 2)
          (monotoneQuarterFiniteBlock parent lo (start + 2) 2)).re) :
    0 ≤ (bombieriFunctional
      (bombieriQuadraticTest
        (monotoneQuarterFourCellBlock parent lo start))).re := by
  apply
    bombieriFunctional_fourCell_re_nonnegative_of_halfLocalCross_absorbs_n_two
  rw [criticalDilationCorrelation_fourCell_eq_sqrt_two_mul_halfCross]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    Real.sqrt 2 * Real.log 2 *
          (Real.sqrt 2 *
            (bombieriQuadraticCrossTest
              (monotoneQuarterFiniteBlock parent lo start 2)
              (monotoneQuarterFiniteBlock parent lo (start + 2) 2) 2).re) =
        2 * (Real.log 2 *
          (bombieriQuadraticCrossTest
            (monotoneQuarterFiniteBlock parent lo start 2)
            (monotoneQuarterFiniteBlock parent lo (start + 2) 2) 2).re) := by
              rw [show Real.sqrt 2 * Real.log 2 *
                  (Real.sqrt 2 *
                    (bombieriQuadraticCrossTest
                      (monotoneQuarterFiniteBlock parent lo start 2)
                      (monotoneQuarterFiniteBlock parent lo (start + 2) 2) 2).re) =
                  (Real.sqrt 2 * Real.sqrt 2) * Real.log 2 *
                    (bombieriQuadraticCrossTest
                      (monotoneQuarterFiniteBlock parent lo start 2)
                      (monotoneQuarterFiniteBlock parent lo (start + 2) 2) 2).re by ring,
                hsqrt]
              ring
    _ ≤ 2 * (bombieriLocalCriticalForm
          (monotoneQuarterFiniteBlock parent lo start 2)
          (monotoneQuarterFiniteBlock parent lo (start + 2) 2)).re :=
      mul_le_mul_of_nonneg_left hhalf (by norm_num)

/-- Useful antiphase subclass: a nonpositive factor-two physical correlation
and a nonnegative local cross between the two common-parent halves imply the
four-cell Bombieri quadratic is nonnegative. -/
theorem bombieriFunctional_fourCell_re_nonnegative_of_antiphase_of_halfLocalCross_nonnegative
    (parent : BombieriTest) (lo : ℤ) (start : ℕ)
    (hantiphase :
      (criticalDilationCorrelation
        (monotoneQuarterFourCellBlock parent lo start) 2).re ≤ 0)
    (hcross : 0 ≤ (bombieriLocalCriticalForm
      (monotoneQuarterFiniteBlock parent lo start 2)
      (monotoneQuarterFiniteBlock parent lo (start + 2) 2)).re) :
    0 ≤ (bombieriFunctional
      (bombieriQuadraticTest
        (monotoneQuarterFourCellBlock parent lo start))).re := by
  apply
    bombieriFunctional_fourCell_re_nonnegative_of_halfLocalCross_absorbs_n_two
  have hcoefficient : 0 ≤ Real.sqrt 2 * Real.log 2 :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by norm_num))
  have hleft : Real.sqrt 2 * Real.log 2 *
      (criticalDilationCorrelation
        (monotoneQuarterFourCellBlock parent lo start) 2).re ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hcoefficient hantiphase
  exact hleft.trans (by linarith)

end

end ArithmeticHodge.Analysis.MultiplicativeWeilBelowThreePrimeReductionStructural
