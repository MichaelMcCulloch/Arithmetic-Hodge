import ArithmeticHodge.Analysis.MultiplicativeWeilMonotonePrimeAtomAbsorptionStructural

set_option autoImplicit false

open Complex Real Set
open scoped ArithmeticFunction BigOperators

namespace ArithmeticHodge.Analysis.MultiplicativeWeilMonotonePrimeAtomAggregateStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilMonotonePrimeAtomAbsorptionStructural
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilMonotoneRatioTwoBlockPropagationStructural
open MultiplicativeWeilRealLogKernelStructural
open MultiplicativeWeilRealMonotonePropagationCriterionStructural
open MultiplicativeWeilRealMonotonePropagationLogDefectStructural

/-!
# Coherent aggregation of the monotone prime atoms

Every transplanted Mangoldt slice from the one-step monotone row lies in the
same ratio-two plateau around the head.  Instead of applying a determinant to
each atom separately, form their weighted sum first and apply one determinant
to the resulting physical test.  This avoids paying one copy of the head
diagonal for every nonzero prime atom.
-/

/-- The uncut weighted sum of the normalized suffix dilates associated to a
finite set of Mangoldt atoms. -/
def monotonePrimeAtomAggregateSource
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) : BombieriTest :=
  ∑ j ∈ S,
    ((bombieriLogPrimeAtomWeight j : ℝ) : ℂ) •
      normalizedDilation ((j + 1 : ℕ) : ℝ) (by positivity)
        (monotoneQuarterCutoff parent (k + 1))

/-- All selected prime transports, coherently cut by their common ratio-two
plateau. -/
def monotonePrimeAtomAggregateSlice
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) : BombieriTest :=
  monotoneRatioTwoBlock
    (monotonePrimeAtomAggregateSource parent k S) (k - 1)

private theorem monotoneRatioTwoBlock_add
    (f g : BombieriTest) (k : ℤ) :
    monotoneRatioTwoBlock (f + g) k =
      monotoneRatioTwoBlock f k + monotoneRatioTwoBlock g k := by
  apply TestFunction.ext
  intro x
  simp only [monotoneRatioTwoBlock_apply, TestFunction.coe_add,
    Pi.add_apply]
  ring

private theorem monotoneRatioTwoBlock_smul
    (c : ℂ) (f : BombieriTest) (k : ℤ) :
    monotoneRatioTwoBlock (c • f) k =
      c • monotoneRatioTwoBlock f k := by
  apply TestFunction.ext
  intro x
  simp only [monotoneRatioTwoBlock_apply, TestFunction.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  ring

private theorem monotoneRatioTwoBlock_zero (k : ℤ) :
    monotoneRatioTwoBlock (0 : BombieriTest) k = 0 := by
  apply TestFunction.ext
  intro x
  simp only [monotoneRatioTwoBlock_apply, TestFunction.coe_zero,
    Pi.zero_apply, mul_zero]

private theorem monotoneRatioTwoBlock_finset_sum
    {J : Type*} [DecidableEq J] (S : Finset J)
    (f : J → BombieriTest) (k : ℤ) :
    monotoneRatioTwoBlock (∑ j ∈ S, f j) k =
      ∑ j ∈ S, monotoneRatioTwoBlock (f j) k := by
  induction S using Finset.induction_on with
  | empty => simp [monotoneRatioTwoBlock_zero]
  | @insert j S hj ih =>
      simp only [Finset.sum_insert, hj, not_false_eq_true,
        monotoneRatioTwoBlock_add, ih]

/-- Cutting commutes with the finite weighted sum, so the aggregate slice is
exactly the sum of the individually transplanted slices. -/
theorem monotonePrimeAtomAggregateSlice_eq_sum
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) :
    monotonePrimeAtomAggregateSlice parent k S =
      ∑ j ∈ S,
        ((bombieriLogPrimeAtomWeight j : ℝ) : ℂ) •
          monotonePrimeAtomTransplantedSlice parent k j := by
  unfold monotonePrimeAtomAggregateSlice monotonePrimeAtomAggregateSource
  rw [monotoneRatioTwoBlock_finset_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [monotoneRatioTwoBlock_smul]
  rfl

/-- The head and the whole aggregate slice are one honest ratio-two block:
the common plateau acts as the identity on the head. -/
theorem monotoneRatioTwoBlock_head_add_smul_aggregateSource
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) (c : ℂ) :
    monotoneRatioTwoBlock
        (monotoneQuarterCell parent k +
          c • monotonePrimeAtomAggregateSource parent k S) (k - 1) =
      monotoneQuarterCell parent k +
        c • monotonePrimeAtomAggregateSlice parent k S := by
  apply TestFunction.ext
  intro x
  simp only [monotoneRatioTwoBlock_apply, TestFunction.coe_add,
    Pi.add_apply, TestFunction.coe_smul, Pi.smul_apply, smul_eq_mul,
    monotoneQuarterCell_apply, monotonePrimeAtomAggregateSlice]
  have habsorb := monotonePrimeAtomPlateauMultiplier_mul_headWeight k x
  change
    ((monotonePrimeAtomPlateauMultiplier k x : ℝ) : ℂ) *
          (((monotoneQuarterWeight k x : ℝ) : ℂ) * parent x +
            c * monotonePrimeAtomAggregateSource parent k S x) =
      ((monotoneQuarterWeight k x : ℝ) : ℂ) * parent x +
        c * (((monotonePrimeAtomPlateauMultiplier k x : ℝ) : ℂ) *
          monotonePrimeAtomAggregateSource parent k S x)
  calc
    ((monotonePrimeAtomPlateauMultiplier k x : ℝ) : ℂ) *
          (((monotoneQuarterWeight k x : ℝ) : ℂ) * parent x +
            c * monotonePrimeAtomAggregateSource parent k S x) =
        (((monotonePrimeAtomPlateauMultiplier k x *
            monotoneQuarterWeight k x : ℝ) : ℂ) * parent x) +
          c * (((monotonePrimeAtomPlateauMultiplier k x : ℝ) : ℂ) *
            monotonePrimeAtomAggregateSource parent k S x) := by
              push_cast
              ring
    _ = _ := by rw [habsorb]

/-- Every scalar pencil on the head and the coherently aggregated slice has
ratio-two support. -/
theorem monotonePrimeAtom_head_add_smul_aggregateSlice_ratioTwo
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) (c : ℂ) :
    BombieriRatioTwoCell
      (monotoneQuarterCell parent k +
        c • monotonePrimeAtomAggregateSlice parent k S) := by
  rw [← monotoneRatioTwoBlock_head_add_smul_aggregateSource]
  exact monotoneRatioTwoBlock_ratioTwo _ (k - 1)

/-- Hence the complete aggregate pencil is unconditionally nonnegative. -/
theorem bombieriFunctional_head_add_smul_aggregateSlice_nonnegative
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) (c : ℂ) :
    0 ≤ (bombieriFunctional (bombieriQuadraticTest
      (monotoneQuarterCell parent k +
        c • monotonePrimeAtomAggregateSlice parent k S))).re := by
  exact bombieriFunctional_quadratic_re_nonneg_of_ratioTwoCell _
    (monotonePrimeAtom_head_add_smul_aggregateSlice_ratioTwo
      parent k S c)

/-- Complete diagonal reserve of the coherently aggregated slice. -/
def monotonePrimeAtomAggregateReserve
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) : ℝ :=
  bombieriRealQuadraticValue
    (monotonePrimeAtomAggregateSlice parent k S)

/-- Complete cross between the head and the coherently aggregated slice. -/
def monotonePrimeAtomAggregateCross
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) : ℂ :=
  bombieriTwoBlockGlobalCrossSymbol
    (monotoneQuarterCell parent k)
    (monotonePrimeAtomAggregateSlice parent k S)

/-- The single aggregate translated-kernel remainder. -/
def monotonePrimeAtomAggregateRemainder
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) : ℝ :=
  (monotonePrimeAtomAggregateCross parent k S).re -
    ∑ j ∈ S, monotonePrimeAtomValue parent k j

/-- Linearity identifies the aggregate cross with the weighted sum of the
individual transported crosses. -/
theorem monotonePrimeAtomAggregateCross_re_eq_sum
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) :
    (monotonePrimeAtomAggregateCross parent k S).re =
      ∑ j ∈ S, bombieriLogPrimeAtomWeight j *
        (monotonePrimeAtomTransportedCross parent k j).re := by
  rw [monotonePrimeAtomAggregateCross,
    monotonePrimeAtomAggregateSlice_eq_sum]
  induction S using Finset.induction_on with
  | empty =>
      simp [bombieriTwoBlockGlobalCrossSymbol_zero_right]
  | @insert j S hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj,
        bombieriTwoBlockGlobalCrossSymbol_add_right,
        bombieriTwoBlockGlobalCrossSymbol_smul_right, Complex.add_re, ih]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, monotonePrimeAtomTransportedCross]

/-- The aggregate remainder is exactly the signed sum of the individual
remainders; no term was discarded in forming the common slice. -/
theorem monotonePrimeAtomAggregateRemainder_eq_sum
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) :
    monotonePrimeAtomAggregateRemainder parent k S =
      ∑ j ∈ S, monotonePrimeAtomTransportRemainder parent k j := by
  rw [monotonePrimeAtomAggregateRemainder,
    monotonePrimeAtomAggregateCross_re_eq_sum]
  simp_rw [monotonePrimeAtomTransportRemainder]
  rw [Finset.sum_sub_distrib]

/-! ## One determinant for the complete finite prime row -/

/-- The common ratio-two pencil gives one determinant for the whole selected
prime row. -/
theorem monotonePrimeAtom_aggregateCross_determinant
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) :
    Complex.normSq (monotonePrimeAtomAggregateCross parent k S) ≤
      bombieriRealQuadraticValue (monotoneQuarterCell parent k) *
        monotonePrimeAtomAggregateReserve parent k S := by
  have hhead : 0 ≤ bombieriRealQuadraticValue
      (monotoneQuarterCell parent k) := by
    unfold bombieriRealQuadraticValue
    exact bombieriFunctional_quadratic_re_nonneg_of_ratioTwoCell _
      (monotoneQuarterCell_ratioTwo parent k)
  have hslice : 0 ≤ monotonePrimeAtomAggregateReserve parent k S := by
    unfold monotonePrimeAtomAggregateReserve bombieriRealQuadraticValue
    exact bombieriFunctional_quadratic_re_nonneg_of_ratioTwoCell _
      (monotoneRatioTwoBlock_ratioTwo _ (k - 1))
  apply (twoSeedHermitian_nonneg_iff
    (bombieriRealQuadraticValue (monotoneQuarterCell parent k))
    (monotonePrimeAtomAggregateReserve parent k S)
    (monotonePrimeAtomAggregateCross parent k S) hhead hslice).1
  intro c
  have hnonneg :=
    bombieriFunctional_head_add_smul_aggregateSlice_nonnegative
      parent k S c
  rw [bombieriFunctional_twoBlock_re] at hnonneg
  simpa only [twoSeedHermitianValue, bombieriRealQuadraticValue,
    monotonePrimeAtomAggregateReserve,
    monotonePrimeAtomAggregateCross] using hnonneg

/-- The single determinant controls the sum of the selected atoms together
with their aggregate translated-kernel remainder. -/
theorem monotonePrimeAtom_sum_add_aggregateRemainder_sq_le
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) :
    ((∑ j ∈ S, monotonePrimeAtomValue parent k j) +
        monotonePrimeAtomAggregateRemainder parent k S) ^ 2 ≤
      bombieriRealQuadraticValue (monotoneQuarterCell parent k) *
        monotonePrimeAtomAggregateReserve parent k S := by
  have hdet := monotonePrimeAtom_aggregateCross_determinant parent k S
  have hre : (monotonePrimeAtomAggregateCross parent k S).re ^ 2 ≤
      Complex.normSq (monotonePrimeAtomAggregateCross parent k S) := by
    simp only [Complex.normSq_apply]
    nlinarith [sq_nonneg (monotonePrimeAtomAggregateCross parent k S).im]
  unfold monotonePrimeAtomAggregateRemainder
  nlinarith

/-- Coherent arithmetic-mean absorption: the head diagonal is paid once,
independently of the number of nonzero Mangoldt atoms. -/
theorem two_mul_monotonePrimeAtom_sum_le_aggregateReserve
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ) :
    2 * (∑ j ∈ S, monotonePrimeAtomValue parent k j) ≤
      bombieriRealQuadraticValue (monotoneQuarterCell parent k) +
        monotonePrimeAtomAggregateReserve parent k S -
          2 * monotonePrimeAtomAggregateRemainder parent k S := by
  let P : ℝ := ∑ j ∈ S, monotonePrimeAtomValue parent k j
  let R : ℝ := monotonePrimeAtomAggregateRemainder parent k S
  let H : ℝ := bombieriRealQuadraticValue (monotoneQuarterCell parent k)
  let T : ℝ := monotonePrimeAtomAggregateReserve parent k S
  have hsq : (P + R) ^ 2 ≤ H * T := by
    simpa only [P, R, H, T] using
      monotonePrimeAtom_sum_add_aggregateRemainder_sq_le parent k S
  have hH : 0 ≤ H := by
    dsimp only [H, bombieriRealQuadraticValue]
    exact bombieriFunctional_quadratic_re_nonneg_of_ratioTwoCell _
      (monotoneQuarterCell_ratioTwo parent k)
  have hT : 0 ≤ T := by
    dsimp only [T, monotonePrimeAtomAggregateReserve,
      bombieriRealQuadraticValue]
    exact bombieriFunctional_quadratic_re_nonneg_of_ratioTwoCell _
      (monotoneRatioTwoBlock_ratioTwo _ (k - 1))
  have hmean : 2 * (P + R) ≤ H + T := by
    nlinarith [sq_nonneg (H - T), sq_nonneg (P + R)]
  simpa only [P, R, H, T] using (show 2 * P ≤ H + T - 2 * R by
    linarith)

/-! ## A coherent one-step propagation target -/

/-- Sharp determinant-scale aggregate absorption.  The arithmetic mean bound
below is not needed: the actual inner suffix diagonal can balance the
aggregate slice through a two-by-two Schur condition. -/
theorem monotoneQuarterCutoff_nonnegative_of_primeAtom_aggregateSchur
    (parent : BombieriTest) (k : ℤ) (Sₚ : Finset ℕ)
    (hout : ∀ j ∉ Sₚ, monotonePrimeAtomValue parent k j = 0)
    (hmean :
      0 ≤ bombieriRealQuadraticValue (monotoneQuarterCell parent k) +
        bombieriRealQuadraticValue
            (monotoneQuarterCutoff parent (k + 1)) +
          2 * (monotoneQuarterHeadSuffixRealArchimedeanCross parent k +
            monotonePrimeAtomAggregateRemainder parent k Sₚ))
    (hschur :
      4 * bombieriRealQuadraticValue (monotoneQuarterCell parent k) *
          monotonePrimeAtomAggregateReserve parent k Sₚ ≤
        (bombieriRealQuadraticValue (monotoneQuarterCell parent k) +
          bombieriRealQuadraticValue
              (monotoneQuarterCutoff parent (k + 1)) +
            2 * (monotoneQuarterHeadSuffixRealArchimedeanCross parent k +
              monotonePrimeAtomAggregateRemainder parent k Sₚ)) ^ 2) :
    0 ≤ bombieriRealQuadraticValue (monotoneQuarterCutoff parent k) := by
  let H : ℝ := bombieriRealQuadraticValue (monotoneQuarterCell parent k)
  let I : ℝ := bombieriRealQuadraticValue
    (monotoneQuarterCutoff parent (k + 1))
  let T : ℝ := monotonePrimeAtomAggregateReserve parent k Sₚ
  let C : ℝ := (monotonePrimeAtomAggregateCross parent k Sₚ).re
  let A : ℝ := monotoneQuarterHeadSuffixRealArchimedeanCross parent k
  let R : ℝ := monotonePrimeAtomAggregateRemainder parent k Sₚ
  let B : ℝ := H + I + 2 * (A + R)
  have hH : 0 ≤ H := by
    dsimp only [H, bombieriRealQuadraticValue]
    exact bombieriFunctional_quadratic_re_nonneg_of_ratioTwoCell _
      (monotoneQuarterCell_ratioTwo parent k)
  have hT : 0 ≤ T := by
    dsimp only [T, monotonePrimeAtomAggregateReserve,
      bombieriRealQuadraticValue]
    exact bombieriFunctional_quadratic_re_nonneg_of_ratioTwoCell _
      (monotoneRatioTwoBlock_ratioTwo _ (k - 1))
  have hC : C ^ 2 ≤ H * T := by
    have hdet := monotonePrimeAtom_aggregateCross_determinant parent k Sₚ
    have hre : (monotonePrimeAtomAggregateCross parent k Sₚ).re ^ 2 ≤
        Complex.normSq (monotonePrimeAtomAggregateCross parent k Sₚ) := by
      simp only [Complex.normSq_apply]
      nlinarith [sq_nonneg (monotonePrimeAtomAggregateCross parent k Sₚ).im]
    exact hre.trans (by simpa only [H, T, C] using hdet)
  have hB : 0 ≤ B := by
    simpa only [B, H, I, A, R] using hmean
  have hscale : 4 * H * T ≤ B ^ 2 := by
    simpa only [B, H, I, T, A, R] using hschur
  have hsq : (2 * C) ^ 2 ≤ B ^ 2 := by
    calc
      (2 * C) ^ 2 = 4 * C ^ 2 := by ring
      _ ≤ 4 * (H * T) := mul_le_mul_of_nonneg_left hC (by norm_num)
      _ = 4 * H * T := by ring
      _ ≤ B ^ 2 := hscale
  have habs : |2 * C| ≤ B := by
    apply (sq_le_sq₀ (abs_nonneg _) hB).mp
    rw [sq_abs]
    exact hsq
  have hcross : 2 * C ≤ B := (le_abs_self _).trans habs
  have hprime :=
    monotoneQuarterHeadSuffixRealPrimeCross_eq_finset parent k Sₚ hout
  have hCeq : C =
      monotoneQuarterHeadSuffixRealPrimeCross parent k + R := by
    dsimp only [C, R, monotonePrimeAtomAggregateRemainder]
    rw [hprime]
    ring
  unfold bombieriRealQuadraticValue
  apply (monotoneQuarterCutoff_nonnegative_iff_logDefect_lowerBound
    parent k).2
  rw [monotoneQuarterRealLogStepDefect_eq_archimedean_sub_mangoldt]
  change -(H + I) ≤ 2 * A -
    2 * monotoneQuarterHeadSuffixRealPrimeCross parent k
  dsimp only [B] at hcross
  rw [hCeq] at hcross
  linarith

/-- If the one aggregate slice, its exact translated-kernel remainder, and
the archimedean cross fit inside the actual suffix diagonal, then the outer
cutoff is nonnegative.  Unlike atomwise absorption, this hypothesis contains
no factor proportional to the number of nonzero prime atoms. -/
theorem monotoneQuarterCutoff_nonnegative_of_primeAtom_aggregateReserve
    (parent : BombieriTest) (k : ℤ) (S : Finset ℕ)
    (hout : ∀ j ∉ S, monotonePrimeAtomValue parent k j = 0)
    (hbudget :
      monotonePrimeAtomAggregateReserve parent k S -
          2 * monotonePrimeAtomAggregateRemainder parent k S -
          2 * monotoneQuarterHeadSuffixRealArchimedeanCross parent k ≤
        bombieriRealQuadraticValue
          (monotoneQuarterCutoff parent (k + 1))) :
    0 ≤ bombieriRealQuadraticValue (monotoneQuarterCutoff parent k) := by
  have hatoms := two_mul_monotonePrimeAtom_sum_le_aggregateReserve
    parent k S
  have hprime :=
    monotoneQuarterHeadSuffixRealPrimeCross_eq_finset parent k S hout
  rw [← hprime] at hatoms
  unfold bombieriRealQuadraticValue
  apply (monotoneQuarterCutoff_nonnegative_iff_logDefect_lowerBound
    parent k).2
  rw [monotoneQuarterRealLogStepDefect_eq_archimedean_sub_mangoldt]
  change -((bombieriRealQuadraticValue (monotoneQuarterCell parent k)) +
      bombieriRealQuadraticValue
        (monotoneQuarterCutoff parent (k + 1))) ≤
    2 * monotoneQuarterHeadSuffixRealArchimedeanCross parent k -
      2 * monotoneQuarterHeadSuffixRealPrimeCross parent k
  linarith

/-- Concrete uniform aggregate-budget property.  Its analytic content is a
single ratio-two prime-transfer reserve at each boundary. -/
def BombieriRealMonotonePrimeAggregateAbsorption : Prop :=
  ∀ parent : BombieriTest,
    bombieriConjugateTest parent = parent →
      ∀ k : ℤ,
        0 ≤ bombieriRealQuadraticValue
            (monotoneQuarterCutoff parent (k + 1)) →
          ∃ S : Finset ℕ,
            (∀ j ∉ S, monotonePrimeAtomValue parent k j = 0) ∧
              monotonePrimeAtomAggregateReserve parent k S -
                  2 * monotonePrimeAtomAggregateRemainder parent k S -
                  2 * monotoneQuarterHeadSuffixRealArchimedeanCross parent k ≤
                bombieriRealQuadraticValue
                  (monotoneQuarterCutoff parent (k + 1))

/-- The coherent aggregate budget supplies the exact monotone propagation
rule needed by the RH criterion. -/
theorem bombieriRealMonotoneCutPropagation_of_primeAggregateAbsorption
    (haggregate : BombieriRealMonotonePrimeAggregateAbsorption) :
    BombieriRealMonotoneCutPropagation := by
  intro parent hparent k hinner
  obtain ⟨S, hout, hbudget⟩ :=
    haggregate parent hparent k hinner
  exact monotoneQuarterCutoff_nonnegative_of_primeAtom_aggregateReserve
    parent k S hout hbudget

/-- Sharper uniform aggregate-Schur property, retaining the actual suffix
diagonal instead of replacing it by an arithmetic-mean slice budget. -/
def BombieriRealMonotonePrimeAggregateSchurAbsorption : Prop :=
  ∀ parent : BombieriTest,
    bombieriConjugateTest parent = parent →
      ∀ k : ℤ,
        0 ≤ bombieriRealQuadraticValue
            (monotoneQuarterCutoff parent (k + 1)) →
          ∃ Sₚ : Finset ℕ,
            (∀ j ∉ Sₚ, monotonePrimeAtomValue parent k j = 0) ∧
            0 ≤ bombieriRealQuadraticValue (monotoneQuarterCell parent k) +
                bombieriRealQuadraticValue
                    (monotoneQuarterCutoff parent (k + 1)) +
                  2 * (monotoneQuarterHeadSuffixRealArchimedeanCross parent k +
                    monotonePrimeAtomAggregateRemainder parent k Sₚ) ∧
            4 * bombieriRealQuadraticValue (monotoneQuarterCell parent k) *
                monotonePrimeAtomAggregateReserve parent k Sₚ ≤
              (bombieriRealQuadraticValue (monotoneQuarterCell parent k) +
                bombieriRealQuadraticValue
                    (monotoneQuarterCutoff parent (k + 1)) +
                  2 * (monotoneQuarterHeadSuffixRealArchimedeanCross parent k +
                    monotonePrimeAtomAggregateRemainder parent k Sₚ)) ^ 2

/-- The determinant-scale aggregate condition also supplies the exact
monotone-cut propagation rule. -/
theorem bombieriRealMonotoneCutPropagation_of_primeAggregateSchurAbsorption
    (haggregate : BombieriRealMonotonePrimeAggregateSchurAbsorption) :
    BombieriRealMonotoneCutPropagation := by
  intro parent hparent k hinner
  obtain ⟨Sₚ, hout, hmean, hschur⟩ :=
    haggregate parent hparent k hinner
  exact monotoneQuarterCutoff_nonnegative_of_primeAtom_aggregateSchur
    parent k Sₚ hout hmean hschur

end

end ArithmeticHodge.Analysis.MultiplicativeWeilMonotonePrimeAtomAggregateStructural
