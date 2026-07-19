import ArithmeticHodge.Analysis.MultiplicativeWeilFejerResidualCrossTestStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilQuadraticEndpoint

set_option autoImplicit false

open Complex Finset Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.MultiplicativeWeilFejerReserveTestStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilFejerLocalizationStructural
open MultiplicativeWeilFejerLinearResidualStructural
open MultiplicativeWeilFejerResidualCrossTestStructural

/-!
# Test-level order-three Fejer reserve

The padded cyclic reserve is the average of its three-cell quadratic tests.
At test level it complements the weighted lag residual exactly.  Ratio-two
windows make the reserve prime-free, so the residual carries the complete
prime sum of the original quadratic test.
-/

private theorem quadraticTest_zero :
    bombieriQuadraticTest (0 : BombieriTest) = 0 := by
  ext x
  rw [bombieriQuadraticTest_apply]
  unfold autocorrelation
  simp

private theorem quadraticCrossTest_comm (f g : BombieriTest) :
    bombieriQuadraticCrossTest f g = bombieriQuadraticCrossTest g f := by
  unfold bombieriQuadraticCrossTest
  rw [add_comm]
  abel

private theorem quadraticCrossTest_zero_right (f : BombieriTest) :
    bombieriQuadraticCrossTest f 0 = 0 := by
  unfold bombieriQuadraticCrossTest
  rw [add_zero, quadraticTest_zero]
  abel

private theorem quadraticCrossTest_zero_left (f : BombieriTest) :
    bombieriQuadraticCrossTest 0 f = 0 := by
  rw [quadraticCrossTest_comm, quadraticCrossTest_zero_right]

private theorem quadraticCrossTest_add_left (f g h : BombieriTest) :
    bombieriQuadraticCrossTest (f + g) h =
      bombieriQuadraticCrossTest f h + bombieriQuadraticCrossTest g h := by
  rw [quadraticCrossTest_comm, bombieriQuadraticCrossTest_add_right]
  congr 1 <;> rw [quadraticCrossTest_comm]

private theorem quadraticTest_add_add (f g h : BombieriTest) :
    bombieriQuadraticTest (f + g + h) =
      bombieriQuadraticTest f + bombieriQuadraticTest g +
        bombieriQuadraticTest h +
        bombieriQuadraticCrossTest f g +
        bombieriQuadraticCrossTest f h +
        bombieriQuadraticCrossTest g h := by
  rw [bombieriQuadraticTest_add_eq_diagonal_add_cross,
    bombieriQuadraticTest_add_eq_diagonal_add_cross,
    quadraticCrossTest_add_left]
  abel

private theorem headWeightedLagCrossTest_add
    (u v : ℕ → ℝ) (f : BombieriTest) (k : ℕ)
    (cells : List BombieriTest) :
    bombieriHeadWeightedLagCrossTest (fun n ↦ u n + v n) f k cells =
      bombieriHeadWeightedLagCrossTest u f k cells +
        bombieriHeadWeightedLagCrossTest v f k cells := by
  induction cells generalizing k with
  | nil => simp [bombieriHeadWeightedLagCrossTest]
  | cons g tail ih =>
      simp only [bombieriHeadWeightedLagCrossTest]
      rw [ih]
      have hc : ((((u k + v k) / 2 : ℝ) : ℂ) : ℂ) =
          (u k / 2 : ℝ) + (v k / 2 : ℝ) := by
        push_cast
        ring
      rw [hc, add_smul]
      abel

private theorem weightedLinearLagCrossTest_add
    (u v : ℕ → ℝ) (cells : List BombieriTest) :
    bombieriWeightedLinearLagCrossTest (fun n ↦ u n + v n) cells =
      bombieriWeightedLinearLagCrossTest u cells +
        bombieriWeightedLinearLagCrossTest v cells := by
  induction cells with
  | nil => simp [bombieriWeightedLinearLagCrossTest]
  | cons f tail ih =>
      simp only [bombieriWeightedLinearLagCrossTest]
      rw [headWeightedLagCrossTest_add, ih]
      abel

private theorem headWeightedLagCrossTest_congr
    (u v : ℕ → ℝ) (h : ∀ k, u k = v k)
    (f : BombieriTest) (k : ℕ) (cells : List BombieriTest) :
    bombieriHeadWeightedLagCrossTest u f k cells =
      bombieriHeadWeightedLagCrossTest v f k cells := by
  induction cells generalizing k with
  | nil => rfl
  | cons g tail ih =>
      simp only [bombieriHeadWeightedLagCrossTest]
      rw [h k, ih (k + 1)]

private theorem weightedLinearLagCrossTest_congr
    (u v : ℕ → ℝ) (h : ∀ k, u k = v k)
    (cells : List BombieriTest) :
    bombieriWeightedLinearLagCrossTest u cells =
      bombieriWeightedLinearLagCrossTest v cells := by
  induction cells with
  | nil => rfl
  | cons f tail ih =>
      simp only [bombieriWeightedLinearLagCrossTest]
      rw [headWeightedLagCrossTest_congr u v h f 1, ih]

private theorem weightedLinearLagCrossTest_two_eq_fejer_add_residual
    (cells : List BombieriTest) :
    bombieriWeightedLinearLagCrossTest (fun _k ↦ 2) cells =
      bombieriWeightedLinearLagCrossTest bombieriFejerThreeLagWeight cells +
        bombieriFejerThreeResidualCrossTest cells := by
  unfold bombieriFejerThreeResidualCrossTest
  rw [← weightedLinearLagCrossTest_add]
  apply weightedLinearLagCrossTest_congr
  intro k
  exact (bombieriFejerThreeLagWeight_add_residual k).symm

private theorem headWeightedLagCrossTest_two
    (f : BombieriTest) (k : ℕ) (cells : List BombieriTest) :
    bombieriHeadWeightedLagCrossTest (fun _n ↦ 2) f k cells =
      bombieriQuadraticCrossTest f cells.sum := by
  induction cells generalizing k with
  | nil =>
      simp [bombieriHeadWeightedLagCrossTest,
        quadraticCrossTest_zero_right]
  | cons g tail ih =>
      simp only [bombieriHeadWeightedLagCrossTest, List.sum_cons]
      norm_num
      rw [ih, bombieriQuadraticCrossTest_add_right]

private theorem quadraticTest_list_sum_eq_diagonal_add_crosses
    (cells : List BombieriTest) :
    bombieriQuadraticTest cells.sum =
      (cells.map bombieriQuadraticTest).sum +
        bombieriWeightedLinearLagCrossTest (fun _k ↦ 2) cells := by
  induction cells with
  | nil =>
      simp [quadraticTest_zero, bombieriWeightedLinearLagCrossTest]
  | cons f tail ih =>
      simp only [List.sum_cons, List.map_cons,
        bombieriWeightedLinearLagCrossTest]
      rw [bombieriQuadraticTest_add_eq_diagonal_add_cross, ih,
        headWeightedLagCrossTest_two]
      abel

/-- Test-level noncyclic order-three Fejer reserve. -/
def bombieriLinearFejerThreeTest (cells : List BombieriTest) : BombieriTest :=
  (cells.map bombieriQuadraticTest).sum +
    bombieriWeightedLinearLagCrossTest bombieriFejerThreeLagWeight cells

theorem quadraticTest_list_sum_eq_linearFejer_add_residual
    (cells : List BombieriTest) :
    bombieriQuadraticTest cells.sum =
      bombieriLinearFejerThreeTest cells +
      bombieriFejerThreeResidualCrossTest cells := by
  rw [quadraticTest_list_sum_eq_diagonal_add_crosses,
    weightedLinearLagCrossTest_two_eq_fejer_add_residual]
  unfold bombieriLinearFejerThreeTest
  abel

/-- Explicit average of the quadratic tests of all cyclic three-cell windows. -/
def bombieriCyclicFejerThreeReserveTest
    {ι : Type*} [Fintype ι]
    (σ : Equiv.Perm ι) (a : ι → BombieriTest) : BombieriTest :=
  ((1 / 3 : ℝ) : ℂ) •
    ∑ i, bombieriQuadraticTest
      (a i + a (σ i) + a (σ (σ i)))

private theorem cyclicReserveTest_eq_expanded
    {ι : Type*} [Fintype ι]
    (σ : Equiv.Perm ι) (a : ι → BombieriTest) :
    bombieriCyclicFejerThreeReserveTest σ a =
      (∑ i, bombieriQuadraticTest (a i)) +
        ((2 / 3 : ℝ) : ℂ) •
          ∑ i, bombieriQuadraticCrossTest (a i) (a (σ i)) +
        ((1 / 3 : ℝ) : ℂ) •
          ∑ i, bombieriQuadraticCrossTest (a i) (a (σ (σ i))) := by
  unfold bombieriCyclicFejerThreeReserveTest
  simp_rw [quadraticTest_add_add, Finset.sum_add_distrib]
  have hq1 :
      (∑ i, bombieriQuadraticTest (a (σ i))) =
        ∑ i, bombieriQuadraticTest (a i) := by
    exact Equiv.sum_comp σ (fun i ↦ bombieriQuadraticTest (a i))
  have hq2 :
      (∑ i, bombieriQuadraticTest (a (σ (σ i)))) =
        ∑ i, bombieriQuadraticTest (a i) := by
    exact Equiv.sum_comp (σ.trans σ) (fun i ↦ bombieriQuadraticTest (a i))
  have hc1 :
      (∑ i, bombieriQuadraticCrossTest (a (σ i)) (a (σ (σ i)))) =
        ∑ i, bombieriQuadraticCrossTest (a i) (a (σ i)) := by
    exact Equiv.sum_comp σ
      (fun i ↦ bombieriQuadraticCrossTest (a i) (a (σ i)))
  rw [hq1, hq2, hc1]
  simp only [smul_add]
  module

private def lagOneCrossWeight (k : ℕ) : ℝ :=
  if k = 1 then 2 else 0

private def lagTwoCrossWeight (k : ℕ) : ℝ :=
  if k = 2 then 2 else 0

private theorem headWeightedLagCrossTest_smul
    (c : ℝ) (u : ℕ → ℝ) (f : BombieriTest) (k : ℕ)
    (cells : List BombieriTest) :
    bombieriHeadWeightedLagCrossTest (fun n ↦ c * u n) f k cells =
      (c : ℂ) • bombieriHeadWeightedLagCrossTest u f k cells := by
  induction cells generalizing k with
  | nil => simp [bombieriHeadWeightedLagCrossTest]
  | cons g tail ih =>
      simp only [bombieriHeadWeightedLagCrossTest]
      rw [ih]
      have hc : ((((c * u k) / 2 : ℝ) : ℂ) : ℂ) =
          (c : ℂ) * ((u k / 2 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hc, mul_smul, smul_add]

private theorem weightedLinearLagCrossTest_smul
    (c : ℝ) (u : ℕ → ℝ) (cells : List BombieriTest) :
    bombieriWeightedLinearLagCrossTest (fun n ↦ c * u n) cells =
      (c : ℂ) • bombieriWeightedLinearLagCrossTest u cells := by
  induction cells with
  | nil => simp [bombieriWeightedLinearLagCrossTest]
  | cons f tail ih =>
      simp only [bombieriWeightedLinearLagCrossTest]
      rw [headWeightedLagCrossTest_smul, ih, smul_add]

private theorem fejerLagWeight_eq_cross_indicator_combination (k : ℕ) :
    bombieriFejerThreeLagWeight k =
      (2 / 3 : ℝ) * lagOneCrossWeight k +
        (1 / 3 : ℝ) * lagTwoCrossWeight k := by
  unfold bombieriFejerThreeLagWeight lagOneCrossWeight lagTwoCrossWeight
  by_cases hk1 : k = 1
  · norm_num [hk1]
  · by_cases hk2 : k = 2
    · norm_num [hk2]
    · simp [hk1, hk2]

private theorem weightedLinearLagCrossTest_fejer_eq_indicators
    (cells : List BombieriTest) :
    bombieriWeightedLinearLagCrossTest bombieriFejerThreeLagWeight cells =
      (((2 / 3 : ℝ) : ℂ) •
        bombieriWeightedLinearLagCrossTest lagOneCrossWeight cells) +
      (((1 / 3 : ℝ) : ℂ) •
        bombieriWeightedLinearLagCrossTest lagTwoCrossWeight cells) := by
  calc
    bombieriWeightedLinearLagCrossTest bombieriFejerThreeLagWeight cells =
        bombieriWeightedLinearLagCrossTest
          (fun k ↦ (2 / 3 : ℝ) * lagOneCrossWeight k +
            (1 / 3 : ℝ) * lagTwoCrossWeight k) cells := by
      apply weightedLinearLagCrossTest_congr
      exact fejerLagWeight_eq_cross_indicator_combination
    _ = bombieriWeightedLinearLagCrossTest
          (fun k ↦ (2 / 3 : ℝ) * lagOneCrossWeight k) cells +
        bombieriWeightedLinearLagCrossTest
          (fun k ↦ (1 / 3 : ℝ) * lagTwoCrossWeight k) cells := by
      exact weightedLinearLagCrossTest_add _ _ _
    _ = _ := by
      rw [weightedLinearLagCrossTest_smul,
        weightedLinearLagCrossTest_smul]

private theorem list_ofFn_binary
    {A B C : Type*} {N : ℕ} (op : A → B → C)
    (a : Fin N → A) (b : Fin N → B) :
    List.ofFn (fun i ↦ op (a i) (b i)) =
      List.zipWith op (List.ofFn a) (List.ofFn b) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ]
      simp only [List.zipWith_cons_cons]
      rw [ih (fun i ↦ a i.succ) (fun i ↦ b i.succ)]

private theorem list_ofFn_finRotate
    {A : Type*} {N : ℕ} (a : Fin (N + 1) → A) :
    List.ofFn (fun i ↦ a (finRotate (N + 1) i)) =
      (List.ofFn a).rotate 1 := by
  apply List.ext_get
  · simp
  · intro k hkleft hkright
    rw [List.get_ofFn, List.get_rotate, List.get_ofFn]
    congr 1
    apply Fin.ext
    rw [finRotate_succ_apply, Fin.val_add]
    simp

private theorem list_ofFn_finRotate_two
    {A : Type*} {N : ℕ} (a : Fin (N + 1) → A) :
    List.ofFn (fun i ↦ a (finRotate (N + 1) (finRotate (N + 1) i))) =
      (List.ofFn a).rotate 2 := by
  rw [list_ofFn_finRotate (fun i ↦ a (finRotate (N + 1) i)),
    list_ofFn_finRotate]
  simp only [List.rotate_rotate, one_add_one_eq_two]

private theorem headLagOneCrossWeight_of_two_le
    (f : BombieriTest) (k : ℕ) (hk : 2 ≤ k)
    (cells : List BombieriTest) :
    bombieriHeadWeightedLagCrossTest lagOneCrossWeight f k cells = 0 := by
  induction cells generalizing k with
  | nil => rfl
  | cons g tail ih =>
      simp only [bombieriHeadWeightedLagCrossTest]
      have hw : lagOneCrossWeight k = 0 := by
        simp [lagOneCrossWeight]
        omega
      rw [hw]
      norm_num
      exact ih (k + 1) (by omega)

private theorem headLagTwoCrossWeight_of_three_le
    (f : BombieriTest) (k : ℕ) (hk : 3 ≤ k)
    (cells : List BombieriTest) :
    bombieriHeadWeightedLagCrossTest lagTwoCrossWeight f k cells = 0 := by
  induction cells generalizing k with
  | nil => rfl
  | cons g tail ih =>
      simp only [bombieriHeadWeightedLagCrossTest]
      have hw : lagTwoCrossWeight k = 0 := by
        simp [lagTwoCrossWeight]
        omega
      rw [hw]
      norm_num
      exact ih (k + 1) (by omega)

private theorem headLagOneCrossWeight_one
    (f : BombieriTest) (cells : List BombieriTest) :
    bombieriHeadWeightedLagCrossTest lagOneCrossWeight f 1 cells =
      match cells with
      | [] => 0
      | g :: _tail => bombieriQuadraticCrossTest f g := by
  cases cells with
  | nil => rfl
  | cons g tail =>
      simp only [bombieriHeadWeightedLagCrossTest]
      rw [show lagOneCrossWeight 1 = 2 by norm_num [lagOneCrossWeight],
        headLagOneCrossWeight_of_two_le f 2 (by omega)]
      norm_num

private theorem headLagTwoCrossWeight_one
    (f : BombieriTest) (cells : List BombieriTest) :
    bombieriHeadWeightedLagCrossTest lagTwoCrossWeight f 1 cells =
      match cells with
      | _g :: h :: _tail => bombieriQuadraticCrossTest f h
      | _ => 0 := by
  cases cells with
  | nil => rfl
  | cons g tail =>
      cases tail with
      | nil =>
          simp [bombieriHeadWeightedLagCrossTest, lagTwoCrossWeight]
      | cons h rest =>
          simp only [bombieriHeadWeightedLagCrossTest]
          rw [show lagTwoCrossWeight 1 = 0 by norm_num [lagTwoCrossWeight],
            show lagTwoCrossWeight 2 = 2 by norm_num [lagTwoCrossWeight],
            headLagTwoCrossWeight_of_three_le f 3 (by omega)]
          norm_num

private theorem headWeightedLagCrossTest_zero_left
    (w : ℕ → ℝ) (k : ℕ) (cells : List BombieriTest) :
    bombieriHeadWeightedLagCrossTest w 0 k cells = 0 := by
  induction cells generalizing k with
  | nil => rfl
  | cons f tail ih =>
      simp only [bombieriHeadWeightedLagCrossTest,
        quadraticCrossTest_zero_left, smul_zero, zero_add]
      exact ih (k + 1)

private theorem zipWith_adjacent_append_zero
    (f : BombieriTest) (tail : List BombieriTest) :
    (List.zipWith bombieriQuadraticCrossTest
        (f :: tail) (tail ++ [0])).sum =
      bombieriWeightedLinearLagCrossTest lagOneCrossWeight (f :: tail) := by
  induction tail generalizing f with
  | nil =>
      simp [bombieriWeightedLinearLagCrossTest,
        bombieriHeadWeightedLagCrossTest, quadraticCrossTest_zero_right]
  | cons g rest ih =>
      simp only [List.cons_append, List.zipWith_cons_cons, List.sum_cons]
      rw [ih g]
      change bombieriQuadraticCrossTest f g +
          bombieriWeightedLinearLagCrossTest lagOneCrossWeight (g :: rest) =
        bombieriHeadWeightedLagCrossTest lagOneCrossWeight f 1 (g :: rest) +
          bombieriWeightedLinearLagCrossTest lagOneCrossWeight (g :: rest)
      rw [headLagOneCrossWeight_one]

private theorem zipWith_second_append_two_zero
    (f g : BombieriTest) (tail : List BombieriTest) :
    (List.zipWith bombieriQuadraticCrossTest
        (f :: g :: tail) (tail ++ [0, 0])).sum =
      bombieriWeightedLinearLagCrossTest lagTwoCrossWeight (f :: g :: tail) := by
  induction tail generalizing f g with
  | nil =>
      simp [bombieriWeightedLinearLagCrossTest,
        bombieriHeadWeightedLagCrossTest, lagTwoCrossWeight,
        quadraticCrossTest_zero_right]
  | cons h rest ih =>
      simp only [List.cons_append, List.zipWith_cons_cons, List.sum_cons]
      rw [ih g h]
      change bombieriQuadraticCrossTest f h +
          bombieriWeightedLinearLagCrossTest lagTwoCrossWeight (g :: h :: rest) =
        bombieriHeadWeightedLagCrossTest lagTwoCrossWeight f 1 (g :: h :: rest) +
          bombieriWeightedLinearLagCrossTest lagTwoCrossWeight (g :: h :: rest)
      rw [headLagTwoCrossWeight_one]

private theorem fin_sum_cross_rotate_eq_zipWith
    {N : ℕ} (a : Fin (N + 1) → BombieriTest) :
    (∑ i, bombieriQuadraticCrossTest (a i) (a (finRotate (N + 1) i))) =
      (List.zipWith bombieriQuadraticCrossTest
        (List.ofFn a) ((List.ofFn a).rotate 1)).sum := by
  rw [← List.sum_ofFn, list_ofFn_binary, list_ofFn_finRotate]

private theorem fin_sum_cross_rotate_two_eq_zipWith
    {N : ℕ} (a : Fin (N + 1) → BombieriTest) :
    (∑ i, bombieriQuadraticCrossTest (a i)
        (a (finRotate (N + 1) (finRotate (N + 1) i)))) =
      (List.zipWith bombieriQuadraticCrossTest
        (List.ofFn a) ((List.ofFn a).rotate 2)).sum := by
  rw [← List.sum_ofFn, list_ofFn_binary, list_ofFn_finRotate_two]

private theorem cyclicFirstCrossTest_frontPadTwo
    {N : ℕ} (a : Fin N → BombieriTest) :
    (∑ i, bombieriQuadraticCrossTest (bombieriFrontPadTwo a i)
        (bombieriFrontPadTwo a (finRotate (N + 2) i))) =
      bombieriWeightedLinearLagCrossTest lagOneCrossWeight (List.ofFn a) := by
  rw [fin_sum_cross_rotate_eq_zipWith (bombieriFrontPadTwo a),
    list_ofFn_bombieriFrontPadTwo]
  have hrotate :
      (0 :: 0 :: List.ofFn a : List BombieriTest).rotate 1 =
        (0 :: List.ofFn a) ++ [0] := by
    simp
  rw [hrotate, zipWith_adjacent_append_zero]
  simp only [bombieriWeightedLinearLagCrossTest,
    headWeightedLagCrossTest_zero_left, zero_add]

private theorem cyclicSecondCrossTest_frontPadTwo
    {N : ℕ} (a : Fin N → BombieriTest) :
    (∑ i, bombieriQuadraticCrossTest (bombieriFrontPadTwo a i)
        (bombieriFrontPadTwo a
          (finRotate (N + 2) (finRotate (N + 2) i)))) =
      bombieriWeightedLinearLagCrossTest lagTwoCrossWeight (List.ofFn a) := by
  rw [fin_sum_cross_rotate_two_eq_zipWith (bombieriFrontPadTwo a),
    list_ofFn_bombieriFrontPadTwo]
  have hrotate :
      (0 :: 0 :: List.ofFn a : List BombieriTest).rotate 2 =
        List.ofFn a ++ [0, 0] := by
    simp
  rw [hrotate, zipWith_second_append_two_zero]
  simp only [bombieriWeightedLinearLagCrossTest,
    headWeightedLagCrossTest_zero_left, zero_add]

private theorem cyclicDiagonalTest_frontPadTwo
    {N : ℕ} (a : Fin N → BombieriTest) :
    (∑ i, bombieriQuadraticTest (bombieriFrontPadTwo a i)) =
      (List.ofFn a |>.map bombieriQuadraticTest).sum := by
  rw [← List.sum_ofFn, List.ofFn_comp',
    list_ofFn_bombieriFrontPadTwo]
  simp only [List.map_cons, List.sum_cons, quadraticTest_zero, zero_add]

theorem cyclicReserveTest_frontPadTwo_eq_linearFejerTest
    {N : ℕ} (a : Fin N → BombieriTest) :
    bombieriCyclicFejerThreeReserveTest (finRotate (N + 2))
        (bombieriFrontPadTwo a) =
      bombieriLinearFejerThreeTest (List.ofFn a) := by
  rw [cyclicReserveTest_eq_expanded, cyclicDiagonalTest_frontPadTwo,
    cyclicFirstCrossTest_frontPadTwo, cyclicSecondCrossTest_frontPadTwo]
  unfold bombieriLinearFejerThreeTest
  rw [weightedLinearLagCrossTest_fejer_eq_indicators]
  abel

/-- The full quadratic test is the explicit cyclic reserve plus exactly the
existing weighted residual cross test. -/
theorem quadraticTest_frontPadTwo_sum_eq_cyclicReserve_add_residual
    {N : ℕ} (a : Fin N → BombieriTest) :
    bombieriQuadraticTest (∑ i, bombieriFrontPadTwo a i) =
      bombieriCyclicFejerThreeReserveTest (finRotate (N + 2))
          (bombieriFrontPadTwo a) +
        bombieriFejerThreeResidualCrossTest (List.ofFn a) := by
  rw [sum_bombieriFrontPadTwo, ← List.sum_ofFn,
    quadraticTest_list_sum_eq_linearFejer_add_residual,
    cyclicReserveTest_frontPadTwo_eq_linearFejerTest]

private theorem primeSum_quadraticTest_eq_zero_of_ratioTwoCell
    (g : BombieriTest) (hg : BombieriRatioTwoCell g) :
    primeSum (bombieriQuadraticTest g) = 0 := by
  obtain ⟨a, b, ha, hab, hsupport, hratio⟩ := hg
  exact primeSum_bombieriQuadraticTest_eq_zero_of_support_ratio_le_two
    g ha hab hsupport hratio

/-- If every cyclic window is a ratio-two cell, the explicit reserve has no
prime term: it is an average solely of prime-free quadratic tests. -/
theorem primeSum_cyclicReserveTest_eq_zero_of_ratioTwo_windows
    {ι : Type*} [Fintype ι]
    (σ : Equiv.Perm ι) (a : ι → BombieriTest)
    (hwindow : ∀ i, BombieriRatioTwoCell
      (a i + a (σ i) + a (σ (σ i)))) :
    primeSum (bombieriCyclicFejerThreeReserveTest σ a) = 0 := by
  unfold bombieriCyclicFejerThreeReserveTest
  change primeSumLinearMap
      (((1 / 3 : ℝ) : ℂ) •
        ∑ i, bombieriQuadraticTest
          (a i + a (σ i) + a (σ (σ i)))) = 0
  rw [map_smul, map_sum]
  simp only [primeSumLinearMap_apply,
    primeSum_quadraticTest_eq_zero_of_ratioTwoCell _ (hwindow _),
    Finset.sum_const_zero, smul_zero]

/-- Consequently the existing weighted residual cross test carries the exact
prime sum of the full padded quadratic test. -/
theorem primeSum_fejerResidualCrossTest_eq_full_of_ratioTwo_windows
    {N : ℕ} (a : Fin N → BombieriTest)
    (hwindow : ∀ i, BombieriRatioTwoCell
      (bombieriFrontPadTwo a i +
        bombieriFrontPadTwo a (finRotate (N + 2) i) +
        bombieriFrontPadTwo a
          (finRotate (N + 2) (finRotate (N + 2) i)))) :
    primeSum (bombieriFejerThreeResidualCrossTest (List.ofFn a)) =
      primeSum (bombieriQuadraticTest (∑ i, bombieriFrontPadTwo a i)) := by
  have htest := quadraticTest_frontPadTwo_sum_eq_cyclicReserve_add_residual a
  have hp := congrArg primeSum htest
  rw [primeSum_add,
    primeSum_cyclicReserveTest_eq_zero_of_ratioTwo_windows
      (finRotate (N + 2)) (bombieriFrontPadTwo a) hwindow,
    zero_add] at hp
  exact hp.symm

end

end ArithmeticHodge.Analysis.MultiplicativeWeilFejerReserveTestStructural

