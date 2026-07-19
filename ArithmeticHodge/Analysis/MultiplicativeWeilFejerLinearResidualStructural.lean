import ArithmeticHodge.Analysis.MultiplicativeWeilFejerLocalizationStructural
import Mathlib.Data.List.Rotate
import Mathlib.Logic.Equiv.Fin.Rotate

set_option autoImplicit false

open Complex Finset Real

namespace ArithmeticHodge.Analysis.MultiplicativeWeilFejerLinearResidualStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilFejerLocalizationStructural

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
  rw [list_ofFn_finRotate
    (fun i ↦ a (finRotate (N + 1) i)), list_ofFn_finRotate]
  simp only [List.rotate_rotate, one_add_one_eq_two]

/-!
# Exact linear-lag expansion of the order-three Fejer residual

For a finite line of Bombieri cells, the order-three Fejer taper retains the
diagonal, coefficient `4/3` at lag one, and coefficient `2/3` at lag two.
Subtracting it from the complete Gram therefore leaves coefficients `2/3`,
`4/3`, and then `2` at every lag at least three.  This module proves that
identity directly for the complete local-minus-prime cross.
-/

/-- Crosses between one cell and a later tail, weighted by their positive
linear lag. -/
def bombieriHeadWeightedLagCross
    (w : ℕ → ℝ) (f : BombieriTest) : ℕ → List BombieriTest → ℝ
  | _k, [] => 0
  | k, g :: tail =>
      w k * bombieriGlobalCrossRealValue f g +
        bombieriHeadWeightedLagCross w f (k + 1) tail

/-- Every unordered cross in a linearly ordered list, weighted only by the
positive difference of its two positions. -/
def bombieriWeightedLinearLagCross
    (w : ℕ → ℝ) : List BombieriTest → ℝ
  | [] => 0
  | f :: tail =>
      bombieriHeadWeightedLagCross w f 1 tail +
        bombieriWeightedLinearLagCross w tail

/-- Order-three Fejer weights on the first two positive linear lags. -/
def bombieriFejerThreeLagWeight (k : ℕ) : ℝ :=
  if k = 1 then 4 / 3 else if k = 2 then 2 / 3 else 0

/-- Coefficients left after subtracting the order-three Fejer taper. -/
def bombieriFejerThreeResidualLagWeight (k : ℕ) : ℝ :=
  if k = 1 then 2 / 3 else if k = 2 then 4 / 3 else 2

private def lagOneWeight (k : ℕ) : ℝ :=
  if k = 1 then 1 else 0

private def lagTwoWeight (k : ℕ) : ℝ :=
  if k = 2 then 1 else 0

@[simp]
theorem bombieriFejerThreeResidualLagWeight_one :
    bombieriFejerThreeResidualLagWeight 1 = 2 / 3 := by
  norm_num [bombieriFejerThreeResidualLagWeight]

@[simp]
theorem bombieriFejerThreeResidualLagWeight_two :
    bombieriFejerThreeResidualLagWeight 2 = 4 / 3 := by
  norm_num [bombieriFejerThreeResidualLagWeight]

theorem bombieriFejerThreeResidualLagWeight_of_three_le
    {k : ℕ} (hk : 3 ≤ k) :
    bombieriFejerThreeResidualLagWeight k = 2 := by
  unfold bombieriFejerThreeResidualLagWeight
  have hk1 : k ≠ 1 := by omega
  have hk2 : k ≠ 2 := by omega
  simp only [if_neg hk1, if_neg hk2]

theorem bombieriFejerThreeLagWeight_add_residual
    (k : ℕ) :
    bombieriFejerThreeLagWeight k +
        bombieriFejerThreeResidualLagWeight k = 2 := by
  unfold bombieriFejerThreeLagWeight bombieriFejerThreeResidualLagWeight
  by_cases hk1 : k = 1
  · norm_num [hk1]
  · by_cases hk2 : k = 2
    · norm_num [hk2]
    · simp [hk1, hk2]

private theorem headWeightedLagCross_add
    (u v : ℕ → ℝ) (f : BombieriTest) (k : ℕ)
    (cells : List BombieriTest) :
    bombieriHeadWeightedLagCross (fun n ↦ u n + v n) f k cells =
      bombieriHeadWeightedLagCross u f k cells +
        bombieriHeadWeightedLagCross v f k cells := by
  induction cells generalizing k with
  | nil => simp [bombieriHeadWeightedLagCross]
  | cons g tail ih =>
      simp only [bombieriHeadWeightedLagCross]
      rw [ih]
      ring

private theorem weightedLinearLagCross_add
    (u v : ℕ → ℝ) (cells : List BombieriTest) :
    bombieriWeightedLinearLagCross (fun n ↦ u n + v n) cells =
      bombieriWeightedLinearLagCross u cells +
        bombieriWeightedLinearLagCross v cells := by
  induction cells with
  | nil => simp [bombieriWeightedLinearLagCross]
  | cons f tail ih =>
      simp only [bombieriWeightedLinearLagCross]
      rw [headWeightedLagCross_add, ih]
      ring

private theorem headWeightedLagCross_smul
    (c : ℝ) (u : ℕ → ℝ) (f : BombieriTest) (k : ℕ)
    (cells : List BombieriTest) :
    bombieriHeadWeightedLagCross (fun n ↦ c * u n) f k cells =
      c * bombieriHeadWeightedLagCross u f k cells := by
  induction cells generalizing k with
  | nil => simp [bombieriHeadWeightedLagCross]
  | cons g tail ih =>
      simp only [bombieriHeadWeightedLagCross]
      rw [ih]
      ring

private theorem weightedLinearLagCross_smul
    (c : ℝ) (u : ℕ → ℝ) (cells : List BombieriTest) :
    bombieriWeightedLinearLagCross (fun n ↦ c * u n) cells =
      c * bombieriWeightedLinearLagCross u cells := by
  induction cells with
  | nil => simp [bombieriWeightedLinearLagCross]
  | cons f tail ih =>
      simp only [bombieriWeightedLinearLagCross]
      rw [headWeightedLagCross_smul, ih]
      ring

private theorem headWeightedLagCross_congr
    (u v : ℕ → ℝ) (h : ∀ k, u k = v k)
    (f : BombieriTest) (k : ℕ) (cells : List BombieriTest) :
    bombieriHeadWeightedLagCross u f k cells =
      bombieriHeadWeightedLagCross v f k cells := by
  induction cells generalizing k with
  | nil => rfl
  | cons g tail ih =>
      simp only [bombieriHeadWeightedLagCross]
      rw [h k, ih (k + 1)]

private theorem weightedLinearLagCross_congr
    (u v : ℕ → ℝ) (h : ∀ k, u k = v k)
    (cells : List BombieriTest) :
    bombieriWeightedLinearLagCross u cells =
      bombieriWeightedLinearLagCross v cells := by
  induction cells with
  | nil => rfl
  | cons f tail ih =>
      simp only [bombieriWeightedLinearLagCross]
      rw [headWeightedLagCross_congr u v h f 1, ih]

private theorem fejerLagWeight_eq_indicator_combination (k : ℕ) :
    bombieriFejerThreeLagWeight k =
      (4 / 3 : ℝ) * lagOneWeight k + (2 / 3 : ℝ) * lagTwoWeight k := by
  unfold bombieriFejerThreeLagWeight lagOneWeight lagTwoWeight
  by_cases hk1 : k = 1
  · norm_num [hk1]
  · by_cases hk2 : k = 2
    · norm_num [hk2]
    · simp [hk1, hk2]

private theorem weightedLinearLagCross_fejer_eq_one_add_two
    (cells : List BombieriTest) :
    bombieriWeightedLinearLagCross bombieriFejerThreeLagWeight cells =
      (4 / 3 : ℝ) * bombieriWeightedLinearLagCross lagOneWeight cells +
        (2 / 3 : ℝ) * bombieriWeightedLinearLagCross lagTwoWeight cells := by
  calc
    bombieriWeightedLinearLagCross bombieriFejerThreeLagWeight cells =
        bombieriWeightedLinearLagCross
          (fun k ↦ (4 / 3 : ℝ) * lagOneWeight k +
            (2 / 3 : ℝ) * lagTwoWeight k) cells := by
      apply weightedLinearLagCross_congr
      exact fejerLagWeight_eq_indicator_combination
    _ = bombieriWeightedLinearLagCross
          (fun k ↦ (4 / 3 : ℝ) * lagOneWeight k) cells +
        bombieriWeightedLinearLagCross
          (fun k ↦ (2 / 3 : ℝ) * lagTwoWeight k) cells := by
      exact weightedLinearLagCross_add _ _ _
    _ = _ := by
      rw [weightedLinearLagCross_smul, weightedLinearLagCross_smul]

private theorem pairCrossSum_eq_weightedLinearLagCross_two
    (cells : List BombieriTest) :
    bombieriCellPairCrossSum cells =
      bombieriWeightedLinearLagCross (fun _k ↦ 2) cells := by
  have hhead : ∀ (f : BombieriTest) (k : ℕ)
      (tail : List BombieriTest),
      bombieriHeadWeightedLagCross (fun _n ↦ 2) f k tail =
        (tail.map (fun g ↦ 2 * bombieriGlobalCrossRealValue f g)).sum := by
    intro f k tail
    induction tail generalizing k with
    | nil => rfl
    | cons g rest ih =>
        simp only [bombieriHeadWeightedLagCross, List.map_cons, List.sum_cons]
        rw [ih]
  induction cells with
  | nil => rfl
  | cons f tail ih =>
      simp only [bombieriCellPairCrossSum, bombieriWeightedLinearLagCross]
      rw [hhead, ih]
      rfl

theorem weightedLinearLagCross_two_eq_fejer_add_residual
    (cells : List BombieriTest) :
    bombieriWeightedLinearLagCross (fun _k ↦ 2) cells =
      bombieriWeightedLinearLagCross bombieriFejerThreeLagWeight cells +
        bombieriWeightedLinearLagCross
          bombieriFejerThreeResidualLagWeight cells := by
  rw [← weightedLinearLagCross_add]
  apply weightedLinearLagCross_congr
  intro k
  exact (bombieriFejerThreeLagWeight_add_residual k).symm

/-- The noncyclic order-three taper. -/
def bombieriLinearFejerThree (cells : List BombieriTest) : ℝ :=
  (cells.map bombieriQuadraticRealValue).sum +
    bombieriWeightedLinearLagCross bombieriFejerThreeLagWeight cells

/-- Exact residual expansion: coefficient `2/3` at lag one, `4/3` at lag
two, and the full coefficient `2` at every lag at least three. -/
theorem bombieriQuadraticRealValue_list_sum_sub_linearFejerThree
    (cells : List BombieriTest) :
    bombieriQuadraticRealValue cells.sum - bombieriLinearFejerThree cells =
      bombieriWeightedLinearLagCross
        bombieriFejerThreeResidualLagWeight cells := by
  have hgram := bombieriFunctional_list_sum_re_eq_diagonal_add_pairs cells
  change bombieriQuadraticRealValue cells.sum =
      (cells.map bombieriQuadraticRealValue).sum +
        bombieriCellPairCrossSum cells at hgram
  rw [hgram, pairCrossSum_eq_weightedLinearLagCross_two,
    weightedLinearLagCross_two_eq_fejer_add_residual]
  unfold bombieriLinearFejerThree
  ring

/-- Finite-family form of the exact residual theorem. -/
theorem bombieriQuadraticRealValue_fin_sum_sub_linearFejerThree
    {N : ℕ} (a : Fin N → BombieriTest) :
    bombieriQuadraticRealValue (∑ i, a i) -
        bombieriLinearFejerThree (List.ofFn a) =
      bombieriWeightedLinearLagCross
        bombieriFejerThreeResidualLagWeight (List.ofFn a) := by
  rw [← List.sum_ofFn]
  exact bombieriQuadraticRealValue_list_sum_sub_linearFejerThree (List.ofFn a)

private theorem bombieriGlobalCrossRealValue_zero_left
    (f : BombieriTest) :
    bombieriGlobalCrossRealValue 0 f = 0 := by
  unfold bombieriGlobalCrossRealValue
  have hconj := bombieriTwoBlockGlobalCrossSymbol_conj_swap
    (0 : BombieriTest) f
  rw [← hconj, bombieriTwoBlockGlobalCrossSymbol_zero_right]
  simp

private theorem bombieriGlobalCrossRealValue_zero_right
    (f : BombieriTest) :
    bombieriGlobalCrossRealValue f 0 = 0 := by
  unfold bombieriGlobalCrossRealValue
  rw [bombieriTwoBlockGlobalCrossSymbol_zero_right]
  rfl

private theorem headLagOneWeight_of_two_le
    (f : BombieriTest) (k : ℕ) (hk : 2 ≤ k)
    (cells : List BombieriTest) :
    bombieriHeadWeightedLagCross lagOneWeight f k cells = 0 := by
  induction cells generalizing k with
  | nil => rfl
  | cons g tail ih =>
      simp only [bombieriHeadWeightedLagCross]
      have hw : lagOneWeight k = 0 := by
        simp [lagOneWeight]
        omega
      rw [hw, zero_mul, zero_add, ih (k + 1) (by omega)]

private theorem headLagTwoWeight_of_three_le
    (f : BombieriTest) (k : ℕ) (hk : 3 ≤ k)
    (cells : List BombieriTest) :
    bombieriHeadWeightedLagCross lagTwoWeight f k cells = 0 := by
  induction cells generalizing k with
  | nil => rfl
  | cons g tail ih =>
      simp only [bombieriHeadWeightedLagCross]
      have hw : lagTwoWeight k = 0 := by
        simp [lagTwoWeight]
        omega
      rw [hw, zero_mul, zero_add, ih (k + 1) (by omega)]

private theorem headLagOneWeight_one
    (f : BombieriTest) (cells : List BombieriTest) :
    bombieriHeadWeightedLagCross lagOneWeight f 1 cells =
      match cells with
      | [] => 0
      | g :: _tail => bombieriGlobalCrossRealValue f g := by
  cases cells with
  | nil => rfl
  | cons g tail =>
      simp only [bombieriHeadWeightedLagCross]
      rw [show lagOneWeight 1 = 1 by norm_num [lagOneWeight], one_mul,
        headLagOneWeight_of_two_le f 2 (by omega)]
      ring

private theorem headLagTwoWeight_one
    (f : BombieriTest) (cells : List BombieriTest) :
    bombieriHeadWeightedLagCross lagTwoWeight f 1 cells =
      match cells with
      | _g :: h :: _tail => bombieriGlobalCrossRealValue f h
      | _ => 0 := by
  cases cells with
  | nil => rfl
  | cons g tail =>
      cases tail with
      | nil =>
          simp [bombieriHeadWeightedLagCross, lagTwoWeight]
      | cons h rest =>
          simp only [bombieriHeadWeightedLagCross]
          rw [show lagTwoWeight 1 = 0 by norm_num [lagTwoWeight],
            show lagTwoWeight 2 = 1 by norm_num [lagTwoWeight],
            headLagTwoWeight_of_three_le f 3 (by omega)]
          ring

private theorem zipWith_adjacent_append_zero
    (f : BombieriTest) (tail : List BombieriTest) :
    (List.zipWith bombieriGlobalCrossRealValue
        (f :: tail) (tail ++ [0])).sum =
      bombieriWeightedLinearLagCross lagOneWeight (f :: tail) := by
  induction tail generalizing f with
  | nil =>
      simp [bombieriWeightedLinearLagCross, bombieriHeadWeightedLagCross,
        bombieriGlobalCrossRealValue_zero_right]
  | cons g rest ih =>
      simp only [List.cons_append, List.zipWith_cons_cons, List.sum_cons]
      rw [ih g]
      change bombieriGlobalCrossRealValue f g +
          bombieriWeightedLinearLagCross lagOneWeight (g :: rest) =
        bombieriHeadWeightedLagCross lagOneWeight f 1 (g :: rest) +
          bombieriWeightedLinearLagCross lagOneWeight (g :: rest)
      rw [headLagOneWeight_one]

private theorem zipWith_second_append_two_zero
    (f g : BombieriTest) (tail : List BombieriTest) :
    (List.zipWith bombieriGlobalCrossRealValue
        (f :: g :: tail) (tail ++ [0, 0])).sum =
      bombieriWeightedLinearLagCross lagTwoWeight (f :: g :: tail) := by
  induction tail generalizing f g with
  | nil =>
      simp [bombieriWeightedLinearLagCross, bombieriHeadWeightedLagCross,
        lagTwoWeight, bombieriGlobalCrossRealValue_zero_right]
  | cons h rest ih =>
      simp only [List.cons_append, List.zipWith_cons_cons, List.sum_cons]
      rw [ih g h]
      change bombieriGlobalCrossRealValue f h +
          bombieriWeightedLinearLagCross lagTwoWeight (g :: h :: rest) =
        bombieriHeadWeightedLagCross lagTwoWeight f 1 (g :: h :: rest) +
          bombieriWeightedLinearLagCross lagTwoWeight (g :: h :: rest)
      rw [headLagTwoWeight_one]

private theorem headWeightedLagCross_zero_left
    (w : ℕ → ℝ) (k : ℕ) (cells : List BombieriTest) :
    bombieriHeadWeightedLagCross w 0 k cells = 0 := by
  induction cells generalizing k with
  | nil => rfl
  | cons f tail ih =>
      simp only [bombieriHeadWeightedLagCross,
        bombieriGlobalCrossRealValue_zero_left, mul_zero, zero_add]
      exact ih (k + 1)

/-- Add two zero slots before a finite line, so cyclic wrap creates no
spurious first- or second-lag cross. -/
def bombieriFrontPadTwo
    {N : ℕ} (a : Fin N → BombieriTest) : Fin (N + 2) → BombieriTest :=
  Fin.cons 0 (Fin.cons 0 a)

@[simp]
theorem list_ofFn_bombieriFrontPadTwo
    {N : ℕ} (a : Fin N → BombieriTest) :
    List.ofFn (bombieriFrontPadTwo a) = 0 :: 0 :: List.ofFn a := by
  simp [bombieriFrontPadTwo]

@[simp]
theorem weightedLinearLagCross_bombieriFrontPadTwo
    (w : ℕ → ℝ) {N : ℕ} (a : Fin N → BombieriTest) :
    bombieriWeightedLinearLagCross w
        (List.ofFn (bombieriFrontPadTwo a)) =
      bombieriWeightedLinearLagCross w (List.ofFn a) := by
  rw [list_ofFn_bombieriFrontPadTwo]
  simp only [bombieriWeightedLinearLagCross,
    headWeightedLagCross_zero_left, zero_add]

private theorem fin_sum_cross_rotate_eq_zipWith
    {N : ℕ} (a : Fin (N + 1) → BombieriTest) :
    (∑ i, bombieriGlobalCrossRealValue (a i)
        (a (finRotate (N + 1) i))) =
      (List.zipWith bombieriGlobalCrossRealValue
        (List.ofFn a) ((List.ofFn a).rotate 1)).sum := by
  rw [← List.sum_ofFn, list_ofFn_binary, list_ofFn_finRotate]

private theorem fin_sum_cross_rotate_two_eq_zipWith
    {N : ℕ} (a : Fin (N + 1) → BombieriTest) :
    (∑ i, bombieriGlobalCrossRealValue (a i)
        (a (finRotate (N + 1) (finRotate (N + 1) i)))) =
      (List.zipWith bombieriGlobalCrossRealValue
        (List.ofFn a) ((List.ofFn a).rotate 2)).sum := by
  rw [← List.sum_ofFn, list_ofFn_binary, list_ofFn_finRotate_two]

private theorem cyclicFirstCross_frontPadTwo
    {N : ℕ} (a : Fin N → BombieriTest) :
    (∑ i, bombieriGlobalCrossRealValue (bombieriFrontPadTwo a i)
        (bombieriFrontPadTwo a (finRotate (N + 2) i))) =
      bombieriWeightedLinearLagCross lagOneWeight (List.ofFn a) := by
  rw [fin_sum_cross_rotate_eq_zipWith (bombieriFrontPadTwo a),
    list_ofFn_bombieriFrontPadTwo]
  have hrotate :
      (0 :: 0 :: List.ofFn a : List BombieriTest).rotate 1 =
        (0 :: List.ofFn a) ++ [0] := by
    simp
  rw [hrotate, zipWith_adjacent_append_zero]
  simp only [bombieriWeightedLinearLagCross,
    headWeightedLagCross_zero_left, zero_add]

private theorem cyclicSecondCross_frontPadTwo
    {N : ℕ} (a : Fin N → BombieriTest) :
    (∑ i, bombieriGlobalCrossRealValue (bombieriFrontPadTwo a i)
        (bombieriFrontPadTwo a
          (finRotate (N + 2) (finRotate (N + 2) i)))) =
      bombieriWeightedLinearLagCross lagTwoWeight (List.ofFn a) := by
  rw [fin_sum_cross_rotate_two_eq_zipWith (bombieriFrontPadTwo a),
    list_ofFn_bombieriFrontPadTwo]
  have hrotate :
      (0 :: 0 :: List.ofFn a : List BombieriTest).rotate 2 =
        List.ofFn a ++ [0, 0] := by
    simp
  rw [hrotate, zipWith_second_append_two_zero]
  simp only [bombieriWeightedLinearLagCross,
    headWeightedLagCross_zero_left, zero_add]

private theorem bombieriQuadraticRealValue_zero :
    bombieriQuadraticRealValue (0 : BombieriTest) = 0 := by
  unfold bombieriQuadraticRealValue
  rw [← bombieriTwoBlockGlobalCrossSymbol_self,
    bombieriTwoBlockGlobalCrossSymbol_zero_right]
  rfl

@[simp]
theorem sum_bombieriFrontPadTwo
    {N : ℕ} (a : Fin N → BombieriTest) :
    (∑ i, bombieriFrontPadTwo a i) = ∑ i, a i := by
  rw [← List.sum_ofFn, list_ofFn_bombieriFrontPadTwo]
  simp only [List.sum_cons, zero_add]
  exact List.sum_ofFn

private theorem cyclicDiagonal_frontPadTwo
    {N : ℕ} (a : Fin N → BombieriTest) :
    (∑ i, bombieriQuadraticRealValue (bombieriFrontPadTwo a i)) =
      (List.ofFn a |>.map bombieriQuadraticRealValue).sum := by
  rw [← List.sum_ofFn, List.ofFn_comp',
    list_ofFn_bombieriFrontPadTwo]
  simp only [List.map_cons, List.sum_cons, bombieriQuadraticRealValue_zero,
    zero_add]

/-- Two leading zeros turn the cyclic taper into the exact noncyclic
order-three taper of the original finite line. -/
theorem bombieriCyclicFejerThree_frontPadTwo_eq_linearFejerThree
    {N : ℕ} (a : Fin N → BombieriTest) :
    bombieriCyclicFejerThree (finRotate (N + 2))
        (bombieriFrontPadTwo a) =
      bombieriLinearFejerThree (List.ofFn a) := by
  unfold bombieriCyclicFejerThree bombieriLinearFejerThree
  rw [cyclicDiagonal_frontPadTwo, cyclicFirstCross_frontPadTwo,
    cyclicSecondCross_frontPadTwo,
    weightedLinearLagCross_fejer_eq_one_add_two]
  ring

/-- The production cyclic residual of the padded family has exact linear-lag
coefficients `2/3`, `4/3`, and then `2`. -/
theorem bombieriCyclicFejerThreeResidual_frontPadTwo_eq_linear_lags
    {N : ℕ} (a : Fin N → BombieriTest) :
    bombieriCyclicFejerThreeResidual (finRotate (N + 2))
        (bombieriFrontPadTwo a) =
      bombieriWeightedLinearLagCross
        bombieriFejerThreeResidualLagWeight (List.ofFn a) := by
  unfold bombieriCyclicFejerThreeResidual
  rw [sum_bombieriFrontPadTwo,
    bombieriCyclicFejerThree_frontPadTwo_eq_linearFejerThree]
  exact bombieriQuadraticRealValue_fin_sum_sub_linearFejerThree a

/-- The lag residual is unchanged by the two leading zero slots used for a
cyclic family. -/
theorem bombieriQuadraticRealValue_frontPadTwo_sum_sub_linearFejerThree
    {N : ℕ} (a : Fin N → BombieriTest) :
    bombieriQuadraticRealValue (∑ i, bombieriFrontPadTwo a i) -
        bombieriLinearFejerThree
          (List.ofFn (bombieriFrontPadTwo a)) =
      bombieriWeightedLinearLagCross
        bombieriFejerThreeResidualLagWeight (List.ofFn a) := by
  rw [← List.sum_ofFn]
  simpa only [weightedLinearLagCross_bombieriFrontPadTwo] using
    bombieriQuadraticRealValue_list_sum_sub_linearFejerThree
      (List.ofFn (bombieriFrontPadTwo a))

end

end ArithmeticHodge.Analysis.MultiplicativeWeilFejerLinearResidualStructural
