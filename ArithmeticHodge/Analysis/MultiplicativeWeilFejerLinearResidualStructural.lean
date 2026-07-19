import ArithmeticHodge.Analysis.MultiplicativeWeilFejerLocalizationStructural

set_option autoImplicit false

open Complex Finset Real

namespace ArithmeticHodge.Analysis.MultiplicativeWeilFejerLinearResidualStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilFejerLocalizationStructural

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
