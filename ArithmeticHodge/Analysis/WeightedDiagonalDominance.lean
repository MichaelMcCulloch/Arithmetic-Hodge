import Mathlib.Analysis.Matrix.PosDef

set_option autoImplicit false

open scoped BigOperators

namespace ArithmeticHodge.Analysis.WeightedDiagonalDominance

private theorem weighted_young
    {u v a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    2 * |u * v| ≤ (b / a) * u ^ 2 + (a / b) * v ^ 2 := by
  have hratio : 0 < b / a := div_pos hb ha
  have h := two_mul_le_add_mul_sq (a := |u|) (b := |v|) hratio
  simpa [abs_mul, sq_abs, inv_div, mul_assoc] using h

private theorem sum_erase_swap
    {n : Type*} [Fintype n] [DecidableEq n]
    (f : n → n → ℝ) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, f i j) =
      ∑ i, ∑ j ∈ Finset.univ.erase i, f j i := by
  classical
  calc
    (∑ i, ∑ j ∈ Finset.univ.erase i, f i j) =
        ∑ i, ∑ j, if j ≠ i then f i j else 0 := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [← Finset.filter_ne' Finset.univ i, Finset.sum_filter]
    _ = ∑ j, ∑ i, if j ≠ i then f i j else 0 :=
      Finset.sum_comm
    _ = ∑ j, ∑ i, if i ≠ j then f i j else 0 := by
      apply Finset.sum_congr rfl
      intro j _hj
      apply Finset.sum_congr rfl
      intro i _hi
      simp only [ne_comm]
    _ = ∑ j, ∑ i ∈ Finset.univ.erase j, f i j := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [← Finset.filter_ne' Finset.univ j, Finset.sum_filter]

private theorem offdiag_abs_sum_le_weighted_squares
    {n : Type*} [Fintype n] [DecidableEq n]
    (w : n → ℝ) (r : n → n → ℝ)
    (hw : ∀ i, 0 < w i)
    (hr0 : ∀ i j, 0 ≤ r i j)
    (hrsymm : ∀ i j, r i j = r j i)
    (x : n → ℝ) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, r i j * |x i * x j|) ≤
      ∑ i, (∑ j ∈ Finset.univ.erase i, r i j * w j / w i) * x i ^ 2 := by
  classical
  let cross : ℝ :=
    ∑ i, ∑ j ∈ Finset.univ.erase i, r i j * |x i * x j|
  let first : ℝ :=
    ∑ i, ∑ j ∈ Finset.univ.erase i,
      r i j * ((w j / w i) * x i ^ 2)
  let second : ℝ :=
    ∑ i, ∑ j ∈ Finset.univ.erase i,
      r i j * ((w i / w j) * x j ^ 2)
  have hterm : ∀ i j, i ≠ j →
      2 * (r i j * |x i * x j|) ≤
        r i j * ((w j / w i) * x i ^ 2) +
          r i j * ((w i / w j) * x j ^ 2) := by
    intro i j _hij
    have hy := weighted_young (u := x i) (v := x j) (hw i) (hw j)
    nlinarith [mul_le_mul_of_nonneg_left hy (hr0 i j)]
  have hdouble : 2 * cross ≤ first + second := by
    dsimp only [cross, first, second]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _hi
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j hj
    exact hterm i j (Finset.ne_of_mem_erase hj).symm
  have hsecond : second = first := by
    dsimp only [second, first]
    calc
      (∑ i, ∑ j ∈ Finset.univ.erase i,
          r i j * ((w i / w j) * x j ^ 2)) =
          ∑ i, ∑ j ∈ Finset.univ.erase i,
            r j i * ((w j / w i) * x i ^ 2) := by
        exact sum_erase_swap
          (fun i j ↦ r i j * ((w i / w j) * x j ^ 2))
      _ = ∑ i, ∑ j ∈ Finset.univ.erase i,
          r i j * ((w j / w i) * x i ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _hi
        apply Finset.sum_congr rfl
        intro j _hj
        rw [hrsymm j i]
  have hfirst : first =
      ∑ i, (∑ j ∈ Finset.univ.erase i, r i j * w j / w i) * x i ^ 2 := by
    dsimp only [first]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  dsimp only [cross] at hdouble ⊢
  rw [hsecond, ← two_mul, hfirst] at hdouble
  linarith

private theorem neg_radius_mul_abs_le_entry_mul
    {a t radius : ℝ} (hradius : |a| ≤ radius) :
    -radius * |t| ≤ a * t := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
    exact mul_le_mul_of_nonneg_right (neg_le_of_abs_le hradius) ht
  · have ht' : t ≤ 0 := le_of_not_ge ht
    rw [abs_of_nonpos ht']
    have ha : a ≤ radius := le_of_abs_le hradius
    nlinarith [mul_le_mul_of_nonpos_right ha ht']

theorem posDef_of_weighted_entry_bounds
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian)
    (d w : n → ℝ) (r : n → n → ℝ)
    (hw : ∀ i, 0 < w i)
    (hr0 : ∀ i j, 0 ≤ r i j)
    (hrsymm : ∀ i j, r i j = r j i)
    (hdiag : ∀ i, d i ≤ A i i)
    (hoff : ∀ i j, i ≠ j → |A i j| ≤ r i j)
    (hdom : ∀ i, (∑ j ∈ Finset.univ.erase i, r i j * w j) < d i * w i) :
    A.PosDef := by
  classical
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hA fun x hx ↦ ?_
  let radiusSum : n → ℝ := fun i ↦
    ∑ j ∈ Finset.univ.erase i, r i j * w j / w i
  have hradiusSum : ∀ i, 0 < d i - radiusSum i := by
    intro i
    dsimp only [radiusSum]
    rw [← Finset.sum_div]
    exact sub_pos.mpr ((div_lt_iff₀ (hw i)).2 (hdom i))
  have hslack : 0 < ∑ i, (d i - radiusSum i) * x i ^ 2 := by
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx (funext h)
    apply Finset.sum_pos'
    · intro j _hj
      exact mul_nonneg (hradiusSum j).le (sq_nonneg (x j))
    · exact ⟨i, Finset.mem_univ i,
        mul_pos (hradiusSum i) (sq_pos_of_ne_zero hi)⟩
  have hcross := offdiag_abs_sum_le_weighted_squares
    w r hw hr0 hrsymm x
  have hlower :
      (∑ i, (d i - radiusSum i) * x i ^ 2) ≤
        ∑ i, d i * x i ^ 2 -
          ∑ i, ∑ j ∈ Finset.univ.erase i, r i j * |x i * x j| := by
    have hslack_eq :
        (∑ i, (d i - radiusSum i) * x i ^ 2) =
          (∑ i, d i * x i ^ 2) - ∑ i, radiusSum i * x i ^ 2 := by
      calc
        (∑ i, (d i - radiusSum i) * x i ^ 2) =
            ∑ i, (d i * x i ^ 2 - radiusSum i * x i ^ 2) := by
          apply Finset.sum_congr rfl
          intro i _hi
          ring
        _ = (∑ i, d i * x i ^ 2) - ∑ i, radiusSum i * x i ^ 2 := by
          rw [Finset.sum_sub_distrib]
    rw [hslack_eq]
    dsimp only [radiusSum]
    linarith
  have hentry :
      (∑ i, (d i * x i ^ 2 -
          ∑ j ∈ Finset.univ.erase i, r i j * |x i * x j|)) ≤
        dotProduct (star x) (A.mulVec x) := by
    simp only [dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _hi
    have hdiagTerm : d i * x i ^ 2 ≤ A i i * x i ^ 2 :=
      mul_le_mul_of_nonneg_right (hdiag i) (sq_nonneg (x i))
    have hoffTerm :
        -(∑ j ∈ Finset.univ.erase i, r i j * |x i * x j|) ≤
          ∑ j ∈ Finset.univ.erase i, x i * (A i j * x j) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_le_sum
      intro j hj
      have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
      have h := neg_radius_mul_abs_le_entry_mul
        (t := x i * x j) (hoff i j hij)
      nlinarith
    rw [← Finset.add_sum_erase Finset.univ
      (fun j ↦ x i * (A i j * x j)) (Finset.mem_univ i)]
    nlinarith
  have hpositive :
      0 < ∑ i, d i * x i ^ 2 -
        ∑ i, ∑ j ∈ Finset.univ.erase i, r i j * |x i * x j| :=
    hslack.trans_le hlower
  apply hpositive.trans_le
  rw [Finset.sum_sub_distrib] at hentry
  exact hentry

end ArithmeticHodge.Analysis.WeightedDiagonalDominance
