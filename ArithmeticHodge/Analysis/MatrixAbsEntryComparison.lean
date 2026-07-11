import Mathlib.Analysis.Matrix.PosDef

set_option autoImplicit false

open scoped BigOperators ComplexOrder

namespace Matrix

private lemma diagonal_comparison (u : ℝ) (a b : ℂ) (h : u ≤ b.re) :
    u * ‖a‖ * ‖a‖ ≤ (star a * b * a).re := by
  calc
    u * ‖a‖ * ‖a‖ = u * ‖a‖ ^ 2 := by ring
    _ ≤ b.re * ‖a‖ ^ 2 := mul_le_mul_of_nonneg_right h (sq_nonneg _)
    _ = (star a * b * a).re := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp only [Complex.star_def, Complex.mul_re, Complex.mul_im,
        Complex.conj_re, Complex.conj_im]
      ring

private lemma offDiagonal_comparison (u : ℝ) (a b c : ℂ) (h : ‖b‖ ≤ -u) :
    u * ‖a‖ * ‖c‖ ≤ (star a * b * c).re := by
  calc
    u * ‖a‖ * ‖c‖ = u * (‖a‖ * ‖c‖) := by ring
    _ ≤ (-‖b‖) * (‖a‖ * ‖c‖) := by
      gcongr
      linarith
    _ = -‖star a * b * c‖ := by simp; ring
    _ ≤ (star a * b * c).re := neg_le_of_abs_le (Complex.abs_re_le_norm _)

theorem posDef_of_abs_entry_comparison
    {n : Type*} [Fintype n] [DecidableEq n]
    (G : Matrix n n ℂ) (U : Matrix n n ℝ)
    (hG : G.IsHermitian) (hU : U.PosDef)
    (hdiag : ∀ i, U i i ≤ (G i i).re)
    (hoff : ∀ i j, i ≠ j → ‖G i j‖ ≤ -U i j) : G.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hG fun z hz ↦ ?_
  apply RCLike.pos_iff.mpr
  refine ⟨?_, hG.im_star_dotProduct_mulVec_self z⟩
  let r : n → ℝ := fun i ↦ ‖z i‖
  have hr : r ≠ 0 := by
    intro hr
    apply hz
    funext i
    exact norm_eq_zero.mp (congr_fun hr i)
  have hpositive : 0 < star r ⬝ᵥ (U *ᵥ r) := hU.dotProduct_mulVec_pos hr
  apply hpositive.trans_le
  simp only [dotProduct, mulVec, Finset.mul_sum, map_sum, star_trivial, r]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  by_cases hij : i = j
  · subst j
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      diagonal_comparison (U i i) (z i) (G i i) (hdiag i)
  · simpa only [mul_assoc, mul_left_comm, mul_comm] using
      offDiagonal_comparison (U i j) (z i) (G i j) (z j) (hoff i j hij)

end Matrix
