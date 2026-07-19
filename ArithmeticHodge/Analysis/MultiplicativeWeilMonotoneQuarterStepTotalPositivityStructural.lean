import ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneQuarterPartitionStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilCoherentCutPencilStructural

set_option autoImplicit false

open Real

namespace ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneQuarterStepTotalPositivityStructural

noncomputable section

open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural
open MultiplicativeWeilCoherentCutPencilStructural

/-!
# Total positivity of adjacent monotone quarter steps

Adjacent canonical steps have disjoint transition interiors: before the
common lattice point the later step is zero, and after that point the earlier
step is one.  Consequently their two-by-two evaluation determinant has a
fixed sign.  For a multiplicative prime ratio `x ≥ 1`, this gives the exact
sign of the antisymmetric head--suffix mask.
-/

/-- Adjacent monotone quarter steps form a TP2 pair.  This stronger additive
order formulation does not require positivity of either evaluation point. -/
theorem monotoneQuarterStep_adjacent_det_nonnegative
    (k : ℤ) {y z : ℝ} (hyz : y ≤ z) :
    0 ≤ monotoneQuarterStep (k + 1) z * monotoneQuarterStep k y -
      monotoneQuarterStep k z * monotoneQuarterStep (k + 1) y := by
  by_cases hy : y ≤ quarterLogLatticePoint (k + 1)
  · rw [monotoneQuarterStep_eq_zero_of_le (k + 1) hy, mul_zero, sub_zero]
    exact mul_nonneg
      (monotoneQuarterStep_nonneg (k + 1) z)
      (monotoneQuarterStep_nonneg k y)
  · have hqy : quarterLogLatticePoint (k + 1) ≤ y := (not_le.mp hy).le
    have hqz : quarterLogLatticePoint (k + 1) ≤ z := hqy.trans hyz
    rw [monotoneQuarterStep_eq_one_of_le k hqy,
      monotoneQuarterStep_eq_one_of_le k hqz, mul_one, one_mul]
    exact sub_nonneg.mpr (monotoneQuarterStep_monotone (k + 1) hyz)

/-- Multiplication by a ratio at least one moves a nonnegative physical point
to the right. -/
theorem monotoneQuarterStep_adjacent_mul_det_nonnegative
    (k : ℤ) {x y : ℝ} (hx : 1 ≤ x) (hy : 0 ≤ y) :
    0 ≤ monotoneQuarterStep (k + 1) (x * y) *
          monotoneQuarterStep k y -
        monotoneQuarterStep k (x * y) *
          monotoneQuarterStep (k + 1) y := by
  apply monotoneQuarterStep_adjacent_det_nonnegative k
  calc
    y = 1 * y := by ring
    _ ≤ x * y := mul_le_mul_of_nonneg_right hx hy

/-- The antisymmetric mask for a head cell and its complete monotone suffix.
Here the head is `step k - step (k+1)` and the suffix is `step (k+1)`. -/
def monotoneQuarterNestedAntisymmetricMask
    (k : ℤ) (x y : ℝ) : ℝ :=
  monotoneQuarterStep (k + 1) (x * y) * monotoneQuarterWeight k y -
    monotoneQuarterWeight k (x * y) * monotoneQuarterStep (k + 1) y

/-- Expanding the head differences cancels the suffix--suffix terms, leaving
exactly the adjacent-step TP2 determinant. -/
theorem monotoneQuarterNestedAntisymmetricMask_eq_step_det
    (k : ℤ) (x y : ℝ) :
    monotoneQuarterNestedAntisymmetricMask k x y =
      monotoneQuarterStep (k + 1) (x * y) *
          monotoneQuarterStep k y -
        monotoneQuarterStep k (x * y) *
          monotoneQuarterStep (k + 1) y := by
  unfold monotoneQuarterNestedAntisymmetricMask monotoneQuarterWeight
  ring

/-- Therefore the complete monotone head--suffix antisymmetric mask has a
fixed nonnegative sign at every real ratio at least one. -/
theorem monotoneQuarterNestedAntisymmetricMask_nonnegative
    (k : ℤ) {x y : ℝ} (hx : 1 ≤ x) (hy : 0 ≤ y) :
    0 ≤ monotoneQuarterNestedAntisymmetricMask k x y := by
  rw [monotoneQuarterNestedAntisymmetricMask_eq_step_det]
  exact monotoneQuarterStep_adjacent_mul_det_nonnegative k hx hy

/-- On the positive integration domain used by Bombieri correlations, the
same sign conclusion needs only `1 ≤ x`. -/
theorem monotoneQuarterNestedAntisymmetricMask_nonnegative_of_pos
    (k : ℤ) {x y : ℝ} (hx : 1 ≤ x) (hy : 0 < y) :
    0 ≤ monotoneQuarterNestedAntisymmetricMask k x y :=
  monotoneQuarterNestedAntisymmetricMask_nonnegative k hx hy.le

/-! ## Connection to the finite coherent-cut API -/

/-- A finite suffix of the explicit weights telescopes to the difference of
its initial and terminal steps. -/
theorem coherentCutSuffixMask_monotoneQuarterWeight_eq_step_sub
    (k hi : ℤ) (hki : k ≤ hi) (z : ℝ) :
    coherentCutSuffixMask monotoneQuarterWeight k hi z =
      monotoneQuarterStep (k + 1) z - monotoneQuarterStep (hi + 1) z := by
  unfold coherentCutSuffixMask
  rw [Int.Icc_eq_finset_map, Finset.sum_map]
  rw [show hi + 1 - (k + 1) = hi - k by ring]
  have hdiff : 0 ≤ hi - k := sub_nonneg.mpr hki
  have hcast : (((hi - k).toNat : ℕ) : ℤ) = hi - k := by
    exact Int.toNat_of_nonneg hdiff
  have hsum := sum_range_monotoneQuarterWeight
    (k + 1) (hi - k).toNat z
  rw [hcast] at hsum
  simpa only [Function.Embedding.trans_apply, Nat.castEmbedding_apply,
    addLeftEmbedding_apply,
    show k + 1 + (hi - k) = hi + 1 by ring] using hsum

/-- If the terminal step vanishes at both correlated points, the coherent
finite-cut antisymmetric mask is exactly the nested-cutoff mask above. -/
theorem coherentCutAntisymmetricMask_monotoneQuarterWeight_eq_nested
    (k hi : ℤ) (hki : k ≤ hi) (x y : ℝ)
    (hterminalY : monotoneQuarterStep (hi + 1) y = 0)
    (hterminalXY : monotoneQuarterStep (hi + 1) (x * y) = 0) :
    coherentCutAntisymmetricMask monotoneQuarterWeight k hi x y =
      monotoneQuarterNestedAntisymmetricMask k x y := by
  unfold coherentCutAntisymmetricMask monotoneQuarterNestedAntisymmetricMask
  rw [coherentCutSuffixMask_monotoneQuarterWeight_eq_step_sub k hi hki y,
    coherentCutSuffixMask_monotoneQuarterWeight_eq_step_sub
      k hi hki (x * y), hterminalY, hterminalXY]
  ring

/-- Hence an actual finite coherent monotone suffix has nonnegative
antisymmetric mask at every prime ratio, on points where its terminal cutoff
has already vanished. -/
theorem coherentCutAntisymmetricMask_monotoneQuarterWeight_nonnegative
    (k hi : ℤ) (hki : k ≤ hi) {x y : ℝ}
    (hx : 1 ≤ x) (hy : 0 ≤ y)
    (hterminalY : monotoneQuarterStep (hi + 1) y = 0)
    (hterminalXY : monotoneQuarterStep (hi + 1) (x * y) = 0) :
    0 ≤ coherentCutAntisymmetricMask monotoneQuarterWeight k hi x y := by
  rw [coherentCutAntisymmetricMask_monotoneQuarterWeight_eq_nested
    k hi hki x y hterminalY hterminalXY]
  exact monotoneQuarterNestedAntisymmetricMask_nonnegative k hx hy

/-- A directly geometric version: the terminal-step hypotheses follow when
both correlated points lie below its lattice threshold. -/
theorem coherentCutAntisymmetricMask_monotoneQuarterWeight_nonnegative_of_le_terminal
    (k hi : ℤ) (hki : k ≤ hi) {x y : ℝ}
    (hx : 1 ≤ x) (hy : 0 ≤ y)
    (hyTerminal : y ≤ quarterLogLatticePoint (hi + 1))
    (hxyTerminal : x * y ≤ quarterLogLatticePoint (hi + 1)) :
    0 ≤ coherentCutAntisymmetricMask monotoneQuarterWeight k hi x y := by
  apply coherentCutAntisymmetricMask_monotoneQuarterWeight_nonnegative
    k hi hki hx hy
  · exact monotoneQuarterStep_eq_zero_of_le (hi + 1) hyTerminal
  · exact monotoneQuarterStep_eq_zero_of_le (hi + 1) hxyTerminal

end

end ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneQuarterStepTotalPositivityStructural
