import ArithmeticHodge.Analysis.MultiplicativeWeilMinimalBlockEndpointEliminationStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneFourCellPrimeGeometryStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilRealMonotoneTailConeCriterionStructural

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeilAllLengthEndpointReserveStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilMinimalNegativeBlockStructural
open MultiplicativeWeilMonotoneFourCellPrimeGeometryStructural
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural
open MultiplicativeWeilRealMonotoneTailConeCriterionStructural

/-!
# The first all-length endpoint remainder

The overlap recurrence first leaves the genuinely remote endpoint pair at
block length five.  The common-parent monotone masks do constrain that pair,
but they do not reduce it to the two adjacent four-cell prime masks.

At factor two, the two endpoint cells have the same canonical weight, so
their product carries the square `w_k^2`.  Meanwhile the two overlapping
four-cell blocks carry the complementary masks

`s_k (1-s_k)` and `s_(k+1) (1-s_(k+1))`.

Their exact inclusion-exclusion identity is

`w_k = s_k (1-s_k) + s_(k+1) (1-s_(k+1)) + w_k^2`.

Thus the first all-length step retains a positive square prime mask after
both adjacent four-cell masks have been used.  That square cannot be bounded
pointwise by any finite multiple of the two complementary masks: at their
shared lattice boundary it equals one while both complementary masks vanish.
Any successful endpoint-reserve argument must therefore use local/endpoint
energy at the same time as the prime term; iterating four-cell prime-mask
absorption alone cannot close the five-cell step.
-/

/-- Factor two transports a canonical cell weight four quarter-steps
forward exactly back to the original weight. -/
theorem monotoneQuarterWeight_add_four_two_mul
    (k : ℤ) (x : ℝ) :
    monotoneQuarterWeight (k + 4) (2 * x) =
      monotoneQuarterWeight k x := by
  unfold monotoneQuarterWeight
  rw [monotoneQuarterStep_add_four_two_mul k x]
  have hindex : k + 4 + 1 = (k + 1) + 4 := by ring
  rw [hindex, monotoneQuarterStep_add_four_two_mul (k + 1) x]

/-- Five consecutive cells, the first block length not covered by the two
overlapping four-cell windows. -/
def monotoneQuarterFiveBlock
    (parent : BombieriTest) (k : ℤ) : BombieriTest :=
  monotoneQuarterFiniteBlock parent k 0 5

/-- The five-cell block telescopes to boundary steps five quarter-steps
apart. -/
theorem monotoneQuarterFiveBlock_apply
    (parent : BombieriTest) (k : ℤ) (x : ℝ) :
    monotoneQuarterFiveBlock parent k x =
      (((monotoneQuarterStep k x -
        monotoneQuarterStep (k + 5) x : ℝ) : ℂ) * parent x) := by
  unfold monotoneQuarterFiveBlock monotoneQuarterFiniteBlock
  simp only [Nat.zero_add]
  rw [sum_range_monotoneQuarterCell_eq_cutoff_sub]
  simp only [TestFunction.coe_sub, Pi.sub_apply,
    monotoneQuarterCutoff_apply]
  push_cast
  ring

/-- The factor-two product of the remote endpoint cells in a five-cell block
has the exact square common-parent mask. -/
theorem fiveCell_remoteEndpoint_two_mul_product_eq_squareMask
    (parent : BombieriTest) (k : ℤ) (x : ℝ) :
    monotoneQuarterCell parent (k + 4) (2 * x) *
        starRingEnd ℂ (monotoneQuarterCell parent k x) =
      ((monotoneQuarterWeight k x ^ 2 : ℝ) : ℂ) *
        parent (2 * x) * starRingEnd ℂ (parent x) := by
  rw [monotoneQuarterCell_apply, monotoneQuarterCell_apply,
    monotoneQuarterWeight_add_four_two_mul,
    map_mul (starRingEnd ℂ), Complex.conj_ofReal]
  push_cast
  ring

/-- The complete factor-two mask of five consecutive cells, restricted to
the only possible base-cell interaction interval, is the full canonical
cell weight rather than a complementary four-cell mask. -/
theorem fiveCell_factorTwo_mask_eq_weight
    (k : ℤ) (x : ℝ) :
    monotoneQuarterStep k x *
        (1 - monotoneQuarterStep (k + 1) x) =
      monotoneQuarterWeight k x := by
  have hnested := monotoneQuarterStep_mul_later
    (k := k) (j := k + 1) (by omega) x
  unfold monotoneQuarterWeight
  nlinarith

/-- On the complete support of the first endpoint cell, the actual
five-cell factor-two product carries exactly the full cell weight. -/
theorem monotoneQuarterFiveBlock_two_mul_product_eq_weight
    (parent : BombieriTest) (k : ℤ) {x : ℝ}
    (hx : x ∈ Set.Icc (quarterLogLatticePoint k)
      (quarterLogLatticePoint (k + 2))) :
    monotoneQuarterFiveBlock parent k (2 * x) *
        starRingEnd ℂ (monotoneQuarterFiveBlock parent k x) =
      ((monotoneQuarterWeight k x : ℝ) : ℂ) *
        parent (2 * x) * starRingEnd ℂ (parent x) := by
  have hupperZero : monotoneQuarterStep (k + 5) x = 0 := by
    apply monotoneQuarterStep_eq_zero_of_le
    exact hx.2.trans (quarterLogLatticePoint_mono (by omega))
  have hlowerOne : monotoneQuarterStep k (2 * x) = 1 := by
    apply monotoneQuarterStep_eq_one_of_le
    calc
      quarterLogLatticePoint (k + 1) ≤
          quarterLogLatticePoint (k + 4) :=
        quarterLogLatticePoint_mono (by omega)
      _ = 2 * quarterLogLatticePoint k := by
        rw [quarterLogLatticePoint_add_four]
      _ ≤ 2 * x := mul_le_mul_of_nonneg_left hx.1 (by norm_num)
  have htransport : monotoneQuarterStep (k + 5) (2 * x) =
      monotoneQuarterStep (k + 1) x := by
    have hindex : k + 5 = (k + 1) + 4 := by ring
    rw [hindex, monotoneQuarterStep_add_four_two_mul]
  rw [monotoneQuarterFiveBlock_apply,
    monotoneQuarterFiveBlock_apply, hupperZero, hlowerOne, htransport,
    map_mul (starRingEnd ℂ), Complex.conj_ofReal]
  have hmask := fiveCell_factorTwo_mask_eq_weight k x
  calc
    ((1 - monotoneQuarterStep (k + 1) x : ℝ) : ℂ) * parent (2 * x) *
          (((monotoneQuarterStep k x - 0 : ℝ) : ℂ) *
            starRingEnd ℂ (parent x)) =
        ((monotoneQuarterStep k x *
          (1 - monotoneQuarterStep (k + 1) x) : ℝ) : ℂ) *
          parent (2 * x) * starRingEnd ℂ (parent x) := by
      push_cast
      ring
    _ = _ := by rw [hmask]

/-- Exact prime-mask inclusion-exclusion at the first all-length step.  The
last summand is precisely the remote endpoint square from the overlap
recurrence. -/
theorem fiveCell_factorTwo_mask_eq_adjacentFourCell_add_remoteSquare
    (k : ℤ) (x : ℝ) :
    monotoneQuarterWeight k x =
      monotoneQuarterStep k x * (1 - monotoneQuarterStep k x) +
        monotoneQuarterStep (k + 1) x *
          (1 - monotoneQuarterStep (k + 1) x) +
        monotoneQuarterWeight k x ^ 2 := by
  have hnested := monotoneQuarterStep_mul_later
    (k := k) (j := k + 1) (by omega) x
  unfold monotoneQuarterWeight
  nlinarith

/-- At the shared boundary of the two adjacent transition intervals, the
remote endpoint square is one while both four-cell complementary masks are
zero. -/
theorem fiveCell_remoteSquare_eq_one_adjacentMasks_eq_zero (k : ℤ) :
    monotoneQuarterWeight k (quarterLogLatticePoint (k + 1)) ^ 2 = 1 ∧
      monotoneQuarterStep k (quarterLogLatticePoint (k + 1)) *
          (1 - monotoneQuarterStep k (quarterLogLatticePoint (k + 1))) = 0 ∧
      monotoneQuarterStep (k + 1) (quarterLogLatticePoint (k + 1)) *
          (1 - monotoneQuarterStep (k + 1)
            (quarterLogLatticePoint (k + 1))) = 0 := by
  have hk : monotoneQuarterStep k (quarterLogLatticePoint (k + 1)) = 1 :=
    monotoneQuarterStep_eq_one_of_le k le_rfl
  have hk1 : monotoneQuarterStep (k + 1)
      (quarterLogLatticePoint (k + 1)) = 0 :=
    monotoneQuarterStep_eq_zero_of_le (k + 1) le_rfl
  rw [monotoneQuarterWeight, hk, hk1]
  norm_num

/-- No finite constant can pay the remote endpoint square using only the two
adjacent four-cell complementary prime masks.  This is an actual
common-parent-mask obstruction, stronger than the abstract equicorrelation
countermodel. -/
theorem no_constant_remoteSquare_bound_by_adjacentFourCellPrimeMasks
    (C : ℝ) (k : ℤ) :
    ¬ ∀ x : ℝ,
      monotoneQuarterWeight k x ^ 2 ≤
        C * (monotoneQuarterStep k x *
              (1 - monotoneQuarterStep k x) +
            monotoneQuarterStep (k + 1) x *
              (1 - monotoneQuarterStep (k + 1) x)) := by
  intro h
  have hboundary := h (quarterLogLatticePoint (k + 1))
  obtain ⟨hsquare, hleft, hright⟩ :=
    fiveCell_remoteSquare_eq_one_adjacentMasks_eq_zero k
  rw [hsquare, hleft, hright] at hboundary
  norm_num at hboundary

end

end ArithmeticHodge.Analysis.MultiplicativeWeilAllLengthEndpointReserveStructural
