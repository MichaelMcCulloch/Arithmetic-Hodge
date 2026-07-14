import ArithmeticHodge.Analysis.CauchyKernelFiniteSumBounds
import ArithmeticHodge.Analysis.YoshidaSineCheckpointedHead
import ArithmeticHodge.Analysis.YoshidaSineStructuralWidth

set_option autoImplicit false

open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaSineCheckpointStructuralWidth

open RatInterval
open CauchyKernelFiniteSumBounds
open YoshidaSineCheckpointedHead
open YoshidaSineMomentEnclosures
open YoshidaSineStructuralWidth

/-!
# Structural widths for checkpointed sine heads

The exact finite head is bounded by one telescoping Cauchy-kernel estimate.
The checkpointed version then pays only the explicit outward-rounding error,
once per block.  Neither argument inspects individual modes or head entries.
-/

theorem sineCauchyChunkInterval_width_eq
    (n start len : ℕ) :
    width (sineCauchyChunkInterval n start len) =
      ∑ k ∈ Finset.range len,
        width (scaledSineCauchyTermInterval n (start + k)) := by
  exact width_recursive_add_eq_sum
    (sineCauchyChunkInterval n start)
    (fun k ↦ scaledSineCauchyTermInterval n (start + k))
    rfl (fun _ ↦ rfl) len

theorem exactSineCheckpointHead_width_eq_terms
    (n blocks : ℕ) :
    width (exactSineCheckpointHead n blocks) =
      ∑ k ∈ Finset.range (256 * blocks),
        width (scaledSineCauchyTermInterval n k) := by
  induction blocks with
  | zero => simp [exactSineCheckpointHead, width_pure]
  | succ blocks ih =>
      rw [exactSineCheckpointHead, width_add, ih]
      rw [show 256 * (blocks + 1) = 256 * blocks + 256 by omega,
        Finset.sum_range_add]
      rw [show scheduledSineCauchyChunkInterval n blocks =
        sineCauchyChunkInterval n (256 * blocks) 256 by rfl]
      rw [sineCauchyChunkInterval_width_eq]

/-- Every positive-mode exact checkpoint head has the same uniform width
budget, regardless of how many checkpoints are retained. -/
theorem exactSineCheckpointHead_width_le
    {n : ℕ} (hn : 1 ≤ n) (blocks : ℕ) :
    width (exactSineCheckpointHead n blocks) ≤
      (1 : ℚ) / 4500000000 := by
  rw [exactSineCheckpointHead_width_eq_terms]
  calc
    (∑ k ∈ Finset.range (256 * blocks),
        width (scaledSineCauchyTermInterval n k)) ≤
        ∑ k ∈ Finset.range (256 * blocks),
          ((n : ℚ) / 2250000000) *
            (sineCauchyDenominatorFloor n k)⁻¹ := by
      exact Finset.sum_le_sum fun k _ ↦
        scaledSineCauchyTermInterval_width_le hn k
    _ = ((n : ℚ) / 2250000000) *
        ∑ k ∈ Finset.range (256 * blocks),
          halfStepQuarterShiftedCauchyKernel n k := by
      rw [← Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      simp only [sineCauchyDenominatorFloor,
        halfStepQuarterShiftedCauchyKernel, one_div]
    _ ≤ ((n : ℚ) / 2250000000) * (1 / (2 * (n : ℚ))) := by
      exact mul_le_mul_of_nonneg_left
        (sum_halfStepQuarterShiftedCauchyKernel_le hn (256 * blocks))
        (by positivity)
    _ = (1 : ℚ) / 4500000000 := by
      have hn0 : (n : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.zero_lt_of_lt hn).ne'
      field_simp [hn0]
      norm_num

private theorem checkpointOutwardRoundedInterval_width_le
    {scale : ℚ} (hscale : 0 < scale) (I : RatInterval) :
    width (YoshidaSineCheckpointedHead.outwardRoundedInterval scale I) ≤
      width I + 2 / scale := by
  simpa only [YoshidaSineCheckpointedHead.outwardRoundedInterval,
    RatInterval.outwardRoundedInterval] using
      (RatInterval.width_outwardRoundedInterval_le hscale I)

theorem exactSineCheckpointHead_width_eq_chunks
    (n blocks : ℕ) :
    width (exactSineCheckpointHead n blocks) =
      ∑ i ∈ Finset.range blocks,
        width (scheduledSineCauchyChunkInterval n i) := by
  exact width_recursive_add_eq_sum
    (exactSineCheckpointHead n)
    (scheduledSineCauchyChunkInterval n)
    rfl (fun _ ↦ rfl) blocks

theorem coarseSineCheckpointHead_width_eq
    (box : ℕ → RatInterval) (blocks : ℕ) :
    width (coarseSineCheckpointHead box blocks) =
      ∑ i ∈ Finset.range blocks, width (box i) := by
  exact width_recursive_add_eq_sum
    (coarseSineCheckpointHead box) box rfl (fun _ ↦ rfl) blocks

/-- Checkpoint rounding contributes at most two grid cells per block. -/
theorem coarseRoundedSineCheckpointHead_width_le
    (n blocks : ℕ) {scale : ℚ} (hscale : 0 < scale) :
    width (coarseSineCheckpointHead
        (roundedSineCauchyChunkBox n scale) blocks) ≤
      width (exactSineCheckpointHead n blocks) +
        (blocks : ℚ) * (2 / scale) := by
  rw [coarseSineCheckpointHead_width_eq,
    exactSineCheckpointHead_width_eq_chunks]
  calc
    (∑ i ∈ Finset.range blocks,
        width (roundedSineCauchyChunkBox n scale i)) ≤
        ∑ i ∈ Finset.range blocks,
          (width (scheduledSineCauchyChunkInterval n i) + 2 / scale) := by
      exact Finset.sum_le_sum fun i _ ↦ by
        simpa only [roundedSineCauchyChunkBox] using
          checkpointOutwardRoundedInterval_width_le hscale
            (scheduledSineCauchyChunkInterval n i)
    _ = (∑ i ∈ Finset.range blocks,
          width (scheduledSineCauchyChunkInterval n i)) +
        (blocks : ℚ) * (2 / scale) := by
      rw [Finset.sum_add_distrib]
      simp

/-- Complete structural width bound for a rounded positive-mode head. -/
theorem coarseRoundedSineCheckpointHead_width_le_uniform
    {n : ℕ} (hn : 1 ≤ n) (blocks : ℕ)
    {scale : ℚ} (hscale : 0 < scale) :
    width (coarseSineCheckpointHead
        (roundedSineCauchyChunkBox n scale) blocks) ≤
      (1 : ℚ) / 4500000000 + (blocks : ℚ) * (2 / scale) := by
  exact (coarseRoundedSineCheckpointHead_width_le n blocks hscale).trans
    (add_le_add (exactSineCheckpointHead_width_le hn blocks) le_rfl)

end ArithmeticHodge.Analysis.YoshidaSineCheckpointStructuralWidth
