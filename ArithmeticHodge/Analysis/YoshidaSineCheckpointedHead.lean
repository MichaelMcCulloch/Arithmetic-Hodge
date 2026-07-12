import ArithmeticHodge.Analysis.YoshidaSineAcceleratedEnclosures

set_option autoImplicit false

open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaSineCheckpointedHead

open RatInterval
open YoshidaMomentSeries
open YoshidaOddGramPrefix
open YoshidaSineAcceleratedEnclosures
open YoshidaSineMomentEnclosures
open YoshidaSineSeriesTail

/-!
# Checkpointed finite heads for Yoshida sine moments

Large exact Cauchy heads are evaluated in independent 256-term chunks.  Each
chunk can then be certified inside a small rational checkpoint box, so the
final enclosure contains only a shallow sum of compact endpoints rather than
one enormous recursively reduced rational expression.
-/

/-- Exact interval evaluation of `len` consecutive scaled Cauchy terms. -/
def sineCauchyChunkInterval (n start : ℕ) : ℕ → RatInterval
  | 0 => pure 0
  | len + 1 =>
      sineCauchyChunkInterval n start len +
        scaledSineCauchyTermInterval n (start + len)

theorem sineCauchyChunkInterval_contains (n start len : ℕ) :
    (sineCauchyChunkInterval n start len).Contains
      (∑ k ∈ Finset.range len, scaledSineCauchyTerm n (start + k)) := by
  induction len with
  | zero =>
      norm_num [sineCauchyChunkInterval, Contains, RatInterval.pure]
  | succ len ih =>
      rw [Finset.sum_range_succ]
      exact contains_add ih
        (scaledSineCauchyTermInterval_contains n (start + len))

/-- The exact interval for checkpoint `i`, consisting of 256 terms. -/
def scheduledSineCauchyChunkInterval (n i : ℕ) : RatInterval :=
  sineCauchyChunkInterval n (256 * i) 256

/-- Exact sum of the first `used` checkpoint intervals. -/
def exactSineCheckpointHead (n : ℕ) : ℕ → RatInterval
  | 0 => pure 0
  | used + 1 =>
      exactSineCheckpointHead n used +
        scheduledSineCauchyChunkInterval n used

/-- Sum of externally supplied compact checkpoint boxes. -/
def coarseSineCheckpointHead (box : ℕ → RatInterval) : ℕ → RatInterval
  | 0 => pure 0
  | used + 1 => coarseSineCheckpointHead box used + box used

/-- Round an interval outward to the grid with spacing `scale⁻¹`. -/
def outwardRoundedInterval (scale : ℚ) (I : RatInterval) : RatInterval :=
  ⟨((I.lower * scale).floor : ℚ) / scale,
    ((I.upper * scale).ceil : ℚ) / scale⟩

theorem outwardRoundedInterval_subinterval
    {scale : ℚ} (hscale : 0 < scale) (I : RatInterval) :
    IsSubinterval I (outwardRoundedInterval scale I) := by
  constructor
  · change ((I.lower * scale).floor : ℚ) / scale ≤ I.lower
    exact (div_le_iff₀ hscale).2 (Rat.floor_le (I.lower * scale))
  · change I.upper ≤ ((I.upper * scale).ceil : ℚ) / scale
    exact (le_div_iff₀ hscale).2 Rat.le_ceil

/-- A compact, automatically outward-rounded box for one exact checkpoint. -/
def roundedSineCauchyChunkBox (n : ℕ) (scale : ℚ) (i : ℕ) : RatInterval :=
  outwardRoundedInterval scale (scheduledSineCauchyChunkInterval n i)

theorem scheduledSineCauchyChunkInterval_sub_rounded
    (n i : ℕ) {scale : ℚ} (hscale : 0 < scale) :
    IsSubinterval (scheduledSineCauchyChunkInterval n i)
      (roundedSineCauchyChunkBox n scale i) :=
  outwardRoundedInterval_subinterval hscale _

theorem exactSineCheckpointHead_contains (n blocks : ℕ) :
    (exactSineCheckpointHead n blocks).Contains
      (∑ k ∈ Finset.range (256 * blocks), scaledSineCauchyTerm n k) := by
  induction blocks with
  | zero =>
      norm_num [exactSineCheckpointHead, Contains, RatInterval.pure]
  | succ blocks ih =>
      rw [exactSineCheckpointHead]
      rw [show 256 * (blocks + 1) = 256 * blocks + 256 by omega]
      rw [Finset.sum_range_add]
      exact contains_add ih
        (sineCauchyChunkInterval_contains n (256 * blocks) 256)

theorem exactSineCheckpointHead_contains_production
    {n : ℕ} (hn : n ≠ 0) (blocks : ℕ) :
    (exactSineCheckpointHead n blocks).Contains
      (∑ k ∈ Finset.range (256 * blocks), sineCauchyTerm n k) := by
  convert exactSineCheckpointHead_contains n blocks using 1
  apply Finset.sum_congr rfl
  intro k _
  exact sineCauchyTerm_eq_scaled hn k

theorem exactSineCheckpointHead_subinterval
    (n blocks : ℕ) (box : ℕ → RatInterval)
    (hcert : ∀ i, i < blocks →
      IsSubinterval (scheduledSineCauchyChunkInterval n i) (box i)) :
    IsSubinterval (exactSineCheckpointHead n blocks)
      (coarseSineCheckpointHead box blocks) := by
  have hprefix : ∀ used, used ≤ blocks →
      IsSubinterval (exactSineCheckpointHead n used)
        (coarseSineCheckpointHead box used) := by
    intro used hused
    induction used with
    | zero => exact ⟨le_rfl, le_rfl⟩
    | succ used ih =>
        rw [exactSineCheckpointHead, coarseSineCheckpointHead]
        change
          (coarseSineCheckpointHead box used).lower + (box used).lower ≤
              (exactSineCheckpointHead n used).lower +
                (scheduledSineCauchyChunkInterval n used).lower ∧
            (exactSineCheckpointHead n used).upper +
                (scheduledSineCauchyChunkInterval n used).upper ≤
              (coarseSineCheckpointHead box used).upper + (box used).upper
        exact ⟨add_le_add (ih (by omega)).1 (hcert used (by omega)).1,
          add_le_add (ih (by omega)).2 (hcert used (by omega)).2⟩
  exact hprefix blocks le_rfl

theorem coarseSineCheckpointHead_contains_production
    {n blocks : ℕ} (hn : n ≠ 0) (box : ℕ → RatInterval)
    (hcert : ∀ i, i < blocks →
      IsSubinterval (scheduledSineCauchyChunkInterval n i) (box i)) :
    (coarseSineCheckpointHead box blocks).Contains
      (∑ k ∈ Finset.range (256 * blocks), sineCauchyTerm n k) := by
  exact contains_of_subinterval
    (exactSineCheckpointHead_subinterval n blocks box hcert)
    (exactSineCheckpointHead_contains_production hn blocks)

/-- Accelerated sine-moment enclosure using compact finite-head checkpoints. -/
def coarseAcceleratedSineSeriesInterval
    (n blocks : ℕ) (box : ℕ → RatInterval) : RatInterval :=
  sinePolarInterval n -
    (coarseSineCheckpointHead box blocks +
      acceleratedCauchyTailInterval n (256 * blocks))

/-- Fully reusable checkpointed enclosure with automatic rational rounding. -/
def roundedAcceleratedSineSeriesInterval
    (n blocks : ℕ) (scale : ℚ) : RatInterval :=
  coarseAcceleratedSineSeriesInterval n blocks
    (roundedSineCauchyChunkBox n scale)

theorem coarseAcceleratedSineSeriesInterval_contains
    {n blocks : ℕ} (hn : n ≠ 0) (hblocks : 0 < blocks)
    (box : ℕ → RatInterval)
    (hcert : ∀ i, i < blocks →
      IsSubinterval (scheduledSineCauchyChunkInterval n i) (box i)) :
    (coarseAcceleratedSineSeriesInterval n blocks box).Contains
      (yoshidaSineMoment n) := by
  rw [yoshidaSineMoment_eq_finiteHead_sub_tail hn (256 * blocks)]
  exact contains_sub (sinePolarInterval_contains n)
    (contains_add
      (coarseSineCheckpointHead_contains_production hn box hcert)
      (acceleratedCauchyTailInterval_contains hn (by omega)))

theorem roundedAcceleratedSineSeriesInterval_contains
    {n blocks : ℕ} (hn : n ≠ 0) (hblocks : 0 < blocks)
    {scale : ℚ} (hscale : 0 < scale) :
    (roundedAcceleratedSineSeriesInterval n blocks scale).Contains
      (yoshidaSineMoment n) := by
  exact coarseAcceleratedSineSeriesInterval_contains hn hblocks _
    (fun i _ ↦ scheduledSineCauchyChunkInterval_sub_rounded n i hscale)

end ArithmeticHodge.Analysis.YoshidaSineCheckpointedHead
