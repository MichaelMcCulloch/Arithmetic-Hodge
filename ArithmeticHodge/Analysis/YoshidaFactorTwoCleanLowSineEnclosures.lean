import ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationSinLowEnclosures
import ArithmeticHodge.Analysis.YoshidaSineCheckpointStructuralWidth
import ArithmeticHodge.Analysis.YoshidaSineStructuralWidth

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoCleanLowSineEnclosures

noncomputable section

open RatInterval
open YoshidaFactorTwoPhasePerturbationSinLowEnclosures
open YoshidaOddGramPrefix
open YoshidaSineCheckpointStructuralWidth
open YoshidaSineMomentEnclosures
open YoshidaSineStructuralWidth

/-!
# Structural clean sine-moment enclosures through mode 200

Every positive mode uses the same checkpointed Cauchy representation.  A
pointwise interval-width estimate is summed by one telescoping majorant, and
the ninth-order tail is controlled from the symbolic cutoff ratio.  Thus the
proof below is uniform in the mode and does not dispatch over finite cases.
-/

/-- Number of rounded 256-term checkpoints used for clean sine mode `n`. -/
def cleanLowSineBlocks (n : ℕ) : ℕ :=
  n / 4 + 2

/-- The common outward-rounding grid for each 256-term checkpoint. -/
def cleanLowSineRoundingScale : ℚ :=
  1000000000000000000

private theorem cleanLowSineBlocks_pos (n : ℕ) :
    0 < cleanLowSineBlocks n := by
  unfold cleanLowSineBlocks
  omega

private theorem cleanLowSineBlocks_le
    {n : ℕ} (hn200 : n ≤ 200) :
    cleanLowSineBlocks n ≤ 52 := by
  unfold cleanLowSineBlocks
  omega

private theorem cleanLowSine_schedule
    {n : ℕ} (hn200 : n ≤ 200) :
    300 * n ≤ 7 * (256 * cleanLowSineBlocks n) := by
  unfold cleanLowSineBlocks
  omega

private theorem cleanLowSineRoundingScale_pos :
    (0 : ℚ) < cleanLowSineRoundingScale := by
  norm_num [cleanLowSineRoundingScale]

/-- The zero-frequency Yoshida sine moment vanishes exactly. -/
@[simp] theorem yoshidaSineMoment_zero :
    yoshidaSineMoment 0 = 0 := by
  simp [yoshidaSineMoment, yoshidaSineMomentIntegrand, yoshidaKappa]

/-- One uniform checkpoint target for every clean sine mode through `200`.
Mode zero remains the exact point interval. -/
def yoshidaFactorTwoCleanLowSineTarget (n : ℕ) : RatInterval :=
  if n = 0 then pure 0
  else
    higherRoundedSineSeriesInterval n (cleanLowSineBlocks n)
      cleanLowSineRoundingScale

/-- Every target contains its exact analytic Yoshida sine moment. -/
theorem yoshidaFactorTwoCleanLowSineTarget_contains
    {n : ℕ} (_hn200 : n ≤ 200) :
    (yoshidaFactorTwoCleanLowSineTarget n).Contains
      (yoshidaSineMoment n) := by
  by_cases hn : n = 0
  · subst n
    simpa [yoshidaFactorTwoCleanLowSineTarget] using contains_pure (0 : ℚ)
  · simp only [yoshidaFactorTwoCleanLowSineTarget, hn, if_false]
    exact higherRoundedSineSeriesInterval_contains hn
      (cleanLowSineBlocks_pos n) cleanLowSineRoundingScale_pos

private theorem yoshidaFactorTwoCleanLowSineTarget_width_le_of_pos
    {n : ℕ} (hn : 1 ≤ n) (hn200 : n ≤ 200) :
    width (yoshidaFactorTwoCleanLowSineTarget n) ≤
      (1 / 1000000000 : ℚ) := by
  have hn0 : n ≠ 0 := by omega
  simp only [yoshidaFactorTwoCleanLowSineTarget, hn0, if_false]
  rw [higherRoundedSineSeriesInterval, width_sub]
  have hpolar := sinePolarInterval_width_le hn
  have hhead := exactSineCheckpointHead_width_le hn (cleanLowSineBlocks n)
  have hKmin : 256 ≤ 256 * cleanLowSineBlocks n := by
    have := cleanLowSineBlocks_pos n
    omega
  have htail := higherSineCauchyTailInterval_width_le hn
    hKmin (cleanLowSine_schedule hn200)
  have hseries := higherRoundedSineCauchySeriesInterval_width_le
    n (cleanLowSineBlocks n) cleanLowSineRoundingScale_pos hhead htail
  have hblocksQ : ((cleanLowSineBlocks n : ℕ) : ℚ) ≤ 52 := by
    exact_mod_cast cleanLowSineBlocks_le hn200
  have hround :
      ((cleanLowSineBlocks n : ℕ) : ℚ) *
          (2 / cleanLowSineRoundingScale) ≤
        52 * (2 / cleanLowSineRoundingScale) := by
    exact mul_le_mul_of_nonneg_right hblocksQ (by
      exact div_nonneg (by norm_num) cleanLowSineRoundingScale_pos.le)
  calc
    width (sinePolarInterval n) +
          width (higherRoundedSineCauchySeriesInterval n
            (cleanLowSineBlocks n) cleanLowSineRoundingScale) ≤
        (1 / 100000000000 : ℚ) +
          ((1 / 4500000000 : ℚ) +
            ((cleanLowSineBlocks n : ℕ) : ℚ) *
              (2 / cleanLowSineRoundingScale) +
            (1 / 4000000000 : ℚ)) :=
      add_le_add hpolar hseries
    _ ≤ (1 / 100000000000 : ℚ) +
          ((1 / 4500000000 : ℚ) +
            52 * (2 / cleanLowSineRoundingScale) +
            (1 / 4000000000 : ℚ)) := by
      linarith
    _ ≤ (1 / 1000000000 : ℚ) := by
      norm_num [cleanLowSineRoundingScale]

/-- A single structural width proof covers all modes `0, ..., 200`. -/
theorem yoshidaFactorTwoCleanLowSineTarget_width_le
    {n : ℕ} (hn200 : n ≤ 200) :
    width (yoshidaFactorTwoCleanLowSineTarget n) ≤
      (1 / 1000000000 : ℚ) := by
  by_cases hn : n = 0
  · subst n
    norm_num [yoshidaFactorTwoCleanLowSineTarget, width, RatInterval.pure]
  · exact yoshidaFactorTwoCleanLowSineTarget_width_le_of_pos
      (Nat.one_le_iff_ne_zero.mpr hn) hn200

/-- Complete structural enclosure package through mode `200`. -/
def YoshidaFactorTwoCleanLowSineTargetEnclosures : Prop :=
  ∀ n, n ≤ 200 →
    (yoshidaFactorTwoCleanLowSineTarget n).Contains
        (yoshidaSineMoment n) ∧
      width (yoshidaFactorTwoCleanLowSineTarget n) ≤
        (1 / 1000000000 : ℚ)

theorem yoshidaFactorTwoCleanLowSineTargetEnclosures :
    YoshidaFactorTwoCleanLowSineTargetEnclosures := by
  intro n hn200
  exact ⟨yoshidaFactorTwoCleanLowSineTarget_contains hn200,
    yoshidaFactorTwoCleanLowSineTarget_width_le hn200⟩

/-! ## Public clean-sine selector -/

/-- The public clean-sine target is the uniform checkpoint target. -/
def yoshidaFactorTwoCleanSineTarget (n : ℕ) : RatInterval :=
  yoshidaFactorTwoCleanLowSineTarget n

theorem yoshidaFactorTwoCleanSineTarget_contains
    {n : ℕ} (hn200 : n ≤ 200) :
    (yoshidaFactorTwoCleanSineTarget n).Contains
      (yoshidaSineMoment n) :=
  yoshidaFactorTwoCleanLowSineTarget_contains hn200

theorem yoshidaFactorTwoCleanSineTarget_width_le
    {n : ℕ} (hn200 : n ≤ 200) :
    width (yoshidaFactorTwoCleanSineTarget n) ≤
      (1 / 1000000000 : ℚ) :=
  yoshidaFactorTwoCleanLowSineTarget_width_le hn200

def YoshidaFactorTwoCleanSineTargetEnclosures : Prop :=
  ∀ n, n ≤ 200 →
    (yoshidaFactorTwoCleanSineTarget n).Contains
        (yoshidaSineMoment n) ∧
      width (yoshidaFactorTwoCleanSineTarget n) ≤
        (1 / 1000000000 : ℚ)

theorem yoshidaFactorTwoCleanSineTargetEnclosures :
    YoshidaFactorTwoCleanSineTargetEnclosures := by
  intro n hn200
  exact ⟨yoshidaFactorTwoCleanSineTarget_contains hn200,
    yoshidaFactorTwoCleanSineTarget_width_le hn200⟩

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoCleanLowSineEnclosures
