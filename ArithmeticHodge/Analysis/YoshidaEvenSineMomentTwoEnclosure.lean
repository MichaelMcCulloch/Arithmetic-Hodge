import ArithmeticHodge.Analysis.YoshidaEvenMomentTargets
import ArithmeticHodge.Analysis.YoshidaSineCheckpointedHead

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaEvenSineMomentTwoEnclosure

open YoshidaEvenMomentTargets
open YoshidaOddGramPrefix
open YoshidaSineCheckpointedHead
open YoshidaSineMomentEnclosures

/-!
# Certified enclosure for the second even sine moment

Sixteen exact 256-term checkpoints cover the finite Cauchy head through
`k = 4095`.  Outward-rounded boxes at scale `10^12` keep the accumulated head
compact, and the accelerated analytic tail starts at `K = 4096`.
-/

private def twoModeSineChunkBox : ℕ → RatInterval
  | 0 => ⟨1459887184140 / 1000000000000, 1459887184224 / 1000000000000⟩
  | 1 => ⟨17717477627 / 1000000000000, 17717477628 / 1000000000000⟩
  | 2 => ⟨5905008663 / 1000000000000, 5905008665 / 1000000000000⟩
  | 3 => ⟨2952118790 / 1000000000000, 2952118791 / 1000000000000⟩
  | 4 => ⟨1771118193 / 1000000000000, 1771118194 / 1000000000000⟩
  | 5 => ⟨1180674805 / 1000000000000, 1180674806 / 1000000000000⟩
  | 6 => ⟨843302376 / 1000000000000, 843302377 / 1000000000000⟩
  | 7 => ⟨632455845 / 1000000000000, 632455846 / 1000000000000⟩
  | 8 => ⟨491897332 / 1000000000000, 491897333 / 1000000000000⟩
  | 9 => ⟨393509644 / 1000000000000, 393509645 / 1000000000000⟩
  | 10 => ⟨321956907 / 1000000000000, 321956908 / 1000000000000⟩
  | 11 => ⟨268293569 / 1000000000000, 268293570 / 1000000000000⟩
  | 12 => ⟨227014869 / 1000000000000, 227014870 / 1000000000000⟩
  | 13 => ⟨194582136 / 1000000000000, 194582137 / 1000000000000⟩
  | 14 => ⟨168636318 / 1000000000000, 168636319 / 1000000000000⟩
  | 15 => ⟨147555602 / 1000000000000, 147555603 / 1000000000000⟩
  | _ => RatInterval.pure 0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem twoModeSineChunk_kernel_certificate
    {i : ℕ} (hi : i < 16) :
    IsSubinterval (scheduledSineCauchyChunkInterval 2 i)
      (twoModeSineChunkBox i) := by
  interval_cases i <;> decide +kernel

theorem checkpointedSineSeries_4096_sub_evenTarget_two :
    IsSubinterval
      (coarseAcceleratedSineSeriesInterval 2 16 twoModeSineChunkBox)
      (yoshidaEvenSineTargets 2) := by
  decide +kernel

/-- The actual second sine moment inhabits its production even target box. -/
theorem yoshidaEvenSineTarget_two_contains :
    (yoshidaEvenSineTargets 2).Contains (yoshidaSineMoment 2) := by
  exact contains_of_subinterval checkpointedSineSeries_4096_sub_evenTarget_two
    (coarseAcceleratedSineSeriesInterval_contains
      (by norm_num) (by norm_num) twoModeSineChunkBox
      (fun _ hi ↦ twoModeSineChunk_kernel_certificate hi))

end ArithmeticHodge.Analysis.YoshidaEvenSineMomentTwoEnclosure
