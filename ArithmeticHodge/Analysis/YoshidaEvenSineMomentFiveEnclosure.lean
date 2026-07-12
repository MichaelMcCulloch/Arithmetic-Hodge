import ArithmeticHodge.Analysis.YoshidaEvenMomentTargets
import ArithmeticHodge.Analysis.YoshidaSineCheckpointedHead

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaEvenSineMomentFiveEnclosure

open YoshidaEvenMomentTargets
open YoshidaOddGramPrefix
open YoshidaSineCheckpointedHead
open YoshidaSineMomentEnclosures

/-!
# Certified enclosure for the fifth even sine moment

Eleven exact 256-term checkpoints cover `k = 0,...,2815`.  Each checkpoint
is rounded outward to the `10^-12` grid before the accelerated analytic tail
starts at `K = 2816`.
-/

private def fiveModeSineChunkBox : ℕ → RatInterval
  | 0 => ⟨1451910551966 / 1000000000000, 1451910552053 / 1000000000000⟩
  | 1 => ⟨44124233036 / 1000000000000, 44124233038 / 1000000000000⟩
  | 2 => ⟨14745436658 / 1000000000000, 14745436659 / 1000000000000⟩
  | 3 => ⟨7376136594 / 1000000000000, 7376136595 / 1000000000000⟩
  | 4 => ⟨4426313845 / 1000000000000, 4426313847 / 1000000000000⟩
  | 5 => ⟨2951032111 / 1000000000000, 2951032112 / 1000000000000⟩
  | 6 => ⟨2107922864 / 1000000000000, 2107922865 / 1000000000000⟩
  | 7 => ⟨1580952632 / 1000000000000, 1580952633 / 1000000000000⟩
  | 8 => ⟨1229630369 / 1000000000000, 1229630370 / 1000000000000⟩
  | 9 => ⟨983701883 / 1000000000000, 983701884 / 1000000000000⟩
  | 10 => ⟨804843951 / 1000000000000, 804843952 / 1000000000000⟩
  | _ => RatInterval.pure 0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem fiveModeSineChunk_kernel_certificate
    {i : ℕ} (hi : i < 11) :
    IsSubinterval (scheduledSineCauchyChunkInterval 5 i)
      (fiveModeSineChunkBox i) := by
  interval_cases i <;> decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem checkpointedSineSeries_2816_sub_evenTarget_five :
    IsSubinterval
      (coarseAcceleratedSineSeriesInterval 5 11 fiveModeSineChunkBox)
      (yoshidaEvenSineTargets 5) := by
  decide +kernel

/-- The actual fifth sine moment inhabits its production even target box. -/
theorem yoshidaEvenSineTarget_five_contains :
    (yoshidaEvenSineTargets 5).Contains (yoshidaSineMoment 5) := by
  exact contains_of_subinterval checkpointedSineSeries_2816_sub_evenTarget_five
    (coarseAcceleratedSineSeriesInterval_contains
      (by norm_num) (by norm_num) fiveModeSineChunkBox
      (fun _ hi ↦ fiveModeSineChunk_kernel_certificate hi))

end ArithmeticHodge.Analysis.YoshidaEvenSineMomentFiveEnclosure
