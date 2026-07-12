import ArithmeticHodge.Analysis.YoshidaEvenMomentTargets
import ArithmeticHodge.Analysis.YoshidaSineCheckpointedHead

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaEvenSineMomentThreeEnclosure

open YoshidaEvenMomentTargets
open YoshidaOddGramPrefix
open YoshidaSineCheckpointedHead
open YoshidaSineMomentEnclosures

/-!
# Certified enclosure for the third even sine moment

Five exact 256-term checkpoints cover the finite Cauchy head through
`k = 1279`.  Outward-rounded boxes at scale `10^12` keep the accumulated head
compact, and the accelerated analytic tail starts at `K = 1280`.
-/

private def threeModeSineChunkBox : ℕ → RatInterval
  | 0 => ⟨1467019294412 / 1000000000000, 1467019294497 / 1000000000000⟩
  | 1 => ⟨26551927139 / 1000000000000, 26551927141 / 1000000000000⟩
  | 2 => ⟨8855070015 / 1000000000000, 8855070016 / 1000000000000⟩
  | 3 => ⟨4427583583 / 1000000000000, 4427583584 / 1000000000000⟩
  | 4 => ⟨2656465572 / 1000000000000, 2656465573 / 1000000000000⟩
  | _ => RatInterval.pure 0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem threeModeSineChunk_kernel_certificate
    {i : ℕ} (hi : i < 5) :
    IsSubinterval (scheduledSineCauchyChunkInterval 3 i)
      (threeModeSineChunkBox i) := by
  interval_cases i <;> decide +kernel

theorem checkpointedSineSeries_1280_sub_evenTarget_three :
    IsSubinterval
      (coarseAcceleratedSineSeriesInterval 3 5 threeModeSineChunkBox)
      (yoshidaEvenSineTargets 3) := by
  decide +kernel

/-- The actual third sine moment inhabits its production even target box. -/
theorem yoshidaEvenSineTarget_three_contains :
    (yoshidaEvenSineTargets 3).Contains (yoshidaSineMoment 3) := by
  exact contains_of_subinterval checkpointedSineSeries_1280_sub_evenTarget_three
    (coarseAcceleratedSineSeriesInterval_contains
      (by norm_num) (by norm_num) threeModeSineChunkBox
      (fun _ hi ↦ threeModeSineChunk_kernel_certificate hi))

end ArithmeticHodge.Analysis.YoshidaEvenSineMomentThreeEnclosure
