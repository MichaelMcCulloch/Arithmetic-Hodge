import ArithmeticHodge.Analysis.YoshidaEvenMomentTargets
import ArithmeticHodge.Analysis.YoshidaSineCheckpointedHead

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaEvenSineMomentFourEnclosure

open YoshidaEvenMomentTargets
open YoshidaOddGramPrefix
open YoshidaSineCheckpointedHead
open YoshidaSineMomentEnclosures

/-!
# Certified enclosure for the fourth even sine moment

Seven exact 256-term checkpoints cover the finite Cauchy head through
`k = 1791`.  Outward-rounded boxes at scale `10^12` keep the accumulated head
compact, and the accelerated analytic tail starts at `K = 1792`.
-/

private def fourModeSineChunkBox : ℕ → RatInterval
  | 0 => ⟨1461937354844 / 1000000000000, 1461937354931 / 1000000000000⟩
  | 1 => ⟨35357342537 / 1000000000000, 35357342539 / 1000000000000⟩
  | 2 => ⟨11802202963 / 1000000000000, 11802202965 / 1000000000000⟩
  | 3 => ⟨5902335220 / 1000000000000, 5902335221 / 1000000000000⟩
  | 4 => ⟨3541558967 / 1000000000000, 3541558968 / 1000000000000⟩
  | 5 => ⟨2361050198 / 1000000000000, 2361050199 / 1000000000000⟩
  | 6 => ⟨1686452478 / 1000000000000, 1686452480 / 1000000000000⟩
  | _ => RatInterval.pure 0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
private theorem fourModeSineChunk_kernel_certificate
    {i : ℕ} (hi : i < 7) :
    IsSubinterval (scheduledSineCauchyChunkInterval 4 i)
      (fourModeSineChunkBox i) := by
  interval_cases i <;> decide +kernel

theorem checkpointedSineSeries_1792_sub_evenTarget_four :
    IsSubinterval
      (coarseAcceleratedSineSeriesInterval 4 7 fourModeSineChunkBox)
      (yoshidaEvenSineTargets 4) := by
  decide +kernel

/-- The actual fourth sine moment inhabits its production even target box. -/
theorem yoshidaEvenSineTarget_four_contains :
    (yoshidaEvenSineTargets 4).Contains (yoshidaSineMoment 4) := by
  exact contains_of_subinterval checkpointedSineSeries_1792_sub_evenTarget_four
    (coarseAcceleratedSineSeriesInterval_contains
      (by norm_num) (by norm_num) fourModeSineChunkBox
      (fun _ hi ↦ fourModeSineChunk_kernel_certificate hi))

end ArithmeticHodge.Analysis.YoshidaEvenSineMomentFourEnclosure
