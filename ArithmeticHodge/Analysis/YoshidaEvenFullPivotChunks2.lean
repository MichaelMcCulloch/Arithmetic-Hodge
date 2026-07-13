import ArithmeticHodge.Analysis.YoshidaEvenFullPivotCore
import ArithmeticHodge.Analysis.YoshidaEvenFullPivotPayload1
import ArithmeticHodge.Analysis.YoshidaEvenFullPivotPayload2

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaEvenFullPivotCertificate

/-! # Rounded pivot chunks for stages 10 through 25 -/

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem evenTarget_chunk10_15 :
    DenseLeadingRoundedChunk evenPivotRoundScale 5 185
      evenCheckpoint10 evenCheckpoint15 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem evenTarget_chunk15_20 :
    DenseLeadingRoundedChunk evenPivotRoundScale 5 180
      evenCheckpoint15 evenCheckpoint20 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem evenTarget_chunk20_25 :
    DenseLeadingRoundedChunk evenPivotRoundScale 5 175
      evenCheckpoint20 evenCheckpoint25 := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem evenTarget_chunks10_25 :
    DenseLeadingRoundedPositivePivots evenPivotRoundScale evenCheckpoint25 →
      DenseLeadingRoundedPositivePivots evenPivotRoundScale evenCheckpoint10 := by
  intro htail
  apply denseLeadingRoundedPositivePivots_of_chunk
    evenPivotRoundScale 5 185 evenCheckpoint10 evenCheckpoint15
    evenTarget_chunk10_15
  apply denseLeadingRoundedPositivePivots_of_chunk
    evenPivotRoundScale 5 180 evenCheckpoint15 evenCheckpoint20
    evenTarget_chunk15_20
  apply denseLeadingRoundedPositivePivots_of_chunk
    evenPivotRoundScale 5 175 evenCheckpoint20 evenCheckpoint25
    evenTarget_chunk20_25
  exact htail

end ArithmeticHodge.Analysis.YoshidaEvenFullPivotCertificate
