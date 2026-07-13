import ArithmeticHodge.Analysis.YoshidaEvenFullPivotCore
import ArithmeticHodge.Analysis.YoshidaEvenFullPivotPayload2
import ArithmeticHodge.Analysis.YoshidaEvenFullPivotPayload3

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaEvenFullPivotCertificate

/-! # Rounded pivot chunks for stages 25 through 40 -/

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem evenTarget_chunk25_30 :
    DenseLeadingRoundedChunk evenPivotRoundScale 5 170
      evenCheckpoint25 evenCheckpoint30 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem evenTarget_chunk30_35 :
    DenseLeadingRoundedChunk evenPivotRoundScale 5 165
      evenCheckpoint30 evenCheckpoint35 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem evenTarget_chunk35_40 :
    DenseLeadingRoundedChunk evenPivotRoundScale 5 160
      evenCheckpoint35 evenCheckpoint40 := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem evenTarget_chunks25_40 :
    DenseLeadingRoundedPositivePivots evenPivotRoundScale evenCheckpoint40 →
      DenseLeadingRoundedPositivePivots evenPivotRoundScale evenCheckpoint25 := by
  intro htail
  apply denseLeadingRoundedPositivePivots_of_chunk
    evenPivotRoundScale 5 170 evenCheckpoint25 evenCheckpoint30
    evenTarget_chunk25_30
  apply denseLeadingRoundedPositivePivots_of_chunk
    evenPivotRoundScale 5 165 evenCheckpoint30 evenCheckpoint35
    evenTarget_chunk30_35
  apply denseLeadingRoundedPositivePivots_of_chunk
    evenPivotRoundScale 5 160 evenCheckpoint35 evenCheckpoint40
    evenTarget_chunk35_40
  exact htail

end ArithmeticHodge.Analysis.YoshidaEvenFullPivotCertificate
