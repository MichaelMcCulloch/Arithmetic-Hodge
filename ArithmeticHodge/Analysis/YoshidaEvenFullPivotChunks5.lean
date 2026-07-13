import ArithmeticHodge.Analysis.YoshidaEvenFullPivotCore
import ArithmeticHodge.Analysis.YoshidaEvenFullPivotPayload4
import ArithmeticHodge.Analysis.YoshidaEvenFullPivotPayload5

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaEvenFullPivotCertificate

/-! # Rounded pivot chunks for stages 60 through 90 -/

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem evenTarget_chunk60_65 :
    DenseLeadingRoundedChunk evenPivotRoundScale 5 135
      evenCheckpoint60 evenCheckpoint65 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem evenTarget_chunk65_70 :
    DenseLeadingRoundedChunk evenPivotRoundScale 5 130
      evenCheckpoint65 evenCheckpoint70 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem evenTarget_chunk70_75 :
    DenseLeadingRoundedChunk evenPivotRoundScale 5 125
      evenCheckpoint70 evenCheckpoint75 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem evenTarget_chunk75_80 :
    DenseLeadingRoundedChunk evenPivotRoundScale 5 120
      evenCheckpoint75 evenCheckpoint80 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem evenTarget_chunk80_85 :
    DenseLeadingRoundedChunk evenPivotRoundScale 5 115
      evenCheckpoint80 evenCheckpoint85 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem evenTarget_chunk85_90 :
    DenseLeadingRoundedChunk evenPivotRoundScale 5 110
      evenCheckpoint85 evenCheckpoint90 := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem evenTarget_chunks60_90 :
    DenseLeadingRoundedPositivePivots evenPivotRoundScale evenCheckpoint90 →
      DenseLeadingRoundedPositivePivots evenPivotRoundScale evenCheckpoint60 := by
  intro htail
  apply denseLeadingRoundedPositivePivots_of_chunk
    evenPivotRoundScale 5 135 evenCheckpoint60 evenCheckpoint65
    evenTarget_chunk60_65
  apply denseLeadingRoundedPositivePivots_of_chunk
    evenPivotRoundScale 5 130 evenCheckpoint65 evenCheckpoint70
    evenTarget_chunk65_70
  apply denseLeadingRoundedPositivePivots_of_chunk
    evenPivotRoundScale 5 125 evenCheckpoint70 evenCheckpoint75
    evenTarget_chunk70_75
  apply denseLeadingRoundedPositivePivots_of_chunk
    evenPivotRoundScale 5 120 evenCheckpoint75 evenCheckpoint80
    evenTarget_chunk75_80
  apply denseLeadingRoundedPositivePivots_of_chunk
    evenPivotRoundScale 5 115 evenCheckpoint80 evenCheckpoint85
    evenTarget_chunk80_85
  apply denseLeadingRoundedPositivePivots_of_chunk
    evenPivotRoundScale 5 110 evenCheckpoint85 evenCheckpoint90
    evenTarget_chunk85_90
  exact htail

end ArithmeticHodge.Analysis.YoshidaEvenFullPivotCertificate
