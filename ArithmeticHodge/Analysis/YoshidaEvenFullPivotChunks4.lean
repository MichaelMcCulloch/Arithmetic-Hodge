import ArithmeticHodge.Analysis.YoshidaEvenFullPivotCore
import ArithmeticHodge.Analysis.YoshidaEvenFullPivotPayload3
import ArithmeticHodge.Analysis.YoshidaEvenFullPivotPayload4

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaEvenFullPivotCertificate

/-! # Rounded pivot chunks for stages 40 through 60 -/

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem evenTarget_chunk40_45 :
    DenseLeadingRoundedChunk evenPivotRoundScale 5 155
      evenCheckpoint40 evenCheckpoint45 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem evenTarget_chunk45_50 :
    DenseLeadingRoundedChunk evenPivotRoundScale 5 150
      evenCheckpoint45 evenCheckpoint50 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem evenTarget_chunk50_55 :
    DenseLeadingRoundedChunk evenPivotRoundScale 5 145
      evenCheckpoint50 evenCheckpoint55 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem evenTarget_chunk55_60 :
    DenseLeadingRoundedChunk evenPivotRoundScale 5 140
      evenCheckpoint55 evenCheckpoint60 := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem evenTarget_chunks40_60 :
    DenseLeadingRoundedPositivePivots evenPivotRoundScale evenCheckpoint60 →
      DenseLeadingRoundedPositivePivots evenPivotRoundScale evenCheckpoint40 := by
  intro htail
  apply denseLeadingRoundedPositivePivots_of_chunk
    evenPivotRoundScale 5 155 evenCheckpoint40 evenCheckpoint45
    evenTarget_chunk40_45
  apply denseLeadingRoundedPositivePivots_of_chunk
    evenPivotRoundScale 5 150 evenCheckpoint45 evenCheckpoint50
    evenTarget_chunk45_50
  apply denseLeadingRoundedPositivePivots_of_chunk
    evenPivotRoundScale 5 145 evenCheckpoint50 evenCheckpoint55
    evenTarget_chunk50_55
  apply denseLeadingRoundedPositivePivots_of_chunk
    evenPivotRoundScale 5 140 evenCheckpoint55 evenCheckpoint60
    evenTarget_chunk55_60
  exact htail

end ArithmeticHodge.Analysis.YoshidaEvenFullPivotCertificate
