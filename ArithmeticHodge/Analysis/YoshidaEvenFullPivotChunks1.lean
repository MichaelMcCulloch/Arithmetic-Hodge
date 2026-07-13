import ArithmeticHodge.Analysis.YoshidaEvenFullPivotCore
import ArithmeticHodge.Analysis.YoshidaEvenFullPivotPayload1

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaEvenFullPivotCertificate

/-! # Rounded pivot chunks for stages 0 through 10 -/

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem evenTarget_chunk0_5 :
    DenseLeadingRoundedChunk evenPivotRoundScale 5 195
      evenTargetInitialDense evenCheckpoint5 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem evenTarget_chunk5_10 :
    DenseLeadingRoundedChunk evenPivotRoundScale 5 190
      evenCheckpoint5 evenCheckpoint10 := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem evenTarget_chunks0_10 :
    DenseLeadingRoundedPositivePivots evenPivotRoundScale evenCheckpoint10 →
      DenseLeadingRoundedPositivePivots evenPivotRoundScale
        evenTargetInitialDense := by
  intro htail
  apply denseLeadingRoundedPositivePivots_of_chunk
    evenPivotRoundScale 5 195 evenTargetInitialDense evenCheckpoint5
    evenTarget_chunk0_5
  apply denseLeadingRoundedPositivePivots_of_chunk
    evenPivotRoundScale 5 190 evenCheckpoint5 evenCheckpoint10
    evenTarget_chunk5_10
  exact htail

end ArithmeticHodge.Analysis.YoshidaEvenFullPivotCertificate
