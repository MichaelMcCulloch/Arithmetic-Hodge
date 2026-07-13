import ArithmeticHodge.Analysis.YoshidaEvenFullPivotCore
import ArithmeticHodge.Analysis.YoshidaEvenFullPivotPayload5
import ArithmeticHodge.Analysis.YoshidaEvenFullPivotPayload6

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaEvenFullPivotCertificate

/-! # Rounded pivot chunks for stages 90 through 200 -/

def evenCheckpoint200 : DenseIntervalMatrix 0 := #v[]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem evenTarget_chunk90_95 :
    DenseLeadingRoundedChunk evenPivotRoundScale 5 105
      evenCheckpoint90 evenCheckpoint95 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem evenTarget_chunk95_100 :
    DenseLeadingRoundedChunk evenPivotRoundScale 5 100
      evenCheckpoint95 evenCheckpoint100 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem evenTarget_chunk100_105 :
    DenseLeadingRoundedChunk evenPivotRoundScale 5 95
      evenCheckpoint100 evenCheckpoint105 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem evenTarget_chunk105_110 :
    DenseLeadingRoundedChunk evenPivotRoundScale 5 90
      evenCheckpoint105 evenCheckpoint110 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem evenTarget_chunk110_115 :
    DenseLeadingRoundedChunk evenPivotRoundScale 5 85
      evenCheckpoint110 evenCheckpoint115 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem evenTarget_chunk115_120 :
    DenseLeadingRoundedChunk evenPivotRoundScale 5 80
      evenCheckpoint115 evenCheckpoint120 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem evenTarget_chunk120_125 :
    DenseLeadingRoundedChunk evenPivotRoundScale 5 75
      evenCheckpoint120 evenCheckpoint125 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem evenTarget_chunk125_130 :
    DenseLeadingRoundedChunk evenPivotRoundScale 5 70
      evenCheckpoint125 evenCheckpoint130 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem evenTarget_chunk130_135 :
    DenseLeadingRoundedChunk evenPivotRoundScale 5 65
      evenCheckpoint130 evenCheckpoint135 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem evenTarget_chunk135_140 :
    DenseLeadingRoundedChunk evenPivotRoundScale 5 60
      evenCheckpoint135 evenCheckpoint140 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem evenTarget_chunk140_145 :
    DenseLeadingRoundedChunk evenPivotRoundScale 5 55
      evenCheckpoint140 evenCheckpoint145 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem evenTarget_chunk145_150 :
    DenseLeadingRoundedChunk evenPivotRoundScale 5 50
      evenCheckpoint145 evenCheckpoint150 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem evenTarget_chunk150_155 :
    DenseLeadingRoundedChunk evenPivotRoundScale 5 45
      evenCheckpoint150 evenCheckpoint155 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem evenTarget_chunk155_160 :
    DenseLeadingRoundedChunk evenPivotRoundScale 5 40
      evenCheckpoint155 evenCheckpoint160 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem evenTarget_chunk160_165 :
    DenseLeadingRoundedChunk evenPivotRoundScale 5 35
      evenCheckpoint160 evenCheckpoint165 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem evenTarget_chunk165_170 :
    DenseLeadingRoundedChunk evenPivotRoundScale 5 30
      evenCheckpoint165 evenCheckpoint170 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem evenTarget_chunk170_175 :
    DenseLeadingRoundedChunk evenPivotRoundScale 5 25
      evenCheckpoint170 evenCheckpoint175 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem evenTarget_chunk175_180 :
    DenseLeadingRoundedChunk evenPivotRoundScale 5 20
      evenCheckpoint175 evenCheckpoint180 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem evenTarget_chunk180_185 :
    DenseLeadingRoundedChunk evenPivotRoundScale 5 15
      evenCheckpoint180 evenCheckpoint185 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem evenTarget_chunk185_190 :
    DenseLeadingRoundedChunk evenPivotRoundScale 5 10
      evenCheckpoint185 evenCheckpoint190 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem evenTarget_chunk190_195 :
    DenseLeadingRoundedChunk evenPivotRoundScale 5 5
      evenCheckpoint190 evenCheckpoint195 := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 1000000000 in
theorem evenTarget_chunk195_200 :
    DenseLeadingRoundedChunk evenPivotRoundScale 5 0
      evenCheckpoint195 evenCheckpoint200 := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem evenTarget_chunks90_200 :
    DenseLeadingRoundedPositivePivots evenPivotRoundScale evenCheckpoint90 := by
  apply denseLeadingRoundedPositivePivots_of_chunk
    evenPivotRoundScale 5 105 evenCheckpoint90 evenCheckpoint95
    evenTarget_chunk90_95
  apply denseLeadingRoundedPositivePivots_of_chunk
    evenPivotRoundScale 5 100 evenCheckpoint95 evenCheckpoint100
    evenTarget_chunk95_100
  apply denseLeadingRoundedPositivePivots_of_chunk
    evenPivotRoundScale 5 95 evenCheckpoint100 evenCheckpoint105
    evenTarget_chunk100_105
  apply denseLeadingRoundedPositivePivots_of_chunk
    evenPivotRoundScale 5 90 evenCheckpoint105 evenCheckpoint110
    evenTarget_chunk105_110
  apply denseLeadingRoundedPositivePivots_of_chunk
    evenPivotRoundScale 5 85 evenCheckpoint110 evenCheckpoint115
    evenTarget_chunk110_115
  apply denseLeadingRoundedPositivePivots_of_chunk
    evenPivotRoundScale 5 80 evenCheckpoint115 evenCheckpoint120
    evenTarget_chunk115_120
  apply denseLeadingRoundedPositivePivots_of_chunk
    evenPivotRoundScale 5 75 evenCheckpoint120 evenCheckpoint125
    evenTarget_chunk120_125
  apply denseLeadingRoundedPositivePivots_of_chunk
    evenPivotRoundScale 5 70 evenCheckpoint125 evenCheckpoint130
    evenTarget_chunk125_130
  apply denseLeadingRoundedPositivePivots_of_chunk
    evenPivotRoundScale 5 65 evenCheckpoint130 evenCheckpoint135
    evenTarget_chunk130_135
  apply denseLeadingRoundedPositivePivots_of_chunk
    evenPivotRoundScale 5 60 evenCheckpoint135 evenCheckpoint140
    evenTarget_chunk135_140
  apply denseLeadingRoundedPositivePivots_of_chunk
    evenPivotRoundScale 5 55 evenCheckpoint140 evenCheckpoint145
    evenTarget_chunk140_145
  apply denseLeadingRoundedPositivePivots_of_chunk
    evenPivotRoundScale 5 50 evenCheckpoint145 evenCheckpoint150
    evenTarget_chunk145_150
  apply denseLeadingRoundedPositivePivots_of_chunk
    evenPivotRoundScale 5 45 evenCheckpoint150 evenCheckpoint155
    evenTarget_chunk150_155
  apply denseLeadingRoundedPositivePivots_of_chunk
    evenPivotRoundScale 5 40 evenCheckpoint155 evenCheckpoint160
    evenTarget_chunk155_160
  apply denseLeadingRoundedPositivePivots_of_chunk
    evenPivotRoundScale 5 35 evenCheckpoint160 evenCheckpoint165
    evenTarget_chunk160_165
  apply denseLeadingRoundedPositivePivots_of_chunk
    evenPivotRoundScale 5 30 evenCheckpoint165 evenCheckpoint170
    evenTarget_chunk165_170
  apply denseLeadingRoundedPositivePivots_of_chunk
    evenPivotRoundScale 5 25 evenCheckpoint170 evenCheckpoint175
    evenTarget_chunk170_175
  apply denseLeadingRoundedPositivePivots_of_chunk
    evenPivotRoundScale 5 20 evenCheckpoint175 evenCheckpoint180
    evenTarget_chunk175_180
  apply denseLeadingRoundedPositivePivots_of_chunk
    evenPivotRoundScale 5 15 evenCheckpoint180 evenCheckpoint185
    evenTarget_chunk180_185
  apply denseLeadingRoundedPositivePivots_of_chunk
    evenPivotRoundScale 5 10 evenCheckpoint185 evenCheckpoint190
    evenTarget_chunk185_190
  apply denseLeadingRoundedPositivePivots_of_chunk
    evenPivotRoundScale 5 5 evenCheckpoint190 evenCheckpoint195
    evenTarget_chunk190_195
  apply denseLeadingRoundedPositivePivots_of_chunk
    evenPivotRoundScale 5 0 evenCheckpoint195 evenCheckpoint200
    evenTarget_chunk195_200
  trivial

end ArithmeticHodge.Analysis.YoshidaEvenFullPivotCertificate
