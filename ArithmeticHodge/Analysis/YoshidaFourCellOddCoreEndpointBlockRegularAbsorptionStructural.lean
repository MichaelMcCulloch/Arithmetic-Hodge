import ArithmeticHodge.Analysis.YoshidaFourCellOddCoreBlockPiconeStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddCoreOffStripRegularAbsorptionStructural

set_option autoImplicit false

open Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddCoreEndpointBlockRegularAbsorptionStructural

noncomputable section

open YoshidaFourCellOddCoreBlockPiconeStructural
open YoshidaFourCellOddCoreGroundStatePiconeStructural
open YoshidaFourCellOddCoreOffStripRegularAbsorptionStructural
open YoshidaFourCellParityOperatorStructural

/-!
# Endpoint-block absorption of the folded regular cross

The affine endpoint-strip pullback has Jacobian `1 / 25`.  After pairing the
two physical strip points over each normalized coordinate, the signed folded
regular density has four cross terms.  Each term is absorbed by the reflected
plus-square with the same pair of physical points.  The adverse strip-odd raw
block has already cancelled exactly, leaving the independent nonnegative
strip-even difference square.
-/

/-! ## Physical strip points and pulled-back regular coefficients -/

def endpointStripPhysicalPlusPoint (z : ℝ) : ℝ :=
  4 / 5 + z / 5

def endpointStripPhysicalMinusPoint (z : ℝ) : ℝ :=
  4 / 5 - z / 5

def endpointStripPulledBackFoldedRegularCoefficient (x y : ℝ) : ℝ :=
  (1 / 25 : ℝ) *
    (fourCellOperatorHalfWidth *
      fourCellOddFoldedRegularDifferenceKernel x y)

def endpointStripFoldedRegularPPCoefficient (z s : ℝ) : ℝ :=
  endpointStripPulledBackFoldedRegularCoefficient
    (endpointStripPhysicalPlusPoint z)
    (endpointStripPhysicalPlusPoint s)

def endpointStripFoldedRegularMMCoefficient (z s : ℝ) : ℝ :=
  endpointStripPulledBackFoldedRegularCoefficient
    (endpointStripPhysicalMinusPoint z)
    (endpointStripPhysicalMinusPoint s)

def endpointStripFoldedRegularPMCoefficient (z s : ℝ) : ℝ :=
  endpointStripPulledBackFoldedRegularCoefficient
    (endpointStripPhysicalPlusPoint z)
    (endpointStripPhysicalMinusPoint s)

def endpointStripFoldedRegularMPCoefficient (z s : ℝ) : ℝ :=
  endpointStripPulledBackFoldedRegularCoefficient
    (endpointStripPhysicalMinusPoint z)
    (endpointStripPhysicalPlusPoint s)

/-- The four physical folded-regular crosses after the affine endpoint-strip
pullback.  The factor `1 / 25` is contained in each coefficient. -/
def endpointStripFoldedRegularCrossDensity
    (z s wPZ wMZ wPS wMS : ℝ) : ℝ :=
  -2 * endpointStripFoldedRegularPPCoefficient z s * wPZ * wPS -
    2 * endpointStripFoldedRegularMMCoefficient z s * wMZ * wMS -
    2 * endpointStripFoldedRegularPMCoefficient z s * wPZ * wMS -
    2 * endpointStripFoldedRegularMPCoefficient z s * wMZ * wPS

/-- Expanded form displaying the common folded-regular coefficient and the
affine Jacobian `1 / 25`. -/
theorem endpointStripFoldedRegularCrossDensity_eq_scaled_kernel_sum
    (z s wPZ wMZ wPS wMS : ℝ) :
    endpointStripFoldedRegularCrossDensity z s wPZ wMZ wPS wMS =
      -(2 * fourCellOperatorHalfWidth / 25) *
        (fourCellOddFoldedRegularDifferenceKernel
              (endpointStripPhysicalPlusPoint z)
              (endpointStripPhysicalPlusPoint s) * wPZ * wPS +
          fourCellOddFoldedRegularDifferenceKernel
              (endpointStripPhysicalMinusPoint z)
              (endpointStripPhysicalMinusPoint s) * wMZ * wMS +
          fourCellOddFoldedRegularDifferenceKernel
              (endpointStripPhysicalPlusPoint z)
              (endpointStripPhysicalMinusPoint s) * wPZ * wMS +
          fourCellOddFoldedRegularDifferenceKernel
              (endpointStripPhysicalMinusPoint z)
              (endpointStripPhysicalPlusPoint s) * wMZ * wPS) := by
  unfold endpointStripFoldedRegularCrossDensity
    endpointStripFoldedRegularPPCoefficient
    endpointStripFoldedRegularMMCoefficient
    endpointStripFoldedRegularPMCoefficient
    endpointStripFoldedRegularMPCoefficient
    endpointStripPulledBackFoldedRegularCoefficient
  ring

theorem endpointStripPhysicalPoints_mem_Ioc
    {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    0 < endpointStripPhysicalPlusPoint z ∧
      endpointStripPhysicalPlusPoint z ≤ 1 ∧
      0 < endpointStripPhysicalMinusPoint z ∧
      endpointStripPhysicalMinusPoint z ≤ 1 := by
  unfold endpointStripPhysicalPlusPoint endpointStripPhysicalMinusPoint
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

private theorem one_div_ten_mul_eq_pulledBackReflectedWeight (u : ℝ) :
    1 / (10 * u) =
      (1 / 25 : ℝ) * (1 / (2 * (u / 5))) := by
  by_cases hu : u = 0
  · simp [hu]
  · field_simp [hu]
    norm_num

theorem stripReflectedPPReserveWeight_eq_pulledBack
    (z s : ℝ) :
    stripReflectedPPReserveWeight z s =
      (1 / 25 : ℝ) * positiveHalfReflectedReserveWeight
        (endpointStripPhysicalPlusPoint z)
        (endpointStripPhysicalPlusPoint s) := by
  unfold stripReflectedPPReserveWeight positiveHalfReflectedReserveWeight
    endpointStripPhysicalPlusPoint
  rw [show (4 / 5 + z / 5) + (4 / 5 + s / 5) =
    (8 + z + s) / 5 by ring]
  exact one_div_ten_mul_eq_pulledBackReflectedWeight (8 + z + s)

theorem stripReflectedMMReserveWeight_eq_pulledBack
    (z s : ℝ) :
    stripReflectedMMReserveWeight z s =
      (1 / 25 : ℝ) * positiveHalfReflectedReserveWeight
        (endpointStripPhysicalMinusPoint z)
        (endpointStripPhysicalMinusPoint s) := by
  unfold stripReflectedMMReserveWeight positiveHalfReflectedReserveWeight
    endpointStripPhysicalMinusPoint
  rw [show (4 / 5 - z / 5) + (4 / 5 - s / 5) =
    (8 - z - s) / 5 by ring]
  exact one_div_ten_mul_eq_pulledBackReflectedWeight (8 - z - s)

theorem stripReflectedPMReserveWeight_eq_pulledBack
    (z s : ℝ) :
    stripReflectedPMReserveWeight z s =
      (1 / 25 : ℝ) * positiveHalfReflectedReserveWeight
        (endpointStripPhysicalPlusPoint z)
        (endpointStripPhysicalMinusPoint s) := by
  unfold stripReflectedPMReserveWeight positiveHalfReflectedReserveWeight
    endpointStripPhysicalPlusPoint endpointStripPhysicalMinusPoint
  rw [show (4 / 5 + z / 5) + (4 / 5 - s / 5) =
    (8 + z - s) / 5 by ring]
  exact one_div_ten_mul_eq_pulledBackReflectedWeight (8 + z - s)

theorem stripReflectedMPReserveWeight_eq_pulledBack
    (z s : ℝ) :
    stripReflectedMPReserveWeight z s =
      (1 / 25 : ℝ) * positiveHalfReflectedReserveWeight
        (endpointStripPhysicalMinusPoint z)
        (endpointStripPhysicalPlusPoint s) := by
  unfold stripReflectedMPReserveWeight positiveHalfReflectedReserveWeight
    endpointStripPhysicalPlusPoint endpointStripPhysicalMinusPoint
  rw [show (4 / 5 - z / 5) + (4 / 5 + s / 5) =
    (8 - z + s) / 5 by ring]
  exact one_div_ten_mul_eq_pulledBackReflectedWeight (8 - z + s)

/-! ## One-channel structural factorization -/

def endpointStripReflectedRegularChannelFactor
    (k c u v : ℝ) : ℝ :=
  (c / 2) * (u - v) ^ 2 + (k - c / 2) * (u + v) ^ 2

theorem reflectedPlusSquare_sub_regularCross_eq_factor
    (k c u v : ℝ) :
    k * (u + v) ^ 2 - 2 * c * u * v =
      endpointStripReflectedRegularChannelFactor k c u v := by
  unfold endpointStripReflectedRegularChannelFactor
  ring

theorem endpointStripReflectedRegularChannelFactor_nonneg
    {k c u v : ℝ} (hc : 0 ≤ c) (hcap : c ≤ 2 * k) :
    0 ≤ endpointStripReflectedRegularChannelFactor k c u v := by
  unfold endpointStripReflectedRegularChannelFactor
  have hk : 0 ≤ k - c / 2 := by linarith
  positivity

theorem nineteenTwentieths_mul_reflectedPlusSquare_le_channelFactor
    {k c u v : ℝ} (hk : 0 ≤ k) (hc : 0 ≤ c) (hcap : c ≤ k / 10) :
    (19 / 20 : ℝ) * (k * (u + v) ^ 2) ≤
      endpointStripReflectedRegularChannelFactor k c u v := by
  have hretained := nineteenTwentieths_mul_twoChannelSquares_le_sub_cross
    (kSub := (0 : ℝ)) (kAdd := k) (c := c)
    (wX := u) (wY := v) (by norm_num) hk hc hcap
  calc
    (19 / 20 : ℝ) * (k * (u + v) ^ 2) ≤
        k * (u + v) ^ 2 - 2 * c * u * v := by
      simpa using hretained
    _ = endpointStripReflectedRegularChannelFactor k c u v :=
      reflectedPlusSquare_sub_regularCross_eq_factor k c u v

theorem endpointStripPulledBackFoldedRegularCoefficient_nonneg
    {x y : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    (hy : 0 < y) (hy1 : y ≤ 1) :
    0 ≤ endpointStripPulledBackFoldedRegularCoefficient x y := by
  have hkernel := fourCellOddFoldedRegularDifferenceKernel_nonneg
    hx.le hx1 hy.le hy1
  have hwidth : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  unfold endpointStripPulledBackFoldedRegularCoefficient
  positivity

theorem endpointStripPulledBackFoldedRegularCoefficient_le_two_reflected
    {x y : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    (hy : 0 < y) (hy1 : y ≤ 1) :
    endpointStripPulledBackFoldedRegularCoefficient x y ≤
      2 * ((1 / 25 : ℝ) * positiveHalfReflectedReserveWeight x y) := by
  have hcap :=
    fourCellOperatorHalfWidth_mul_foldedRegularDifferenceKernel_le_two_reflected
      hx hx1 hy hy1
  unfold endpointStripPulledBackFoldedRegularCoefficient
  nlinarith

theorem endpointStripPulledBackFoldedRegularCoefficient_le_tenth_reflected
    {x y : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    (hy : 0 < y) (hy1 : y ≤ 1) :
    endpointStripPulledBackFoldedRegularCoefficient x y ≤
      ((1 / 25 : ℝ) * positiveHalfReflectedReserveWeight x y) / 10 := by
  have hcap :=
    fourCellOperatorHalfWidth_mul_foldedRegularDifferenceKernel_le_tenth_reflected
      hx hx1 hy hy1
  unfold endpointStripPulledBackFoldedRegularCoefficient
  nlinarith

/-! ## Exact four-channel endpoint block -/

theorem endpointStripRawReserveBlockPair_eq_survivingSquares
    (z s eZ oZ eS oS : ℝ) :
    endpointStripRawReserveBlockPair z s eZ oZ eS oS =
      (stripSameDifferenceReserveWeight z s +
          stripSameCrossReserveWeight z s) * (eZ - eS) ^ 2 +
        stripReflectedPPReserveWeight z s *
          (stripParityValue eZ oZ 1 + stripParityValue eS oS 1) ^ 2 +
        stripReflectedMMReserveWeight z s *
          (stripParityValue eZ oZ (-1) + stripParityValue eS oS (-1)) ^ 2 +
        stripReflectedPMReserveWeight z s *
          (stripParityValue eZ oZ 1 + stripParityValue eS oS (-1)) ^ 2 +
        stripReflectedMPReserveWeight z s *
          (stripParityValue eZ oZ (-1) + stripParityValue eS oS 1) ^ 2 := by
  unfold endpointStripRawReserveBlockPair stripReflectedRawBlockPair
  rw [stripSameAdverseBlockPair_eq_even]
  ring

/-- Exact structural factorization of the endpoint raw-minus-adverse block
plus all four pulled-back folded-regular crosses. -/
theorem endpointStripRawReserveBlockPair_add_regularCross_eq_factors
    (z s eZ oZ eS oS : ℝ) :
    endpointStripRawReserveBlockPair z s eZ oZ eS oS +
        endpointStripFoldedRegularCrossDensity z s
          (stripParityValue eZ oZ 1)
          (stripParityValue eZ oZ (-1))
          (stripParityValue eS oS 1)
          (stripParityValue eS oS (-1)) =
      (stripSameDifferenceReserveWeight z s +
          stripSameCrossReserveWeight z s) * (eZ - eS) ^ 2 +
        endpointStripReflectedRegularChannelFactor
          (stripReflectedPPReserveWeight z s)
          (endpointStripFoldedRegularPPCoefficient z s)
          (stripParityValue eZ oZ 1)
          (stripParityValue eS oS 1) +
        endpointStripReflectedRegularChannelFactor
          (stripReflectedMMReserveWeight z s)
          (endpointStripFoldedRegularMMCoefficient z s)
          (stripParityValue eZ oZ (-1))
          (stripParityValue eS oS (-1)) +
        endpointStripReflectedRegularChannelFactor
          (stripReflectedPMReserveWeight z s)
          (endpointStripFoldedRegularPMCoefficient z s)
          (stripParityValue eZ oZ 1)
          (stripParityValue eS oS (-1)) +
        endpointStripReflectedRegularChannelFactor
          (stripReflectedMPReserveWeight z s)
          (endpointStripFoldedRegularMPCoefficient z s)
          (stripParityValue eZ oZ (-1))
          (stripParityValue eS oS 1) := by
  unfold endpointStripRawReserveBlockPair
    endpointStripFoldedRegularCrossDensity stripReflectedRawBlockPair
  rw [stripSameAdverseBlockPair_eq_even]
  repeat' rw [← reflectedPlusSquare_sub_regularCross_eq_factor]
  ring

/-- Uniform pointwise absorption on the entire normalized endpoint square.
The totalized diagonal `z = s` causes no exception: its surviving same-sign
weight is merely nonnegative, while all four regular crosses are paid for by
their matching reflected plus-squares. -/
theorem endpointStripRawReserveBlockPair_add_regularCross_nonneg
    {z s eZ oZ eS oS : ℝ}
    (hz : 0 < z) (hz1 : z ≤ 1)
    (hs : 0 < s) (hs1 : s ≤ 1) :
    0 ≤ endpointStripRawReserveBlockPair z s eZ oZ eS oS +
      endpointStripFoldedRegularCrossDensity z s
        (stripParityValue eZ oZ 1)
        (stripParityValue eZ oZ (-1))
        (stripParityValue eS oS 1)
        (stripParityValue eS oS (-1)) := by
  rcases endpointStripPhysicalPoints_mem_Ioc hz hz1 with
    ⟨hpz0, hpz1, hmz0, hmz1⟩
  rcases endpointStripPhysicalPoints_mem_Ioc hs hs1 with
    ⟨hps0, hps1, hms0, hms1⟩
  have hsame :
      0 ≤ (stripSameDifferenceReserveWeight z s +
          stripSameCrossReserveWeight z s) * (eZ - eS) ^ 2 := by
    have hkDiff := stripSameDifferenceReserveWeight_nonneg z s
    have hkSum := (stripSameCrossReserveWeight_pos hz hs).le
    positivity
  have hPP0 := endpointStripPulledBackFoldedRegularCoefficient_nonneg
    hpz0 hpz1 hps0 hps1
  have hMM0 := endpointStripPulledBackFoldedRegularCoefficient_nonneg
    hmz0 hmz1 hms0 hms1
  have hPM0 := endpointStripPulledBackFoldedRegularCoefficient_nonneg
    hpz0 hpz1 hms0 hms1
  have hMP0 := endpointStripPulledBackFoldedRegularCoefficient_nonneg
    hmz0 hmz1 hps0 hps1
  have hPPcap0 := endpointStripPulledBackFoldedRegularCoefficient_le_two_reflected
    hpz0 hpz1 hps0 hps1
  have hMMcap0 := endpointStripPulledBackFoldedRegularCoefficient_le_two_reflected
    hmz0 hmz1 hms0 hms1
  have hPMcap0 := endpointStripPulledBackFoldedRegularCoefficient_le_two_reflected
    hpz0 hpz1 hms0 hms1
  have hMPcap0 := endpointStripPulledBackFoldedRegularCoefficient_le_two_reflected
    hmz0 hmz1 hps0 hps1
  have hPPcap : endpointStripFoldedRegularPPCoefficient z s ≤
      2 * stripReflectedPPReserveWeight z s := by
    unfold endpointStripFoldedRegularPPCoefficient
    rw [stripReflectedPPReserveWeight_eq_pulledBack]
    exact hPPcap0
  have hMMcap : endpointStripFoldedRegularMMCoefficient z s ≤
      2 * stripReflectedMMReserveWeight z s := by
    unfold endpointStripFoldedRegularMMCoefficient
    rw [stripReflectedMMReserveWeight_eq_pulledBack]
    exact hMMcap0
  have hPMcap : endpointStripFoldedRegularPMCoefficient z s ≤
      2 * stripReflectedPMReserveWeight z s := by
    unfold endpointStripFoldedRegularPMCoefficient
    rw [stripReflectedPMReserveWeight_eq_pulledBack]
    exact hPMcap0
  have hMPcap : endpointStripFoldedRegularMPCoefficient z s ≤
      2 * stripReflectedMPReserveWeight z s := by
    unfold endpointStripFoldedRegularMPCoefficient
    rw [stripReflectedMPReserveWeight_eq_pulledBack]
    exact hMPcap0
  have hPP := endpointStripReflectedRegularChannelFactor_nonneg
    (k := stripReflectedPPReserveWeight z s)
    (c := endpointStripFoldedRegularPPCoefficient z s)
    (u := stripParityValue eZ oZ 1)
    (v := stripParityValue eS oS 1) hPP0 hPPcap
  have hMM := endpointStripReflectedRegularChannelFactor_nonneg
    (k := stripReflectedMMReserveWeight z s)
    (c := endpointStripFoldedRegularMMCoefficient z s)
    (u := stripParityValue eZ oZ (-1))
    (v := stripParityValue eS oS (-1)) hMM0 hMMcap
  have hPM := endpointStripReflectedRegularChannelFactor_nonneg
    (k := stripReflectedPMReserveWeight z s)
    (c := endpointStripFoldedRegularPMCoefficient z s)
    (u := stripParityValue eZ oZ 1)
    (v := stripParityValue eS oS (-1)) hPM0 hPMcap
  have hMP := endpointStripReflectedRegularChannelFactor_nonneg
    (k := stripReflectedMPReserveWeight z s)
    (c := endpointStripFoldedRegularMPCoefficient z s)
    (u := stripParityValue eZ oZ (-1))
    (v := stripParityValue eS oS 1) hMP0 hMPcap
  rw [endpointStripRawReserveBlockPair_add_regularCross_eq_factors]
  positivity

/-- The sharp common kernel lower bound leaves nineteen twentieths of the
entire endpoint raw-minus-adverse reserve, not merely nonnegativity. -/
theorem nineteenTwentieths_mul_endpointStripRawReserveBlockPair_le_add_regularCross
    {z s eZ oZ eS oS : ℝ}
    (hz : 0 < z) (hz1 : z ≤ 1)
    (hs : 0 < s) (hs1 : s ≤ 1) :
    (19 / 20 : ℝ) * endpointStripRawReserveBlockPair z s eZ oZ eS oS ≤
      endpointStripRawReserveBlockPair z s eZ oZ eS oS +
        endpointStripFoldedRegularCrossDensity z s
          (stripParityValue eZ oZ 1)
          (stripParityValue eZ oZ (-1))
          (stripParityValue eS oS 1)
          (stripParityValue eS oS (-1)) := by
  rcases endpointStripPhysicalPoints_mem_Ioc hz hz1 with
    ⟨hpz0, hpz1, hmz0, hmz1⟩
  rcases endpointStripPhysicalPoints_mem_Ioc hs hs1 with
    ⟨hps0, hps1, hms0, hms1⟩
  rcases stripReflectedReserveWeights_pos hz.le hz1 hs.le hs1 with
    ⟨hkPP, hkMM, hkPM, hkMP⟩
  have hsame :
      0 ≤ (stripSameDifferenceReserveWeight z s +
          stripSameCrossReserveWeight z s) * (eZ - eS) ^ 2 := by
    have hkDiff := stripSameDifferenceReserveWeight_nonneg z s
    have hkSum := (stripSameCrossReserveWeight_pos hz hs).le
    positivity
  have hPP0 := endpointStripPulledBackFoldedRegularCoefficient_nonneg
    hpz0 hpz1 hps0 hps1
  have hMM0 := endpointStripPulledBackFoldedRegularCoefficient_nonneg
    hmz0 hmz1 hms0 hms1
  have hPM0 := endpointStripPulledBackFoldedRegularCoefficient_nonneg
    hpz0 hpz1 hms0 hms1
  have hMP0 := endpointStripPulledBackFoldedRegularCoefficient_nonneg
    hmz0 hmz1 hps0 hps1
  have hPPcap0 :=
    endpointStripPulledBackFoldedRegularCoefficient_le_tenth_reflected
      hpz0 hpz1 hps0 hps1
  have hMMcap0 :=
    endpointStripPulledBackFoldedRegularCoefficient_le_tenth_reflected
      hmz0 hmz1 hms0 hms1
  have hPMcap0 :=
    endpointStripPulledBackFoldedRegularCoefficient_le_tenth_reflected
      hpz0 hpz1 hms0 hms1
  have hMPcap0 :=
    endpointStripPulledBackFoldedRegularCoefficient_le_tenth_reflected
      hmz0 hmz1 hps0 hps1
  have hPPcap : endpointStripFoldedRegularPPCoefficient z s ≤
      stripReflectedPPReserveWeight z s / 10 := by
    unfold endpointStripFoldedRegularPPCoefficient
    rw [stripReflectedPPReserveWeight_eq_pulledBack]
    exact hPPcap0
  have hMMcap : endpointStripFoldedRegularMMCoefficient z s ≤
      stripReflectedMMReserveWeight z s / 10 := by
    unfold endpointStripFoldedRegularMMCoefficient
    rw [stripReflectedMMReserveWeight_eq_pulledBack]
    exact hMMcap0
  have hPMcap : endpointStripFoldedRegularPMCoefficient z s ≤
      stripReflectedPMReserveWeight z s / 10 := by
    unfold endpointStripFoldedRegularPMCoefficient
    rw [stripReflectedPMReserveWeight_eq_pulledBack]
    exact hPMcap0
  have hMPcap : endpointStripFoldedRegularMPCoefficient z s ≤
      stripReflectedMPReserveWeight z s / 10 := by
    unfold endpointStripFoldedRegularMPCoefficient
    rw [stripReflectedMPReserveWeight_eq_pulledBack]
    exact hMPcap0
  have hPP := nineteenTwentieths_mul_reflectedPlusSquare_le_channelFactor
    (k := stripReflectedPPReserveWeight z s)
    (c := endpointStripFoldedRegularPPCoefficient z s)
    (u := stripParityValue eZ oZ 1)
    (v := stripParityValue eS oS 1) hkPP.le hPP0 hPPcap
  have hMM := nineteenTwentieths_mul_reflectedPlusSquare_le_channelFactor
    (k := stripReflectedMMReserveWeight z s)
    (c := endpointStripFoldedRegularMMCoefficient z s)
    (u := stripParityValue eZ oZ (-1))
    (v := stripParityValue eS oS (-1)) hkMM.le hMM0 hMMcap
  have hPM := nineteenTwentieths_mul_reflectedPlusSquare_le_channelFactor
    (k := stripReflectedPMReserveWeight z s)
    (c := endpointStripFoldedRegularPMCoefficient z s)
    (u := stripParityValue eZ oZ 1)
    (v := stripParityValue eS oS (-1)) hkPM.le hPM0 hPMcap
  have hMP := nineteenTwentieths_mul_reflectedPlusSquare_le_channelFactor
    (k := stripReflectedMPReserveWeight z s)
    (c := endpointStripFoldedRegularMPCoefficient z s)
    (u := stripParityValue eZ oZ (-1))
    (v := stripParityValue eS oS 1) hkMP.le hMP0 hMPcap
  rw [endpointStripRawReserveBlockPair_add_regularCross_eq_factors,
    endpointStripRawReserveBlockPair_eq_survivingSquares]
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddCoreEndpointBlockRegularAbsorptionStructural
