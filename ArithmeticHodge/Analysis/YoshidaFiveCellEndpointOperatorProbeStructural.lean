import ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellSingleProfileStructural
import ArithmeticHodge.Analysis.YoshidaFourCellParityOperatorStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointParityPencil

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFiveCellEndpointOperatorProbeStructural

noncomputable section

open MultiplicativeWeilFiveCellSingleProfileStructural
open CenteredEndpointCorrelation
open YoshidaFactorTwoEndpointParityPencil
open YoshidaEndpointPotentialBound
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaFourCellRawParityFoldStructural
open YoshidaFourCellRegularKernelSquareStructural
open YoshidaGeneralEndpointPhysicalRealQuadraticStructural
open YoshidaRegularKernelBound

/-!
# Structural probe of the five-cell endpoint operator

The normalized five-cell prime atom couples the endpoint strips
`[1 / 3, 1]` and `[-1, -1 / 3]` at lag `4 / 3`.  This file keeps that
channel exact.  Its first normal form is the pointwise Hadamard
diagonalization into matched and antimatched strip squares.
-/

/-- Fixed normalized halfwidth of five consecutive quarter cells. -/
def fiveCellOperatorHalfWidth : ℝ :=
  3 * Real.log 2 / 4

/-- The matched Hadamard square on the five-cell endpoint strips. -/
def fiveCellEndpointMatchedSquare (w : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ in (1 / 3 : ℝ)..1,
    (w x + w (x - 4 / 3)) ^ 2

/-- The antimatched Hadamard square on the five-cell endpoint strips. -/
def fiveCellEndpointAntimatchedSquare (w : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ in (1 / 3 : ℝ)..1,
    (w x - w (x - 4 / 3)) ^ 2

/-- The exact endpoint-corrected five-cell operator. -/
def fiveCellEndpointOperator (w : ℝ → ℝ) : ℝ :=
  centeredClippedPhysicalQuadratic fiveCellOperatorHalfWidth w -
    Real.sqrt 2 * Real.log 2 * fiveCellEndpointPairing w

/-- Both Hadamard channels are literal nonnegative squares. -/
theorem fiveCellEndpointMatchedSquare_nonneg (w : ℝ → ℝ) :
    0 ≤ fiveCellEndpointMatchedSquare w := by
  unfold fiveCellEndpointMatchedSquare
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro x _hx
  positivity

theorem fiveCellEndpointAntimatchedSquare_nonneg (w : ℝ → ℝ) :
    0 ≤ fiveCellEndpointAntimatchedSquare w := by
  unfold fiveCellEndpointAntimatchedSquare
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro x _hx
  positivity

/-- Sharp Hadamard signature of the lag-`4 / 3` endpoint pairing.  No
endpoint trace, parity, or finite-dimensional hypothesis enters. -/
theorem four_mul_fiveCellEndpointPairing_eq_matched_sub_antimatched
    (w : ℝ → ℝ) (hw : Continuous w) :
    4 * fiveCellEndpointPairing w =
      fiveCellEndpointMatchedSquare w -
        fiveCellEndpointAntimatchedSquare w := by
  have hplus : IntervalIntegrable
      (fun x : ℝ ↦ (w x + w (x - 4 / 3)) ^ 2)
      volume (1 / 3) 1 := by
    exact (by fun_prop : Continuous
      (fun x : ℝ ↦ (w x + w (x - 4 / 3)) ^ 2)).intervalIntegrable _ _
  have hminus : IntervalIntegrable
      (fun x : ℝ ↦ (w x - w (x - 4 / 3)) ^ 2)
      volume (1 / 3) 1 := by
    exact (by fun_prop : Continuous
      (fun x : ℝ ↦ (w x - w (x - 4 / 3)) ^ 2)).intervalIntegrable _ _
  unfold fiveCellEndpointPairing fiveCellEndpointMatchedSquare
    fiveCellEndpointAntimatchedSquare
  rw [← intervalIntegral.integral_sub hplus hminus,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _hx
  ring

/-- Exact positive-minus-negative square normal form of the complete
five-cell endpoint operator. -/
theorem fiveCellEndpointOperator_eq_physical_add_antimatched_sub_matched
    (w : ℝ → ℝ) (hw : Continuous w) :
    fiveCellEndpointOperator w =
      centeredClippedPhysicalQuadratic fiveCellOperatorHalfWidth w +
          (Real.sqrt 2 * Real.log 2 / 4) *
            fiveCellEndpointAntimatchedSquare w -
        (Real.sqrt 2 * Real.log 2 / 4) *
          fiveCellEndpointMatchedSquare w := by
  unfold fiveCellEndpointOperator
  rw [show fiveCellEndpointPairing w =
      (fiveCellEndpointMatchedSquare w -
        fiveCellEndpointAntimatchedSquare w) / 4 by
    linarith [four_mul_fiveCellEndpointPairing_eq_matched_sub_antimatched
      w hw]]
  ring

/-- The sharp universal capacity frontier.  Positivity is exactly the
requirement that the physical diagonal plus the favorable antimatched
channel pay for the adverse matched channel. -/
theorem fiveCellEndpointOperator_nonnegative_iff_capacity
    (w : ℝ → ℝ) (hw : Continuous w) :
    0 ≤ fiveCellEndpointOperator w ↔
      (Real.sqrt 2 * Real.log 2 / 4) *
          fiveCellEndpointMatchedSquare w ≤
        centeredClippedPhysicalQuadratic fiveCellOperatorHalfWidth w +
          (Real.sqrt 2 * Real.log 2 / 4) *
            fiveCellEndpointAntimatchedSquare w := by
  rw [fiveCellEndpointOperator_eq_physical_add_antimatched_sub_matched w hw]
  exact sub_nonneg

/-! ## Reflection-parity half-strip normal form -/

/-- The sum of the two positive-half traces exchanged by the five-cell
endpoint involution. -/
def fiveCellEndpointHalfMatched (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  w (1 / 3 + t) + w (1 - t)

/-- The difference of the same two positive-half traces. -/
def fiveCellEndpointHalfAntimatched (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  w (1 / 3 + t) - w (1 - t)

/-- Symmetric mass of the two traces exchanged on the five-cell endpoint
strip. -/
def fiveCellEndpointHalfMass (w : ℝ → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ t : ℝ in 0..2 / 3,
    (w (1 / 3 + t) ^ 2 + w (1 - t) ^ 2)

private theorem fiveCellEndpointMatchedSquare_shift (w : ℝ → ℝ) :
    fiveCellEndpointMatchedSquare w =
      ∫ t : ℝ in 0..2 / 3,
        (w (1 / 3 + t) + w (-1 + t)) ^ 2 := by
  unfold fiveCellEndpointMatchedSquare
  have hshift := intervalIntegral.integral_comp_add_left
    (f := fun x : ℝ ↦ (w x + w (x - 4 / 3)) ^ 2)
    (a := (0 : ℝ)) (b := 2 / 3) (1 / 3)
  norm_num at hshift ⊢
  calc
    _ = ∫ t : ℝ in 0..2 / 3,
        (w (1 / 3 + t) + w (1 / 3 + t - 4 / 3)) ^ 2 := hshift.symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t _ht
      change (w (1 / 3 + t) + w (1 / 3 + t - 4 / 3)) ^ 2 =
        (w (1 / 3 + t) + w (-1 + t)) ^ 2
      rw [show 1 / 3 + t - 4 / 3 = -1 + t by ring]

private theorem fiveCellEndpointAntimatchedSquare_shift (w : ℝ → ℝ) :
    fiveCellEndpointAntimatchedSquare w =
      ∫ t : ℝ in 0..2 / 3,
        (w (1 / 3 + t) - w (-1 + t)) ^ 2 := by
  unfold fiveCellEndpointAntimatchedSquare
  have hshift := intervalIntegral.integral_comp_add_left
    (f := fun x : ℝ ↦ (w x - w (x - 4 / 3)) ^ 2)
    (a := (0 : ℝ)) (b := 2 / 3) (1 / 3)
  norm_num at hshift ⊢
  calc
    _ = ∫ t : ℝ in 0..2 / 3,
        (w (1 / 3 + t) - w (1 / 3 + t - 4 / 3)) ^ 2 := hshift.symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t _ht
      change (w (1 / 3 + t) - w (1 / 3 + t - 4 / 3)) ^ 2 =
        (w (1 / 3 + t) - w (-1 + t)) ^ 2
      rw [show 1 / 3 + t - 4 / 3 = -1 + t by ring]

/-- In even reflection parity, the full matched endpoint square is the
positive-half matched channel. -/
theorem fiveCellEndpointMatchedSquare_eq_halfMatched_of_even
    (w : ℝ → ℝ) (heven : Function.Even w) :
    fiveCellEndpointMatchedSquare w =
      ∫ t : ℝ in 0..2 / 3, fiveCellEndpointHalfMatched w t ^ 2 := by
  rw [fiveCellEndpointMatchedSquare_shift]
  unfold fiveCellEndpointHalfMatched
  apply intervalIntegral.integral_congr
  intro t _ht
  change (w (1 / 3 + t) + w (-1 + t)) ^ 2 =
    (w (1 / 3 + t) + w (1 - t)) ^ 2
  rw [show -1 + t = -(1 - t) by ring, heven]

/-- In even reflection parity, the full antimatched endpoint square is the
positive-half antimatched channel. -/
theorem fiveCellEndpointAntimatchedSquare_eq_halfAntimatched_of_even
    (w : ℝ → ℝ) (heven : Function.Even w) :
    fiveCellEndpointAntimatchedSquare w =
      ∫ t : ℝ in 0..2 / 3,
        fiveCellEndpointHalfAntimatched w t ^ 2 := by
  rw [fiveCellEndpointAntimatchedSquare_shift]
  unfold fiveCellEndpointHalfAntimatched
  apply intervalIntegral.integral_congr
  intro t _ht
  change (w (1 / 3 + t) - w (-1 + t)) ^ 2 =
    (w (1 / 3 + t) - w (1 - t)) ^ 2
  rw [show -1 + t = -(1 - t) by ring, heven]

/-- Odd reflection swaps the full matched square into the positive-half
antimatched channel. -/
theorem fiveCellEndpointMatchedSquare_eq_halfAntimatched_of_odd
    (w : ℝ → ℝ) (hodd : Function.Odd w) :
    fiveCellEndpointMatchedSquare w =
      ∫ t : ℝ in 0..2 / 3,
        fiveCellEndpointHalfAntimatched w t ^ 2 := by
  rw [fiveCellEndpointMatchedSquare_shift]
  unfold fiveCellEndpointHalfAntimatched
  apply intervalIntegral.integral_congr
  intro t _ht
  change (w (1 / 3 + t) + w (-1 + t)) ^ 2 =
    (w (1 / 3 + t) - w (1 - t)) ^ 2
  rw [show -1 + t = -(1 - t) by ring, hodd]
  ring

/-- Odd reflection swaps the full antimatched square into the positive-half
matched channel. -/
theorem fiveCellEndpointAntimatchedSquare_eq_halfMatched_of_odd
    (w : ℝ → ℝ) (hodd : Function.Odd w) :
    fiveCellEndpointAntimatchedSquare w =
      ∫ t : ℝ in 0..2 / 3, fiveCellEndpointHalfMatched w t ^ 2 := by
  rw [fiveCellEndpointAntimatchedSquare_shift]
  unfold fiveCellEndpointHalfMatched
  apply intervalIntegral.integral_congr
  intro t _ht
  change (w (1 / 3 + t) - w (-1 + t)) ^ 2 =
    (w (1 / 3 + t) + w (1 - t)) ^ 2
  rw [show -1 + t = -(1 - t) by ring, hodd]
  ring

/-- Pointwise parallelogram identity for the two five-cell endpoint
channels. -/
theorem fiveCell_halfMatched_add_halfAntimatched_eq_four_mul_halfMass
    (w : ℝ → ℝ) (hw : Continuous w) :
    (∫ t : ℝ in 0..2 / 3, fiveCellEndpointHalfMatched w t ^ 2) +
        (∫ t : ℝ in 0..2 / 3,
          fiveCellEndpointHalfAntimatched w t ^ 2) =
      4 * fiveCellEndpointHalfMass w := by
  have hplus : IntervalIntegrable
      (fun t : ℝ ↦ fiveCellEndpointHalfMatched w t ^ 2)
      volume 0 (2 / 3) :=
    (by
      unfold fiveCellEndpointHalfMatched
      fun_prop : Continuous
        (fun t : ℝ ↦ fiveCellEndpointHalfMatched w t ^ 2)).intervalIntegrable _ _
  have hminus : IntervalIntegrable
      (fun t : ℝ ↦ fiveCellEndpointHalfAntimatched w t ^ 2)
      volume 0 (2 / 3) :=
    (by
      unfold fiveCellEndpointHalfAntimatched
      fun_prop : Continuous
        (fun t : ℝ ↦ fiveCellEndpointHalfAntimatched w t ^ 2)).intervalIntegrable _ _
  rw [← intervalIntegral.integral_add hplus hminus]
  unfold fiveCellEndpointHalfMatched fiveCellEndpointHalfAntimatched
    fiveCellEndpointHalfMass
  rw [show (fun t : ℝ ↦
      (w (1 / 3 + t) + w (1 - t)) ^ 2 +
        (w (1 / 3 + t) - w (1 - t)) ^ 2) =
      fun t ↦ 2 * (w (1 / 3 + t) ^ 2 + w (1 - t) ^ 2) by
    funext t
    ring,
    intervalIntegral.integral_const_mul]
  ring

/-- Even parity retains the favorable antimatched square and pays exactly
one symmetric strip mass. -/
theorem neg_fiveCellPairing_eq_halfAntimatched_sub_mass_of_even
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w) :
    -(Real.sqrt 2 * Real.log 2) * fiveCellEndpointPairing w =
      (Real.sqrt 2 * Real.log 2 / 2) *
          (∫ t : ℝ in 0..2 / 3,
            fiveCellEndpointHalfAntimatched w t ^ 2) -
        Real.sqrt 2 * Real.log 2 * fiveCellEndpointHalfMass w := by
  have hp := four_mul_fiveCellEndpointPairing_eq_matched_sub_antimatched w hw
  rw [fiveCellEndpointMatchedSquare_eq_halfMatched_of_even w heven,
    fiveCellEndpointAntimatchedSquare_eq_halfAntimatched_of_even w heven] at hp
  have hs := fiveCell_halfMatched_add_halfAntimatched_eq_four_mul_halfMass w hw
  linear_combination
    (-(Real.sqrt 2 * Real.log 2) / 4) * hp +
      (-(Real.sqrt 2 * Real.log 2) / 4) * hs

/-- Odd parity swaps the endpoint ranks and therefore retains the favorable
matched square. -/
theorem neg_fiveCellPairing_eq_halfMatched_sub_mass_of_odd
    (w : ℝ → ℝ) (hw : Continuous w) (hodd : Function.Odd w) :
    -(Real.sqrt 2 * Real.log 2) * fiveCellEndpointPairing w =
      (Real.sqrt 2 * Real.log 2 / 2) *
          (∫ t : ℝ in 0..2 / 3,
            fiveCellEndpointHalfMatched w t ^ 2) -
        Real.sqrt 2 * Real.log 2 * fiveCellEndpointHalfMass w := by
  have hp := four_mul_fiveCellEndpointPairing_eq_matched_sub_antimatched w hw
  rw [fiveCellEndpointMatchedSquare_eq_halfAntimatched_of_odd w hodd,
    fiveCellEndpointAntimatchedSquare_eq_halfMatched_of_odd w hodd] at hp
  have hs := fiveCell_halfMatched_add_halfAntimatched_eq_four_mul_halfMass w hw
  linear_combination
    (-(Real.sqrt 2 * Real.log 2) / 4) * hp +
      (-(Real.sqrt 2 * Real.log 2) / 4) * hs

/-! ## Complete parity operators -/

/-- The complete regular-kernel quadratic at five-cell halfwidth. -/
def fiveCellRegularFullSquare (w : ℝ → ℝ) : ℝ :=
  ∫ y : ℝ in -1..1, ∫ x : ℝ in -1..1,
    yoshidaRegularKernel
        (fiveCellOperatorHalfWidth * |y - x|) * w y * w x

/-- Exact positive-half normal form in the reflection-even sector. -/
def fiveCellEvenParityOperator (w : ℝ → ℝ) : ℝ :=
  (1 / 2 : ℝ) *
      (fourCellPositiveHalfRawSameSignEnergy w +
        fourCellPositiveHalfRawReflectedEnergy w 1) +
    2 * (∫ x : ℝ in 0..1,
      yoshidaEndpointPotential x * w x ^ 2) -
    2 * (Real.log (2 * fiveCellOperatorHalfWidth) +
        Real.eulerMascheroniConstant + Real.log Real.pi) *
      (∫ x : ℝ in 0..1, w x ^ 2) -
    fiveCellOperatorHalfWidth * fiveCellRegularFullSquare w +
    8 * fiveCellOperatorHalfWidth *
      fourCellPositiveCoshMoment w
        (fiveCellOperatorHalfWidth / 2) ^ 2 +
    (Real.sqrt 2 * Real.log 2 / 2) *
      (∫ t : ℝ in 0..2 / 3,
        fiveCellEndpointHalfAntimatched w t ^ 2) -
    Real.sqrt 2 * Real.log 2 * fiveCellEndpointHalfMass w

/-- Exact positive-half normal form in the reflection-odd sector. -/
def fiveCellOddParityOperator (w : ℝ → ℝ) : ℝ :=
  (1 / 2 : ℝ) *
      (fourCellPositiveHalfRawSameSignEnergy w +
        fourCellPositiveHalfRawReflectedEnergy w (-1)) +
    2 * (∫ x : ℝ in 0..1,
      yoshidaEndpointPotential x * w x ^ 2) -
    2 * (Real.log (2 * fiveCellOperatorHalfWidth) +
        Real.eulerMascheroniConstant + Real.log Real.pi) *
      (∫ x : ℝ in 0..1, w x ^ 2) -
    fiveCellOperatorHalfWidth * fiveCellRegularFullSquare w -
    8 * fiveCellOperatorHalfWidth *
      fourCellPositiveSinhMoment w
        (fiveCellOperatorHalfWidth / 2) ^ 2 +
    (Real.sqrt 2 * Real.log 2 / 2) *
      (∫ t : ℝ in 0..2 / 3,
        fiveCellEndpointHalfMatched w t ^ 2) -
    Real.sqrt 2 * Real.log 2 * fiveCellEndpointHalfMass w

private theorem fiveCellOperatorHalfWidth_nonneg :
    0 ≤ fiveCellOperatorHalfWidth := by
  unfold fiveCellOperatorHalfWidth
  positivity

private theorem fiveCellOperatorHalfWidth_le_log_three_div_two :
    fiveCellOperatorHalfWidth ≤ Real.log 3 / 2 := by
  have hpow : (2 : ℝ) ^ 3 < (3 : ℝ) ^ 2 := by norm_num
  have hlog := Real.strictMonoOn_log (by norm_num) (by norm_num) hpow
  rw [Real.log_pow, Real.log_pow] at hlog
  norm_num at hlog
  unfold fiveCellOperatorHalfWidth
  linarith

/-- The full endpoint-zero five-cell bracket on an even locally Lipschitz
profile is exactly the even operator.  The polar contribution is one
positive cosh rank. -/
theorem fiveCellEndpointOperator_eq_evenParityOperator
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w) :
    fiveCellEndpointOperator w = fiveCellEvenParityOperator w := by
  have hraw := centeredRawLogEnergy_div_four_eq_positiveHalf_even
    w hlocal heven
  have hpotential := endpointPotential_eq_two_mul_positiveHalf
    w hw (Or.inl heven)
  have hmass := integral_sq_eq_two_mul_positiveHalf
    w hw (Or.inl heven)
  have hregular :=
    two_mul_integral_yoshidaRegularKernel_mul_centeredCorrelation_eq_fullSquare
      w hw fiveCellOperatorHalfWidth fiveCellOperatorHalfWidth_nonneg
        fiveCellOperatorHalfWidth_le_log_three_div_two
  have hpolar := physicalPolarProduct_eq_positiveCoshSquare_of_even
    w hw heven fiveCellOperatorHalfWidth
  have hprime := neg_fiveCellPairing_eq_halfAntimatched_sub_mass_of_even
    w hw heven
  unfold fiveCellEndpointOperator centeredClippedPhysicalQuadratic
    fiveCellEvenParityOperator fiveCellRegularFullSquare
  rw [hraw, hpotential, hmass, hpolar]
  linear_combination hprime - fiveCellOperatorHalfWidth * hregular

/-- The full endpoint-zero five-cell bracket on an odd locally Lipschitz
profile is exactly the odd operator.  Its polar contribution is one
negative sinh rank. -/
theorem fiveCellEndpointOperator_eq_oddParityOperator
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (hodd : Function.Odd w) :
    fiveCellEndpointOperator w = fiveCellOddParityOperator w := by
  have hraw := centeredRawLogEnergy_div_four_eq_positiveHalf_odd
    w hlocal hodd
  have hpotential := endpointPotential_eq_two_mul_positiveHalf
    w hw (Or.inr hodd)
  have hmass := integral_sq_eq_two_mul_positiveHalf
    w hw (Or.inr hodd)
  have hregular :=
    two_mul_integral_yoshidaRegularKernel_mul_centeredCorrelation_eq_fullSquare
      w hw fiveCellOperatorHalfWidth fiveCellOperatorHalfWidth_nonneg
        fiveCellOperatorHalfWidth_le_log_three_div_two
  have hpolar := physicalPolarProduct_eq_neg_positiveSinhSquare_of_odd
    w hw hodd fiveCellOperatorHalfWidth
  have hprime := neg_fiveCellPairing_eq_halfMatched_sub_mass_of_odd
    w hw hodd
  unfold fiveCellEndpointOperator centeredClippedPhysicalQuadratic
    fiveCellOddParityOperator fiveCellRegularFullSquare
  rw [hraw, hpotential, hmass, hpolar]
  linear_combination hprime - fiveCellOperatorHalfWidth * hregular

end

end ArithmeticHodge.Analysis.YoshidaFiveCellEndpointOperatorProbeStructural
