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

/-! ## Trace eigenspaces and the parity-sign obstruction -/

/-- On the antimatched trace eigenspace, the retained prime atom is a
strictly favorable strip-mass term.  This is an infinite-dimensional linear
condition, not a modal truncation. -/
theorem fiveCellEndpointOperator_eq_physical_add_stripMass_of_antimatched
    (w : ℝ → ℝ)
    (hanti : ∀ x ∈ uIcc (1 / 3 : ℝ) 1,
      w (x - 4 / 3) = -w x) :
    fiveCellEndpointOperator w =
      centeredClippedPhysicalQuadratic fiveCellOperatorHalfWidth w +
        Real.sqrt 2 * Real.log 2 *
          (∫ x : ℝ in (1 / 3 : ℝ)..1, w x ^ 2) := by
  have hpair : fiveCellEndpointPairing w =
      -(∫ x : ℝ in (1 / 3 : ℝ)..1, w x ^ 2) := by
    unfold fiveCellEndpointPairing
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x hx
    change w x * w (x - 4 / 3) = -(w x ^ 2)
    rw [hanti x hx]
    ring
  unfold fiveCellEndpointOperator
  rw [hpair]
  ring

/-- Consequently, nonnegativity of the local physical diagonal gives an
exact strip-mass coercive lower bound on the antimatched trace subspace. -/
theorem fiveCellEndpointOperator_stripMass_le_of_antimatched
    (w : ℝ → ℝ)
    (hanti : ∀ x ∈ uIcc (1 / 3 : ℝ) 1,
      w (x - 4 / 3) = -w x)
    (hphysical :
      0 ≤ centeredClippedPhysicalQuadratic fiveCellOperatorHalfWidth w) :
    Real.sqrt 2 * Real.log 2 *
        (∫ x : ℝ in (1 / 3 : ℝ)..1, w x ^ 2) ≤
      fiveCellEndpointOperator w := by
  rw [fiveCellEndpointOperator_eq_physical_add_stripMass_of_antimatched
    w hanti]
  linarith

/-- On the matched trace eigenspace the same strip mass occurs with the
opposite sign.  Any relaxation which forgets this channel loses exactly this
adverse direction. -/
theorem fiveCellEndpointOperator_eq_physical_sub_stripMass_of_matched
    (w : ℝ → ℝ)
    (hmatch : ∀ x ∈ uIcc (1 / 3 : ℝ) 1,
      w (x - 4 / 3) = w x) :
    fiveCellEndpointOperator w =
      centeredClippedPhysicalQuadratic fiveCellOperatorHalfWidth w -
        Real.sqrt 2 * Real.log 2 *
          (∫ x : ℝ in (1 / 3 : ℝ)..1, w x ^ 2) := by
  have hpair : fiveCellEndpointPairing w =
      ∫ x : ℝ in (1 / 3 : ℝ)..1, w x ^ 2 := by
    unfold fiveCellEndpointPairing
    apply intervalIntegral.integral_congr
    intro x hx
    change w x * w (x - 4 / 3) = w x ^ 2
    rw [hmatch x hx]
    ring
  unfold fiveCellEndpointOperator
  rw [hpair]

/-- A small exact polynomial integration helper for the four endpoint-zero
witnesses below. -/
private theorem integral_polynomial_ten
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ l r : ℝ) :
    (∫ x : ℝ in l..r,
      a₀ * x ^ 0 + a₁ * x ^ 1 + a₂ * x ^ 2 + a₃ * x ^ 3 + a₄ * x ^ 4 +
        a₅ * x ^ 5 + a₆ * x ^ 6 + a₇ * x ^ 7 + a₈ * x ^ 8 +
          a₉ * x ^ 9 + a₁₀ * x ^ 10) =
      a₀ * (r - l) + a₁ * (r ^ 2 - l ^ 2) / 2 +
        a₂ * (r ^ 3 - l ^ 3) / 3 + a₃ * (r ^ 4 - l ^ 4) / 4 +
          a₄ * (r ^ 5 - l ^ 5) / 5 + a₅ * (r ^ 6 - l ^ 6) / 6 +
            a₆ * (r ^ 7 - l ^ 7) / 7 + a₇ * (r ^ 8 - l ^ 8) / 8 +
              a₈ * (r ^ 9 - l ^ 9) / 9 + a₉ * (r ^ 10 - l ^ 10) / 10 +
                a₁₀ * (r ^ 11 - l ^ 11) / 11 := by
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) l r)
    (Continuous.intervalIntegrable (by fun_prop) l r)]
  repeat rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

/-- Lowest endpoint-zero even profile; its endpoint pairing is positive. -/
def fiveCellEvenPositiveWitness (x : ℝ) : ℝ :=
  1 - x ^ 2

/-- An endpoint-zero even profile whose additional interior node reverses
the sign of the endpoint pairing. -/
def fiveCellEvenNegativeWitness (x : ℝ) : ℝ :=
  (1 - x ^ 2) * (x ^ 2 - 4 / 9)

/-- Lowest endpoint-zero odd profile; its endpoint pairing is negative. -/
def fiveCellOddNegativeWitness (x : ℝ) : ℝ :=
  x * (1 - x ^ 2)

/-- An endpoint-zero odd profile whose additional interior node reverses
the sign of the endpoint pairing. -/
def fiveCellOddPositiveWitness (x : ℝ) : ℝ :=
  x * (1 - x ^ 2) * (x ^ 2 - 4 / 9)

theorem fiveCellEvenPositiveWitness_contDiff :
    ContDiff ℝ 1 fiveCellEvenPositiveWitness := by
  unfold fiveCellEvenPositiveWitness
  fun_prop

theorem fiveCellEvenNegativeWitness_contDiff :
    ContDiff ℝ 1 fiveCellEvenNegativeWitness := by
  unfold fiveCellEvenNegativeWitness
  fun_prop

theorem fiveCellOddNegativeWitness_contDiff :
    ContDiff ℝ 1 fiveCellOddNegativeWitness := by
  unfold fiveCellOddNegativeWitness
  fun_prop

theorem fiveCellOddPositiveWitness_contDiff :
    ContDiff ℝ 1 fiveCellOddPositiveWitness := by
  unfold fiveCellOddPositiveWitness
  fun_prop

theorem fiveCellEvenPositiveWitness_even :
    Function.Even fiveCellEvenPositiveWitness := by
  intro x
  unfold fiveCellEvenPositiveWitness
  ring

theorem fiveCellEvenNegativeWitness_even :
    Function.Even fiveCellEvenNegativeWitness := by
  intro x
  unfold fiveCellEvenNegativeWitness
  ring

theorem fiveCellOddNegativeWitness_odd :
    Function.Odd fiveCellOddNegativeWitness := by
  intro x
  unfold fiveCellOddNegativeWitness
  ring

theorem fiveCellOddPositiveWitness_odd :
    Function.Odd fiveCellOddPositiveWitness := by
  intro x
  unfold fiveCellOddPositiveWitness
  ring

theorem fiveCellEvenPositiveWitness_endpoints_zero :
    fiveCellEvenPositiveWitness (-1) = 0 ∧
      fiveCellEvenPositiveWitness 1 = 0 := by
  norm_num [fiveCellEvenPositiveWitness]

theorem fiveCellEvenNegativeWitness_endpoints_zero :
    fiveCellEvenNegativeWitness (-1) = 0 ∧
      fiveCellEvenNegativeWitness 1 = 0 := by
  norm_num [fiveCellEvenNegativeWitness]

theorem fiveCellOddNegativeWitness_endpoints_zero :
    fiveCellOddNegativeWitness (-1) = 0 ∧
      fiveCellOddNegativeWitness 1 = 0 := by
  norm_num [fiveCellOddNegativeWitness]

theorem fiveCellOddPositiveWitness_endpoints_zero :
    fiveCellOddPositiveWitness (-1) = 0 ∧
      fiveCellOddPositiveWitness 1 = 0 := by
  norm_num [fiveCellOddPositiveWitness]

theorem fiveCellEndpointPairing_evenPositiveWitness :
    fiveCellEndpointPairing fiveCellEvenPositiveWitness = 496 / 3645 := by
  unfold fiveCellEndpointPairing
  rw [show (fun x : ℝ ↦ fiveCellEvenPositiveWitness x *
      fiveCellEvenPositiveWitness (x - 4 / 3)) =
      fun x ↦ (-7 / 9) * x ^ 0 + (8 / 3) * x ^ 1 + (-2 / 9) * x ^ 2 +
        (-8 / 3) * x ^ 3 + 1 * x ^ 4 + 0 * x ^ 5 + 0 * x ^ 6 +
          0 * x ^ 7 + 0 * x ^ 8 + 0 * x ^ 9 + 0 * x ^ 10 by
    funext x
    unfold fiveCellEvenPositiveWitness
    ring,
    integral_polynomial_ten]
  norm_num

theorem fiveCellEndpointPairing_oddNegativeWitness :
    fiveCellEndpointPairing fiveCellOddNegativeWitness = -880 / 15309 := by
  unfold fiveCellEndpointPairing
  rw [show (fun x : ℝ ↦ fiveCellOddNegativeWitness x *
      fiveCellOddNegativeWitness (x - 4 / 3)) =
      fun x ↦ 0 * x ^ 0 + (28 / 27) * x ^ 1 + (-13 / 3) * x ^ 2 +
        (80 / 27) * x ^ 3 + (10 / 3) * x ^ 4 + (-4) * x ^ 5 +
          1 * x ^ 6 + 0 * x ^ 7 + 0 * x ^ 8 + 0 * x ^ 9 + 0 * x ^ 10 by
    funext x
    unfold fiveCellOddNegativeWitness
    ring,
    integral_polynomial_ten]
  norm_num

theorem fiveCellEndpointPairing_evenNegativeWitness :
    fiveCellEndpointPairing fiveCellEvenNegativeWitness = -4592 / 885735 := by
  unfold fiveCellEndpointPairing
  rw [show (fun x : ℝ ↦ fiveCellEvenNegativeWitness x *
      fiveCellEvenNegativeWitness (x - 4 / 3)) =
      fun x ↦ (112 / 243) * x ^ 0 + (-608 / 243) * x ^ 1 +
        (632 / 243) * x ^ 2 + (1400 / 243) * x ^ 3 +
          (-959 / 81) * x ^ 4 + (56 / 27) * x ^ 5 +
            (70 / 9) * x ^ 6 + (-16 / 3) * x ^ 7 + 1 * x ^ 8 +
              0 * x ^ 9 + 0 * x ^ 10 by
    funext x
    unfold fiveCellEvenNegativeWitness
    ring,
    integral_polynomial_ten]
  norm_num

theorem fiveCellEndpointPairing_oddPositiveWitness :
    fiveCellEndpointPairing fiveCellOddPositiveWitness =
      180688 / 87687765 := by
  unfold fiveCellEndpointPairing
  rw [show (fun x : ℝ ↦ fiveCellOddPositiveWitness x *
      fiveCellOddPositiveWitness (x - 4 / 3)) =
      fun x ↦ 0 * x ^ 0 + (-448 / 729) * x ^ 1 +
        (2768 / 729) * x ^ 2 + (-4352 / 729) * x ^ 3 +
          (-3704 / 729) * x ^ 4 + (5236 / 243) * x ^ 5 +
            (-1183 / 81) * x ^ 6 + (-224 / 27) * x ^ 7 +
              (134 / 9) * x ^ 8 + (-20 / 3) * x ^ 9 + 1 * x ^ 10 by
    funext x
    unfold fiveCellOddPositiveWitness
    ring,
    integral_polynomial_ten]
  norm_num

/-- Reflection parity alone does not give the endpoint atom a sign: even
endpoint-zero `C¹` profiles realize both signs. -/
theorem fiveCellEndpointPairing_sign_indefinite_even :
    ∃ u v : ℝ → ℝ,
      ContDiff ℝ 1 u ∧ Function.Even u ∧ u (-1) = 0 ∧ u 1 = 0 ∧
      ContDiff ℝ 1 v ∧ Function.Even v ∧ v (-1) = 0 ∧ v 1 = 0 ∧
      0 < fiveCellEndpointPairing u ∧ fiveCellEndpointPairing v < 0 := by
  refine ⟨fiveCellEvenPositiveWitness, fiveCellEvenNegativeWitness,
    fiveCellEvenPositiveWitness_contDiff, fiveCellEvenPositiveWitness_even,
    fiveCellEvenPositiveWitness_endpoints_zero.1,
    fiveCellEvenPositiveWitness_endpoints_zero.2,
    fiveCellEvenNegativeWitness_contDiff, fiveCellEvenNegativeWitness_even,
    fiveCellEvenNegativeWitness_endpoints_zero.1,
    fiveCellEvenNegativeWitness_endpoints_zero.2, ?_, ?_⟩
  · rw [fiveCellEndpointPairing_evenPositiveWitness]
    norm_num
  · rw [fiveCellEndpointPairing_evenNegativeWitness]
    norm_num

/-- The same obstruction occurs inside the odd sector: odd endpoint-zero
`C¹` profiles also realize both signs. -/
theorem fiveCellEndpointPairing_sign_indefinite_odd :
    ∃ u v : ℝ → ℝ,
      ContDiff ℝ 1 u ∧ Function.Odd u ∧ u (-1) = 0 ∧ u 1 = 0 ∧
      ContDiff ℝ 1 v ∧ Function.Odd v ∧ v (-1) = 0 ∧ v 1 = 0 ∧
      fiveCellEndpointPairing u < 0 ∧ 0 < fiveCellEndpointPairing v := by
  refine ⟨fiveCellOddNegativeWitness, fiveCellOddPositiveWitness,
    fiveCellOddNegativeWitness_contDiff, fiveCellOddNegativeWitness_odd,
    fiveCellOddNegativeWitness_endpoints_zero.1,
    fiveCellOddNegativeWitness_endpoints_zero.2,
    fiveCellOddPositiveWitness_contDiff, fiveCellOddPositiveWitness_odd,
    fiveCellOddPositiveWitness_endpoints_zero.1,
    fiveCellOddPositiveWitness_endpoints_zero.2, ?_, ?_⟩
  · rw [fiveCellEndpointPairing_oddNegativeWitness]
    norm_num
  · rw [fiveCellEndpointPairing_oddPositiveWitness]
    norm_num

end

end ArithmeticHodge.Analysis.YoshidaFiveCellEndpointOperatorProbeStructural
