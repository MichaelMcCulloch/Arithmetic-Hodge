import ArithmeticHodge.Analysis.YoshidaFourCellEndpointSquareStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellEndpointHalfFoldStructural

noncomputable section

open YoshidaFourCellEndpointSquareStructural

/-!
# Half-interval fold of the four-cell endpoint channel

Reflection parity turns the matched and antimatched endpoint squares into two
literal trace-channel squares on `[0, 2 / 5]`.  The even and odd sectors swap
the two channels; no absolute-value estimate is used.
-/

/-- The sum of the two positive-half endpoint traces paired by the four-cell
reflection. -/
def fourCellEndpointHalfMatched (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  w (3 / 5 + t) + w (1 - t)

/-- The difference of the same two positive-half endpoint traces. -/
def fourCellEndpointHalfAntimatched (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  w (3 / 5 + t) - w (1 - t)

private theorem matched_shift (w : ℝ → ℝ) :
    fourCellEndpointMatchedSquare w =
      ∫ t : ℝ in 0..2 / 5,
        (w (8 / 5 + (-1 + t)) + w (-1 + t)) ^ 2 := by
  unfold fourCellEndpointMatchedSquare
  have hshift := intervalIntegral.integral_comp_add_left
    (f := fun x : ℝ ↦ (w (8 / 5 + x) + w x) ^ 2)
    (a := (0 : ℝ)) (b := 2 / 5) (-1)
  norm_num at hshift ⊢
  exact hshift.symm

private theorem antimatched_shift (w : ℝ → ℝ) :
    fourCellEndpointAntimatchedSquare w =
      ∫ t : ℝ in 0..2 / 5,
        (w (8 / 5 + (-1 + t)) - w (-1 + t)) ^ 2 := by
  unfold fourCellEndpointAntimatchedSquare
  have hshift := intervalIntegral.integral_comp_add_left
    (f := fun x : ℝ ↦ (w (8 / 5 + x) - w x) ^ 2)
    (a := (0 : ℝ)) (b := 2 / 5) (-1)
  norm_num at hshift ⊢
  exact hshift.symm

/-- Even reflection identifies the full matched endpoint square with the
positive-half matched trace channel. -/
theorem fourCellEndpointMatchedSquare_eq_halfMatched_of_even
    (w : ℝ → ℝ) (heven : Function.Even w) :
    fourCellEndpointMatchedSquare w =
      ∫ t : ℝ in 0..2 / 5, fourCellEndpointHalfMatched w t ^ 2 := by
  rw [matched_shift]
  unfold fourCellEndpointHalfMatched
  apply intervalIntegral.integral_congr
  intro t _ht
  change (w (8 / 5 + (-1 + t)) + w (-1 + t)) ^ 2 =
    (w (3 / 5 + t) + w (1 - t)) ^ 2
  rw [show 8 / 5 + (-1 + t) = 3 / 5 + t by ring,
    show -1 + t = -(1 - t) by ring, heven]

/-- Even reflection identifies the full antimatched endpoint square with the
positive-half antimatched trace channel. -/
theorem fourCellEndpointAntimatchedSquare_eq_halfAntimatched_of_even
    (w : ℝ → ℝ) (heven : Function.Even w) :
    fourCellEndpointAntimatchedSquare w =
      ∫ t : ℝ in 0..2 / 5,
        fourCellEndpointHalfAntimatched w t ^ 2 := by
  rw [antimatched_shift]
  unfold fourCellEndpointHalfAntimatched
  apply intervalIntegral.integral_congr
  intro t _ht
  change (w (8 / 5 + (-1 + t)) - w (-1 + t)) ^ 2 =
    (w (3 / 5 + t) - w (1 - t)) ^ 2
  rw [show 8 / 5 + (-1 + t) = 3 / 5 + t by ring,
    show -1 + t = -(1 - t) by ring, heven]

/-- Odd reflection swaps the full matched endpoint square into the
positive-half antimatched trace channel. -/
theorem fourCellEndpointMatchedSquare_eq_halfAntimatched_of_odd
    (w : ℝ → ℝ) (hodd : Function.Odd w) :
    fourCellEndpointMatchedSquare w =
      ∫ t : ℝ in 0..2 / 5,
        fourCellEndpointHalfAntimatched w t ^ 2 := by
  rw [matched_shift]
  unfold fourCellEndpointHalfAntimatched
  apply intervalIntegral.integral_congr
  intro t _ht
  change (w (8 / 5 + (-1 + t)) + w (-1 + t)) ^ 2 =
    (w (3 / 5 + t) - w (1 - t)) ^ 2
  rw [show 8 / 5 + (-1 + t) = 3 / 5 + t by ring,
    show -1 + t = -(1 - t) by ring, hodd]
  ring

/-- Odd reflection swaps the full antimatched endpoint square into the
positive-half matched trace channel. -/
theorem fourCellEndpointAntimatchedSquare_eq_halfMatched_of_odd
    (w : ℝ → ℝ) (hodd : Function.Odd w) :
    fourCellEndpointAntimatchedSquare w =
      ∫ t : ℝ in 0..2 / 5, fourCellEndpointHalfMatched w t ^ 2 := by
  rw [antimatched_shift]
  unfold fourCellEndpointHalfMatched
  apply intervalIntegral.integral_congr
  intro t _ht
  change (w (8 / 5 + (-1 + t)) - w (-1 + t)) ^ 2 =
    (w (3 / 5 + t) + w (1 - t)) ^ 2
  rw [show 8 / 5 + (-1 + t) = 3 / 5 + t by ring,
    show -1 + t = -(1 - t) by ring, hodd]
  ring

end

end ArithmeticHodge.Analysis.YoshidaFourCellEndpointHalfFoldStructural
