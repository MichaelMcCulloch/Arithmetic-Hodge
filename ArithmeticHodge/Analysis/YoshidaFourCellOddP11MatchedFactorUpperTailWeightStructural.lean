import ArithmeticHodge.Analysis.YoshidaFourCellOddP11MatchedFactorObstructionStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11MatchedFactorUpperTailWeightStructural

noncomputable section

open EndpointPotentialPolynomialPairBilinearStructural
open ShiftedLegendreCenteredLowModes
open ShiftedLegendreOrthogonality
open YoshidaConstantBounds
open YoshidaEndpointPotentialLegendreDiagonalStructural
open YoshidaEndpointPotentialLegendreOffDiagonalStructural
open YoshidaFourCellOddP11CoupledRieszDefectClosureStructural
open YoshidaFourCellOddP11MatchedFactorObstructionStructural
open YoshidaFourCellOddP1OrthogonalFormDualClosureStructural

/-!
# Exact scalar weight of the matched-factor upper-tail packet

The ordinary strip terms are evaluated from one exact power-basis identity.
The endpoint-potential term is kept in the Legendre basis: its diagonal is
controlled by the all-degree Jacobi recurrence and every off-diagonal entry
by the all-degree spectral-gap formula.  No sampled coefficient matrix or
finite spectral search is used.
-/

/-- The even quotient after factoring the odd packet by the centered
coordinate. -/
def fourCellOddP11MatchedFactorUpperTailReduced (x : ℝ) : ℝ :=
  (-3184919 / 4194304 : ℝ) +
    (226595395 / 1048576 : ℝ) * x ^ 2 -
    (16919145243 / 2097152 : ℝ) * x ^ 4 +
    (134884669491 / 1048576 : ℝ) * x ^ 6 -
    (4741182837105 / 4194304 : ℝ) * x ^ 8 +
    (3199537009851 / 524288 : ℝ) * x ^ 10 -
    (22466334759925 / 1048576 : ℝ) * x ^ 12 +
    (26400875871015 / 524288 : ℝ) * x ^ 14 -
    (334967587023465 / 4194304 : ℝ) * x ^ 16 +
    (88438268185575 / 1048576 : ℝ) * x ^ 18 -
    (119156836954155 / 2097152 : ℝ) * x ^ 20 +
    (23156523921375 / 1048576 : ℝ) * x ^ 22 -
    (15801325804719 / 4194304 : ℝ) * x ^ 24

set_option maxHeartbeats 2000000 in
/-- Exact odd factorization of the eight-mode packet. -/
theorem fourCellOddP11MatchedFactorUpperTail_eq_mul_reduced (x : ℝ) :
    fourCellOddP11MatchedFactorUpperTail x =
      x * fourCellOddP11MatchedFactorUpperTailReduced x := by
  unfold fourCellOddP11MatchedFactorUpperTail
    fourCellOddP11MatchedFactorUpperTailPolynomial
    fourCellOddP11MatchedFactorUpperTailReduced
  norm_num [centeredShiftedLegendreReal, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_comp, Polynomial.eval_map,
    Polynomial.eval_finset_sum, Finset.sum_range_succ, Nat.choose,
    Polynomial.smul_eq_C_mul]
  ring

set_option maxHeartbeats 2000000 in
/-- Exact lower-strip square mass of the packet. -/
theorem fourCellOddP11MatchedFactorUpperTail_lowerStrip_sq_eq :
    (∫ x : ℝ in 0..3 / 5,
      fourCellOddP11MatchedFactorUpperTail x ^ 2) =
      (7638620412835750174405230398174102746605672 /
        989957107844219308390165679156780242919921875 : ℝ) := by
  simp_rw [fourCellOddP11MatchedFactorUpperTail_eq_mul_reduced]
  unfold fourCellOddP11MatchedFactorUpperTailReduced
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 (3 / 5))
    (Continuous.intervalIntegrable (by fun_prop) 0 (3 / 5))]
  norm_num

set_option maxHeartbeats 2000000 in
/-- Exact upper-strip square mass of the packet. -/
theorem fourCellOddP11MatchedFactorUpperTail_upperStrip_sq_eq :
    (∫ x : ℝ in 3 / 5..1,
      fourCellOddP11MatchedFactorUpperTail x ^ 2) =
      (5971489421427658768555891573915589509044771856 /
        26728841911793921326534473337233066558837890625 : ℝ) := by
  simp_rw [fourCellOddP11MatchedFactorUpperTail_eq_mul_reduced]
  unfold fourCellOddP11MatchedFactorUpperTailReduced
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (3 / 5) 1)
    (Continuous.intervalIntegrable (by fun_prop) (3 / 5) 1)]
  norm_num

set_option maxHeartbeats 2000000 in
/-- Exact reciprocal upper-strip mass; oddness removes the apparent pole. -/
theorem fourCellOddP11MatchedFactorUpperTail_upperStrip_sq_div_eq :
    (∫ x : ℝ in 3 / 5..1,
      fourCellOddP11MatchedFactorUpperTail x ^ 2 / x) =
      (11367055594804610892181850192403970112882176 /
        49536568180741369360475800931453704833984375 : ℝ) := by
  simp_rw [fourCellOddP11MatchedFactorUpperTail_eq_mul_reduced]
  rw [show (fun x : ℝ ↦
      (x * fourCellOddP11MatchedFactorUpperTailReduced x) ^ 2 / x) =
    fun x ↦ x * fourCellOddP11MatchedFactorUpperTailReduced x ^ 2 by
      funext x
      by_cases hx : x = 0
      · simp [hx]
      · field_simp [hx]]
  unfold fourCellOddP11MatchedFactorUpperTailReduced
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (3 / 5) 1)
    (Continuous.intervalIntegrable (by fun_prop) (3 / 5) 1)]
  norm_num

/-- Exact positive-half square mass, also obtainable by summing the eight
all-degree Legendre norms. -/
theorem fourCellOddP11MatchedFactorUpperTail_positiveHalf_sq_eq :
    (∫ x : ℝ in 0..1,
      fourCellOddP11MatchedFactorUpperTail x ^ 2) =
      (69555080776 / 300940006185 : ℝ) := by
  have hcont : Continuous (fun x : ℝ ↦
      fourCellOddP11MatchedFactorUpperTail x ^ 2) :=
    contDiff_fourCellOddP11MatchedFactorUpperTail.continuous.pow 2
  have hL : IntervalIntegrable (fun x : ℝ ↦
      fourCellOddP11MatchedFactorUpperTail x ^ 2)
      volume 0 (3 / 5) := hcont.intervalIntegrable 0 (3 / 5)
  have hU : IntervalIntegrable (fun x : ℝ ↦
      fourCellOddP11MatchedFactorUpperTail x ^ 2)
      volume (3 / 5) 1 := hcont.intervalIntegrable (3 / 5) 1
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hL hU
  calc
    (∫ x : ℝ in 0..1,
        fourCellOddP11MatchedFactorUpperTail x ^ 2) =
        (∫ x : ℝ in 0..3 / 5,
          fourCellOddP11MatchedFactorUpperTail x ^ 2) +
          ∫ x : ℝ in 3 / 5..1,
            fourCellOddP11MatchedFactorUpperTail x ^ 2 := hsplit.symm
    _ = (69555080776 / 300940006185 : ℝ) := by
      rw [fourCellOddP11MatchedFactorUpperTail_lowerStrip_sq_eq,
        fourCellOddP11MatchedFactorUpperTail_upperStrip_sq_eq]
      norm_num

/-! ## Structural endpoint-potential certificate -/

/-- A recursively generated strict lower certificate for every diagonal.
The recurrence is the same all-degree Jacobi recurrence as the true
endpoint-potential diagonal; only its degree-zero seed is rationalized. -/
private def matchedFactorEndpointDiagonalLower : ℕ → ℝ
  | 0 => 61370563 / 100000000
  | n + 1 =>
      ((2 * (n : ℝ) + 1) * matchedFactorEndpointDiagonalLower n +
        2 / ((n + 1 : ℝ) * (2 * (n : ℝ) + 1) *
          (2 * (n : ℝ) + 3))) /
        (2 * (n : ℝ) + 3)

private theorem matchedFactorEndpointDiagonalLower_lt (n : ℕ) :
    matchedFactorEndpointDiagonalLower n <
      endpointPotentialLegendreDiagonal n := by
  induction n with
  | zero =>
      rw [matchedFactorEndpointDiagonalLower,
        endpointPotentialLegendreDiagonal_zero]
      linarith [strict_log_two_fine_bounds.2]
  | succ n ih =>
      rw [matchedFactorEndpointDiagonalLower]
      have hrec := endpointPotentialLegendreDiagonal_succ n
      have hcoef : 0 < 2 * (n : ℝ) + 1 := by positivity
      have hden : 0 < 2 * (n : ℝ) + 3 := by positivity
      apply (div_lt_iff₀ hden).2
      calc
        (2 * (n : ℝ) + 1) * matchedFactorEndpointDiagonalLower n +
              2 / ((n + 1 : ℝ) * (2 * (n : ℝ) + 1) *
                (2 * (n : ℝ) + 3)) <
            (2 * (n : ℝ) + 1) * endpointPotentialLegendreDiagonal n +
              2 / ((n + 1 : ℝ) * (2 * (n : ℝ) + 1) *
                (2 * (n : ℝ) + 3)) :=
          add_lt_add_left (mul_lt_mul_of_pos_left ih hcoef) _
        _ = endpointPotentialLegendreDiagonal (n + 1) *
              (2 * (n : ℝ) + 3) := by
          simpa only [mul_comm (2 * (n : ℝ) + 3)
            (endpointPotentialLegendreDiagonal (n + 1))] using hrec.symm

/-- The matching recursively generated upper diagonal certificate. -/
private def matchedFactorEndpointDiagonalUpper : ℕ → ℝ
  | 0 => 61370564 / 100000000
  | n + 1 =>
      ((2 * (n : ℝ) + 1) * matchedFactorEndpointDiagonalUpper n +
        2 / ((n + 1 : ℝ) * (2 * (n : ℝ) + 1) *
          (2 * (n : ℝ) + 3))) /
        (2 * (n : ℝ) + 3)

private theorem endpointPotentialLegendreDiagonal_lt_matchedFactorUpper
    (n : ℕ) :
    endpointPotentialLegendreDiagonal n <
      matchedFactorEndpointDiagonalUpper n := by
  induction n with
  | zero =>
      rw [matchedFactorEndpointDiagonalUpper,
        endpointPotentialLegendreDiagonal_zero]
      linarith [strict_log_two_fine_bounds.1]
  | succ n ih =>
      rw [matchedFactorEndpointDiagonalUpper]
      have hrec := endpointPotentialLegendreDiagonal_succ n
      have hcoef : 0 < 2 * (n : ℝ) + 1 := by positivity
      have hden : 0 < 2 * (n : ℝ) + 3 := by positivity
      apply (lt_div_iff₀ hden).2
      calc
        endpointPotentialLegendreDiagonal (n + 1) *
              (2 * (n : ℝ) + 3) =
            (2 * (n : ℝ) + 3) *
              endpointPotentialLegendreDiagonal (n + 1) := by ring
        _ = (2 * (n : ℝ) + 1) * endpointPotentialLegendreDiagonal n +
              2 / ((n + 1 : ℝ) * (2 * (n : ℝ) + 1) *
                (2 * (n : ℝ) + 3)) := hrec
        _ < (2 * (n : ℝ) + 1) * matchedFactorEndpointDiagonalUpper n +
              2 / ((n + 1 : ℝ) * (2 * (n : ℝ) + 1) *
                (2 * (n : ℝ) + 3)) :=
          add_lt_add_left (mul_lt_mul_of_pos_left ih hcoef) _

private theorem endpointPotentialPolynomialPair_odd_offDiagonal
    {m n : ℕ} (hmn : m < n) (heven : Even (m + n)) :
    endpointPotentialPolynomialPair
        (centeredShiftedLegendreReal m)
        (centeredShiftedLegendreReal n) =
      2 / (((n : ℝ) - m) * ((n : ℝ) + m + 1)) := by
  simpa only [endpointPotentialPolynomialPair] using
    integral_endpointPotential_mul_centeredShiftedLegendreReal_of_even
      hmn heven

private theorem endpointPotentialPolynomialPair_upperTail_expansion :
    endpointPotentialPolynomialPair
        fourCellOddP11MatchedFactorUpperTailPolynomial
        fourCellOddP11MatchedFactorUpperTailPolynomial =
      endpointPotentialLegendreDiagonal 11 +
        endpointPotentialLegendreDiagonal 13 +
        endpointPotentialLegendreDiagonal 15 +
        endpointPotentialLegendreDiagonal 17 +
        endpointPotentialLegendreDiagonal 19 +
        endpointPotentialLegendreDiagonal 21 +
        endpointPotentialLegendreDiagonal 23 +
        endpointPotentialLegendreDiagonal 25 +
        2 * (
          endpointPotentialPolynomialPair
              (centeredShiftedLegendreReal 11)
              (centeredShiftedLegendreReal 13) +
          endpointPotentialPolynomialPair
              (centeredShiftedLegendreReal 11)
              (centeredShiftedLegendreReal 15) +
          endpointPotentialPolynomialPair
              (centeredShiftedLegendreReal 11)
              (centeredShiftedLegendreReal 17) +
          endpointPotentialPolynomialPair
              (centeredShiftedLegendreReal 11)
              (centeredShiftedLegendreReal 19) +
          endpointPotentialPolynomialPair
              (centeredShiftedLegendreReal 11)
              (centeredShiftedLegendreReal 21) +
          endpointPotentialPolynomialPair
              (centeredShiftedLegendreReal 11)
              (centeredShiftedLegendreReal 23) +
          endpointPotentialPolynomialPair
              (centeredShiftedLegendreReal 11)
              (centeredShiftedLegendreReal 25) +
          endpointPotentialPolynomialPair
              (centeredShiftedLegendreReal 13)
              (centeredShiftedLegendreReal 15) +
          endpointPotentialPolynomialPair
              (centeredShiftedLegendreReal 13)
              (centeredShiftedLegendreReal 17) +
          endpointPotentialPolynomialPair
              (centeredShiftedLegendreReal 13)
              (centeredShiftedLegendreReal 19) +
          endpointPotentialPolynomialPair
              (centeredShiftedLegendreReal 13)
              (centeredShiftedLegendreReal 21) +
          endpointPotentialPolynomialPair
              (centeredShiftedLegendreReal 13)
              (centeredShiftedLegendreReal 23) +
          endpointPotentialPolynomialPair
              (centeredShiftedLegendreReal 13)
              (centeredShiftedLegendreReal 25) +
          endpointPotentialPolynomialPair
              (centeredShiftedLegendreReal 15)
              (centeredShiftedLegendreReal 17) +
          endpointPotentialPolynomialPair
              (centeredShiftedLegendreReal 15)
              (centeredShiftedLegendreReal 19) +
          endpointPotentialPolynomialPair
              (centeredShiftedLegendreReal 15)
              (centeredShiftedLegendreReal 21) +
          endpointPotentialPolynomialPair
              (centeredShiftedLegendreReal 15)
              (centeredShiftedLegendreReal 23) +
          endpointPotentialPolynomialPair
              (centeredShiftedLegendreReal 15)
              (centeredShiftedLegendreReal 25) +
          endpointPotentialPolynomialPair
              (centeredShiftedLegendreReal 17)
              (centeredShiftedLegendreReal 19) +
          endpointPotentialPolynomialPair
              (centeredShiftedLegendreReal 17)
              (centeredShiftedLegendreReal 21) +
          endpointPotentialPolynomialPair
              (centeredShiftedLegendreReal 17)
              (centeredShiftedLegendreReal 23) +
          endpointPotentialPolynomialPair
              (centeredShiftedLegendreReal 17)
              (centeredShiftedLegendreReal 25) +
          endpointPotentialPolynomialPair
              (centeredShiftedLegendreReal 19)
              (centeredShiftedLegendreReal 21) +
          endpointPotentialPolynomialPair
              (centeredShiftedLegendreReal 19)
              (centeredShiftedLegendreReal 23) +
          endpointPotentialPolynomialPair
              (centeredShiftedLegendreReal 19)
              (centeredShiftedLegendreReal 25) +
          endpointPotentialPolynomialPair
              (centeredShiftedLegendreReal 21)
              (centeredShiftedLegendreReal 23) +
          endpointPotentialPolynomialPair
              (centeredShiftedLegendreReal 21)
              (centeredShiftedLegendreReal 25) +
          endpointPotentialPolynomialPair
              (centeredShiftedLegendreReal 23)
              (centeredShiftedLegendreReal 25)) := by
  unfold fourCellOddP11MatchedFactorUpperTailPolynomial
    endpointPotentialLegendreDiagonal
  simp only [endpointPotentialPolynomialPair_add_left,
    endpointPotentialPolynomialPair_add_right]
  rw [endpointPotentialPolynomialPair_comm
      (centeredShiftedLegendreReal 13) (centeredShiftedLegendreReal 11),
    endpointPotentialPolynomialPair_comm
      (centeredShiftedLegendreReal 15) (centeredShiftedLegendreReal 11),
    endpointPotentialPolynomialPair_comm
      (centeredShiftedLegendreReal 15) (centeredShiftedLegendreReal 13),
    endpointPotentialPolynomialPair_comm
      (centeredShiftedLegendreReal 17) (centeredShiftedLegendreReal 11),
    endpointPotentialPolynomialPair_comm
      (centeredShiftedLegendreReal 17) (centeredShiftedLegendreReal 13),
    endpointPotentialPolynomialPair_comm
      (centeredShiftedLegendreReal 17) (centeredShiftedLegendreReal 15),
    endpointPotentialPolynomialPair_comm
      (centeredShiftedLegendreReal 19) (centeredShiftedLegendreReal 11),
    endpointPotentialPolynomialPair_comm
      (centeredShiftedLegendreReal 19) (centeredShiftedLegendreReal 13),
    endpointPotentialPolynomialPair_comm
      (centeredShiftedLegendreReal 19) (centeredShiftedLegendreReal 15),
    endpointPotentialPolynomialPair_comm
      (centeredShiftedLegendreReal 19) (centeredShiftedLegendreReal 17),
    endpointPotentialPolynomialPair_comm
      (centeredShiftedLegendreReal 21) (centeredShiftedLegendreReal 11),
    endpointPotentialPolynomialPair_comm
      (centeredShiftedLegendreReal 21) (centeredShiftedLegendreReal 13),
    endpointPotentialPolynomialPair_comm
      (centeredShiftedLegendreReal 21) (centeredShiftedLegendreReal 15),
    endpointPotentialPolynomialPair_comm
      (centeredShiftedLegendreReal 21) (centeredShiftedLegendreReal 17),
    endpointPotentialPolynomialPair_comm
      (centeredShiftedLegendreReal 21) (centeredShiftedLegendreReal 19),
    endpointPotentialPolynomialPair_comm
      (centeredShiftedLegendreReal 23) (centeredShiftedLegendreReal 11),
    endpointPotentialPolynomialPair_comm
      (centeredShiftedLegendreReal 23) (centeredShiftedLegendreReal 13),
    endpointPotentialPolynomialPair_comm
      (centeredShiftedLegendreReal 23) (centeredShiftedLegendreReal 15),
    endpointPotentialPolynomialPair_comm
      (centeredShiftedLegendreReal 23) (centeredShiftedLegendreReal 17),
    endpointPotentialPolynomialPair_comm
      (centeredShiftedLegendreReal 23) (centeredShiftedLegendreReal 19),
    endpointPotentialPolynomialPair_comm
      (centeredShiftedLegendreReal 23) (centeredShiftedLegendreReal 21),
    endpointPotentialPolynomialPair_comm
      (centeredShiftedLegendreReal 25) (centeredShiftedLegendreReal 11),
    endpointPotentialPolynomialPair_comm
      (centeredShiftedLegendreReal 25) (centeredShiftedLegendreReal 13),
    endpointPotentialPolynomialPair_comm
      (centeredShiftedLegendreReal 25) (centeredShiftedLegendreReal 15),
    endpointPotentialPolynomialPair_comm
      (centeredShiftedLegendreReal 25) (centeredShiftedLegendreReal 17),
    endpointPotentialPolynomialPair_comm
      (centeredShiftedLegendreReal 25) (centeredShiftedLegendreReal 19),
    endpointPotentialPolynomialPair_comm
      (centeredShiftedLegendreReal 25) (centeredShiftedLegendreReal 21),
    endpointPotentialPolynomialPair_comm
      (centeredShiftedLegendreReal 25) (centeredShiftedLegendreReal 23)]
  ring

/-- The endpoint-potential pair of the packet is bounded below using only
the uniform diagonal recurrence and the uniform off-diagonal formula. -/
theorem endpointPotentialPolynomialPair_upperTail_gt_1091 :
    (1091 / 1000 : ℝ) <
      endpointPotentialPolynomialPair
        fourCellOddP11MatchedFactorUpperTailPolynomial
        fourCellOddP11MatchedFactorUpperTailPolynomial := by
  have h11 : (6019 / 100000 : ℝ) <
      endpointPotentialLegendreDiagonal 11 := by
    exact (show (6019 / 100000 : ℝ) <
      matchedFactorEndpointDiagonalLower 11 by
        norm_num [matchedFactorEndpointDiagonalLower]).trans
          (matchedFactorEndpointDiagonalLower_lt 11)
  have h13 : (5129 / 100000 : ℝ) <
      endpointPotentialLegendreDiagonal 13 := by
    exact (show (5129 / 100000 : ℝ) <
      matchedFactorEndpointDiagonalLower 13 by
        norm_num [matchedFactorEndpointDiagonalLower]).trans
          (matchedFactorEndpointDiagonalLower_lt 13)
  have h15 : (4468 / 100000 : ℝ) <
      endpointPotentialLegendreDiagonal 15 := by
    exact (show (4468 / 100000 : ℝ) <
      matchedFactorEndpointDiagonalLower 15 by
        norm_num [matchedFactorEndpointDiagonalLower]).trans
          (matchedFactorEndpointDiagonalLower_lt 15)
  have h17 : (3958 / 100000 : ℝ) <
      endpointPotentialLegendreDiagonal 17 := by
    exact (show (3958 / 100000 : ℝ) <
      matchedFactorEndpointDiagonalLower 17 by
        norm_num [matchedFactorEndpointDiagonalLower]).trans
          (matchedFactorEndpointDiagonalLower_lt 17)
  have h19 : (3552 / 100000 : ℝ) <
      endpointPotentialLegendreDiagonal 19 := by
    exact (show (3552 / 100000 : ℝ) <
      matchedFactorEndpointDiagonalLower 19 by
        norm_num [matchedFactorEndpointDiagonalLower]).trans
          (matchedFactorEndpointDiagonalLower_lt 19)
  have h21 : (3222 / 100000 : ℝ) <
      endpointPotentialLegendreDiagonal 21 := by
    exact (show (3222 / 100000 : ℝ) <
      matchedFactorEndpointDiagonalLower 21 by
        norm_num [matchedFactorEndpointDiagonalLower]).trans
          (matchedFactorEndpointDiagonalLower_lt 21)
  have h23 : (2948 / 100000 : ℝ) <
      endpointPotentialLegendreDiagonal 23 := by
    exact (show (2948 / 100000 : ℝ) <
      matchedFactorEndpointDiagonalLower 23 by
        norm_num [matchedFactorEndpointDiagonalLower]).trans
          (matchedFactorEndpointDiagonalLower_lt 23)
  have h25 : (2717 / 100000 : ℝ) <
      endpointPotentialLegendreDiagonal 25 := by
    exact (show (2717 / 100000 : ℝ) <
      matchedFactorEndpointDiagonalLower 25 by
        norm_num [matchedFactorEndpointDiagonalLower]).trans
          (matchedFactorEndpointDiagonalLower_lt 25)
  rw [endpointPotentialPolynomialPair_upperTail_expansion,
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 11) (n := 13) (by omega)
        (by norm_num : Even (11 + 13)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 11) (n := 15) (by omega)
        (by norm_num : Even (11 + 15)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 11) (n := 17) (by omega)
        (by norm_num : Even (11 + 17)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 11) (n := 19) (by omega)
        (by norm_num : Even (11 + 19)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 11) (n := 21) (by omega)
        (by norm_num : Even (11 + 21)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 11) (n := 23) (by omega)
        (by norm_num : Even (11 + 23)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 11) (n := 25) (by omega)
        (by norm_num : Even (11 + 25)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 13) (n := 15) (by omega)
        (by norm_num : Even (13 + 15)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 13) (n := 17) (by omega)
        (by norm_num : Even (13 + 17)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 13) (n := 19) (by omega)
        (by norm_num : Even (13 + 19)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 13) (n := 21) (by omega)
        (by norm_num : Even (13 + 21)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 13) (n := 23) (by omega)
        (by norm_num : Even (13 + 23)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 13) (n := 25) (by omega)
        (by norm_num : Even (13 + 25)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 15) (n := 17) (by omega)
        (by norm_num : Even (15 + 17)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 15) (n := 19) (by omega)
        (by norm_num : Even (15 + 19)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 15) (n := 21) (by omega)
        (by norm_num : Even (15 + 21)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 15) (n := 23) (by omega)
        (by norm_num : Even (15 + 23)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 15) (n := 25) (by omega)
        (by norm_num : Even (15 + 25)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 17) (n := 19) (by omega)
        (by norm_num : Even (17 + 19)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 17) (n := 21) (by omega)
        (by norm_num : Even (17 + 21)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 17) (n := 23) (by omega)
        (by norm_num : Even (17 + 23)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 17) (n := 25) (by omega)
        (by norm_num : Even (17 + 25)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 19) (n := 21) (by omega)
        (by norm_num : Even (19 + 21)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 19) (n := 23) (by omega)
        (by norm_num : Even (19 + 23)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 19) (n := 25) (by omega)
        (by norm_num : Even (19 + 25)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 21) (n := 23) (by omega)
        (by norm_num : Even (21 + 23)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 21) (n := 25) (by omega)
        (by norm_num : Even (21 + 25)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 23) (n := 25) (by omega)
        (by norm_num : Even (23 + 25))]
  norm_num only [Nat.cast_ofNat]
  linarith

/-- Matching upper enclosure for the packet endpoint-potential pair. -/
theorem endpointPotentialPolynomialPair_upperTail_lt_273_div_250 :
    endpointPotentialPolynomialPair
        fourCellOddP11MatchedFactorUpperTailPolynomial
        fourCellOddP11MatchedFactorUpperTailPolynomial <
      (273 / 250 : ℝ) := by
  have h11 : endpointPotentialLegendreDiagonal 11 <
      (6020 / 100000 : ℝ) := by
    exact (endpointPotentialLegendreDiagonal_lt_matchedFactorUpper 11).trans
      (show matchedFactorEndpointDiagonalUpper 11 <
        (6020 / 100000 : ℝ) by
          norm_num [matchedFactorEndpointDiagonalUpper])
  have h13 : endpointPotentialLegendreDiagonal 13 <
      (5130 / 100000 : ℝ) := by
    exact (endpointPotentialLegendreDiagonal_lt_matchedFactorUpper 13).trans
      (show matchedFactorEndpointDiagonalUpper 13 <
        (5130 / 100000 : ℝ) by
          norm_num [matchedFactorEndpointDiagonalUpper])
  have h15 : endpointPotentialLegendreDiagonal 15 <
      (4469 / 100000 : ℝ) := by
    exact (endpointPotentialLegendreDiagonal_lt_matchedFactorUpper 15).trans
      (show matchedFactorEndpointDiagonalUpper 15 <
        (4469 / 100000 : ℝ) by
          norm_num [matchedFactorEndpointDiagonalUpper])
  have h17 : endpointPotentialLegendreDiagonal 17 <
      (3959 / 100000 : ℝ) := by
    exact (endpointPotentialLegendreDiagonal_lt_matchedFactorUpper 17).trans
      (show matchedFactorEndpointDiagonalUpper 17 <
        (3959 / 100000 : ℝ) by
          norm_num [matchedFactorEndpointDiagonalUpper])
  have h19 : endpointPotentialLegendreDiagonal 19 <
      (3553 / 100000 : ℝ) := by
    exact (endpointPotentialLegendreDiagonal_lt_matchedFactorUpper 19).trans
      (show matchedFactorEndpointDiagonalUpper 19 <
        (3553 / 100000 : ℝ) by
          norm_num [matchedFactorEndpointDiagonalUpper])
  have h21 : endpointPotentialLegendreDiagonal 21 <
      (3223 / 100000 : ℝ) := by
    exact (endpointPotentialLegendreDiagonal_lt_matchedFactorUpper 21).trans
      (show matchedFactorEndpointDiagonalUpper 21 <
        (3223 / 100000 : ℝ) by
          norm_num [matchedFactorEndpointDiagonalUpper])
  have h23 : endpointPotentialLegendreDiagonal 23 <
      (2949 / 100000 : ℝ) := by
    exact (endpointPotentialLegendreDiagonal_lt_matchedFactorUpper 23).trans
      (show matchedFactorEndpointDiagonalUpper 23 <
        (2949 / 100000 : ℝ) by
          norm_num [matchedFactorEndpointDiagonalUpper])
  have h25 : endpointPotentialLegendreDiagonal 25 <
      (2718 / 100000 : ℝ) := by
    exact (endpointPotentialLegendreDiagonal_lt_matchedFactorUpper 25).trans
      (show matchedFactorEndpointDiagonalUpper 25 <
        (2718 / 100000 : ℝ) by
          norm_num [matchedFactorEndpointDiagonalUpper])
  rw [endpointPotentialPolynomialPair_upperTail_expansion,
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 11) (n := 13) (by omega)
        (by norm_num : Even (11 + 13)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 11) (n := 15) (by omega)
        (by norm_num : Even (11 + 15)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 11) (n := 17) (by omega)
        (by norm_num : Even (11 + 17)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 11) (n := 19) (by omega)
        (by norm_num : Even (11 + 19)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 11) (n := 21) (by omega)
        (by norm_num : Even (11 + 21)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 11) (n := 23) (by omega)
        (by norm_num : Even (11 + 23)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 11) (n := 25) (by omega)
        (by norm_num : Even (11 + 25)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 13) (n := 15) (by omega)
        (by norm_num : Even (13 + 15)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 13) (n := 17) (by omega)
        (by norm_num : Even (13 + 17)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 13) (n := 19) (by omega)
        (by norm_num : Even (13 + 19)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 13) (n := 21) (by omega)
        (by norm_num : Even (13 + 21)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 13) (n := 23) (by omega)
        (by norm_num : Even (13 + 23)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 13) (n := 25) (by omega)
        (by norm_num : Even (13 + 25)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 15) (n := 17) (by omega)
        (by norm_num : Even (15 + 17)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 15) (n := 19) (by omega)
        (by norm_num : Even (15 + 19)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 15) (n := 21) (by omega)
        (by norm_num : Even (15 + 21)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 15) (n := 23) (by omega)
        (by norm_num : Even (15 + 23)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 15) (n := 25) (by omega)
        (by norm_num : Even (15 + 25)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 17) (n := 19) (by omega)
        (by norm_num : Even (17 + 19)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 17) (n := 21) (by omega)
        (by norm_num : Even (17 + 21)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 17) (n := 23) (by omega)
        (by norm_num : Even (17 + 23)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 17) (n := 25) (by omega)
        (by norm_num : Even (17 + 25)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 19) (n := 21) (by omega)
        (by norm_num : Even (19 + 21)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 19) (n := 23) (by omega)
        (by norm_num : Even (19 + 23)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 19) (n := 25) (by omega)
        (by norm_num : Even (19 + 25)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 21) (n := 23) (by omega)
        (by norm_num : Even (21 + 23)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 21) (n := 25) (by omega)
        (by norm_num : Even (21 + 25)),
    endpointPotentialPolynomialPair_odd_offDiagonal
      (m := 23) (n := 25) (by omega)
        (by norm_num : Even (23 + 25))]
  norm_num only [Nat.cast_ofNat]
  linarith

/-- Directly scaled form used by the matched-factor core estimate. -/
theorem ninetyThree_hundredths_mul_endpointPotentialPair_upperTail_lt :
    (93 / 100 : ℝ) * endpointPotentialPolynomialPair
        fourCellOddP11MatchedFactorUpperTailPolynomial
        fourCellOddP11MatchedFactorUpperTailPolynomial <
      (51 / 50 : ℝ) := by
  calc
    (93 / 100 : ℝ) * endpointPotentialPolynomialPair
          fourCellOddP11MatchedFactorUpperTailPolynomial
          fourCellOddP11MatchedFactorUpperTailPolynomial <
        (93 / 100 : ℝ) * (273 / 250 : ℝ) :=
      mul_lt_mul_of_pos_left
        endpointPotentialPolynomialPair_upperTail_lt_273_div_250 (by norm_num)
    _ < (51 / 50 : ℝ) := by norm_num

/-- The exact scalar tail weight of the eight-mode packet is strictly above
`39 / 50`.  This is the upper-factor obstruction threshold. -/
theorem thirtyNine_fiftieths_lt_fourCellOddP1ExactTailWeight_upperTail :
    (39 / 50 : ℝ) <
      fourCellOddP1ExactTailWeight
        fourCellOddP11MatchedFactorUpperTail := by
  have hformula :
      fourCellOddP1ExactTailWeight
          fourCellOddP11MatchedFactorUpperTail =
        (27 / 250 : ℝ) * (∫ x : ℝ in 0..3 / 5,
          fourCellOddP11MatchedFactorUpperTail x ^ 2) +
        (93 / 100 : ℝ) * endpointPotentialPolynomialPair
          fourCellOddP11MatchedFactorUpperTailPolynomial
          fourCellOddP11MatchedFactorUpperTailPolynomial +
        (6 / 5 : ℝ) * (∫ x : ℝ in 3 / 5..1,
          fourCellOddP11MatchedFactorUpperTail x ^ 2 / x) -
        (57 / 25 : ℝ) * (∫ x : ℝ in 3 / 5..1,
          fourCellOddP11MatchedFactorUpperTail x ^ 2) := by
    simpa only [fourCellOddP11MatchedFactorUpperTail] using
      fourCellOddP1ExactTailWeight_polynomial_eq
        fourCellOddP11MatchedFactorUpperTailPolynomial
        odd_fourCellOddP11MatchedFactorUpperTail
  rw [hformula,
    fourCellOddP11MatchedFactorUpperTail_lowerStrip_sq_eq,
    fourCellOddP11MatchedFactorUpperTail_upperStrip_sq_div_eq,
    fourCellOddP11MatchedFactorUpperTail_upperStrip_sq_eq]
  linarith [endpointPotentialPolynomialPair_upperTail_gt_1091]

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11MatchedFactorUpperTailWeightStructural
