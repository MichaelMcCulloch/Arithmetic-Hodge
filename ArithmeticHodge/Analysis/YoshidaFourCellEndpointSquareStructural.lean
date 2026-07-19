import ArithmeticHodge.Analysis.YoshidaFourCellWidthPerturbationStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSingularSquare

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellEndpointSquareStructural

noncomputable section

open CenteredEndpointCorrelation
open MultiplicativeWeil
open MultiplicativeWeilFourCellRealDiagonalStructural
open MultiplicativeWeilFourCellRealRescaleStructural
open MultiplicativeWeilFourCellSingleProfileStructural
open MultiplicativeWeilMonotoneFourCellPrimeGeometryStructural
open YoshidaEndpointBoundaryTailFold
open YoshidaEndpointSingularCorrelation
open YoshidaEndpointTriangleFoldLipschitz
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseEnvelope
open YoshidaFactorTwoPhaseSingularSquare
open YoshidaFourCellEndpointVarianceStructural
open YoshidaGeneralEndpointPhysicalRealQuadraticStructural

/-!
# Exact endpoint square in the four-cell bracket

At the four-cell lag, the retained prime-two correlation is not estimated by
absolute values.  Twice that correlation completes the positive-distance and
endpoint-boundary defects to two exact translation squares.
-/

/-- The two translation-square pieces produced by completing the four-cell
prime endpoint atom. -/
def fourCellTranslationSquareEnergy (w : ℝ → ℝ) : ℝ :=
  (∫ x : ℝ in -1..3 / 5, (w (2 / 5 + x) - w x) ^ 2) +
    ∫ x : ℝ in -1..-3 / 5, (w (8 / 5 + x) - w x) ^ 2

/-- The antimatched Hadamard square on the two endpoint strips. -/
def fourCellEndpointAntimatchedSquare (w : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ in -1..-3 / 5, (w (8 / 5 + x) - w x) ^ 2

/-- The matched Hadamard square on the two endpoint strips. -/
def fourCellEndpointMatchedSquare (w : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ in -1..-3 / 5, (w (8 / 5 + x) + w x) ^ 2

/-- The four-cell prime endpoint atom completes exactly to the two translation
squares at the complementary shifts `2 / 5` and `8 / 5`. -/
theorem fourCellEndpointDefect_eq_translationSquares
    (w : ℝ → ℝ) (hw : Continuous w) :
    centeredPositiveDistanceEnergy w (2 / 5) +
          centeredEndpointBoundaryTail w (2 / 5) -
        2 * fourCellEndpointPairing w =
      fourCellTranslationSquareEnergy w := by
  have h := factorTwoPhaseSingularCorrelationNumerator_eq_square
    w (fun _ ↦ 0) hw continuous_const 2 0 (2 / 5)
  norm_num [factorTwoPhaseSingularCorrelationNumerator,
    factorTwoPhaseSingularSquareNumerator,
    factorTwoPhaseEndpointSquare,
    factorTwoCenteredPhaseCorrelation,
    factorTwoCenteredCrossCorrelation,
    centeredEndpointCorrelation,
    centeredPositiveDistanceEnergy, centeredEndpointBoundaryTail,
    sq] at h
  rw [fourCellEndpointPairing_eq_centeredEndpointCorrelation]
  unfold centeredPositiveDistanceEnergy centeredEndpointBoundaryTail
    fourCellTranslationSquareEnergy
  norm_num [centeredEndpointCorrelation, pow_two]
  exact h

/-- The completed translation-square energy is nonnegative without any
parity, endpoint-trace, or Fourier hypothesis. -/
theorem fourCellTranslationSquareEnergy_nonneg (w : ℝ → ℝ) :
    0 ≤ fourCellTranslationSquareEnergy w := by
  unfold fourCellTranslationSquareEnergy
  apply add_nonneg
  · apply intervalIntegral.integral_nonneg (by norm_num)
    intro x _hx
    positivity
  · apply intervalIntegral.integral_nonneg (by norm_num)
    intro x _hx
    positivity

/-- After cancelling the positive-distance square common to both sides, the
endpoint boundary tail minus twice the prime pairing is exactly one far
translation square. -/
theorem fourCellEndpointBoundaryTail_sub_pairing_eq_square
    (w : ℝ → ℝ) (hw : Continuous w) :
    centeredEndpointBoundaryTail w (2 / 5) -
        2 * fourCellEndpointPairing w =
      fourCellEndpointAntimatchedSquare w := by
  have h := fourCellEndpointDefect_eq_translationSquares w hw
  unfold centeredPositiveDistanceEnergy fourCellTranslationSquareEnergy at h
  unfold fourCellEndpointAntimatchedSquare
  norm_num at h
  linarith

/-- The antimatched endpoint square is nonnegative. -/
theorem fourCellEndpointAntimatchedSquare_nonneg (w : ℝ → ℝ) :
    0 ≤ fourCellEndpointAntimatchedSquare w := by
  unfold fourCellEndpointAntimatchedSquare
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro x _hx
  positivity

/-- The opposite radius-two specialization completes the same endpoint tail
to the matched Hadamard square. -/
theorem fourCellEndpointBoundaryTail_add_pairing_eq_square
    (w : ℝ → ℝ) (hw : Continuous w) :
    centeredEndpointBoundaryTail w (2 / 5) +
        2 * fourCellEndpointPairing w =
      fourCellEndpointMatchedSquare w := by
  have h := factorTwoPhaseSingularCorrelationNumerator_eq_square
    w (fun _ ↦ 0) hw continuous_const (-2) 0 (2 / 5)
  norm_num [factorTwoPhaseSingularCorrelationNumerator,
    factorTwoPhaseSingularSquareNumerator,
    factorTwoPhaseEndpointSquare,
    factorTwoCenteredPhaseCorrelation,
    factorTwoCenteredCrossCorrelation,
    centeredEndpointCorrelation,
    centeredPositiveDistanceEnergy, centeredEndpointBoundaryTail,
    sq] at h
  have hmatch (x : ℝ) :
      w (8 / 5 + x) - -(2 * w x) / 2 = w (8 / 5 + x) + w x := by
    ring
  simp_rw [hmatch] at h
  rw [fourCellEndpointPairing_eq_centeredEndpointCorrelation]
  unfold centeredEndpointBoundaryTail fourCellEndpointMatchedSquare
  norm_num [centeredEndpointCorrelation, pow_two]
  linarith

/-- The matched endpoint square is nonnegative. -/
theorem fourCellEndpointMatchedSquare_nonneg (w : ℝ → ℝ) :
    0 ≤ fourCellEndpointMatchedSquare w := by
  unfold fourCellEndpointMatchedSquare
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro x _hx
  positivity

/-- Exact normalized Hadamard diagonalization of the prime-two endpoint
pairing. -/
theorem four_mul_fourCellEndpointPairing_eq_matched_sub_antimatched
    (w : ℝ → ℝ) (hw : Continuous w) :
    4 * fourCellEndpointPairing w =
      fourCellEndpointMatchedSquare w -
        fourCellEndpointAntimatchedSquare w := by
  have hminus := fourCellEndpointBoundaryTail_sub_pairing_eq_square w hw
  have hplus := fourCellEndpointBoundaryTail_add_pairing_eq_square w hw
  linarith

/-- Cancellation of the redundant positive-distance square leaves the sharp
coupled endpoint form: half of the boundary tail is charged and the far
translation square is retained with exactly the same coefficient. -/
theorem fourCellBracket_eq_boundaryPenalty_add_endpointSquare
    (w : ℝ → ℝ) (hw : Continuous w) :
    centeredClippedPhysicalQuadratic (5 * Real.log 2 / 8) w -
        Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w =
      (centeredClippedPhysicalQuadratic (5 * Real.log 2 / 8) w -
          (Real.sqrt 2 * Real.log 2 / 2) *
            centeredEndpointBoundaryTail w (2 / 5)) +
        (Real.sqrt 2 * Real.log 2 / 2) *
          fourCellEndpointAntimatchedSquare w := by
  rw [← fourCellEndpointBoundaryTail_sub_pairing_eq_square w hw]
  ring

/-- Hadamard normal form of the four-cell bracket.  The local physical
quadratic and the antimatched square must jointly pay for the matched square;
no endpoint channel has been estimated separately. -/
theorem fourCellBracket_eq_physical_add_antimatched_sub_matched
    (w : ℝ → ℝ) (hw : Continuous w) :
    centeredClippedPhysicalQuadratic (5 * Real.log 2 / 8) w -
        Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w =
      centeredClippedPhysicalQuadratic (5 * Real.log 2 / 8) w +
          (Real.sqrt 2 * Real.log 2 / 4) *
            fourCellEndpointAntimatchedSquare w -
        (Real.sqrt 2 * Real.log 2 / 4) *
          fourCellEndpointMatchedSquare w := by
  rw [show fourCellEndpointPairing w =
      (fourCellEndpointMatchedSquare w -
        fourCellEndpointAntimatchedSquare w) / 4 by
    linarith [four_mul_fourCellEndpointPairing_eq_matched_sub_antimatched w hw]]
  ring

/-- Sharp endpoint-capacity characterization of four-cell positivity. -/
theorem fourCellBracket_nonnegative_iff_endpointCapacity
    (w : ℝ → ℝ) (hw : Continuous w) :
    0 ≤ centeredClippedPhysicalQuadratic (5 * Real.log 2 / 8) w -
          Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w ↔
      (Real.sqrt 2 * Real.log 2 / 4) *
          fourCellEndpointMatchedSquare w ≤
        centeredClippedPhysicalQuadratic (5 * Real.log 2 / 8) w +
          (Real.sqrt 2 * Real.log 2 / 4) *
            fourCellEndpointAntimatchedSquare w := by
  rw [fourCellBracket_eq_physical_add_antimatched_sub_matched w hw]
  exact sub_nonneg

/-- Production form of the sharp capacity frontier: the complete real
four-cell Bombieri value is nonnegative exactly when its normalized endpoint
map satisfies the matched-versus-antimatched capacity inequality. -/
theorem bombieriFunctional_fourBlock_re_nonnegative_iff_endpointCapacity
    (parent : BombieriTest) (k : ℤ)
    (hparent : bombieriConjugateTest parent = parent) :
    0 ≤ (bombieriFunctional
          (bombieriQuadraticTest (monotoneQuarterFourBlock parent k))).re ↔
      (Real.sqrt 2 * Real.log 2 / 4) *
          fourCellEndpointMatchedSquare
            (fourCellNormalizedRealProfile parent k) ≤
        centeredClippedPhysicalQuadratic (5 * Real.log 2 / 8)
            (fourCellNormalizedRealProfile parent k) +
          (Real.sqrt 2 * Real.log 2 / 4) *
            fourCellEndpointAntimatchedSquare
              (fourCellNormalizedRealProfile parent k) := by
  rw [bombieriFunctional_fourBlock_re_eq_centeredPhysical_sub_pairing
    parent k hparent, fourCellWholeHalfWidth_eq]
  rw [mul_nonneg_iff_of_pos_left (by positivity :
    0 < 5 * Real.log 2 / 8)]
  exact fourCellBracket_nonnegative_iff_endpointCapacity
    (fourCellNormalizedRealProfile parent k)
    (fourCellNormalizedRealProfile_continuous parent k)

end

end ArithmeticHodge.Analysis.YoshidaFourCellEndpointSquareStructural
