import ArithmeticHodge.Analysis.YoshidaFourCellOddP11SelectorConstructionStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddFiveModeStrictCoercivityStructural
import ArithmeticHodge.Analysis.ShiftedLegendreCenteredL2Structural
import ArithmeticHodge.Analysis.YoshidaEndpointPotentialLegendreDiagonalStructural
import ArithmeticHodge.Analysis.YoshidaFourCellRegularKernelWideEnvelope

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP11ExplicitSelectorCauchyStructural

noncomputable section

open CenteredOddOneThreeEnergy
open ShiftedLegendreCenteredL2Structural
open ShiftedLegendreCenteredLowModes
open ShiftedLegendreOrthogonality
open UnitIntervalLogEnergyAffine
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyProjection
open ShiftedLegendreLogEigen
open ShiftedLegendrePolynomialGap
open YoshidaEndpointOcticPotential
open YoshidaFactorTwoPhaseCenteredP9Structural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaEndpointPotentialLegendreDiagonalStructural
open YoshidaEndpointPotentialLegendreOffDiagonalStructural
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialIntegrable
open YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
open YoshidaEndpointOddResidualRegularity
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellRawParityFoldStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaFourCellOddFiveModeCoreExpressionBridgeStructural
open YoshidaFourCellOddFiveModeStrictCoercivityStructural
open YoshidaFourCellOddP11SelectorConstructionStructural
open YoshidaFourCellOddP11WeightedDualSelectorStructural
open YoshidaFourCellOddP11CoupledRieszDefectClosureStructural
open YoshidaFourCellOddP1OrthogonalCoupledClosureStructural
open YoshidaFourCellOddP1OrthogonalFormDualClosureStructural
open YoshidaFourCellOddEndpointStripCoercivityStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicOddP5CorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicOddP5PerturbationCrossStructural
open YoshidaFactorTwoPhaseIntrinsicOddP5PerturbationDiagonalStructural
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoIntegrableLagRepresenterStructural
open YoshidaFactorTwoPhaseP67ResidualAnalyticSchurStructural
open YoshidaRegularKernelBound
open CenteredEndpointCorrelation

/-!
# A structural adversarial test for the odd `P₁₁+` selector target

The scalar-weight Cauchy target is tested on one explicit low polynomial and
one four-mode `P₁₁/P₁₃/P₁₅/P₁₇` tail.  The high witness is
genuinely in the common kernel of the first five odd Legendre coordinates;
that fact is proved below from all-degree Legendre orthogonality rather than
by expanding seventeen powers.
-/

/-- The low direction selected by the thin five-mode eigenchannel. -/
def fourCellOddP11CauchyLowWitness : ℝ → ℝ :=
  fourCellOddOneThreeFiveSevenNineLowProfile
    (-(9 / 10 : ℝ)) 1 (-(1 / 5 : ℝ)) 0 (1 / 10 : ℝ)

/-- A four-mode tail beginning exactly at the first omitted odd mode.  The
sign convention uses `centeredShiftedLegendreReal`; odd centered modes are
the negatives of the classical `Pₙ` used by the five-mode API. -/
def fourCellOddP11CauchyTailPolynomial : ℝ[X] :=
  (3 / 10 : ℝ) • centeredShiftedLegendreReal 11 -
    centeredShiftedLegendreReal 13 +
      (1 / 8 : ℝ) • centeredShiftedLegendreReal 15 +
        (3 / 5 : ℝ) • centeredShiftedLegendreReal 17

def fourCellOddP11CauchyTailWitness : ℝ → ℝ := fun x ↦
  fourCellOddP11CauchyTailPolynomial.eval x

theorem contDiff_fourCellOddP11CauchyTailWitness :
    ContDiff ℝ 1 fourCellOddP11CauchyTailWitness := by
  unfold fourCellOddP11CauchyTailWitness
  exact fourCellOddP11CauchyTailPolynomial.contDiff_aeval (𝕜 := ℝ) 1

theorem odd_fourCellOddP11CauchyTailWitness :
    Function.Odd fourCellOddP11CauchyTailWitness := by
  intro x
  unfold fourCellOddP11CauchyTailWitness fourCellOddP11CauchyTailPolynomial
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_smul,
    smul_eq_mul, eval_centeredShiftedLegendreReal_neg]
  norm_num
  ring

private theorem centeredP1_eq_neg_centeredShiftedLegendre_one :
    centeredP1 = fun x ↦ -(centeredShiftedLegendreReal 1).eval x := by
  funext x
  rw [ShiftedLegendreCenteredLowModes.eval_centeredShiftedLegendreReal_one]
  unfold centeredP1
  ring

private theorem centeredP3_eq_neg_centeredShiftedLegendre_three :
    centeredP3 = fun x ↦ -(centeredShiftedLegendreReal 3).eval x := by
  funext x
  norm_num [centeredShiftedLegendreReal, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_comp,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose, centeredP3,
    Polynomial.smul_eq_C_mul]
  ring

private theorem centeredP5_eq_neg_centeredShiftedLegendre_five :
    factorTwoCenteredP5 =
      fun x ↦ -(centeredShiftedLegendreReal 5).eval x := by
  funext x
  norm_num [centeredShiftedLegendreReal, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_comp,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose, factorTwoCenteredP5,
    Polynomial.smul_eq_C_mul]
  ring

private theorem centeredP7_eq_neg_centeredShiftedLegendre_seven :
    factorTwoCenteredP7 =
      fun x ↦ -(centeredShiftedLegendreReal 7).eval x := by
  funext x
  have h := centeredPullback_factorTwoCenteredP7 ((x + 1) / 2)
  unfold centeredPullback at h
  rw [show 2 * ((x + 1) / 2) - 1 = x by ring] at h
  rw [eval_centeredShiftedLegendreReal]
  linarith

private theorem centeredP9_eq_neg_centeredShiftedLegendre_nine :
    factorTwoCenteredP9 =
      fun x ↦ -(centeredShiftedLegendreReal 9).eval x := by
  funext x
  have h := centeredPullback_factorTwoCenteredP9 ((x + 1) / 2)
  unfold centeredPullback at h
  rw [show 2 * ((x + 1) / 2) - 1 = x by ring] at h
  rw [eval_centeredShiftedLegendreReal]
  linarith

private theorem integral_cauchyTail_mul_centeredMode_eq_zero
    (n : ℕ) (hn : n < 11) :
    (∫ x : ℝ in -1..1,
      fourCellOddP11CauchyTailWitness x *
        (centeredShiftedLegendreReal n).eval x) = 0 := by
  have h11 := centeredPolynomialPair_legendre_eq_zero
    (m := 11) (n := n) (by omega)
  have h13 := centeredPolynomialPair_legendre_eq_zero
    (m := 13) (n := n) (by omega)
  have h15 := centeredPolynomialPair_legendre_eq_zero
    (m := 15) (n := n) (by omega)
  have h17 := centeredPolynomialPair_legendre_eq_zero
    (m := 17) (n := n) (by omega)
  unfold centeredPolynomialPair at h11 h13 h15 h17
  have h11I : IntervalIntegrable (fun x : ℝ ↦
      (centeredShiftedLegendreReal 11).eval x *
        (centeredShiftedLegendreReal n).eval x) volume (-1) 1 := by
    exact ((centeredShiftedLegendreReal 11).continuous.mul
      (centeredShiftedLegendreReal n).continuous).intervalIntegrable _ _
  have h13I : IntervalIntegrable (fun x : ℝ ↦
      (centeredShiftedLegendreReal 13).eval x *
        (centeredShiftedLegendreReal n).eval x) volume (-1) 1 := by
    exact ((centeredShiftedLegendreReal 13).continuous.mul
      (centeredShiftedLegendreReal n).continuous).intervalIntegrable _ _
  have h15I : IntervalIntegrable (fun x : ℝ ↦
      (centeredShiftedLegendreReal 15).eval x *
        (centeredShiftedLegendreReal n).eval x) volume (-1) 1 := by
    exact ((centeredShiftedLegendreReal 15).continuous.mul
      (centeredShiftedLegendreReal n).continuous).intervalIntegrable _ _
  have h17I : IntervalIntegrable (fun x : ℝ ↦
      (centeredShiftedLegendreReal 17).eval x *
        (centeredShiftedLegendreReal n).eval x) volume (-1) 1 := by
    exact ((centeredShiftedLegendreReal 17).continuous.mul
      (centeredShiftedLegendreReal n).continuous).intervalIntegrable _ _
  unfold fourCellOddP11CauchyTailWitness fourCellOddP11CauchyTailPolynomial
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_smul,
    smul_eq_mul]
  rw [show (fun x : ℝ ↦
      (((3 / 10 : ℝ) * (centeredShiftedLegendreReal 11).eval x -
          (centeredShiftedLegendreReal 13).eval x +
        (1 / 8 : ℝ) * (centeredShiftedLegendreReal 15).eval x) +
          (3 / 5 : ℝ) * (centeredShiftedLegendreReal 17).eval x) *
            (centeredShiftedLegendreReal n).eval x) = fun x ↦
      (3 / 10 : ℝ) * ((centeredShiftedLegendreReal 11).eval x *
        (centeredShiftedLegendreReal n).eval x) -
      (centeredShiftedLegendreReal 13).eval x *
        (centeredShiftedLegendreReal n).eval x +
      (1 / 8 : ℝ) * ((centeredShiftedLegendreReal 15).eval x *
        (centeredShiftedLegendreReal n).eval x) +
      (3 / 5 : ℝ) * ((centeredShiftedLegendreReal 17).eval x *
        (centeredShiftedLegendreReal n).eval x) by
    funext x
    ring]
  rw [intervalIntegral.integral_add
      (((h11I.const_mul (3 / 10 : ℝ)).sub h13I).add
        (h15I.const_mul (1 / 8 : ℝ)))
      (h17I.const_mul (3 / 5 : ℝ)),
    intervalIntegral.integral_add
      ((h11I.const_mul (3 / 10 : ℝ)).sub h13I)
      (h15I.const_mul (1 / 8 : ℝ)),
    intervalIntegral.integral_sub
      (h11I.const_mul (3 / 10 : ℝ)) h13I,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  rw [h11, h13, h15, h17]
  ring

theorem fourCellOddP11CauchyTailWitness_moments :
    centeredOddP1Coefficient fourCellOddP11CauchyTailWitness = 0 ∧
    centeredOddP3Coefficient fourCellOddP11CauchyTailWitness = 0 ∧
    centeredOddP5Coefficient fourCellOddP11CauchyTailWitness = 0 ∧
    centeredOddP7Coefficient fourCellOddP11CauchyTailWitness = 0 ∧
    centeredOddP9Coefficient fourCellOddP11CauchyTailWitness = 0 := by
  unfold centeredOddP1Coefficient centeredOddP3Coefficient
    centeredOddP5Coefficient centeredOddP7Coefficient centeredOddP9Coefficient
  rw [centeredP1_eq_neg_centeredShiftedLegendre_one,
    centeredP3_eq_neg_centeredShiftedLegendre_three,
    centeredP5_eq_neg_centeredShiftedLegendre_five,
    centeredP7_eq_neg_centeredShiftedLegendre_seven,
    centeredP9_eq_neg_centeredShiftedLegendre_nine]
  have h1 := integral_cauchyTail_mul_centeredMode_eq_zero 1 (by omega)
  have h3 := integral_cauchyTail_mul_centeredMode_eq_zero 3 (by omega)
  have h5 := integral_cauchyTail_mul_centeredMode_eq_zero 5 (by omega)
  have h7 := integral_cauchyTail_mul_centeredMode_eq_zero 7 (by omega)
  have h9 := integral_cauchyTail_mul_centeredMode_eq_zero 9 (by omega)
  simp only []
  rw [show (fun x : ℝ ↦ fourCellOddP11CauchyTailWitness x *
      -(centeredShiftedLegendreReal 1).eval x) = fun x ↦
        -(fourCellOddP11CauchyTailWitness x *
          (centeredShiftedLegendreReal 1).eval x) by funext x; ring,
    intervalIntegral.integral_neg, h1]
  rw [show (fun x : ℝ ↦ fourCellOddP11CauchyTailWitness x *
      -(centeredShiftedLegendreReal 3).eval x) = fun x ↦
        -(fourCellOddP11CauchyTailWitness x *
          (centeredShiftedLegendreReal 3).eval x) by funext x; ring,
    intervalIntegral.integral_neg, h3]
  rw [show (fun x : ℝ ↦ fourCellOddP11CauchyTailWitness x *
      -(centeredShiftedLegendreReal 5).eval x) = fun x ↦
        -(fourCellOddP11CauchyTailWitness x *
          (centeredShiftedLegendreReal 5).eval x) by funext x; ring,
    intervalIntegral.integral_neg, h5]
  rw [show (fun x : ℝ ↦ fourCellOddP11CauchyTailWitness x *
      -(centeredShiftedLegendreReal 7).eval x) = fun x ↦
        -(fourCellOddP11CauchyTailWitness x *
          (centeredShiftedLegendreReal 7).eval x) by funext x; ring,
    intervalIntegral.integral_neg, h7]
  rw [show (fun x : ℝ ↦ fourCellOddP11CauchyTailWitness x *
      -(centeredShiftedLegendreReal 9).eval x) = fun x ↦
        -(fourCellOddP11CauchyTailWitness x *
          (centeredShiftedLegendreReal 9).eval x) by funext x; ring,
    intervalIntegral.integral_neg, h9]
  norm_num

/-! ## The exact endpoint-potential mass of the witness

The only transcendental entry in the scalar tail weight is treated in the
Legendre basis.  Bilinearity reduces it to four diagonal entries and the six
closed off-diagonal entries; the diagonal values are generated by the
all-degree Jacobi recurrence.
-/

private theorem endpointPotentialPolynomialPair_add_left_local
    (p q r : ℝ[X]) :
    endpointPotentialPolynomialPair (p + q) r =
      endpointPotentialPolynomialPair p r +
        endpointPotentialPolynomialPair q r := by
  unfold endpointPotentialPolynomialPair
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x * (p + q).eval x * r.eval x) =
    fun x : ℝ ↦
      yoshidaEndpointPotential x * p.eval x * r.eval x +
        yoshidaEndpointPotential x * q.eval x * r.eval x by
    funext x
    simp only [Polynomial.eval_add]
    ring]
  rw [intervalIntegral.integral_add]
  · simpa only [mul_assoc] using intervalIntegrable_endpointPotential_mul
      (fun x : ℝ ↦ p.eval x * r.eval x)
      (p.continuous.mul r.continuous)
  · simpa only [mul_assoc] using intervalIntegrable_endpointPotential_mul
      (fun x : ℝ ↦ q.eval x * r.eval x)
      (q.continuous.mul r.continuous)

private theorem endpointPotentialPolynomialPair_sub_left_local
    (p q r : ℝ[X]) :
    endpointPotentialPolynomialPair (p - q) r =
      endpointPotentialPolynomialPair p r -
        endpointPotentialPolynomialPair q r := by
  unfold endpointPotentialPolynomialPair
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x * (p - q).eval x * r.eval x) =
    fun x : ℝ ↦
      yoshidaEndpointPotential x * p.eval x * r.eval x -
        yoshidaEndpointPotential x * q.eval x * r.eval x by
    funext x
    simp only [Polynomial.eval_sub]
    ring]
  rw [intervalIntegral.integral_sub]
  · simpa only [mul_assoc] using intervalIntegrable_endpointPotential_mul
      (fun x : ℝ ↦ p.eval x * r.eval x)
      (p.continuous.mul r.continuous)
  · simpa only [mul_assoc] using intervalIntegrable_endpointPotential_mul
      (fun x : ℝ ↦ q.eval x * r.eval x)
      (q.continuous.mul r.continuous)

private theorem endpointPotentialPolynomialPair_smul_left_local
    (a : ℝ) (p q : ℝ[X]) :
    endpointPotentialPolynomialPair (a • p) q =
      a * endpointPotentialPolynomialPair p q := by
  unfold endpointPotentialPolynomialPair
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x * (a • p).eval x * q.eval x) =
    fun x : ℝ ↦
      a * (yoshidaEndpointPotential x * p.eval x * q.eval x) by
    funext x
    simp only [Polynomial.eval_smul, smul_eq_mul]
    ring,
    intervalIntegral.integral_const_mul]

private theorem endpointPotentialPolynomialPair_comm_local
    (p q : ℝ[X]) :
    endpointPotentialPolynomialPair p q =
      endpointPotentialPolynomialPair q p := by
  unfold endpointPotentialPolynomialPair
  apply intervalIntegral.integral_congr
  intro x _hx
  ring

private theorem endpointPotentialPolynomialPair_add_right_local
    (p q r : ℝ[X]) :
    endpointPotentialPolynomialPair p (q + r) =
      endpointPotentialPolynomialPair p q +
        endpointPotentialPolynomialPair p r := by
  rw [endpointPotentialPolynomialPair_comm_local p (q + r),
    endpointPotentialPolynomialPair_add_left_local,
    endpointPotentialPolynomialPair_comm_local q p,
    endpointPotentialPolynomialPair_comm_local r p]

private theorem endpointPotentialPolynomialPair_sub_right_local
    (p q r : ℝ[X]) :
    endpointPotentialPolynomialPair p (q - r) =
      endpointPotentialPolynomialPair p q -
        endpointPotentialPolynomialPair p r := by
  rw [endpointPotentialPolynomialPair_comm_local p (q - r),
    endpointPotentialPolynomialPair_sub_left_local,
    endpointPotentialPolynomialPair_comm_local q p,
    endpointPotentialPolynomialPair_comm_local r p]

private theorem endpointPotentialPolynomialPair_smul_right_local
    (a : ℝ) (p q : ℝ[X]) :
    endpointPotentialPolynomialPair p (a • q) =
      a * endpointPotentialPolynomialPair p q := by
  rw [endpointPotentialPolynomialPair_comm_local p (a • q),
    endpointPotentialPolynomialPair_smul_left_local,
    endpointPotentialPolynomialPair_comm_local q p]

set_option maxHeartbeats 2000000 in
private theorem endpointPotentialLegendreDiagonal_witness_values :
    endpointPotentialLegendreDiagonal 11 =
        (3708740681 / 30786816060 : ℝ) - (2 / 23) * Real.log 2 ∧
      endpointPotentialLegendreDiagonal 13 =
        (55641506293 / 542115674100 : ℝ) - (2 / 27) * Real.log 2 ∧
      endpointPotentialLegendreDiagonal 15 =
        (7146812078221 / 79937681066100 : ℝ) - (2 / 31) * Real.log 2 ∧
      endpointPotentialLegendreDiagonal 17 =
        (100063457447249 / 1263531087819000 : ℝ) -
          (2 / 35) * Real.log 2 := by
  have h0 := endpointPotentialLegendreDiagonal_zero
  have h1r := endpointPotentialLegendreDiagonal_succ 0
  norm_num [h0] at h1r
  have h1 : endpointPotentialLegendreDiagonal 1 =
      (8 / 9 : ℝ) - (2 / 3) * Real.log 2 := by linarith [h1r]
  have h2r := endpointPotentialLegendreDiagonal_succ 1
  norm_num [h1] at h2r
  have h2 : endpointPotentialLegendreDiagonal 2 =
      (41 / 75 : ℝ) - (2 / 5) * Real.log 2 := by linarith [h2r]
  have h3r := endpointPotentialLegendreDiagonal_succ 2
  norm_num [h2] at h3r
  have h3 : endpointPotentialLegendreDiagonal 3 =
      (289 / 735 : ℝ) - (2 / 7) * Real.log 2 := by linarith [h3r]
  have h4r := endpointPotentialLegendreDiagonal_succ 3
  norm_num [h3] at h4r
  have h4 : endpointPotentialLegendreDiagonal 4 =
      (1739 / 5670 : ℝ) - (2 / 9) * Real.log 2 := by linarith [h4r]
  have h5r := endpointPotentialLegendreDiagonal_succ 4
  norm_num [h4] at h5r
  have h5 : endpointPotentialLegendreDiagonal 5 =
      (19157 / 76230 : ℝ) - (2 / 11) * Real.log 2 := by linarith [h5r]
  have h6r := endpointPotentialLegendreDiagonal_succ 5
  norm_num [h5] at h6r
  have h6 : endpointPotentialLegendreDiagonal 6 =
      (249251 / 1171170 : ℝ) - (2 / 13) * Real.log 2 := by linarith [h6r]
  have h7r := endpointPotentialLegendreDiagonal_succ 6
  norm_num [h6] at h7r
  have h7 : endpointPotentialLegendreDiagonal 7 =
      (249383 / 1351350 : ℝ) - (2 / 15) * Real.log 2 := by linarith [h7r]
  have h8r := endpointPotentialLegendreDiagonal_succ 7
  norm_num [h7] at h8r
  have h8 : endpointPotentialLegendreDiagonal 8 =
      (1696405 / 10414404 : ℝ) - (2 / 17) * Real.log 2 := by linarith [h8r]
  have h9r := endpointPotentialLegendreDiagonal_succ 8
  norm_num [h8] at h9r
  have h9 : endpointPotentialLegendreDiagonal 9 =
      (32239703 / 221152932 : ℝ) - (2 / 19) * Real.log 2 := by linarith [h9r]
  have h10r := endpointPotentialLegendreDiagonal_succ 9
  norm_num [h9] at h10r
  have h10 : endpointPotentialLegendreDiagonal 10 =
      (161227687 / 1222160940 : ℝ) - (2 / 21) * Real.log 2 := by linarith [h10r]
  have h11r := endpointPotentialLegendreDiagonal_succ 10
  norm_num [h10] at h11r
  have h11 : endpointPotentialLegendreDiagonal 11 =
      (3708740681 / 30786816060 : ℝ) - (2 / 23) * Real.log 2 := by
    linarith [h11r]
  have h12r := endpointPotentialLegendreDiagonal_succ 11
  norm_num [h11] at h12r
  have h12 : endpointPotentialLegendreDiagonal 12 =
      (18545643343 / 167319652500 : ℝ) - (2 / 25) * Real.log 2 := by
    linarith [h12r]
  have h13r := endpointPotentialLegendreDiagonal_succ 12
  norm_num [h12] at h13r
  have h13 : endpointPotentialLegendreDiagonal 13 =
      (55641506293 / 542115674100 : ℝ) - (2 / 27) * Real.log 2 := by
    linarith [h13r]
  have h14r := endpointPotentialLegendreDiagonal_succ 13
  norm_num [h13] at h14r
  have h14 : endpointPotentialLegendreDiagonal 14 =
      (230529988171 / 2412271332900 : ℝ) - (2 / 29) * Real.log 2 := by
    linarith [h14r]
  have h15r := endpointPotentialLegendreDiagonal_succ 14
  norm_num [h14] at h15r
  have h15 : endpointPotentialLegendreDiagonal 15 =
      (7146812078221 / 79937681066100 : ℝ) - (2 / 31) * Real.log 2 := by
    linarith [h15r]
  have h16r := endpointPotentialLegendreDiagonal_succ 15
  norm_num [h15] at h16r
  have h16 : endpointPotentialLegendreDiagonal 16 =
      (14294254321367 / 170189901624600 : ℝ) - (2 / 33) * Real.log 2 := by
    linarith [h16r]
  have h17r := endpointPotentialLegendreDiagonal_succ 16
  norm_num [h16] at h17r
  have h17 : endpointPotentialLegendreDiagonal 17 =
      (100063457447249 / 1263531087819000 : ℝ) -
        (2 / 35) * Real.log 2 := by
    linarith [h17r]
  exact ⟨h11, h13, h15, h17⟩

set_option maxHeartbeats 1000000 in
private theorem endpointPotentialPolynomialPair_cauchyTail_eq :
    endpointPotentialPolynomialPair
        fourCellOddP11CauchyTailPolynomial
        fourCellOddP11CauchyTailPolynomial =
      (151907373440363061449 / 1496876121329450400000 : ℝ) -
        (55778431 / 539028000) * Real.log 2 := by
  rcases endpointPotentialLegendreDiagonal_witness_values with
    ⟨h11, h13, h15, h17⟩
  change endpointPotentialPolynomialPair
      (centeredShiftedLegendreReal 11)
      (centeredShiftedLegendreReal 11) = _ at h11
  change endpointPotentialPolynomialPair
      (centeredShiftedLegendreReal 13)
      (centeredShiftedLegendreReal 13) = _ at h13
  change endpointPotentialPolynomialPair
      (centeredShiftedLegendreReal 15)
      (centeredShiftedLegendreReal 15) = _ at h15
  change endpointPotentialPolynomialPair
      (centeredShiftedLegendreReal 17)
      (centeredShiftedLegendreReal 17) = _ at h17
  have h1113 : endpointPotentialPolynomialPair
      (centeredShiftedLegendreReal 11)
      (centeredShiftedLegendreReal 13) = (1 / 25 : ℝ) := by
    have h := integral_endpointPotential_mul_centeredShiftedLegendreReal_of_even
      (m := 11) (n := 13) (by omega) (by norm_num : Even (11 + 13))
    norm_num at h
    simpa only [endpointPotentialPolynomialPair] using h
  have h1115 : endpointPotentialPolynomialPair
      (centeredShiftedLegendreReal 11)
      (centeredShiftedLegendreReal 15) = (1 / 54 : ℝ) := by
    have h := integral_endpointPotential_mul_centeredShiftedLegendreReal_of_even
      (m := 11) (n := 15) (by omega) (by norm_num : Even (11 + 15))
    norm_num at h
    simpa only [endpointPotentialPolynomialPair] using h
  have h1117 : endpointPotentialPolynomialPair
      (centeredShiftedLegendreReal 11)
      (centeredShiftedLegendreReal 17) = (1 / 87 : ℝ) := by
    have h := integral_endpointPotential_mul_centeredShiftedLegendreReal_of_even
      (m := 11) (n := 17) (by omega) (by norm_num : Even (11 + 17))
    norm_num at h
    simpa only [endpointPotentialPolynomialPair] using h
  have h1315 : endpointPotentialPolynomialPair
      (centeredShiftedLegendreReal 13)
      (centeredShiftedLegendreReal 15) = (1 / 29 : ℝ) := by
    have h := integral_endpointPotential_mul_centeredShiftedLegendreReal_of_even
      (m := 13) (n := 15) (by omega) (by norm_num : Even (13 + 15))
    norm_num at h
    simpa only [endpointPotentialPolynomialPair] using h
  have h1317 : endpointPotentialPolynomialPair
      (centeredShiftedLegendreReal 13)
      (centeredShiftedLegendreReal 17) = (1 / 62 : ℝ) := by
    have h := integral_endpointPotential_mul_centeredShiftedLegendreReal_of_even
      (m := 13) (n := 17) (by omega) (by norm_num : Even (13 + 17))
    norm_num at h
    simpa only [endpointPotentialPolynomialPair] using h
  have h1517 : endpointPotentialPolynomialPair
      (centeredShiftedLegendreReal 15)
      (centeredShiftedLegendreReal 17) = (1 / 33 : ℝ) := by
    have h := integral_endpointPotential_mul_centeredShiftedLegendreReal_of_even
      (m := 15) (n := 17) (by omega) (by norm_num : Even (15 + 17))
    norm_num at h
    simpa only [endpointPotentialPolynomialPair] using h
  unfold fourCellOddP11CauchyTailPolynomial
  simp only [endpointPotentialPolynomialPair_add_left_local,
    endpointPotentialPolynomialPair_sub_left_local,
    endpointPotentialPolynomialPair_smul_left_local,
    endpointPotentialPolynomialPair_add_right_local,
    endpointPotentialPolynomialPair_sub_right_local,
    endpointPotentialPolynomialPair_smul_right_local]
  rw [h11, h13, h15, h17,
    h1113, h1115, h1117, h1315, h1317, h1517,
    endpointPotentialPolynomialPair_comm_local
      (centeredShiftedLegendreReal 13) (centeredShiftedLegendreReal 11),
    endpointPotentialPolynomialPair_comm_local
      (centeredShiftedLegendreReal 15) (centeredShiftedLegendreReal 11),
    endpointPotentialPolynomialPair_comm_local
      (centeredShiftedLegendreReal 17) (centeredShiftedLegendreReal 11),
    endpointPotentialPolynomialPair_comm_local
      (centeredShiftedLegendreReal 15) (centeredShiftedLegendreReal 13),
    endpointPotentialPolynomialPair_comm_local
      (centeredShiftedLegendreReal 17) (centeredShiftedLegendreReal 13),
    endpointPotentialPolynomialPair_comm_local
      (centeredShiftedLegendreReal 17) (centeredShiftedLegendreReal 15),
    h1113, h1115, h1117, h1315, h1317, h1517]
  ring

private theorem integral_endpointPotential_cauchyTail_sq_eq :
    (∫ x : ℝ in 0..1,
      yoshidaEndpointPotential x * fourCellOddP11CauchyTailWitness x ^ 2) =
      (151907373440363061449 / 2993752242658900800000 : ℝ) -
        (55778431 / 1078056000) * Real.log 2 := by
  have hfold := endpointPotential_eq_two_mul_positiveHalf
    fourCellOddP11CauchyTailWitness
    contDiff_fourCellOddP11CauchyTailWitness.continuous
    (Or.inr odd_fourCellOddP11CauchyTailWitness)
  have hpair := endpointPotentialPolynomialPair_cauchyTail_eq
  unfold endpointPotentialPolynomialPair at hpair
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x * fourCellOddP11CauchyTailPolynomial.eval x *
        fourCellOddP11CauchyTailPolynomial.eval x) = fun x ↦
      yoshidaEndpointPotential x * fourCellOddP11CauchyTailWitness x ^ 2 by
    funext x
    unfold fourCellOddP11CauchyTailWitness
    ring] at hpair
  rw [hpair] at hfold
  linarith

theorem integral_endpointPotential_cauchyTail_sq_lt :
    (∫ x : ℝ in 0..1,
      yoshidaEndpointPotential x * fourCellOddP11CauchyTailWitness x ^ 2) <
      (3 / 200 : ℝ) := by
  rw [integral_endpointPotential_cauchyTail_sq_eq]
  nlinarith [YoshidaConstantBounds.strict_log_two_bounds.1]

set_option maxHeartbeats 2000000 in
private theorem integral_lower_cauchyTail_sq_eq :
    (∫ x : ℝ in 0..3 / 5, fourCellOddP11CauchyTailWitness x ^ 2) =
      (137085653690330052784608445239 /
        4648230969905853271484375000000 : ℝ) := by
  unfold fourCellOddP11CauchyTailWitness fourCellOddP11CauchyTailPolynomial
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_smul,
    smul_eq_mul]
  norm_num [centeredShiftedLegendreReal, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_comp,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose, Polynomial.smul_eq_C_mul]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 (3 / 5))
    (Continuous.intervalIntegrable (by fun_prop) 0 (3 / 5))]
  norm_num

set_option maxHeartbeats 2000000 in
private theorem integral_upper_cauchyTail_sq_eq :
    (∫ x : ℝ in 3 / 5..1, fourCellOddP11CauchyTailWitness x ^ 2) =
      (1396075673113783032143503762711 /
        62751118093729019165039062500000 : ℝ) := by
  unfold fourCellOddP11CauchyTailWitness fourCellOddP11CauchyTailPolynomial
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_smul,
    smul_eq_mul]
  norm_num [centeredShiftedLegendreReal, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_comp,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose, Polynomial.smul_eq_C_mul]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (3 / 5) 1)
    (Continuous.intervalIntegrable (by fun_prop) (3 / 5) 1)]
  norm_num

/-- The odd quotient of the four-mode tail.  This is used only for the
reciprocal strip mass; the Legendre arguments above never expand modes. -/
private def fourCellOddP11CauchyTailOddQuotient (x : ℝ) : ℝ :=
  (349701 / 163840 : ℝ) - (322179 / 16384) * x ^ 2 -
    (37756719 / 81920) * x ^ 4 + (487675617 / 81920) * x ^ 6 -
    (219259183 / 8192) * x ^ 8 + (4889437371 / 81920) * x ^ 10 -
    (1165647245 / 16384) * x ^ 12 + (711601623 / 16384) * x ^ 14 -
    (350040933 / 32768) * x ^ 16

set_option maxHeartbeats 1000000 in
private theorem fourCellOddP11CauchyTailWitness_eq_mul_oddQuotient
    (x : ℝ) :
    fourCellOddP11CauchyTailWitness x =
      x * fourCellOddP11CauchyTailOddQuotient x := by
  unfold fourCellOddP11CauchyTailWitness fourCellOddP11CauchyTailPolynomial
    fourCellOddP11CauchyTailOddQuotient
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_smul,
    smul_eq_mul]
  norm_num [centeredShiftedLegendreReal, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_comp,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose, Polynomial.smul_eq_C_mul]
  ring

set_option maxHeartbeats 2000000 in
private theorem integral_upper_cauchyTail_sq_div_eq :
    (∫ x : ℝ in 3 / 5..1,
      fourCellOddP11CauchyTailWitness x ^ 2 / x) =
      (20819797827696200112883177201 /
        713174231350421905517578125000 : ℝ) := by
  rw [show (fun x : ℝ ↦ fourCellOddP11CauchyTailWitness x ^ 2 / x) =
      fun x ↦ x * fourCellOddP11CauchyTailOddQuotient x ^ 2 by
    funext x
    rw [fourCellOddP11CauchyTailWitness_eq_mul_oddQuotient]
    by_cases hx : x = 0
    · simp [hx]
    · field_simp [hx]]
  unfold fourCellOddP11CauchyTailOddQuotient
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (3 / 5) 1)
    (Continuous.intervalIntegrable (by fun_prop) (3 / 5) 1)]
  norm_num

/-- Certified scalar-weight cost of the explicit `P₁₁+` tail. -/
theorem fourCellOddP1ExactTailWeight_cauchyTail_lt :
    fourCellOddP1ExactTailWeight fourCellOddP11CauchyTailWitness <
      (2 / 125 : ℝ) := by
  unfold fourCellOddP1ExactTailWeight
  rw [integral_lower_cauchyTail_sq_eq,
    integral_upper_cauchyTail_sq_eq,
    integral_upper_cauchyTail_sq_div_eq]
  nlinarith [integral_endpointPotential_cauchyTail_sq_lt]

/-! ## A structural upper box for the finite witness

The `P₉` diagonal is the only finite entry for which the production API
exposes only a lower bound.  We derive the needed upper box from the same
all-degree logarithmic eigenidentity: a centered polynomial raw energy is
four times its shifted-Legendre pairing.
-/

private theorem centeredRawLogEnergy_eq_four_mul_shiftedPair_of_polynomial
    (q : ℝ → ℝ) (p : ℝ[X])
    (hmode : ∀ t : ℝ, centeredPullback q t = p.eval t) :
    centeredRawLogEnergy q =
      4 * ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear p p := by
  let f : unitInterval → ℝ := fun t ↦ centeredPullback q (t : ℝ)
  have hfeq : f = fun t : unitInterval ↦ p.eval (t : ℝ) := by
    funext t
    exact hmode t
  have henergy : Integrable (unitIntervalRawLogEnergyIntegrand f) := by
    rw [hfeq]
    exact integrable_unitIntervalRawLogEnergyIntegrand_polynomial p
  have hbridge := unitIntervalLogEnergy_centeredPullback q henergy
  change unitIntervalLogEnergy f = (1 / 4 : ℝ) * centeredRawLogEnergy q
    at hbridge
  rw [hfeq] at hbridge
  have hpoly := integral_unitIntervalRawLogEnergyIntegrand_polynomial p
  unfold unitIntervalLogEnergy at hbridge
  rw [hpoly] at hbridge
  rw [ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear_apply,
    ← integral_unitInterval_eq_intervalIntegral]
  linarith

private theorem integral_shiftedLegendreReal_sq_closed (n : ℕ) :
    (∫ x : ℝ in 0..1, (shiftedLegendreReal n).eval x ^ 2) =
      1 / (2 * (n : ℝ) + 1) := by
  have hdiag := centeredLegendreL2Diagonal_closed n
  unfold centeredLegendreL2Diagonal centeredPolynomialPair at hdiag
  have htransport := integral_comp_two_mul_sub_one
    (fun x : ℝ ↦ (centeredShiftedLegendreReal n).eval x ^ 2)
  rw [show (fun t : ℝ ↦
      (centeredShiftedLegendreReal n).eval (2 * t - 1) ^ 2) =
      fun t ↦ (shiftedLegendreReal n).eval t ^ 2 by
    funext t
    rw [eval_centeredShiftedLegendreReal]
    congr 2
    ring] at htransport
  rw [show (fun x : ℝ ↦
      (centeredShiftedLegendreReal n).eval x ^ 2) = fun x ↦
      (centeredShiftedLegendreReal n).eval x *
        (centeredShiftedLegendreReal n).eval x by
    funext x
    ring,
    hdiag] at htransport
  calc
    (∫ x : ℝ in 0..1, (shiftedLegendreReal n).eval x ^ 2) =
        (1 / 2 : ℝ) * (2 / (2 * (n : ℝ) + 1)) := htransport
    _ = 1 / (2 * (n : ℝ) + 1) := by ring

private theorem shiftedLogEnergyBilinear_legendre_ne
    {m n : ℕ} (hmn : m ≠ n) :
    ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear
        (shiftedLegendreReal m) (shiftedLegendreReal n) = 0 := by
  rw [ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear_apply,
    shiftedLogKernel_shiftedLegendreReal]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  rw [show (fun x : ℝ ↦
      (shiftedLegendreReal m).eval x *
        (2 * (harmonic n : ℝ) * (shiftedLegendreReal n).eval x)) =
      fun x ↦ (2 * (harmonic n : ℝ)) *
        ((shiftedLegendreReal m).eval x *
          (shiftedLegendreReal n).eval x) by
    funext x
    ring,
    intervalIntegral.integral_const_mul,
    ShiftedLegendreBasis.integral_shiftedLegendreReal_mul_eq_zero hmn]
  ring

private theorem shiftedLogEnergyBilinear_legendre_self (n : ℕ) :
    ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear
        (shiftedLegendreReal n) (shiftedLegendreReal n) =
      2 * (harmonic n : ℝ) / (2 * (n : ℝ) + 1) := by
  rw [ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear_apply,
    shiftedLogKernel_shiftedLegendreReal]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  rw [show (fun x : ℝ ↦
      (shiftedLegendreReal n).eval x *
        (2 * (harmonic n : ℝ) * (shiftedLegendreReal n).eval x)) =
      fun x ↦ (2 * (harmonic n : ℝ)) *
        ((shiftedLegendreReal n).eval x ^ 2) by
    funext x
    ring,
    intervalIntegral.integral_const_mul,
    integral_shiftedLegendreReal_sq_closed]
  ring

private def endpointStripOddP9ShiftedPolynomial : ℝ[X] := -(
  (-303036 / 1953125 : ℝ) • shiftedLegendreReal 1 +
    (1126916 / 1953125 : ℝ) • shiftedLegendreReal 3 +
    (195844 / 1953125 : ℝ) • shiftedLegendreReal 5 +
    (372 / 390625 : ℝ) • shiftedLegendreReal 7 +
    (1 / 1953125 : ℝ) • shiftedLegendreReal 9)

set_option maxHeartbeats 1000000 in
private theorem centeredPullback_endpointStripOdd_P9_eq_shiftedPolynomial
    (t : ℝ) :
    centeredPullback
        (fourCellOddEndpointStripOdd factorTwoCenteredP9) t =
      endpointStripOddP9ShiftedPolynomial.eval t := by
  unfold centeredPullback fourCellOddEndpointStripOdd
    fourCellOddEndpointStripPullback endpointStripOddP9ShiftedPolynomial
    factorTwoCenteredP9
  simp only [Polynomial.eval_neg, Polynomial.eval_add,
    Polynomial.eval_smul, smul_eq_mul]
  norm_num [shiftedLegendreReal, Polynomial.shiftedLegendre,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 1000000 in
private theorem endpointStripOddP9_shiftedPair_gt :
    (77 / 400 : ℝ) <
      ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear
        endpointStripOddP9ShiftedPolynomial
        endpointStripOddP9ShiftedPolynomial := by
  unfold endpointStripOddP9ShiftedPolynomial
  simp only [map_neg, LinearMap.neg_apply, map_add, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [shiftedLogEnergyBilinear_legendre_self 1,
    shiftedLogEnergyBilinear_legendre_self 3,
    shiftedLogEnergyBilinear_legendre_self 5,
    shiftedLogEnergyBilinear_legendre_self 7,
    shiftedLogEnergyBilinear_legendre_self 9,
    shiftedLogEnergyBilinear_legendre_ne (m := 1) (n := 3) (by omega),
    shiftedLogEnergyBilinear_legendre_ne (m := 1) (n := 5) (by omega),
    shiftedLogEnergyBilinear_legendre_ne (m := 1) (n := 7) (by omega),
    shiftedLogEnergyBilinear_legendre_ne (m := 1) (n := 9) (by omega),
    shiftedLogEnergyBilinear_legendre_ne (m := 3) (n := 1) (by omega),
    shiftedLogEnergyBilinear_legendre_ne (m := 3) (n := 5) (by omega),
    shiftedLogEnergyBilinear_legendre_ne (m := 3) (n := 7) (by omega),
    shiftedLogEnergyBilinear_legendre_ne (m := 3) (n := 9) (by omega),
    shiftedLogEnergyBilinear_legendre_ne (m := 5) (n := 1) (by omega),
    shiftedLogEnergyBilinear_legendre_ne (m := 5) (n := 3) (by omega),
    shiftedLogEnergyBilinear_legendre_ne (m := 5) (n := 7) (by omega),
    shiftedLogEnergyBilinear_legendre_ne (m := 5) (n := 9) (by omega),
    shiftedLogEnergyBilinear_legendre_ne (m := 7) (n := 1) (by omega),
    shiftedLogEnergyBilinear_legendre_ne (m := 7) (n := 3) (by omega),
    shiftedLogEnergyBilinear_legendre_ne (m := 7) (n := 5) (by omega),
    shiftedLogEnergyBilinear_legendre_ne (m := 7) (n := 9) (by omega),
    shiftedLogEnergyBilinear_legendre_ne (m := 9) (n := 1) (by omega),
    shiftedLogEnergyBilinear_legendre_ne (m := 9) (n := 3) (by omega),
    shiftedLogEnergyBilinear_legendre_ne (m := 9) (n := 5) (by omega),
    shiftedLogEnergyBilinear_legendre_ne (m := 9) (n := 7) (by omega)]
  norm_num [harmonic, Finset.sum_range_succ]

private theorem centeredRawLogEnergy_endpointStripOdd_P9_gt :
    (77 / 100 : ℝ) < centeredRawLogEnergy
      (fourCellOddEndpointStripOdd factorTwoCenteredP9) := by
  rw [centeredRawLogEnergy_eq_four_mul_shiftedPair_of_polynomial
    (fourCellOddEndpointStripOdd factorTwoCenteredP9)
      endpointStripOddP9ShiftedPolynomial
      centeredPullback_endpointStripOdd_P9_eq_shiftedPolynomial]
  nlinarith [endpointStripOddP9_shiftedPair_gt]

private theorem centeredRawLogEnergy_factorTwoCenteredP9_eq :
    centeredRawLogEnergy factorTwoCenteredP9 = (7129 / 5985 : ℝ) := by
  rw [centeredRawLogEnergy_eq_four_mul_shiftedPair_of_polynomial
    factorTwoCenteredP9 (-(shiftedLegendreReal 9))]
  · simp only [map_neg, LinearMap.neg_apply]
    rw [shiftedLogEnergyBilinear_legendre_self 9]
    norm_num [harmonic, Finset.sum_range_succ]
  · intro t
    rw [centeredPullback_factorTwoCenteredP9]
    simp

private theorem fourCellOddRawStripCancellationReserve_eq_raw_sub_strip_local
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (hodd : Function.Odd w) :
    fourCellOddRawStripCancellationReserve w =
      (1 / 4 : ℝ) * centeredRawLogEnergy w -
        (1 / 2 : ℝ) * fourCellOddEndpointStripOddRawEnergy w := by
  have hwLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w :=
    hw.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  have hfold := centeredRawLogEnergy_div_four_eq_positiveHalf_odd
    w hwLocal hodd
  unfold fourCellOddRawStripCancellationReserve
  rw [← hfold]
  ring

set_option maxHeartbeats 1000000 in
private theorem endpointStripMass_P9_lt :
    fourCellOddEndpointStripEvenMass factorTwoCenteredP9 +
        fourCellOddEndpointStripOddMass factorTwoCenteredP9 <
      (31 / 1000 : ℝ) := by
  rw [← fourCellOddEndpointStrip_mass_eq_even_add_odd
    factorTwoCenteredP9 continuous_factorTwoCenteredP9]
  unfold fourCellOddEndpointStripPullback
  simp_rw [factorTwoCenteredP9_eq]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  norm_num

private theorem endpointStripPrimeMass_P9_lt :
    Real.sqrt 2 * Real.log 2 *
        fourCellOddEndpointStripEvenMass factorTwoCenteredP9 +
      (2 - Real.sqrt 2 * Real.log 2) *
        fourCellOddEndpointStripOddMass factorTwoCenteredP9 <
      (651 / 20000 : ℝ) := by
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : Real.sqrt 2 ^ 2 = 2 := by
    simpa only using Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hslo : (7 / 5 : ℝ) < Real.sqrt 2 := by nlinarith
  have hshi : Real.sqrt 2 < (3 / 2 : ℝ) := by nlinarith
  have hlog := YoshidaConstantBounds.strict_log_two_bounds
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hklo : (19 / 20 : ℝ) < Real.sqrt 2 * Real.log 2 := by
    calc
      (19 / 20 : ℝ) < (7 / 5 : ℝ) * (6931 / 10000 : ℝ) := by
        norm_num
      _ < Real.sqrt 2 * (6931 / 10000 : ℝ) :=
        mul_lt_mul_of_pos_right hslo (by norm_num)
      _ < Real.sqrt 2 * Real.log 2 :=
        mul_lt_mul_of_pos_left hlog.1 (Real.sqrt_pos.2 (by norm_num))
  have hkhi : Real.sqrt 2 * Real.log 2 < (21 / 20 : ℝ) := by
    calc
      Real.sqrt 2 * Real.log 2 < (3 / 2 : ℝ) * Real.log 2 :=
        mul_lt_mul_of_pos_right hshi hlog0
      _ < (3 / 2 : ℝ) * (6932 / 10000 : ℝ) :=
        mul_lt_mul_of_pos_left hlog.2 (by norm_num)
      _ < (21 / 20 : ℝ) := by norm_num
  have he : 0 ≤ fourCellOddEndpointStripEvenMass factorTwoCenteredP9 := by
    unfold fourCellOddEndpointStripEvenMass
    exact mul_nonneg (by norm_num) (intervalIntegral.integral_nonneg
      (by norm_num) (fun _ _ ↦ sq_nonneg _))
  have ho : 0 ≤ fourCellOddEndpointStripOddMass factorTwoCenteredP9 := by
    unfold fourCellOddEndpointStripOddMass
    exact mul_nonneg (by norm_num) (intervalIntegral.integral_nonneg
      (by norm_num) (fun _ _ ↦ sq_nonneg _))
  have hmass := endpointStripMass_P9_lt
  have heBound := mul_le_mul_of_nonneg_right hkhi.le he
  have hoBound :
      (2 - Real.sqrt 2 * Real.log 2) *
          fourCellOddEndpointStripOddMass factorTwoCenteredP9 ≤
        (21 / 20 : ℝ) *
          fourCellOddEndpointStripOddMass factorTwoCenteredP9 := by
    exact mul_le_mul_of_nonneg_right (by linarith) ho
  nlinarith

private theorem integral_zero_one_P9_sq_eq :
    (∫ x : ℝ in 0..1, factorTwoCenteredP9 x ^ 2) = (1 / 19 : ℝ) := by
  have hfold := integral_sq_eq_two_mul_positiveHalf
    factorTwoCenteredP9 continuous_factorTwoCenteredP9
      (Or.inr odd_factorTwoCenteredP9)
  have henergy := factorTwoCenteredP9_energy
  unfold factorTwoIntrinsicEnergy at henergy
  rw [henergy] at hfold
  linarith

private theorem integral_zero_one_endpointPotential_P9_sq_lt :
    (∫ x : ℝ in 0..1,
      yoshidaEndpointPotential x * factorTwoCenteredP9 x ^ 2) <
      (73 / 2000 : ℝ) := by
  have hfold := endpointPotential_eq_two_mul_positiveHalf
    factorTwoCenteredP9 continuous_factorTwoCenteredP9
      (Or.inr odd_factorTwoCenteredP9)
  have hpot := factorTwoCenteredP9_potential_lt_seventy_three_thousandths
  unfold factorTwoIntrinsicPotentialEnergy at hpot
  linarith

private theorem abs_regularCorrelationIntegral_P9_le :
    |∫ t : ℝ in 0..2,
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        centeredEndpointCorrelation factorTwoCenteredP9 t| ≤
      (1 / 190 : ℝ) := by
  have h := abs_fourCellRegularCorrelation_le_one_twentieth_centeredMass
    factorTwoCenteredP9 continuous_factorTwoCenteredP9
      odd_factorTwoCenteredP9
  have henergy := factorTwoCenteredP9_energy
  unfold factorTwoIntrinsicEnergy at henergy
  rw [henergy] at h
  norm_num at h ⊢
  exact h

theorem fourCellOddCoreLocalQuadratic_P9_lt_four_twenty_fifths :
    fourCellOddCoreLocalQuadratic factorTwoCenteredP9 < (4 / 25 : ℝ) := by
  let R : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
      centeredEndpointCorrelation factorTwoCenteredP9 t
  have hRabs : |R| ≤ (1 / 190 : ℝ) := by
    simpa only [R] using abs_regularCorrelationIntegral_P9_le
  have ha0 : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have ha : fourCellOperatorHalfWidth ≤ (1 / 2 : ℝ) := by
    have hlog := YoshidaConstantBounds.strict_log_two_bounds.2
    unfold fourCellOperatorHalfWidth
    nlinarith
  have hregular :
      -(2 * fourCellOperatorHalfWidth * R) ≤ (1 / 190 : ℝ) := by
    calc
      -(2 * fourCellOperatorHalfWidth * R) ≤
          2 * fourCellOperatorHalfWidth * |R| := by
        have hneg : -R ≤ |R| := neg_le_abs R
        nlinarith
      _ ≤ 1 * |R| := by
        exact mul_le_mul_of_nonneg_right (by nlinarith) (abs_nonneg R)
      _ ≤ (1 / 190 : ℝ) := by simpa using hRabs
  have hscalar := fourCellScalar_fine_bounds.1
  have hrawEndpoint := centeredRawLogEnergy_endpointStripOdd_P9_gt
  have hprime := endpointStripPrimeMass_P9_lt
  have hpotential := integral_zero_one_endpointPotential_P9_sq_lt
  rw [fourCellOddCoreLocalQuadratic_eq_retained_sub_signed]
  unfold fourCellOddRetainedEndpointQuadratic
    fourCellOddRetainedPrimePotentialQuadratic
    fourCellOddSignedMassRegularQuadratic
  rw [fourCellOddRawStripCancellationReserve_eq_raw_sub_strip_local
      factorTwoCenteredP9 (by
        rw [show factorTwoCenteredP9 = fun x ↦
            (12155 * x ^ 9 - 25740 * x ^ 7 + 18018 * x ^ 5 -
              4620 * x ^ 3 + 315 * x) / 128 by
          funext x
          exact factorTwoCenteredP9_eq x]
        fun_prop)
      odd_factorTwoCenteredP9,
    centeredRawLogEnergy_factorTwoCenteredP9_eq,
    integral_zero_one_P9_sq_eq]
  unfold fourCellOddEndpointStripOddRawEnergy
  change
    (1 / 4 : ℝ) * (7129 / 5985) -
          (1 / 2) * ((1 / 5) *
            centeredRawLogEnergy
              (fourCellOddEndpointStripOdd factorTwoCenteredP9)) +
        (Real.sqrt 2 * Real.log 2 *
            fourCellOddEndpointStripEvenMass factorTwoCenteredP9 +
          (2 - Real.sqrt 2 * Real.log 2) *
            fourCellOddEndpointStripOddMass factorTwoCenteredP9 +
          (93 / 50) *
            (∫ x : ℝ in 0..1,
              yoshidaEndpointPotential x * factorTwoCenteredP9 x ^ 2)) -
        ((2 * (Real.log (2 * fourCellOperatorHalfWidth) +
            Real.eulerMascheroniConstant + Real.log Real.pi) + 3 / 200) *
            (1 / 19 : ℝ) + 2 * fourCellOperatorHalfWidth * R) <
      (4 / 25 : ℝ)
  nlinarith

private theorem sqrt_two_mul_log_two_cauchy_fine_bounds :
    (1414213562 / 1000000000 : ℝ) *
        (69314718055 / 100000000000 : ℝ) <
          Real.sqrt 2 * Real.log 2 ∧
      Real.sqrt 2 * Real.log 2 <
        (1414213563 / 1000000000 : ℝ) *
          (69314718057 / 100000000000 : ℝ) := by
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : Real.sqrt 2 ^ 2 = 2 := by
    simpa only using Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hslo : (1414213562 / 1000000000 : ℝ) < Real.sqrt 2 := by
    have hrat : (1414213562 / 1000000000 : ℝ) ^ 2 < 2 := by
      norm_num
    nlinarith
  have hshi : Real.sqrt 2 < (1414213563 / 1000000000 : ℝ) := by
    have hrat : (2 : ℝ) <
        (1414213563 / 1000000000 : ℝ) ^ 2 := by
      norm_num
    nlinarith
  have hlog := YoshidaConstantBounds.strict_log_two_fine_bounds
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · exact (mul_lt_mul_of_pos_right hslo (by norm_num)).trans
      (mul_lt_mul_of_pos_left hlog.1 hspos)
  · exact (mul_lt_mul_of_pos_right hshi hlogpos).trans
      (mul_lt_mul_of_pos_left hlog.2 (by norm_num))

private theorem fourCellOddOneThreeFiveCombined_cauchyLow_lt :
    fourCellOddOneThreeFiveCombinedQuadratic
        (-(9 / 10 : ℝ)) 1 (-(1 / 5 : ℝ)) <
      (2597199 / 500000000 : ℝ) := by
  have hlog := YoshidaConstantBounds.strict_log_two_fine_bounds
  have hsqrtlog := sqrt_two_mul_log_two_cauchy_fine_bounds
  have hscalar := fourCellScalar_fine_bounds
  unfold fourCellOddOneThreeFiveCombinedQuadratic
    fourCellOddLowCombined11 fourCellOddLowCombined13
    fourCellOddLowCombined33
    fourCellOddOneThreeFiveCombined15
    fourCellOddOneThreeFiveCombined35
    fourCellOddOneThreeFiveCombined55
    fourCellOddLowLocalAlgebraic11
    fourCellOddLowLocalAlgebraic13
    fourCellOddLowLocalAlgebraic33
    fourCellOddOneThreeFiveLocalAlgebraic15
    fourCellOddOneThreeFiveLocalAlgebraic35
    fourCellOddOneThreeFiveLocalAlgebraic55
  nlinarith

private theorem fourCellOddOneThreeFiveRegularQuadratic_cauchyLow_gt :
    (4393 / 1000000 : ℝ) <
      fourCellOddOneThreeFiveRegularQuadratic
        (-(9 / 10 : ℝ)) 1 (-(1 / 5 : ℝ)) := by
  let E11 := fourCellWideRegularEnvelopeError oddStructuralCorrelation11
  let E13 := fourCellWideRegularEnvelopeError oddStructuralCorrelation13
  let E33 := fourCellWideRegularEnvelopeError oddStructuralCorrelation33
  let E15 := fourCellWideRegularEnvelopeError oddP5Correlation15
  let E35 := fourCellWideRegularEnvelopeError oddP5Correlation35
  let E55 := fourCellWideRegularEnvelopeError oddP5Correlation55
  have hE11raw := abs_fourCellWideRegularEnvelopeError_le_sevenEighths
    oddStructuralCorrelation11 (by unfold oddStructuralCorrelation11; fun_prop)
  have hE13raw := abs_fourCellWideRegularEnvelopeError_le_sevenEighths
    oddStructuralCorrelation13 (by unfold oddStructuralCorrelation13; fun_prop)
  have hE33raw := abs_fourCellWideRegularEnvelopeError_le_sevenEighths
    oddStructuralCorrelation33 (by unfold oddStructuralCorrelation33; fun_prop)
  have hE15raw := abs_fourCellWideRegularEnvelopeError_le_sevenEighths
    oddP5Correlation15 (by unfold oddP5Correlation15; fun_prop)
  have hE35raw := abs_fourCellWideRegularEnvelopeError_le_sevenEighths
    oddP5Correlation35 (by unfold oddP5Correlation35; fun_prop)
  have hE55raw := abs_fourCellWideRegularEnvelopeError_le_sevenEighths
    oddP5Correlation55 (by unfold oddP5Correlation55; fun_prop)
  have hE11 : |E11| ≤ (1 / 120000 : ℝ) := by
    change |E11| ≤ (1 / 80000 : ℝ) *
      (∫ t : ℝ in 0..2, |oddStructuralCorrelation11 t|) at hE11raw
    nlinarith [integral_abs_oddStructuralCorrelation11_le]
  have hE13 : |E13| ≤ (1 / 480000 : ℝ) := by
    change |E13| ≤ (1 / 80000 : ℝ) *
      (∫ t : ℝ in 0..2, |oddStructuralCorrelation13 t|) at hE13raw
    nlinarith [integral_abs_oddStructuralCorrelation13_lt]
  have hE33 : |E33| ≤ (1 / 280000 : ℝ) := by
    change |E33| ≤ (1 / 80000 : ℝ) *
      (∫ t : ℝ in 0..2, |oddStructuralCorrelation33 t|) at hE33raw
    nlinarith [integral_abs_oddStructuralCorrelation33_le]
  have hE15 : |E15| ≤ (1 / 1000000 : ℝ) := by
    change |E15| ≤ (1 / 80000 : ℝ) *
      (∫ t : ℝ in 0..2, |oddP5Correlation15 t|) at hE15raw
    nlinarith [integral_abs_oddP5Correlation15_lt]
  have hE35 : |E35| ≤ (11 / 10000000 : ℝ) := by
    change |E35| ≤ (1 / 80000 : ℝ) *
      (∫ t : ℝ in 0..2, |oddP5Correlation35 t|) at hE35raw
    nlinarith [integral_abs_oddP5Correlation35_lt]
  have hE55 : |E55| ≤ (1 / 440000 : ℝ) := by
    change |E55| ≤ (1 / 80000 : ℝ) *
      (∫ t : ℝ in 0..2, |oddP5Correlation55 t|) at hE55raw
    nlinarith [integral_abs_oddP5Correlation55_le]
  rcases fourCellWideRegularPolynomial_entry_bounds with
    ⟨h11lo, h11hi, h13lo, h13hi, h33lo, h33hi,
      h15lo, h15hi, h35lo, h35hi, h55lo, h55hi⟩
  rcases fourCellOddOneThreeFiveRegular_entries_eq with
    ⟨h11, h13, h33, h15, h35, h55⟩
  change fourCellOddOneThreeFiveRegular11 =
    fourCellWideRegularPolynomial11 + E11 at h11
  change fourCellOddOneThreeFiveRegular13 =
    fourCellWideRegularPolynomial13 + E13 at h13
  change fourCellOddOneThreeFiveRegular33 =
    fourCellWideRegularPolynomial33 + E33 at h33
  change fourCellOddOneThreeFiveRegular15 =
    fourCellWideRegularPolynomial15 + E15 at h15
  change fourCellOddOneThreeFiveRegular35 =
    fourCellWideRegularPolynomial35 + E35 at h35
  change fourCellOddOneThreeFiveRegular55 =
    fourCellWideRegularPolynomial55 + E55 at h55
  rw [fourCellOddOneThreeFiveRegularQuadratic_expansion,
    fourCellOddLowRegularQuadratic_expansion]
  change (4393 / 1000000 : ℝ) <
    (((-(9 / 10 : ℝ)) ^ 2 * fourCellOddOneThreeFiveRegular11 +
        2 * (-(9 / 10 : ℝ)) * 1 * fourCellOddOneThreeFiveRegular13 +
        1 ^ 2 * fourCellOddOneThreeFiveRegular33) +
      2 * (-(9 / 10 : ℝ)) * (-(1 / 5 : ℝ)) *
        fourCellOddOneThreeFiveRegular15 +
      2 * 1 * (-(1 / 5 : ℝ)) *
        fourCellOddOneThreeFiveRegular35 +
      (-(1 / 5 : ℝ)) ^ 2 * fourCellOddOneThreeFiveRegular55)
  rw [h11, h13, h33, h15, h35, h55]
  have hE11lo := neg_abs_le E11
  have hE13hi := le_abs_self E13
  have hE33lo := neg_abs_le E33
  have hE15lo := neg_abs_le E15
  have hE35hi := le_abs_self E35
  have hE55lo := neg_abs_le E55
  nlinarith

private theorem fourCellOddOneThreeFivePerturbed_cauchyLow_lt :
    fourCellOddOneThreeFivePerturbedQuadratic
        (-(9 / 10 : ℝ)) 1 (-(1 / 5 : ℝ)) <
      (139 / 100000 : ℝ) := by
  let W : ℝ := 2 * fourCellOperatorHalfWidth
  let R : ℝ := fourCellOddOneThreeFiveRegularQuadratic
    (-(9 / 10 : ℝ)) 1 (-(1 / 5 : ℝ))
  have hW : (8664 / 10000 : ℝ) < W := by
    have hlog := YoshidaConstantBounds.strict_log_two_fine_bounds.1
    dsimp only [W]
    unfold fourCellOperatorHalfWidth
    nlinarith
  have hW0 : 0 < W := (by norm_num : (0 : ℝ) < 8664 / 10000).trans hW
  have hR : (4393 / 1000000 : ℝ) < R := by
    simpa only [R] using
      fourCellOddOneThreeFiveRegularQuadratic_cauchyLow_gt
  have hproduct :
      (8664 / 10000 : ℝ) * (4393 / 1000000 : ℝ) < W * R := by
    calc
      (8664 / 10000 : ℝ) * (4393 / 1000000 : ℝ) <
          W * (4393 / 1000000 : ℝ) :=
        mul_lt_mul_of_pos_right hW (by norm_num)
      _ < W * R := mul_lt_mul_of_pos_left hR hW0
  have hcombined := fourCellOddOneThreeFiveCombined_cauchyLow_lt
  have hid := fourCellOddOneThreeFiveCombined_sub_regular_eq_perturbed
    (-(9 / 10 : ℝ)) 1 (-(1 / 5 : ℝ))
  change fourCellOddOneThreeFiveCombinedQuadratic
      (-(9 / 10 : ℝ)) 1 (-(1 / 5 : ℝ)) - W * R =
    fourCellOddOneThreeFivePerturbedQuadratic
      (-(9 / 10 : ℝ)) 1 (-(1 / 5 : ℝ)) at hid
  nlinarith

theorem fourCellOddCoreLocalQuadratic_cauchyLow_lt :
    fourCellOddCoreLocalQuadratic fourCellOddP11CauchyLowWitness <
      (11 / 5000 : ℝ) := by
  have hP135 := fourCellOddOneThreeFivePerturbed_cauchyLow_lt
  rcases fourCellOddCoreLocalBilinear_P1_high_certificate_bounds with
    ⟨h17lo, h17hi, h19lo, h19hi⟩
  rcases fourCellOddCoreLocalBilinear_P3_P9_bounds with ⟨h39lo, h39hi⟩
  rcases fourCellOddCoreLocal_highCross_certificate_bounds with
    ⟨h57lo, h57hi, h59lo, h59hi, h79lo, h79hi⟩
  have hP9 := fourCellOddCoreLocalQuadratic_P9_lt_four_twenty_fifths
  unfold fourCellOddP11CauchyLowWitness
  rw [fourCellOddCoreLocalQuadratic_fiveMode_eq_coreExpression]
  unfold fourCellOddFiveModeCoreExpression
  norm_num
  nlinarith

/-! ## The mixed low--tail row -/

private def cauchyLowEndpointStripOddShiftedPolynomial : ℝ[X] := -(
  (7581339 / 19531250 : ℝ) • shiftedLegendreReal 1 +
    (379083 / 9765625 : ℝ) • shiftedLegendreReal 3 +
    (97297 / 9765625 : ℝ) • shiftedLegendreReal 5 +
    (186 / 1953125 : ℝ) • shiftedLegendreReal 7 +
    (1 / 19531250 : ℝ) • shiftedLegendreReal 9)

private def cauchyTailEndpointStripOddShiftedPolynomial : ℝ[X] := -(
  (52940972943 / 1525878906250 : ℝ) • shiftedLegendreReal 1 -
    (590619284401 / 1525878906250 : ℝ) • shiftedLegendreReal 3 +
    (670138980159 / 1525878906250 : ℝ) • shiftedLegendreReal 5 -
    (1771365419429 / 7629394531250 : ℝ) • shiftedLegendreReal 7 -
    (281859775893 / 7629394531250 : ℝ) • shiftedLegendreReal 9 -
    (3360939274 / 3814697265625 : ℝ) • shiftedLegendreReal 11 -
    (37879367 / 7629394531250 : ℝ) • shiftedLegendreReal 13 -
    (187613 / 30517578125000 : ℝ) • shiftedLegendreReal 15 -
    (3 / 3814697265625 : ℝ) • shiftedLegendreReal 17)

set_option maxHeartbeats 5000000 in
private theorem centeredPullback_cauchyLowEndpointStripOdd_eq
    (t : ℝ) :
    centeredPullback
        (fourCellOddEndpointStripOdd fourCellOddP11CauchyLowWitness) t =
      cauchyLowEndpointStripOddShiftedPolynomial.eval t := by
  unfold centeredPullback fourCellOddEndpointStripOdd
    fourCellOddEndpointStripPullback fourCellOddP11CauchyLowWitness
    fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    centeredP1 centeredP3 factorTwoCenteredP5 factorTwoCenteredP9
    cauchyLowEndpointStripOddShiftedPolynomial
  simp only [Polynomial.eval_neg, Polynomial.eval_add, Polynomial.eval_smul,
    smul_eq_mul]
  norm_num [shiftedLegendreReal, Polynomial.shiftedLegendre,
    Polynomial.eval_map, Polynomial.eval_finset_sum,
    Finset.sum_range_succ, Nat.choose]
  ring

set_option maxHeartbeats 5000000 in
private theorem centeredPullback_cauchyTailEndpointStripOdd_eq
    (t : ℝ) :
    centeredPullback
        (fourCellOddEndpointStripOdd fourCellOddP11CauchyTailWitness) t =
      cauchyTailEndpointStripOddShiftedPolynomial.eval t := by
  unfold centeredPullback fourCellOddEndpointStripOdd
    fourCellOddEndpointStripPullback fourCellOddP11CauchyTailWitness
    fourCellOddP11CauchyTailPolynomial
    cauchyTailEndpointStripOddShiftedPolynomial
  simp only [Polynomial.eval_neg, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_smul, smul_eq_mul]
  norm_num [centeredShiftedLegendreReal, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_comp, Polynomial.eval_map,
    Polynomial.eval_finset_sum, Finset.sum_range_succ, Nat.choose,
    Polynomial.smul_eq_C_mul]
  ring

private theorem shiftedLogEnergyBilinear_legendre_eq (m n : ℕ) :
    ShiftedLegendrePolynomialGap.shiftedLogEnergyBilinear
        (shiftedLegendreReal m) (shiftedLegendreReal n) =
      if m = n then 2 * (harmonic n : ℝ) / (2 * (n : ℝ) + 1) else 0 := by
  by_cases hmn : m = n
  · subst n
    rw [if_pos rfl, shiftedLogEnergyBilinear_legendre_self]
  · rw [if_neg hmn, shiftedLogEnergyBilinear_legendre_ne hmn]

set_option maxHeartbeats 5000000 in
private theorem cauchy_endpointStripOddRawPolarization_eq :
    fourCellOddEndpointStripOddRawPolarization
        fourCellOddP11CauchyLowWitness fourCellOddP11CauchyTailWitness =
      (60851227229540918677 / 26077032089233398437500 : ℝ) := by
  have hsum (t : ℝ) :
      centeredPullback
          (fourCellOddEndpointStripOdd
            (fourCellOddP11CauchyLowWitness +
              fourCellOddP11CauchyTailWitness)) t =
        (cauchyLowEndpointStripOddShiftedPolynomial +
          cauchyTailEndpointStripOddShiftedPolynomial).eval t := by
    have hlo := centeredPullback_cauchyLowEndpointStripOdd_eq t
    have htail := centeredPullback_cauchyTailEndpointStripOdd_eq t
    unfold centeredPullback fourCellOddEndpointStripOdd
      fourCellOddEndpointStripPullback at hlo htail ⊢
    simp only [Pi.add_apply, Polynomial.eval_add]
    linarith
  unfold fourCellOddEndpointStripOddRawPolarization
    fourCellOddEndpointStripOddRawEnergy
  rw [centeredRawLogEnergy_eq_four_mul_shiftedPair_of_polynomial
      (fourCellOddEndpointStripOdd
        (fourCellOddP11CauchyLowWitness +
          fourCellOddP11CauchyTailWitness))
      (cauchyLowEndpointStripOddShiftedPolynomial +
        cauchyTailEndpointStripOddShiftedPolynomial) hsum,
    centeredRawLogEnergy_eq_four_mul_shiftedPair_of_polynomial
      (fourCellOddEndpointStripOdd fourCellOddP11CauchyLowWitness)
      cauchyLowEndpointStripOddShiftedPolynomial
      centeredPullback_cauchyLowEndpointStripOdd_eq,
    centeredRawLogEnergy_eq_four_mul_shiftedPair_of_polynomial
      (fourCellOddEndpointStripOdd fourCellOddP11CauchyTailWitness)
      cauchyTailEndpointStripOddShiftedPolynomial
      centeredPullback_cauchyTailEndpointStripOdd_eq]
  unfold cauchyLowEndpointStripOddShiftedPolynomial
    cauchyTailEndpointStripOddShiftedPolynomial
  simp only [map_neg, map_add, map_sub, map_smul, LinearMap.neg_apply,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    shiftedLogEnergyBilinear_legendre_eq]
  norm_num [harmonic, Finset.sum_range_succ]

set_option maxHeartbeats 5000000 in
private theorem cauchy_endpointStripEvenMassBilinear_eq :
    fourCellOddEndpointStripEvenMassBilinear
        fourCellOddP11CauchyLowWitness fourCellOddP11CauchyTailWitness =
      (1212113361834921004 / 186264514923095703125 : ℝ) := by
  unfold fourCellOddEndpointStripEvenMassBilinear
    fourCellOddEndpointStripEven fourCellOddEndpointStripPullback
    fourCellOddP11CauchyLowWitness
    fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    centeredP1 centeredP3 factorTwoCenteredP5 factorTwoCenteredP9
    fourCellOddP11CauchyTailWitness fourCellOddP11CauchyTailPolynomial
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_smul,
    smul_eq_mul]
  norm_num [centeredShiftedLegendreReal, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_comp, Polynomial.eval_map,
    Polynomial.eval_finset_sum, Finset.sum_range_succ, Nat.choose,
    Polynomial.smul_eq_C_mul]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  norm_num

set_option maxHeartbeats 5000000 in
private theorem cauchy_endpointStripOddMassBilinear_eq :
    fourCellOddEndpointStripOddMassBilinear
        fourCellOddP11CauchyLowWitness fourCellOddP11CauchyTailWitness =
      (1428511930592826272 / 1303851604461669921875 : ℝ) := by
  unfold fourCellOddEndpointStripOddMassBilinear
    fourCellOddEndpointStripOdd fourCellOddEndpointStripPullback
    fourCellOddP11CauchyLowWitness
    fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    centeredP1 centeredP3 factorTwoCenteredP5 factorTwoCenteredP9
    fourCellOddP11CauchyTailWitness fourCellOddP11CauchyTailPolynomial
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_smul,
    smul_eq_mul]
  norm_num [centeredShiftedLegendreReal, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_comp, Polynomial.eval_map,
    Polynomial.eval_finset_sum, Finset.sum_range_succ, Nat.choose,
    Polynomial.smul_eq_C_mul]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  norm_num

private def fourCellOddP11CauchyLowPolynomial : ℝ[X] :=
  (9 / 10 : ℝ) • centeredShiftedLegendreReal 1 -
    centeredShiftedLegendreReal 3 +
    (1 / 5 : ℝ) • centeredShiftedLegendreReal 5 -
    (1 / 10 : ℝ) • centeredShiftedLegendreReal 9

private theorem fourCellOddP11CauchyLowWitness_eq_eval (x : ℝ) :
    fourCellOddP11CauchyLowWitness x =
      fourCellOddP11CauchyLowPolynomial.eval x := by
  have h1 := congrFun centeredP1_eq_neg_centeredShiftedLegendre_one x
  have h3 := congrFun centeredP3_eq_neg_centeredShiftedLegendre_three x
  have h5 := congrFun centeredP5_eq_neg_centeredShiftedLegendre_five x
  have h9 := congrFun centeredP9_eq_neg_centeredShiftedLegendre_nine x
  unfold fourCellOddP11CauchyLowWitness
    fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    fourCellOddP11CauchyLowPolynomial
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_smul,
    smul_eq_mul]
  rw [h1, h3, h5, h9]
  ring

set_option maxHeartbeats 1000000 in
private theorem endpointPotentialPolynomialPair_cauchyLow_tail_eq :
    endpointPotentialPolynomialPair fourCellOddP11CauchyLowPolynomial
        fourCellOddP11CauchyTailPolynomial =
      (-(3658121 / 42590457000 : ℝ)) := by
  have hoff : ∀ {m n : ℕ}, m < n → Even (m + n) →
      endpointPotentialPolynomialPair
          (centeredShiftedLegendreReal m)
          (centeredShiftedLegendreReal n) =
        2 / (((n : ℝ) - m) * ((n : ℝ) + m + 1)) := by
    intro m n hmn heven
    simpa only [endpointPotentialPolynomialPair] using
      integral_endpointPotential_mul_centeredShiftedLegendreReal_of_even
        hmn heven
  unfold fourCellOddP11CauchyLowPolynomial
    fourCellOddP11CauchyTailPolynomial
  simp only [endpointPotentialPolynomialPair_add_left_local,
    endpointPotentialPolynomialPair_sub_left_local,
    endpointPotentialPolynomialPair_smul_left_local,
    endpointPotentialPolynomialPair_add_right_local,
    endpointPotentialPolynomialPair_sub_right_local,
    endpointPotentialPolynomialPair_smul_right_local]
  rw [hoff (m := 1) (n := 11) (by omega) (by norm_num),
    hoff (m := 1) (n := 13) (by omega) (by norm_num),
    hoff (m := 1) (n := 15) (by omega) (by norm_num),
    hoff (m := 1) (n := 17) (by omega) (by norm_num),
    hoff (m := 3) (n := 11) (by omega) (by norm_num),
    hoff (m := 3) (n := 13) (by omega) (by norm_num),
    hoff (m := 3) (n := 15) (by omega) (by norm_num),
    hoff (m := 3) (n := 17) (by omega) (by norm_num),
    hoff (m := 5) (n := 11) (by omega) (by norm_num),
    hoff (m := 5) (n := 13) (by omega) (by norm_num),
    hoff (m := 5) (n := 15) (by omega) (by norm_num),
    hoff (m := 5) (n := 17) (by omega) (by norm_num),
    hoff (m := 9) (n := 11) (by omega) (by norm_num),
    hoff (m := 9) (n := 13) (by omega) (by norm_num),
    hoff (m := 9) (n := 15) (by omega) (by norm_num),
    hoff (m := 9) (n := 17) (by omega) (by norm_num)]
  norm_num

private theorem integral_endpointPotential_cauchyLow_mul_tail_eq :
    (∫ x : ℝ in 0..1,
      yoshidaEndpointPotential x * fourCellOddP11CauchyLowWitness x *
        fourCellOddP11CauchyTailWitness x) =
      (-(3658121 / 85180914000 : ℝ)) := by
  have hpair := endpointPotentialPolynomialPair_cauchyLow_tail_eq
  unfold endpointPotentialPolynomialPair at hpair
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x * fourCellOddP11CauchyLowPolynomial.eval x *
        fourCellOddP11CauchyTailPolynomial.eval x) = fun x ↦
      yoshidaEndpointPotential x * fourCellOddP11CauchyLowWitness x *
        fourCellOddP11CauchyTailWitness x by
    funext x
    rw [fourCellOddP11CauchyLowWitness_eq_eval]
    rfl] at hpair
  have hInt : IntervalIntegrable (fun x : ℝ ↦
      yoshidaEndpointPotential x *
        (fourCellOddP11CauchyLowWitness x *
          fourCellOddP11CauchyTailWitness x)) volume (-1) 1 :=
    intervalIntegrable_endpointPotential_mul
      (fun x : ℝ ↦ fourCellOddP11CauchyLowWitness x *
        fourCellOddP11CauchyTailWitness x)
      ((contDiff_fourCellOddOneThreeFiveSevenNineLowProfile
          (-(9 / 10 : ℝ)) 1 (-(1 / 5 : ℝ)) 0 (1 / 10 : ℝ)).continuous.mul
        contDiff_fourCellOddP11CauchyTailWitness.continuous)
  have heven : Function.Even (fun x : ℝ ↦
      yoshidaEndpointPotential x *
        (fourCellOddP11CauchyLowWitness x *
          fourCellOddP11CauchyTailWitness x)) := by
    intro x
    change yoshidaEndpointPotential (-x) *
        (fourCellOddP11CauchyLowWitness (-x) *
          fourCellOddP11CauchyTailWitness (-x)) =
      yoshidaEndpointPotential x *
        (fourCellOddP11CauchyLowWitness x *
          fourCellOddP11CauchyTailWitness x)
    unfold yoshidaEndpointPotential
    rw [show fourCellOddP11CauchyLowWitness (-x) =
        -fourCellOddP11CauchyLowWitness x by
      exact odd_fourCellOddOneThreeFiveSevenNineLowProfile
        (-(9 / 10 : ℝ)) 1 (-(1 / 5 : ℝ)) 0 (1 / 10 : ℝ) x,
      odd_fourCellOddP11CauchyTailWitness]
    ring_nf
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even
    (fun x : ℝ ↦ yoshidaEndpointPotential x *
      (fourCellOddP11CauchyLowWitness x *
        fourCellOddP11CauchyTailWitness x)) hInt heven
  rw [show (fun x : ℝ ↦ yoshidaEndpointPotential x *
      (fourCellOddP11CauchyLowWitness x *
        fourCellOddP11CauchyTailWitness x)) = fun x ↦
      yoshidaEndpointPotential x * fourCellOddP11CauchyLowWitness x *
        fourCellOddP11CauchyTailWitness x by
    funext x
    ring_nf] at hfold
  rw [hpair] at hfold
  linarith

private def cauchyLowTailCenteredCorrelation (t : ℝ) : ℝ :=
  (33 / 400 : ℝ) * t ^ 2 - (15509 / 400) * t ^ 3 +
    (1725307 / 1600) * t ^ 4 - (39044461 / 3200) * t ^ 5 +
    (490941127 / 6400) * t ^ 6 - (13772105259 / 44800) * t ^ 7 +
    (1355525059 / 1600) * t ^ 8 - (86083608039 / 51200) * t ^ 9 +
    (253186674379 / 102400) * t ^ 10 -
      (140279595027 / 51200) * t ^ 11 +
    (94376686209 / 40960) * t ^ 12 -
      (600903345163 / 409600) * t ^ 13 +
    (799365176847 / 1146880) * t ^ 14 -
      (39105496627 / 163840) * t ^ 15 +
    (17852087583 / 327680) * t ^ 16 -
      (10882573159 / 1638400) * t ^ 17 +
    (38305287 / 524288) * t ^ 19 +
    (1777300771 / 734003200) * t ^ 21 -
      (21064103 / 41943040) * t ^ 23 +
    (12564279 / 335544320) * t ^ 25 -
      (504339 / 419430400) * t ^ 27

set_option maxHeartbeats 10000000 in
private theorem factorTwoCenteredCorrelationBilinear_cauchy_eq
    (t : ℝ) :
    factorTwoCenteredCorrelationBilinear fourCellOddP11CauchyLowWitness
        fourCellOddP11CauchyTailWitness t =
      cauchyLowTailCenteredCorrelation t := by
  unfold factorTwoCenteredCorrelationBilinear
    factorTwoCenteredCrossCorrelation
    fourCellOddP11CauchyLowWitness
    fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    centeredP1 centeredP3 factorTwoCenteredP5 factorTwoCenteredP9
    fourCellOddP11CauchyTailWitness fourCellOddP11CauchyTailPolynomial
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_smul,
    smul_eq_mul]
  norm_num [centeredShiftedLegendreReal, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_comp, Polynomial.eval_map,
    Polynomial.eval_finset_sum, Finset.sum_range_succ, Nat.choose,
    Polynomial.smul_eq_C_mul]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) (1 - t))
    (Continuous.intervalIntegrable (by fun_prop) (-1) (1 - t))]
  simp only [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_mul_const,
    YoshidaEndpointOcticPotential.integral_pow_nat]
  have hlinear (c : ℝ) :
      (∫ x : ℝ in -1..1 - t, c * x) =
        c * (((1 - t) ^ 2 - (-1 : ℝ) ^ 2) / 2) := by
    calc
      (∫ x : ℝ in -1..1 - t, c * x) =
          c * (∫ x : ℝ in -1..1 - t, x) :=
        intervalIntegral.integral_const_mul c (fun x : ℝ ↦ x)
      _ = c * (((1 - t) ^ 2 - (-1 : ℝ) ^ 2) / 2) := by
        congr 1
        convert YoshidaEndpointOcticPotential.integral_pow_nat 1
          (-(1 : ℝ)) (1 - t) using 1 <;> norm_num
  repeat rw [hlinear]
  norm_num
  unfold cauchyLowTailCenteredCorrelation
  ring

set_option maxHeartbeats 5000000 in
private theorem integral_regularPolynomial_cauchyCorrelation_eq :
    (∫ t : ℝ in 0..2,
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
        cauchyLowTailCenteredCorrelation t) =
      (1 / 11746560 : ℝ) * Real.log 2 +
        (13 / 155669299200 : ℝ) * Real.log 2 ^ 3 +
        (8239195 / 73852957102253801472 : ℝ) * Real.log 2 ^ 5 := by
  unfold yoshidaRegularKernelPolynomial6 fourCellOperatorHalfWidth
    cauchyLowTailCenteredCorrelation
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  norm_num
  ring

set_option maxHeartbeats 5000000 in
private theorem factorTwoIntrinsicEnergy_cauchyLow_eq :
    factorTwoIntrinsicEnergy fourCellOddP11CauchyLowWitness =
      (6101 / 7315 : ℝ) := by
  unfold factorTwoIntrinsicEnergy fourCellOddP11CauchyLowWitness
    fourCellOddOneThreeFiveSevenNineLowProfile
    fourCellOddOneThreeFiveLowProfile factorTwoOddStructuralLowProfile
    centeredP1 centeredP3 factorTwoCenteredP5
  simp_rw [factorTwoCenteredP9_eq]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [YoshidaEndpointOcticPotential.integral_pow_nat]
  norm_num

set_option maxHeartbeats 5000000 in
private theorem factorTwoIntrinsicEnergy_cauchyTail_eq :
    factorTwoIntrinsicEnergy fourCellOddP11CauchyTailWitness =
      (55778431 / 539028000 : ℝ) := by
  unfold factorTwoIntrinsicEnergy fourCellOddP11CauchyTailWitness
    fourCellOddP11CauchyTailPolynomial
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_smul,
    smul_eq_mul]
  norm_num [centeredShiftedLegendreReal, shiftedLegendreReal,
    Polynomial.shiftedLegendre, Polynomial.eval_comp, Polynomial.eval_map,
    Polynomial.eval_finset_sum, Finset.sum_range_succ, Nat.choose,
    Polynomial.smul_eq_C_mul]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  norm_num

private theorem abs_regularKernel_cauchyCorrelation_lt :
    |∫ t : ℝ in 0..2,
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        cauchyLowTailCenteredCorrelation t| < (1 / 100000 : ℝ) := by
  let C : ℝ → ℝ := cauchyLowTailCenteredCorrelation
  let K : ℝ → ℝ := fun t ↦
    yoshidaRegularKernel (fourCellOperatorHalfWidth * t)
  let P : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) * C t
  let E : ℝ := fourCellWideRegularEnvelopeError C
  have hC : Continuous C := by
    dsimp only [C]
    unfold cauchyLowTailCenteredCorrelation
    fun_prop
  have hKmeas : Measurable K := by
    dsimp only [K]
    exact measurable_yoshidaRegularKernel.comp
      (measurable_const.mul measurable_id)
  have hKbound : ∀ t ∈ Icc (0 : ℝ) 2, |K t| ≤ (1 / 4 : ℝ) := by
    intro t ht
    have harg0 : 0 ≤ fourCellOperatorHalfWidth * t :=
      mul_nonneg (by unfold fourCellOperatorHalfWidth; positivity) ht.1
    have harg4 : fourCellOperatorHalfWidth * t ≤ 5 * Real.log 2 / 4 := by
      have hmul := mul_le_mul_of_nonneg_left ht.2
        (by unfold fourCellOperatorHalfWidth; positivity :
          0 ≤ fourCellOperatorHalfWidth)
      calc
        fourCellOperatorHalfWidth * t ≤
            fourCellOperatorHalfWidth * 2 := hmul
        _ = 5 * Real.log 2 / 4 := by
          unfold fourCellOperatorHalfWidth
          ring
    have hk0 := yoshidaRegularKernel_nonneg_fourCellRange harg0 harg4
    have hk1 := yoshidaRegularKernel_le_quarter harg0
    dsimp only [K]
    rw [abs_of_nonneg hk0]
    exact hk1
  have hfull : IntervalIntegrable (fun t : ℝ ↦ K t * C t)
      volume 0 2 :=
    intervalIntegrable_boundedLag_mul_continuous K C hKmeas hC
      (1 / 4 : ℝ) hKbound
  have hpoly : IntervalIntegrable (fun t : ℝ ↦
      yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) * C t)
      volume 0 2 := by
    exact (by
      unfold yoshidaRegularKernelPolynomial6
      fun_prop : Continuous (fun t : ℝ ↦
        yoshidaRegularKernelPolynomial6 (fourCellOperatorHalfWidth * t) *
          C t)).intervalIntegrable 0 2
  have hEeq : E = (∫ t : ℝ in 0..2, K t * C t) - P := by
    dsimp only [E, P]
    unfold fourCellWideRegularEnvelopeError
    rw [← intervalIntegral.integral_sub hfull hpoly]
    apply intervalIntegral.integral_congr
    intro t _ht
    dsimp only [K]
    ring
  have hPexact := integral_regularPolynomial_cauchyCorrelation_eq
  change P = _ at hPexact
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hloghi := YoshidaConstantBounds.strict_log_two_bounds.2
  have hlogseven : Real.log 2 < (7 / 10 : ℝ) := by
    exact hloghi.trans (by norm_num)
  have hlog3 : Real.log 2 ^ 3 < (7 / 10 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ hlogseven hlog0.le (by norm_num : (3 : ℕ) ≠ 0)
  have hlog5 : Real.log 2 ^ 5 < (7 / 10 : ℝ) ^ 5 :=
    pow_lt_pow_left₀ hlogseven hlog0.le (by norm_num : (5 : ℕ) ≠ 0)
  have hPpos : 0 < P := by
    rw [hPexact]
    positivity
  have hPabs : |P| < (1 / 1000000 : ℝ) := by
    rw [abs_of_pos hPpos, hPexact]
    nlinarith
  have hmass :=
    integral_abs_factorTwoCenteredCorrelationBilinear_le_half_energy_add
      fourCellOddP11CauchyLowWitness fourCellOddP11CauchyTailWitness
      (contDiff_fourCellOddOneThreeFiveSevenNineLowProfile
        (-(9 / 10 : ℝ)) 1 (-(1 / 5 : ℝ)) 0
          (1 / 10 : ℝ)).continuous
      contDiff_fourCellOddP11CauchyTailWitness.continuous
  simp_rw [factorTwoCenteredCorrelationBilinear_cauchy_eq] at hmass
  rw [factorTwoIntrinsicEnergy_cauchyLow_eq,
    factorTwoIntrinsicEnergy_cauchyTail_eq] at hmass
  have herr := abs_fourCellWideRegularEnvelopeError_le_sevenEighths C hC
  change |E| ≤ (1 / 80000 : ℝ) * (∫ t : ℝ in 0..2, |C t|)
    at herr
  have hEabs : |E| ≤ (3 / 500000 : ℝ) := by
    calc
      |E| ≤ (1 / 80000 : ℝ) * (∫ t : ℝ in 0..2, |C t|) :=
        herr
      _ ≤ (1 / 80000 : ℝ) *
          ((1 / 2 : ℝ) * (6101 / 7315 + 55778431 / 539028000)) := by
        exact mul_le_mul_of_nonneg_left hmass (by norm_num)
      _ ≤ (3 / 500000 : ℝ) := by norm_num
  have hdecomp : (∫ t : ℝ in 0..2, K t * C t) = P + E := by
    linarith [hEeq]
  change |∫ t : ℝ in 0..2, K t * C t| < (1 / 100000 : ℝ)
  rw [hdecomp]
  calc
    |P + E| ≤ |P| + |E| := abs_add_le P E
    _ < (1 / 1000000 : ℝ) + 3 / 500000 :=
      add_lt_add_of_lt_of_le hPabs hEabs
    _ < (1 / 100000 : ℝ) := by norm_num

private theorem abs_two_width_regular_cauchy_lt :
    |2 * fourCellOperatorHalfWidth *
      (∫ t : ℝ in 0..2,
        yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
          factorTwoCenteredCorrelationBilinear
            fourCellOddP11CauchyLowWitness
            fourCellOddP11CauchyTailWitness t)| <
      (1 / 100000 : ℝ) := by
  simp_rw [factorTwoCenteredCorrelationBilinear_cauchy_eq]
  have hI := abs_regularKernel_cauchyCorrelation_lt
  have hwidth0 : 0 ≤ 2 * fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have hwidth1 : 2 * fourCellOperatorHalfWidth < (1 : ℝ) := by
    have hlog := YoshidaConstantBounds.strict_log_two_bounds.2
    unfold fourCellOperatorHalfWidth
    nlinarith
  rw [abs_mul, abs_of_nonneg hwidth0]
  calc
    2 * fourCellOperatorHalfWidth *
        |∫ t : ℝ in 0..2,
          yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
            cauchyLowTailCenteredCorrelation t| ≤
      1 * |∫ t : ℝ in 0..2,
          yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
            cauchyLowTailCenteredCorrelation t| := by
        exact mul_le_mul_of_nonneg_right hwidth1.le (abs_nonneg _)
    _ < 1 * (1 / 100000 : ℝ) :=
      mul_lt_mul_of_pos_left hI (by norm_num)
    _ = (1 / 100000 : ℝ) := one_mul _

theorem fourCellOddCoreLocalBilinear_cauchyLow_tail_gt :
    (3 / 500 : ℝ) <
      fourCellOddCoreLocalBilinear fourCellOddP11CauchyLowWitness
        fourCellOddP11CauchyTailWitness := by
  rcases fourCellOddP11CauchyTailWitness_moments with
    ⟨hone, hthree, hfive, hseven, hnine⟩
  have hrow := fourCellOddCoreLocalBilinear_fiveMode_P11Plus_fullyReduced
    fourCellOddP11CauchyTailWitness
      contDiff_fourCellOddP11CauchyTailWitness
      odd_fourCellOddP11CauchyTailWitness
      hone hthree hfive hseven hnine
      (-(9 / 10 : ℝ)) 1 (-(1 / 5 : ℝ)) 0 (1 / 10 : ℝ)
  change fourCellOddCoreLocalBilinear fourCellOddP11CauchyLowWitness
      fourCellOddP11CauchyTailWitness =
    -(1 / 2 : ℝ) * fourCellOddEndpointStripOddRawPolarization
        fourCellOddP11CauchyLowWitness fourCellOddP11CauchyTailWitness +
      fourCellOddRetainedPrimePotentialBilinear
        fourCellOddP11CauchyLowWitness fourCellOddP11CauchyTailWitness -
      2 * fourCellOperatorHalfWidth *
        (∫ t : ℝ in 0..2,
          yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
            factorTwoCenteredCorrelationBilinear
              fourCellOddP11CauchyLowWitness
              fourCellOddP11CauchyTailWitness t) at hrow
  unfold fourCellOddRetainedPrimePotentialBilinear at hrow
  rw [cauchy_endpointStripOddRawPolarization_eq,
    cauchy_endpointStripEvenMassBilinear_eq,
    cauchy_endpointStripOddMassBilinear_eq,
    integral_endpointPotential_cauchyLow_mul_tail_eq] at hrow
  let R : ℝ := 2 * fourCellOperatorHalfWidth *
    (∫ t : ℝ in 0..2,
      yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
        factorTwoCenteredCorrelationBilinear
          fourCellOddP11CauchyLowWitness
          fourCellOddP11CauchyTailWitness t)
  have hRabs : |R| < (1 / 100000 : ℝ) := by
    simpa only [R] using abs_two_width_regular_cauchy_lt
  have hRhi := (le_abs_self R).trans_lt hRabs
  have hkfine := sqrt_two_mul_log_two_cauchy_fine_bounds.1
  have hk : (19 / 20 : ℝ) < Real.sqrt 2 * Real.log 2 := by
    nlinarith
  change fourCellOddCoreLocalBilinear fourCellOddP11CauchyLowWitness
      fourCellOddP11CauchyTailWitness =
    -(1 / 2 : ℝ) *
        (60851227229540918677 / 26077032089233398437500 : ℝ) +
      (Real.sqrt 2 * Real.log 2 *
          (1212113361834921004 / 186264514923095703125 : ℝ) +
        (2 - Real.sqrt 2 * Real.log 2) *
          (1428511930592826272 / 1303851604461669921875 : ℝ) +
        (93 / 50 : ℝ) * (-(3658121 / 85180914000 : ℝ))) - R at hrow
  rw [hrow]
  nlinarith

theorem cauchyLow_tail_strictly_reverses_weightedCauchy :
    fourCellOddCoreLocalQuadratic fourCellOddP11CauchyLowWitness *
        fourCellOddP1ExactTailWeight fourCellOddP11CauchyTailWitness <
      fourCellOddCoreLocalBilinear fourCellOddP11CauchyLowWitness
        fourCellOddP11CauchyTailWitness ^ 2 := by
  have hQ := fourCellOddCoreLocalQuadratic_cauchyLow_lt
  have hW := fourCellOddP1ExactTailWeight_cauchyTail_lt
  have hB := fourCellOddCoreLocalBilinear_cauchyLow_tail_gt
  have hQ0 : 0 ≤ fourCellOddCoreLocalQuadratic
      fourCellOddP11CauchyLowWitness := by
    unfold fourCellOddP11CauchyLowWitness
    rw [fourCellOddCoreLocalQuadratic_fiveMode_eq_coreExpression]
    exact fourCellOddFiveModeCoreExpression_nonneg _ _ _ _ _
  have hW0 : 0 ≤ fourCellOddP1ExactTailWeight
      fourCellOddP11CauchyTailWitness :=
    fourCellOddP1ExactTailWeight_nonneg
      fourCellOddP11CauchyTailWitness
      contDiff_fourCellOddP11CauchyTailWitness.continuous
  have hproduct :
      fourCellOddCoreLocalQuadratic fourCellOddP11CauchyLowWitness *
          fourCellOddP1ExactTailWeight fourCellOddP11CauchyTailWitness <
        (11 / 5000 : ℝ) * (2 / 125 : ℝ) := by
    calc
      fourCellOddCoreLocalQuadratic fourCellOddP11CauchyLowWitness *
          fourCellOddP1ExactTailWeight fourCellOddP11CauchyTailWitness ≤
        (11 / 5000 : ℝ) *
          fourCellOddP1ExactTailWeight fourCellOddP11CauchyTailWitness :=
        mul_le_mul_of_nonneg_right hQ.le hW0
      _ < (11 / 5000 : ℝ) * (2 / 125 : ℝ) :=
        mul_lt_mul_of_pos_left hW (by norm_num)
  calc
    fourCellOddCoreLocalQuadratic fourCellOddP11CauchyLowWitness *
        fourCellOddP1ExactTailWeight fourCellOddP11CauchyTailWitness <
      (11 / 5000 : ℝ) * (2 / 125 : ℝ) := hproduct
    _ < (3 / 500 : ℝ) ^ 2 := by norm_num
    _ < fourCellOddCoreLocalBilinear fourCellOddP11CauchyLowWitness
        fourCellOddP11CauchyTailWitness ^ 2 := by nlinarith

private theorem cauchyLowWitness_is_coupledLoewnerSelectorProfile :
    ∃ s t : ℝ,
      fourCellOddP11CoupledLoewnerSelectorProfile
          1 (-(1 / 5 : ℝ)) 0 (1 / 10 : ℝ) s t =
        fourCellOddP11CauchyLowWitness := by
  let p : ℝ → ℝ :=
    fourCellOddOneThreeFiveSevenNineLowProfile
      0 1 (-(1 / 5 : ℝ)) 0 (1 / 10 : ℝ)
  let A : ℝ := fourCellOddCoreLocalQuadratic centeredP1
  let b : ℝ := fourCellOddCoreLocalBilinear centeredP1 p
  let F : ℝ := fourCellOddP11FiniteCorrectedReserve
    1 (-(1 / 5 : ℝ)) 0 (1 / 10 : ℝ)
  have hA : 0 < A := by
    dsimp only [A]
    exact fourCellOddCoreLocalQuadratic_centeredP1_pos
  have hcoeff :
      (![1, (-(1 / 5 : ℝ)), 0, (1 / 10 : ℝ)] : Fin 4 → ℝ) ≠ 0 := by
    intro hzero
    have hfirst := congrFun hzero (0 : Fin 4)
    norm_num at hfirst
  have hF : 0 < F := by
    dsimp only [F]
    exact fourCellOddP11FiniteCorrectedReserve_pos
      1 (-(1 / 5 : ℝ)) 0 (1 / 10 : ℝ) hcoeff
  let t : ℝ := 1 / A
  let s : ℝ := (-(9 / 10 : ℝ) + t * b) / F
  refine ⟨s, t, ?_⟩
  rw [fourCellOddP11CoupledLoewnerSelectorProfile_eq_lowProfile]
  dsimp only
  change fourCellOddOneThreeFiveSevenNineLowProfile
      (F * s - t * b) (t * A * 1) (t * A * (-(1 / 5 : ℝ)))
        (t * A * 0) (t * A * (1 / 10 : ℝ)) =
    fourCellOddP11CauchyLowWitness
  have htA : t * A = 1 := by
    dsimp only [t]
    field_simp [hA.ne']
  have hc : F * s - t * b = (-(9 / 10 : ℝ)) := by
    dsimp only [s]
    field_simp [hF.ne']
    ring
  rw [hc, htA]
  norm_num [fourCellOddP11CauchyLowWitness]

theorem not_fourCellOddP11CoupledSelectorLoewnerCertificate :
    ¬ FourCellOddP11CoupledSelectorLoewnerCertificate := by
  intro hcertificate
  have hselector :=
    (fourCellOddP11CoupledSelectorLoewnerCertificate_iff_explicitSelectorCauchy).mp
      hcertificate
  rcases cauchyLowWitness_is_coupledLoewnerSelectorProfile with
    ⟨s, t, hprofile⟩
  rcases fourCellOddP11CauchyTailWitness_moments with
    ⟨hone, hthree, hfive, hseven, hnine⟩
  have hcauchy := hselector
    1 (-(1 / 5 : ℝ)) 0 (1 / 10 : ℝ)
    fourCellOddP11CauchyTailWitness
    contDiff_fourCellOddP11CauchyTailWitness
    odd_fourCellOddP11CauchyTailWitness
    hone hthree hfive hseven hnine s t
  rw [hprofile] at hcauchy
  have hreverse := cauchyLow_tail_strictly_reverses_weightedCauchy
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP11ExplicitSelectorCauchyStructural
