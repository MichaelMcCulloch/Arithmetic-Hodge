import ArithmeticHodge.Analysis.FiniteIntervalMultiplierGramLoewnerStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorRemainderTraceStructural

set_option autoImplicit false

open Matrix MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorReciprocalLoewnerStructural

open FiniteIntervalMultiplierGramLoewnerStructural
open FiniteIntervalWeightedGramTraceStructural
open MatrixIntervalQuadraticSOS
open ShiftedLegendreLogEnergyOrthogonalProjection
open YoshidaEndpointEvenAtanhReciprocalMajorant
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorQuotientStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorRemainderGramStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorRemainderTraceStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorSOSStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedReciprocalMajorantStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedRepresentersStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedSelectorHomogeneityStructural
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseSingularWeightedCauchyStructural

noncomputable section

/-!
# Full-matrix reciprocal Loewner bounds for the retained P024 selector

The reciprocal polynomial bounds are applied before taking a trace.  The
resulting upper Grams preserve every coefficient direction.  The odd upper
gap is shifted into the interval SOS reserve, which exactly compensates the
opposite signs of the alternating Gram in the affine lift.
-/

/-- Reciprocal-polynomial upper Gram for the six retained even remainder
rows. -/
def retainedP024SelectorWholeEvenRemainderReciprocalUpperGram :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  finiteIntervalMultiplierGram (-1) 1
    (fun x ↦ (205 / 39 : ℝ) * atanhTailWeightReciprocalMajorant x)
    retainedP024SelectorWholeEvenShiftedRemainder

/-- Reciprocal-polynomial upper Gram for the original three alternating
remainder rows. -/
def retainedP024SelectorAlternatingRemainderReciprocalUpperGram :
    Matrix (Fin 3) (Fin 3) ℝ :=
  finiteIntervalMultiplierGram (-1) 1
    (fun x ↦ (41 / 2 : ℝ) * atanhTailWeightReciprocalMajorant x)
    retainedP024SelectorAlternatingShiftedRemainder

/-- The even reciprocal-upper entries are unconditionally integrable: exact
pole cancellation leaves bounded rows, and the reciprocal majorant is a
continuous polynomial. -/
theorem intervalIntegrable_retainedP024SelectorWholeEvenRemainderReciprocalUpper
    (i j : Fin 3 ⊕ Fin 3) :
    IntervalIntegrable
      (fun x ↦
        ((205 / 39 : ℝ) * atanhTailWeightReciprocalMajorant x) *
          retainedP024SelectorWholeEvenShiftedRemainder i x *
          retainedP024SelectorWholeEvenShiftedRemainder j x)
      volume (-1) 1 := by
  have hcross :=
    intervalIntegrable_retainedP024SelectorWholeEvenShiftedRemainder_mul i j
  have hmult : Continuous
      (fun x : ℝ ↦ (205 / 39 : ℝ) * atanhTailWeightReciprocalMajorant x) := by
    unfold atanhTailWeightReciprocalMajorant
      atanhTailWeightReciprocalMajorantPolynomial
    fun_prop
  simpa only [mul_assoc] using hcross.continuousOn_mul hmult.continuousOn

/-- The alternating reciprocal-upper entries are unconditionally integrable
for the same structural reason. -/
theorem intervalIntegrable_retainedP024SelectorAlternatingRemainderReciprocalUpper
    (i j : Fin 3) :
    IntervalIntegrable
      (fun x ↦
        ((41 / 2 : ℝ) * atanhTailWeightReciprocalMajorant x) *
          retainedP024SelectorAlternatingShiftedRemainder i x *
          retainedP024SelectorAlternatingShiftedRemainder j x)
      volume (-1) 1 := by
  have hcross :=
    intervalIntegrable_retainedP024SelectorAlternatingShiftedRemainder_mul i j
  have hmult : Continuous
      (fun x : ℝ ↦ (41 / 2 : ℝ) * atanhTailWeightReciprocalMajorant x) := by
    unfold atanhTailWeightReciprocalMajorant
      atanhTailWeightReciprocalMajorantPolynomial
    fun_prop
  simpa only [mul_assoc] using hcross.continuousOn_mul hmult.continuousOn

/-- The original alternating remainder Gram is its generic interval weighted
Gram. -/
theorem retainedP024SelectorAlternatingShiftedRemainderGram_eq_intervalWeightedGram :
    retainedP024SelectorAlternatingShiftedRemainderGram =
      finiteIntervalWeightedGram (-1) 1
        factorTwoIntrinsicElevenRetainedOddWeight
        retainedP024SelectorAlternatingShiftedRemainder := by
  ext i j
  rw [retainedP024SelectorAlternatingShiftedRemainderGram_apply]
  rfl

/-- The reciprocal-polynomial even Gram is an unconditional full Loewner
upper certificate. -/
theorem retainedP024SelectorWholeEvenRemainderReciprocalUpperGram_sub_posSemidef :
    (retainedP024SelectorWholeEvenRemainderReciprocalUpperGram -
      retainedP024SelectorWholeEvenShiftedRemainderGram).PosSemidef := by
  rw [retainedP024SelectorWholeEvenShiftedRemainderGram_eq_intervalWeightedGram]
  exact finiteIntervalMultiplierGram_sub_weightedGram_posSemidef_of_inv_le_Ioo
    (-1) 1 (by norm_num)
    factorTwoIntrinsicElevenRetainedEvenWeight
    (fun x ↦ (205 / 39 : ℝ) * atanhTailWeightReciprocalMajorant x)
    retainedP024SelectorWholeEvenShiftedRemainder
    intervalIntegrable_retainedP024SelectorWholeEvenShiftedRemainderCross
    intervalIntegrable_retainedP024SelectorWholeEvenRemainderReciprocalUpper
    (fun _x hx ↦ inv_retainedEvenWeight_le_reciprocalMajorant hx)

/-- The reciprocal-polynomial alternating Gram is a full Loewner upper
certificate for the original odd rows, before any projection contraction. -/
theorem retainedP024SelectorAlternatingRemainderReciprocalUpperGram_sub_posSemidef
    : (retainedP024SelectorAlternatingRemainderReciprocalUpperGram -
      retainedP024SelectorAlternatingShiftedRemainderGram).PosSemidef := by
  rw [retainedP024SelectorAlternatingShiftedRemainderGram_eq_intervalWeightedGram]
  exact finiteIntervalMultiplierGram_sub_weightedGram_posSemidef_of_inv_le_Ioo
    (-1) 1 (by norm_num)
    factorTwoIntrinsicElevenRetainedOddWeight
    (fun x ↦ (41 / 2 : ℝ) * atanhTailWeightReciprocalMajorant x)
    retainedP024SelectorAlternatingShiftedRemainder
    intervalIntegrable_retainedP024SelectorAlternatingShiftedRemainderCross
    intervalIntegrable_retainedP024SelectorAlternatingRemainderReciprocalUpper
    (fun _x hx ↦ inv_retainedOddWeight_le_reciprocalMajorant hx)

/-- Inverse-weight-free fixed Gram obtained by replacing both negative
remainder occurrences with their directional reciprocal upper Grams. -/
def retainedP024SelectorReciprocalLoewnerCore :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  retainedP024SharpLowSOSGram -
      retainedP024SelectorWholeEvenNonquotientGram -
    retainedP024SelectorWholeEvenRemainderReciprocalUpperGram +
    retainedP024AlternatingSignedLift
      retainedP024SelectorAlternatingNonquotientGram +
    retainedP024AlternatingSignedLift
      retainedP024SelectorAlternatingRemainderReciprocalUpperGram

/-- Exact SOS Gram after shifting the odd reciprocal upper gap into the
interval reserve. -/
def retainedP024SelectorReciprocalShiftedSOSGram :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  retainedP024SelectorAsymmetricSOSGram +
    retainedP024AlternatingSignedLift
      (retainedP024SelectorAlternatingRemainderReciprocalUpperGram -
        retainedP024SelectorAlternatingShiftedRemainderGram)

/-- The matching interval reserve absorbs exactly the same odd upper gap. -/
def retainedP024SelectorReciprocalShiftedSOSReserve :
    Matrix (Fin 3) (Fin 3) ℝ :=
  retainedP024SelectorSOSReserve +
    (retainedP024SelectorAlternatingRemainderReciprocalUpperGram -
      retainedP024SelectorAlternatingShiftedRemainderGram)

/-- The phase-dependent core actually seen by the P024 coefficient vector.
Unlike the fixed `6 x 6` Loewner core, this compressed `3 x 3` pencil retains
the positive interval reserve and therefore asks for no positivity in affine
directions that never occur. -/
def retainedP024SelectorReciprocalAffineCore (a : ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  (affineLiftMatrix (n := Fin 3) a)ᴴ *
      retainedP024SelectorReciprocalLoewnerCore *
      affineLiftMatrix (n := Fin 3) a +
    (1 - a ^ 2) • retainedP024SelectorSOSReserve

/-- The shifted SOS Gram is the inverse-weight-free Loewner core plus the
positive even upper-certificate gap. -/
theorem retainedP024SelectorReciprocalShiftedSOSGram_eq_core_add_evenGap :
    retainedP024SelectorReciprocalShiftedSOSGram =
      retainedP024SelectorReciprocalLoewnerCore +
        (retainedP024SelectorWholeEvenRemainderReciprocalUpperGram -
          retainedP024SelectorWholeEvenShiftedRemainderGram) := by
  unfold retainedP024SelectorReciprocalShiftedSOSGram
  rw [retainedP024SelectorAsymmetricSOSGram_eq_nonquotient_remainders]
  unfold retainedP024SelectorReciprocalLoewnerCore
    retainedP024AlternatingSignedLift
  ext i j
  rcases i with i | i <;> rcases j with j | j
  all_goals simp <;> module

/-- An affine lift turns a signed alternating block into the negative
interval reserve with the exact factor `1 - a^2`. -/
theorem affineLiftMatrix_conjTranspose_mul_retainedP024AlternatingSignedLift_mul
    (G : Matrix (Fin 3) (Fin 3) ℝ) (a : ℝ) :
    (affineLiftMatrix (n := Fin 3) a)ᴴ *
        retainedP024AlternatingSignedLift G *
        affineLiftMatrix (n := Fin 3) a =
      -(1 - a ^ 2) • G := by
  unfold retainedP024AlternatingSignedLift
  rw [affineLiftMatrix_conjTranspose_mul_fromBlocks_mul_affineLiftMatrix]
  ext i j
  simp
  ring

/-- The boundary gap has an exact interval-SOS representation after the odd
Loewner gap is shifted from the affine Gram into the reserve. -/
theorem retainedP024SelectorBoundaryGapMatrix_eq_reciprocalShifted_sos
    (a : ℝ) :
    retainedP024SelectorBoundaryGapMatrix a =
      (affineLiftMatrix (n := Fin 3) a)ᴴ *
          retainedP024SelectorReciprocalShiftedSOSGram *
          affineLiftMatrix (n := Fin 3) a +
        (1 - a ^ 2) •
          retainedP024SelectorReciprocalShiftedSOSReserve := by
  rw [retainedP024SelectorBoundaryGapMatrix_eq_asymmetric_sos]
  unfold retainedP024SelectorReciprocalShiftedSOSGram
    retainedP024SelectorReciprocalShiftedSOSReserve
  simp only [Matrix.mul_add, Matrix.add_mul, smul_add]
  rw [affineLiftMatrix_conjTranspose_mul_retainedP024AlternatingSignedLift_mul]
  module

/-- Exact Loewner decomposition of the boundary gap into the compressed
affine core and the two unconditional reciprocal-upper Gram gaps. -/
theorem retainedP024SelectorBoundaryGapMatrix_eq_affineCore_add_gaps
    (a : ℝ) :
    retainedP024SelectorBoundaryGapMatrix a =
      retainedP024SelectorReciprocalAffineCore a +
        (affineLiftMatrix (n := Fin 3) a)ᴴ *
          (retainedP024SelectorWholeEvenRemainderReciprocalUpperGram -
            retainedP024SelectorWholeEvenShiftedRemainderGram) *
          affineLiftMatrix (n := Fin 3) a +
        (1 - a ^ 2) •
          (retainedP024SelectorAlternatingRemainderReciprocalUpperGram -
            retainedP024SelectorAlternatingShiftedRemainderGram) := by
  rw [retainedP024SelectorBoundaryGapMatrix_eq_reciprocalShifted_sos,
    retainedP024SelectorReciprocalShiftedSOSGram_eq_core_add_evenGap]
  unfold retainedP024SelectorReciprocalAffineCore
    retainedP024SelectorReciprocalShiftedSOSReserve
  simp only [Matrix.mul_add, Matrix.add_mul, smul_add]
  module

/-- Positive semidefiniteness of the compressed `3 x 3` affine core is the
only phase-dependent input needed for the full P024 boundary gap. -/
theorem retainedP024SelectorBoundaryGapMatrix_posSemidef_of_affineCore
    (a : ℝ) (ha : a ^ 2 ≤ 1)
    (hAffine :
      (retainedP024SelectorReciprocalAffineCore a).PosSemidef) :
    (retainedP024SelectorBoundaryGapMatrix a).PosSemidef := by
  have hEvenLift :=
    retainedP024SelectorWholeEvenRemainderReciprocalUpperGram_sub_posSemidef.conjTranspose_mul_mul_same
      (affineLiftMatrix (n := Fin 3) a)
  have hOddScaled :=
    retainedP024SelectorAlternatingRemainderReciprocalUpperGram_sub_posSemidef.smul
      (sub_nonneg.mpr ha)
  rw [retainedP024SelectorBoundaryGapMatrix_eq_affineCore_add_gaps]
  exact (hAffine.add hEvenLift).add hOddScaled

/-- Positive definiteness of the inverse-weight-free core transfers to the
shifted SOS Gram through the full even Loewner gap. -/
theorem retainedP024SelectorReciprocalShiftedSOSGram_posDef_of_core
    (hCore : retainedP024SelectorReciprocalLoewnerCore.PosDef) :
    retainedP024SelectorReciprocalShiftedSOSGram.PosDef := by
  rw [retainedP024SelectorReciprocalShiftedSOSGram_eq_core_add_evenGap]
  exact hCore.add_posSemidef
    retainedP024SelectorWholeEvenRemainderReciprocalUpperGram_sub_posSemidef

/-- The shifted reserve is positive semidefinite through the full odd
Loewner gap. -/
theorem retainedP024SelectorReciprocalShiftedSOSReserve_posSemidef
    : retainedP024SelectorReciprocalShiftedSOSReserve.PosSemidef := by
  unfold retainedP024SelectorReciprocalShiftedSOSReserve
  exact retainedP024SelectorSOSReserve_posSemidef.add
    retainedP024SelectorAlternatingRemainderReciprocalUpperGram_sub_posSemidef

/-- Full-direction P024 selector handoff.  Positivity of one
inverse-weight-free fixed core implies the production selector inequality at
every point of the closed phase disk; reciprocal-upper integrability is now
discharged unconditionally. -/
theorem exists_sharpRetunedP024Selector_of_reciprocalLoewner
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hCore : retainedP024SelectorReciprocalLoewnerCore.PosDef)
    (c0 c2 c4 : ℝ) :
    ∃ qE qO : ℝ[X],
      qE.natDegree < 11 ∧ qO.natDegree < 11 ∧
      factorTwoIntrinsicElevenRetainedConstrainedSelectorDual
          (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
            (1 / 512 : ℝ) (retainedP024Polynomial c0 c2 c4) 0 a b)
          (factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt
            (1 / 512 : ℝ) (retainedP024Polynomial c0 c2 c4) 0 a b)
          qE qO ≤
        factorTwoEndpointChannelPhase
            (centeredPolynomialLift (retainedP024Polynomial c0 c2 c4))
            (centeredPolynomialLift 0) a b -
          (1 / 8192 : ℝ) * factorTwoPhaseSingularWeightedEnergy
            (centeredPolynomialLift (retainedP024Polynomial c0 c2 c4))
            (centeredPolynomialLift 0) a b := by
  exact exists_sharpRetunedP024Selector_of_boundary_matrix_sos
    a b hab
    retainedP024SelectorPlus0 retainedP024SelectorPlus2
    retainedP024SelectorPlus4 retainedP024SelectorMinus0
    retainedP024SelectorMinus2 retainedP024SelectorMinus4
    retainedP024SelectorAlt0 retainedP024SelectorAlt2
    retainedP024SelectorAlt4
    retainedP024SelectorPlus0_natDegree_lt
    retainedP024SelectorPlus2_natDegree_lt
    retainedP024SelectorPlus4_natDegree_lt
    retainedP024SelectorMinus0_natDegree_lt
    retainedP024SelectorMinus2_natDegree_lt
    retainedP024SelectorMinus4_natDegree_lt
    retainedP024SelectorAlt0_natDegree_lt
    retainedP024SelectorAlt2_natDegree_lt
    retainedP024SelectorAlt4_natDegree_lt
    (retainedP024SelectorBoundaryGapMatrix a)
    retainedP024SelectorReciprocalShiftedSOSGram
    retainedP024SelectorReciprocalShiftedSOSReserve
    (retainedP024SelectorReciprocalShiftedSOSGram_posDef_of_core hCore)
    retainedP024SelectorReciprocalShiftedSOSReserve_posSemidef
    (retainedP024BoundaryGap_eq_matrixQuadratic a)
    (retainedP024SelectorBoundaryGapMatrix_eq_reciprocalShifted_sos a)
    c0 c2 c4

/-- Sharp P024 selector handoff from the exact phase-dependent `3 x 3`
affine core.  This is strictly weaker than positivity of the fixed `6 x 6`
Loewner core because only affine-lift directions are retained. -/
theorem exists_sharpRetunedP024Selector_of_reciprocalAffineCore
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hAffine :
      (retainedP024SelectorReciprocalAffineCore a).PosSemidef)
    (c0 c2 c4 : ℝ) :
    ∃ qE qO : ℝ[X],
      qE.natDegree < 11 ∧ qO.natDegree < 11 ∧
      factorTwoIntrinsicElevenRetainedConstrainedSelectorDual
          (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
            (1 / 512 : ℝ) (retainedP024Polynomial c0 c2 c4) 0 a b)
          (factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt
            (1 / 512 : ℝ) (retainedP024Polynomial c0 c2 c4) 0 a b)
          qE qO ≤
        factorTwoEndpointChannelPhase
            (centeredPolynomialLift (retainedP024Polynomial c0 c2 c4))
            (centeredPolynomialLift 0) a b -
          (1 / 8192 : ℝ) * factorTwoPhaseSingularWeightedEnergy
            (centeredPolynomialLift (retainedP024Polynomial c0 c2 c4))
            (centeredPolynomialLift 0) a b := by
  have ha : a ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg b]
  have hGap :
      (retainedP024SelectorBoundaryGapMatrix a).PosSemidef :=
    retainedP024SelectorBoundaryGapMatrix_posSemidef_of_affineCore
      a ha hAffine
  have hboundary : ∀ d0 d2 d4 : ℝ,
      retainedP024BoundaryChordCost (1 / 512 : ℝ)
          (retainedP024Polynomial d0 d2 d4)
          (threeSelectorPolynomial d0 d2 d4
            retainedP024SelectorPlus0 retainedP024SelectorPlus2
            retainedP024SelectorPlus4)
          (threeSelectorPolynomial d0 d2 d4
            retainedP024SelectorMinus0 retainedP024SelectorMinus2
            retainedP024SelectorMinus4)
          (threeSelectorPolynomial d0 d2 d4
            retainedP024SelectorAlt0 retainedP024SelectorAlt2
            retainedP024SelectorAlt4) a ≤
        ThreeByThreeRankOneSchur.symmetricQuadratic
          (retainedP024SharpLow00 a)
          (retainedP024SharpLow02 a)
          (retainedP024SharpLow04 a)
          (retainedP024SharpLow22 a)
          (retainedP024SharpLow24 a)
          (retainedP024SharpLow44 a)
          d0 d2 d4 := by
    intro d0 d2 d4
    let x : Fin 3 → ℝ := ![d0, d2, d4]
    have hnonneg := hGap.re_dotProduct_nonneg x
    have hidentity :=
      retainedP024BoundaryGap_eq_matrixQuadratic a d0 d2 d4
    change 0 ≤ star x ⬝ᵥ
      (retainedP024SelectorBoundaryGapMatrix a *ᵥ x) at hnonneg
    rw [← hidentity] at hnonneg
    linarith
  exact exists_sharpRetunedP024Selector_of_boundary_chord
    a b hab
    retainedP024SelectorPlus0 retainedP024SelectorPlus2
    retainedP024SelectorPlus4 retainedP024SelectorMinus0
    retainedP024SelectorMinus2 retainedP024SelectorMinus4
    retainedP024SelectorAlt0 retainedP024SelectorAlt2
    retainedP024SelectorAlt4
    retainedP024SelectorPlus0_natDegree_lt
    retainedP024SelectorPlus2_natDegree_lt
    retainedP024SelectorPlus4_natDegree_lt
    retainedP024SelectorMinus0_natDegree_lt
    retainedP024SelectorMinus2_natDegree_lt
    retainedP024SelectorMinus4_natDegree_lt
    retainedP024SelectorAlt0_natDegree_lt
    retainedP024SelectorAlt2_natDegree_lt
    retainedP024SelectorAlt4_natDegree_lt
    hboundary c0 c2 c4

end


end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorReciprocalLoewnerStructural
