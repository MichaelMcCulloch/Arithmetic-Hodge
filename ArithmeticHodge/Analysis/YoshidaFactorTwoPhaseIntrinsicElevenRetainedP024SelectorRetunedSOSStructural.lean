import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorSOSStructural

set_option autoImplicit false

open Matrix Polynomial

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorRetunedSOSStructural

open MatrixIntervalQuadraticSOS
open ShiftedLegendreLogEnergyOrthogonalProjection
open ThreeByThreePositiveMixedDeterminant
open ThreeByThreeRankOneSchur
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024Structural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorSOSStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedRepresentersStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedSelectorHomogeneityStructural
open YoshidaFactorTwoPhaseSingularWeightedCauchyStructural

noncomputable section

/-!
# Retuned exact matrix-SOS for the retained P024 boundary pencil

The reciprocal-weight polynomial majorant is too lossy in the endpoint
directions.  This certificate instead keeps the exact selector Gram entries
and changes only the nonunique reserve and skew block of the quadratic matrix
pencil.  The reserve and skew are rational; no phase subdivision occurs.
-/

/-- Rational interval reserve for the exact boundary-gap pencil. -/
def retainedP024SelectorRetunedSOSReserve :
    Matrix (Fin 3) (Fin 3) ℝ :=
  symmetricMatrix3
    (110 / 1000 : ℝ) (100 / 1000 : ℝ) (-15 / 1000 : ℝ)
    (95 / 1000 : ℝ) (5 / 1000 : ℝ) (87 / 1000 : ℝ)

/-- The retuned reserve is strictly positive by exact rational pivots. -/
theorem retainedP024SelectorRetunedSOSReserve_posDef :
    retainedP024SelectorRetunedSOSReserve.PosDef := by
  unfold retainedP024SelectorRetunedSOSReserve
  apply symmetricMatrix3_posDef
  · norm_num
  · unfold leadingMinorTwo
    norm_num
  · unfold symmetricDeterminant
    norm_num

theorem retainedP024SelectorRetunedSOSReserve_posSemidef :
    retainedP024SelectorRetunedSOSReserve.PosSemidef :=
  retainedP024SelectorRetunedSOSReserve_posDef.posSemidef

/-- Rational skew freedom in the two off-diagonal affine-lift blocks. -/
def retainedP024SelectorRetunedSOSSkew :
    Matrix (Fin 3) (Fin 3) ℝ :=
  ![![0, (6 / 1000 : ℝ), (34 / 1000 : ℝ)],
    ![(-6 / 1000 : ℝ), 0, (29 / 1000 : ℝ)],
    ![(-34 / 1000 : ℝ), (-29 / 1000 : ℝ), 0]]

/-- Fixed exact Gram for the retuned degree-two matrix-SOS.  Its entries
remain the genuine analytic selector Gram entries through the three boundary
coefficient matrices; only the reserve and skew freedom are rationally
retuned. -/
def retainedP024SelectorRetunedSOSGram :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  Matrix.fromBlocks
    (retainedP024SelectorBoundaryGapConstant -
      retainedP024SelectorRetunedSOSReserve)
    ((1 / 2 : ℝ) • retainedP024SelectorBoundaryGapLinear +
      retainedP024SelectorRetunedSOSSkew)
    ((1 / 2 : ℝ) • retainedP024SelectorBoundaryGapLinear -
      retainedP024SelectorRetunedSOSSkew)
    (retainedP024SelectorBoundaryGapQuadratic +
      retainedP024SelectorRetunedSOSReserve)

/-- Exact retuned matrix-SOS identity for every real phase. -/
theorem retainedP024SelectorBoundaryGapMatrix_eq_retuned_sos (a : ℝ) :
    retainedP024SelectorBoundaryGapMatrix a =
      (affineLiftMatrix (n := Fin 3) a)ᴴ *
          retainedP024SelectorRetunedSOSGram *
          affineLiftMatrix (n := Fin 3) a +
        (1 - a ^ 2) • retainedP024SelectorRetunedSOSReserve := by
  rw [retainedP024SelectorBoundaryGapMatrix_eq_coefficients,
    retainedP024SelectorRetunedSOSGram,
    affineLiftMatrix_conjTranspose_mul_fromBlocks_mul_affineLiftMatrix]
  module

/-- The retuned fixed Gram is the sole remaining input for the sharp P024
selector handoff. -/
theorem exists_sharpRetunedP024Selector_of_retunedSOS
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hGram : retainedP024SelectorRetunedSOSGram.PosDef)
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
    retainedP024SelectorRetunedSOSGram
    retainedP024SelectorRetunedSOSReserve
    hGram retainedP024SelectorRetunedSOSReserve_posSemidef
    (retainedP024BoundaryGap_eq_matrixQuadratic a)
    (retainedP024SelectorBoundaryGapMatrix_eq_retuned_sos a)
    c0 c2 c4

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorRetunedSOSStructural
