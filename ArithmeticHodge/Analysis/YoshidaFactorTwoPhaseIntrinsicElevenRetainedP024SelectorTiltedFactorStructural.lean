import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorSOSStructural

set_option autoImplicit false

open Matrix Polynomial

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorTiltedFactorStructural

open ThreeByThreePositiveMixedDeterminant
open ShiftedLegendreLogEnergyOrthogonalProjection
open YoshidaEndpointEvenStructuralReduction
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorSOSStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024Structural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedRepresentersStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedSelectorHomogeneityStructural
open YoshidaFactorTwoPhaseSingularWeightedCauchyStructural

noncomputable section

/-!
# Tilted factorization of the retained P024 boundary pencil

The exact quadratic boundary-gap pencil is factored as one congruence and two
positive scalar multiples of fixed `3 x 3` matrices.  This retains the full
phase dependence while replacing the fixed `6 x 6` matrix-SOS gate by three
smaller structural gates.
-/

/-- Rational diagonal tilt chosen to balance the three fixed residual gates. -/
def retainedP024SelectorTiltedDiagonal : Matrix (Fin 3) (Fin 3) ℝ :=
  diagonal ![(-81 / 50 : ℝ), (-77 / 50 : ℝ), (-8 / 5 : ℝ)]

/-- The congruence core.  Its entrywise multipliers solve exactly
`L = A T + Tᴴ A` for the diagonal tilt `T`. -/
def retainedP024SelectorTiltedCore : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![(-25 / 81 : ℝ) * retainedP024SelectorBoundaryGapLinear 0 0,
      (-25 / 79 : ℝ) * retainedP024SelectorBoundaryGapLinear 0 1,
      (-50 / 161 : ℝ) * retainedP024SelectorBoundaryGapLinear 0 2],
    ![(-25 / 79 : ℝ) * retainedP024SelectorBoundaryGapLinear 1 0,
      (-25 / 77 : ℝ) * retainedP024SelectorBoundaryGapLinear 1 1,
      (-50 / 157 : ℝ) * retainedP024SelectorBoundaryGapLinear 1 2],
    ![(-50 / 161 : ℝ) * retainedP024SelectorBoundaryGapLinear 2 0,
      (-50 / 157 : ℝ) * retainedP024SelectorBoundaryGapLinear 2 1,
      (-5 / 16 : ℝ) * retainedP024SelectorBoundaryGapLinear 2 2]]

/-- Constant residual after removing the tilted congruence core. -/
def retainedP024SelectorTiltedConstantReserve :
    Matrix (Fin 3) (Fin 3) ℝ :=
  retainedP024SelectorBoundaryGapConstant - retainedP024SelectorTiltedCore

/-- Quadratic residual after removing the tilted congruence and shifting the
constant reserve into the interval multiplier. -/
def retainedP024SelectorTiltedQuadraticReserve :
    Matrix (Fin 3) (Fin 3) ℝ :=
  retainedP024SelectorBoundaryGapQuadratic +
      retainedP024SelectorTiltedConstantReserve -
    retainedP024SelectorTiltedDiagonalᴴ *
      retainedP024SelectorTiltedCore * retainedP024SelectorTiltedDiagonal

/-- Phase-dependent congruence factor. -/
def retainedP024SelectorTiltedFactor (a : ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  1 + a • retainedP024SelectorTiltedDiagonal

/-- The rational diagonal tilt is Hermitian. -/
theorem retainedP024SelectorTiltedDiagonal_conjTranspose :
    retainedP024SelectorTiltedDiagonalᴴ =
      retainedP024SelectorTiltedDiagonal := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [retainedP024SelectorTiltedDiagonal]

/-- The chosen entrywise multipliers solve the tilted linear coefficient
equation exactly. -/
theorem retainedP024SelectorBoundaryGapLinear_eq_tilted :
    retainedP024SelectorBoundaryGapLinear =
      retainedP024SelectorTiltedCore * retainedP024SelectorTiltedDiagonal +
        retainedP024SelectorTiltedDiagonalᴴ *
          retainedP024SelectorTiltedCore := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [retainedP024SelectorTiltedDiagonal,
      retainedP024SelectorTiltedCore, Matrix.mul_apply,
      Fin.sum_univ_succ] <;>
    ring

/-- Exact structural factorization of the full boundary-gap pencil. -/
theorem retainedP024SelectorBoundaryGapMatrix_eq_tilted_factorization
    (a : ℝ) :
    retainedP024SelectorBoundaryGapMatrix a =
      (retainedP024SelectorTiltedFactor a)ᴴ *
          retainedP024SelectorTiltedCore *
          retainedP024SelectorTiltedFactor a +
        a ^ 2 • retainedP024SelectorTiltedQuadraticReserve +
        (1 - a ^ 2) • retainedP024SelectorTiltedConstantReserve := by
  rw [retainedP024SelectorBoundaryGapMatrix_eq_coefficients]
  unfold retainedP024SelectorTiltedFactor
  rw [conjTranspose_add, conjTranspose_one, conjTranspose_smul,
    retainedP024SelectorTiltedDiagonal_conjTranspose,
    retainedP024SelectorBoundaryGapLinear_eq_tilted]
  simp only [star_trivial]
  unfold retainedP024SelectorTiltedQuadraticReserve
    retainedP024SelectorTiltedConstantReserve
  rw [retainedP024SelectorTiltedDiagonal_conjTranspose]
  simp only [Matrix.add_mul, Matrix.mul_add, one_mul, mul_one,
    Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_sub]
  module

/-- The three fixed positive-semidefinite gates imply positivity of the exact
boundary pencil at every point of the interval. -/
theorem retainedP024SelectorBoundaryGapMatrix_posSemidef_of_tilted
    (a : ℝ) (ha : a ^ 2 ≤ 1)
    (hCore : retainedP024SelectorTiltedCore.PosSemidef)
    (hConstant : retainedP024SelectorTiltedConstantReserve.PosSemidef)
    (hQuadratic : retainedP024SelectorTiltedQuadraticReserve.PosSemidef) :
    (retainedP024SelectorBoundaryGapMatrix a).PosSemidef := by
  have hCongruence := hCore.conjTranspose_mul_mul_same
    (retainedP024SelectorTiltedFactor a)
  have hQuadraticScaled := hQuadratic.smul (sq_nonneg a)
  have hConstantScaled := hConstant.smul (sub_nonneg.mpr ha)
  rw [retainedP024SelectorBoundaryGapMatrix_eq_tilted_factorization]
  exact (hCongruence.add hQuadraticScaled).add hConstantScaled

/-- Production selector handoff from the three fixed tilted `3 x 3` gates. -/
theorem exists_sharpRetunedP024Selector_of_tilted
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hCore : retainedP024SelectorTiltedCore.PosSemidef)
    (hConstant : retainedP024SelectorTiltedConstantReserve.PosSemidef)
    (hQuadratic : retainedP024SelectorTiltedQuadraticReserve.PosSemidef)
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
  have hGap : (retainedP024SelectorBoundaryGapMatrix a).PosSemidef :=
    retainedP024SelectorBoundaryGapMatrix_posSemidef_of_tilted
      a ha hCore hConstant hQuadratic
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
    have hidentity := retainedP024BoundaryGap_eq_matrixQuadratic a d0 d2 d4
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

/-- The three fixed tilted gates feed the sharp selector directly into the
production low--tail estimate on the `P₀/P₂/P₄` slice.  Thus no selector
existence hypothesis remains between the fixed matrix certificate and the
mixed Cauchy inequality used by the cutoff-eleven argument. -/
theorem factorTwoEndpointLowTailMixed_retainedP024_sq_le_of_tilted
    (c0 c2 c4 : ℝ) (eR oR : ℝ → ℝ)
    (heRc : Continuous eR) (hoRc : Continuous oR)
    (heR : Function.Even eR) (hoR : Function.Odd oR)
    (heR0 : centeredEvenP0Coefficient eR = 0)
    (heRlocal : LocallyLipschitzOn (Set.Icc (-1) 1) eR)
    (hoRlocal : LocallyLipschitzOn (Set.Icc (-1) 1) oR)
    (heGap : centeredLegendreMomentsVanishBelow eR 11)
    (hoGap : centeredLegendreMomentsVanishBelow oR 11)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hCore : retainedP024SelectorTiltedCore.PosSemidef)
    (hConstant : retainedP024SelectorTiltedConstantReserve.PosSemidef)
    (hQuadratic : retainedP024SelectorTiltedQuadraticReserve.PosSemidef) :
    factorTwoEndpointLowTailMixed
          (centeredPolynomialLift (retainedP024Polynomial c0 c2 c4)) eR
          (centeredPolynomialLift (0 : ℝ[X])) oR a b ^ 2 ≤
      factorTwoEndpointChannelPhase
          (centeredPolynomialLift (retainedP024Polynomial c0 c2 c4))
          (centeredPolynomialLift (0 : ℝ[X])) a b *
        factorTwoEndpointChannelPhase eR oR a b := by
  obtain ⟨qE, qO, hqE, hqO, hselector⟩ :=
    exists_sharpRetunedP024Selector_of_tilted
      a b hab hCore hConstant hQuadratic c0 c2 c4
  exact
    factorTwoEndpointLowTailMixed_centeredPolynomialLift_sq_le_of_sharpRetunedAsymmetricRetainedSelector
      (retainedP024Polynomial c0 c2 c4) 0 eR oR
      heRc hoRc heR hoR heR0 heRlocal hoRlocal heGap hoGap
      (retainedP024Polynomial_natDegree_lt c0 c2 c4) (by simp)
      a b hab qE qO hqE hqO hselector

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorTiltedFactorStructural
