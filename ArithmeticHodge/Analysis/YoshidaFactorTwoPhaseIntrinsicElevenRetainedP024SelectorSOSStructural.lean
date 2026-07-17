import ArithmeticHodge.Analysis.ThreeByThreePositiveMixedDeterminant
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenSelectorGramStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorStructural

set_option autoImplicit false

open Matrix MeasureTheory Polynomial Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorSOSStructural

open ThreeByThreePositiveMixedDeterminant
open ThreeByThreeRankOneSchur
open ShiftedLegendreBasis
open ShiftedLegendreLogEnergyOrthogonalProjection
open ShiftedLegendreOrthogonality
open MatrixIntervalQuadraticSOS
open YoshidaFactorTwoPhaseIntrinsicElevenConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedRepresentersStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedSelectorHomogeneityStructural
open YoshidaFactorTwoPhaseIntrinsicElevenSelectorGramStructural
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseLowSchur

noncomputable section

/-!
# A rational interval reserve for the retained `P₀/P₂/P₄` selector pencil

The boundary gap is a quadratic matrix polynomial in the symmetric phase.
Its matrix-SOS certificate uses the following fixed rational reserve.  The
reserve is proved positive by exact Sylvester pivots; no decimal approximation
enters the theorem.
-/

/-- Rational reserve selected for the affine-lift matrix-SOS decomposition of
the sharp retained selector gap. -/
def retainedP024SelectorSOSReserve : Matrix (Fin 3) (Fin 3) ℝ :=
  symmetricMatrix3
    (1661 / 10000 : ℝ) (1535 / 10000 : ℝ) (-67 / 10000 : ℝ)
    (1492 / 10000 : ℝ) (262 / 10000 : ℝ) (1470 / 10000 : ℝ)

/-- The rational SOS reserve is strictly positive definite. -/
theorem retainedP024SelectorSOSReserve_posDef :
    retainedP024SelectorSOSReserve.PosDef := by
  unfold retainedP024SelectorSOSReserve
  apply symmetricMatrix3_posDef
  · norm_num
  · unfold leadingMinorTwo
    norm_num
  · unfold symmetricDeterminant
    norm_num

/-- Semidefinite form used directly by the interval matrix-SOS theorem. -/
theorem retainedP024SelectorSOSReserve_posSemidef :
    retainedP024SelectorSOSReserve.PosSemidef :=
  retainedP024SelectorSOSReserve_posDef.posSemidef

/-! ## Rational phase-affine selector polynomials -/

/-- Degree-below-eleven even selector synthesized in the shifted Legendre
basis of degrees `0,2,4,6,8,10`. -/
def retainedP024EvenSelectorPolynomial
    (c : Fin 6 → ℝ) : ℝ[X] :=
  ∑ i : Fin 6, c i • shiftedLegendreReal (2 * i.1)

/-- Degree-below-eleven odd selector synthesized in the shifted Legendre
basis of degrees `1,3,5,7,9`. -/
def retainedP024OddSelectorPolynomial
    (c : Fin 5 → ℝ) : ℝ[X] :=
  ∑ i : Fin 5, c i • shiftedLegendreReal (2 * i.1 + 1)

theorem retainedP024EvenSelectorPolynomial_natDegree_lt
    (c : Fin 6 → ℝ) :
    (retainedP024EvenSelectorPolynomial c).natDegree < 11 := by
  unfold retainedP024EvenSelectorPolynomial
  have hle : (∑ i : Fin 6,
      c i • shiftedLegendreReal (2 * i.1)).natDegree ≤ 10 :=
    Polynomial.natDegree_sum_le_of_forall_le Finset.univ _
      (fun i _hi ↦ (Polynomial.natDegree_smul_le (c i)
        (shiftedLegendreReal (2 * i.1))).trans (by
          rw [natDegree_shiftedLegendreReal]
          omega))
  omega

theorem retainedP024OddSelectorPolynomial_natDegree_lt
    (c : Fin 5 → ℝ) :
    (retainedP024OddSelectorPolynomial c).natDegree < 11 := by
  unfold retainedP024OddSelectorPolynomial
  have hle : (∑ i : Fin 5,
      c i • shiftedLegendreReal (2 * i.1 + 1)).natDegree ≤ 10 :=
    Polynomial.natDegree_sum_le_of_forall_le Finset.univ _
      (fun i _hi ↦ (Polynomial.natDegree_smul_le (c i)
        (shiftedLegendreReal (2 * i.1 + 1))).trans (by
          rw [natDegree_shiftedLegendreReal]
          omega))
  omega

/-- Positive symmetric-endpoint selector for the `P₀` production row. -/
def retainedP024SelectorPlus0 : ℝ[X] :=
  retainedP024EvenSelectorPolynomial
    ![0.581480, 0.314986, 0.376195, -0.045923, 0.246891, -0.159897]

/-- Positive symmetric-endpoint selector for the `P₂` production row. -/
def retainedP024SelectorPlus2 : ℝ[X] :=
  retainedP024EvenSelectorPolynomial
    ![-2.934156, 0.681927, 0.461601, 0.083303, 0.255626, -0.161282]

/-- Positive symmetric-endpoint selector for the `P₄` production row. -/
def retainedP024SelectorPlus4 : ℝ[X] :=
  retainedP024EvenSelectorPolynomial
    ![-39.098129, -17.266459, 0.362598, 0.551321, 0.222774, -0.095316]

/-- Negative symmetric-endpoint selector for the `P₀` production row. -/
def retainedP024SelectorMinus0 : ℝ[X] :=
  retainedP024EvenSelectorPolynomial
    ![2.492016, 1.367893, 0.492694, 0.615180, 0.143920, 0.380736]

/-- Negative symmetric-endpoint selector for the `P₂` production row. -/
def retainedP024SelectorMinus2 : ℝ[X] :=
  retainedP024EvenSelectorPolynomial
    ![3.270732, 0.645948, 0.791604, 0.587345, 0.175252, 0.397966]

/-- Negative symmetric-endpoint selector for the `P₄` production row. -/
def retainedP024SelectorMinus4 : ℝ[X] :=
  retainedP024EvenSelectorPolynomial
    ![39.194672, 17.962684, 0.975760, 0.573942, 0.339151, 0.378283]

/-- Alternating selector for the `P₀` production row. -/
def retainedP024SelectorAlt0 : ℝ[X] :=
  retainedP024OddSelectorPolynomial
    ![-0.114841, -0.517797, -0.052190, -0.191992, -0.152185]

/-- Alternating selector for the `P₂` production row. -/
def retainedP024SelectorAlt2 : ℝ[X] :=
  retainedP024OddSelectorPolynomial
    ![1.299077, -0.417890, 0.063268, -0.234226, -0.060096]

/-- Alternating selector for the `P₄` production row. -/
def retainedP024SelectorAlt4 : ℝ[X] :=
  retainedP024OddSelectorPolynomial
    ![52.719703, 1.779121, 0.021973, -0.245683, 0.136005]

theorem retainedP024SelectorPlus0_natDegree_lt :
    retainedP024SelectorPlus0.natDegree < 11 :=
  retainedP024EvenSelectorPolynomial_natDegree_lt _

theorem retainedP024SelectorPlus2_natDegree_lt :
    retainedP024SelectorPlus2.natDegree < 11 :=
  retainedP024EvenSelectorPolynomial_natDegree_lt _

theorem retainedP024SelectorPlus4_natDegree_lt :
    retainedP024SelectorPlus4.natDegree < 11 :=
  retainedP024EvenSelectorPolynomial_natDegree_lt _

theorem retainedP024SelectorMinus0_natDegree_lt :
    retainedP024SelectorMinus0.natDegree < 11 :=
  retainedP024EvenSelectorPolynomial_natDegree_lt _

theorem retainedP024SelectorMinus2_natDegree_lt :
    retainedP024SelectorMinus2.natDegree < 11 :=
  retainedP024EvenSelectorPolynomial_natDegree_lt _

theorem retainedP024SelectorMinus4_natDegree_lt :
    retainedP024SelectorMinus4.natDegree < 11 :=
  retainedP024EvenSelectorPolynomial_natDegree_lt _

theorem retainedP024SelectorAlt0_natDegree_lt :
    retainedP024SelectorAlt0.natDegree < 11 :=
  retainedP024OddSelectorPolynomial_natDegree_lt _

theorem retainedP024SelectorAlt2_natDegree_lt :
    retainedP024SelectorAlt2.natDegree < 11 :=
  retainedP024OddSelectorPolynomial_natDegree_lt _

theorem retainedP024SelectorAlt4_natDegree_lt :
    retainedP024SelectorAlt4.natDegree < 11 :=
  retainedP024OddSelectorPolynomial_natDegree_lt _

/-! ## Concrete boundary Gram matrices -/

/-- The six polarized entries of a three-row selector family, packaged as a
real symmetric matrix. -/
def retainedP024ThreeSelectorGramMatrix
    (W F0 F2 F4 : ℝ → ℝ) (q0 q2 q4 : ℝ[X]) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  symmetricMatrix3
    (factorTwoIntrinsicElevenSelectorCrossDual W F0 F0 q0 q0)
    (factorTwoIntrinsicElevenSelectorCrossDual W F0 F2 q0 q2)
    (factorTwoIntrinsicElevenSelectorCrossDual W F0 F4 q0 q4)
    (factorTwoIntrinsicElevenSelectorCrossDual W F2 F2 q2 q2)
    (factorTwoIntrinsicElevenSelectorCrossDual W F2 F4 q2 q4)
    (factorTwoIntrinsicElevenSelectorCrossDual W F4 F4 q4 q4)

/-- The symmetric three-row package agrees entrywise with the full polarized
selector Gram. -/
theorem retainedP024ThreeSelectorGramMatrix_apply
    (W F0 F2 F4 : ℝ → ℝ) (q0 q2 q4 : ℝ[X]) (i j : Fin 3) :
    retainedP024ThreeSelectorGramMatrix W F0 F2 F4 q0 q2 q4 i j =
      factorTwoIntrinsicElevenSelectorCrossDual W
        (![F0, F2, F4] i) (![F0, F2, F4] j)
        (![q0, q2, q4] i) (![q0, q2, q4] j) := by
  fin_cases i <;> fin_cases j <;>
    simp [retainedP024ThreeSelectorGramMatrix, symmetricMatrix3,
      factorTwoIntrinsicElevenSelectorCrossDual_comm]

private theorem quadraticForm_symmetricMatrix3
    (q00 q02 q04 q22 q24 q44 c0 c2 c4 : ℝ) :
    star (![c0, c2, c4] : Fin 3 → ℝ) ⬝ᵥ
        (symmetricMatrix3 q00 q02 q04 q22 q24 q44 *ᵥ
          (![c0, c2, c4] : Fin 3 → ℝ)) =
      symmetricQuadratic q00 q02 q04 q22 q24 q44 c0 c2 c4 := by
  simp [dotProduct, mulVec, symmetricMatrix3,
    Fin.sum_univ_succ, symmetricQuadratic]
  ring

/-- The generic three-selector integral is exactly the quadratic form of its
concrete Gram matrix. -/
theorem factorTwoIntrinsicElevenSelectorDual_three_eq_matrixQuadratic
    (W F0 F2 F4 : ℝ → ℝ) (q0 q2 q4 : ℝ[X])
    (hInt : ThreeSelectorGramIntegrable W F0 F2 F4 q0 q2 q4)
    (c0 c2 c4 : ℝ) :
    factorTwoIntrinsicElevenSelectorDual W
        (threeSelectorRepresenter c0 c2 c4 F0 F2 F4)
        (threeSelectorPolynomial c0 c2 c4 q0 q2 q4) =
      star (![c0, c2, c4] : Fin 3 → ℝ) ⬝ᵥ
        (retainedP024ThreeSelectorGramMatrix W F0 F2 F4 q0 q2 q4 *ᵥ
          (![c0, c2, c4] : Fin 3 → ℝ)) := by
  rw [factorTwoIntrinsicElevenSelectorDual_three_eq_symmetricQuadratic
    W F0 F2 F4 q0 q2 q4 hInt c0 c2 c4]
  unfold retainedP024ThreeSelectorGramMatrix
  rw [quadraticForm_symmetricMatrix3]

/-- Three-row retained even Gram at a fixed symmetric endpoint phase. -/
def retainedP024EvenEndpointSelectorGram
    (a : ℝ) (q0 q2 q4 : ℝ[X]) : Matrix (Fin 3) (Fin 3) ℝ :=
  retainedP024ThreeSelectorGramMatrix
    factorTwoIntrinsicElevenRetainedEvenWeight
    (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
      (1 / 512 : ℝ) (shiftedLegendreReal 0) 0 a 0)
    (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
      (1 / 512 : ℝ) (shiftedLegendreReal 2) 0 a 0)
    (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
      (1 / 512 : ℝ) (shiftedLegendreReal 4) 0 a 0)
    q0 q2 q4

/-- Exact positive-endpoint selector Gram. -/
def retainedP024SelectorPlusGram : Matrix (Fin 3) (Fin 3) ℝ :=
  retainedP024EvenEndpointSelectorGram 1
    retainedP024SelectorPlus0 retainedP024SelectorPlus2 retainedP024SelectorPlus4

/-- Exact negative-endpoint selector Gram. -/
def retainedP024SelectorMinusGram : Matrix (Fin 3) (Fin 3) ℝ :=
  retainedP024EvenEndpointSelectorGram (-1)
    retainedP024SelectorMinus0 retainedP024SelectorMinus2 retainedP024SelectorMinus4

/-- The retained even selector cost at either endpoint is the quadratic form
of its exact three-row Gram matrix. -/
theorem retainedP024EvenEndpointSelectorDual_eq_matrixQuadratic
    (a c0 c2 c4 : ℝ) (q0 q2 q4 : ℝ[X]) :
    factorTwoIntrinsicElevenSelectorDual
        factorTwoIntrinsicElevenRetainedEvenWeight
        (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
          (1 / 512 : ℝ) (retainedP024Polynomial c0 c2 c4) 0 a 0)
        (threeSelectorPolynomial c0 c2 c4 q0 q2 q4) =
      star (![c0, c2, c4] : Fin 3 → ℝ) ⬝ᵥ
        (retainedP024EvenEndpointSelectorGram a q0 q2 q4 *ᵥ
          (![c0, c2, c4] : Fin 3 → ℝ)) := by
  have hcongr := factorTwoIntrinsicElevenSelectorDual_congr_on_Icc
    factorTwoIntrinsicElevenRetainedEvenWeight
    (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
      (1 / 512 : ℝ) (retainedP024Polynomial c0 c2 c4) 0 a 0)
    (threeSelectorRepresenter c0 c2 c4
      (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
        (1 / 512 : ℝ) (shiftedLegendreReal 0) 0 a 0)
      (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
        (1 / 512 : ℝ) (shiftedLegendreReal 2) 0 a 0)
      (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
        (1 / 512 : ℝ) (shiftedLegendreReal 4) 0 a 0))
    (threeSelectorPolynomial c0 c2 c4 q0 q2 q4)
    (fun x hx ↦ by
      rw [retainedP024Polynomial_eq_threeSelectorPolynomial]
      exact retainedEvenMixedRepresenterAt_threeSelectorPolynomial_on_Icc
        (1 / 512 : ℝ) c0 c2 c4 a 0
        (shiftedLegendreReal 0) (shiftedLegendreReal 2)
        (shiftedLegendreReal 4) x hx)
  rw [hcongr]
  simpa only [retainedP024EvenEndpointSelectorGram] using
    factorTwoIntrinsicElevenSelectorDual_three_eq_matrixQuadratic
      factorTwoIntrinsicElevenRetainedEvenWeight
      (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
        (1 / 512 : ℝ) (shiftedLegendreReal 0) 0 a 0)
      (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
        (1 / 512 : ℝ) (shiftedLegendreReal 2) 0 a 0)
      (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
        (1 / 512 : ℝ) (shiftedLegendreReal 4) 0 a 0)
      q0 q2 q4
      (retainedEvenThreeSelectorGramIntegrable
        (1 / 512 : ℝ)
        (shiftedLegendreReal 0) (shiftedLegendreReal 2)
        (shiftedLegendreReal 4) q0 q2 q4 a 0)
      c0 c2 c4

/-- Exact Gram of the symmetric endpoint half-difference rows. -/
def retainedP024SymmetricSelectorGram
    (qP0 qP2 qP4 qM0 qM2 qM4 : ℝ[X]) : Matrix (Fin 3) (Fin 3) ℝ :=
  retainedP024ThreeSelectorGramMatrix
    factorTwoIntrinsicElevenRetainedEvenWeight
    (retainedEvenSymmetricRepresenterAt
      (1 / 512 : ℝ) (shiftedLegendreReal 0))
    (retainedEvenSymmetricRepresenterAt
      (1 / 512 : ℝ) (shiftedLegendreReal 2))
    (retainedEvenSymmetricRepresenterAt
      (1 / 512 : ℝ) (shiftedLegendreReal 4))
    (retainedP024SymmetricSelector qP0 qM0)
    (retainedP024SymmetricSelector qP2 qM2)
    (retainedP024SymmetricSelector qP4 qM4)

/-- Exact symmetric half-difference Gram for the fixed selector candidates. -/
def retainedP024SelectorSymmetricGram : Matrix (Fin 3) (Fin 3) ℝ :=
  retainedP024SymmetricSelectorGram
    retainedP024SelectorPlus0 retainedP024SelectorPlus2 retainedP024SelectorPlus4
    retainedP024SelectorMinus0 retainedP024SelectorMinus2 retainedP024SelectorMinus4

/-- Exact Gram of the alternating odd rows. -/
def retainedP024AlternatingSelectorGram
    (q0 q2 q4 : ℝ[X]) : Matrix (Fin 3) (Fin 3) ℝ :=
  retainedP024ThreeSelectorGramMatrix
    factorTwoIntrinsicElevenRetainedOddWeight
    (retainedOddAlternatingRepresenterAt
      (1 / 512 : ℝ) (shiftedLegendreReal 0))
    (retainedOddAlternatingRepresenterAt
      (1 / 512 : ℝ) (shiftedLegendreReal 2))
    (retainedOddAlternatingRepresenterAt
      (1 / 512 : ℝ) (shiftedLegendreReal 4))
    q0 q2 q4

/-- Exact alternating Gram for the fixed selector candidates. -/
def retainedP024SelectorAlternatingGram : Matrix (Fin 3) (Fin 3) ℝ :=
  retainedP024AlternatingSelectorGram
    retainedP024SelectorAlt0 retainedP024SelectorAlt2 retainedP024SelectorAlt4

private theorem retainedP024SymmetricSelector_three
    (c0 c2 c4 : ℝ) (qP0 qP2 qP4 qM0 qM2 qM4 : ℝ[X]) :
    retainedP024SymmetricSelector
        (threeSelectorPolynomial c0 c2 c4 qP0 qP2 qP4)
        (threeSelectorPolynomial c0 c2 c4 qM0 qM2 qM4) =
      threeSelectorPolynomial c0 c2 c4
        (retainedP024SymmetricSelector qP0 qM0)
        (retainedP024SymmetricSelector qP2 qM2)
        (retainedP024SymmetricSelector qP4 qM4) := by
  unfold retainedP024SymmetricSelector threeSelectorPolynomial
  module

private theorem retainedEvenSymmetricRepresenterAt_threeSelector_on_Icc
    (gamma c0 c2 c4 : ℝ) (p0 p2 p4 : ℝ[X])
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    retainedEvenSymmetricRepresenterAt gamma
        (threeSelectorPolynomial c0 c2 c4 p0 p2 p4) x =
      threeSelectorRepresenter c0 c2 c4
        (retainedEvenSymmetricRepresenterAt gamma p0)
        (retainedEvenSymmetricRepresenterAt gamma p2)
        (retainedEvenSymmetricRepresenterAt gamma p4) x := by
  unfold retainedEvenSymmetricRepresenterAt
  rw [retainedEvenMixedRepresenterAt_threeSelectorPolynomial_on_Icc
    gamma c0 c2 c4 1 0 p0 p2 p4 x hx]
  unfold retainedEvenBaseRepresenterAt
  rw [retainedEvenMixedRepresenterAt_threeSelectorPolynomial_on_Icc
    gamma c0 c2 c4 0 0 p0 p2 p4 x hx]
  unfold threeSelectorRepresenter
  ring

/-- The symmetric half-difference selector cost is the quadratic form of its
exact three-row Gram matrix. -/
theorem retainedP024SymmetricSelectorDual_eq_matrixQuadratic
    (c0 c2 c4 : ℝ) (qP0 qP2 qP4 qM0 qM2 qM4 : ℝ[X]) :
    factorTwoIntrinsicElevenSelectorDual
        factorTwoIntrinsicElevenRetainedEvenWeight
        (retainedEvenSymmetricRepresenterAt
          (1 / 512 : ℝ) (retainedP024Polynomial c0 c2 c4))
        (retainedP024SymmetricSelector
          (threeSelectorPolynomial c0 c2 c4 qP0 qP2 qP4)
          (threeSelectorPolynomial c0 c2 c4 qM0 qM2 qM4)) =
      star (![c0, c2, c4] : Fin 3 → ℝ) ⬝ᵥ
        (retainedP024SymmetricSelectorGram
            qP0 qP2 qP4 qM0 qM2 qM4 *ᵥ
          (![c0, c2, c4] : Fin 3 → ℝ)) := by
  rw [retainedP024SymmetricSelector_three]
  have hcongr := factorTwoIntrinsicElevenSelectorDual_congr_on_Icc
    factorTwoIntrinsicElevenRetainedEvenWeight
    (retainedEvenSymmetricRepresenterAt
      (1 / 512 : ℝ) (retainedP024Polynomial c0 c2 c4))
    (threeSelectorRepresenter c0 c2 c4
      (retainedEvenSymmetricRepresenterAt
        (1 / 512 : ℝ) (shiftedLegendreReal 0))
      (retainedEvenSymmetricRepresenterAt
        (1 / 512 : ℝ) (shiftedLegendreReal 2))
      (retainedEvenSymmetricRepresenterAt
        (1 / 512 : ℝ) (shiftedLegendreReal 4)))
    (threeSelectorPolynomial c0 c2 c4
      (retainedP024SymmetricSelector qP0 qM0)
      (retainedP024SymmetricSelector qP2 qM2)
      (retainedP024SymmetricSelector qP4 qM4))
    (fun x hx ↦ by
      rw [retainedP024Polynomial_eq_threeSelectorPolynomial]
      exact retainedEvenSymmetricRepresenterAt_threeSelector_on_Icc
        (1 / 512 : ℝ) c0 c2 c4
        (shiftedLegendreReal 0) (shiftedLegendreReal 2)
        (shiftedLegendreReal 4) x hx)
  rw [hcongr]
  simpa only [retainedP024SymmetricSelectorGram] using
    factorTwoIntrinsicElevenSelectorDual_three_eq_matrixQuadratic
      factorTwoIntrinsicElevenRetainedEvenWeight
      (retainedEvenSymmetricRepresenterAt
        (1 / 512 : ℝ) (shiftedLegendreReal 0))
      (retainedEvenSymmetricRepresenterAt
        (1 / 512 : ℝ) (shiftedLegendreReal 2))
      (retainedEvenSymmetricRepresenterAt
        (1 / 512 : ℝ) (shiftedLegendreReal 4))
      (retainedP024SymmetricSelector qP0 qM0)
      (retainedP024SymmetricSelector qP2 qM2)
      (retainedP024SymmetricSelector qP4 qM4)
      (retainedEvenSymmetricThreeSelectorGramIntegrable
        (1 / 512 : ℝ)
        (shiftedLegendreReal 0) (shiftedLegendreReal 2)
        (shiftedLegendreReal 4)
        qP0 qP2 qP4 qM0 qM2 qM4)
      c0 c2 c4

/-- The alternating selector cost is the quadratic form of its exact
three-row odd Gram matrix. -/
theorem retainedP024AlternatingSelectorDual_eq_matrixQuadratic
    (c0 c2 c4 : ℝ) (q0 q2 q4 : ℝ[X]) :
    factorTwoIntrinsicElevenSelectorDual
        factorTwoIntrinsicElevenRetainedOddWeight
        (retainedOddAlternatingRepresenterAt
          (1 / 512 : ℝ) (retainedP024Polynomial c0 c2 c4))
        (threeSelectorPolynomial c0 c2 c4 q0 q2 q4) =
      star (![c0, c2, c4] : Fin 3 → ℝ) ⬝ᵥ
        (retainedP024AlternatingSelectorGram q0 q2 q4 *ᵥ
          (![c0, c2, c4] : Fin 3 → ℝ)) := by
  have hcongr := factorTwoIntrinsicElevenSelectorDual_congr_on_Icc
    factorTwoIntrinsicElevenRetainedOddWeight
    (retainedOddAlternatingRepresenterAt
      (1 / 512 : ℝ) (retainedP024Polynomial c0 c2 c4))
    (threeSelectorRepresenter c0 c2 c4
      (retainedOddAlternatingRepresenterAt
        (1 / 512 : ℝ) (shiftedLegendreReal 0))
      (retainedOddAlternatingRepresenterAt
        (1 / 512 : ℝ) (shiftedLegendreReal 2))
      (retainedOddAlternatingRepresenterAt
        (1 / 512 : ℝ) (shiftedLegendreReal 4)))
    (threeSelectorPolynomial c0 c2 c4 q0 q2 q4)
    (fun x hx ↦ by
      unfold retainedOddAlternatingRepresenterAt
      rw [retainedP024Polynomial_eq_threeSelectorPolynomial]
      exact retainedOddMixedRepresenterAt_threeSelectorPolynomial_on_Icc
        (1 / 512 : ℝ) c0 c2 c4 0 1
        (shiftedLegendreReal 0) (shiftedLegendreReal 2)
        (shiftedLegendreReal 4) x hx)
  rw [hcongr]
  simpa only [retainedP024AlternatingSelectorGram] using
    factorTwoIntrinsicElevenSelectorDual_three_eq_matrixQuadratic
      factorTwoIntrinsicElevenRetainedOddWeight
      (retainedOddAlternatingRepresenterAt
        (1 / 512 : ℝ) (shiftedLegendreReal 0))
      (retainedOddAlternatingRepresenterAt
        (1 / 512 : ℝ) (shiftedLegendreReal 2))
      (retainedOddAlternatingRepresenterAt
        (1 / 512 : ℝ) (shiftedLegendreReal 4))
      q0 q2 q4
      (by
        simpa only [retainedOddAlternatingRepresenterAt] using
          (retainedOddThreeSelectorGramIntegrable
            (1 / 512 : ℝ)
            (shiftedLegendreReal 0) (shiftedLegendreReal 2)
          (shiftedLegendreReal 4) q0 q2 q4 0 1))
      c0 c2 c4

/-- The exact sharp-retuned low budget as a symmetric `3 x 3` matrix. -/
def retainedP024SharpLowMatrix (a : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  symmetricMatrix3
    (retainedP024SharpLow00 a)
    (retainedP024SharpLow02 a)
    (retainedP024SharpLow04 a)
    (retainedP024SharpLow22 a)
    (retainedP024SharpLow24 a)
    (retainedP024SharpLow44 a)

/-- The signed selector Gram occurring in the phase-boundary chord. -/
def retainedP024BoundarySelectorGram (a : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  retainedP024ChordPlus a • retainedP024SelectorPlusGram +
    retainedP024ChordMinus a • retainedP024SelectorMinusGram -
    (1 - a ^ 2) • retainedP024SelectorSymmetricGram +
    (1 - a ^ 2) • retainedP024SelectorAlternatingGram

/-- Exact boundary gap matrix: sharp low budget minus signed selector cost. -/
def retainedP024SelectorBoundaryGapMatrix
    (a : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  retainedP024SharpLowMatrix a - retainedP024BoundarySelectorGram a

/-- The fixed-selector boundary chord is exactly the quadratic form of its
signed boundary Gram matrix. -/
theorem retainedP024BoundaryChordCost_eq_matrixQuadratic
    (a c0 c2 c4 : ℝ) :
    retainedP024BoundaryChordCost (1 / 512 : ℝ)
        (retainedP024Polynomial c0 c2 c4)
        (threeSelectorPolynomial c0 c2 c4
          retainedP024SelectorPlus0 retainedP024SelectorPlus2
          retainedP024SelectorPlus4)
        (threeSelectorPolynomial c0 c2 c4
          retainedP024SelectorMinus0 retainedP024SelectorMinus2
          retainedP024SelectorMinus4)
        (threeSelectorPolynomial c0 c2 c4
          retainedP024SelectorAlt0 retainedP024SelectorAlt2
          retainedP024SelectorAlt4) a =
      star (![c0, c2, c4] : Fin 3 → ℝ) ⬝ᵥ
        (retainedP024BoundarySelectorGram a *ᵥ
          (![c0, c2, c4] : Fin 3 → ℝ)) := by
  unfold retainedP024BoundaryChordCost
  rw [retainedP024EvenEndpointSelectorDual_eq_matrixQuadratic
      1 c0 c2 c4 retainedP024SelectorPlus0 retainedP024SelectorPlus2
      retainedP024SelectorPlus4,
    retainedP024EvenEndpointSelectorDual_eq_matrixQuadratic
      (-1) c0 c2 c4 retainedP024SelectorMinus0 retainedP024SelectorMinus2
      retainedP024SelectorMinus4,
    retainedP024SymmetricSelectorDual_eq_matrixQuadratic
      c0 c2 c4 retainedP024SelectorPlus0 retainedP024SelectorPlus2
      retainedP024SelectorPlus4 retainedP024SelectorMinus0
      retainedP024SelectorMinus2 retainedP024SelectorMinus4,
    retainedP024AlternatingSelectorDual_eq_matrixQuadratic
      c0 c2 c4 retainedP024SelectorAlt0 retainedP024SelectorAlt2
      retainedP024SelectorAlt4]
  simp only [retainedP024SelectorPlusGram,
    retainedP024SelectorMinusGram, retainedP024SelectorSymmetricGram,
    retainedP024SelectorAlternatingGram,
    retainedP024BoundarySelectorGram, add_mulVec, sub_mulVec, smul_mulVec,
    dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul]

/-- The sharp low quadratic is the quadratic form of its concrete matrix. -/
theorem retainedP024SharpLow_eq_matrixQuadratic
    (a c0 c2 c4 : ℝ) :
    symmetricQuadratic
        (retainedP024SharpLow00 a)
        (retainedP024SharpLow02 a)
        (retainedP024SharpLow04 a)
        (retainedP024SharpLow22 a)
        (retainedP024SharpLow24 a)
        (retainedP024SharpLow44 a)
        c0 c2 c4 =
      star (![c0, c2, c4] : Fin 3 → ℝ) ⬝ᵥ
        (retainedP024SharpLowMatrix a *ᵥ
          (![c0, c2, c4] : Fin 3 → ℝ)) := by
  unfold retainedP024SharpLowMatrix
  rw [quadraticForm_symmetricMatrix3]

/-- Exact `hGap` identity required by the fixed matrix-SOS selector handoff. -/
theorem retainedP024BoundaryGap_eq_matrixQuadratic
    (a c0 c2 c4 : ℝ) :
    symmetricQuadratic
          (retainedP024SharpLow00 a)
          (retainedP024SharpLow02 a)
          (retainedP024SharpLow04 a)
          (retainedP024SharpLow22 a)
          (retainedP024SharpLow24 a)
          (retainedP024SharpLow44 a)
          c0 c2 c4 -
        retainedP024BoundaryChordCost (1 / 512 : ℝ)
          (retainedP024Polynomial c0 c2 c4)
          (threeSelectorPolynomial c0 c2 c4
            retainedP024SelectorPlus0 retainedP024SelectorPlus2
            retainedP024SelectorPlus4)
          (threeSelectorPolynomial c0 c2 c4
            retainedP024SelectorMinus0 retainedP024SelectorMinus2
            retainedP024SelectorMinus4)
          (threeSelectorPolynomial c0 c2 c4
            retainedP024SelectorAlt0 retainedP024SelectorAlt2
            retainedP024SelectorAlt4) a =
      star (![c0, c2, c4] : Fin 3 → ℝ) ⬝ᵥ
        (retainedP024SelectorBoundaryGapMatrix a *ᵥ
          (![c0, c2, c4] : Fin 3 → ℝ)) := by
  rw [retainedP024SharpLow_eq_matrixQuadratic,
    retainedP024BoundaryChordCost_eq_matrixQuadratic]
  simp only [retainedP024SelectorBoundaryGapMatrix, sub_mulVec,
    dotProduct_sub]

/-! ## Fixed affine-lift realization of the boundary pencil -/

/-- Constant coefficient of the exact quadratic boundary-gap pencil. -/
def retainedP024SelectorBoundaryGapConstant : Matrix (Fin 3) (Fin 3) ℝ :=
  retainedP024SelectorBoundaryGapMatrix 0

/-- Linear coefficient of the exact quadratic boundary-gap pencil. -/
def retainedP024SelectorBoundaryGapLinear : Matrix (Fin 3) (Fin 3) ℝ :=
  (1 / 2 : ℝ) •
    (retainedP024SelectorBoundaryGapMatrix 1 -
      retainedP024SelectorBoundaryGapMatrix (-1))

/-- Quadratic coefficient of the exact boundary-gap pencil. -/
def retainedP024SelectorBoundaryGapQuadratic : Matrix (Fin 3) (Fin 3) ℝ :=
  (1 / 2 : ℝ) •
      (retainedP024SelectorBoundaryGapMatrix 1 +
        retainedP024SelectorBoundaryGapMatrix (-1)) -
    retainedP024SelectorBoundaryGapMatrix 0

/-- The boundary gap is exactly reconstructed from its three coefficient
matrices.  This is polynomial interpolation, not a phase subdivision. -/
theorem retainedP024SelectorBoundaryGapMatrix_eq_coefficients (a : ℝ) :
    retainedP024SelectorBoundaryGapMatrix a =
      retainedP024SelectorBoundaryGapConstant +
        a • retainedP024SelectorBoundaryGapLinear +
        a ^ 2 • retainedP024SelectorBoundaryGapQuadratic := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [retainedP024SelectorBoundaryGapConstant,
      retainedP024SelectorBoundaryGapLinear,
      retainedP024SelectorBoundaryGapQuadratic,
      retainedP024SelectorBoundaryGapMatrix,
      retainedP024BoundarySelectorGram, retainedP024SharpLowMatrix,
      retainedP024ChordPlus, retainedP024ChordMinus,
      retainedP024SharpLow00, retainedP024SharpLow02,
      retainedP024SharpLow04, retainedP024SharpLow22,
      retainedP024SharpLow24, retainedP024SharpLow44,
      factorTwoStructuralPhaseLow00, factorTwoStructuralPhaseLow02,
      factorTwoStructuralPhaseLow22, factorTwoIntrinsicFourP45Cross04,
      factorTwoIntrinsicFourP45Cross24, factorTwoIntrinsicP4PhaseDiagonal,
      symmetricMatrix3] <;>
    ring

/-- Fixed `6 x 6` affine-lift Gram associated to the selected rational
reserve.  Its entries are exact analytic Gram entries, not decimal samples. -/
def retainedP024SelectorSOSGram :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  Matrix.fromBlocks
    (retainedP024SelectorBoundaryGapConstant -
      retainedP024SelectorSOSReserve)
    ((1 / 2 : ℝ) • retainedP024SelectorBoundaryGapLinear)
    ((1 / 2 : ℝ) • retainedP024SelectorBoundaryGapLinear)
    (retainedP024SelectorBoundaryGapQuadratic +
      retainedP024SelectorSOSReserve)

/-! ## Asymmetric off-block realization

The affine lift only sees the sum of the two off-diagonal blocks.  We use
that freedom to retain the oriented base--symmetric selector pairing instead
of replacing it by its symmetric part.  This is the matrix coordinate in
which the analytic selector loss becomes one whole weighted residual square.
-/

/-- Endpoint-average of two polynomial selectors. -/
def retainedP024BaseSelector (qPlus qMinus : ℝ[X]) : ℝ[X] :=
  (1 / 2 : ℝ) • (qPlus + qMinus)

/-- The endpoint-average residual is exactly the phase-independent base
residual. -/
theorem retainedP024BaseSelectorResidual_eq_endpoint_half_add
    (gamma : ℝ) (p qPlus qMinus : ℝ[X]) (x : ℝ) :
    factorTwoIntrinsicElevenSelectorResidual
        (retainedEvenBaseRepresenterAt gamma p)
        (retainedP024BaseSelector qPlus qMinus) x =
      (1 / 2 : ℝ) *
        (factorTwoIntrinsicElevenSelectorResidual
            (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
              gamma p 0 1 0) qPlus x +
          factorTwoIntrinsicElevenSelectorResidual
            (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
              gamma p 0 (-1) 0) qMinus x) := by
  unfold factorTwoIntrinsicElevenSelectorResidual retainedP024BaseSelector
  rw [centeredPolynomialLift_smul, centeredPolynomialLift_add,
    retainedEvenRepresenterAt_zero_odd_phase_split,
    retainedEvenRepresenterAt_zero_odd_phase_split]
  ring

/-- The symmetric residual is the complementary endpoint half-difference.
This public form is used to orient the off-block Gram. -/
theorem retainedP024SymmetricSelectorResidual_eq_endpoint_half_sub
    (gamma : ℝ) (p qPlus qMinus : ℝ[X]) (x : ℝ) :
    factorTwoIntrinsicElevenSelectorResidual
        (retainedEvenSymmetricRepresenterAt gamma p)
        (retainedP024SymmetricSelector qPlus qMinus) x =
      (1 / 2 : ℝ) *
        (factorTwoIntrinsicElevenSelectorResidual
            (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
              gamma p 0 1 0) qPlus x -
          factorTwoIntrinsicElevenSelectorResidual
            (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
              gamma p 0 (-1) 0) qMinus x) := by
  unfold factorTwoIntrinsicElevenSelectorResidual
    retainedP024SymmetricSelector retainedEvenSymmetricRepresenterAt
    retainedEvenBaseRepresenterAt
  rw [centeredPolynomialLift_smul]
  have hsub : centeredPolynomialLift (qPlus - qMinus) x =
      centeredPolynomialLift qPlus x - centeredPolynomialLift qMinus x := by
    unfold centeredPolynomialLift
    rw [Polynomial.eval_sub]
  rw [hsub,
    retainedEvenRepresenterAt_zero_odd_phase_split gamma p (-1) 0 x]
  simp only [retainedEvenSymmetricRepresenterAt,
    retainedEvenBaseRepresenterAt]
  ring

/-- Every endpoint-average selector residual lies in the same retained
weighted `L²` space as its two endpoint residuals. -/
theorem retainedEvenBaseSelectorResidual_div_sqrt_memLp_two
    (gamma : ℝ) (p qPlus qMinus : ℝ[X]) :
    MemLp (fun x ↦
      factorTwoIntrinsicElevenSelectorResidual
          (retainedEvenBaseRepresenterAt gamma p)
          (retainedP024BaseSelector qPlus qMinus) x /
        Real.sqrt (factorTwoIntrinsicElevenRetainedEvenWeight x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  have hPlus :=
    factorTwoIntrinsicElevenRetainedEvenSelectorResidual_div_sqrt_memLp_two
      gamma p 0 qPlus 1 0
  have hMinus :=
    factorTwoIntrinsicElevenRetainedEvenSelectorResidual_div_sqrt_memLp_two
      gamma p 0 qMinus (-1) 0
  have hAverage := (hPlus.add hMinus).const_mul (1 / 2 : ℝ)
  apply (memLp_congr_ae (μ := volume.restrict (Ioc (-1 : ℝ) 1)) ?_).mpr
    hAverage
  filter_upwards [] with x
  rw [retainedP024BaseSelectorResidual_eq_endpoint_half_add
    gamma p qPlus qMinus x]
  dsimp only [Pi.add_apply]
  ring

/-- Polarization of two endpoint-average residual rows.  This is the
index-free identity behind the upper-left block of the whole residual Gram. -/
private theorem retainedEvenBaseCross_eq_endpoint_average_sub_symmetric
    (gamma : ℝ) (p r qPlus qMinus sPlus sMinus : ℝ[X]) :
    factorTwoIntrinsicElevenSelectorCrossDual
        factorTwoIntrinsicElevenRetainedEvenWeight
        (retainedEvenBaseRepresenterAt gamma p)
        (retainedEvenBaseRepresenterAt gamma r)
        (retainedP024BaseSelector qPlus qMinus)
        (retainedP024BaseSelector sPlus sMinus) =
      (1 / 2 : ℝ) *
        (factorTwoIntrinsicElevenSelectorCrossDual
            factorTwoIntrinsicElevenRetainedEvenWeight
            (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
              gamma p 0 1 0)
            (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
              gamma r 0 1 0) qPlus sPlus +
          factorTwoIntrinsicElevenSelectorCrossDual
            factorTwoIntrinsicElevenRetainedEvenWeight
            (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
              gamma p 0 (-1) 0)
            (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
              gamma r 0 (-1) 0) qMinus sMinus) -
        factorTwoIntrinsicElevenSelectorCrossDual
          factorTwoIntrinsicElevenRetainedEvenWeight
          (retainedEvenSymmetricRepresenterAt gamma p)
          (retainedEvenSymmetricRepresenterAt gamma r)
          (retainedP024SymmetricSelector qPlus qMinus)
          (retainedP024SymmetricSelector sPlus sMinus) := by
  let W := factorTwoIntrinsicElevenRetainedEvenWeight
  let FP := factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
    gamma p 0 1 0
  let FM := factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
    gamma p 0 (-1) 0
  let GP := factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
    gamma r 0 1 0
  let GM := factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
    gamma r 0 (-1) 0
  let FS := retainedEvenSymmetricRepresenterAt gamma p
  let GS := retainedEvenSymmetricRepresenterAt gamma r
  have hP := intervalIntegrable_selectorCross_of_memLp
    W FP GP qPlus sPlus
    (fun x hx ↦ factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc hx)
    (factorTwoIntrinsicElevenRetainedEvenSelectorResidual_div_sqrt_memLp_two
      gamma p 0 qPlus 1 0)
    (factorTwoIntrinsicElevenRetainedEvenSelectorResidual_div_sqrt_memLp_two
      gamma r 0 sPlus 1 0)
  have hM := intervalIntegrable_selectorCross_of_memLp
    W FM GM qMinus sMinus
    (fun x hx ↦ factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc hx)
    (factorTwoIntrinsicElevenRetainedEvenSelectorResidual_div_sqrt_memLp_two
      gamma p 0 qMinus (-1) 0)
    (factorTwoIntrinsicElevenRetainedEvenSelectorResidual_div_sqrt_memLp_two
      gamma r 0 sMinus (-1) 0)
  have hS := intervalIntegrable_selectorCross_of_memLp W FS GS
    (retainedP024SymmetricSelector qPlus qMinus)
    (retainedP024SymmetricSelector sPlus sMinus)
    (fun x hx ↦ factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc hx)
    (retainedEvenSymmetricSelectorResidual_div_sqrt_memLp_two
      gamma p qPlus qMinus)
    (retainedEvenSymmetricSelectorResidual_div_sqrt_memLp_two
      gamma r sPlus sMinus)
  unfold factorTwoIntrinsicElevenSelectorCrossDual
  rw [show (fun x : ℝ ↦
      factorTwoIntrinsicElevenSelectorResidual
          (retainedEvenBaseRepresenterAt gamma p)
          (retainedP024BaseSelector qPlus qMinus) x *
        factorTwoIntrinsicElevenSelectorResidual
          (retainedEvenBaseRepresenterAt gamma r)
          (retainedP024BaseSelector sPlus sMinus) x /
        factorTwoIntrinsicElevenRetainedEvenWeight x) =
      fun x ↦ (1 / 2 : ℝ) *
          (factorTwoIntrinsicElevenSelectorResidual FP qPlus x *
                factorTwoIntrinsicElevenSelectorResidual GP sPlus x / W x +
            factorTwoIntrinsicElevenSelectorResidual FM qMinus x *
                factorTwoIntrinsicElevenSelectorResidual GM sMinus x / W x) -
        factorTwoIntrinsicElevenSelectorResidual FS
              (retainedP024SymmetricSelector qPlus qMinus) x *
            factorTwoIntrinsicElevenSelectorResidual GS
              (retainedP024SymmetricSelector sPlus sMinus) x / W x by
    funext x
    rw [retainedP024BaseSelectorResidual_eq_endpoint_half_add
        gamma p qPlus qMinus x,
      retainedP024BaseSelectorResidual_eq_endpoint_half_add
        gamma r sPlus sMinus x,
      retainedP024SymmetricSelectorResidual_eq_endpoint_half_sub
        gamma p qPlus qMinus x,
      retainedP024SymmetricSelectorResidual_eq_endpoint_half_sub
        gamma r sPlus sMinus x]
    dsimp only [W, FP, FM, GP, GM, FS, GS]
    ring]
  rw [intervalIntegral.integral_sub ((hP.add hM).const_mul _) hS,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hP hM]

/-- The symmetric part of the oriented base--symmetric cross is the
half-difference of the two endpoint Grams. -/
private theorem retainedEvenBaseSymmetricCross_add_swap_eq_endpoint_half_sub
    (gamma : ℝ) (p r qPlus qMinus sPlus sMinus : ℝ[X]) :
    factorTwoIntrinsicElevenSelectorCrossDual
        factorTwoIntrinsicElevenRetainedEvenWeight
        (retainedEvenBaseRepresenterAt gamma p)
        (retainedEvenSymmetricRepresenterAt gamma r)
        (retainedP024BaseSelector qPlus qMinus)
        (retainedP024SymmetricSelector sPlus sMinus) +
      factorTwoIntrinsicElevenSelectorCrossDual
        factorTwoIntrinsicElevenRetainedEvenWeight
        (retainedEvenSymmetricRepresenterAt gamma p)
        (retainedEvenBaseRepresenterAt gamma r)
        (retainedP024SymmetricSelector qPlus qMinus)
        (retainedP024BaseSelector sPlus sMinus) =
      (1 / 2 : ℝ) *
        (factorTwoIntrinsicElevenSelectorCrossDual
            factorTwoIntrinsicElevenRetainedEvenWeight
            (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
              gamma p 0 1 0)
            (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
              gamma r 0 1 0) qPlus sPlus -
          factorTwoIntrinsicElevenSelectorCrossDual
            factorTwoIntrinsicElevenRetainedEvenWeight
            (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
              gamma p 0 (-1) 0)
            (factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
              gamma r 0 (-1) 0) qMinus sMinus) := by
  let W := factorTwoIntrinsicElevenRetainedEvenWeight
  let FP := factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
    gamma p 0 1 0
  let FM := factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
    gamma p 0 (-1) 0
  let GP := factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
    gamma r 0 1 0
  let GM := factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
    gamma r 0 (-1) 0
  let FB := retainedEvenBaseRepresenterAt gamma p
  let GB := retainedEvenBaseRepresenterAt gamma r
  let FS := retainedEvenSymmetricRepresenterAt gamma p
  let GS := retainedEvenSymmetricRepresenterAt gamma r
  have hP := intervalIntegrable_selectorCross_of_memLp
    W FP GP qPlus sPlus
    (fun x hx ↦ factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc hx)
    (factorTwoIntrinsicElevenRetainedEvenSelectorResidual_div_sqrt_memLp_two
      gamma p 0 qPlus 1 0)
    (factorTwoIntrinsicElevenRetainedEvenSelectorResidual_div_sqrt_memLp_two
      gamma r 0 sPlus 1 0)
  have hM := intervalIntegrable_selectorCross_of_memLp
    W FM GM qMinus sMinus
    (fun x hx ↦ factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc hx)
    (factorTwoIntrinsicElevenRetainedEvenSelectorResidual_div_sqrt_memLp_two
      gamma p 0 qMinus (-1) 0)
    (factorTwoIntrinsicElevenRetainedEvenSelectorResidual_div_sqrt_memLp_two
      gamma r 0 sMinus (-1) 0)
  have hBS := intervalIntegrable_selectorCross_of_memLp W FB GS
    (retainedP024BaseSelector qPlus qMinus)
    (retainedP024SymmetricSelector sPlus sMinus)
    (fun x hx ↦ factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc hx)
    (retainedEvenBaseSelectorResidual_div_sqrt_memLp_two
      gamma p qPlus qMinus)
    (retainedEvenSymmetricSelectorResidual_div_sqrt_memLp_two
      gamma r sPlus sMinus)
  have hSB := intervalIntegrable_selectorCross_of_memLp W FS GB
    (retainedP024SymmetricSelector qPlus qMinus)
    (retainedP024BaseSelector sPlus sMinus)
    (fun x hx ↦ factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc hx)
    (retainedEvenSymmetricSelectorResidual_div_sqrt_memLp_two
      gamma p qPlus qMinus)
    (retainedEvenBaseSelectorResidual_div_sqrt_memLp_two
      gamma r sPlus sMinus)
  unfold factorTwoIntrinsicElevenSelectorCrossDual
  rw [← intervalIntegral.integral_add hBS hSB,
    ← intervalIntegral.integral_sub hP hM,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _hx
  dsimp only [W, FP, FM, GP, GM, FB, GB, FS, GS]
  rw [retainedP024BaseSelectorResidual_eq_endpoint_half_add
      gamma p qPlus qMinus x,
    retainedP024BaseSelectorResidual_eq_endpoint_half_add
      gamma r sPlus sMinus x,
    retainedP024SymmetricSelectorResidual_eq_endpoint_half_sub
      gamma p qPlus qMinus x,
    retainedP024SymmetricSelectorResidual_eq_endpoint_half_sub
      gamma r sPlus sMinus x]
  ring

/-- Endpoint-average selector attached to one of the three retained even
rows. -/
def retainedP024SelectorBasePolynomial (i : Fin 3) : ℝ[X] :=
  retainedP024BaseSelector
    (![retainedP024SelectorPlus0, retainedP024SelectorPlus2,
      retainedP024SelectorPlus4] i)
    (![retainedP024SelectorMinus0, retainedP024SelectorMinus2,
      retainedP024SelectorMinus4] i)

/-- Exact Gram of the three endpoint-average residual rows. -/
def retainedP024SelectorBaseGram : Matrix (Fin 3) (Fin 3) ℝ := fun i j ↦
  factorTwoIntrinsicElevenSelectorCrossDual
    factorTwoIntrinsicElevenRetainedEvenWeight
    (retainedEvenBaseRepresenterAt
      (1 / 512 : ℝ) (shiftedLegendreReal (2 * i.1)))
    (retainedEvenBaseRepresenterAt
      (1 / 512 : ℝ) (shiftedLegendreReal (2 * j.1)))
    (retainedP024SelectorBasePolynomial i)
    (retainedP024SelectorBasePolynomial j)

/-- The endpoint-average normalized residual belongs to the retained weighted
`L²` space. -/
theorem retainedP024BaseSelectorResidual_div_sqrt_memLp_two (i : Fin 3) :
    MemLp (fun x ↦
      factorTwoIntrinsicElevenSelectorResidual
          (retainedEvenBaseRepresenterAt
            (1 / 512 : ℝ) (shiftedLegendreReal (2 * i.1)))
          (retainedP024SelectorBasePolynomial i) x /
        Real.sqrt (factorTwoIntrinsicElevenRetainedEvenWeight x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  exact retainedEvenBaseSelectorResidual_div_sqrt_memLp_two
    (1 / 512 : ℝ) (shiftedLegendreReal (2 * i.1))
    (![retainedP024SelectorPlus0, retainedP024SelectorPlus2,
      retainedP024SelectorPlus4] i)
    (![retainedP024SelectorMinus0, retainedP024SelectorMinus2,
      retainedP024SelectorMinus4] i)

/-- The base and symmetric residual rows as one six-row family. -/
def retainedP024SelectorWholeEvenRepresenter :
    Fin 3 ⊕ Fin 3 → ℝ → ℝ
  | Sum.inl i => retainedEvenBaseRepresenterAt
      (1 / 512 : ℝ) (shiftedLegendreReal (2 * i.1))
  | Sum.inr i => retainedEvenSymmetricRepresenterAt
      (1 / 512 : ℝ) (shiftedLegendreReal (2 * i.1))

/-- Matching base and symmetric polynomial selectors. -/
def retainedP024SelectorWholeEvenPolynomial :
    Fin 3 ⊕ Fin 3 → ℝ[X]
  | Sum.inl i => retainedP024SelectorBasePolynomial i
  | Sum.inr i => retainedP024SymmetricSelector
      (![retainedP024SelectorPlus0, retainedP024SelectorPlus2,
        retainedP024SelectorPlus4] i)
      (![retainedP024SelectorMinus0, retainedP024SelectorMinus2,
        retainedP024SelectorMinus4] i)

/-- Exact Gram of the single combined base--symmetric retained-even residual
square. -/
def retainedP024SelectorWholeEvenGram :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  factorTwoIntrinsicElevenSelectorGram
    factorTwoIntrinsicElevenRetainedEvenWeight
    retainedP024SelectorWholeEvenRepresenter
    retainedP024SelectorWholeEvenPolynomial

/-- The combined six-row Gram is literally one retained-even selector dual,
not a collection of independently bounded entries. -/
theorem retainedP024SelectorWholeEvenDual_eq_matrixQuadratic
    (c : Fin 3 ⊕ Fin 3 → ℝ) :
    factorTwoIntrinsicElevenSelectorDual
        factorTwoIntrinsicElevenRetainedEvenWeight
        (factorTwoIntrinsicElevenSelectorRepresenterSum
          retainedP024SelectorWholeEvenRepresenter c)
        (factorTwoIntrinsicElevenSelectorPolynomialSum
          retainedP024SelectorWholeEvenPolynomial c) =
      star c ⬝ᵥ (retainedP024SelectorWholeEvenGram *ᵥ c) := by
  apply factorTwoIntrinsicElevenSelectorDual_sum_eq_matrixQuadratic
  intro i j
  apply intervalIntegrable_selectorCross_of_memLp
    factorTwoIntrinsicElevenRetainedEvenWeight
    (retainedP024SelectorWholeEvenRepresenter i)
    (retainedP024SelectorWholeEvenRepresenter j)
    (retainedP024SelectorWholeEvenPolynomial i)
    (retainedP024SelectorWholeEvenPolynomial j)
    (fun x hx ↦ factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc hx)
  · rcases i with i | i
    · exact retainedP024BaseSelectorResidual_div_sqrt_memLp_two i
    · exact retainedEvenSymmetricSelectorResidual_div_sqrt_memLp_two
        (1 / 512 : ℝ) (shiftedLegendreReal (2 * i.1))
        (![retainedP024SelectorPlus0, retainedP024SelectorPlus2,
          retainedP024SelectorPlus4] i)
        (![retainedP024SelectorMinus0, retainedP024SelectorMinus2,
          retainedP024SelectorMinus4] i)
  · rcases j with j | j
    · exact retainedP024BaseSelectorResidual_div_sqrt_memLp_two j
    · exact retainedEvenSymmetricSelectorResidual_div_sqrt_memLp_two
        (1 / 512 : ℝ) (shiftedLegendreReal (2 * j.1))
        (![retainedP024SelectorPlus0, retainedP024SelectorPlus2,
          retainedP024SelectorPlus4] j)
        (![retainedP024SelectorMinus0, retainedP024SelectorMinus2,
          retainedP024SelectorMinus4] j)

/-- Oriented weighted Gram from the endpoint-average residual to the
symmetric half-difference residual.  Unlike the ordinary selector Grams this
matrix need not be symmetric. -/
def retainedP024SelectorBaseSymmetricCrossGram :
    Matrix (Fin 3) (Fin 3) ℝ := fun i j ↦
  factorTwoIntrinsicElevenSelectorCrossDual
    factorTwoIntrinsicElevenRetainedEvenWeight
    (retainedEvenBaseRepresenterAt
      (1 / 512 : ℝ) (shiftedLegendreReal (2 * i.1)))
    (retainedEvenSymmetricRepresenterAt
      (1 / 512 : ℝ) (shiftedLegendreReal (2 * j.1)))
    (retainedP024SelectorBasePolynomial i)
    (retainedP024SymmetricSelector
      (![retainedP024SelectorPlus0, retainedP024SelectorPlus2,
        retainedP024SelectorPlus4] j)
      (![retainedP024SelectorMinus0, retainedP024SelectorMinus2,
        retainedP024SelectorMinus4] j))

/-- The combined retained-even residual Gram has its literal base, oriented
cross, and symmetric blocks. -/
theorem retainedP024SelectorWholeEvenGram_eq_fromBlocks :
    retainedP024SelectorWholeEvenGram =
      Matrix.fromBlocks
        retainedP024SelectorBaseGram
        retainedP024SelectorBaseSymmetricCrossGram
        retainedP024SelectorBaseSymmetricCrossGramᴴ
        retainedP024SelectorSymmetricGram := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · rfl
  · rfl
  · simp only [retainedP024SelectorWholeEvenGram,
      factorTwoIntrinsicElevenSelectorGram,
      retainedP024SelectorWholeEvenRepresenter,
      retainedP024SelectorWholeEvenPolynomial,
      Matrix.fromBlocks_apply₂₁, Matrix.conjTranspose_apply,
      retainedP024SelectorBaseSymmetricCrossGram, star_trivial]
    exact factorTwoIntrinsicElevenSelectorCrossDual_comm _ _ _ _ _
  · fin_cases i <;> fin_cases j <;>
      simp [retainedP024SelectorWholeEvenGram,
        factorTwoIntrinsicElevenSelectorGram,
        retainedP024SelectorWholeEvenRepresenter,
        retainedP024SelectorWholeEvenPolynomial,
        retainedP024SelectorSymmetricGram,
        retainedP024SymmetricSelectorGram,
        retainedP024ThreeSelectorGramMatrix, symmetricMatrix3,
        factorTwoIntrinsicElevenSelectorCrossDual_comm]

/-- Endpoint averaging is exactly the sum of the base and symmetric Grams. -/
theorem retainedP024SelectorEndpointAverageGram_eq :
    (1 / 2 : ℝ) •
        (retainedP024SelectorPlusGram + retainedP024SelectorMinusGram) =
      retainedP024SelectorBaseGram + retainedP024SelectorSymmetricGram := by
  ext i j
  have h := retainedEvenBaseCross_eq_endpoint_average_sub_symmetric
    (1 / 512 : ℝ)
    (shiftedLegendreReal (2 * i.1))
    (shiftedLegendreReal (2 * j.1))
    (![retainedP024SelectorPlus0, retainedP024SelectorPlus2,
      retainedP024SelectorPlus4] i)
    (![retainedP024SelectorMinus0, retainedP024SelectorMinus2,
      retainedP024SelectorMinus4] i)
    (![retainedP024SelectorPlus0, retainedP024SelectorPlus2,
      retainedP024SelectorPlus4] j)
    (![retainedP024SelectorMinus0, retainedP024SelectorMinus2,
      retainedP024SelectorMinus4] j)
  fin_cases i <;> fin_cases j <;>
    simp [retainedP024SelectorPlusGram, retainedP024SelectorMinusGram,
      retainedP024EvenEndpointSelectorGram,
      retainedP024SelectorBaseGram, retainedP024SelectorBasePolynomial,
      retainedP024SelectorSymmetricGram,
      retainedP024SymmetricSelectorGram,
      retainedP024ThreeSelectorGramMatrix, symmetricMatrix3,
      factorTwoIntrinsicElevenSelectorCrossDual_comm] at h ⊢ <;>
    linarith

/-- The half-difference of the endpoint Grams is the Hermitian part of the
oriented base--symmetric cross Gram. -/
theorem retainedP024SelectorEndpointHalfDifferenceGram_eq :
    (1 / 2 : ℝ) •
        (retainedP024SelectorPlusGram - retainedP024SelectorMinusGram) =
      retainedP024SelectorBaseSymmetricCrossGram +
        retainedP024SelectorBaseSymmetricCrossGramᴴ := by
  ext i j
  have h := retainedEvenBaseSymmetricCross_add_swap_eq_endpoint_half_sub
    (1 / 512 : ℝ)
    (shiftedLegendreReal (2 * i.1))
    (shiftedLegendreReal (2 * j.1))
    (![retainedP024SelectorPlus0, retainedP024SelectorPlus2,
      retainedP024SelectorPlus4] i)
    (![retainedP024SelectorMinus0, retainedP024SelectorMinus2,
      retainedP024SelectorMinus4] i)
    (![retainedP024SelectorPlus0, retainedP024SelectorPlus2,
      retainedP024SelectorPlus4] j)
    (![retainedP024SelectorMinus0, retainedP024SelectorMinus2,
      retainedP024SelectorMinus4] j)
  fin_cases i <;> fin_cases j <;>
    simp [retainedP024SelectorPlusGram, retainedP024SelectorMinusGram,
      retainedP024EvenEndpointSelectorGram,
      retainedP024SelectorBaseSymmetricCrossGram,
      retainedP024SelectorBasePolynomial,
      retainedP024ThreeSelectorGramMatrix, symmetricMatrix3,
      factorTwoIntrinsicElevenSelectorCrossDual_comm] at h ⊢ <;>
    linarith

/-- Constant coefficient of the gap after endpoint polarization. -/
theorem retainedP024SelectorBoundaryGapConstant_eq_polarized :
    retainedP024SelectorBoundaryGapConstant =
      retainedP024SharpLowMatrix 0 - retainedP024SelectorBaseGram -
        retainedP024SelectorAlternatingGram := by
  have hHalf :
      (1 / 2 : ℝ) • retainedP024SelectorPlusGram +
          (1 / 2 : ℝ) • retainedP024SelectorMinusGram =
        retainedP024SelectorBaseGram + retainedP024SelectorSymmetricGram := by
    simpa only [smul_add] using retainedP024SelectorEndpointAverageGram_eq
  unfold retainedP024SelectorBoundaryGapConstant
    retainedP024SelectorBoundaryGapMatrix retainedP024BoundarySelectorGram
  simp only [retainedP024ChordPlus, retainedP024ChordMinus]
  norm_num only [zero_pow, sub_zero, one_smul]
  rw [hHalf]
  module

/-- Linear coefficient of the gap after endpoint polarization. -/
theorem retainedP024SelectorBoundaryGapLinear_eq_polarized :
    retainedP024SelectorBoundaryGapLinear =
      (1 / 2 : ℝ) •
          (retainedP024SharpLowMatrix 1 - retainedP024SharpLowMatrix (-1)) -
        (retainedP024SelectorBaseSymmetricCrossGram +
          retainedP024SelectorBaseSymmetricCrossGramᴴ) := by
  have hBoundary :
      (1 / 2 : ℝ) •
          (retainedP024BoundarySelectorGram 1 -
            retainedP024BoundarySelectorGram (-1)) =
        retainedP024SelectorBaseSymmetricCrossGram +
          retainedP024SelectorBaseSymmetricCrossGramᴴ := by
    simpa [retainedP024BoundarySelectorGram, retainedP024ChordPlus,
      retainedP024ChordMinus] using
        retainedP024SelectorEndpointHalfDifferenceGram_eq
  unfold retainedP024SelectorBoundaryGapLinear
    retainedP024SelectorBoundaryGapMatrix
  calc
    (1 / 2 : ℝ) •
        ((retainedP024SharpLowMatrix 1 -
            retainedP024BoundarySelectorGram 1) -
          (retainedP024SharpLowMatrix (-1) -
            retainedP024BoundarySelectorGram (-1))) =
      (1 / 2 : ℝ) •
          (retainedP024SharpLowMatrix 1 -
            retainedP024SharpLowMatrix (-1)) -
        (1 / 2 : ℝ) •
          (retainedP024BoundarySelectorGram 1 -
            retainedP024BoundarySelectorGram (-1)) := by
      module
    _ = _ := by rw [hBoundary]

/-- Quadratic coefficient of the gap after endpoint polarization. -/
theorem retainedP024SelectorBoundaryGapQuadratic_eq_polarized :
    retainedP024SelectorBoundaryGapQuadratic =
      (1 / 2 : ℝ) •
          (retainedP024SharpLowMatrix 1 + retainedP024SharpLowMatrix (-1)) -
        retainedP024SharpLowMatrix 0 -
        retainedP024SelectorSymmetricGram +
        retainedP024SelectorAlternatingGram := by
  have hBoundary :
      (1 / 2 : ℝ) •
          (retainedP024BoundarySelectorGram 1 +
            retainedP024BoundarySelectorGram (-1)) -
        retainedP024BoundarySelectorGram 0 =
      retainedP024SelectorSymmetricGram -
        retainedP024SelectorAlternatingGram := by
    unfold retainedP024BoundarySelectorGram
    simp only [retainedP024ChordPlus, retainedP024ChordMinus]
    norm_num only [one_pow, neg_sq, zero_pow, sub_self, zero_smul,
      add_zero, zero_add, one_smul]
    module
  unfold retainedP024SelectorBoundaryGapQuadratic
    retainedP024SelectorBoundaryGapMatrix
  calc
    (1 / 2 : ℝ) •
          ((retainedP024SharpLowMatrix 1 -
              retainedP024BoundarySelectorGram 1) +
            (retainedP024SharpLowMatrix (-1) -
              retainedP024BoundarySelectorGram (-1))) -
        (retainedP024SharpLowMatrix 0 -
          retainedP024BoundarySelectorGram 0) =
      ((1 / 2 : ℝ) •
          (retainedP024SharpLowMatrix 1 +
            retainedP024SharpLowMatrix (-1)) -
        retainedP024SharpLowMatrix 0) -
      ((1 / 2 : ℝ) •
          (retainedP024BoundarySelectorGram 1 +
            retainedP024BoundarySelectorGram (-1)) -
        retainedP024BoundarySelectorGram 0) := by
      module
    _ = _ := by rw [hBoundary]; module

/-- The same boundary pencil with the skew part of the oriented selector
cross Gram retained in the off-diagonal blocks. -/
def retainedP024SelectorAsymmetricSOSGram :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  let G := retainedP024SelectorBaseSymmetricCrossGram
  Matrix.fromBlocks
    (retainedP024SelectorBoundaryGapConstant -
      retainedP024SelectorSOSReserve)
    ((1 / 2 : ℝ) • retainedP024SelectorBoundaryGapLinear +
      (1 / 2 : ℝ) • (Gᴴ - G))
    ((1 / 2 : ℝ) • retainedP024SelectorBoundaryGapLinear +
      (1 / 2 : ℝ) • (G - Gᴴ))
    (retainedP024SelectorBoundaryGapQuadratic +
      retainedP024SelectorSOSReserve)

/-- The phase-affine lift of the sharp low budget, with the fixed reserve
shifted from the constant block to the quadratic block. -/
def retainedP024SharpLowSOSGram :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  Matrix.fromBlocks
    (retainedP024SharpLowMatrix 0 -
      retainedP024SelectorSOSReserve)
    ((1 / 4 : ℝ) •
      (retainedP024SharpLowMatrix 1 -
        retainedP024SharpLowMatrix (-1)))
    ((1 / 4 : ℝ) •
      (retainedP024SharpLowMatrix 1 -
        retainedP024SharpLowMatrix (-1)))
    ((1 / 2 : ℝ) •
        (retainedP024SharpLowMatrix 1 +
          retainedP024SharpLowMatrix (-1)) -
      retainedP024SharpLowMatrix 0 +
      retainedP024SelectorSOSReserve)

/-- The alternating selector contributes with opposite signs to the constant
and quadratic affine-lift blocks. -/
def retainedP024SelectorAlternatingSignedLiftGram :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  Matrix.fromBlocks
    (-retainedP024SelectorAlternatingGram) 0 0
    retainedP024SelectorAlternatingGram

/-- Exact structural decomposition of the asymmetric selector SOS Gram.  The
only non-low whole-square term is the Gram of the complete even retained
residual; the alternating selector is isolated as a signed affine lift. -/
theorem retainedP024SelectorAsymmetricSOSGram_eq_structural :
    retainedP024SelectorAsymmetricSOSGram =
      retainedP024SharpLowSOSGram -
        retainedP024SelectorWholeEvenGram +
        retainedP024SelectorAlternatingSignedLiftGram := by
  rw [retainedP024SelectorWholeEvenGram_eq_fromBlocks]
  unfold retainedP024SelectorAsymmetricSOSGram retainedP024SharpLowSOSGram
    retainedP024SelectorAlternatingSignedLiftGram
  rw [retainedP024SelectorBoundaryGapConstant_eq_polarized,
    retainedP024SelectorBoundaryGapLinear_eq_polarized,
    retainedP024SelectorBoundaryGapQuadratic_eq_polarized]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  all_goals
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
      Matrix.smul_apply, Matrix.zero_apply, Matrix.conjTranspose_apply,
      star_trivial]
    module

/-- Exact affine-lift SOS identity for the full P024 boundary-gap pencil. -/
theorem retainedP024SelectorBoundaryGapMatrix_eq_sos (a : ℝ) :
    retainedP024SelectorBoundaryGapMatrix a =
      (affineLiftMatrix (n := Fin 3) a)ᴴ * retainedP024SelectorSOSGram *
          affineLiftMatrix (n := Fin 3) a +
        (1 - a ^ 2) • retainedP024SelectorSOSReserve := by
  rw [retainedP024SelectorBoundaryGapMatrix_eq_coefficients,
    retainedP024SelectorSOSGram,
    affineLiftMatrix_conjTranspose_mul_fromBlocks_mul_affineLiftMatrix]
  ext i j
  simp
  ring

/-- Exact affine-lift SOS identity with the oriented off-block selector
pairing exposed.  No analytic estimate is used here: the added skew blocks
cancel identically under the affine lift. -/
theorem retainedP024SelectorBoundaryGapMatrix_eq_asymmetric_sos (a : ℝ) :
    retainedP024SelectorBoundaryGapMatrix a =
      (affineLiftMatrix (n := Fin 3) a)ᴴ *
          retainedP024SelectorAsymmetricSOSGram *
          affineLiftMatrix (n := Fin 3) a +
        (1 - a ^ 2) • retainedP024SelectorSOSReserve := by
  rw [retainedP024SelectorBoundaryGapMatrix_eq_coefficients,
    retainedP024SelectorAsymmetricSOSGram,
    affineLiftMatrix_conjTranspose_mul_fromBlocks_mul_affineLiftMatrix]
  ext i j
  simp
  ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorSOSStructural
