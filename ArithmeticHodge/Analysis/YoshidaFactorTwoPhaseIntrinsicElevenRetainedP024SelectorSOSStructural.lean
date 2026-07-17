import ArithmeticHodge.Analysis.ThreeByThreePositiveMixedDeterminant
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorStructural

set_option autoImplicit false

open Matrix Polynomial
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorSOSStructural

open ThreeByThreePositiveMixedDeterminant
open ThreeByThreeRankOneSchur
open ShiftedLegendreBasis
open ShiftedLegendreOrthogonality

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
    ![0.581480084230057, 0.314985947369881, 0.376194868402193,
      -0.0459233632117648, 0.246890925381244, -0.159896748897116]

/-- Positive symmetric-endpoint selector for the `P₂` production row. -/
def retainedP024SelectorPlus2 : ℝ[X] :=
  retainedP024EvenSelectorPolynomial
    ![-2.93415610542607, 0.681926869082122, 0.461601127142810,
      0.083303222844454, 0.255626108276939, -0.161281708195295]

/-- Positive symmetric-endpoint selector for the `P₄` production row. -/
def retainedP024SelectorPlus4 : ℝ[X] :=
  retainedP024EvenSelectorPolynomial
    ![-39.0981285401200, -17.2664590255019, 0.362597775779095,
      0.551321383289806, 0.222773813641156, -0.095315779709292]

/-- Negative symmetric-endpoint selector for the `P₀` production row. -/
def retainedP024SelectorMinus0 : ℝ[X] :=
  retainedP024EvenSelectorPolynomial
    ![2.49201571123514, 1.36789293909456, 0.492693756283890,
      0.615180355550550, 0.143920379021179, 0.380735864188658]

/-- Negative symmetric-endpoint selector for the `P₂` production row. -/
def retainedP024SelectorMinus2 : ℝ[X] :=
  retainedP024EvenSelectorPolynomial
    ![3.27073188271896, 0.645948496050952, 0.791604350613995,
      0.587344967137150, 0.175251943922381, 0.397965507733058]

/-- Negative symmetric-endpoint selector for the `P₄` production row. -/
def retainedP024SelectorMinus4 : ℝ[X] :=
  retainedP024EvenSelectorPolynomial
    ![39.1946717206406, 17.9626842909223, 0.975760404287665,
      0.573942233904833, 0.339150817752883, 0.378282604632681]

/-- Alternating selector for the `P₀` production row. -/
def retainedP024SelectorAlt0 : ℝ[X] :=
  retainedP024OddSelectorPolynomial
    ![-0.114841038855505, -0.517796780771150, -0.052190223852219,
      -0.191992337114470, -0.152184575620256]

/-- Alternating selector for the `P₂` production row. -/
def retainedP024SelectorAlt2 : ℝ[X] :=
  retainedP024OddSelectorPolynomial
    ![1.29907711964846, -0.417889966349968, 0.063267794787125,
      -0.234226196095805, -0.060095909312134]

/-- Alternating selector for the `P₄` production row. -/
def retainedP024SelectorAlt4 : ℝ[X] :=
  retainedP024OddSelectorPolynomial
    ![52.7197029705882, 1.77912057730193, 0.021972924733990,
      -0.245683150634203, 0.136004953890509]

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

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorSOSStructural
