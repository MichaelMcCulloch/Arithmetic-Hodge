import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailResidualStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6SelectorGramStructural

set_option autoImplicit false

open Matrix MeasureTheory Polynomial Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorGramStructural

noncomputable section

open ShiftedLegendreLogEnergyOrthogonalProjection
open ShiftedLegendreOrthogonality
open YoshidaFactorTwoPhaseIntrinsicElevenCompleteRepresentersStructural
open YoshidaFactorTwoPhaseIntrinsicElevenConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedRepresentersStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedSelectorHomogeneityStructural
open YoshidaFactorTwoPhaseIntrinsicElevenSelectorGramStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6CompleteRepresenterStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailResidualStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6RetainedRepresenterStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6SelectorGramStructural
open YoshidaFactorTwoPhaseIntrinsicNineFullMixedDecompositionStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive

/-!
# A `3 x 3` selector Gram for the honest retained endpoint row

Only the endpoint-even `P0/P2/P4` row survives at the two projective
endpoints.  This module applies weighted Cauchy directly to the exact
`1 / 512` pole-subtracted representer and keeps the three rows coupled in one
Gram matrix.
-/

/-- The three pole-subtracted direct `P6` basis rows. -/
def factorTwoIntrinsicNineDirectP6ExactResidualBasisRepresenter
    (sigma : ℝ) (i : Fin 3) : ℝ → ℝ :=
  factorTwoIntrinsicNineDirectP6RetainedWholeRepresenterAt
    (1 / 512 : ℝ) sigma 0
    (factorTwoIntrinsicNineDirectP024Embed (Pi.single i 1))

/-- Weighted selector Gram of the three exact residual rows. -/
def factorTwoIntrinsicNineDirectP6ExactResidualSelectorGram
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) : Matrix (Fin 3) (Fin 3) ℝ :=
  factorTwoIntrinsicElevenSelectorGram
    factorTwoIntrinsicElevenRetainedEvenWeight
    (factorTwoIntrinsicNineDirectP6ExactResidualBasisRepresenter sigma) q

@[simp] theorem factorTwoIntrinsicNineDirectP024Embed_apply_zero
    (c : Fin 3 → ℝ) : factorTwoIntrinsicNineDirectP024Embed c 0 = c 0 := rfl

@[simp] theorem factorTwoIntrinsicNineDirectP024Embed_apply_one
    (c : Fin 3 → ℝ) : factorTwoIntrinsicNineDirectP024Embed c 1 = c 1 := rfl

@[simp] theorem factorTwoIntrinsicNineDirectP024Embed_apply_two
    (c : Fin 3 → ℝ) : factorTwoIntrinsicNineDirectP024Embed c 2 = c 2 := rfl

@[simp] theorem factorTwoIntrinsicNineDirectP024Embed_apply_three
    (c : Fin 3 → ℝ) : factorTwoIntrinsicNineDirectP024Embed c 3 = 0 := rfl

@[simp] theorem factorTwoIntrinsicNineDirectP024Embed_apply_four
    (c : Fin 3 → ℝ) : factorTwoIntrinsicNineDirectP024Embed c 4 = 0 := rfl

@[simp] theorem factorTwoIntrinsicNineDirectP024Embed_apply_five
    (c : Fin 3 → ℝ) : factorTwoIntrinsicNineDirectP024Embed c 5 = 0 := rfl

/-- Every retained endpoint basis residual belongs to the weighted dual
space, uniformly in the selector polynomial. -/
theorem exactResidualBasisSelectorResidual_div_sqrt_memLp_two
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) (i : Fin 3) :
    MemLp (fun z ↦
      factorTwoIntrinsicElevenSelectorResidual
          (factorTwoIntrinsicNineDirectP6ExactResidualBasisRepresenter sigma i)
          (q i) z /
        Real.sqrt (factorTwoIntrinsicElevenRetainedEvenWeight z)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  let e : Fin 6 → ℝ :=
    factorTwoIntrinsicNineDirectP024Embed (Pi.single i 1)
  let pE := factorTwoIntrinsicNineDirectP024Polynomial e
  let pO := factorTwoIntrinsicNineDirectP135Polynomial e
  let qBase := q i - factorTwoIntrinsicNineDirectP6RankPolynomial sigma e
  have h :=
    factorTwoIntrinsicElevenRetainedEvenSelectorResidual_div_sqrt_memLp_two
      (1 / 512 : ℝ) pE pO qBase sigma 0
  apply (memLp_congr_ae (μ := volume.restrict (Ioc (-1 : ℝ) 1)) ?_).mpr h
  filter_upwards [] with z
  unfold factorTwoIntrinsicNineDirectP6ExactResidualBasisRepresenter
    factorTwoIntrinsicNineDirectP6RetainedWholeRepresenterAt
    factorTwoIntrinsicNineDirectP6WholeRepresenter
    factorTwoIntrinsicNineDirectP6PotentialPoleRepresenter
    factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
    factorTwoIntrinsicElevenSelectorResidual
  dsimp only [e, pE, pO, qBase]
  rw [show centeredPolynomialLift
        (q i - factorTwoIntrinsicNineDirectP6RankPolynomial sigma e) z =
      centeredPolynomialLift (q i) z -
        centeredPolynomialLift
          (factorTwoIntrinsicNineDirectP6RankPolynomial sigma e) z by
      unfold centeredPolynomialLift
      rw [Polynomial.eval_sub]]
  rw [congrFun (centeredPolynomialLift_directP6RankPolynomial sigma e) z]
  ring

/-- The exact retained representer synthesized from the three endpoint-even
coordinates agrees pointwise on the physical interval with the synthesis of
the three basis rows. -/
theorem exactResidualRepresenter_eq_basisSum_on_Icc
    (sigma : ℝ) (c : Fin 3 → ℝ) (z : ℝ) (hz : z ∈ Icc (-1 : ℝ) 1) :
    factorTwoIntrinsicNineDirectP6RetainedWholeRepresenterAt
        (1 / 512 : ℝ) sigma 0
        (factorTwoIntrinsicNineDirectP024Embed c) z =
      factorTwoIntrinsicElevenSelectorRepresenterSum
        (factorTwoIntrinsicNineDirectP6ExactResidualBasisRepresenter sigma)
        c z := by
  have hEven (d : Fin 3 → ℝ) :
      factorTwoIntrinsicNineDirectP024Polynomial
          (factorTwoIntrinsicNineDirectP024Embed d) =
        threeSelectorPolynomial (d 0) (d 1) (d 2)
          (shiftedLegendreReal 0) (shiftedLegendreReal 2)
          (shiftedLegendreReal 4) := by
    unfold factorTwoIntrinsicNineDirectP024Polynomial
      factorTwoIntrinsicNineEvenPolynomial threeSelectorPolynomial
    simp
  have hOdd (d : Fin 3 → ℝ) :
      factorTwoIntrinsicNineDirectP135Polynomial
          (factorTwoIntrinsicNineDirectP024Embed d) = 0 := by
    unfold factorTwoIntrinsicNineDirectP135Polynomial
      factorTwoIntrinsicNineOddPolynomial
    simp
  have hWhole (d : Fin 3 → ℝ) :
      factorTwoIntrinsicNineDirectP6RetainedWholeRepresenterAt
          (1 / 512 : ℝ) sigma 0
          (factorTwoIntrinsicNineDirectP024Embed d) z =
        factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
            (1 / 512 : ℝ)
            (threeSelectorPolynomial (d 0) (d 1) (d 2)
              (shiftedLegendreReal 0) (shiftedLegendreReal 2)
              (shiftedLegendreReal 4)) 0 sigma 0 z +
          factorTwoIntrinsicNineDirectP6RankRepresenter sigma
            (factorTwoIntrinsicNineDirectP024Embed d) z := by
    unfold factorTwoIntrinsicNineDirectP6RetainedWholeRepresenterAt
      factorTwoIntrinsicNineDirectP6WholeRepresenter
      factorTwoIntrinsicNineDirectP6PotentialPoleRepresenter
      factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
    rw [hEven d, hOdd d]
    ring
  unfold factorTwoIntrinsicNineDirectP6ExactResidualBasisRepresenter
    factorTwoIntrinsicElevenSelectorRepresenterSum
  norm_num [Fin.sum_univ_succ]
  rw [hWhole c, hWhole (Pi.single 0 1), hWhole (Pi.single 1 1),
    hWhole (Pi.single 2 1)]
  rw [retainedEvenMixedRepresenterAt_threeSelectorPolynomial_on_Icc
      (1 / 512 : ℝ) (c 0) (c 1) (c 2) sigma 0
      (shiftedLegendreReal 0) (shiftedLegendreReal 2)
      (shiftedLegendreReal 4) z hz]
  unfold threeSelectorPolynomial threeSelectorRepresenter
    factorTwoIntrinsicNineDirectP6RankRepresenter
  simp
  ring

/-- The exact residual scalar border is the pairing of `P6` with the finite
synthesis of its three retained basis rows. -/
theorem factorTwoIntrinsicNineDirectP6ExactResidualBorder_eq_basisSumPairing
    (sigma : ℝ) (c : Fin 3 → ℝ) :
    factorTwoIntrinsicNineDirectP6ExactResidualBorder sigma c =
      ∫ z : ℝ in -1..1,
        factorTwoIntrinsicElevenSelectorRepresenterSum
            (factorTwoIntrinsicNineDirectP6ExactResidualBasisRepresenter sigma)
            c z * factorTwoCenteredP6 z := by
  rw [factorTwoIntrinsicNineDirectP6ExactResidualBorder_eq_pairing]
  apply intervalIntegral.integral_congr
  intro z hz
  rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hz
  change
    factorTwoIntrinsicNineDirectP6RetainedWholeRepresenterAt
          (1 / 512 : ℝ) sigma 0
          (factorTwoIntrinsicNineDirectP024Embed c) z *
        factorTwoCenteredP6 z =
      factorTwoIntrinsicElevenSelectorRepresenterSum
          (factorTwoIntrinsicNineDirectP6ExactResidualBasisRepresenter sigma)
          c z * factorTwoCenteredP6 z
  rw [exactResidualRepresenter_eq_basisSum_on_Icc sigma c z hz]

/-- A finite synthesis of degree-below-six endpoint selectors is again
degree below six. -/
theorem exactResidualSelectorPolynomialSum_natDegree_lt_six
    (q : Fin 3 → ℝ[X]) (hq : ∀ i, (q i).natDegree < 6)
    (c : Fin 3 → ℝ) :
    (factorTwoIntrinsicElevenSelectorPolynomialSum q c).natDegree < 6 := by
  unfold factorTwoIntrinsicElevenSelectorPolynomialSum
  have hle : (∑ i : Fin 3, c i • q i).natDegree ≤ 5 :=
    Polynomial.natDegree_sum_le_of_forall_le Finset.univ _
      (fun i _hi ↦ (Polynomial.natDegree_smul_le (c i) (q i)).trans
        (Nat.le_pred_of_lt (hq i)))
  omega

/-- Weighted Cauchy for the complete pole-subtracted endpoint row. -/
theorem factorTwoIntrinsicNineDirectP6ExactResidualBorder_sq_le_selectorGram_mul_mass
    (sigma : ℝ) (q : Fin 3 → ℝ[X])
    (hq : ∀ i, (q i).natDegree < 6) (c : Fin 3 → ℝ) :
    factorTwoIntrinsicNineDirectP6ExactResidualBorder sigma c ^ 2 ≤
      (star c ⬝ᵥ
        (factorTwoIntrinsicNineDirectP6ExactResidualSelectorGram sigma q *ᵥ c)) *
        factorTwoIntrinsicNineDirectP6WeightedMass := by
  classical
  let W := factorTwoIntrinsicElevenRetainedEvenWeight
  let F := factorTwoIntrinsicNineDirectP6ExactResidualBasisRepresenter sigma
  let p := factorTwoIntrinsicElevenSelectorPolynomialSum q c
  have hW : ∀ z ∈ Icc (-1 : ℝ) 1, 0 < W z := by
    intro z hz
    exact factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc hz
  have hRow (i : Fin 3) : MemLp (fun z ↦
      factorTwoIntrinsicElevenSelectorResidual (F i) (q i) z /
        Real.sqrt (W z)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    simpa only [W, F] using
      exactResidualBasisSelectorResidual_div_sqrt_memLp_two sigma q i
  have hDual : MemLp (fun z ↦
      factorTwoIntrinsicElevenSelectorResidual
          (factorTwoIntrinsicElevenSelectorRepresenterSum F c) p z /
        Real.sqrt (W z)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    have hSum : MemLp (fun z ↦ ∑ i : Fin 3,
        c i * (factorTwoIntrinsicElevenSelectorResidual (F i) (q i) z /
          Real.sqrt (W z))) 2
        (volume.restrict (Ioc (-1 : ℝ) 1)) := by
      apply memLp_finset_sum Finset.univ
      intro i _hi
      exact (hRow i).const_mul (c i)
    apply (memLp_congr_ae (μ := volume.restrict (Ioc (-1 : ℝ) 1)) ?_).mpr
      hSum
    filter_upwards [] with z
    dsimp only [p]
    rw [factorTwoIntrinsicElevenSelectorResidual_sum]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  have hPrimal := sqrt_retainedEvenWeight_mul_memLp_two
    factorTwoCenteredP6 continuous_factorTwoCenteredP6
  have hDegree : p.natDegree < 6 := by
    simpa only [p] using
      exactResidualSelectorPolynomialSum_natDegree_lt_six q hq c
  have hCauchy := sq_representerPairing_le_selectorDual_mul_reserve
    W (factorTwoIntrinsicElevenSelectorRepresenterSum F c)
      factorTwoCenteredP6 continuous_factorTwoCenteredP6
      factorTwoCenteredP6_momentsVanishBelow p hDegree hW hDual hPrimal
  have hInt : ∀ i j : Fin 3, IntervalIntegrable (fun z ↦
      factorTwoIntrinsicElevenSelectorResidual (F i) (q i) z *
        factorTwoIntrinsicElevenSelectorResidual (F j) (q j) z / W z)
      volume (-1) 1 := by
    intro i j
    exact intervalIntegrable_selectorCross_of_memLp
      W (F i) (F j) (q i) (q j) hW (hRow i) (hRow j)
  have hGram := factorTwoIntrinsicElevenSelectorDual_sum_eq_matrixQuadratic
    W F q hInt c
  rw [← factorTwoIntrinsicNineDirectP6ExactResidualBorder_eq_basisSumPairing
    sigma c, hGram] at hCauchy
  simpa only [W, F, p,
    factorTwoIntrinsicNineDirectP6ExactResidualSelectorGram,
    factorTwoIntrinsicNineDirectP6WeightedMass] using hCauchy

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorGramStructural
