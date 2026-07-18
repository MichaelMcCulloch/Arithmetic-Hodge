import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedConstrainedWeightedDualStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenSelectorGramStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6CompleteRepresenterStructural

set_option autoImplicit false

open Matrix MeasureTheory Polynomial Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6SelectorGramStructural

noncomputable section

open ShiftedLegendreLogEnergyOrthogonalProjection
open ShiftedLegendreOrthogonality
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialIntegrable
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicElevenCompleteRepresentersStructural
open YoshidaFactorTwoPhaseIntrinsicElevenConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedRepresentersStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedSelectorHomogeneityStructural
open YoshidaFactorTwoPhaseIntrinsicElevenSelectorGramStructural
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6BorderStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6CompleteRepresenterStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectSixSchurStructural
open YoshidaFactorTwoPhaseIntrinsicNineFullMixedDecompositionStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive

/-!
# A retained-weight selector Gram for the direct `P6` border

The complete `P6` border row contains endpoint logarithms, so an unweighted
`L²` Gram is not the natural object.  This file keeps the exact coupled row,
subtracts an arbitrary degree-below-six polynomial selector, and measures the
residual in the retained even weight.  The explicit rank-one `P0`--`P6`
correction is absorbed into the selector polynomial before invoking weighted
regularity.
-/

/-- Polynomial whose centered lift is the explicit rank-one part of the
complete direct `P6` representer. -/
def factorTwoIntrinsicNineDirectP6RankPolynomial
    (a : ℝ) (x : Fin 6 → ℝ) : ℝ[X] :=
  (a * poleFreeCoeff6 yoshidaEndpointA * (16 / 231 : ℝ) * x 0) •
    shiftedLegendreReal 6

theorem centeredPolynomialLift_directP6RankPolynomial
    (a : ℝ) (x : Fin 6 → ℝ) :
    centeredPolynomialLift
        (factorTwoIntrinsicNineDirectP6RankPolynomial a x) =
      factorTwoIntrinsicNineDirectP6RankRepresenter a x := by
  funext z
  unfold factorTwoIntrinsicNineDirectP6RankPolynomial
    factorTwoIntrinsicNineDirectP6RankRepresenter
    centeredPolynomialLift factorTwoCenteredP6
  rw [Polynomial.eval_smul]
  rfl

/-- The six complete row functions obtained from the coordinate units. -/
def factorTwoIntrinsicNineDirectP6BasisRepresenter
    (a b : ℝ) (i : Fin 6) : ℝ → ℝ :=
  factorTwoIntrinsicNineDirectP6WholeRepresenter a b (Pi.single i 1)

/-- Every selected basis row belongs to the retained weighted dual space.
The rank polynomial is folded into the selector before applying the existing
complete-representer regularity theorem. -/
theorem directP6BasisSelectorResidual_div_sqrt_memLp_two
    (a b : ℝ) (q : Fin 6 → ℝ[X]) (i : Fin 6) :
    MemLp (fun z ↦
      factorTwoIntrinsicElevenSelectorResidual
          (factorTwoIntrinsicNineDirectP6BasisRepresenter a b i) (q i) z /
        Real.sqrt (factorTwoIntrinsicElevenRetainedEvenWeight z)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  let e : Fin 6 → ℝ := Pi.single i 1
  let pE := factorTwoIntrinsicNineDirectP024Polynomial e
  let pO := factorTwoIntrinsicNineDirectP135Polynomial e
  let qBase := q i - factorTwoIntrinsicNineDirectP6RankPolynomial a e
  have h :=
    factorTwoIntrinsicElevenRetainedEvenSelectorResidual_div_sqrt_memLp_two
      0 pE pO qBase a b
  apply (memLp_congr_ae (μ := volume.restrict (Ioc (-1 : ℝ) 1)) ?_).mpr h
  filter_upwards [] with z
  unfold factorTwoIntrinsicNineDirectP6BasisRepresenter
    factorTwoIntrinsicNineDirectP6WholeRepresenter
    factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
    factorTwoIntrinsicElevenSelectorResidual
  dsimp only [e, pE, pO, qBase]
  rw [show centeredPolynomialLift
        (q i - factorTwoIntrinsicNineDirectP6RankPolynomial a e) z =
      centeredPolynomialLift (q i) z -
        centeredPolynomialLift
          (factorTwoIntrinsicNineDirectP6RankPolynomial a e) z by
      unfold centeredPolynomialLift
      rw [Polynomial.eval_sub]]
  rw [congrFun (centeredPolynomialLift_directP6RankPolynomial a e) z]
  simp only [zero_mul, sub_zero]
  ring

/-- Weighted selector Gram of the six complete direct `P6` basis rows. -/
def factorTwoIntrinsicNineDirectP6SelectorGram
    (a b : ℝ) (q : Fin 6 → ℝ[X]) : Matrix (Fin 6) (Fin 6) ℝ :=
  factorTwoIntrinsicElevenSelectorGram
    factorTwoIntrinsicElevenRetainedEvenWeight
    (factorTwoIntrinsicNineDirectP6BasisRepresenter a b) q

/-- Exact retained-weight mass of the target `P6` mode. -/
def factorTwoIntrinsicNineDirectP6WeightedMass : ℝ :=
  ∫ z : ℝ in -1..1,
    factorTwoIntrinsicElevenRetainedEvenWeight z *
      factorTwoCenteredP6 z ^ 2

/-- Closed form of the retained target mass.  Its only transcendental entry
is the exact centered-`P6` endpoint-potential ratio. -/
theorem factorTwoIntrinsicNineDirectP6WeightedMass_eq :
    factorTwoIntrinsicNineDirectP6WeightedMass =
      ((13 / 100 : ℝ) +
        (63 / 128 : ℝ) * (249251 / 180180 - Real.log 2)) *
          (2 / 13 : ℝ) := by
  have hConst : IntervalIntegrable (fun z : ℝ ↦
      (13 / 100 : ℝ) * factorTwoCenteredP6 z ^ 2) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul (continuous_factorTwoCenteredP6.pow 2)
  have hPotential : IntervalIntegrable (fun z : ℝ ↦
      (63 / 128 : ℝ) *
        (yoshidaEndpointPotential z * factorTwoCenteredP6 z ^ 2))
      volume (-1) 1 := by
    apply IntervalIntegrable.const_mul
    apply intervalIntegrable_endpointPotential_mul
    exact continuous_factorTwoCenteredP6.pow 2
  unfold factorTwoIntrinsicNineDirectP6WeightedMass
    factorTwoIntrinsicElevenRetainedEvenWeight
  rw [show (fun z : ℝ ↦
      ((13 / 100 : ℝ) + (63 / 128 : ℝ) * yoshidaEndpointPotential z) *
        factorTwoCenteredP6 z ^ 2) =
      fun z ↦ (13 / 100 : ℝ) * factorTwoCenteredP6 z ^ 2 +
        (63 / 128 : ℝ) *
          (yoshidaEndpointPotential z * factorTwoCenteredP6 z ^ 2) by
      funext z
      ring,
    intervalIntegral.integral_add hConst hPotential,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  change (13 / 100 : ℝ) * factorTwoIntrinsicEnergy factorTwoCenteredP6 +
      (63 / 128 : ℝ) *
        factorTwoIntrinsicPotentialEnergy factorTwoCenteredP6 = _
  rw [factorTwoCenteredP6_potential_ratio, factorTwoCenteredP6_energy]
  ring

theorem intervalIntegrable_directP6BasisRepresenter_mul_P6
    (a b : ℝ) (i : Fin 6) :
    IntervalIntegrable (fun z : ℝ ↦
      factorTwoIntrinsicNineDirectP6BasisRepresenter a b i z *
        factorTwoCenteredP6 z) volume (-1) 1 := by
  let e : Fin 6 → ℝ := Pi.single i 1
  let pE := factorTwoIntrinsicNineDirectP024Polynomial e
  let pO := factorTwoIntrinsicNineDirectP135Polynomial e
  have hComplete := intervalIntegrable_completeEvenRepresenter_mul
    pE pO factorTwoCenteredP6 continuous_factorTwoCenteredP6 a b
  have hRank : IntervalIntegrable (fun z : ℝ ↦
      factorTwoIntrinsicNineDirectP6RankRepresenter a e z *
        factorTwoCenteredP6 z) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold factorTwoIntrinsicNineDirectP6RankRepresenter
    exact (continuous_const.mul continuous_factorTwoCenteredP6).mul
      continuous_factorTwoCenteredP6
  apply (hComplete.add hRank).congr
  intro z _hz
  unfold factorTwoIntrinsicNineDirectP6BasisRepresenter
    factorTwoIntrinsicNineDirectP6WholeRepresenter
  dsimp only [e, pE, pO]
  ring

/-- The scalar border functional is the pairing of `P6` with the finite
synthesis of its six complete basis rows. -/
theorem factorTwoIntrinsicNineDirectP6BorderFunctional_eq_basisSumPairing
    (a b : ℝ) (x : Fin 6 → ℝ) :
    factorTwoIntrinsicNineDirectP6BorderFunctional a b x =
      ∫ z : ℝ in -1..1,
        factorTwoIntrinsicElevenSelectorRepresenterSum
            (factorTwoIntrinsicNineDirectP6BasisRepresenter a b) x z *
          factorTwoCenteredP6 z := by
  classical
  let F := factorTwoIntrinsicNineDirectP6BasisRepresenter a b
  have hBasis (i : Fin 6) :
      factorTwoIntrinsicNineDirectP6BorderFunctional a b (Pi.single i 1) =
        ∫ z : ℝ in -1..1, F i z * factorTwoCenteredP6 z := by
    simpa only [F, factorTwoIntrinsicNineDirectP6BasisRepresenter] using
      factorTwoIntrinsicNineDirectP6BorderFunctional_eq_wholeRepresenterPairing
        a b (Pi.single i 1)
  calc
    factorTwoIntrinsicNineDirectP6BorderFunctional a b x =
        ∑ i : Fin 6, x i *
          factorTwoIntrinsicNineDirectP6BorderFunctional a b
            (Pi.single i 1) := by
      unfold factorTwoIntrinsicNineDirectP6BorderFunctional
      simp only [single_one_dotProduct]
      rfl
    _ = ∑ i : Fin 6, x i *
          (∫ z : ℝ in -1..1, F i z * factorTwoCenteredP6 z) := by
      simp_rw [hBasis]
    _ = ∑ i : Fin 6, ∫ z : ℝ in -1..1,
          x i * (F i z * factorTwoCenteredP6 z) := by
      simp_rw [intervalIntegral.integral_const_mul]
    _ = ∫ z : ℝ in -1..1,
          ∑ i : Fin 6, x i * (F i z * factorTwoCenteredP6 z) := by
      rw [intervalIntegral.integral_finset_sum]
      intro i _hi
      exact (intervalIntegrable_directP6BasisRepresenter_mul_P6 a b i).const_mul
        (x i)
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro z _hz
      unfold factorTwoIntrinsicElevenSelectorRepresenterSum
      dsimp only [F]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _hi
      ring

theorem directP6SelectorPolynomialSum_natDegree_lt_six
    (q : Fin 6 → ℝ[X]) (hq : ∀ i, (q i).natDegree < 6)
    (x : Fin 6 → ℝ) :
    (factorTwoIntrinsicElevenSelectorPolynomialSum q x).natDegree < 6 := by
  unfold factorTwoIntrinsicElevenSelectorPolynomialSum
  have hle : (∑ i : Fin 6, x i • q i).natDegree ≤ 5 :=
    Polynomial.natDegree_sum_le_of_forall_le Finset.univ _
      (fun i _hi ↦ (Polynomial.natDegree_smul_le (x i) (q i)).trans
        (Nat.le_pred_of_lt (hq i)))
  omega

/-- Weighted Cauchy after exact subtraction of six arbitrary
degree-below-six selectors.  The right side is one coupled Gram quadratic;
no rowwise triangle inequality is used. -/
theorem factorTwoIntrinsicNineDirectP6Border_sq_le_selectorGram_mul_mass
    (a b : ℝ) (q : Fin 6 → ℝ[X])
    (hq : ∀ i, (q i).natDegree < 6) (x : Fin 6 → ℝ) :
    factorTwoIntrinsicNineDirectP6BorderFunctional a b x ^ 2 ≤
      (star x ⬝ᵥ
        (factorTwoIntrinsicNineDirectP6SelectorGram a b q *ᵥ x)) *
        factorTwoIntrinsicNineDirectP6WeightedMass := by
  classical
  let W := factorTwoIntrinsicElevenRetainedEvenWeight
  let F := factorTwoIntrinsicNineDirectP6BasisRepresenter a b
  let p := factorTwoIntrinsicElevenSelectorPolynomialSum q x
  have hW : ∀ z ∈ Icc (-1 : ℝ) 1, 0 < W z := by
    intro z hz
    exact factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc hz
  have hRow (i : Fin 6) : MemLp (fun z ↦
      factorTwoIntrinsicElevenSelectorResidual (F i) (q i) z /
        Real.sqrt (W z)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    simpa only [W, F] using
      directP6BasisSelectorResidual_div_sqrt_memLp_two a b q i
  have hDual : MemLp (fun z ↦
      factorTwoIntrinsicElevenSelectorResidual
          (factorTwoIntrinsicElevenSelectorRepresenterSum F x) p z /
        Real.sqrt (W z)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    have hSum : MemLp (fun z ↦ ∑ i : Fin 6,
        x i * (factorTwoIntrinsicElevenSelectorResidual (F i) (q i) z /
          Real.sqrt (W z))) 2
        (volume.restrict (Ioc (-1 : ℝ) 1)) := by
      apply memLp_finset_sum Finset.univ
      intro i _hi
      exact (hRow i).const_mul (x i)
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
      directP6SelectorPolynomialSum_natDegree_lt_six q hq x
  have hCauchy := sq_representerPairing_le_selectorDual_mul_reserve
    W (factorTwoIntrinsicElevenSelectorRepresenterSum F x)
      factorTwoCenteredP6 continuous_factorTwoCenteredP6
      factorTwoCenteredP6_momentsVanishBelow p hDegree hW hDual hPrimal
  have hInt : ∀ i j : Fin 6, IntervalIntegrable (fun z ↦
      factorTwoIntrinsicElevenSelectorResidual (F i) (q i) z *
        factorTwoIntrinsicElevenSelectorResidual (F j) (q j) z / W z)
      volume (-1) 1 := by
    intro i j
    exact intervalIntegrable_selectorCross_of_memLp
      W (F i) (F j) (q i) (q j) hW (hRow i) (hRow j)
  have hGram := factorTwoIntrinsicElevenSelectorDual_sum_eq_matrixQuadratic
    W F q hInt x
  rw [← factorTwoIntrinsicNineDirectP6BorderFunctional_eq_basisSumPairing
    a b x, hGram] at hCauchy
  simpa only [W, F, p, factorTwoIntrinsicNineDirectP6SelectorGram,
    factorTwoIntrinsicNineDirectP6WeightedMass] using hCauchy

/-- An inverse-free retained-weight Loewner gap closes the first bordered
cutoff-nine extension.  The hypothesis is a single `6 × 6` positive-definite
matrix inequality, rather than six separately estimated border entries. -/
theorem factorTwoIntrinsicNineDirectP6PrefixMatrix_posDef_of_selectorGramLoewner
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1)
    (q : Fin 6 → ℝ[X]) (hq : ∀ i, (q i).natDegree < 6)
    (hLoewner :
      ((factorTwoIntrinsicNineDirectP6RetainedDiagonal a b) •
          factorTwoIntrinsicNineDirectCoreMatrix a b -
        factorTwoIntrinsicNineDirectP6WeightedMass •
          factorTwoIntrinsicNineDirectP6SelectorGram a b q).PosDef) :
    (factorTwoIntrinsicNineDirectP6PrefixMatrix a b).PosDef := by
  apply factorTwoIntrinsicNineDirectP6PrefixMatrix_posDef_of_border_cauchy
    a b hab
  intro x hx
  have hCauchy :=
    factorTwoIntrinsicNineDirectP6Border_sq_le_selectorGram_mul_mass
      a b q hq x
  simp only [star_trivial] at hCauchy
  have hGap := hLoewner.dotProduct_mulVec_pos hx
  simp only [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul,
    star_trivial, smul_eq_mul] at hGap
  nlinarith

/-- Certificate-friendly variant: the finite Loewner certificate may be only
positive semidefinite at any scalar `δ` strictly below the honest retained
`P6` diagonal.  Strictness is supplied structurally by the already-proved
positive-definite six-mode core. -/
theorem factorTwoIntrinsicNineDirectP6PrefixMatrix_posDef_of_selectorGramLoewner_le
    (a b δ : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1)
    (q : Fin 6 → ℝ[X]) (hq : ∀ i, (q i).natDegree < 6)
    (hδ : δ < factorTwoIntrinsicNineDirectP6RetainedDiagonal a b)
    (hLoewner :
      (δ • factorTwoIntrinsicNineDirectCoreMatrix a b -
        factorTwoIntrinsicNineDirectP6WeightedMass •
          factorTwoIntrinsicNineDirectP6SelectorGram a b q).PosSemidef) :
    (factorTwoIntrinsicNineDirectP6PrefixMatrix a b).PosDef := by
  apply factorTwoIntrinsicNineDirectP6PrefixMatrix_posDef_of_border_cauchy
    a b hab
  intro x hx
  have hCauchy :=
    factorTwoIntrinsicNineDirectP6Border_sq_le_selectorGram_mul_mass
      a b q hq x
  simp only [star_trivial] at hCauchy
  have hGap := hLoewner.dotProduct_mulVec_nonneg x
  simp only [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul,
    star_trivial, smul_eq_mul] at hGap
  have hCore :=
    (factorTwoIntrinsicNineDirectCoreMatrix_posDef a b hab).dotProduct_mulVec_pos
      hx
  simp only [star_trivial] at hCore
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6SelectorGramStructural
