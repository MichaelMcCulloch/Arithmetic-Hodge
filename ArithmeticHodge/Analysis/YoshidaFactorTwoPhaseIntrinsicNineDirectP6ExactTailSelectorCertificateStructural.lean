import ArithmeticHodge.Analysis.ThreeByThreePositiveMixedDeterminant
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorReciprocalLoewnerStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectPSevenEndpointSchurStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineFullMixedDecompositionStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseRetainedSingularSchurStructural

set_option autoImplicit false

open Matrix MeasureTheory Polynomial Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorCertificateStructural

noncomputable section

open ShiftedLegendreOrthogonality
open ShiftedLegendreBasis
open ShiftedLegendreLogEnergyOrthogonalProjection
open ThreeByThreePositiveMixedDeterminant
open ThreeByThreeRankOneSchur
open UnitIntervalLogEnergyAffine
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointOddResidualRegularity
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024Structural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailResidualStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorGramStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorReciprocalLoewnerStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6BorderDecompositionStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6BorderStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6CompleteRepresenterStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectP6SelectorGramStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectPSevenEndpointSchurStructural
open YoshidaFactorTwoPhaseIntrinsicNineDirectProjectiveDeterminantStructural
open YoshidaFactorTwoPhaseIntrinsicNineFullMixedDecompositionStructural
open YoshidaFactorTwoPhaseIntrinsicNineStaticNestedSchurStructural
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicSixP4EndpointProfile
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixSchurReduction
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticEvenPositiveStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticSchurReductionStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseRetainedSingularSchurStructural
open YoshidaFactorTwoPhaseSingularWeightedCauchyStructural
open YoshidaFactorTwoPhaseStructuralLowData

/-!
# Concrete exact-tail selector certificate

The endpoint `P0/P2/P4` block and the pole-subtracted `P6` row are kept as
one coupled `3 x 3` Loewner inequality.  The two selector triples below are
exact rational degree-four polynomials; no floating-point value enters their
definition.
-/

/-- Exact matrix of the endpoint low complement after the `1 / 2048`
half-singular retention. -/
def factorTwoIntrinsicNineDirectP024ExactLowMatrix
    (sigma : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  symmetricMatrix3
    (factorTwoStructuralPhaseLow00 sigma -
      (1 / 2048 : ℝ) * (2 - sigma))
    (factorTwoStructuralPhaseLow02 sigma -
      (1 / 2048 : ℝ) * ((2 - sigma) / 6))
    (factorTwoIntrinsicFourP45Cross04 sigma -
      (1 / 2048 : ℝ) * ((2 - sigma) / 20))
    (factorTwoStructuralPhaseLow22 sigma -
      (1 / 2048 : ℝ) * ((172 - 11 * sigma) / 150))
    (factorTwoIntrinsicFourP45Cross24 sigma -
      (1 / 2048 : ℝ) * ((15 - 4 * sigma) / 105))
    (factorTwoIntrinsicP4PhaseDiagonal sigma -
      (1 / 2048 : ℝ) * ((8728 - 269 * sigma) / 11340))

/-- The named exact low complement is precisely the quadratic form of its
concrete symmetric matrix. -/
theorem factorTwoIntrinsicNineDirectP024ExactLowComplement_eq_matrixQuadratic
    (sigma : ℝ) (c : Fin 3 → ℝ) :
    factorTwoIntrinsicNineDirectP024ExactLowComplement sigma c =
      star c ⬝ᵥ
        (factorTwoIntrinsicNineDirectP024ExactLowMatrix sigma *ᵥ c) := by
  rw [factorTwoIntrinsicNineDirectP024ExactLowComplement,
    factorTwoEndpointChannelPhase_intrinsicEvenP024_eq_quadratic,
    half_singularWeightedEnergy_intrinsicEvenP024]
  simp [factorTwoIntrinsicNineDirectP024ExactLowMatrix,
    symmetricMatrix3, dotProduct, mulVec, Fin.sum_univ_succ,
    symmetricQuadratic]
  ring

/-- A `3 x 3` coefficient matrix synthesizes three admissible even selectors
in the span of `P0`, `P2`, and `P4`. -/
def factorTwoIntrinsicNineDirectP6ExactSelectorPolynomial
    (C : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) : ℝ[X] :=
  ∑ k : Fin 3, C i k • shiftedLegendreReal (2 * k.1)

theorem factorTwoIntrinsicNineDirectP6ExactSelectorPolynomial_natDegree_lt_six
    (C : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) :
    (factorTwoIntrinsicNineDirectP6ExactSelectorPolynomial C i).natDegree < 6 := by
  unfold factorTwoIntrinsicNineDirectP6ExactSelectorPolynomial
  have hle : (∑ k : Fin 3,
      C i k • shiftedLegendreReal (2 * k.1)).natDegree ≤ 4 :=
    Polynomial.natDegree_sum_le_of_forall_le Finset.univ _
      (fun k _hk ↦
        (Polynomial.natDegree_smul_le (C i k)
          (shiftedLegendreReal (2 * k.1))).trans (by
            rw [natDegree_shiftedLegendreReal]
            omega))
  omega

/-- Rational selector coefficients for the positive endpoint. -/
def factorTwoIntrinsicNineDirectP6ExactSelectorPlusCoefficients :
    Matrix (Fin 3) (Fin 3) ℝ :=
  !![582 / 1000, 322 / 1000, 410 / 1000;
    -2936 / 1000, 672 / 1000, 439 / 1000;
    -39110 / 1000, -17340 / 1000, 132 / 1000]

/-- Rational selector coefficients for the negative endpoint. -/
def factorTwoIntrinsicNineDirectP6ExactSelectorMinusCoefficients :
    Matrix (Fin 3) (Fin 3) ℝ :=
  !![2477 / 1000, 1279 / 1000, 218 / 1000;
    3256 / 1000, 561 / 1000, 530 / 1000;
    39180 / 1000, 17879 / 1000, 727 / 1000]

def factorTwoIntrinsicNineDirectP6ExactSelectorPlus (i : Fin 3) : ℝ[X] :=
  factorTwoIntrinsicNineDirectP6ExactSelectorPolynomial
    factorTwoIntrinsicNineDirectP6ExactSelectorPlusCoefficients i

def factorTwoIntrinsicNineDirectP6ExactSelectorMinus (i : Fin 3) : ℝ[X] :=
  factorTwoIntrinsicNineDirectP6ExactSelectorPolynomial
    factorTwoIntrinsicNineDirectP6ExactSelectorMinusCoefficients i

theorem factorTwoIntrinsicNineDirectP6ExactSelectorPlus_natDegree_lt_six
    (i : Fin 3) :
    (factorTwoIntrinsicNineDirectP6ExactSelectorPlus i).natDegree < 6 :=
  factorTwoIntrinsicNineDirectP6ExactSelectorPolynomial_natDegree_lt_six _ i

theorem factorTwoIntrinsicNineDirectP6ExactSelectorMinus_natDegree_lt_six
    (i : Fin 3) :
    (factorTwoIntrinsicNineDirectP6ExactSelectorMinus i).natDegree < 6 :=
  factorTwoIntrinsicNineDirectP6ExactSelectorPolynomial_natDegree_lt_six _ i

/-- Exact Loewner gap whose positive definiteness certifies the complete
pole-subtracted endpoint row. -/
def factorTwoIntrinsicNineDirectP6ExactSelectorLoewnerGap
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) : Matrix (Fin 3) (Fin 3) ℝ :=
  factorTwoIntrinsicNineDirectP6ExactTailComplement sigma •
      factorTwoIntrinsicNineDirectP024ExactLowMatrix sigma -
    factorTwoIntrinsicNineDirectP6WeightedMass •
      factorTwoIntrinsicNineDirectP6ExactResidualSelectorGram sigma q

/-- Inverse-weight-free upper gap for the exact direct selector rows.  Its
positive definiteness is a stronger but polynomially accessible certificate. -/
def factorTwoIntrinsicNineDirectP6ReciprocalUpperSelectorLoewnerGap
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) : Matrix (Fin 3) (Fin 3) ℝ :=
  factorTwoIntrinsicNineDirectP6ExactTailComplement sigma •
      factorTwoIntrinsicNineDirectP024ExactLowMatrix sigma -
    factorTwoIntrinsicNineDirectP6WeightedMass •
      factorTwoIntrinsicNineDirectP6ExactResidualReciprocalUpperSelectorGram
        sigma q

/-- The target `P6` mode has strictly positive retained weighted mass. -/
theorem factorTwoIntrinsicNineDirectP6WeightedMass_pos :
    0 < factorTwoIntrinsicNineDirectP6WeightedMass := by
  rw [factorTwoIntrinsicNineDirectP6WeightedMass_eq]
  have hlog := YoshidaConstantBounds.strict_log_two_fine_bounds.2
  norm_num at hlog ⊢
  nlinarith

/-- The exact gap is the reciprocal-upper gap plus the positive Loewner
correction which was removed from the selector Gram. -/
theorem factorTwoIntrinsicNineDirectP6ExactSelectorLoewnerGap_eq_upper_add
    (sigma : ℝ) (q : Fin 3 → ℝ[X]) :
    factorTwoIntrinsicNineDirectP6ExactSelectorLoewnerGap sigma q =
      factorTwoIntrinsicNineDirectP6ReciprocalUpperSelectorLoewnerGap sigma q +
        factorTwoIntrinsicNineDirectP6WeightedMass •
          (factorTwoIntrinsicNineDirectP6ExactResidualReciprocalUpperSelectorGram
              sigma q -
            factorTwoIntrinsicNineDirectP6ExactResidualSelectorGram sigma q) := by
  unfold factorTwoIntrinsicNineDirectP6ExactSelectorLoewnerGap
    factorTwoIntrinsicNineDirectP6ReciprocalUpperSelectorLoewnerGap
  module

/-- Positive definiteness of the inverse-weight-free upper gap transfers to
the exact selector gap by Loewner monotonicity. -/
theorem factorTwoIntrinsicNineDirectP6ExactSelectorLoewnerGap_posDef_of_upper
    (sigma : ℝ) (q : Fin 3 → ℝ[X])
    (hUpper :
      (factorTwoIntrinsicNineDirectP6ReciprocalUpperSelectorLoewnerGap
        sigma q).PosDef) :
    (factorTwoIntrinsicNineDirectP6ExactSelectorLoewnerGap sigma q).PosDef := by
  rw [factorTwoIntrinsicNineDirectP6ExactSelectorLoewnerGap_eq_upper_add]
  exact hUpper.add_posSemidef
    ((factorTwoIntrinsicNineDirectP6ExactResidualReciprocalUpperSelectorGram_sub_posSemidef
      sigma q).smul factorTwoIntrinsicNineDirectP6WeightedMass_pos.le)

/-- Positive definiteness of the exact-tail selector Loewner gap gives the
strict residual determinant inequality in every nonzero low direction. -/
theorem factorTwoIntrinsicNineDirectP6ExactResidualBorder_sq_lt_of_selectorLoewner
    (sigma : ℝ) (q : Fin 3 → ℝ[X])
    (hq : ∀ i, (q i).natDegree < 6)
    (hLoewner :
      (factorTwoIntrinsicNineDirectP6ExactSelectorLoewnerGap sigma q).PosDef)
    (c : Fin 3 → ℝ) (hc : c ≠ 0) :
    factorTwoIntrinsicNineDirectP6ExactResidualBorder sigma c ^ 2 <
      factorTwoIntrinsicNineDirectP024ExactLowComplement sigma c *
        factorTwoIntrinsicNineDirectP6ExactTailComplement sigma := by
  have hCauchy :=
    factorTwoIntrinsicNineDirectP6ExactResidualBorder_sq_le_selectorGram_mul_mass
      sigma q hq c
  simp only [star_trivial] at hCauchy
  have hGap := hLoewner.dotProduct_mulVec_pos hc
  simp only [factorTwoIntrinsicNineDirectP6ExactSelectorLoewnerGap,
    sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul,
    star_trivial, smul_eq_mul] at hGap
  have hLow :=
    factorTwoIntrinsicNineDirectP024ExactLowComplement_eq_matrixQuadratic
      sigma c
  simp only [star_trivial] at hLow
  rw [← hLow] at hGap
  nlinarith

private theorem factorTwoIntrinsicNineDirectP024Embed_profile
    (c : Fin 3 → ℝ) :
    factorTwoIntrinsicNineDirectP024Profile
        (factorTwoIntrinsicNineDirectP024Embed c) =
      factorTwoIntrinsicEvenP024Profile (c 0) (c 1) (c 2) := by
  funext z
  unfold factorTwoIntrinsicNineDirectP024Profile
    factorTwoIntrinsicNineDirectP024Embed
    factorTwoIntrinsicEvenP024Profile factorTwoIntrinsicSixEvenTail
  simp

private theorem factorTwoIntrinsicNineDirectP135Embed_profile
    (c : Fin 3 → ℝ) :
    factorTwoIntrinsicNineDirectP135Profile
        (factorTwoIntrinsicNineDirectP024Embed c) = 0 := by
  funext z
  unfold factorTwoIntrinsicNineDirectP135Profile
    factorTwoIntrinsicNineDirectP024Embed
    factorTwoIntrinsicSixOddTail factorTwoOddStructuralLowProfile
  simp

/-- The Loewner certificate controls the honest endpoint border, not merely
its pole-subtracted residual.  The retained singular Gram is added back by
the strict asymmetric Schur theorem. -/
theorem factorTwoIntrinsicNineDirectP6BorderFunctional_sq_lt_of_exactSelectorLoewner
    (sigma : ℝ) (hsigma : sigma = 1 ∨ sigma = -1)
    (q : Fin 3 → ℝ[X]) (hq : ∀ i, (q i).natDegree < 6)
    (hLoewner :
      (factorTwoIntrinsicNineDirectP6ExactSelectorLoewnerGap sigma q).PosDef)
    (c : Fin 3 → ℝ) (hc : c ≠ 0) :
    factorTwoIntrinsicNineDirectP6BorderFunctional sigma 0
          (factorTwoIntrinsicNineDirectP024Embed c) ^ 2 <
      factorTwoEndpointChannelPhase
          (factorTwoIntrinsicEvenP024Profile (c 0) (c 1) (c 2))
          (0 : ℝ → ℝ) sigma 0 *
        factorTwoIntrinsicNineDirectP6RetainedDiagonal sigma 0 := by
  let x := factorTwoIntrinsicNineDirectP024Embed c
  let uLow := factorTwoIntrinsicNineDirectP024Profile x
  let pE := factorTwoIntrinsicNineDirectP024Polynomial x
  have hsquare : sigma ^ 2 + (0 : ℝ) ^ 2 ≤ 1 := by
    rcases hsigma with rfl | rfl <;> norm_num
  have huEq : uLow =
      factorTwoIntrinsicEvenP024Profile (c 0) (c 1) (c 2) := by
    simpa only [uLow, x] using factorTwoIntrinsicNineDirectP024Embed_profile c
  have hvEq : factorTwoIntrinsicNineDirectP135Profile x = 0 := by
    simpa only [x] using factorTwoIntrinsicNineDirectP135Embed_profile c
  have huC : Continuous uLow := by
    simpa only [uLow] using
      continuous_factorTwoIntrinsicNineDirectP024Profile x
  have huLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) uLow := by
    have huPointwise : uLow = fun z : ℝ ↦
        x 0 + x 1 * ((3 * z ^ 2 - 1) / 2) +
          x 2 * ((35 * z ^ 4 - 30 * z ^ 2 + 3) / 8) := by
      funext z
      dsimp only [uLow]
      unfold factorTwoIntrinsicNineDirectP024Profile
        factorTwoEvenStructuralLowProfile factorTwoIntrinsicSixEvenTail
        centeredEvenP0 centeredEvenP2 factorTwoCenteredP4
      simp only [Pi.add_apply, mul_one]
    have hd : ContDiff ℝ 1 uLow := by
      rw [huPointwise]
      fun_prop
    exact hd.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  have hzeroLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      (0 : ℝ → ℝ) := by
    have hd : ContDiff ℝ 1 (fun _ : ℝ ↦ (0 : ℝ)) := contDiff_const
    exact hd.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  have hpLift : centeredPolynomialLift pE = uLow := by
    simpa only [pE, uLow] using centeredPolynomialLift_directP024Polynomial x
  have hpDegree : pE.natDegree < 6 := by
    simpa only [pE] using
      factorTwoIntrinsicNineDirectP024Polynomial_natDegree_lt_six x
  have huRaw := centeredRawLogEnergy_centeredPolynomialLift_add_tail
    pE factorTwoCenteredP6 continuous_factorTwoCenteredP6
      locallyLipschitzOn_factorTwoCenteredP6
      factorTwoCenteredP6_momentsVanishBelow hpDegree
  rw [hpLift] at huRaw
  have huOrth := intervalIntegral_centeredPolynomialLift_mul_tail_eq_zero
    pE factorTwoCenteredP6 continuous_factorTwoCenteredP6
      factorTwoCenteredP6_momentsVanishBelow hpDegree
  rw [hpLift] at huOrth
  have hvRaw : centeredRawLogEnergy ((0 : ℝ → ℝ) + 0) =
      centeredRawLogEnergy (0 : ℝ → ℝ) +
        centeredRawLogEnergy (0 : ℝ → ℝ) := by
    simp [centeredRawLogEnergy]
  have hvOrth : (∫ z : ℝ in -1..1,
      (0 : ℝ → ℝ) z * (0 : ℝ → ℝ) z) = 0 := by
    simp
  have hlowComplement :
      0 ≤ factorTwoIntrinsicNineDirectP024ExactLowComplement sigma c :=
    (factorTwoIntrinsicNineDirectP024ExactLowComplement_pos
      sigma hsigma c hc).le
  have htailComplement :
      0 ≤ factorTwoIntrinsicNineDirectP6ExactTailComplement sigma :=
    (factorTwoIntrinsicNineDirectP6ExactTailComplement_pos
      sigma (by simpa using hsquare)).le
  have hlowRetains :
      (1 / 2048 : ℝ) * ((1 / 2 : ℝ) *
          factorTwoPhaseSingularWeightedEnergy uLow 0 sigma 0) +
        factorTwoIntrinsicNineDirectP024ExactLowComplement sigma c ≤
      factorTwoEndpointChannelPhase uLow 0 sigma 0 := by
    rw [huEq]
    unfold factorTwoIntrinsicNineDirectP024ExactLowComplement
    ring_nf
    exact le_rfl
  have htailRetains :
      (1 / 128 : ℝ) * ((1 / 2 : ℝ) *
          factorTwoPhaseSingularWeightedEnergy factorTwoCenteredP6 0 sigma 0) +
        factorTwoIntrinsicNineDirectP6ExactTailComplement sigma ≤
      factorTwoIntrinsicNineDirectP6RetainedDiagonal sigma 0 := by
    unfold factorTwoIntrinsicNineDirectP6ExactTailComplement
    ring_nf
    exact le_rfl
  have hResidual :=
    factorTwoIntrinsicNineDirectP6ExactResidualBorder_sq_lt_of_selectorLoewner
      sigma q hq hLoewner c hc
  have hremaining :
      (factorTwoIntrinsicNineDirectP6BorderFunctional sigma 0 x -
          (1 / 512 : ℝ) * factorTwoPhasePotentialPoleMixed
            uLow 0 factorTwoCenteredP6 0 sigma 0) ^ 2 <
        factorTwoIntrinsicNineDirectP024ExactLowComplement sigma c *
          factorTwoIntrinsicNineDirectP6ExactTailComplement sigma := by
    have heq :
        factorTwoIntrinsicNineDirectP6ExactResidualBorder sigma c =
          factorTwoIntrinsicNineDirectP6BorderFunctional sigma 0 x -
            (1 / 512 : ℝ) * factorTwoPhasePotentialPoleMixed
              uLow 0 factorTwoCenteredP6 0 sigma 0 := by
      unfold factorTwoIntrinsicNineDirectP6ExactResidualBorder
      dsimp only [x, uLow]
      rw [factorTwoIntrinsicNineDirectP135Embed_profile]
    rw [← heq]
    exact hResidual
  have hMixed := mixed_sq_lt_of_asymmetrically_retained_singular_targets
    uLow (0 : ℝ → ℝ) factorTwoCenteredP6 (0 : ℝ → ℝ)
    huC continuous_zero continuous_factorTwoCenteredP6 continuous_zero
    huLocal hzeroLocal locallyLipschitzOn_factorTwoCenteredP6 hzeroLocal
    sigma 0 (1 / 2048 : ℝ) (1 / 128 : ℝ) (1 / 512 : ℝ)
    (factorTwoEndpointChannelPhase uLow 0 sigma 0)
    (factorTwoIntrinsicNineDirectP6RetainedDiagonal sigma 0)
    (factorTwoIntrinsicNineDirectP024ExactLowComplement sigma c)
    (factorTwoIntrinsicNineDirectP6ExactTailComplement sigma)
    (factorTwoIntrinsicNineDirectP6BorderFunctional sigma 0 x)
    hsquare (by norm_num) (by norm_num) (by norm_num)
    huRaw hvRaw huOrth hvOrth hlowComplement htailComplement
    hlowRetains htailRetains hremaining
  simpa only [x, huEq] using hMixed

/-- The positive-endpoint certificate is now one concrete `3 x 3`
positive-definiteness statement. -/
def FactorTwoIntrinsicNineDirectP6ExactSelectorPlusCertificate : Prop :=
  (factorTwoIntrinsicNineDirectP6ExactSelectorLoewnerGap 1
    factorTwoIntrinsicNineDirectP6ExactSelectorPlus).PosDef

/-- The negative-endpoint certificate is now one concrete `3 x 3`
positive-definiteness statement. -/
def FactorTwoIntrinsicNineDirectP6ExactSelectorMinusCertificate : Prop :=
  (factorTwoIntrinsicNineDirectP6ExactSelectorLoewnerGap (-1)
    factorTwoIntrinsicNineDirectP6ExactSelectorMinus).PosDef

/-- Inverse-weight-free positive-endpoint certificate. -/
def FactorTwoIntrinsicNineDirectP6ReciprocalUpperSelectorPlusCertificate : Prop :=
  (factorTwoIntrinsicNineDirectP6ReciprocalUpperSelectorLoewnerGap 1
    factorTwoIntrinsicNineDirectP6ExactSelectorPlus).PosDef

/-- Inverse-weight-free negative-endpoint certificate. -/
def FactorTwoIntrinsicNineDirectP6ReciprocalUpperSelectorMinusCertificate : Prop :=
  (factorTwoIntrinsicNineDirectP6ReciprocalUpperSelectorLoewnerGap (-1)
    factorTwoIntrinsicNineDirectP6ExactSelectorMinus).PosDef

theorem factorTwoIntrinsicNineDirectP6ExactSelectorPlusCertificate_of_reciprocalUpper
    (h : FactorTwoIntrinsicNineDirectP6ReciprocalUpperSelectorPlusCertificate) :
    FactorTwoIntrinsicNineDirectP6ExactSelectorPlusCertificate := by
  exact factorTwoIntrinsicNineDirectP6ExactSelectorLoewnerGap_posDef_of_upper
    1 factorTwoIntrinsicNineDirectP6ExactSelectorPlus h

theorem factorTwoIntrinsicNineDirectP6ExactSelectorMinusCertificate_of_reciprocalUpper
    (h : FactorTwoIntrinsicNineDirectP6ReciprocalUpperSelectorMinusCertificate) :
    FactorTwoIntrinsicNineDirectP6ExactSelectorMinusCertificate := by
  exact factorTwoIntrinsicNineDirectP6ExactSelectorLoewnerGap_posDef_of_upper
    (-1) factorTwoIntrinsicNineDirectP6ExactSelectorMinus h

/-- The positive-endpoint selector certificate closes the corresponding
inverse-free adjugate gap. -/
theorem factorTwoIntrinsicNineDirectP6PlusAdjugateGap_pos_of_exactSelectorCertificate
    (h : FactorTwoIntrinsicNineDirectP6ExactSelectorPlusCertificate) :
    0 < factorTwoIntrinsicNineDirectP6PlusAdjugateGap := by
  rcases factorTwoIntrinsicSixUnbalancedEPlus_positive with
    ⟨h00, hminor, hdet⟩
  have hd : 0 < factorTwoIntrinsicNineDirectP6RetainedDiagonal 1 0 :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 160)
      (one_div_one_hundred_sixty_le_P6RetainedDiagonal 1 0 (by norm_num))
  have hadj :=
    adjugateQuadratic_lt_symmetricDeterminant_mul_of_border_lt
      factorTwoIntrinsicSixUnbalancedEPlus00
      factorTwoIntrinsicSixUnbalancedEPlus02
      factorTwoIntrinsicSixUnbalancedEPlus04
      factorTwoIntrinsicSixUnbalancedEPlus22
      factorTwoIntrinsicSixUnbalancedEPlus24
      factorTwoIntrinsicSixUnbalancedEPlus44
      factorTwoIntrinsicNineEPlus06
      factorTwoIntrinsicNineEPlus26
      factorTwoIntrinsicNineEPlus46
      (factorTwoIntrinsicNineDirectP6RetainedDiagonal 1 0)
      h00 hminor hdet hd (by
        intro x0 x1 x2 hx
        let c : Fin 3 → ℝ := ![x0, x1, x2]
        have hc : c ≠ 0 := by
          intro hzero
          rcases hx with hx0 | hx1 | hx2
          · apply hx0
            have hz := congrFun hzero 0
            simpa only [c] using hz
          · apply hx1
            have hz := congrFun hzero 1
            simpa only [c] using hz
          · apply hx2
            have hz := congrFun hzero 2
            simpa only [c] using hz
        have hb :=
          factorTwoIntrinsicNineDirectP6BorderFunctional_sq_lt_of_exactSelectorLoewner
            1 (Or.inl rfl)
            factorTwoIntrinsicNineDirectP6ExactSelectorPlus
            factorTwoIntrinsicNineDirectP6ExactSelectorPlus_natDegree_lt_six
            h c hc
        rw [factorTwoIntrinsicNineDirectP6BorderFunctional_plus_eq,
          factorTwoEndpointChannelPhase_intrinsicEvenP024_eq_quadratic] at hb
        simpa [c, factorTwoIntrinsicNineDirectP024Embed,
          factorTwoIntrinsicSixUnbalancedEPlus00,
          factorTwoIntrinsicSixUnbalancedEPlus02,
          factorTwoIntrinsicSixUnbalancedEPlus04,
          factorTwoIntrinsicSixUnbalancedEPlus22,
          factorTwoIntrinsicSixUnbalancedEPlus24,
          factorTwoIntrinsicSixUnbalancedEPlus44] using hb)
  unfold factorTwoIntrinsicNineDirectP6PlusAdjugateGap
  exact sub_pos.mpr (by
    simpa only [factorTwoIntrinsicSixUnbalancedEPlusDet] using hadj)

/-- The negative-endpoint selector certificate closes the corresponding
inverse-free adjugate gap. -/
theorem factorTwoIntrinsicNineDirectP6MinusAdjugateGap_pos_of_exactSelectorCertificate
    (h : FactorTwoIntrinsicNineDirectP6ExactSelectorMinusCertificate) :
    0 < factorTwoIntrinsicNineDirectP6MinusAdjugateGap := by
  rcases factorTwoIntrinsicSixUnbalancedEMinus_positive with
    ⟨h00, hminor, hdet⟩
  have hd : 0 < factorTwoIntrinsicNineDirectP6RetainedDiagonal (-1) 0 :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 160)
      (one_div_one_hundred_sixty_le_P6RetainedDiagonal (-1) 0 (by norm_num))
  have hadj :=
    adjugateQuadratic_lt_symmetricDeterminant_mul_of_border_lt
      factorTwoIntrinsicSixUnbalancedEMinus00
      factorTwoIntrinsicSixUnbalancedEMinus02
      factorTwoIntrinsicSixUnbalancedEMinus04
      factorTwoIntrinsicSixUnbalancedEMinus22
      factorTwoIntrinsicSixUnbalancedEMinus24
      factorTwoIntrinsicSixUnbalancedEMinus44
      factorTwoIntrinsicNineEMinus06
      factorTwoIntrinsicNineEMinus26
      factorTwoIntrinsicNineEMinus46
      (factorTwoIntrinsicNineDirectP6RetainedDiagonal (-1) 0)
      h00 hminor hdet hd (by
        intro x0 x1 x2 hx
        let c : Fin 3 → ℝ := ![x0, x1, x2]
        have hc : c ≠ 0 := by
          intro hzero
          rcases hx with hx0 | hx1 | hx2
          · apply hx0
            have hz := congrFun hzero 0
            simpa only [c] using hz
          · apply hx1
            have hz := congrFun hzero 1
            simpa only [c] using hz
          · apply hx2
            have hz := congrFun hzero 2
            simpa only [c] using hz
        have hb :=
          factorTwoIntrinsicNineDirectP6BorderFunctional_sq_lt_of_exactSelectorLoewner
            (-1) (Or.inr rfl)
            factorTwoIntrinsicNineDirectP6ExactSelectorMinus
            factorTwoIntrinsicNineDirectP6ExactSelectorMinus_natDegree_lt_six
            h c hc
        rw [factorTwoIntrinsicNineDirectP6BorderFunctional_minus_eq,
          factorTwoEndpointChannelPhase_intrinsicEvenP024_eq_quadratic] at hb
        simpa [c, factorTwoIntrinsicNineDirectP024Embed,
          factorTwoIntrinsicSixUnbalancedEMinus00,
          factorTwoIntrinsicSixUnbalancedEMinus02,
          factorTwoIntrinsicSixUnbalancedEMinus04,
          factorTwoIntrinsicSixUnbalancedEMinus22,
          factorTwoIntrinsicSixUnbalancedEMinus24,
          factorTwoIntrinsicSixUnbalancedEMinus44] using hb)
  unfold factorTwoIntrinsicNineDirectP6MinusAdjugateGap
  exact sub_pos.mpr (by
    simpa only [factorTwoIntrinsicSixUnbalancedEMinusDet] using hadj)

/-- The two exact selector certificates are sufficient for both endpoint
adjugate gaps. -/
theorem factorTwoIntrinsicNineDirectP6AdjugateGaps_pos_of_exactSelectorCertificates
    (hPlus : FactorTwoIntrinsicNineDirectP6ExactSelectorPlusCertificate)
    (hMinus : FactorTwoIntrinsicNineDirectP6ExactSelectorMinusCertificate) :
    0 < factorTwoIntrinsicNineDirectP6PlusAdjugateGap ∧
      0 < factorTwoIntrinsicNineDirectP6MinusAdjugateGap :=
  ⟨factorTwoIntrinsicNineDirectP6PlusAdjugateGap_pos_of_exactSelectorCertificate
      hPlus,
    factorTwoIntrinsicNineDirectP6MinusAdjugateGap_pos_of_exactSelectorCertificate
      hMinus⟩

/-- Consequently the same two concrete certificates close the two endpoint
coefficients in the degree-seven determinant polynomial. -/
theorem factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven_endpoint_coefficients_pos_of_exactSelectorCertificates
    (hPlus : FactorTwoIntrinsicNineDirectP6ExactSelectorPlusCertificate)
    (hMinus : FactorTwoIntrinsicNineDirectP6ExactSelectorMinusCertificate) :
    0 < factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven.coeff 0 ∧
      0 < factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven.coeff 7 :=
  factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven_endpoint_coefficients_pos_of_adjugateGaps
    (factorTwoIntrinsicNineDirectP6PlusAdjugateGap_pos_of_exactSelectorCertificate
      hPlus)
    (factorTwoIntrinsicNineDirectP6MinusAdjugateGap_pos_of_exactSelectorCertificate
      hMinus)

/-- The two inverse-weight-free endpoint certificates therefore close both
endpoint coefficients of the degree-seven prefix determinant. -/
theorem factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven_endpoint_coefficients_pos_of_reciprocalUpperCertificates
    (hPlus :
      FactorTwoIntrinsicNineDirectP6ReciprocalUpperSelectorPlusCertificate)
    (hMinus :
      FactorTwoIntrinsicNineDirectP6ReciprocalUpperSelectorMinusCertificate) :
    0 < factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven.coeff 0 ∧
      0 < factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven.coeff 7 :=
  factorTwoIntrinsicNineDirectPrefixDeterminantPolynomialSeven_endpoint_coefficients_pos_of_exactSelectorCertificates
    (factorTwoIntrinsicNineDirectP6ExactSelectorPlusCertificate_of_reciprocalUpper
      hPlus)
    (factorTwoIntrinsicNineDirectP6ExactSelectorMinusCertificate_of_reciprocalUpper
      hMinus)

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectP6ExactTailSelectorCertificateStructural
