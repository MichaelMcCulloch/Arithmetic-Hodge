import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedConstrainedWeightedDualStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenCleanSharp
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep01Slope23FifthsStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4EndpointProfile
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4CleanCrossStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourC2Structural
import ArithmeticHodge.Analysis.YoshidaEndpointEvenFullPolarization

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedSelectorObstructionStructural

open ShiftedLegendreLogEnergyOrthogonalProjection
open ShiftedLegendreBasis
open ShiftedLegendreOrthogonality
open UnitIntervalLogEnergyAffine
open YoshidaEndpointEvenExactLowGramPositive
open YoshidaEndpointEvenFullPolarization
open YoshidaEndpointEvenLowProfile
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointPotentialBound
open YoshidaFactorTwoEndpointChannelRadius
open YoshidaFactorTwoPhaseEnvelope
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicElevenCompleteRepresentersStructural
open YoshidaFactorTwoPhaseIntrinsicElevenConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedRepresentersStructural
open YoshidaFactorTwoPhaseIntrinsicEightUnbalancedStaticDiskStructural
open YoshidaFactorTwoPhaseIntrinsicEvenCleanSharp
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLowControlStep01Slope23FifthsStructural
open YoshidaFactorTwoPhaseIntrinsicNineFullMixedDecompositionStructural
open YoshidaFactorTwoPhaseIntrinsicNineUnbalancedStaticDiskStructural
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseIntrinsicRetainedSingularGapStructural
open YoshidaFactorTwoPhaseIntrinsicSixSchurReduction
open YoshidaFactorTwoPhaseIntrinsicSixP4CleanCrossStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4EndpointProfile
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixP4WeightedMass
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourC2Structural
open YoshidaFactorTwoPhaseSingularWeightedCauchyStructural
open YoshidaFactorTwoPhaseLowSchur
open YoshidaRegularKernelSchur

noncomputable section

open ThreeByThreeRankOneSchur
open YoshidaEndpointPotentialIntegrable
open YoshidaFactorTwoPhaseLegendreFourFiveStructural

/-!
# Obstruction to the retained cutoff-eleven selector target

The retained `1 / 128` singular charge is too large on a concrete vector in
the low `{P₀,P₂}` plane.  Its exact low complement is negative, whereas every
constrained selector dual is nonnegative.  Thus no choice of polynomial
selectors can satisfy the finite hypothesis of the retained Schur handoff
for this vector.
-/

/-- The obstructing cutoff-eleven polynomial, equal to `-8 L₀ + 9 L₂`. -/
def factorTwoIntrinsicElevenRetainedBadEvenPolynomial : ℝ[X] :=
  factorTwoIntrinsicNineEvenPolynomial (-8) 9 0 0 0

theorem factorTwoIntrinsicElevenRetainedBadEvenPolynomial_natDegree_lt :
    factorTwoIntrinsicElevenRetainedBadEvenPolynomial.natDegree < 11 := by
  unfold factorTwoIntrinsicElevenRetainedBadEvenPolynomial
    factorTwoIntrinsicNineEvenPolynomial
  have hdeg :
      (((-8 : ℝ) • shiftedLegendreReal 0 + (9 : ℝ) • shiftedLegendreReal 2 +
        (0 : ℝ) • shiftedLegendreReal 4 + (0 : ℝ) • shiftedLegendreReal 6 +
        (0 : ℝ) • shiftedLegendreReal 8)).natDegree ≤ 8 := by
    compute_degree
  omega

theorem centeredPolynomialLift_retainedBadEvenPolynomial :
    centeredPolynomialLift factorTwoIntrinsicElevenRetainedBadEvenPolynomial =
      yoshidaEndpointEvenLowProfile (-8) 9 := by
  unfold factorTwoIntrinsicElevenRetainedBadEvenPolynomial
  rw [centeredPolynomialLift_intrinsicNineEvenPolynomial]
  funext x
  unfold factorTwoIntrinsicNineEvenProfile factorTwoIntrinsicEightEvenProfile
    factorTwoIntrinsicSixEvenTail factorTwoEvenStructuralLowProfile
    yoshidaEndpointEvenLowProfile centeredEvenP0
  simp only [Pi.add_apply]
  ring

/-- The singular charge on the obstructing profile is exact.  Isolating it
lets us compare different retained fractions without recomputing the profile
integrals. -/
theorem factorTwoIntrinsicElevenRetainedBadSingularCharge_eq :
    (1 / 128 : ℝ) * factorTwoPhaseSingularWeightedEnergy
        (yoshidaEndpointEvenLowProfile (-8) 9) 0 0 0 = 2161 / 800 := by
  let e : ℝ → ℝ := yoshidaEndpointEvenLowProfile (-8) 9
  have hec : Continuous e := by
    simpa only [e] using continuous_yoshidaEndpointEvenLowProfile (-8) 9
  have helocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) e := by
    have hd : ContDiff ℝ 1 e := by
      dsimp only [e]
      unfold yoshidaEndpointEvenLowProfile centeredEvenP2
      fun_prop
    exact hd.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  have h0c : Continuous (0 : ℝ → ℝ) := continuous_zero
  have h0local : LocallyLipschitzOn (Icc (-1 : ℝ) 1) (0 : ℝ → ℝ) := by
    have hd : ContDiff ℝ 1 (fun _ : ℝ ↦ (0 : ℝ)) := contDiff_const
    change LocallyLipschitzOn (Icc (-1 : ℝ) 1) (fun _ : ℝ ↦ (0 : ℝ))
    exact hd.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  have hraw0 : centeredRawLogEnergy (0 : ℝ → ℝ) = 0 := by
    unfold centeredRawLogEnergy
    simp
  have hs0 := half_singularWeightedEnergy_eq_protected_add_logMass
    e (0 : ℝ → ℝ) hec h0c helocal h0local 0 0
  unfold factorTwoIntrinsicProtectedBlock factorTwoIntrinsicEnergy
    factorTwoIntrinsicPotentialEnergy at hs0
  simp [factorTwoCenteredPhaseCorrelation, hraw0] at hs0
  dsimp only [e] at hs0
  rw [centeredRawLogEnergy_yoshidaEndpointEvenLowProfile,
    integral_endpointPotential_mul_yoshidaEndpointEvenLowProfile_sq,
    integral_yoshidaEndpointEvenLowProfile_sq] at hs0
  norm_num at hs0 ⊢
  ring_nf at hs0
  nlinarith

/-- The exact low complement required by the retained selector theorem is
strictly negative on `-8 P₀ + 9 P₂`. -/
theorem factorTwoIntrinsicElevenRetainedBadLowComplement_neg :
    factorTwoEndpointChannelPhase
          (yoshidaEndpointEvenLowProfile (-8) 9) 0 0 0 -
        (1 / 128 : ℝ) * factorTwoPhaseSingularWeightedEnergy
          (yoshidaEndpointEvenLowProfile (-8) 9) 0 0 0 < 0 := by
  let e : ℝ → ℝ := yoshidaEndpointEvenLowProfile (-8) 9
  have heProfile : e = fun x : ℝ ↦
      (-8 : ℝ) * centeredEvenP0 x + 9 * centeredEvenP2 x := by
    funext x
    simp [e, yoshidaEndpointEvenLowProfile, centeredEvenP0]
  have hclean : yoshidaEndpointOddCleanQuadratic e < (1963 / 2000 : ℝ) := by
    rw [heProfile, yoshidaEndpointEvenLowGram_quadratic_eq_clean]
    have h00 := intrinsicEven_cleanGram00_lt_step01
    have h02 := intrinsicEven_cleanGram02_bounds.1
    have h22 := intrinsicEven_cleanGram22_lt_step01
    norm_num at h00 h02 h22 ⊢
    nlinarith
  have hzero : yoshidaEndpointOddCleanQuadratic (0 : ℝ → ℝ) = 0 := by
    unfold yoshidaEndpointOddCleanQuadratic centeredRawLogEnergy
      yoshidaEndpointRegularQuadratic yoshidaEndpointHyperbolicQuadratic
    simp
  have hphase : factorTwoEndpointChannelPhase e 0 0 0 =
      yoshidaEndpointOddCleanQuadratic e := by
    unfold factorTwoEndpointChannelPhase factorTwoEndpointChannelCleanSum
    rw [hzero]
    ring
  have hsing :
      (1 / 128 : ℝ) * factorTwoPhaseSingularWeightedEnergy e 0 0 0 =
        2161 / 800 := by
    simpa only [e] using factorTwoIntrinsicElevenRetainedBadSingularCharge_eq
  change factorTwoEndpointChannelPhase e 0 0 0 -
      (1 / 128 : ℝ) * factorTwoPhaseSingularWeightedEnergy e 0 0 0 < 0
  rw [hphase, hsing]
  linarith

/-- Retaining only one quarter of the failed singular charge repairs its
concrete obstruction: the same `-8 P₀ + 9 P₂` profile has strictly positive
low complement at retained coefficient `1 / 256` of the half-energy. -/
theorem factorTwoIntrinsicElevenOneDiv256BadLowComplement_pos :
    0 < factorTwoEndpointChannelPhase
          (yoshidaEndpointEvenLowProfile (-8) 9) 0 0 0 -
        (1 / 256 : ℝ) * (1 / 2 : ℝ) *
          factorTwoPhaseSingularWeightedEnergy
            (yoshidaEndpointEvenLowProfile (-8) 9) 0 0 0 := by
  let e : ℝ → ℝ := yoshidaEndpointEvenLowProfile (-8) 9
  have heProfile : e = fun x : ℝ ↦
      (-8 : ℝ) * centeredEvenP0 x + 9 * centeredEvenP2 x := by
    funext x
    simp [e, yoshidaEndpointEvenLowProfile, centeredEvenP0]
  have hclean : (9317 / 10000 : ℝ) < yoshidaEndpointOddCleanQuadratic e := by
    rw [heProfile, yoshidaEndpointEvenLowGram_quadratic_eq_clean]
    have h00 := intrinsicEven_cleanGram00_gt
    have h02 := intrinsicEven_cleanGram02_bounds.2
    have h22 := intrinsicEven_cleanGram22_gt
    norm_num at h00 h02 h22 ⊢
    nlinarith
  have hzero : yoshidaEndpointOddCleanQuadratic (0 : ℝ → ℝ) = 0 := by
    unfold yoshidaEndpointOddCleanQuadratic centeredRawLogEnergy
      yoshidaEndpointRegularQuadratic yoshidaEndpointHyperbolicQuadratic
    simp
  have hphase : factorTwoEndpointChannelPhase e 0 0 0 =
      yoshidaEndpointOddCleanQuadratic e := by
    unfold factorTwoEndpointChannelPhase factorTwoEndpointChannelCleanSum
    rw [hzero]
    ring
  have hsing :
      (1 / 256 : ℝ) * (1 / 2 : ℝ) *
          factorTwoPhaseSingularWeightedEnergy e 0 0 0 = 2161 / 3200 := by
    have h := factorTwoIntrinsicElevenRetainedBadSingularCharge_eq
    change (1 / 128 : ℝ) * factorTwoPhaseSingularWeightedEnergy e 0 0 0 =
      2161 / 800 at h
    norm_num at h ⊢
    linarith
  change 0 < factorTwoEndpointChannelPhase e 0 0 0 -
      (1 / 256 : ℝ) * (1 / 2 : ℝ) *
        factorTwoPhaseSingularWeightedEnergy e 0 0 0
  rw [hphase, hsing]
  linarith

/-! ## The stronger three-mode obstruction -/

/-- The three-mode profile which still obstructs a `1 / 256` low retained
fraction after the original two-mode witness has been repaired. -/
def factorTwoIntrinsicElevenRetainedStrongerBadEvenProfile : ℝ → ℝ :=
  factorTwoIntrinsicEvenP024Profile (-16) 18 (-3)

/-- Structural clean-entry bounds give a small phase-zero value on the
stronger `P₀/P₂/P₄` witness. -/
theorem factorTwoIntrinsicElevenRetainedStrongerBadPhase_lt :
    factorTwoEndpointChannelPhase
        factorTwoIntrinsicElevenRetainedStrongerBadEvenProfile 0 0 0 <
      (1639037 / 1750000 : ℝ) := by
  rw [show factorTwoIntrinsicElevenRetainedStrongerBadEvenProfile =
      factorTwoIntrinsicEvenP024Profile (-16) 18 (-3) by rfl,
    factorTwoEndpointChannelPhase_intrinsicEvenP024_eq_quadratic]
  have h00 := intrinsicEven_cleanGram00_lt_step01
  have h02 := intrinsicEven_cleanGram02_bounds.1
  have h22 := intrinsicEven_cleanGram22_lt_step01
  have h04 := factorTwoIntrinsicP4CleanCross04_sub_one_tenth_abs_lt
  have h24 := factorTwoIntrinsicP4CleanCross24_sub_one_seventh_abs_lt
  have h44 := factorTwoP4_clean_diagonal_lt_three_hundred_fifteen_thousandths
  rw [abs_lt] at h04 h24
  unfold symmetricQuadratic factorTwoStructuralPhaseLow00
    factorTwoStructuralPhaseLow02 factorTwoStructuralPhaseLow22
    factorTwoIntrinsicFourP45Cross04 factorTwoIntrinsicFourP45Cross24
    factorTwoIntrinsicP4PhaseDiagonal
  norm_num at h00 h02 h22 h04 h24 h44 ⊢
  nlinarith

/-- Even after discarding the nonnegative raw-log part, the half singular
energy on the stronger witness has the displayed large rational lower bound.
The proof uses only exact polynomial masses and endpoint-potential pairings. -/
theorem factorTwoIntrinsicElevenRetainedStrongerBadHalfSingular_ge :
    (1556263 / 3150 : ℝ) ≤ (1 / 2 : ℝ) *
      factorTwoPhaseSingularWeightedEnergy
        factorTwoIntrinsicElevenRetainedStrongerBadEvenProfile 0 0 0 := by
  let p : ℝ → ℝ := yoshidaEndpointEvenLowProfile (-16) 18
  let r : ℝ → ℝ := fun x ↦ (-3 : ℝ) * factorTwoCenteredP4 x
  let e : ℝ → ℝ := fun x ↦ p x + r x
  have heProfile : e = factorTwoIntrinsicElevenRetainedStrongerBadEvenProfile := by
    funext x
    unfold e p r factorTwoIntrinsicElevenRetainedStrongerBadEvenProfile
      factorTwoIntrinsicEvenP024Profile factorTwoEvenStructuralLowProfile
      factorTwoIntrinsicSixEvenTail yoshidaEndpointEvenLowProfile centeredEvenP0
    simp only [Pi.add_apply]
    ring
  have hp : Continuous p := by
    simpa only [p] using continuous_yoshidaEndpointEvenLowProfile (-16) 18
  have hr : Continuous r := by
    dsimp only [r]
    exact continuous_const.mul continuous_factorTwoCenteredP4
  have hec : Continuous e := hp.add hr
  have helocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) e := by
    have hd : ContDiff ℝ 1 e := by
      dsimp only [e, p, r]
      unfold yoshidaEndpointEvenLowProfile centeredEvenP2 factorTwoCenteredP4
      fun_prop
    exact hd.locallyLipschitz.locallyLipschitzOn
  have h0c : Continuous (0 : ℝ → ℝ) := continuous_zero
  have h0local : LocallyLipschitzOn (Icc (-1 : ℝ) 1) (0 : ℝ → ℝ) := by
    have hd : ContDiff ℝ 1 (fun _ : ℝ ↦ (0 : ℝ)) := contDiff_const
    change LocallyLipschitzOn (Icc (-1 : ℝ) 1) (fun _ : ℝ ↦ (0 : ℝ))
    exact hd.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  have hpMass : (∫ x : ℝ in -1..1, p x ^ 2) = (3208 / 5 : ℝ) := by
    dsimp only [p]
    rw [integral_yoshidaEndpointEvenLowProfile_sq]
    norm_num
  have hpPot : (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * p x ^ 2) =
        (12428 / 25 : ℝ) - (3208 / 5 : ℝ) * Real.log 2 := by
    dsimp only [p]
    rw [integral_endpointPotential_mul_yoshidaEndpointEvenLowProfile_sq]
    ring
  have hrMass : (∫ x : ℝ in -1..1, r x ^ 2) = (2 : ℝ) := by
    rw [show (fun x : ℝ ↦ r x ^ 2) =
        fun x ↦ (9 : ℝ) * factorTwoCenteredP4 x ^ 2 by
      funext x
      dsimp only [r]
      ring,
      intervalIntegral.integral_const_mul,
      integral_factorTwoCenteredP4_sq]
    norm_num
  have hrPot : (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * r x ^ 2) =
        (1739 / 630 : ℝ) - 2 * Real.log 2 := by
    rw [show (fun x : ℝ ↦ yoshidaEndpointPotential x * r x ^ 2) =
        fun x ↦ (9 : ℝ) *
          (yoshidaEndpointPotential x * factorTwoCenteredP4 x ^ 2) by
      funext x
      dsimp only [r]
      ring,
      intervalIntegral.integral_const_mul,
      integral_endpointPotential_mul_factorTwoCenteredP4_sq]
    ring
  have hcrossM : (∫ x : ℝ in -1..1, p x * r x) = 0 := by
    have hP4 : IntervalIntegrable factorTwoCenteredP4 volume (-1) 1 :=
      continuous_factorTwoCenteredP4.intervalIntegrable (-1) 1
    have hP4P2 : IntervalIntegrable
        (fun x : ℝ ↦ factorTwoCenteredP4 x * centeredEvenP2 x)
        volume (-1) 1 :=
      (continuous_factorTwoCenteredP4.mul (by
        unfold centeredEvenP2
        fun_prop)).intervalIntegrable (-1) 1
    rw [show (fun x : ℝ ↦ p x * r x) =
        fun x ↦ (48 : ℝ) * factorTwoCenteredP4 x -
          54 * (factorTwoCenteredP4 x * centeredEvenP2 x) by
      funext x
      dsimp only [p, r]
      unfold yoshidaEndpointEvenLowProfile
      ring,
      intervalIntegral.integral_sub (hP4.const_mul 48) (hP4P2.const_mul 54),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      integral_factorTwoCenteredP4,
      integral_factorTwoCenteredP4_mul_centeredEvenP2]
    ring
  have hcrossV : (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * p x * r x) = (-102 / 35 : ℝ) := by
    have hpotMul (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
        IntervalIntegrable
          (fun x : ℝ ↦ yoshidaEndpointPotential x * u x * v x)
          volume (-1) 1 := by
      have huv := intervalIntegrable_endpointPotential_mul_sq (u + v)
        (hu.add hv)
      have huu := intervalIntegrable_endpointPotential_mul_sq u hu
      have hvv := intervalIntegrable_endpointPotential_mul_sq v hv
      apply (((huv.sub huu).sub hvv).const_mul (1 / 2 : ℝ)).congr
      intro x _hx
      simp only [Pi.add_apply]
      ring
    have h04 : IntervalIntegrable
        (fun x : ℝ ↦ yoshidaEndpointPotential x * centeredEvenP0 x *
          factorTwoCenteredP4 x) volume (-1) 1 :=
      hpotMul centeredEvenP0 factorTwoCenteredP4
        (by unfold centeredEvenP0; fun_prop) continuous_factorTwoCenteredP4
    have h24 : IntervalIntegrable
        (fun x : ℝ ↦ yoshidaEndpointPotential x * centeredEvenP2 x *
          factorTwoCenteredP4 x) volume (-1) 1 :=
      hpotMul centeredEvenP2 factorTwoCenteredP4
        (by unfold centeredEvenP2; fun_prop) continuous_factorTwoCenteredP4
    rw [show (fun x : ℝ ↦ yoshidaEndpointPotential x * p x * r x) =
        fun x ↦ (48 : ℝ) *
            (yoshidaEndpointPotential x * centeredEvenP0 x *
              factorTwoCenteredP4 x) -
          54 * (yoshidaEndpointPotential x * centeredEvenP2 x *
            factorTwoCenteredP4 x) by
      funext x
      dsimp only [p, r]
      unfold yoshidaEndpointEvenLowProfile centeredEvenP0
      ring,
      intervalIntegral.integral_sub (h04.const_mul 48) (h24.const_mul 54),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      integral_endpointPotential_mul_centeredEvenP0_mul_P4,
      integral_endpointPotential_mul_centeredEvenP2_mul_P4]
    norm_num
  have hMsplit := integral_add_sq p r hp hr
  have hVsplit := integral_endpointPotential_add_sq p r hp hr
  have hmass : (∫ x : ℝ in -1..1, e x ^ 2) = (3218 / 5 : ℝ) := by
    dsimp only [e] at *
    rw [hMsplit, hpMass, hcrossM, hrMass]
    norm_num
  have hpot : (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * e x ^ 2) =
        (1556263 / 3150 : ℝ) - (3218 / 5 : ℝ) * Real.log 2 := by
    dsimp only [e] at *
    rw [hVsplit, hpPot, hcrossV, hrPot]
    ring
  have hVlog :
      (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * e x ^ 2) +
          Real.log 2 * (∫ x : ℝ in -1..1, e x ^ 2) =
        (1556263 / 3150 : ℝ) := by
    rw [hpot, hmass]
    ring
  have hrawNonneg : 0 ≤ centeredRawLogEnergy e := by
    unfold centeredRawLogEnergy
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x _hx
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro y _hy
    exact div_nonneg (sq_nonneg (e x - e y)) (abs_nonneg (x - y))
  have hraw0 : centeredRawLogEnergy (0 : ℝ → ℝ) = 0 := by
    unfold centeredRawLogEnergy
    simp
  have hs0 := half_singularWeightedEnergy_eq_protected_add_logMass
    e (0 : ℝ → ℝ) hec h0c helocal h0local 0 0
  unfold factorTwoIntrinsicProtectedBlock factorTwoIntrinsicEnergy
    factorTwoIntrinsicPotentialEnergy at hs0
  simp [factorTwoCenteredPhaseCorrelation, hraw0] at hs0
  rw [← heProfile]
  nlinarith

/-- The symmetric `1 / 256` retained split is still impossible on the full
cutoff-eleven low space: the three-mode witness has negative low complement. -/
theorem factorTwoIntrinsicElevenOneDiv256StrongerBadLowComplement_neg :
    factorTwoEndpointChannelPhase
          factorTwoIntrinsicElevenRetainedStrongerBadEvenProfile 0 0 0 -
        (1 / 256 : ℝ) * ((1 / 2 : ℝ) *
          factorTwoPhaseSingularWeightedEnergy
            factorTwoIntrinsicElevenRetainedStrongerBadEvenProfile 0 0 0) < 0 := by
  have hphase := factorTwoIntrinsicElevenRetainedStrongerBadPhase_lt
  have hsing := factorTwoIntrinsicElevenRetainedStrongerBadHalfSingular_ge
  norm_num at hphase hsing ⊢
  nlinarith

/-- No pair of polynomial selectors can meet the retained finite-selector
hypothesis on the obstructing low vector.  This is independent of selector
degree and weighted-dual regularity. -/
theorem factorTwoIntrinsicElevenRetainedBadSelector_impossible
    (qE qO : ℝ[X]) :
    ¬ factorTwoIntrinsicElevenRetainedConstrainedSelectorDual
          (factorTwoIntrinsicElevenRetainedEvenMixedRepresenter
            factorTwoIntrinsicElevenRetainedBadEvenPolynomial 0 0 0)
          (factorTwoIntrinsicElevenRetainedOddMixedRepresenter
            factorTwoIntrinsicElevenRetainedBadEvenPolynomial 0 0 0)
          qE qO ≤
        factorTwoEndpointChannelPhase
            (centeredPolynomialLift
              factorTwoIntrinsicElevenRetainedBadEvenPolynomial)
            (centeredPolynomialLift (0 : ℝ[X])) 0 0 -
          (1 / 128 : ℝ) * factorTwoPhaseSingularWeightedEnergy
            (centeredPolynomialLift
              factorTwoIntrinsicElevenRetainedBadEvenPolynomial)
            (centeredPolynomialLift (0 : ℝ[X])) 0 0 := by
  intro hselector
  have hnonneg :=
    factorTwoIntrinsicElevenRetainedConstrainedSelectorDual_nonneg
      (factorTwoIntrinsicElevenRetainedEvenMixedRepresenter
        factorTwoIntrinsicElevenRetainedBadEvenPolynomial 0 0 0)
      (factorTwoIntrinsicElevenRetainedOddMixedRepresenter
        factorTwoIntrinsicElevenRetainedBadEvenPolynomial 0 0 0)
      qE qO
  have hzero : centeredPolynomialLift (0 : ℝ[X]) = (0 : ℝ → ℝ) := by
    funext x
    simp [centeredPolynomialLift]
  have hright :
      factorTwoEndpointChannelPhase
            (centeredPolynomialLift
              factorTwoIntrinsicElevenRetainedBadEvenPolynomial)
            (centeredPolynomialLift (0 : ℝ[X])) 0 0 -
          (1 / 128 : ℝ) * factorTwoPhaseSingularWeightedEnergy
            (centeredPolynomialLift
              factorTwoIntrinsicElevenRetainedBadEvenPolynomial)
            (centeredPolynomialLift (0 : ℝ[X])) 0 0 < 0 := by
    rw [centeredPolynomialLift_retainedBadEvenPolynomial, hzero]
    exact factorTwoIntrinsicElevenRetainedBadLowComplement_neg
  linarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedSelectorObstructionStructural
