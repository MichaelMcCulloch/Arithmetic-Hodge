import ArithmeticHodge.Analysis.ThreeByThreeSymmetricDeterminantMonotone
import ArithmeticHodge.Analysis.YoshidaEndpointEvenFullPolarization
import ArithmeticHodge.Analysis.YoshidaEndpointOddOneThreeRawPolarization
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicRetainedSingularGapStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4CleanCrossStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4EndpointProfile
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourC2Structural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024Structural

noncomputable section

open ThreeByThreeRankOneSchur
open ThreeByThreeConvexPencil
open ThreeByThreeSymmetricDeterminantMonotone
open UnitIntervalLogEnergyAffine
open YoshidaEndpointEvenFullPolarization
open YoshidaEndpointEvenLowProfile
open YoshidaEndpointEvenP2LogEnergy
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointPotentialBound
open YoshidaFactorTwoPhaseEnvelope
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicEvenCleanSharp
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseIntrinsicRetainedSingularGapStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4CleanCrossStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4CleanDiagonalStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4EndpointProfile
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixP4WeightedMass
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourC2Structural
open YoshidaFactorTwoPhaseIntrinsicSixSchurReduction
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseSingularWeightedCauchyStructural

/-!
# The retained singular operator on the even `P₀/P₂/P₄` core

The first viable retained low charge is `1 / 1024`.  This file identifies
the singular operator exactly on the three-dimensional even core before
proving coercivity.  The raw logarithmic cross vanishes by Legendre
orthogonality, and every remaining entry is an exact mass or endpoint-
potential pairing.
-/

/-- At phase zero, one half of the singular weighted energy has the exact
rational Gram matrix displayed below on the intrinsic even `P₀/P₂/P₄`
profile. -/
theorem half_singularWeightedEnergy_intrinsicEvenP024_zero
    (c0 c2 c4 : ℝ) :
    (1 / 2 : ℝ) * factorTwoPhaseSingularWeightedEnergy
        (factorTwoIntrinsicEvenP024Profile c0 c2 c4)
        (0 : ℝ → ℝ) 0 0 =
      symmetricQuadratic
        2 (1 / 3) (1 / 10) (86 / 75) (1 / 7) (2182 / 2835)
        c0 c2 c4 := by
  let p : ℝ → ℝ := yoshidaEndpointEvenLowProfile c0 c2
  let r : ℝ → ℝ := fun x ↦ c4 * factorTwoCenteredP4 x
  let w : ℝ → ℝ := fun x ↦ p x + r x
  have hw : w = factorTwoIntrinsicEvenP024Profile c0 c2 c4 := by
    funext x
    unfold w p r factorTwoIntrinsicEvenP024Profile
      factorTwoEvenStructuralLowProfile factorTwoIntrinsicSixEvenTail
      yoshidaEndpointEvenLowProfile centeredEvenP0
    simp only [Pi.add_apply]
    ring
  rw [← hw]
  have hp : Continuous p := by
    simpa only [p] using continuous_yoshidaEndpointEvenLowProfile c0 c2
  have hr : Continuous r := by
    dsimp only [r]
    exact continuous_const.mul continuous_factorTwoCenteredP4
  have hwc : Continuous w := hp.add hr
  have hrLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) r := by
    have hd : ContDiff ℝ 1 r := by
      dsimp only [r]
      unfold factorTwoCenteredP4
      fun_prop
    exact hd.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  have hwLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w := by
    have hd : ContDiff ℝ 1 w := by
      dsimp only [w, p, r]
      unfold yoshidaEndpointEvenLowProfile centeredEvenP2
        factorTwoCenteredP4
      fun_prop
    exact hd.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  have hpair :
      (∫ x : ℝ in -1..1, r x * centeredEvenP2 x) = 0 := by
    rw [show (fun x : ℝ ↦ r x * centeredEvenP2 x) =
        fun x ↦ c4 * (factorTwoCenteredP4 x * centeredEvenP2 x) by
      funext x
      dsimp only [r]
      ring,
      intervalIntegral.integral_const_mul,
      integral_factorTwoCenteredP4_mul_centeredEvenP2]
    ring
  have hraw : centeredRawLogEnergy w =
      (12 / 5 : ℝ) * c2 ^ 2 + (50 / 27 : ℝ) * c4 ^ 2 := by
    calc
      centeredRawLogEnergy w = centeredRawLogEnergy
          (fun x ↦ c0 * centeredEvenP0 x + c2 * centeredEvenP2 x + r x) := by
        congr 1
      _ = c2 ^ 2 * centeredRawLogEnergy centeredEvenP2 +
            centeredRawLogEnergy r :=
        centeredRawLogEnergy_low_tail r hrLocal hpair c0 c2
      _ = _ := by
        dsimp only [r]
        rw [centeredRawLogEnergy_centeredEvenP2,
          YoshidaEndpointOddOneThreeRawPolarization.centeredRawLogEnergy_const_mul,
          centeredRawLogEnergy_factorTwoCenteredP4]
        ring
  have hP4Int : IntervalIntegrable factorTwoCenteredP4 volume (-1) 1 :=
    continuous_factorTwoCenteredP4.intervalIntegrable (-1) 1
  have hP4P2Int : IntervalIntegrable
      (fun x : ℝ ↦ factorTwoCenteredP4 x * centeredEvenP2 x)
      volume (-1) 1 :=
    (continuous_factorTwoCenteredP4.mul (by
      unfold centeredEvenP2
      fun_prop)).intervalIntegrable (-1) 1
  have hcrossM : (∫ x : ℝ in -1..1, p x * r x) = 0 := by
    rw [show (fun x : ℝ ↦ p x * r x) = fun x ↦
        (c0 * c4) * factorTwoCenteredP4 x +
          (c2 * c4) * (factorTwoCenteredP4 x * centeredEvenP2 x) by
      funext x
      dsimp only [p, r]
      unfold yoshidaEndpointEvenLowProfile
      ring,
      intervalIntegral.integral_add
        (hP4Int.const_mul (c0 * c4)) (hP4P2Int.const_mul (c2 * c4)),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      integral_factorTwoCenteredP4,
      integral_factorTwoCenteredP4_mul_centeredEvenP2]
    ring
  have hrM : (∫ x : ℝ in -1..1, r x ^ 2) =
      (2 / 9 : ℝ) * c4 ^ 2 := by
    rw [show (fun x : ℝ ↦ r x ^ 2) =
        fun x ↦ c4 ^ 2 * factorTwoCenteredP4 x ^ 2 by
      funext x
      dsimp only [r]
      ring,
      intervalIntegral.integral_const_mul,
      integral_factorTwoCenteredP4_sq]
    ring
  have hmass : (∫ x : ℝ in -1..1, w x ^ 2) =
      2 * c0 ^ 2 + (2 / 5 : ℝ) * c2 ^ 2 +
        (2 / 9 : ℝ) * c4 ^ 2 := by
    dsimp only [w]
    rw [integral_add_sq p r hp hr,
      integral_yoshidaEndpointEvenLowProfile_sq, hcrossM, hrM]
    ring
  have hV0 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * centeredEvenP0 x *
        factorTwoCenteredP4 x) volume (-1) 1 :=
    intervalIntegrable_endpointPotential_mul centeredEvenP0
      factorTwoCenteredP4 (by unfold centeredEvenP0; fun_prop)
      continuous_factorTwoCenteredP4
  have hV2 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * centeredEvenP2 x *
        factorTwoCenteredP4 x) volume (-1) 1 :=
    intervalIntegrable_endpointPotential_mul centeredEvenP2
      factorTwoCenteredP4 (by unfold centeredEvenP2; fun_prop)
      continuous_factorTwoCenteredP4
  have hcrossV : (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * p x * r x) =
        (1 / 10 : ℝ) * c0 * c4 + (1 / 7 : ℝ) * c2 * c4 := by
    rw [show (fun x : ℝ ↦ yoshidaEndpointPotential x * p x * r x) =
        fun x ↦ (c0 * c4) *
            (yoshidaEndpointPotential x * centeredEvenP0 x *
              factorTwoCenteredP4 x) +
          (c2 * c4) *
            (yoshidaEndpointPotential x * centeredEvenP2 x *
              factorTwoCenteredP4 x) by
      funext x
      dsimp only [p, r]
      unfold yoshidaEndpointEvenLowProfile centeredEvenP0
      ring,
      intervalIntegral.integral_add
        (hV0.const_mul (c0 * c4)) (hV2.const_mul (c2 * c4)),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      integral_endpointPotential_mul_centeredEvenP0_mul_P4,
      integral_endpointPotential_mul_centeredEvenP2_mul_P4]
    ring
  have hrV : (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * r x ^ 2) =
        c4 ^ 2 * (1739 / 5670 - (2 / 9 : ℝ) * Real.log 2) := by
    rw [show (fun x : ℝ ↦ yoshidaEndpointPotential x * r x ^ 2) =
        fun x ↦ c4 ^ 2 *
          (yoshidaEndpointPotential x * factorTwoCenteredP4 x ^ 2) by
      funext x
      dsimp only [r]
      ring,
      intervalIntegral.integral_const_mul,
      integral_endpointPotential_mul_factorTwoCenteredP4_sq]
  have hpot : (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * w x ^ 2) =
        (2 - 2 * Real.log 2) * c0 ^ 2 +
          (2 / 3 : ℝ) * c0 * c2 +
          (41 / 75 - (2 / 5 : ℝ) * Real.log 2) * c2 ^ 2 +
          2 * (1 / 10 : ℝ) * c0 * c4 +
          2 * (1 / 7 : ℝ) * c2 * c4 +
          (1739 / 5670 - (2 / 9 : ℝ) * Real.log 2) * c4 ^ 2 := by
    dsimp only [w]
    rw [integral_endpointPotential_add_sq p r hp hr,
      integral_endpointPotential_mul_yoshidaEndpointEvenLowProfile_sq,
      hcrossV, hrV]
    ring
  have h0raw : centeredRawLogEnergy (0 : ℝ → ℝ) = 0 := by
    unfold centeredRawLogEnergy
    simp
  have h0local : LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      (0 : ℝ → ℝ) := by
    have hd : ContDiff ℝ 1 (fun _ : ℝ ↦ (0 : ℝ)) := contDiff_const
    change LocallyLipschitzOn (Icc (-1 : ℝ) 1) (fun _ : ℝ ↦ (0 : ℝ))
    exact hd.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  have hs := half_singularWeightedEnergy_eq_protected_add_logMass
    w (0 : ℝ → ℝ) hwc continuous_zero hwLocal h0local 0 0
  unfold factorTwoIntrinsicProtectedBlock factorTwoIntrinsicEnergy
    factorTwoIntrinsicPotentialEnergy at hs
  simp [factorTwoCenteredPhaseCorrelation, h0raw] at hs
  rw [hraw, hpot, hmass] at hs
  unfold symmetricQuadratic
  norm_num at hs ⊢
  ring_nf at hs ⊢
  nlinarith

/-! ## Structural coercivity at the first viable retained charge -/

/-- Determinant in the aligned basis
`(P₀ + P₂, P₂ - P₀, P₄)`.  The signs correspond to the matrix
`[[A, -X, S], [-X, C, D], [S, D, F]]`. -/
def retainedP024AlignedDeterminant
    (A X C S D F : ℝ) : ℝ :=
  (F * (A * C - X ^ 2) - A * D ^ 2 - C * S ^ 2 -
    2 * X * S * D) / 4

/-- Strong-pivot Schur identity for the retained aligned determinant.

It exposes the only delicate endpoint comparison as a strict Cauchy gap
between the weak coordinate and `P₄`, after both have been projected off
the strong `P₀ + P₂` coordinate. -/
theorem retainedP024AlignedDeterminant_strongPivot_identity
    (A X C S D F : ℝ) :
    4 * A * retainedP024AlignedDeterminant A X C S D F =
      (A * C - X ^ 2) * (A * F - S ^ 2) -
        (A * D + X * S) ^ 2 := by
  unfold retainedP024AlignedDeterminant
  ring

set_option maxHeartbeats 800000

/-- The phase-zero clean matrix remains positive definite after subtracting
`1 / 1024` of the exact half-singular Gram matrix.  The determinant proof is
a six-coordinate monotonicity telescope to one rational comparison matrix. -/
private theorem retainedP024Zero_gates :
    let A := yoshidaEndpointEvenLowGram00 - (1 / 1024 : ℝ) * 2
    let B := yoshidaEndpointEvenLowGram02 - (1 / 1024 : ℝ) * (1 / 3)
    let C := yoshidaEndpointEvenCleanBilinear
      centeredEvenP0 factorTwoCenteredP4 - (1 / 1024 : ℝ) * (1 / 10)
    let D := yoshidaEndpointEvenLowGram22 - (1 / 1024 : ℝ) * (86 / 75)
    let E := yoshidaEndpointEvenCleanBilinear
      centeredEvenP2 factorTwoCenteredP4 - (1 / 1024 : ℝ) * (1 / 7)
    let F := yoshidaEndpointOddCleanQuadratic factorTwoCenteredP4 -
      (1 / 1024 : ℝ) * (2182 / 2835)
    0 < A ∧ 0 < leadingMinorTwo A B D ∧
      0 < symmetricDeterminant A B C D E F := by
  dsimp only
  let A := yoshidaEndpointEvenLowGram00 - (1 / 1024 : ℝ) * 2
  let B := yoshidaEndpointEvenLowGram02 - (1 / 1024 : ℝ) * (1 / 3)
  let C := yoshidaEndpointEvenCleanBilinear
    centeredEvenP0 factorTwoCenteredP4 - (1 / 1024 : ℝ) * (1 / 10)
  let D := yoshidaEndpointEvenLowGram22 - (1 / 1024 : ℝ) * (86 / 75)
  let E := yoshidaEndpointEvenCleanBilinear
    centeredEvenP2 factorTwoCenteredP4 - (1 / 1024 : ℝ) * (1 / 7)
  let F := yoshidaEndpointOddCleanQuadratic factorTwoCenteredP4 -
    (1 / 1024 : ℝ) * (2182 / 2835)
  let a : ℝ := 3665 / 10000 - (1 / 1024 : ℝ) * 2
  let bl : ℝ := 3402 / 10000 - (1 / 1024 : ℝ) * (1 / 3)
  let b : ℝ := 3403 / 10000 - (1 / 1024 : ℝ) * (1 / 3)
  let c : ℝ := 1 / 10 - 1 / 250000 - (1 / 1024 : ℝ) * (1 / 10)
  let cu : ℝ := 1 / 10 + 1 / 250000 - (1 / 1024 : ℝ) * (1 / 10)
  let d : ℝ := 3269 / 10000 - (1 / 1024 : ℝ) * (86 / 75)
  let el : ℝ := 1 / 7 - 7 / 200000 - (1 / 1024 : ℝ) * (1 / 7)
  let e : ℝ := 1 / 7 + 7 / 200000 - (1 / 1024 : ℝ) * (1 / 7)
  let f : ℝ := 1571 / 5000 - (1 / 1024 : ℝ) * (2182 / 2835)
  have h00 := intrinsicEven_cleanGram00_gt
  have h02 := intrinsicEven_cleanGram02_bounds
  have h22 := intrinsicEven_cleanGram22_gt
  have h04 := factorTwoIntrinsicP4CleanCross04_sub_one_tenth_abs_lt
  have h24 := factorTwoIntrinsicP4CleanCross24_sub_one_seventh_abs_lt
  have h44 := one_thousand_five_hundred_seventy_one_five_thousandths_lt_clean_p4
  rw [abs_lt] at h04 h24
  have hA : a < A := by
    dsimp only [a, A]
    linarith
  have hBL : bl < B := by
    dsimp only [bl, B]
    linarith
  have hBU : B < b := by
    dsimp only [b, B]
    linarith
  have hC : c < C := by
    dsimp only [c, C]
    linarith
  have hCU : C < cu := by
    dsimp only [cu, C]
    linarith
  have hD : d < D := by
    dsimp only [d, D]
    linarith
  have hEL : el < E := by
    dsimp only [el, E]
    linarith
  have hEU : E < e := by
    dsimp only [e, E]
    linarith
  have hF : f < F := by
    dsimp only [f, F]
    linarith
  have ha0 : 0 < a := by norm_num [a]
  have hbl0 : 0 < bl := by norm_num [bl]
  have hb0 : 0 < b := by norm_num [b]
  have hc0 : 0 < c := by norm_num [c]
  have hcu0 : 0 < cu := by norm_num [cu]
  have hd0 : 0 < d := by norm_num [d]
  have hel0 : 0 < el := by norm_num [el]
  have he0 : 0 < e := by norm_num [e]
  have hf0 : 0 < f := by norm_num [f]
  have hB0 : 0 < B := hbl0.trans hBL
  have hC0 : 0 < C := hc0.trans hC
  have hE0 : 0 < E := hel0.trans hEL
  have hcornerMinor : 0 < a * d - b ^ 2 := by
    norm_num [a, b, d]
  have hAD : a * d < A * D := by
    calc
      a * d < A * d := mul_lt_mul_of_pos_right hA hd0
      _ < A * D := mul_lt_mul_of_pos_left hD (ha0.trans hA)
  have hBsq : B ^ 2 < b ^ 2 :=
    pow_lt_pow_left₀ hBU hB0.le (by norm_num)
  have hminor22 : 0 < A * D - B ^ 2 := by linarith
  have hminor00 : 0 ≤ d * f - e ^ 2 := by
    norm_num [d, e, f]
  have hslope01 : 2 * c * e ≤ f * (B + b) := by
    have hrational : 2 * c * e < f * (bl + b) := by
      norm_num [c, e, f, bl, b]
    nlinarith
  have hslope02 : d * (c + C) ≤ 2 * B * e := by
    have hrational : d * (c + cu) < 2 * bl * e := by
      norm_num [d, c, cu, bl, e]
    nlinarith
  have hCsq : C ^ 2 < cu ^ 2 :=
    pow_lt_pow_left₀ hCU hC0.le (by norm_num)
  have hminor11 : 0 ≤ A * f - C ^ 2 := by
    have hAf : a * f < A * f := mul_lt_mul_of_pos_right hA hf0
    have hrational : cu ^ 2 < a * f := by
      norm_num [cu, a, f]
    nlinarith
  have hBC : B * C < b * cu := by
    calc
      B * C < b * C := mul_lt_mul_of_pos_right hBU hC0
      _ < b * cu := mul_lt_mul_of_pos_left hCU hb0
  have hAE : a * (el + e) < A * (E + e) := by
    have hsum : el + e < E + e := by linarith
    calc
      a * (el + e) < A * (el + e) :=
        mul_lt_mul_of_pos_right hA (add_pos hel0 he0)
      _ < A * (E + e) :=
        mul_lt_mul_of_pos_left hsum (ha0.trans hA)
  have hslope12 : 2 * B * C ≤ A * (E + e) := by
    have hrational : 2 * b * cu < a * (el + e) := by
      norm_num [b, cu, a, el, e]
    nlinarith
  have hdetCorner : 0 < symmetricDeterminant a b c d e f := by
    norm_num [symmetricDeterminant, a, b, c, d, e, f]
  have hdetCompare : symmetricDeterminant a b c d e f ≤
      symmetricDeterminant A B C D E F :=
    symmetricDeterminant_corner_le_of_six_coordinate_telescope
      hA.le hBU.le hC.le hD.le hEU.le hF.le
      hminor00 hslope01 hslope02 hminor11 hslope12 hminor22.le
  exact ⟨ha0.trans hA, by simpa only [leadingMinorTwo] using hminor22,
    hdetCorner.trans_le hdetCompare⟩

/-- The phase-zero `P₀/P₂/P₄` form is strictly coercive after retaining
`1 / 1024` of the half-singular operator. -/
theorem factorTwoEndpointChannelPhase_sub_oneDiv1024_halfSingular_pos_zero
    (c0 c2 c4 : ℝ) (hne : c0 ≠ 0 ∨ c2 ≠ 0 ∨ c4 ≠ 0) :
    0 < factorTwoEndpointChannelPhase
          (factorTwoIntrinsicEvenP024Profile c0 c2 c4)
          (0 : ℝ → ℝ) 0 0 -
        (1 / 1024 : ℝ) * ((1 / 2 : ℝ) *
          factorTwoPhaseSingularWeightedEnergy
            (factorTwoIntrinsicEvenP024Profile c0 c2 c4)
            (0 : ℝ → ℝ) 0 0) := by
  rw [factorTwoEndpointChannelPhase_intrinsicEvenP024_eq_quadratic,
    half_singularWeightedEnergy_intrinsicEvenP024_zero]
  have hgates := retainedP024Zero_gates
  have hpos := symmetricQuadratic_pos
    (yoshidaEndpointEvenLowGram00 - (1 / 1024 : ℝ) * 2)
    (yoshidaEndpointEvenLowGram02 - (1 / 1024 : ℝ) * (1 / 3))
    (yoshidaEndpointEvenCleanBilinear centeredEvenP0 factorTwoCenteredP4 -
      (1 / 1024 : ℝ) * (1 / 10))
    (yoshidaEndpointEvenLowGram22 - (1 / 1024 : ℝ) * (86 / 75))
    (yoshidaEndpointEvenCleanBilinear centeredEvenP2 factorTwoCenteredP4 -
      (1 / 1024 : ℝ) * (1 / 7))
    (yoshidaEndpointOddCleanQuadratic factorTwoCenteredP4 -
      (1 / 1024 : ℝ) * (2182 / 2835))
    hgates.1 hgates.2.1 hgates.2.2 c0 c2 c4 hne
  convert hpos using 1
  unfold factorTwoStructuralPhaseLow00 factorTwoStructuralPhaseLow02
    factorTwoStructuralPhaseLow22 factorTwoIntrinsicFourP45Cross04
    factorTwoIntrinsicFourP45Cross24 factorTwoIntrinsicP4PhaseDiagonal
    symmetricQuadratic
  ring

set_option maxHeartbeats 200000

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024Structural
