import ArithmeticHodge.Analysis.ThreeByThreeSymmetricDeterminantMonotone
import ArithmeticHodge.Analysis.YoshidaEndpointEvenFullPolarization
import ArithmeticHodge.Analysis.YoshidaEndpointOddOneThreeRawPolarization
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicRetainedSingularGapStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4CleanCrossStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4CorrelationStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4EndpointProfile
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourC2Structural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusPositiveStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusMinorStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseStructuralLowData

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024Structural

noncomputable section

open CenteredEndpointCorrelation
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
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseEnvelope
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicEvenCleanSharp
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowStaticMinusRationalSchur
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseIntrinsicRetainedSingularGapStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4CleanCrossStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4CleanDiagonalStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4CorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4EndpointProfile
open YoshidaFactorTwoPhaseIntrinsicSixP4MinusEndpointStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4PlusEndpointExactSchur
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixP4WeightedMass
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotSecondSharpStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourC2Structural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticMinusPositiveStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusMinorStructural
open YoshidaFactorTwoPhaseIntrinsicSixSchurReduction
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseSingularWeightedCauchyStructural
open YoshidaFactorTwoPhaseStructuralLowData

/-!
# The retained singular operator on the even `P₀/P₂/P₄` core

This file identifies the singular operator exactly on the three-dimensional
even core before proving coercivity at the phase-zero `1 / 1024` charge and
the retuned `1 / 2048` charge.  The raw logarithmic cross vanishes by Legendre
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

/-- Exact overlap correlation of the retained even core. -/
private theorem centeredEndpointCorrelation_intrinsicEvenP024
    (c0 c2 c4 t : ℝ) :
    centeredEndpointCorrelation
        (factorTwoIntrinsicEvenP024Profile c0 c2 c4) t =
      c0 ^ 2 * (2 - t) +
        2 * c0 * c2 *
          (-t * (t - 2) * (t - 1) / 2) +
        c2 ^ 2 *
          (-(t - 2) *
            (3 * t ^ 4 + 6 * t ^ 3 - 8 * t ^ 2 - 16 * t + 8) / 40) +
        2 * c0 * c4 * factorTwoIntrinsicP4Correlation04 t +
        2 * c2 * c4 * factorTwoIntrinsicP4Correlation24 t +
        c4 ^ 2 * factorTwoIntrinsicP4Correlation44 t := by
  let p : ℝ → ℝ := factorTwoEvenStructuralLowProfile c0 c2
  let r : ℝ → ℝ := c4 • factorTwoCenteredP4
  have hp : Continuous p := by
    simpa only [p] using continuous_factorTwoEvenStructuralLowProfile c0 c2
  have hr : Continuous r := by
    exact continuous_factorTwoCenteredP4.const_smul c4
  have hp0 : Continuous centeredEvenP0 := by
    unfold centeredEvenP0
    fun_prop
  have hp2 : Continuous centeredEvenP2 := by
    unfold centeredEvenP2
    fun_prop
  have hw : factorTwoIntrinsicEvenP024Profile c0 c2 c4 = p + r := by
    funext x
    unfold factorTwoIntrinsicEvenP024Profile factorTwoIntrinsicSixEvenTail
      p r
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hw, centeredEndpointCorrelation_add p r hp hr]
  have hcross : factorTwoCenteredCorrelationBilinear p r t =
      c0 * c4 * factorTwoIntrinsicP4Correlation04 t +
        c2 * c4 * factorTwoIntrinsicP4Correlation24 t := by
    have hadd : factorTwoCenteredCorrelationBilinear
        (c0 • centeredEvenP0 + c2 • centeredEvenP2)
        (c4 • factorTwoCenteredP4) t =
      factorTwoCenteredCorrelationBilinear
          (c0 • centeredEvenP0) (c4 • factorTwoCenteredP4) t +
        factorTwoCenteredCorrelationBilinear
          (c2 • centeredEvenP2) (c4 • factorTwoCenteredP4) t := by
      unfold factorTwoCenteredCorrelationBilinear
      rw [factorTwoCenteredCrossCorrelation_add_left
          (c0 • centeredEvenP0) (c2 • centeredEvenP2)
          (c4 • factorTwoCenteredP4)
          (hp0.const_smul c0) (hp2.const_smul c2) hr t,
        factorTwoCenteredCrossCorrelation_add_right
          (c4 • factorTwoCenteredP4) (c0 • centeredEvenP0)
          (c2 • centeredEvenP2) hr
          (hp0.const_smul c0) (hp2.const_smul c2) t]
      ring
    rw [show p = c0 • centeredEvenP0 + c2 • centeredEvenP2 by
        simpa only [p] using factorTwoEvenStructuralLowProfile_eq_smul_add c0 c2,
      show r = c4 • factorTwoCenteredP4 by rfl, hadd,
      factorTwoCenteredCorrelationBilinear_smul_smul,
      factorTwoCenteredCorrelationBilinear_smul_smul,
      factorTwoCenteredCorrelationBilinear_p0_p4,
      factorTwoCenteredCorrelationBilinear_p2_p4]
  have hpCorr := centeredEndpointCorrelation_evenStructuralProfile c0 c2 t
  have hrCorr : centeredEndpointCorrelation r t =
      c4 ^ 2 * factorTwoIntrinsicP4Correlation44 t := by
    rw [← factorTwoCenteredCorrelationBilinear_self,
      show r = c4 • factorTwoCenteredP4 by rfl,
      factorTwoCenteredCorrelationBilinear_smul_smul,
      factorTwoCenteredCorrelationBilinear_self,
      centeredEndpointCorrelation_p4]
    ring
  rw [show centeredEndpointCorrelation p t =
      c0 ^ 2 * (2 - t) +
        2 * c0 * c2 * (-t * (t - 2) * (t - 1) / 2) +
        c2 ^ 2 * (-(t - 2) *
          (3 * t ^ 4 + 6 * t ^ 3 - 8 * t ^ 2 - 16 * t + 8) / 40) by
      simpa only [p, evenStructuralCorrelation00,
        evenStructuralCorrelation02, evenStructuralCorrelation22] using hpCorr,
    hcross, hrCorr]
  ring

private theorem integral_polynomial_eight
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ l r : ℝ) :
    (∫ x : ℝ in l..r,
      a₀ * x ^ 0 + (a₁ * x ^ 1 + (a₂ * x ^ 2 +
        (a₃ * x ^ 3 + (a₄ * x ^ 4 + (a₅ * x ^ 5 +
          (a₆ * x ^ 6 + (a₇ * x ^ 7 + a₈ * x ^ 8)))))))) =
      a₀ * (r - l) + a₁ * (r ^ 2 - l ^ 2) / 2 +
        a₂ * (r ^ 3 - l ^ 3) / 3 + a₃ * (r ^ 4 - l ^ 4) / 4 +
        a₄ * (r ^ 5 - l ^ 5) / 5 + a₅ * (r ^ 6 - l ^ 6) / 6 +
        a₆ * (r ^ 7 - l ^ 7) / 7 + a₇ * (r ^ 8 - l ^ 8) / 8 +
        a₈ * (r ^ 9 - l ^ 9) / 9 := by
  repeat' rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) l r)
    (Continuous.intervalIntegrable (by fun_prop) l r)]
  repeat' rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

/-- The reflected-pole Gram matrix on `P₀/P₂/P₄` is exact and rational. -/
private theorem integral_centeredEndpointCorrelation_intrinsicEvenP024_div_two_sub
    (c0 c2 c4 : ℝ) :
    (∫ t : ℝ in 0..2,
        centeredEndpointCorrelation
          (factorTwoIntrinsicEvenP024Profile c0 c2 c4) t / (2 - t)) =
      symmetricQuadratic
        2 (1 / 3) (1 / 10) (11 / 75) (8 / 105) (269 / 5670)
        c0 c2 c4 := by
  have heq : ∀ᵐ t : ℝ ∂volume,
      centeredEndpointCorrelation
          (factorTwoIntrinsicEvenP024Profile c0 c2 c4) t / (2 - t) =
        c0 ^ 2 +
          2 * c0 * c2 * (t * (t - 1) / 2) +
          c2 ^ 2 *
            ((3 * t ^ 4 + 6 * t ^ 3 - 8 * t ^ 2 - 16 * t + 8) / 40) +
          2 * c0 * c4 *
            (t * (t - 1) * (7 * t ^ 2 - 14 * t + 4) / 8) +
          2 * c2 * c4 *
            (t * (t ^ 5 + 2 * t ^ 4 - 6 * t ^ 3 - 12 * t ^ 2 +
              24 * t - 8) / 16) +
          c4 ^ 2 *
            ((35 * t ^ 8 + 70 * t ^ 7 - 220 * t ^ 6 - 440 * t ^ 5 +
              416 * t ^ 4 + 832 * t ^ 3 - 256 * t ^ 2 - 512 * t + 128) /
              1152) := by
    filter_upwards [MeasureTheory.Measure.ae_ne volume (2 : ℝ)] with t ht
    rw [centeredEndpointCorrelation_intrinsicEvenP024]
    have hden : 2 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
    unfold factorTwoIntrinsicP4Correlation04
      factorTwoIntrinsicP4Correlation24 factorTwoIntrinsicP4Correlation44
    field_simp [hden]
    ring
  have heqI : ∀ᵐ t : ℝ ∂volume, t ∈ uIoc (0 : ℝ) 2 →
      centeredEndpointCorrelation
          (factorTwoIntrinsicEvenP024Profile c0 c2 c4) t / (2 - t) =
        c0 ^ 2 +
          2 * c0 * c2 * (t * (t - 1) / 2) +
          c2 ^ 2 *
            ((3 * t ^ 4 + 6 * t ^ 3 - 8 * t ^ 2 - 16 * t + 8) / 40) +
          2 * c0 * c4 *
            (t * (t - 1) * (7 * t ^ 2 - 14 * t + 4) / 8) +
          2 * c2 * c4 *
            (t * (t ^ 5 + 2 * t ^ 4 - 6 * t ^ 3 - 12 * t ^ 2 +
              24 * t - 8) / 16) +
          c4 ^ 2 *
            ((35 * t ^ 8 + 70 * t ^ 7 - 220 * t ^ 6 - 440 * t ^ 5 +
              416 * t ^ 4 + 832 * t ^ 3 - 256 * t ^ 2 - 512 * t + 128) /
              1152) := heq.mono fun _ ht _ ↦ ht
  rw [intervalIntegral.integral_congr_ae heqI]
  rw [show (fun t : ℝ ↦
        c0 ^ 2 +
          2 * c0 * c2 * (t * (t - 1) / 2) +
          c2 ^ 2 *
            ((3 * t ^ 4 + 6 * t ^ 3 - 8 * t ^ 2 - 16 * t + 8) / 40) +
          2 * c0 * c4 *
            (t * (t - 1) * (7 * t ^ 2 - 14 * t + 4) / 8) +
          2 * c2 * c4 *
            (t * (t ^ 5 + 2 * t ^ 4 - 6 * t ^ 3 - 12 * t ^ 2 +
              24 * t - 8) / 16) +
          c4 ^ 2 *
            ((35 * t ^ 8 + 70 * t ^ 7 - 220 * t ^ 6 - 440 * t ^ 5 +
              416 * t ^ 4 + 832 * t ^ 3 - 256 * t ^ 2 - 512 * t + 128) /
              1152)) =
      fun t ↦
        (c0 ^ 2 + c2 ^ 2 / 5 + c4 ^ 2 / 9) * t ^ 0 +
        ((-c0 * c2 - c0 * c4 - c2 * c4 - 2 * c2 ^ 2 / 5 -
            4 * c4 ^ 2 / 9) * t ^ 1 +
        ((c0 * c2 + 9 * c0 * c4 / 2 + 3 * c2 * c4 - c2 ^ 2 / 5 -
            2 * c4 ^ 2 / 9) * t ^ 2 +
        ((-21 * c0 * c4 / 4 - 3 * c2 * c4 / 2 + 3 * c2 ^ 2 / 20 +
            13 * c4 ^ 2 / 18) * t ^ 3 +
        ((7 * c0 * c4 / 4 - 3 * c2 * c4 / 4 + 3 * c2 ^ 2 / 40 +
            13 * c4 ^ 2 / 36) * t ^ 4 +
        ((c2 * c4 / 4 - 55 * c4 ^ 2 / 144) * t ^ 5 +
        ((c2 * c4 / 8 - 55 * c4 ^ 2 / 288) * t ^ 6 +
        ((35 * c4 ^ 2 / 576) * t ^ 7 +
          (35 * c4 ^ 2 / 1152) * t ^ 8))))))) by
    funext t
    ring,
    integral_polynomial_eight]
  unfold symmetricQuadratic
  norm_num
  ring

/-- Exact phase-dependent half-singular Gram matrix on the retained even
core.  The alternating phase coordinate disappears because the odd profile
is zero. -/
theorem half_singularWeightedEnergy_intrinsicEvenP024
    (c0 c2 c4 a b : ℝ) :
    (1 / 2 : ℝ) * factorTwoPhaseSingularWeightedEnergy
        (factorTwoIntrinsicEvenP024Profile c0 c2 c4)
        (0 : ℝ → ℝ) a b =
      symmetricQuadratic
        (2 - a) ((2 - a) / 6) ((2 - a) / 20)
        ((172 - 11 * a) / 150) ((15 - 4 * a) / 105)
        ((8728 - 269 * a) / 11340) c0 c2 c4 := by
  let w := factorTwoIntrinsicEvenP024Profile c0 c2 c4
  have hwc : Continuous w := by
    dsimp only [w]
    unfold factorTwoIntrinsicEvenP024Profile
      factorTwoEvenStructuralLowProfile factorTwoIntrinsicSixEvenTail
      centeredEvenP0 centeredEvenP2 factorTwoCenteredP4
    fun_prop
  have hwLocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w := by
    have hd : ContDiff ℝ 1 w := by
      have hlow : ContDiff ℝ 1
          (factorTwoEvenStructuralLowProfile c0 c2) := by
        unfold factorTwoEvenStructuralLowProfile centeredEvenP0 centeredEvenP2
        fun_prop
      have htail : ContDiff ℝ 1 (factorTwoIntrinsicSixEvenTail c4) := by
        unfold factorTwoIntrinsicSixEvenTail factorTwoCenteredP4
        fun_prop
      simpa only [w, factorTwoIntrinsicEvenP024Profile] using hlow.add htail
    exact hd.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  have h0local : LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      (0 : ℝ → ℝ) := by
    have hd : ContDiff ℝ 1 (fun _ : ℝ ↦ (0 : ℝ)) := contDiff_const
    change LocallyLipschitzOn (Icc (-1 : ℝ) 1) (fun _ : ℝ ↦ (0 : ℝ))
    exact hd.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  have hs := half_singularWeightedEnergy_eq_protected_add_logMass
    w (0 : ℝ → ℝ) hwc continuous_zero hwLocal h0local a b
  have hs0 := half_singularWeightedEnergy_eq_protected_add_logMass
    w (0 : ℝ → ℝ) hwc continuous_zero hwLocal h0local 0 0
  have hphase : factorTwoCenteredPhaseCorrelation
      w (0 : ℝ → ℝ) a (-b) =
        fun t ↦ a * centeredEndpointCorrelation w t := by
    funext t
    unfold factorTwoCenteredPhaseCorrelation
      factorTwoCenteredCrossCorrelation centeredEndpointCorrelation
    simp
  unfold factorTwoIntrinsicProtectedBlock at hs hs0
  rw [hphase] at hs
  simp [factorTwoCenteredPhaseCorrelation,
    factorTwoCenteredCrossCorrelation] at hs0
  rw [show (fun t : ℝ ↦
      a * centeredEndpointCorrelation w t / (2 - t)) =
      fun t ↦ a * (centeredEndpointCorrelation w t / (2 - t)) by
        funext t
        ring,
    intervalIntegral.integral_const_mul,
    show (∫ t : ℝ in 0..2, centeredEndpointCorrelation w t / (2 - t)) =
        symmetricQuadratic
          2 (1 / 3) (1 / 10) (11 / 75) (8 / 105) (269 / 5670)
          c0 c2 c4 by
      simpa only [w] using
        integral_centeredEndpointCorrelation_intrinsicEvenP024_div_two_sub
          c0 c2 c4] at hs
  have hzero := half_singularWeightedEnergy_intrinsicEvenP024_zero c0 c2 c4
  change (1 / 2 : ℝ) * factorTwoPhaseSingularWeightedEnergy
      w (0 : ℝ → ℝ) a b = _
  change (1 / 2 : ℝ) * factorTwoPhaseSingularWeightedEnergy
      w (0 : ℝ → ℝ) 0 0 = _ at hzero
  unfold symmetricQuadratic at hs hzero ⊢
  norm_num at hs hs0 hzero ⊢
  ring_nf at hs hs0 hzero ⊢
  nlinarith

/-! ## Structural coercivity at the retained charges -/

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

/-- The aligned determinant is the original `P₀/P₂/P₄` determinant.
The unnormalised sum/difference change of basis multiplies determinants by
`4`; the built-in factor `1 / 4` cancels it. -/
theorem retainedP024AlignedDeterminant_eq_symmetricDeterminant
    (q00 q02 q04 q22 q24 q44 : ℝ) :
    retainedP024AlignedDeterminant
        (q00 + 2 * q02 + q22) (q00 - q22)
        (q00 - 2 * q02 + q22) (q04 + q24) (q24 - q04) q44 =
      symmetricDeterminant q00 q02 q04 q22 q24 q44 := by
  unfold retainedP024AlignedDeterminant symmetricDeterminant
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

/-- The phase-zero retained core is strictly coercive at the weaker
`1 / 2048` low charge.  This is the low coefficient used by the retuned
asymmetric Schur split. -/
theorem factorTwoEndpointChannelPhase_sub_oneDiv2048_halfSingular_pos_zero
    (c0 c2 c4 : ℝ) (hne : c0 ≠ 0 ∨ c2 ≠ 0 ∨ c4 ≠ 0) :
    0 < factorTwoEndpointChannelPhase
          (factorTwoIntrinsicEvenP024Profile c0 c2 c4)
          (0 : ℝ → ℝ) 0 0 -
        (1 / 2048 : ℝ) * ((1 / 2 : ℝ) *
          factorTwoPhaseSingularWeightedEnergy
            (factorTwoIntrinsicEvenP024Profile c0 c2 c4)
            (0 : ℝ → ℝ) 0 0) := by
  have hstrong :=
    factorTwoEndpointChannelPhase_sub_oneDiv1024_halfSingular_pos_zero
      c0 c2 c4 hne
  have hsingular :
      0 ≤ factorTwoPhaseSingularWeightedEnergy
        (factorTwoIntrinsicEvenP024Profile c0 c2 c4)
        (0 : ℝ → ℝ) 0 0 :=
    factorTwoPhaseSingularWeightedEnergy_nonneg
      (factorTwoIntrinsicEvenP024Profile c0 c2 c4)
      (0 : ℝ → ℝ) 0 0 (by norm_num)
  nlinarith

/-! ## Retuned positive endpoint -/

/-- Positive-endpoint principal minors after retaining `1 / 2048` of the
half-singular Gram.  The determinant is certified in the strong/weak aligned
basis; the only new analytic input is the cancellation-preserving weak bound
from the integrated pole-free envelope. -/
private theorem retainedP024Plus_gates :
    let q00 := factorTwoStructuralPhaseLow00 1 - (1 / 2048 : ℝ)
    let q02 := factorTwoStructuralPhaseLow02 1 -
      (1 / 2048 : ℝ) * (1 / 6)
    let q04 := factorTwoIntrinsicFourP45Cross04 1 -
      (1 / 2048 : ℝ) * (1 / 20)
    let q22 := factorTwoStructuralPhaseLow22 1 -
      (1 / 2048 : ℝ) * (161 / 150)
    let q24 := factorTwoIntrinsicFourP45Cross24 1 -
      (1 / 2048 : ℝ) * (11 / 105)
    let q44 := factorTwoIntrinsicP4PhaseDiagonal 1 -
      (1 / 2048 : ℝ) * (8459 / 11340)
    0 < q00 ∧ 0 < leadingMinorTwo q00 q02 q22 ∧
      0 < symmetricDeterminant q00 q02 q04 q22 q24 q44 := by
  dsimp only
  let q00 := factorTwoStructuralPhaseLow00 1 - (1 / 2048 : ℝ)
  let q02 := factorTwoStructuralPhaseLow02 1 -
    (1 / 2048 : ℝ) * (1 / 6)
  let q04 := factorTwoIntrinsicFourP45Cross04 1 -
    (1 / 2048 : ℝ) * (1 / 20)
  let q22 := factorTwoStructuralPhaseLow22 1 -
    (1 / 2048 : ℝ) * (161 / 150)
  let q24 := factorTwoIntrinsicFourP45Cross24 1 -
    (1 / 2048 : ℝ) * (11 / 105)
  let q44 := factorTwoIntrinsicP4PhaseDiagonal 1 -
    (1 / 2048 : ℝ) * (8459 / 11340)
  let A := factorTwoStructuralPhaseLow00 1 +
      2 * factorTwoStructuralPhaseLow02 1 +
      factorTwoStructuralPhaseLow22 1 -
    (1 / 2048 : ℝ) * (361 / 150)
  let X := factorTwoStructuralPhaseLow00 1 -
      factorTwoStructuralPhaseLow22 1 +
    (1 / 2048 : ℝ) * (11 / 150)
  let C := factorTwoStructuralPhaseLow00 1 -
      2 * factorTwoStructuralPhaseLow02 1 +
      factorTwoStructuralPhaseLow22 1 -
    (1 / 2048 : ℝ) * (87 / 50)
  let S := factorTwoIntrinsicFourP45Cross04 1 +
      factorTwoIntrinsicFourP45Cross24 1 -
    (1 / 2048 : ℝ) * (13 / 84)
  let D := factorTwoIntrinsicFourP45Cross24 1 -
      factorTwoIntrinsicFourP45Cross04 1 -
    (1 / 2048 : ℝ) * (23 / 420)
  let F := factorTwoIntrinsicP4PhaseDiagonal 1 -
    (1 / 2048 : ℝ) * (8459 / 11340)
  let a : ℝ := 547765 / 1000000 -
    (1 / 2048 : ℝ) * (361 / 150)
  let au : ℝ := 549941 / 1000000 -
    (1 / 2048 : ℝ) * (361 / 150)
  let xl : ℝ := -141 / 1000000 +
    (1 / 2048 : ℝ) * (11 / 150)
  let x : ℝ := 1919 / 1000000 +
    (1 / 2048 : ℝ) * (11 / 150)
  let c : ℝ := 6790 / 1000000 -
    (1 / 2048 : ℝ) * (87 / 50)
  let sl : ℝ := 1924 / 10000 -
    (1 / 2048 : ℝ) * (13 / 84)
  let s : ℝ := 193 / 1000 -
    (1 / 2048 : ℝ) * (13 / 84)
  let dl : ℝ := 1925 / 100000 -
    (1 / 2048 : ℝ) * (23 / 420)
  let d : ℝ := 39 / 2000 -
    (1 / 2048 : ℝ) * (23 / 420)
  let f : ℝ := 3439 / 25000 -
    (1 / 2048 : ℝ) * (8459 / 11340)
  let p : ℝ := a * c - x ^ 2
  let q : ℝ := a * f - s ^ 2
  let r : ℝ := au * d + x * s
  rcases factorTwoIntrinsicP4_positive_aligned_bounds with
    ⟨hAL, hAU, hXL, hXU, _hSL, _hSU, _hCL, _hCU, _hDL, _hDU⟩
  have hWeak :=
    factorTwoIntrinsicP4_positive_weak_gt_six_thousand_seven_hundred_ninety_div_million
  have hCrossLower := factorTwoIntrinsicP4PlusCrossCoordinate_lower_bounds
  have hSU := factorTwoIntrinsicP4PlusCrossSum_bounds.2
  have hDU := factorTwoIntrinsicP4PlusCrossDifference_bounds.2
  have hCleanF :=
    one_thousand_five_hundred_seventy_one_five_thousandths_lt_clean_p4
  have hPertF := factorTwoCenteredSymmetricPerturbation_p4_lower
  have hA : a < A := by dsimp only [a, A]; linarith
  have hAU' : A < au := by dsimp only [au, A]; linarith
  have hXL' : xl < X := by dsimp only [xl, X]; linarith
  have hXU' : X < x := by dsimp only [x, X]; linarith
  have hC : c < C := by dsimp only [c, C]; linarith
  have hSL : sl < S := by
    have h := hCrossLower.1
    unfold factorTwoIntrinsicP4PlusCrossSum at h
    dsimp only [sl, S]
    linarith
  have hS : S < s := by
    have h := hSU
    unfold factorTwoIntrinsicP4PlusCrossSum at h
    dsimp only [s, S]
    linarith
  have hDL : dl < D := by
    have h := hCrossLower.2
    unfold factorTwoIntrinsicP4PlusCrossDifference at h
    dsimp only [dl, D]
    linarith
  have hD : D < d := by
    have h := hDU
    unfold factorTwoIntrinsicP4PlusCrossDifference at h
    dsimp only [d, D]
    linarith
  have hF : f < F := by
    dsimp only [f, F]
    unfold factorTwoIntrinsicP4PhaseDiagonal
    nlinarith only [hCleanF, hPertF]
  have ha0 : 0 < a := by norm_num [a]
  have hau0 : 0 < au := by norm_num [au]
  have hxlneg : xl < 0 := by norm_num [xl]
  have hx0 : 0 < x := by norm_num [x]
  have hc0 : 0 < c := by norm_num [c]
  have hsl0 : 0 < sl := by norm_num [sl]
  have hs0 : 0 < s := by norm_num [s]
  have hdl0 : 0 < dl := by norm_num [dl]
  have hd0 : 0 < d := by norm_num [d]
  have hf0 : 0 < f := by norm_num [f]
  have hp0 : 0 < p := by norm_num [p, a, c, x]
  have hq0 : 0 < q := by norm_num [q, a, f, s]
  have hr0 : 0 < r := by norm_num [r, au, d, x, s]
  have hrat : r ^ 2 < p * q := by
    norm_num [r, p, q, a, au, c, d, f, s, x]
  have hA0 : 0 < A := ha0.trans hA
  have hC0 : 0 < C := hc0.trans hC
  have hS0 : 0 < S := hsl0.trans hSL
  have hD0 : 0 < D := hdl0.trans hDL
  have hF0 : 0 < F := hf0.trans hF
  have hXabs : |X| < x := by
    rw [abs_lt]
    constructor
    · have : -x < xl := by norm_num [x, xl]
      linarith only [this, hXL']
    · exact hXU'
  have hXsq : X ^ 2 < x ^ 2 := by
    rcases (abs_lt.mp hXabs) with ⟨hneg, hpos⟩
    nlinarith only [hneg, hpos, hx0]
  have hSsq : S ^ 2 < s ^ 2 := by
    nlinarith only [hS, hS0, hs0]
  have hAC : a * c < A * C := by
    calc
      a * c < A * c := mul_lt_mul_of_pos_right hA hc0
      _ < A * C := mul_lt_mul_of_pos_left hC hA0
  have hAF : a * f < A * F := by
    calc
      a * f < A * f := mul_lt_mul_of_pos_right hA hf0
      _ < A * F := mul_lt_mul_of_pos_left hF hA0
  have hFirst : p < A * C - X ^ 2 := by
    dsimp only [p]
    nlinarith only [hAC, hXsq]
  have hSecond : q < A * F - S ^ 2 := by
    dsimp only [q]
    nlinarith only [hAF, hSsq]
  have hFirst0 : 0 < A * C - X ^ 2 := hp0.trans hFirst
  have hSecond0 : 0 < A * F - S ^ 2 := hq0.trans hSecond
  have hProduct :
      p * q < (A * C - X ^ 2) * (A * F - S ^ 2) := by
    calc
      p * q < (A * C - X ^ 2) * q :=
        mul_lt_mul_of_pos_right hFirst hq0
      _ < (A * C - X ^ 2) * (A * F - S ^ 2) :=
        mul_lt_mul_of_pos_left hSecond hFirst0
  have hAD : A * D < au * d := by
    calc
      A * D < au * D := mul_lt_mul_of_pos_right hAU' hD0
      _ < au * d := mul_lt_mul_of_pos_left hD hau0
  have hXS : |X * S| < x * s := by
    rw [abs_mul, abs_of_pos hS0]
    calc
      |X| * S < x * S := mul_lt_mul_of_pos_right hXabs hS0
      _ < x * s := mul_lt_mul_of_pos_left hS hx0
  have hCrossAbs : |A * D + X * S| < r := by
    calc
      |A * D + X * S| ≤ |A * D| + |X * S| := abs_add_le _ _
      _ = A * D + |X * S| := by rw [abs_of_pos (mul_pos hA0 hD0)]
      _ < au * d + x * s := add_lt_add hAD hXS
      _ = r := by rfl
  have hCrossSq : (A * D + X * S) ^ 2 < r ^ 2 := by
    rcases (abs_lt.mp hCrossAbs) with ⟨hneg, hpos⟩
    nlinarith only [hneg, hpos, hr0]
  have hGap :
      0 < (A * C - X ^ 2) * (A * F - S ^ 2) -
        (A * D + X * S) ^ 2 := by
    nlinarith only [hProduct, hCrossSq, hrat]
  have hAligned : 0 < retainedP024AlignedDeterminant A X C S D F := by
    have hid := retainedP024AlignedDeterminant_strongPivot_identity A X C S D F
    have hmul : 0 < 4 * A * retainedP024AlignedDeterminant A X C S D F := by
      rw [hid]
      exact hGap
    exact pos_of_mul_pos_right hmul (by positivity : 0 ≤ 4 * A)
  have hAeq : A = q00 + 2 * q02 + q22 := by
    dsimp only [A, q00, q02, q22]
    ring
  have hXeq : X = q00 - q22 := by
    dsimp only [X, q00, q22]
    ring
  have hCeq : C = q00 - 2 * q02 + q22 := by
    dsimp only [C, q00, q02, q22]
    ring
  have hSeq : S = q04 + q24 := by
    dsimp only [S, q04, q24]
    ring
  have hDeq : D = q24 - q04 := by
    dsimp only [D, q04, q24]
    ring
  have hFeq : F = q44 := by rfl
  have hq00eq : 4 * q00 = A + C + 2 * X := by
    rw [hAeq, hCeq, hXeq]
    ring
  have hqCorner : 0 < a + c + 2 * xl := by
    norm_num [a, c, xl]
  have hq00 : 0 < q00 := by
    nlinarith only [hA, hC, hXL', hq00eq, hqCorner]
  have hminorEq :
      4 * leadingMinorTwo q00 q02 q22 = A * C - X ^ 2 := by
    rw [hAeq, hCeq, hXeq]
    unfold leadingMinorTwo
    ring
  have hminor : 0 < leadingMinorTwo q00 q02 q22 := by
    nlinarith only [hminorEq, hFirst, hp0]
  have hdetEq :
      retainedP024AlignedDeterminant A X C S D F =
        symmetricDeterminant q00 q02 q04 q22 q24 q44 := by
    rw [hAeq, hXeq, hCeq, hSeq, hDeq, hFeq]
    exact retainedP024AlignedDeterminant_eq_symmetricDeterminant
      q00 q02 q04 q22 q24 q44
  exact ⟨hq00, hminor, hdetEq ▸ hAligned⟩

/-- The positive endpoint is strictly coercive on `P₀/P₂/P₄` after
the retuned `1 / 2048` half-singular retention. -/
theorem factorTwoEndpointChannelPhase_sub_oneDiv2048_halfSingular_pos_plus
    (c0 c2 c4 : ℝ) (hne : c0 ≠ 0 ∨ c2 ≠ 0 ∨ c4 ≠ 0) :
    0 < factorTwoEndpointChannelPhase
          (factorTwoIntrinsicEvenP024Profile c0 c2 c4)
          (0 : ℝ → ℝ) 1 0 -
        (1 / 2048 : ℝ) * ((1 / 2 : ℝ) *
          factorTwoPhaseSingularWeightedEnergy
            (factorTwoIntrinsicEvenP024Profile c0 c2 c4)
            (0 : ℝ → ℝ) 1 0) := by
  rw [factorTwoEndpointChannelPhase_intrinsicEvenP024_eq_quadratic,
    half_singularWeightedEnergy_intrinsicEvenP024]
  have hgates := retainedP024Plus_gates
  have hpos := symmetricQuadratic_pos
    (factorTwoStructuralPhaseLow00 1 - (1 / 2048 : ℝ))
    (factorTwoStructuralPhaseLow02 1 - (1 / 2048 : ℝ) * (1 / 6))
    (factorTwoIntrinsicFourP45Cross04 1 - (1 / 2048 : ℝ) * (1 / 20))
    (factorTwoStructuralPhaseLow22 1 - (1 / 2048 : ℝ) * (161 / 150))
    (factorTwoIntrinsicFourP45Cross24 1 - (1 / 2048 : ℝ) * (11 / 105))
    (factorTwoIntrinsicP4PhaseDiagonal 1 -
      (1 / 2048 : ℝ) * (8459 / 11340))
    hgates.1 hgates.2.1 hgates.2.2 c0 c2 c4 hne
  convert hpos using 1
  unfold symmetricQuadratic
  norm_num
  ring

/-! ## Retuned negative endpoint -/

/-- Rational lower-comparison gates at the negative endpoint after retaining
`1 / 2048` of the half-singular Gram.  The only non-rational entries are the
two aligned `P₄` cross coordinates, controlled together by their structural
sum/difference bounds. -/
private theorem retainedP024MinusLower_gates :
    let q00 := intrinsicStaticMinusEvenLower00 - (1 / 2048 : ℝ) * 3
    let q02 := intrinsicStaticMinusEvenLower02 -
      (1 / 2048 : ℝ) * (1 / 2)
    let q04 := factorTwoIntrinsicFourP45Cross04 (-1) -
      (1 / 2048 : ℝ) * (3 / 20)
    let q22 := intrinsicStaticMinusEvenLower22 -
      (1 / 2048 : ℝ) * (61 / 50)
    let q24 := factorTwoIntrinsicFourP45Cross24 (-1) -
      (1 / 2048 : ℝ) * (19 / 105)
    let q44 := factorTwoIntrinsicP4MinusDiagonalLower -
      (1 / 2048 : ℝ) * (8997 / 11340)
    0 < q00 ∧ 0 < leadingMinorTwo q00 q02 q22 ∧
      0 < symmetricDeterminant q00 q02 q04 q22 q24 q44 := by
  dsimp only
  let q00 := intrinsicStaticMinusEvenLower00 - (1 / 2048 : ℝ) * 3
  let q02 := intrinsicStaticMinusEvenLower02 -
    (1 / 2048 : ℝ) * (1 / 2)
  let q04 := factorTwoIntrinsicFourP45Cross04 (-1) -
    (1 / 2048 : ℝ) * (3 / 20)
  let q22 := intrinsicStaticMinusEvenLower22 -
    (1 / 2048 : ℝ) * (61 / 50)
  let q24 := factorTwoIntrinsicFourP45Cross24 (-1) -
    (1 / 2048 : ℝ) * (19 / 105)
  let q44 := factorTwoIntrinsicP4MinusDiagonalLower -
    (1 / 2048 : ℝ) * (8997 / 11340)
  let A := intrinsicStaticMinusEvenLower00 +
      2 * intrinsicStaticMinusEvenLower02 +
      intrinsicStaticMinusEvenLower22 -
    (1 / 2048 : ℝ) * (261 / 50)
  let X := intrinsicStaticMinusEvenLower00 -
      intrinsicStaticMinusEvenLower22 -
    (1 / 2048 : ℝ) * (89 / 50)
  let C := intrinsicStaticMinusEvenLower00 -
      2 * intrinsicStaticMinusEvenLower02 +
      intrinsicStaticMinusEvenLower22 -
    (1 / 2048 : ℝ) * (161 / 50)
  let S := factorTwoIntrinsicP4MinusCrossSum -
    (1 / 2048 : ℝ) * (139 / 420)
  let D := factorTwoIntrinsicP4MinusCrossDifference -
    (1 / 2048 : ℝ) * (13 / 420)
  let F := factorTwoIntrinsicP4MinusDiagonalLower -
    (1 / 2048 : ℝ) * (8997 / 11340)
  let sl : ℝ := 2927 / 10000 - (1 / 2048 : ℝ) * (139 / 420)
  let s : ℝ := 2931 / 10000 - (1 / 2048 : ℝ) * (139 / 420)
  let dl : ℝ := 662 / 10000 - (1 / 2048 : ℝ) * (13 / 420)
  let d : ℝ := 666 / 10000 - (1 / 2048 : ℝ) * (13 / 420)
  let p : ℝ := A * C - X ^ 2
  let q : ℝ := A * F - s ^ 2
  let r : ℝ := A * d + X * s
  rcases factorTwoIntrinsicP4MinusCross_refined_bounds with
    ⟨hSL0, hSU0, hDL0, hDU0⟩
  have hSL : sl < S := by
    dsimp only [sl, S]
    linarith
  have hS : S < s := by
    dsimp only [s, S]
    linarith
  have hDL : dl < D := by
    dsimp only [dl, D]
    linarith
  have hD : D < d := by
    dsimp only [d, D]
    linarith
  have hA0 : 0 < A := by
    norm_num [A, intrinsicStaticMinusEvenLower00,
      intrinsicStaticMinusEvenLower02, intrinsicStaticMinusEvenLower22]
  have hX0 : 0 < X := by
    norm_num [X, intrinsicStaticMinusEvenLower00,
      intrinsicStaticMinusEvenLower22]
  have hC0 : 0 < C := by
    norm_num [C, intrinsicStaticMinusEvenLower00,
      intrinsicStaticMinusEvenLower02, intrinsicStaticMinusEvenLower22]
  have hS0 : 0 < S := by
    have : 0 < sl := by norm_num [sl]
    exact this.trans hSL
  have hD0 : 0 < D := by
    have : 0 < dl := by norm_num [dl]
    exact this.trans hDL
  have hF0 : 0 < F := by
    norm_num [F, factorTwoIntrinsicP4MinusDiagonalLower]
  have hp0 : 0 < p := by
    norm_num [p, A, X, C, intrinsicStaticMinusEvenLower00,
      intrinsicStaticMinusEvenLower02, intrinsicStaticMinusEvenLower22]
  have hq0 : 0 < q := by
    norm_num [q, A, F, s, intrinsicStaticMinusEvenLower00,
      intrinsicStaticMinusEvenLower02, intrinsicStaticMinusEvenLower22,
      factorTwoIntrinsicP4MinusDiagonalLower]
  have hr0 : 0 < r := by
    norm_num [r, A, X, d, s, intrinsicStaticMinusEvenLower00,
      intrinsicStaticMinusEvenLower02, intrinsicStaticMinusEvenLower22]
  have hrat : r ^ 2 < p * q := by
    norm_num [r, p, q, A, X, C, F, d, s,
      intrinsicStaticMinusEvenLower00, intrinsicStaticMinusEvenLower02,
      intrinsicStaticMinusEvenLower22,
      factorTwoIntrinsicP4MinusDiagonalLower]
  have hSsq : S ^ 2 < s ^ 2 := by
    have hs0 : 0 < s := by norm_num [s]
    nlinarith only [hS, hS0, hs0]
  have hSecond : q < A * F - S ^ 2 := by
    dsimp only [q]
    nlinarith only [hSsq]
  have hAD : A * D < A * d := mul_lt_mul_of_pos_left hD hA0
  have hXS : X * S < X * s := mul_lt_mul_of_pos_left hS hX0
  have hCross : A * D + X * S < r := by
    dsimp only [r]
    linarith only [hAD, hXS]
  have hCross0 : 0 < A * D + X * S := by positivity
  have hCrossSq : (A * D + X * S) ^ 2 < r ^ 2 := by
    nlinarith only [hCross, hCross0, hr0]
  have hProduct : p * q < p * (A * F - S ^ 2) :=
    mul_lt_mul_of_pos_left hSecond hp0
  have hGap :
      0 < (A * C - X ^ 2) * (A * F - S ^ 2) -
        (A * D + X * S) ^ 2 := by
    dsimp only [p] at hProduct hrat
    nlinarith only [hProduct, hCrossSq, hrat]
  have hAligned : 0 < retainedP024AlignedDeterminant A X C S D F := by
    have hid := retainedP024AlignedDeterminant_strongPivot_identity A X C S D F
    have hmul : 0 < 4 * A * retainedP024AlignedDeterminant A X C S D F := by
      rw [hid]
      exact hGap
    exact pos_of_mul_pos_right hmul (by positivity : 0 ≤ 4 * A)
  have hAeq : A = q00 + 2 * q02 + q22 := by
    dsimp only [A, q00, q02, q22]
    ring
  have hXeq : X = q00 - q22 := by
    dsimp only [X, q00, q22]
    ring
  have hCeq : C = q00 - 2 * q02 + q22 := by
    dsimp only [C, q00, q02, q22]
    ring
  have hSeq : S = q04 + q24 := by
    dsimp only [S, q04, q24]
    unfold factorTwoIntrinsicP4MinusCrossSum
    ring
  have hDeq : D = q24 - q04 := by
    dsimp only [D, q04, q24]
    unfold factorTwoIntrinsicP4MinusCrossDifference
    ring
  have hFeq : F = q44 := by rfl
  have hq00 : 0 < q00 := by
    norm_num [q00, intrinsicStaticMinusEvenLower00]
  have hminor : 0 < leadingMinorTwo q00 q02 q22 := by
    norm_num [leadingMinorTwo, q00, q02, q22,
      intrinsicStaticMinusEvenLower00, intrinsicStaticMinusEvenLower02,
      intrinsicStaticMinusEvenLower22]
  have hdetEq :
      retainedP024AlignedDeterminant A X C S D F =
        symmetricDeterminant q00 q02 q04 q22 q24 q44 := by
    rw [hAeq, hXeq, hCeq, hSeq, hDeq, hFeq]
    exact retainedP024AlignedDeterminant_eq_symmetricDeterminant
      q00 q02 q04 q22 q24 q44
  exact ⟨hq00, hminor, hdetEq ▸ hAligned⟩

/-- The negative endpoint is strictly coercive on `P₀/P₂/P₄` after
the retuned `1 / 2048` half-singular retention. -/
theorem factorTwoEndpointChannelPhase_sub_oneDiv2048_halfSingular_pos_minus
    (c0 c2 c4 : ℝ) (hne : c0 ≠ 0 ∨ c2 ≠ 0 ∨ c4 ≠ 0) :
    0 < factorTwoEndpointChannelPhase
          (factorTwoIntrinsicEvenP024Profile c0 c2 c4)
          (0 : ℝ → ℝ) (-1) 0 -
        (1 / 2048 : ℝ) * ((1 / 2 : ℝ) *
          factorTwoPhaseSingularWeightedEnergy
            (factorTwoIntrinsicEvenP024Profile c0 c2 c4)
            (0 : ℝ → ℝ) (-1) 0) := by
  rw [factorTwoEndpointChannelPhase_intrinsicEvenP024_eq_quadratic,
    half_singularWeightedEnergy_intrinsicEvenP024]
  have hgates := retainedP024MinusLower_gates
  have hlower := symmetricQuadratic_pos
    (intrinsicStaticMinusEvenLower00 - (1 / 2048 : ℝ) * 3)
    (intrinsicStaticMinusEvenLower02 - (1 / 2048 : ℝ) * (1 / 2))
    (factorTwoIntrinsicFourP45Cross04 (-1) -
      (1 / 2048 : ℝ) * (3 / 20))
    (intrinsicStaticMinusEvenLower22 - (1 / 2048 : ℝ) * (61 / 50))
    (factorTwoIntrinsicFourP45Cross24 (-1) -
      (1 / 2048 : ℝ) * (19 / 105))
    (factorTwoIntrinsicP4MinusDiagonalLower -
      (1 / 2048 : ℝ) * (8997 / 11340))
    hgates.1 hgates.2.1 hgates.2.2 c0 c2 c4 hne
  have hlower' :
      0 < factorTwoIntrinsicP024MinusLowerQuadratic c0 c2 c4 -
        (1 / 2048 : ℝ) *
          symmetricQuadratic 3 (1 / 2) (3 / 20) (61 / 50)
            (19 / 105) (8997 / 11340) c0 c2 c4 := by
    convert hlower using 1
    unfold factorTwoIntrinsicP024MinusLowerQuadratic symmetricQuadratic
    norm_num
    ring
  have hcompare :=
    factorTwoIntrinsicP024MinusLowerQuadratic_le_exact c0 c2 c4
  nlinarith

/-! ## Exact affine disk interpolation -/

/-- The alternating phase coordinate vanishes identically on the even
`P₀/P₂/P₄` core, so the endpoint quadratic formula holds for every `b`. -/
theorem factorTwoEndpointChannelPhase_intrinsicEvenP024_eq_quadratic_disk
    (c0 c2 c4 a b : ℝ) :
    factorTwoEndpointChannelPhase
        (factorTwoIntrinsicEvenP024Profile c0 c2 c4)
        (0 : ℝ → ℝ) a b =
      symmetricQuadratic
        (factorTwoStructuralPhaseLow00 a)
        (factorTwoStructuralPhaseLow02 a)
        (factorTwoIntrinsicFourP45Cross04 a)
        (factorTwoStructuralPhaseLow22 a)
        (factorTwoIntrinsicFourP45Cross24 a)
        (factorTwoIntrinsicP4PhaseDiagonal a)
        c0 c2 c4 := by
  let w := factorTwoIntrinsicEvenP024Profile c0 c2 c4
  have hAlt : factorTwoCenteredAlternatingCoupling w (0 : ℝ → ℝ) = 0 := by
    simpa only [zero_smul, zero_mul] using
      (factorTwoCenteredAlternatingCoupling_smul_right 0 w w)
  have hzero :=
    factorTwoEndpointChannelPhase_intrinsicEvenP024_eq_quadratic
      c0 c2 c4 a
  change factorTwoEndpointChannelPhase w (0 : ℝ → ℝ) a b = _
  change factorTwoEndpointChannelPhase w (0 : ℝ → ℝ) a 0 = _ at hzero
  unfold factorTwoEndpointChannelPhase at hzero ⊢
  rw [hAlt] at hzero ⊢
  simpa only [mul_zero, add_zero] using hzero

/-- Exact structural coercivity of the retuned retained `P₀/P₂/P₄` pencil
throughout the closed phase disk.  The charged quadratic is the convex
interpolation of its two signed endpoints; no phase subdivision is used. -/
theorem factorTwoEndpointChannelPhase_sub_oneDiv2048_halfSingular_pos_p024_disk
    (c0 c2 c4 a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hne : c0 ≠ 0 ∨ c2 ≠ 0 ∨ c4 ≠ 0) :
    0 < factorTwoEndpointChannelPhase
          (factorTwoIntrinsicEvenP024Profile c0 c2 c4)
          (0 : ℝ → ℝ) a b -
        (1 / 2048 : ℝ) * ((1 / 2 : ℝ) *
          factorTwoPhaseSingularWeightedEnergy
            (factorTwoIntrinsicEvenP024Profile c0 c2 c4)
            (0 : ℝ → ℝ) a b) := by
  let lambda : ℝ := (1 + a) / 2
  let mu : ℝ := (1 - a) / 2
  have haLower : -1 ≤ a := by
    nlinarith [sq_nonneg b, sq_nonneg (a + 1)]
  have haUpper : a ≤ 1 := by
    nlinarith [sq_nonneg b, sq_nonneg (a - 1)]
  have hlambda : 0 ≤ lambda := by
    dsimp only [lambda]
    linarith
  have hmu : 0 ≤ mu := by
    dsimp only [mu]
    linarith
  have hsum : lambda + mu = 1 := by
    dsimp only [lambda, mu]
    ring
  have hPlus :=
    factorTwoEndpointChannelPhase_sub_oneDiv2048_halfSingular_pos_plus
      c0 c2 c4 hne
  have hMinus :=
    factorTwoEndpointChannelPhase_sub_oneDiv2048_halfSingular_pos_minus
      c0 c2 c4 hne
  have hAffine :
      factorTwoEndpointChannelPhase
          (factorTwoIntrinsicEvenP024Profile c0 c2 c4)
          (0 : ℝ → ℝ) a b -
        (1 / 2048 : ℝ) * ((1 / 2 : ℝ) *
          factorTwoPhaseSingularWeightedEnergy
            (factorTwoIntrinsicEvenP024Profile c0 c2 c4)
            (0 : ℝ → ℝ) a b) =
      lambda *
        (factorTwoEndpointChannelPhase
            (factorTwoIntrinsicEvenP024Profile c0 c2 c4)
            (0 : ℝ → ℝ) 1 0 -
          (1 / 2048 : ℝ) * ((1 / 2 : ℝ) *
            factorTwoPhaseSingularWeightedEnergy
              (factorTwoIntrinsicEvenP024Profile c0 c2 c4)
              (0 : ℝ → ℝ) 1 0)) +
      mu *
        (factorTwoEndpointChannelPhase
            (factorTwoIntrinsicEvenP024Profile c0 c2 c4)
            (0 : ℝ → ℝ) (-1) 0 -
          (1 / 2048 : ℝ) * ((1 / 2 : ℝ) *
            factorTwoPhaseSingularWeightedEnergy
              (factorTwoIntrinsicEvenP024Profile c0 c2 c4)
              (0 : ℝ → ℝ) (-1) 0)) := by
    rw [factorTwoEndpointChannelPhase_intrinsicEvenP024_eq_quadratic_disk,
      factorTwoEndpointChannelPhase_intrinsicEvenP024_eq_quadratic_disk,
      factorTwoEndpointChannelPhase_intrinsicEvenP024_eq_quadratic_disk,
      half_singularWeightedEnergy_intrinsicEvenP024,
      half_singularWeightedEnergy_intrinsicEvenP024,
      half_singularWeightedEnergy_intrinsicEvenP024]
    dsimp only [lambda, mu]
    unfold symmetricQuadratic factorTwoStructuralPhaseLow00
      factorTwoStructuralPhaseLow02 factorTwoStructuralPhaseLow22
      factorTwoIntrinsicFourP45Cross04 factorTwoIntrinsicFourP45Cross24
      factorTwoIntrinsicP4PhaseDiagonal
    ring
  rw [hAffine]
  rcases hlambda.eq_or_lt with hlambdaZero | hlambdaPos
  · have hmuOne : mu = 1 := by linarith
    rw [← hlambdaZero, zero_mul, zero_add, hmuOne, one_mul]
    exact hMinus
  · exact add_pos_of_pos_of_nonneg
      (mul_pos hlambdaPos hPlus) (mul_nonneg hmu hMinus.le)

set_option maxHeartbeats 200000

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024Structural
