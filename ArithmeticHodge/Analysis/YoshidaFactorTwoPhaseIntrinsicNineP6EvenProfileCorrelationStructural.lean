import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenCorrelationStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4EndpointProfile
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4PerturbationStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenProfileCorrelationStructural

noncomputable section

open CenteredEndpointCorrelation
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicNineP6EvenCorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseIntrinsicSixP4CorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4EndpointProfile
open YoshidaFactorTwoPhaseIntrinsicSixP4PerturbationStructural
open YoshidaFactorTwoPhaseIntrinsicSixSchurReduction
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFactorTwoPhaseLowSchur

/-!
# The exact `P0/P2/P4/P6` even correlation profile

This file packages the first four centered even Legendre modes as one genuine
profile.  Its correlation and degree-six pole-free kernel integral are exact
quadratic identities.  In particular, adding `P6` to the old `P0/P2/P4`
polynomial Gram creates only the `P0-P6` degree-six boundary term.
-/

/-- The intrinsic even profile through degree six. -/
def factorTwoIntrinsicEvenP0246Profile
    (c0 c2 c4 c6 : ℝ) : ℝ → ℝ :=
  factorTwoIntrinsicEvenP024Profile c0 c2 c4 +
    c6 • factorTwoCenteredP6

theorem continuous_factorTwoIntrinsicEvenP0246Profile
    (c0 c2 c4 c6 : ℝ) :
    Continuous (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) := by
  unfold factorTwoIntrinsicEvenP0246Profile
    factorTwoIntrinsicEvenP024Profile factorTwoIntrinsicSixEvenTail
  exact ((continuous_factorTwoEvenStructuralLowProfile c0 c2).add
    (continuous_const.mul continuous_factorTwoCenteredP4)).add
      (continuous_factorTwoCenteredP6.const_smul c6)

theorem even_factorTwoIntrinsicEvenP0246Profile
    (c0 c2 c4 c6 : ℝ) :
    Function.Even (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) := by
  intro x
  unfold factorTwoIntrinsicEvenP0246Profile
    factorTwoIntrinsicEvenP024Profile factorTwoEvenStructuralLowProfile
    factorTwoIntrinsicSixEvenTail centeredEvenP0 centeredEvenP2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [even_factorTwoCenteredP4, even_factorTwoCenteredP6]
  ring

/-- Exact overlap correlation of the old `P0/P2/P4` core. -/
theorem centeredEndpointCorrelation_intrinsicEvenP024
    (c0 c2 c4 t : ℝ) :
    centeredEndpointCorrelation
        (factorTwoIntrinsicEvenP024Profile c0 c2 c4) t =
      c0 ^ 2 * evenStructuralCorrelation00 t +
        2 * c0 * c2 * evenStructuralCorrelation02 t +
        c2 ^ 2 * evenStructuralCorrelation22 t +
        2 * c0 * c4 * factorTwoIntrinsicP4Correlation04 t +
        2 * c2 * c4 * factorTwoIntrinsicP4Correlation24 t +
        c4 ^ 2 * factorTwoIntrinsicP4Correlation44 t := by
  let p : ℝ → ℝ := factorTwoEvenStructuralLowProfile c0 c2
  let r : ℝ → ℝ := c4 • factorTwoCenteredP4
  have hp : Continuous p := by
    simpa only [p] using continuous_factorTwoEvenStructuralLowProfile c0 c2
  have hr : Continuous r := continuous_factorTwoCenteredP4.const_smul c4
  have hp0 : Continuous centeredEvenP0 := by
    unfold centeredEvenP0
    fun_prop
  have hp2 : Continuous centeredEvenP2 := by
    unfold centeredEvenP2
    fun_prop
  have hw : factorTwoIntrinsicEvenP024Profile c0 c2 c4 = p + r := by
    funext x
    unfold factorTwoIntrinsicEvenP024Profile factorTwoIntrinsicSixEvenTail p r
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
      c0 ^ 2 * evenStructuralCorrelation00 t +
        2 * c0 * c2 * evenStructuralCorrelation02 t +
        c2 ^ 2 * evenStructuralCorrelation22 t by
      simpa only [p] using hpCorr,
    hcross, hrCorr]
  ring

/-- Exact `P0/P2/P4` against `P6` correlation row. -/
theorem factorTwoCenteredCorrelationBilinear_intrinsicEvenP024_p6
    (c0 c2 c4 t : ℝ) :
    factorTwoCenteredCorrelationBilinear
        (factorTwoIntrinsicEvenP024Profile c0 c2 c4)
        factorTwoCenteredP6 t =
      c0 * factorTwoIntrinsicP6Correlation06 t +
        c2 * factorTwoIntrinsicP6Correlation26 t +
        c4 * factorTwoIntrinsicP6Correlation46 t := by
  let p : ℝ → ℝ := factorTwoEvenStructuralLowProfile c0 c2
  let r : ℝ → ℝ := c4 • factorTwoCenteredP4
  have hp : Continuous p := by
    simpa only [p] using continuous_factorTwoEvenStructuralLowProfile c0 c2
  have hr : Continuous r := continuous_factorTwoCenteredP4.const_smul c4
  have h6 := continuous_factorTwoCenteredP6
  have hp0 : Continuous centeredEvenP0 := by
    unfold centeredEvenP0
    fun_prop
  have hp2 : Continuous centeredEvenP2 := by
    unfold centeredEvenP2
    fun_prop
  have hw : factorTwoIntrinsicEvenP024Profile c0 c2 c4 = p + r := by
    funext x
    unfold factorTwoIntrinsicEvenP024Profile factorTwoIntrinsicSixEvenTail p r
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have houter : factorTwoCenteredCorrelationBilinear (p + r)
      factorTwoCenteredP6 t =
      factorTwoCenteredCorrelationBilinear p factorTwoCenteredP6 t +
        factorTwoCenteredCorrelationBilinear r factorTwoCenteredP6 t := by
    unfold factorTwoCenteredCorrelationBilinear
    rw [factorTwoCenteredCrossCorrelation_add_left p r factorTwoCenteredP6
        hp hr h6 t,
      factorTwoCenteredCrossCorrelation_add_right factorTwoCenteredP6 p r
        h6 hp hr t]
    ring
  have hlow : factorTwoCenteredCorrelationBilinear p factorTwoCenteredP6 t =
      c0 * factorTwoIntrinsicP6Correlation06 t +
        c2 * factorTwoIntrinsicP6Correlation26 t := by
    have hadd : factorTwoCenteredCorrelationBilinear
        (c0 • centeredEvenP0 + c2 • centeredEvenP2)
        factorTwoCenteredP6 t =
      factorTwoCenteredCorrelationBilinear (c0 • centeredEvenP0)
          factorTwoCenteredP6 t +
        factorTwoCenteredCorrelationBilinear (c2 • centeredEvenP2)
          factorTwoCenteredP6 t := by
      unfold factorTwoCenteredCorrelationBilinear
      rw [factorTwoCenteredCrossCorrelation_add_left
          (c0 • centeredEvenP0) (c2 • centeredEvenP2)
          factorTwoCenteredP6 (hp0.const_smul c0) (hp2.const_smul c2) h6 t,
        factorTwoCenteredCrossCorrelation_add_right
          factorTwoCenteredP6 (c0 • centeredEvenP0) (c2 • centeredEvenP2)
          h6 (hp0.const_smul c0) (hp2.const_smul c2) t]
      ring
    have h0 : factorTwoCenteredCorrelationBilinear
        (c0 • centeredEvenP0) factorTwoCenteredP6 t =
        c0 * factorTwoCenteredCorrelationBilinear
          centeredEvenP0 factorTwoCenteredP6 t := by
      simpa using factorTwoCenteredCorrelationBilinear_smul_smul
        c0 1 centeredEvenP0 factorTwoCenteredP6 t
    have h2 : factorTwoCenteredCorrelationBilinear
        (c2 • centeredEvenP2) factorTwoCenteredP6 t =
        c2 * factorTwoCenteredCorrelationBilinear
          centeredEvenP2 factorTwoCenteredP6 t := by
      simpa using factorTwoCenteredCorrelationBilinear_smul_smul
        c2 1 centeredEvenP2 factorTwoCenteredP6 t
    rw [show p = c0 • centeredEvenP0 + c2 • centeredEvenP2 by
        simpa only [p] using factorTwoEvenStructuralLowProfile_eq_smul_add c0 c2,
      hadd, h0, h2,
      factorTwoCenteredCorrelationBilinear_p0_p6,
      factorTwoCenteredCorrelationBilinear_p2_p6]
  have h4 : factorTwoCenteredCorrelationBilinear
      (c4 • factorTwoCenteredP4) factorTwoCenteredP6 t =
      c4 * factorTwoCenteredCorrelationBilinear
        factorTwoCenteredP4 factorTwoCenteredP6 t := by
    simpa using factorTwoCenteredCorrelationBilinear_smul_smul
      c4 1 factorTwoCenteredP4 factorTwoCenteredP6 t
  rw [hw, houter, hlow, show r = c4 • factorTwoCenteredP4 by rfl,
    h4,
    factorTwoCenteredCorrelationBilinear_p4_p6]

/-- Full exact autocorrelation of the intrinsic four-mode even profile. -/
theorem centeredEndpointCorrelation_intrinsicEvenP0246
    (c0 c2 c4 c6 t : ℝ) :
    centeredEndpointCorrelation
        (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) t =
      c0 ^ 2 * evenStructuralCorrelation00 t +
        2 * c0 * c2 * evenStructuralCorrelation02 t +
        c2 ^ 2 * evenStructuralCorrelation22 t +
        2 * c0 * c4 * factorTwoIntrinsicP4Correlation04 t +
        2 * c2 * c4 * factorTwoIntrinsicP4Correlation24 t +
        c4 ^ 2 * factorTwoIntrinsicP4Correlation44 t +
        2 * c0 * c6 * factorTwoIntrinsicP6Correlation06 t +
        2 * c2 * c6 * factorTwoIntrinsicP6Correlation26 t +
        2 * c4 * c6 * factorTwoIntrinsicP6Correlation46 t +
        c6 ^ 2 * factorTwoIntrinsicP6Correlation66 t := by
  let p : ℝ → ℝ := factorTwoIntrinsicEvenP024Profile c0 c2 c4
  let r : ℝ → ℝ := c6 • factorTwoCenteredP6
  have hp : Continuous p := by
    dsimp only [p]
    unfold factorTwoIntrinsicEvenP024Profile factorTwoIntrinsicSixEvenTail
    exact (continuous_factorTwoEvenStructuralLowProfile c0 c2).add
      (continuous_const.mul continuous_factorTwoCenteredP4)
  have hr : Continuous r := continuous_factorTwoCenteredP6.const_smul c6
  have hw : factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6 = p + r := rfl
  have hpr : factorTwoCenteredCorrelationBilinear p r t =
      c6 * factorTwoCenteredCorrelationBilinear p factorTwoCenteredP6 t := by
    rw [show r = c6 • factorTwoCenteredP6 by rfl]
    simpa using factorTwoCenteredCorrelationBilinear_smul_smul
      1 c6 p factorTwoCenteredP6 t
  rw [hw, centeredEndpointCorrelation_add p r hp hr,
    centeredEndpointCorrelation_intrinsicEvenP024,
    hpr,
    factorTwoCenteredCorrelationBilinear_intrinsicEvenP024_p6,
    ← factorTwoCenteredCorrelationBilinear_self,
    show r = c6 • factorTwoCenteredP6 by rfl,
    factorTwoCenteredCorrelationBilinear_smul_smul,
    factorTwoCenteredCorrelationBilinear_p6_p6]
  ring

/-- Exact diagonal `L2` energy of the four mutually orthogonal modes. -/
theorem factorTwoIntrinsicEnergy_intrinsicEvenP0246
    (c0 c2 c4 c6 : ℝ) :
    factorTwoIntrinsicEnergy
        (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) =
      2 * c0 ^ 2 + (2 / 5 : ℝ) * c2 ^ 2 +
        (2 / 9 : ℝ) * c4 ^ 2 + (2 / 13 : ℝ) * c6 ^ 2 := by
  unfold factorTwoIntrinsicEnergy
  rw [← centeredEndpointCorrelation_zero,
    centeredEndpointCorrelation_intrinsicEvenP0246]
  norm_num [evenStructuralCorrelation00, evenStructuralCorrelation02,
    evenStructuralCorrelation22, factorTwoIntrinsicP4Correlation04,
    factorTwoIntrinsicP4Correlation24, factorTwoIntrinsicP4Correlation44,
    factorTwoIntrinsicP6Correlation06, factorTwoIntrinsicP6Correlation26,
    factorTwoIntrinsicP6Correlation46, factorTwoIntrinsicP6Correlation66]
  ring

/-! ## Exact degree-six polynomial-kernel Gram -/

theorem evenStructuralCorrelation00_moments :
    (∫ t : ℝ in 0..2, evenStructuralCorrelation00 t) = 2 ∧
      (∫ t : ℝ in 0..2, t ^ 2 * evenStructuralCorrelation00 t) = 4 / 3 ∧
      (∫ t : ℝ in 0..2, t ^ 4 * evenStructuralCorrelation00 t) = 32 / 15 ∧
      (∫ t : ℝ in 0..2, t ^ 6 * evenStructuralCorrelation00 t) = 32 / 7 := by
  constructor
  · unfold evenStructuralCorrelation00
    ring_nf
    repeat rw [intervalIntegral.integral_sub
      (Continuous.intervalIntegrable (by fun_prop) 0 2)
      (Continuous.intervalIntegrable (by fun_prop) 0 2)]
    repeat rw [intervalIntegral.integral_const]
    norm_num
  · constructor
    · unfold evenStructuralCorrelation00
      ring_nf
      repeat rw [intervalIntegral.integral_sub
        (Continuous.intervalIntegrable (by fun_prop) 0 2)
        (Continuous.intervalIntegrable (by fun_prop) 0 2)]
      repeat rw [intervalIntegral.integral_mul_const]
      repeat rw [YoshidaEndpointOcticPotential.integral_pow_nat]
      norm_num
    · constructor
      · unfold evenStructuralCorrelation00
        ring_nf
        repeat rw [intervalIntegral.integral_sub
          (Continuous.intervalIntegrable (by fun_prop) 0 2)
          (Continuous.intervalIntegrable (by fun_prop) 0 2)]
        repeat rw [intervalIntegral.integral_mul_const]
        repeat rw [YoshidaEndpointOcticPotential.integral_pow_nat]
        norm_num
      · unfold evenStructuralCorrelation00
        ring_nf
        repeat rw [intervalIntegral.integral_sub
          (Continuous.intervalIntegrable (by fun_prop) 0 2)
          (Continuous.intervalIntegrable (by fun_prop) 0 2)]
        repeat rw [intervalIntegral.integral_mul_const]
        repeat rw [YoshidaEndpointOcticPotential.integral_pow_nat]
        norm_num

theorem evenStructuralCorrelation02_moments :
    (∫ t : ℝ in 0..2, evenStructuralCorrelation02 t) = 0 ∧
      (∫ t : ℝ in 0..2, t ^ 2 * evenStructuralCorrelation02 t) = 4 / 15 ∧
      (∫ t : ℝ in 0..2, t ^ 4 * evenStructuralCorrelation02 t) = 16 / 21 ∧
      (∫ t : ℝ in 0..2, t ^ 6 * evenStructuralCorrelation02 t) = 32 / 15 := by
  constructor
  · unfold evenStructuralCorrelation02
    ring_nf
    repeat rw [intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) 0 2)
      (Continuous.intervalIntegrable (by fun_prop) 0 2)]
    repeat rw [intervalIntegral.integral_mul_const]
    repeat rw [integral_pow]
    rw [show (fun x : ℝ ↦ -x) = fun x ↦ (-1 : ℝ) * x ^ 1 by
      funext x
      ring, intervalIntegral.integral_const_mul, integral_pow]
    norm_num
  · constructor
    · unfold evenStructuralCorrelation02
      ring_nf
      repeat rw [intervalIntegral.integral_add
        (Continuous.intervalIntegrable (by fun_prop) 0 2)
        (Continuous.intervalIntegrable (by fun_prop) 0 2)]
      repeat rw [intervalIntegral.integral_mul_const]
      repeat rw [integral_pow]
      norm_num
    · constructor
      · unfold evenStructuralCorrelation02
        ring_nf
        repeat rw [intervalIntegral.integral_add
          (Continuous.intervalIntegrable (by fun_prop) 0 2)
          (Continuous.intervalIntegrable (by fun_prop) 0 2)]
        repeat rw [intervalIntegral.integral_mul_const]
        repeat rw [integral_pow]
        norm_num
      · unfold evenStructuralCorrelation02
        ring_nf
        repeat rw [intervalIntegral.integral_add
          (Continuous.intervalIntegrable (by fun_prop) 0 2)
          (Continuous.intervalIntegrable (by fun_prop) 0 2)]
        repeat rw [intervalIntegral.integral_mul_const]
        repeat rw [integral_pow]
        norm_num

theorem evenStructuralCorrelation22_moments :
    (∫ t : ℝ in 0..2, evenStructuralCorrelation22 t) = 0 ∧
      (∫ t : ℝ in 0..2, t ^ 2 * evenStructuralCorrelation22 t) = 0 ∧
      (∫ t : ℝ in 0..2, t ^ 4 * evenStructuralCorrelation22 t) = 16 / 75 ∧
      (∫ t : ℝ in 0..2, t ^ 6 * evenStructuralCorrelation22 t) = 32 / 35 := by
  constructor
  · unfold evenStructuralCorrelation22
    ring_nf
    repeat rw [intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) 0 2)
      (Continuous.intervalIntegrable (by fun_prop) 0 2)]
    repeat rw [intervalIntegral.integral_mul_const]
    repeat rw [integral_pow]
    rw [intervalIntegral.integral_sub
      (Continuous.intervalIntegrable (by fun_prop) 0 2)
      (Continuous.intervalIntegrable (by fun_prop) 0 2),
      intervalIntegral.integral_const,
      show (fun x : ℝ ↦ x) = fun x ↦ (1 : ℝ) * x ^ 1 by
        funext x
        ring,
      intervalIntegral.integral_const_mul, integral_pow]
    norm_num
  · constructor
    · unfold evenStructuralCorrelation22
      ring_nf
      repeat rw [intervalIntegral.integral_add
        (Continuous.intervalIntegrable (by fun_prop) 0 2)
        (Continuous.intervalIntegrable (by fun_prop) 0 2)]
      repeat rw [intervalIntegral.integral_mul_const]
      repeat rw [integral_pow]
      norm_num
    · constructor
      · unfold evenStructuralCorrelation22
        ring_nf
        repeat rw [intervalIntegral.integral_add
          (Continuous.intervalIntegrable (by fun_prop) 0 2)
          (Continuous.intervalIntegrable (by fun_prop) 0 2)]
        repeat rw [intervalIntegral.integral_mul_const]
        repeat rw [integral_pow]
        norm_num
      · unfold evenStructuralCorrelation22
        ring_nf
        repeat rw [intervalIntegral.integral_add
          (Continuous.intervalIntegrable (by fun_prop) 0 2)
          (Continuous.intervalIntegrable (by fun_prop) 0 2)]
        repeat rw [intervalIntegral.integral_mul_const]
        repeat rw [integral_pow]
        norm_num

private theorem integral_evenPolynomial6_mul
    (a₀ a₂ a₄ a₆ : ℝ) (C : ℝ → ℝ) (hC : Continuous C) :
    (∫ t : ℝ in 0..2,
      (a₀ + a₂ * t ^ 2 + a₄ * t ^ 4 + a₆ * t ^ 6) * C t) =
      a₀ * (∫ t : ℝ in 0..2, C t) +
        a₂ * (∫ t : ℝ in 0..2, t ^ 2 * C t) +
        a₄ * (∫ t : ℝ in 0..2, t ^ 4 * C t) +
        a₆ * (∫ t : ℝ in 0..2, t ^ 6 * C t) := by
  have h0 : IntervalIntegrable C volume 0 2 := hC.intervalIntegrable 0 2
  have h2 : IntervalIntegrable (fun t : ℝ ↦ t ^ 2 * C t)
      volume 0 2 := ((continuous_id.pow 2).mul hC).intervalIntegrable 0 2
  have h4 : IntervalIntegrable (fun t : ℝ ↦ t ^ 4 * C t)
      volume 0 2 := ((continuous_id.pow 4).mul hC).intervalIntegrable 0 2
  have h6 : IntervalIntegrable (fun t : ℝ ↦ t ^ 6 * C t)
      volume 0 2 := ((continuous_id.pow 6).mul hC).intervalIntegrable 0 2
  rw [show (fun t : ℝ ↦
      (a₀ + a₂ * t ^ 2 + a₄ * t ^ 4 + a₆ * t ^ 6) * C t) =
    fun t ↦ a₀ * C t + a₂ * (t ^ 2 * C t) +
      a₄ * (t ^ 4 * C t) + a₆ * (t ^ 6 * C t) by
    funext t
    ring,
    intervalIntegral.integral_add
      (((h0.const_mul a₀).add (h2.const_mul a₂)).add (h4.const_mul a₄))
      (h6.const_mul a₆),
    intervalIntegral.integral_add
      ((h0.const_mul a₀).add (h2.const_mul a₂)) (h4.const_mul a₄),
    intervalIntegral.integral_add (h0.const_mul a₀) (h2.const_mul a₂)]
  repeat rw [intervalIntegral.integral_const_mul]

/-- Exact degree-six kernel entries on the old `P0/P2` core. -/
theorem integral_poleFreeKernelPolynomial6_mul_evenStructuralCorrelations :
    (∫ t : ℝ in 0..2,
      poleFreeKernelPolynomial6 t * evenStructuralCorrelation00 t) =
        2 * poleFreeCoeff0 yoshidaEndpointA +
          (4 / 3 : ℝ) * poleFreeCoeff2 yoshidaEndpointA +
          (32 / 15 : ℝ) * poleFreeCoeff4 yoshidaEndpointA +
          (32 / 7 : ℝ) * poleFreeCoeff6 yoshidaEndpointA ∧
      (∫ t : ℝ in 0..2,
        poleFreeKernelPolynomial6 t * evenStructuralCorrelation02 t) =
          (4 / 15 : ℝ) * poleFreeCoeff2 yoshidaEndpointA +
            (16 / 21 : ℝ) * poleFreeCoeff4 yoshidaEndpointA +
            (32 / 15 : ℝ) * poleFreeCoeff6 yoshidaEndpointA ∧
      (∫ t : ℝ in 0..2,
        poleFreeKernelPolynomial6 t * evenStructuralCorrelation22 t) =
          (16 / 75 : ℝ) * poleFreeCoeff4 yoshidaEndpointA +
            (32 / 35 : ℝ) * poleFreeCoeff6 yoshidaEndpointA := by
  have h00 := evenStructuralCorrelation00_moments
  have h02 := evenStructuralCorrelation02_moments
  have h22 := evenStructuralCorrelation22_moments
  constructor
  · rw [show (fun t : ℝ ↦
        poleFreeKernelPolynomial6 t * evenStructuralCorrelation00 t) =
      fun t ↦
        (poleFreeCoeff0 yoshidaEndpointA +
          poleFreeCoeff2 yoshidaEndpointA * t ^ 2 +
          poleFreeCoeff4 yoshidaEndpointA * t ^ 4 +
          poleFreeCoeff6 yoshidaEndpointA * t ^ 6) *
            evenStructuralCorrelation00 t by
      funext t
      rw [poleFreeKernelPolynomial6_expansion],
      integral_evenPolynomial6_mul _ _ _ _ _
        (by unfold evenStructuralCorrelation00; fun_prop),
      h00.1, h00.2.1, h00.2.2.1, h00.2.2.2]
    ring
  · constructor
    · rw [show (fun t : ℝ ↦
          poleFreeKernelPolynomial6 t * evenStructuralCorrelation02 t) =
        fun t ↦
          (poleFreeCoeff0 yoshidaEndpointA +
            poleFreeCoeff2 yoshidaEndpointA * t ^ 2 +
            poleFreeCoeff4 yoshidaEndpointA * t ^ 4 +
            poleFreeCoeff6 yoshidaEndpointA * t ^ 6) *
              evenStructuralCorrelation02 t by
        funext t
        rw [poleFreeKernelPolynomial6_expansion],
        integral_evenPolynomial6_mul _ _ _ _ _
          (by unfold evenStructuralCorrelation02; fun_prop),
        h02.1, h02.2.1, h02.2.2.1, h02.2.2.2]
      ring
    · rw [show (fun t : ℝ ↦
          poleFreeKernelPolynomial6 t * evenStructuralCorrelation22 t) =
        fun t ↦
          (poleFreeCoeff0 yoshidaEndpointA +
            poleFreeCoeff2 yoshidaEndpointA * t ^ 2 +
            poleFreeCoeff4 yoshidaEndpointA * t ^ 4 +
            poleFreeCoeff6 yoshidaEndpointA * t ^ 6) *
              evenStructuralCorrelation22 t by
        funext t
        rw [poleFreeKernelPolynomial6_expansion],
        integral_evenPolynomial6_mul _ _ _ _ _
          (by unfold evenStructuralCorrelation22; fun_prop),
        h22.1, h22.2.1, h22.2.2.1, h22.2.2.2]
      ring

/-- Exact degree-six kernel entries in the new `P6` row. -/
theorem integral_poleFreeKernelPolynomial6_mul_factorTwoIntrinsicP6Correlations :
    (∫ t : ℝ in 0..2,
      poleFreeKernelPolynomial6 t * factorTwoIntrinsicP6Correlation06 t) =
        poleFreeCoeff6 yoshidaEndpointA * (32 / 3003) ∧
      (∫ t : ℝ in 0..2,
        poleFreeKernelPolynomial6 t * factorTwoIntrinsicP6Correlation26 t) = 0 ∧
      (∫ t : ℝ in 0..2,
        poleFreeKernelPolynomial6 t * factorTwoIntrinsicP6Correlation46 t) = 0 ∧
      (∫ t : ℝ in 0..2,
        poleFreeKernelPolynomial6 t * factorTwoIntrinsicP6Correlation66 t) = 0 := by
  have h06 := factorTwoIntrinsicP6Correlation06_moments
  have h26 := factorTwoIntrinsicP6Correlation26_moments
  have h46 := factorTwoIntrinsicP6Correlation46_moments
  have h66 := factorTwoIntrinsicP6Correlation66_moments
  constructor
  · rw [show (fun t : ℝ ↦
        poleFreeKernelPolynomial6 t * factorTwoIntrinsicP6Correlation06 t) =
      fun t ↦
        (poleFreeCoeff0 yoshidaEndpointA +
          poleFreeCoeff2 yoshidaEndpointA * t ^ 2 +
          poleFreeCoeff4 yoshidaEndpointA * t ^ 4 +
          poleFreeCoeff6 yoshidaEndpointA * t ^ 6) *
            factorTwoIntrinsicP6Correlation06 t by
      funext t
      rw [poleFreeKernelPolynomial6_expansion],
      integral_evenPolynomial6_mul _ _ _ _ _
        continuous_factorTwoIntrinsicP6Correlation06,
      h06.1, h06.2.1, h06.2.2.1, h06.2.2.2]
    ring
  · constructor
    · rw [show (fun t : ℝ ↦
          poleFreeKernelPolynomial6 t * factorTwoIntrinsicP6Correlation26 t) =
        fun t ↦
          (poleFreeCoeff0 yoshidaEndpointA +
            poleFreeCoeff2 yoshidaEndpointA * t ^ 2 +
            poleFreeCoeff4 yoshidaEndpointA * t ^ 4 +
            poleFreeCoeff6 yoshidaEndpointA * t ^ 6) *
              factorTwoIntrinsicP6Correlation26 t by
        funext t
        rw [poleFreeKernelPolynomial6_expansion],
        integral_evenPolynomial6_mul _ _ _ _ _
          continuous_factorTwoIntrinsicP6Correlation26,
        h26.1, h26.2.1, h26.2.2.1, h26.2.2.2]
      ring
    · constructor
      · rw [show (fun t : ℝ ↦
            poleFreeKernelPolynomial6 t * factorTwoIntrinsicP6Correlation46 t) =
          fun t ↦
            (poleFreeCoeff0 yoshidaEndpointA +
              poleFreeCoeff2 yoshidaEndpointA * t ^ 2 +
              poleFreeCoeff4 yoshidaEndpointA * t ^ 4 +
              poleFreeCoeff6 yoshidaEndpointA * t ^ 6) *
                factorTwoIntrinsicP6Correlation46 t by
          funext t
          rw [poleFreeKernelPolynomial6_expansion],
          integral_evenPolynomial6_mul _ _ _ _ _
            continuous_factorTwoIntrinsicP6Correlation46,
          h46.1, h46.2.1, h46.2.2.1, h46.2.2.2]
        ring
      · rw [show (fun t : ℝ ↦
            poleFreeKernelPolynomial6 t * factorTwoIntrinsicP6Correlation66 t) =
          fun t ↦
            (poleFreeCoeff0 yoshidaEndpointA +
              poleFreeCoeff2 yoshidaEndpointA * t ^ 2 +
              poleFreeCoeff4 yoshidaEndpointA * t ^ 4 +
              poleFreeCoeff6 yoshidaEndpointA * t ^ 6) *
                factorTwoIntrinsicP6Correlation66 t by
          funext t
          rw [poleFreeKernelPolynomial6_expansion],
          integral_evenPolynomial6_mul _ _ _ _ _
            continuous_factorTwoIntrinsicP6Correlation66,
          h66.1, h66.2.1, h66.2.2.1, h66.2.2.2]
        ring

/-- The exact degree-six polynomial-kernel Gram on the old `P0/P2/P4`
profile. -/
def factorTwoIntrinsicEvenP024PolynomialKernelGram
    (c0 c2 c4 : ℝ) : ℝ :=
  c0 ^ 2 *
      (2 * poleFreeCoeff0 yoshidaEndpointA +
        (4 / 3 : ℝ) * poleFreeCoeff2 yoshidaEndpointA +
        (32 / 15 : ℝ) * poleFreeCoeff4 yoshidaEndpointA +
        (32 / 7 : ℝ) * poleFreeCoeff6 yoshidaEndpointA) +
    2 * c0 * c2 *
      ((4 / 15 : ℝ) * poleFreeCoeff2 yoshidaEndpointA +
        (16 / 21 : ℝ) * poleFreeCoeff4 yoshidaEndpointA +
        (32 / 15 : ℝ) * poleFreeCoeff6 yoshidaEndpointA) +
    c2 ^ 2 *
      ((16 / 75 : ℝ) * poleFreeCoeff4 yoshidaEndpointA +
        (32 / 35 : ℝ) * poleFreeCoeff6 yoshidaEndpointA) +
    2 * c0 * c4 *
      (poleFreeCoeff4 yoshidaEndpointA * (16 / 315) +
        poleFreeCoeff6 yoshidaEndpointA * (32 / 99)) +
    2 * c2 * c4 *
      (poleFreeCoeff6 yoshidaEndpointA * (32 / 315))

/-- Adding `P6` to the `P0/P2/P4` profile changes the degree-six kernel Gram
by exactly the `P0-P6` boundary entry.  Every `P2-P6`, `P4-P6`, and `P6-P6`
contribution vanishes. -/
theorem integral_poleFreeKernelPolynomial6_mul_intrinsicEvenP0246Correlation
    (c0 c2 c4 c6 : ℝ) :
    (∫ t : ℝ in 0..2,
      poleFreeKernelPolynomial6 t *
        centeredEndpointCorrelation
          (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) t) =
      factorTwoIntrinsicEvenP024PolynomialKernelGram c0 c2 c4 +
        2 * c0 * c6 *
          (poleFreeCoeff6 yoshidaEndpointA * (32 / 3003)) := by
  have hlow :=
    integral_poleFreeKernelPolynomial6_mul_evenStructuralCorrelations
  have h4 :=
    integral_poleFreeKernelPolynomial6_mul_factorTwoIntrinsicP4Correlations
  have h6 :=
    integral_poleFreeKernelPolynomial6_mul_factorTwoIntrinsicP6Correlations
  rw [show (fun t : ℝ ↦ poleFreeKernelPolynomial6 t *
      centeredEndpointCorrelation
        (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) t) =
    fun t ↦
      c0 ^ 2 * (poleFreeKernelPolynomial6 t * evenStructuralCorrelation00 t) +
      2 * c0 * c2 *
        (poleFreeKernelPolynomial6 t * evenStructuralCorrelation02 t) +
      c2 ^ 2 * (poleFreeKernelPolynomial6 t * evenStructuralCorrelation22 t) +
      2 * c0 * c4 *
        (poleFreeKernelPolynomial6 t * factorTwoIntrinsicP4Correlation04 t) +
      2 * c2 * c4 *
        (poleFreeKernelPolynomial6 t * factorTwoIntrinsicP4Correlation24 t) +
      c4 ^ 2 *
        (poleFreeKernelPolynomial6 t * factorTwoIntrinsicP4Correlation44 t) +
      2 * c0 * c6 *
        (poleFreeKernelPolynomial6 t * factorTwoIntrinsicP6Correlation06 t) +
      2 * c2 * c6 *
        (poleFreeKernelPolynomial6 t * factorTwoIntrinsicP6Correlation26 t) +
      2 * c4 * c6 *
        (poleFreeKernelPolynomial6 t * factorTwoIntrinsicP6Correlation46 t) +
      c6 ^ 2 *
        (poleFreeKernelPolynomial6 t * factorTwoIntrinsicP6Correlation66 t) by
    funext t
    rw [centeredEndpointCorrelation_intrinsicEvenP0246]
    ring]
  have hK := continuous_poleFreeKernelPolynomial6
  have h00I : IntervalIntegrable
      (fun t : ℝ ↦ poleFreeKernelPolynomial6 t * evenStructuralCorrelation00 t)
      volume 0 2 := (hK.mul (by
        unfold evenStructuralCorrelation00
        fun_prop)).intervalIntegrable 0 2
  have h02I : IntervalIntegrable
      (fun t : ℝ ↦ poleFreeKernelPolynomial6 t * evenStructuralCorrelation02 t)
      volume 0 2 := (hK.mul (by
        unfold evenStructuralCorrelation02
        fun_prop)).intervalIntegrable 0 2
  have h22I : IntervalIntegrable
      (fun t : ℝ ↦ poleFreeKernelPolynomial6 t * evenStructuralCorrelation22 t)
      volume 0 2 := (hK.mul (by
        unfold evenStructuralCorrelation22
        fun_prop)).intervalIntegrable 0 2
  have h04I : IntervalIntegrable
      (fun t : ℝ ↦ poleFreeKernelPolynomial6 t *
        factorTwoIntrinsicP4Correlation04 t) volume 0 2 :=
    (hK.mul continuous_factorTwoIntrinsicP4Correlation04).intervalIntegrable 0 2
  have h24I : IntervalIntegrable
      (fun t : ℝ ↦ poleFreeKernelPolynomial6 t *
        factorTwoIntrinsicP4Correlation24 t) volume 0 2 :=
    (hK.mul continuous_factorTwoIntrinsicP4Correlation24).intervalIntegrable 0 2
  have h44I : IntervalIntegrable
      (fun t : ℝ ↦ poleFreeKernelPolynomial6 t *
        factorTwoIntrinsicP4Correlation44 t) volume 0 2 :=
    (hK.mul continuous_factorTwoIntrinsicP4Correlation44).intervalIntegrable 0 2
  have h06I : IntervalIntegrable
      (fun t : ℝ ↦ poleFreeKernelPolynomial6 t *
        factorTwoIntrinsicP6Correlation06 t) volume 0 2 :=
    (hK.mul continuous_factorTwoIntrinsicP6Correlation06).intervalIntegrable 0 2
  have h26I : IntervalIntegrable
      (fun t : ℝ ↦ poleFreeKernelPolynomial6 t *
        factorTwoIntrinsicP6Correlation26 t) volume 0 2 :=
    (hK.mul continuous_factorTwoIntrinsicP6Correlation26).intervalIntegrable 0 2
  have h46I : IntervalIntegrable
      (fun t : ℝ ↦ poleFreeKernelPolynomial6 t *
        factorTwoIntrinsicP6Correlation46 t) volume 0 2 :=
    (hK.mul continuous_factorTwoIntrinsicP6Correlation46).intervalIntegrable 0 2
  have h66I : IntervalIntegrable
      (fun t : ℝ ↦ poleFreeKernelPolynomial6 t *
        factorTwoIntrinsicP6Correlation66 t) volume 0 2 :=
    (hK.mul continuous_factorTwoIntrinsicP6Correlation66).intervalIntegrable 0 2
  let i0 := h00I.const_mul (c0 ^ 2)
  let i1 := h02I.const_mul (2 * c0 * c2)
  let i2 := h22I.const_mul (c2 ^ 2)
  let i3 := h04I.const_mul (2 * c0 * c4)
  let i4 := h24I.const_mul (2 * c2 * c4)
  let i5 := h44I.const_mul (c4 ^ 2)
  let i6 := h06I.const_mul (2 * c0 * c6)
  let i7 := h26I.const_mul (2 * c2 * c6)
  let i8 := h46I.const_mul (2 * c4 * c6)
  let i9 := h66I.const_mul (c6 ^ 2)
  rw [intervalIntegral.integral_add
      ((((((((i0.add i1).add i2).add i3).add i4).add i5).add i6).add i7).add i8) i9,
    intervalIntegral.integral_add
      (((((((i0.add i1).add i2).add i3).add i4).add i5).add i6).add i7) i8,
    intervalIntegral.integral_add
      ((((((i0.add i1).add i2).add i3).add i4).add i5).add i6) i7,
    intervalIntegral.integral_add
      (((((i0.add i1).add i2).add i3).add i4).add i5) i6,
    intervalIntegral.integral_add
      ((((i0.add i1).add i2).add i3).add i4) i5,
    intervalIntegral.integral_add
      (((i0.add i1).add i2).add i3) i4,
    intervalIntegral.integral_add ((i0.add i1).add i2) i3,
    intervalIntegral.integral_add (i0.add i1) i2,
    intervalIntegral.integral_add i0 i1]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [hlow.1, hlow.2.1, hlow.2.2,
    h4.1, h4.2.1, h4.2.2,
    h6.1, h6.2.1, h6.2.2.1, h6.2.2.2]
  unfold factorTwoIntrinsicEvenP024PolynomialKernelGram
  ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenProfileCorrelationStructural
