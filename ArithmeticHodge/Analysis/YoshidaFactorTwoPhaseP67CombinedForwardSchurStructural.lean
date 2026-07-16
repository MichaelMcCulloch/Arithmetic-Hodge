import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67CombinedSchurArithmeticStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67DyadicNineInterpolationStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ForwardHankelRepresenterStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ForwardReducedRepresenterDerivativesStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67ForwardReducedRepresenterBridgeStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67CombinedForwardSchurStructural

open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFactorTwoPhaseP67CombinedSchurArithmeticStructural
open YoshidaFactorTwoPhaseP67DyadicNineInterpolationStructural
open YoshidaFactorTwoPhaseP67ForwardHankelRepresenterStructural
open YoshidaFactorTwoPhaseP67ForwardReducedRepresenterBridgeStructural
open YoshidaFactorTwoPhaseP67ForwardReducedRepresenterDerivativesStructural
open YoshidaFactorTwoPhaseP67ResidualAnalyticSchurStructural
open YoshidaFactorTwoPhaseP67ResidualRegularDecompositionStructural

noncomputable section

/-!
# Combined analytic and forward-Hankel Schur bound

The analytic and forward-Hankel errors occupy the same four low--residual
energy cells.  They therefore have to be combined inside each cell before
the four-row Schur argument is applied.  The first theorem below isolates
that algebra from the representer reduction.  The second theorem feeds the
four reduced representers through the dyadic ninth-order interpolation
bound; its only external inputs are the four exact moment-gap pairing
identities and the four pointwise ninth-derivative envelopes.
-/

/-- The complete analytic plus forward-Hankel half-cross. -/
def factorTwoP67ResidualCombinedForwardMixed
    (p₆ p₇ eR oR : ℝ → ℝ) (a b : ℝ) : ℝ :=
  factorTwoP67ResidualAnalyticMixed p₆ p₇ eR oR a b +
    factorTwoP67ResidualForwardHankelMixed p₆ p₇ eR oR a b

private theorem factorTwoIntrinsicEnergy_smul_real
    (r : ℝ) (w : ℝ → ℝ) :
    factorTwoIntrinsicEnergy (r • w) =
      r ^ 2 * factorTwoIntrinsicEnergy w := by
  unfold factorTwoIntrinsicEnergy
  rw [show (fun x : ℝ ↦ (r • w) x ^ 2) =
      fun x ↦ r ^ 2 * w x ^ 2 by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    ring,
    intervalIntegral.integral_const_mul]

/-- Multiplication of two independently normalized square bounds.  Keeping
this outside the four-row theorem prevents nonlinear normalization from
replaying in the large profile context. -/
private theorem mul_sq_le_mul_of_sq_le
    (q z Q R : ℝ) (hq : q ^ 2 ≤ Q) (hz : z ^ 2 ≤ R)
    (hQ : 0 ≤ Q) :
    (q * z) ^ 2 ≤ Q * R := by
  rw [mul_pow]
  exact mul_le_mul hq hz (sq_nonneg z) hQ

/-- Same-cell Schur assembly once the four actual forward-Hankel pairings
have their normalized square bounds. -/
theorem factorTwoP67ResidualCombinedForwardMixed_sq_le_reserve_mul_of_pairing_sq_bounds
    (eR oR : ℝ → ℝ)
    (heRc : Continuous eR) (hoRc : Continuous oR)
    (heRe : Function.Even eR) (hoRo : Function.Odd oR)
    (c d a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hK₆ :
      (∫ x : ℝ in -1..1,
        eR x * factorTwoForwardHankelK factorTwoCenteredP6 x) ^ 2 ≤
        (1 / 8778792960000000 : ℝ) * 14000 ^ 2 *
          factorTwoIntrinsicEnergy eR)
    (hL₆ :
      (∫ x : ℝ in -1..1,
        oR x * factorTwoForwardHankelL factorTwoCenteredP6 x) ^ 2 ≤
        (1 / 8778792960000000 : ℝ) * 16000 ^ 2 *
          factorTwoIntrinsicEnergy oR)
    (hL₇ :
      (∫ x : ℝ in -1..1,
        eR x * factorTwoForwardHankelL factorTwoCenteredP7 x) ^ 2 ≤
        (1 / 8778792960000000 : ℝ) * 100000 ^ 2 *
          factorTwoIntrinsicEnergy eR)
    (hK₇ :
      (∫ x : ℝ in -1..1,
        oR x * factorTwoForwardHankelK factorTwoCenteredP7 x) ^ 2 ≤
        (1 / 8778792960000000 : ℝ) * 130000 ^ 2 *
          factorTwoIntrinsicEnergy oR) :
    factorTwoP67ResidualCombinedForwardMixed
        (c • factorTwoCenteredP6) (d • factorTwoCenteredP7)
        eR oR a b ^ 2 ≤
      ((1 / 100 : ℝ) *
          (factorTwoIntrinsicEnergy factorTwoCenteredP6 * c ^ 2 +
            factorTwoIntrinsicEnergy factorTwoCenteredP7 * d ^ 2)) *
        ((1 / 250 : ℝ) * factorTwoIntrinsicEnergy eR +
          (1 / 2500 : ℝ) * factorTwoIntrinsicEnergy oR) := by
  let E₆ := factorTwoIntrinsicEnergy factorTwoCenteredP6
  let E₇ := factorTwoIntrinsicEnergy factorTwoCenteredP7
  let Ee := factorTwoIntrinsicEnergy eR
  let Eo := factorTwoIntrinsicEnergy oR
  let x₀ := (1 / 100 : ℝ) * E₆ * c ^ 2
  let x₁ := (1 / 100 : ℝ) * E₇ * d ^ 2
  let y₀ := (1 / 250 : ℝ) * Ee
  let y₁ := (1 / 2500 : ℝ) * Eo

  let A₀₀ := a * factorTwoP67ResidualSymmetricAnalyticBorder
    (c • factorTwoCenteredP6) eR
  let A₀₁ := (b / 2) * factorTwoP67ResidualAlternatingAnalyticBorder
    (c • factorTwoCenteredP6) oR
  let A₁₀ := (b / 2) * factorTwoP67ResidualAlternatingAnalyticBorder
    eR (d • factorTwoCenteredP7)
  let A₁₁ := a * factorTwoP67ResidualSymmetricAnalyticBorder
    (d • factorTwoCenteredP7) oR

  let Iₖ₆ := ∫ x : ℝ in -1..1,
    eR x * factorTwoForwardHankelK factorTwoCenteredP6 x
  let Iₗ₆ := ∫ x : ℝ in -1..1,
    oR x * factorTwoForwardHankelL factorTwoCenteredP6 x
  let Iₗ₇ := ∫ x : ℝ in -1..1,
    eR x * factorTwoForwardHankelL factorTwoCenteredP7 x
  let Iₖ₇ := ∫ x : ℝ in -1..1,
    oR x * factorTwoForwardHankelK factorTwoCenteredP7 x
  let F₀₀ := -(a * c / 4) * Iₖ₆
  let F₀₁ := (b * c / 4) * Iₗ₆
  let F₁₀ := -(b * d / 4) * Iₗ₇
  let F₁₁ := -(a * d / 4) * Iₖ₇

  let z₀₀ := A₀₀ + F₀₀
  let z₀₁ := A₀₁ + F₀₁
  let z₁₀ := A₁₀ + F₁₀
  let z₁₁ := A₁₁ + F₁₁

  have hE₆ : 0 ≤ E₆ := by
    dsimp only [E₆]
    exact factorTwoIntrinsicEnergy_nonneg factorTwoCenteredP6
  have hE₇ : 0 ≤ E₇ := by
    dsimp only [E₇]
    exact factorTwoIntrinsicEnergy_nonneg factorTwoCenteredP7
  have hEe : 0 ≤ Ee := by
    dsimp only [Ee]
    exact factorTwoIntrinsicEnergy_nonneg eR
  have hEo : 0 ≤ Eo := by
    dsimp only [Eo]
    exact factorTwoIntrinsicEnergy_nonneg oR
  have hx₀ : 0 ≤ x₀ := by dsimp only [x₀]; positivity
  have hx₁ : 0 ≤ x₁ := by dsimp only [x₁]; positivity
  have hy₀ : 0 ≤ y₀ := by dsimp only [y₀]; positivity
  have hy₁ : 0 ≤ y₁ := by dsimp only [y₁]; positivity
  have ha : a ^ 2 ≤ 1 := by nlinarith [sq_nonneg b]
  have hb : b ^ 2 ≤ 1 := by nlinarith [sq_nonneg a]
  have hbquarter : (b / 2) ^ 2 ≤ (1 / 4 : ℝ) := by nlinarith

  have hp₆Energy :
      factorTwoIntrinsicEnergy (c • factorTwoCenteredP6) = c ^ 2 * E₆ := by
    simpa only [E₆] using
      factorTwoIntrinsicEnergy_smul_real c factorTwoCenteredP6
  have hp₇Energy :
      factorTwoIntrinsicEnergy (d • factorTwoCenteredP7) = d ^ 2 * E₇ := by
    simpa only [E₇] using
      factorTwoIntrinsicEnergy_smul_real d factorTwoCenteredP7

  have hsym₆ := factorTwoP67ResidualSymmetricAnalyticBorder_sq_le_energy_mul
    (c • factorTwoCenteredP6) eR
    (continuous_factorTwoCenteredP6.const_smul c) heRc
  have hsym₇ := factorTwoP67ResidualSymmetricAnalyticBorder_sq_le_energy_mul
    (d • factorTwoCenteredP7) oR
    (continuous_factorTwoCenteredP7.const_smul d) hoRc
  have halt₆ := factorTwoP67ResidualAlternatingAnalyticBorder_sq_le_energy_mul
    (c • factorTwoCenteredP6) oR
    (continuous_factorTwoCenteredP6.const_smul c) hoRc
    (even_factorTwoCenteredP6.const_smul c) hoRo
  have halt₇ := factorTwoP67ResidualAlternatingAnalyticBorder_sq_le_energy_mul
    eR (d • factorTwoCenteredP7) heRc
    (continuous_factorTwoCenteredP7.const_smul d)
    heRe (odd_factorTwoCenteredP7.const_smul d)
  rw [hp₆Energy] at hsym₆ halt₆
  rw [hp₇Energy] at hsym₇ halt₇

  have hA₀₀ : A₀₀ ^ 2 ≤
      factorTwoP67AnalyticWeight₀₀ * x₀ * y₀ := by
    have hrow : 0 ≤
        (9 / 64000000 : ℝ) * (c ^ 2 * E₆) * Ee := by positivity
    have hscaled := mul_sq_le_mul_of_sq_le a
      (factorTwoP67ResidualSymmetricAnalyticBorder
        (c • factorTwoCenteredP6) eR)
      1 ((9 / 64000000 : ℝ) * (c ^ 2 * E₆) * Ee)
      ha hsym₆ (by norm_num)
    calc
      A₀₀ ^ 2 ≤ (9 / 64000000 : ℝ) * (c ^ 2 * E₆) * Ee := by
        simpa only [A₀₀, one_mul] using hscaled
      _ = factorTwoP67AnalyticWeight₀₀ * x₀ * y₀ := by
        dsimp only [x₀, y₀]
        norm_num [factorTwoP67AnalyticWeight₀₀]
        ring

  have hA₀₁ : A₀₁ ^ 2 ≤
      factorTwoP67AnalyticWeight₀₁ * x₀ * y₁ := by
    have hrow : 0 ≤
        (1 / 250000 : ℝ) * (c ^ 2 * E₆) * Eo := by positivity
    have hscaled := mul_sq_le_mul_of_sq_le (b / 2)
      (factorTwoP67ResidualAlternatingAnalyticBorder
        (c • factorTwoCenteredP6) oR)
      (1 / 4) ((1 / 250000 : ℝ) * (c ^ 2 * E₆) * Eo)
      hbquarter halt₆ (by norm_num)
    calc
      A₀₁ ^ 2 ≤ (1 / 4 : ℝ) *
          ((1 / 250000 : ℝ) * (c ^ 2 * E₆) * Eo) := by
        simpa only [A₀₁] using hscaled
      _ = factorTwoP67AnalyticWeight₀₁ * x₀ * y₁ := by
        dsimp only [x₀, y₁]
        norm_num [factorTwoP67AnalyticWeight₀₁]
        ring

  have hA₁₀ : A₁₀ ^ 2 ≤
      factorTwoP67AnalyticWeight₁₀ * x₁ * y₀ := by
    have hrow : 0 ≤
        (1 / 250000 : ℝ) * Ee * (d ^ 2 * E₇) := by positivity
    have hscaled := mul_sq_le_mul_of_sq_le (b / 2)
      (factorTwoP67ResidualAlternatingAnalyticBorder
        eR (d • factorTwoCenteredP7))
      (1 / 4) ((1 / 250000 : ℝ) * Ee * (d ^ 2 * E₇))
      hbquarter halt₇ (by norm_num)
    calc
      A₁₀ ^ 2 ≤ (1 / 4 : ℝ) *
          ((1 / 250000 : ℝ) * Ee * (d ^ 2 * E₇)) := by
        simpa only [A₁₀] using hscaled
      _ = factorTwoP67AnalyticWeight₁₀ * x₁ * y₀ := by
        dsimp only [x₁, y₀]
        norm_num [factorTwoP67AnalyticWeight₁₀]
        ring

  have hA₁₁ : A₁₁ ^ 2 ≤
      factorTwoP67AnalyticWeight₁₁ * x₁ * y₁ := by
    have hrow : 0 ≤
        (9 / 64000000 : ℝ) * (d ^ 2 * E₇) * Eo := by positivity
    have hscaled := mul_sq_le_mul_of_sq_le a
      (factorTwoP67ResidualSymmetricAnalyticBorder
        (d • factorTwoCenteredP7) oR)
      1 ((9 / 64000000 : ℝ) * (d ^ 2 * E₇) * Eo)
      ha hsym₇ (by norm_num)
    calc
      A₁₁ ^ 2 ≤ (9 / 64000000 : ℝ) * (d ^ 2 * E₇) * Eo := by
        simpa only [A₁₁, one_mul] using hscaled
      _ = factorTwoP67AnalyticWeight₁₁ * x₁ * y₁ := by
        dsimp only [x₁, y₁]
        norm_num [factorTwoP67AnalyticWeight₁₁]
        ring

  have hIₖ₆ : Iₖ₆ ^ 2 ≤
      (1 / 8778792960000000 : ℝ) * 14000 ^ 2 * Ee := by
    simpa only [Iₖ₆, Ee] using hK₆
  have hIₗ₆ : Iₗ₆ ^ 2 ≤
      (1 / 8778792960000000 : ℝ) * 16000 ^ 2 * Eo := by
    simpa only [Iₗ₆, Eo] using hL₆
  have hIₗ₇ : Iₗ₇ ^ 2 ≤
      (1 / 8778792960000000 : ℝ) * 100000 ^ 2 * Ee := by
    simpa only [Iₗ₇, Ee] using hL₇
  have hIₖ₇ : Iₖ₇ ^ 2 ≤
      (1 / 8778792960000000 : ℝ) * 130000 ^ 2 * Eo := by
    simpa only [Iₖ₇, Eo] using hK₇

  have hac : (-(a * c / 4)) ^ 2 ≤ (1 / 16 : ℝ) * c ^ 2 := by
    have h := mul_le_mul_of_nonneg_right ha (sq_nonneg c)
    calc
      (-(a * c / 4)) ^ 2 = (1 / 16 : ℝ) * (a ^ 2 * c ^ 2) := by ring
      _ ≤ (1 / 16 : ℝ) * (1 * c ^ 2) :=
        mul_le_mul_of_nonneg_left h (by norm_num)
      _ = (1 / 16 : ℝ) * c ^ 2 := by ring
  have hbc : (b * c / 4) ^ 2 ≤ (1 / 16 : ℝ) * c ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hb (sq_nonneg c)
    calc
      (b * c / 4) ^ 2 = (1 / 16 : ℝ) * (b ^ 2 * c ^ 2) := by ring
      _ ≤ (1 / 16 : ℝ) * (1 * c ^ 2) :=
        mul_le_mul_of_nonneg_left h (by norm_num)
      _ = (1 / 16 : ℝ) * c ^ 2 := by ring
  have hbd : (-(b * d / 4)) ^ 2 ≤ (1 / 16 : ℝ) * d ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hb (sq_nonneg d)
    calc
      (-(b * d / 4)) ^ 2 = (1 / 16 : ℝ) * (b ^ 2 * d ^ 2) := by ring
      _ ≤ (1 / 16 : ℝ) * (1 * d ^ 2) :=
        mul_le_mul_of_nonneg_left h (by norm_num)
      _ = (1 / 16 : ℝ) * d ^ 2 := by ring
  have had : (-(a * d / 4)) ^ 2 ≤ (1 / 16 : ℝ) * d ^ 2 := by
    have h := mul_le_mul_of_nonneg_right ha (sq_nonneg d)
    calc
      (-(a * d / 4)) ^ 2 = (1 / 16 : ℝ) * (a ^ 2 * d ^ 2) := by ring
      _ ≤ (1 / 16 : ℝ) * (1 * d ^ 2) :=
        mul_le_mul_of_nonneg_left h (by norm_num)
      _ = (1 / 16 : ℝ) * d ^ 2 := by ring

  have hF₀₀ : F₀₀ ^ 2 ≤
      factorTwoP67ForwardWeight₀₀ * x₀ * y₀ := by
    have hmul := mul_sq_le_mul_of_sq_le (-(a * c / 4)) Iₖ₆
      ((1 / 16 : ℝ) * c ^ 2)
      ((1 / 8778792960000000 : ℝ) * 14000 ^ 2 * Ee)
      hac hIₖ₆ (by positivity)
    calc
      F₀₀ ^ 2 ≤ ((1 / 16 : ℝ) * c ^ 2) *
          ((1 / 8778792960000000 : ℝ) * 14000 ^ 2 * Ee) := by
        simpa only [F₀₀] using hmul
      _ = ((1 / 16 : ℝ) * (1 / 8778792960000000) * 14000 ^ 2) *
          c ^ 2 * Ee := by ring
      _ = (factorTwoP67ForwardWeight₀₀ * (1 / 100) * (2 / 13) *
          (1 / 250)) * c ^ 2 * Ee := by
        rw [factorTwoP67ForwardWeight₀₀_normalization]
      _ = factorTwoP67ForwardWeight₀₀ * x₀ * y₀ := by
        dsimp only [x₀, y₀, E₆]
        rw [factorTwoCenteredP6_energy]
        ring

  have hF₀₁ : F₀₁ ^ 2 ≤
      factorTwoP67ForwardWeight₀₁ * x₀ * y₁ := by
    have hmul := mul_sq_le_mul_of_sq_le (b * c / 4) Iₗ₆
      ((1 / 16 : ℝ) * c ^ 2)
      ((1 / 8778792960000000 : ℝ) * 16000 ^ 2 * Eo)
      hbc hIₗ₆ (by positivity)
    calc
      F₀₁ ^ 2 ≤ ((1 / 16 : ℝ) * c ^ 2) *
          ((1 / 8778792960000000 : ℝ) * 16000 ^ 2 * Eo) := by
        simpa only [F₀₁] using hmul
      _ = ((1 / 16 : ℝ) * (1 / 8778792960000000) * 16000 ^ 2) *
          c ^ 2 * Eo := by ring
      _ = (factorTwoP67ForwardWeight₀₁ * (1 / 100) * (2 / 13) *
          (1 / 2500)) * c ^ 2 * Eo := by
        rw [factorTwoP67ForwardWeight₀₁_normalization]
      _ = factorTwoP67ForwardWeight₀₁ * x₀ * y₁ := by
        dsimp only [x₀, y₁, E₆]
        rw [factorTwoCenteredP6_energy]
        ring

  have hF₁₀ : F₁₀ ^ 2 ≤
      factorTwoP67ForwardWeight₁₀ * x₁ * y₀ := by
    have hmul := mul_sq_le_mul_of_sq_le (-(b * d / 4)) Iₗ₇
      ((1 / 16 : ℝ) * d ^ 2)
      ((1 / 8778792960000000 : ℝ) * 100000 ^ 2 * Ee)
      hbd hIₗ₇ (by positivity)
    calc
      F₁₀ ^ 2 ≤ ((1 / 16 : ℝ) * d ^ 2) *
          ((1 / 8778792960000000 : ℝ) * 100000 ^ 2 * Ee) := by
        simpa only [F₁₀] using hmul
      _ = ((1 / 16 : ℝ) * (1 / 8778792960000000) * 100000 ^ 2) *
          d ^ 2 * Ee := by ring
      _ = (factorTwoP67ForwardWeight₁₀ * (1 / 100) * (2 / 15) *
          (1 / 250)) * d ^ 2 * Ee := by
        rw [factorTwoP67ForwardWeight₁₀_normalization]
      _ = factorTwoP67ForwardWeight₁₀ * x₁ * y₀ := by
        dsimp only [x₁, y₀, E₇]
        rw [factorTwoCenteredP7_energy]
        ring

  have hF₁₁ : F₁₁ ^ 2 ≤
      factorTwoP67ForwardWeight₁₁ * x₁ * y₁ := by
    have hmul := mul_sq_le_mul_of_sq_le (-(a * d / 4)) Iₖ₇
      ((1 / 16 : ℝ) * d ^ 2)
      ((1 / 8778792960000000 : ℝ) * 130000 ^ 2 * Eo)
      had hIₖ₇ (by positivity)
    calc
      F₁₁ ^ 2 ≤ ((1 / 16 : ℝ) * d ^ 2) *
          ((1 / 8778792960000000 : ℝ) * 130000 ^ 2 * Eo) := by
        simpa only [F₁₁] using hmul
      _ = ((1 / 16 : ℝ) * (1 / 8778792960000000) * 130000 ^ 2) *
          d ^ 2 * Eo := by ring
      _ = (factorTwoP67ForwardWeight₁₁ * (1 / 100) * (2 / 15) *
          (1 / 2500)) * d ^ 2 * Eo := by
        rw [factorTwoP67ForwardWeight₁₁_normalization]
      _ = factorTwoP67ForwardWeight₁₁ * x₁ * y₁ := by
        dsimp only [x₁, y₁, E₇]
        rw [factorTwoCenteredP7_energy]
        ring

  have hz₀₀Base := sq_add_le_combined_cell
    A₀₀ F₀₀ factorTwoP67AnalyticWeight₀₀ factorTwoP67ForwardWeight₀₀
    (x₀ * y₀) factorTwoP67YoungParameter₀₀
    (by norm_num [factorTwoP67YoungParameter₀₀])
    (by simpa only [mul_assoc] using hA₀₀)
    (by simpa only [mul_assoc] using hF₀₀)
  rw [factorTwoP67CombinedWeight₀₀_eq_young] at hz₀₀Base
  have hz₀₀ : z₀₀ ^ 2 ≤
      factorTwoP67CombinedWeight₀₀ * x₀ * y₀ := by
    dsimp only [z₀₀]
    simpa only [mul_assoc] using hz₀₀Base

  have hz₀₁Base := sq_add_le_combined_cell
    A₀₁ F₀₁ factorTwoP67AnalyticWeight₀₁ factorTwoP67ForwardWeight₀₁
    (x₀ * y₁) factorTwoP67YoungParameter₀₁
    (by norm_num [factorTwoP67YoungParameter₀₁])
    (by simpa only [mul_assoc] using hA₀₁)
    (by simpa only [mul_assoc] using hF₀₁)
  rw [factorTwoP67CombinedWeight₀₁_eq_young] at hz₀₁Base
  have hz₀₁ : z₀₁ ^ 2 ≤
      factorTwoP67CombinedWeight₀₁ * x₀ * y₁ := by
    dsimp only [z₀₁]
    simpa only [mul_assoc] using hz₀₁Base

  have hz₁₀Base := sq_add_le_combined_cell
    A₁₀ F₁₀ factorTwoP67AnalyticWeight₁₀ factorTwoP67ForwardWeight₁₀
    (x₁ * y₀) factorTwoP67YoungParameter₁₀
    (by norm_num [factorTwoP67YoungParameter₁₀])
    (by simpa only [mul_assoc] using hA₁₀)
    (by simpa only [mul_assoc] using hF₁₀)
  rw [factorTwoP67CombinedWeight₁₀_eq_young] at hz₁₀Base
  have hz₁₀ : z₁₀ ^ 2 ≤
      factorTwoP67CombinedWeight₁₀ * x₁ * y₀ := by
    dsimp only [z₁₀]
    simpa only [mul_assoc] using hz₁₀Base

  have hz₁₁Base := sq_add_le_combined_cell
    A₁₁ F₁₁ factorTwoP67AnalyticWeight₁₁ factorTwoP67ForwardWeight₁₁
    (x₁ * y₁) factorTwoP67YoungParameter₁₁
    (by norm_num [factorTwoP67YoungParameter₁₁])
    (by simpa only [mul_assoc] using hA₁₁)
    (by simpa only [mul_assoc] using hF₁₁)
  rw [factorTwoP67CombinedWeight₁₁_eq_young] at hz₁₁Base
  have hz₁₁ : z₁₁ ^ 2 ≤
      factorTwoP67CombinedWeight₁₁ * x₁ * y₁ := by
    dsimp only [z₁₁]
    simpa only [mul_assoc] using hz₁₁Base

  have hschur := four_row_schur_of_normalized_sq_bounds
    factorTwoP67CombinedWeight₀₀ factorTwoP67CombinedWeight₀₁
    factorTwoP67CombinedWeight₁₀ factorTwoP67CombinedWeight₁₁
    z₀₀ z₀₁ z₁₀ z₁₁ x₀ x₁ y₀ y₁
    (by norm_num [factorTwoP67CombinedWeight₀₀])
    (by norm_num [factorTwoP67CombinedWeight₀₁])
    (by norm_num [factorTwoP67CombinedWeight₁₀])
    (by norm_num [factorTwoP67CombinedWeight₁₁])
    factorTwoP67CombinedWeight_sum_le_one
    hx₀ hx₁ hy₀ hy₁ hz₀₀ hz₀₁ hz₁₀ hz₁₁
  have hforward := factorTwoP67ResidualForwardHankelMixed_scaled_P67_eq_pairings
    eR oR heRc hoRc c d a b
  calc
    factorTwoP67ResidualCombinedForwardMixed
        (c • factorTwoCenteredP6) (d • factorTwoCenteredP7)
        eR oR a b ^ 2 =
      (z₀₀ + z₀₁ + z₁₀ + z₁₁) ^ 2 := by
        unfold factorTwoP67ResidualCombinedForwardMixed
        rw [hforward]
        dsimp only [z₀₀, z₀₁, z₁₀, z₁₁,
          A₀₀, A₀₁, A₁₀, A₁₁,
          F₀₀, F₀₁, F₁₀, F₁₁,
          Iₖ₆, Iₗ₆, Iₗ₇, Iₖ₇]
        unfold factorTwoP67ResidualAnalyticMixed
        ring
    _ ≤ (x₀ + x₁) * (y₀ + y₁) := hschur
    _ = ((1 / 100 : ℝ) *
          (factorTwoIntrinsicEnergy factorTwoCenteredP6 * c ^ 2 +
            factorTwoIntrinsicEnergy factorTwoCenteredP7 * d ^ 2)) *
        ((1 / 250 : ℝ) * factorTwoIntrinsicEnergy eR +
          (1 / 2500 : ℝ) * factorTwoIntrinsicEnergy oR) := by
      dsimp only [x₀, x₁, y₀, y₁, E₆, E₇, Ee, Eo]
      ring

/-- Dyadic wrapper for the same-cell theorem.  Once the four reduction
equalities and four derivative envelopes are supplied, no further analytic
or scalar estimate is needed. -/
theorem factorTwoP67ResidualCombinedForwardMixed_sq_le_reserve_mul_of_reduced_pairings
    (eR oR : ℝ → ℝ)
    (heRc : Continuous eR) (hoRc : Continuous oR)
    (heRe : Function.Even eR) (hoRo : Function.Odd oR)
    (heLow : centeredLegendreMomentsVanishBelow eR 9)
    (hoLow : centeredLegendreMomentsVanishBelow oR 9)
    (c d a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hK₆reduce :
      (∫ x : ℝ in -1..1,
        eR x * factorTwoForwardHankelK factorTwoCenteredP6 x) =
      ∫ x : ℝ in -1..1, eR x * factorTwoForwardKP6 x)
    (hL₆reduce :
      (∫ x : ℝ in -1..1,
        oR x * factorTwoForwardHankelL factorTwoCenteredP6 x) =
      ∫ x : ℝ in -1..1, oR x * factorTwoForwardLP6 x)
    (hL₇reduce :
      (∫ x : ℝ in -1..1,
        eR x * factorTwoForwardHankelL factorTwoCenteredP7 x) =
      ∫ x : ℝ in -1..1, eR x * factorTwoForwardLP7 x)
    (hK₇reduce :
      (∫ x : ℝ in -1..1,
        oR x * factorTwoForwardHankelK factorTwoCenteredP7 x) =
      ∫ x : ℝ in -1..1, oR x * factorTwoForwardKP7 x)
    (hKP₆ : ∀ x ∈ Icc (-1 : ℝ) 1,
      |iteratedDerivWithin 9 factorTwoForwardKP6 (Icc (-1 : ℝ) 1) x| ≤
        14000)
    (hLP₆ : ∀ x ∈ Icc (-1 : ℝ) 1,
      |iteratedDerivWithin 9 factorTwoForwardLP6 (Icc (-1 : ℝ) 1) x| ≤
        16000)
    (hLP₇ : ∀ x ∈ Icc (-1 : ℝ) 1,
      |iteratedDerivWithin 9 factorTwoForwardLP7 (Icc (-1 : ℝ) 1) x| ≤
        100000)
    (hKP₇ : ∀ x ∈ Icc (-1 : ℝ) 1,
      |iteratedDerivWithin 9 factorTwoForwardKP7 (Icc (-1 : ℝ) 1) x| ≤
        130000) :
    factorTwoP67ResidualCombinedForwardMixed
        (c • factorTwoCenteredP6) (d • factorTwoCenteredP7)
        eR oR a b ^ 2 ≤
      ((1 / 100 : ℝ) *
          (factorTwoIntrinsicEnergy factorTwoCenteredP6 * c ^ 2 +
            factorTwoIntrinsicEnergy factorTwoCenteredP7 * d ^ 2)) *
        ((1 / 250 : ℝ) * factorTwoIntrinsicEnergy eR +
          (1 / 2500 : ℝ) * factorTwoIntrinsicEnergy oR) := by
  have hK₆reduced := sq_intervalIntegral_mul_le_dyadicNineRemainder
    eR factorTwoForwardKP6 heRc continuousOn_factorTwoForwardKP6
    contDiffOn_factorTwoForwardKP6 heLow 14000 hKP₆
  have hL₆reduced := sq_intervalIntegral_mul_le_dyadicNineRemainder
    oR factorTwoForwardLP6 hoRc continuousOn_factorTwoForwardLP6
    contDiffOn_factorTwoForwardLP6 hoLow 16000 hLP₆
  have hL₇reduced := sq_intervalIntegral_mul_le_dyadicNineRemainder
    eR factorTwoForwardLP7 heRc continuousOn_factorTwoForwardLP7
    contDiffOn_factorTwoForwardLP7 heLow 100000 hLP₇
  have hK₇reduced := sq_intervalIntegral_mul_le_dyadicNineRemainder
    oR factorTwoForwardKP7 hoRc continuousOn_factorTwoForwardKP7
    contDiffOn_factorTwoForwardKP7 hoLow 130000 hKP₇
  apply factorTwoP67ResidualCombinedForwardMixed_sq_le_reserve_mul_of_pairing_sq_bounds
    eR oR heRc hoRc heRe hoRo c d a b hab
  · rw [hK₆reduce]
    exact hK₆reduced
  · rw [hL₆reduce]
    exact hL₆reduced
  · rw [hL₇reduce]
    exact hL₇reduced
  · rw [hK₇reduce]
    exact hK₇reduced

/-- Production form: the exact polynomial-reduction bridges and the four
certified ninth-derivative envelopes discharge all hypotheses of the dyadic
wrapper. -/
theorem factorTwoP67ResidualCombinedForwardMixed_sq_le_reserve_mul
    (eR oR : ℝ → ℝ)
    (heRc : Continuous eR) (hoRc : Continuous oR)
    (heRe : Function.Even eR) (hoRo : Function.Odd oR)
    (heLow : centeredLegendreMomentsVanishBelow eR 9)
    (hoLow : centeredLegendreMomentsVanishBelow oR 9)
    (c d a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    factorTwoP67ResidualCombinedForwardMixed
        (c • factorTwoCenteredP6) (d • factorTwoCenteredP7)
        eR oR a b ^ 2 ≤
      ((1 / 100 : ℝ) *
          (factorTwoIntrinsicEnergy factorTwoCenteredP6 * c ^ 2 +
            factorTwoIntrinsicEnergy factorTwoCenteredP7 * d ^ 2)) *
        ((1 / 250 : ℝ) * factorTwoIntrinsicEnergy eR +
          (1 / 2500 : ℝ) * factorTwoIntrinsicEnergy oR) := by
  apply factorTwoP67ResidualCombinedForwardMixed_sq_le_reserve_mul_of_reduced_pairings
    eR oR heRc hoRc heRe hoRo heLow hoLow c d a b hab
  · exact integral_mul_factorTwoForwardHankelK_P6_eq_reduced eR heRc heLow
  · exact integral_mul_factorTwoForwardHankelL_P6_eq_reduced oR hoRc hoLow
  · exact integral_mul_factorTwoForwardHankelL_P7_eq_reduced eR heRc heLow
  · exact integral_mul_factorTwoForwardHankelK_P7_eq_reduced oR hoRc hoLow
  · exact abs_iteratedDerivWithin_nine_factorTwoForwardKP6_le
  · exact abs_iteratedDerivWithin_nine_factorTwoForwardLP6_le
  · exact abs_iteratedDerivWithin_nine_factorTwoForwardLP7_le
  · exact abs_iteratedDerivWithin_nine_factorTwoForwardKP7_le

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP67CombinedForwardSchurStructural
