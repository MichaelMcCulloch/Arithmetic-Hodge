import ArithmeticHodge.Analysis.TwoByTwoSchur
import ArithmeticHodge.Analysis.YoshidaEndpointEvenFullPolarization
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSingularSquare

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSingularWeightedCauchyStructural

open UnitIntervalLogEnergyAffine
open YoshidaEndpointEvenFullPolarization
open YoshidaEndpointPotentialBound
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseEnvelope
open YoshidaFactorTwoPhaseSingularSquare

noncomputable section

/-!
# Weighted Cauchy estimate for the general phase singular square

For a fixed disk phase `(a,b)`, the completed singular square is a positive
quadratic form in the pair of real profiles.  This file exposes its exact
polarization before integrating against `dr / r`.  The resulting Cauchy
estimate retains the constant mode and, unlike the profile-static pole
square, applies to the genuine two-parameter phase used by the production
low--tail decomposition.
-/

/-- Polarization of the positive-distance part of the singular square. -/
def factorTwoPhasePositiveDistanceMixedIntegrand
    (u₁ v₁ u₂ v₂ : ℝ → ℝ) (r x : ℝ) : ℝ :=
  (u₁ (r + x) - u₁ x) * (u₂ (r + x) - u₂ x) +
    (v₁ (r + x) - v₁ x) * (v₂ (r + x) - v₂ x)

/-- Polarization of the completed endpoint square. -/
def factorTwoPhaseEndpointMixedIntegrand
    (u₁ v₁ u₂ v₂ : ℝ → ℝ) (a b r x : ℝ) : ℝ :=
  (u₁ (2 - r + x) - (a * u₁ x + b * v₁ x) / 2) *
      (u₂ (2 - r + x) - (a * u₂ x + b * v₂ x) / 2) +
    (v₁ (2 - r + x) - (-b * u₁ x + a * v₁ x) / 2) *
      (v₂ (2 - r + x) - (-b * u₂ x + a * v₂ x) / 2) +
    (1 - (a ^ 2 + b ^ 2) / 4) *
      (u₁ x * u₂ x + v₁ x * v₂ x)

/-- Exact quadratic expansion of the positive-distance integrand. -/
theorem factorTwoPhasePositiveDistance_linearCombination_eq
    (u₁ v₁ u₂ v₂ : ℝ → ℝ) (r x c d : ℝ) :
    ((c * u₁ (r + x) + d * u₂ (r + x)) -
          (c * u₁ x + d * u₂ x)) ^ 2 +
        ((c * v₁ (r + x) + d * v₂ (r + x)) -
          (c * v₁ x + d * v₂ x)) ^ 2 =
      c ^ 2 *
          ((u₁ (r + x) - u₁ x) ^ 2 +
            (v₁ (r + x) - v₁ x) ^ 2) +
        2 * c * d *
          factorTwoPhasePositiveDistanceMixedIntegrand
            u₁ v₁ u₂ v₂ r x +
        d ^ 2 *
          ((u₂ (r + x) - u₂ x) ^ 2 +
            (v₂ (r + x) - v₂ x) ^ 2) := by
  unfold factorTwoPhasePositiveDistanceMixedIntegrand
  ring

/-- Exact quadratic expansion of the endpoint completion. -/
theorem factorTwoPhaseEndpointSquare_linearCombination_eq
    (u₁ v₁ u₂ v₂ : ℝ → ℝ) (a b r x c d : ℝ) :
    factorTwoPhaseEndpointSquare
        (fun y ↦ c * u₁ y + d * u₂ y)
        (fun y ↦ c * v₁ y + d * v₂ y) a b r x =
      c ^ 2 * factorTwoPhaseEndpointSquare u₁ v₁ a b r x +
        2 * c * d *
          factorTwoPhaseEndpointMixedIntegrand
            u₁ v₁ u₂ v₂ a b r x +
        d ^ 2 * factorTwoPhaseEndpointSquare u₂ v₂ a b r x := by
  unfold factorTwoPhaseEndpointSquare factorTwoPhaseEndpointMixedIntegrand
  ring

/-- Polarization of the complete fixed-distance singular numerator. -/
def factorTwoPhaseSingularMixedNumerator
    (u₁ v₁ u₂ v₂ : ℝ → ℝ) (a b r : ℝ) : ℝ :=
  (∫ x : ℝ in -1..1 - r,
      factorTwoPhasePositiveDistanceMixedIntegrand
        u₁ v₁ u₂ v₂ r x) +
    ∫ x : ℝ in -1..-1 + r,
      factorTwoPhaseEndpointMixedIntegrand
        u₁ v₁ u₂ v₂ a b r x

private theorem continuous_factorTwoPhasePositiveDistanceMixedIntegrand
    (u₁ v₁ u₂ v₂ : ℝ → ℝ)
    (hu₁ : Continuous u₁) (hv₁ : Continuous v₁)
    (hu₂ : Continuous u₂) (hv₂ : Continuous v₂)
    (r : ℝ) :
    Continuous
      (factorTwoPhasePositiveDistanceMixedIntegrand
        u₁ v₁ u₂ v₂ r) := by
  unfold factorTwoPhasePositiveDistanceMixedIntegrand
  fun_prop

private theorem continuous_factorTwoPhaseEndpointMixedIntegrand
    (u₁ v₁ u₂ v₂ : ℝ → ℝ)
    (hu₁ : Continuous u₁) (hv₁ : Continuous v₁)
    (hu₂ : Continuous u₂) (hv₂ : Continuous v₂)
    (a b r : ℝ) :
    Continuous
      (factorTwoPhaseEndpointMixedIntegrand
        u₁ v₁ u₂ v₂ a b r) := by
  unfold factorTwoPhaseEndpointMixedIntegrand
  fun_prop

/-- Exact quadratic expansion of the complete singular numerator. -/
theorem factorTwoPhaseSingularSquareNumerator_linearCombination_eq
    (u₁ v₁ u₂ v₂ : ℝ → ℝ)
    (hu₁ : Continuous u₁) (hv₁ : Continuous v₁)
    (hu₂ : Continuous u₂) (hv₂ : Continuous v₂)
    (a b r c d : ℝ) :
    factorTwoPhaseSingularSquareNumerator
        (fun y ↦ c * u₁ y + d * u₂ y)
        (fun y ↦ c * v₁ y + d * v₂ y) a b r =
      c ^ 2 * factorTwoPhaseSingularSquareNumerator u₁ v₁ a b r +
        2 * c * d *
          factorTwoPhaseSingularMixedNumerator
            u₁ v₁ u₂ v₂ a b r +
        d ^ 2 * factorTwoPhaseSingularSquareNumerator u₂ v₂ a b r := by
  have hPos₁ : IntervalIntegrable
      (fun x : ℝ ↦
        (u₁ (r + x) - u₁ x) ^ 2 + (v₁ (r + x) - v₁ x) ^ 2)
      volume (-1) (1 - r) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hPos₂ : IntervalIntegrable
      (fun x : ℝ ↦
        (u₂ (r + x) - u₂ x) ^ 2 + (v₂ (r + x) - v₂ x) ^ 2)
      volume (-1) (1 - r) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hPosM : IntervalIntegrable
      (factorTwoPhasePositiveDistanceMixedIntegrand
        u₁ v₁ u₂ v₂ r) volume (-1) (1 - r) :=
    (continuous_factorTwoPhasePositiveDistanceMixedIntegrand
      u₁ v₁ u₂ v₂ hu₁ hv₁ hu₂ hv₂ r).intervalIntegrable _ _
  have hEnd₁ : IntervalIntegrable
      (factorTwoPhaseEndpointSquare u₁ v₁ a b r)
      volume (-1) (-1 + r) := by
    apply Continuous.intervalIntegrable
    unfold factorTwoPhaseEndpointSquare
    fun_prop
  have hEnd₂ : IntervalIntegrable
      (factorTwoPhaseEndpointSquare u₂ v₂ a b r)
      volume (-1) (-1 + r) := by
    apply Continuous.intervalIntegrable
    unfold factorTwoPhaseEndpointSquare
    fun_prop
  have hEndM : IntervalIntegrable
      (factorTwoPhaseEndpointMixedIntegrand
        u₁ v₁ u₂ v₂ a b r) volume (-1) (-1 + r) :=
    (continuous_factorTwoPhaseEndpointMixedIntegrand
      u₁ v₁ u₂ v₂ hu₁ hv₁ hu₂ hv₂ a b r).intervalIntegrable _ _
  have hPos :
      (∫ x : ℝ in -1..1 - r,
          ((c * u₁ (r + x) + d * u₂ (r + x)) -
              (c * u₁ x + d * u₂ x)) ^ 2 +
            ((c * v₁ (r + x) + d * v₂ (r + x)) -
              (c * v₁ x + d * v₂ x)) ^ 2) =
        c ^ 2 * (∫ x : ℝ in -1..1 - r,
          (u₁ (r + x) - u₁ x) ^ 2 + (v₁ (r + x) - v₁ x) ^ 2) +
        2 * c * d * (∫ x : ℝ in -1..1 - r,
          factorTwoPhasePositiveDistanceMixedIntegrand
            u₁ v₁ u₂ v₂ r x) +
        d ^ 2 * (∫ x : ℝ in -1..1 - r,
          (u₂ (r + x) - u₂ x) ^ 2 +
            (v₂ (r + x) - v₂ x) ^ 2) := by
    rw [show (fun x : ℝ ↦
        ((c * u₁ (r + x) + d * u₂ (r + x)) -
            (c * u₁ x + d * u₂ x)) ^ 2 +
          ((c * v₁ (r + x) + d * v₂ (r + x)) -
            (c * v₁ x + d * v₂ x)) ^ 2) =
        fun x ↦
          c ^ 2 * ((u₁ (r + x) - u₁ x) ^ 2 +
            (v₁ (r + x) - v₁ x) ^ 2) +
          2 * c * d * factorTwoPhasePositiveDistanceMixedIntegrand
            u₁ v₁ u₂ v₂ r x +
          d ^ 2 * ((u₂ (r + x) - u₂ x) ^ 2 +
            (v₂ (r + x) - v₂ x) ^ 2) by
        funext x
        exact factorTwoPhasePositiveDistance_linearCombination_eq
          u₁ v₁ u₂ v₂ r x c d,
      intervalIntegral.integral_add
        ((hPos₁.const_mul (c ^ 2)).add (hPosM.const_mul (2 * c * d)))
        (hPos₂.const_mul (d ^ 2)),
      intervalIntegral.integral_add
        (hPos₁.const_mul (c ^ 2)) (hPosM.const_mul (2 * c * d))]
    repeat rw [intervalIntegral.integral_const_mul]
  have hEnd :
      (∫ x : ℝ in -1..-1 + r,
          factorTwoPhaseEndpointSquare
            (fun y ↦ c * u₁ y + d * u₂ y)
            (fun y ↦ c * v₁ y + d * v₂ y) a b r x) =
        c ^ 2 * (∫ x : ℝ in -1..-1 + r,
          factorTwoPhaseEndpointSquare u₁ v₁ a b r x) +
        2 * c * d * (∫ x : ℝ in -1..-1 + r,
          factorTwoPhaseEndpointMixedIntegrand
            u₁ v₁ u₂ v₂ a b r x) +
        d ^ 2 * (∫ x : ℝ in -1..-1 + r,
          factorTwoPhaseEndpointSquare u₂ v₂ a b r x) := by
    rw [show (fun x : ℝ ↦
        factorTwoPhaseEndpointSquare
          (fun y ↦ c * u₁ y + d * u₂ y)
          (fun y ↦ c * v₁ y + d * v₂ y) a b r x) =
        fun x ↦
          c ^ 2 * factorTwoPhaseEndpointSquare u₁ v₁ a b r x +
          2 * c * d * factorTwoPhaseEndpointMixedIntegrand
            u₁ v₁ u₂ v₂ a b r x +
          d ^ 2 * factorTwoPhaseEndpointSquare u₂ v₂ a b r x by
        funext x
        exact factorTwoPhaseEndpointSquare_linearCombination_eq
          u₁ v₁ u₂ v₂ a b r x c d,
      intervalIntegral.integral_add
        ((hEnd₁.const_mul (c ^ 2)).add (hEndM.const_mul (2 * c * d)))
        (hEnd₂.const_mul (d ^ 2)),
      intervalIntegral.integral_add
        (hEnd₁.const_mul (c ^ 2)) (hEndM.const_mul (2 * c * d))]
    repeat rw [intervalIntegral.integral_const_mul]
  unfold factorTwoPhaseSingularSquareNumerator
    factorTwoPhaseSingularMixedNumerator
  rw [hPos, hEnd]
  ring

/-- The logarithmically weighted general-phase singular energy. -/
def factorTwoPhaseSingularWeightedEnergy
    (u v : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ r : ℝ in 0..2,
    factorTwoPhaseSingularSquareNumerator u v a b r / r

/-- The logarithmically weighted polarization of the singular energy. -/
def factorTwoPhaseSingularWeightedMixed
    (u₁ v₁ u₂ v₂ : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ r : ℝ in 0..2,
    factorTwoPhaseSingularMixedNumerator u₁ v₁ u₂ v₂ a b r / r

/-- The weighted mixed singular numerator is genuinely integrable at zero. -/
theorem intervalIntegrable_factorTwoPhaseSingularMixedNumerator_div
    (u₁ v₁ u₂ v₂ : ℝ → ℝ)
    (hu₁ : Continuous u₁) (hv₁ : Continuous v₁)
    (hu₂ : Continuous u₂) (hv₂ : Continuous v₂)
    (hlocalu₁ : LocallyLipschitzOn (Icc (-1) 1) u₁)
    (hlocalv₁ : LocallyLipschitzOn (Icc (-1) 1) v₁)
    (hlocalu₂ : LocallyLipschitzOn (Icc (-1) 1) u₂)
    (hlocalv₂ : LocallyLipschitzOn (Icc (-1) 1) v₂)
    (a b : ℝ) :
    IntervalIntegrable
      (fun r : ℝ ↦
        factorTwoPhaseSingularMixedNumerator
          u₁ v₁ u₂ v₂ a b r / r) volume 0 2 := by
  have hsum := intervalIntegrable_factorTwoPhaseSingularSquareNumerator_div
    (u₁ + u₂) (v₁ + v₂) (hu₁.add hu₂) (hv₁.add hv₂)
      (hlocalu₁.add hlocalu₂) (hlocalv₁.add hlocalv₂) a b
  have h₁ := intervalIntegrable_factorTwoPhaseSingularSquareNumerator_div
    u₁ v₁ hu₁ hv₁ hlocalu₁ hlocalv₁ a b
  have h₂ := intervalIntegrable_factorTwoPhaseSingularSquareNumerator_div
    u₂ v₂ hu₂ hv₂ hlocalu₂ hlocalv₂ a b
  have hpolarized := ((hsum.sub h₁).sub h₂).const_mul (1 / 2 : ℝ)
  apply hpolarized.congr
  intro r _hr
  have hquadratic :=
    factorTwoPhaseSingularSquareNumerator_linearCombination_eq
      u₁ v₁ u₂ v₂ hu₁ hv₁ hu₂ hv₂ a b r 1 1
  simp only [one_mul, one_pow, mul_one] at hquadratic
  change factorTwoPhaseSingularSquareNumerator
      (u₁ + u₂) (v₁ + v₂) a b r = _ at hquadratic
  change (1 / 2 : ℝ) *
      (factorTwoPhaseSingularSquareNumerator (u₁ + u₂) (v₁ + v₂) a b r / r -
        factorTwoPhaseSingularSquareNumerator u₁ v₁ a b r / r -
        factorTwoPhaseSingularSquareNumerator u₂ v₂ a b r / r) =
      factorTwoPhaseSingularMixedNumerator u₁ v₁ u₂ v₂ a b r / r
  rw [hquadratic]
  ring

/-- Exact quadratic expansion of the weighted singular energy. -/
theorem factorTwoPhaseSingularWeightedEnergy_linearCombination_eq
    (u₁ v₁ u₂ v₂ : ℝ → ℝ)
    (hu₁ : Continuous u₁) (hv₁ : Continuous v₁)
    (hu₂ : Continuous u₂) (hv₂ : Continuous v₂)
    (hlocalu₁ : LocallyLipschitzOn (Icc (-1) 1) u₁)
    (hlocalv₁ : LocallyLipschitzOn (Icc (-1) 1) v₁)
    (hlocalu₂ : LocallyLipschitzOn (Icc (-1) 1) u₂)
    (hlocalv₂ : LocallyLipschitzOn (Icc (-1) 1) v₂)
    (a b c d : ℝ) :
    factorTwoPhaseSingularWeightedEnergy
        (fun y ↦ c * u₁ y + d * u₂ y)
        (fun y ↦ c * v₁ y + d * v₂ y) a b =
      c ^ 2 * factorTwoPhaseSingularWeightedEnergy u₁ v₁ a b +
        2 * c * d *
          factorTwoPhaseSingularWeightedMixed u₁ v₁ u₂ v₂ a b +
        d ^ 2 * factorTwoPhaseSingularWeightedEnergy u₂ v₂ a b := by
  have h₁ := intervalIntegrable_factorTwoPhaseSingularSquareNumerator_div
    u₁ v₁ hu₁ hv₁ hlocalu₁ hlocalv₁ a b
  have h₂ := intervalIntegrable_factorTwoPhaseSingularSquareNumerator_div
    u₂ v₂ hu₂ hv₂ hlocalu₂ hlocalv₂ a b
  have hm := intervalIntegrable_factorTwoPhaseSingularMixedNumerator_div
    u₁ v₁ u₂ v₂ hu₁ hv₁ hu₂ hv₂
      hlocalu₁ hlocalv₁ hlocalu₂ hlocalv₂ a b
  unfold factorTwoPhaseSingularWeightedEnergy
    factorTwoPhaseSingularWeightedMixed
  rw [show (fun r : ℝ ↦
      factorTwoPhaseSingularSquareNumerator
        (fun y ↦ c * u₁ y + d * u₂ y)
        (fun y ↦ c * v₁ y + d * v₂ y) a b r / r) =
      fun r ↦
        c ^ 2 * (factorTwoPhaseSingularSquareNumerator u₁ v₁ a b r / r) +
          2 * c * d *
            (factorTwoPhaseSingularMixedNumerator
              u₁ v₁ u₂ v₂ a b r / r) +
          d ^ 2 * (factorTwoPhaseSingularSquareNumerator u₂ v₂ a b r / r) by
      funext r
      rw [factorTwoPhaseSingularSquareNumerator_linearCombination_eq
        u₁ v₁ u₂ v₂ hu₁ hv₁ hu₂ hv₂ a b r c d]
      ring,
    intervalIntegral.integral_add
      ((h₁.const_mul (c ^ 2)).add (hm.const_mul (2 * c * d)))
      (h₂.const_mul (d ^ 2)),
    intervalIntegral.integral_add
      (h₁.const_mul (c ^ 2)) (hm.const_mul (2 * c * d))]
  repeat rw [intervalIntegral.integral_const_mul]

/-- The weighted singular energy is nonnegative on the sharp radius-two
phase disk. -/
theorem factorTwoPhaseSingularWeightedEnergy_nonneg_of_sq_add_sq_le_four
    (u v : ℝ → ℝ) (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 4) :
    0 ≤ factorTwoPhaseSingularWeightedEnergy u v a b := by
  unfold factorTwoPhaseSingularWeightedEnergy
  exact
    integral_factorTwoPhaseSingularSquareNumerator_div_nonneg_of_sq_add_sq_le_four
      u v a b hab

/-- Production-disk specialization of the sharp weighted nonnegativity. -/
theorem factorTwoPhaseSingularWeightedEnergy_nonneg
    (u v : ℝ → ℝ) (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    0 ≤ factorTwoPhaseSingularWeightedEnergy u v a b := by
  exact factorTwoPhaseSingularWeightedEnergy_nonneg_of_sq_add_sq_le_four
    u v a b (hab.trans (by norm_num))

/-- Sharp Cauchy--Schwarz for the weighted general-phase polarization on the
radius-two phase disk. -/
theorem factorTwoPhaseSingularWeightedMixed_sq_le_of_sq_add_sq_le_four
    (u₁ v₁ u₂ v₂ : ℝ → ℝ)
    (hu₁ : Continuous u₁) (hv₁ : Continuous v₁)
    (hu₂ : Continuous u₂) (hv₂ : Continuous v₂)
    (hlocalu₁ : LocallyLipschitzOn (Icc (-1) 1) u₁)
    (hlocalv₁ : LocallyLipschitzOn (Icc (-1) 1) v₁)
    (hlocalu₂ : LocallyLipschitzOn (Icc (-1) 1) u₂)
    (hlocalv₂ : LocallyLipschitzOn (Icc (-1) 1) v₂)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 4) :
    factorTwoPhaseSingularWeightedMixed u₁ v₁ u₂ v₂ a b ^ 2 ≤
      factorTwoPhaseSingularWeightedEnergy u₁ v₁ a b *
        factorTwoPhaseSingularWeightedEnergy u₂ v₂ a b := by
  let Q₁ := factorTwoPhaseSingularWeightedEnergy u₁ v₁ a b
  let Q₂ := factorTwoPhaseSingularWeightedEnergy u₂ v₂ a b
  let B := factorTwoPhaseSingularWeightedMixed u₁ v₁ u₂ v₂ a b
  have hpencil : ∀ c d : ℝ,
      0 ≤ Q₁ * c ^ 2 + 2 * B * c * d + Q₂ * d ^ 2 := by
    intro c d
    have hnonneg :=
      factorTwoPhaseSingularWeightedEnergy_nonneg_of_sq_add_sq_le_four
      (fun y ↦ c * u₁ y + d * u₂ y)
      (fun y ↦ c * v₁ y + d * v₂ y) a b hab
    rw [factorTwoPhaseSingularWeightedEnergy_linearCombination_eq
      u₁ v₁ u₂ v₂ hu₁ hv₁ hu₂ hv₂
        hlocalu₁ hlocalv₁ hlocalu₂ hlocalv₂ a b c d] at hnonneg
    dsimp only [Q₁, Q₂, B]
    nlinarith
  exact ((real_quadratic_pencil_nonneg_iff Q₁ Q₂ B).mp hpencil).2.2

/-- Production-disk specialization of weighted Cauchy--Schwarz. -/
theorem factorTwoPhaseSingularWeightedMixed_sq_le
    (u₁ v₁ u₂ v₂ : ℝ → ℝ)
    (hu₁ : Continuous u₁) (hv₁ : Continuous v₁)
    (hu₂ : Continuous u₂) (hv₂ : Continuous v₂)
    (hlocalu₁ : LocallyLipschitzOn (Icc (-1) 1) u₁)
    (hlocalv₁ : LocallyLipschitzOn (Icc (-1) 1) v₁)
    (hlocalu₂ : LocallyLipschitzOn (Icc (-1) 1) u₂)
    (hlocalv₂ : LocallyLipschitzOn (Icc (-1) 1) v₂)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    factorTwoPhaseSingularWeightedMixed u₁ v₁ u₂ v₂ a b ^ 2 ≤
      factorTwoPhaseSingularWeightedEnergy u₁ v₁ a b *
        factorTwoPhaseSingularWeightedEnergy u₂ v₂ a b := by
  exact factorTwoPhaseSingularWeightedMixed_sq_le_of_sq_add_sq_le_four
    u₁ v₁ u₂ v₂ hu₁ hv₁ hu₂ hv₂
      hlocalu₁ hlocalv₁ hlocalu₂ hlocalv₂ a b
      (hab.trans (by norm_num))

/-- The potential and reflected-pole portion of a general phase cross. -/
def factorTwoPhasePotentialPoleMixed
    (uLow vLow uR vR : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * uLow x * uR x) +
    (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * vLow x * vR x) -
    (1 / 4 : ℝ) *
      ((∫ t : ℝ in 0..2,
          factorTwoCenteredPhaseCorrelation
            (uLow + uR) (vLow + vR) a (-b) t / (2 - t)) -
        (∫ t : ℝ in 0..2,
          factorTwoCenteredPhaseCorrelation uLow vLow a (-b) t / (2 - t)) -
        ∫ t : ℝ in 0..2,
          factorTwoCenteredPhaseCorrelation uR vR a (-b) t / (2 - t))

/-- Raw-log and ordinary `L²` orthogonality identify the full general-phase
potential/pole cross with one half of the weighted singular polarization. -/
theorem factorTwoPhasePotentialPoleMixed_eq_half_weightedMixed
    (uLow vLow uR vR : ℝ → ℝ)
    (huLow : Continuous uLow) (hvLow : Continuous vLow)
    (huR : Continuous uR) (hvR : Continuous vR)
    (hlocaluLow : LocallyLipschitzOn (Icc (-1) 1) uLow)
    (hlocalvLow : LocallyLipschitzOn (Icc (-1) 1) vLow)
    (hlocaluR : LocallyLipschitzOn (Icc (-1) 1) uR)
    (hlocalvR : LocallyLipschitzOn (Icc (-1) 1) vR)
    (a b : ℝ)
    (huRaw : centeredRawLogEnergy (uLow + uR) =
      centeredRawLogEnergy uLow + centeredRawLogEnergy uR)
    (hvRaw : centeredRawLogEnergy (vLow + vR) =
      centeredRawLogEnergy vLow + centeredRawLogEnergy vR)
    (huOrth : (∫ x : ℝ in -1..1, uLow x * uR x) = 0)
    (hvOrth : (∫ x : ℝ in -1..1, vLow x * vR x) = 0) :
    factorTwoPhasePotentialPoleMixed uLow vLow uR vR a b =
      (1 / 2 : ℝ) *
        factorTwoPhaseSingularWeightedMixed uLow vLow uR vR a b := by
  have hsum := centeredEnergy_add_potential_add_logMass_sub_half_phasePole_eq_square
    (uLow + uR) (vLow + vR) (huLow.add huR) (hvLow.add hvR)
      (hlocaluLow.add hlocaluR) (hlocalvLow.add hlocalvR) a b
  have hlow := centeredEnergy_add_potential_add_logMass_sub_half_phasePole_eq_square
    uLow vLow huLow hvLow hlocaluLow hlocalvLow a b
  have hres := centeredEnergy_add_potential_add_logMass_sub_half_phasePole_eq_square
    uR vR huR hvR hlocaluR hlocalvR a b
  have hquadratic := factorTwoPhaseSingularWeightedEnergy_linearCombination_eq
    uLow vLow uR vR huLow hvLow huR hvR
      hlocaluLow hlocalvLow hlocaluR hlocalvR a b 1 1
  simp only [one_mul, one_pow, mul_one] at hquadratic
  change factorTwoPhaseSingularWeightedEnergy
      (uLow + uR) (vLow + vR) a b = _ at hquadratic
  have huPotential := integral_endpointPotential_add_sq uLow uR huLow huR
  have hvPotential := integral_endpointPotential_add_sq vLow vR hvLow hvR
  have huMass := integral_add_sq uLow uR huLow huR
  have hvMass := integral_add_sq vLow vR hvLow hvR
  simp only [Pi.add_apply] at hsum
  rw [huRaw, hvRaw, huPotential, hvPotential,
    huMass, hvMass, huOrth, hvOrth] at hsum
  unfold factorTwoPhaseSingularWeightedEnergy at hquadratic
  unfold factorTwoPhasePotentialPoleMixed
  nlinarith

/-- The exact determinant allocation carried by the potential/pole cross.
Each diagonal spends one half of its weighted singular energy. -/
theorem factorTwoPhasePotentialPoleMixed_sq_le_half_energy_mul_half_energy
    (uLow vLow uR vR : ℝ → ℝ)
    (huLow : Continuous uLow) (hvLow : Continuous vLow)
    (huR : Continuous uR) (hvR : Continuous vR)
    (hlocaluLow : LocallyLipschitzOn (Icc (-1) 1) uLow)
    (hlocalvLow : LocallyLipschitzOn (Icc (-1) 1) vLow)
    (hlocaluR : LocallyLipschitzOn (Icc (-1) 1) uR)
    (hlocalvR : LocallyLipschitzOn (Icc (-1) 1) vR)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 4)
    (huRaw : centeredRawLogEnergy (uLow + uR) =
      centeredRawLogEnergy uLow + centeredRawLogEnergy uR)
    (hvRaw : centeredRawLogEnergy (vLow + vR) =
      centeredRawLogEnergy vLow + centeredRawLogEnergy vR)
    (huOrth : (∫ x : ℝ in -1..1, uLow x * uR x) = 0)
    (hvOrth : (∫ x : ℝ in -1..1, vLow x * vR x) = 0) :
    factorTwoPhasePotentialPoleMixed uLow vLow uR vR a b ^ 2 ≤
      ((1 / 2 : ℝ) *
          factorTwoPhaseSingularWeightedEnergy uLow vLow a b) *
        ((1 / 2 : ℝ) *
          factorTwoPhaseSingularWeightedEnergy uR vR a b) := by
  rw [factorTwoPhasePotentialPoleMixed_eq_half_weightedMixed
    uLow vLow uR vR huLow hvLow huR hvR
      hlocaluLow hlocalvLow hlocaluR hlocalvR a b
      huRaw hvRaw huOrth hvOrth]
  have hCauchy :=
    factorTwoPhaseSingularWeightedMixed_sq_le_of_sq_add_sq_le_four
      uLow vLow uR vR huLow hvLow huR hvR
        hlocaluLow hlocalvLow hlocaluR hlocalvR a b hab
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSingularWeightedCauchyStructural
