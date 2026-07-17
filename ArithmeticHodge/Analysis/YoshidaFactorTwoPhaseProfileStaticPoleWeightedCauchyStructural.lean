import ArithmeticHodge.Analysis.YoshidaEndpointEvenFullPolarization
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseProfileStaticPoleMixedCauchyStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseProfileStaticPoleWeightedCauchyStructural

open CenteredEndpointCorrelation
open YoshidaEndpointBoundaryTailFold
open YoshidaEndpointEvenFullPolarization
open YoshidaEndpointPotentialBound
open YoshidaEndpointSingularCorrelation
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseEnvelope
open YoshidaFactorTwoPhaseProfileStaticPoleMixedCauchyStructural
open YoshidaFactorTwoPhaseProfileStaticPoleSquareStructural
open YoshidaFactorTwoPhaseProfileStaticSquareAssemblyStructural

noncomputable section

/-!
# Log-weighted Cauchy estimate for the profile-static pole square

The pointwise three-square completion remains a positive quadratic form after
integrating first over the endpoint overlap and then against `dr / r`.  This
file exposes that weighted quadratic form and its polarization.  Integrability
at `r = 0` is proved from the exact boundary-tail/reflected-correlation fold;
it is not inferred merely from pointwise nonnegativity.

No assertion about the signed smooth remainder is made here.
-/

/-- The logarithmically weighted energy carried by the static pole square. -/
def factorTwoProfileStaticPoleWeightedEnergy
    (e o : ℝ → ℝ) (sigma : ℝ) : ℝ :=
  ∫ r : ℝ in 0..2,
    factorTwoProfileStaticPoleSquareNumerator e o sigma r / r

/-- The logarithmically weighted polarization of the static pole square. -/
def factorTwoProfileStaticPoleWeightedMixed
    (e₁ o₁ e₂ o₂ : ℝ → ℝ) (sigma : ℝ) : ℝ :=
  ∫ r : ℝ in 0..2,
    factorTwoProfileStaticPoleMixedNumerator e₁ o₁ e₂ o₂ sigma r / r

private theorem intervalIntegrable_profileStaticReflectedCorrelation_two_sub_div
    (e o : ℝ → ℝ) (he : Continuous e) (ho : Continuous o)
    (sigma : ℝ) :
    IntervalIntegrable
      (fun r : ℝ ↦
        factorTwoProfileStaticReflectedCorrelation e o sigma (2 - r) / r)
      volume 0 2 := by
  have he0 := intervalIntegrable_factorTwoCenteredPhaseCorrelation_two_sub_div
    e (0 : ℝ → ℝ) he continuous_zero sigma 0
  have ho0 := intervalIntegrable_factorTwoCenteredPhaseCorrelation_two_sub_div
    o (0 : ℝ → ℝ) ho continuous_zero (-sigma) 0
  have heo := intervalIntegrable_factorTwoCenteredPhaseCorrelation_two_sub_div
    e o he ho 0 (-1)
  apply ((he0.add ho0).add heo).congr
  intro r _hr
  unfold factorTwoProfileStaticReflectedCorrelation
    factorTwoProfileStaticCrossDifference factorTwoCenteredPhaseCorrelation
    centeredEndpointCorrelation factorTwoCenteredCrossCorrelation
  simp only [Pi.zero_apply, zero_mul, mul_zero,
    intervalIntegral.integral_zero, add_zero, zero_add,
    sub_zero, neg_mul, one_mul]
  ring

/-- The weighted pole-square energy is genuinely interval-integrable at the
singular endpoint. -/
theorem intervalIntegrable_factorTwoProfileStaticPoleSquareNumerator_div
    (e o : ℝ → ℝ) (he : Continuous e) (ho : Continuous o)
    (sigma : ℝ) (hsigma : sigma ^ 2 = 1) :
    IntervalIntegrable
      (fun r : ℝ ↦
        factorTwoProfileStaticPoleSquareNumerator e o sigma r / r)
      volume 0 2 := by
  have heTail := intervalIntegrable_centeredEndpointBoundaryTail_div e he
  have hoTail := intervalIntegrable_centeredEndpointBoundaryTail_div o ho
  have hreflected :=
    intervalIntegrable_profileStaticReflectedCorrelation_two_sub_div
      e o he ho sigma
  apply ((heTail.add hoTail).sub hreflected).congr
  intro r _hr
  change centeredEndpointBoundaryTail e r / r +
      centeredEndpointBoundaryTail o r / r -
      factorTwoProfileStaticReflectedCorrelation e o sigma (2 - r) / r =
    factorTwoProfileStaticPoleSquareNumerator e o sigma r / r
  rw [← factorTwoProfileStaticPoleDefectNumerator_eq_square
      e o sigma hsigma r,
    factorTwoProfileStaticPoleDefectNumerator_eq_boundaryTail_sub_reflected
      e o he ho sigma r]
  ring

/-- The weighted mixed pole numerator is genuinely interval-integrable.  The
proof polarizes three already-integrable pole energies. -/
theorem intervalIntegrable_factorTwoProfileStaticPoleMixedNumerator_div
    (e₁ o₁ e₂ o₂ : ℝ → ℝ)
    (he₁ : Continuous e₁) (ho₁ : Continuous o₁)
    (he₂ : Continuous e₂) (ho₂ : Continuous o₂)
    (sigma : ℝ) (hsigma : sigma ^ 2 = 1) :
    IntervalIntegrable
      (fun r : ℝ ↦
        factorTwoProfileStaticPoleMixedNumerator
          e₁ o₁ e₂ o₂ sigma r / r)
      volume 0 2 := by
  have hsum := intervalIntegrable_factorTwoProfileStaticPoleSquareNumerator_div
    (fun y ↦ e₁ y + e₂ y) (fun y ↦ o₁ y + o₂ y)
      (he₁.add he₂) (ho₁.add ho₂) sigma hsigma
  have h₁ := intervalIntegrable_factorTwoProfileStaticPoleSquareNumerator_div
    e₁ o₁ he₁ ho₁ sigma hsigma
  have h₂ := intervalIntegrable_factorTwoProfileStaticPoleSquareNumerator_div
    e₂ o₂ he₂ ho₂ sigma hsigma
  have hpolarized := ((hsum.sub h₁).sub h₂).const_mul (1 / 2 : ℝ)
  apply hpolarized.congr
  intro r _hr
  have hquadratic :=
    factorTwoProfileStaticPoleSquareNumerator_linearCombination_eq
      e₁ o₁ e₂ o₂ he₁ ho₁ he₂ ho₂ sigma r 1 1
  simp only [one_mul, one_pow, mul_one] at hquadratic
  change (1 / 2 : ℝ) *
      (factorTwoProfileStaticPoleSquareNumerator
          (fun y ↦ e₁ y + e₂ y) (fun y ↦ o₁ y + o₂ y) sigma r / r -
        factorTwoProfileStaticPoleSquareNumerator e₁ o₁ sigma r / r -
        factorTwoProfileStaticPoleSquareNumerator e₂ o₂ sigma r / r) =
      factorTwoProfileStaticPoleMixedNumerator e₁ o₁ e₂ o₂ sigma r / r
  rw [hquadratic]
  ring

/-- Exact quadratic expansion of the logarithmically weighted pole energy. -/
theorem factorTwoProfileStaticPoleWeightedEnergy_linearCombination_eq
    (e₁ o₁ e₂ o₂ : ℝ → ℝ)
    (he₁ : Continuous e₁) (ho₁ : Continuous o₁)
    (he₂ : Continuous e₂) (ho₂ : Continuous o₂)
    (sigma : ℝ) (hsigma : sigma ^ 2 = 1)
    (c d : ℝ) :
    factorTwoProfileStaticPoleWeightedEnergy
        (fun y ↦ c * e₁ y + d * e₂ y)
        (fun y ↦ c * o₁ y + d * o₂ y) sigma =
      c ^ 2 * factorTwoProfileStaticPoleWeightedEnergy e₁ o₁ sigma +
        2 * c * d *
          factorTwoProfileStaticPoleWeightedMixed e₁ o₁ e₂ o₂ sigma +
        d ^ 2 * factorTwoProfileStaticPoleWeightedEnergy e₂ o₂ sigma := by
  have h₁ := intervalIntegrable_factorTwoProfileStaticPoleSquareNumerator_div
    e₁ o₁ he₁ ho₁ sigma hsigma
  have h₂ := intervalIntegrable_factorTwoProfileStaticPoleSquareNumerator_div
    e₂ o₂ he₂ ho₂ sigma hsigma
  have hm := intervalIntegrable_factorTwoProfileStaticPoleMixedNumerator_div
    e₁ o₁ e₂ o₂ he₁ ho₁ he₂ ho₂ sigma hsigma
  unfold factorTwoProfileStaticPoleWeightedEnergy
    factorTwoProfileStaticPoleWeightedMixed
  rw [show (fun r : ℝ ↦
      factorTwoProfileStaticPoleSquareNumerator
        (fun y ↦ c * e₁ y + d * e₂ y)
        (fun y ↦ c * o₁ y + d * o₂ y) sigma r / r) =
      fun r ↦
        c ^ 2 *
            (factorTwoProfileStaticPoleSquareNumerator e₁ o₁ sigma r / r) +
          2 * c * d *
            (factorTwoProfileStaticPoleMixedNumerator
              e₁ o₁ e₂ o₂ sigma r / r) +
          d ^ 2 *
            (factorTwoProfileStaticPoleSquareNumerator e₂ o₂ sigma r / r) by
      funext r
      rw [factorTwoProfileStaticPoleSquareNumerator_linearCombination_eq
        e₁ o₁ e₂ o₂ he₁ ho₁ he₂ ho₂ sigma r c d]
      ring,
    intervalIntegral.integral_add
      ((h₁.const_mul (c ^ 2)).add (hm.const_mul (2 * c * d)))
      (h₂.const_mul (d ^ 2)),
    intervalIntegral.integral_add
      (h₁.const_mul (c ^ 2)) (hm.const_mul (2 * c * d))]
  repeat rw [intervalIntegral.integral_const_mul]

/-- The logarithmically weighted static pole energy is nonnegative. -/
theorem factorTwoProfileStaticPoleWeightedEnergy_nonneg
    (e o : ℝ → ℝ) (sigma : ℝ) (hsigma : sigma ^ 2 = 1) :
    0 ≤ factorTwoProfileStaticPoleWeightedEnergy e o sigma := by
  unfold factorTwoProfileStaticPoleWeightedEnergy
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro r hr
  rw [← factorTwoProfileStaticPoleDefectNumerator_eq_square
    e o sigma hsigma r]
  exact div_nonneg
    (factorTwoProfileStaticPoleDefectNumerator_nonneg
      e o sigma hsigma r hr.1) hr.1

/-- Exact boundary-tail fold of the weighted static pole energy.  Besides
being useful for integrability, this identifies precisely which endpoint
potential and reflected-pole terms are carried by the Hadamard reserve. -/
theorem factorTwoProfileStaticPoleWeightedEnergy_eq_potential_mass_sub_reflected
    (e o : ℝ → ℝ) (he : Continuous e) (ho : Continuous o)
    (sigma : ℝ) (hsigma : sigma ^ 2 = 1) :
    factorTwoProfileStaticPoleWeightedEnergy e o sigma =
      2 *
          ((∫ x : ℝ in -1..1,
              yoshidaEndpointPotential x * e x ^ 2) +
            Real.log 2 * (∫ x : ℝ in -1..1, e x ^ 2) +
            (∫ x : ℝ in -1..1,
              yoshidaEndpointPotential x * o x ^ 2) +
            Real.log 2 * (∫ x : ℝ in -1..1, o x ^ 2)) -
        ∫ r : ℝ in 0..2,
          factorTwoProfileStaticReflectedCorrelation e o sigma (2 - r) / r := by
  have heTail := intervalIntegrable_centeredEndpointBoundaryTail_div e he
  have hoTail := intervalIntegrable_centeredEndpointBoundaryTail_div o ho
  have hreflected :=
    intervalIntegrable_profileStaticReflectedCorrelation_two_sub_div
      e o he ho sigma
  have heFold := half_integral_centeredEndpointBoundaryTail_div_eq e he
  have hoFold := half_integral_centeredEndpointBoundaryTail_div_eq o ho
  unfold factorTwoProfileStaticPoleWeightedEnergy
  rw [show (fun r : ℝ ↦
      factorTwoProfileStaticPoleSquareNumerator e o sigma r / r) =
      fun r ↦
        centeredEndpointBoundaryTail e r / r +
          centeredEndpointBoundaryTail o r / r -
          factorTwoProfileStaticReflectedCorrelation e o sigma (2 - r) / r by
      funext r
      rw [← factorTwoProfileStaticPoleDefectNumerator_eq_square
          e o sigma hsigma r,
        factorTwoProfileStaticPoleDefectNumerator_eq_boundaryTail_sub_reflected
          e o he ho sigma r]
      ring,
    intervalIntegral.integral_sub (heTail.add hoTail) hreflected,
    intervalIntegral.integral_add heTail hoTail]
  linarith

/-- The potential and reflected-pole part of the mixed static branch.  Its
three written reflected integrals use the original `t / (2 - t)` orientation
from the endpoint phase formula. -/
def factorTwoProfileStaticPotentialPoleMixed
    (eLow oLow eR oR : ℝ → ℝ) (sigma : ℝ) : ℝ :=
  (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * eLow x * eR x) +
    (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * oLow x * oR x) -
    (1 / 4 : ℝ) *
      ((∫ t : ℝ in 0..2,
          factorTwoProfileStaticReflectedCorrelation
            (eLow + eR) (oLow + oR) sigma t / (2 - t)) -
        (∫ t : ℝ in 0..2,
          factorTwoProfileStaticReflectedCorrelation
            eLow oLow sigma t / (2 - t)) -
        ∫ t : ℝ in 0..2,
          factorTwoProfileStaticReflectedCorrelation
            eR oR sigma t / (2 - t))

/-- Under the two ordinary `L²` orthogonality rows, the complete static
potential-plus-reflected-pole low/residual cross is exactly one half of the
log-weighted Hadamard polarization.  No absolute-value split is used. -/
theorem factorTwoProfileStaticPotentialPoleMixed_eq_half_weightedMixed
    (eLow oLow eR oR : ℝ → ℝ)
    (heLow : Continuous eLow) (hoLow : Continuous oLow)
    (heR : Continuous eR) (hoR : Continuous oR)
    (sigma : ℝ) (hsigma : sigma ^ 2 = 1)
    (heOrth : (∫ x : ℝ in -1..1, eLow x * eR x) = 0)
    (hoOrth : (∫ x : ℝ in -1..1, oLow x * oR x) = 0) :
    factorTwoProfileStaticPotentialPoleMixed
        eLow oLow eR oR sigma =
      (1 / 2 : ℝ) *
        factorTwoProfileStaticPoleWeightedMixed
          eLow oLow eR oR sigma := by
  have hsum :=
    factorTwoProfileStaticPoleWeightedEnergy_eq_potential_mass_sub_reflected
      (eLow + eR) (oLow + oR) (heLow.add heR) (hoLow.add hoR)
      sigma hsigma
  have hlow :=
    factorTwoProfileStaticPoleWeightedEnergy_eq_potential_mass_sub_reflected
      eLow oLow heLow hoLow sigma hsigma
  have hres :=
    factorTwoProfileStaticPoleWeightedEnergy_eq_potential_mass_sub_reflected
      eR oR heR hoR sigma hsigma
  have hquadratic :=
    factorTwoProfileStaticPoleWeightedEnergy_linearCombination_eq
      eLow oLow eR oR heLow hoLow heR hoR sigma hsigma 1 1
  simp only [one_mul, one_pow, mul_one] at hquadratic
  change factorTwoProfileStaticPoleWeightedEnergy
      (eLow + eR) (oLow + oR) sigma = _ at hquadratic
  have hePotential := integral_endpointPotential_add_sq
    eLow eR heLow heR
  have hoPotential := integral_endpointPotential_add_sq
    oLow oR hoLow hoR
  have heMass := integral_add_sq eLow eR heLow heR
  have hoMass := integral_add_sq oLow oR hoLow hoR
  have hrefsum :=
    integral_profileStaticReflectedCorrelation_div_two_sub_eq_reflected
      (eLow + eR) (oLow + oR) sigma
  have hreflow :=
    integral_profileStaticReflectedCorrelation_div_two_sub_eq_reflected
      eLow oLow sigma
  have hrefres :=
    integral_profileStaticReflectedCorrelation_div_two_sub_eq_reflected
      eR oR sigma
  simp only [Pi.add_apply] at hsum
  rw [hePotential, hoPotential, heMass, hoMass, heOrth, hoOrth] at hsum
  unfold factorTwoProfileStaticPotentialPoleMixed
  rw [hrefsum, hreflow, hrefres]
  nlinarith

/-- Sharp Cauchy--Schwarz for the logarithmically weighted static pole
polarization.  This retains the constant mode and spends no signed smooth
remainder. -/
theorem factorTwoProfileStaticPoleWeightedMixed_sq_le
    (e₁ o₁ e₂ o₂ : ℝ → ℝ)
    (he₁ : Continuous e₁) (ho₁ : Continuous o₁)
    (he₂ : Continuous e₂) (ho₂ : Continuous o₂)
    (sigma : ℝ) (hsigma : sigma ^ 2 = 1) :
    factorTwoProfileStaticPoleWeightedMixed e₁ o₁ e₂ o₂ sigma ^ 2 ≤
      factorTwoProfileStaticPoleWeightedEnergy e₁ o₁ sigma *
        factorTwoProfileStaticPoleWeightedEnergy e₂ o₂ sigma := by
  let Q₁ := factorTwoProfileStaticPoleWeightedEnergy e₁ o₁ sigma
  let Q₂ := factorTwoProfileStaticPoleWeightedEnergy e₂ o₂ sigma
  let B := factorTwoProfileStaticPoleWeightedMixed e₁ o₁ e₂ o₂ sigma
  have hpencil : ∀ c d : ℝ,
      0 ≤ Q₁ * c ^ 2 + 2 * B * c * d + Q₂ * d ^ 2 := by
    intro c d
    have hnonneg := factorTwoProfileStaticPoleWeightedEnergy_nonneg
      (fun y ↦ c * e₁ y + d * e₂ y)
      (fun y ↦ c * o₁ y + d * o₂ y) sigma hsigma
    rw [factorTwoProfileStaticPoleWeightedEnergy_linearCombination_eq
      e₁ o₁ e₂ o₂ he₁ ho₁ he₂ ho₂ sigma hsigma c d] at hnonneg
    dsimp only [Q₁, Q₂, B]
    nlinarith
  exact ((real_quadratic_pencil_nonneg_iff Q₁ Q₂ B).mp hpencil).2.2

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseProfileStaticPoleWeightedCauchyStructural
