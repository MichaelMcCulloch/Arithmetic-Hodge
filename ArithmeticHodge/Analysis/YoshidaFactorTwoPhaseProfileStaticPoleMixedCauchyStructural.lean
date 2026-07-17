import ArithmeticHodge.Analysis.TwoByTwoSchur
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseProfileStaticSquareAssemblyStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseProfileStaticPoleMixedCauchyStructural

open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseProfileStaticPoleSquareStructural

noncomputable section

/-!
# Mixed Cauchy estimate for the profile-static pole square

The reflected static pole is already the squared norm of three expressions
which depend linearly on the even/odd profile pair.  This file exposes its
polarization and proves Cauchy--Schwarz first pointwise and then for each fixed
endpoint length.  In particular, the estimate does not require a mean-zero
hypothesis and therefore applies to the retained constant mode.

No assertion about the signed smooth remainder is made here.
-/

/-- Polarization of the three-component Hadamard square at a fixed endpoint
length and point. -/
def factorTwoProfileStaticPoleHadamardMixedIntegrand
    (e₁ o₁ e₂ o₂ : ℝ → ℝ) (sigma r x : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
      ((e₁ (2 - r + x) - sigma * o₁ (2 - r + x) -
            (sigma * e₁ x + o₁ x)) *
        (e₂ (2 - r + x) - sigma * o₂ (2 - r + x) -
            (sigma * e₂ x + o₂ x)) +
      (e₁ (2 - r + x) + sigma * o₁ (2 - r + x)) *
        (e₂ (2 - r + x) + sigma * o₂ (2 - r + x)) +
      (e₁ x - sigma * o₁ x) * (e₂ x - sigma * o₂ x))

/-- Exact quadratic expansion of the Hadamard square under an arbitrary
linear combination of two profile pairs. -/
theorem factorTwoProfileStaticPoleHadamardSquare_linearCombination_eq
    (e₁ o₁ e₂ o₂ : ℝ → ℝ) (sigma r x c d : ℝ) :
    factorTwoProfileStaticPoleHadamardSquare
        (fun y ↦ c * e₁ y + d * e₂ y)
        (fun y ↦ c * o₁ y + d * o₂ y) sigma r x =
      c ^ 2 * factorTwoProfileStaticPoleHadamardSquare e₁ o₁ sigma r x +
        2 * c * d *
          factorTwoProfileStaticPoleHadamardMixedIntegrand
            e₁ o₁ e₂ o₂ sigma r x +
        d ^ 2 * factorTwoProfileStaticPoleHadamardSquare e₂ o₂ sigma r x := by
  unfold factorTwoProfileStaticPoleHadamardSquare
    factorTwoProfileStaticPoleHadamardMixedIntegrand
  ring

/-- Pointwise Cauchy--Schwarz for the three-component Hadamard
polarization. -/
theorem factorTwoProfileStaticPoleHadamardMixedIntegrand_sq_le
    (e₁ o₁ e₂ o₂ : ℝ → ℝ) (sigma r x : ℝ) :
    factorTwoProfileStaticPoleHadamardMixedIntegrand
          e₁ o₁ e₂ o₂ sigma r x ^ 2 ≤
      factorTwoProfileStaticPoleHadamardSquare e₁ o₁ sigma r x *
        factorTwoProfileStaticPoleHadamardSquare e₂ o₂ sigma r x := by
  let a₁ := e₁ (2 - r + x) - sigma * o₁ (2 - r + x) -
    (sigma * e₁ x + o₁ x)
  let b₁ := e₁ (2 - r + x) + sigma * o₁ (2 - r + x)
  let c₁ := e₁ x - sigma * o₁ x
  let a₂ := e₂ (2 - r + x) - sigma * o₂ (2 - r + x) -
    (sigma * e₂ x + o₂ x)
  let b₂ := e₂ (2 - r + x) + sigma * o₂ (2 - r + x)
  let c₂ := e₂ x - sigma * o₂ x
  have hab : 0 ≤ (a₁ * b₂ - b₁ * a₂) ^ 2 := sq_nonneg _
  have hac : 0 ≤ (a₁ * c₂ - c₁ * a₂) ^ 2 := sq_nonneg _
  have hbc : 0 ≤ (b₁ * c₂ - c₁ * b₂) ^ 2 := sq_nonneg _
  change ((1 / 2 : ℝ) *
      (a₁ * a₂ + b₁ * b₂ + c₁ * c₂)) ^ 2 ≤
    ((1 / 2 : ℝ) * a₁ ^ 2 + (1 / 2 : ℝ) * b₁ ^ 2 +
        (1 / 2 : ℝ) * c₁ ^ 2) *
      ((1 / 2 : ℝ) * a₂ ^ 2 + (1 / 2 : ℝ) * b₂ ^ 2 +
        (1 / 2 : ℝ) * c₂ ^ 2)
  nlinarith

/-- Fixed-length polarization of the integrated static pole square. -/
def factorTwoProfileStaticPoleMixedNumerator
    (e₁ o₁ e₂ o₂ : ℝ → ℝ) (sigma r : ℝ) : ℝ :=
  ∫ x : ℝ in -1..-1 + r,
    factorTwoProfileStaticPoleHadamardMixedIntegrand
      e₁ o₁ e₂ o₂ sigma r x

private theorem continuous_factorTwoProfileStaticPoleHadamardSquare
    (e o : ℝ → ℝ) (he : Continuous e) (ho : Continuous o)
    (sigma r : ℝ) :
    Continuous
      (factorTwoProfileStaticPoleHadamardSquare e o sigma r) := by
  unfold factorTwoProfileStaticPoleHadamardSquare
  fun_prop

private theorem continuous_factorTwoProfileStaticPoleHadamardMixedIntegrand
    (e₁ o₁ e₂ o₂ : ℝ → ℝ)
    (he₁ : Continuous e₁) (ho₁ : Continuous o₁)
    (he₂ : Continuous e₂) (ho₂ : Continuous o₂)
    (sigma r : ℝ) :
    Continuous
      (factorTwoProfileStaticPoleHadamardMixedIntegrand
        e₁ o₁ e₂ o₂ sigma r) := by
  unfold factorTwoProfileStaticPoleHadamardMixedIntegrand
  fun_prop

/-- Exact quadratic expansion after integrating over the endpoint interval. -/
theorem factorTwoProfileStaticPoleSquareNumerator_linearCombination_eq
    (e₁ o₁ e₂ o₂ : ℝ → ℝ)
    (he₁ : Continuous e₁) (ho₁ : Continuous o₁)
    (he₂ : Continuous e₂) (ho₂ : Continuous o₂)
    (sigma r c d : ℝ) :
    factorTwoProfileStaticPoleSquareNumerator
        (fun y ↦ c * e₁ y + d * e₂ y)
        (fun y ↦ c * o₁ y + d * o₂ y) sigma r =
      c ^ 2 * factorTwoProfileStaticPoleSquareNumerator e₁ o₁ sigma r +
        2 * c * d *
          factorTwoProfileStaticPoleMixedNumerator
            e₁ o₁ e₂ o₂ sigma r +
        d ^ 2 * factorTwoProfileStaticPoleSquareNumerator e₂ o₂ sigma r := by
  have h₁ : IntervalIntegrable
      (factorTwoProfileStaticPoleHadamardSquare e₁ o₁ sigma r)
      volume (-1) (-1 + r) :=
    (continuous_factorTwoProfileStaticPoleHadamardSquare
      e₁ o₁ he₁ ho₁ sigma r).intervalIntegrable (-1) (-1 + r)
  have h₂ : IntervalIntegrable
      (factorTwoProfileStaticPoleHadamardSquare e₂ o₂ sigma r)
      volume (-1) (-1 + r) :=
    (continuous_factorTwoProfileStaticPoleHadamardSquare
      e₂ o₂ he₂ ho₂ sigma r).intervalIntegrable (-1) (-1 + r)
  have hm : IntervalIntegrable
      (factorTwoProfileStaticPoleHadamardMixedIntegrand
        e₁ o₁ e₂ o₂ sigma r) volume (-1) (-1 + r) :=
    (continuous_factorTwoProfileStaticPoleHadamardMixedIntegrand
      e₁ o₁ e₂ o₂ he₁ ho₁ he₂ ho₂ sigma r).intervalIntegrable
        (-1) (-1 + r)
  unfold factorTwoProfileStaticPoleSquareNumerator
    factorTwoProfileStaticPoleMixedNumerator
  rw [show (fun x : ℝ ↦
      factorTwoProfileStaticPoleHadamardSquare
        (fun y ↦ c * e₁ y + d * e₂ y)
        (fun y ↦ c * o₁ y + d * o₂ y) sigma r x) =
      fun x ↦
        c ^ 2 * factorTwoProfileStaticPoleHadamardSquare e₁ o₁ sigma r x +
          2 * c * d *
            factorTwoProfileStaticPoleHadamardMixedIntegrand
              e₁ o₁ e₂ o₂ sigma r x +
          d ^ 2 * factorTwoProfileStaticPoleHadamardSquare e₂ o₂ sigma r x by
      funext x
      exact factorTwoProfileStaticPoleHadamardSquare_linearCombination_eq
        e₁ o₁ e₂ o₂ sigma r x c d,
    intervalIntegral.integral_add
      ((h₁.const_mul (c ^ 2)).add (hm.const_mul (2 * c * d)))
      (h₂.const_mul (d ^ 2)),
    intervalIntegral.integral_add
      (h₁.const_mul (c ^ 2)) (hm.const_mul (2 * c * d))]
  repeat rw [intervalIntegral.integral_const_mul]

/-- Cauchy--Schwarz for the integrated pole-square numerators at every
nonnegative endpoint length.  This is obtained from positivity of the exact
Hadamard square, not from a mode expansion. -/
theorem factorTwoProfileStaticPoleMixedNumerator_sq_le
    (e₁ o₁ e₂ o₂ : ℝ → ℝ)
    (he₁ : Continuous e₁) (ho₁ : Continuous o₁)
    (he₂ : Continuous e₂) (ho₂ : Continuous o₂)
    (sigma : ℝ) (hsigma : sigma ^ 2 = 1)
    (r : ℝ) (hr : 0 ≤ r) :
    factorTwoProfileStaticPoleMixedNumerator
          e₁ o₁ e₂ o₂ sigma r ^ 2 ≤
      factorTwoProfileStaticPoleSquareNumerator e₁ o₁ sigma r *
        factorTwoProfileStaticPoleSquareNumerator e₂ o₂ sigma r := by
  let Q₁ := factorTwoProfileStaticPoleSquareNumerator e₁ o₁ sigma r
  let Q₂ := factorTwoProfileStaticPoleSquareNumerator e₂ o₂ sigma r
  let B := factorTwoProfileStaticPoleMixedNumerator
    e₁ o₁ e₂ o₂ sigma r
  have hpencil : ∀ c d : ℝ,
      0 ≤ Q₁ * c ^ 2 + 2 * B * c * d + Q₂ * d ^ 2 := by
    intro c d
    have hnonneg := factorTwoProfileStaticPoleDefectNumerator_nonneg
      (fun y ↦ c * e₁ y + d * e₂ y)
      (fun y ↦ c * o₁ y + d * o₂ y) sigma hsigma r hr
    rw [factorTwoProfileStaticPoleDefectNumerator_eq_square
      (fun y ↦ c * e₁ y + d * e₂ y)
      (fun y ↦ c * o₁ y + d * o₂ y) sigma hsigma r,
      factorTwoProfileStaticPoleSquareNumerator_linearCombination_eq
        e₁ o₁ e₂ o₂ he₁ ho₁ he₂ ho₂ sigma r c d] at hnonneg
    dsimp only [Q₁, Q₂, B]
    nlinarith
  exact ((real_quadratic_pencil_nonneg_iff Q₁ Q₂ B).mp hpencil).2.2

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseProfileStaticPoleMixedCauchyStructural
