import ArithmeticHodge.Analysis.YoshidaFiveCellEndpointOperatorProbeStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreFourFiveStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFiveCellLowModeClosureStructural

noncomputable section

open MultiplicativeWeilFiveCellSingleProfileStructural
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointOcticPotential
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFiveCellEndpointOperatorProbeStructural
open YoshidaGeneralEndpointPhysicalRealQuadraticStructural

/-!
# A structural low-mode probe for the five-cell operator

Below shifted-Legendre cutoff nine, the endpoint-zero even and odd carriers
already contain the adjacent differences

* `P₀ - P₂`, `P₂ - P₄`,
* `P₁ - P₃`, `P₃ - P₅`.

The endpoint pairing is reduced exactly on these two-dimensional blocks.
The calculation is a symbolic polarization and Schur determinant, not a
modal or spatial enumeration.
-/

/-- Symmetric polarization of the five-cell endpoint pairing. -/
def fiveCellEndpointPolarCross (u v : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ in (1 / 3 : ℝ)..1,
    (u x * v (x - 4 / 3) + v x * u (x - 4 / 3))

/-- Exact quadratic expansion of the endpoint atom on every continuous
two-profile span. -/
theorem fiveCellEndpointPairing_linearCombination
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (a b : ℝ) :
    fiveCellEndpointPairing (fun x ↦ a * u x + b * v x) =
      a ^ 2 * fiveCellEndpointPairing u +
        a * b * fiveCellEndpointPolarCross u v +
          b ^ 2 * fiveCellEndpointPairing v := by
  have huu : IntervalIntegrable
      (fun x : ℝ ↦ u x * u (x - 4 / 3)) volume (1 / 3) 1 :=
    (by fun_prop : Continuous
      (fun x : ℝ ↦ u x * u (x - 4 / 3))).intervalIntegrable _ _
  have huv : IntervalIntegrable
      (fun x : ℝ ↦
        u x * v (x - 4 / 3) + v x * u (x - 4 / 3))
      volume (1 / 3) 1 :=
    (by fun_prop : Continuous (fun x : ℝ ↦
      u x * v (x - 4 / 3) +
        v x * u (x - 4 / 3))).intervalIntegrable _ _
  have hvv : IntervalIntegrable
      (fun x : ℝ ↦ v x * v (x - 4 / 3)) volume (1 / 3) 1 :=
    (by fun_prop : Continuous
      (fun x : ℝ ↦ v x * v (x - 4 / 3))).intervalIntegrable _ _
  unfold fiveCellEndpointPairing fiveCellEndpointPolarCross
  calc
    (∫ x : ℝ in (1 / 3 : ℝ)..1,
        (a * u x + b * v x) *
          (a * u (x - 4 / 3) + b * v (x - 4 / 3))) =
        ∫ x : ℝ in (1 / 3 : ℝ)..1,
          (a ^ 2 * (u x * u (x - 4 / 3)) +
            a * b *
              (u x * v (x - 4 / 3) + v x * u (x - 4 / 3))) +
            b ^ 2 * (v x * v (x - 4 / 3)) := by
      apply intervalIntegral.integral_congr
      intro x _hx
      ring
    _ = (∫ x : ℝ in (1 / 3 : ℝ)..1,
          a ^ 2 * (u x * u (x - 4 / 3)) +
            a * b *
              (u x * v (x - 4 / 3) + v x * u (x - 4 / 3))) +
        ∫ x : ℝ in (1 / 3 : ℝ)..1,
          b ^ 2 * (v x * v (x - 4 / 3)) := by
      rw [intervalIntegral.integral_add
        ((huu.const_mul (a ^ 2)).add (huv.const_mul (a * b)))
        (hvv.const_mul (b ^ 2))]
    _ = ((∫ x : ℝ in (1 / 3 : ℝ)..1,
          a ^ 2 * (u x * u (x - 4 / 3))) +
        ∫ x : ℝ in (1 / 3 : ℝ)..1,
          a * b *
            (u x * v (x - 4 / 3) + v x * u (x - 4 / 3))) +
        ∫ x : ℝ in (1 / 3 : ℝ)..1,
          b ^ 2 * (v x * v (x - 4 / 3)) := by
      rw [intervalIntegral.integral_add
        (huu.const_mul (a ^ 2)) (huv.const_mul (a * b))]
    _ = _ := by
      repeat rw [intervalIntegral.integral_const_mul]

/-- Endpoint-zero adjacent even shifted-Legendre differences. -/
def fiveCellEvenLow02 (x : ℝ) : ℝ :=
  centeredEvenP0 x - centeredEvenP2 x

def fiveCellEvenLow24 (x : ℝ) : ℝ :=
  centeredEvenP2 x - factorTwoCenteredP4 x

/-- Endpoint-zero adjacent odd shifted-Legendre differences. -/
def fiveCellOddLow13 (x : ℝ) : ℝ :=
  centeredP1 x - centeredP3 x

def fiveCellOddLow35 (x : ℝ) : ℝ :=
  centeredP3 x - factorTwoCenteredP5 x

/-- The two exact low parity blocks. -/
def fiveCellEvenLowProfile (a b x : ℝ) : ℝ :=
  a * fiveCellEvenLow02 x + b * fiveCellEvenLow24 x

def fiveCellOddLowProfile (a b x : ℝ) : ℝ :=
  a * fiveCellOddLow13 x + b * fiveCellOddLow35 x

theorem fiveCellEvenLow02_eq (x : ℝ) :
    fiveCellEvenLow02 x = (3 / 2 : ℝ) * (1 - x ^ 2) := by
  unfold fiveCellEvenLow02 centeredEvenP0 centeredEvenP2
  ring

theorem fiveCellEvenLow24_eq (x : ℝ) :
    fiveCellEvenLow24 x =
      (77 / 72 : ℝ) * (1 - x ^ 2) +
        (35 / 8 : ℝ) * ((1 - x ^ 2) * (x ^ 2 - 4 / 9)) := by
  unfold fiveCellEvenLow24 centeredEvenP2 factorTwoCenteredP4
  ring

theorem fiveCellOddLow13_eq (x : ℝ) :
    fiveCellOddLow13 x = (5 / 2 : ℝ) * (x * (1 - x ^ 2)) := by
  unfold fiveCellOddLow13 centeredP1 centeredP3
  ring

theorem fiveCellOddLow35_eq (x : ℝ) :
    fiveCellOddLow35 x =
      (1 / 8 : ℝ) * (x * (1 - x ^ 2)) +
        (63 / 8 : ℝ) * (x * (1 - x ^ 2) * (x ^ 2 - 4 / 9)) := by
  unfold fiveCellOddLow35 centeredP3 factorTwoCenteredP5
  ring

theorem fiveCellEvenLowProfile_eq_witnessCoordinates (a b : ℝ) :
    fiveCellEvenLowProfile a b = fun x ↦
      ((3 / 2 : ℝ) * a + 77 / 72 * b) *
          fiveCellEvenPositiveWitness x +
        (35 / 8 : ℝ) * b * fiveCellEvenNegativeWitness x := by
  funext x
  unfold fiveCellEvenLowProfile fiveCellEvenPositiveWitness
    fiveCellEvenNegativeWitness
  rw [fiveCellEvenLow02_eq, fiveCellEvenLow24_eq]
  ring

theorem fiveCellOddLowProfile_eq_witnessCoordinates (a b : ℝ) :
    fiveCellOddLowProfile a b = fun x ↦
      ((5 / 2 : ℝ) * a + 1 / 8 * b) *
          fiveCellOddNegativeWitness x +
        (63 / 8 : ℝ) * b * fiveCellOddPositiveWitness x := by
  funext x
  unfold fiveCellOddLowProfile fiveCellOddNegativeWitness
    fiveCellOddPositiveWitness
  rw [fiveCellOddLow13_eq, fiveCellOddLow35_eq]
  ring

theorem fiveCellEvenLowProfile_contDiff (a b : ℝ) :
    ContDiff ℝ 1 (fiveCellEvenLowProfile a b) := by
  unfold fiveCellEvenLowProfile fiveCellEvenLow02 fiveCellEvenLow24
    centeredEvenP0 centeredEvenP2 factorTwoCenteredP4
  fun_prop

theorem fiveCellOddLowProfile_contDiff (a b : ℝ) :
    ContDiff ℝ 1 (fiveCellOddLowProfile a b) := by
  unfold fiveCellOddLowProfile fiveCellOddLow13 fiveCellOddLow35
    centeredP1 centeredP3 factorTwoCenteredP5
  fun_prop

theorem fiveCellEvenLowProfile_even (a b : ℝ) :
    Function.Even (fiveCellEvenLowProfile a b) := by
  intro x
  unfold fiveCellEvenLowProfile fiveCellEvenLow02 fiveCellEvenLow24
    centeredEvenP0 centeredEvenP2 factorTwoCenteredP4
  ring

theorem fiveCellOddLowProfile_odd (a b : ℝ) :
    Function.Odd (fiveCellOddLowProfile a b) := by
  intro x
  unfold fiveCellOddLowProfile fiveCellOddLow13 fiveCellOddLow35
    centeredP1 centeredP3 factorTwoCenteredP5
  ring

theorem fiveCellEvenLowProfile_endpoints_zero (a b : ℝ) :
    fiveCellEvenLowProfile a b (-1) = 0 ∧
      fiveCellEvenLowProfile a b 1 = 0 := by
  constructor <;>
    norm_num [fiveCellEvenLowProfile, fiveCellEvenLow02,
      fiveCellEvenLow24, centeredEvenP0, centeredEvenP2,
      factorTwoCenteredP4]

theorem fiveCellOddLowProfile_endpoints_zero (a b : ℝ) :
    fiveCellOddLowProfile a b (-1) = 0 ∧
      fiveCellOddLowProfile a b 1 = 0 := by
  constructor <;>
    norm_num [fiveCellOddLowProfile, fiveCellOddLow13,
      fiveCellOddLow35, centeredP1, centeredP3, factorTwoCenteredP5]

/-- The full five-cell operator restricts to the exact even parity/rank
operator on the low even block. -/
theorem fiveCellEndpointOperator_evenLow_eq_parityOperator (a b : ℝ) :
    fiveCellEndpointOperator (fiveCellEvenLowProfile a b) =
      fiveCellEvenParityOperator (fiveCellEvenLowProfile a b) := by
  exact fiveCellEndpointOperator_eq_evenParityOperator
    (fiveCellEvenLowProfile a b)
    (fiveCellEvenLowProfile_contDiff a b).continuous
    ((fiveCellEvenLowProfile_contDiff a b).contDiffOn.locallyLipschitzOn
      (convex_Icc (-1) 1))
    (fiveCellEvenLowProfile_even a b)

/-- The analogous exact odd parity/rank restriction. -/
theorem fiveCellEndpointOperator_oddLow_eq_parityOperator (a b : ℝ) :
    fiveCellEndpointOperator (fiveCellOddLowProfile a b) =
      fiveCellOddParityOperator (fiveCellOddLowProfile a b) := by
  exact fiveCellEndpointOperator_eq_oddParityOperator
    (fiveCellOddLowProfile a b)
    (fiveCellOddLowProfile_contDiff a b).continuous
    ((fiveCellOddLowProfile_contDiff a b).contDiffOn.locallyLipschitzOn
      (convex_Icc (-1) 1))
    (fiveCellOddLowProfile_odd a b)

/-! ## Exact endpoint Schur blocks -/

private theorem integral_polynomial_ten
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ l r : ℝ) :
    (∫ x : ℝ in l..r,
      a₀ * x ^ 0 + a₁ * x ^ 1 + a₂ * x ^ 2 + a₃ * x ^ 3 + a₄ * x ^ 4 +
        a₅ * x ^ 5 + a₆ * x ^ 6 + a₇ * x ^ 7 + a₈ * x ^ 8 +
          a₉ * x ^ 9 + a₁₀ * x ^ 10) =
      a₀ * (r - l) + a₁ * (r ^ 2 - l ^ 2) / 2 +
        a₂ * (r ^ 3 - l ^ 3) / 3 + a₃ * (r ^ 4 - l ^ 4) / 4 +
          a₄ * (r ^ 5 - l ^ 5) / 5 + a₅ * (r ^ 6 - l ^ 6) / 6 +
            a₆ * (r ^ 7 - l ^ 7) / 7 + a₇ * (r ^ 8 - l ^ 8) / 8 +
              a₈ * (r ^ 9 - l ^ 9) / 9 + a₉ * (r ^ 10 - l ^ 10) / 10 +
                a₁₀ * (r ^ 11 - l ^ 11) / 11 := by
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) l r)
    (Continuous.intervalIntegrable (by fun_prop) l r)]
  repeat rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

theorem fiveCellEndpointPolarCross_evenWitnesses :
    fiveCellEndpointPolarCross fiveCellEvenPositiveWitness
        fiveCellEvenNegativeWitness = 1376 / 229635 := by
  unfold fiveCellEndpointPolarCross
  rw [show (fun x : ℝ ↦
      fiveCellEvenPositiveWitness x *
          fiveCellEvenNegativeWitness (x - 4 / 3) +
        fiveCellEvenNegativeWitness x *
          fiveCellEvenPositiveWitness (x - 4 / 3)) =
      fun x ↦ (-56 / 81) * x ^ 0 + (40 / 9) * x ^ 1 +
        (-718 / 81) * x ^ 2 + (32 / 9) * x ^ 3 +
          (68 / 9) * x ^ 4 + (-8) * x ^ 5 + 2 * x ^ 6 +
            0 * x ^ 7 + 0 * x ^ 8 + 0 * x ^ 9 + 0 * x ^ 10 by
    funext x
    unfold fiveCellEvenPositiveWitness fiveCellEvenNegativeWitness
    ring,
    integral_polynomial_ten]
  norm_num

theorem fiveCellEndpointPolarCross_oddWitnesses :
    fiveCellEndpointPolarCross fiveCellOddNegativeWitness
        fiveCellOddPositiveWitness = -14752 / 6200145 := by
  unfold fiveCellEndpointPolarCross
  rw [show (fun x : ℝ ↦
      fiveCellOddNegativeWitness x *
          fiveCellOddPositiveWitness (x - 4 / 3) +
        fiveCellOddPositiveWitness x *
          fiveCellOddNegativeWitness (x - 4 / 3)) =
      fun x ↦ 0 * x ^ 0 + (224 / 243) * x ^ 1 +
        (-536 / 81) * x ^ 2 + (3952 / 243) * x ^ 3 +
          (-1102 / 81) * x ^ 4 + (-176 / 27) * x ^ 5 +
            (164 / 9) * x ^ 6 + (-32 / 3) * x ^ 7 +
              2 * x ^ 8 + 0 * x ^ 9 + 0 * x ^ 10 by
    funext x
    unfold fiveCellOddNegativeWitness fiveCellOddPositiveWitness
    ring,
    integral_polynomial_ten]
  norm_num

/-- Exact endpoint quadratic on the even adjacent-difference block. -/
theorem fiveCellEndpointPairing_evenLowProfile (a b : ℝ) :
    fiveCellEndpointPairing (fiveCellEvenLowProfile a b) =
      (124 / 405 : ℝ) * a ^ 2 +
        (5204 / 10935 : ℝ) * a * b +
          (74788 / 885735 : ℝ) * b ^ 2 := by
  rw [fiveCellEvenLowProfile_eq_witnessCoordinates]
  rw [fiveCellEndpointPairing_linearCombination
    fiveCellEvenPositiveWitness fiveCellEvenNegativeWitness
    fiveCellEvenPositiveWitness_contDiff.continuous
    fiveCellEvenNegativeWitness_contDiff.continuous]
  rw [fiveCellEndpointPairing_evenPositiveWitness,
    fiveCellEndpointPolarCross_evenWitnesses,
    fiveCellEndpointPairing_evenNegativeWitness]
  ring

/-- Exact endpoint quadratic on the odd adjacent-difference block. -/
theorem fiveCellEndpointPairing_oddLowProfile (a b : ℝ) :
    fiveCellEndpointPairing (fiveCellOddLowProfile a b) =
      (-5500 / 15309 : ℝ) * a ^ 2 +
        (-11404 / 137781 : ℝ) * a * b +
          (188764 / 1515591 : ℝ) * b ^ 2 := by
  rw [fiveCellOddLowProfile_eq_witnessCoordinates]
  rw [fiveCellEndpointPairing_linearCombination
    fiveCellOddNegativeWitness fiveCellOddPositiveWitness
    fiveCellOddNegativeWitness_contDiff.continuous
    fiveCellOddPositiveWitness_contDiff.continuous]
  rw [fiveCellEndpointPairing_oddNegativeWitness,
    fiveCellEndpointPolarCross_oddWitnesses,
    fiveCellEndpointPairing_oddPositiveWitness]
  ring

/-- Exact rank-one Schur congruence of the even low endpoint block.  One
positive square and one negative square remain; the signature is exposed
without diagonalizing numerically. -/
theorem fiveCellEndpointPairing_evenLowProfile_schur (a b : ℝ) :
    fiveCellEndpointPairing (fiveCellEvenLowProfile a b) =
      (124 / 405 : ℝ) * (a + 1301 / 1674 * b) ^ 2 -
        (551875 / 5491557 : ℝ) * b ^ 2 := by
  rw [fiveCellEndpointPairing_evenLowProfile]
  ring

/-- Exact rank-one Schur congruence of the odd low endpoint block, pivoted
on its positive `P₃-P₅` direction. -/
theorem fiveCellEndpointPairing_oddLowProfile_schur (a b : ℝ) :
    fiveCellEndpointPairing (fiveCellOddLowProfile a b) =
      (188764 / 1515591 : ℝ) *
          (b - 31361 / 94382 * a) ^ 2 -
        (346480673 / 928860453 : ℝ) * a ^ 2 := by
  rw [fiveCellEndpointPairing_oddLowProfile]
  ring

/-- The even endpoint matrix has negative determinant although both
adjacent-difference diagonal entries are positive. -/
theorem fiveCellEvenLowEndpointDeterminant_eq :
    (124 / 405 : ℝ) * (74788 / 885735) -
        (2602 / 10935) ^ 2 =
      -441500 / 14348907 := by
  norm_num

/-- The odd endpoint matrix likewise has one positive and one negative
Schur direction. -/
theorem fiveCellOddLowEndpointDeterminant_eq :
    (-5500 / 15309 : ℝ) * (188764 / 1515591) -
        (-5702 / 137781) ^ 2 =
      -17998996 / 387420489 := by
  norm_num

/-- Structural counterdirection in the even low block: each basis vector
has positive endpoint pairing, but their difference has negative pairing.
Thus a diagonal-by-mode endpoint relaxation is invalid. -/
theorem fiveCellEvenLowEndpoint_offDiagonal_obstruction :
    0 < fiveCellEndpointPairing (fiveCellEvenLowProfile 1 0) ∧
      0 < fiveCellEndpointPairing (fiveCellEvenLowProfile 0 1) ∧
        fiveCellEndpointPairing (fiveCellEvenLowProfile 1 (-1)) < 0 := by
  repeat' rw [fiveCellEndpointPairing_evenLowProfile]
  norm_num

/-- The odd low block already realizes both signs on its two natural
adjacent-difference axes. -/
theorem fiveCellOddLowEndpoint_axis_obstruction :
    fiveCellEndpointPairing (fiveCellOddLowProfile 1 0) < 0 ∧
      0 < fiveCellEndpointPairing (fiveCellOddLowProfile 0 1) := by
  rw [fiveCellEndpointPairing_oddLowProfile,
    fiveCellEndpointPairing_oddLowProfile]
  norm_num

/-- On the even Schur counterdirection the retained prime term is an exact
positive rational multiple of `sqrt 2 * log 2`; the unresolved part is now
only the physical parity operator. -/
theorem fiveCellEndpointOperator_evenLowCounterdirection_eq :
    fiveCellEndpointOperator (fiveCellEvenLowProfile 1 (-1)) =
      centeredClippedPhysicalQuadratic fiveCellOperatorHalfWidth
          (fiveCellEvenLowProfile 1 (-1)) +
        Real.sqrt 2 * Real.log 2 * (75548 / 885735 : ℝ) := by
  unfold fiveCellEndpointOperator
  rw [fiveCellEndpointPairing_evenLowProfile]
  ring

end

end ArithmeticHodge.Analysis.YoshidaFiveCellLowModeClosureStructural
