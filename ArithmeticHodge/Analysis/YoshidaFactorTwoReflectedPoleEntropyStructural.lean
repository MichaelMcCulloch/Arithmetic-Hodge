import ArithmeticHodge.Analysis.YoshidaEndpointPotentialBound
import ArithmeticHodge.Analysis.YoshidaFactorTwoReflectedPolePolynomialReductionStructural
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

set_option autoImplicit false

open Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoReflectedPoleEntropyStructural

open YoshidaEndpointPotentialBound
open YoshidaFactorTwoReflectedPolePolynomialReductionStructural

noncomputable section

/-!
# Signed endpoint entropy for reflected-pole selectors

The two endpoint logarithms share the singular even potential.  Their
difference is the following globally continuous signed entropy.  Extracting
it makes every reflected polynomial selector an exact potential-polynomial
term plus a continuous remainder.
-/

/-- Continuous signed binary entropy in the centered coordinate. -/
def reflectedEndpointSignedEntropy (x : ℝ) : ℝ :=
  Real.negMulLog ((x + 1) / 2) -
    Real.negMulLog ((1 - x) / 2)

@[fun_prop] theorem continuous_reflectedEndpointSignedEntropy :
    Continuous reflectedEndpointSignedEntropy := by
  unfold reflectedEndpointSignedEntropy
  fun_prop

theorem reflectedEndpointSignedEntropy_odd :
    Function.Odd reflectedEndpointSignedEntropy := by
  intro x
  unfold reflectedEndpointSignedEntropy
  rw [show (-x + 1) / 2 = (1 - x) / 2 by ring,
    show (1 - -x) / 2 = (x + 1) / 2 by ring]
  ring

@[simp] theorem reflectedEndpointSignedEntropy_neg_one :
    reflectedEndpointSignedEntropy (-1) = 0 := by
  simp [reflectedEndpointSignedEntropy]

@[simp] theorem reflectedEndpointSignedEntropy_one :
    reflectedEndpointSignedEntropy 1 = 0 := by
  simp [reflectedEndpointSignedEntropy]

/-- The sum of the two endpoint logarithms is exactly twice the shifted
endpoint potential. -/
theorem reflectedEndpointLogs_sum_eq_potential
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    -Real.log ((x + 1) / 2) + -Real.log ((1 - x) / 2) =
      2 * (yoshidaEndpointPotential x + Real.log 2) := by
  have hplus : x + 1 ≠ 0 := by linarith [hx.1]
  have hminus : 1 - x ≠ 0 := by linarith [hx.2]
  rw [Real.log_div hplus (by norm_num),
    Real.log_div hminus (by norm_num)]
  unfold yoshidaEndpointPotential
  rw [show 1 - x ^ 2 = (x + 1) * (1 - x) by ring,
    Real.log_mul hplus hminus]
  ring

/-- Exact extraction from the logarithm singular at the right endpoint. -/
theorem reflectedEndpointLogPlus_eq_potential_add_entropy
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    -Real.log ((x + 1) / 2) =
      (1 - x) * (yoshidaEndpointPotential x + Real.log 2) +
        reflectedEndpointSignedEntropy x := by
  have hsum := reflectedEndpointLogs_sum_eq_potential hx
  have hhalf :
      yoshidaEndpointPotential x + Real.log 2 =
        (-Real.log ((x + 1) / 2) +
          -Real.log ((1 - x) / 2)) / 2 := by
    linarith
  rw [hhalf]
  unfold reflectedEndpointSignedEntropy Real.negMulLog
  ring

/-- Exact extraction from the logarithm singular at the left endpoint. -/
theorem reflectedEndpointLogMinus_eq_potential_sub_entropy
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    -Real.log ((1 - x) / 2) =
      (1 + x) * (yoshidaEndpointPotential x + Real.log 2) -
        reflectedEndpointSignedEntropy x := by
  have hsum := reflectedEndpointLogs_sum_eq_potential hx
  have hhalf :
      yoshidaEndpointPotential x + Real.log 2 =
        (-Real.log ((x + 1) / 2) +
          -Real.log ((1 - x) / 2)) / 2 := by
    linarith
  rw [hhalf]
  unfold reflectedEndpointSignedEntropy Real.negMulLog
  ring

/-- Polynomial coefficient of the potential in the symmetric reflected
selector. -/
def reflectedPoleKPotentialSelector (p : ℝ[X]) (x : ℝ) : ℝ :=
  (1 - x) * p.eval ((x + 3) / 2) +
    (1 + x) * p.eval ((x - 1) / 2)

/-- Polynomial coefficient of the potential in the alternating reflected
selector. -/
def reflectedPoleJPotentialSelector (p : ℝ[X]) (x : ℝ) : ℝ :=
  (1 - x) * p.eval ((x + 3) / 2) -
    (1 + x) * p.eval ((x - 1) / 2)

/-- Continuous remainder after removing the potential from the symmetric
reflected selector. -/
def reflectedPoleKEntropyRemainder (p : ℝ[X]) (x : ℝ) : ℝ :=
  Real.log 2 * reflectedPoleKPotentialSelector p x +
    reflectedEndpointSignedEntropy x *
      (p.eval ((x + 3) / 2) - p.eval ((x - 1) / 2))

/-- Continuous remainder after removing the potential from the alternating
reflected selector. -/
def reflectedPoleJEntropyRemainder (p : ℝ[X]) (x : ℝ) : ℝ :=
  Real.log 2 * reflectedPoleJPotentialSelector p x +
    reflectedEndpointSignedEntropy x *
      (p.eval ((x + 3) / 2) + p.eval ((x - 1) / 2))

theorem continuous_reflectedPoleKEntropyRemainder (p : ℝ[X]) :
    Continuous (reflectedPoleKEntropyRemainder p) := by
  unfold reflectedPoleKEntropyRemainder reflectedPoleKPotentialSelector
  fun_prop

theorem continuous_reflectedPoleJEntropyRemainder (p : ℝ[X]) :
    Continuous (reflectedPoleJEntropyRemainder p) := by
  unfold reflectedPoleJEntropyRemainder reflectedPoleJPotentialSelector
  fun_prop

/-- Symmetric reflected logarithmic selector equals a potential-polynomial
row plus a continuous entropy remainder. -/
theorem reflectedPoleKLogSelector_eq_potential_add_entropy
    (p : ℝ[X]) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    reflectedPoleKLogSelector p x =
      yoshidaEndpointPotential x * reflectedPoleKPotentialSelector p x +
        reflectedPoleKEntropyRemainder p x := by
  rw [show reflectedPoleKLogSelector p x =
      p.eval ((x + 3) / 2) * (-Real.log ((x + 1) / 2)) +
        p.eval ((x - 1) / 2) * (-Real.log ((1 - x) / 2)) by
    unfold reflectedPoleKLogSelector
    ring,
    reflectedEndpointLogPlus_eq_potential_add_entropy hx,
    reflectedEndpointLogMinus_eq_potential_sub_entropy hx]
  unfold reflectedPoleKEntropyRemainder reflectedPoleKPotentialSelector
  ring

/-- Alternating reflected logarithmic selector equals a potential-polynomial
row plus a continuous entropy remainder. -/
theorem reflectedPoleJLogSelector_eq_potential_add_entropy
    (p : ℝ[X]) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    reflectedPoleJLogSelector p x =
      yoshidaEndpointPotential x * reflectedPoleJPotentialSelector p x +
        reflectedPoleJEntropyRemainder p x := by
  rw [show reflectedPoleJLogSelector p x =
      p.eval ((x + 3) / 2) * (-Real.log ((x + 1) / 2)) -
        p.eval ((x - 1) / 2) * (-Real.log ((1 - x) / 2)) by
    unfold reflectedPoleJLogSelector
    ring,
    reflectedEndpointLogPlus_eq_potential_add_entropy hx,
    reflectedEndpointLogMinus_eq_potential_sub_entropy hx]
  unfold reflectedPoleJEntropyRemainder reflectedPoleJPotentialSelector
  ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoReflectedPoleEntropyStructural
