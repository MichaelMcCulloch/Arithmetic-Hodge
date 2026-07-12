import ArithmeticHodge.Analysis.YoshidaMomentSeries
import ArithmeticHodge.Analysis.YoshidaShiftedGeometricSeries
import ArithmeticHodge.Analysis.YoshidaClippedMomentBridge

set_option autoImplicit false

open MeasureTheory Real
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaDiagonalMomentSeries

noncomputable section

open YoshidaClippedMomentBridge
open YoshidaMomentSeries
open YoshidaOddGramPrefix
open YoshidaRenormalizedGeometricKernel
open YoshidaShiftedGeometricSeries

/-!
# Exact series terms for Yoshida's diagonal moments

The diagonal moment is the diagonal odd Gram value after removing its
normalized sine-moment contribution.  Evaluating the full clipped diagonal
correlation against one odd exponential rate reveals an additional useful
cancellation: its two second-order endpoint corrections combine into a
residual with a squared Cauchy denominator.

This module records only exact identities.  Numerical enclosures and tail
bounds belong to the certificate layer.
-/

/-- Recover the diagonal moment from the corresponding odd Gram entry by
subtracting its normalized sine-moment contribution. -/
theorem yoshidaDiagonalMoment_eq_diagonal_oddMomentGram_sub_sine
    {n : ℕ} (hn : n ≠ 0) :
    yoshidaDiagonalMoment n =
      oddMomentGram yoshidaSineMoment yoshidaDiagonalMoment n n -
        yoshidaSineMoment n / (2 * Real.pi * (n : ℝ)) := by
  rw [oddMomentGram, if_pos rfl, yoshidaKappa]
  field_simp [yoshidaLength_pos.ne', Real.pi_ne_zero,
    Nat.cast_ne_zero.mpr hn]
  ring

private def expCosPrimitive (b κ : ℝ) (u : ℝ) : ℝ :=
  Real.exp (-b * u) *
    (-b * Real.cos (κ * u) + κ * Real.sin (κ * u)) /
      (b ^ 2 + κ ^ 2)

private def expSinPrimitive (b κ : ℝ) (u : ℝ) : ℝ :=
  Real.exp (-b * u) *
    (-b * Real.sin (κ * u) - κ * Real.cos (κ * u)) /
      (b ^ 2 + κ ^ 2)

private theorem hasDerivAt_expCosPrimitive
    {b κ : ℝ} (hden : b ^ 2 + κ ^ 2 ≠ 0) (u : ℝ) :
    HasDerivAt (expCosPrimitive b κ)
      (Real.exp (-b * u) * Real.cos (κ * u)) u := by
  have hexp : HasDerivAt (fun x : ℝ ↦ Real.exp (-b * x))
      (-b * Real.exp (-b * u)) u := by
    convert (Real.hasDerivAt_exp (-b * u)).comp u
      ((hasDerivAt_id u).const_mul (-b)) using 1
    ring_nf
  have hcos : HasDerivAt (fun x : ℝ ↦ Real.cos (κ * x))
      (-κ * Real.sin (κ * u)) u := by
    convert (Real.hasDerivAt_cos (κ * u)).comp u
      ((hasDerivAt_id u).const_mul κ) using 1
    ring_nf
  have hsin : HasDerivAt (fun x : ℝ ↦ Real.sin (κ * x))
      (κ * Real.cos (κ * u)) u := by
    convert (Real.hasDerivAt_sin (κ * u)).comp u
      ((hasDerivAt_id u).const_mul κ) using 1
    ring_nf
  unfold expCosPrimitive
  convert (hexp.mul
    ((hcos.const_mul (-b)).add (hsin.const_mul κ))).div_const
      (b ^ 2 + κ ^ 2) using 1
  simp only [Pi.add_apply]
  field_simp [hden]
  ring

private theorem hasDerivAt_expSinPrimitive
    {b κ : ℝ} (hden : b ^ 2 + κ ^ 2 ≠ 0) (u : ℝ) :
    HasDerivAt (expSinPrimitive b κ)
      (Real.exp (-b * u) * Real.sin (κ * u)) u := by
  have hexp : HasDerivAt (fun x : ℝ ↦ Real.exp (-b * x))
      (-b * Real.exp (-b * u)) u := by
    convert (Real.hasDerivAt_exp (-b * u)).comp u
      ((hasDerivAt_id u).const_mul (-b)) using 1
    ring_nf
  have hsin : HasDerivAt (fun x : ℝ ↦ Real.sin (κ * x))
      (κ * Real.cos (κ * u)) u := by
    convert (Real.hasDerivAt_sin (κ * u)).comp u
      ((hasDerivAt_id u).const_mul κ) using 1
    ring_nf
  have hcos : HasDerivAt (fun x : ℝ ↦ Real.cos (κ * x))
      (-κ * Real.sin (κ * u)) u := by
    convert (Real.hasDerivAt_cos (κ * u)).comp u
      ((hasDerivAt_id u).const_mul κ) using 1
    ring_nf
  unfold expSinPrimitive
  convert (hexp.mul
    ((hsin.const_mul (-b)).sub (hcos.const_mul κ))).div_const
      (b ^ 2 + κ ^ 2) using 1
  simp only [Pi.sub_apply]
  field_simp [hden]
  ring

private def expUCosPrimitive (b κ : ℝ) (u : ℝ) : ℝ :=
  u * expCosPrimitive b κ u -
    ((-b / (b ^ 2 + κ ^ 2)) * expCosPrimitive b κ u +
      (κ / (b ^ 2 + κ ^ 2)) * expSinPrimitive b κ u)

private theorem hasDerivAt_expUCosPrimitive
    {b κ : ℝ} (hden : b ^ 2 + κ ^ 2 ≠ 0) (u : ℝ) :
    HasDerivAt (expUCosPrimitive b κ)
      (u * (Real.exp (-b * u) * Real.cos (κ * u))) u := by
  have hc := hasDerivAt_expCosPrimitive hden u
  have hs := hasDerivAt_expSinPrimitive hden u
  unfold expUCosPrimitive
  convert ((hasDerivAt_id u).mul hc).sub
    ((hc.const_mul (-b / (b ^ 2 + κ ^ 2))).add
      (hs.const_mul (κ / (b ^ 2 + κ ^ 2)))) using 1
  simp only [id_eq, expCosPrimitive]
  field_simp [hden]
  ring

private theorem integral_exp_neg_mul_cos
    {b κ L : ℝ} (hden : b ^ 2 + κ ^ 2 ≠ 0)
    (hsin : Real.sin (κ * L) = 0)
    (hcos : Real.cos (κ * L) = 1) :
    (∫ u in 0..L, Real.exp (-b * u) * Real.cos (κ * u)) =
      b * (1 - Real.exp (-b * L)) / (b ^ 2 + κ ^ 2) := by
  have hint : IntervalIntegrable
      (fun u : ℝ ↦ Real.exp (-b * u) * Real.cos (κ * u)) volume 0 L :=
    Continuous.intervalIntegrable (by fun_prop) 0 L
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _hu ↦ hasDerivAt_expCosPrimitive hden u) hint
  rw [hfund]
  simp only [expCosPrimitive, mul_zero, Real.exp_zero, Real.cos_zero,
    Real.sin_zero, hsin, hcos]
  field_simp [hden]
  ring

private theorem integral_u_mul_exp_neg_mul_cos
    {b κ L : ℝ} (hden : b ^ 2 + κ ^ 2 ≠ 0)
    (hsin : Real.sin (κ * L) = 0)
    (hcos : Real.cos (κ * L) = 1) :
    (∫ u in 0..L, u * (Real.exp (-b * u) * Real.cos (κ * u))) =
      2 * b ^ 2 * (1 - Real.exp (-b * L)) /
          (b ^ 2 + κ ^ 2) ^ 2 -
        (1 - Real.exp (-b * L) + b * L * Real.exp (-b * L)) /
          (b ^ 2 + κ ^ 2) := by
  have hint : IntervalIntegrable
      (fun u : ℝ ↦ u * (Real.exp (-b * u) * Real.cos (κ * u)))
      volume 0 L := Continuous.intervalIntegrable (by fun_prop) 0 L
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _hu ↦ hasDerivAt_expUCosPrimitive hden u) hint
  rw [hfund]
  simp only [expUCosPrimitive, expCosPrimitive, expSinPrimitive, mul_zero,
    zero_mul, Real.exp_zero, Real.cos_zero, Real.sin_zero, hsin, hcos]
  field_simp [hden]
  ring

private theorem integral_exp_neg_mul_fullDiagonalCorrelation
    {b κ L : ℝ} (hL : L ≠ 0) (hκ : κ ≠ 0)
    (hden : b ^ 2 + κ ^ 2 ≠ 0)
    (hsin : Real.sin (κ * L) = 0)
    (hcos : Real.cos (κ * L) = 1) :
    (∫ u in 0..L,
      Real.exp (-b * u) *
        (((L - u) * Real.cos (κ * u) + Real.sin (κ * u) / κ) / L)) =
      b / (b ^ 2 + κ ^ 2) +
        2 * κ ^ 2 * (1 - Real.exp (-b * L)) /
          (L * (b ^ 2 + κ ^ 2) ^ 2) := by
  have hIcos := integral_exp_neg_mul_cos hden hsin hcos
  have hIucos := integral_u_mul_exp_neg_mul_cos hden hsin hcos
  have hIsin := YoshidaMomentSeries.integral_exp_neg_mul_sin
    hden hsin hcos
  have hcosInt : IntervalIntegrable
      (fun u : ℝ ↦ Real.exp (-b * u) * Real.cos (κ * u)) volume 0 L :=
    Continuous.intervalIntegrable (by fun_prop) 0 L
  have hucosInt : IntervalIntegrable
      (fun u : ℝ ↦ u * (Real.exp (-b * u) * Real.cos (κ * u)))
      volume 0 L := Continuous.intervalIntegrable (by fun_prop) 0 L
  have hsinInt : IntervalIntegrable
      (fun u : ℝ ↦ Real.exp (-b * u) * Real.sin (κ * u)) volume 0 L :=
    Continuous.intervalIntegrable (by fun_prop) 0 L
  rw [show (fun u : ℝ ↦
      Real.exp (-b * u) *
        (((L - u) * Real.cos (κ * u) + Real.sin (κ * u) / κ) / L)) =
      fun u : ℝ ↦
        Real.exp (-b * u) * Real.cos (κ * u) -
          (1 / L) * (u * (Real.exp (-b * u) * Real.cos (κ * u))) +
          (1 / (L * κ)) * (Real.exp (-b * u) * Real.sin (κ * u)) by
    funext u
    field_simp [hL, hκ]]
  rw [intervalIntegral.integral_add
      (hcosInt.sub (hucosInt.const_mul (1 / L)))
      (hsinInt.const_mul (1 / (L * κ))),
    intervalIntegral.integral_sub hcosInt (hucosInt.const_mul (1 / L)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    hIcos, hIucos, hIsin]
  field_simp [hL, hκ, hden]
  ring

/-- The two apparent denominator-one endpoint corrections combine into a
squared-denominator residual. -/
theorem diagonal_second_order_cancellation
    {b κ L q : ℝ} (hL : L ≠ 0) (hden : b ^ 2 + κ ^ 2 ≠ 0) :
    4 * (1 - q) / (L * (b ^ 2 + κ ^ 2)) -
        4 * b ^ 2 * (1 - q) / (L * (b ^ 2 + κ ^ 2) ^ 2) =
      4 * κ ^ 2 * (1 - q) / (L * (b ^ 2 + κ ^ 2) ^ 2) := by
  field_simp [hL, hden]
  ring

/-- Exact diagonal full-correlation Laplace term.  The endpoint residual has
the squared Cauchy denominator rather than an uncancelled second-order one. -/
theorem geometricIntegralTerm_diagonal_eq
    {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    geometricIntegralTerm yoshidaLength
        (clippedOddCorrelation yoshidaHalfLength n n) k =
      2 * oddRate k / (oddRate k ^ 2 + yoshidaKappa n ^ 2) +
        4 * yoshidaKappa n ^ 2 *
            (1 - Real.exp (-oddRate k * yoshidaLength)) /
          (yoshidaLength *
            (oddRate k ^ 2 + yoshidaKappa n ^ 2) ^ 2) := by
  have hκ : yoshidaKappa n ≠ 0 := by
    rw [yoshidaKappa]
    exact div_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
        (Nat.cast_ne_zero.mpr hn))
      yoshidaLength_pos.ne'
  have hden : oddRate k ^ 2 + yoshidaKappa n ^ 2 ≠ 0 := by positivity
  have h := integral_exp_neg_mul_fullDiagonalCorrelation
    yoshidaLength_pos.ne' hκ hden
    (yoshida_sin_endpoint n) (yoshida_cos_endpoint n)
  rw [geometricIntegralTerm]
  simp_rw [clippedOddCorrelation_half_diag hn]
  rw [h]
  ring

/-- The renormalized diagonal geometric summand after subtracting the
unit-correlation harmonic counterterm. -/
theorem renormalizedTerm_diagonal_eq
    {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    renormalizedTerm yoshidaLength 1
        (clippedOddCorrelation yoshidaHalfLength n n) k =
      2 * oddRate k / (oddRate k ^ 2 + yoshidaKappa n ^ 2) +
        4 * yoshidaKappa n ^ 2 *
            (1 - Real.exp (-oddRate k * yoshidaLength)) /
          (yoshidaLength *
            (oddRate k ^ 2 + yoshidaKappa n ^ 2) ^ 2) -
        1 / (k + 1 : ℕ) := by
  rw [renormalizedTerm_eq_geometricIntegralTerm,
    geometricIntegralTerm_diagonal_eq hn]

end

end ArithmeticHodge.Analysis.YoshidaDiagonalMomentSeries
