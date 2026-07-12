import ArithmeticHodge.Analysis.YoshidaMomentIntegrability
import ArithmeticHodge.Analysis.YoshidaOddCorrelationIntegrability

set_option autoImplicit false

open Filter MeasureTheory Real Set Topology
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaMomentSeries

noncomputable section

open YoshidaOddGramPrefix
open YoshidaRenormalizedGeometricKernel
open YoshidaOddCorrelationIntegrability
open YoshidaMomentIntegrability

/-!
# Exact Cauchy-series representations of Yoshida's odd moments

The removable sine moment can be evaluated without numerical quadrature.
Its singular geometric factor is the sum of the odd exponential rates
`2k + 1/2`; dominated convergence is discharged by the generic removable
kernel theorem.  The resulting Laplace integrals have elementary endpoint
values because `yoshidaKappa n * yoshidaLength = 2 * pi * n`.

This module supplies the exact analytic identity.  Rational head-and-tail
enclosures are kept in a separate certificate layer.
-/

/-- The continuous divided-sine factor in
`sin (yoshidaKappa n * u) = u * sineRemovableD n u`. -/
def sineRemovableD (n : ℕ) (u : ℝ) : ℝ :=
  yoshidaKappa n * Real.sinc (yoshidaKappa n * u)

theorem continuous_sineRemovableD (n : ℕ) :
    Continuous (sineRemovableD n) := by
  unfold sineRemovableD
  fun_prop

theorem sine_eq_mul_sineRemovableD (n : ℕ) (u : ℝ) :
    Real.sin (yoshidaKappa n * u) = u * sineRemovableD n u := by
  by_cases hu : u = 0
  · subst u
    simp [sineRemovableD]
  by_cases hk : yoshidaKappa n = 0
  · simp [hk, sineRemovableD]
  rw [sineRemovableD, Real.sinc_of_ne_zero (mul_ne_zero hk hu)]
  field_simp [hu, hk]

theorem sine_pairedIntegralInterchange (n : ℕ) :
    PairedIntegralInterchange yoshidaLength 0
      (fun u : ℝ ↦ Real.sin (yoshidaKappa n * u)) := by
  apply pairedIntegralInterchange_of_removable yoshidaLength_pos
    (by fun_prop)
  · intro u _hu
    simpa only [zero_add] using sine_eq_mul_sineRemovableD n u
  · exact removableMajorantLimit_intervalIntegrable
      (continuous_sineRemovableD n) 0 yoshidaLength

theorem sine_stableGeometricIntegrand_intervalIntegrable (n : ℕ) :
    IntervalIntegrable
      (stableGeometricIntegrand 0
        (fun u : ℝ ↦ Real.sin (yoshidaKappa n * u))) volume
      0 yoshidaLength := by
  exact stableGeometricIntegrand_intervalIntegrable_of_removable
    (continuous_sineRemovableD n) 0 yoshidaLength
    (fun u ↦ by simpa only [zero_add] using sine_eq_mul_sineRemovableD n u)

theorem hasSum_sine_geometricIntegrals (n : ℕ) :
    HasSum
      (renormalizedTerm yoshidaLength 0
        (fun u : ℝ ↦ Real.sin (yoshidaKappa n * u)))
      (∫ u in 0..yoshidaLength,
        oddKernel u * Real.sin (yoshidaKappa n * u)) := by
  have h := renormalizedSeries_hasSum_stable yoshidaLength_pos
    (by fun_prop : Continuous
      (fun u : ℝ ↦ Real.sin (yoshidaKappa n * u)))
    (sine_pairedIntegralInterchange n)
    (sine_stableGeometricIntegrand_intervalIntegrable n)
    (referenceRegularized_intervalIntegrable yoshidaLength)
  simpa [stableGeometricIntegrand] using h

theorem yoshidaKappa_mul_length (n : ℕ) :
    yoshidaKappa n * yoshidaLength = 2 * Real.pi * n := by
  rw [yoshidaKappa]
  field_simp [yoshidaLength_pos.ne']

/-- Elementary finite-interval Laplace transform at a complete sine period. -/
theorem integral_exp_neg_mul_sin
    {b κ L : ℝ} (hden : b ^ 2 + κ ^ 2 ≠ 0)
    (hsin : Real.sin (κ * L) = 0) (hcos : Real.cos (κ * L) = 1) :
    (∫ u in 0..L, Real.exp (-b * u) * Real.sin (κ * u)) =
      κ * (1 - Real.exp (-b * L)) / (b ^ 2 + κ ^ 2) := by
  let F : ℝ → ℝ := fun u ↦
    Real.exp (-b * u) *
      (-b * Real.sin (κ * u) - κ * Real.cos (κ * u)) /
        (b ^ 2 + κ ^ 2)
  have hF : ∀ u : ℝ, HasDerivAt F
      (Real.exp (-b * u) * Real.sin (κ * u)) u := by
    intro u
    have hexp : HasDerivAt (fun x : ℝ ↦ Real.exp (-b * x))
        (-b * Real.exp (-b * u)) u := by
      convert (Real.hasDerivAt_exp (-b * u)).comp u
        ((hasDerivAt_id u).const_mul (-b)) using 1
      all_goals ring_nf
    have hsin' : HasDerivAt (fun x : ℝ ↦ Real.sin (κ * x))
        (κ * Real.cos (κ * u)) u := by
      convert (Real.hasDerivAt_sin (κ * u)).comp u
        ((hasDerivAt_id u).const_mul κ) using 1
      all_goals ring_nf
    have hcos' : HasDerivAt (fun x : ℝ ↦ Real.cos (κ * x))
        (-κ * Real.sin (κ * u)) u := by
      convert (Real.hasDerivAt_cos (κ * u)).comp u
        ((hasDerivAt_id u).const_mul κ) using 1
      all_goals ring_nf
    dsimp only [F]
    convert (hexp.mul
      ((hsin'.const_mul (-b)).sub (hcos'.const_mul κ))).div_const
        (b ^ 2 + κ ^ 2) using 1
    simp only [Pi.sub_apply]
    field_simp [hden]
    ring
  have hint : IntervalIntegrable
      (fun u : ℝ ↦ Real.exp (-b * u) * Real.sin (κ * u)) volume 0 L :=
    Continuous.intervalIntegrable (by fun_prop) 0 L
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _hu ↦ hF u) hint
  rw [hfund]
  dsimp only [F]
  rw [hsin, hcos]
  simp only [mul_zero, Real.exp_zero, Real.sin_zero, Real.cos_zero,
    zero_sub, mul_one]
  field_simp [hden]
  ring

theorem yoshida_sin_endpoint (n : ℕ) :
    Real.sin (yoshidaKappa n * yoshidaLength) = 0 := by
  rw [yoshidaKappa_mul_length]
  rw [show 2 * Real.pi * (n : ℝ) = (2 * n : ℕ) * Real.pi by
    push_cast
    ring]
  exact Real.sin_nat_mul_pi (2 * n)

theorem yoshida_cos_endpoint (n : ℕ) :
    Real.cos (yoshidaKappa n * yoshidaLength) = 1 := by
  rw [yoshidaKappa_mul_length]
  rw [show 2 * Real.pi * (n : ℝ) = (2 * n : ℕ) * Real.pi by
    push_cast
    ring]
  rw [Real.cos_nat_mul_pi, pow_mul]
  norm_num

/-- Closed rational-function value of every odd-rate sine Laplace term. -/
theorem renormalizedTerm_sine_eq
    {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    renormalizedTerm yoshidaLength 0
        (fun u : ℝ ↦ Real.sin (yoshidaKappa n * u)) k =
      2 * yoshidaKappa n *
          (1 - Real.exp (-oddRate k * yoshidaLength)) /
        (oddRate k ^ 2 + yoshidaKappa n ^ 2) := by
  have hkappa : yoshidaKappa n ≠ 0 := by
    rw [yoshidaKappa]
    exact div_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
        (Nat.cast_ne_zero.mpr hn))
      yoshidaLength_pos.ne'
  have hden : oddRate k ^ 2 + yoshidaKappa n ^ 2 ≠ 0 := by
    positivity
  rw [renormalizedTerm]
  norm_num
  have hvalue := integral_exp_neg_mul_sin hden
    (yoshida_sin_endpoint n) (yoshida_cos_endpoint n)
  rw [show (fun u : ℝ ↦ Real.exp (-(oddRate k * u)) *
      Real.sin (yoshidaKappa n * u)) =
      fun u : ℝ ↦ Real.exp (-oddRate k * u) *
        Real.sin (yoshidaKappa n * u) by
    funext u
    congr 2
    ring]
  rw [hvalue]
  ring_nf

/-- Elementary contribution of the two nonsingular exponential weights. -/
def sinePolarValue (n : ℕ) : ℝ :=
  2 * yoshidaKappa n *
    ((1 - Real.sqrt 2) / ((1 / 2 : ℝ) ^ 2 + yoshidaKappa n ^ 2) +
      (1 - (Real.sqrt 2)⁻¹) /
        ((1 / 2 : ℝ) ^ 2 + yoshidaKappa n ^ 2))

/-- Explicit positive Cauchy term after evaluating the dyadic endpoint. -/
def sineCauchyTerm (n k : ℕ) : ℝ :=
  2 * yoshidaKappa n *
      (1 - (Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k) /
    (oddRate k ^ 2 + yoshidaKappa n ^ 2)

theorem exp_yoshidaLength_half :
    Real.exp (yoshidaLength / 2) = Real.sqrt 2 := by
  rw [yoshidaLength, Real.exp_half, Real.exp_log (by norm_num)]

theorem exp_neg_yoshidaLength_half :
    Real.exp (-yoshidaLength / 2) = (Real.sqrt 2)⁻¹ := by
  rw [show -yoshidaLength / 2 = -(yoshidaLength / 2) by ring,
    Real.exp_neg, exp_yoshidaLength_half]

theorem exp_neg_oddRate_mul_length (k : ℕ) :
    Real.exp (-oddRate k * yoshidaLength) =
      (Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k := by
  rw [show -oddRate k * yoshidaLength =
      -yoshidaLength / 2 + (k : ℝ) * (-2 * yoshidaLength) by
    rw [oddRate]
    ring,
    Real.exp_add]
  rw [show Real.exp ((k : ℝ) * (-2 * yoshidaLength)) =
      Real.exp (-2 * yoshidaLength) ^ k by
    simpa only [Nat.cast_ofNat] using Real.exp_nat_mul (-2 * yoshidaLength) k]
  rw [show Real.exp (-2 * yoshidaLength) = (1 / 4 : ℝ) by
    rw [show -2 * yoshidaLength = -(2 * yoshidaLength) by ring,
      Real.exp_neg]
    rw [show Real.exp (2 * yoshidaLength) = (4 : ℝ) by
      rw [show 2 * yoshidaLength = yoshidaLength + yoshidaLength by ring,
        Real.exp_add, yoshidaLength, Real.exp_log (by norm_num)]
      norm_num]
    norm_num,
    exp_neg_yoshidaLength_half]
  rw [one_div, inv_pow]
  ring

theorem integral_yoshida_polar_sine_eq
    {n : ℕ} (hn : n ≠ 0) :
    (∫ u in 0..yoshidaLength,
      2 * (Real.exp (u / 2) + Real.exp (-u / 2)) *
        Real.sin (yoshidaKappa n * u)) = sinePolarValue n := by
  have hk : yoshidaKappa n ≠ 0 := by
    rw [yoshidaKappa]
    exact div_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
        (Nat.cast_ne_zero.mpr hn))
      yoshidaLength_pos.ne'
  have hdenNeg : (-1 / 2 : ℝ) ^ 2 + yoshidaKappa n ^ 2 ≠ 0 := by
    positivity
  have hdenPos : (1 / 2 : ℝ) ^ 2 + yoshidaKappa n ^ 2 ≠ 0 := by
    positivity
  have hneg := integral_exp_neg_mul_sin hdenNeg
    (yoshida_sin_endpoint n) (yoshida_cos_endpoint n)
    (b := (-1 / 2 : ℝ))
  have hpos := integral_exp_neg_mul_sin hdenPos
    (yoshida_sin_endpoint n) (yoshida_cos_endpoint n)
    (b := (1 / 2 : ℝ))
  rw [show (fun u : ℝ ↦
      2 * (Real.exp (u / 2) + Real.exp (-u / 2)) *
        Real.sin (yoshidaKappa n * u)) =
      fun u : ℝ ↦ 2 *
        (Real.exp (-(-1 / 2 : ℝ) * u) *
            Real.sin (yoshidaKappa n * u) +
          Real.exp (-(1 / 2 : ℝ) * u) *
            Real.sin (yoshidaKappa n * u)) by
    funext u
    rw [show -(-1 / 2 : ℝ) * u = u / 2 by ring,
      show -(1 / 2 : ℝ) * u = -u / 2 by ring]
    ring]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) 0 yoshidaLength)
      (Continuous.intervalIntegrable (by fun_prop) 0 yoshidaLength),
    hneg, hpos]
  rw [show -(-1 / 2 : ℝ) * yoshidaLength = yoshidaLength / 2 by ring,
    show -(1 / 2 : ℝ) * yoshidaLength = -yoshidaLength / 2 by ring,
    exp_yoshidaLength_half, exp_neg_yoshidaLength_half]
  rw [sinePolarValue]
  ring

private theorem sine_integrand_eq_stable
    {n : ℕ} (hn : n ≠ 0) {u : ℝ} (hu : u ≠ 0) :
    yoshidaSineMomentIntegrand n u =
      2 * (Real.exp (u / 2) + Real.exp (-u / 2)) *
          Real.sin (yoshidaKappa n * u) -
        oddKernel u * Real.sin (yoshidaKappa n * u) := by
  have hk : yoshidaKappa n ≠ 0 := by
    rw [yoshidaKappa]
    exact div_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
        (Nat.cast_ne_zero.mpr hn))
      yoshidaLength_pos.ne'
  rw [yoshidaSineMomentIntegrand, yoshidaWeightPlus, if_neg hu,
    yoshidaWeight, oddKernel,
    Real.sinc_of_ne_zero (mul_ne_zero hk hu)]
  field_simp [hu, hk]
  ring

/-- Exact infinite Cauchy-series form of the removable sine moment. -/
theorem yoshidaSineMoment_eq_polar_sub_tsum
    {n : ℕ} (hn : n ≠ 0) :
    yoshidaSineMoment n =
      (∫ u in 0..yoshidaLength,
        2 * (Real.exp (u / 2) + Real.exp (-u / 2)) *
          Real.sin (yoshidaKappa n * u)) -
      ∑' k : ℕ,
        2 * yoshidaKappa n *
            (1 - Real.exp (-oddRate k * yoshidaLength)) /
          (oddRate k ^ 2 + yoshidaKappa n ^ 2) := by
  have hpolar : IntervalIntegrable
      (fun u : ℝ ↦ 2 * (Real.exp (u / 2) + Real.exp (-u / 2)) *
        Real.sin (yoshidaKappa n * u)) volume 0 yoshidaLength :=
    Continuous.intervalIntegrable (by fun_prop) 0 yoshidaLength
  have hgeom : IntervalIntegrable
      (fun u : ℝ ↦ oddKernel u * Real.sin (yoshidaKappa n * u))
      volume 0 yoshidaLength := by
    convert sine_stableGeometricIntegrand_intervalIntegrable n using 1
    funext u
    rw [stableGeometricIntegrand]
    ring
  have hintegral :
      (∫ u in 0..yoshidaLength, yoshidaSineMomentIntegrand n u) =
        (∫ u in 0..yoshidaLength,
          2 * (Real.exp (u / 2) + Real.exp (-u / 2)) *
            Real.sin (yoshidaKappa n * u)) -
        ∫ u in 0..yoshidaLength,
          oddKernel u * Real.sin (yoshidaKappa n * u) := by
    rw [← intervalIntegral.integral_sub hpolar hgeom]
    apply intervalIntegral.integral_congr_ae
    have hne : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hne] with u hu _huIoc
    exact sine_integrand_eq_stable hn hu
  rw [yoshidaSineMoment, hintegral]
  rw [← (hasSum_sine_geometricIntegrals n).tsum_eq]
  congr 1
  apply tsum_congr
  intro k
  exact renormalizedTerm_sine_eq hn k

/-- Fully elementary head plus positive Cauchy series representation. -/
theorem yoshidaSineMoment_eq_sinePolarValue_sub_tsum
    {n : ℕ} (hn : n ≠ 0) :
    yoshidaSineMoment n = sinePolarValue n -
      ∑' k : ℕ,
        2 * yoshidaKappa n *
            (1 - Real.exp (-oddRate k * yoshidaLength)) /
          (oddRate k ^ 2 + yoshidaKappa n ^ 2) := by
  rw [yoshidaSineMoment_eq_polar_sub_tsum hn,
    integral_yoshida_polar_sine_eq hn]

/-- Dyadic endpoint form used by the rational enclosure layer. -/
theorem yoshidaSineMoment_eq_explicitCauchySeries
    {n : ℕ} (hn : n ≠ 0) :
    yoshidaSineMoment n = sinePolarValue n -
      ∑' k : ℕ, sineCauchyTerm n k := by
  rw [yoshidaSineMoment_eq_sinePolarValue_sub_tsum hn]
  congr 1
  apply tsum_congr
  intro k
  rw [sineCauchyTerm, exp_neg_oddRate_mul_length]

end

end ArithmeticHodge.Analysis.YoshidaMomentSeries
