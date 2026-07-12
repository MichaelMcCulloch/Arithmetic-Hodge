import ArithmeticHodge.Analysis.YoshidaStructuralKernelIntegrability

set_option autoImplicit false

open Filter MeasureTheory Real Set Topology
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaZeroModeStructuralCore

noncomputable section

open YoshidaRenormalizedGeometricKernel
open YoshidaStructuralKernelIntegrability

/-!
# Clean structural zero-mode core

This module restates the Yoshida moment and Stieltjes data behind the zero
mode without importing the legacy finite-mode enclosure graph.  The moment is
defined by the original interval integral; its raw-series expansion follows
from removable-kernel summation and exact antiderivatives.
-/

/-- The full clipped interval length, isolated from the certificate layer. -/
def structuralYoshidaLength : ℝ := Real.log 2

/-- The angular frequency `2πn / log 2`. -/
def structuralYoshidaKappa (n : ℕ) : ℝ :=
  2 * Real.pi * n / structuralYoshidaLength

/-- Yoshida's singular real-space weight. -/
def structuralYoshidaWeight (u : ℝ) : ℝ :=
  2 * (Real.exp (u / 2) + Real.exp (-u / 2) -
    Real.exp (u / 2) / (Real.exp u - Real.exp (-u)))

/-- The removable extension of `structuralYoshidaWeight u + 1/u`. -/
def structuralYoshidaWeightPlus (u : ℝ) : ℝ :=
  if u = 0 then 7 / 2 else structuralYoshidaWeight u + 1 / u

/-- The exact structural diagonal-moment integrand. -/
def structuralYoshidaDiagonalMomentIntegrand (n : ℕ) (u : ℝ) : ℝ :=
  structuralYoshidaWeightPlus u *
      ((structuralYoshidaLength - u) / structuralYoshidaLength) *
      Real.cos (structuralYoshidaKappa n * u) +
    2 * Real.sin (structuralYoshidaKappa n * u / 2) ^ 2 / u +
    Real.cos (structuralYoshidaKappa n * u) / structuralYoshidaLength

/-- Yoshida's desingularized diagonal moment, with no enclosure imports. -/
def structuralYoshidaDiagonalMoment (n : ℕ) : ℝ :=
  (∫ u in 0..structuralYoshidaLength,
      structuralYoshidaDiagonalMomentIntegrand n u) -
    (Real.log structuralYoshidaLength + Real.eulerMascheroniConstant +
      Real.log 2 + Real.log Real.pi)

/-- Closed ramp integral used only as an exact rational function. -/
def structuralDiagonalRampClosed (L p a q : ℝ) : ℝ :=
  ((q - 1 + a * L) * (a ^ 2 - p) + 2 * a * p * L) /
    (L * (a ^ 2 + p) ^ 2)

/-- The positive Stieltjes profile at squared frequency. -/
def structuralYoshidaStieltjesProfile (t : ℝ) : ℝ :=
  2 * (Real.sqrt 2 + (Real.sqrt 2)⁻¹ - 2) /
      ((1 / 2 : ℝ) ^ 2 + t) +
    ∑' k : ℕ,
      2 * (1 - (Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k) /
        (oddRate k ^ 2 + t)

theorem structuralYoshidaLength_pos : 0 < structuralYoshidaLength := by
  exact Real.log_pos (by norm_num)

private theorem exp_structuralYoshidaLength_half :
    Real.exp (structuralYoshidaLength / 2) = Real.sqrt 2 := by
  rw [structuralYoshidaLength, Real.exp_half, Real.exp_log (by norm_num)]

private theorem exp_neg_structuralYoshidaLength_half :
    Real.exp (-structuralYoshidaLength / 2) = (Real.sqrt 2)⁻¹ := by
  rw [show -structuralYoshidaLength / 2 =
      -(structuralYoshidaLength / 2) by ring,
    Real.exp_neg, exp_structuralYoshidaLength_half]

private theorem exp_neg_oddRate_mul_structuralLength (k : ℕ) :
    Real.exp (-oddRate k * structuralYoshidaLength) =
      (Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k := by
  rw [show -oddRate k * structuralYoshidaLength =
      -structuralYoshidaLength / 2 +
        (k : ℝ) * (-2 * structuralYoshidaLength) by
    rw [oddRate]
    ring,
    Real.exp_add]
  rw [show Real.exp ((k : ℝ) * (-2 * structuralYoshidaLength)) =
      Real.exp (-2 * structuralYoshidaLength) ^ k by
    simpa only [Nat.cast_ofNat] using
      Real.exp_nat_mul (-2 * structuralYoshidaLength) k]
  rw [show Real.exp (-2 * structuralYoshidaLength) = (1 / 4 : ℝ) by
    rw [show -2 * structuralYoshidaLength =
        -(2 * structuralYoshidaLength) by ring,
      Real.exp_neg]
    rw [show Real.exp (2 * structuralYoshidaLength) = (4 : ℝ) by
      rw [show 2 * structuralYoshidaLength =
          structuralYoshidaLength + structuralYoshidaLength by ring,
        Real.exp_add, structuralYoshidaLength,
        Real.exp_log (by norm_num)]
      norm_num]
    norm_num,
    exp_neg_structuralYoshidaLength_half]
  rw [one_div, inv_pow]
  ring

private def zeroCorrelation (u : ℝ) : ℝ :=
  1 - u / structuralYoshidaLength

private def zeroRemovableD (_u : ℝ) : ℝ :=
  -1 / structuralYoshidaLength

private theorem continuous_zeroCorrelation : Continuous zeroCorrelation := by
  unfold zeroCorrelation
  fun_prop

private theorem continuous_zeroRemovableD : Continuous zeroRemovableD := by
  unfold zeroRemovableD
  fun_prop

private theorem zeroCorrelation_removable (u : ℝ) :
    zeroCorrelation u = 1 + u * zeroRemovableD u := by
  unfold zeroCorrelation zeroRemovableD
  ring

private theorem zero_pairedIntegralInterchange :
    PairedIntegralInterchange structuralYoshidaLength 1 zeroCorrelation := by
  apply pairedIntegralInterchange_of_removable structuralYoshidaLength_pos
    continuous_zeroCorrelation
  · intro u _hu
    exact zeroCorrelation_removable u
  · exact removableMajorantLimit_intervalIntegrable
      continuous_zeroRemovableD 1 structuralYoshidaLength

private theorem zero_stableGeometricIntegrand_intervalIntegrable :
    IntervalIntegrable (stableGeometricIntegrand 1 zeroCorrelation)
      volume 0 structuralYoshidaLength := by
  exact stableGeometricIntegrand_intervalIntegrable_of_removable
    continuous_zeroRemovableD 1 structuralYoshidaLength
    zeroCorrelation_removable

private theorem zero_negated_geometric_identity :
    -Real.eulerMascheroniConstant -
        ∑' k : ℕ, renormalizedTerm structuralYoshidaLength 1 zeroCorrelation k =
      (∫ u in 0..structuralYoshidaLength,
        -oddKernel u * zeroCorrelation u + 1 / u) -
        (Real.log structuralYoshidaLength +
          Real.eulerMascheroniConstant + Real.log 2) := by
  simpa only [mul_one] using
    negated_geometric_identity structuralYoshidaLength_pos
      continuous_zeroCorrelation zero_pairedIntegralInterchange
      zero_stableGeometricIntegrand_intervalIntegrable
      (referenceRegularized_intervalIntegrable structuralYoshidaLength)

private theorem zero_renormalized_hasSum :
    HasSum (renormalizedTerm structuralYoshidaLength 1 zeroCorrelation)
      ((∫ u in 0..structuralYoshidaLength,
          stableGeometricIntegrand 1 zeroCorrelation u) +
        (Real.log structuralYoshidaLength + Real.log 2)) := by
  simpa only [mul_one] using
    renormalizedSeries_hasSum_stable structuralYoshidaLength_pos
      continuous_zeroCorrelation zero_pairedIntegralInterchange
      zero_stableGeometricIntegrand_intervalIntegrable
      (referenceRegularized_intervalIntegrable structuralYoshidaLength)

private def zeroRampPrimitive (a u : ℝ) : ℝ :=
  Real.exp (-a * u) *
    (-1 / a + u / (structuralYoshidaLength * a) +
      1 / (structuralYoshidaLength * a ^ 2))

private theorem zeroRampPrimitive_hasDerivAt
    {a u : ℝ} (ha : a ≠ 0) :
    HasDerivAt (zeroRampPrimitive a)
      (Real.exp (-a * u) * (1 - u / structuralYoshidaLength)) u := by
  have hexp : HasDerivAt (fun x : ℝ ↦ Real.exp (-a * x))
      (-a * Real.exp (-a * u)) u := by
    convert (Real.hasDerivAt_exp (-a * u)).comp u
      ((hasDerivAt_id u).const_mul (-a)) using 1
    ring
  have hlinear : HasDerivAt
      (fun x : ℝ ↦
        -1 / a + x / (structuralYoshidaLength * a) +
          1 / (structuralYoshidaLength * a ^ 2))
      (1 / (structuralYoshidaLength * a)) u := by
    convert ((hasDerivAt_const u (-1 / a)).add
      ((hasDerivAt_id u).div_const
        (structuralYoshidaLength * a))).add_const
        (1 / (structuralYoshidaLength * a ^ 2)) using 1
    all_goals ring
  unfold zeroRampPrimitive
  convert hexp.mul hlinear using 1
  field_simp [ha, structuralYoshidaLength_pos.ne']
  ring

private theorem integral_exp_neg_mul_zeroCorrelation_eq_ramp
    {a : ℝ} (ha : a ≠ 0) :
    (∫ u in 0..structuralYoshidaLength,
        Real.exp (-a * u) * zeroCorrelation u) =
      structuralDiagonalRampClosed structuralYoshidaLength 0 a
        (Real.exp (-a * structuralYoshidaLength)) := by
  have hint : IntervalIntegrable
      (fun u : ℝ ↦ Real.exp (-a * u) * zeroCorrelation u)
      volume 0 structuralYoshidaLength :=
    Continuous.intervalIntegrable (by
      unfold zeroCorrelation
      fun_prop) 0 structuralYoshidaLength
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _hu ↦ zeroRampPrimitive_hasDerivAt ha) hint
  change (∫ u in 0..structuralYoshidaLength,
    Real.exp (-a * u) * (1 - u / structuralYoshidaLength)) = _
  rw [hfund]
  unfold zeroRampPrimitive structuralDiagonalRampClosed
  simp only [mul_zero, Real.exp_zero, zero_div, sub_zero]
  field_simp [ha, structuralYoshidaLength_pos.ne']
  ring

private theorem zero_polar_integral_eq_ramps :
    (∫ u in 0..structuralYoshidaLength,
      2 * (Real.exp (u / 2) + Real.exp (-u / 2)) * zeroCorrelation u) =
      2 * structuralDiagonalRampClosed structuralYoshidaLength 0
          (-1 / 2) (Real.sqrt 2) +
        2 * structuralDiagonalRampClosed structuralYoshidaLength 0
          (1 / 2) (Real.sqrt 2)⁻¹ := by
  have hplus : IntervalIntegrable
      (fun u : ℝ ↦ Real.exp (u / 2) * zeroCorrelation u)
      volume 0 structuralYoshidaLength :=
    Continuous.intervalIntegrable (by
      unfold zeroCorrelation
      fun_prop) 0 structuralYoshidaLength
  have hminus : IntervalIntegrable
      (fun u : ℝ ↦ Real.exp (-u / 2) * zeroCorrelation u)
      volume 0 structuralYoshidaLength :=
    Continuous.intervalIntegrable (by
      unfold zeroCorrelation
      fun_prop) 0 structuralYoshidaLength
  rw [show (fun u : ℝ ↦
      2 * (Real.exp (u / 2) + Real.exp (-u / 2)) * zeroCorrelation u) =
      fun u : ℝ ↦ 2 *
        (Real.exp (u / 2) * zeroCorrelation u +
          Real.exp (-u / 2) * zeroCorrelation u) by
    funext u
    ring]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hplus hminus]
  rw [show (fun u : ℝ ↦ Real.exp (u / 2) * zeroCorrelation u) =
      fun u : ℝ ↦
        Real.exp (-(-1 / 2 : ℝ) * u) * zeroCorrelation u by
    funext u
    congr 2
    ring]
  rw [show (fun u : ℝ ↦ Real.exp (-u / 2) * zeroCorrelation u) =
      fun u : ℝ ↦
        Real.exp (-(1 / 2 : ℝ) * u) * zeroCorrelation u by
    funext u
    congr 2
    ring]
  rw [integral_exp_neg_mul_zeroCorrelation_eq_ramp
      (by norm_num : (-1 / 2 : ℝ) ≠ 0),
    integral_exp_neg_mul_zeroCorrelation_eq_ramp
      (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  rw [show -(-1 / 2 : ℝ) * structuralYoshidaLength =
      structuralYoshidaLength / 2 by ring,
    show -(1 / 2 : ℝ) * structuralYoshidaLength =
      -structuralYoshidaLength / 2 by ring,
    exp_structuralYoshidaLength_half,
    exp_neg_structuralYoshidaLength_half]
  ring

private theorem zero_moment_integrand_ae_identity :
    ∀ᵐ u : ℝ ∂volume,
      structuralYoshidaDiagonalMomentIntegrand 0 u =
        2 * (Real.exp (u / 2) + Real.exp (-u / 2)) * zeroCorrelation u +
          (-oddKernel u * zeroCorrelation u + 1 / u) := by
  filter_upwards [show ∀ᵐ u : ℝ ∂volume, u ≠ 0 by
    simp [ae_iff, measure_singleton]] with u hu
  rw [structuralYoshidaDiagonalMomentIntegrand,
    structuralYoshidaWeightPlus, if_neg hu]
  simp only [structuralYoshidaKappa, Nat.cast_zero, mul_zero, zero_div,
    Real.cos_zero, Real.sin_zero, zero_mul]
  unfold structuralYoshidaWeight zeroCorrelation oddKernel
  have hden : Real.exp u - Real.exp (-u) ≠ 0 := by
    intro h
    have heq : Real.exp u = Real.exp (-u) := sub_eq_zero.mp h
    exact hu (by linarith [Real.exp_injective heq])
  field_simp [hu, structuralYoshidaLength_pos.ne', hden]
  norm_num
  ring

/-- The exact raw zero-mode series term. -/
def structuralZeroRawTerm (k : ℕ) : ℝ :=
  2 * structuralDiagonalRampClosed structuralYoshidaLength 0 (oddRate k)
      ((Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k) -
    1 / (k + 1 : ℕ)

private theorem renormalizedTerm_zeroCorrelation_eq_raw (k : ℕ) :
    renormalizedTerm structuralYoshidaLength 1 zeroCorrelation k =
      structuralZeroRawTerm k := by
  rw [renormalizedTerm]
  rw [integral_exp_neg_mul_zeroCorrelation_eq_ramp (oddRate_pos k).ne']
  rw [exp_neg_oddRate_mul_structuralLength]
  unfold structuralZeroRawTerm
  push_cast
  ring

theorem summable_structuralZeroRawTerm : Summable structuralZeroRawTerm := by
  exact zero_renormalized_hasSum.summable.congr
    (fun k ↦ renormalizedTerm_zeroCorrelation_eq_raw k)

private theorem structuralYoshidaDiagonalMoment_zero_eq_rawSeries :
    structuralYoshidaDiagonalMoment 0 =
      2 * structuralDiagonalRampClosed structuralYoshidaLength 0
          (-1 / 2) (Real.sqrt 2) +
        2 * structuralDiagonalRampClosed structuralYoshidaLength 0
          (1 / 2) (Real.sqrt 2)⁻¹ -
        Real.eulerMascheroniConstant - Real.log Real.pi -
        ∑' k : ℕ, structuralZeroRawTerm k := by
  let P : ℝ → ℝ := fun u ↦
    2 * (Real.exp (u / 2) + Real.exp (-u / 2)) * zeroCorrelation u
  let N : ℝ → ℝ := fun u ↦
    -oddKernel u * zeroCorrelation u + 1 / u
  have hP : IntervalIntegrable P volume 0 structuralYoshidaLength := by
    exact Continuous.intervalIntegrable (by
      dsimp only [P]
      unfold zeroCorrelation
      fun_prop) 0 structuralYoshidaLength
  have hN : IntervalIntegrable N volume 0 structuralYoshidaLength := by
    have h := zero_stableGeometricIntegrand_intervalIntegrable.neg
    apply h.congr
    intro u _hu
    dsimp only [N]
    simp only [Pi.neg_apply]
    unfold stableGeometricIntegrand
    ring
  have hintegral :
      (∫ u in 0..structuralYoshidaLength,
          structuralYoshidaDiagonalMomentIntegrand 0 u) =
        (∫ u in 0..structuralYoshidaLength, P u) +
          ∫ u in 0..structuralYoshidaLength, N u := by
    calc
      (∫ u in 0..structuralYoshidaLength,
          structuralYoshidaDiagonalMomentIntegrand 0 u) =
          ∫ u in 0..structuralYoshidaLength, P u + N u := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [zero_moment_integrand_ae_identity] with u hu
        intro _hu
        simpa only [P, N] using hu
      _ = (∫ u in 0..structuralYoshidaLength, P u) +
          ∫ u in 0..structuralYoshidaLength, N u :=
        intervalIntegral.integral_add hP hN
  have hPvalue :
      (∫ u in 0..structuralYoshidaLength, P u) =
        2 * structuralDiagonalRampClosed structuralYoshidaLength 0
            (-1 / 2) (Real.sqrt 2) +
          2 * structuralDiagonalRampClosed structuralYoshidaLength 0
            (1 / 2) (Real.sqrt 2)⁻¹ := by
    simpa only [P] using zero_polar_integral_eq_ramps
  have hNvalue := zero_negated_geometric_identity
  have htsum :
      (∑' k : ℕ, renormalizedTerm structuralYoshidaLength 1 zeroCorrelation k) =
        ∑' k : ℕ, structuralZeroRawTerm k := by
    apply tsum_congr
    exact renormalizedTerm_zeroCorrelation_eq_raw
  rw [htsum] at hNvalue
  rw [structuralYoshidaDiagonalMoment, hintegral, hPvalue]
  linarith

private theorem structuralZeroRawTerm_zero :
    structuralZeroRawTerm 0 =
      2 * structuralDiagonalRampClosed structuralYoshidaLength 0
          (1 / 2) (Real.sqrt 2)⁻¹ - 1 := by
  unfold structuralZeroRawTerm oddRate
  norm_num

/-- The zero moment is a polar ramp minus the exact raw structural tail. -/
theorem structuralYoshidaDiagonalMoment_zero_eq_positiveRamp_sub_rawTail :
    structuralYoshidaDiagonalMoment 0 =
      2 * structuralDiagonalRampClosed structuralYoshidaLength 0
          (-1 / 2) (Real.sqrt 2) + 1 -
        Real.eulerMascheroniConstant - Real.log Real.pi -
        ∑' j : ℕ, structuralZeroRawTerm (j + 1) := by
  have hmain := structuralYoshidaDiagonalMoment_zero_eq_rawSeries
  have hsplit := summable_structuralZeroRawTerm.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at hsplit
  rw [structuralZeroRawTerm_zero] at hsplit
  linarith

end

end ArithmeticHodge.Analysis.YoshidaZeroModeStructuralCore
