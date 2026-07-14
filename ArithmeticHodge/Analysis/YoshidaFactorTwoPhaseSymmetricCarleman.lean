import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSymmetricCoercivity
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseAlternatingCoercivity

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSymmetricCarleman

noncomputable section

open CenteredEndpointCorrelation
open EndpointParityCarleman
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseAlternatingCoercivity
open YoshidaFactorTwoPhaseSymmetricCoercivity
open YoshidaEndpointSingularCorrelation

/-- Every overlap autocorrelation is bounded by the full centered energy.
This is the elementary two-square estimate, with both overlap copies kept on
their actual subintervals. -/
theorem abs_centeredEndpointCorrelation_le_energy
    (w : ℝ → ℝ) (hw : Continuous w) {t : ℝ}
    (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    |centeredEndpointCorrelation w t| ≤
      ∫ x : ℝ in -1..1, w x ^ 2 := by
  let E : ℝ := ∫ x : ℝ in -1..1, w x ^ 2
  let q : ℝ → ℝ := fun x ↦ w x ^ 2
  have hq : Continuous q := by
    dsimp only [q]
    fun_prop
  have hleft :
      (∫ x : ℝ in t - 1..1, q x) ≤ E := by
    dsimp only [E]
    apply intervalIntegral.integral_mono_interval
      (c := (-1 : ℝ)) (d := 1) (by linarith) (by linarith) le_rfl
    · filter_upwards with x
      exact sq_nonneg (w x)
    · exact hq.intervalIntegrable _ _
  have hright :
      (∫ x : ℝ in -1..1 - t, q x) ≤ E := by
    dsimp only [E]
    apply intervalIntegral.integral_mono_interval
      (c := (-1 : ℝ)) (d := 1) le_rfl (by linarith) (by linarith)
    · filter_upwards with x
      exact sq_nonneg (w x)
    · exact hq.intervalIntegrable _ _
  have hcorr :=
    two_mul_abs_centeredEndpointCorrelation_two_sub_le_boundaryTail
      w hw (t := 2 - t) (by linarith)
  rw [show 2 - (2 - t) = t by ring] at hcorr
  unfold centeredEndpointBoundaryTail at hcorr
  have hcorr' : 2 * |centeredEndpointCorrelation w t| ≤
      (∫ x : ℝ in t - 1..1, q x) +
        ∫ x : ℝ in -1..1 - t, q x := by
    simpa only [q, show 1 - (2 - t) = t - 1 by ring,
      show -1 + (2 - t) = 1 - t by ring] using hcorr
  nlinarith

/-- The positive-distance absolute autocorrelation costs at most twice the
centered energy.  This deliberately cheap bound is sufficient once the odd
regular scalar is centered around its exact zero correlation mean. -/
theorem integral_abs_centeredEndpointCorrelation_le_two_mul_energy
    (w : ℝ → ℝ) (hw : Continuous w) :
    (∫ t : ℝ in 0..2, |centeredEndpointCorrelation w t|) ≤
      2 * (∫ x : ℝ in -1..1, w x ^ 2) := by
  let E : ℝ := ∫ x : ℝ in -1..1, w x ^ 2
  have hC : Continuous (fun t : ℝ ↦
      |centeredEndpointCorrelation w t|) :=
    (continuous_centeredEndpointCorrelation_of_continuous w hw).abs
  calc
    (∫ t : ℝ in 0..2, |centeredEndpointCorrelation w t|) ≤
        ∫ _t : ℝ in 0..2, E := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (hC.intervalIntegrable _ _) (continuous_const.intervalIntegrable 0 2)
      intro t ht
      exact abs_centeredEndpointCorrelation_le_energy w hw ht.1 ht.2
    _ = 2 * (∫ x : ℝ in -1..1, w x ^ 2) := by
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      dsimp only [E]
      ring

/-- Odd reflection forces the unweighted positive-distance autocorrelation
to have zero mean.  This is the zero-hyperbolic-rank specialization of the
exact correlation-square identity. -/
theorem integral_centeredEndpointCorrelation_eq_zero_of_odd
    (w : ℝ → ℝ) (hw : Continuous w) (hodd : Function.Odd w) :
    (∫ t : ℝ in 0..2, centeredEndpointCorrelation w t) = 0 := by
  have h := two_mul_integral_cosh_mul_centeredCorrelation_of_odd
    w hw hodd 0
  simpa [centeredSinhMoment] using h

/-!
# The self-correlation endpoint pole on an odd profile

Taking absolute values turns an odd profile into an even one.  The existing
even--odd parity fold can therefore be applied to the pair `(|w|, w)`.  Its
positive folded density is exactly the absolute autocorrelation majorant of
`w`, so the sharp centered cost of the half-pole is `pi / 4`.
-/

/-- The half endpoint pole of a continuous odd profile has sharp Carleman
cost `pi / 4` of its centered energy. -/
theorem abs_half_centeredCorrelation_pole_le_pi_quarter_energy_of_odd
    (w : ℝ → ℝ) (hw : Continuous w) (hodd : Function.Odd w) :
    |(1 / 2 : ℝ) *
        (∫ t : ℝ in 0..2,
          centeredEndpointCorrelation w t / (2 - t))| ≤
      (Real.pi / 4) * (∫ x : ℝ in -1..1, w x ^ 2) := by
  let e : ℝ → ℝ := fun x ↦ |w x|
  let C : ℝ → ℝ := factorTwoCenteredCrossCorrelation w w
  let Ca : ℝ → ℝ := factorTwoCenteredCrossCorrelation e e
  let E : ℝ := ∫ x : ℝ in -1..1, w x ^ 2
  have hec : Continuous e := hw.abs
  have heven : Function.Even e := by
    intro x
    dsimp only [e]
    rw [hodd x, abs_neg]
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg (w x))
  have hCint :=
    intervalIntegrable_factorTwoCenteredCrossCorrelation_div_two_sub
      w w hw hw
  have hCaint :=
    intervalIntegrable_factorTwoCenteredCrossCorrelation_div_two_sub
      e e hec hec
  have habsEq :
      (∫ t : ℝ in 0..2, |C t / (2 - t)|) =
        ∫ t : ℝ in 0..2, |C t| / (2 - t) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ne volume (2 : ℝ)] with t ht2
    intro htmem
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at htmem
    have hden : 0 ≤ 2 - t := sub_nonneg.mpr htmem.2
    rw [abs_div, abs_of_nonneg hden]
  have hmono :
      (∫ t : ℝ in 0..2, |C t| / (2 - t)) ≤
        ∫ t : ℝ in 0..2, Ca t / (2 - t) := by
    rw [← habsEq]
    apply intervalIntegral.integral_mono_on_of_le_Ioo
      (by norm_num : (0 : ℝ) ≤ 2) hCint.abs hCaint
    intro t ht
    have hden : 0 < 2 - t := by linarith [ht.2]
    have htriangle : |C t| ≤ Ca t := by
      dsimp only [C, Ca, e]
      unfold factorTwoCenteredCrossCorrelation
      have habsIntegral := intervalIntegral.abs_integral_le_integral_abs
        (μ := volume)
        (show (-1 : ℝ) ≤ 1 - t by linarith [ht.2])
        (f := fun x : ℝ ↦ w (t + x) * w x)
      simpa only [abs_mul] using habsIntegral
    rw [abs_div, abs_of_pos hden]
    exact div_le_div_of_nonneg_right htriangle hden.le
  let f : ℝ → ℝ := fun p ↦ e (1 - p)
  let g : ℝ → ℝ := fun q ↦ w (1 - q)
  have hfc : Continuous f := by
    dsimp only [f]
    fun_prop
  have hgc : Continuous g := by
    dsimp only [g]
    fun_prop
  have hfold :=
    integral_abs_cross_div_two_sub_eq_parityFoldedTriangleDensity
      e w hec hw heven hodd
  have hcarleman :=
    integral_parityFoldedTriangleAbsBilinearDensity_le_pi_mul_sqrt_energy
      f g hfc hgc
  have hhalfE := endpoint_half_energy_of_even_or_odd
    e hec (Or.inl heven)
  have hhalfW := endpoint_half_energy_of_even_or_odd
    w hw (Or.inr hodd)
  have heEnergy :
      (∫ x : ℝ in -1..1, e x ^ 2) = E := by
    dsimp only [e, E]
    apply intervalIntegral.integral_congr
    intro x _hx
    exact sq_abs (w x)
  have hnormalize :
      Real.pi * Real.sqrt
          ((∫ p : ℝ in 0..1, f p ^ 2) *
            (∫ q : ℝ in 0..1, g q ^ 2)) =
        (Real.pi / 2) * E := by
    dsimp only [f, g]
    rw [hhalfE, hhalfW, heEnergy]
    rw [show ((1 / 2 : ℝ) * E) * ((1 / 2 : ℝ) * E) =
        (1 / 4 : ℝ) * (E * E) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1 / 4)]
    norm_num
    rw [show E * E = E ^ 2 by ring, Real.sqrt_sq_eq_abs,
      abs_of_nonneg hE]
    ring
  have hCaFold :
      (∫ t : ℝ in 0..2, Ca t / (2 - t)) =
        ∫ z : ℝ × ℝ,
          parityFoldedTriangleAbsBilinearDensity f g z
            ∂((volume.restrict (Ioc 0 1)).prod
              (volume.restrict (Ioc 0 1))) := by
    simpa only [Ca, e, f, g, abs_abs] using hfold
  have hpole :
      |(∫ t : ℝ in 0..2, C t / (2 - t))| ≤
        (Real.pi / 2) * E := by
    calc
      |(∫ t : ℝ in 0..2, C t / (2 - t))| ≤
          ∫ t : ℝ in 0..2, |C t / (2 - t)| :=
        intervalIntegral.abs_integral_le_integral_abs
          (by norm_num : (0 : ℝ) ≤ 2)
      _ = ∫ t : ℝ in 0..2, |C t| / (2 - t) := habsEq
      _ ≤ ∫ t : ℝ in 0..2, Ca t / (2 - t) := hmono
      _ = ∫ z : ℝ × ℝ,
          parityFoldedTriangleAbsBilinearDensity f g z
            ∂((volume.restrict (Ioc 0 1)).prod
              (volume.restrict (Ioc 0 1))) := hCaFold
      _ ≤ Real.pi * Real.sqrt
          ((∫ p : ℝ in 0..1, f p ^ 2) *
            (∫ q : ℝ in 0..1, g q ^ 2)) := hcarleman
      _ = (Real.pi / 2) * E := hnormalize
  change |(1 / 2 : ℝ) *
      (∫ t : ℝ in 0..2, C t / (2 - t))| ≤
    (Real.pi / 4) * E
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSymmetricCarleman
