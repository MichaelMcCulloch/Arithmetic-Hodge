import ArithmeticHodge.Analysis.YoshidaFactorTwoSelfCorrelationSupport

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoDiagonalGeometric

noncomputable section

open MultiplicativeWeil
open YoshidaBombieriCrossDistribution
open YoshidaCriticalLogCorrelation
open YoshidaFactorTwoCrossDistribution
open YoshidaFactorTwoSelfCorrelationSupport
open YoshidaRenormalizedGeometricKernel
open YoshidaShiftedGeometricSeries
open YoshidaStructuralKernelIntegrability
open YoshidaZeroCorrelationGeometricSeries

/-!
# Structural resummation of the factor-two diagonal Cauchy series

The self-correlation is folded onto `[0, log 2]`, where each Cauchy value is
the corresponding real Laplace moment.  The full harmonic-subtracted series
is then summed through the removable-numerator dominated-convergence theorem.
-/

def factorTwoSelfCorrelationRe (g : BombieriTest) (s : ℝ) : ℝ :=
  (factorTwoSelfCorrelation g s).re

def factorTwoDiagonalStableIntegrand (g : BombieriTest) (s : ℝ) : ℝ :=
  -oddKernel s * factorTwoSelfCorrelationRe g s +
    factorTwoSelfCorrelationRe g 0 / s

theorem bombieriCauchySelfValue_eq_factorTwo_interval
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) (k : ℕ) :
    bombieriCauchyCrossValue g g k =
      ∫ s : ℝ in -factorTwoLogLength..factorTwoLogLength,
        ((Real.exp (-oddRate k * |s|) : ℝ) : ℂ) *
          factorTwoSelfCorrelation g s := by
  rw [bombieriCauchyCrossValue,
    intervalIntegral.integral_of_le (by
      linarith [factorTwoLogLength_pos] :
        -factorTwoLogLength ≤ factorTwoLogLength),
    ← integral_Icc_eq_integral_Ioc]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun s hs ↦ by
    change ((Real.exp (-oddRate k * |s|) : ℝ) : ℂ) *
      factorTwoSelfCorrelation g s = 0
    rw [factorTwoSelfCorrelation_eq_zero_outside
      g ha hab hsupport hratio hs, mul_zero])).symm

theorem bombieriCauchySelfValue_re_eq_geometricIntegralTerm
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) (k : ℕ) :
    (bombieriCauchyCrossValue g g k).re =
      geometricIntegralTerm factorTwoLogLength
        (factorTwoSelfCorrelationRe g) k := by
  let J : ℝ → ℂ := fun s ↦
    ((Real.exp (-oddRate k * |s|) : ℝ) : ℂ) *
      factorTwoSelfCorrelation g s
  let R : ℝ → ℝ := fun s ↦
    Real.exp (-oddRate k * |s|) * factorTwoSelfCorrelationRe g s
  have hJ : IntervalIntegrable J volume
      (-factorTwoLogLength) factorTwoLogLength := by
    apply Continuous.intervalIntegrable
    exact (by fun_prop : Continuous (fun s : ℝ ↦
      ((Real.exp (-oddRate k * |s|) : ℝ) : ℂ))).mul
        (factorTwoSelfCorrelation_contDiff g 0).continuous
  have hR : IntervalIntegrable R volume
      (-factorTwoLogLength) factorTwoLogLength := by
    apply Continuous.intervalIntegrable
    unfold R factorTwoSelfCorrelationRe
    exact (by fun_prop : Continuous (fun s : ℝ ↦
      Real.exp (-oddRate k * |s|))).mul
        (Complex.continuous_re.comp
          (factorTwoSelfCorrelation_contDiff g 0).continuous)
  have hL : 0 ≤ factorTwoLogLength := factorTwoLogLength_pos.le
  have hneg : IntervalIntegrable R volume (-factorTwoLogLength) 0 := by
    apply hR.mono_set
    intro s hs
    rw [uIcc_of_le (by linarith : -factorTwoLogLength ≤ 0)] at hs
    rw [uIcc_of_le (by linarith : -factorTwoLogLength ≤ factorTwoLogLength)]
    exact ⟨hs.1, hs.2.trans hL⟩
  have hpos : IntervalIntegrable R volume 0 factorTwoLogLength := by
    apply hR.mono_set
    intro s hs
    rw [uIcc_of_le hL] at hs
    rw [uIcc_of_le (by linarith : -factorTwoLogLength ≤ factorTwoLogLength)]
    exact ⟨(neg_nonpos.mpr hL).trans hs.1, hs.2⟩
  have hreflect : IntervalIntegrable (fun s : ℝ ↦ R (-s)) volume
      0 factorTwoLogLength := by
    have h := (hneg.comp_mul_left (c := (-1 : ℝ))).symm
    convert h using 1 <;> norm_num
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hneg hpos
  have hreflectIntegral := intervalIntegral.integral_comp_neg
    (f := R) (a := 0) (b := factorTwoLogLength)
  rw [bombieriCauchySelfValue_eq_factorTwo_interval
    g ha hab hsupport hratio k]
  change (∫ s : ℝ in -factorTwoLogLength..factorTwoLogLength, J s).re = _
  calc
    (∫ s : ℝ in -factorTwoLogLength..factorTwoLogLength, J s).re =
        ∫ s : ℝ in -factorTwoLogLength..factorTwoLogLength,
          (J s).re := by
      simpa only [Complex.reCLM_apply] using
        (Complex.reCLM.intervalIntegral_comp_comm hJ).symm
    _ = ∫ s : ℝ in -factorTwoLogLength..factorTwoLogLength, R s := by
      apply intervalIntegral.integral_congr
      intro s _hs
      simp only [J, R, factorTwoSelfCorrelationRe, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    _ = (∫ s : ℝ in -factorTwoLogLength..0, R s) +
        ∫ s : ℝ in 0..factorTwoLogLength, R s := hsplit.symm
    _ = (∫ s : ℝ in 0..factorTwoLogLength, R (-s)) +
        ∫ s : ℝ in 0..factorTwoLogLength, R s := by
      rw [hreflectIntegral]
      simp only [neg_zero]
    _ = ∫ s : ℝ in 0..factorTwoLogLength, (R (-s) + R s) := by
      rw [intervalIntegral.integral_add hreflect hpos]
    _ = 2 * ∫ s : ℝ in 0..factorTwoLogLength,
        Real.exp (-oddRate k * s) * factorTwoSelfCorrelationRe g s := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro s hs
      have hs' : 0 ≤ s := by
        rw [uIcc_of_le hL] at hs
        exact hs.1
      dsimp only [R]
      unfold factorTwoSelfCorrelationRe
      rw [abs_neg, abs_of_nonneg hs',
        factorTwoSelfCorrelation_neg]
      simp only [Complex.conj_re]
      ring
    _ = geometricIntegralTerm factorTwoLogLength
        (factorTwoSelfCorrelationRe g) k := by
      unfold geometricIntegralTerm
      rfl

theorem factorTwoDiagonalRenormalizedSeries_hasSum
    (g : BombieriTest) :
    HasSum
      (renormalizedTerm factorTwoLogLength
        (factorTwoSelfCorrelationRe g 0)
        (factorTwoSelfCorrelationRe g))
      ((∫ s : ℝ in 0..factorTwoLogLength,
          stableGeometricIntegrand
            (factorTwoSelfCorrelationRe g 0)
            (factorTwoSelfCorrelationRe g) s) +
        (Real.log factorTwoLogLength + Real.log 2) *
          factorTwoSelfCorrelationRe g 0) := by
  have hCdiff : ContDiff ℝ 1 (factorTwoSelfCorrelationRe g) := by
    exact Complex.reCLM.contDiff.comp
      (factorTwoSelfCorrelation_contDiff g 1)
  obtain ⟨D, hD, hrem⟩ :=
    exists_continuous_removable_slope (factorTwoSelfCorrelationRe g) hCdiff
  have hinterchange : PairedIntegralInterchange factorTwoLogLength
      (factorTwoSelfCorrelationRe g 0) (factorTwoSelfCorrelationRe g) := by
    apply pairedIntegralInterchange_of_removable
      factorTwoLogLength_pos hCdiff.continuous
    · intro s _hs
      exact hrem s
    · exact removableMajorantLimit_intervalIntegrable hD
        (factorTwoSelfCorrelationRe g 0) factorTwoLogLength
  have hstable : IntervalIntegrable
      (stableGeometricIntegrand
        (factorTwoSelfCorrelationRe g 0) (factorTwoSelfCorrelationRe g))
      volume 0 factorTwoLogLength :=
    stableGeometricIntegrand_intervalIntegrable_of_removable
      hD (factorTwoSelfCorrelationRe g 0) factorTwoLogLength hrem
  have href : IntervalIntegrable referenceRegularized volume
      0 factorTwoLogLength :=
    referenceRegularized_intervalIntegrable factorTwoLogLength
  exact renormalizedSeries_hasSum_stable factorTwoLogLength_pos
    hCdiff.continuous hinterchange hstable href

theorem factorTwoDiagonalRenormalizedSeries_eq_stable
    (g : BombieriTest) :
    -Real.eulerMascheroniConstant * factorTwoSelfCorrelationRe g 0 -
        ∑' k : ℕ, renormalizedTerm factorTwoLogLength
          (factorTwoSelfCorrelationRe g 0)
          (factorTwoSelfCorrelationRe g) k =
      (∫ s : ℝ in 0..factorTwoLogLength,
        factorTwoDiagonalStableIntegrand g s) -
        (Real.log factorTwoLogLength + Real.eulerMascheroniConstant +
          Real.log 2) * factorTwoSelfCorrelationRe g 0 := by
  have hCdiff : ContDiff ℝ 1 (factorTwoSelfCorrelationRe g) := by
    exact Complex.reCLM.contDiff.comp
      (factorTwoSelfCorrelation_contDiff g 1)
  obtain ⟨D, hD, hrem⟩ :=
    exists_continuous_removable_slope (factorTwoSelfCorrelationRe g) hCdiff
  have hinterchange : PairedIntegralInterchange factorTwoLogLength
      (factorTwoSelfCorrelationRe g 0) (factorTwoSelfCorrelationRe g) := by
    apply pairedIntegralInterchange_of_removable
      factorTwoLogLength_pos hCdiff.continuous
    · intro s _hs
      exact hrem s
    · exact removableMajorantLimit_intervalIntegrable hD
        (factorTwoSelfCorrelationRe g 0) factorTwoLogLength
  have hstable : IntervalIntegrable
      (stableGeometricIntegrand
        (factorTwoSelfCorrelationRe g 0) (factorTwoSelfCorrelationRe g))
      volume 0 factorTwoLogLength :=
    stableGeometricIntegrand_intervalIntegrable_of_removable
      hD (factorTwoSelfCorrelationRe g 0) factorTwoLogLength hrem
  have href : IntervalIntegrable referenceRegularized volume
      0 factorTwoLogLength :=
    referenceRegularized_intervalIntegrable factorTwoLogLength
  have h := negated_geometric_identity factorTwoLogLength_pos
    hCdiff.continuous hinterchange hstable href
  simpa only [factorTwoDiagonalStableIntegrand,
    stableGeometricIntegrand, factorTwoSelfCorrelationRe] using h

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoDiagonalGeometric
