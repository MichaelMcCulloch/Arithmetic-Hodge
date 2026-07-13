import ArithmeticHodge.Analysis.YoshidaFactorTwoDiagonalGeometric
import ArithmeticHodge.Analysis.YoshidaFactorTwoCoreReduction

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoDiagonalPhysical

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilRestrictedSupportEndpointPositive
open YoshidaBombieriCrossDistribution
open YoshidaBombieriCrossMoments
open YoshidaBombieriDiagonalResidual
open YoshidaCriticalLogCorrelation
open YoshidaFactorTwoAdjacentKernel
open YoshidaFactorTwoCoreReduction
open YoshidaFactorTwoCrossDistribution
open YoshidaFactorTwoDiagonalGeometric
open YoshidaFactorTwoSelfCorrelationSupport
open YoshidaRenormalizedGeometricKernel
open YoshidaShiftedGeometricSeries
open YoshidaStructuralKernelIntegrability
open YoshidaZeroCorrelationGeometricSeries

/-!
# Exact physical diagonal on a factor-two cell

The polar moments and the complete renormalized digamma series are assembled
in the same self-correlation coordinates as the adjacent cross symbol.
-/

theorem integral_exp_selfCorrelation_eq_factorTwo_interval
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) (t : ℝ) :
    (∫ s : ℝ, ((Real.exp (t * s) : ℝ) : ℂ) *
      bombieriCriticalCrossCorrelation g g s) =
      ∫ s : ℝ in -factorTwoLogLength..factorTwoLogLength,
        ((Real.exp (t * s) : ℝ) : ℂ) *
          factorTwoSelfCorrelation g s := by
  change (∫ s : ℝ, ((Real.exp (t * s) : ℝ) : ℂ) *
      factorTwoSelfCorrelation g s) = _
  rw [intervalIntegral.integral_of_le (by
      linarith [factorTwoLogLength_pos] :
        -factorTwoLogLength ≤ factorTwoLogLength),
    ← integral_Icc_eq_integral_Ioc]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun s hs ↦ by
    rw [factorTwoSelfCorrelation_eq_zero_outside
      g ha hab hsupport hratio hs, mul_zero])).symm

theorem bombieriSelfPolar_re_eq_factorTwo_integral
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    (star (mellin (g : ℝ → ℂ) 1) * mellin (g : ℝ → ℂ) 0 +
      star (mellin (g : ℝ → ℂ) 0) * mellin (g : ℝ → ℂ) 1).re =
      ∫ s : ℝ in 0..factorTwoLogLength,
        4 * Real.cosh (s / 2) * factorTwoSelfCorrelationRe g s := by
  let J : ℝ → ℂ := fun s ↦
    ((((Real.exp (s / 2) + Real.exp (-s / 2) : ℝ)) : ℂ) *
      factorTwoSelfCorrelation g s)
  let R : ℝ → ℝ := fun s ↦
    (Real.exp (s / 2) + Real.exp (-s / 2)) *
      factorTwoSelfCorrelationRe g s
  have hplus := integral_exp_mul_bombieriCriticalCrossCorrelation
    (1 / 2 : ℝ) g g
  rw [bombieriCriticalMoment_neg_half_eq_mellin_one,
    bombieriCriticalMoment_half_eq_mellin_zero] at hplus
  have hminus := integral_exp_mul_bombieriCriticalCrossCorrelation
    (-(1 / 2) : ℝ) g g
  rw [show -(-(1 / 2 : ℝ)) = 1 / 2 by ring,
    bombieriCriticalMoment_half_eq_mellin_zero,
    bombieriCriticalMoment_neg_half_eq_mellin_one] at hminus
  have hplusInterval := integral_exp_selfCorrelation_eq_factorTwo_interval
    g ha hab hsupport hratio (1 / 2)
  have hminusInterval := integral_exp_selfCorrelation_eq_factorTwo_interval
    g ha hab hsupport hratio (-(1 / 2))
  have hJ : IntervalIntegrable J volume
      (-factorTwoLogLength) factorTwoLogLength := by
    apply Continuous.intervalIntegrable
    unfold J
    exact (by fun_prop : Continuous (fun s : ℝ ↦
      (((Real.exp (s / 2) + Real.exp (-s / 2) : ℝ)) : ℂ))).mul
        (factorTwoSelfCorrelation_contDiff g 0).continuous
  have hR : IntervalIntegrable R volume
      (-factorTwoLogLength) factorTwoLogLength := by
    apply Continuous.intervalIntegrable
    unfold R factorTwoSelfCorrelationRe
    exact (by fun_prop : Continuous (fun s : ℝ ↦
      Real.exp (s / 2) + Real.exp (-s / 2))).mul
        (Complex.continuous_re.comp
          (factorTwoSelfCorrelation_contDiff g 0).continuous)
  have hplusInt : IntervalIntegrable (fun s : ℝ ↦
      ((Real.exp ((1 / 2 : ℝ) * s) : ℝ) : ℂ) *
        factorTwoSelfCorrelation g s) volume
      (-factorTwoLogLength) factorTwoLogLength := by
    apply Continuous.intervalIntegrable
    exact (by fun_prop : Continuous (fun s : ℝ ↦
      ((Real.exp ((1 / 2 : ℝ) * s) : ℝ) : ℂ))).mul
        (factorTwoSelfCorrelation_contDiff g 0).continuous
  have hminusInt : IntervalIntegrable (fun s : ℝ ↦
      ((Real.exp (-(1 / 2 : ℝ) * s) : ℝ) : ℂ) *
        factorTwoSelfCorrelation g s) volume
      (-factorTwoLogLength) factorTwoLogLength := by
    apply Continuous.intervalIntegrable
    exact (by fun_prop : Continuous (fun s : ℝ ↦
      ((Real.exp (-(1 / 2 : ℝ) * s) : ℝ) : ℂ))).mul
        (factorTwoSelfCorrelation_contDiff g 0).continuous
  have hpolar :
      star (mellin (g : ℝ → ℂ) 1) * mellin (g : ℝ → ℂ) 0 +
          star (mellin (g : ℝ → ℂ) 0) * mellin (g : ℝ → ℂ) 1 =
        ∫ s : ℝ in -factorTwoLogLength..factorTwoLogLength, J s := by
    rw [← hplus, ← hminus, hplusInterval, hminusInterval,
      ← intervalIntegral.integral_add hplusInt hminusInt]
    apply intervalIntegral.integral_congr
    intro s _hs
    unfold J
    push_cast
    rw [show (1 / 2 : ℂ) * (s : ℂ) = (s : ℂ) / 2 by ring,
      show -(1 / 2 : ℂ) * (s : ℂ) = -(s : ℂ) / 2 by ring]
    ring
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
  rw [hpolar]
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
    _ = ∫ s : ℝ in 0..factorTwoLogLength,
        4 * Real.cosh (s / 2) * factorTwoSelfCorrelationRe g s := by
      apply intervalIntegral.integral_congr
      intro s _hs
      dsimp only [R]
      unfold factorTwoSelfCorrelationRe
      rw [factorTwoSelfCorrelation_neg]
      simp only [Complex.conj_re]
      rw [Real.cosh_eq]
      ring

def factorTwoDiagonalPhysicalIntegrand
    (g : BombieriTest) (s : ℝ) : ℝ :=
  2 * factorTwoAdjacentSmoothKernel s * factorTwoSelfCorrelationRe g s +
    factorTwoSelfCorrelationRe g 0 / s

theorem bombieriDiagonalResidual_eq_factorTwo_geometric
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) (n : ℕ) :
    bombieriDiagonalResidual g n =
      factorTwoSelfCorrelationRe g 0 / (n + 1 : ℕ) -
        geometricIntegralTerm factorTwoLogLength
          (factorTwoSelfCorrelationRe g) (n + 1) := by
  have hcoefRe : (((((n + 1 : ℕ) : ℝ) : ℂ))⁻¹).re =
      (((n + 1 : ℕ) : ℝ)⁻¹) := by
    rw [Complex.inv_re, Complex.normSq_ofReal]
    norm_num only [Complex.ofReal_re]
    field_simp
  have hcoefIm : (((((n + 1 : ℕ) : ℝ) : ℂ))⁻¹).im = 0 := by
    rw [Complex.inv_im]
    simp
  have hres := congrArg Complex.re
    (ofReal_bombieriDiagonalResidual_eq_cauchyResidual g n)
  simp only [Complex.ofReal_re, Complex.sub_re, Complex.mul_re] at hres
  rw [hcoefRe, hcoefIm, zero_mul, sub_zero] at hres
  rw [bombieriCauchySelfValue_re_eq_geometricIntegralTerm
    g ha hab hsupport hratio (n + 1)] at hres
  simpa only [div_eq_mul_inv, mul_comm] using hres

theorem tsum_bombieriDiagonalResidual_eq_factorTwo_geometric
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    (∑' n : ℕ, bombieriDiagonalResidual g n) =
      ∑' n : ℕ,
        (factorTwoSelfCorrelationRe g 0 / (n + 1 : ℕ) -
          geometricIntegralTerm factorTwoLogLength
            (factorTwoSelfCorrelationRe g) (n + 1)) := by
  apply tsum_congr
  intro n
  exact bombieriDiagonalResidual_eq_factorTwo_geometric
    g ha hab hsupport hratio n

theorem factorTwoDiagonalStableIntegrand_intervalIntegrable
    (g : BombieriTest) :
    IntervalIntegrable (factorTwoDiagonalStableIntegrand g) volume
      0 factorTwoLogLength := by
  have hCdiff : ContDiff ℝ 1 (factorTwoSelfCorrelationRe g) := by
    exact Complex.reCLM.contDiff.comp
      (factorTwoSelfCorrelation_contDiff g 1)
  obtain ⟨D, hD, hrem⟩ :=
    exists_continuous_removable_slope (factorTwoSelfCorrelationRe g) hCdiff
  have hstable : IntervalIntegrable
      (stableGeometricIntegrand
        (factorTwoSelfCorrelationRe g 0) (factorTwoSelfCorrelationRe g))
      volume 0 factorTwoLogLength :=
    stableGeometricIntegrand_intervalIntegrable_of_removable
      hD (factorTwoSelfCorrelationRe g 0) factorTwoLogLength hrem
  apply hstable.neg.congr
  intro s _hs
  change -(oddKernel s * factorTwoSelfCorrelationRe g s -
      factorTwoSelfCorrelationRe g 0 / s) =
    -oddKernel s * factorTwoSelfCorrelationRe g s +
      factorTwoSelfCorrelationRe g 0 / s
  ring

theorem factorTwoDiagonalPhysicalIntegrand_intervalIntegrable
    (g : BombieriTest) :
    IntervalIntegrable (factorTwoDiagonalPhysicalIntegrand g) volume
      0 factorTwoLogLength := by
  have hpolarInt : IntervalIntegrable (fun s : ℝ ↦
      4 * Real.cosh (s / 2) * factorTwoSelfCorrelationRe g s)
      volume 0 factorTwoLogLength := by
    apply Continuous.intervalIntegrable
    unfold factorTwoSelfCorrelationRe
    exact (by fun_prop : Continuous (fun s : ℝ ↦
      4 * Real.cosh (s / 2))).mul
        (Complex.continuous_re.comp
          (factorTwoSelfCorrelation_contDiff g 0).continuous)
  have hstableInt := factorTwoDiagonalStableIntegrand_intervalIntegrable g
  apply (hpolarInt.add hstableInt).congr
  intro s _hs
  unfold factorTwoDiagonalPhysicalIntegrand
  unfold factorTwoDiagonalStableIntegrand
  unfold factorTwoAdjacentSmoothKernel
  ring

theorem bombieriLocalCriticalForm_self_re_eq_factorTwoDiagonalPhysical
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    (bombieriLocalCriticalForm g g).re =
      (∫ s : ℝ in 0..factorTwoLogLength,
        factorTwoDiagonalPhysicalIntegrand g s) -
        (Real.log factorTwoLogLength + Real.eulerMascheroniConstant +
          Real.log 2 + Real.log Real.pi) *
            factorTwoSelfCorrelationRe g 0 := by
  let C0 : ℝ := factorTwoSelfCorrelationRe g 0
  let G : ℕ → ℝ := fun k ↦
    geometricIntegralTerm factorTwoLogLength
      (factorTwoSelfCorrelationRe g) k
  let R : ℕ → ℝ := fun k ↦
    renormalizedTerm factorTwoLogLength C0
      (factorTwoSelfCorrelationRe g) k
  have hres := tsum_bombieriDiagonalResidual_eq_factorTwo_geometric
    g ha hab hsupport hratio
  have hren := factorTwoDiagonalRenormalizedSeries_hasSum g
  have hindex := geometricIntegralTerm_zero_add_tsum_shifted_eq hren
  have hresNeg :
      (∑' n : ℕ, bombieriDiagonalResidual g n) =
        -(∑' n : ℕ, (G (n + 1) - C0 / (n + 1 : ℕ))) := by
    rw [hres]
    calc
      (∑' n : ℕ,
          (factorTwoSelfCorrelationRe g 0 / (n + 1 : ℕ) -
            geometricIntegralTerm factorTwoLogLength
              (factorTwoSelfCorrelationRe g) (n + 1))) =
          ∑' n : ℕ, -(G (n + 1) - C0 / (n + 1 : ℕ)) := by
        apply tsum_congr
        intro n
        dsimp only [G, C0]
        ring
      _ = -(∑' n : ℕ, (G (n + 1) - C0 / (n + 1 : ℕ))) := by
        rw [tsum_neg]
  have hindex' :
      G 0 + ∑' n : ℕ, (G (n + 1) - C0 / (n + 1 : ℕ)) =
        ∑' n : ℕ, R n := by
    have hrenTsum : (∑' n : ℕ, R n) =
        (∫ s : ℝ in 0..factorTwoLogLength,
          stableGeometricIntegrand
            (factorTwoSelfCorrelationRe g 0)
            (factorTwoSelfCorrelationRe g) s) +
          (Real.log factorTwoLogLength + Real.log 2) *
            factorTwoSelfCorrelationRe g 0 := by
      simpa only [R, C0] using hren.tsum_eq
    calc
      G 0 + ∑' n : ℕ, (G (n + 1) - C0 / (n + 1 : ℕ)) =
          (∫ s : ℝ in 0..factorTwoLogLength,
            stableGeometricIntegrand
              (factorTwoSelfCorrelationRe g 0)
              (factorTwoSelfCorrelationRe g) s) +
            (Real.log factorTwoLogLength + Real.log 2) *
              factorTwoSelfCorrelationRe g 0 := by
        simpa only [G, C0] using hindex
      _ = ∑' n : ℕ, R n := hrenTsum.symm
  have hcauchyZero := bombieriCauchySelfValue_re_eq_geometricIntegralTerm
    g ha hab hsupport hratio 0
  have hcore : bombieriCoreDiagonal g =
      (star (mellin (g : ℝ → ℂ) 1) * mellin (g : ℝ → ℂ) 0 +
        star (mellin (g : ℝ → ℂ) 0) * mellin (g : ℝ → ℂ) 1).re -
        (bombieriCauchyCrossValue g g 0).re -
        Real.eulerMascheroniConstant * C0 -
        Real.log Real.pi * C0 := by
    unfold bombieriCoreDiagonal bombieriCoreDiagonalSymbol
    dsimp only [C0, factorTwoSelfCorrelationRe, factorTwoSelfCorrelation,
      bombieriCriticalCrossCorrelation]
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
  have hseries := factorTwoDiagonalRenormalizedSeries_eq_stable g
  have hpolar := bombieriSelfPolar_re_eq_factorTwo_integral
    g ha hab hsupport hratio
  have hpolarInt : IntervalIntegrable (fun s : ℝ ↦
      4 * Real.cosh (s / 2) * factorTwoSelfCorrelationRe g s)
      volume 0 factorTwoLogLength := by
    apply Continuous.intervalIntegrable
    unfold factorTwoSelfCorrelationRe
    exact (by fun_prop : Continuous (fun s : ℝ ↦
      4 * Real.cosh (s / 2))).mul
        (Complex.continuous_re.comp
          (factorTwoSelfCorrelation_contDiff g 0).continuous)
  have hstableInt := factorTwoDiagonalStableIntegrand_intervalIntegrable g
  have hlocalDecomp : (bombieriLocalCriticalForm g g).re =
      (star (mellin (g : ℝ → ℂ) 1) * mellin (g : ℝ → ℂ) 0 +
        star (mellin (g : ℝ → ℂ) 0) * mellin (g : ℝ → ℂ) 1).re -
        Real.eulerMascheroniConstant * C0 -
        (∑' n : ℕ, R n) - Real.log Real.pi * C0 := by
    rw [bombieriLocalCriticalForm_self_re_eq_core_add_residual,
      hcore, hresNeg, hcauchyZero]
    linarith [hindex']
  have hseries' :
      -Real.eulerMascheroniConstant * C0 - ∑' n : ℕ, R n =
      (∫ s : ℝ in 0..factorTwoLogLength,
        factorTwoDiagonalStableIntegrand g s) -
        (Real.log factorTwoLogLength + Real.eulerMascheroniConstant +
          Real.log 2) * C0 := by
    simpa only [C0, R] using hseries
  rw [hlocalDecomp]
  calc
    (star (mellin (g : ℝ → ℂ) 1) * mellin (g : ℝ → ℂ) 0 +
          star (mellin (g : ℝ → ℂ) 0) * mellin (g : ℝ → ℂ) 1).re -
          Real.eulerMascheroniConstant * C0 -
          (∑' n : ℕ, R n) - Real.log Real.pi * C0 =
        (star (mellin (g : ℝ → ℂ) 1) * mellin (g : ℝ → ℂ) 0 +
          star (mellin (g : ℝ → ℂ) 0) * mellin (g : ℝ → ℂ) 1).re +
          (-Real.eulerMascheroniConstant * C0 - ∑' n : ℕ, R n) -
          Real.log Real.pi * C0 := by ring
    _ = (∫ s : ℝ in 0..factorTwoLogLength,
          4 * Real.cosh (s / 2) * factorTwoSelfCorrelationRe g s) +
        (∫ s : ℝ in 0..factorTwoLogLength,
          factorTwoDiagonalStableIntegrand g s) -
        (Real.log factorTwoLogLength + Real.eulerMascheroniConstant +
          Real.log 2) * C0 - Real.log Real.pi * C0 := by
      rw [hpolar, hseries']
      ring
    _ = (∫ s : ℝ in 0..factorTwoLogLength,
          (4 * Real.cosh (s / 2) * factorTwoSelfCorrelationRe g s +
            factorTwoDiagonalStableIntegrand g s)) -
        (Real.log factorTwoLogLength + Real.eulerMascheroniConstant +
          Real.log 2) * C0 - Real.log Real.pi * C0 := by
      rw [intervalIntegral.integral_add hpolarInt hstableInt]
    _ = (∫ s : ℝ in 0..factorTwoLogLength,
          factorTwoDiagonalPhysicalIntegrand g s) -
        (Real.log factorTwoLogLength + Real.eulerMascheroniConstant +
          Real.log 2 + Real.log Real.pi) *
            factorTwoSelfCorrelationRe g 0 := by
      have hintegrand :
          (∫ s : ℝ in 0..factorTwoLogLength,
            (4 * Real.cosh (s / 2) * factorTwoSelfCorrelationRe g s +
              factorTwoDiagonalStableIntegrand g s)) =
            ∫ s : ℝ in 0..factorTwoLogLength,
              factorTwoDiagonalPhysicalIntegrand g s := by
        apply intervalIntegral.integral_congr
        intro s _hs
        unfold factorTwoDiagonalPhysicalIntegrand
        unfold factorTwoDiagonalStableIntegrand
        unfold factorTwoAdjacentSmoothKernel
        ring
      rw [hintegrand]
      dsimp only [C0]
      ring

theorem bombieriFunctional_quadratic_re_eq_factorTwoDiagonalPhysical
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    (bombieriFunctional (bombieriQuadraticTest g)).re =
      (∫ s : ℝ in 0..factorTwoLogLength,
        factorTwoDiagonalPhysicalIntegrand g s) -
        (Real.log factorTwoLogLength + Real.eulerMascheroniConstant +
          Real.log 2 + Real.log Real.pi) *
            factorTwoSelfCorrelationRe g 0 := by
  rw [bombieriFunctional_quadratic_eq_bombieriLocalCriticalForm_le_two
    g ha hab hsupport hratio]
  exact bombieriLocalCriticalForm_self_re_eq_factorTwoDiagonalPhysical
    g ha hab hsupport hratio

/-- The same physical diagonal with the sole diagonal prime atom retained at
the factor-two endpoint.  The atom vanishes structurally because the
self-correlation is zero at `log 2`. -/
theorem bombieriFunctional_quadratic_re_eq_factorTwoDiagonalPhysical_with_endpoint
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    (bombieriFunctional (bombieriQuadraticTest g)).re =
      (∫ s : ℝ in 0..factorTwoLogLength,
        factorTwoDiagonalPhysicalIntegrand g s) -
        (Real.log factorTwoLogLength + Real.eulerMascheroniConstant +
          Real.log 2 + Real.log Real.pi) *
            factorTwoSelfCorrelationRe g 0 -
        2 * (Real.log 2 / Real.sqrt 2) *
          factorTwoSelfCorrelationRe g factorTwoLogLength := by
  have hend := congrArg Complex.re
    (factorTwoSelfCorrelation_length_eq_zero
      g ha hab hsupport hratio)
  simp only [Complex.zero_re] at hend
  rw [bombieriFunctional_quadratic_re_eq_factorTwoDiagonalPhysical
      g ha hab hsupport hratio,
    show factorTwoSelfCorrelationRe g factorTwoLogLength = 0 by
      exact hend,
    mul_zero, sub_zero]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoDiagonalPhysical
