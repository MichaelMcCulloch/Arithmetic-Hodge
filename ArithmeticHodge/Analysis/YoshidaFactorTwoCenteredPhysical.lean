import ArithmeticHodge.Analysis.YoshidaFactorTwoPhysicalSymbol

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ComplexConjugate

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoCenteredPhysical

noncomputable section

open MultiplicativeWeil
open YoshidaBombieriCrossDistribution
open YoshidaCriticalLogCorrelation
open YoshidaFactorTwoAdjacentKernel
open YoshidaFactorTwoAdjacentSchwartz
open YoshidaFactorTwoCrossDistribution
open YoshidaFactorTwoPhysicalSymbol
open YoshidaFactorTwoPrimeCorrelationSymbol
open YoshidaRenormalizedGeometricKernel

/-!
# The centered physical factor-two symbol

The one-sided adjacent-correlation formula is translated by `log 2`.  This
places the self-correlation on its natural symmetric interval and retains the
smooth archimedean kernel and both prime atoms exactly.
-/

def factorTwoCenteredIntegrand (g : BombieriTest) (s : ℝ) : ℂ :=
  ((factorTwoAdjacentSmoothKernel (factorTwoLogLength + s) : ℝ) : ℂ) *
    factorTwoSelfCorrelation g s

def factorTwoSymmetricWeight (s : ℝ) : ℝ :=
  factorTwoAdjacentSmoothKernel (factorTwoLogLength + s) +
    factorTwoAdjacentSmoothKernel (factorTwoLogLength - s)

def factorTwoAntisymmetricWeight (s : ℝ) : ℝ :=
  factorTwoAdjacentSmoothKernel (factorTwoLogLength + s) -
    factorTwoAdjacentSmoothKernel (factorTwoLogLength - s)

def factorTwoPrimeShift : ℝ := Real.log (3 / 2 : ℝ)

def factorTwoFoldedIntegrand (g : BombieriTest) (s : ℝ) : ℂ :=
  ((factorTwoAdjacentSmoothKernel (factorTwoLogLength - s) : ℝ) : ℂ) *
      starRingEnd ℂ (factorTwoSelfCorrelation g s) +
    ((factorTwoAdjacentSmoothKernel (factorTwoLogLength + s) : ℝ) : ℂ) *
      factorTwoSelfCorrelation g s

theorem factorTwoSelfCorrelation_zero_im (g : BombieriTest) :
    (factorTwoSelfCorrelation g 0).im = 0 := by
  have hsym := factorTwoSelfCorrelation_neg g 0
  rw [neg_zero] at hsym
  change factorTwoSelfCorrelation g 0 =
    conj (factorTwoSelfCorrelation g 0) at hsym
  have him := congrArg Complex.im hsym
  rw [Complex.conj_im] at him
  linarith

theorem factorTwoCenteredIntegrand_intervalIntegrable
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    IntervalIntegrable (factorTwoCenteredIntegrand g) volume
      (-factorTwoLogLength) factorTwoLogLength := by
  have hgrow : IntervalIntegrable (fun u : ℝ ↦
      ((Real.exp (u / 2) : ℝ) : ℂ) *
        factorTwoAdjacentCorrelation g u)
      volume 0 factorTwoPhysicalLength := by
    apply Continuous.intervalIntegrable
    have hexp : Continuous (fun u : ℝ ↦
        ((Real.exp (u / 2) : ℝ) : ℂ)) := by fun_prop
    exact hexp.mul
      (factorTwoAdjacentCorrelation_contDiff g 0).continuous
  have htail := factorTwoTailIntegrand_intervalIntegrable
    g ha hab hsupport hratio
  have hsmooth : IntervalIntegrable (fun u : ℝ ↦
      ((factorTwoAdjacentSmoothKernel u : ℝ) : ℂ) *
        factorTwoAdjacentCorrelation g u)
      volume 0 factorTwoPhysicalLength := by
    have hsub := hgrow.sub htail
    apply hsub.congr
    intro u _hu
    unfold factorTwoAdjacentSmoothKernel factorTwoTailKernel
    change ((Real.exp (u / 2) : ℝ) : ℂ) *
          factorTwoAdjacentCorrelation g u -
        (((oddKernel u / 2 - Real.exp (-u / 2) : ℝ)) : ℂ) *
          factorTwoAdjacentCorrelation g u =
      (((2 * Real.cosh (u / 2) - oddKernel u / 2 : ℝ)) : ℂ) *
        factorTwoAdjacentCorrelation g u
    rw [Real.cosh_eq]
    push_cast
    ring
  have hshift := hsmooth.comp_add_right factorTwoLogLength
  convert hshift using 1
  · funext s
    unfold factorTwoCenteredIntegrand
    rw [factorTwoAdjacentCorrelation_eq_shift]
    congr 3 <;> ring
  · ring
  · unfold factorTwoPhysicalLength
    ring

theorem factorTwoCenteredIntegral_eq_folded
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    (∫ s : ℝ in -factorTwoLogLength..factorTwoLogLength,
      factorTwoCenteredIntegrand g s) =
      ∫ s : ℝ in 0..factorTwoLogLength,
        factorTwoFoldedIntegrand g s := by
  have hcenter := factorTwoCenteredIntegrand_intervalIntegrable
    g ha hab hsupport hratio
  have hL : 0 ≤ factorTwoLogLength := factorTwoLogLength_pos.le
  have hneg : IntervalIntegrable (factorTwoCenteredIntegrand g) volume
      (-factorTwoLogLength) 0 := by
    apply hcenter.mono_set
    intro s hs
    rw [uIcc_of_le (by linarith : -factorTwoLogLength ≤ 0)] at hs
    rw [uIcc_of_le (by linarith : -factorTwoLogLength ≤ factorTwoLogLength)]
    exact ⟨hs.1, hs.2.trans hL⟩
  have hpos : IntervalIntegrable (factorTwoCenteredIntegrand g) volume
      0 factorTwoLogLength := by
    apply hcenter.mono_set
    intro s hs
    rw [uIcc_of_le hL] at hs
    rw [uIcc_of_le (by linarith : -factorTwoLogLength ≤ factorTwoLogLength)]
    exact ⟨(neg_nonpos.mpr hL).trans hs.1, hs.2⟩
  have hreflect : IntervalIntegrable
      (fun s : ℝ ↦ factorTwoCenteredIntegrand g (-s)) volume
      0 factorTwoLogLength := by
    have h := (hneg.comp_mul_left (c := (-1 : ℝ))).symm
    convert h using 1 <;> norm_num
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hneg hpos
  have hreflectIntegral := intervalIntegral.integral_comp_neg
    (f := factorTwoCenteredIntegrand g)
    (a := 0) (b := factorTwoLogLength)
  calc
    (∫ s : ℝ in -factorTwoLogLength..factorTwoLogLength,
        factorTwoCenteredIntegrand g s) =
        (∫ s : ℝ in -factorTwoLogLength..0,
          factorTwoCenteredIntegrand g s) +
        ∫ s : ℝ in 0..factorTwoLogLength,
          factorTwoCenteredIntegrand g s := hsplit.symm
    _ = (∫ s : ℝ in 0..factorTwoLogLength,
          factorTwoCenteredIntegrand g (-s)) +
        ∫ s : ℝ in 0..factorTwoLogLength,
          factorTwoCenteredIntegrand g s := by
      rw [hreflectIntegral]
      simp only [neg_zero]
    _ = ∫ s : ℝ in 0..factorTwoLogLength,
        (factorTwoCenteredIntegrand g (-s) +
          factorTwoCenteredIntegrand g s) := by
      rw [intervalIntegral.integral_add hreflect hpos]
    _ = ∫ s : ℝ in 0..factorTwoLogLength,
        factorTwoFoldedIntegrand g s := by
      apply intervalIntegral.integral_congr
      intro s _hs
      unfold factorTwoFoldedIntegrand factorTwoCenteredIntegrand
      dsimp only
      rw [show factorTwoLogLength + -s = factorTwoLogLength - s by ring,
        factorTwoSelfCorrelation_neg]

theorem factorTwoFoldedIntegrand_intervalIntegrable
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    IntervalIntegrable (factorTwoFoldedIntegrand g) volume
      0 factorTwoLogLength := by
  have hcenter := factorTwoCenteredIntegrand_intervalIntegrable
    g ha hab hsupport hratio
  have hL : 0 ≤ factorTwoLogLength := factorTwoLogLength_pos.le
  have hneg : IntervalIntegrable (factorTwoCenteredIntegrand g) volume
      (-factorTwoLogLength) 0 := by
    apply hcenter.mono_set
    intro s hs
    rw [uIcc_of_le (by linarith : -factorTwoLogLength ≤ 0)] at hs
    rw [uIcc_of_le (by linarith : -factorTwoLogLength ≤ factorTwoLogLength)]
    exact ⟨hs.1, hs.2.trans hL⟩
  have hpos : IntervalIntegrable (factorTwoCenteredIntegrand g) volume
      0 factorTwoLogLength := by
    apply hcenter.mono_set
    intro s hs
    rw [uIcc_of_le hL] at hs
    rw [uIcc_of_le (by linarith : -factorTwoLogLength ≤ factorTwoLogLength)]
    exact ⟨(neg_nonpos.mpr hL).trans hs.1, hs.2⟩
  have hreflect : IntervalIntegrable
      (fun s : ℝ ↦ factorTwoCenteredIntegrand g (-s)) volume
      0 factorTwoLogLength := by
    have h := (hneg.comp_mul_left (c := (-1 : ℝ))).symm
    convert h using 1 <;> norm_num
  have hadd := hreflect.add hpos
  apply hadd.congr
  intro s _hs
  unfold factorTwoFoldedIntegrand factorTwoCenteredIntegrand
  dsimp only
  rw [show factorTwoLogLength + -s = factorTwoLogLength - s by ring,
    factorTwoSelfCorrelation_neg]

theorem factorTwoCenteredIntegral_re_eq_symmetric
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    (∫ s : ℝ in -factorTwoLogLength..factorTwoLogLength,
      factorTwoCenteredIntegrand g s).re =
      ∫ s : ℝ in 0..factorTwoLogLength,
        factorTwoSymmetricWeight s *
          (factorTwoSelfCorrelation g s).re := by
  have hfold := factorTwoCenteredIntegral_eq_folded
    g ha hab hsupport hratio
  have hfoldInt := factorTwoFoldedIntegrand_intervalIntegrable
    g ha hab hsupport hratio
  calc
    (∫ s : ℝ in -factorTwoLogLength..factorTwoLogLength,
        factorTwoCenteredIntegrand g s).re =
        (∫ s : ℝ in 0..factorTwoLogLength,
          factorTwoFoldedIntegrand g s).re := congrArg Complex.re hfold
    _ = ∫ s : ℝ in 0..factorTwoLogLength,
        (factorTwoFoldedIntegrand g s).re := by
      simpa only [Complex.reCLM_apply] using
        (Complex.reCLM.intervalIntegral_comp_comm hfoldInt).symm
    _ = ∫ s : ℝ in 0..factorTwoLogLength,
        factorTwoSymmetricWeight s *
          (factorTwoSelfCorrelation g s).re := by
      apply intervalIntegral.integral_congr
      intro s _hs
      unfold factorTwoFoldedIntegrand factorTwoSymmetricWeight
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.conj_re, zero_mul, sub_zero]
      ring

theorem factorTwoCenteredIntegral_im_eq_antisymmetric
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    (∫ s : ℝ in -factorTwoLogLength..factorTwoLogLength,
      factorTwoCenteredIntegrand g s).im =
      ∫ s : ℝ in 0..factorTwoLogLength,
        factorTwoAntisymmetricWeight s *
          (factorTwoSelfCorrelation g s).im := by
  have hfold := factorTwoCenteredIntegral_eq_folded
    g ha hab hsupport hratio
  have hfoldInt := factorTwoFoldedIntegrand_intervalIntegrable
    g ha hab hsupport hratio
  calc
    (∫ s : ℝ in -factorTwoLogLength..factorTwoLogLength,
        factorTwoCenteredIntegrand g s).im =
        (∫ s : ℝ in 0..factorTwoLogLength,
          factorTwoFoldedIntegrand g s).im := congrArg Complex.im hfold
    _ = ∫ s : ℝ in 0..factorTwoLogLength,
        (factorTwoFoldedIntegrand g s).im := by
      simpa only [Complex.imCLM_apply] using
        (Complex.imCLM.intervalIntegral_comp_comm hfoldInt).symm
    _ = ∫ s : ℝ in 0..factorTwoLogLength,
        factorTwoAntisymmetricWeight s *
          (factorTwoSelfCorrelation g s).im := by
      apply intervalIntegral.integral_congr
      intro s _hs
      unfold factorTwoFoldedIntegrand factorTwoAntisymmetricWeight
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.conj_re, Complex.conj_im, zero_mul,
        add_zero]
      ring

theorem factorTwoGlobalCrossSymbol_eq_centered_physical
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    factorTwoGlobalCrossSymbol g =
      (∫ s : ℝ in -factorTwoLogLength..factorTwoLogLength,
        factorTwoCenteredIntegrand g s) -
        factorTwoPrimeCorrelationSymbol g := by
  rw [factorTwoGlobalCrossSymbol_eq_physical
    g ha hab hsupport hratio]
  congr 1
  rw [show (fun u : ℝ ↦
      ((factorTwoAdjacentSmoothKernel u : ℝ) : ℂ) *
        factorTwoAdjacentCorrelation g u) =
      fun u : ℝ ↦
        ((factorTwoAdjacentSmoothKernel u : ℝ) : ℂ) *
          factorTwoSelfCorrelation g (u - factorTwoLogLength) by
    funext u
    rw [factorTwoAdjacentCorrelation_eq_shift]]
  have hshift := intervalIntegral.integral_comp_add_right
    (f := fun u : ℝ ↦
      ((factorTwoAdjacentSmoothKernel u : ℝ) : ℂ) *
        factorTwoSelfCorrelation g (u - factorTwoLogLength))
    (a := -factorTwoLogLength) (b := factorTwoLogLength)
    factorTwoLogLength
  rw [show (fun s : ℝ ↦ factorTwoCenteredIntegrand g s) =
      fun s : ℝ ↦
        (((factorTwoAdjacentSmoothKernel (s + factorTwoLogLength) : ℝ) : ℂ) *
          factorTwoSelfCorrelation g
            ((s + factorTwoLogLength) - factorTwoLogLength)) by
    funext s
    unfold factorTwoCenteredIntegrand
    congr 3 <;> ring]
  rw [hshift]
  congr 1
  · ring
  · unfold factorTwoPhysicalLength
    ring

theorem factorTwoGlobalCrossSymbol_re_eq_parity
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    (factorTwoGlobalCrossSymbol g).re =
      (∫ s : ℝ in 0..factorTwoLogLength,
        factorTwoSymmetricWeight s *
          (factorTwoSelfCorrelation g s).re) -
        (Real.log 2 / Real.sqrt 2) *
          (factorTwoSelfCorrelation g 0).re -
        (Real.log 3 / Real.sqrt 3) *
          (factorTwoSelfCorrelation g factorTwoPrimeShift).re := by
  rw [factorTwoGlobalCrossSymbol_eq_centered_physical
      g ha hab hsupport hratio,
    Complex.sub_re,
    factorTwoCenteredIntegral_re_eq_symmetric
      g ha hab hsupport hratio]
  unfold factorTwoPrimeCorrelationSymbol factorTwoPrimeShift
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring

theorem factorTwoGlobalCrossSymbol_im_eq_parity
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    (factorTwoGlobalCrossSymbol g).im =
      (∫ s : ℝ in 0..factorTwoLogLength,
        factorTwoAntisymmetricWeight s *
          (factorTwoSelfCorrelation g s).im) -
        (Real.log 3 / Real.sqrt 3) *
          (factorTwoSelfCorrelation g factorTwoPrimeShift).im := by
  rw [factorTwoGlobalCrossSymbol_eq_centered_physical
      g ha hab hsupport hratio,
    Complex.sub_im,
    factorTwoCenteredIntegral_im_eq_antisymmetric
      g ha hab hsupport hratio]
  unfold factorTwoPrimeCorrelationSymbol factorTwoPrimeShift
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero]
  rw [factorTwoSelfCorrelation_zero_im]
  ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoCenteredPhysical
