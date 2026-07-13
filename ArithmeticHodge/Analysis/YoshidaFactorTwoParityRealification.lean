import ArithmeticHodge.Analysis.YoshidaFactorTwoParityDeterminant
import ArithmeticHodge.Analysis.MultiplicativeWeilQuadraticReality

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoParityRealification

noncomputable section

open MultiplicativeWeil
open YoshidaBombieriCrossDistribution
open YoshidaCauchyPairing
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoCrossDistribution
open YoshidaFactorTwoDiagonalGeometric
open YoshidaFactorTwoDiagonalPhysical
open YoshidaFactorTwoParityDeterminant

/-!
# Exact realification of the factor-two parity channels

The critical self-correlation is expanded through the canonical coefficient-
conjugation-fixed real and imaginary Bombieri projections.  This section is
purely structural: it introduces no positivity or determinant hypothesis.
-/

/-- The critical cross-correlation of two coefficient-conjugation-fixed tests
is real at every shift. -/
theorem bombieriCriticalCrossCorrelation_im_eq_zero_of_conjugateFixed
    (f g : BombieriTest)
    (hf : bombieriConjugateTest f = f)
    (hg : bombieriConjugateTest g = g) (s : ℝ) :
    (bombieriCriticalCrossCorrelation f g s).im = 0 := by
  have hf_apply (x : ℝ) : starRingEnd ℂ (f x) = f x := by
    have h := congrArg (fun q : BombieriTest ↦ q x) hf
    simpa only [bombieriConjugateTest_apply] using h
  have hg_apply (x : ℝ) : starRingEnd ℂ (g x) = g x := by
    have h := congrArg (fun q : BombieriTest ↦ q x) hg
    simpa only [bombieriConjugateTest_apply] using h
  have hf_pullback (x : ℝ) :
      starRingEnd ℂ (f.logarithmicPullbackSchwartz (1 / 2) x) =
        f.logarithmicPullbackSchwartz (1 / 2) x := by
    simp only [BombieriTest.logarithmicPullbackSchwartz_apply,
      BombieriTest.logarithmicPullback, map_mul, Complex.conj_ofReal,
      hf_apply]
  have hg_pullback (x : ℝ) :
      starRingEnd ℂ (g.logarithmicPullbackSchwartz (1 / 2) x) =
        g.logarithmicPullbackSchwartz (1 / 2) x := by
    simp only [BombieriTest.logarithmicPullbackSchwartz_apply,
      BombieriTest.logarithmicPullback, map_mul, Complex.conj_ofReal,
      hg_apply]
  have hfixed :
      bombieriCriticalCrossCorrelation f g s =
        starRingEnd ℂ (bombieriCriticalCrossCorrelation f g s) := by
    rw [bombieriCriticalCrossCorrelation, crossCorrelation_apply]
    calc
      (∫ x : ℝ,
          star (f.logarithmicPullbackSchwartz (1 / 2) x) *
            g.logarithmicPullbackSchwartz (1 / 2) (s + x)) =
          ∫ x : ℝ,
            starRingEnd ℂ
              (star (f.logarithmicPullbackSchwartz (1 / 2) x) *
                g.logarithmicPullbackSchwartz (1 / 2) (s + x)) := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [map_mul, starRingEnd_apply, star_star, hg_pullback]
        exact congrArg
          (fun z : ℂ ↦ z *
            g.logarithmicPullbackSchwartz (1 / 2) (s + x))
          (hf_pullback x)
      _ = starRingEnd ℂ
          (∫ x : ℝ,
            star (f.logarithmicPullbackSchwartz (1 / 2) x) *
              g.logarithmicPullbackSchwartz (1 / 2) (s + x)) := by
        simpa only [RCLike.star_def] using
          (integral_conj (f := fun x : ℝ ↦
            star (f.logarithmicPullbackSchwartz (1 / 2) x) *
              g.logarithmicPullbackSchwartz (1 / 2) (s + x)))
  exact Complex.conj_eq_iff_im.mp hfixed.symm

/-- Exact sesquilinear expansion of the self-correlation through the
canonical real and imaginary Bombieri projections. -/
theorem factorTwoSelfCorrelation_eq_realImag (g : BombieriTest) (s : ℝ) :
    let u := bombieriRealPartTest g
    let v := bombieriImagPartTest g
    factorTwoSelfCorrelation g s =
      factorTwoSelfCorrelation u s + factorTwoSelfCorrelation v s +
        Complex.I *
          (bombieriCriticalCrossCorrelation u v s -
            bombieriCriticalCrossCorrelation v u s) := by
  dsimp only
  change bombieriCriticalCrossCorrelation g g s =
    bombieriCriticalCrossCorrelation
        (bombieriRealPartTest g) (bombieriRealPartTest g) s +
      bombieriCriticalCrossCorrelation
        (bombieriImagPartTest g) (bombieriImagPartTest g) s +
      Complex.I *
        (bombieriCriticalCrossCorrelation
            (bombieriRealPartTest g) (bombieriImagPartTest g) s -
          bombieriCriticalCrossCorrelation
            (bombieriImagPartTest g) (bombieriRealPartTest g) s)
  calc
    bombieriCriticalCrossCorrelation g g s =
        bombieriCriticalCrossCorrelation
          (bombieriRealPartTest g +
            Complex.I • bombieriImagPartTest g)
          (bombieriRealPartTest g +
            Complex.I • bombieriImagPartTest g) s := by
      rw [bombieriRealPartTest_add_I_smul_imagPartTest]
    _ = _ := by
      simp only [bombieriCriticalCrossCorrelation_add_left,
        bombieriCriticalCrossCorrelation_add_right,
        bombieriCriticalCrossCorrelation_smul_left,
        bombieriCriticalCrossCorrelation_smul_right, starRingEnd_apply]
      rw [show star (Complex.I : ℂ) = -Complex.I from Complex.conj_I]
      ring_nf
      rw [Complex.I_sq]
      ring

/-- The real self-correlation is the sum of its two conjugation-fixed
diagonal channels. -/
theorem factorTwoSelfCorrelation_re_eq_realImag (g : BombieriTest) (s : ℝ) :
    let u := bombieriRealPartTest g
    let v := bombieriImagPartTest g
    (factorTwoSelfCorrelation g s).re =
      (factorTwoSelfCorrelation u s).re +
        (factorTwoSelfCorrelation v s).re := by
  dsimp only
  have huv :=
    bombieriCriticalCrossCorrelation_im_eq_zero_of_conjugateFixed
      (bombieriRealPartTest g) (bombieriImagPartTest g)
      (bombieriConjugateTest_realPartTest g)
      (bombieriConjugateTest_imagPartTest g) s
  have hvu :=
    bombieriCriticalCrossCorrelation_im_eq_zero_of_conjugateFixed
      (bombieriImagPartTest g) (bombieriRealPartTest g)
      (bombieriConjugateTest_imagPartTest g)
      (bombieriConjugateTest_realPartTest g) s
  have h := congrArg Complex.re (factorTwoSelfCorrelation_eq_realImag g s)
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, zero_mul, one_mul, Complex.sub_im,
    huv, hvu, sub_self, add_zero] at h
  exact h

/-- The imaginary self-correlation is the alternating real mixed channel;
there is no additional factor of two. -/
theorem factorTwoSelfCorrelation_im_eq_realImag (g : BombieriTest) (s : ℝ) :
    let u := bombieriRealPartTest g
    let v := bombieriImagPartTest g
    (factorTwoSelfCorrelation g s).im =
      (bombieriCriticalCrossCorrelation u v s).re -
        (bombieriCriticalCrossCorrelation v u s).re := by
  dsimp only
  have huu :=
    bombieriCriticalCrossCorrelation_im_eq_zero_of_conjugateFixed
      (bombieriRealPartTest g) (bombieriRealPartTest g)
      (bombieriConjugateTest_realPartTest g)
      (bombieriConjugateTest_realPartTest g) s
  have hvv :=
    bombieriCriticalCrossCorrelation_im_eq_zero_of_conjugateFixed
      (bombieriImagPartTest g) (bombieriImagPartTest g)
      (bombieriConjugateTest_imagPartTest g)
      (bombieriConjugateTest_imagPartTest g) s
  change (factorTwoSelfCorrelation
    (bombieriRealPartTest g) s).im = 0 at huu
  change (factorTwoSelfCorrelation
    (bombieriImagPartTest g) s).im = 0 at hvv
  have h := congrArg Complex.im (factorTwoSelfCorrelation_eq_realImag g s)
  simp only [Complex.add_im, Complex.sub_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add,
    huu, hvv] at h
  exact h

/-- The endpoint-retaining physical diagonal coordinate. -/
def factorTwoDiagonalCoordinate (g : BombieriTest) : ℝ :=
  (∫ s : ℝ in 0..factorTwoLogLength,
      factorTwoDiagonalPhysicalIntegrand g s) -
    (Real.log factorTwoLogLength + Real.eulerMascheroniConstant +
      Real.log 2 + Real.log Real.pi) * factorTwoSelfCorrelationRe g 0 -
    2 * (Real.log 2 / Real.sqrt 2) *
      factorTwoSelfCorrelationRe g factorTwoLogLength

/-- The symmetric real folded cross coordinate. -/
def factorTwoSymmetricCoordinate (g : BombieriTest) : ℝ :=
  (∫ s : ℝ in 0..factorTwoLogLength,
      factorTwoSymmetricWeight s * (factorTwoSelfCorrelation g s).re) -
    (Real.log 2 / Real.sqrt 2) * (factorTwoSelfCorrelation g 0).re -
    (Real.log 3 / Real.sqrt 3) *
      (factorTwoSelfCorrelation g factorTwoPrimeShift).re

/-- The antisymmetric imaginary folded cross coordinate. -/
def factorTwoAntisymmetricCoordinate (g : BombieriTest) : ℝ :=
  (∫ s : ℝ in 0..factorTwoLogLength,
      factorTwoAntisymmetricWeight s * (factorTwoSelfCorrelation g s).im) -
    (Real.log 3 / Real.sqrt 3) *
      (factorTwoSelfCorrelation g factorTwoPrimeShift).im

/-- The alternating real mixed channel between two conjugation-fixed tests. -/
def factorTwoMixedParityCoupling (u v : BombieriTest) : ℝ :=
  (∫ s : ℝ in 0..factorTwoLogLength,
      factorTwoAntisymmetricWeight s *
        ((bombieriCriticalCrossCorrelation u v s).re -
          (bombieriCriticalCrossCorrelation v u s).re)) -
    (Real.log 3 / Real.sqrt 3) *
      ((bombieriCriticalCrossCorrelation u v factorTwoPrimeShift).re -
        (bombieriCriticalCrossCorrelation v u factorTwoPrimeShift).re)

/-- The physical diagonal is additive across the canonical real and imaginary
projections.  Its removable integrand is interval-integrable without support
hypotheses. -/
theorem factorTwoDiagonalCoordinate_eq_realImag (g : BombieriTest) :
    factorTwoDiagonalCoordinate g =
      factorTwoDiagonalCoordinate (bombieriRealPartTest g) +
        factorTwoDiagonalCoordinate (bombieriImagPartTest g) := by
  have huInt := factorTwoDiagonalPhysicalIntegrand_intervalIntegrable
    (bombieriRealPartTest g)
  have hvInt := factorTwoDiagonalPhysicalIntegrand_intervalIntegrable
    (bombieriImagPartTest g)
  have hintegral :
      (∫ s : ℝ in 0..factorTwoLogLength,
          factorTwoDiagonalPhysicalIntegrand g s) =
        ∫ s : ℝ in 0..factorTwoLogLength,
          (factorTwoDiagonalPhysicalIntegrand
              (bombieriRealPartTest g) s +
            factorTwoDiagonalPhysicalIntegrand
              (bombieriImagPartTest g) s) := by
    apply intervalIntegral.integral_congr
    intro s _hs
    unfold factorTwoDiagonalPhysicalIntegrand
    unfold factorTwoSelfCorrelationRe
    rw [factorTwoSelfCorrelation_re_eq_realImag g s,
      factorTwoSelfCorrelation_re_eq_realImag g 0]
    ring
  unfold factorTwoDiagonalCoordinate
  rw [hintegral, intervalIntegral.integral_add huInt hvInt]
  unfold factorTwoSelfCorrelationRe
  rw [factorTwoSelfCorrelation_re_eq_realImag g 0,
    factorTwoSelfCorrelation_re_eq_realImag g factorTwoLogLength]
  ring

/-- Under the ratio-two support hypotheses that make the folded symmetric
integrals genuine Bochner integrals, the symmetric coordinate is additive
across the canonical real and imaginary projections. -/
theorem factorTwoSymmetricCoordinate_eq_realImag
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    factorTwoSymmetricCoordinate g =
      factorTwoSymmetricCoordinate (bombieriRealPartTest g) +
        factorTwoSymmetricCoordinate (bombieriImagPartTest g) := by
  have huSupport :
      tsupport (bombieriRealPartTest g : ℝ → ℂ) ⊆ Set.Icc a b :=
    (bombieriRealPartTest_tsupport_subset g).trans hsupport
  have hvSupport :
      tsupport (bombieriImagPartTest g : ℝ → ℂ) ⊆ Set.Icc a b :=
    (bombieriImagPartTest_tsupport_subset g).trans hsupport
  have huFold := factorTwoFoldedIntegrand_intervalIntegrable
    (bombieriRealPartTest g) ha hab huSupport hratio
  have hvFold := factorTwoFoldedIntegrand_intervalIntegrable
    (bombieriImagPartTest g) ha hab hvSupport hratio
  have huFoldRe : IntervalIntegrable
      (fun s : ℝ ↦
        (factorTwoFoldedIntegrand (bombieriRealPartTest g) s).re)
      volume 0 factorTwoLogLength :=
    ⟨Complex.reCLM.integrable_comp huFold.1,
      Complex.reCLM.integrable_comp huFold.2⟩
  have hvFoldRe : IntervalIntegrable
      (fun s : ℝ ↦
        (factorTwoFoldedIntegrand (bombieriImagPartTest g) s).re)
      volume 0 factorTwoLogLength :=
    ⟨Complex.reCLM.integrable_comp hvFold.1,
      Complex.reCLM.integrable_comp hvFold.2⟩
  have huInt : IntervalIntegrable
      (fun s : ℝ ↦ factorTwoSymmetricWeight s *
        (factorTwoSelfCorrelation (bombieriRealPartTest g) s).re)
      volume 0 factorTwoLogLength := by
    apply huFoldRe.congr
    intro s _hs
    unfold factorTwoFoldedIntegrand factorTwoSymmetricWeight
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re, zero_mul, sub_zero]
    ring
  have hvInt : IntervalIntegrable
      (fun s : ℝ ↦ factorTwoSymmetricWeight s *
        (factorTwoSelfCorrelation (bombieriImagPartTest g) s).re)
      volume 0 factorTwoLogLength := by
    apply hvFoldRe.congr
    intro s _hs
    unfold factorTwoFoldedIntegrand factorTwoSymmetricWeight
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re, zero_mul, sub_zero]
    ring
  have hintegral :
      (∫ s : ℝ in 0..factorTwoLogLength,
          factorTwoSymmetricWeight s *
            (factorTwoSelfCorrelation g s).re) =
        ∫ s : ℝ in 0..factorTwoLogLength,
          (factorTwoSymmetricWeight s *
              (factorTwoSelfCorrelation (bombieriRealPartTest g) s).re +
            factorTwoSymmetricWeight s *
              (factorTwoSelfCorrelation (bombieriImagPartTest g) s).re) := by
    apply intervalIntegral.integral_congr
    intro s _hs
    dsimp only
    rw [factorTwoSelfCorrelation_re_eq_realImag]
    ring
  unfold factorTwoSymmetricCoordinate
  rw [hintegral, intervalIntegral.integral_add huInt hvInt,
    factorTwoSelfCorrelation_re_eq_realImag g 0,
    factorTwoSelfCorrelation_re_eq_realImag g factorTwoPrimeShift]
  ring

/-- The antisymmetric coordinate is exactly the alternating mixed real
channel of the canonical projections. -/
theorem factorTwoAntisymmetricCoordinate_eq_realImag (g : BombieriTest) :
    factorTwoAntisymmetricCoordinate g =
      factorTwoMixedParityCoupling
        (bombieriRealPartTest g) (bombieriImagPartTest g) := by
  have hintegral :
      (∫ s : ℝ in 0..factorTwoLogLength,
          factorTwoAntisymmetricWeight s *
            (factorTwoSelfCorrelation g s).im) =
        ∫ s : ℝ in 0..factorTwoLogLength,
          factorTwoAntisymmetricWeight s *
            ((bombieriCriticalCrossCorrelation
                (bombieriRealPartTest g) (bombieriImagPartTest g) s).re -
              (bombieriCriticalCrossCorrelation
                (bombieriImagPartTest g) (bombieriRealPartTest g) s).re) := by
    apply intervalIntegral.integral_congr
    intro s _hs
    dsimp only
    rw [factorTwoSelfCorrelation_im_eq_realImag]
  unfold factorTwoAntisymmetricCoordinate factorTwoMixedParityCoupling
  rw [hintegral,
    factorTwoSelfCorrelation_im_eq_realImag g factorTwoPrimeShift]

/-- Universal nonnegativity on the same-seed factor-two span is exactly the
realified determinant inequality for the two diagonal channels and their
alternating mixed coupling. -/
theorem bombieriFunctional_twoBump_nonneg_iff_realImagParity
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    (∀ c : ℂ,
      0 ≤ (bombieriFunctional
        (bombieriQuadraticTest
          (g + c • normalizedDilation 2 (by norm_num) g))).re) ↔
      (factorTwoSymmetricCoordinate (bombieriRealPartTest g) +
          factorTwoSymmetricCoordinate (bombieriImagPartTest g)) ^ 2 +
        factorTwoMixedParityCoupling
            (bombieriRealPartTest g) (bombieriImagPartTest g) ^ 2 ≤
      (factorTwoDiagonalCoordinate (bombieriRealPartTest g) +
          factorTwoDiagonalCoordinate (bombieriImagPartTest g)) ^ 2 := by
  have hfold := bombieriFunctional_twoBump_nonneg_iff_foldedParity
    g ha hab hsupport hratio
  change
    (∀ c : ℂ,
      0 ≤ (bombieriFunctional
        (bombieriQuadraticTest
          (g + c • normalizedDilation 2 (by norm_num) g))).re) ↔
      factorTwoSymmetricCoordinate g ^ 2 +
        factorTwoAntisymmetricCoordinate g ^ 2 ≤
          factorTwoDiagonalCoordinate g ^ 2 at hfold
  rw [factorTwoSymmetricCoordinate_eq_realImag
      g ha hab hsupport hratio,
    factorTwoAntisymmetricCoordinate_eq_realImag g,
    factorTwoDiagonalCoordinate_eq_realImag g] at hfold
  exact hfold

/-- A strict reverse of the realified determinant is exactly the existence of
a negative same-seed factor-two Bombieri test. -/
theorem exists_bombieriFunctional_twoBump_neg_iff_realImagParity
    (g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hsupport : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    (∃ c : ℂ,
      (bombieriFunctional
        (bombieriQuadraticTest
          (g + c • normalizedDilation 2 (by norm_num) g))).re < 0) ↔
      (factorTwoDiagonalCoordinate (bombieriRealPartTest g) +
          factorTwoDiagonalCoordinate (bombieriImagPartTest g)) ^ 2 <
        (factorTwoSymmetricCoordinate (bombieriRealPartTest g) +
            factorTwoSymmetricCoordinate (bombieriImagPartTest g)) ^ 2 +
          factorTwoMixedParityCoupling
              (bombieriRealPartTest g) (bombieriImagPartTest g) ^ 2 := by
  have hfold := exists_bombieriFunctional_twoBump_neg_iff_foldedParity
    g ha hab hsupport hratio
  change
    (∃ c : ℂ,
      (bombieriFunctional
        (bombieriQuadraticTest
          (g + c • normalizedDilation 2 (by norm_num) g))).re < 0) ↔
      factorTwoDiagonalCoordinate g ^ 2 <
        factorTwoSymmetricCoordinate g ^ 2 +
          factorTwoAntisymmetricCoordinate g ^ 2 at hfold
  rw [factorTwoSymmetricCoordinate_eq_realImag
      g ha hab hsupport hratio,
    factorTwoAntisymmetricCoordinate_eq_realImag g,
    factorTwoDiagonalCoordinate_eq_realImag g] at hfold
  exact hfold

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoParityRealification
