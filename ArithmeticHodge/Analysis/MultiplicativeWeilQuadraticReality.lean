import ArithmeticHodge.Analysis.MultiplicativeWeilFunctional
import ArithmeticHodge.Analysis.MultiplicativeWeilQuadraticMellin

/-!
# Reality of Bombieri's quadratic functional

The multiplicative autocorrelation is carried to its pointwise complex
conjugate by Bombieri's transpose.  Each source-side component commutes with
coefficient conjugation, so the complete quadratic value is real without RH.
-/

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ContDiff Distributions

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

def bombieriConjugateTest (f : BombieriTest) : BombieriTest :=
  TestFunction.postcompCLM Complex.conjCLE.toContinuousLinearMap f

@[simp]
theorem bombieriConjugateTest_apply (f : BombieriTest) (x : ℝ) :
    bombieriConjugateTest f x = starRingEnd ℂ (f x) := rfl

theorem BombieriTest.apply_eq_zero_of_nonpos (f : BombieriTest)
    {x : ℝ} (hx : ¬ 0 < x) : f x = 0 := by
  by_contra hne
  exact hx (by
    simpa [positiveHalfLine] using
      f.tsupport_subset (subset_tsupport f (Function.mem_support.mpr hne)))

theorem transpose_bombieriQuadraticTest_apply_eq_conj
    (g : BombieriTest) {x : ℝ} (hx : 0 < x) :
    transpose (bombieriQuadraticTest g : ℝ → ℂ) x =
      starRingEnd ℂ (bombieriQuadraticTest g x) := by
  rw [transpose_apply_of_pos _ hx, bombieriQuadraticTest_apply,
    bombieriQuadraticTest_apply]
  unfold autocorrelation
  let h : ℝ → ℂ := fun y ↦
    g (x⁻¹ * y) * starRingEnd ℂ (g y)
  have hscale := integral_comp_mul_right_Ioi h 0 hx
  calc
    (∫ y : ℝ in Ioi 0, h y) / (x : ℂ) =
        ∫ y : ℝ in Ioi 0, h (y * x) := by
      rw [hscale]
      simp only [zero_mul]
      change (∫ y : ℝ in Ioi 0, h y) * (x : ℂ)⁻¹ =
        ((x⁻¹ : ℝ) : ℂ) * (∫ y : ℝ in Ioi 0, h y)
      rw [Complex.ofReal_inv]
      ring
    _ = ∫ y : ℝ in Ioi 0,
        starRingEnd ℂ (g (x * y) * starRingEnd ℂ (g y)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y _hy
      simp only [h, map_mul, starRingEnd_self_apply]
      rw [show x⁻¹ * (y * x) = y by field_simp]
      ring
    _ = starRingEnd ℂ
        (∫ y : ℝ in Ioi 0, g (x * y) * starRingEnd ℂ (g y)) :=
      integral_conj

theorem transposeLinearMap_bombieriQuadraticTest
    (g : BombieriTest) :
    transposeLinearMap (bombieriQuadraticTest g) =
      bombieriConjugateTest (bombieriQuadraticTest g) := by
  ext x
  by_cases hx : 0 < x
  · rw [transposeLinearMap_apply,
      transpose_bombieriQuadraticTest_apply_eq_conj g hx]
    rfl
  · rw [(transposeLinearMap (bombieriQuadraticTest g)).apply_eq_zero_of_nonpos hx,
      (bombieriConjugateTest (bombieriQuadraticTest g)).apply_eq_zero_of_nonpos hx]

theorem mellin_bombieriConjugateTest (f : BombieriTest) (s : ℂ) :
    mellin (bombieriConjugateTest f : ℝ → ℂ) s =
      coefficientConjugate (mellin (f : ℝ → ℂ)) s := by
  simpa only [bombieriConjugateTest_apply] using
    mellin_conjugate (f : ℝ → ℂ) s

theorem bombieriPolarLinearMap_conjugateTest (f : BombieriTest) :
    bombieriPolarLinearMap (bombieriConjugateTest f) =
      starRingEnd ℂ (bombieriPolarLinearMap f) := by
  simp only [bombieriPolarLinearMap_apply, mellin_bombieriConjugateTest,
    coefficientConjugate, map_add, map_zero, map_one]

theorem transpose_bombieriConjugateTest_apply_of_pos
    (f : BombieriTest) {x : ℝ} (hx : 0 < x) :
    transpose (bombieriConjugateTest f : ℝ → ℂ) x =
      starRingEnd ℂ (transpose (f : ℝ → ℂ) x) := by
  rw [transpose_apply_of_pos _ hx, transpose_apply_of_pos _ hx]
  simp only [bombieriConjugateTest_apply, map_div₀, Complex.conj_ofReal]

theorem primeKernel_conjugateTest (f : BombieriTest) (k : ℕ) :
    primeKernel (bombieriConjugateTest f) k =
      starRingEnd ℂ (primeKernel f k) := by
  have hk : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
  simp only [primeKernel, bombieriConjugateTest_apply, map_add]
  rw [transpose_bombieriConjugateTest_apply_of_pos f hk]

theorem vonMangoldtPrimeSummand_conjugateTest
    (f : BombieriTest) (k : ℕ) :
    vonMangoldtPrimeSummand (bombieriConjugateTest f) k =
      starRingEnd ℂ (vonMangoldtPrimeSummand f k) := by
  simp only [vonMangoldtPrimeSummand, primeKernel_conjugateTest, map_mul,
    Complex.conj_ofReal]

theorem primeSum_conjugateTest (f : BombieriTest) :
    primeSum (bombieriConjugateTest f) =
      starRingEnd ℂ (primeSum f) := by
  rw [primeSum, primeSum, Complex.conj_tsum]
  exact tsum_congr (vonMangoldtPrimeSummand_conjugateTest f)

theorem bombieriArchIntegrand_conjugateTest
    (f : BombieriTest) {x : ℝ} (hx : 0 < x) :
    bombieriArchIntegrand (bombieriConjugateTest f) x =
      starRingEnd ℂ (bombieriArchIntegrand f x) := by
  rw [bombieriArchIntegrand, bombieriArchIntegrand,
    transpose_bombieriConjugateTest_apply_of_pos f hx]
  simp only [bombieriConjugateTest_apply, map_sub, map_add, map_mul,
    map_div₀, map_pow, Complex.conj_ofReal, map_ofNat, map_one]

theorem bombieriArchTerm_conjugateTest (f : BombieriTest) :
    bombieriArchTerm (bombieriConjugateTest f) =
      starRingEnd ℂ (bombieriArchTerm f) := by
  have hintegral :
      (∫ x : ℝ in Ioi 1,
          bombieriArchIntegrand (bombieriConjugateTest f) x) =
        starRingEnd ℂ
          (∫ x : ℝ in Ioi 1, bombieriArchIntegrand f x) := by
    calc
      (∫ x : ℝ in Ioi 1,
          bombieriArchIntegrand (bombieriConjugateTest f) x) =
          ∫ x : ℝ in Ioi 1,
            starRingEnd ℂ (bombieriArchIntegrand f x) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        exact bombieriArchIntegrand_conjugateTest f (zero_lt_one.trans hx)
      _ = starRingEnd ℂ
          (∫ x : ℝ in Ioi 1, bombieriArchIntegrand f x) :=
        integral_conj
  unfold bombieriArchTerm
  rw [hintegral]
  simp only [bombieriConjugateTest_apply, map_sub, map_mul, map_neg,
    Complex.conj_ofReal]

theorem bombieriFunctional_conjugateTest (f : BombieriTest) :
    bombieriFunctional (bombieriConjugateTest f) =
      starRingEnd ℂ (bombieriFunctional f) := by
  change bombieriPolarLinearMap (bombieriConjugateTest f) -
      primeSum (bombieriConjugateTest f) +
        bombieriArchTerm (bombieriConjugateTest f) =
    starRingEnd ℂ
      (bombieriPolarLinearMap f - primeSum f + bombieriArchTerm f)
  rw [bombieriPolarLinearMap_conjugateTest,
    primeSum_conjugateTest, bombieriArchTerm_conjugateTest]
  simp only [map_add, map_sub]

theorem bombieriFunctional_bombieriQuadraticTest_im_eq_zero
    (g : BombieriTest) :
    (bombieriFunctional (bombieriQuadraticTest g)).im = 0 := by
  have hfixed :
      bombieriFunctional (bombieriQuadraticTest g) =
        starRingEnd ℂ (bombieriFunctional (bombieriQuadraticTest g)) := by
    calc
      bombieriFunctional (bombieriQuadraticTest g) =
          bombieriFunctional
            (transposeLinearMap (bombieriQuadraticTest g)) :=
        (bombieriFunctional_transpose (bombieriQuadraticTest g)).symm
      _ = bombieriFunctional
          (bombieriConjugateTest (bombieriQuadraticTest g)) := by
        rw [transposeLinearMap_bombieriQuadraticTest]
      _ = starRingEnd ℂ
          (bombieriFunctional (bombieriQuadraticTest g)) :=
        bombieriFunctional_conjugateTest _
  exact Complex.conj_eq_iff_im.mp hfixed.symm

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
