import ArithmeticHodge.Analysis.MultiplicativeWeilGlobalCrossSesquilinearStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilQuadraticReality

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-!
# Exact real--imaginary splitting of the Bombieri quadratic

The autocorrelation test itself has an additional imaginary antisymmetric
cross term.  The concrete Bombieri functional kills that term exactly.  The
reason is structural: coefficient conjugation preserves the quadratic value,
and the complete local-minus-prime Hermitian cross of two conjugation-fixed
Bombieri tests is real.
-/

/-- Multiplicative autocorrelation commutes with coefficient conjugation. -/
theorem bombieriQuadraticTest_conjugateTest
    (g : BombieriTest) :
    bombieriQuadraticTest (bombieriConjugateTest g) =
      bombieriConjugateTest (bombieriQuadraticTest g) := by
  ext x
  simp only [bombieriQuadraticTest_apply, bombieriConjugateTest_apply]
  unfold autocorrelation
  calc
    (∫ y : ℝ in Set.Ioi 0,
        starRingEnd ℂ (g (x * y)) *
          starRingEnd ℂ (starRingEnd ℂ (g y))) =
      ∫ y : ℝ in Set.Ioi 0,
        starRingEnd ℂ
          (g (x * y) * starRingEnd ℂ (g y)) := by
            apply integral_congr_ae
            filter_upwards [] with y
            simp only [map_mul, starRingEnd_self_apply]
    _ = starRingEnd ℂ
        (∫ y : ℝ in Set.Ioi 0,
          g (x * y) * starRingEnd ℂ (g y)) := integral_conj

/-- Consequently the complete Bombieri quadratic value is invariant under
coefficient conjugation. -/
theorem bombieriFunctional_quadratic_conjugateTest
    (g : BombieriTest) :
    bombieriFunctional
        (bombieriQuadraticTest (bombieriConjugateTest g)) =
      bombieriFunctional (bombieriQuadraticTest g) := by
  rw [bombieriQuadraticTest_conjugateTest,
    bombieriFunctional_conjugateTest]
  apply Complex.ext
  · simp
  · rw [starRingEnd_apply]
    simp only [Complex.star_def, Complex.conj_im,
      bombieriFunctional_bombieriQuadraticTest_im_eq_zero, neg_zero]

/-- The complete local-minus-prime Hermitian cross of two real-valued
Bombieri tests is real.  Here real-valuedness is expressed intrinsically as
being fixed by coefficient conjugation. -/
theorem bombieriTwoBlockGlobalCrossSymbol_im_eq_zero_of_conjugate_fixed
    (f g : BombieriTest)
    (hf : bombieriConjugateTest f = f)
    (hg : bombieriConjugateTest g = g) :
    (bombieriTwoBlockGlobalCrossSymbol f g).im = 0 := by
  have harg :
      bombieriConjugateTest (f + Complex.I • g) =
        f + (-Complex.I) • g := by
    rw [bombieriConjugateTest_add, bombieriConjugateTest_smul, hf, hg]
    simp
  have hconj := bombieriFunctional_quadratic_conjugateTest
    (f + Complex.I • g)
  rw [harg] at hconj
  have hre := congrArg Complex.re hconj
  rw [bombieriFunctional_twoBlock_re f g (-Complex.I),
    bombieriFunctional_twoBlock_re f g Complex.I] at hre
  norm_num [Complex.normSq_apply, Complex.mul_re] at hre
  linarith

/-- Equivalent fixed-point form of the preceding reality statement. -/
theorem bombieriTwoBlockGlobalCrossSymbol_conj_eq_self_of_conjugate_fixed
    (f g : BombieriTest)
    (hf : bombieriConjugateTest f = f)
    (hg : bombieriConjugateTest g = g) :
    starRingEnd ℂ (bombieriTwoBlockGlobalCrossSymbol f g) =
      bombieriTwoBlockGlobalCrossSymbol f g := by
  apply Complex.ext
  · simp
  · rw [starRingEnd_apply]
    simp only [Complex.star_def, Complex.conj_im,
      bombieriTwoBlockGlobalCrossSymbol_im_eq_zero_of_conjugate_fixed
        f g hf hg, neg_zero]

/-- Before applying the functional, the exact obstruction to literal
real--imaginary splitting is one antisymmetric mixed autocorrelation. -/
theorem bombieriQuadraticTest_eq_realPart_add_imagPart_add_skewCross
    (g : BombieriTest) :
    bombieriQuadraticTest g =
      bombieriQuadraticTest (bombieriRealPartTest g) +
        bombieriQuadraticTest (bombieriImagPartTest g) +
          bombieriQuadraticCrossTest
            (bombieriRealPartTest g)
            (Complex.I • bombieriImagPartTest g) := by
  calc
    bombieriQuadraticTest g =
        bombieriQuadraticTest
          (bombieriRealPartTest g +
            Complex.I • bombieriImagPartTest g) :=
      congrArg bombieriQuadraticTest
        (bombieriRealPartTest_add_I_smul_imagPartTest g).symm
    _ = _ := by
      rw [bombieriQuadraticTest_add_eq_diagonal_add_cross,
        bombieriQuadraticTest_smul]
      norm_num [Complex.normSq_apply]

/-- Literal splitting already at the autocorrelation-test level holds exactly
when the antisymmetric real--imaginary cross test vanishes. -/
theorem bombieriQuadraticTest_eq_realPart_add_imagPart_iff
    (g : BombieriTest) :
    bombieriQuadraticTest g =
        bombieriQuadraticTest (bombieriRealPartTest g) +
          bombieriQuadraticTest (bombieriImagPartTest g) ↔
      bombieriQuadraticCrossTest
        (bombieriRealPartTest g)
        (Complex.I • bombieriImagPartTest g) = 0 := by
  rw [bombieriQuadraticTest_eq_realPart_add_imagPart_add_skewCross]
  constructor
  · intro h
    apply add_left_cancel
      (a := bombieriQuadraticTest (bombieriRealPartTest g) +
        bombieriQuadraticTest (bombieriImagPartTest g))
    simpa only [add_zero] using h
  · intro h
    rw [h, add_zero]

/-- The concrete Bombieri quadratic functional splits exactly into the
quadratics of the pointwise real and imaginary parts. -/
theorem bombieriFunctional_quadratic_eq_realPart_add_imagPart
    (g : BombieriTest) :
    bombieriFunctional (bombieriQuadraticTest g) =
      bombieriFunctional
          (bombieriQuadraticTest (bombieriRealPartTest g)) +
        bombieriFunctional
          (bombieriQuadraticTest (bombieriImagPartTest g)) := by
  have hcross :=
    bombieriTwoBlockGlobalCrossSymbol_im_eq_zero_of_conjugate_fixed
      (bombieriRealPartTest g) (bombieriImagPartTest g)
      (bombieriConjugateTest_realPartTest g)
      (bombieriConjugateTest_imagPartTest g)
  have hre := bombieriFunctional_twoBlock_re
    (bombieriRealPartTest g) (bombieriImagPartTest g) Complex.I
  rw [bombieriRealPartTest_add_I_smul_imagPartTest] at hre
  norm_num [Complex.normSq_apply, Complex.mul_re, hcross] at hre
  apply Complex.ext
  · simpa only [Complex.add_re] using hre
  · simp only [Complex.add_im,
      bombieriFunctional_bombieriQuadraticTest_im_eq_zero, add_zero]

/-- The antisymmetric real--imaginary autocorrelation can be nontrivial as a
test, but it lies exactly in the kernel of the concrete Bombieri functional. -/
theorem bombieriFunctional_realPart_imagPart_skewCross_eq_zero
    (g : BombieriTest) :
    bombieriFunctional
        (bombieriQuadraticCrossTest
          (bombieriRealPartTest g)
          (Complex.I • bombieriImagPartTest g)) = 0 := by
  have htest := congrArg bombieriFunctional
    (bombieriQuadraticTest_eq_realPart_add_imagPart_add_skewCross g)
  simp only [map_add] at htest
  rw [bombieriFunctional_quadratic_eq_realPart_add_imagPart] at htest
  apply add_left_cancel
    (a := bombieriFunctional
        (bombieriQuadraticTest (bombieriRealPartTest g)) +
      bombieriFunctional
        (bombieriQuadraticTest (bombieriImagPartTest g)))
  simpa only [add_zero] using htest.symm

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
