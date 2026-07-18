import ArithmeticHodge.Analysis.MultiplicativeWeilLogLatticeCovarianceStructural

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ContDiff Distributions

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-!
# Additivity and finite Gram expansion of the global Bombieri cross

The global cross symbol must be kept as one local-minus-prime object: neither
piece has the sign needed for global assembly.  We prove directly that this
complete symbol is additive in its second cell and use that fact to expand an
arbitrary finite cell sum into its diagonal terms and every unordered cross.

No positivity hypothesis enters the expansion.
-/

private theorem bombieriDirectedCorrelation_integrableOn'
    (f g : BombieriTest) (x : ℝ) :
    IntegrableOn
      (fun y : ℝ ↦ f (x * y) * starRingEnd ℂ (g y))
      (Set.Ioi 0) := by
  have hcont : Continuous
      (fun y : ℝ ↦ f (x * y) * starRingEnd ℂ (g y)) := by
    fun_prop
  have hgcompact : HasCompactSupport
      (fun y : ℝ ↦ starRingEnd ℂ (g y)) := by
    exact g.hasCompactSupport.comp_left (by simp)
  have hcompact : HasCompactSupport
      (fun y : ℝ ↦ f (x * y) * starRingEnd ℂ (g y)) := by
    simpa only [Pi.mul_apply] using
      hgcompact.mul_left (f := fun y : ℝ ↦ f (x * y))
  exact (hcont.integrable_of_hasCompactSupport hcompact).integrableOn

private theorem bombieriDirectedCorrelation_add_left
    (f g h : BombieriTest) (x : ℝ) :
    bombieriDirectedCorrelation (f + g) h x =
      bombieriDirectedCorrelation f h x +
        bombieriDirectedCorrelation g h x := by
  unfold bombieriDirectedCorrelation
  rw [← integral_add
    (bombieriDirectedCorrelation_integrableOn' f h x)
    (bombieriDirectedCorrelation_integrableOn' g h x)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y _hy
  simp only [TestFunction.coe_add, Pi.add_apply]
  ring

private theorem bombieriDirectedCorrelation_add_right
    (f g h : BombieriTest) (x : ℝ) :
    bombieriDirectedCorrelation f (g + h) x =
      bombieriDirectedCorrelation f g x +
        bombieriDirectedCorrelation f h x := by
  unfold bombieriDirectedCorrelation
  rw [← integral_add
    (bombieriDirectedCorrelation_integrableOn' f g x)
    (bombieriDirectedCorrelation_integrableOn' f h x)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y _hy
  simp only [TestFunction.coe_add, Pi.add_apply, map_add]
  ring

/-- The mixed quadratic test is additive in its second seed. -/
theorem bombieriQuadraticCrossTest_add_right
    (f g h : BombieriTest) :
    bombieriQuadraticCrossTest f (g + h) =
      bombieriQuadraticCrossTest f g +
        bombieriQuadraticCrossTest f h := by
  ext x
  simp only [bombieriQuadraticCrossTest_apply,
    bombieriDirectedCorrelation_add_left,
    bombieriDirectedCorrelation_add_right,
    TestFunction.coe_add, Pi.add_apply]
  abel

/-- Complex polarization of the prime cross remains additive; the real and
imaginary polarization coordinates are assembled before subtraction. -/
theorem bombieriPolarizedPrimeCross_add_right
    (f g h : BombieriTest) :
    bombieriPolarizedPrimeCross f (g + h) =
      bombieriPolarizedPrimeCross f g +
        bombieriPolarizedPrimeCross f h := by
  unfold bombieriPolarizedPrimeCross
  rw [bombieriQuadraticCrossTest_add_right, primeSum_add]
  have hI : Complex.I • (g + h) =
      Complex.I • g + Complex.I • h := by
    exact smul_add Complex.I g h
  rw [hI, bombieriQuadraticCrossTest_add_right, primeSum_add]
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, add_zero, sub_zero] <;>
    ring

/-- The complete local-minus-prime cross is additive in its second cell. -/
theorem bombieriTwoBlockGlobalCrossSymbol_add_right
    (f g h : BombieriTest) :
    bombieriTwoBlockGlobalCrossSymbol f (g + h) =
      bombieriTwoBlockGlobalCrossSymbol f g +
        bombieriTwoBlockGlobalCrossSymbol f h := by
  unfold bombieriTwoBlockGlobalCrossSymbol
  rw [map_add, bombieriPolarizedPrimeCross_add_right]
  ring

/-- The complete cross against the zero cell vanishes. -/
theorem bombieriTwoBlockGlobalCrossSymbol_zero_right
    (f : BombieriTest) :
    bombieriTwoBlockGlobalCrossSymbol f 0 = 0 := by
  have h := bombieriTwoBlockGlobalCrossSymbol_add_right f 0 0
  apply add_left_cancel
  simpa only [add_zero] using h.symm

/-- Additivity in the first cell follows from Hermitian symmetry without
separating the local and prime contributions. -/
theorem bombieriTwoBlockGlobalCrossSymbol_add_left
    (f g h : BombieriTest) :
    bombieriTwoBlockGlobalCrossSymbol (f + g) h =
      bombieriTwoBlockGlobalCrossSymbol f h +
        bombieriTwoBlockGlobalCrossSymbol g h := by
  calc
    bombieriTwoBlockGlobalCrossSymbol (f + g) h =
        starRingEnd ℂ
          (bombieriTwoBlockGlobalCrossSymbol h (f + g)) :=
      (bombieriTwoBlockGlobalCrossSymbol_conj_swap (f + g) h).symm
    _ = starRingEnd ℂ
        (bombieriTwoBlockGlobalCrossSymbol h f +
          bombieriTwoBlockGlobalCrossSymbol h g) := by
      rw [bombieriTwoBlockGlobalCrossSymbol_add_right]
    _ = starRingEnd ℂ (bombieriTwoBlockGlobalCrossSymbol h f) +
        starRingEnd ℂ (bombieriTwoBlockGlobalCrossSymbol h g) := by
      rw [map_add]
    _ = bombieriTwoBlockGlobalCrossSymbol f h +
        bombieriTwoBlockGlobalCrossSymbol g h := by
      have hfh := bombieriTwoBlockGlobalCrossSymbol_conj_swap f h
      have hgh := bombieriTwoBlockGlobalCrossSymbol_conj_swap g h
      simpa only [starRingEnd_apply] using congrArg₂ (· + ·) hfh hgh

/-- Cross against a finite sum is the sum of the complete crosses. -/
theorem bombieriTwoBlockGlobalCrossSymbol_list_sum_right
    (f : BombieriTest) (cells : List BombieriTest) :
    bombieriTwoBlockGlobalCrossSymbol f cells.sum =
      (cells.map (bombieriTwoBlockGlobalCrossSymbol f)).sum := by
  induction cells with
  | nil =>
      simpa using bombieriTwoBlockGlobalCrossSymbol_zero_right f
  | cons g tail ih =>
      simp only [List.sum_cons, List.map_cons]
      rw [bombieriTwoBlockGlobalCrossSymbol_add_right, ih]

/-- Sum of every unordered complete cross in a finite cell list. -/
def bombieriCellPairCrossSum : List BombieriTest → ℝ
  | [] => 0
  | f :: tail =>
      (tail.map (fun g ↦
        2 * (bombieriTwoBlockGlobalCrossSymbol f g).re)).sum +
        bombieriCellPairCrossSum tail

private theorem complex_re_list_sum (xs : List ℂ) :
    xs.sum.re = (xs.map Complex.re).sum := by
  induction xs with
  | nil => simp
  | cons z tail ih =>
      simp only [List.sum_cons, Complex.add_re, List.map_cons]
      rw [ih]

private theorem two_mul_list_sum (xs : List ℝ) :
    2 * xs.sum = (xs.map (fun x ↦ 2 * x)).sum := by
  induction xs with
  | nil => simp
  | cons x tail ih =>
      simp only [List.sum_cons, List.map_cons]
      rw [← ih]
      ring

/-- Exact finite Gram expansion of the Bombieri quadratic.  This is the
entry point for a signed near/far or Fourier assembly: every cross shown here
is the combined local-minus-prime symbol. -/
theorem bombieriFunctional_list_sum_re_eq_diagonal_add_pairs
    (cells : List BombieriTest) :
    (bombieriFunctional (bombieriQuadraticTest cells.sum)).re =
      (cells.map (fun f ↦
        (bombieriFunctional (bombieriQuadraticTest f)).re)).sum +
        bombieriCellPairCrossSum cells := by
  induction cells with
  | nil =>
      have hzero :
          bombieriFunctional (bombieriQuadraticTest (0 : BombieriTest)) = 0 := by
        simpa using
          bombieriFunctional_quadratic_smul (0 : ℂ) (0 : BombieriTest)
      simp only [List.sum_nil, hzero, Complex.zero_re, List.map_nil,
        bombieriCellPairCrossSum]
      ring
  | cons f tail ih =>
      rw [List.sum_cons]
      have hexpand := bombieriFunctional_twoBlock_re f tail.sum 1
      simp only [one_smul, Complex.normSq_one, one_mul] at hexpand
      rw [hexpand]
      simp only [List.map_cons, List.sum_cons, bombieriCellPairCrossSum]
      rw [ih, bombieriTwoBlockGlobalCrossSymbol_list_sum_right]
      rw [complex_re_list_sum]
      have htwo :
          2 * ((tail.map
            (bombieriTwoBlockGlobalCrossSymbol f)).map Complex.re).sum =
            (tail.map (fun g ↦
              2 * (bombieriTwoBlockGlobalCrossSymbol f g).re)).sum := by
        simpa only [List.map_map, Function.comp_apply] using
          two_mul_list_sum
            ((tail.map
              (bombieriTwoBlockGlobalCrossSymbol f)).map Complex.re)
      rw [htwo]
      ring

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
