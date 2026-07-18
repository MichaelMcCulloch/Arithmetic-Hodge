import ArithmeticHodge.Analysis.MultiplicativeWeilExplicitFormula
import ArithmeticHodge.Analysis.MultiplicativeWeilGlobalCrossAdditiveStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilQuadraticMellin

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ContDiff Distributions

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-!
# Zero-side expansion of the global cross under dilation

Complex polarization of Bombieri's unconditional zero formula identifies the
complete local-minus-prime cross with one oriented mixed Mellin product.  A
normalized dilation in the second variable then contributes the exact factor
`r ^ (1 / 2 - rho)`.  No critical-line or positivity hypothesis enters.
-/

/-- At an arbitrary complex Mellin argument, normalized dilation contributes
the exact complex power `r ^ (1 / 2 - s)`. -/
theorem mellin_normalizedDilation_cpow
    (r : ℝ) (hr : 0 < r) (g : BombieriTest) (s : ℂ) :
    mellin (normalizedDilation r hr g : ℝ → ℂ) s =
      (r : ℂ) ^ ((1 / 2 : ℂ) - s) * mellin (g : ℝ → ℂ) s := by
  have hscale :
      mellin (fun x : ℝ ↦ g (r * x)) s =
        (r : ℂ) ^ (-s) * mellin (g : ℝ → ℂ) s := by
    simpa only [smul_eq_mul] using
      (mellin_comp_mul_left (g : ℝ → ℂ) s hr)
  have hsqrt :
      (((Real.sqrt r : ℝ) : ℂ)) = (r : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hr.le]
    norm_num
  have hpow :
      (r : ℂ) ^ ((1 / 2 : ℂ) - s) =
        (r : ℂ) ^ (1 / 2 : ℂ) * (r : ℂ) ^ (-s) := by
    rw [show (1 / 2 : ℂ) - s = (1 / 2 : ℂ) + (-s) by ring,
      Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hr.ne')]
  change mellin
      (fun x : ℝ ↦ (((Real.sqrt r : ℝ) : ℂ)) • g (r * x)) s = _
  rw [mellin_const_smul]
  rw [hscale, hsqrt, hpow]
  simp only [smul_eq_mul]
  ring

private theorem mellin_add_bombieriTest
    (f g : BombieriTest) (s : ℂ) :
    mellin (f + g : BombieriTest) s =
      mellin (f : ℝ → ℂ) s + mellin (g : ℝ → ℂ) s := by
  change mellinLinearMap s (f + g) =
    mellinLinearMap s f + mellinLinearMap s g
  exact map_add (mellinLinearMap s) f g

private theorem mellin_smul_bombieriTest
    (c : ℂ) (g : BombieriTest) (s : ℂ) :
    mellin (c • g : BombieriTest) s =
      c * mellin (g : ℝ → ℂ) s := by
  change mellinLinearMap s (c • g) = c * mellinLinearMap s g
  simpa only [smul_eq_mul] using map_smul (mellinLinearMap s) c g

/-- The Mellin transform of a mixed quadratic test is the sum of its two
oriented spectral products. -/
theorem mellin_bombieriQuadraticCrossTest_eq_oriented
    (f g : BombieriTest) (s : ℂ) :
    mellin (bombieriQuadraticCrossTest f g : BombieriTest) s =
      mellin (f : ℝ → ℂ) s *
          coefficientConjugate (mellin (g : ℝ → ℂ)) (1 - s) +
        mellin (g : ℝ → ℂ) s *
          coefficientConjugate (mellin (f : ℝ → ℂ)) (1 - s) := by
  have hquadratic (h : BombieriTest) :
      mellin (bombieriQuadraticTest h : BombieriTest) s =
        spectralTerm (h : ℝ → ℂ) s := by
    exact (bombieriQuadraticTestData_hasMellin h s).2
  have hcross :
      mellin (bombieriQuadraticCrossTest f g : BombieriTest) s =
        spectralTerm (f + g : BombieriTest) s -
          spectralTerm (f : ℝ → ℂ) s -
            spectralTerm (g : ℝ → ℂ) s := by
    unfold bombieriQuadraticCrossTest
    change mellinLinearMap s
        (bombieriQuadraticTest (f + g) -
          bombieriQuadraticTest f - bombieriQuadraticTest g) = _
    rw [map_sub, map_sub]
    simp only [mellinLinearMap_apply]
    rw [hquadratic, hquadratic, hquadratic]
  rw [hcross]
  unfold spectralTerm coefficientConjugate
  simp only [map_sub, map_one]
  rw [mellin_add_bombieriTest f g s,
    mellin_add_bombieriTest f g (1 - starRingEnd ℂ s), map_add]
  ring

/-- The oriented zero-side product matching the conjugate-linear/linear
orientation of `bombieriTwoBlockGlobalCrossSymbol`. -/
def bombieriZeroCrossTerm (f g : BombieriTest) (s : ℂ) : ℂ :=
  mellin (g : ℝ → ℂ) s *
    coefficientConjugate (mellin (f : ℝ → ℂ)) (1 - s)

/-- Pointwise complex polarization isolates the oriented mixed product from
the two real quadratic-cross directions `1` and `I`. -/
theorem bombieriZeroCrossTerm_eq_polarization
    (f g : BombieriTest) (s : ℂ) :
    bombieriZeroCrossTerm f g s =
      (mellin (bombieriQuadraticCrossTest f g : BombieriTest) s -
          Complex.I * mellin
            (bombieriQuadraticCrossTest f (Complex.I • g) : BombieriTest) s) /
        2 := by
  rw [mellin_bombieriQuadraticCrossTest_eq_oriented,
    mellin_bombieriQuadraticCrossTest_eq_oriented]
  unfold bombieriZeroCrossTerm coefficientConjugate
  simp only [map_sub, map_one]
  rw [mellin_smul_bombieriTest Complex.I g s,
    mellin_smul_bombieriTest Complex.I g (1 - starRingEnd ℂ s), map_mul,
    Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The oriented mixed zero-side series is absolutely summable.  This follows
directly from the two quadratic-cross test series, so no zero-location
hypothesis is needed. -/
theorem ZetaZeroEnumeration.bombieriZeroCrossTerm_summable
    (zeros : ZetaZeroEnumeration) (f g : BombieriTest) :
    Summable (fun n ↦ bombieriZeroCrossTerm f g (zeros.zero n).val) := by
  have hreal := zeros.mellin_summable (bombieriQuadraticCrossTest f g)
  have himag := zeros.mellin_summable
    (bombieriQuadraticCrossTest f (Complex.I • g))
  have hpolarized := (hreal.sub (himag.mul_left Complex.I)).div_const 2
  exact hpolarized.congr fun n ↦
    (bombieriZeroCrossTerm_eq_polarization
      f g (zeros.zero n).val).symm

/-- Summing the pointwise polarization commutes with the absolutely
convergent zero series. -/
theorem tsum_bombieriZeroCrossTerm_eq_polarization
    (zeros : ZetaZeroEnumeration) (f g : BombieriTest) :
    ∑' n, bombieriZeroCrossTerm f g (zeros.zero n).val =
      ((∑' n, mellin (bombieriQuadraticCrossTest f g : BombieriTest)
          (zeros.zero n).val) -
        Complex.I *
          (∑' n, mellin
            (bombieriQuadraticCrossTest f (Complex.I • g) : BombieriTest)
              (zeros.zero n).val)) /
        2 := by
  have hreal :=
    (zeros.mellin_summable (bombieriQuadraticCrossTest f g)).hasSum
  have himag :=
    (zeros.mellin_summable
      (bombieriQuadraticCrossTest f (Complex.I • g))).hasSum
  have hpolarized := (hreal.sub (himag.mul_left Complex.I)).div_const 2
  apply HasSum.tsum_eq
  exact HasSum.congr_fun hpolarized fun n ↦
    (bombieriZeroCrossTerm_eq_polarization
      f g (zeros.zero n).val)

private theorem bombieriFunctional_quadraticCross_im_eq_zero
    (f g : BombieriTest) :
    (bombieriFunctional (bombieriQuadraticCrossTest f g)).im = 0 := by
  unfold bombieriQuadraticCrossTest
  simp only [map_sub, Complex.sub_im,
    bombieriFunctional_bombieriQuadraticTest_im_eq_zero]
  ring

/-- The complete global cross is exactly the complex polarization of the two
real mixed quadratic-functional directions. -/
theorem bombieriTwoBlockGlobalCrossSymbol_eq_functional_polarization
    (f g : BombieriTest) :
    bombieriTwoBlockGlobalCrossSymbol f g =
      (bombieriFunctional (bombieriQuadraticCrossTest f g) -
        Complex.I * bombieriFunctional
          (bombieriQuadraticCrossTest f (Complex.I • g))) /
        2 := by
  have hreal := bombieriFunctional_quadraticCross_twoBlock_re
    f g (1 : ℂ)
  simp only [one_smul, one_mul] at hreal
  have himag := bombieriFunctional_quadraticCross_twoBlock_re
    f g Complex.I
  have hfirstIm := bombieriFunctional_quadraticCross_im_eq_zero f g
  have hsecondIm := bombieriFunctional_quadraticCross_im_eq_zero
    f (Complex.I • g)
  apply (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).2
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.sub_re, Complex.I_re, Complex.I_im,
      Complex.re_ofNat, Complex.im_ofNat, zero_mul, mul_zero, sub_zero]
    linarith
  · simp only [Complex.mul_im, Complex.sub_im, Complex.I_re, Complex.I_im,
      Complex.re_ofNat, Complex.im_ofNat, zero_mul, mul_zero,
      one_mul]
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul,
      one_mul] at himag
    linarith

/-- Any Bombieri zero-sum formula transports complex polarization to the
single oriented mixed zero series. -/
theorem bombieriTwoBlockGlobalCrossSymbol_eq_zeroSum_of_formula
    (zeros : ZetaZeroEnumeration) (hformula : BombieriZeroSumFormula zeros)
    (f g : BombieriTest) :
    bombieriTwoBlockGlobalCrossSymbol f g =
      ∑' n, bombieriZeroCrossTerm f g (zeros.zero n).val := by
  rw [bombieriTwoBlockGlobalCrossSymbol_eq_functional_polarization]
  rw [hformula (bombieriQuadraticCrossTest f g),
    hformula (bombieriQuadraticCrossTest f (Complex.I • g))]
  exact (tsum_bombieriZeroCrossTerm_eq_polarization zeros f g).symm

/-- Unconditional zero-side expansion of the complete global Bombieri cross.
The only analytic input is the already-proved Bombieri zero-sum formula. -/
theorem bombieriTwoBlockGlobalCrossSymbol_eq_zeroSum
    (zeros : ZetaZeroEnumeration) (f g : BombieriTest) :
    bombieriTwoBlockGlobalCrossSymbol f g =
      ∑' n, bombieriZeroCrossTerm f g (zeros.zero n).val :=
  bombieriTwoBlockGlobalCrossSymbol_eq_zeroSum_of_formula
    zeros (bombieriZeroSumFormula zeros) f g

/-- Exact zero-side expansion after normalized dilation of the second block.
Every zero `rho` acquires the structural factor `r ^ (1 / 2 - rho)`.  This is
unconditional and in particular assumes neither RH nor positivity. -/
theorem bombieriTwoBlockGlobalCrossSymbol_normalizedDilation_eq_zeroSum
    (zeros : ZetaZeroEnumeration) (f g : BombieriTest)
    (r : ℝ) (hr : 0 < r) :
    bombieriTwoBlockGlobalCrossSymbol f (normalizedDilation r hr g) =
      ∑' n,
        (r : ℂ) ^ ((1 / 2 : ℂ) - (zeros.zero n).val) *
          mellin (g : ℝ → ℂ) (zeros.zero n).val *
            coefficientConjugate (mellin (f : ℝ → ℂ))
              (1 - (zeros.zero n).val) := by
  rw [bombieriTwoBlockGlobalCrossSymbol_eq_zeroSum]
  apply tsum_congr
  intro n
  unfold bombieriZeroCrossTerm
  rw [mellin_normalizedDilation_cpow]

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
