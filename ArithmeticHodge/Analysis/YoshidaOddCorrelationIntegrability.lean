import ArithmeticHodge.Analysis.YoshidaRenormalizedGeometricKernel
import ArithmeticHodge.Analysis.YoshidaClippedMomentBridge
import Mathlib.Analysis.Complex.RemovableSingularity

set_option autoImplicit false

open Complex Filter MeasureTheory Real Set Topology
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaOddCorrelationIntegrability

noncomputable section

open ArithmeticHodge.Analysis.YoshidaOddGramPrefix
open ArithmeticHodge.Analysis.YoshidaClippedMomentBridge
open ArithmeticHodge.Analysis.YoshidaRenormalizedGeometricKernel

/-!
# Removable integrability for Yoshida odd correlations

Entire divided-slope surrogates remove the apparent singularities in the odd
geometric kernel and its reference subtraction.  The explicit diagonal and
off-diagonal clipped correlations are then factored as `C0 + u * D u` with
continuous `D`.  This discharges the dominated series/integral interchange
and stable-kernel integrability required by the renormalized identity for
every nonzero odd mode pair.
-/

theorem yoshidaKappa_ne_zero {n : ℕ} (hn : n ≠ 0) :
    yoshidaKappa n ≠ 0 := by
  rw [yoshidaKappa]
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      (Nat.cast_ne_zero.mpr hn))
    yoshidaLength_pos.ne'

def offdiagRemovableD (n m : ℕ) (u : ℝ) : ℝ :=
  (2 * (-1 : ℝ) ^ (n + m) / yoshidaLength) *
    (yoshidaKappa n * yoshidaKappa m) *
    (Real.sinc (yoshidaKappa m * u) -
      Real.sinc (yoshidaKappa n * u)) /
    (yoshidaKappa n ^ 2 - yoshidaKappa m ^ 2)

theorem continuous_offdiagRemovableD (n m : ℕ) :
    Continuous (offdiagRemovableD n m) := by
  unfold offdiagRemovableD
  fun_prop

theorem clippedOddCorrelation_offdiag_removable
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (hnm : n ≠ m) (u : ℝ) :
    clippedOddCorrelation yoshidaHalfLength n m u =
      0 + u * offdiagRemovableD n m u := by
  rw [clippedOddCorrelation_half_offdiag hn hm hnm]
  by_cases hu : u = 0
  · subst u
    simp
  · have hkn : yoshidaKappa n ≠ 0 := yoshidaKappa_ne_zero hn
    have hkm : yoshidaKappa m ≠ 0 := yoshidaKappa_ne_zero hm
    rw [offdiagRemovableD,
      Real.sinc_of_ne_zero (mul_ne_zero hkm hu),
      Real.sinc_of_ne_zero (mul_ne_zero hkn hu)]
    field_simp [hu, hkn, hkm]
    ring

theorem continuous_clippedOddCorrelation_offdiag
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (hnm : n ≠ m) :
    Continuous (clippedOddCorrelation yoshidaHalfLength n m) := by
  rw [show clippedOddCorrelation yoshidaHalfLength n m =
      fun u : ℝ ↦ 0 + u * offdiagRemovableD n m u by
    funext u
    exact clippedOddCorrelation_offdiag_removable hn hm hnm u]
  exact continuous_const.add (continuous_id.mul (continuous_offdiagRemovableD n m))

def cosineSlope (n : ℕ) : ℝ → ℝ :=
  dslope (fun u : ℝ ↦ Real.cos (yoshidaKappa n * u)) 0

theorem continuous_cosineSlope (n : ℕ) : Continuous (cosineSlope n) := by
  rw [continuous_iff_continuousAt]
  intro u
  rw [cosineSlope]
  by_cases hu : u = 0
  · subst u
    rw [continuousAt_dslope_same]
    fun_prop
  · rw [continuousAt_dslope_of_ne hu]
    fun_prop

def diagonalRemovableD (n : ℕ) (u : ℝ) : ℝ :=
  cosineSlope n u +
    (Real.sinc (yoshidaKappa n * u) -
      Real.cos (yoshidaKappa n * u)) / yoshidaLength

theorem continuous_diagonalRemovableD (n : ℕ) :
    Continuous (diagonalRemovableD n) := by
  unfold diagonalRemovableD
  exact (continuous_cosineSlope n).add (by fun_prop)

theorem clippedOddCorrelation_diag_removable
    {n : ℕ} (hn : n ≠ 0) (u : ℝ) :
    clippedOddCorrelation yoshidaHalfLength n n u =
      1 + u * diagonalRemovableD n u := by
  rw [clippedOddCorrelation_half_diag hn]
  by_cases hu : u = 0
  · subst u
    simp [yoshidaLength_pos.ne']
  · have hk : yoshidaKappa n ≠ 0 := yoshidaKappa_ne_zero hn
    rw [diagonalRemovableD, cosineSlope, dslope_of_ne _ hu,
      Real.sinc_of_ne_zero (mul_ne_zero hk hu)]
    simp [slope]
    field_simp [hu, hk, yoshidaLength_pos.ne']
    ring

theorem continuous_clippedOddCorrelation_diag
    {n : ℕ} (hn : n ≠ 0) :
    Continuous (clippedOddCorrelation yoshidaHalfLength n n) := by
  rw [show clippedOddCorrelation yoshidaHalfLength n n =
      fun u : ℝ ↦ 1 + u * diagonalRemovableD n u by
    funext u
    exact clippedOddCorrelation_diag_removable hn u]
  exact continuous_const.add (continuous_id.mul (continuous_diagonalRemovableD n))

private theorem complex_dslope_zero_differentiable
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (dslope f 0) := by
  intro z
  have hOn : DifferentiableOn ℂ (dslope f 0) Set.univ :=
    (Complex.differentiableOn_dslope (s := Set.univ) (by simp)).2
      hf.differentiableOn
  exact hOn.differentiableAt (by simp)

def complexExpTwoCore (z : ℂ) : ℂ := Complex.exp (2 * z) - 1

def complexExpThreeHalfCore (z : ℂ) : ℂ :=
  Complex.exp ((3 / 2 : ℂ) * z) - 1

def complexReferenceCore (z : ℂ) : ℂ :=
  Complex.exp (2 * z) - 1 - 2 * z

theorem complexExpTwoCore_differentiable :
    Differentiable ℂ complexExpTwoCore := by
  unfold complexExpTwoCore
  fun_prop

theorem complexExpThreeHalfCore_differentiable :
    Differentiable ℂ complexExpThreeHalfCore := by
  unfold complexExpThreeHalfCore
  fun_prop

theorem complexReferenceCore_differentiable :
    Differentiable ℂ complexReferenceCore := by
  unfold complexReferenceCore
  fun_prop

theorem complexExpTwoCore_deriv_zero :
    deriv complexExpTwoCore 0 = 2 := by
  have hlin : HasDerivAt (fun z : ℂ ↦ 2 * z) 2 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_mul 2
  have h := hlin.cexp.sub_const 1
  change deriv (fun z : ℂ ↦ Complex.exp (2 * z) - 1) 0 = 2
  (convert h.deriv using 1; norm_num)

theorem complexReferenceCore_deriv_zero :
    deriv complexReferenceCore 0 = 0 := by
  have hlin : HasDerivAt (fun z : ℂ ↦ 2 * z) 2 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_mul 2
  have hexp := hlin.cexp
  have h := (hexp.sub_const 1).sub hlin
  change deriv (fun z : ℂ ↦ Complex.exp (2 * z) - 1 - 2 * z) 0 = 0
  (convert h.deriv using 1; norm_num)

def complexExpTwoSlope : ℂ → ℂ := dslope complexExpTwoCore 0

def complexExpThreeHalfSlope : ℂ → ℂ :=
  dslope complexExpThreeHalfCore 0

def complexReferenceSecondSlope : ℂ → ℂ :=
  dslope (dslope complexReferenceCore 0) 0

theorem complexExpTwoSlope_differentiable :
    Differentiable ℂ complexExpTwoSlope :=
  complex_dslope_zero_differentiable complexExpTwoCore_differentiable

theorem complexExpThreeHalfSlope_differentiable :
    Differentiable ℂ complexExpThreeHalfSlope :=
  complex_dslope_zero_differentiable complexExpThreeHalfCore_differentiable

theorem complexReferenceSecondSlope_differentiable :
    Differentiable ℂ complexReferenceSecondSlope :=
  complex_dslope_zero_differentiable
    (complex_dslope_zero_differentiable complexReferenceCore_differentiable)

theorem complexExpTwoCore_ofReal (u : ℝ) :
    complexExpTwoCore (u : ℂ) = (Real.exp (2 * u) - 1 : ℝ) := by
  rw [complexExpTwoCore]
  have harg : (2 : ℂ) * (u : ℂ) = ((2 * u : ℝ) : ℂ) := by
    push_cast
    ring
  rw [harg, ← Complex.ofReal_exp]
  push_cast
  ring

theorem complexExpThreeHalfCore_ofReal (u : ℝ) :
    complexExpThreeHalfCore (u : ℂ) =
      (Real.exp ((3 / 2 : ℝ) * u) - 1 : ℝ) := by
  rw [complexExpThreeHalfCore]
  have harg : (3 / 2 : ℂ) * (u : ℂ) =
      (((3 / 2 : ℝ) * u : ℝ) : ℂ) := by
    push_cast
    ring
  rw [harg, ← Complex.ofReal_exp]
  push_cast
  ring

theorem complexReferenceCore_ofReal (u : ℝ) :
    complexReferenceCore (u : ℂ) =
      (Real.exp (2 * u) - 1 - 2 * u : ℝ) := by
  rw [complexReferenceCore]
  have harg : (2 : ℂ) * (u : ℂ) = ((2 * u : ℝ) : ℂ) := by
    push_cast
    ring
  rw [harg, ← Complex.ofReal_exp]
  push_cast
  ring

theorem complexExpTwoSlope_ofReal {u : ℝ} (hu : u ≠ 0) :
    complexExpTwoSlope (u : ℂ) =
      ((Real.exp (2 * u) - 1) / u : ℝ) := by
  rw [complexExpTwoSlope, dslope_of_ne _ (by exact_mod_cast hu)]
  simp only [slope, sub_zero, smul_eq_mul]
  rw [complexExpTwoCore_ofReal]
  simp [complexExpTwoCore]
  rw [div_eq_mul_inv]
  ring

theorem complexExpThreeHalfSlope_ofReal {u : ℝ} (hu : u ≠ 0) :
    complexExpThreeHalfSlope (u : ℂ) =
      ((Real.exp ((3 / 2 : ℝ) * u) - 1) / u : ℝ) := by
  rw [complexExpThreeHalfSlope, dslope_of_ne _ (by exact_mod_cast hu)]
  simp only [slope, sub_zero, smul_eq_mul]
  rw [complexExpThreeHalfCore_ofReal]
  simp [complexExpThreeHalfCore]
  rw [div_eq_mul_inv]
  ring

theorem complexReferenceSecondSlope_ofReal {u : ℝ} (hu : u ≠ 0) :
    complexReferenceSecondSlope (u : ℂ) =
      ((Real.exp (2 * u) - 1 - 2 * u) / u ^ 2 : ℝ) := by
  rw [complexReferenceSecondSlope,
    dslope_of_ne _ (by exact_mod_cast hu)]
  simp only [slope, sub_zero, smul_eq_mul]
  rw [dslope_same, complexReferenceCore_deriv_zero]
  rw [dslope_of_ne _ (by exact_mod_cast hu)]
  simp only [slope, sub_zero, smul_eq_mul]
  rw [complexReferenceCore_ofReal]
  simp [complexReferenceCore]
  field_simp [hu]

theorem complexExpTwoSlope_ofReal_ne (u : ℝ) :
    complexExpTwoSlope (u : ℂ) ≠ 0 := by
  by_cases hu : u = 0
  · subst u
    change complexExpTwoSlope (0 : ℂ) ≠ 0
    rw [complexExpTwoSlope, dslope_same, complexExpTwoCore_deriv_zero]
    norm_num
  · rw [complexExpTwoSlope_ofReal hu]
    have hnum : Real.exp (2 * u) - 1 ≠ 0 := by
      intro h
      have heq : Real.exp (2 * u) = Real.exp 0 := by
        simpa only [sub_eq_zero, Real.exp_zero] using h
      have : 2 * u = 0 := Real.exp_injective heq
      exact hu (by linarith)
    exact_mod_cast div_ne_zero hnum hu

theorem oddKernel_eq_alt {u : ℝ} (hu : u ≠ 0) :
    oddKernel u =
      2 * Real.exp ((3 / 2 : ℝ) * u) / (Real.exp (2 * u) - 1) := by
  have hden1 : Real.exp u - Real.exp (-u) ≠ 0 := by
    intro h
    have heq : Real.exp u = Real.exp (-u) := sub_eq_zero.mp h
    exact hu (by linarith [Real.exp_injective heq])
  have hden2 : Real.exp (2 * u) - 1 ≠ 0 := by
    intro h
    have heq : Real.exp (2 * u) = Real.exp 0 := by
      simpa only [sub_eq_zero, Real.exp_zero] using h
    exact hu (by linarith [Real.exp_injective heq])
  have hhalf : Real.exp ((3 / 2 : ℝ) * u) =
      Real.exp (u / 2) * Real.exp u := by
    rw [← Real.exp_add]
    congr 1
    ring
  have htwo : Real.exp (2 * u) = Real.exp u * Real.exp u := by
    rw [show 2 * u = u + u by ring, Real.exp_add]
  have hinv : Real.exp u * Real.exp (-u) = 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [oddKernel]
  field_simp [hden1, hden2]
  rw [show u * 3 / 2 = (3 / 2 : ℝ) * u by ring, hhalf, htwo]
  rw [← hinv]
  ring

theorem referenceKernel_eq_alt {u : ℝ} (hu : u ≠ 0) :
    referenceKernel u = 2 / (Real.exp (2 * u) - 1) := by
  have hden1 : 1 - Real.exp (-2 * u) ≠ 0 := by
    intro h
    have heq : Real.exp (-2 * u) = Real.exp 0 := by
      simpa only [sub_eq_zero, Real.exp_zero] using (sub_eq_zero.mp h).symm
    exact hu (by linarith [Real.exp_injective heq])
  have hden2 : Real.exp (2 * u) - 1 ≠ 0 := by
    intro h
    have heq : Real.exp (2 * u) = Real.exp 0 := by
      simpa only [sub_eq_zero, Real.exp_zero] using h
    exact hu (by linarith [Real.exp_injective heq])
  have hinv : Real.exp (-2 * u) * Real.exp (2 * u) = 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [referenceKernel]
  apply (div_eq_div_iff hden1 hden2).2
  nlinarith

private theorem ofReal_div_re (a b : ℝ) :
    (((a : ℂ) / (b : ℂ)).re) = a / b := by
  rw [← Complex.ofReal_div]
  simp

def uOddKernelSurrogate (u : ℝ) : ℝ :=
  (((2 * Real.exp ((3 / 2 : ℝ) * u) : ℝ) : ℂ) /
    complexExpTwoSlope (u : ℂ)).re

def kernelDifferenceSurrogate (u : ℝ) : ℝ :=
  (2 * complexExpThreeHalfSlope (u : ℂ) /
    complexExpTwoSlope (u : ℂ)).re

def referenceRegularizedSurrogate (u : ℝ) : ℝ :=
  (complexReferenceSecondSlope (u : ℂ) /
    complexExpTwoSlope (u : ℂ)).re

theorem continuous_uOddKernelSurrogate : Continuous uOddKernelSurrogate := by
  have hnum : Continuous (fun u : ℝ ↦
      ((2 * Real.exp ((3 / 2 : ℝ) * u) : ℝ) : ℂ)) := by
    fun_prop
  have hden : Continuous (fun u : ℝ ↦ complexExpTwoSlope (u : ℂ)) :=
    complexExpTwoSlope_differentiable.continuous.comp Complex.continuous_ofReal
  have hquot : Continuous (fun u : ℝ ↦
      ((2 * Real.exp ((3 / 2 : ℝ) * u) : ℝ) : ℂ) /
        complexExpTwoSlope (u : ℂ)) :=
    hnum.div hden complexExpTwoSlope_ofReal_ne
  exact Complex.continuous_re.comp hquot

theorem continuous_kernelDifferenceSurrogate :
    Continuous kernelDifferenceSurrogate := by
  have hnum : Continuous (fun u : ℝ ↦
      2 * complexExpThreeHalfSlope (u : ℂ)) := by
    exact continuous_const.mul
      (complexExpThreeHalfSlope_differentiable.continuous.comp
        Complex.continuous_ofReal)
  have hden : Continuous (fun u : ℝ ↦ complexExpTwoSlope (u : ℂ)) :=
    complexExpTwoSlope_differentiable.continuous.comp Complex.continuous_ofReal
  have hquot : Continuous (fun u : ℝ ↦
      2 * complexExpThreeHalfSlope (u : ℂ) /
        complexExpTwoSlope (u : ℂ)) :=
    hnum.div hden complexExpTwoSlope_ofReal_ne
  exact Complex.continuous_re.comp hquot

theorem continuous_referenceRegularizedSurrogate :
    Continuous referenceRegularizedSurrogate := by
  have hnum : Continuous (fun u : ℝ ↦
      complexReferenceSecondSlope (u : ℂ)) :=
    complexReferenceSecondSlope_differentiable.continuous.comp
      Complex.continuous_ofReal
  have hden : Continuous (fun u : ℝ ↦ complexExpTwoSlope (u : ℂ)) :=
    complexExpTwoSlope_differentiable.continuous.comp Complex.continuous_ofReal
  have hquot : Continuous (fun u : ℝ ↦
      complexReferenceSecondSlope (u : ℂ) /
        complexExpTwoSlope (u : ℂ)) :=
    hnum.div hden complexExpTwoSlope_ofReal_ne
  exact Complex.continuous_re.comp hquot

theorem exp_two_sub_one_ne {u : ℝ} (hu : u ≠ 0) :
    Real.exp (2 * u) - 1 ≠ 0 := by
  intro h
  have heq : Real.exp (2 * u) = Real.exp 0 := by
    simpa only [sub_eq_zero, Real.exp_zero] using h
  exact hu (by linarith [Real.exp_injective heq])

theorem uOddKernelSurrogate_eq {u : ℝ} (hu : u ≠ 0) :
    uOddKernelSurrogate u = u * oddKernel u := by
  rw [uOddKernelSurrogate, complexExpTwoSlope_ofReal hu,
    ofReal_div_re, oddKernel_eq_alt hu]
  field_simp [hu, exp_two_sub_one_ne hu]

theorem kernelDifferenceSurrogate_eq {u : ℝ} (hu : u ≠ 0) :
    kernelDifferenceSurrogate u = oddKernel u - referenceKernel u := by
  rw [kernelDifferenceSurrogate,
    complexExpThreeHalfSlope_ofReal hu, complexExpTwoSlope_ofReal hu]
  rw [show (2 : ℂ) *
      (((Real.exp ((3 / 2 : ℝ) * u) - 1) / u : ℝ) : ℂ) =
      (((2 * ((Real.exp ((3 / 2 : ℝ) * u) - 1) / u) : ℝ) : ℂ)) by
    push_cast
    ring]
  rw [ofReal_div_re, oddKernel_eq_alt hu, referenceKernel_eq_alt hu]
  field_simp [hu, exp_two_sub_one_ne hu]

theorem referenceRegularizedSurrogate_eq {u : ℝ} (hu : u ≠ 0) :
    referenceRegularizedSurrogate u = referenceRegularized u := by
  rw [referenceRegularizedSurrogate,
    complexReferenceSecondSlope_ofReal hu, complexExpTwoSlope_ofReal hu,
    ofReal_div_re, referenceRegularized, referenceKernel_eq_alt hu]
  field_simp [hu, exp_two_sub_one_ne hu]

private theorem ae_ne_zero : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := by
  simp [ae_iff, measure_singleton]

theorem referenceRegularized_intervalIntegrable (L : ℝ) :
    IntervalIntegrable referenceRegularized volume 0 L := by
  have hsur : IntervalIntegrable referenceRegularizedSurrogate volume 0 L :=
    Continuous.intervalIntegrable continuous_referenceRegularizedSurrogate 0 L
  apply hsur.congr_ae
  refine ae_restrict_of_ae ?_
  filter_upwards [ae_ne_zero] with u hu
  exact referenceRegularizedSurrogate_eq hu

theorem kernelDifference_intervalIntegrable (L : ℝ) :
    IntervalIntegrable (fun u : ℝ ↦ oddKernel u - referenceKernel u)
      volume 0 L := by
  have hsur : IntervalIntegrable kernelDifferenceSurrogate volume 0 L :=
    Continuous.intervalIntegrable continuous_kernelDifferenceSurrogate 0 L
  apply hsur.congr_ae
  refine ae_restrict_of_ae ?_
  filter_upwards [ae_ne_zero] with u hu
  exact kernelDifferenceSurrogate_eq hu

theorem oddKernel_mul_u_intervalIntegrable
    {D : ℝ → ℝ} (hD : Continuous D) (L : ℝ) :
    IntervalIntegrable (fun u : ℝ ↦ oddKernel u * (u * D u)) volume 0 L := by
  have hsur : IntervalIntegrable
      (fun u : ℝ ↦ uOddKernelSurrogate u * D u) volume 0 L :=
    Continuous.intervalIntegrable (continuous_uOddKernelSurrogate.mul hD) 0 L
  apply hsur.congr_ae
  refine ae_restrict_of_ae ?_
  filter_upwards [ae_ne_zero] with u hu
  rw [uOddKernelSurrogate_eq hu]
  ring

theorem oddKernel_mul_u_abs_intervalIntegrable
    {D : ℝ → ℝ} (hD : Continuous D) (L : ℝ) :
    IntervalIntegrable (fun u : ℝ ↦ oddKernel u * (u * |D u|)) volume 0 L := by
  exact oddKernel_mul_u_intervalIntegrable hD.abs L

theorem removableMajorantLimit_intervalIntegrable
    {D : ℝ → ℝ} (hD : Continuous D) (C0 L : ℝ) :
    IntervalIntegrable (removableMajorantLimit C0 D) volume 0 L := by
  rw [show removableMajorantLimit C0 D = fun u : ℝ ↦
      oddKernel u * (u * |D u|) +
        |C0| * (oddKernel u - referenceKernel u) by rfl]
  exact (oddKernel_mul_u_abs_intervalIntegrable hD L).add
    ((kernelDifference_intervalIntegrable L).const_mul |C0|)

theorem stableGeometricIntegrand_intervalIntegrable_of_removable
    {C D : ℝ → ℝ} (hD : Continuous D) (C0 L : ℝ)
    (hrem : ∀ u : ℝ, C u = C0 + u * D u) :
    IntervalIntegrable (stableGeometricIntegrand C0 C) volume 0 L := by
  have hmain := oddKernel_mul_u_intervalIntegrable hD L
  have hcorr := (kernelDifference_intervalIntegrable L).sub
    (referenceRegularized_intervalIntegrable L)
  have hsum := hmain.add (hcorr.const_mul C0)
  apply hsum.congr
  intro u hu
  unfold stableGeometricIntegrand referenceRegularized
  rw [hrem u]
  ring

theorem offdiag_removableMajorantLimit_intervalIntegrable
    (n m : ℕ) :
    IntervalIntegrable
      (removableMajorantLimit 0 (offdiagRemovableD n m)) volume
      0 yoshidaLength := by
  exact removableMajorantLimit_intervalIntegrable
    (continuous_offdiagRemovableD n m) 0 yoshidaLength

theorem offdiag_stableGeometricIntegrand_intervalIntegrable
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (hnm : n ≠ m) :
    IntervalIntegrable
      (stableGeometricIntegrand 0
        (clippedOddCorrelation yoshidaHalfLength n m)) volume
      0 yoshidaLength := by
  exact stableGeometricIntegrand_intervalIntegrable_of_removable
    (continuous_offdiagRemovableD n m) 0 yoshidaLength
    (clippedOddCorrelation_offdiag_removable hn hm hnm)

theorem offdiag_pairedIntegralInterchange
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (hnm : n ≠ m) :
    PairedIntegralInterchange yoshidaLength 0
      (clippedOddCorrelation yoshidaHalfLength n m) := by
  apply pairedIntegralInterchange_of_removable yoshidaLength_pos
    (continuous_clippedOddCorrelation_offdiag hn hm hnm)
  · intro u hu
    exact clippedOddCorrelation_offdiag_removable hn hm hnm u
  · exact offdiag_removableMajorantLimit_intervalIntegrable n m

theorem diagonal_removableMajorantLimit_intervalIntegrable
    (n : ℕ) :
    IntervalIntegrable
      (removableMajorantLimit 1 (diagonalRemovableD n)) volume
      0 yoshidaLength := by
  exact removableMajorantLimit_intervalIntegrable
    (continuous_diagonalRemovableD n) 1 yoshidaLength

theorem diagonal_stableGeometricIntegrand_intervalIntegrable
    {n : ℕ} (hn : n ≠ 0) :
    IntervalIntegrable
      (stableGeometricIntegrand 1
        (clippedOddCorrelation yoshidaHalfLength n n)) volume
      0 yoshidaLength := by
  exact stableGeometricIntegrand_intervalIntegrable_of_removable
    (continuous_diagonalRemovableD n) 1 yoshidaLength
    (clippedOddCorrelation_diag_removable hn)

theorem diagonal_pairedIntegralInterchange
    {n : ℕ} (hn : n ≠ 0) :
    PairedIntegralInterchange yoshidaLength 1
      (clippedOddCorrelation yoshidaHalfLength n n) := by
  apply pairedIntegralInterchange_of_removable yoshidaLength_pos
    (continuous_clippedOddCorrelation_diag hn)
  · intro u hu
    exact clippedOddCorrelation_diag_removable hn u
  · exact diagonal_removableMajorantLimit_intervalIntegrable n

theorem offdiag_negated_geometric_identity
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (hnm : n ≠ m) :
    -Real.eulerMascheroniConstant * 0 -
        ∑' k : ℕ, renormalizedTerm yoshidaLength 0
          (clippedOddCorrelation yoshidaHalfLength n m) k =
      (∫ u in 0..yoshidaLength,
        -oddKernel u * clippedOddCorrelation yoshidaHalfLength n m u + 0 / u) -
      (Real.log yoshidaLength + Real.eulerMascheroniConstant + Real.log 2) * 0 := by
  exact negated_geometric_identity yoshidaLength_pos
    (continuous_clippedOddCorrelation_offdiag hn hm hnm)
    (offdiag_pairedIntegralInterchange hn hm hnm)
    (offdiag_stableGeometricIntegrand_intervalIntegrable hn hm hnm)
    (referenceRegularized_intervalIntegrable yoshidaLength)

theorem diagonal_negated_geometric_identity
    {n : ℕ} (hn : n ≠ 0) :
    -Real.eulerMascheroniConstant * 1 -
        ∑' k : ℕ, renormalizedTerm yoshidaLength 1
          (clippedOddCorrelation yoshidaHalfLength n n) k =
      (∫ u in 0..yoshidaLength,
        -oddKernel u * clippedOddCorrelation yoshidaHalfLength n n u + 1 / u) -
      (Real.log yoshidaLength + Real.eulerMascheroniConstant + Real.log 2) * 1 := by
  exact negated_geometric_identity yoshidaLength_pos
    (continuous_clippedOddCorrelation_diag hn)
    (diagonal_pairedIntegralInterchange hn)
    (diagonal_stableGeometricIntegrand_intervalIntegrable hn)
    (referenceRegularized_intervalIntegrable yoshidaLength)

theorem continuous_clippedOddCorrelation
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    Continuous (clippedOddCorrelation yoshidaHalfLength n m) := by
  by_cases hnm : n = m
  · subst m
    exact continuous_clippedOddCorrelation_diag hn
  · exact continuous_clippedOddCorrelation_offdiag hn hm hnm

theorem odd_stableGeometricIntegrand_intervalIntegrable
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    IntervalIntegrable
      (stableGeometricIntegrand
        (clippedOddCorrelation yoshidaHalfLength n m 0)
        (clippedOddCorrelation yoshidaHalfLength n m)) volume
      0 yoshidaLength := by
  by_cases hnm : n = m
  · subst m
    simpa only [clippedOddCorrelation_half_zero hn hn, if_pos rfl] using
      diagonal_stableGeometricIntegrand_intervalIntegrable hn
  · simpa only [clippedOddCorrelation_half_zero hn hm, if_neg hnm] using
      offdiag_stableGeometricIntegrand_intervalIntegrable hn hm hnm

theorem odd_pairedIntegralInterchange
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    PairedIntegralInterchange yoshidaLength
      (clippedOddCorrelation yoshidaHalfLength n m 0)
      (clippedOddCorrelation yoshidaHalfLength n m) := by
  by_cases hnm : n = m
  · subst m
    simpa only [clippedOddCorrelation_half_zero hn hn, if_pos rfl] using
      diagonal_pairedIntegralInterchange hn
  · simpa only [clippedOddCorrelation_half_zero hn hm, if_neg hnm] using
      offdiag_pairedIntegralInterchange hn hm hnm

/-- Uniform diagonal/off-diagonal form of the concrete renormalized identity,
with the actual zero-shift correlation as counterterm. -/
theorem odd_negated_geometric_identity
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    -Real.eulerMascheroniConstant *
          clippedOddCorrelation yoshidaHalfLength n m 0 -
        ∑' k : ℕ, renormalizedTerm yoshidaLength
          (clippedOddCorrelation yoshidaHalfLength n m 0)
          (clippedOddCorrelation yoshidaHalfLength n m) k =
      (∫ u in 0..yoshidaLength,
        -oddKernel u * clippedOddCorrelation yoshidaHalfLength n m u +
          clippedOddCorrelation yoshidaHalfLength n m 0 / u) -
      (Real.log yoshidaLength + Real.eulerMascheroniConstant + Real.log 2) *
        clippedOddCorrelation yoshidaHalfLength n m 0 := by
  by_cases hnm : n = m
  · subst m
    simpa only [clippedOddCorrelation_half_zero hn hn, if_pos rfl] using
      diagonal_negated_geometric_identity hn
  · simpa only [clippedOddCorrelation_half_zero hn hm, if_neg hnm] using
      offdiag_negated_geometric_identity hn hm hnm

end

end ArithmeticHodge.Analysis.YoshidaOddCorrelationIntegrability
