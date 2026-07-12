import ArithmeticHodge.Analysis.YoshidaClippedMomentBridgeFull
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaMomentIntegrability

noncomputable section

open YoshidaOddGramPrefix
open YoshidaClippedMomentBridge
open YoshidaClippedMomentBridgeFull

/-!
# Integrability of Yoshida's removable odd moments

The apparent singularities in the odd sine and diagonal moment integrands are
removed by holomorphic divided-difference extensions.  Agreement away from the
single null point `u = 0` transfers interval integrability to the production
integrands, discharging all twenty mode obligations for frequencies 1 through
10.
-/

private theorem complex_dslope_zero_differentiable
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (dslope f 0) := by
  intro z
  have hOn : DifferentiableOn ℂ (dslope f 0) Set.univ :=
    (Complex.differentiableOn_dslope (s := Set.univ) (by simp)).2 hf.differentiableOn
  exact hOn.differentiableAt (by simp)

def complexSinhSlope : ℂ → ℂ := dslope Complex.sinh 0

private theorem complexSinhSlope_differentiable :
    Differentiable ℂ complexSinhSlope := by
  exact complex_dslope_zero_differentiable Complex.differentiable_sinh

private theorem complexSinhSlope_continuous :
    Continuous complexSinhSlope := complexSinhSlope_differentiable.continuous

private theorem complexSinhSlope_ofReal_ne (u : ℝ) :
    complexSinhSlope (u : ℂ) ≠ 0 := by
  by_cases hu : u = 0
  · subst u
    change dslope Complex.sinh 0 (0 : ℂ) ≠ 0
    rw [dslope_same, Complex.deriv_sinh]
    simp
  · rw [complexSinhSlope, dslope_of_ne _ (by exact_mod_cast hu)]
    simp only [slope, sub_zero, Complex.sinh_zero, smul_eq_mul]
    have hsinh : Complex.sinh (u : ℂ) ≠ 0 := by
      intro hzero
      have hre := congrArg Complex.re hzero
      change Real.sinh u = 0 at hre
      exact hu (Real.sinh_eq_zero.mp hre)
    exact mul_ne_zero (inv_ne_zero (by exact_mod_cast hu))
      (by simpa using hsinh)

private theorem complexSinhSlope_ofReal {u : ℝ} (hu : u ≠ 0) :
    complexSinhSlope (u : ℂ) = (Real.sinh u / u : ℝ) := by
  rw [complexSinhSlope, dslope_of_ne _ (by exact_mod_cast hu)]
  simp only [slope, sub_zero, Complex.sinh_zero, smul_eq_mul]
  rw [← Complex.ofReal_sinh]
  simp
  field_simp [hu]

def complexDiagonalFactor (n : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (z / 2) * (1 - z / (yoshidaLength : ℂ)) *
    Complex.cos ((yoshidaKappa n : ℂ) * z)

def complexDiagonalCore (n : ℕ) (z : ℂ) : ℂ :=
  Complex.sinh z - z * complexDiagonalFactor n z

private theorem complexDiagonalFactor_differentiable (n : ℕ) :
    Differentiable ℂ (complexDiagonalFactor n) := by
  unfold complexDiagonalFactor
  fun_prop

private theorem complexDiagonalCore_differentiable (n : ℕ) :
    Differentiable ℂ (complexDiagonalCore n) := by
  unfold complexDiagonalCore
  exact Complex.differentiable_sinh.sub
    (differentiable_id.mul (complexDiagonalFactor_differentiable n))

private theorem complexDiagonalCore_deriv_zero (n : ℕ) :
    deriv (complexDiagonalCore n) 0 = 0 := by
  have hfactor := (complexDiagonalFactor_differentiable n 0).hasDerivAt
  have hprod := (hasDerivAt_id (0 : ℂ)).mul hfactor
  have hcore := (Complex.hasDerivAt_sinh 0).sub hprod
  simpa [complexDiagonalCore, complexDiagonalFactor] using hcore.deriv

private theorem complexDiagonalCore_ofReal (n : ℕ) (u : ℝ) :
    complexDiagonalCore n (u : ℂ) =
      (Real.sinh u - u * Real.exp (u / 2) *
        (1 - u / yoshidaLength) * Real.cos (yoshidaKappa n * u) : ℝ) := by
  have hexp : Complex.exp ((u : ℂ) / 2) = (Real.exp (u / 2) : ℝ) := by
    calc
      Complex.exp ((u : ℂ) / 2) = Complex.exp ((u / 2 : ℝ) : ℂ) := by
        congr 1
        push_cast
        ring
      _ = (Real.exp (u / 2) : ℝ) := (Complex.ofReal_exp _).symm
  have hcos : Complex.cos ((yoshidaKappa n : ℂ) * (u : ℂ)) =
      (Real.cos (yoshidaKappa n * u) : ℝ) := by
    calc
      Complex.cos ((yoshidaKappa n : ℂ) * (u : ℂ)) =
          Complex.cos ((yoshidaKappa n * u : ℝ) : ℂ) := by
        congr 1
        push_cast
        ring
      _ = (Real.cos (yoshidaKappa n * u) : ℝ) := (Complex.ofReal_cos _).symm
  rw [complexDiagonalCore, complexDiagonalFactor, ← Complex.ofReal_sinh,
    hexp, hcos]
  push_cast
  ring

def complexDiagonalSecondSlope (n : ℕ) : ℂ → ℂ :=
  dslope (dslope (complexDiagonalCore n) 0) 0

private theorem complexDiagonalSecondSlope_differentiable (n : ℕ) :
    Differentiable ℂ (complexDiagonalSecondSlope n) := by
  exact complex_dslope_zero_differentiable
    (complex_dslope_zero_differentiable (complexDiagonalCore_differentiable n))

private theorem complexDiagonalSecondSlope_continuous (n : ℕ) :
    Continuous (complexDiagonalSecondSlope n) :=
  (complexDiagonalSecondSlope_differentiable n).continuous

private theorem complexDiagonalSecondSlope_ofReal
    (n : ℕ) {u : ℝ} (hu : u ≠ 0) :
    complexDiagonalSecondSlope n (u : ℂ) =
      ((Real.sinh u - u * Real.exp (u / 2) *
        (1 - u / yoshidaLength) * Real.cos (yoshidaKappa n * u)) / u ^ 2 : ℝ) := by
  rw [complexDiagonalSecondSlope, dslope_of_ne _ (by exact_mod_cast hu)]
  simp only [slope, sub_zero, smul_eq_mul]
  rw [dslope_same, complexDiagonalCore_deriv_zero]
  rw [dslope_of_ne _ (by exact_mod_cast hu)]
  simp only [slope, sub_zero, smul_eq_mul, complexDiagonalCore_ofReal]
  simp [complexDiagonalCore, complexDiagonalFactor]
  field_simp [hu]

def yoshidaSineMomentSurrogate (n : ℕ) (u : ℝ) : ℝ :=
  2 * (Real.exp (u / 2) + Real.exp (-u / 2)) *
      Real.sin (yoshidaKappa n * u) -
    (((Real.exp (u / 2) * yoshidaKappa n *
      Real.sinc (yoshidaKappa n * u) : ℝ) : ℂ) /
        complexSinhSlope (u : ℂ)).re

private theorem yoshidaSineMomentSurrogate_continuous (n : ℕ) :
    Continuous (yoshidaSineMomentSurrogate n) := by
  have hnum : Continuous (fun u : ℝ ↦
      ((Real.exp (u / 2) * yoshidaKappa n *
        Real.sinc (yoshidaKappa n * u) : ℝ) : ℂ)) := by
    fun_prop
  have hden : Continuous (fun u : ℝ ↦ complexSinhSlope (u : ℂ)) :=
    complexSinhSlope_continuous.comp Complex.continuous_ofReal
  have hquot : Continuous (fun u : ℝ ↦
      ((Real.exp (u / 2) * yoshidaKappa n *
        Real.sinc (yoshidaKappa n * u) : ℝ) : ℂ) /
          complexSinhSlope (u : ℂ)) :=
    hnum.div hden complexSinhSlope_ofReal_ne
  exact (by fun_prop : Continuous (fun u : ℝ ↦
    2 * (Real.exp (u / 2) + Real.exp (-u / 2)) *
      Real.sin (yoshidaKappa n * u))).sub (Complex.continuous_re.comp hquot)

def yoshidaDiagonalMomentSurrogate (n : ℕ) (u : ℝ) : ℝ :=
  2 * (Real.exp (u / 2) + Real.exp (-u / 2)) *
      ((yoshidaLength - u) / yoshidaLength) *
      Real.cos (yoshidaKappa n * u) +
    (complexDiagonalSecondSlope n (u : ℂ) /
      complexSinhSlope (u : ℂ)).re

private theorem yoshidaDiagonalMomentSurrogate_continuous (n : ℕ) :
    Continuous (yoshidaDiagonalMomentSurrogate n) := by
  have hnum : Continuous (fun u : ℝ ↦
      complexDiagonalSecondSlope n (u : ℂ)) :=
    (complexDiagonalSecondSlope_continuous n).comp Complex.continuous_ofReal
  have hden : Continuous (fun u : ℝ ↦ complexSinhSlope (u : ℂ)) :=
    complexSinhSlope_continuous.comp Complex.continuous_ofReal
  have hquot : Continuous (fun u : ℝ ↦
      complexDiagonalSecondSlope n (u : ℂ) /
        complexSinhSlope (u : ℂ)) :=
    hnum.div hden complexSinhSlope_ofReal_ne
  exact (by fun_prop : Continuous (fun u : ℝ ↦
    2 * (Real.exp (u / 2) + Real.exp (-u / 2)) *
      ((yoshidaLength - u) / yoshidaLength) *
      Real.cos (yoshidaKappa n * u))).add (Complex.continuous_re.comp hquot)

private theorem yoshidaKappa_ne_zero {n : ℕ} (hn : n ≠ 0) :
    yoshidaKappa n ≠ 0 := by
  rw [yoshidaKappa]
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      (Nat.cast_ne_zero.mpr hn))
    yoshidaLength_pos.ne'

private theorem real_sinh_eq_exp (u : ℝ) :
    Real.sinh u = (Real.exp u - Real.exp (-u)) / 2 :=
  Real.sinh_eq u

private theorem ofReal_div_re (a b : ℝ) :
    (((a : ℂ) / (b : ℂ)).re) = a / b := by
  rw [← Complex.ofReal_div]
  simp

private theorem yoshidaSineMomentIntegrand_eq_surrogate
    {n : ℕ} (hn : n ≠ 0) {u : ℝ} (hu : u ≠ 0) :
    yoshidaSineMomentIntegrand n u = yoshidaSineMomentSurrogate n u := by
  have hk : yoshidaKappa n ≠ 0 := yoshidaKappa_ne_zero hn
  have hku : yoshidaKappa n * u ≠ 0 := mul_ne_zero hk hu
  have hsinh : Real.sinh u ≠ 0 := Real.sinh_eq_zero.not.mpr hu
  have hdiff : Real.exp u - Real.exp (-u) ≠ 0 := by
    intro hzero
    apply hsinh
    rw [real_sinh_eq_exp, hzero]
    norm_num
  rw [yoshidaSineMomentIntegrand, yoshidaSineMomentSurrogate,
    yoshidaWeightPlus, if_neg hu, yoshidaWeight,
    Real.sinc_of_ne_zero hku, complexSinhSlope_ofReal hu]
  rw [ofReal_div_re]
  rw [real_sinh_eq_exp] at hsinh ⊢
  field_simp [hu, hk, hsinh, hdiff]
  ring

private theorem yoshidaDiagonalMomentIntegrand_eq_surrogate
    (n : ℕ) {u : ℝ} (hu : u ≠ 0) :
    yoshidaDiagonalMomentIntegrand n u =
      yoshidaDiagonalMomentSurrogate n u := by
  have hsinh : Real.sinh u ≠ 0 := Real.sinh_eq_zero.not.mpr hu
  have hdiff : Real.exp u - Real.exp (-u) ≠ 0 := by
    intro hzero
    apply hsinh
    rw [real_sinh_eq_exp, hzero]
    norm_num
  have htrig : 2 * Real.sin (yoshidaKappa n * u / 2) ^ 2 =
      1 - Real.cos (yoshidaKappa n * u) := by
    have hcos := Real.cos_two_mul' (yoshidaKappa n * u / 2)
    have hsum := Real.sin_sq_add_cos_sq (yoshidaKappa n * u / 2)
    rw [show 2 * (yoshidaKappa n * u / 2) =
      yoshidaKappa n * u by ring] at hcos
    nlinarith
  rw [yoshidaDiagonalMomentIntegrand, yoshidaDiagonalMomentSurrogate,
    yoshidaWeightPlus, if_neg hu, yoshidaWeight,
    complexDiagonalSecondSlope_ofReal n hu,
    complexSinhSlope_ofReal hu, ofReal_div_re, htrig]
  rw [real_sinh_eq_exp] at hsinh ⊢
  field_simp [hu, yoshidaLength_pos.ne', hsinh, hdiff]
  ring

theorem yoshidaSineMomentIntegrand_intervalIntegrable
    {n : ℕ} (hn : n ≠ 0) :
    IntervalIntegrable (yoshidaSineMomentIntegrand n)
      MeasureTheory.volume 0 yoshidaLength := by
  have hsur : IntervalIntegrable (yoshidaSineMomentSurrogate n)
      MeasureTheory.volume 0 yoshidaLength :=
    Continuous.intervalIntegrable (yoshidaSineMomentSurrogate_continuous n) _ _
  apply hsur.congr_ae
  refine ae_restrict_of_ae ?_
  have hne : ∀ᵐ u : ℝ ∂MeasureTheory.volume, u ≠ 0 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hne] with u hu
  exact (yoshidaSineMomentIntegrand_eq_surrogate hn hu).symm

theorem yoshidaDiagonalMomentIntegrand_intervalIntegrable (n : ℕ) :
    IntervalIntegrable (yoshidaDiagonalMomentIntegrand n)
      MeasureTheory.volume 0 yoshidaLength := by
  have hsur : IntervalIntegrable (yoshidaDiagonalMomentSurrogate n)
      MeasureTheory.volume 0 yoshidaLength :=
    Continuous.intervalIntegrable (yoshidaDiagonalMomentSurrogate_continuous n) _ _
  apply hsur.congr_ae
  refine ae_restrict_of_ae ?_
  have hne : ∀ᵐ u : ℝ ∂MeasureTheory.volume, u ≠ 0 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hne] with u hu
  exact (yoshidaDiagonalMomentIntegrand_eq_surrogate n hu).symm

theorem clippedOddTenMomentIntegrable :
    ∀ n : ℕ, 1 ≤ n → n ≤ 10 →
      IntervalIntegrable (yoshidaSineMomentIntegrand n)
          MeasureTheory.volume 0 yoshidaLength ∧
        IntervalIntegrable (yoshidaDiagonalMomentIntegrand n)
          MeasureTheory.volume 0 yoshidaLength := by
  intro n hn _
  exact ⟨yoshidaSineMomentIntegrand_intervalIntegrable (by omega),
    yoshidaDiagonalMomentIntegrand_intervalIntegrable n⟩

theorem clippedOddPrefixMomentIntegrable : ClippedOddPrefixMomentIntegrable := by
  intro n hn hn3
  exact clippedOddTenMomentIntegrable n hn (by omega)

/-- All twenty removable moment integrands required by the full odd block are
interval-integrable. -/
theorem clippedOddFullMomentIntegrable : ClippedOddFullMomentIntegrable :=
  clippedOddTenMomentIntegrable

end

end ArithmeticHodge.Analysis.YoshidaMomentIntegrability
