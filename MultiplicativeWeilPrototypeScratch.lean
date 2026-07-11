import ArithmeticHodge.Analysis.WeilPositivity
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeilPrototypeScratch

noncomputable section

/-!
# A source-faithful multiplicative Weil prototype

This scratch file follows Bombieri, *Remarks on Weil's quadratic functional
in the theory of prime numbers, I* (2000), Theorems 1--2.

Bombieri keeps two operations distinct:

* the linear transpose `f*(x) = x^-1 f(x^-1)`;
* the transpose conjugate `bar(g)*(x) = x^-1 conj (g(x^-1))`.

The second, rather than the bare transpose, is the involution used in the
quadratic test `g starMul bar(g)*`.  All functions below are represented on
`R`, but every integral and every source-level identity is restricted to
`Ioi 0`, the multiplicative group `(0, infinity)`.
-/

/-- Bombieri's linear transpose `f*(x) = x^-1 f(x^-1)`.

The complex power is used so that the definition talks directly to Mathlib's
Mellin-transform API.  On the positive half-line it is ordinary division by
`x`; see `transpose_apply_of_pos`. -/
def transpose (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (-1 : ℂ) * f x⁻¹

/-- Bombieri's transpose conjugate `bar(f)*(x)`. -/
def transposeConjugate (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  transpose (fun y => starRingEnd ℂ (f y)) x

/-- Conjugating the coefficients of a function of a complex variable:
`bar(F)(s) = conj (F(conj s))`. -/
def coefficientConjugate (F : ℂ → ℂ) (s : ℂ) : ℂ :=
  starRingEnd ℂ (F (starRingEnd ℂ s))

/-- Multiplicative convolution with Haar density `dy/y` on `(0, infinity)`. -/
noncomputable def mulConvolution (f g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y : ℝ in Ioi 0, f (x / y) * g y / y

/-- Bombieri's second presentation of the quadratic convolution:
`integral g(xy) conj(g(y)) dy`. -/
noncomputable def mulAutocorrelation (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y : ℝ in Ioi 0, g (x * y) * starRingEnd ℂ (g y)

/-- The two-variable kernel whose absolute integrability is exactly the
Fubini hypothesis for Mellin transforming a multiplicative convolution. -/
def convolutionMellinKernel (f g : ℝ → ℂ) (s : ℂ) (p : ℝ × ℝ) : ℂ :=
  ((p.1 : ℂ) ^ (s - 1) * f (p.1 / p.2)) * (g p.2 / p.2)

/-- Explicit absolute-integrability condition for the convolution theorem.

The product measure is `(dx on x > 0) x (dy on y > 0)`. -/
def ConvolutionFubiniAt (f g : ℝ → ℂ) (s : ℂ) : Prop :=
  Integrable (convolutionMellinKernel f g s)
    ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))

/-- All convergence assumptions carried by the integrability-aware Mellin
product API. -/
def MellinProductHypotheses (f g : ℝ → ℂ) (s : ℂ) : Prop :=
  MellinConvergent f s ∧ MellinConvergent g s ∧ ConvolutionFubiniAt f g s

/-- The Mellin-side quadratic term occurring in Bombieri's Theorem 1:
`M g(s) * bar(M g)(1-s)`.

After expanding `coefficientConjugate`, the second factor is
`conj (M g (1 - conj s))`; on the critical line it is `conj (M g s)`. -/
noncomputable def spectralTerm (g : ℝ → ℂ) (s : ℂ) : ℂ :=
  mellin g s * coefficientConjugate (mellin g) (1 - s)

theorem transpose_apply_of_pos (f : ℝ → ℂ) {x : ℝ} (_hx : 0 < x) :
    transpose f x = f x⁻¹ / x := by
  rw [transpose, Complex.cpow_neg_one, ← Complex.ofReal_inv]
  simp only [div_eq_mul_inv, Complex.ofReal_inv]
  ring

theorem transposeConjugate_apply_of_pos (f : ℝ → ℂ) {x : ℝ} (hx : 0 < x) :
    transposeConjugate f x = starRingEnd ℂ (f x⁻¹) / x := by
  rw [transposeConjugate, transpose_apply_of_pos _ hx]

theorem transpose_involutive_on_pos (f : ℝ → ℂ) {x : ℝ} (hx : 0 < x) :
    transpose (transpose f) x = f x := by
  rw [transpose_apply_of_pos _ hx,
    transpose_apply_of_pos f (inv_pos.mpr hx), inv_inv]
  rw [Complex.ofReal_inv]
  field_simp [Complex.ofReal_ne_zero.mpr hx.ne']

theorem transposeConjugate_involutive_on_pos (f : ℝ → ℂ) {x : ℝ} (hx : 0 < x) :
    transposeConjugate (transposeConjugate f) x = f x := by
  rw [transposeConjugate_apply_of_pos _ hx,
    transposeConjugate_apply_of_pos f (inv_pos.mpr hx), inv_inv]
  simp only [map_div₀, Complex.conj_ofReal, starRingEnd_self_apply]
  rw [Complex.ofReal_inv]
  field_simp [Complex.ofReal_ne_zero.mpr hx.ne']

/-- The source's two formulas for the quadratic convolution agree.  The
factor `dy/y` and the `y^-1` in the transpose conjugate combine into the
Jacobian for `y |-> y^-1`. -/
theorem mulConvolution_transposeConjugate_eq_autocorrelation
    (g : ℝ → ℂ) (x : ℝ) :
    mulConvolution g (transposeConjugate g) x = mulAutocorrelation g x := by
  unfold mulConvolution mulAutocorrelation
  calc
    (∫ y : ℝ in Ioi 0,
        g (x / y) * transposeConjugate g y / y) =
      ∫ y : ℝ in Ioi 0,
        ((|(-1 : ℝ)| * y ^ ((-1 : ℝ) - 1)) : ℝ) •
          (g (x * y ^ (-1 : ℝ)) *
            starRingEnd ℂ (g (y ^ (-1 : ℝ)))) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      rw [transposeConjugate_apply_of_pos g hy, Real.rpow_neg_one]
      norm_num only [abs_neg, abs_one, one_mul, neg_sub]
      rw [Real.rpow_neg hy.le 2, Real.rpow_two]
      rw [Complex.real_smul]
      rw [Complex.ofReal_inv]
      have hcast : ((y ^ 2 : ℝ) : ℂ) = (y : ℂ) ^ 2 := by
        apply Complex.ext <;> simp
      have hinv : ((y : ℂ) ^ 2)⁻¹ = ((y ^ 2 : ℝ) : ℂ)⁻¹ :=
        congrArg Inv.inv hcast.symm
      have hpoint :
        g (x / y) * (starRingEnd ℂ (g y⁻¹) / y) / y =
          ((y ^ 2 : ℝ) : ℂ)⁻¹ *
            (g (x * y⁻¹) * starRingEnd ℂ (g y⁻¹)) := by
        calc
          g (x / y) * (starRingEnd ℂ (g y⁻¹) / y) / y =
              ((y : ℂ) ^ 2)⁻¹ *
                (g (x * y⁻¹) * starRingEnd ℂ (g y⁻¹)) := by
            rw [div_eq_mul_inv]
            ring
          _ = ((y ^ 2 : ℝ) : ℂ)⁻¹ *
                (g (x * y⁻¹) * starRingEnd ℂ (g y⁻¹)) :=
            congrArg (fun z => z *
              (g (x * y⁻¹) * starRingEnd ℂ (g y⁻¹))) hinv
      simpa only using hpoint
    _ = ∫ y : ℝ in Ioi 0,
        g (x * y) * starRingEnd ℂ (g y) :=
      integral_comp_rpow_Ioi
        (fun y : ℝ => g (x * y) * starRingEnd ℂ (g y))
        (by norm_num : (-1 : ℝ) ≠ 0)

/-- The linear transpose reverses the Mellin variable around `1/2`.

This identity is unconditional because Mathlib's Bochner integral is
totalized; useful analytic applications should separately carry
`MellinConvergent f (1-s)` (equivalently convergence of the left side). -/
theorem mellin_transpose (f : ℝ → ℂ) (s : ℂ) :
    mellin (transpose f) s = mellin f (1 - s) := by
  calc
    mellin (transpose f) s =
        mellin (fun x : ℝ => f x⁻¹) (s + (-1 : ℂ)) := by
          simpa [transpose, smul_eq_mul] using
            (mellin_cpow_smul (fun x : ℝ => f x⁻¹) s (-1 : ℂ))
    _ = mellin f (-(s + (-1 : ℂ))) := mellin_comp_inv f (s + (-1 : ℂ))
    _ = mellin f (1 - s) := by ring

/-- Convergence is reflected by the same `s |-> 1-s` operation. -/
theorem mellinConvergent_transpose (f : ℝ → ℂ) (s : ℂ) :
    MellinConvergent (transpose f) s ↔ MellinConvergent f (1 - s) := by
  change MellinConvergent
      (fun x : ℝ => (x : ℂ) ^ (-1 : ℂ) • f x⁻¹) s ↔ _
  rw [MellinConvergent.cpow_smul]
  simp_rw [← Real.rpow_neg_one]
  rw [MellinConvergent.comp_rpow (by norm_num : (-1 : ℝ) ≠ 0)]
  norm_num only [Complex.ofReal_neg, Complex.ofReal_one]
  rw [show (s + (-1 : ℂ)) / (-1 : ℂ) = 1 - s by ring]

/-- Integrability-aware version of `mellin_transpose`. -/
theorem hasMellin_transpose (f : ℝ → ℂ) (s : ℂ)
    (hf : MellinConvergent f (1 - s)) :
    HasMellin (transpose f) s (mellin f (1 - s)) :=
  ⟨(mellinConvergent_transpose f s).2 hf, mellin_transpose f s⟩

/-- Mellin transform of pointwise complex conjugation. -/
theorem mellin_conjugate (f : ℝ → ℂ) (s : ℂ) :
    mellin (fun x => starRingEnd ℂ (f x)) s =
      coefficientConjugate (mellin f) s := by
  unfold mellin coefficientConjugate
  change (∫ t : ℝ in Ioi 0,
      (t : ℂ) ^ (s - 1) * starRingEnd ℂ (f t)) =
    starRingEnd ℂ (∫ t : ℝ in Ioi 0,
      (t : ℂ) ^ (starRingEnd ℂ s - 1) * f t)
  calc
    (∫ t : ℝ in Ioi 0,
        (t : ℂ) ^ (s - 1) * starRingEnd ℂ (f t)) =
      ∫ t : ℝ in Ioi 0, starRingEnd ℂ
        ((t : ℂ) ^ (starRingEnd ℂ s - 1) * f t) := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          have hxpos : 0 < x := hx
          have harg : (x : ℂ).arg ≠ Real.pi := by
            rw [Complex.arg_ofReal_of_nonneg hxpos.le]
            exact Real.pi_ne_zero.symm
          have hcpow := Complex.cpow_conj (x : ℂ)
            (starRingEnd ℂ s - 1) harg
          simp only [map_sub, map_one, starRingEnd_self_apply,
            Complex.conj_ofReal] at hcpow
          rw [map_mul, hcpow]
    _ = starRingEnd ℂ (∫ t : ℝ in Ioi 0,
        (t : ℂ) ^ (starRingEnd ℂ s - 1) * f t) := integral_conj

/-- Source-faithful transform rule for the transpose conjugate. -/
theorem mellin_transposeConjugate (f : ℝ → ℂ) (s : ℂ) :
    mellin (transposeConjugate f) s =
      coefficientConjugate (mellin f) (1 - s) := by
  change mellin (transpose (fun y => starRingEnd ℂ (f y))) s = _
  rw [mellin_transpose, mellin_conjugate]

/-- Integrability-aware transpose-conjugate transform rule. -/
theorem hasMellin_transposeConjugate (f : ℝ → ℂ) (s : ℂ)
    (hf : MellinConvergent (fun y => starRingEnd ℂ (f y)) (1 - s)) :
    HasMellin (transposeConjugate f) s
      (coefficientConjugate (mellin f) (1 - s)) := by
  exact ⟨(mellinConvergent_transpose
      (fun y => starRingEnd ℂ (f y)) s).2 hf,
    mellin_transposeConjugate f s⟩

private theorem ofReal_inv_cpow_neg {y : ℝ} (hy : 0 < y) (s : ℂ) :
    ((y⁻¹ : ℝ) : ℂ) ^ (-s) = (y : ℂ) ^ s := by
  have harg : (y : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hy.le]
    exact Real.pi_ne_zero.symm
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _ harg,
    Complex.cpow_neg, inv_inv]

/-- Mellin turns multiplicative convolution into multiplication once the
two-variable kernel is absolutely integrable.

This is the Fubini/change-of-scale step used implicitly in Bombieri's
`M(g starMul bar(g)*)(s) = M g(s) bar(M g)(1-s)`. -/
theorem mellin_mulConvolution
    (f g : ℝ → ℂ) (s : ℂ) (hfg : ConvolutionFubiniAt f g s) :
    mellin (mulConvolution f g) s = mellin f s * mellin g s := by
  unfold mellin mulConvolution
  change (∫ x : ℝ in Ioi 0, (x : ℂ) ^ (s - 1) *
      (∫ y : ℝ in Ioi 0, f (x / y) * g y / y)) = _
  calc
    (∫ x : ℝ in Ioi 0, (x : ℂ) ^ (s - 1) *
        (∫ y : ℝ in Ioi 0, f (x / y) * g y / y)) =
      ∫ x : ℝ in Ioi 0, ∫ y : ℝ in Ioi 0,
        convolutionMellinKernel f g s (x, y) := by
          apply integral_congr_ae
          filter_upwards with x
          calc
            (x : ℂ) ^ (s - 1) *
                (∫ y : ℝ in Ioi 0, f (x / y) * g y / y) =
              ∫ y : ℝ in Ioi 0, (x : ℂ) ^ (s - 1) *
                (f (x / y) * g y / y) :=
              (integral_const_mul (μ := volume.restrict (Ioi 0))
                ((x : ℂ) ^ (s - 1))
                (fun y : ℝ => f (x / y) * g y / y)).symm
            _ = ∫ y : ℝ in Ioi 0,
                convolutionMellinKernel f g s (x, y) := by
              apply integral_congr_ae
              filter_upwards with y
              simp only [convolutionMellinKernel]
              ring
    _ = ∫ y : ℝ in Ioi 0, ∫ x : ℝ in Ioi 0,
        convolutionMellinKernel f g s (x, y) :=
      integral_integral_swap hfg
    _ = ∫ y : ℝ in Ioi 0,
        mellin f s * ((y : ℂ) ^ (s - 1) * g y) := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
          calc
            (∫ x : ℝ in Ioi 0,
                convolutionMellinKernel f g s (x, y)) =
              (∫ x : ℝ in Ioi 0,
                (x : ℂ) ^ (s - 1) * f (x / y)) * (g y / y) := by
              calc
                (∫ x : ℝ in Ioi 0,
                    convolutionMellinKernel f g s (x, y)) =
                  ∫ x : ℝ in Ioi 0,
                    ((x : ℂ) ^ (s - 1) * f (x / y)) * (g y / y) := by
                    apply integral_congr_ae
                    filter_upwards with x
                    simp only [convolutionMellinKernel]
                _ = (∫ x : ℝ in Ioi 0,
                    (x : ℂ) ^ (s - 1) * f (x / y)) * (g y / y) :=
                  integral_mul_const (μ := volume.restrict (Ioi 0))
                    (g y / y) (fun x : ℝ =>
                      (x : ℂ) ^ (s - 1) * f (x / y))
            _ = mellin f s * ((y : ℂ) ^ (s - 1) * g y) := by
              change mellin (fun x : ℝ => f (x / y)) s * (g y / y) = _
              have hfun : (fun x : ℝ => f (x / y)) =
                  fun x : ℝ => f (x * y⁻¹) := by
                funext x
                rw [div_eq_mul_inv]
              rw [hfun, mellin_comp_mul_right f s (inv_pos.mpr hy),
                ofReal_inv_cpow_neg hy]
              simp only [smul_eq_mul]
              have hyne : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
              rw [Complex.cpow_sub s 1 hyne, Complex.cpow_one]
              ring
    _ = mellin f s * mellin g s := by
          change (∫ y : ℝ in Ioi 0,
              mellin f s * ((y : ℂ) ^ (s - 1) * g y)) =
            mellin f s * (∫ y : ℝ in Ioi 0,
              (y : ℂ) ^ (s - 1) * g y)
          exact integral_const_mul _ _

/-- The same absolute-integrability witness also proves convergence of the
Mellin transform of the convolution. -/
theorem mellinConvergent_mulConvolution
    (f g : ℝ → ℂ) (s : ℂ) (hfg : ConvolutionFubiniAt f g s) :
    MellinConvergent (mulConvolution f g) s := by
  change Integrable (fun x : ℝ =>
      (x : ℂ) ^ (s - 1) * mulConvolution f g x)
    (volume.restrict (Ioi 0))
  change Integrable (convolutionMellinKernel f g s)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) at hfg
  have houter := hfg.integral_prod_left
  refine houter.congr ?_
  filter_upwards with x
  unfold mulConvolution
  calc
    (∫ y : ℝ in Ioi 0,
        convolutionMellinKernel f g s (x, y)) =
      ∫ y : ℝ in Ioi 0, (x : ℂ) ^ (s - 1) *
        (f (x / y) * g y / y) := by
      apply integral_congr_ae
      filter_upwards with y
      simp only [convolutionMellinKernel]
      ring
    _ = (x : ℂ) ^ (s - 1) *
        (∫ y : ℝ in Ioi 0, f (x / y) * g y / y) :=
      integral_const_mul (μ := volume.restrict (Ioi 0))
        ((x : ℂ) ^ (s - 1))
        (fun y : ℝ => f (x / y) * g y / y)

/-- Fully integrability-aware product relation. -/
theorem hasMellin_mulConvolution
    (f g : ℝ → ℂ) (s : ℂ)
    (h : MellinProductHypotheses f g s) :
    HasMellin (mulConvolution f g) s (mellin f s * mellin g s) := by
  exact ⟨mellinConvergent_mulConvolution f g s h.2.2,
    mellin_mulConvolution f g s h.2.2⟩

/-- The quadratic convolution has Bombieri's source-oriented Mellin factor. -/
theorem mellin_quadraticConvolution
    (g : ℝ → ℂ) (s : ℂ)
    (hg : ConvolutionFubiniAt g (transposeConjugate g) s) :
    mellin (mulConvolution g (transposeConjugate g)) s = spectralTerm g s := by
  rw [mellin_mulConvolution g (transposeConjugate g) s hg,
    mellin_transposeConjugate]
  rfl

/-- On the critical line the Bombieri spectral term is a squared norm. -/
theorem spectralTerm_eq_normSq_of_re_eq_half
    (g : ℝ → ℂ) {s : ℂ} (hs : s.re = 1 / 2) :
    spectralTerm g s = (Complex.normSq (mellin g s) : ℂ) := by
  have hreflect : 1 - starRingEnd ℂ s = s := by
    apply Complex.ext
    · simp only [sub_re, one_re, conj_re]
      linarith
    · simp
  unfold spectralTerm coefficientConjugate
  simp only [map_sub, map_one]
  rw [hreflect, Complex.normSq_eq_conj_mul_self]
  ring

/-- Finite multiplicity-weighted spectral sums are nonnegative on the
critical line.  This is the algebraic core of the RH-forward implication;
the actual zeta-zero sum is infinite and needs a convergence theorem. -/
theorem finite_spectral_sum_re_nonneg
    {ι : Type*} (S : Finset ι) (zeros : ι → ℂ) (g : ℝ → ℂ)
    (hcrit : ∀ i ∈ S, (zeros i).re = 1 / 2) :
    0 ≤ (∑ i ∈ S, spectralTerm g (zeros i)).re := by
  change 0 ≤ Complex.reCLM (∑ i ∈ S, spectralTerm g (zeros i))
  rw [map_sum Complex.reCLM]
  exact Finset.sum_nonneg fun i hi => by
    rw [spectralTerm_eq_normSq_of_re_eq_half g (hcrit i hi)]
    exact Complex.normSq_nonneg _

/-!
## Conditional infinite spectral statement

The following interface deliberately supplies the missing analytic input:
an exhaustive zero sequence with analytic multiplicity, summability of the
Bombieri terms, and the explicit-formula equality.  None of these properties
follows from the current repository's `NontrivialZetaZero` provenance alone.
-/

/-- A concrete model of `C_c^infinity((0,infinity))`: a globally smooth
extension whose compact support stays inside the positive half-line. -/
def IsBombieriTest (f : ℝ → ℂ) : Prop :=
  ContDiff ℝ ⊤ f ∧ HasCompactSupport f ∧ Function.support f ⊆ Ioi 0

/-- Source-oriented conditional form of Bombieri's Theorem 2.

It records all three assertions from the paper: summability of the zero side,
transpose invariance `T[f] = T[f*]`, and the explicit formula
`T[f] = sum_rho M f(rho)`.  The zero sequence must be understood as exhaustive
and multiplicity-aware by the caller; the repository's current zero type does
not express that invariant. -/
def BombieriExplicitFormula
    (T : (ℝ → ℂ) →ₗ[ℂ] ℂ) (zeros : ℕ → NontrivialZetaZero) : Prop :=
  ∀ f : ℝ → ℂ, IsBombieriTest f →
    Summable (fun n => mellin f (zeros n).val) ∧
      T f = T (transpose f) ∧
      T f = ∑' n, mellin f (zeros n).val

/-- Correctly oriented RH-forward positivity: the functional is evaluated on
`g starMul bar(g)*`, while the spectral side consists of Mellin squared norms.

Strict positivity from Bombieri's Theorem 1 additionally needs the zero-density
argument proving that a nonzero compactly-supported smooth `g` cannot have a
Mellin transform vanishing at every zeta zero. -/
theorem rh_implies_bombieri_nonneg
    (T : (ℝ → ℂ) →ₗ[ℂ] ℂ) (zeros : ℕ → NontrivialZetaZero)
    (hexplicit : BombieriExplicitFormula T zeros)
    (hRH : RiemannHypothesis) (g : ℝ → ℂ)
    (hquadraticTest : IsBombieriTest
      (mulConvolution g (transposeConjugate g)))
    (hfubini : ∀ n,
      ConvolutionFubiniAt g (transposeConjugate g) (zeros n).val) :
    0 ≤ (T (mulConvolution g (transposeConjugate g))).re := by
  let q := mulConvolution g (transposeConjugate g)
  have hexpl := hexplicit q hquadraticTest
  have hterm : ∀ n, mellin q (zeros n).val =
      spectralTerm g (zeros n).val := by
    intro n
    exact mellin_quadraticConvolution g (zeros n).val (hfubini n)
  have hsumm : Summable (fun n => spectralTerm g (zeros n).val) :=
    hexpl.1.congr hterm
  rw [hexpl.2.2, tsum_congr hterm]
  change 0 ≤ Complex.reCLM (∑' n, spectralTerm g (zeros n).val)
  rw [Complex.reCLM.map_tsum hsumm]
  exact tsum_nonneg fun n => by
    rw [spectralTerm_eq_normSq_of_re_eq_half]
    · exact Complex.normSq_nonneg _
    · exact hRH (zeros n).val (zeros n).is_zero (by
        rintro ⟨k, hk⟩
        have hre := (zeros n).re_pos
        rw [hk] at hre
        have hkpos : (0 : ℝ) < (k : ℝ) + 1 := Nat.cast_add_one_pos k
        norm_num at hre
        linarith) (by
          intro hone
          have : (zeros n).val.re = 1 := by rw [hone]; simp
          linarith [(zeros n).re_lt_one])

/-!
## Remaining analytic boundary

This file does **not** prove or assume as hidden facts:

* that `IsBombieriTest g` implies the quadratic convolution is again an
  `IsBombieriTest`;
* the two-variable absolute-integrability witnesses at all zeta zeros;
* an exhaustive, multiplicity-aware enumeration of nontrivial zeros;
* Bombieri's explicit formula and its convergence;
* strict positivity for nonzero tests (which uses zero density versus the
  exponential type of the Mellin transform);
* the converse construction producing a negative test when RH fails.

The repository's current `weilFunctionalFull` cannot instantiate `T` here:
it is a real additive/Fourier scaffold and its implemented archimedean kernel
is `log norm Gamma`, whereas Bombieri's multiplicative functional is complex
linear and uses the logarithmic derivative of Gamma.  Bridging those APIs is
therefore analytic work, not an algebraic rewrite.
-/

#print axioms transpose_apply_of_pos
#print axioms transpose_involutive_on_pos
#print axioms transposeConjugate_involutive_on_pos
#print axioms mulConvolution_transposeConjugate_eq_autocorrelation
#print axioms mellin_transpose
#print axioms mellinConvergent_transpose
#print axioms hasMellin_transpose
#print axioms mellin_conjugate
#print axioms mellin_transposeConjugate
#print axioms hasMellin_transposeConjugate
#print axioms mellin_mulConvolution
#print axioms mellinConvergent_mulConvolution
#print axioms hasMellin_mulConvolution
#print axioms mellin_quadraticConvolution
#print axioms spectralTerm_eq_normSq_of_re_eq_half
#print axioms finite_spectral_sum_re_nonneg
#print axioms rh_implies_bombieri_nonneg

end

end ArithmeticHodge.Analysis.MultiplicativeWeilPrototypeScratch
