import ArithmeticHodge.Analysis.YoshidaEndpointEvenFullPolarization
import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
import ArithmeticHodge.Analysis.YoshidaEndpointWeightedCauchy
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenHyperbolicStructural

noncomputable section

open YoshidaEndpointEvenConstantCross
open YoshidaEndpointEvenFullPolarization
open YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointWeightedCauchy
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive

/-!
# Global hyperbolic data for the `P0/P2/P4/P6` block

The fixed endpoint cosh factor is replaced by its global degree-six Taylor
polynomial.  Exact Legendre moments retain a positive rank-one term.  The
single Taylor remainder is charged by Cauchy--Schwarz to the full centered
energy; no interval subdivision or sampled certificate occurs.
-/

/-- The retained even profile through degree six. -/
def factorTwoIntrinsicP0246Profile
    (c0 c2 c4 c6 x : ℝ) : ℝ :=
  c0 * centeredEvenP0 x + c2 * centeredEvenP2 x +
    c4 * factorTwoCenteredP4 x + c6 * factorTwoCenteredP6 x

theorem continuous_factorTwoIntrinsicP0246Profile
    (c0 c2 c4 c6 : ℝ) :
    Continuous (factorTwoIntrinsicP0246Profile c0 c2 c4 c6) := by
  unfold factorTwoIntrinsicP0246Profile centeredEvenP0 centeredEvenP2
    factorTwoCenteredP4
  rw [show factorTwoCenteredP6 = fun x ↦
      (231 * x ^ 6 - 315 * x ^ 4 + 105 * x ^ 2 - 5) / 16 by
    funext x
    exact factorTwoCenteredP6_eq x]
  fun_prop

theorem even_factorTwoIntrinsicP0246Profile
    (c0 c2 c4 c6 : ℝ) :
    Function.Even (factorTwoIntrinsicP0246Profile c0 c2 c4 c6) := by
  intro x
  unfold factorTwoIntrinsicP0246Profile
  rw [even_factorTwoCenteredP4 x, even_factorTwoCenteredP6 x]
  unfold centeredEvenP0 centeredEvenP2
  ring

/-- The polynomial cosh moment before inserting a particular profile. -/
def yoshidaEndpointCoshPolynomial6Moment (e : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ in -1..1, yoshidaEndpointCoshPolynomial6 x * e x

/-- The single endpoint-cosh Taylor residual. -/
def yoshidaEndpointCoshPolynomial6Error (x : ℝ) : ℝ :=
  Real.cosh (yoshidaEndpointA * x / 2) -
    yoshidaEndpointCoshPolynomial6 x

theorem continuous_yoshidaEndpointCoshPolynomial6Error :
    Continuous yoshidaEndpointCoshPolynomial6Error := by
  unfold yoshidaEndpointCoshPolynomial6Error
    yoshidaEndpointCoshPolynomial6
  fun_prop

theorem abs_yoshidaEndpointCoshPolynomial6Error_lt
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |yoshidaEndpointCoshPolynomial6Error x| <
      (1 / 48000000000 : ℝ) := by
  exact abs_cosh_sub_yoshidaEndpointCoshPolynomial6_lt hx

private theorem integral_polynomial_twelve
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ l r : ℝ) :
    (∫ x : ℝ in l..r,
      a₀ * x ^ 0 + a₁ * x ^ 1 + a₂ * x ^ 2 + a₃ * x ^ 3 +
        a₄ * x ^ 4 + a₅ * x ^ 5 + a₆ * x ^ 6 + a₇ * x ^ 7 +
        a₈ * x ^ 8 + a₉ * x ^ 9 + a₁₀ * x ^ 10 + a₁₁ * x ^ 11 +
        a₁₂ * x ^ 12) =
      a₀ * (r - l) + a₁ * (r ^ 2 - l ^ 2) / 2 +
        a₂ * (r ^ 3 - l ^ 3) / 3 + a₃ * (r ^ 4 - l ^ 4) / 4 +
        a₄ * (r ^ 5 - l ^ 5) / 5 + a₅ * (r ^ 6 - l ^ 6) / 6 +
        a₆ * (r ^ 7 - l ^ 7) / 7 + a₇ * (r ^ 8 - l ^ 8) / 8 +
        a₈ * (r ^ 9 - l ^ 9) / 9 + a₉ * (r ^ 10 - l ^ 10) / 10 +
        a₁₀ * (r ^ 11 - l ^ 11) / 11 +
        a₁₁ * (r ^ 12 - l ^ 12) / 12 +
        a₁₂ * (r ^ 13 - l ^ 13) / 13 := by
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) l r)
    (Continuous.intervalIntegrable (by fun_prop) l r)]
  repeat rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

/-- Exact degree-six cosh-polynomial moment of an arbitrary even sextic. -/
theorem integral_coshPolynomial6_mul_evenSextic
    (q0 q2 q4 q6 : ℝ) :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointCoshPolynomial6 x *
        (q0 + q2 * x ^ 2 + q4 * x ^ 4 + q6 * x ^ 6)) =
      2 * q0 +
        (2 / 3 : ℝ) * (q2 + yoshidaEndpointA ^ 2 / 8 * q0) +
        (2 / 5 : ℝ) *
          (q4 + yoshidaEndpointA ^ 2 / 8 * q2 +
            yoshidaEndpointA ^ 4 / 384 * q0) +
        (2 / 7 : ℝ) *
          (q6 + yoshidaEndpointA ^ 2 / 8 * q4 +
            yoshidaEndpointA ^ 4 / 384 * q2 +
            yoshidaEndpointA ^ 6 / 46080 * q0) +
        (2 / 9 : ℝ) *
          (yoshidaEndpointA ^ 2 / 8 * q6 +
            yoshidaEndpointA ^ 4 / 384 * q4 +
            yoshidaEndpointA ^ 6 / 46080 * q2) +
        (2 / 11 : ℝ) *
          (yoshidaEndpointA ^ 4 / 384 * q6 +
            yoshidaEndpointA ^ 6 / 46080 * q4) +
        (2 / 13 : ℝ) * (yoshidaEndpointA ^ 6 / 46080 * q6) := by
  rw [show (fun x : ℝ ↦
      yoshidaEndpointCoshPolynomial6 x *
        (q0 + q2 * x ^ 2 + q4 * x ^ 4 + q6 * x ^ 6)) =
      fun x ↦
        q0 * x ^ 0 + 0 * x ^ 1 +
        (q2 + yoshidaEndpointA ^ 2 / 8 * q0) * x ^ 2 + 0 * x ^ 3 +
        (q4 + yoshidaEndpointA ^ 2 / 8 * q2 +
          yoshidaEndpointA ^ 4 / 384 * q0) * x ^ 4 + 0 * x ^ 5 +
        (q6 + yoshidaEndpointA ^ 2 / 8 * q4 +
          yoshidaEndpointA ^ 4 / 384 * q2 +
          yoshidaEndpointA ^ 6 / 46080 * q0) * x ^ 6 + 0 * x ^ 7 +
        (yoshidaEndpointA ^ 2 / 8 * q6 +
          yoshidaEndpointA ^ 4 / 384 * q4 +
          yoshidaEndpointA ^ 6 / 46080 * q2) * x ^ 8 + 0 * x ^ 9 +
        (yoshidaEndpointA ^ 4 / 384 * q6 +
          yoshidaEndpointA ^ 6 / 46080 * q4) * x ^ 10 + 0 * x ^ 11 +
        (yoshidaEndpointA ^ 6 / 46080 * q6) * x ^ 12 by
    funext x
    unfold yoshidaEndpointCoshPolynomial6
    ring,
    integral_polynomial_twelve]
  ring

theorem integral_coshPolynomial6_mul_p0 :
    yoshidaEndpointCoshPolynomial6Moment centeredEvenP0 =
      2 + yoshidaEndpointA ^ 2 / 12 +
        yoshidaEndpointA ^ 4 / 960 +
        yoshidaEndpointA ^ 6 / 161280 := by
  unfold yoshidaEndpointCoshPolynomial6Moment
  rw [show centeredEvenP0 = fun x : ℝ ↦
      1 + 0 * x ^ 2 + 0 * x ^ 4 + 0 * x ^ 6 by
    funext x
    simp [centeredEvenP0],
    integral_coshPolynomial6_mul_evenSextic]
  ring

theorem integral_coshPolynomial6_mul_p2 :
    yoshidaEndpointCoshPolynomial6Moment centeredEvenP2 =
      yoshidaEndpointA ^ 2 / 30 +
        yoshidaEndpointA ^ 4 / 1680 +
        yoshidaEndpointA ^ 6 / 241920 := by
  unfold yoshidaEndpointCoshPolynomial6Moment
  rw [show centeredEvenP2 = fun x : ℝ ↦
      (-1 / 2 : ℝ) + (3 / 2 : ℝ) * x ^ 2 +
        0 * x ^ 4 + 0 * x ^ 6 by
    funext x
    unfold centeredEvenP2
    ring,
    integral_coshPolynomial6_mul_evenSextic]
  ring

theorem integral_coshPolynomial6_mul_p4 :
    yoshidaEndpointCoshPolynomial6Moment factorTwoCenteredP4 =
      yoshidaEndpointA ^ 4 / 7560 +
        yoshidaEndpointA ^ 6 / 665280 := by
  unfold yoshidaEndpointCoshPolynomial6Moment
  rw [show factorTwoCenteredP4 = fun x : ℝ ↦
      (3 / 8 : ℝ) + (-15 / 4 : ℝ) * x ^ 2 +
        (35 / 8 : ℝ) * x ^ 4 + 0 * x ^ 6 by
    funext x
    unfold factorTwoCenteredP4
    ring,
    integral_coshPolynomial6_mul_evenSextic]
  ring

/-- The degree-six Legendre mode sees only the top Taylor coefficient. -/
theorem integral_coshPolynomial6_mul_p6 :
    yoshidaEndpointCoshPolynomial6Moment factorTwoCenteredP6 =
      yoshidaEndpointA ^ 6 / 4324320 := by
  unfold yoshidaEndpointCoshPolynomial6Moment
  rw [show factorTwoCenteredP6 = fun x : ℝ ↦
      (-5 / 16 : ℝ) + (105 / 16 : ℝ) * x ^ 2 +
        (-315 / 16 : ℝ) * x ^ 4 + (231 / 16 : ℝ) * x ^ 6 by
    funext x
    rw [factorTwoCenteredP6_eq]
    ring,
    integral_coshPolynomial6_mul_evenSextic]
  ring

/-- The exact coefficient-linear rank-one coordinate. -/
def factorTwoIntrinsicP0246CoshPolynomialMoment
    (c0 c2 c4 c6 : ℝ) : ℝ :=
  c0 * (2 + yoshidaEndpointA ^ 2 / 12 +
      yoshidaEndpointA ^ 4 / 960 + yoshidaEndpointA ^ 6 / 161280) +
    c2 * (yoshidaEndpointA ^ 2 / 30 +
      yoshidaEndpointA ^ 4 / 1680 + yoshidaEndpointA ^ 6 / 241920) +
    c4 * (yoshidaEndpointA ^ 4 / 7560 +
      yoshidaEndpointA ^ 6 / 665280) +
    c6 * (yoshidaEndpointA ^ 6 / 4324320)

theorem coshPolynomial6Moment_factorTwoIntrinsicP0246Profile
    (c0 c2 c4 c6 : ℝ) :
    yoshidaEndpointCoshPolynomial6Moment
        (factorTwoIntrinsicP0246Profile c0 c2 c4 c6) =
      factorTwoIntrinsicP0246CoshPolynomialMoment c0 c2 c4 c6 := by
  unfold yoshidaEndpointCoshPolynomial6Moment
    factorTwoIntrinsicP0246Profile
  rw [show (fun x : ℝ ↦
      yoshidaEndpointCoshPolynomial6 x *
        (c0 * centeredEvenP0 x + c2 * centeredEvenP2 x +
          c4 * factorTwoCenteredP4 x + c6 * factorTwoCenteredP6 x)) =
      fun x ↦ yoshidaEndpointCoshPolynomial6 x *
        ((c0 - c2 / 2 + 3 * c4 / 8 - 5 * c6 / 16) +
          (3 * c2 / 2 - 15 * c4 / 4 + 105 * c6 / 16) * x ^ 2 +
          (35 * c4 / 8 - 315 * c6 / 16) * x ^ 4 +
          (231 * c6 / 16) * x ^ 6) by
    funext x
    unfold centeredEvenP0 centeredEvenP2 factorTwoCenteredP4
    rw [factorTwoCenteredP6_eq]
    ring,
    integral_coshPolynomial6_mul_evenSextic]
  unfold factorTwoIntrinsicP0246CoshPolynomialMoment
  ring

/-- Exact `L²` norm of an arbitrary even sextic in monomial coordinates. -/
private theorem integral_evenSextic_sq
    (q0 q2 q4 q6 : ℝ) :
    (∫ x : ℝ in -1..1,
      (q0 + q2 * x ^ 2 + q4 * x ^ 4 + q6 * x ^ 6) ^ 2) =
      2 * q0 ^ 2 + (2 / 3 : ℝ) * (2 * q0 * q2) +
        (2 / 5 : ℝ) * (q2 ^ 2 + 2 * q0 * q4) +
        (2 / 7 : ℝ) * (2 * q0 * q6 + 2 * q2 * q4) +
        (2 / 9 : ℝ) * (q4 ^ 2 + 2 * q2 * q6) +
        (2 / 11 : ℝ) * (2 * q4 * q6) +
        (2 / 13 : ℝ) * q6 ^ 2 := by
  rw [show (fun x : ℝ ↦
      (q0 + q2 * x ^ 2 + q4 * x ^ 4 + q6 * x ^ 6) ^ 2) =
      fun x ↦ q0 ^ 2 * x ^ 0 + 0 * x ^ 1 +
        (2 * q0 * q2) * x ^ 2 + 0 * x ^ 3 +
        (q2 ^ 2 + 2 * q0 * q4) * x ^ 4 + 0 * x ^ 5 +
        (2 * q0 * q6 + 2 * q2 * q4) * x ^ 6 + 0 * x ^ 7 +
        (q4 ^ 2 + 2 * q2 * q6) * x ^ 8 + 0 * x ^ 9 +
        (2 * q4 * q6) * x ^ 10 + 0 * x ^ 11 + q6 ^ 2 * x ^ 12 by
    funext x
    ring,
    integral_polynomial_twelve]
  ring

theorem integral_factorTwoIntrinsicP0246Profile_sq
    (c0 c2 c4 c6 : ℝ) :
    (∫ x : ℝ in -1..1,
      factorTwoIntrinsicP0246Profile c0 c2 c4 c6 x ^ 2) =
      2 * c0 ^ 2 + (2 / 5 : ℝ) * c2 ^ 2 +
        (2 / 9 : ℝ) * c4 ^ 2 + (2 / 13 : ℝ) * c6 ^ 2 := by
  rw [show (fun x : ℝ ↦
      factorTwoIntrinsicP0246Profile c0 c2 c4 c6 x ^ 2) =
      fun x ↦
        ((c0 - c2 / 2 + 3 * c4 / 8 - 5 * c6 / 16) +
          (3 * c2 / 2 - 15 * c4 / 4 + 105 * c6 / 16) * x ^ 2 +
          (35 * c4 / 8 - 315 * c6 / 16) * x ^ 4 +
          (231 * c6 / 16) * x ^ 6) ^ 2 by
    funext x
    unfold factorTwoIntrinsicP0246Profile centeredEvenP0 centeredEvenP2
      factorTwoCenteredP4
    rw [factorTwoCenteredP6_eq]
    ring,
    integral_evenSextic_sq]
  ring

private theorem sq_intervalIntegral_mul_le
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    (∫ x : ℝ in -1..1, f x * g x) ^ 2 ≤
      (∫ x : ℝ in -1..1, f x ^ 2) *
        (∫ x : ℝ in -1..1, g x ^ 2) := by
  let μ : Measure ℝ := volume.restrict (Ioc (-1 : ℝ) 1)
  have hfMeas : AEStronglyMeasurable f μ :=
    hf.aestronglyMeasurable.restrict
  have hgMeas : AEStronglyMeasurable g μ :=
    hg.aestronglyMeasurable.restrict
  have hfLp : MemLp f 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hfMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖f x‖ ^ 2)
        (Icc (-1 : ℝ) 1) :=
      (hf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have hgLp : MemLp g 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hgMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖g x‖ ^ 2)
        (Icc (-1 : ℝ) 1) :=
      (hg.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have h := sq_integral_mul_le_weighted μ (fun _ : ℝ ↦ 1) f g
    (by simp) (by simpa using hfLp) (by simpa using hgLp)
  repeat rw [intervalIntegral.integral_of_le (by norm_num)]
  simpa only [μ, div_one, one_mul] using h

theorem integral_coshPolynomial6Error_sq_le :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointCoshPolynomial6Error x ^ 2) ≤
      2 * (1 / 48000000000 : ℝ) ^ 2 := by
  have herr : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointCoshPolynomial6Error x ^ 2)
      volume (-1) 1 :=
    (continuous_yoshidaEndpointCoshPolynomial6Error.pow 2).intervalIntegrable
      (-1) 1
  have hconst : IntervalIntegrable
      (fun _x : ℝ ↦ (1 / 48000000000 : ℝ) ^ 2)
      volume (-1) 1 := continuous_const.intervalIntegrable (-1) 1
  calc
    (∫ x : ℝ in -1..1,
        yoshidaEndpointCoshPolynomial6Error x ^ 2) ≤
        ∫ _x : ℝ in -1..1, (1 / 48000000000 : ℝ) ^ 2 := by
      apply intervalIntegral.integral_mono_on (by norm_num) herr hconst
      intro x hx
      have habs :=
        (abs_yoshidaEndpointCoshPolynomial6Error_lt hx).le
      have hsquare := (sq_le_sq₀ (abs_nonneg _)
        (by norm_num : (0 : ℝ) ≤ 1 / 48000000000)).2 habs
      simpa only [sq_abs] using hsquare
    _ = 2 * (1 / 48000000000 : ℝ) ^ 2 := by norm_num

theorem yoshidaEndpointCoshMoment_sub_polynomial6Moment_eq
    (e : ℝ → ℝ) (he : Continuous e) :
    yoshidaEndpointCoshMoment e -
        yoshidaEndpointCoshPolynomial6Moment e =
      ∫ x : ℝ in -1..1,
        yoshidaEndpointCoshPolynomial6Error x * e x := by
  have htrue : IntervalIntegrable
      (fun x : ℝ ↦ Real.cosh (yoshidaEndpointA * x / 2) * e x)
      volume (-1) 1 := (by fun_prop : Continuous
        (fun x : ℝ ↦ Real.cosh (yoshidaEndpointA * x / 2) * e x))
          |>.intervalIntegrable (-1) 1
  have hpoly : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointCoshPolynomial6 x * e x)
      volume (-1) 1 := (by
        unfold yoshidaEndpointCoshPolynomial6
        fun_prop : Continuous
          (fun x : ℝ ↦ yoshidaEndpointCoshPolynomial6 x * e x))
          |>.intervalIntegrable (-1) 1
  unfold yoshidaEndpointCoshMoment yoshidaEndpointCoshPolynomial6Moment
  rw [← intervalIntegral.integral_sub htrue hpoly]
  apply intervalIntegral.integral_congr
  intro x _hx
  unfold yoshidaEndpointCoshPolynomial6Error
  ring

/-- Global energy-relative error for the degree-six cosh moment. -/
theorem sq_coshMoment_sub_polynomial6Moment_le_energy
    (e : ℝ → ℝ) (he : Continuous e) :
    (yoshidaEndpointCoshMoment e -
        yoshidaEndpointCoshPolynomial6Moment e) ^ 2 ≤
      2 * (1 / 48000000000 : ℝ) ^ 2 *
        (∫ x : ℝ in -1..1, e x ^ 2) := by
  rw [yoshidaEndpointCoshMoment_sub_polynomial6Moment_eq e he]
  have hcauchy := sq_intervalIntegral_mul_le
    yoshidaEndpointCoshPolynomial6Error e
    continuous_yoshidaEndpointCoshPolynomial6Error he
  have henergy : 0 ≤ ∫ x : ℝ in -1..1, e x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg (e x))
  exact hcauchy.trans <| mul_le_mul_of_nonneg_right
    integral_coshPolynomial6Error_sq_le henergy

theorem hyperbolicQuadratic_eq_two_mul_coshMoment_sq_of_even
    (e : ℝ → ℝ) (heven : Function.Even e) :
    yoshidaEndpointHyperbolicQuadratic (fun x ↦ (e x : ℂ)) =
      2 * yoshidaEndpointA * yoshidaEndpointCoshMoment e ^ 2 := by
  rw [yoshidaEndpointHyperbolicQuadratic_ofReal_eq_moments,
    yoshidaEndpointSinhMoment_eq_zero_of_even e heven]
  ring

/-- The positive degree-six rank-one term survives globally; the sole loss
is four Taylor-error masses. -/
theorem coshPolynomial6_rankOne_sub_error_le_hyperbolicQuadratic
    (e : ℝ → ℝ) (he : Continuous e) (heven : Function.Even e) :
    yoshidaEndpointA * yoshidaEndpointCoshPolynomial6Moment e ^ 2 -
        4 * yoshidaEndpointA * (1 / 48000000000 : ℝ) ^ 2 *
          (∫ x : ℝ in -1..1, e x ^ 2) ≤
      yoshidaEndpointHyperbolicQuadratic (fun x ↦ (e x : ℂ)) := by
  rw [hyperbolicQuadratic_eq_two_mul_coshMoment_sq_of_even e heven]
  let m : ℝ := yoshidaEndpointCoshMoment e
  let p : ℝ := yoshidaEndpointCoshPolynomial6Moment e
  let E : ℝ := ∫ x : ℝ in -1..1, e x ^ 2
  have herr : (m - p) ^ 2 ≤
      2 * (1 / 48000000000 : ℝ) ^ 2 * E := by
    simpa only [m, p, E] using
      sq_coshMoment_sub_polynomial6Moment_le_energy e he
  have hyoung : p ^ 2 ≤ 2 * m ^ 2 + 2 * (m - p) ^ 2 := by
    nlinarith [sq_nonneg (2 * m - p)]
  have hyoungScaled := mul_le_mul_of_nonneg_left hyoung yoshidaEndpointA_pos.le
  have herrScaled := mul_le_mul_of_nonneg_left herr
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) yoshidaEndpointA_pos.le)
  dsimp only [m, p, E] at hyoungScaled herrScaled ⊢
  nlinarith

theorem sq_coshMoment_P0246_sub_exactPolynomial_le
    (c0 c2 c4 c6 : ℝ) :
    (yoshidaEndpointCoshMoment
        (factorTwoIntrinsicP0246Profile c0 c2 c4 c6) -
      factorTwoIntrinsicP0246CoshPolynomialMoment c0 c2 c4 c6) ^ 2 ≤
      2 * (1 / 48000000000 : ℝ) ^ 2 *
        (2 * c0 ^ 2 + (2 / 5 : ℝ) * c2 ^ 2 +
          (2 / 9 : ℝ) * c4 ^ 2 + (2 / 13 : ℝ) * c6 ^ 2) := by
  have h := sq_coshMoment_sub_polynomial6Moment_le_energy
    (factorTwoIntrinsicP0246Profile c0 c2 c4 c6)
    (continuous_factorTwoIntrinsicP0246Profile c0 c2 c4 c6)
  rw [coshPolynomial6Moment_factorTwoIntrinsicP0246Profile,
    integral_factorTwoIntrinsicP0246Profile_sq] at h
  exact h

/-- Coefficient-level retained rank-one lower bound for the complete even
`P0/P2/P4/P6` profile. -/
theorem P0246_coshPolynomial_rankOne_sub_error_le_hyperbolicQuadratic
    (c0 c2 c4 c6 : ℝ) :
    yoshidaEndpointA *
        factorTwoIntrinsicP0246CoshPolynomialMoment c0 c2 c4 c6 ^ 2 -
      4 * yoshidaEndpointA * (1 / 48000000000 : ℝ) ^ 2 *
        (2 * c0 ^ 2 + (2 / 5 : ℝ) * c2 ^ 2 +
          (2 / 9 : ℝ) * c4 ^ 2 + (2 / 13 : ℝ) * c6 ^ 2) ≤
      yoshidaEndpointHyperbolicQuadratic
        (fun x ↦
          (factorTwoIntrinsicP0246Profile c0 c2 c4 c6 x : ℂ)) := by
  have h := coshPolynomial6_rankOne_sub_error_le_hyperbolicQuadratic
    (factorTwoIntrinsicP0246Profile c0 c2 c4 c6)
    (continuous_factorTwoIntrinsicP0246Profile c0 c2 c4 c6)
    (even_factorTwoIntrinsicP0246Profile c0 c2 c4 c6)
  rw [coshPolynomial6Moment_factorTwoIntrinsicP0246Profile,
    integral_factorTwoIntrinsicP0246Profile_sq] at h
  exact h

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenHyperbolicStructural
