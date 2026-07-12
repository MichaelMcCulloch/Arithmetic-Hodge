import ArithmeticHodge.Analysis.YoshidaOddGramPrefix

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaClippedMomentBridge

noncomputable section

open YoshidaOddGramPrefix

/-!
# Yoshida's clipped odd moment bridge reduction

This module proves the exact normalized-sine realization and one-sided
correlation formulas for Yoshida's clipped odd modes.  It reduces the
admissible real-space distribution value to the existing sine and diagonal
moment model, including the removable value at zero.

The final production moment bridge is conditional on two honestly named
analytic boundaries: agreement of the spectral clipped form with Yoshida's
admissible real-space distribution, and interval integrability of the six
leading removable moment integrands.  No positivity or Riemann-hypothesis
claim is made here.
-/

/-- Pointwise real-sine realization of the production clipped odd mode on
the closed interval. -/
theorem yoshidaClippedOddMode_apply_of_mem
    {a x : ℝ} (ha : 0 < a) (n : ℕ) (hx : x ∈ Set.Icc (-a) a) :
    yoshidaClippedOddMode a n x =
      (((Real.sqrt a)⁻¹ * Real.sin (Real.pi * (n : ℝ) * x / a) : ℝ) : ℂ) := by
  rw [yoshidaClippedOddMode]
  simp only [Submodule.coe_smul, Pi.smul_apply, Submodule.coe_sub,
    Pi.sub_apply, smul_eq_mul,
    yoshidaClippedExponential_apply_of_mem _ hx]
  have hsqrtA : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have hsqrtTwoA : Real.sqrt (2 * a) ≠ 0 :=
    (Real.sqrt_pos.2 (mul_pos (by norm_num) ha)).ne'
  let θ : ℝ := Real.pi * (n : ℝ) * x / a
  have hposarg :
      Real.pi * Complex.I * ((n : ℤ) : ℂ) * (x : ℂ) / (a : ℝ) =
        (θ : ℂ) * Complex.I := by
    dsimp [θ]
    push_cast
    field_simp [ha.ne']
  have hnegarg :
      Real.pi * Complex.I * ((-(n : ℤ) : ℤ) : ℂ) * (x : ℂ) / (a : ℝ) =
        ((-θ : ℝ) : ℂ) * Complex.I := by
    dsimp [θ]
    push_cast
    field_simp [ha.ne']
  rw [hposarg, hnegarg, Complex.exp_ofReal_mul_I,
    Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
  have hsqrtMul : Real.sqrt (2 * a) = Real.sqrt 2 * Real.sqrt a := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hsqrtTwo : Real.sqrt 2 ≠ 0 := by positivity
  have hdiff :
      ((Real.sqrt (2 * a) : ℂ)⁻¹ *
            ((Real.cos θ : ℝ) + (Real.sin θ : ℝ) * Complex.I) -
          (Real.sqrt (2 * a) : ℂ)⁻¹ *
            ((Real.cos θ : ℝ) + (-(Real.sin θ) : ℝ) * Complex.I)) =
        2 * (Real.sqrt (2 * a) : ℂ)⁻¹ * (Real.sin θ : ℝ) * Complex.I := by
    push_cast
    ring
  rw [hdiff, hsqrtMul]
  rw [show Real.pi * (n : ℝ) * x / a = θ by rfl]
  push_cast
  field_simp [hsqrtA, hsqrtTwo]
  rw [Complex.I_sq]
  norm_num
  left
  exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)).symm

/-- Real sine representative of the clipped odd mode. -/
def clippedOddRealMode (a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (Real.sqrt a)⁻¹ * Real.sin (Real.pi * (n : ℝ) * x / a)

/-- One-sided correlation entering Yoshida's admissible autocorrelation. -/
def clippedOddCorrelation (a : ℝ) (n m : ℕ) (u : ℝ) : ℝ :=
  ∫ x in -a..a - u,
    clippedOddRealMode a n (u + x) * clippedOddRealMode a m x

private theorem integral_cos_affine
    {c d p q : ℝ} (hc : c ≠ 0) :
    (∫ x in p..q, Real.cos (c * x + d)) =
      (Real.sin (c * q + d) - Real.sin (c * p + d)) / c := by
  have hderiv : ∀ x ∈ Set.uIcc p q,
      HasDerivAt (fun y : ℝ ↦ Real.sin (c * y + d) / c)
        (Real.cos (c * x + d)) x := by
    intro x _
    have hinner : HasDerivAt (fun y : ℝ ↦ c * y + d) c x := by
      simpa [add_comm] using
        (((hasDerivAt_id x).const_mul c).const_add d)
    convert (((Real.hasDerivAt_sin (c * x + d)).comp x hinner).div_const c) using 1
    field_simp [hc]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (Continuous.intervalIntegrable (by fun_prop) p q)
  convert h using 1
  ring

private theorem integral_sin_shift_mul_sin
    {a α β u : ℝ} (hsub : α - β ≠ 0) (hadd : α + β ≠ 0) :
    (∫ x in -a..a - u, Real.sin (α * (u + x)) * Real.sin (β * x)) =
      ((Real.sin ((α - β) * (a - u) + α * u) -
          Real.sin ((α - β) * (-a) + α * u)) / (α - β) -
        (Real.sin ((α + β) * (a - u) + α * u) -
          Real.sin ((α + β) * (-a) + α * u)) / (α + β)) / 2 := by
  have hpoint : (fun x : ℝ ↦
      Real.sin (α * (u + x)) * Real.sin (β * x)) =
      fun x ↦ (Real.cos ((α - β) * x + α * u) -
        Real.cos ((α + β) * x + α * u)) / 2 := by
    funext x
    apply (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).2
    calc
      Real.sin (α * (u + x)) * Real.sin (β * x) * 2 =
          2 * Real.sin (α * (u + x)) * Real.sin (β * x) := by ring
      _ = Real.cos (α * (u + x) - β * x) -
          Real.cos (α * (u + x) + β * x) :=
        Real.two_mul_sin_mul_sin _ _
      _ = _ := by congr 2 <;> ring
  rw [hpoint]
  rw [show (fun x : ℝ ↦
      (Real.cos ((α - β) * x + α * u) -
        Real.cos ((α + β) * x + α * u)) / 2) =
      fun x ↦ (1 / 2 : ℝ) *
        (Real.cos ((α - β) * x + α * u) -
          Real.cos ((α + β) * x + α * u)) by
    funext x
    ring]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_sub]
  · rw [integral_cos_affine hsub, integral_cos_affine hadd]
    ring
  · exact Continuous.intervalIntegrable (by fun_prop) _ _
  · exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- Angular frequency of the interval sine mode. -/
def clippedOddFrequency (a : ℝ) (n : ℕ) : ℝ :=
  Real.pi * (n : ℝ) / a

/-- Exact off-diagonal correlation formula used in Yoshida's real-space
matrix reduction. -/
theorem clippedOddCorrelation_offdiag
    {a u : ℝ} (ha : 0 < a) {n m : ℕ}
    (hn : n ≠ 0) (hm : m ≠ 0) (hnm : n ≠ m) :
    clippedOddCorrelation a n m u =
      ((-1 : ℝ) ^ (n + m) / a) *
        (clippedOddFrequency a n * Real.sin (clippedOddFrequency a m * u) -
          clippedOddFrequency a m * Real.sin (clippedOddFrequency a n * u)) /
        (clippedOddFrequency a n ^ 2 - clippedOddFrequency a m ^ 2) := by
  let α := clippedOddFrequency a n
  let β := clippedOddFrequency a m
  have ha0 : a ≠ 0 := ha.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hsub : α - β ≠ 0 := by
    dsimp [α, β, clippedOddFrequency]
    intro h
    field_simp [ha0] at h
    apply hnm
    have hcast : (n : ℝ) = (m : ℝ) := by
      apply mul_left_cancel₀ hpi
      nlinarith [h]
    exact_mod_cast hcast
  have hadd : α + β ≠ 0 := by
    have hα : 0 < α := by
      dsimp [α, clippedOddFrequency]
      positivity
    have hβ : 0 < β := by
      dsimp [β, clippedOddFrequency]
      positivity
    positivity
  have hsqrt : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have hqsub :
      Real.sin ((α - β) * (a - u) + α * u) =
        (-1 : ℝ) ^ (n + m) * Real.sin (β * u) := by
    rw [show (α - β) * (a - u) + α * u =
        (β * u - (m : ℝ) * Real.pi) + (n : ℝ) * Real.pi by
      dsimp [α, β, clippedOddFrequency]
      field_simp [ha0]
      ring]
    rw [Real.sin_add_nat_mul_pi, Real.sin_sub_nat_mul_pi, pow_add]
    ring
  have hpsub :
      Real.sin ((α - β) * (-a) + α * u) =
        (-1 : ℝ) ^ (n + m) * Real.sin (α * u) := by
    rw [show (α - β) * (-a) + α * u =
        (α * u - (n : ℝ) * Real.pi) + (m : ℝ) * Real.pi by
      dsimp [α, β, clippedOddFrequency]
      field_simp [ha0]
      ring]
    rw [Real.sin_add_nat_mul_pi, Real.sin_sub_nat_mul_pi, pow_add]
    ring
  have hqadd :
      Real.sin ((α + β) * (a - u) + α * u) =
        -((-1 : ℝ) ^ (n + m) * Real.sin (β * u)) := by
    rw [show (α + β) * (a - u) + α * u =
        ((n + m : ℕ) : ℝ) * Real.pi - β * u by
      dsimp [α, β, clippedOddFrequency]
      push_cast
      field_simp [ha0]
      ring]
    exact Real.sin_nat_mul_pi_sub _ _
  have hpadd :
      Real.sin ((α + β) * (-a) + α * u) =
        (-1 : ℝ) ^ (n + m) * Real.sin (α * u) := by
    rw [show (α + β) * (-a) + α * u =
        α * u - ((n + m : ℕ) : ℝ) * Real.pi by
      dsimp [α, β, clippedOddFrequency]
      push_cast
      field_simp [ha0]
      ring]
    exact Real.sin_sub_nat_mul_pi _ _
  rw [clippedOddCorrelation]
  simp only [clippedOddRealMode]
  have hαarg (x : ℝ) : Real.pi * (n : ℝ) * x / a = α * x := by
    dsimp [α, clippedOddFrequency]
    field_simp [ha0]
  have hβarg (x : ℝ) : Real.pi * (m : ℝ) * x / a = β * x := by
    dsimp [β, clippedOddFrequency]
    field_simp [ha0]
  simp_rw [hαarg, hβarg]
  rw [show (fun x : ℝ ↦
      ((Real.sqrt a)⁻¹ * Real.sin (α * (u + x))) *
        ((Real.sqrt a)⁻¹ * Real.sin (β * x))) =
      fun x ↦ ((Real.sqrt a)⁻¹) ^ 2 *
        (Real.sin (α * (u + x)) * Real.sin (β * x)) by
    funext x
    ring]
  rw [intervalIntegral.integral_const_mul,
    integral_sin_shift_mul_sin hsub hadd, hqsub, hpsub, hqadd, hpadd]
  rw [show ((Real.sqrt a)⁻¹) ^ 2 = a⁻¹ by
    rw [inv_pow, Real.sq_sqrt ha.le]]
  change _ = ((-1 : ℝ) ^ (n + m) / a) *
    (α * Real.sin (β * u) - β * Real.sin (α * u)) /
      (α ^ 2 - β ^ 2)
  have hsquare : α ^ 2 - β ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero hadd hsub
  field_simp [hsub, hadd, hsquare]
  ring

private theorem integral_sin_shift_mul_self
    {a α u : ℝ} (hα : α ≠ 0) :
    (∫ x in -a..a - u, Real.sin (α * (u + x)) * Real.sin (α * x)) =
      ((2 * a - u) * Real.cos (α * u) -
        (Real.sin (2 * α * (a - u) + α * u) -
          Real.sin (2 * α * (-a) + α * u)) / (2 * α)) / 2 := by
  have hpoint : (fun x : ℝ ↦
      Real.sin (α * (u + x)) * Real.sin (α * x)) =
      fun x ↦ (Real.cos (α * u) - Real.cos (2 * α * x + α * u)) / 2 := by
    funext x
    apply (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).2
    calc
      Real.sin (α * (u + x)) * Real.sin (α * x) * 2 =
          2 * Real.sin (α * (u + x)) * Real.sin (α * x) := by ring
      _ = Real.cos (α * (u + x) - α * x) -
          Real.cos (α * (u + x) + α * x) :=
        Real.two_mul_sin_mul_sin _ _
      _ = _ := by congr 2 <;> ring
  rw [hpoint]
  rw [show (fun x : ℝ ↦
      (Real.cos (α * u) - Real.cos (2 * α * x + α * u)) / 2) =
      fun x ↦ (1 / 2 : ℝ) *
        (Real.cos (α * u) - Real.cos (2 * α * x + α * u)) by
    funext x
    ring]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_sub]
  · rw [intervalIntegral.integral_const,
      integral_cos_affine (mul_ne_zero (by norm_num) hα)]
    simp only [smul_eq_mul]
    ring
  · exact Continuous.intervalIntegrable continuous_const _ _
  · exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- Exact diagonal correlation formula used in Yoshida's real-space matrix
reduction. -/
theorem clippedOddCorrelation_diag
    {a u : ℝ} (ha : 0 < a) {n : ℕ} (hn : n ≠ 0) :
    clippedOddCorrelation a n n u =
      ((2 * a - u) * Real.cos (clippedOddFrequency a n * u) +
        Real.sin (clippedOddFrequency a n * u) /
          clippedOddFrequency a n) / (2 * a) := by
  let α := clippedOddFrequency a n
  have ha0 : a ≠ 0 := ha.ne'
  have hα : α ≠ 0 := by
    dsimp [α, clippedOddFrequency]
    positivity
  have hsqrt : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have hupper :
      Real.sin (2 * α * (a - u) + α * u) = -Real.sin (α * u) := by
    rw [show 2 * α * (a - u) + α * u =
        (2 * n : ℕ) * Real.pi - α * u by
      dsimp [α, clippedOddFrequency]
      push_cast
      field_simp [ha0]
      ring]
    rw [Real.sin_nat_mul_pi_sub, pow_mul]
    norm_num
  have hlower :
      Real.sin (2 * α * (-a) + α * u) = Real.sin (α * u) := by
    rw [show 2 * α * (-a) + α * u =
        α * u - (2 * n : ℕ) * Real.pi by
      dsimp [α, clippedOddFrequency]
      push_cast
      field_simp [ha0]
      ring]
    rw [Real.sin_sub_nat_mul_pi, pow_mul]
    norm_num
  rw [clippedOddCorrelation]
  simp only [clippedOddRealMode]
  have hαarg (x : ℝ) : Real.pi * (n : ℝ) * x / a = α * x := by
    dsimp [α, clippedOddFrequency]
    field_simp [ha0]
  simp_rw [hαarg]
  rw [show (fun x : ℝ ↦
      ((Real.sqrt a)⁻¹ * Real.sin (α * (u + x))) *
        ((Real.sqrt a)⁻¹ * Real.sin (α * x))) =
      fun x ↦ ((Real.sqrt a)⁻¹) ^ 2 *
        (Real.sin (α * (u + x)) * Real.sin (α * x)) by
    funext x
    ring]
  rw [intervalIntegral.integral_const_mul,
    integral_sin_shift_mul_self hα, hupper, hlower]
  rw [show ((Real.sqrt a)⁻¹) ^ 2 = a⁻¹ by
    rw [inv_pow, Real.sq_sqrt ha.le]]
  change _ = ((2 * a - u) * Real.cos (α * u) +
    Real.sin (α * u) / α) / (2 * a)
  field_simp [ha0, hα]
  ring

theorem two_mul_yoshidaHalfLength :
    2 * yoshidaHalfLength = yoshidaLength := by
  rw [yoshidaHalfLength]
  ring

theorem clippedOddFrequency_yoshidaHalfLength (n : ℕ) :
    clippedOddFrequency yoshidaHalfLength n = yoshidaKappa n := by
  rw [clippedOddFrequency, yoshidaKappa, yoshidaHalfLength]
  field_simp [yoshidaLength_pos.ne']

theorem clippedOddCorrelation_half_offdiag
    {u : ℝ} {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (hnm : n ≠ m) :
    clippedOddCorrelation yoshidaHalfLength n m u =
      (2 * (-1 : ℝ) ^ (n + m) / yoshidaLength) *
        (yoshidaKappa n * Real.sin (yoshidaKappa m * u) -
          yoshidaKappa m * Real.sin (yoshidaKappa n * u)) /
        (yoshidaKappa n ^ 2 - yoshidaKappa m ^ 2) := by
  rw [clippedOddCorrelation_offdiag yoshidaHalfLength_pos hn hm hnm]
  simp only [clippedOddFrequency_yoshidaHalfLength]
  rw [← two_mul_yoshidaHalfLength]
  ring

theorem clippedOddCorrelation_half_diag
    {u : ℝ} {n : ℕ} (hn : n ≠ 0) :
    clippedOddCorrelation yoshidaHalfLength n n u =
      ((yoshidaLength - u) * Real.cos (yoshidaKappa n * u) +
        Real.sin (yoshidaKappa n * u) / yoshidaKappa n) /
        yoshidaLength := by
  rw [clippedOddCorrelation_diag yoshidaHalfLength_pos hn]
  rw [clippedOddFrequency_yoshidaHalfLength, two_mul_yoshidaHalfLength]

theorem clippedOddCorrelation_half_zero
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    clippedOddCorrelation yoshidaHalfLength n m 0 =
      if n = m then 1 else 0 := by
  by_cases hnm : n = m
  · subst m
    rw [if_pos rfl, clippedOddCorrelation_half_diag hn]
    simp [yoshidaLength_pos.ne', yoshidaKappa]
  · rw [if_neg hnm, clippedOddCorrelation_half_offdiag hn hm hnm]
    simp

/-- Removable real-space distribution integrand.  For a normalized diagonal
correlation the `1/u` term cancels the principal part of `yoshidaWeight`;
for an off-diagonal correlation the numerator vanishes at zero. -/
def clippedOddStableCorrelationIntegrand (n m : ℕ) (u : ℝ) : ℝ :=
  yoshidaWeightPlus u * clippedOddCorrelation yoshidaHalfLength n m u +
    (clippedOddCorrelation yoshidaHalfLength n m 0 -
      clippedOddCorrelation yoshidaHalfLength n m u) / u

private theorem yoshidaKappa_ne_zero {n : ℕ} (hn : n ≠ 0) :
    yoshidaKappa n ≠ 0 := by
  rw [yoshidaKappa]
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      (Nat.cast_ne_zero.mpr hn))
    yoshidaLength_pos.ne'

/-- Away from the removable endpoint, the off-diagonal correlation
distribution integrand is exactly the linear combination of Yoshida's
desingularized sine-moment integrands. -/
theorem clippedOddStableCorrelationIntegrand_offdiag
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (hnm : n ≠ m)
    {u : ℝ} (hu : u ≠ 0) :
    clippedOddStableCorrelationIntegrand n m u =
      (2 * (-1 : ℝ) ^ (n + m) / yoshidaLength) *
        (yoshidaKappa n * yoshidaSineMomentIntegrand m u -
          yoshidaKappa m * yoshidaSineMomentIntegrand n u) /
        (yoshidaKappa n ^ 2 - yoshidaKappa m ^ 2) := by
  rw [clippedOddStableCorrelationIntegrand,
    clippedOddCorrelation_half_zero hn hm, if_neg hnm,
    clippedOddCorrelation_half_offdiag hn hm hnm]
  have hκn : yoshidaKappa n ≠ 0 := yoshidaKappa_ne_zero hn
  have hκm : yoshidaKappa m ≠ 0 := yoshidaKappa_ne_zero hm
  rw [yoshidaSineMomentIntegrand, yoshidaSineMomentIntegrand,
    Real.sinc_of_ne_zero (mul_ne_zero hκm hu),
    Real.sinc_of_ne_zero (mul_ne_zero hκn hu)]
  field_simp [hu, hκn, hκm]
  ring

theorem clippedOddStableCorrelationIntegrand_offdiag_all
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (hnm : n ≠ m)
    (u : ℝ) :
    clippedOddStableCorrelationIntegrand n m u =
      (2 * (-1 : ℝ) ^ (n + m) / yoshidaLength) *
        (yoshidaKappa n * yoshidaSineMomentIntegrand m u -
          yoshidaKappa m * yoshidaSineMomentIntegrand n u) /
        (yoshidaKappa n ^ 2 - yoshidaKappa m ^ 2) := by
  by_cases hu : u = 0
  · subst u
    rw [clippedOddStableCorrelationIntegrand,
      clippedOddCorrelation_half_zero hn hm, if_neg hnm]
    simp [yoshidaSineMomentIntegrand]
    ring
  · exact clippedOddStableCorrelationIntegrand_offdiag hn hm hnm hu

/-- Away from the removable endpoint, the diagonal correlation distribution
integrand is exactly the diagonal-moment integrand plus the normalized sine
moment correction. -/
theorem clippedOddStableCorrelationIntegrand_diag
    {n : ℕ} (hn : n ≠ 0) {u : ℝ} (hu : u ≠ 0) :
    clippedOddStableCorrelationIntegrand n n u =
      yoshidaDiagonalMomentIntegrand n u +
        yoshidaSineMomentIntegrand n u /
          (yoshidaLength * yoshidaKappa n) := by
  rw [clippedOddStableCorrelationIntegrand,
    clippedOddCorrelation_half_zero hn hn, if_pos rfl,
    clippedOddCorrelation_half_diag hn]
  have hκ : yoshidaKappa n ≠ 0 := yoshidaKappa_ne_zero hn
  rw [yoshidaDiagonalMomentIntegrand, yoshidaSineMomentIntegrand,
    Real.sinc_of_ne_zero (mul_ne_zero hκ hu)]
  field_simp [hu, hκ, yoshidaLength_pos.ne']
  have htrig : 2 * Real.sin (u * yoshidaKappa n / 2) ^ 2 =
      1 - Real.cos (u * yoshidaKappa n) := by
    have hcos := Real.cos_two_mul' (u * yoshidaKappa n / 2)
    have hsum := Real.sin_sq_add_cos_sq (u * yoshidaKappa n / 2)
    rw [show 2 * (u * yoshidaKappa n / 2) =
      u * yoshidaKappa n by ring] at hcos
    nlinarith
  rw [show yoshidaLength * 2 * Real.sin (u * yoshidaKappa n / 2) ^ 2 =
      yoshidaLength * (2 * Real.sin (u * yoshidaKappa n / 2) ^ 2) by ring,
    htrig]
  ring

theorem clippedOddStableCorrelationIntegrand_diag_all
    {n : ℕ} (hn : n ≠ 0) (u : ℝ) :
    clippedOddStableCorrelationIntegrand n n u =
      yoshidaDiagonalMomentIntegrand n u +
        yoshidaSineMomentIntegrand n u /
          (yoshidaLength * yoshidaKappa n) := by
  by_cases hu : u = 0
  · subst u
    rw [clippedOddStableCorrelationIntegrand,
      clippedOddCorrelation_half_zero hn hn, if_pos rfl]
    simp [yoshidaDiagonalMomentIntegrand, yoshidaSineMomentIntegrand,
      yoshidaWeightPlus]
    field_simp [yoshidaLength_pos.ne', yoshidaKappa_ne_zero hn]
    ring
  · exact clippedOddStableCorrelationIntegrand_diag hn hu

/-- The admissible real-space value attached to the exact clipped
correlation.  The constant term is the `Q` archimedean local constant. -/
def clippedOddAdmissibleRealSpaceGram (n m : ℕ) : ℝ :=
  (∫ u in 0..yoshidaLength,
      clippedOddStableCorrelationIntegrand n m u) -
    (Real.log yoshidaLength + Real.eulerMascheroniConstant +
      Real.log 2 + Real.log Real.pi) *
      clippedOddCorrelation yoshidaHalfLength n m 0

/-- Once the two sine integrands are known interval-integrable, the exact
off-diagonal admissible real-space value is the production moment model. -/
theorem clippedOddAdmissibleRealSpaceGram_offdiag_eq_oddMomentGram
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (hnm : n ≠ m)
    (hSn : IntervalIntegrable (yoshidaSineMomentIntegrand n)
      MeasureTheory.volume 0 yoshidaLength)
    (hSm : IntervalIntegrable (yoshidaSineMomentIntegrand m)
      MeasureTheory.volume 0 yoshidaLength) :
    clippedOddAdmissibleRealSpaceGram n m =
      oddMomentGram yoshidaSineMoment yoshidaDiagonalMoment n m := by
  rw [clippedOddAdmissibleRealSpaceGram,
    clippedOddCorrelation_half_zero hn hm, if_neg hnm, mul_zero, sub_zero]
  rw [intervalIntegral.integral_congr (fun u _ ↦
    clippedOddStableCorrelationIntegrand_offdiag_all hn hm hnm u)]
  rw [oddMomentGram, if_neg hnm]
  let C : ℝ :=
    (2 * (-1 : ℝ) ^ (n + m) / yoshidaLength) /
      (yoshidaKappa n ^ 2 - yoshidaKappa m ^ 2)
  rw [show (fun u : ℝ ↦
      (2 * (-1 : ℝ) ^ (n + m) / yoshidaLength) *
          (yoshidaKappa n * yoshidaSineMomentIntegrand m u -
            yoshidaKappa m * yoshidaSineMomentIntegrand n u) /
          (yoshidaKappa n ^ 2 - yoshidaKappa m ^ 2)) =
      fun u ↦ C *
        (yoshidaKappa n * yoshidaSineMomentIntegrand m u -
          yoshidaKappa m * yoshidaSineMomentIntegrand n u) by
    funext u
    dsimp [C]
    ring]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_sub
    (hSm.const_mul (yoshidaKappa n))
    (hSn.const_mul (yoshidaKappa m))]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  rw [yoshidaSineMoment, yoshidaSineMoment]
  dsimp [C]
  ring

/-- Once the diagonal and sine integrands are known interval-integrable, the
exact diagonal admissible real-space value is the production moment model. -/
theorem clippedOddAdmissibleRealSpaceGram_diag_eq_oddMomentGram
    {n : ℕ} (hn : n ≠ 0)
    (hSn : IntervalIntegrable (yoshidaSineMomentIntegrand n)
      MeasureTheory.volume 0 yoshidaLength)
    (hDn : IntervalIntegrable (yoshidaDiagonalMomentIntegrand n)
      MeasureTheory.volume 0 yoshidaLength) :
    clippedOddAdmissibleRealSpaceGram n n =
      oddMomentGram yoshidaSineMoment yoshidaDiagonalMoment n n := by
  rw [clippedOddAdmissibleRealSpaceGram,
    clippedOddCorrelation_half_zero hn hn, if_pos rfl]
  rw [intervalIntegral.integral_congr (fun u _ ↦
    clippedOddStableCorrelationIntegrand_diag_all hn u)]
  rw [oddMomentGram, if_pos rfl]
  let c : ℝ := (yoshidaLength * yoshidaKappa n)⁻¹
  rw [show (fun u : ℝ ↦ yoshidaDiagonalMomentIntegrand n u +
      yoshidaSineMomentIntegrand n u /
        (yoshidaLength * yoshidaKappa n)) =
      fun u ↦ yoshidaDiagonalMomentIntegrand n u +
        c * yoshidaSineMomentIntegrand n u by
    funext u
    dsimp [c]
    ring]
  rw [intervalIntegral.integral_add hDn (hSn.const_mul c),
    intervalIntegral.integral_const_mul]
  rw [yoshidaDiagonalMoment, yoshidaSineMoment]
  dsimp [c]
  ring

/-- The only spectral/distribution assertion still needed after the exact
correlation calculation: the production digamma-kernel form on each leading
clipped mode pair agrees with the admissible real-space distribution value. -/
def ClippedOddAdmissibleDistributionBridge : Prop :=
  ∀ i j : Fin 3,
    clippedOddPrefixGram i j =
      (clippedOddAdmissibleRealSpaceGram (i.1 + 1) (j.1 + 1) : ℂ)

/-- Integrability boundary for the six removable moment integrands used by
the leading three frequencies. -/
def ClippedOddPrefixMomentIntegrable : Prop :=
  ∀ n : ℕ, 1 ≤ n → n ≤ 3 →
    IntervalIntegrable (yoshidaSineMomentIntegrand n)
        MeasureTheory.volume 0 yoshidaLength ∧
      IntervalIntegrable (yoshidaDiagonalMomentIntegrand n)
        MeasureTheory.volume 0 yoshidaLength

/-- The exact production `ClippedOddMomentBridge` follows from the remaining
spectral-to-admissible-distribution theorem and removable-integrand
integrability.  All mode/correlation/moment algebra is discharged here. -/
theorem clippedOddMomentBridge_of_admissibleDistributionBridge
    (hdist : ClippedOddAdmissibleDistributionBridge)
    (hint : ClippedOddPrefixMomentIntegrable) :
    ClippedOddMomentBridge := by
  intro i j
  rw [hdist i j]
  norm_cast
  unfold oddMomentPrefixGram
  have hni : (i.1 + 1 : ℕ) ≠ 0 := by omega
  have hnj : (j.1 + 1 : ℕ) ≠ 0 := by omega
  have hiLe : i.1 + 1 ≤ 3 := by omega
  have hjLe : j.1 + 1 ≤ 3 := by omega
  have hiInt := hint (i.1 + 1) (by omega) hiLe
  have hjInt := hint (j.1 + 1) (by omega) hjLe
  by_cases hnm : i.1 + 1 = j.1 + 1
  · rw [← hnm]
    exact clippedOddAdmissibleRealSpaceGram_diag_eq_oddMomentGram
      hni hiInt.1 hiInt.2
  · exact clippedOddAdmissibleRealSpaceGram_offdiag_eq_oddMomentGram
      hni hnj hnm hiInt.1 hjInt.1

end

end ArithmeticHodge.Analysis.YoshidaClippedMomentBridge
