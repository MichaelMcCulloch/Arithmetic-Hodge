import ArithmeticHodge.Analysis.YoshidaEvenIntervalCertificate
import ArithmeticHodge.Analysis.YoshidaMomentIntegrability

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaClippedEvenMomentBridge

noncomputable section

open YoshidaClippedMomentBridge
open YoshidaEvenIntervalCertificate
open YoshidaMomentIntegrability
open YoshidaOddGramPrefix

/-!
# Exact clipped even moment bridge reduction

This module computes the normalized cosine and zero-mode one-sided
correlations used by Yoshida's even block.  It identifies their admissible
real-space values with `evenMomentGram` in every zero, diagonal, and
off-diagonal case.  The endpoint identities are used almost everywhere,
because the even removable representatives need not agree at the single point
`u = 0`.

The final production bridge is conditional only on the honestly named
spectral-to-admissible-distribution assembly boundary.  No positivity or
Riemann-hypothesis claim is made here.
-/

/-- Pointwise real-cosine realization of a positive-frequency clipped even
mode on the closed interval. -/
theorem yoshidaClippedEvenMode_apply_of_mem
    {a x : ℝ} (ha : 0 < a) (n : ℕ) (hx : x ∈ Set.Icc (-a) a) :
    yoshidaClippedEvenMode a n x =
      (((Real.sqrt a)⁻¹ * Real.cos (Real.pi * (n : ℝ) * x / a) : ℝ) : ℂ) := by
  rw [yoshidaClippedEvenMode]
  simp only [Submodule.coe_smul, Pi.smul_apply, Submodule.coe_add,
    Pi.add_apply, smul_eq_mul,
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
  rw [hsqrtMul]
  push_cast
  field_simp [hsqrtA, hsqrtTwo]
  have hthetaC :
      (Real.pi : ℂ) * (n : ℂ) * (x : ℂ) / (a : ℂ) = (θ : ℂ) := by
    dsimp [θ]
    push_cast
    rfl
  rw [hthetaC]
  have hsqrtTwoSq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  rw [hsqrtTwoSq]
  ring

/-- Pointwise real realization of the normalized zero-frequency mode. -/
theorem yoshidaClippedEvenZeroMode_apply_of_mem
    {a x : ℝ} (hx : x ∈ Set.Icc (-a) a) :
    yoshidaClippedEvenZeroMode a x =
      (((Real.sqrt (2 * a))⁻¹ : ℝ) : ℂ) := by
  rw [yoshidaClippedEvenZeroMode,
    yoshidaClippedExponential_apply_of_mem _ hx]
  norm_num

/-- Positive-frequency real cosine representative. -/
def clippedEvenRealMode (a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (Real.sqrt a)⁻¹ * Real.cos (Real.pi * (n : ℝ) * x / a)

/-- Normalized real zero-frequency representative. -/
def clippedEvenZeroRealMode (a : ℝ) (_x : ℝ) : ℝ :=
  (Real.sqrt (2 * a))⁻¹

/-- One-sided correlation between two positive-frequency even modes. -/
def clippedEvenCorrelation (a : ℝ) (n m : ℕ) (u : ℝ) : ℝ :=
  ∫ x in -a..a - u,
    clippedEvenRealMode a n (u + x) * clippedEvenRealMode a m x

/-- One-sided correlation with the zero mode in the first slot. -/
def clippedEvenZeroPositiveCorrelation
    (a : ℝ) (m : ℕ) (u : ℝ) : ℝ :=
  ∫ x in -a..a - u,
    clippedEvenZeroRealMode a (u + x) * clippedEvenRealMode a m x

/-- One-sided correlation with the zero mode in the second slot. -/
def clippedEvenPositiveZeroCorrelation
    (a : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  ∫ x in -a..a - u,
    clippedEvenRealMode a n (u + x) * clippedEvenZeroRealMode a x

/-- One-sided zero/zero correlation. -/
def clippedEvenZeroCorrelation (a u : ℝ) : ℝ :=
  ∫ x in -a..a - u,
    clippedEvenZeroRealMode a (u + x) * clippedEvenZeroRealMode a x

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

/-- Angular frequency of the interval cosine mode. -/
def clippedEvenFrequency (a : ℝ) (n : ℕ) : ℝ :=
  Real.pi * (n : ℝ) / a

private theorem integral_cos_shift_mul_cos
    {a α β u : ℝ} (hsub : α - β ≠ 0) (hadd : α + β ≠ 0) :
    (∫ x in -a..a - u, Real.cos (α * (u + x)) * Real.cos (β * x)) =
      ((Real.sin ((α - β) * (a - u) + α * u) -
          Real.sin ((α - β) * (-a) + α * u)) / (α - β) +
        (Real.sin ((α + β) * (a - u) + α * u) -
          Real.sin ((α + β) * (-a) + α * u)) / (α + β)) / 2 := by
  have hpoint : (fun x : ℝ ↦
      Real.cos (α * (u + x)) * Real.cos (β * x)) =
      fun x ↦ (Real.cos ((α - β) * x + α * u) +
        Real.cos ((α + β) * x + α * u)) / 2 := by
    funext x
    apply (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).2
    calc
      Real.cos (α * (u + x)) * Real.cos (β * x) * 2 =
          2 * Real.cos (α * (u + x)) * Real.cos (β * x) := by ring
      _ = Real.cos (α * (u + x) - β * x) +
          Real.cos (α * (u + x) + β * x) :=
        Real.two_mul_cos_mul_cos _ _
      _ = _ := by congr 2 <;> ring
  rw [hpoint]
  rw [show (fun x : ℝ ↦
      (Real.cos ((α - β) * x + α * u) +
        Real.cos ((α + β) * x + α * u)) / 2) =
      fun x ↦ (1 / 2 : ℝ) *
        (Real.cos ((α - β) * x + α * u) +
          Real.cos ((α + β) * x + α * u)) by
    funext x
    ring]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_add]
  · rw [integral_cos_affine hsub, integral_cos_affine hadd]
    ring
  · exact Continuous.intervalIntegrable (by fun_prop) _ _
  · exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- Exact positive-frequency off-diagonal even correlation. -/
theorem clippedEvenCorrelation_offdiag
    {a u : ℝ} (ha : 0 < a) {n m : ℕ}
    (hn : n ≠ 0) (hm : m ≠ 0) (hnm : n ≠ m) :
    clippedEvenCorrelation a n m u =
      ((-1 : ℝ) ^ (n + m) / a) *
        (clippedEvenFrequency a m * Real.sin (clippedEvenFrequency a m * u) -
          clippedEvenFrequency a n * Real.sin (clippedEvenFrequency a n * u)) /
        (clippedEvenFrequency a n ^ 2 - clippedEvenFrequency a m ^ 2) := by
  let α := clippedEvenFrequency a n
  let β := clippedEvenFrequency a m
  have ha0 : a ≠ 0 := ha.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hsub : α - β ≠ 0 := by
    dsimp [α, β, clippedEvenFrequency]
    intro h
    field_simp [ha0] at h
    apply hnm
    have hcast : (n : ℝ) = (m : ℝ) := by
      apply mul_left_cancel₀ hpi
      nlinarith [h]
    exact_mod_cast hcast
  have hadd : α + β ≠ 0 := by
    have hα : 0 < α := by
      dsimp [α, clippedEvenFrequency]
      positivity
    have hβ : 0 < β := by
      dsimp [β, clippedEvenFrequency]
      positivity
    positivity
  have hsqrt : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have hqsub :
      Real.sin ((α - β) * (a - u) + α * u) =
        (-1 : ℝ) ^ (n + m) * Real.sin (β * u) := by
    rw [show (α - β) * (a - u) + α * u =
        (β * u - (m : ℝ) * Real.pi) + (n : ℝ) * Real.pi by
      dsimp [α, β, clippedEvenFrequency]
      field_simp [ha0]
      ring]
    rw [Real.sin_add_nat_mul_pi, Real.sin_sub_nat_mul_pi, pow_add]
    ring
  have hpsub :
      Real.sin ((α - β) * (-a) + α * u) =
        (-1 : ℝ) ^ (n + m) * Real.sin (α * u) := by
    rw [show (α - β) * (-a) + α * u =
        (α * u - (n : ℝ) * Real.pi) + (m : ℝ) * Real.pi by
      dsimp [α, β, clippedEvenFrequency]
      field_simp [ha0]
      ring]
    rw [Real.sin_add_nat_mul_pi, Real.sin_sub_nat_mul_pi, pow_add]
    ring
  have hqadd :
      Real.sin ((α + β) * (a - u) + α * u) =
        -((-1 : ℝ) ^ (n + m) * Real.sin (β * u)) := by
    rw [show (α + β) * (a - u) + α * u =
        ((n + m : ℕ) : ℝ) * Real.pi - β * u by
      dsimp [α, β, clippedEvenFrequency]
      push_cast
      field_simp [ha0]
      ring]
    exact Real.sin_nat_mul_pi_sub _ _
  have hpadd :
      Real.sin ((α + β) * (-a) + α * u) =
        (-1 : ℝ) ^ (n + m) * Real.sin (α * u) := by
    rw [show (α + β) * (-a) + α * u =
        α * u - ((n + m : ℕ) : ℝ) * Real.pi by
      dsimp [α, β, clippedEvenFrequency]
      push_cast
      field_simp [ha0]
      ring]
    exact Real.sin_sub_nat_mul_pi _ _
  rw [clippedEvenCorrelation]
  simp only [clippedEvenRealMode]
  have hαarg (x : ℝ) : Real.pi * (n : ℝ) * x / a = α * x := by
    dsimp [α, clippedEvenFrequency]
    field_simp [ha0]
  have hβarg (x : ℝ) : Real.pi * (m : ℝ) * x / a = β * x := by
    dsimp [β, clippedEvenFrequency]
    field_simp [ha0]
  simp_rw [hαarg, hβarg]
  rw [show (fun x : ℝ ↦
      ((Real.sqrt a)⁻¹ * Real.cos (α * (u + x))) *
        ((Real.sqrt a)⁻¹ * Real.cos (β * x))) =
      fun x ↦ ((Real.sqrt a)⁻¹) ^ 2 *
        (Real.cos (α * (u + x)) * Real.cos (β * x)) by
    funext x
    ring]
  rw [intervalIntegral.integral_const_mul,
    integral_cos_shift_mul_cos hsub hadd, hqsub, hpsub, hqadd, hpadd]
  rw [show ((Real.sqrt a)⁻¹) ^ 2 = a⁻¹ by
    rw [inv_pow, Real.sq_sqrt ha.le]]
  change _ = ((-1 : ℝ) ^ (n + m) / a) *
    (β * Real.sin (β * u) - α * Real.sin (α * u)) /
      (α ^ 2 - β ^ 2)
  have hsquare : α ^ 2 - β ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero hadd hsub
  field_simp [hsub, hadd, hsquare]
  ring

private theorem integral_cos_shift_mul_self
    {a α u : ℝ} (hα : α ≠ 0) :
    (∫ x in -a..a - u, Real.cos (α * (u + x)) * Real.cos (α * x)) =
      ((2 * a - u) * Real.cos (α * u) +
        (Real.sin (2 * α * (a - u) + α * u) -
          Real.sin (2 * α * (-a) + α * u)) / (2 * α)) / 2 := by
  have hpoint : (fun x : ℝ ↦
      Real.cos (α * (u + x)) * Real.cos (α * x)) =
      fun x ↦ (Real.cos (α * u) + Real.cos (2 * α * x + α * u)) / 2 := by
    funext x
    apply (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).2
    calc
      Real.cos (α * (u + x)) * Real.cos (α * x) * 2 =
          2 * Real.cos (α * (u + x)) * Real.cos (α * x) := by ring
      _ = Real.cos (α * (u + x) - α * x) +
          Real.cos (α * (u + x) + α * x) :=
        Real.two_mul_cos_mul_cos _ _
      _ = _ := by congr 2 <;> ring
  rw [hpoint]
  rw [show (fun x : ℝ ↦
      (Real.cos (α * u) + Real.cos (2 * α * x + α * u)) / 2) =
      fun x ↦ (1 / 2 : ℝ) *
        (Real.cos (α * u) + Real.cos (2 * α * x + α * u)) by
    funext x
    ring]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_const,
      integral_cos_affine (mul_ne_zero (by norm_num) hα)]
    simp only [smul_eq_mul]
    ring
  · exact Continuous.intervalIntegrable continuous_const _ _
  · exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- Exact positive-frequency diagonal even correlation. -/
theorem clippedEvenCorrelation_diag
    {a u : ℝ} (ha : 0 < a) {n : ℕ} (hn : n ≠ 0) :
    clippedEvenCorrelation a n n u =
      ((2 * a - u) * Real.cos (clippedEvenFrequency a n * u) -
        Real.sin (clippedEvenFrequency a n * u) /
          clippedEvenFrequency a n) / (2 * a) := by
  let α := clippedEvenFrequency a n
  have ha0 : a ≠ 0 := ha.ne'
  have hα : α ≠ 0 := by
    dsimp [α, clippedEvenFrequency]
    positivity
  have hsqrt : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have hupper :
      Real.sin (2 * α * (a - u) + α * u) = -Real.sin (α * u) := by
    rw [show 2 * α * (a - u) + α * u =
        (2 * n : ℕ) * Real.pi - α * u by
      dsimp [α, clippedEvenFrequency]
      push_cast
      field_simp [ha0]
      ring]
    rw [Real.sin_nat_mul_pi_sub, pow_mul]
    norm_num
  have hlower :
      Real.sin (2 * α * (-a) + α * u) = Real.sin (α * u) := by
    rw [show 2 * α * (-a) + α * u =
        α * u - (2 * n : ℕ) * Real.pi by
      dsimp [α, clippedEvenFrequency]
      push_cast
      field_simp [ha0]
      ring]
    rw [Real.sin_sub_nat_mul_pi, pow_mul]
    norm_num
  rw [clippedEvenCorrelation]
  simp only [clippedEvenRealMode]
  have hαarg (x : ℝ) : Real.pi * (n : ℝ) * x / a = α * x := by
    dsimp [α, clippedEvenFrequency]
    field_simp [ha0]
  simp_rw [hαarg]
  rw [show (fun x : ℝ ↦
      ((Real.sqrt a)⁻¹ * Real.cos (α * (u + x))) *
        ((Real.sqrt a)⁻¹ * Real.cos (α * x))) =
      fun x ↦ ((Real.sqrt a)⁻¹) ^ 2 *
        (Real.cos (α * (u + x)) * Real.cos (α * x)) by
    funext x
    ring]
  rw [intervalIntegral.integral_const_mul,
    integral_cos_shift_mul_self hα, hupper, hlower]
  rw [show ((Real.sqrt a)⁻¹) ^ 2 = a⁻¹ by
    rw [inv_pow, Real.sq_sqrt ha.le]]
  change _ = ((2 * a - u) * Real.cos (α * u) -
    Real.sin (α * u) / α) / (2 * a)
  field_simp [ha0, hα]
  ring

/-- Exact zero/positive even correlation. -/
theorem clippedEvenZeroPositiveCorrelation_eq
    {a u : ℝ} (ha : 0 < a) {m : ℕ} (hm : m ≠ 0) :
    clippedEvenZeroPositiveCorrelation a m u =
      (-1 : ℝ) ^ (m + 1) * Real.sin (clippedEvenFrequency a m * u) /
        (Real.sqrt 2 * a * clippedEvenFrequency a m) := by
  let β := clippedEvenFrequency a m
  have ha0 : a ≠ 0 := ha.ne'
  have hβ : β ≠ 0 := by
    dsimp [β, clippedEvenFrequency]
    positivity
  have hsqrtA : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have hsqrtTwo : Real.sqrt 2 ≠ 0 := by positivity
  have hsqrtTwoA : Real.sqrt (2 * a) ≠ 0 :=
    (Real.sqrt_pos.2 (mul_pos (by norm_num) ha)).ne'
  have hupper : Real.sin (β * (a - u)) =
      (-1 : ℝ) ^ (m + 1) * Real.sin (β * u) := by
    rw [show β * (a - u) = (m : ℝ) * Real.pi - β * u by
      dsimp [β, clippedEvenFrequency]
      field_simp [ha0]]
    rw [Real.sin_nat_mul_pi_sub, pow_succ]
    ring
  have hlower : Real.sin (β * (-a)) = 0 := by
    rw [show β * (-a) = -(m : ℝ) * Real.pi by
      dsimp [β, clippedEvenFrequency]
      field_simp [ha0]]
    rw [show -(m : ℝ) * Real.pi = -((m : ℝ) * Real.pi) by ring,
      Real.sin_neg, Real.sin_nat_mul_pi]
    simp
  rw [clippedEvenZeroPositiveCorrelation]
  simp only [clippedEvenZeroRealMode, clippedEvenRealMode]
  have hβarg (x : ℝ) : Real.pi * (m : ℝ) * x / a = β * x := by
    dsimp [β, clippedEvenFrequency]
    field_simp [ha0]
  simp_rw [hβarg]
  rw [show (fun x : ℝ ↦
      (Real.sqrt (2 * a))⁻¹ * ((Real.sqrt a)⁻¹ * Real.cos (β * x))) =
      fun x ↦ ((Real.sqrt (2 * a))⁻¹ * (Real.sqrt a)⁻¹) *
        Real.cos (β * x) by
    funext x
    ring]
  rw [intervalIntegral.integral_const_mul]
  rw [show (fun x : ℝ ↦ Real.cos (β * x)) =
      fun x ↦ Real.cos (β * x + 0) by
    funext x
    simp]
  rw [integral_cos_affine hβ]
  simp only [add_zero]
  rw [hupper, hlower]
  change _ = (-1 : ℝ) ^ (m + 1) * Real.sin (β * u) /
    (Real.sqrt 2 * a * β)
  rw [show Real.sqrt (2 * a) = Real.sqrt 2 * Real.sqrt a by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]]
  field_simp [ha0, hβ, hsqrtA, hsqrtTwo]
  rw [Real.sq_sqrt ha.le]
  ring

/-- Exact positive/zero even correlation. -/
theorem clippedEvenPositiveZeroCorrelation_eq
    {a u : ℝ} (ha : 0 < a) {n : ℕ} (hn : n ≠ 0) :
    clippedEvenPositiveZeroCorrelation a n u =
      (-1 : ℝ) ^ (n + 1) * Real.sin (clippedEvenFrequency a n * u) /
        (Real.sqrt 2 * a * clippedEvenFrequency a n) := by
  let α := clippedEvenFrequency a n
  have ha0 : a ≠ 0 := ha.ne'
  have hα : α ≠ 0 := by
    dsimp [α, clippedEvenFrequency]
    positivity
  have hsqrtA : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have hsqrtTwo : Real.sqrt 2 ≠ 0 := by positivity
  have hsqrtTwoA : Real.sqrt (2 * a) ≠ 0 :=
    (Real.sqrt_pos.2 (mul_pos (by norm_num) ha)).ne'
  have hupper : Real.sin (α * (a - u) + α * u) = 0 := by
    rw [show α * (a - u) + α * u = (n : ℝ) * Real.pi by
      dsimp [α, clippedEvenFrequency]
      field_simp [ha0]
      ring]
    exact Real.sin_nat_mul_pi n
  have hlower : Real.sin (α * (-a) + α * u) =
      (-1 : ℝ) ^ n * Real.sin (α * u) := by
    rw [show α * (-a) + α * u =
        α * u - (n : ℝ) * Real.pi by
      dsimp [α, clippedEvenFrequency]
      field_simp [ha0]
      ring]
    exact Real.sin_sub_nat_mul_pi _ _
  rw [clippedEvenPositiveZeroCorrelation]
  simp only [clippedEvenZeroRealMode, clippedEvenRealMode]
  have hαarg (x : ℝ) : Real.pi * (n : ℝ) * x / a = α * x := by
    dsimp [α, clippedEvenFrequency]
    field_simp [ha0]
  simp_rw [hαarg]
  rw [show (fun x : ℝ ↦
      ((Real.sqrt a)⁻¹ * Real.cos (α * (u + x))) *
        (Real.sqrt (2 * a))⁻¹) =
      fun x ↦ ((Real.sqrt a)⁻¹ * (Real.sqrt (2 * a))⁻¹) *
        Real.cos (α * x + α * u) by
    funext x
    rw [show α * (u + x) = α * x + α * u by ring]
    ring]
  rw [intervalIntegral.integral_const_mul,
    integral_cos_affine hα, hupper, hlower]
  rw [show Real.sqrt (2 * a) = Real.sqrt 2 * Real.sqrt a by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]]
  change _ = (-1 : ℝ) ^ (n + 1) * Real.sin (α * u) /
    (Real.sqrt 2 * a * α)
  field_simp [ha0, hα, hsqrtA, hsqrtTwo]
  rw [Real.sq_sqrt ha.le]
  rw [show (-1 : ℝ) ^ (n + 1) = -((-1 : ℝ) ^ n) by
    rw [pow_succ]
    ring]
  ring

/-- Exact zero/zero even correlation. -/
theorem clippedEvenZeroCorrelation_eq
    {a u : ℝ} (ha : 0 < a) :
    clippedEvenZeroCorrelation a u = (2 * a - u) / (2 * a) := by
  have ha0 : a ≠ 0 := ha.ne'
  have hsqrtTwoA : Real.sqrt (2 * a) ≠ 0 :=
    (Real.sqrt_pos.2 (mul_pos (by norm_num) ha)).ne'
  rw [clippedEvenZeroCorrelation]
  simp only [clippedEvenZeroRealMode]
  rw [show (fun _x : ℝ ↦
      (Real.sqrt (2 * a))⁻¹ * (Real.sqrt (2 * a))⁻¹) =
      fun _x ↦ ((Real.sqrt (2 * a))⁻¹) ^ 2 by
    funext x
    ring]
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  rw [show ((Real.sqrt (2 * a))⁻¹) ^ 2 = (2 * a)⁻¹ by
    rw [inv_pow, Real.sq_sqrt (mul_nonneg (by norm_num) ha.le)]]
  field_simp [ha0]
  ring

theorem clippedEvenFrequency_yoshidaHalfLength (n : ℕ) :
    clippedEvenFrequency yoshidaHalfLength n = yoshidaKappa n := by
  rw [clippedEvenFrequency, yoshidaKappa, yoshidaHalfLength]
  field_simp [yoshidaLength_pos.ne']

theorem clippedEvenCorrelation_half_offdiag
    {u : ℝ} {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (hnm : n ≠ m) :
    clippedEvenCorrelation yoshidaHalfLength n m u =
      (2 * (-1 : ℝ) ^ (n + m) / yoshidaLength) *
        (yoshidaKappa m * Real.sin (yoshidaKappa m * u) -
          yoshidaKappa n * Real.sin (yoshidaKappa n * u)) /
        (yoshidaKappa n ^ 2 - yoshidaKappa m ^ 2) := by
  rw [clippedEvenCorrelation_offdiag yoshidaHalfLength_pos hn hm hnm]
  simp only [clippedEvenFrequency_yoshidaHalfLength]
  rw [← two_mul_yoshidaHalfLength]
  ring

theorem clippedEvenCorrelation_half_diag
    {u : ℝ} {n : ℕ} (hn : n ≠ 0) :
    clippedEvenCorrelation yoshidaHalfLength n n u =
      ((yoshidaLength - u) * Real.cos (yoshidaKappa n * u) -
        Real.sin (yoshidaKappa n * u) / yoshidaKappa n) /
        yoshidaLength := by
  rw [clippedEvenCorrelation_diag yoshidaHalfLength_pos hn]
  rw [clippedEvenFrequency_yoshidaHalfLength, two_mul_yoshidaHalfLength]

theorem clippedEvenZeroPositiveCorrelation_half
    {u : ℝ} {m : ℕ} (hm : m ≠ 0) :
    clippedEvenZeroPositiveCorrelation yoshidaHalfLength m u =
      2 * (-1 : ℝ) ^ (m + 1) * Real.sin (yoshidaKappa m * u) /
        (yoshidaLength * Real.sqrt 2 * yoshidaKappa m) := by
  rw [clippedEvenZeroPositiveCorrelation_eq yoshidaHalfLength_pos hm,
    clippedEvenFrequency_yoshidaHalfLength, ← two_mul_yoshidaHalfLength]
  ring

theorem clippedEvenPositiveZeroCorrelation_half
    {u : ℝ} {n : ℕ} (hn : n ≠ 0) :
    clippedEvenPositiveZeroCorrelation yoshidaHalfLength n u =
      2 * (-1 : ℝ) ^ (n + 1) * Real.sin (yoshidaKappa n * u) /
        (yoshidaLength * Real.sqrt 2 * yoshidaKappa n) := by
  rw [clippedEvenPositiveZeroCorrelation_eq yoshidaHalfLength_pos hn,
    clippedEvenFrequency_yoshidaHalfLength, ← two_mul_yoshidaHalfLength]
  ring

theorem clippedEvenZeroCorrelation_half (u : ℝ) :
    clippedEvenZeroCorrelation yoshidaHalfLength u =
      (yoshidaLength - u) / yoshidaLength := by
  rw [clippedEvenZeroCorrelation_eq yoshidaHalfLength_pos,
    two_mul_yoshidaHalfLength]

/-- Unified one-sided even correlation, including the separately normalized
zero mode. -/
def clippedEvenUnifiedCorrelation (n m : ℕ) (u : ℝ) : ℝ :=
  if n = 0 then
    if m = 0 then clippedEvenZeroCorrelation yoshidaHalfLength u
    else clippedEvenZeroPositiveCorrelation yoshidaHalfLength m u
  else if m = 0 then clippedEvenPositiveZeroCorrelation yoshidaHalfLength n u
  else clippedEvenCorrelation yoshidaHalfLength n m u

theorem clippedEvenUnifiedCorrelation_zero
    (n m : ℕ) :
    clippedEvenUnifiedCorrelation n m 0 = if n = m then 1 else 0 := by
  by_cases hn : n = 0
  · subst n
    by_cases hm : m = 0
    · subst m
      simp [clippedEvenUnifiedCorrelation,
        clippedEvenZeroCorrelation_half, yoshidaLength_pos.ne']
    · simp [clippedEvenUnifiedCorrelation, hm, Ne.symm hm,
        clippedEvenZeroPositiveCorrelation_half hm]
  · by_cases hm : m = 0
    · subst m
      simp [clippedEvenUnifiedCorrelation, hn,
        clippedEvenPositiveZeroCorrelation_half hn]
    · by_cases hnm : n = m
      · subst m
        simp [clippedEvenUnifiedCorrelation, hn,
          clippedEvenCorrelation_half_diag hn, yoshidaLength_pos.ne']
      · simp [clippedEvenUnifiedCorrelation, hn, hm, hnm,
          clippedEvenCorrelation_half_offdiag hn hm hnm]

/-- Removable distribution integrand for the unified even correlation.  Its
chosen endpoint value is immaterial to the interval integral; unlike the odd
case, the scalar moment expression agrees only away from zero. -/
def clippedEvenStableCorrelationIntegrand (n m : ℕ) (u : ℝ) : ℝ :=
  yoshidaWeightPlus u * clippedEvenUnifiedCorrelation n m u +
    (clippedEvenUnifiedCorrelation n m 0 -
      clippedEvenUnifiedCorrelation n m u) / u

/-- Admissible real-space value attached to the exact unified even
correlation. -/
def clippedEvenAdmissibleRealSpaceGram (n m : ℕ) : ℝ :=
  (∫ u in 0..yoshidaLength,
      clippedEvenStableCorrelationIntegrand n m u) -
    (Real.log yoshidaLength + Real.eulerMascheroniConstant +
      Real.log 2 + Real.log Real.pi) *
      clippedEvenUnifiedCorrelation n m 0

private theorem yoshidaKappa_ne_zero {n : ℕ} (hn : n ≠ 0) :
    yoshidaKappa n ≠ 0 := by
  rw [yoshidaKappa]
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      (Nat.cast_ne_zero.mpr hn))
    yoshidaLength_pos.ne'

theorem clippedEvenStableCorrelationIntegrand_zero_zero
    {u : ℝ} (hu : u ≠ 0) :
    clippedEvenStableCorrelationIntegrand 0 0 u =
      yoshidaDiagonalMomentIntegrand 0 u := by
  rw [clippedEvenStableCorrelationIntegrand,
    clippedEvenUnifiedCorrelation_zero,
    clippedEvenUnifiedCorrelation, if_pos rfl, if_pos rfl,
    clippedEvenZeroCorrelation_half]
  simp [yoshidaDiagonalMomentIntegrand, yoshidaKappa]
  field_simp [hu, yoshidaLength_pos.ne']
  ring

theorem clippedEvenStableCorrelationIntegrand_zero_positive
    {m : ℕ} (hm : m ≠ 0) {u : ℝ} (hu : u ≠ 0) :
    clippedEvenStableCorrelationIntegrand 0 m u =
      (2 * (-1 : ℝ) ^ (m + 1) /
          (yoshidaLength * Real.sqrt 2 * yoshidaKappa m)) *
        yoshidaSineMomentIntegrand m u := by
  rw [clippedEvenStableCorrelationIntegrand,
    clippedEvenUnifiedCorrelation_zero, if_neg (by omega : 0 ≠ m),
    clippedEvenUnifiedCorrelation, if_pos rfl, if_neg hm,
    clippedEvenZeroPositiveCorrelation_half hm]
  have hκ : yoshidaKappa m ≠ 0 := yoshidaKappa_ne_zero hm
  have hsqrtTwo : Real.sqrt 2 ≠ 0 := by positivity
  rw [yoshidaSineMomentIntegrand,
    Real.sinc_of_ne_zero (mul_ne_zero hκ hu)]
  field_simp [hu, hκ, hsqrtTwo, yoshidaLength_pos.ne']
  ring

theorem clippedEvenStableCorrelationIntegrand_positive_zero
    {n : ℕ} (hn : n ≠ 0) {u : ℝ} (hu : u ≠ 0) :
    clippedEvenStableCorrelationIntegrand n 0 u =
      (2 * (-1 : ℝ) ^ (n + 1) /
          (yoshidaLength * Real.sqrt 2 * yoshidaKappa n)) *
        yoshidaSineMomentIntegrand n u := by
  rw [clippedEvenStableCorrelationIntegrand,
    clippedEvenUnifiedCorrelation_zero, if_neg hn,
    clippedEvenUnifiedCorrelation, if_neg hn, if_pos rfl,
    clippedEvenPositiveZeroCorrelation_half hn]
  have hκ : yoshidaKappa n ≠ 0 := yoshidaKappa_ne_zero hn
  have hsqrtTwo : Real.sqrt 2 ≠ 0 := by positivity
  rw [yoshidaSineMomentIntegrand,
    Real.sinc_of_ne_zero (mul_ne_zero hκ hu)]
  field_simp [hu, hκ, hsqrtTwo, yoshidaLength_pos.ne']
  ring

theorem clippedEvenStableCorrelationIntegrand_diag
    {n : ℕ} (hn : n ≠ 0) {u : ℝ} (hu : u ≠ 0) :
    clippedEvenStableCorrelationIntegrand n n u =
      yoshidaDiagonalMomentIntegrand n u -
        yoshidaSineMomentIntegrand n u /
          (yoshidaLength * yoshidaKappa n) := by
  rw [clippedEvenStableCorrelationIntegrand,
    clippedEvenUnifiedCorrelation_zero, if_pos rfl,
    clippedEvenUnifiedCorrelation, if_neg hn, if_neg hn,
    clippedEvenCorrelation_half_diag hn]
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

theorem clippedEvenStableCorrelationIntegrand_offdiag
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (hnm : n ≠ m)
    {u : ℝ} (hu : u ≠ 0) :
    clippedEvenStableCorrelationIntegrand n m u =
      (2 * (-1 : ℝ) ^ (n + m) / yoshidaLength) *
        (yoshidaKappa m * yoshidaSineMomentIntegrand m u -
          yoshidaKappa n * yoshidaSineMomentIntegrand n u) /
        (yoshidaKappa n ^ 2 - yoshidaKappa m ^ 2) := by
  rw [clippedEvenStableCorrelationIntegrand,
    clippedEvenUnifiedCorrelation_zero, if_neg hnm,
    clippedEvenUnifiedCorrelation, if_neg hn, if_neg hm,
    clippedEvenCorrelation_half_offdiag hn hm hnm]
  have hκn : yoshidaKappa n ≠ 0 := yoshidaKappa_ne_zero hn
  have hκm : yoshidaKappa m ≠ 0 := yoshidaKappa_ne_zero hm
  rw [yoshidaSineMomentIntegrand, yoshidaSineMomentIntegrand,
    Real.sinc_of_ne_zero (mul_ne_zero hκm hu),
    Real.sinc_of_ne_zero (mul_ne_zero hκn hu)]
  field_simp [hu, hκn, hκm]
  ring

theorem clippedEvenAdmissibleRealSpaceGram_zero_zero :
    clippedEvenAdmissibleRealSpaceGram 0 0 =
      evenMomentGram yoshidaSineMoment yoshidaDiagonalMoment 0 0 := by
  have hint :
      (∫ u in 0..yoshidaLength,
          clippedEvenStableCorrelationIntegrand 0 0 u) =
        ∫ u in 0..yoshidaLength, yoshidaDiagonalMomentIntegrand 0 u := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [show ∀ᵐ u : ℝ ∂volume, u ≠ 0 by
      simp [ae_iff, measure_singleton]] with u hu
    intro _
    exact clippedEvenStableCorrelationIntegrand_zero_zero hu
  rw [clippedEvenAdmissibleRealSpaceGram, hint,
    clippedEvenUnifiedCorrelation_zero, if_pos rfl,
    evenMomentGram_zero_zero, yoshidaDiagonalMoment]
  ring

theorem clippedEvenAdmissibleRealSpaceGram_zero_positive
    {m : ℕ} (hm : m ≠ 0) :
    clippedEvenAdmissibleRealSpaceGram 0 m =
      evenMomentGram yoshidaSineMoment yoshidaDiagonalMoment 0 m := by
  let c : ℝ := 2 * (-1 : ℝ) ^ (m + 1) /
    (yoshidaLength * Real.sqrt 2 * yoshidaKappa m)
  have hint :
      (∫ u in 0..yoshidaLength,
          clippedEvenStableCorrelationIntegrand 0 m u) =
        ∫ u in 0..yoshidaLength,
          c * yoshidaSineMomentIntegrand m u := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [show ∀ᵐ u : ℝ ∂volume, u ≠ 0 by
      simp [ae_iff, measure_singleton]] with u hu
    intro _
    exact clippedEvenStableCorrelationIntegrand_zero_positive hm hu
  rw [clippedEvenAdmissibleRealSpaceGram, hint,
    intervalIntegral.integral_const_mul,
    clippedEvenUnifiedCorrelation_zero, if_neg (by omega : 0 ≠ m),
    mul_zero, sub_zero, evenMomentGram, if_pos rfl, if_neg hm,
    yoshidaSineMoment]
  dsimp [c]
  ring

theorem clippedEvenAdmissibleRealSpaceGram_positive_zero
    {n : ℕ} (hn : n ≠ 0) :
    clippedEvenAdmissibleRealSpaceGram n 0 =
      evenMomentGram yoshidaSineMoment yoshidaDiagonalMoment n 0 := by
  let c : ℝ := 2 * (-1 : ℝ) ^ (n + 1) /
    (yoshidaLength * Real.sqrt 2 * yoshidaKappa n)
  have hint :
      (∫ u in 0..yoshidaLength,
          clippedEvenStableCorrelationIntegrand n 0 u) =
        ∫ u in 0..yoshidaLength,
          c * yoshidaSineMomentIntegrand n u := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [show ∀ᵐ u : ℝ ∂volume, u ≠ 0 by
      simp [ae_iff, measure_singleton]] with u hu
    intro _
    exact clippedEvenStableCorrelationIntegrand_positive_zero hn hu
  rw [clippedEvenAdmissibleRealSpaceGram, hint,
    intervalIntegral.integral_const_mul,
    clippedEvenUnifiedCorrelation_zero, if_neg hn,
    mul_zero, sub_zero, evenMomentGram, if_neg hn, if_pos rfl,
    yoshidaSineMoment]
  dsimp [c]
  ring

theorem clippedEvenAdmissibleRealSpaceGram_diag
    {n : ℕ} (hn : n ≠ 0) :
    clippedEvenAdmissibleRealSpaceGram n n =
      evenMomentGram yoshidaSineMoment yoshidaDiagonalMoment n n := by
  let c : ℝ := (yoshidaLength * yoshidaKappa n)⁻¹
  have hint :
      (∫ u in 0..yoshidaLength,
          clippedEvenStableCorrelationIntegrand n n u) =
        ∫ u in 0..yoshidaLength,
          (yoshidaDiagonalMomentIntegrand n u -
            c * yoshidaSineMomentIntegrand n u) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [show ∀ᵐ u : ℝ ∂volume, u ≠ 0 by
      simp [ae_iff, measure_singleton]] with u hu
    intro _
    rw [clippedEvenStableCorrelationIntegrand_diag hn hu]
    dsimp [c]
    ring
  rw [clippedEvenAdmissibleRealSpaceGram, hint,
    intervalIntegral.integral_sub
      (yoshidaDiagonalMomentIntegrand_intervalIntegrable n)
      ((yoshidaSineMomentIntegrand_intervalIntegrable hn).const_mul c),
    intervalIntegral.integral_const_mul,
    clippedEvenUnifiedCorrelation_zero, if_pos rfl,
    evenMomentGram, if_neg hn, if_neg hn, if_pos rfl,
    yoshidaDiagonalMoment, yoshidaSineMoment]
  dsimp [c]
  ring

theorem clippedEvenAdmissibleRealSpaceGram_offdiag
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (hnm : n ≠ m) :
    clippedEvenAdmissibleRealSpaceGram n m =
      evenMomentGram yoshidaSineMoment yoshidaDiagonalMoment n m := by
  let C : ℝ :=
    (2 * (-1 : ℝ) ^ (n + m) / yoshidaLength) /
      (yoshidaKappa n ^ 2 - yoshidaKappa m ^ 2)
  have hint :
      (∫ u in 0..yoshidaLength,
          clippedEvenStableCorrelationIntegrand n m u) =
        ∫ u in 0..yoshidaLength,
          C * (yoshidaKappa m * yoshidaSineMomentIntegrand m u -
            yoshidaKappa n * yoshidaSineMomentIntegrand n u) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [show ∀ᵐ u : ℝ ∂volume, u ≠ 0 by
      simp [ae_iff, measure_singleton]] with u hu
    intro _
    rw [clippedEvenStableCorrelationIntegrand_offdiag hn hm hnm hu]
    dsimp [C]
    ring
  rw [clippedEvenAdmissibleRealSpaceGram, hint,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub
      ((yoshidaSineMomentIntegrand_intervalIntegrable hm).const_mul
        (yoshidaKappa m))
      ((yoshidaSineMomentIntegrand_intervalIntegrable hn).const_mul
        (yoshidaKappa n)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    clippedEvenUnifiedCorrelation_zero, if_neg hnm,
    mul_zero, sub_zero,
    evenMomentGram, if_neg hn, if_neg hm, if_neg hnm,
    yoshidaSineMoment]
  simp only [yoshidaSineMoment]
  dsimp [C]
  ring

/-- Exact real-space moment identity for every pair of even frequencies,
including the separately normalized zero mode. -/
theorem clippedEvenAdmissibleRealSpaceGram_eq_evenMomentGram (n m : ℕ) :
    clippedEvenAdmissibleRealSpaceGram n m =
      evenMomentGram yoshidaSineMoment yoshidaDiagonalMoment n m := by
  by_cases hn : n = 0
  · subst n
    by_cases hm : m = 0
    · subst m
      exact clippedEvenAdmissibleRealSpaceGram_zero_zero
    · exact clippedEvenAdmissibleRealSpaceGram_zero_positive hm
  · by_cases hm : m = 0
    · subst m
      exact clippedEvenAdmissibleRealSpaceGram_positive_zero hn
    · by_cases hnm : n = m
      · subst m
        exact clippedEvenAdmissibleRealSpaceGram_diag hn
      · exact clippedEvenAdmissibleRealSpaceGram_offdiag hn hm hnm

/-- The remaining analytic boundary: the production clipped critical form
must be assembled into the exact admissible real-space value. -/
def ClippedEvenFullAdmissibleDistributionBridge : Prop :=
  ∀ i j : YoshidaEvenIndex,
    clippedEvenFullGram i j =
      (clippedEvenAdmissibleRealSpaceGram i.1 j.1 : ℂ)

/-- Once the spectral-to-admissible-distribution identity is supplied, all
cosine/zero correlation and removable-moment algebra yields the production
full even moment bridge. -/
theorem clippedEvenFullMomentBridge_of_admissibleDistributionBridge
    (hdist : ClippedEvenFullAdmissibleDistributionBridge) :
    ClippedEvenFullMomentBridge := by
  intro i j
  rw [hdist i j]
  norm_cast
  unfold evenMomentFullGram
  exact clippedEvenAdmissibleRealSpaceGram_eq_evenMomentGram i.1 j.1

end


end ArithmeticHodge.Analysis.YoshidaClippedEvenMomentBridge
