import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteEvenPerturbationAdaptation
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseAlternatingCoercivity

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteAlternatingFormula

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaClippedMomentBridge
open YoshidaCoercivityNumerics
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointScaledCorrelation
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseAlternatingCoercivity
open YoshidaFactorTwoPhaseConcreteEvenPerturbationAdaptation
open YoshidaFactorTwoPhaseConcreteLowMatrix
open YoshidaFactorTwoPhaseEndpointAdaptedLow
open YoshidaFactorTwoPhaseEnvelope
open YoshidaWeightedTailBounds

/-!
# Exact entries of the concrete alternating block

The ordered even--odd correlation has three elementary trigonometric forms:
one for the even zero mode, one on the positive-frequency diagonal, and one
off the diagonal.  Endpoint adaptation then subtracts one shared frequency
`200` row.
-/

/-- The globally continuous normalized centered sine mode of positive
frequency `m`. -/
def factorTwoCenteredCanonicalOddProfile (m : ℕ) : ℝ → ℝ :=
  fun x ↦ (Real.sqrt yoshidaA)⁻¹ *
    Real.sin (Real.pi * (m : ℝ) * x)

theorem continuous_factorTwoCenteredCanonicalOddProfile (m : ℕ) :
    Continuous (factorTwoCenteredCanonicalOddProfile m) := by
  unfold factorTwoCenteredCanonicalOddProfile
  fun_prop

/-- Closed form for the ordered correlation of canonical centered even and
odd modes.  The odd frequency is assumed positive by the theorems below. -/
def factorTwoCanonicalEvenOddCrossFormula
    (n : FactorTwoCanonicalEvenIndex) (m : ℕ) (t : ℝ) : ℝ :=
  if n.1 = 0 then
    (-1 : ℝ) ^ m * (1 - Real.cos (Real.pi * (m : ℝ) * t)) /
      (Real.sqrt 2 * yoshidaA * Real.pi * (m : ℝ))
  else if n.1 = m then
    -(2 - t) * Real.sin (Real.pi * (m : ℝ) * t) /
      (2 * yoshidaA)
  else
    (-1 : ℝ) ^ (n.1 + m) * (m : ℝ) *
        (Real.cos (Real.pi * (n.1 : ℝ) * t) -
          Real.cos (Real.pi * (m : ℝ) * t)) /
      (yoshidaA * Real.pi *
        ((m : ℝ) ^ 2 - (n.1 : ℝ) ^ 2))

private theorem integral_sin_affine
    {a b l r : ℝ} (ha : a ≠ 0) :
    (∫ x : ℝ in l..r, Real.sin (a * x + b)) =
      (-Real.cos (a * r + b) + Real.cos (a * l + b)) / a := by
  let F : ℝ → ℝ := fun x ↦ -Real.cos (a * x + b) / a
  have hderiv (x : ℝ) : HasDerivAt F (Real.sin (a * x + b)) x := by
    have hinner : HasDerivAt (fun y : ℝ ↦ a * y + b) a x := by
      simpa [add_comm] using
        (((hasDerivAt_id x).const_mul a).const_add b)
    have hcos := (Real.hasDerivAt_cos (a * x + b)).comp x hinner
    dsimp only [F]
    convert hcos.neg.div_const a using 1
    field_simp [ha]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _hx ↦ hderiv x) (Continuous.intervalIntegrable (by fun_prop) l r)]
  dsimp only [F]
  field_simp [ha]
  ring

private theorem integral_cos_shift_mul_sin
    {a alpha beta u : ℝ}
    (hsub : beta - alpha ≠ 0) (hadd : beta + alpha ≠ 0) :
    (∫ x : ℝ in -a..a - u,
        Real.cos (alpha * (u + x)) * Real.sin (beta * x)) =
      ((-Real.cos ((beta - alpha) * (a - u) - alpha * u) +
            Real.cos ((beta - alpha) * (-a) - alpha * u)) /
          (beta - alpha) +
        (-Real.cos ((beta + alpha) * (a - u) + alpha * u) +
            Real.cos ((beta + alpha) * (-a) + alpha * u)) /
          (beta + alpha)) / 2 := by
  have hpoint : (fun x : ℝ ↦
      Real.cos (alpha * (u + x)) * Real.sin (beta * x)) =
      fun x ↦ (Real.sin ((beta - alpha) * x - alpha * u) +
        Real.sin ((beta + alpha) * x + alpha * u)) / 2 := by
    funext x
    apply (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).2
    calc
      Real.cos (alpha * (u + x)) * Real.sin (beta * x) * 2 =
          2 * Real.sin (beta * x) * Real.cos (alpha * (u + x)) := by ring
      _ = Real.sin (beta * x - alpha * (u + x)) +
          Real.sin (beta * x + alpha * (u + x)) :=
        Real.two_mul_sin_mul_cos _ _
      _ = _ := by
        rw [show beta * x - alpha * (u + x) =
              (beta - alpha) * x - alpha * u by ring,
          show beta * x + alpha * (u + x) =
              (beta + alpha) * x + alpha * u by ring]
  rw [hpoint]
  rw [show (fun x : ℝ ↦
      (Real.sin ((beta - alpha) * x - alpha * u) +
        Real.sin ((beta + alpha) * x + alpha * u)) / 2) =
      fun x ↦ (1 / 2 : ℝ) *
        (Real.sin ((beta - alpha) * x + (-alpha * u)) +
          Real.sin ((beta + alpha) * x + alpha * u)) by
    funext x
    ring]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    integral_sin_affine hsub, integral_sin_affine hadd]
  ring

private theorem integral_sin_nat_pi
    (m : ℕ) (hm : m ≠ 0) (t : ℝ) :
    (∫ x : ℝ in -1..1 - t,
        Real.sin (Real.pi * (m : ℝ) * x)) =
      (-1 : ℝ) ^ m *
        (1 - Real.cos (Real.pi * (m : ℝ) * t)) /
          (Real.pi * (m : ℝ)) := by
  let beta : ℝ := Real.pi * (m : ℝ)
  have hbeta : beta ≠ 0 := by
    dsimp only [beta]
    exact mul_ne_zero Real.pi_ne_zero (Nat.cast_ne_zero.mpr hm)
  have hupper : Real.cos (beta * (1 - t)) =
      (-1 : ℝ) ^ m * Real.cos (beta * t) := by
    rw [show beta * (1 - t) = (m : ℝ) * Real.pi - beta * t by
      dsimp only [beta]
      ring]
    exact Real.cos_nat_mul_pi_sub _ _
  have hlower : Real.cos (beta * (-1)) = (-1 : ℝ) ^ m := by
    rw [show beta * (-1) = -((m : ℝ) * Real.pi) by
      dsimp only [beta]
      ring,
      Real.cos_neg, Real.cos_nat_mul_pi]
  rw [show (fun x : ℝ ↦ Real.sin (Real.pi * (m : ℝ) * x)) =
      fun x ↦ Real.sin (beta * x + 0) by
    funext x
    apply congrArg Real.sin
    dsimp only [beta]
    ring,
    integral_sin_affine hbeta]
  simp only [add_zero]
  rw [hupper, hlower]
  dsimp only [beta]
  ring

private theorem integral_cos_shift_mul_sin_diag
    (m : ℕ) (hm : m ≠ 0) (t : ℝ) :
    (∫ x : ℝ in -1..1 - t,
        Real.cos (Real.pi * (m : ℝ) * (t + x)) *
          Real.sin (Real.pi * (m : ℝ) * x)) =
      -(2 - t) * Real.sin (Real.pi * (m : ℝ) * t) / 2 := by
  let beta : ℝ := Real.pi * (m : ℝ)
  have hbeta : beta ≠ 0 := by
    dsimp only [beta]
    exact mul_ne_zero Real.pi_ne_zero (Nat.cast_ne_zero.mpr hm)
  have htwoBeta : 2 * beta ≠ 0 := mul_ne_zero (by norm_num) hbeta
  have hupper : Real.cos (2 * beta * (1 - t) + beta * t) =
      Real.cos (beta * t) := by
    rw [show 2 * beta * (1 - t) + beta * t =
        -(beta * t) + (m : ℝ) * (2 * Real.pi) by
      dsimp only [beta]
      ring,
      Real.cos_add_nat_mul_two_pi, Real.cos_neg]
  have hlower : Real.cos (2 * beta * (-1) + beta * t) =
      Real.cos (beta * t) := by
    rw [show 2 * beta * (-1) + beta * t =
        beta * t - (m : ℝ) * (2 * Real.pi) by
      dsimp only [beta]
      ring,
      Real.cos_sub_nat_mul_two_pi]
  have hosc :
      (∫ x : ℝ in -1..1 - t,
          Real.sin (2 * beta * x + beta * t)) = 0 := by
    rw [integral_sin_affine htwoBeta, hupper, hlower]
    ring
  have hconst :
      (∫ _x : ℝ in -1..1 - t, Real.sin (beta * t)) =
        (2 - t) * Real.sin (beta * t) := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  have hpoint : (fun x : ℝ ↦
      Real.cos (beta * (t + x)) * Real.sin (beta * x)) =
      fun x ↦ (Real.sin (2 * beta * x + beta * t) -
        Real.sin (beta * t)) / 2 := by
    funext x
    apply (eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)).2
    calc
      Real.cos (beta * (t + x)) * Real.sin (beta * x) * 2 =
          2 * Real.sin (beta * x) * Real.cos (beta * (t + x)) := by ring
      _ = Real.sin (beta * x - beta * (t + x)) +
          Real.sin (beta * x + beta * (t + x)) :=
        Real.two_mul_sin_mul_cos _ _
      _ = _ := by
        rw [show beta * x - beta * (t + x) = -(beta * t) by ring,
          Real.sin_neg,
          show beta * x + beta * (t + x) =
            2 * beta * x + beta * t by ring]
        ring
  rw [show (fun x : ℝ ↦
      Real.cos (Real.pi * (m : ℝ) * (t + x)) *
        Real.sin (Real.pi * (m : ℝ) * x)) =
      fun x ↦ Real.cos (beta * (t + x)) * Real.sin (beta * x) by
    funext x
    rfl,
    hpoint]
  rw [show (fun x : ℝ ↦
      (Real.sin (2 * beta * x + beta * t) - Real.sin (beta * t)) / 2) =
      fun x ↦ (1 / 2 : ℝ) *
        (Real.sin (2 * beta * x + beta * t) - Real.sin (beta * t)) by
    funext x
    ring,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub
      (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable continuous_const _ _),
    hosc, hconst]
  dsimp only [beta]
  ring

private theorem integral_cos_shift_mul_sin_offdiag
    (n m : ℕ) (hn : n ≠ 0) (hm : m ≠ 0) (hnm : n ≠ m)
    (t : ℝ) :
    (∫ x : ℝ in -1..1 - t,
        Real.cos (Real.pi * (n : ℝ) * (t + x)) *
          Real.sin (Real.pi * (m : ℝ) * x)) =
      (-1 : ℝ) ^ (n + m) * (m : ℝ) *
          (Real.cos (Real.pi * (n : ℝ) * t) -
            Real.cos (Real.pi * (m : ℝ) * t)) /
        (Real.pi * ((m : ℝ) ^ 2 - (n : ℝ) ^ 2)) := by
  let alpha : ℝ := Real.pi * (n : ℝ)
  let beta : ℝ := Real.pi * (m : ℝ)
  have halpha : 0 < alpha := by
    dsimp only [alpha]
    positivity
  have hbeta : 0 < beta := by
    dsimp only [beta]
    positivity
  have hsub : beta - alpha ≠ 0 := by
    intro h
    apply hnm
    have hcast : (n : ℝ) = (m : ℝ) := by
      apply mul_left_cancel₀ Real.pi_ne_zero
      dsimp only [alpha, beta] at h
      linarith
    exact_mod_cast hcast
  have hadd : beta + alpha ≠ 0 := by positivity
  have hqsub :
      Real.cos ((beta - alpha) * (1 - t) - alpha * t) =
        (-1 : ℝ) ^ (n + m) * Real.cos (beta * t) := by
    rw [show (beta - alpha) * (1 - t) - alpha * t =
        ((m : ℝ) * Real.pi - beta * t) - (n : ℝ) * Real.pi by
      dsimp only [alpha, beta]
      ring,
      Real.cos_sub_nat_mul_pi, Real.cos_nat_mul_pi_sub, pow_add]
    ring
  have hpsub :
      Real.cos ((beta - alpha) * (-1) - alpha * t) =
        (-1 : ℝ) ^ (n + m) * Real.cos (alpha * t) := by
    rw [show (beta - alpha) * (-1) - alpha * t =
        ((n : ℝ) * Real.pi - alpha * t) - (m : ℝ) * Real.pi by
      dsimp only [alpha, beta]
      ring,
      Real.cos_sub_nat_mul_pi, Real.cos_nat_mul_pi_sub, pow_add]
    ring
  have hqadd :
      Real.cos ((beta + alpha) * (1 - t) + alpha * t) =
        (-1 : ℝ) ^ (n + m) * Real.cos (beta * t) := by
    rw [show (beta + alpha) * (1 - t) + alpha * t =
        ((n + m : ℕ) : ℝ) * Real.pi - beta * t by
      dsimp only [alpha, beta]
      push_cast
      ring,
      Real.cos_nat_mul_pi_sub]
  have hpadd :
      Real.cos ((beta + alpha) * (-1) + alpha * t) =
        (-1 : ℝ) ^ (n + m) * Real.cos (alpha * t) := by
    rw [show (beta + alpha) * (-1) + alpha * t =
        alpha * t - ((n + m : ℕ) : ℝ) * Real.pi by
      dsimp only [alpha, beta]
      push_cast
      ring,
      Real.cos_sub_nat_mul_pi]
  have hmn : (m : ℝ) ≠ (n : ℝ) := by
    exact_mod_cast Ne.symm hnm
  have hsquares : (m : ℝ) ^ 2 - (n : ℝ) ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero (by positivity) (sub_ne_zero.mpr hmn)
  rw [show (fun x : ℝ ↦
      Real.cos (Real.pi * (n : ℝ) * (t + x)) *
        Real.sin (Real.pi * (m : ℝ) * x)) =
      fun x ↦ Real.cos (alpha * (t + x)) * Real.sin (beta * x) by
    funext x
    rfl,
    integral_cos_shift_mul_sin (a := 1) hsub hadd,
    hqsub, hpsub, hqadd, hpadd]
  have hden : beta ^ 2 - alpha ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero hadd hsub
  calc
    _ = (-1 : ℝ) ^ (n + m) * beta *
          (Real.cos (alpha * t) - Real.cos (beta * t)) /
            (beta ^ 2 - alpha ^ 2) := by
      field_simp [hsub, hadd, hden]
      ring
    _ = _ := by
      dsimp only [alpha, beta]
      field_simp [hsquares, Real.pi_ne_zero]

/-- Exact three-branch ordered correlation of a canonical centered even mode
with a positive-frequency canonical centered odd mode. -/
theorem factorTwoCenteredCrossCorrelation_canonicalEven_odd_eq_formula
    (n : FactorTwoCanonicalEvenIndex) (m : ℕ) (hm : m ≠ 0)
    (t : ℝ) (_ht0 : 0 ≤ t) (_ht2 : t ≤ 2) :
    factorTwoCenteredCrossCorrelation
        (factorTwoCenteredCanonicalEvenProfile n)
        (factorTwoCenteredCanonicalOddProfile m) t =
      factorTwoCanonicalEvenOddCrossFormula n m t := by
  have hsqrtA : Real.sqrt yoshidaA ≠ 0 :=
    (Real.sqrt_pos.2 yoshidaA_pos).ne'
  have hsqrtTwo : Real.sqrt 2 ≠ 0 := by positivity
  have hsqrtTwoA : Real.sqrt (2 * yoshidaA) ≠ 0 :=
    (Real.sqrt_pos.2 (mul_pos (by norm_num) yoshidaA_pos)).ne'
  have hsqrtMul : Real.sqrt (2 * yoshidaA) =
      Real.sqrt 2 * Real.sqrt yoshidaA := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  by_cases hn : n.1 = 0
  · rw [factorTwoCanonicalEvenOddCrossFormula, if_pos hn]
    unfold factorTwoCenteredCrossCorrelation
      factorTwoCenteredCanonicalEvenProfile
      factorTwoCenteredCanonicalOddProfile
    rw [if_pos hn]
    rw [show (fun x : ℝ ↦
        (Real.sqrt (2 * yoshidaA))⁻¹ *
          ((Real.sqrt yoshidaA)⁻¹ *
            Real.sin (Real.pi * (m : ℝ) * x))) =
        fun x ↦ ((Real.sqrt (2 * yoshidaA))⁻¹ *
          (Real.sqrt yoshidaA)⁻¹) *
            Real.sin (Real.pi * (m : ℝ) * x) by
      funext x
      ring,
      intervalIntegral.integral_const_mul,
      integral_sin_nat_pi m hm t,
      hsqrtMul]
    rw [show (Real.sqrt 2 * Real.sqrt yoshidaA)⁻¹ *
        (Real.sqrt yoshidaA)⁻¹ =
        1 / (Real.sqrt 2 * yoshidaA) by
      field_simp [hsqrtA, hsqrtTwo]
      rw [Real.sq_sqrt yoshidaA_pos.le]
      rw [div_self yoshidaA_pos.ne']]
    field_simp [yoshidaA_pos.ne']
  · by_cases hnm : n.1 = m
    · rw [factorTwoCanonicalEvenOddCrossFormula, if_neg hn, if_pos hnm]
      unfold factorTwoCenteredCrossCorrelation
        factorTwoCenteredCanonicalEvenProfile
        factorTwoCenteredCanonicalOddProfile
      rw [if_neg hn]
      rw [show (fun x : ℝ ↦
          ((Real.sqrt yoshidaA)⁻¹ *
              Real.cos (Real.pi * (n.1 : ℝ) * (t + x))) *
            ((Real.sqrt yoshidaA)⁻¹ *
              Real.sin (Real.pi * (m : ℝ) * x))) =
          fun x ↦ ((Real.sqrt yoshidaA)⁻¹) ^ 2 *
            (Real.cos (Real.pi * (m : ℝ) * (t + x)) *
              Real.sin (Real.pi * (m : ℝ) * x)) by
        funext x
        rw [hnm]
        ring,
        intervalIntegral.integral_const_mul,
        integral_cos_shift_mul_sin_diag m hm t,
        show ((Real.sqrt yoshidaA)⁻¹) ^ 2 = yoshidaA⁻¹ by
          rw [inv_pow, Real.sq_sqrt yoshidaA_pos.le]]
      field_simp [yoshidaA_pos.ne']

    · rw [factorTwoCanonicalEvenOddCrossFormula, if_neg hn, if_neg hnm]
      unfold factorTwoCenteredCrossCorrelation
        factorTwoCenteredCanonicalEvenProfile
        factorTwoCenteredCanonicalOddProfile
      rw [if_neg hn]
      rw [show (fun x : ℝ ↦
          ((Real.sqrt yoshidaA)⁻¹ *
              Real.cos (Real.pi * (n.1 : ℝ) * (t + x))) *
            ((Real.sqrt yoshidaA)⁻¹ *
              Real.sin (Real.pi * (m : ℝ) * x))) =
          fun x ↦ ((Real.sqrt yoshidaA)⁻¹) ^ 2 *
            (Real.cos (Real.pi * (n.1 : ℝ) * (t + x)) *
              Real.sin (Real.pi * (m : ℝ) * x)) by
        funext x
        ring,
        intervalIntegral.integral_const_mul,
        integral_cos_shift_mul_sin_offdiag n.1 m hn hm hnm t,
        show ((Real.sqrt yoshidaA)⁻¹) ^ 2 = yoshidaA⁻¹ by
          rw [inv_pow, Real.sq_sqrt yoshidaA_pos.le]]
      field_simp [yoshidaA_pos.ne']

/-- On the centered endpoint interval, the production odd low profile agrees
with its global canonical sine representative. -/
theorem factorTwoCenteredOddLowProfile_eq_canonical
    (j : YoshidaOddIndex) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    factorTwoCenteredOddLowProfile j x =
      factorTwoCenteredCanonicalOddProfile (j.1 + 1) x := by
  have hAx : yoshidaA * x ∈ Set.Icc (-yoshidaA) yoshidaA := by
    constructor
    · nlinarith [yoshidaA_pos, hx.1]
    · nlinarith [yoshidaA_pos, hx.2]
  have hargC :
      (Real.pi : ℂ) * ((j.1 : ℂ) + 1) *
          ((yoshidaA : ℂ) * (x : ℂ)) / (yoshidaA : ℂ) =
        ((Real.pi * ((j.1 : ℝ) + 1) * x : ℝ) : ℂ) := by
    push_cast
    field_simp [yoshidaA_pos.ne']
  simp [factorTwoCenteredOddLowProfile, centeredRescale,
    yoshidaClippedOddLowMode, factorTwoCenteredCanonicalOddProfile,
    yoshidaClippedOddMode_apply_of_mem yoshidaA_pos (j.1 + 1) hAx]
  left
  rw [hargC, Complex.sin_ofReal_re]

/-- A global even representative of the endpoint-adapted low mode. -/
def factorTwoCenteredCanonicalAdaptedEvenProfile
    (i : YoshidaEvenIndex) : ℝ → ℝ :=
  factorTwoCenteredCanonicalEvenProfile
      (factorTwoCanonicalEvenLowIndex i) +
    (-endpointEvenLowTraceRatio i) •
      factorTwoCenteredCanonicalEvenProfile factorTwoCanonicalEvenTopIndex

/-- Endpoint adaptation subtracts the trace-ratio multiple of the shared
frequency-`200` ordered correlation. -/
def factorTwoAdaptedEvenOddCrossFormula
    (i : YoshidaEvenIndex) (m : ℕ) (t : ℝ) : ℝ :=
  factorTwoCanonicalEvenOddCrossFormula
      (factorTwoCanonicalEvenLowIndex i) m t -
    endpointEvenLowTraceRatio i *
      factorTwoCanonicalEvenOddCrossFormula
        factorTwoCanonicalEvenTopIndex m t

private theorem factorTwoCenteredCrossCorrelation_congr_Icc
    {u u' v v' : ℝ → ℝ}
    (hu : ∀ x ∈ Set.Icc (-1 : ℝ) 1, u x = u' x)
    (hv : ∀ x ∈ Set.Icc (-1 : ℝ) 1, v x = v' x)
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    factorTwoCenteredCrossCorrelation u v t =
      factorTwoCenteredCrossCorrelation u' v' t := by
  unfold factorTwoCenteredCrossCorrelation
  apply intervalIntegral.integral_congr
  intro x hx
  rw [Set.uIcc_of_le (by linarith : (-1 : ℝ) ≤ 1 - t)] at hx
  have hxIcc : x ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  have htxIcc : t + x ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  change u (t + x) * v x = u' (t + x) * v' x
  rw [hu (t + x) htxIcc, hv x hxIcc]

/-- On the overlap range, the concrete endpoint-adapted even--odd ordered
correlation is the canonical low-frequency formula minus its trace-ratio
multiple of the frequency-`200` formula. -/
theorem factorTwoCenteredCrossCorrelation_adaptedEven_oddLow_eq_formula
    (i : YoshidaEvenIndex) (j : YoshidaOddIndex) (t : ℝ)
    (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    factorTwoCenteredCrossCorrelation
        (factorTwoCenteredAdaptedEvenLowProfile i)
        (factorTwoCenteredOddLowProfile j) t =
      factorTwoAdaptedEvenOddCrossFormula i (j.1 + 1) t := by
  have hm : j.1 + 1 ≠ 0 := by omega
  have heqEven : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      factorTwoCenteredAdaptedEvenLowProfile i x =
        factorTwoCenteredCanonicalAdaptedEvenProfile i x := by
    intro x hx
    rw [factorTwoCenteredAdaptedEvenLowProfile_eq_canonical_sub i hx]
    simp only [factorTwoCenteredCanonicalAdaptedEvenProfile,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have heqOdd : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      factorTwoCenteredOddLowProfile j x =
        factorTwoCenteredCanonicalOddProfile (j.1 + 1) x :=
    fun x hx ↦ factorTwoCenteredOddLowProfile_eq_canonical j hx
  rw [factorTwoCenteredCrossCorrelation_congr_Icc
    heqEven heqOdd ht0 ht2]
  unfold factorTwoCenteredCanonicalAdaptedEvenProfile
  rw [factorTwoCenteredCrossCorrelation_add_left
      (factorTwoCenteredCanonicalEvenProfile
        (factorTwoCanonicalEvenLowIndex i))
      ((-endpointEvenLowTraceRatio i) •
        factorTwoCenteredCanonicalEvenProfile
          factorTwoCanonicalEvenTopIndex)
      (factorTwoCenteredCanonicalOddProfile (j.1 + 1))
      (continuous_factorTwoCenteredCanonicalEvenProfile _)
      (by
        simpa only [Pi.smul_apply] using
          (continuous_factorTwoCenteredCanonicalEvenProfile
            factorTwoCanonicalEvenTopIndex).const_smul
              (-endpointEvenLowTraceRatio i))
      (continuous_factorTwoCenteredCanonicalOddProfile _) t,
    factorTwoCenteredCrossCorrelation_smul_left,
    factorTwoCenteredCrossCorrelation_canonicalEven_odd_eq_formula
      (factorTwoCanonicalEvenLowIndex i) (j.1 + 1) hm t ht0 ht2,
    factorTwoCenteredCrossCorrelation_canonicalEven_odd_eq_formula
      factorTwoCanonicalEvenTopIndex (j.1 + 1) hm t ht0 ht2]
  unfold factorTwoAdaptedEvenOddCrossFormula
  ring

theorem factorTwoCenteredCanonicalEvenProfile_even
    (n : FactorTwoCanonicalEvenIndex) :
    Function.Even (factorTwoCenteredCanonicalEvenProfile n) := by
  intro x
  unfold factorTwoCenteredCanonicalEvenProfile
  split_ifs
  · rfl
  · change (Real.sqrt yoshidaA)⁻¹ *
        Real.cos (Real.pi * (n.1 : ℝ) * (-x)) =
      (Real.sqrt yoshidaA)⁻¹ *
        Real.cos (Real.pi * (n.1 : ℝ) * x)
    rw [show Real.pi * (n.1 : ℝ) * (-x) =
        -(Real.pi * (n.1 : ℝ) * x) by ring,
      Real.cos_neg]

theorem factorTwoCenteredCanonicalOddProfile_odd (m : ℕ) :
    Function.Odd (factorTwoCenteredCanonicalOddProfile m) := by
  intro x
  unfold factorTwoCenteredCanonicalOddProfile
  rw [show Real.pi * (m : ℝ) * (-x) =
      -(Real.pi * (m : ℝ) * x) by ring,
    Real.sin_neg]
  ring

theorem factorTwoCenteredCanonicalAdaptedEvenProfile_even
    (i : YoshidaEvenIndex) :
    Function.Even (factorTwoCenteredCanonicalAdaptedEvenProfile i) := by
  intro x
  simp only [factorTwoCenteredCanonicalAdaptedEvenProfile,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [factorTwoCenteredCanonicalEvenProfile_even
      (factorTwoCanonicalEvenLowIndex i) x,
    factorTwoCenteredCanonicalEvenProfile_even
      factorTwoCanonicalEvenTopIndex x]

/-- The two ordered concrete correlations differ by `-2` times the
even--odd ordering, expressed by the endpoint-adapted closed formula. -/
theorem factorTwoCenteredCrossDifference_adaptedEven_oddLow_eq_formula
    (i : YoshidaEvenIndex) (j : YoshidaOddIndex) (t : ℝ)
    (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    factorTwoCenteredCrossCorrelation
          (factorTwoCenteredOddLowProfile j)
          (factorTwoCenteredAdaptedEvenLowProfile i) t -
        factorTwoCenteredCrossCorrelation
          (factorTwoCenteredAdaptedEvenLowProfile i)
          (factorTwoCenteredOddLowProfile j) t =
      -2 * factorTwoAdaptedEvenOddCrossFormula i (j.1 + 1) t := by
  have heqEven : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      factorTwoCenteredAdaptedEvenLowProfile i x =
        factorTwoCenteredCanonicalAdaptedEvenProfile i x := by
    intro x hx
    rw [factorTwoCenteredAdaptedEvenLowProfile_eq_canonical_sub i hx]
    simp only [factorTwoCenteredCanonicalAdaptedEvenProfile,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have heqOdd : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      factorTwoCenteredOddLowProfile j x =
        factorTwoCenteredCanonicalOddProfile (j.1 + 1) x :=
    fun x hx ↦ factorTwoCenteredOddLowProfile_eq_canonical j hx
  calc
    _ = factorTwoCenteredCrossCorrelation
          (factorTwoCenteredCanonicalOddProfile (j.1 + 1))
          (factorTwoCenteredCanonicalAdaptedEvenProfile i) t -
        factorTwoCenteredCrossCorrelation
          (factorTwoCenteredCanonicalAdaptedEvenProfile i)
          (factorTwoCenteredCanonicalOddProfile (j.1 + 1)) t := by
      rw [factorTwoCenteredCrossCorrelation_congr_Icc
          heqOdd heqEven ht0 ht2,
        factorTwoCenteredCrossCorrelation_congr_Icc
          heqEven heqOdd ht0 ht2]
    _ = -2 * factorTwoCenteredCrossCorrelation
          (factorTwoCenteredCanonicalAdaptedEvenProfile i)
          (factorTwoCenteredCanonicalOddProfile (j.1 + 1)) t :=
      factorTwo_crossDifference_eq_neg_two_cross_of_even_odd
        (factorTwoCenteredCanonicalAdaptedEvenProfile_even i)
        (factorTwoCenteredCanonicalOddProfile_odd (j.1 + 1)) t
    _ = -2 * factorTwoCenteredCrossCorrelation
          (factorTwoCenteredAdaptedEvenLowProfile i)
          (factorTwoCenteredOddLowProfile j) t := by
      congr 1
      exact (factorTwoCenteredCrossCorrelation_congr_Icc
        heqEven heqOdd ht0 ht2).symm
    _ = _ := by
      rw [factorTwoCenteredCrossCorrelation_adaptedEven_oddLow_eq_formula
        i j t ht0 ht2]

/-- Every concrete alternating entry is the weighted integral of the
endpoint-adapted three-branch ordered-correlation formula, together with the
exact retained `p = 3` atom. -/
theorem factorTwoConcreteAlternatingMatrix_apply
    (i : YoshidaEvenIndex) (j : YoshidaOddIndex) :
    factorTwoConcreteAlternatingMatrix i j =
      -2 * yoshidaEndpointA *
          (∫ t : ℝ in 0..2,
            factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
              factorTwoAdaptedEvenOddCrossFormula i (j.1 + 1) t) +
        2 * (Real.log 3 / Real.sqrt 3) *
          factorTwoAdaptedEvenOddCrossFormula i (j.1 + 1)
            (factorTwoPrimeShift / yoshidaEndpointA) := by
  have hint :
      (∫ t : ℝ in 0..2,
        factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
          (factorTwoCenteredCrossCorrelation
              (factorTwoCenteredOddLowProfile j)
              (factorTwoCenteredAdaptedEvenLowProfile i) t -
            factorTwoCenteredCrossCorrelation
              (factorTwoCenteredAdaptedEvenLowProfile i)
              (factorTwoCenteredOddLowProfile j) t)) =
        ∫ t : ℝ in 0..2,
          factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
            (-2 * factorTwoAdaptedEvenOddCrossFormula
              i (j.1 + 1) t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
    change factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
        (factorTwoCenteredCrossCorrelation
            (factorTwoCenteredOddLowProfile j)
            (factorTwoCenteredAdaptedEvenLowProfile i) t -
          factorTwoCenteredCrossCorrelation
            (factorTwoCenteredAdaptedEvenLowProfile i)
            (factorTwoCenteredOddLowProfile j) t) =
      factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
        (-2 * factorTwoAdaptedEvenOddCrossFormula i (j.1 + 1) t)
    rw [factorTwoCenteredCrossDifference_adaptedEven_oddLow_eq_formula
      i j t ht.1 ht.2]
  have hscale :
      (∫ t : ℝ in 0..2,
          factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
            (-2 * factorTwoAdaptedEvenOddCrossFormula
              i (j.1 + 1) t)) =
        -2 *
          (∫ t : ℝ in 0..2,
            factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
              factorTwoAdaptedEvenOddCrossFormula i (j.1 + 1) t) := by
    rw [show (fun t : ℝ ↦
        factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
          (-2 * factorTwoAdaptedEvenOddCrossFormula i (j.1 + 1) t)) =
        fun t ↦ -2 *
          (factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
            factorTwoAdaptedEvenOddCrossFormula i (j.1 + 1) t) by
      funext t
      ring,
      intervalIntegral.integral_const_mul]
  have htau := factorTwoPrimeShift_div_endpointA_mem_one_two
  have htau0 : 0 ≤ factorTwoPrimeShift / yoshidaEndpointA :=
    le_trans (by norm_num) htau.1
  have hprime :=
    factorTwoCenteredCrossDifference_adaptedEven_oddLow_eq_formula
      i j (factorTwoPrimeShift / yoshidaEndpointA) htau0 htau.2
  change factorTwoCenteredAlternatingCoupling
      (factorTwoCenteredAdaptedEvenLowProfile i)
      (factorTwoCenteredOddLowProfile j) = _
  unfold factorTwoCenteredAlternatingCoupling
  rw [hint, hscale, hprime]
  ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteAlternatingFormula
