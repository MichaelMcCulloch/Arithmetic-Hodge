import ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointParityPencil
import ArithmeticHodge.Analysis.YoshidaEndpointBoundaryTailFold

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEnvelope

noncomputable section

open CenteredEndpointCorrelation
open YoshidaEndpointBoundaryTailFold
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointPotentialBound
open YoshidaEndpointSingularCorrelation
open YoshidaFactorTwoAdjacentKernel
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoCrossDistribution
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaRegularKernelBound

/-!
# Phase-uniform endpoint correlation envelopes

The symmetric and alternating factor-two channels are the dot and oriented
area pairings of two real two-vectors.  Keeping those pairings together gives
the sharp unit-disk estimate below.  Its endpoint-tail consequence controls
the reflected Cauchy pole without estimating the two channels separately.
-/

/-- The centered correlation in an arbitrary closed-disk phase direction. -/
def factorTwoCenteredPhaseCorrelation
    (u v : ℝ → ℝ) (a b t : ℝ) : ℝ :=
  a * (centeredEndpointCorrelation u t +
      centeredEndpointCorrelation v t) +
    b * (factorTwoCenteredCrossCorrelation v u t -
      factorTwoCenteredCrossCorrelation u v t)

/-- Every fixed phase direction gives a continuous overlap correlation. -/
theorem continuous_factorTwoCenteredPhaseCorrelation
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (a b : ℝ) :
    Continuous (factorTwoCenteredPhaseCorrelation u v a b) := by
  unfold factorTwoCenteredPhaseCorrelation
  exact
    (continuous_const.mul
        ((continuous_centeredEndpointCorrelation_of_continuous u hu).add
          (continuous_centeredEndpointCorrelation_of_continuous v hv))).add
      (continuous_const.mul
        ((continuous_factorTwoCenteredCrossCorrelation v u hv hu).sub
          (continuous_factorTwoCenteredCrossCorrelation u v hu hv)))

/-- The two adjacent-kernel branches with their correct opposite phase signs
on the reflected branch. -/
def factorTwoCenteredPhaseKernel
    (u v : ℝ → ℝ) (a b t : ℝ) : ℝ :=
  factorTwoAdjacentSmoothKernel
      (factorTwoLogLength + yoshidaEndpointA * t) *
        factorTwoCenteredPhaseCorrelation u v a b t +
    factorTwoAdjacentSmoothKernel
      (factorTwoLogLength - yoshidaEndpointA * t) *
        factorTwoCenteredPhaseCorrelation u v a (-b) t

/-- Pointwise recombination of the symmetric and alternating kernels.  This
records the sign reversal `b ↦ -b` on the reflected branch. -/
theorem factorTwoCenteredPhaseKernel_eq_symmetric_add_alternating
    (u v : ℝ → ℝ) (a b t : ℝ) :
    factorTwoCenteredPhaseKernel u v a b t =
      a * (factorTwoSymmetricWeight (yoshidaEndpointA * t) *
        (centeredEndpointCorrelation u t +
          centeredEndpointCorrelation v t)) +
      b * (factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
        (factorTwoCenteredCrossCorrelation v u t -
          factorTwoCenteredCrossCorrelation u v t)) := by
  unfold factorTwoCenteredPhaseKernel factorTwoCenteredPhaseCorrelation
    factorTwoSymmetricWeight factorTwoAntisymmetricWeight
  simp only [sub_eq_add_neg, add_comm]
  ring

/-- The regular part of the reflected adjacent branch after its Cauchy pole
has been removed. -/
def factorTwoCenteredReflectedRegularKernel (t : ℝ) : ℝ :=
  2 * Real.cosh (yoshidaEndpointA * (2 - t) / 2) -
    yoshidaRegularKernel (yoshidaEndpointA * (2 - t))

/-- The nonsingular forward adjacent branch of the phase kernel. -/
def factorTwoCenteredForwardPhaseKernel
    (u v : ℝ → ℝ) (a b t : ℝ) : ℝ :=
  factorTwoAdjacentSmoothKernel (yoshidaEndpointA * (2 + t)) *
    factorTwoCenteredPhaseCorrelation u v a b t

/-- The reflected branch after its explicit Cauchy pole has been added back.
The written expression is useful because both summands are integrable even
without a separate continuity theorem for the removable regular kernel. -/
def factorTwoCenteredReflectedDesingularizedPhaseKernel
    (u v : ℝ → ℝ) (a b t : ℝ) : ℝ :=
  yoshidaEndpointA *
      factorTwoAdjacentSmoothKernel (yoshidaEndpointA * (2 - t)) *
      factorTwoCenteredPhaseCorrelation u v a (-b) t +
    (1 / 2 : ℝ) *
      (factorTwoCenteredPhaseCorrelation u v a (-b) t / (2 - t))

/-- On the open overlap interval, the reflected phase branch is its regular
part minus exactly one half of the dimensionless endpoint pole. -/
theorem endpoint_mul_reflectedPhaseBranch_eq_regular_sub_half_pole
    (u v : ℝ → ℝ) (a b : ℝ) {t : ℝ}
    (ht2 : t < 2) :
    yoshidaEndpointA *
        factorTwoAdjacentSmoothKernel
          (factorTwoLogLength - yoshidaEndpointA * t) *
        factorTwoCenteredPhaseCorrelation u v a (-b) t =
      yoshidaEndpointA * factorTwoCenteredReflectedRegularKernel t *
          factorTwoCenteredPhaseCorrelation u v a (-b) t -
        (1 / (2 * (2 - t))) *
          factorTwoCenteredPhaseCorrelation u v a (-b) t := by
  have harg : yoshidaEndpointA * (2 - t) ≠ 0 :=
    mul_ne_zero yoshidaEndpointA_pos.ne' (by linarith)
  rw [show factorTwoLogLength - yoshidaEndpointA * t =
      yoshidaEndpointA * (2 - t) by
        rw [factorTwoLogLength_eq_two_mul_yoshidaEndpointA]
        ring,
    factorTwoAdjacentSmoothKernel_eq_cosh_sub_regular_sub_pole harg]
  unfold factorTwoCenteredReflectedRegularKernel
  have htwo : 2 - t ≠ 0 := by linarith
  field_simp [yoshidaEndpointA_pos.ne', htwo]

/-- The branch notation is exactly the two terms of the complete phase
kernel. -/
theorem factorTwoCenteredPhaseKernel_eq_forward_add_reflected
    (u v : ℝ → ℝ) (a b t : ℝ) :
    factorTwoCenteredPhaseKernel u v a b t =
      factorTwoCenteredForwardPhaseKernel u v a b t +
        factorTwoAdjacentSmoothKernel (yoshidaEndpointA * (2 - t)) *
          factorTwoCenteredPhaseCorrelation u v a (-b) t := by
  unfold factorTwoCenteredPhaseKernel factorTwoCenteredForwardPhaseKernel
  rw [factorTwoLogLength_eq_two_mul_yoshidaEndpointA]
  congr 2 <;> ring_nf

/-- Exact complete formula for a phase combination of the two symmetric
self channels and the alternating cross channel. -/
theorem phase_symmetric_add_alternating_eq_kernel_sub_primes
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (a b : ℝ) :
    a * (factorTwoCenteredSymmetricPerturbation u +
        factorTwoCenteredSymmetricPerturbation v) +
      b * factorTwoCenteredAlternatingCoupling u v =
        yoshidaEndpointA *
          (∫ t : ℝ in 0..2,
            factorTwoCenteredPhaseKernel u v a b t) -
        (Real.log 2 / Real.sqrt 2) * a *
          (centeredEndpointCorrelation u 0 +
            centeredEndpointCorrelation v 0) -
        (Real.log 3 / Real.sqrt 3) *
          factorTwoCenteredPhaseCorrelation u v a b
            (factorTwoPrimeShift / yoshidaEndpointA) := by
  have huu0 := intervalIntegrable_factorTwoCenteredSymmetricKernel u u hu hu
  have hvv0 := intervalIntegrable_factorTwoCenteredSymmetricKernel v v hv hv
  have huu : IntervalIntegrable
      (fun t : ℝ ↦ factorTwoSymmetricWeight (yoshidaEndpointA * t) *
        centeredEndpointCorrelation u t) volume 0 2 := by
    simpa only [factorTwoCenteredCorrelationBilinear_self] using huu0
  have hvv : IntervalIntegrable
      (fun t : ℝ ↦ factorTwoSymmetricWeight (yoshidaEndpointA * t) *
        centeredEndpointCorrelation v t) volume 0 2 := by
    simpa only [factorTwoCenteredCorrelationBilinear_self] using hvv0
  have halt := intervalIntegrable_factorTwoCenteredAlternatingKernel
    u v hu hv
  unfold factorTwoCenteredSymmetricPerturbation
    factorTwoCenteredAlternatingCoupling
  rw [show (fun t : ℝ ↦ factorTwoCenteredPhaseKernel u v a b t) =
      fun t ↦
        a * (factorTwoSymmetricWeight (yoshidaEndpointA * t) *
          centeredEndpointCorrelation u t +
          factorTwoSymmetricWeight (yoshidaEndpointA * t) *
            centeredEndpointCorrelation v t) +
        b * (factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
          (factorTwoCenteredCrossCorrelation v u t -
            factorTwoCenteredCrossCorrelation u v t)) by
      funext t
      rw [factorTwoCenteredPhaseKernel_eq_symmetric_add_alternating]
      ring,
    intervalIntegral.integral_add ((huu.add hvv).const_mul a)
      (halt.const_mul b),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add huu hvv]
  unfold factorTwoCenteredPhaseCorrelation
  ring

/-- Sharp real two-vector Cauchy estimate, uniform over the closed unit disk
of phase coefficients. -/
theorem two_mul_abs_phase_pairing_le
    (a b u₀ v₀ u₁ v₁ : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    2 * |a * (u₁ * u₀ + v₁ * v₀) +
        b * (v₁ * u₀ - u₁ * v₀)| ≤
      u₀ ^ 2 + v₀ ^ 2 + (u₁ ^ 2 + v₁ ^ 2) := by
  let R := u₁ * u₀ + v₁ * v₀
  let D := v₁ * u₀ - u₁ * v₀
  let X := u₀ ^ 2 + v₀ ^ 2
  let Y := u₁ ^ 2 + v₁ ^ 2
  let E := a * R + b * D
  have hRD : R ^ 2 + D ^ 2 = X * Y := by
    dsimp only [R, D, X, Y]
    ring
  have hRD0 : 0 ≤ R ^ 2 + D ^ 2 :=
    add_nonneg (sq_nonneg R) (sq_nonneg D)
  have hscaled :
      (a ^ 2 + b ^ 2) * (R ^ 2 + D ^ 2) ≤ R ^ 2 + D ^ 2 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hab hRD0
  have hE : E ^ 2 ≤ R ^ 2 + D ^ 2 := by
    have horth := sq_nonneg (a * D - b * R)
    dsimp only [E]
    nlinarith
  have hX0 : 0 ≤ X := add_nonneg (sq_nonneg u₀) (sq_nonneg v₀)
  have hY0 : 0 ≤ Y := add_nonneg (sq_nonneg u₁) (sq_nonneg v₁)
  have hsum0 : 0 ≤ X + Y := add_nonneg hX0 hY0
  have hsquares : (2 * |E|) ^ 2 ≤ (X + Y) ^ 2 := by
    rw [hRD] at hE
    calc
      (2 * |E|) ^ 2 = 4 * E ^ 2 := by
        rw [mul_pow, sq_abs]
        ring
      _ ≤ (X + Y) ^ 2 := by
        nlinarith [sq_nonneg (X - Y)]
  have habs0 : 0 ≤ 2 * |E| := mul_nonneg (by norm_num) (abs_nonneg E)
  have hfinal : 2 * |E| ≤ X + Y :=
    (sq_le_sq₀ habs0 hsum0).mp hsquares
  simpa only [E, R, D, X, Y, add_assoc] using hfinal

/-- At an overlap of length `t`, every unit-disk phase correlation is
controlled by the sum of the two profiles' boundary tails. -/
theorem two_mul_abs_phaseCorrelation_two_sub_le_boundaryTail
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) {t : ℝ}
    (ht0 : 0 ≤ t) :
    2 * |factorTwoCenteredPhaseCorrelation u v a b (2 - t)| ≤
      centeredEndpointBoundaryTail u t +
        centeredEndpointBoundaryTail v t := by
  let p : ℝ → ℝ := fun x ↦
    a * (u (2 - t + x) * u x + v (2 - t + x) * v x) +
      b * (v (2 - t + x) * u x - u (2 - t + x) * v x)
  let q : ℝ → ℝ := fun x ↦ u x ^ 2 + v x ^ 2
  have hbounds : (-1 : ℝ) ≤ -1 + t := by linarith
  have hpcont : Continuous p := by
    dsimp only [p]
    fun_prop
  have hqcont : Continuous q := by
    dsimp only [q]
    fun_prop
  have hpint : IntervalIntegrable p volume (-1) (-1 + t) :=
    hpcont.intervalIntegrable _ _
  have hqleft : IntervalIntegrable q volume (-1) (-1 + t) :=
    hqcont.intervalIntegrable _ _
  have hqshift : IntervalIntegrable (fun x ↦ q (2 - t + x))
      volume (-1) (-1 + t) :=
    (hqcont.comp (continuous_const.add continuous_id)).intervalIntegrable _ _
  have huu : IntervalIntegrable
      (fun x ↦ u (2 - t + x) * u x) volume (-1) (-1 + t) :=
    ((hu.comp (continuous_const.add continuous_id)).mul hu).intervalIntegrable _ _
  have hvv : IntervalIntegrable
      (fun x ↦ v (2 - t + x) * v x) volume (-1) (-1 + t) :=
    ((hv.comp (continuous_const.add continuous_id)).mul hv).intervalIntegrable _ _
  have hvu : IntervalIntegrable
      (fun x ↦ v (2 - t + x) * u x) volume (-1) (-1 + t) :=
    ((hv.comp (continuous_const.add continuous_id)).mul hu).intervalIntegrable _ _
  have huv : IntervalIntegrable
      (fun x ↦ u (2 - t + x) * v x) volume (-1) (-1 + t) :=
    ((hu.comp (continuous_const.add continuous_id)).mul hv).intervalIntegrable _ _
  have hphase :
      factorTwoCenteredPhaseCorrelation u v a b (2 - t) =
        ∫ x : ℝ in -1..-1 + t, p x := by
    unfold factorTwoCenteredPhaseCorrelation centeredEndpointCorrelation
      factorTwoCenteredCrossCorrelation
    rw [show 1 - (2 - t) = -1 + t by ring]
    dsimp only [p]
    rw [intervalIntegral.integral_add
        ((huu.add hvv).const_mul a) ((hvu.sub huv).const_mul b),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add huu hvv,
      intervalIntegral.integral_sub hvu huv]
  rw [hphase]
  calc
    2 * |∫ x : ℝ in -1..-1 + t, p x| =
        2 * ‖∫ x : ℝ in -1..-1 + t, p x‖ := by
      rw [Real.norm_eq_abs]
    _ ≤ 2 * ∫ x : ℝ in -1..-1 + t, ‖p x‖ := by
      gcongr
      exact intervalIntegral.norm_integral_le_integral_norm hbounds
    _ = ∫ x : ℝ in -1..-1 + t, 2 * ‖p x‖ := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ ∫ x : ℝ in -1..-1 + t, q (2 - t + x) + q x := by
      apply intervalIntegral.integral_mono_on hbounds
      · exact hpint.norm.const_mul 2
      · exact hqshift.add hqleft
      · intro x _hx
        dsimp only [p, q]
        rw [Real.norm_eq_abs]
        simpa only [add_comm, add_left_comm, add_assoc] using
          two_mul_abs_phase_pairing_le a b
            (u x) (v x) (u (2 - t + x)) (v (2 - t + x)) hab
    _ = (∫ x : ℝ in -1..-1 + t, q (2 - t + x)) +
          ∫ x : ℝ in -1..-1 + t, q x := by
      rw [intervalIntegral.integral_add hqshift hqleft]
    _ = (∫ x : ℝ in 1 - t..1, q x) +
          ∫ x : ℝ in -1..-1 + t, q x := by
      rw [intervalIntegral.integral_comp_add_left]
      congr 2 <;> ring
    _ = centeredEndpointBoundaryTail u t +
          centeredEndpointBoundaryTail v t := by
      unfold centeredEndpointBoundaryTail
      dsimp only [q]
      rw [intervalIntegral.integral_add
          ((hu.pow 2).intervalIntegrable _ _)
          ((hv.pow 2).intervalIntegrable _ _),
        intervalIntegral.integral_add
          ((hu.pow 2).intervalIntegrable _ _)
          ((hv.pow 2).intervalIntegrable _ _)]
      ring

/-- Boundary intervals of length at most one are disjoint, so their combined
mass is bounded by the full centered mass. -/
theorem centeredEndpointBoundaryTail_le_mass
    (w : ℝ → ℝ) (hw : Continuous w) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    centeredEndpointBoundaryTail w t ≤
      ∫ x : ℝ in -1..1, w x ^ 2 := by
  let q : ℝ → ℝ := fun x ↦ w x ^ 2
  have hq : Continuous q := by
    dsimp only [q]
    fun_prop
  have h₁ : (-1 : ℝ) ≤ -1 + t := by linarith
  have h₂ : -1 + t ≤ 1 - t := by linarith
  have h₃ : 1 - t ≤ (1 : ℝ) := by linarith
  have hleftMiddle :
      (∫ x : ℝ in -1..-1 + t, q x) +
          (∫ x : ℝ in -1 + t..1 - t, q x) =
        ∫ x : ℝ in -1..1 - t, q x :=
    intervalIntegral.integral_add_adjacent_intervals
      (hq.intervalIntegrable (-1) (-1 + t))
      (hq.intervalIntegrable (-1 + t) (1 - t))
  have hwhole :
      (∫ x : ℝ in -1..1 - t, q x) +
          (∫ x : ℝ in 1 - t..1, q x) =
        ∫ x : ℝ in -1..1, q x :=
    intervalIntegral.integral_add_adjacent_intervals
      (hq.intervalIntegrable (-1) (1 - t))
      (hq.intervalIntegrable (1 - t) 1)
  have hmiddle : 0 ≤ ∫ x : ℝ in -1 + t..1 - t, q x := by
    apply intervalIntegral.integral_nonneg h₂
    intro x _hx
    dsimp only [q]
    exact sq_nonneg _
  unfold centeredEndpointBoundaryTail
  dsimp only [q] at hleftMiddle hwhole ⊢
  linarith

/-- Every unit-disk phase correlation at a shift between one and two is a
half-mass contraction. -/
theorem two_mul_abs_phaseCorrelation_le_mass_of_one_le
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) {t : ℝ}
    (ht1 : 1 ≤ t) (ht2 : t ≤ 2) :
    2 * |factorTwoCenteredPhaseCorrelation u v a b t| ≤
      (∫ x : ℝ in -1..1, u x ^ 2) +
        ∫ x : ℝ in -1..1, v x ^ 2 := by
  let r := 2 - t
  have hr0 : 0 ≤ r := by dsimp only [r]; linarith
  have hr1 : r ≤ 1 := by dsimp only [r]; linarith
  have hphase := two_mul_abs_phaseCorrelation_two_sub_le_boundaryTail
    u v hu hv a b hab (t := r) hr0
  have huTail := centeredEndpointBoundaryTail_le_mass u hu hr0 hr1
  have hvTail := centeredEndpointBoundaryTail_le_mass v hv hr0 hr1
  dsimp only [r] at hphase huTail hvTail
  rw [show 2 - (2 - t) = t by ring] at hphase
  linarith

/-- The dimensionless retained-prime lag lies between one and two. -/
theorem factorTwoPrimeShift_div_endpointA_mem_one_two :
    factorTwoPrimeShift / yoshidaEndpointA ∈ Set.Icc (1 : ℝ) 2 := by
  have hsqrt2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2sq : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt2lt : Real.sqrt 2 < (3 / 2 : ℝ) := by nlinarith
  have hlog := Real.strictMonoOn_log hsqrt2pos (by norm_num) hsqrt2lt
  have hlogsqrt : Real.log (Real.sqrt 2) = Real.log 2 / 2 := by
    rw [Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hlogsqrt] at hlog
  constructor
  · rw [le_div_iff₀ yoshidaEndpointA_pos]
    unfold factorTwoPrimeShift yoshidaEndpointA
    simpa only [one_mul] using hlog.le
  · rw [div_le_iff₀ yoshidaEndpointA_pos]
    exact factorTwoPrimeShift_mem_endpointInterval.2

/-- The complete `p = 3` phase atom is bounded by half of the two-profile
mass, with the symmetric and alternating pieces kept together. -/
theorem two_mul_abs_phaseCorrelation_primeShift_le_mass
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    2 * |factorTwoCenteredPhaseCorrelation u v a b
        (factorTwoPrimeShift / yoshidaEndpointA)| ≤
      (∫ x : ℝ in -1..1, u x ^ 2) +
        ∫ x : ℝ in -1..1, v x ^ 2 := by
  exact two_mul_abs_phaseCorrelation_le_mass_of_one_le
    u v hu hv a b hab
      factorTwoPrimeShift_div_endpointA_mem_one_two.1
      factorTwoPrimeShift_div_endpointA_mem_one_two.2

/-- At zero shift the alternating correlation vanishes, so the phase
correlation is exactly `a` times the two-profile mass. -/
theorem factorTwoCenteredPhaseCorrelation_zero
    (u v : ℝ → ℝ) (a b : ℝ) :
    factorTwoCenteredPhaseCorrelation u v a b 0 =
      a * ((∫ x : ℝ in -1..1, u x ^ 2) +
        ∫ x : ℝ in -1..1, v x ^ 2) := by
  have hcross : factorTwoCenteredCrossCorrelation v u 0 =
      factorTwoCenteredCrossCorrelation u v 0 := by
    unfold factorTwoCenteredCrossCorrelation
    simp only [zero_add, sub_zero]
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  unfold factorTwoCenteredPhaseCorrelation
  rw [centeredEndpointCorrelation_zero,
    centeredEndpointCorrelation_zero, hcross]
  ring

/-- The two retained prime atoms in the complete phase formula have a uniform
lower bound in terms of the two-profile mass.  The `p = 3` contribution uses
the sharp half-mass contraction above. -/
theorem phase_prime_terms_lower
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    -((Real.log 2 / Real.sqrt 2) * a *
          (centeredEndpointCorrelation u 0 +
            centeredEndpointCorrelation v 0)) -
        (Real.log 3 / Real.sqrt 3) *
          factorTwoCenteredPhaseCorrelation u v a b
            (factorTwoPrimeShift / yoshidaEndpointA) ≥
      -((Real.log 2 / Real.sqrt 2) * |a| +
          (Real.log 3 / Real.sqrt 3) / 2) *
        ((∫ x : ℝ in -1..1, u x ^ 2) +
          ∫ x : ℝ in -1..1, v x ^ 2) := by
  let M : ℝ := (∫ x : ℝ in -1..1, u x ^ 2) +
    ∫ x : ℝ in -1..1, v x ^ 2
  let z : ℝ := factorTwoCenteredPhaseCorrelation u v a b
    (factorTwoPrimeShift / yoshidaEndpointA)
  have huMass : 0 ≤ ∫ x : ℝ in -1..1, u x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg (u x))
  have hvMass : 0 ≤ ∫ x : ℝ in -1..1, v x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg (v x))
  have hM : 0 ≤ M := by dsimp only [M]; linarith
  have hz := two_mul_abs_phaseCorrelation_primeShift_le_mass
    u v hu hv a b hab
  have hzUpper : z ≤ M / 2 := by
    dsimp only [z, M] at hz ⊢
    nlinarith [le_abs_self
      (factorTwoCenteredPhaseCorrelation u v a b
        (factorTwoPrimeShift / yoshidaEndpointA))]
  have haUpper : a ≤ |a| := le_abs_self a
  have hα : 0 ≤ Real.log 2 / Real.sqrt 2 := by positivity
  have hβ : 0 ≤ Real.log 3 / Real.sqrt 3 := by positivity
  have htwoAtom :
      (Real.log 2 / Real.sqrt 2) * a * M ≤
        (Real.log 2 / Real.sqrt 2) * |a| * M := by
    calc
      (Real.log 2 / Real.sqrt 2) * a * M =
          ((Real.log 2 / Real.sqrt 2) * M) * a := by ring
      _ ≤ ((Real.log 2 / Real.sqrt 2) * M) * |a| :=
        mul_le_mul_of_nonneg_left haUpper (mul_nonneg hα hM)
      _ = (Real.log 2 / Real.sqrt 2) * |a| * M := by ring
  have hthreeAtom :
      (Real.log 3 / Real.sqrt 3) * z ≤
        (Real.log 3 / Real.sqrt 3) * (M / 2) :=
    mul_le_mul_of_nonneg_left hzUpper hβ
  rw [centeredEndpointCorrelation_zero,
    centeredEndpointCorrelation_zero]
  dsimp only [M, z] at htwoAtom hthreeAtom ⊢
  nlinarith

/-- The ordered cross-correlation divided by the reflected overlap length is
interval-integrable. -/
theorem intervalIntegrable_factorTwoCenteredCrossCorrelation_two_sub_div
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v) :
    IntervalIntegrable
      (fun t : ℝ ↦ factorTwoCenteredCrossCorrelation u v (2 - t) / t)
      volume 0 2 := by
  have hreflect :=
    (intervalIntegrable_factorTwoCenteredCrossCorrelation_div_two_sub
      u v hu hv).comp_sub_left 2
  convert hreflect.symm using 1 <;> norm_num

/-- The reflected-pole quotient remains interval-integrable after taking an
arbitrary real phase direction. -/
theorem intervalIntegrable_factorTwoCenteredPhaseCorrelation_two_sub_div
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (a b : ℝ) :
    IntervalIntegrable
      (fun t : ℝ ↦ factorTwoCenteredPhaseCorrelation u v a b (2 - t) / t)
      volume 0 2 := by
  have huu := intervalIntegrable_centeredEndpointCorrelation_two_sub_div u hu
  have hvv := intervalIntegrable_centeredEndpointCorrelation_two_sub_div v hv
  have hvu :=
    intervalIntegrable_factorTwoCenteredCrossCorrelation_two_sub_div v u hv hu
  have huv :=
    intervalIntegrable_factorTwoCenteredCrossCorrelation_two_sub_div u v hu hv
  have hsum := ((huu.add hvv).const_mul a).add ((hvu.sub huv).const_mul b)
  apply hsum.congr
  intro t _ht
  unfold factorTwoCenteredPhaseCorrelation
  ring

/-- The complete phase kernel is interval-integrable.  This packages the
already desingularized symmetric and alternating channel theorems without
discarding their common phase. -/
theorem intervalIntegrable_factorTwoCenteredPhaseKernel
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (a b : ℝ) :
    IntervalIntegrable (factorTwoCenteredPhaseKernel u v a b)
      volume 0 2 := by
  have huu0 :=
    intervalIntegrable_factorTwoCenteredSymmetricKernel u u hu hu
  have hvv0 :=
    intervalIntegrable_factorTwoCenteredSymmetricKernel v v hv hv
  have huu : IntervalIntegrable
      (fun t : ℝ ↦ factorTwoSymmetricWeight (yoshidaEndpointA * t) *
        centeredEndpointCorrelation u t) volume 0 2 := by
    simpa only [factorTwoCenteredCorrelationBilinear_self] using huu0
  have hvv : IntervalIntegrable
      (fun t : ℝ ↦ factorTwoSymmetricWeight (yoshidaEndpointA * t) *
        centeredEndpointCorrelation v t) volume 0 2 := by
    simpa only [factorTwoCenteredCorrelationBilinear_self] using hvv0
  have halt :=
    intervalIntegrable_factorTwoCenteredAlternatingKernel u v hu hv
  have hsum := ((huu.add hvv).const_mul a).add (halt.const_mul b)
  apply hsum.congr
  intro t _ht
  rw [factorTwoCenteredPhaseKernel_eq_symmetric_add_alternating]
  ring

/-- The forward adjacent branch stays uniformly away from its kernel pole
and is therefore interval-integrable by ordinary continuity. -/
theorem intervalIntegrable_factorTwoCenteredForwardPhaseKernel
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (a b : ℝ) :
    IntervalIntegrable (factorTwoCenteredForwardPhaseKernel u v a b)
      volume 0 2 := by
  let d : ℝ → ℝ := factorTwoCenteredPhaseCorrelation u v a b
  have hd : Continuous d := by
    dsimp only [d]
    exact continuous_factorTwoCenteredPhaseCorrelation u v hu hv a b
  unfold factorTwoCenteredForwardPhaseKernel
  apply ContinuousOn.intervalIntegrable
  intro t ht
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
  have harg : yoshidaEndpointA * (2 + t) ≠ 0 :=
    mul_ne_zero yoshidaEndpointA_pos.ne'
      (by nlinarith [ht.1] : 2 + t ≠ 0)
  have hkernelMul : ContinuousAt (fun z : ℝ ↦
      factorTwoAdjacentSmoothKernel (yoshidaEndpointA * z)) (2 + t) :=
    (continuousAt_factorTwoAdjacentSmoothKernel_of_ne_zero harg).comp'
      (continuousAt_const.mul continuousAt_id)
  have hkernel : ContinuousAt (fun x : ℝ ↦
      factorTwoAdjacentSmoothKernel (yoshidaEndpointA * (2 + x))) t :=
    hkernelMul.comp' (continuousAt_const.add continuousAt_id)
  exact (hkernel.mul hd.continuousAt).continuousWithinAt

/-- The original reflected-pole quotient is interval-integrable in every
phase direction. -/
theorem intervalIntegrable_factorTwoCenteredPhaseCorrelation_div_two_sub
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (a b : ℝ) :
    IntervalIntegrable
      (fun t : ℝ ↦ factorTwoCenteredPhaseCorrelation u v a b t /
        (2 - t)) volume 0 2 := by
  have hreflect :=
    (intervalIntegrable_factorTwoCenteredPhaseCorrelation_two_sub_div
      u v hu hv a b).comp_sub_left 2
  convert hreflect.symm using 1 <;> norm_num

/-- Adding back the explicit half-pole leaves an interval-integrable
reflected remainder. -/
theorem intervalIntegrable_factorTwoCenteredReflectedDesingularizedPhaseKernel
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (a b : ℝ) :
    IntervalIntegrable
      (factorTwoCenteredReflectedDesingularizedPhaseKernel u v a b)
      volume 0 2 := by
  have hcomplete :=
    intervalIntegrable_factorTwoCenteredPhaseKernel u v hu hv a b
  have hforward :=
    intervalIntegrable_factorTwoCenteredForwardPhaseKernel u v hu hv a b
  have hreflected : IntervalIntegrable
      (fun t : ℝ ↦
        factorTwoAdjacentSmoothKernel (yoshidaEndpointA * (2 - t)) *
          factorTwoCenteredPhaseCorrelation u v a (-b) t) volume 0 2 := by
    apply (hcomplete.sub hforward).congr
    intro t _ht
    change factorTwoCenteredPhaseKernel u v a b t -
        factorTwoCenteredForwardPhaseKernel u v a b t = _
    rw [factorTwoCenteredPhaseKernel_eq_forward_add_reflected]
    ring
  have hquotient :=
    intervalIntegrable_factorTwoCenteredPhaseCorrelation_div_two_sub
      u v hu hv a (-b)
  have hsum :=
    (hreflected.const_mul yoshidaEndpointA).add
      (hquotient.const_mul (1 / 2 : ℝ))
  apply hsum.congr
  intro t _ht
  unfold factorTwoCenteredReflectedDesingularizedPhaseKernel
  ring

/-- Exact integral separation of the complete adjacent kernel into its
forward branch, its desingularized reflected remainder, and the signed
half-pole. -/
theorem endpoint_mul_integral_phaseKernel_eq_regular_sub_half_pole
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (a b : ℝ) :
    yoshidaEndpointA *
        (∫ t : ℝ in 0..2, factorTwoCenteredPhaseKernel u v a b t) =
      yoshidaEndpointA *
          (∫ t : ℝ in 0..2,
            factorTwoCenteredForwardPhaseKernel u v a b t) +
        (∫ t : ℝ in 0..2,
          factorTwoCenteredReflectedDesingularizedPhaseKernel u v a b t) -
        (1 / 2 : ℝ) *
          (∫ t : ℝ in 0..2,
            factorTwoCenteredPhaseCorrelation u v a (-b) t / (2 - t)) := by
  have hforward :=
    intervalIntegrable_factorTwoCenteredForwardPhaseKernel u v hu hv a b
  have hdesingularized :=
    intervalIntegrable_factorTwoCenteredReflectedDesingularizedPhaseKernel
      u v hu hv a b
  have hquotient :=
    intervalIntegrable_factorTwoCenteredPhaseCorrelation_div_two_sub
      u v hu hv a (-b)
  have hregular :=
    (hforward.const_mul yoshidaEndpointA).add hdesingularized
  calc
    yoshidaEndpointA *
          (∫ t : ℝ in 0..2, factorTwoCenteredPhaseKernel u v a b t) =
        ∫ t : ℝ in 0..2,
          yoshidaEndpointA * factorTwoCenteredPhaseKernel u v a b t := by
      rw [intervalIntegral.integral_const_mul]
    _ = ∫ t : ℝ in 0..2,
          (yoshidaEndpointA *
              factorTwoCenteredForwardPhaseKernel u v a b t +
            factorTwoCenteredReflectedDesingularizedPhaseKernel
              u v a b t) -
            (1 / 2 : ℝ) *
              (factorTwoCenteredPhaseCorrelation u v a (-b) t /
                (2 - t)) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      change yoshidaEndpointA *
          factorTwoCenteredPhaseKernel u v a b t = _
      rw [factorTwoCenteredPhaseKernel_eq_forward_add_reflected]
      unfold factorTwoCenteredReflectedDesingularizedPhaseKernel
      ring
    _ = (∫ t : ℝ in 0..2,
            yoshidaEndpointA *
                factorTwoCenteredForwardPhaseKernel u v a b t +
              factorTwoCenteredReflectedDesingularizedPhaseKernel
                u v a b t) -
          ∫ t : ℝ in 0..2,
            (1 / 2 : ℝ) *
              (factorTwoCenteredPhaseCorrelation u v a (-b) t /
                (2 - t)) := by
      rw [intervalIntegral.integral_sub hregular
        (hquotient.const_mul (1 / 2 : ℝ))]
    _ = _ := by
      rw [intervalIntegral.integral_add
          (hforward.const_mul yoshidaEndpointA) hdesingularized,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]

/-- Exact signed normal form for the complete phase perturbation.  Unlike the
envelopes below, this identity keeps the reflected pole and both prime atoms
with their phases, so no cancellation has yet been spent. -/
theorem phase_symmetric_add_alternating_eq_regular_sub_pole_sub_primes
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (a b : ℝ) :
    a * (factorTwoCenteredSymmetricPerturbation u +
        factorTwoCenteredSymmetricPerturbation v) +
      b * factorTwoCenteredAlternatingCoupling u v =
        yoshidaEndpointA *
            (∫ t : ℝ in 0..2,
              factorTwoCenteredForwardPhaseKernel u v a b t) +
          (∫ t : ℝ in 0..2,
            factorTwoCenteredReflectedDesingularizedPhaseKernel
              u v a b t) -
          (1 / 2 : ℝ) *
            (∫ t : ℝ in 0..2,
              factorTwoCenteredPhaseCorrelation u v a (-b) t /
                (2 - t)) -
          (Real.log 2 / Real.sqrt 2) * a *
            ((∫ x : ℝ in -1..1, u x ^ 2) +
              ∫ x : ℝ in -1..1, v x ^ 2) -
          (Real.log 3 / Real.sqrt 3) *
            factorTwoCenteredPhaseCorrelation u v a b
              (factorTwoPrimeShift / yoshidaEndpointA) := by
  have hformula :=
    phase_symmetric_add_alternating_eq_kernel_sub_primes
      u v hu hv a b
  rw [endpoint_mul_integral_phaseKernel_eq_regular_sub_half_pole
      u v hu hv a b,
    centeredEndpointCorrelation_zero,
    centeredEndpointCorrelation_zero] at hformula
  exact hformula

/-- The phase quotient feeding the reflected singular pole is bounded by the
exact endpoint potential and `log 2` masses, uniformly over every phase in
the closed unit disk.  The actual adjacent-kernel pole carries the additional
coefficient `-1/2`, recorded in the lower-bound theorem below.  No triangle
inequality separates the symmetric and alternating channels before their
common two-vector Cauchy estimate. -/
theorem integral_abs_phaseCorrelation_two_sub_div_le_potential_mass
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    (∫ t : ℝ in 0..2,
        |factorTwoCenteredPhaseCorrelation u v a b (2 - t) / t|) ≤
      ((∫ x : ℝ in -1..1, yoshidaEndpointPotential x * u x ^ 2) +
          (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * v x ^ 2)) +
        Real.log 2 *
          ((∫ x : ℝ in -1..1, u x ^ 2) +
            ∫ x : ℝ in -1..1, v x ^ 2) := by
  have hphase :=
    intervalIntegrable_factorTwoCenteredPhaseCorrelation_two_sub_div
      u v hu hv a b
  have huBoundary := intervalIntegrable_centeredEndpointBoundaryTail_div u hu
  have hvBoundary := intervalIntegrable_centeredEndpointBoundaryTail_div v hv
  have hmajorant : IntervalIntegrable
      (fun t : ℝ ↦
        (1 / 2 : ℝ) * (centeredEndpointBoundaryTail u t / t) +
          (1 / 2 : ℝ) * (centeredEndpointBoundaryTail v t / t))
      volume 0 2 :=
    (huBoundary.const_mul (1 / 2 : ℝ)).add
      (hvBoundary.const_mul (1 / 2 : ℝ))
  have hmono :
      (∫ t : ℝ in 0..2,
          |factorTwoCenteredPhaseCorrelation u v a b (2 - t) / t|) ≤
        ∫ t : ℝ in 0..2,
          ((1 / 2 : ℝ) * (centeredEndpointBoundaryTail u t / t) +
            (1 / 2 : ℝ) * (centeredEndpointBoundaryTail v t / t)) := by
    apply intervalIntegral.integral_mono_on (by norm_num) hphase.abs hmajorant
    intro t ht
    by_cases htzero : t = 0
    · simp [htzero]
    · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htzero)
      have hpoint :=
        two_mul_abs_phaseCorrelation_two_sub_le_boundaryTail
          u v hu hv a b hab ht.1
      rw [abs_div, abs_of_pos htpos, div_le_iff₀ htpos]
      calc
        |factorTwoCenteredPhaseCorrelation u v a b (2 - t)| ≤
            (1 / 2 : ℝ) *
              (centeredEndpointBoundaryTail u t +
                centeredEndpointBoundaryTail v t) := by
          linarith
        _ = ((1 / 2 : ℝ) *
                (centeredEndpointBoundaryTail u t / t) +
              (1 / 2 : ℝ) *
                (centeredEndpointBoundaryTail v t / t)) * t := by
          field_simp [htzero]
  calc
    (∫ t : ℝ in 0..2,
        |factorTwoCenteredPhaseCorrelation u v a b (2 - t) / t|) ≤
        ∫ t : ℝ in 0..2,
          ((1 / 2 : ℝ) * (centeredEndpointBoundaryTail u t / t) +
            (1 / 2 : ℝ) * (centeredEndpointBoundaryTail v t / t)) := hmono
    _ = (1 / 2 : ℝ) *
          (∫ t : ℝ in 0..2, centeredEndpointBoundaryTail u t / t) +
        (1 / 2 : ℝ) *
          (∫ t : ℝ in 0..2, centeredEndpointBoundaryTail v t / t) := by
      rw [intervalIntegral.integral_add
          (huBoundary.const_mul (1 / 2 : ℝ))
          (hvBoundary.const_mul (1 / 2 : ℝ)),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
    _ = ((∫ x : ℝ in -1..1, yoshidaEndpointPotential x * u x ^ 2) +
          Real.log 2 * (∫ x : ℝ in -1..1, u x ^ 2)) +
        ((∫ x : ℝ in -1..1, yoshidaEndpointPotential x * v x ^ 2) +
          Real.log 2 * (∫ x : ℝ in -1..1, v x ^ 2)) := by
      rw [half_integral_centeredEndpointBoundaryTail_div_eq u hu,
        half_integral_centeredEndpointBoundaryTail_div_eq v hv]
    _ = _ := by ring

/-- Reflection exchanges the two presentations of the phase pole. -/
theorem integral_phaseCorrelation_div_two_sub_eq_reflected
    (u v : ℝ → ℝ) (a b : ℝ) :
    (∫ t : ℝ in 0..2,
        factorTwoCenteredPhaseCorrelation u v a b t / (2 - t)) =
      ∫ t : ℝ in 0..2,
        factorTwoCenteredPhaseCorrelation u v a b (2 - t) / t := by
  have hreflect := intervalIntegral.integral_comp_sub_left
    (f := fun t : ℝ ↦
      factorTwoCenteredPhaseCorrelation u v a b t / (2 - t))
    (a := (0 : ℝ)) (b := 2) 2
  simpa only [sub_zero, sub_self, sub_sub_cancel] using hreflect.symm

/-- Quantitative lower bound for the signed reflected Cauchy pole occurring
in the complete phase pencil. -/
theorem neg_half_integral_phaseCorrelation_div_two_sub_lower
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    -(1 / 2 : ℝ) *
        (((∫ x : ℝ in -1..1, yoshidaEndpointPotential x * u x ^ 2) +
            (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * v x ^ 2)) +
          Real.log 2 *
            ((∫ x : ℝ in -1..1, u x ^ 2) +
              ∫ x : ℝ in -1..1, v x ^ 2)) ≤
      -(1 / 2 : ℝ) *
        (∫ t : ℝ in 0..2,
          factorTwoCenteredPhaseCorrelation u v a b t / (2 - t)) := by
  let f : ℝ → ℝ := fun t ↦
    factorTwoCenteredPhaseCorrelation u v a b (2 - t) / t
  let V : ℝ :=
    ((∫ x : ℝ in -1..1, yoshidaEndpointPotential x * u x ^ 2) +
        (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * v x ^ 2)) +
      Real.log 2 *
        ((∫ x : ℝ in -1..1, u x ^ 2) +
          ∫ x : ℝ in -1..1, v x ^ 2)
  have habsIntegral :
      |∫ t : ℝ in 0..2, f t| ≤ ∫ t : ℝ in 0..2, |f t| :=
    intervalIntegral.abs_integral_le_integral_abs (by norm_num)
  have habsBound : (∫ t : ℝ in 0..2, |f t|) ≤ V := by
    simpa only [f, V] using
      integral_abs_phaseCorrelation_two_sub_div_le_potential_mass
        u v hu hv a b hab
  have hupper : (∫ t : ℝ in 0..2, f t) ≤ V :=
    (le_abs_self _).trans (habsIntegral.trans habsBound)
  rw [integral_phaseCorrelation_div_two_sub_eq_reflected]
  dsimp only [f, V] at hupper ⊢
  linarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEnvelope
