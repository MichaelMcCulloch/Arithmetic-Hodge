import ArithmeticHodge.Analysis.CenteredOddOneThreeEnergy
import ArithmeticHodge.Analysis.YoshidaClippedMomentBridge
import ArithmeticHodge.Analysis.YoshidaEndpointScaledCorrelation
import ArithmeticHodge.Analysis.YoshidaOddTailLowFunctional

set_option autoImplicit false

open Filter MeasureTheory Real Set Topology

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseOddRawGap

open CenteredOddOneThreeEnergy
open ShiftedLegendreCenteredLowModeThreeL2
open ShiftedLegendreCenteredParity
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine
open UnitIntervalLogEnergyProjection
open YoshidaEndpointOcticPotential
open YoshidaClippedMomentBridge
open YoshidaClippedCircleBridge
open YoshidaCoercivityNumerics
open YoshidaEndpointScaledCorrelation
open YoshidaOddHomogeneousCoercivity
open YoshidaOddTailLowFunctional
open YoshidaOddTailPaired
open YoshidaSectionSixAnalytic
open YoshidaWeightedTailBounds

noncomputable section

private theorem integral_mul_sin_nat_pi
    (n : ℕ) (hn : n ≠ 0) :
    (∫ x : ℝ in -1..1, x * Real.sin (Real.pi * (n : ℝ) * x)) =
      -2 * (-1 : ℝ) ^ n / (Real.pi * (n : ℝ)) := by
  let α : ℝ := Real.pi * (n : ℝ)
  have hα : α ≠ 0 := by
    dsimp only [α]
    positivity
  let F : ℝ → ℝ := fun x ↦
    -(x * Real.cos (α * x)) / α + Real.sin (α * x) / α ^ 2
  have hderiv (x : ℝ) :
      HasDerivAt F (x * Real.sin (α * x)) x := by
    have hsin : HasDerivAt (fun y : ℝ ↦ Real.sin (α * y))
        (α * Real.cos (α * x)) x := by
      convert (Real.hasDerivAt_sin (α * x)).comp x
        ((hasDerivAt_id x).const_mul α) using 1
      all_goals ring
    have hcos : HasDerivAt (fun y : ℝ ↦ Real.cos (α * y))
        (-α * Real.sin (α * x)) x := by
      convert (Real.hasDerivAt_cos (α * x)).comp x
        ((hasDerivAt_id x).const_mul α) using 1
      all_goals ring
    dsimp only [F]
    convert (((hasDerivAt_id x).mul hcos).neg.div_const α).add
      (hsin.div_const (α ^ 2)) using 1
    simp only [id_eq]
    field_simp [hα]
    ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _hx ↦ hderiv x)
      (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
  rw [show (fun x : ℝ ↦ x * Real.sin (Real.pi * (n : ℝ) * x)) =
      fun x ↦ x * Real.sin (α * x) by rfl, hint]
  dsimp only [F]
  have hαeq : α = (n : ℝ) * Real.pi := by
    dsimp only [α]
    ring
  have hsinPos : Real.sin (α * 1) = 0 := by
    rw [hαeq, mul_one, Real.sin_nat_mul_pi]
  have hcosPos : Real.cos (α * 1) = (-1 : ℝ) ^ n := by
    rw [hαeq, mul_one, Real.cos_nat_mul_pi]
  have hsinNeg : Real.sin (α * (-1)) = 0 := by
    rw [show α * (-1) = -(α * 1) by ring, Real.sin_neg, hsinPos,
      neg_zero]
  have hcosNeg : Real.cos (α * (-1)) = (-1 : ℝ) ^ n := by
    rw [show α * (-1) = -(α * 1) by ring, Real.cos_neg, hcosPos]
  rw [hsinPos, hcosPos, hsinNeg, hcosNeg]
  rw [hαeq] at hα ⊢
  field_simp [hα]
  ring

private theorem integral_pow_three_mul_sin_nat_pi
    (n : ℕ) (hn : n ≠ 0) :
    (∫ x : ℝ in -1..1, x ^ 3 * Real.sin (Real.pi * (n : ℝ) * x)) =
      (-1 : ℝ) ^ n *
        (-2 / (Real.pi * (n : ℝ)) +
          12 / (Real.pi * (n : ℝ)) ^ 3) := by
  let α : ℝ := Real.pi * (n : ℝ)
  have hα : α ≠ 0 := by
    dsimp only [α]
    positivity
  let F : ℝ → ℝ := fun x ↦
    -(x ^ 3 * Real.cos (α * x)) / α +
      3 * x ^ 2 * Real.sin (α * x) / α ^ 2 +
      6 * x * Real.cos (α * x) / α ^ 3 -
      6 * Real.sin (α * x) / α ^ 4
  have hderiv (x : ℝ) :
      HasDerivAt F (x ^ 3 * Real.sin (α * x)) x := by
    have hsin : HasDerivAt (fun y : ℝ ↦ Real.sin (α * y))
        (α * Real.cos (α * x)) x := by
      convert (Real.hasDerivAt_sin (α * x)).comp x
        ((hasDerivAt_id x).const_mul α) using 1
      all_goals ring
    have hcos : HasDerivAt (fun y : ℝ ↦ Real.cos (α * y))
        (-α * Real.sin (α * x)) x := by
      convert (Real.hasDerivAt_cos (α * x)).comp x
        ((hasDerivAt_id x).const_mul α) using 1
      all_goals ring
    have hfirst : HasDerivAt
        (fun y : ℝ ↦ -(y ^ 3 * Real.cos (α * y)) / α)
        (-(3 * x ^ 2 * Real.cos (α * x) +
          x ^ 3 * (-α * Real.sin (α * x))) / α) x := by
      convert ((((hasDerivAt_id x).pow 3).mul hcos).neg.div_const α) using 1
      all_goals simp [id_eq]
    have hsecond : HasDerivAt
        (fun y : ℝ ↦ 3 * y ^ 2 * Real.sin (α * y) / α ^ 2)
        (3 * (2 * x * Real.sin (α * x) +
          x ^ 2 * (α * Real.cos (α * x))) / α ^ 2) x := by
      convert (((((hasDerivAt_id x).pow 2).mul hsin).const_mul 3).div_const
        (α ^ 2)) using 1
      · funext y
        simp only [id_eq, Pi.pow_apply, Pi.mul_apply]
        ring
      · simp only [id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub]
        ring
    have hthird : HasDerivAt
        (fun y : ℝ ↦ 6 * y * Real.cos (α * y) / α ^ 3)
        (6 * (Real.cos (α * x) +
          x * (-α * Real.sin (α * x))) / α ^ 3) x := by
      convert ((((hasDerivAt_id x).mul hcos).const_mul 6).div_const
        (α ^ 3)) using 1
      · funext y
        simp only [id_eq, Pi.mul_apply]
        ring
      · simp only [id_eq]
        ring
    have hfourth : HasDerivAt
        (fun y : ℝ ↦ 6 * Real.sin (α * y) / α ^ 4)
        (6 * (α * Real.cos (α * x)) / α ^ 4) x := by
      exact (hsin.const_mul 6).div_const (α ^ 4)
    dsimp only [F]
    convert ((hfirst.add hsecond).add hthird).sub hfourth using 1
    field_simp [hα]
    ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _hx ↦ hderiv x)
      (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
  rw [show (fun x : ℝ ↦ x ^ 3 * Real.sin (Real.pi * (n : ℝ) * x)) =
      fun x ↦ x ^ 3 * Real.sin (α * x) by rfl, hint]
  dsimp only [F]
  have hαeq : α = (n : ℝ) * Real.pi := by
    dsimp only [α]
    ring
  have hsinPos : Real.sin (α * 1) = 0 := by
    rw [hαeq, mul_one, Real.sin_nat_mul_pi]
  have hcosPos : Real.cos (α * 1) = (-1 : ℝ) ^ n := by
    rw [hαeq, mul_one, Real.cos_nat_mul_pi]
  have hsinNeg : Real.sin (α * (-1)) = 0 := by
    rw [show α * (-1) = -(α * 1) by ring, Real.sin_neg, hsinPos,
      neg_zero]
  have hcosNeg : Real.cos (α * (-1)) = (-1 : ℝ) ^ n := by
    rw [show α * (-1) = -(α * 1) by ring, Real.cos_neg, hcosPos]
  rw [hsinPos, hcosPos, hsinNeg, hcosNeg]
  rw [hαeq] at hα ⊢
  field_simp [hα]
  ring

private theorem integral_centeredP3_mul_sin_nat_pi
    (n : ℕ) (hn : n ≠ 0) :
    (∫ x : ℝ in -1..1,
      centeredP3 x * Real.sin (Real.pi * (n : ℝ) * x)) =
      2 * (-1 : ℝ) ^ n *
        (-1 / (Real.pi * (n : ℝ)) +
          15 / (Real.pi * (n : ℝ)) ^ 3) := by
  rw [show (fun x : ℝ ↦
      centeredP3 x * Real.sin (Real.pi * (n : ℝ) * x)) =
      fun x ↦ (5 / 2 : ℝ) *
          (x ^ 3 * Real.sin (Real.pi * (n : ℝ) * x)) -
        (3 / 2 : ℝ) *
          (x * Real.sin (Real.pi * (n : ℝ) * x)) by
    funext x
    simp only [centeredP3]
    ring]
  rw [intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    integral_pow_three_mul_sin_nat_pi n hn,
    integral_mul_sin_nat_pi n hn]
  · ring
  · exact Continuous.intervalIntegrable (by fun_prop) (-1) 1
  · exact Continuous.intervalIntegrable (by fun_prop) (-1) 1

private theorem normSq_weightedIntegral_le_energy
    {a : ℝ} (ha : 0 < a) (p : ℝ → ℂ) (hp : Continuous p)
    (f : YoshidaClippedSmooth a) :
    Complex.normSq (∫ x : ℝ in -a..a, p x * f x) ≤
      (∫ x : ℝ in -a..a, ‖p x‖ ^ 2) * clippedIntervalEnergy f := by
  let I : Set ℝ := Set.Ioc (-a) a
  let μ : Measure ℝ := volume.restrict I
  have hpMeas : AEStronglyMeasurable p μ :=
    hp.aestronglyMeasurable.restrict
  have hpLp : MemLp p 2 μ := by
    rw [memLp_two_iff_integrable_sq_norm hpMeas]
    have hcompact : IntegrableOn (fun x : ℝ ↦ ‖p x‖ ^ 2)
        (Set.Icc (-a) a) :=
      (hp.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have hfLp : MemLp (fun x : ℝ ↦ f x) 2 μ := by
    simpa only [μ, I] using yoshidaClippedSmooth_memLp_two f
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (p := 2) (q := 2) (f := p) (g := fun x : ℝ ↦ f x) (μ := μ)
    Real.HolderConjugate.two_two (by simpa using hpLp) (by simpa using hfLp)
  have hA0 : 0 ≤ ∫ x : ℝ, ‖p x‖ ^ 2 ∂μ :=
    integral_nonneg fun _ ↦ sq_nonneg _
  have hB0 : 0 ≤ ∫ x : ℝ, ‖f x‖ ^ 2 ∂μ :=
    integral_nonneg fun _ ↦ sq_nonneg _
  have hholder' :
      (∫ x : ℝ, ‖p x‖ * ‖f x‖ ∂μ) ≤
        Real.sqrt (∫ x : ℝ, ‖p x‖ ^ 2 ∂μ) *
          Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2 ∂μ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    simpa only [Real.rpow_two] using hholder
  have hnorm :
      ‖∫ x : ℝ in -a..a, p x * f x‖ ≤
        ∫ x : ℝ, ‖p x‖ * ‖f x‖ ∂μ := by
    calc
      ‖∫ x : ℝ in -a..a, p x * f x‖ ≤
          ∫ x : ℝ in -a..a, ‖p x * f x‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by linarith)
      _ = ∫ x : ℝ in -a..a, ‖p x‖ * ‖f x‖ := by
        apply intervalIntegral.integral_congr
        intro x _hx
        exact norm_mul (p x) (f x)
      _ = ∫ x : ℝ, ‖p x‖ * ‖f x‖ ∂μ := by
        rw [intervalIntegral.integral_of_le (by linarith)]
  have hbound := hnorm.trans hholder'
  have hsq :
      ‖∫ x : ℝ in -a..a, p x * f x‖ ^ 2 ≤
        (∫ x : ℝ, ‖p x‖ ^ 2 ∂μ) *
          (∫ x : ℝ, ‖f x‖ ^ 2 ∂μ) := by
    calc
      ‖∫ x : ℝ in -a..a, p x * f x‖ ^ 2 ≤
          (Real.sqrt (∫ x : ℝ, ‖p x‖ ^ 2 ∂μ) *
            Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2 ∂μ)) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hbound
      _ = (∫ x : ℝ, ‖p x‖ ^ 2 ∂μ) *
          (∫ x : ℝ, ‖f x‖ ^ 2 ∂μ) := by
        rw [mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt hB0]
  rw [Complex.normSq_eq_norm_sq, clippedIntervalEnergy]
  change ‖∫ x : ℝ in -a..a, p x * f x‖ ^ 2 ≤ _
  simpa only [μ, I,
    intervalIntegral.integral_of_le (by linarith : -a ≤ a)] using hsq

private theorem weightedIntegral_oddTailSinePartialSum_tendsto
    (f : YoshidaOddTenTail) (p : ℝ → ℂ) (hp : Continuous p) :
    Tendsto
      (fun N : ℕ ↦ ∫ x : ℝ in -yoshidaA..yoshidaA,
        p x * oddTailSinePartialSum f N x)
      atTop
      (𝓝 (∫ x : ℝ in -yoshidaA..yoshidaA,
        p x * oddTenTailToClippedSmooth f x)) := by
  let W : ℝ := ∫ x : ℝ in -yoshidaA..yoshidaA, ‖p x‖ ^ 2
  have hW : 0 ≤ W := by
    dsimp only [W]
    exact intervalIntegral.integral_nonneg
      (by linarith [yoshidaA_pos]) (fun _ _ ↦ sq_nonneg _)
  have hsqBound (N : ℕ) :
      Complex.normSq
          (∫ x : ℝ in -yoshidaA..yoshidaA,
            p x * (oddTailSinePartialSum f N -
              oddTenTailToClippedSmooth f) x) ≤
        W * clippedIntervalEnergy
          (oddTailSinePartialSum f N - oddTenTailToClippedSmooth f) := by
    simpa only [W] using normSq_weightedIntegral_le_energy
      yoshidaA_pos p hp
        (oddTailSinePartialSum f N - oddTenTailToClippedSmooth f)
  have hrhs : Tendsto
      (fun N : ℕ ↦ W * clippedIntervalEnergy
        (oddTailSinePartialSum f N - oddTenTailToClippedSmooth f))
      atTop (𝓝 0) := by
    convert tendsto_const_nhds.mul
      (oddTailSinePartialSum_energy_remainder_tendsto_zero f) using 1
    norm_num
  have hnormSq : Tendsto
      (fun N : ℕ ↦ Complex.normSq
        (∫ x : ℝ in -yoshidaA..yoshidaA,
          p x * (oddTailSinePartialSum f N -
            oddTenTailToClippedSmooth f) x))
      atTop (𝓝 0) :=
    squeeze_zero (fun N ↦ Complex.normSq_nonneg _) hsqBound hrhs
  have hnorm : Tendsto
      (fun N : ℕ ↦
        ‖∫ x : ℝ in -yoshidaA..yoshidaA,
          p x * (oddTailSinePartialSum f N -
            oddTenTailToClippedSmooth f) x‖)
      atTop (𝓝 0) := by
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hnormSq
    simpa only [Function.comp_def, Complex.normSq_eq_norm_sq,
      Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt
  have hdiff : Tendsto
      (fun N : ℕ ↦
        ∫ x : ℝ in -yoshidaA..yoshidaA,
          p x * (oddTailSinePartialSum f N -
            oddTenTailToClippedSmooth f) x)
      atTop (𝓝 0) :=
    (tendsto_zero_iff_norm_tendsto_zero).2 hnorm
  have hsub (N : ℕ) :
      (∫ x : ℝ in -yoshidaA..yoshidaA,
        p x * (oddTailSinePartialSum f N -
          oddTenTailToClippedSmooth f) x) =
        (∫ x : ℝ in -yoshidaA..yoshidaA,
          p x * oddTailSinePartialSum f N x) -
        ∫ x : ℝ in -yoshidaA..yoshidaA,
          p x * oddTenTailToClippedSmooth f x := by
    rw [show (fun x : ℝ ↦
        p x * (oddTailSinePartialSum f N -
          oddTenTailToClippedSmooth f) x) =
        fun x ↦ p x * oddTailSinePartialSum f N x -
          p x * oddTenTailToClippedSmooth f x by
      funext x
      simp only [Submodule.coe_sub, Pi.sub_apply]
      ring]
    rw [intervalIntegral.integral_sub]
    · exact (hp.continuousOn.mul
        (oddTailSinePartialSum f N).property.1.continuousOn)
          |>.intervalIntegrable_of_Icc (by linarith [yoshidaA_pos])
    · exact (hp.continuousOn.mul
        (oddTenTailToClippedSmooth f).property.1.continuousOn)
          |>.intervalIntegrable_of_Icc (by linarith [yoshidaA_pos])
  apply tendsto_sub_nhds_zero_iff.mp
  convert hdiff using 1
  funext N
  exact (hsub N).symm

/-- The real centered profile canonically attached to an actual algebraic
tenth odd-tail vector. -/
def oddTailCenteredProfile (f : YoshidaOddTenTail) : ℝ → ℝ :=
  centeredRescale yoshidaA
    (fun y ↦ (oddTenTailToClippedSmooth f y).re)

private def oddTailP1Moment (f : YoshidaOddTenTail) : ℂ :=
  ((3 / (2 * yoshidaA) : ℝ) : ℂ) *
    ∫ y : ℝ in -yoshidaA..yoshidaA,
      ((y / yoshidaA : ℝ) : ℂ) * oddTenTailToClippedSmooth f y

private def oddTailP3Moment (f : YoshidaOddTenTail) : ℂ :=
  ((7 / (2 * yoshidaA) : ℝ) : ℂ) *
    ∫ y : ℝ in -yoshidaA..yoshidaA,
      (centeredP3 (y / yoshidaA) : ℂ) * oddTenTailToClippedSmooth f y

private def oddTailP1FourierWeight (k : ℕ) : ℂ :=
  let n : ℕ := 11 + k
  ((-3 * (-1 : ℝ) ^ n /
    (Real.sqrt yoshidaA * (Real.pi * (n : ℝ))) : ℝ) : ℂ)

private def oddTailP3FourierWeight (k : ℕ) : ℂ :=
  let n : ℕ := 11 + k
  ((7 * (-1 : ℝ) ^ n / Real.sqrt yoshidaA *
    (-1 / (Real.pi * (n : ℝ)) +
      15 / (Real.pi * (n : ℝ)) ^ 3) : ℝ) : ℂ)

private theorem p1Moment_oddMode (n : ℕ) (hn : n ≠ 0) :
    ((3 / (2 * yoshidaA) : ℝ) : ℂ) *
        (∫ y : ℝ in -yoshidaA..yoshidaA,
          ((y / yoshidaA : ℝ) : ℂ) *
            yoshidaClippedOddMode yoshidaA n y) =
      ((-3 * (-1 : ℝ) ^ n /
        (Real.sqrt yoshidaA * (Real.pi * (n : ℝ))) : ℝ) : ℂ) := by
  let q : ℝ → ℂ := fun y ↦
    ((y / yoshidaA : ℝ) : ℂ) * yoshidaClippedOddMode yoshidaA n y
  have hsubst := intervalIntegral.smul_integral_comp_mul_add
    (a := (-1 : ℝ)) (b := 1) q yoshidaA 0
  have hscale :
      (∫ y : ℝ in -yoshidaA..yoshidaA, q y) =
        yoshidaA • ∫ x : ℝ in -1..1, q (yoshidaA * x) := by
    simpa only [mul_neg, mul_one, add_zero, mul_zero, zero_add] using hsubst.symm
  have hcenter :
      (∫ x : ℝ in -1..1, q (yoshidaA * x)) =
        (((Real.sqrt yoshidaA)⁻¹ : ℝ) : ℂ) *
          ((∫ x : ℝ in -1..1,
            x * Real.sin (Real.pi * (n : ℝ) * x) : ℝ) : ℂ) := by
    calc
      (∫ x : ℝ in -1..1, q (yoshidaA * x)) =
          ∫ x : ℝ in -1..1,
            (((Real.sqrt yoshidaA)⁻¹ : ℝ) : ℂ) *
              ((x * Real.sin (Real.pi * (n : ℝ) * x) : ℝ) : ℂ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : x ∈ Set.Icc (-1 : ℝ) 1 := by
          simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx
        have hax : yoshidaA * x ∈ Set.Icc (-yoshidaA) yoshidaA := by
          constructor
          · have h := mul_le_mul_of_nonneg_left hx'.1 yoshidaA_pos.le
            simpa only [mul_neg, mul_one] using h
          · have h := mul_le_mul_of_nonneg_left hx'.2 yoshidaA_pos.le
            simpa only [mul_one] using h
        dsimp only [q]
        rw [yoshidaClippedOddMode_apply_of_mem yoshidaA_pos n hax]
        push_cast
        field_simp [yoshidaA_pos.ne']
      _ = (((Real.sqrt yoshidaA)⁻¹ : ℝ) : ℂ) *
          ∫ x : ℝ in -1..1,
            ((x * Real.sin (Real.pi * (n : ℝ) * x) : ℝ) : ℂ) := by
        exact intervalIntegral.integral_const_mul
          (μ := volume) ((((Real.sqrt yoshidaA)⁻¹ : ℝ) : ℂ))
          (fun x : ℝ ↦
            ((x * Real.sin (Real.pi * (n : ℝ) * x) : ℝ) : ℂ))
      _ = _ := by rw [intervalIntegral.integral_ofReal]
  rw [show (∫ y : ℝ in -yoshidaA..yoshidaA,
      ((y / yoshidaA : ℝ) : ℂ) * yoshidaClippedOddMode yoshidaA n y) =
      ∫ y : ℝ in -yoshidaA..yoshidaA, q y by rfl,
    hscale, hcenter, integral_mul_sin_nat_pi n hn]
  have hsqrt : Real.sqrt yoshidaA ≠ 0 :=
    (Real.sqrt_pos.2 yoshidaA_pos).ne'
  simp only [Complex.real_smul]
  have hreal :
      (3 / (2 * yoshidaA) : ℝ) *
          (yoshidaA * ((Real.sqrt yoshidaA)⁻¹ *
            (-2 * (-1 : ℝ) ^ n / (Real.pi * (n : ℝ))))) =
        -3 * (-1 : ℝ) ^ n /
          (Real.sqrt yoshidaA * (Real.pi * (n : ℝ))) := by
    field_simp [yoshidaA_pos.ne', hsqrt, Real.pi_ne_zero, hn]
  exact_mod_cast hreal

private theorem p3Moment_oddMode (n : ℕ) (hn : n ≠ 0) :
    ((7 / (2 * yoshidaA) : ℝ) : ℂ) *
        (∫ y : ℝ in -yoshidaA..yoshidaA,
          (centeredP3 (y / yoshidaA) : ℂ) *
            yoshidaClippedOddMode yoshidaA n y) =
      ((7 * (-1 : ℝ) ^ n / Real.sqrt yoshidaA *
        (-1 / (Real.pi * (n : ℝ)) +
          15 / (Real.pi * (n : ℝ)) ^ 3) : ℝ) : ℂ) := by
  let q : ℝ → ℂ := fun y ↦
    (centeredP3 (y / yoshidaA) : ℂ) *
      yoshidaClippedOddMode yoshidaA n y
  have hsubst := intervalIntegral.smul_integral_comp_mul_add
    (a := (-1 : ℝ)) (b := 1) q yoshidaA 0
  have hscale :
      (∫ y : ℝ in -yoshidaA..yoshidaA, q y) =
        yoshidaA • ∫ x : ℝ in -1..1, q (yoshidaA * x) := by
    simpa only [mul_neg, mul_one, add_zero, mul_zero, zero_add] using hsubst.symm
  have hcenter :
      (∫ x : ℝ in -1..1, q (yoshidaA * x)) =
        (((Real.sqrt yoshidaA)⁻¹ : ℝ) : ℂ) *
          ((∫ x : ℝ in -1..1,
            centeredP3 x * Real.sin (Real.pi * (n : ℝ) * x) : ℝ) : ℂ) := by
    calc
      (∫ x : ℝ in -1..1, q (yoshidaA * x)) =
          ∫ x : ℝ in -1..1,
            (((Real.sqrt yoshidaA)⁻¹ : ℝ) : ℂ) *
              ((centeredP3 x *
                Real.sin (Real.pi * (n : ℝ) * x) : ℝ) : ℂ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : x ∈ Set.Icc (-1 : ℝ) 1 := by
          simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx
        have hax : yoshidaA * x ∈ Set.Icc (-yoshidaA) yoshidaA := by
          constructor
          · have h := mul_le_mul_of_nonneg_left hx'.1 yoshidaA_pos.le
            simpa only [mul_neg, mul_one] using h
          · have h := mul_le_mul_of_nonneg_left hx'.2 yoshidaA_pos.le
            simpa only [mul_one] using h
        dsimp only [q]
        rw [yoshidaClippedOddMode_apply_of_mem yoshidaA_pos n hax]
        push_cast
        field_simp [yoshidaA_pos.ne']
      _ = (((Real.sqrt yoshidaA)⁻¹ : ℝ) : ℂ) *
          ∫ x : ℝ in -1..1,
            ((centeredP3 x *
              Real.sin (Real.pi * (n : ℝ) * x) : ℝ) : ℂ) := by
        exact intervalIntegral.integral_const_mul
          (μ := volume) ((((Real.sqrt yoshidaA)⁻¹ : ℝ) : ℂ))
          (fun x : ℝ ↦ ((centeredP3 x *
            Real.sin (Real.pi * (n : ℝ) * x) : ℝ) : ℂ))
      _ = _ := by rw [intervalIntegral.integral_ofReal]
  rw [show (∫ y : ℝ in -yoshidaA..yoshidaA,
      (centeredP3 (y / yoshidaA) : ℂ) *
        yoshidaClippedOddMode yoshidaA n y) =
      ∫ y : ℝ in -yoshidaA..yoshidaA, q y by rfl,
    hscale, hcenter, integral_centeredP3_mul_sin_nat_pi n hn]
  have hsqrt : Real.sqrt yoshidaA ≠ 0 :=
    (Real.sqrt_pos.2 yoshidaA_pos).ne'
  simp only [Complex.real_smul]
  have hreal :
      (7 / (2 * yoshidaA) : ℝ) *
          (yoshidaA * ((Real.sqrt yoshidaA)⁻¹ *
            (2 * (-1 : ℝ) ^ n *
              (-1 / (Real.pi * (n : ℝ)) +
                15 / (Real.pi * (n : ℝ)) ^ 3)))) =
        7 * (-1 : ℝ) ^ n / Real.sqrt yoshidaA *
          (-1 / (Real.pi * (n : ℝ)) +
            15 / (Real.pi * (n : ℝ)) ^ 3) := by
    field_simp [yoshidaA_pos.ne', hsqrt, Real.pi_ne_zero, hn]
  exact_mod_cast hreal

private theorem norm_oddTailP1FourierWeight_sq_le (k : ℕ) :
    ‖oddTailP1FourierWeight k‖ ^ 2 ≤
      (1 / yoshidaA : ℝ) *
        (1 / (((11 + k : ℕ) : ℝ) ^ 2)) := by
  let n : ℕ := 11 + k
  have hn : n ≠ 0 := by
    dsimp only [n]
    omega
  have hnPos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by omega)
  have hsqrtPos : 0 < Real.sqrt yoshidaA :=
    Real.sqrt_pos.2 yoshidaA_pos
  have hsqrtSq : Real.sqrt yoshidaA ^ 2 = yoshidaA :=
    Real.sq_sqrt yoshidaA_pos.le
  have hsign : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
    rw [← pow_mul]
    norm_num
  have hpiSq : (9 : ℝ) ≤ Real.pi ^ 2 := by
    nlinarith [Real.pi_gt_three]
  change ‖((-3 * (-1 : ℝ) ^ n /
    (Real.sqrt yoshidaA * (Real.pi * (n : ℝ))) : ℝ) : ℂ)‖ ^ 2 ≤
      (1 / yoshidaA : ℝ) * (1 / ((n : ℝ) ^ 2))
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [div_pow]
  have hdenPos : 0 <
      (Real.sqrt yoshidaA * (Real.pi * (n : ℝ))) ^ 2 := by
    exact sq_pos_of_pos
      (mul_pos hsqrtPos (mul_pos Real.pi_pos hnPos))
  have hrhsDenPos : 0 < yoshidaA * (n : ℝ) ^ 2 := by
    exact mul_pos yoshidaA_pos (sq_pos_of_pos hnPos)
  rw [show (1 / yoshidaA : ℝ) * (1 / (n : ℝ) ^ 2) =
      1 / (yoshidaA * (n : ℝ) ^ 2) by ring]
  rw [div_le_div_iff₀ hdenPos hrhsDenPos]
  rw [mul_pow, mul_pow, hsqrtSq, hsign]
  have hprod : 0 ≤ (Real.pi ^ 2 - 9) *
      (yoshidaA * (n : ℝ) ^ 2) :=
    mul_nonneg (sub_nonneg.mpr hpiSq)
      (mul_nonneg yoshidaA_pos.le (sq_nonneg _))
  nlinarith

private theorem summable_sq_oddTailP1FourierWeight :
    Summable (fun k : ℕ ↦ ‖oddTailP1FourierWeight k‖ ^ 2) := by
  let b : ℕ → ℝ := fun k ↦ 1 / (((11 + k : ℕ) : ℝ) ^ 2)
  have hb : Summable b := by
    simpa [b, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      summable_invPow_tail 10 2 (by omega)
  have hmajor : Summable (fun k ↦ (1 / yoshidaA : ℝ) * b k) :=
    hb.mul_left (1 / yoshidaA : ℝ)
  exact hmajor.of_nonneg_of_le
    (fun k ↦ sq_nonneg ‖oddTailP1FourierWeight k‖)
    (fun k ↦ by
      simpa only [b] using norm_oddTailP1FourierWeight_sq_le k)

private theorem tsum_sq_oddTailP1FourierWeight_le :
    (∑' k : ℕ, ‖oddTailP1FourierWeight k‖ ^ 2) ≤
      1 / (10 * yoshidaA) := by
  let b : ℕ → ℝ := fun k ↦ 1 / (((11 + k : ℕ) : ℝ) ^ 2)
  have hb : Summable b := by
    simpa [b, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      summable_invPow_tail 10 2 (by omega)
  have hbase : (∑' k : ℕ, b k) ≤ 1 / (10 : ℝ) := by
    simpa [b, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      invSq_tail_le 10 (by omega)
  calc
    (∑' k : ℕ, ‖oddTailP1FourierWeight k‖ ^ 2) ≤
        ∑' k : ℕ, (1 / yoshidaA : ℝ) * b k :=
      summable_sq_oddTailP1FourierWeight.tsum_le_tsum
        (fun k ↦ by
          simpa only [b] using norm_oddTailP1FourierWeight_sq_le k)
        (hb.mul_left (1 / yoshidaA : ℝ))
    _ = (1 / yoshidaA : ℝ) * ∑' k : ℕ, b k :=
      hb.tsum_mul_left (1 / yoshidaA : ℝ)
    _ ≤ (1 / yoshidaA : ℝ) * (1 / 10 : ℝ) := by
      exact mul_le_mul_of_nonneg_left hbase
        (div_nonneg (by norm_num) yoshidaA_pos.le)
    _ = 1 / (10 * yoshidaA) := by ring

private theorem abs_p3_frequencyFactor_le
    (n : ℕ) (hn : 11 ≤ n) :
    |-1 / (Real.pi * (n : ℝ)) +
        15 / (Real.pi * (n : ℝ)) ^ 3| ≤
      1 / (Real.pi * (n : ℝ)) := by
  let t : ℝ := Real.pi * (n : ℝ)
  have hnPos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by omega)
  have ht : 0 < t := mul_pos Real.pi_pos hnPos
  have htLarge : (15 : ℝ) ≤ t ^ 2 := by
    have hnThree : (3 : ℝ) ≤ n := by exact_mod_cast (by omega : 3 ≤ n)
    dsimp only [t]
    nlinarith [Real.pi_gt_three,
      mul_nonneg (sub_nonneg.mpr hnThree) Real.pi_pos.le]
  have hfrac : 15 / t ^ 3 ≤ 1 / t := by
    rw [div_le_div_iff₀ (pow_pos ht 3) ht]
    have hmul : 0 ≤ t * (t ^ 2 - 15) :=
      mul_nonneg ht.le (sub_nonneg.mpr htLarge)
    nlinarith
  have hpositive : 0 ≤ 15 / t ^ 3 := by positivity
  have hinv : 0 ≤ 1 / t := by positivity
  change |-1 / t + 15 / t ^ 3| ≤ 1 / t
  rw [show -1 / t = -(1 / t) by ring]
  rw [abs_le]
  constructor <;> linarith

private theorem norm_oddTailP3FourierWeight_sq_le (k : ℕ) :
    ‖oddTailP3FourierWeight k‖ ^ 2 ≤
      (49 / (9 * yoshidaA) : ℝ) *
        (1 / (((11 + k : ℕ) : ℝ) ^ 2)) := by
  let n : ℕ := 11 + k
  let t : ℝ := Real.pi * (n : ℝ)
  let q : ℝ := -1 / t + 15 / t ^ 3
  have hn : 11 ≤ n := by
    dsimp only [n]
    omega
  have hnPos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by omega)
  have ht : 0 < t := by
    dsimp only [t]
    exact mul_pos Real.pi_pos hnPos
  have hsqrtSq : Real.sqrt yoshidaA ^ 2 = yoshidaA :=
    Real.sq_sqrt yoshidaA_pos.le
  have hsign : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
    rw [← pow_mul]
    norm_num
  have habs : |q| ≤ 1 / t := by
    dsimp only [q, t]
    exact abs_p3_frequencyFactor_le n hn
  have hqSq : q ^ 2 ≤ (1 / t) ^ 2 := by
    rw [← sq_abs q]
    exact (sq_le_sq₀ (abs_nonneg q) (by positivity)).2 habs
  have hpiSq : (9 : ℝ) ≤ Real.pi ^ 2 := by
    nlinarith [Real.pi_gt_three]
  have hden : 9 * (n : ℝ) ^ 2 ≤ t ^ 2 := by
    dsimp only [t]
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hpiSq (sq_nonneg _)
  have hfreqSq : (1 / t) ^ 2 ≤
      (1 / 9 : ℝ) * (1 / (n : ℝ) ^ 2) := by
    have hinv : 1 / t ^ 2 ≤ 1 / (9 * (n : ℝ) ^ 2) :=
      one_div_le_one_div_of_le (by positivity) hden
    calc
      (1 / t) ^ 2 = 1 / t ^ 2 := by ring
      _ ≤ 1 / (9 * (n : ℝ) ^ 2) := hinv
      _ = (1 / 9 : ℝ) * (1 / (n : ℝ) ^ 2) := by ring
  have hnorm :
      ‖((7 * (-1 : ℝ) ^ n / Real.sqrt yoshidaA * q : ℝ) : ℂ)‖ ^ 2 =
        (49 / yoshidaA : ℝ) * q ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    simp only [mul_pow, div_pow, hsign, hsqrtSq]
    field_simp [yoshidaA_pos.ne']
    ring
  change ‖((7 * (-1 : ℝ) ^ n / Real.sqrt yoshidaA * q : ℝ) : ℂ)‖ ^ 2 ≤
      (49 / (9 * yoshidaA) : ℝ) * (1 / (n : ℝ) ^ 2)
  rw [hnorm]
  calc
    (49 / yoshidaA : ℝ) * q ^ 2 ≤
        (49 / yoshidaA : ℝ) * (1 / t) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hqSq
        (div_nonneg (by norm_num) yoshidaA_pos.le)
    _ ≤ (49 / yoshidaA : ℝ) *
        ((1 / 9 : ℝ) * (1 / (n : ℝ) ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hfreqSq
        (div_nonneg (by norm_num) yoshidaA_pos.le)
    _ = _ := by ring

private theorem summable_sq_oddTailP3FourierWeight :
    Summable (fun k : ℕ ↦ ‖oddTailP3FourierWeight k‖ ^ 2) := by
  let b : ℕ → ℝ := fun k ↦ 1 / (((11 + k : ℕ) : ℝ) ^ 2)
  have hb : Summable b := by
    simpa [b, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      summable_invPow_tail 10 2 (by omega)
  have hmajor : Summable
      (fun k ↦ (49 / (9 * yoshidaA) : ℝ) * b k) :=
    hb.mul_left (49 / (9 * yoshidaA) : ℝ)
  exact hmajor.of_nonneg_of_le
    (fun k ↦ sq_nonneg ‖oddTailP3FourierWeight k‖)
    (fun k ↦ by
      simpa only [b] using norm_oddTailP3FourierWeight_sq_le k)

private theorem tsum_sq_oddTailP3FourierWeight_le :
    (∑' k : ℕ, ‖oddTailP3FourierWeight k‖ ^ 2) ≤
      49 / (90 * yoshidaA) := by
  let b : ℕ → ℝ := fun k ↦ 1 / (((11 + k : ℕ) : ℝ) ^ 2)
  have hb : Summable b := by
    simpa [b, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      summable_invPow_tail 10 2 (by omega)
  have hbase : (∑' k : ℕ, b k) ≤ 1 / (10 : ℝ) := by
    simpa [b, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      invSq_tail_le 10 (by omega)
  calc
    (∑' k : ℕ, ‖oddTailP3FourierWeight k‖ ^ 2) ≤
        ∑' k : ℕ, (49 / (9 * yoshidaA) : ℝ) * b k :=
      summable_sq_oddTailP3FourierWeight.tsum_le_tsum
        (fun k ↦ by
          simpa only [b] using norm_oddTailP3FourierWeight_sq_le k)
        (hb.mul_left (49 / (9 * yoshidaA) : ℝ))
    _ = (49 / (9 * yoshidaA) : ℝ) * ∑' k : ℕ, b k :=
      hb.tsum_mul_left (49 / (9 * yoshidaA) : ℝ)
    _ ≤ (49 / (9 * yoshidaA) : ℝ) * (1 / 10 : ℝ) := by
      exact mul_le_mul_of_nonneg_left hbase
        (div_nonneg (by norm_num)
          (mul_nonneg (by norm_num) yoshidaA_pos.le))
    _ = 49 / (90 * yoshidaA) := by ring

/-!
# The exact odd one/three raw-energy gap

This file records the purely algebraic last step in the odd Fourier-tail
argument.  Once the degree-one and degree-three centered Legendre
coefficients satisfy their sharp Fourier-tail bounds, the existing
one/three/tail spectral estimate gives the exact constant `383 / 180`.
-/

/-- The exact `383 / 180` consequence of the centered one/three/tail
estimate.  The two coefficient hypotheses are precisely the Fourier-tail
bounds supplied by frequencies `n ≥ 11`; no slack is introduced in this
algebraic assembly step. -/
theorem centeredRawLogEnergy_ge_three_hundred_eighty_three_div_one_hundred_eighty
    (w : ℝ → ℝ) (hwcont : Continuous w)
    (hf : MemLp (fun t : unitInterval ↦ centeredPullback w (t : ℝ)) 2)
    (henergy : Integrable (unitIntervalRawLogEnergyIntegrand
      (fun t : unitInterval ↦ centeredPullback w (t : ℝ))))
    (hwodd : Function.Odd w)
    (hone : centeredOddP1Coefficient w ^ 2 ≤
      (1 / 10 : ℝ) * ∫ x : ℝ in -1..1, w x ^ 2)
    (hthree : centeredOddP3Coefficient w ^ 2 ≤
      (49 / 90 : ℝ) * ∫ x : ℝ in -1..1, w x ^ 2) :
    (383 / 180 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) ≤
      centeredRawLogEnergy w / 4 := by
  have hspectral := centered_odd_one_three_tail_energy_le
    w hwcont hf henergy hwodd
  have hresidual := integral_centeredOddOneThreeResidual_sq w hwcont
  rw [hresidual] at hspectral
  nlinarith [sq_nonneg (centeredOddP1Coefficient w),
    sq_nonneg (centeredOddP3Coefficient w)]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseOddRawGap
