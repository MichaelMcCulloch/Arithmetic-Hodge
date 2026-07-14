import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSymmetricCoercivity

set_option autoImplicit false

open MeasureTheory Real

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoLaplaceModes

noncomputable section

open YoshidaFactorTwoPhaseSymmetricCoercivity
open CenteredEndpointCorrelation
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoCenteredPhysical
open YoshidaEndpointHyperbolicBound
open YoshidaRenormalizedGeometricKernel

/-!
# Exact centered Laplace moments of Fourier modes

The symmetric factor-two kernel is a signed sum of hyperbolic ranks.  These
identities give the exact coordinates of those ranks on the canonical
centered cosine and sine modes; no numerical approximation is involved.
-/

/-- The finite hyperbolic-rank truncation of the complete symmetric weight. -/
def factorTwoSymmetricRankPartialWeight (N : ℕ) (t : ℝ) : ℝ :=
  2 * Real.exp yoshidaEndpointA *
      Real.cosh (yoshidaEndpointA * t / 2) -
    ∑ m ∈ Finset.range N,
      2 * Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
        Real.cosh (yoshidaEndpointA * oddRate (m + 1) * t)

/-- The corresponding finite-rank truncation of the archimedean block. -/
def factorTwoCenteredArchPartial
    (w : ℝ → ℝ) (N : ℕ) : ℝ :=
  yoshidaEndpointA * ∫ t : ℝ in 0..2,
    factorTwoSymmetricRankPartialWeight N t *
      centeredEndpointCorrelation w t

/-- On an even profile, the finite symmetric archimedean truncation is one
positive growing Laplace square minus the finite decaying square family. -/
theorem factorTwoCenteredArchPartial_eq_evenSquares
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w) (N : ℕ) :
    factorTwoCenteredArchPartial w N =
      yoshidaEndpointA *
        (Real.exp yoshidaEndpointA *
            centeredCoshMoment w (yoshidaEndpointA / 2) ^ 2 -
          ∑ m ∈ Finset.range N,
            Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
              centeredCoshMoment w
                (yoshidaEndpointA * oddRate (m + 1)) ^ 2) := by
  let C : ℝ → ℝ := centeredEndpointCorrelation w
  have hC : Continuous C :=
    continuous_centeredEndpointCorrelation_of_continuous w hw
  have hhead := two_mul_integral_cosh_mul_centeredCorrelation_of_even
    w hw heven (yoshidaEndpointA / 2)
  have htail (m : ℕ) :=
    two_mul_integral_cosh_mul_centeredCorrelation_of_even
      w hw heven (yoshidaEndpointA * oddRate (m + 1))
  have hheadInt : IntervalIntegrable
      (fun t : ℝ ↦
        (2 * Real.exp yoshidaEndpointA *
          Real.cosh (yoshidaEndpointA * t / 2)) * C t)
      volume 0 2 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have htailInt : ∀ m ∈ Finset.range N, IntervalIntegrable
      (fun t : ℝ ↦
        (2 * Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          Real.cosh (yoshidaEndpointA * oddRate (m + 1) * t)) * C t)
      volume 0 2 := by
    intro m _hm
    apply Continuous.intervalIntegrable
    fun_prop
  unfold factorTwoCenteredArchPartial factorTwoSymmetricRankPartialWeight
  rw [show (fun t : ℝ ↦
      (2 * Real.exp yoshidaEndpointA *
          Real.cosh (yoshidaEndpointA * t / 2) -
        ∑ m ∈ Finset.range N,
          2 * Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
            Real.cosh (yoshidaEndpointA * oddRate (m + 1) * t)) * C t) =
      fun t ↦
        (2 * Real.exp yoshidaEndpointA *
          Real.cosh (yoshidaEndpointA * t / 2)) * C t -
        (∑ m ∈ Finset.range N, fun t : ℝ ↦
          (2 * Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
            Real.cosh (yoshidaEndpointA * oddRate (m + 1) * t)) * C t) t by
      funext t
      simp only [Finset.sum_apply]
      rw [sub_mul, Finset.sum_mul]]
  apply congrArg (fun z : ℝ ↦ yoshidaEndpointA * z)
  rw [intervalIntegral.integral_sub hheadInt
      (IntervalIntegrable.sum (Finset.range N) htailInt)]
  simp only [Finset.sum_apply]
  rw [intervalIntegral.integral_finset_sum htailInt]
  rw [show (∫ t : ℝ in 0..2,
      (2 * Real.exp yoshidaEndpointA *
        Real.cosh (yoshidaEndpointA * t / 2)) * C t) =
      Real.exp yoshidaEndpointA *
        (2 * ∫ t : ℝ in 0..2,
          Real.cosh ((yoshidaEndpointA / 2) * t) * C t) by
      rw [show (fun t : ℝ ↦
          (2 * Real.exp yoshidaEndpointA *
            Real.cosh (yoshidaEndpointA * t / 2)) * C t) =
          fun t ↦ Real.exp yoshidaEndpointA *
            (2 * (Real.cosh ((yoshidaEndpointA / 2) * t) * C t)) by
          funext t
          ring_nf,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]]
  simp_rw [show ∀ m : ℕ,
      (∫ t : ℝ in 0..2,
        (2 * Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          Real.cosh (yoshidaEndpointA * oddRate (m + 1) * t)) * C t) =
      Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
        (2 * ∫ t : ℝ in 0..2,
          Real.cosh ((yoshidaEndpointA * oddRate (m + 1)) * t) * C t) by
      intro m
      rw [show (fun t : ℝ ↦
          (2 * Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
            Real.cosh (yoshidaEndpointA * oddRate (m + 1) * t)) * C t) =
          fun t ↦ Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
            (2 * (Real.cosh
              ((yoshidaEndpointA * oddRate (m + 1)) * t) * C t)) by
          funext t
          ring_nf,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]]
  dsimp only [C]
  rw [hhead]
  simp_rw [htail]

/-- On an odd profile, the same finite truncation has the opposite signs:
the growing rank is negative and every decaying rank is positive. -/
theorem factorTwoCenteredArchPartial_eq_oddSquares
    (w : ℝ → ℝ) (hw : Continuous w) (hodd : Function.Odd w) (N : ℕ) :
    factorTwoCenteredArchPartial w N =
      yoshidaEndpointA *
        (-Real.exp yoshidaEndpointA *
            centeredSinhMoment w (yoshidaEndpointA / 2) ^ 2 +
          ∑ m ∈ Finset.range N,
            Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
              centeredSinhMoment w
                (yoshidaEndpointA * oddRate (m + 1)) ^ 2) := by
  let C : ℝ → ℝ := centeredEndpointCorrelation w
  have hC : Continuous C :=
    continuous_centeredEndpointCorrelation_of_continuous w hw
  have hhead := two_mul_integral_cosh_mul_centeredCorrelation_of_odd
    w hw hodd (yoshidaEndpointA / 2)
  have htail (m : ℕ) :=
    two_mul_integral_cosh_mul_centeredCorrelation_of_odd
      w hw hodd (yoshidaEndpointA * oddRate (m + 1))
  have hheadInt : IntervalIntegrable
      (fun t : ℝ ↦
        (2 * Real.exp yoshidaEndpointA *
          Real.cosh (yoshidaEndpointA * t / 2)) * C t)
      volume 0 2 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have htailInt : ∀ m ∈ Finset.range N, IntervalIntegrable
      (fun t : ℝ ↦
        (2 * Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          Real.cosh (yoshidaEndpointA * oddRate (m + 1) * t)) * C t)
      volume 0 2 := by
    intro m _hm
    apply Continuous.intervalIntegrable
    fun_prop
  unfold factorTwoCenteredArchPartial factorTwoSymmetricRankPartialWeight
  rw [show (fun t : ℝ ↦
      (2 * Real.exp yoshidaEndpointA *
          Real.cosh (yoshidaEndpointA * t / 2) -
        ∑ m ∈ Finset.range N,
          2 * Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
            Real.cosh (yoshidaEndpointA * oddRate (m + 1) * t)) * C t) =
      fun t ↦
        (2 * Real.exp yoshidaEndpointA *
          Real.cosh (yoshidaEndpointA * t / 2)) * C t -
        (∑ m ∈ Finset.range N, fun t : ℝ ↦
          (2 * Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
            Real.cosh (yoshidaEndpointA * oddRate (m + 1) * t)) * C t) t by
      funext t
      simp only [Finset.sum_apply]
      rw [sub_mul, Finset.sum_mul]]
  apply congrArg (fun z : ℝ ↦ yoshidaEndpointA * z)
  rw [intervalIntegral.integral_sub hheadInt
      (IntervalIntegrable.sum (Finset.range N) htailInt)]
  simp only [Finset.sum_apply]
  rw [intervalIntegral.integral_finset_sum htailInt]
  rw [show (∫ t : ℝ in 0..2,
      (2 * Real.exp yoshidaEndpointA *
        Real.cosh (yoshidaEndpointA * t / 2)) * C t) =
      Real.exp yoshidaEndpointA *
        (2 * ∫ t : ℝ in 0..2,
          Real.cosh ((yoshidaEndpointA / 2) * t) * C t) by
      rw [show (fun t : ℝ ↦
          (2 * Real.exp yoshidaEndpointA *
            Real.cosh (yoshidaEndpointA * t / 2)) * C t) =
          fun t ↦ Real.exp yoshidaEndpointA *
            (2 * (Real.cosh ((yoshidaEndpointA / 2) * t) * C t)) by
          funext t
          ring_nf,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]]
  simp_rw [show ∀ m : ℕ,
      (∫ t : ℝ in 0..2,
        (2 * Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
          Real.cosh (yoshidaEndpointA * oddRate (m + 1) * t)) * C t) =
      Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
        (2 * ∫ t : ℝ in 0..2,
          Real.cosh ((yoshidaEndpointA * oddRate (m + 1)) * t) * C t) by
      intro m
      rw [show (fun t : ℝ ↦
          (2 * Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
            Real.cosh (yoshidaEndpointA * oddRate (m + 1) * t)) * C t) =
          fun t ↦ Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
            (2 * (Real.cosh
              ((yoshidaEndpointA * oddRate (m + 1)) * t) * C t)) by
          funext t
          ring_nf,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]]
  dsimp only [C]
  rw [hhead]
  simp_rw [htail]
  simp only [mul_neg, Finset.sum_neg_distrib, sub_neg_eq_add]
  ring

/-- Exact even Laplace moment of the centered cosine mode. -/
theorem centeredCoshMoment_cos_nat_pi
    (lambda : ℝ) (hlambda : 0 < lambda) (n : ℕ) :
    centeredCoshMoment
        (fun x : ℝ ↦ Real.cos (Real.pi * (n : ℝ) * x)) lambda =
      2 * lambda * Real.sinh lambda * (-1 : ℝ) ^ n /
        (lambda ^ 2 + (Real.pi * (n : ℝ)) ^ 2) := by
  let mu : ℝ := Real.pi * (n : ℝ)
  let den : ℝ := lambda ^ 2 + mu ^ 2
  have hden : den ≠ 0 := by
    dsimp only [den]
    positivity
  let F : ℝ → ℝ := fun x ↦
    (lambda * Real.sinh (lambda * x) * Real.cos (mu * x) +
      mu * Real.cosh (lambda * x) * Real.sin (mu * x)) / den
  have hderiv (x : ℝ) :
      HasDerivAt F
        (Real.cosh (lambda * x) * Real.cos (mu * x)) x := by
    have hsinh : HasDerivAt (fun y : ℝ ↦ Real.sinh (lambda * y))
        (lambda * Real.cosh (lambda * x)) x := by
      convert (Real.hasDerivAt_sinh (lambda * x)).comp x
        ((hasDerivAt_id x).const_mul lambda) using 1
      all_goals ring
    have hcosh : HasDerivAt (fun y : ℝ ↦ Real.cosh (lambda * y))
        (lambda * Real.sinh (lambda * x)) x := by
      convert (Real.hasDerivAt_cosh (lambda * x)).comp x
        ((hasDerivAt_id x).const_mul lambda) using 1
      all_goals ring
    have hsin : HasDerivAt (fun y : ℝ ↦ Real.sin (mu * y))
        (mu * Real.cos (mu * x)) x := by
      convert (Real.hasDerivAt_sin (mu * x)).comp x
        ((hasDerivAt_id x).const_mul mu) using 1
      all_goals ring
    have hcos : HasDerivAt (fun y : ℝ ↦ Real.cos (mu * y))
        (-mu * Real.sin (mu * x)) x := by
      convert (Real.hasDerivAt_cos (mu * x)).comp x
        ((hasDerivAt_id x).const_mul mu) using 1
      all_goals ring
    dsimp only [F]
    convert ((((hsinh.const_mul lambda).mul hcos).add
      ((hcosh.const_mul mu).mul hsin)).div_const den) using 1
    dsimp only [den]
    field_simp [hden]
    ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _hx ↦ hderiv x)
      (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
  unfold centeredCoshMoment
  rw [show (fun x : ℝ ↦
      Real.cosh (lambda * x) *
        Real.cos (Real.pi * (n : ℝ) * x)) =
      fun x ↦ Real.cosh (lambda * x) * Real.cos (mu * x) by rfl,
    hint]
  dsimp only [F]
  have hmueq : mu = (n : ℝ) * Real.pi := by
    dsimp only [mu]
    ring
  have hsinPos : Real.sin (mu * 1) = 0 := by
    rw [hmueq, mul_one, Real.sin_nat_mul_pi]
  have hcosPos : Real.cos (mu * 1) = (-1 : ℝ) ^ n := by
    rw [hmueq, mul_one, Real.cos_nat_mul_pi]
  have hsinNeg : Real.sin (mu * (-1)) = 0 := by
    rw [show mu * (-1) = -(mu * 1) by ring, Real.sin_neg, hsinPos,
      neg_zero]
  have hcosNeg : Real.cos (mu * (-1)) = (-1 : ℝ) ^ n := by
    rw [show mu * (-1) = -(mu * 1) by ring, Real.cos_neg, hcosPos]
  rw [hsinPos, hcosPos, hsinNeg, hcosNeg,
    show lambda * 1 = lambda by ring,
    show lambda * (-1) = -lambda by ring,
    Real.sinh_neg]
  dsimp only [den, mu] at hden ⊢
  field_simp [hden]
  ring

/-- Exact odd Laplace moment of the centered sine mode. -/
theorem centeredSinhMoment_sin_nat_pi
    (lambda : ℝ) (hlambda : 0 < lambda) (n : ℕ) :
    centeredSinhMoment
        (fun x : ℝ ↦ Real.sin (Real.pi * (n : ℝ) * x)) lambda =
      -2 * (Real.pi * (n : ℝ)) * Real.sinh lambda * (-1 : ℝ) ^ n /
        (lambda ^ 2 + (Real.pi * (n : ℝ)) ^ 2) := by
  let mu : ℝ := Real.pi * (n : ℝ)
  let den : ℝ := lambda ^ 2 + mu ^ 2
  have hden : den ≠ 0 := by
    dsimp only [den]
    positivity
  let F : ℝ → ℝ := fun x ↦
    (lambda * Real.cosh (lambda * x) * Real.sin (mu * x) -
      mu * Real.sinh (lambda * x) * Real.cos (mu * x)) / den
  have hderiv (x : ℝ) :
      HasDerivAt F
        (Real.sinh (lambda * x) * Real.sin (mu * x)) x := by
    have hsinh : HasDerivAt (fun y : ℝ ↦ Real.sinh (lambda * y))
        (lambda * Real.cosh (lambda * x)) x := by
      convert (Real.hasDerivAt_sinh (lambda * x)).comp x
        ((hasDerivAt_id x).const_mul lambda) using 1
      all_goals ring
    have hcosh : HasDerivAt (fun y : ℝ ↦ Real.cosh (lambda * y))
        (lambda * Real.sinh (lambda * x)) x := by
      convert (Real.hasDerivAt_cosh (lambda * x)).comp x
        ((hasDerivAt_id x).const_mul lambda) using 1
      all_goals ring
    have hsin : HasDerivAt (fun y : ℝ ↦ Real.sin (mu * y))
        (mu * Real.cos (mu * x)) x := by
      convert (Real.hasDerivAt_sin (mu * x)).comp x
        ((hasDerivAt_id x).const_mul mu) using 1
      all_goals ring
    have hcos : HasDerivAt (fun y : ℝ ↦ Real.cos (mu * y))
        (-mu * Real.sin (mu * x)) x := by
      convert (Real.hasDerivAt_cos (mu * x)).comp x
        ((hasDerivAt_id x).const_mul mu) using 1
      all_goals ring
    dsimp only [F]
    convert ((((hcosh.const_mul lambda).mul hsin).sub
      ((hsinh.const_mul mu).mul hcos)).div_const den) using 1
    dsimp only [den]
    field_simp [hden]
    ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _hx ↦ hderiv x)
      (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
  unfold centeredSinhMoment
  rw [show (fun x : ℝ ↦
      Real.sinh (lambda * x) *
        Real.sin (Real.pi * (n : ℝ) * x)) =
      fun x ↦ Real.sinh (lambda * x) * Real.sin (mu * x) by rfl,
    hint]
  dsimp only [F]
  have hmueq : mu = (n : ℝ) * Real.pi := by
    dsimp only [mu]
    ring
  have hsinPos : Real.sin (mu * 1) = 0 := by
    rw [hmueq, mul_one, Real.sin_nat_mul_pi]
  have hcosPos : Real.cos (mu * 1) = (-1 : ℝ) ^ n := by
    rw [hmueq, mul_one, Real.cos_nat_mul_pi]
  have hsinNeg : Real.sin (mu * (-1)) = 0 := by
    rw [show mu * (-1) = -(mu * 1) by ring, Real.sin_neg, hsinPos,
      neg_zero]
  have hcosNeg : Real.cos (mu * (-1)) = (-1 : ℝ) ^ n := by
    rw [show mu * (-1) = -(mu * 1) by ring, Real.cos_neg, hcosPos]
  rw [hsinPos, hcosPos, hsinNeg, hcosNeg,
    show lambda * 1 = lambda by ring,
    show lambda * (-1) = -lambda by ring,
    Real.sinh_neg, Real.cosh_neg]
  dsimp only [den, mu] at hden ⊢
  field_simp [hden]
  ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoLaplaceModes
