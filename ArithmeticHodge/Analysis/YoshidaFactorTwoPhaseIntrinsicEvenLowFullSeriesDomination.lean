import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenLowEndpointPositive
import ArithmeticHodge.Analysis.TwoByTwoRankOneVariance

set_option autoImplicit false

open Filter MeasureTheory Real Set Topology
open scoped BigOperators Interval

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenLowFullSeriesDomination

noncomputable section

open YoshidaEndpointEvenExactLowGramPositive
open YoshidaEndpointEvenLowProfile
open YoshidaEndpointEvenLowHyperbolic
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseIntrinsicEvenLowEndpointPositive
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseRankLimit
open YoshidaFactorTwoPhaseStructuralLowData
open YoshidaFactorTwoPhaseSymmetricCoercivity
open YoshidaRenormalizedGeometricKernel
open TwoByTwoRankOneVariance

/-!
# Full-series domination on the intrinsic even plane

The negative symmetric endpoint contains one adverse growing cosh square.
Its favourable part is not truncated: it is the Gram form obtained from the
complete decaying half-odd family together with the coupled `p = 2,3` prime
block.  This file exposes that infinite Gram exactly and gives the sharp
two-dimensional Schur invariant which remains to prove.

No rank cutoff occurs in any definition or theorem below.
-/

/-- The two fixed moment coordinates of the intrinsic even plane. -/
def intrinsicEvenMoment0 (lambda : ℝ) : ℝ :=
  centeredCoshMoment centeredEvenP0 lambda

def intrinsicEvenMoment2 (lambda : ℝ) : ℝ :=
  centeredCoshMoment centeredEvenP2 lambda

theorem centeredCoshMoment_intrinsicEven (c d lambda : ℝ) :
    centeredCoshMoment (factorTwoEvenStructuralLowProfile c d) lambda =
      c * intrinsicEvenMoment0 lambda + d * intrinsicEvenMoment2 lambda := by
  unfold centeredCoshMoment factorTwoEvenStructuralLowProfile
    intrinsicEvenMoment0 intrinsicEvenMoment2
  have h0 : Continuous (fun x : ℝ ↦
      c * (Real.cosh (lambda * x) * centeredEvenP0 x)) := by
    unfold centeredEvenP0
    fun_prop
  have h2 : Continuous (fun x : ℝ ↦
      d * (Real.cosh (lambda * x) * centeredEvenP2 x)) := by
    unfold centeredEvenP2
    fun_prop
  rw [show (fun x : ℝ ↦
      Real.cosh (lambda * x) *
        (c * centeredEvenP0 x + d * centeredEvenP2 x)) =
      fun x ↦ c * (Real.cosh (lambda * x) * centeredEvenP0 x) +
        d * (Real.cosh (lambda * x) * centeredEvenP2 x) by
    funext x
    ring,
    intervalIntegral.integral_add
      (h0.intervalIntegrable (-1) 1)
      (h2.intervalIntegrable (-1) 1),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  rfl

/-- Exact transform of the constant moment. -/
theorem intrinsicEvenMoment0_eq {lambda : ℝ} (hlambda : lambda ≠ 0) :
    intrinsicEvenMoment0 lambda = 2 * Real.sinh lambda / lambda := by
  unfold intrinsicEvenMoment0 centeredCoshMoment centeredEvenP0
  have h := integral_cosh_scaled (a := 2 * lambda) (mul_ne_zero (by norm_num) hlambda)
  simp only [mul_one]
  rw [show (fun x : ℝ ↦ Real.cosh (lambda * x)) =
      fun x ↦ Real.cosh ((2 * lambda) * x / 2) by
    funext x
    congr 1
    ring,
    h]
  field_simp [hlambda]
  ring

/-- Exact transform of the centered quadratic moment. -/
theorem intrinsicEvenMoment2_eq {lambda : ℝ} (hlambda : lambda ≠ 0) :
    intrinsicEvenMoment2 lambda =
      2 * ((lambda ^ 2 + 3) * Real.sinh lambda -
        3 * lambda * Real.cosh lambda) / lambda ^ 3 := by
  unfold intrinsicEvenMoment2 centeredCoshMoment
  have h := integral_cosh_scaled_mul_centeredEvenP2
    (a := 2 * lambda) (mul_ne_zero (by norm_num) hlambda)
  rw [show (fun x : ℝ ↦ Real.cosh (lambda * x) * centeredEvenP2 x) =
      fun x ↦ Real.cosh ((2 * lambda) * x / 2) * centeredEvenP2 x by
    funext x
    congr 2
    ring,
    h]
  field_simp [hlambda]
  ring

/-- Closed form of the direction of each positive rank-one Gram row. -/
def intrinsicEvenMomentRatio (lambda : ℝ) : ℝ :=
  intrinsicEvenMoment2 lambda / intrinsicEvenMoment0 lambda

theorem intrinsicEvenMomentRatio_eq {lambda : ℝ} (hlambda : 0 < lambda) :
    intrinsicEvenMomentRatio lambda =
      1 + 3 / lambda ^ 2 -
        3 * Real.cosh lambda / (lambda * Real.sinh lambda) := by
  have hne : lambda ≠ 0 := hlambda.ne'
  have hsinh : Real.sinh lambda ≠ 0 := (Real.sinh_pos_iff.mpr hlambda).ne'
  unfold intrinsicEvenMomentRatio
  rw [intrinsicEvenMoment0_eq hne, intrinsicEvenMoment2_eq hne]
  field_simp [hne, hsinh]

/-! ## Ordered directions of the complete rank family -/

/-- The hyperbolic expression controlling the derivative of the moment
ratio is strictly positive.  The proof is a four-step derivative chain from
`4 x sinh (2x)`, rather than a power-series truncation. -/
private theorem momentRatio_derivativeNumerator_pos
    {x : ℝ} (hx : 0 < x) :
    0 < x * Real.cosh x * Real.sinh x + x ^ 2 -
      2 * Real.sinh x ^ 2 := by
  let H : ℝ → ℝ := fun y ↦
    2 * y * Real.cosh (2 * y) - Real.sinh (2 * y)
  let G : ℝ → ℝ := fun y ↦
    y * Real.sinh (2 * y) - Real.cosh (2 * y) + 1
  let J : ℝ → ℝ := fun y ↦
    y * Real.cosh (2 * y) + 2 * y -
      (3 / 2 : ℝ) * Real.sinh (2 * y)
  let F : ℝ → ℝ := fun y ↦
    y * Real.cosh y * Real.sinh y + y ^ 2 -
      2 * Real.sinh y ^ 2
  have hlin (y : ℝ) : HasDerivAt (fun z : ℝ ↦ 2 * z) 2 y := by
    simpa only [mul_one] using (hasDerivAt_id y).const_mul 2
  have hsinh2 (y : ℝ) :
      HasDerivAt (fun z : ℝ ↦ Real.sinh (2 * z))
        (2 * Real.cosh (2 * y)) y := by
    convert (Real.hasDerivAt_sinh (2 * y)).comp y (hlin y) using 1
    ring
  have hcosh2 (y : ℝ) :
      HasDerivAt (fun z : ℝ ↦ Real.cosh (2 * z))
        (2 * Real.sinh (2 * y)) y := by
    convert (Real.hasDerivAt_cosh (2 * y)).comp y (hlin y) using 1
    ring
  have hHderiv (y : ℝ) :
      HasDerivAt H (4 * y * Real.sinh (2 * y)) y := by
    dsimp only [H]
    convert (((hasDerivAt_id y).const_mul 2).mul (hcosh2 y)).sub
      (hsinh2 y) using 1
    simp only [id_eq]
    ring
  have hHcont : Continuous H := by
    dsimp only [H]
    fun_prop
  have hHstrict : StrictMonoOn H (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) hHcont.continuousOn
    intro y hy
    rw [(hHderiv y).deriv]
    have hy0 : 0 < y := by
      simpa only [interior_Ici, mem_Ioi] using hy
    have hsinh : 0 < Real.sinh (2 * y) :=
      Real.sinh_pos_iff.mpr (by linarith)
    positivity
  have hHpos {y : ℝ} (hy : 0 < y) : 0 < H y := by
    have h := hHstrict (show (0 : ℝ) ∈ Ici 0 by simp)
      (show y ∈ Ici 0 by exact hy.le) hy
    norm_num [H] at h ⊢
    exact h
  have hGderiv (y : ℝ) : HasDerivAt G (H y) y := by
    dsimp only [G, H]
    convert (((hasDerivAt_id y).mul (hsinh2 y)).sub (hcosh2 y)).add
      (hasDerivAt_const y 1) using 1
    simp only [id_eq]
    ring
  have hGcont : Continuous G := by
    dsimp only [G]
    fun_prop
  have hGstrict : StrictMonoOn G (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) hGcont.continuousOn
    intro y hy
    rw [(hGderiv y).deriv]
    apply hHpos
    simpa only [interior_Ici, mem_Ioi] using hy
  have hGpos {y : ℝ} (hy : 0 < y) : 0 < G y := by
    have h := hGstrict (show (0 : ℝ) ∈ Ici 0 by simp)
      (show y ∈ Ici 0 by exact hy.le) hy
    norm_num [G] at h ⊢
    exact h
  have hJderiv (y : ℝ) : HasDerivAt J (2 * G y) y := by
    dsimp only [J, G]
    convert ((((hasDerivAt_id y).mul (hcosh2 y)).add
      ((hasDerivAt_id y).const_mul 2)).sub
        ((hsinh2 y).const_mul (3 / 2 : ℝ))) using 1
    simp only [id_eq]
    ring
  have hJcont : Continuous J := by
    dsimp only [J]
    fun_prop
  have hJstrict : StrictMonoOn J (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) hJcont.continuousOn
    intro y hy
    rw [(hJderiv y).deriv]
    exact mul_pos (by norm_num) (hGpos (by
      simpa only [interior_Ici, mem_Ioi] using hy))
  have hJpos {y : ℝ} (hy : 0 < y) : 0 < J y := by
    have h := hJstrict (show (0 : ℝ) ∈ Ici 0 by simp)
      (show y ∈ Ici 0 by exact hy.le) hy
    norm_num [J] at h ⊢
    exact h
  have hFderiv (y : ℝ) : HasDerivAt F (J y) y := by
    have hsq : HasDerivAt (fun z : ℝ ↦ z ^ 2) (2 * y) y := by
      convert (hasDerivAt_id y).pow 2 using 1
      simp only [id_eq, Nat.cast_ofNat]
      ring
    dsimp only [F, J]
    convert (((((hasDerivAt_id y).mul (Real.hasDerivAt_cosh y)).mul
      (Real.hasDerivAt_sinh y)).add hsq).sub
        (((Real.hasDerivAt_sinh y).pow 2).const_mul 2)) using 1
    simp only [id_eq, Pi.mul_apply, Nat.cast_ofNat]
    rw [Real.cosh_two_mul, Real.sinh_two_mul]
    ring
  have hFcont : Continuous F := by
    dsimp only [F]
    fun_prop
  have hFstrict : StrictMonoOn F (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) hFcont.continuousOn
    intro y hy
    rw [(hFderiv y).deriv]
    apply hJpos
    simpa only [interior_Ici, mem_Ioi] using hy
  have h := hFstrict (show (0 : ℝ) ∈ Ici 0 by simp)
    (show x ∈ Ici 0 by exact hx.le) hx
  norm_num [F] at h ⊢
  exact h

/-- The closed moment direction is strictly increasing on the positive
axis.  This orders every rank-one row in the genuine infinite family. -/
theorem intrinsicEvenMomentRatio_strictMonoOn :
    StrictMonoOn intrinsicEvenMomentRatio (Ioi 0) := by
  let R : ℝ → ℝ := fun x ↦
    1 + 3 / x ^ 2 - 3 * Real.cosh x / (x * Real.sinh x)
  have hRderiv {x : ℝ} (hx : 0 < x) :
      HasDerivAt R
        (3 * (x * Real.cosh x * Real.sinh x + x ^ 2 -
          2 * Real.sinh x ^ 2) / (x ^ 3 * Real.sinh x ^ 2)) x := by
    have hxne : x ≠ 0 := hx.ne'
    have hsinhne : Real.sinh x ≠ 0 :=
      (Real.sinh_pos_iff.mpr hx).ne'
    have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hxne
    have hden : x * Real.sinh x ≠ 0 := mul_ne_zero hxne hsinhne
    have hpow : HasDerivAt (fun y : ℝ ↦ y ^ 2) (2 * x) x := by
      convert (hasDerivAt_id x).pow 2 using 1
      simp only [id_eq, Nat.cast_ofNat]
      ring
    have hfirst : HasDerivAt (fun y : ℝ ↦ 1 + 3 / y ^ 2)
        (-6 / x ^ 3) x := by
      convert (hasDerivAt_const x 1).add
        ((hasDerivAt_const x 3).div hpow hx2) using 1
      field_simp [hxne]
      ring
    have hnum := (Real.hasDerivAt_cosh x).const_mul 3
    have hdenDeriv : HasDerivAt (fun y : ℝ ↦ y * Real.sinh y)
        (Real.sinh x + x * Real.cosh x) x := by
      convert (hasDerivAt_id x).mul (Real.hasDerivAt_sinh x) using 1
      simp only [id_eq]
      ring
    dsimp only [R]
    convert hfirst.sub (hnum.div hdenDeriv hden) using 1
    · field_simp [hxne, hsinhne]
      have hc : Real.cosh x ^ 2 = 1 + Real.sinh x ^ 2 := by
        nlinarith [Real.cosh_sq_sub_sinh_sq x]
      ring_nf at ⊢ hc
      nlinarith
  have hRcont : ContinuousOn R (Ioi 0) := by
    intro x hx
    exact (hRderiv hx).continuousAt.continuousWithinAt
  have hRstrict : StrictMonoOn R (Ioi 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioi (0 : ℝ)) hRcont
    intro x hx
    rw [(hRderiv (by simpa only [interior_Ioi, mem_Ioi] using hx)).deriv]
    have hx0 : 0 < x := by
      simpa only [interior_Ioi, mem_Ioi] using hx
    have hnum := momentRatio_derivativeNumerator_pos hx0
    have hden : 0 < x ^ 3 * Real.sinh x ^ 2 := by positivity
    positivity
  intro x hx y hy hxy
  rw [intrinsicEvenMomentRatio_eq hx, intrinsicEvenMomentRatio_eq hy]
  exact hRstrict hx hy hxy

/-- Parameter, positive Gram weight, and ordered direction of the `m`-th
row.  These names expose the complete family without choosing a cutoff. -/
def intrinsicEvenRankParameter (m : ℕ) : ℝ :=
  yoshidaEndpointA * oddRate (m + 1)

def intrinsicEvenTailWeight (m : ℕ) : ℝ :=
  yoshidaEndpointA *
    Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
      intrinsicEvenMoment0 (intrinsicEvenRankParameter m) ^ 2

def intrinsicEvenTailDirection (m : ℕ) : ℝ :=
  intrinsicEvenMomentRatio (intrinsicEvenRankParameter m)

theorem intrinsicEvenRankParameter_pos (m : ℕ) :
    0 < intrinsicEvenRankParameter m := by
  unfold intrinsicEvenRankParameter
  exact mul_pos yoshidaEndpointA_pos (oddRate_pos (m + 1))

theorem intrinsicEvenMoment0_pos {lambda : ℝ} (hlambda : 0 < lambda) :
    0 < intrinsicEvenMoment0 lambda := by
  rw [intrinsicEvenMoment0_eq hlambda.ne']
  exact div_pos (mul_pos (by norm_num) (Real.sinh_pos_iff.mpr hlambda)) hlambda

private theorem x_mul_cosh_sub_sinh_pos {x : ℝ} (hx : 0 < x) :
    0 < x * Real.cosh x - Real.sinh x := by
  let h : ℝ → ℝ := fun y ↦ y * Real.cosh y - Real.sinh y
  have hhderiv (y : ℝ) : HasDerivAt h (y * Real.sinh y) y := by
    dsimp only [h]
    convert ((hasDerivAt_id y).mul (Real.hasDerivAt_cosh y)).sub
      (Real.hasDerivAt_sinh y) using 1
    simp only [id_eq]
    ring
  have hhcont : Continuous h := by
    dsimp only [h]
    fun_prop
  have hhstrict : StrictMonoOn h (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) hhcont.continuousOn
    intro y hy
    rw [(hhderiv y).deriv]
    have hy0 : 0 < y := by
      simpa only [interior_Ici, mem_Ioi] using hy
    exact mul_pos hy0 (Real.sinh_pos_iff.mpr hy0)
  have hpos := hhstrict (show (0 : ℝ) ∈ Ici 0 by simp)
    (show x ∈ Ici 0 by exact hx.le) hx
  norm_num [h] at hpos ⊢
  exact hpos

theorem intrinsicEvenMoment2_pos {lambda : ℝ} (hlambda : 0 < lambda) :
    0 < intrinsicEvenMoment2 lambda := by
  let g : ℝ → ℝ := fun x ↦
    (x ^ 2 + 3) * Real.sinh x - 3 * x * Real.cosh x
  have hgderiv (x : ℝ) :
      HasDerivAt g (x * (x * Real.cosh x - Real.sinh x)) x := by
    have hpoly : HasDerivAt (fun y : ℝ ↦ y ^ 2 + 3) (2 * x) x := by
      convert ((hasDerivAt_id x).pow 2).add (hasDerivAt_const x 3) using 1
      simp only [id_eq, Nat.cast_ofNat]
      ring
    dsimp only [g]
    convert (hpoly.mul (Real.hasDerivAt_sinh x)).sub
      (((hasDerivAt_id x).const_mul 3).mul
        (Real.hasDerivAt_cosh x)) using 1
    simp only [id_eq]
    ring
  have hgcont : Continuous g := by
    dsimp only [g]
    fun_prop
  have hgstrict : StrictMonoOn g (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) hgcont.continuousOn
    intro x hx
    rw [(hgderiv x).deriv]
    have hx0 : 0 < x := by
      simpa only [interior_Ici, mem_Ioi] using hx
    exact mul_pos hx0 (x_mul_cosh_sub_sinh_pos hx0)
  have hgpos := hgstrict (show (0 : ℝ) ∈ Ici 0 by simp)
    (show lambda ∈ Ici 0 by exact hlambda.le) hlambda
  have hnum : 0 <
      (lambda ^ 2 + 3) * Real.sinh lambda -
        3 * lambda * Real.cosh lambda := by
    norm_num [g] at hgpos ⊢
    exact hgpos
  rw [intrinsicEvenMoment2_eq hlambda.ne']
  exact div_pos (mul_pos (by norm_num) hnum) (pow_pos hlambda 3)

theorem intrinsicEvenMoment2_lt_moment0
    {lambda : ℝ} (hlambda : 0 < lambda) :
    intrinsicEvenMoment2 lambda < intrinsicEvenMoment0 lambda := by
  rw [intrinsicEvenMoment0_eq hlambda.ne',
    intrinsicEvenMoment2_eq hlambda.ne']
  have hcore := x_mul_cosh_sub_sinh_pos hlambda
  rw [div_lt_div_iff₀ (pow_pos hlambda 3) hlambda]
  nlinarith

theorem intrinsicEvenMomentRatio_mem_Ioo
    {lambda : ℝ} (hlambda : 0 < lambda) :
    intrinsicEvenMomentRatio lambda ∈ Ioo (0 : ℝ) 1 := by
  have h0 := intrinsicEvenMoment0_pos hlambda
  constructor
  · unfold intrinsicEvenMomentRatio
    exact div_pos (intrinsicEvenMoment2_pos hlambda) h0
  · rw [intrinsicEvenMomentRatio, div_lt_one h0]
    exact intrinsicEvenMoment2_lt_moment0 hlambda

theorem intrinsicEvenTailWeight_pos (m : ℕ) :
    0 < intrinsicEvenTailWeight m := by
  unfold intrinsicEvenTailWeight
  exact mul_pos
    (mul_pos yoshidaEndpointA_pos (Real.exp_pos _))
    (sq_pos_of_pos (intrinsicEvenMoment0_pos
      (intrinsicEvenRankParameter_pos m)))

/-- Rank directions are strictly ordered throughout the infinite family. -/
theorem intrinsicEvenTailDirection_strictMono :
    StrictMono intrinsicEvenTailDirection := by
  intro m n hmn
  have hrate : oddRate (m + 1) < oddRate (n + 1) := by
    have hmnr : (m : ℝ) < (n : ℝ) := by exact_mod_cast hmn
    unfold oddRate
    push_cast
    nlinarith
  have hparameter : intrinsicEvenRankParameter m <
      intrinsicEvenRankParameter n := by
    unfold intrinsicEvenRankParameter
    exact mul_lt_mul_of_pos_left hrate yoshidaEndpointA_pos
  unfold intrinsicEvenTailDirection
  exact intrinsicEvenMomentRatio_strictMonoOn
    (intrinsicEvenRankParameter_pos m)
    (intrinsicEvenRankParameter_pos n) hparameter

/-- Every row is literally `weight * (c + direction*d)^2`. -/
theorem intrinsicEven_rankRow_eq_directional
    (m : ℕ) (c d : ℝ) :
    yoshidaEndpointA *
        Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
        (c * intrinsicEvenMoment0 (intrinsicEvenRankParameter m) +
          d * intrinsicEvenMoment2 (intrinsicEvenRankParameter m)) ^ 2 =
      intrinsicEvenTailWeight m *
        (c + intrinsicEvenTailDirection m * d) ^ 2 := by
  have h0 := intrinsicEvenMoment0_pos (intrinsicEvenRankParameter_pos m)
  have hratio : intrinsicEvenMoment2 (intrinsicEvenRankParameter m) =
      intrinsicEvenMoment0 (intrinsicEvenRankParameter m) *
        intrinsicEvenTailDirection m := by
    unfold intrinsicEvenTailDirection intrinsicEvenMomentRatio
    field_simp [h0.ne']
  rw [hratio]
  unfold intrinsicEvenTailWeight
  ring

/-- Complete decaying-rank Gram entries. -/
def intrinsicEvenTailGram00 : ℝ :=
  yoshidaEndpointA * ∑' m : ℕ,
    Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
      intrinsicEvenMoment0
        (yoshidaEndpointA * oddRate (m + 1)) ^ 2

def intrinsicEvenTailGram02 : ℝ :=
  yoshidaEndpointA * ∑' m : ℕ,
    Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
      intrinsicEvenMoment0
        (yoshidaEndpointA * oddRate (m + 1)) *
      intrinsicEvenMoment2
        (yoshidaEndpointA * oddRate (m + 1))

def intrinsicEvenTailGram22 : ℝ :=
  yoshidaEndpointA * ∑' m : ℕ,
    Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
      intrinsicEvenMoment2
        (yoshidaEndpointA * oddRate (m + 1)) ^ 2

private theorem even_centeredEvenP0 : Function.Even centeredEvenP0 := by
  intro x
  rfl

private theorem even_centeredEvenP2 : Function.Even centeredEvenP2 := by
  intro x
  unfold centeredEvenP2
  ring

private theorem continuous_centeredEvenP0 : Continuous centeredEvenP0 := by
  unfold centeredEvenP0
  fun_prop

private theorem continuous_centeredEvenP2 : Continuous centeredEvenP2 := by
  unfold centeredEvenP2
  fun_prop

private theorem summable_intrinsicEvenTailGram00 : Summable (fun m : ℕ ↦
    Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
      intrinsicEvenMoment0
        (yoshidaEndpointA * oddRate (m + 1)) ^ 2) := by
  simpa only [intrinsicEvenMoment0] using
    (hasSum_factorTwoCenteredArch_evenRankSquares centeredEvenP0
      continuous_centeredEvenP0 even_centeredEvenP0).summable

private theorem summable_intrinsicEvenTailGram22 : Summable (fun m : ℕ ↦
    Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
      intrinsicEvenMoment2
        (yoshidaEndpointA * oddRate (m + 1)) ^ 2) := by
  simpa only [intrinsicEvenMoment2] using
    (hasSum_factorTwoCenteredArch_evenRankSquares centeredEvenP2
      continuous_centeredEvenP2 even_centeredEvenP2).summable

private theorem summable_intrinsicEvenTailGram02 : Summable (fun m : ℕ ↦
    Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
      intrinsicEvenMoment0
        (yoshidaEndpointA * oddRate (m + 1)) *
      intrinsicEvenMoment2
        (yoshidaEndpointA * oddRate (m + 1))) := by
  let u : ℕ → ℝ := fun m ↦
    Real.sqrt (Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1))) *
      intrinsicEvenMoment0 (yoshidaEndpointA * oddRate (m + 1))
  let v : ℕ → ℝ := fun m ↦
    Real.sqrt (Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1))) *
      intrinsicEvenMoment2 (yoshidaEndpointA * oddRate (m + 1))
  have hu : Summable (fun m ↦ u m ^ 2) := by
    apply summable_intrinsicEvenTailGram00.congr
    intro m
    dsimp only [u]
    rw [mul_pow, Real.sq_sqrt (Real.exp_pos _).le]
  have hv : Summable (fun m ↦ v m ^ 2) := by
    apply summable_intrinsicEvenTailGram22.congr
    intro m
    dsimp only [v]
    rw [mul_pow, Real.sq_sqrt (Real.exp_pos _).le]
  have habs : Summable (fun m ↦ |u m * v m|) := by
    apply ((hu.add hv).mul_left (1 / 2 : ℝ)).of_nonneg_of_le
    · intro m
      exact abs_nonneg _
    · intro m
      rw [abs_mul]
      nlinarith [sq_nonneg (|u m| - |v m|), sq_abs (u m), sq_abs (v m)]
  have huv : Summable (fun m ↦ u m * v m) := habs.of_abs
  apply huv.congr
  intro m
  dsimp only [u, v]
  rw [show Real.sqrt (Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1))) *
        intrinsicEvenMoment0 (yoshidaEndpointA * oddRate (m + 1)) *
        (Real.sqrt (Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1))) *
          intrinsicEvenMoment2 (yoshidaEndpointA * oddRate (m + 1))) =
      (Real.sqrt (Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1))) ^ 2) *
        intrinsicEvenMoment0 (yoshidaEndpointA * oddRate (m + 1)) *
        intrinsicEvenMoment2 (yoshidaEndpointA * oddRate (m + 1)) by ring,
    Real.sq_sqrt (Real.exp_pos _).le]

theorem summable_intrinsicEvenTailWeight : Summable intrinsicEvenTailWeight := by
  apply (summable_intrinsicEvenTailGram00.mul_left yoshidaEndpointA).congr
  intro m
  unfold intrinsicEvenTailWeight intrinsicEvenRankParameter
  ring

theorem summable_intrinsicEvenTailWeight_mul_direction :
    Summable (fun m ↦
      intrinsicEvenTailWeight m * intrinsicEvenTailDirection m) := by
  apply (summable_intrinsicEvenTailGram02.mul_left yoshidaEndpointA).congr
  intro m
  have h0 := intrinsicEvenMoment0_pos (intrinsicEvenRankParameter_pos m)
  unfold intrinsicEvenTailWeight intrinsicEvenTailDirection
    intrinsicEvenMomentRatio intrinsicEvenRankParameter
  field_simp [h0.ne']

theorem summable_intrinsicEvenTailWeight_mul_direction_sq :
    Summable (fun m ↦
      intrinsicEvenTailWeight m * intrinsicEvenTailDirection m ^ 2) := by
  apply (summable_intrinsicEvenTailGram22.mul_left yoshidaEndpointA).congr
  intro m
  have h0 : 0 < intrinsicEvenMoment0
      (yoshidaEndpointA * oddRate (m + 1)) := by
    apply intrinsicEvenMoment0_pos
    exact mul_pos yoshidaEndpointA_pos (oddRate_pos (m + 1))
  unfold intrinsicEvenTailWeight intrinsicEvenTailDirection
    intrinsicEvenMomentRatio intrinsicEvenRankParameter
  field_simp [h0.ne']

/-- Moment presentation of the complete tail Gram. -/
theorem intrinsicEvenTailGram00_eq_tsum_weight :
    intrinsicEvenTailGram00 = ∑' m : ℕ, intrinsicEvenTailWeight m := by
  unfold intrinsicEvenTailGram00 intrinsicEvenTailWeight
    intrinsicEvenRankParameter
  rw [← tsum_mul_left]
  apply tsum_congr
  intro m
  ring

theorem intrinsicEvenTailGram02_eq_tsum_weight_direction :
    intrinsicEvenTailGram02 =
      ∑' m : ℕ, intrinsicEvenTailWeight m * intrinsicEvenTailDirection m := by
  unfold intrinsicEvenTailGram02
  rw [← tsum_mul_left]
  apply tsum_congr
  intro m
  have h0 := intrinsicEvenMoment0_pos (intrinsicEvenRankParameter_pos m)
  unfold intrinsicEvenTailWeight intrinsicEvenTailDirection
    intrinsicEvenMomentRatio intrinsicEvenRankParameter
  field_simp [h0.ne']

theorem intrinsicEvenTailGram22_eq_tsum_weight_direction_sq :
    intrinsicEvenTailGram22 =
      ∑' m : ℕ,
        intrinsicEvenTailWeight m * intrinsicEvenTailDirection m ^ 2 := by
  unfold intrinsicEvenTailGram22
  rw [← tsum_mul_left]
  apply tsum_congr
  intro m
  have h0 : 0 < intrinsicEvenMoment0
      (yoshidaEndpointA * oddRate (m + 1)) := by
    apply intrinsicEvenMoment0_pos
    exact mul_pos yoshidaEndpointA_pos (oddRate_pos (m + 1))
  unfold intrinsicEvenTailWeight intrinsicEvenTailDirection
    intrinsicEvenMomentRatio intrinsicEvenRankParameter
  field_simp [h0.ne']

/-- The complete decaying family is exactly its infinite `2 x 2` Gram. -/
theorem factorTwoIntrinsicEvenDecayingTail_eq_fullGram (c d : ℝ) :
    factorTwoIntrinsicEvenDecayingTail c d =
      intrinsicEvenTailGram00 * c ^ 2 +
        2 * intrinsicEvenTailGram02 * c * d +
        intrinsicEvenTailGram22 * d ^ 2 := by
  let f00 : ℕ → ℝ := fun m ↦
    Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
      intrinsicEvenMoment0 (yoshidaEndpointA * oddRate (m + 1)) ^ 2
  let f02 : ℕ → ℝ := fun m ↦
    Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
      intrinsicEvenMoment0 (yoshidaEndpointA * oddRate (m + 1)) *
      intrinsicEvenMoment2 (yoshidaEndpointA * oddRate (m + 1))
  let f22 : ℕ → ℝ := fun m ↦
    Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
      intrinsicEvenMoment2 (yoshidaEndpointA * oddRate (m + 1)) ^ 2
  have h00 : Summable f00 := by
    simpa only [f00] using summable_intrinsicEvenTailGram00
  have h02 : Summable f02 := by
    simpa only [f02] using summable_intrinsicEvenTailGram02
  have h22 : Summable f22 := by
    simpa only [f22] using summable_intrinsicEvenTailGram22
  unfold factorTwoIntrinsicEvenDecayingTail
  simp_rw [centeredCoshMoment_intrinsicEven]
  rw [show (fun m : ℕ ↦
      Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
        (c * intrinsicEvenMoment0 (yoshidaEndpointA * oddRate (m + 1)) +
          d * intrinsicEvenMoment2
            (yoshidaEndpointA * oddRate (m + 1))) ^ 2) =
      fun m ↦ c ^ 2 * f00 m +
        ((2 * c * d) * f02 m + d ^ 2 * f22 m) by
    funext m
    dsimp only [f00, f02, f22]
    ring]
  rw [Summable.tsum_add (h00.mul_left (c ^ 2))
      ((h02.mul_left (2 * c * d)).add (h22.mul_left (d ^ 2))),
    Summable.tsum_add (h02.mul_left (2 * c * d))
      (h22.mul_left (d ^ 2)),
    h00.tsum_mul_left, h02.tsum_mul_left, h22.tsum_mul_left]
  unfold intrinsicEvenTailGram00 intrinsicEvenTailGram02
    intrinsicEvenTailGram22
  dsimp only [f00, f02, f22]
  ring

/-- Exact intrinsic correlation polynomial, before any prime estimate. -/
theorem centeredEndpointCorrelation_intrinsicEven (c d t : ℝ) :
    CenteredEndpointCorrelation.centeredEndpointCorrelation
        (factorTwoEvenStructuralLowProfile c d) t =
      c ^ 2 * (2 - t) +
        2 * c * d * (-t * (t - 2) * (t - 1) / 2) +
        d ^ 2 *
          (-(t - 2) *
            (3 * t ^ 4 + 6 * t ^ 3 - 8 * t ^ 2 - 16 * t + 8) / 40) := by
  have h0 : Continuous centeredEvenP0 := continuous_centeredEvenP0
  have h2 : Continuous centeredEvenP2 := continuous_centeredEvenP2
  rw [factorTwoEvenStructuralLowProfile_eq_smul_add,
    centeredEndpointCorrelation_add (c • centeredEvenP0)
      (d • centeredEvenP2) (h0.const_smul c) (h2.const_smul d)]
  have hself0 :
      CenteredEndpointCorrelation.centeredEndpointCorrelation
          (c • centeredEvenP0) t =
        c ^ 2 * factorTwoCenteredCorrelationBilinear
          centeredEvenP0 centeredEvenP0 t := by
    rw [← factorTwoCenteredCorrelationBilinear_self,
      factorTwoCenteredCorrelationBilinear_smul_smul]
    ring
  have hself2 :
      CenteredEndpointCorrelation.centeredEndpointCorrelation
          (d • centeredEvenP2) t =
        d ^ 2 * factorTwoCenteredCorrelationBilinear
          centeredEvenP2 centeredEvenP2 t := by
    rw [← factorTwoCenteredCorrelationBilinear_self,
      factorTwoCenteredCorrelationBilinear_smul_smul]
    ring
  rw [hself0, hself2,
    factorTwoCenteredCorrelationBilinear_smul_smul,
    factorTwoCenteredCorrelationBilinear_p0_p0,
    factorTwoCenteredCorrelationBilinear_p0_p2,
    factorTwoCenteredCorrelationBilinear_p2_p2]
  ring

/-- Exact coupled-prime Gram entries. -/
def intrinsicEvenPrimeGram00 : ℝ :=
  (Real.log 2 / Real.sqrt 2) * 2 +
    (Real.log 3 / Real.sqrt 3) *
      (2 - factorTwoPrimeShift / yoshidaEndpointA)

def intrinsicEvenPrimeGram02 : ℝ :=
  (Real.log 3 / Real.sqrt 3) *
    (-(factorTwoPrimeShift / yoshidaEndpointA) *
      (factorTwoPrimeShift / yoshidaEndpointA - 2) *
      (factorTwoPrimeShift / yoshidaEndpointA - 1) / 2)

def intrinsicEvenPrimeGram22 : ℝ :=
  (Real.log 2 / Real.sqrt 2) * (2 / 5) +
    (Real.log 3 / Real.sqrt 3) *
      (-(factorTwoPrimeShift / yoshidaEndpointA - 2) *
        (3 * (factorTwoPrimeShift / yoshidaEndpointA) ^ 4 +
          6 * (factorTwoPrimeShift / yoshidaEndpointA) ^ 3 -
          8 * (factorTwoPrimeShift / yoshidaEndpointA) ^ 2 -
          16 * (factorTwoPrimeShift / yoshidaEndpointA) + 8) / 40)

/-- The retained `p = 2,3` package remains one exact Gram form. -/
theorem factorTwoIntrinsicEvenPrimeBlock_eq_gram (c d : ℝ) :
    factorTwoIntrinsicEvenPrimeBlock c d =
      intrinsicEvenPrimeGram00 * c ^ 2 +
        2 * intrinsicEvenPrimeGram02 * c * d +
        intrinsicEvenPrimeGram22 * d ^ 2 := by
  let w := factorTwoEvenStructuralLowProfile c d
  have hprofile : w = yoshidaEndpointEvenLowProfile c d := by
    funext x
    unfold w factorTwoEvenStructuralLowProfile
      yoshidaEndpointEvenLowProfile centeredEvenP0
    ring
  have henergy :
      (∫ x : ℝ in -1..1, w x ^ 2) =
        2 * c ^ 2 + (2 / 5 : ℝ) * d ^ 2 := by
    rw [hprofile]
    exact integral_yoshidaEndpointEvenLowProfile_sq c d
  have hcorr := centeredEndpointCorrelation_intrinsicEven c d
    (factorTwoPrimeShift / yoshidaEndpointA)
  unfold factorTwoIntrinsicEvenPrimeBlock factorTwoCenteredPrimeBlock
  dsimp only [w] at henergy hcorr ⊢
  rw [henergy, hcorr]
  unfold intrinsicEvenPrimeGram00 intrinsicEvenPrimeGram02
    intrinsicEvenPrimeGram22
  ring

/-! ## The complete favourable Gram and the adverse rank -/

/-- Gram of the complete decaying family plus the coupled prime package. -/
def intrinsicEvenFavourableGram00 : ℝ :=
  intrinsicEvenTailGram00 + intrinsicEvenPrimeGram00

def intrinsicEvenFavourableGram02 : ℝ :=
  intrinsicEvenTailGram02 + intrinsicEvenPrimeGram02

def intrinsicEvenFavourableGram22 : ℝ :=
  intrinsicEvenTailGram22 + intrinsicEvenPrimeGram22

/-- The growing rank vector, before its positive scalar weight is applied. -/
def intrinsicEvenGrowingVector0 : ℝ :=
  intrinsicEvenMoment0 (yoshidaEndpointA / 2)

def intrinsicEvenGrowingVector2 : ℝ :=
  intrinsicEvenMoment2 (yoshidaEndpointA / 2)

def intrinsicEvenGrowingWeight : ℝ :=
  yoshidaEndpointA * Real.exp yoshidaEndpointA

theorem intrinsicEvenGrowingWeight_pos : 0 < intrinsicEvenGrowingWeight := by
  unfold intrinsicEvenGrowingWeight
  exact mul_pos yoshidaEndpointA_pos (Real.exp_pos _)

/-- Normalize the adverse row by its positive constant coordinate. -/
def intrinsicEvenGrowingMass : ℝ :=
  intrinsicEvenGrowingWeight * intrinsicEvenGrowingVector0 ^ 2

def intrinsicEvenGrowingDirection : ℝ :=
  intrinsicEvenGrowingVector2 / intrinsicEvenGrowingVector0

theorem intrinsicEvenGrowingVector0_pos :
    0 < intrinsicEvenGrowingVector0 := by
  unfold intrinsicEvenGrowingVector0
  exact intrinsicEvenMoment0_pos (half_pos yoshidaEndpointA_pos)

theorem intrinsicEvenGrowingMass_pos : 0 < intrinsicEvenGrowingMass := by
  unfold intrinsicEvenGrowingMass
  exact mul_pos intrinsicEvenGrowingWeight_pos
    (sq_pos_of_pos intrinsicEvenGrowingVector0_pos)

theorem intrinsicEvenGrowingDirection_mem_Ioo :
    intrinsicEvenGrowingDirection ∈ Ioo (0 : ℝ) 1 := by
  unfold intrinsicEvenGrowingDirection intrinsicEvenGrowingVector0
    intrinsicEvenGrowingVector2
  simpa only [intrinsicEvenMomentRatio] using
    intrinsicEvenMomentRatio_mem_Ioo (half_pos yoshidaEndpointA_pos)

/-- Every decaying rank lies strictly beyond the adverse growing direction.
This is a global ordering theorem for the family, not a rank check. -/
theorem intrinsicEvenGrowingDirection_lt_tailDirection (m : ℕ) :
    intrinsicEvenGrowingDirection < intrinsicEvenTailDirection m := by
  have hhalf : 0 < yoshidaEndpointA / 2 := half_pos yoshidaEndpointA_pos
  have hparameter : yoshidaEndpointA / 2 < intrinsicEvenRankParameter m := by
    have hrate : (1 / 2 : ℝ) < oddRate (m + 1) := by
      have hm : 0 ≤ (m : ℝ) := by positivity
      unfold oddRate
      push_cast
      nlinarith
    unfold intrinsicEvenRankParameter
    calc
      yoshidaEndpointA / 2 = yoshidaEndpointA * (1 / 2 : ℝ) := by ring
      _ < yoshidaEndpointA * oddRate (m + 1) :=
        mul_lt_mul_of_pos_left hrate yoshidaEndpointA_pos
  unfold intrinsicEvenGrowingDirection intrinsicEvenGrowingVector0
    intrinsicEvenGrowingVector2 intrinsicEvenTailDirection
  simpa only [intrinsicEvenMomentRatio] using
    intrinsicEvenMomentRatio_strictMonoOn hhalf
      (intrinsicEvenRankParameter_pos m) hparameter

theorem intrinsicEvenGrowing_cross_eq_mass_direction :
    intrinsicEvenGrowingWeight * intrinsicEvenGrowingVector0 *
        intrinsicEvenGrowingVector2 =
      intrinsicEvenGrowingMass * intrinsicEvenGrowingDirection := by
  unfold intrinsicEvenGrowingMass intrinsicEvenGrowingDirection
  field_simp [intrinsicEvenGrowingVector0_pos.ne']

theorem intrinsicEvenGrowing_22_eq_mass_direction_sq :
    intrinsicEvenGrowingWeight * intrinsicEvenGrowingVector2 ^ 2 =
      intrinsicEvenGrowingMass * intrinsicEvenGrowingDirection ^ 2 := by
  unfold intrinsicEvenGrowingMass intrinsicEvenGrowingDirection
  field_simp [intrinsicEvenGrowingVector0_pos.ne']

/-- Base form left after retaining the exact coupled prime Gram and removing
the adverse growing row. -/
def intrinsicEvenPrimeHeadBase00 : ℝ :=
  intrinsicEvenPrimeGram00 - intrinsicEvenGrowingMass

def intrinsicEvenPrimeHeadBase02 : ℝ :=
  intrinsicEvenPrimeGram02 -
    intrinsicEvenGrowingMass * intrinsicEvenGrowingDirection

def intrinsicEvenPrimeHeadBase22 : ℝ :=
  intrinsicEvenPrimeGram22 -
    intrinsicEvenGrowingMass * intrinsicEvenGrowingDirection ^ 2

/-- Scalar full-series variance gap.  Positivity of this one expression is
the remaining analytic statement on the negative endpoint route. -/
def intrinsicEvenRankPrimeCenteredVarianceGap : ℝ :=
  twoByTwoDet intrinsicEvenPrimeHeadBase00
      intrinsicEvenPrimeHeadBase02 intrinsicEvenPrimeHeadBase22 +
    (intrinsicEvenPrimeHeadBase00 * intrinsicEvenTailGram22 +
      intrinsicEvenPrimeHeadBase22 * intrinsicEvenTailGram00 -
      2 * intrinsicEvenPrimeHeadBase02 * intrinsicEvenTailGram02) +
    intrinsicEvenTailGram00 *
      (∑' m : ℕ, intrinsicEvenTailWeight m *
        (intrinsicEvenTailDirection m -
          intrinsicEvenGrowingDirection) ^ 2) -
    (∑' m : ℕ, intrinsicEvenTailWeight m *
      (intrinsicEvenTailDirection m -
        intrinsicEvenGrowingDirection)) ^ 2

/-- Exact centered-variance expansion of the complete rank/prime gap
determinant.  The final two terms are the full infinite variance; no row is
selected or discarded. -/
theorem intrinsicEven_rankPrimeGap_det_eq_centeredVariance :
    twoByTwoDet
        (intrinsicEvenFavourableGram00 - intrinsicEvenGrowingMass)
        (intrinsicEvenFavourableGram02 -
          intrinsicEvenGrowingMass * intrinsicEvenGrowingDirection)
        (intrinsicEvenFavourableGram22 -
          intrinsicEvenGrowingMass * intrinsicEvenGrowingDirection ^ 2) =
      twoByTwoDet intrinsicEvenPrimeHeadBase00
          intrinsicEvenPrimeHeadBase02 intrinsicEvenPrimeHeadBase22 +
        (intrinsicEvenPrimeHeadBase00 * intrinsicEvenTailGram22 +
          intrinsicEvenPrimeHeadBase22 * intrinsicEvenTailGram00 -
          2 * intrinsicEvenPrimeHeadBase02 * intrinsicEvenTailGram02) +
        intrinsicEvenTailGram00 *
          (∑' m : ℕ, intrinsicEvenTailWeight m *
            (intrinsicEvenTailDirection m -
              intrinsicEvenGrowingDirection) ^ 2) -
        (∑' m : ℕ, intrinsicEvenTailWeight m *
          (intrinsicEvenTailDirection m -
            intrinsicEvenGrowingDirection)) ^ 2 := by
  have h := det_base_add_tsum_weighted_eq_centered
    intrinsicEvenTailWeight intrinsicEvenTailDirection
    intrinsicEvenPrimeHeadBase00 intrinsicEvenPrimeHeadBase02
    intrinsicEvenPrimeHeadBase22 intrinsicEvenGrowingDirection
    summable_intrinsicEvenTailWeight
    summable_intrinsicEvenTailWeight_mul_direction
    summable_intrinsicEvenTailWeight_mul_direction_sq
  rw [← intrinsicEvenTailGram00_eq_tsum_weight,
    ← intrinsicEvenTailGram02_eq_tsum_weight_direction,
    ← intrinsicEvenTailGram22_eq_tsum_weight_direction_sq] at h
  unfold intrinsicEvenFavourableGram00 intrinsicEvenFavourableGram02
    intrinsicEvenFavourableGram22
  unfold intrinsicEvenPrimeHeadBase00 intrinsicEvenPrimeHeadBase02
    intrinsicEvenPrimeHeadBase22 at h ⊢
  convert h using 1
  all_goals ring

theorem intrinsicEven_rankPrimeGap_det_eq_centeredVarianceGap :
    twoByTwoDet
        (intrinsicEvenFavourableGram00 - intrinsicEvenGrowingMass)
        (intrinsicEvenFavourableGram02 -
          intrinsicEvenGrowingMass * intrinsicEvenGrowingDirection)
        (intrinsicEvenFavourableGram22 -
          intrinsicEvenGrowingMass * intrinsicEvenGrowingDirection ^ 2) =
      intrinsicEvenRankPrimeCenteredVarianceGap := by
  rw [intrinsicEven_rankPrimeGap_det_eq_centeredVariance]
  rfl

/-- The favourable side is exactly one complete infinite Gram. -/
theorem intrinsicEven_favourable_eq_fullGram (c d : ℝ) :
    factorTwoIntrinsicEvenDecayingTail c d +
        factorTwoIntrinsicEvenPrimeBlock c d =
      intrinsicEvenFavourableGram00 * c ^ 2 +
        2 * intrinsicEvenFavourableGram02 * c * d +
        intrinsicEvenFavourableGram22 * d ^ 2 := by
  rw [factorTwoIntrinsicEvenDecayingTail_eq_fullGram,
    factorTwoIntrinsicEvenPrimeBlock_eq_gram]
  unfold intrinsicEvenFavourableGram00 intrinsicEvenFavourableGram02
    intrinsicEvenFavourableGram22
  ring

/-- The only adverse term at the negative endpoint is a genuine rank-one
Gram, with no estimate. -/
theorem factorTwoIntrinsicEvenGrowingHead_eq_rankOne (c d : ℝ) :
    factorTwoIntrinsicEvenGrowingHead c d =
      intrinsicEvenGrowingWeight *
        (intrinsicEvenGrowingVector0 * c +
          intrinsicEvenGrowingVector2 * d) ^ 2 := by
  unfold factorTwoIntrinsicEvenGrowingHead intrinsicEvenGrowingWeight
    intrinsicEvenGrowingVector0 intrinsicEvenGrowingVector2
  rw [centeredCoshMoment_intrinsicEven]
  ring

/-- The complete favourable Gram is positive definite.  This uses positivity
of the coupled prime block and only nonnegativity of the entire infinite
rank family; no individual rank is selected. -/
theorem intrinsicEvenFavourableGram_principal_minors_pos :
    0 < intrinsicEvenFavourableGram00 ∧
      0 < intrinsicEvenFavourableGram00 * intrinsicEvenFavourableGram22 -
        intrinsicEvenFavourableGram02 ^ 2 := by
  have hquad : ∀ c d : ℝ, c ≠ 0 ∨ d ≠ 0 →
      0 < intrinsicEvenFavourableGram00 * c ^ 2 +
        2 * intrinsicEvenFavourableGram02 * c * d +
        intrinsicEvenFavourableGram22 * d ^ 2 := by
    intro c d hne
    rw [← intrinsicEven_favourable_eq_fullGram]
    exact add_pos_of_nonneg_of_pos
      (factorTwoIntrinsicEvenDecayingTail_nonneg c d)
      (factorTwoIntrinsicEvenPrimeBlock_pos c d hne)
  exact real_twoByTwo_coefficients_pos_of_quadratic_pos
    intrinsicEvenFavourableGram00 intrinsicEvenFavourableGram02
    intrinsicEvenFavourableGram22 hquad

/-- The exact dual norm numerator of the growing rank in the complete
favourable Gram. -/
def intrinsicEvenGrowingDualNumerator : ℝ :=
  intrinsicEvenGrowingWeight *
    (intrinsicEvenFavourableGram22 * intrinsicEvenGrowingVector0 ^ 2 -
      2 * intrinsicEvenFavourableGram02 * intrinsicEvenGrowingVector0 *
        intrinsicEvenGrowingVector2 +
      intrinsicEvenFavourableGram00 * intrinsicEvenGrowingVector2 ^ 2)

/-- The remaining dual inequality is exactly, not merely sufficiently, the
positivity of the full rank/prime-minus-growing determinant. -/
theorem intrinsicEvenGrowingDualNumerator_lt_det_iff_gapDet_pos :
    intrinsicEvenGrowingDualNumerator <
        twoByTwoDet intrinsicEvenFavourableGram00
          intrinsicEvenFavourableGram02 intrinsicEvenFavourableGram22 ↔
      0 < twoByTwoDet
        (intrinsicEvenFavourableGram00 -
          intrinsicEvenGrowingWeight * intrinsicEvenGrowingVector0 ^ 2)
        (intrinsicEvenFavourableGram02 -
          intrinsicEvenGrowingWeight * intrinsicEvenGrowingVector0 *
            intrinsicEvenGrowingVector2)
        (intrinsicEvenFavourableGram22 -
          intrinsicEvenGrowingWeight * intrinsicEvenGrowingVector2 ^ 2) := by
  have hid :
      twoByTwoDet
          (intrinsicEvenFavourableGram00 -
            intrinsicEvenGrowingWeight * intrinsicEvenGrowingVector0 ^ 2)
          (intrinsicEvenFavourableGram02 -
            intrinsicEvenGrowingWeight * intrinsicEvenGrowingVector0 *
              intrinsicEvenGrowingVector2)
          (intrinsicEvenFavourableGram22 -
            intrinsicEvenGrowingWeight * intrinsicEvenGrowingVector2 ^ 2) =
        twoByTwoDet intrinsicEvenFavourableGram00
            intrinsicEvenFavourableGram02 intrinsicEvenFavourableGram22 -
          intrinsicEvenGrowingDualNumerator := by
    unfold twoByTwoDet intrinsicEvenGrowingDualNumerator
    ring
  rw [hid]
  constructor <;> intro h <;> linarith

/-- Abstract rank-one Schur domination.  The displayed scalar is the exact
dual squared norm of `sqrt k * h`; hence there is no trace loss. -/
private theorem rankOne_strictly_dominated_of_dual_numerator_lt
    (q00 q02 q22 k h0 h2 : ℝ)
    (hk : 0 < k) (hq00 : 0 < q00)
    (hqdet : 0 < q00 * q22 - q02 ^ 2)
    (hdual :
      k * (q22 * h0 ^ 2 - 2 * q02 * h0 * h2 + q00 * h2 ^ 2) <
        q00 * q22 - q02 ^ 2) :
    0 < q00 - k * h0 ^ 2 ∧
      0 < (q00 - k * h0 ^ 2) * (q22 - k * h2 ^ 2) -
        (q02 - k * h0 * h2) ^ 2 := by
  let D : ℝ := q00 * q22 - q02 ^ 2
  let N : ℝ :=
    k * (q22 * h0 ^ 2 - 2 * q02 * h0 * h2 + q00 * h2 ^ 2)
  have hscaled : D * (k * h0 ^ 2) ≤ q00 * N := by
    have hid :
        q00 * N - D * (k * h0 ^ 2) =
          k * (q00 * h2 - q02 * h0) ^ 2 := by
      dsimp only [D, N]
      ring
    apply sub_nonneg.mp
    rw [hid]
    exact mul_nonneg hk.le (sq_nonneg _)
  have hhead00 : k * h0 ^ 2 < q00 := by
    dsimp only [D, N] at hscaled hdual ⊢
    nlinarith [mul_pos hq00 hqdet]
  constructor
  · linarith
  · have hdetIdentity :
        (q00 - k * h0 ^ 2) * (q22 - k * h2 ^ 2) -
            (q02 - k * h0 * h2) ^ 2 = D - N := by
      dsimp only [D, N]
      ring
    rw [hdetIdentity]
    dsimp only [D, N] at hdual ⊢
    linarith

/-- The single full-series inequality which makes the complete favourable
rank/prime Gram dominate the growing rank. -/
theorem intrinsicEven_rankPrime_gap_principal_minors_pos
    (hdual : intrinsicEvenGrowingDualNumerator <
      intrinsicEvenFavourableGram00 * intrinsicEvenFavourableGram22 -
        intrinsicEvenFavourableGram02 ^ 2) :
    0 < intrinsicEvenFavourableGram00 -
          intrinsicEvenGrowingWeight * intrinsicEvenGrowingVector0 ^ 2 ∧
      0 <
        (intrinsicEvenFavourableGram00 -
            intrinsicEvenGrowingWeight * intrinsicEvenGrowingVector0 ^ 2) *
          (intrinsicEvenFavourableGram22 -
            intrinsicEvenGrowingWeight * intrinsicEvenGrowingVector2 ^ 2) -
        (intrinsicEvenFavourableGram02 -
          intrinsicEvenGrowingWeight * intrinsicEvenGrowingVector0 *
            intrinsicEvenGrowingVector2) ^ 2 := by
  exact rankOne_strictly_dominated_of_dual_numerator_lt
    intrinsicEvenFavourableGram00 intrinsicEvenFavourableGram02
    intrinsicEvenFavourableGram22 intrinsicEvenGrowingWeight
    intrinsicEvenGrowingVector0 intrinsicEvenGrowingVector2
    intrinsicEvenGrowingWeight_pos
    intrinsicEvenFavourableGram_principal_minors_pos.1
    intrinsicEvenFavourableGram_principal_minors_pos.2 hdual

/-- Sharp full-series rank/prime domination on every nonzero intrinsic even
profile, from its one scalar dual-norm inequality. -/
theorem intrinsicEven_growingHead_lt_fullTail_add_prime
    (hdual : intrinsicEvenGrowingDualNumerator <
      intrinsicEvenFavourableGram00 * intrinsicEvenFavourableGram22 -
        intrinsicEvenFavourableGram02 ^ 2)
    (c d : ℝ) (hne : c ≠ 0 ∨ d ≠ 0) :
    factorTwoIntrinsicEvenGrowingHead c d <
      factorTwoIntrinsicEvenDecayingTail c d +
        factorTwoIntrinsicEvenPrimeBlock c d := by
  rw [intrinsicEven_favourable_eq_fullGram,
    factorTwoIntrinsicEvenGrowingHead_eq_rankOne]
  have hmin := intrinsicEven_rankPrime_gap_principal_minors_pos hdual
  have hq := real_twoByTwo_quadratic_pos
    (intrinsicEvenFavourableGram00 -
      intrinsicEvenGrowingWeight * intrinsicEvenGrowingVector0 ^ 2)
    (intrinsicEvenFavourableGram02 -
      intrinsicEvenGrowingWeight * intrinsicEvenGrowingVector0 *
        intrinsicEvenGrowingVector2)
    (intrinsicEvenFavourableGram22 -
      intrinsicEvenGrowingWeight * intrinsicEvenGrowingVector2 ^ 2)
    c d hmin.1 hmin.2 hne
  nlinarith

/-- Consequently the negative endpoint profile form, and hence both of its
Sylvester gates, close from that one full-series inequality. -/
theorem factorTwoIntrinsicEven_minus_endpoint_gates_of_fullSeries
    (hdual : intrinsicEvenGrowingDualNumerator <
      intrinsicEvenFavourableGram00 * intrinsicEvenFavourableGram22 -
        intrinsicEvenFavourableGram02 ^ 2) :
    0 < factorTwoStructuralPhaseLow00 (-1) ∧
      0 < factorTwoIntrinsicEvenPhaseDet (-1) := by
  apply factorTwoIntrinsicEven_endpoint_gates_of_profile_pos (-1)
  intro c d hne
  have hgap := intrinsicEven_growingHead_lt_fullTail_add_prime
    hdual c d hne
  have hclean := factorTwoIntrinsicEven_clean_pos c d hne
  have hform :
      0 < yoshidaEndpointOddCleanQuadratic
          (factorTwoEvenStructuralLowProfile c d) -
        factorTwoCenteredSymmetricPerturbation
          (factorTwoEvenStructuralLowProfile c d) := by
    rw [factorTwoIntrinsicEven_minus_endpoint_eq_rankPrime]
    nlinarith
  simpa only [neg_one_mul, sub_eq_add_neg] using hform

/-- Final structural interface: positivity of the exact centered variance
gap closes the negative endpoint gates.  What remains is now solely an
analytic lower bound for this infinite variance expression. -/
theorem factorTwoIntrinsicEven_minus_endpoint_gates_of_centeredVarianceGap
    (hgap : 0 < intrinsicEvenRankPrimeCenteredVarianceGap) :
    0 < factorTwoStructuralPhaseLow00 (-1) ∧
      0 < factorTwoIntrinsicEvenPhaseDet (-1) := by
  have hdetMass : 0 < twoByTwoDet
      (intrinsicEvenFavourableGram00 - intrinsicEvenGrowingMass)
      (intrinsicEvenFavourableGram02 -
        intrinsicEvenGrowingMass * intrinsicEvenGrowingDirection)
      (intrinsicEvenFavourableGram22 -
        intrinsicEvenGrowingMass * intrinsicEvenGrowingDirection ^ 2) := by
    rw [intrinsicEven_rankPrimeGap_det_eq_centeredVarianceGap]
    exact hgap
  have hdetVector : 0 < twoByTwoDet
      (intrinsicEvenFavourableGram00 -
        intrinsicEvenGrowingWeight * intrinsicEvenGrowingVector0 ^ 2)
      (intrinsicEvenFavourableGram02 -
        intrinsicEvenGrowingWeight * intrinsicEvenGrowingVector0 *
          intrinsicEvenGrowingVector2)
      (intrinsicEvenFavourableGram22 -
        intrinsicEvenGrowingWeight * intrinsicEvenGrowingVector2 ^ 2) := by
    rw [intrinsicEvenGrowing_cross_eq_mass_direction,
      intrinsicEvenGrowing_22_eq_mass_direction_sq]
    simpa only [intrinsicEvenGrowingMass] using hdetMass
  have hdual :=
    intrinsicEvenGrowingDualNumerator_lt_det_iff_gapDet_pos.mpr hdetVector
  apply factorTwoIntrinsicEven_minus_endpoint_gates_of_fullSeries
  simpa only [twoByTwoDet] using hdual

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenLowFullSeriesDomination
