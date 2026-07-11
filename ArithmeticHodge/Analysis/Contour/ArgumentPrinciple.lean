/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
Authors: Chris Birkbeck
Modified for the ArithmeticHodge namespace and current Mathlib API.
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import ArithmeticHodge.Analysis.Contour.CauchyGoursat

/-!
# The argument principle

For `f : ℂ → ℂ` meromorphic on a closed disc `C(c, R)` whose nonzero-order points are contained in a
finite set `S` inside the open disc, on which `ord z = meromorphicOrderAt f z`, the contour integral
of the logarithmic derivative counts the zeros and poles with multiplicity:
`∮_{C(c,R)} f'/f = 2πi · ∑_{z ∈ S} ord z`.

The order is positive at a zero and negative at a pole. No pointwise regularity of the raw function
is required: the proof passes through Mathlib's meromorphic normal form, so isolated wrong values do
not affect the contour integral.

## Main results

* `ArithmeticHodge.Analysis.Contour.logDeriv_eventuallyEq_principalPart` splits the logarithmic
  derivative into its simple-pole principal part and an analytic term.
* `ArithmeticHodge.Analysis.Contour.argumentPrinciple` counts every nonzero meromorphic order in a
  finite subset of the open disc.
* `ArithmeticHodge.Analysis.Contour.argumentPrinciple_local` is the one-point specialization.

## Provenance

Ported from TauCeti commit `0c70accf71cf8085ca7661cc7cbf7dd6c2bca7be`. TauCeti's circle
specialization was adapted from the AINTLIB `LeanModularForms` generalized residue theory,
particularly `GeneralizedResidueTheory/Residue.lean` and `Residue/GeneralizedTheoremBase.lean`.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997.
-/

public section

open Filter Topology Metric Complex
open scoped Real

namespace ArithmeticHodge.Analysis.Contour

/-- At a point where a function is analytic and non-vanishing, its logarithmic derivative is
analytic. -/
lemma analyticAt_logDeriv_of_analyticAt {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z)
    (hz : f z ≠ 0) : AnalyticAt ℂ (logDeriv f) z := by
  rw [logDeriv]
  exact hf.deriv.div hf hz

/-- The logarithmic derivative depends only on the germ. -/
private lemma logDeriv_eq_of_eventuallyEq {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) :
    logDeriv f z = logDeriv g z := by
  rw [logDeriv_apply, logDeriv_apply, h.deriv_eq, h.eq_of_nhds]

/-- Logarithmic derivative of a local factorization `(· - c) ^ n · g`, away from `c`. -/
private lemma logDeriv_zpow_sub_mul {g : ℂ → ℂ} {c z : ℂ} {n : ℤ} (hz : z ≠ c)
    (hg_ne : g z ≠ 0) (hg_diff : DifferentiableAt ℂ g z) :
    logDeriv (fun w => (w - c) ^ n * g w) z =
      (n : ℂ) * (z - c)⁻¹ + logDeriv g z := by
  have hz_sub : z - c ≠ 0 := sub_ne_zero.2 hz
  have hzpow : (z - c) ^ n ≠ 0 := zpow_ne_zero n hz_sub
  have hdz : DifferentiableAt ℂ (fun w => (w - c) ^ n) z :=
    (differentiableAt_id.sub_const c).zpow (Or.inl hz_sub)
  have hld_sub : logDeriv (fun w => w - c) z = (z - c)⁻¹ := by
    have hderiv : deriv (fun w => w - c) z = 1 := by simp
    rw [logDeriv_apply, hderiv, one_div]
  rw [logDeriv_mul z hzpow hg_ne hdz hg_diff,
    logDeriv_fun_zpow (f := fun w => w - c) (differentiableAt_id.sub_const c) n, hld_sub]

/-- **Simple-pole splitting of the logarithmic derivative.** Near a point `s` where `F` is
meromorphic of order `n`, its logarithmic derivative is the principal part
`n · (· - s)⁻¹` plus the logarithmic derivative of an analytic non-vanishing factor. -/
theorem logDeriv_eventuallyEq_principalPart {F : ℂ → ℂ} {s : ℂ} {n : ℤ}
    (hF : MeromorphicAt F s) (hn : meromorphicOrderAt F s = (n : WithTop ℤ)) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g s ∧ g s ≠ 0 ∧
      logDeriv F =ᶠ[𝓝[≠] s] fun z => (n : ℂ) * (z - s)⁻¹ + logDeriv g z := by
  obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := (meromorphicOrderAt_eq_int_iff hF).1 hn
  refine ⟨g, hg_an, hg_ne, ?_⟩
  have hFH : ∀ᶠ z in 𝓝[≠] s, F =ᶠ[𝓝 z] fun w => (w - s) ^ n • g w := by
    obtain ⟨U, hU_open, hcU, hU_sub⟩ := mem_nhdsWithin.1 hg_eq
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hU_open.mem_nhds hcU), self_mem_nhdsWithin]
      with z hzU hz_ne
    filter_upwards [(hU_open.inter isOpen_compl_singleton).mem_nhds ⟨hzU, hz_ne⟩] with w hw
      using hU_sub hw
  filter_upwards [hFH, hg_an.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    (hg_an.continuousAt.eventually_ne hg_ne).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hz_FH hz_gan hz_gne hz_ne
  have hmul : (fun w => (w - s) ^ n • g w) = fun w => (w - s) ^ n * g w := by
    funext w
    rw [smul_eq_mul]
  rw [logDeriv_eq_of_eventuallyEq hz_FH, hmul]
  exact logDeriv_zpow_sub_mul hz_ne hz_gne hz_gan.differentiableAt

/-- **The argument principle.** The circle integral of the logarithmic derivative counts the
zeros minus poles in the disc, with meromorphic multiplicity. -/
theorem argumentPrinciple {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (S : Finset ℂ) (ord : ℂ → ℤ)
    (hf : MeromorphicOn f (Metric.closedBall c R))
    (hS : (S : Set ℂ) ⊆ Metric.ball c R)
    (hsupp : ∀ z ∈ Metric.closedBall c R, meromorphicOrderAt f z ≠ 0 → z ∈ S)
    (hord : ∀ z ∈ S, meromorphicOrderAt f z = (ord z : WithTop ℤ)) :
    circleIntegral (logDeriv f) c R =
      2 * (Real.pi : ℂ) * Complex.I * (∑ z ∈ S, (ord z : ℂ)) := by
  set F := toMeromorphicNFOn f (closedBall c R) with hF_def
  have hF_nf : MeromorphicNFOn F (closedBall c R) := meromorphicNFOn_toMeromorphicNFOn f _
  have hF_mero : MeromorphicOn F (closedBall c R) := hF_nf.meromorphicOn
  have hordF : ∀ z ∈ closedBall c R, meromorphicOrderAt F z = meromorphicOrderAt f z :=
    fun z hz => meromorphicOrderAt_toMeromorphicNFOn hf hz
  have hoffF : ∀ z ∈ closedBall c R, z ∉ S → AnalyticAt ℂ F z ∧ F z ≠ 0 := by
    intro z hz hzS
    have h0 : meromorphicOrderAt F z = 0 := by
      rw [hordF z hz]
      by_contra h
      exact hzS (hsupp z hz h)
    exact ⟨(hF_nf hz).meromorphicOrderAt_nonneg_iff_analyticAt.1 h0.symm.le,
      (hF_nf hz).meromorphicOrderAt_eq_zero_iff.1 h0⟩
  have htransfer : circleIntegral (logDeriv f) c R = circleIntegral (logDeriv F) c R := by
    refine circleIntegral.circleIntegral_congr_codiscreteWithin ?_ hR.ne'
    have hspU : sphere c |R| ⊆ closedBall c R := by
      rw [abs_of_pos hR]
      exact sphere_subset_closedBall
    filter_upwards [(toMeromorphicNFOn_eqOn_codiscrete hf).filter_mono
        (Filter.codiscreteWithin.mono hspU), self_mem_codiscreteWithin (sphere c |R|)]
      with z hz_eq hz_mem
    have hne : f =ᶠ[𝓝[≠] z] F :=
      (hf.toMeromorphicNFOn_eq_self_on_nhdsNE (hspU hz_mem)).symm
    exact logDeriv_eq_of_eventuallyEq (eventuallyEq_nhds_of_eventuallyEq_nhdsNE hne hz_eq)
  rw [htransfer]
  have hsphere_notS : ∀ z ∈ sphere c R, z ∉ S := by
    intro z hz hzS
    rw [Metric.mem_sphere] at hz
    exact absurd hz (ne_of_lt (Metric.mem_ball.1 (hS (Finset.mem_coe.2 hzS))))
  have hzs_ne : ∀ z ∈ sphere c R, ∀ s ∈ S, z ≠ s := by
    intro z hz s hsS h
    subst h
    exact absurd hsS (hsphere_notS z hz)
  set P : ℂ → ℂ := fun z => ∑ s ∈ S, (ord s : ℂ) * (z - s)⁻¹ with hP_def
  have hP_mero : MeromorphicOn P (closedBall c R) := by
    rw [hP_def]
    refine MeromorphicOn.fun_sum fun s z _ => ?_
    exact (MeromorphicAt.const (ord s : ℂ) z).mul
      (((MeromorphicAt.id z).sub (MeromorphicAt.const s z)).inv)
  have hlogF_mero : MeromorphicOn (logDeriv F) (closedBall c R) := hF_mero.logDeriv
  have hA0 : circleIntegral (fun z => logDeriv F z - P z) c R = 0 := by
    refine circleIntegral_eq_zero_of_meromorphicOrderAt_nonneg hR.le
      (hlogF_mero.sub hP_mero) ?_
    intro z hz
    by_cases hzS : z ∈ S
    · have hz_ord : meromorphicOrderAt F z = (ord z : WithTop ℤ) :=
        (hordF z hz).trans (hord z hzS)
      obtain ⟨g, hg_an, hg_ne, hg_germ⟩ :=
        logDeriv_eventuallyEq_principalPart (hF_mero z hz) hz_ord
      have hA_eq : (fun w => logDeriv F w - P w) =ᶠ[𝓝[≠] z]
          fun w => logDeriv g w - ∑ s ∈ S.erase z, (ord s : ℂ) * (w - s)⁻¹ := by
        filter_upwards [hg_germ] with w hw
        simp only [hP_def,
          ← Finset.add_sum_erase S (fun s => (ord s : ℂ) * (w - s)⁻¹) hzS]
        rw [hw]
        ring
      have hrest_an :
          AnalyticAt ℂ (fun w => ∑ s ∈ S.erase z, (ord s : ℂ) * (w - s)⁻¹) z :=
        Finset.analyticAt_fun_sum _ fun s hs =>
          analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).inv
            (sub_ne_zero.2 (Ne.symm (Finset.ne_of_mem_erase hs))))
      rw [meromorphicOrderAt_congr hA_eq]
      exact ((analyticAt_logDeriv_of_analyticAt hg_an hg_ne).sub
        hrest_an).meromorphicOrderAt_nonneg
    · have hz_off := hoffF z hz hzS
      have hP_an : AnalyticAt ℂ P z := by
        rw [hP_def]
        refine Finset.analyticAt_fun_sum _ fun s hsS =>
          analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.2 ?_))
        rintro rfl
        exact hzS hsS
      exact ((analyticAt_logDeriv_of_analyticAt hz_off.1 hz_off.2).sub
        hP_an).meromorphicOrderAt_nonneg
  have hP_intble : ∀ s ∈ S,
      CircleIntegrable (fun z => (ord s : ℂ) * (z - s)⁻¹) c R := fun s hsS =>
    ContinuousOn.circleIntegrable hR.le (continuousOn_const.mul
      ((continuousOn_id.sub continuousOn_const).inv₀
        fun z hz => sub_ne_zero.2 (hzs_ne z hz s hsS)))
  have hPint : circleIntegral P c R =
      2 * (Real.pi : ℂ) * Complex.I * (∑ z ∈ S, (ord z : ℂ)) := by
    have hterm : ∀ s ∈ S, (∮ z in C(c, R), (ord s : ℂ) * (z - s)⁻¹) =
        (ord s : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := fun s hsS => by
      rw [circleIntegral.integral_const_mul,
        circleIntegral.integral_sub_inv_of_mem_ball (hS (Finset.mem_coe.2 hsS))]
    rw [hP_def, circleIntegral.integral_fun_sum hP_intble, Finset.sum_congr rfl hterm,
      ← Finset.sum_mul]
    ring
  have hlogF_cont : ContinuousOn (logDeriv F) (sphere c R) := fun z hz =>
    (analyticAt_logDeriv_of_analyticAt
      (hoffF z (sphere_subset_closedBall hz) (hsphere_notS z hz)).1
      (hoffF z (sphere_subset_closedBall hz) (hsphere_notS z hz)).2).continuousAt.continuousWithinAt
  have hP_cont : ContinuousOn P (sphere c R) := by
    rw [hP_def]
    exact continuousOn_finset_sum S fun s hsS => continuousOn_const.mul
      ((continuousOn_id.sub continuousOn_const).inv₀
        fun z hz => sub_ne_zero.2 (hzs_ne z hz s hsS))
  have hsub := (circleIntegral.integral_sub
    (ContinuousOn.circleIntegrable hR.le hlogF_cont)
    (ContinuousOn.circleIntegrable hR.le hP_cont)).symm
  rw [hA0, sub_eq_zero] at hsub
  rw [hsub, hPint]

/-- **Local argument principle.** If `c` is the only point of the closed disc that can have
nonzero meromorphic order, then the logarithmic-derivative integral is `2πi` times that order. -/
theorem argumentPrinciple_local {f : ℂ → ℂ} {c : ℂ} {R : ℝ} {n : ℤ} (hR : 0 < R)
    (hf : MeromorphicOn f (Metric.closedBall c R))
    (honly : ∀ z ∈ Metric.closedBall c R, meromorphicOrderAt f z ≠ 0 → z = c)
    (hn : meromorphicOrderAt f c = (n : WithTop ℤ)) :
    circleIntegral (logDeriv f) c R =
      2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) := by
  have key := argumentPrinciple hR {c} (fun _ => n) hf
    (by
      rw [Finset.coe_singleton, Set.singleton_subset_iff]
      exact Metric.mem_ball_self hR)
    (fun z hz hz0 => Finset.mem_singleton.2 (honly z hz hz0))
    (fun z hz => by
      rw [Finset.mem_singleton.1 hz]
      exact hn)
  simpa using key

end ArithmeticHodge.Analysis.Contour
