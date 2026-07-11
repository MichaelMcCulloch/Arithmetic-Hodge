/-
  Enumeration-independent zero counting for the Riemann xi function.

  The divisor of an entire function records distinct zeros together with their
  analytic multiplicities.  Restricting the xi divisor to a compact rectangle
  therefore gives a finite, enumeration-independent zero count suitable for a
  future Riemann--von Mangoldt theorem.
-/

import ArithmeticHodge.Analysis.ZetaProduct
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.Analysis.Meromorphic.NormalForm

open Complex Filter Topology

namespace ArithmeticHodge.Analysis

/-- The closed axis-parallel complex rectangle
`[sigmaLower, sigmaUpper] x [heightLower, heightUpper]`. -/
def xiZeroRectangle (sigmaLower sigmaUpper heightLower heightUpper : ℝ) : Set ℂ :=
  Set.Icc sigmaLower sigmaUpper ×ℂ Set.Icc heightLower heightUpper

theorem isCompact_xiZeroRectangle (sigmaLower sigmaUpper heightLower heightUpper : ℝ) :
    IsCompact (xiZeroRectangle sigmaLower sigmaUpper heightLower heightUpper) := by
  exact isCompact_Icc.reProdIm isCompact_Icc

/-- The global meromorphic divisor of xi.  Since xi is entire, this divisor is
pointwise nonnegative and its values are zero multiplicities. -/
noncomputable def xiDivisor : Function.locallyFinsupp ℂ ℤ :=
  MeromorphicOn.divisor xiFunction Set.univ

private theorem analyticOnNhd_xiFunction_univ :
    AnalyticOnNhd ℂ xiFunction Set.univ :=
  differentiable_xiFunction.differentiableOn.analyticOnNhd isOpen_univ

theorem xiDivisor_nonneg (z : ℂ) : 0 ≤ xiDivisor z := by
  exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg analyticOnNhd_xiFunction_univ z

private theorem xiFunction_meromorphicOrderAt_ne_top (z : ℂ) :
    meromorphicOrderAt xiFunction z ≠ ⊤ := by
  have hnormal0 :=
    (analyticOnNhd_xiFunction_univ 0 (Set.mem_univ 0)).meromorphicNFAt
  have horder0 : meromorphicOrderAt xiFunction 0 = 0 :=
    hnormal0.meromorphicOrderAt_eq_zero_iff.mpr (by
      rw [xiFunction_zero_val]
      norm_num)
  have hfinite0 : meromorphicOrderAt xiFunction 0 ≠ ⊤ := by
    rw [horder0]
    exact WithTop.zero_ne_top
  exact analyticOnNhd_xiFunction_univ.meromorphicOn
    |>.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (Set.mem_univ 0) (Set.mem_univ z) hfinite0

/-- The support of the xi divisor is exactly the zero set of xi. -/
theorem mem_xiDivisor_support_iff (z : ℂ) :
    z ∈ Function.support xiDivisor ↔ xiFunction z = 0 := by
  have hzeroSet := analyticOnNhd_xiFunction_univ.meromorphicNFOn
    |>.zero_set_eq_divisor_support (fun z => xiFunction_meromorphicOrderAt_ne_top z)
  have hz := Set.ext_iff.mp hzeroSet z
  simpa [xiDivisor] using hz.symm

/-- The analytic multiplicity of `z` as a zero of xi. -/
noncomputable def xiZeroMultiplicity (z : ℂ) : ℕ :=
  (xiDivisor z).toNat

/-- Positive multiplicity is equivalent to vanishing of xi. -/
theorem xiZeroMultiplicity_pos_iff (z : ℂ) :
    0 < xiZeroMultiplicity z ↔ xiFunction z = 0 := by
  constructor
  · intro hpos
    apply (mem_xiDivisor_support_iff z).mp
    rw [Function.mem_support]
    intro hzero
    simp [xiZeroMultiplicity, hzero] at hpos
  · intro hxi
    have hdiv_ne : xiDivisor z ≠ 0 := by
      simpa [Function.mem_support] using (mem_xiDivisor_support_iff z).mpr hxi
    have hnat_ne : xiZeroMultiplicity z ≠ 0 := by
      intro hzero
      have hle : xiDivisor z ≤ 0 := Int.toNat_eq_zero.mp hzero
      exact hdiv_ne (le_antisymm hle (xiDivisor_nonneg z))
    exact Nat.pos_of_ne_zero hnat_ne

/-- Multiplicity weight restricted to a compact rectangle. -/
noncomputable def xiZeroWeight
    (sigmaLower sigmaUpper heightLower heightUpper : ℝ) (z : ℂ) : ℕ := by
  classical
  exact if z ∈ xiZeroRectangle sigmaLower sigmaUpper heightLower heightUpper then
      xiZeroMultiplicity z
    else
      0

/-- The restricted multiplicity weight has finite support. -/
theorem xiZeroWeight_hasFiniteSupport
    (sigmaLower sigmaUpper heightLower heightUpper : ℝ) :
    Function.HasFiniteSupport
      (xiZeroWeight sigmaLower sigmaUpper heightLower heightUpper) := by
  let rectangle := xiZeroRectangle sigmaLower sigmaUpper heightLower heightUpper
  have hfinite :
      (rectangle ∩ Function.support (xiDivisor : ℂ → ℤ)).Finite :=
    xiDivisor.locallyFiniteSupport.finite_inter_support_of_isCompact
      (isCompact_xiZeroRectangle sigmaLower sigmaUpper heightLower heightUpper)
  apply hfinite.subset
  intro z hz
  have hweight_ne :
      xiZeroWeight sigmaLower sigmaUpper heightLower heightUpper z ≠ 0 := hz
  have hzrect : z ∈ rectangle := by
    by_contra hznot
    exact hweight_ne (by simp [xiZeroWeight, rectangle, hznot])
  have hmult_ne : xiZeroMultiplicity z ≠ 0 := by
    simpa [xiZeroWeight, rectangle, hzrect] using hweight_ne
  have hdiv_ne : xiDivisor z ≠ 0 := by
    intro hzero
    exact hmult_ne (by simp [xiZeroMultiplicity, hzero])
  exact ⟨hzrect, hdiv_ne⟩

/-- A multiplicity-weighted, enumeration-independent xi zero count in a
closed rectangle. -/
noncomputable def xiZeroCount
    (sigmaLower sigmaUpper heightLower heightUpper : ℝ) : ℕ :=
  ∑ᶠ z : ℂ, xiZeroWeight sigmaLower sigmaUpper heightLower heightUpper z

/-- A point contributes positively precisely when it lies in the rectangle
and is a zero of xi. -/
theorem xiZeroWeight_pos_iff
    (sigmaLower sigmaUpper heightLower heightUpper : ℝ) (z : ℂ) :
    0 < xiZeroWeight sigmaLower sigmaUpper heightLower heightUpper z ↔
      z ∈ xiZeroRectangle sigmaLower sigmaUpper heightLower heightUpper ∧
        xiFunction z = 0 := by
  by_cases hz : z ∈ xiZeroRectangle sigmaLower sigmaUpper heightLower heightUpper
  · simp [xiZeroWeight, hz, xiZeroMultiplicity_pos_iff]
  · simp [xiZeroWeight, hz]

/-- The finite set of distinct xi zeros in the rectangle.  Multiplicity is
carried separately by `xiZeroMultiplicity`. -/
noncomputable def xiZerosInRectangle
    (sigmaLower sigmaUpper heightLower heightUpper : ℝ) : Finset ℂ :=
  (xiZeroWeight_hasFiniteSupport sigmaLower sigmaUpper heightLower heightUpper).toFinset

theorem mem_xiZerosInRectangle_iff
    (sigmaLower sigmaUpper heightLower heightUpper : ℝ) (z : ℂ) :
    z ∈ xiZerosInRectangle sigmaLower sigmaUpper heightLower heightUpper ↔
      z ∈ xiZeroRectangle sigmaLower sigmaUpper heightLower heightUpper ∧
        xiFunction z = 0 := by
  rw [xiZerosInRectangle, Set.Finite.mem_toFinset]
  change xiZeroWeight sigmaLower sigmaUpper heightLower heightUpper z ≠ 0 ↔ _
  rw [← Nat.pos_iff_ne_zero, xiZeroWeight_pos_iff]

/-- The `finsum` count is an ordinary finite sum of analytic multiplicities
over the distinct zeros in the rectangle. -/
theorem xiZeroCount_eq_sum
    (sigmaLower sigmaUpper heightLower heightUpper : ℝ) :
    xiZeroCount sigmaLower sigmaUpper heightLower heightUpper =
      ∑ z ∈ xiZerosInRectangle sigmaLower sigmaUpper heightLower heightUpper,
        xiZeroMultiplicity z := by
  classical
  rw [xiZeroCount, finsum_eq_sum _
    (xiZeroWeight_hasFiniteSupport sigmaLower sigmaUpper heightLower heightUpper)]
  apply Finset.sum_congr rfl
  intro z hz
  have hzrect : z ∈ xiZeroRectangle sigmaLower sigmaUpper heightLower heightUpper :=
    (mem_xiZerosInRectangle_iff sigmaLower sigmaUpper heightLower heightUpper z).mp hz |>.1
  simp [xiZeroWeight, hzrect]

/-- The affine involution appearing in the xi functional equation. -/
def complexOneSubEquiv : ℂ ≃ ℂ where
  toFun z := 1 - z
  invFun z := 1 - z
  left_inv z := by ring
  right_inv z := by ring

/-- The functional equation preserves analytic zero multiplicity. -/
theorem xiDivisor_one_sub (z : ℂ) : xiDivisor (1 - z) = xiDivisor z := by
  have hg : AnalyticAt ℂ (fun w : ℂ => 1 - w) z :=
    analyticAt_const.sub analyticAt_id
  have hgderiv : deriv (fun w : ℂ => 1 - w) z ≠ 0 := by
    change deriv ((fun _ : ℂ => (1 : ℂ)) - id) z ≠ 0
    rw [((hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z)).deriv]
    norm_num
  have hcomp := meromorphicOrderAt_comp_of_deriv_ne_zero
    (f := xiFunction) hg hgderiv
  have hfun : xiFunction ∘ (fun w : ℂ => 1 - w) = xiFunction := by
    funext w
    exact xiFunction_one_sub w
  have horder :
      meromorphicOrderAt xiFunction (1 - z) = meromorphicOrderAt xiFunction z := by
    rw [← hcomp, hfun]
  rw [xiDivisor,
    MeromorphicOn.divisor_apply analyticOnNhd_xiFunction_univ.meromorphicOn (Set.mem_univ _),
    MeromorphicOn.divisor_apply analyticOnNhd_xiFunction_univ.meromorphicOn (Set.mem_univ _),
    horder]

theorem xiZeroMultiplicity_one_sub (z : ℂ) :
    xiZeroMultiplicity (1 - z) = xiZeroMultiplicity z := by
  simp [xiZeroMultiplicity, xiDivisor_one_sub]

theorem one_sub_mem_xiZeroRectangle_iff
    (sigmaLower sigmaUpper heightLower heightUpper : ℝ) (z : ℂ) :
    1 - z ∈ xiZeroRectangle (1 - sigmaUpper) (1 - sigmaLower)
        (-heightUpper) (-heightLower) ↔
      z ∈ xiZeroRectangle sigmaLower sigmaUpper heightLower heightUpper := by
  simp only [xiZeroRectangle, mem_reProdIm, Set.mem_Icc, Complex.sub_re,
    Complex.one_re, Complex.sub_im, Complex.one_im]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

theorem xiZeroWeight_one_sub
    (sigmaLower sigmaUpper heightLower heightUpper : ℝ) (z : ℂ) :
    xiZeroWeight (1 - sigmaUpper) (1 - sigmaLower) (-heightUpper) (-heightLower)
        (complexOneSubEquiv z) =
      xiZeroWeight sigmaLower sigmaUpper heightLower heightUpper z := by
  classical
  change xiZeroWeight (1 - sigmaUpper) (1 - sigmaLower) (-heightUpper) (-heightLower)
      (1 - z) = xiZeroWeight sigmaLower sigmaUpper heightLower heightUpper z
  simp only [xiZeroWeight]
  rw [one_sub_mem_xiZeroRectangle_iff]
  split_ifs with hz
  · exact xiZeroMultiplicity_one_sub z
  · rfl

/-- Rectangle counts are invariant under the functional-equation symmetry
`z |-> 1 - z`, including analytic multiplicity. -/
theorem xiZeroCount_one_sub
    (sigmaLower sigmaUpper heightLower heightUpper : ℝ) :
    xiZeroCount (1 - sigmaUpper) (1 - sigmaLower) (-heightUpper) (-heightLower) =
      xiZeroCount sigmaLower sigmaUpper heightLower heightUpper := by
  calc
    xiZeroCount (1 - sigmaUpper) (1 - sigmaLower) (-heightUpper) (-heightLower) =
        ∑ᶠ z : ℂ,
          xiZeroWeight (1 - sigmaUpper) (1 - sigmaLower) (-heightUpper) (-heightLower)
            (complexOneSubEquiv z) := by
              rw [xiZeroCount]
              exact (finsum_comp_equiv complexOneSubEquiv).symm
    _ = xiZeroCount sigmaLower sigmaUpper heightLower heightUpper := by
      rw [xiZeroCount]
      apply finsum_congr
      exact xiZeroWeight_one_sub sigmaLower sigmaUpper heightLower heightUpper

/-- Functional-equation symmetry exchanges the upper and lower halves of the
critical strip, with analytic multiplicities preserved. -/
theorem xiCriticalStripZeroCount_lower_eq_upper (T : ℝ) :
    xiZeroCount 0 1 (-T) 0 = xiZeroCount 0 1 0 T := by
  simpa using xiZeroCount_one_sub 0 1 0 T

open Metric Function

/-- Every multiplicity counted in a rectangle contained in the radius-`r`
disk contributes at least `log 2` to Jensen's integrated count at radius
`2 * r`. -/
theorem xiZeroCount_mul_log_two_le_integratedZeroCount
    (sigmaLower sigmaUpper heightLower heightUpper r : ℝ)
    (hr : 0 < r)
    (hrectangle : ∀ z ∈ xiZeroRectangle sigmaLower sigmaUpper heightLower heightUpper,
      ‖z‖ ≤ r) :
    (xiZeroCount sigmaLower sigmaUpper heightLower heightUpper : ℝ) * Real.log 2 ≤
      EntireFunction.integratedZeroCount xiFunction (2 * r) := by
  have hR : 0 < 2 * r := by positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hD0 : xiDivisor 0 = 0 := by
    by_contra hne
    have hxi := (mem_xiDivisor_support_iff 0).mp hne
    rw [xiFunction_zero_val] at hxi
    norm_num at hxi
  unfold EntireFunction.integratedZeroCount
  rw [show (↑(0 : ℂ) : WithTop ℂ) = 0 by simp]
  rw [ValueDistribution.logCounting_zero]
  have hposPart : (MeromorphicOn.divisor xiFunction Set.univ)⁺ = xiDivisor := by
    ext z
    change (xiDivisor z)⁺ = xiDivisor z
    exact posPart_eq_self.mpr (xiDivisor_nonneg z)
  rw [hposPart]
  unfold Function.locallyFinsuppWithin.logCounting
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, hD0, Int.cast_zero, zero_mul, add_zero]
  let DB := Function.locallyFinsuppWithin.toClosedBall (2 * r) xiDivisor
  have hsupport : DB.support.Finite :=
    DB.finiteSupport (isCompact_closedBall 0 |2 * r|)
  rw [finsum_eq_sum_of_support_subset _ (s := hsupport.toFinset) (fun z hz => by
    simp only [Finset.mem_coe, hsupport.mem_toFinset, Function.mem_support]
    intro hzero
    exact (Function.mem_support.mp hz) (by simp [DB, hzero]))]
  have hzero_subset :
      xiZerosInRectangle sigmaLower sigmaUpper heightLower heightUpper ⊆
        hsupport.toFinset := by
    intro z hz
    have hzdata :=
      (mem_xiZerosInRectangle_iff sigmaLower sigmaUpper heightLower heightUpper z).mp hz
    have hzr : ‖z‖ ≤ r := hrectangle z hzdata.1
    have hzball : z ∈ closedBall (0 : ℂ) |2 * r| := by
      simp only [mem_closedBall, dist_zero_right, abs_of_pos hR]
      linarith
    rw [hsupport.mem_toFinset, Function.mem_support]
    rw [show DB z = xiDivisor z by
      exact Function.locallyFinsuppWithin.toClosedBall_eval_within xiDivisor hzball]
    intro hdiv
    have hmult_zero : xiZeroMultiplicity z = 0 := by
      simp [xiZeroMultiplicity, hdiv]
    have hmult_pos := (xiZeroMultiplicity_pos_iff z).mpr hzdata.2
    omega
  have hterm_nonneg : ∀ z ∈ hsupport.toFinset,
      0 ≤ (DB z : ℝ) * Real.log (2 * r * ‖z‖⁻¹) := by
    intro z hz
    have hzball : z ∈ closedBall (0 : ℂ) |2 * r| :=
      Function.locallyFinsuppWithin.toClosedBall_support_subset_closedBall xiDivisor
        (hsupport.mem_toFinset.mp hz)
    have hDB_ne : DB z ≠ 0 := hsupport.mem_toFinset.mp hz
    have hz_ne : z ≠ 0 := by
      intro hz0
      subst z
      have hDB0 : DB 0 = xiDivisor 0 :=
        Function.locallyFinsuppWithin.toClosedBall_eval_within xiDivisor (by
          simp [abs_of_pos hR, hr.le])
      exact hDB_ne (hDB0.trans hD0)
    rw [show DB z = xiDivisor z by
      exact Function.locallyFinsuppWithin.toClosedBall_eval_within xiDivisor hzball]
    apply mul_nonneg
    · exact_mod_cast xiDivisor_nonneg z
    · apply Real.log_nonneg
      rw [le_mul_inv_iff₀ (norm_pos_iff.mpr hz_ne)]
      simpa [mem_closedBall, dist_zero_right, abs_of_pos hR] using hzball
  have hterm_lower : ∀ z ∈
      xiZerosInRectangle sigmaLower sigmaUpper heightLower heightUpper,
      (xiZeroMultiplicity z : ℝ) * Real.log 2 ≤
        (DB z : ℝ) * Real.log (2 * r * ‖z‖⁻¹) := by
    intro z hz
    have hzdata :=
      (mem_xiZerosInRectangle_iff sigmaLower sigmaUpper heightLower heightUpper z).mp hz
    have hzr : ‖z‖ ≤ r := hrectangle z hzdata.1
    have hz_ne : z ≠ 0 := by
      intro hz0
      subst z
      rw [xiFunction_zero_val] at hzdata
      norm_num at hzdata
    have hzball : z ∈ closedBall (0 : ℂ) |2 * r| := by
      simp only [mem_closedBall, dist_zero_right, abs_of_pos hR]
      linarith
    have hlog : Real.log 2 ≤ Real.log (2 * r * ‖z‖⁻¹) := by
      apply Real.log_le_log (by norm_num)
      rw [le_mul_inv_iff₀ (norm_pos_iff.mpr hz_ne)]
      nlinarith
    have hmult_int : (xiZeroMultiplicity z : ℤ) = xiDivisor z :=
      Int.toNat_of_nonneg (xiDivisor_nonneg z)
    have hmult_real : (xiZeroMultiplicity z : ℝ) = (xiDivisor z : ℝ) := by
      exact_mod_cast hmult_int
    calc
      (xiZeroMultiplicity z : ℝ) * Real.log 2
          ≤ (xiZeroMultiplicity z : ℝ) * Real.log (2 * r * ‖z‖⁻¹) :=
        mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)
      _ = (DB z : ℝ) * Real.log (2 * r * ‖z‖⁻¹) := by
        rw [show DB z = xiDivisor z by
          exact Function.locallyFinsuppWithin.toClosedBall_eval_within xiDivisor hzball,
          hmult_real]
  calc
    (xiZeroCount sigmaLower sigmaUpper heightLower heightUpper : ℝ) * Real.log 2 =
        ∑ z ∈ xiZerosInRectangle sigmaLower sigmaUpper heightLower heightUpper,
          (xiZeroMultiplicity z : ℝ) * Real.log 2 := by
      rw [xiZeroCount_eq_sum]
      push_cast
      rw [Finset.sum_mul]
    _ ≤ ∑ z ∈ xiZerosInRectangle sigmaLower sigmaUpper heightLower heightUpper,
          (DB z : ℝ) * Real.log (2 * r * ‖z‖⁻¹) := by
      exact Finset.sum_le_sum fun z hz => hterm_lower z hz
    _ ≤ ∑ z ∈ hsupport.toFinset,
          (DB z : ℝ) * Real.log (2 * r * ‖z‖⁻¹) :=
      Finset.sum_le_sum_of_subset_of_nonneg hzero_subset
        (fun z hz _ => hterm_nonneg z hz)

/-- Jensen's quantitative max-modulus bound for the production
multiplicity-weighted rectangle count. -/
theorem xiZeroCount_le_logMax
    (sigmaLower sigmaUpper heightLower heightUpper r : ℝ)
    (hr : 0 < r)
    (hrectangle : ∀ z ∈ xiZeroRectangle sigmaLower sigmaUpper heightLower heightUpper,
      ‖z‖ ≤ r) :
    (xiZeroCount sigmaLower sigmaUpper heightLower heightUpper : ℝ) ≤
      (1 / Real.log 2) *
        (Real.log (EntireFunction.maxModulus xiFunction (2 * r)) -
          Real.log ‖xiFunction 0‖) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlower := xiZeroCount_mul_log_two_le_integratedZeroCount
    sigmaLower sigmaUpper heightLower heightUpper r hr hrectangle
  have hxi0 : xiFunction 0 ≠ 0 := by
    rw [xiFunction_zero_val]
    norm_num
  have hJensen := EntireFunction.jensen_zero_count_le_log_max
    xiFunction differentiable_xiFunction hxi0 (2 * r) (by positivity)
  have hchain :
      (xiZeroCount sigmaLower sigmaUpper heightLower heightUpper : ℝ) * Real.log 2 ≤
        Real.log (EntireFunction.maxModulus xiFunction (2 * r)) -
          Real.log ‖xiFunction 0‖ := hlower.trans hJensen
  calc
    (xiZeroCount sigmaLower sigmaUpper heightLower heightUpper : ℝ) =
        (xiZeroCount sigmaLower sigmaUpper heightLower heightUpper : ℝ) *
            Real.log 2 / Real.log 2 := by
      rw [mul_div_cancel_right₀ _ hlog2.ne']
    _ ≤ (Real.log (EntireFunction.maxModulus xiFunction (2 * r)) -
          Real.log ‖xiFunction 0‖) / Real.log 2 :=
      div_le_div_of_nonneg_right hchain hlog2.le
    _ = (1 / Real.log 2) *
        (Real.log (EntireFunction.maxModulus xiFunction (2 * r)) -
          Real.log ‖xiFunction 0‖) := by ring

/-- The standard symmetric critical-strip rectangle of height `T` lies in
the disk of radius `T + 1`. -/
theorem norm_le_height_add_one_of_mem_xiZeroRectangle
    {T : ℝ} (_hT : 0 ≤ T) {z : ℂ}
    (hz : z ∈ xiZeroRectangle 0 1 (-T) T) :
    ‖z‖ ≤ T + 1 := by
  rw [xiZeroRectangle, mem_reProdIm] at hz
  have hre : |z.re| ≤ 1 := by
    rw [abs_of_nonneg hz.1.1]
    exact hz.1.2
  have him : |z.im| ≤ T := (abs_le.mpr ⟨hz.2.1, hz.2.2⟩)
  calc
    ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ 1 + T := add_le_add hre him
    _ = T + 1 := by ring

/-- Direct Jensen bound for all nontrivial xi zeros with `|Im z| ≤ T`. -/
theorem xiCriticalStripZeroCount_le_logMax (T : ℝ) (hT : 0 ≤ T) :
    (xiZeroCount 0 1 (-T) T : ℝ) ≤
      (1 / Real.log 2) *
        (Real.log (EntireFunction.maxModulus xiFunction (2 * (T + 1))) -
          Real.log ‖xiFunction 0‖) := by
  apply xiZeroCount_le_logMax 0 1 (-T) T (T + 1) (by linarith)
  intro z hz
  exact norm_le_height_add_one_of_mem_xiZeroRectangle hT hz

namespace EntireFunction

/-- The standard eventual max-modulus consequence of the definition of
entire order, exposed here for the weighted-count experiment. -/
private theorem logMax_eventually_le_rpow (f : ℂ → ℂ) (alpha : ℝ)
    (halpha : entireOrder f < (alpha : EReal)) :
    ∀ᶠ r in Filter.atTop, Real.log (maxModulus f r) ≤ r ^ alpha := by
  have hev := eventually_lt_of_limsup_lt halpha
  apply (hev.and (Filter.eventually_ge_atTop 2)).mono
  intro r hr
  rcases hr with ⟨hr_limsup, hr_ge⟩
  have hr_gt1 : (1 : ℝ) < r := by linarith
  have hlogr : 0 < Real.log r := Real.log_pos hr_gt1
  have hr_limsup' :
      Real.log (Real.log (maxModulus f r)) / Real.log r < alpha := by
    exact_mod_cast hr_limsup
  by_cases hlogM : Real.log (maxModulus f r) ≤ 0
  · exact le_trans hlogM (Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one hr_gt1)) alpha)
  · push_neg at hlogM
    rw [show r ^ alpha = Real.exp (alpha * Real.log r) by
      rw [Real.rpow_def_of_pos (lt_trans zero_lt_one hr_gt1), mul_comm]]
    exact le_of_lt
      ((Real.log_lt_iff_lt_exp hlogM).mp ((div_lt_iff₀ hlogr).mp hr_limsup'))

end EntireFunction

/-- For every exponent strictly larger than one, the multiplicity-weighted
critical-strip xi zero count is eventually `O(T^alpha)`. -/
theorem xiCriticalStripZeroCount_eventually_le_rpow
    (alpha : ℝ) (halpha : 1 < alpha) :
    ∃ (C Rzero : ℝ), 0 < C ∧ 1 ≤ Rzero ∧
      ∀ T, Rzero ≤ T →
        (xiZeroCount 0 1 (-T) T : ℝ) ≤ C * T ^ alpha := by
  have horder : EntireFunction.entireOrder xiFunction < (alpha : EReal) := by
    rw [xiFunction_order]
    exact_mod_cast halpha
  obtain ⟨Rone, hRone⟩ := Filter.eventually_atTop.mp
    (EntireFunction.logMax_eventually_le_rpow xiFunction alpha horder)
  let Rzero := max 1 Rone
  let C := (1 / Real.log 2) * (4 ^ alpha + 1)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have halpha_pos : 0 < alpha := zero_lt_one.trans halpha
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hRzero : 1 ≤ Rzero := by
    exact le_max_left _ _
  refine ⟨C, Rzero, hC, hRzero, fun T hT => ?_⟩
  have hT_one : 1 ≤ T := hRzero.trans hT
  have hT_pos : 0 < T := zero_lt_one.trans_le hT_one
  have hscale_ge : Rone ≤ 2 * (T + 1) := by
    have hRone_T : Rone ≤ T := (le_max_right 1 Rone).trans hT
    linarith
  have hlogM :
      Real.log (EntireFunction.maxModulus xiFunction (2 * (T + 1))) ≤
        (2 * (T + 1)) ^ alpha := hRone _ hscale_ge
  have hpow : (2 * (T + 1)) ^ alpha ≤ 4 ^ alpha * T ^ alpha := by
    calc
      (2 * (T + 1)) ^ alpha ≤ (4 * T) ^ alpha := by
        apply Real.rpow_le_rpow (by positivity) (by linarith) halpha_pos.le
      _ = 4 ^ alpha * T ^ alpha := Real.mul_rpow (by norm_num) hT_pos.le
  have hlog2_le : Real.log 2 ≤ T ^ alpha := by
    calc
      Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
      _ ≤ T ^ alpha := Real.one_le_rpow hT_one halpha_pos.le
  have hxiLog : Real.log ‖xiFunction 0‖ = -Real.log 2 := by
    rw [xiFunction_zero_val]
    norm_num
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hJ := xiCriticalStripZeroCount_le_logMax T hT_pos.le
  rw [hxiLog, sub_neg_eq_add] at hJ
  calc
    (xiZeroCount 0 1 (-T) T : ℝ)
        ≤ (1 / Real.log 2) *
            (Real.log (EntireFunction.maxModulus xiFunction (2 * (T + 1))) +
              Real.log 2) := hJ
    _ ≤ (1 / Real.log 2) * (4 ^ alpha * T ^ alpha + T ^ alpha) := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg one_pos.le hlog2.le)
      linarith [hlogM.trans hpow]
    _ = C * T ^ alpha := by
      dsimp [C]
      ring

/-! ### RH as a statement about the xi divisor -/

/-- Every point of positive xi divisor multiplicity lies on the critical
line.  This is an enumeration-independent formulation of RH. -/
def XiDivisorOnCriticalLine : Prop :=
  ∀ z : ℂ, 0 < xiZeroMultiplicity z → z.re = 1 / 2

theorem xiDivisorOnCriticalLine_iff_RH :
    XiDivisorOnCriticalLine ↔ RiemannHypothesis := by
  constructor
  · intro hline s hs_zero hs_not_trivial hs_ne_one
    have hre := nontrivial_zeta_zero_re s hs_zero hs_not_trivial hs_ne_one
    apply hline s
    exact (xiZeroMultiplicity_pos_iff s).mpr
      ((xiFunction_zero_iff hre.1 hre.2).mpr hs_zero)
  · intro hRH z hmult
    have hxi := (xiZeroMultiplicity_pos_iff z).mp hmult
    have hre := xiFunction_zero_re hxi
    have hzeta := (xiFunction_zero_iff hre.1 hre.2).mp hxi
    apply hRH z hzeta
    · rintro ⟨n, hn⟩
      rw [hn] at hre
      have htriv_re : (-2 * ((n : ℂ) + 1)).re =
          -2 * ((n : ℝ) + 1) := by
        simp [Complex.add_re, Complex.mul_re, Complex.neg_re,
          Complex.one_re, Complex.one_im]
      rw [htriv_re] at hre
      have hn_nonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    · intro hz_one
      rw [hz_one] at hre
      norm_num at hre

/-- A falsification certificate for RH is exactly a positive-multiplicity xi
zero off the critical line. -/
theorem not_RH_iff_exists_xiZero_off_critical_line :
    ¬ RiemannHypothesis ↔
      ∃ z : ℂ, 0 < xiZeroMultiplicity z ∧ z.re ≠ 1 / 2 := by
  rw [← xiDivisorOnCriticalLine_iff_RH]
  simp [XiDivisorOnCriticalLine]

/-! ### Principal logarithms do not encode unwrapped contour phase -/

/-- The principal logarithm cannot satisfy the unwrapped Stirling-phase
identity used by the legacy prefix-count proof.  At the concrete height
`T = 100`, the proposed right-hand side is greater than `π`, whereas
`Complex.log_im_le_pi` bounds the left-hand side by `π` for every input. -/
theorem no_principal_log_Gamma_stirling_phase_at_100 :
    ¬ ∃ ε : ℝ, |ε| ≤ 1 ∧
      (Complex.log (Complex.Gamma
        (↑(1 / 4 : ℝ) + ↑((100 : ℝ) / 2) * Complex.I))).im =
        (100 : ℝ) / 2 * Real.log ((100 : ℝ) / 2) -
          (100 : ℝ) / 2 - Real.pi / 4 + ε / 100 := by
  rintro ⟨ε, hε, heq⟩
  have hexp_three_lt_fifty : Real.exp 3 < 50 := by
    calc
      Real.exp 3 = Real.exp 1 ^ (3 : ℕ) := by
        rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
        ring
      _ < 3 ^ (3 : ℕ) := by
        exact pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos 1).le (by norm_num)
      _ < 50 := by norm_num
  have hlog_fifty : 3 < Real.log 50 := by
    exact (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 50)).mpr
      hexp_three_lt_fifty
  have hε_lower : -1 ≤ ε := neg_le_of_abs_le hε
  have hpi_upper : Real.pi < 4 := Real.pi_lt_four
  have hphase_gt_pi : Real.pi <
      (100 : ℝ) / 2 * Real.log ((100 : ℝ) / 2) -
        (100 : ℝ) / 2 - Real.pi / 4 + ε / 100 := by
    norm_num at hlog_fifty ⊢
    nlinarith
  have hprincipal := Complex.log_im_le_pi
    (Complex.Gamma
      (↑(1 / 4 : ℝ) + ↑((100 : ℝ) / 2) * Complex.I))
  rw [heq] at hprincipal
  exact (not_lt_of_ge hprincipal) hphase_gt_pi

end ArithmeticHodge.Analysis
