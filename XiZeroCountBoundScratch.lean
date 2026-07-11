import ArithmeticHodge.Analysis.ZetaZeroCount
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic

open Complex Filter Topology Real MeromorphicOn

namespace ArithmeticHodge.Analysis

open Metric Function

/-- Every multiplicity counted in a rectangle contained in the radius-`r`
disk contributes at least `log 2` to Jensen's integrated count at radius
`2 * r`. -/
theorem xiZeroCount_mul_log_two_le_integratedZeroCount_scratch
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
theorem xiZeroCount_le_logMax_scratch
    (sigmaLower sigmaUpper heightLower heightUpper r : ℝ)
    (hr : 0 < r)
    (hrectangle : ∀ z ∈ xiZeroRectangle sigmaLower sigmaUpper heightLower heightUpper,
      ‖z‖ ≤ r) :
    (xiZeroCount sigmaLower sigmaUpper heightLower heightUpper : ℝ) ≤
      (1 / Real.log 2) *
        (Real.log (EntireFunction.maxModulus xiFunction (2 * r)) -
          Real.log ‖xiFunction 0‖) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlower := xiZeroCount_mul_log_two_le_integratedZeroCount_scratch
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
theorem norm_le_height_add_one_of_mem_xiZeroRectangle_scratch
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
theorem xiCriticalStripZeroCount_le_logMax_scratch (T : ℝ) (hT : 0 ≤ T) :
    (xiZeroCount 0 1 (-T) T : ℝ) ≤
      (1 / Real.log 2) *
        (Real.log (EntireFunction.maxModulus xiFunction (2 * (T + 1))) -
          Real.log ‖xiFunction 0‖) := by
  apply xiZeroCount_le_logMax_scratch 0 1 (-T) T (T + 1) (by linarith)
  intro z hz
  exact norm_le_height_add_one_of_mem_xiZeroRectangle_scratch hT hz

namespace EntireFunction

/-- The standard eventual max-modulus consequence of the definition of
entire order, exposed here for the weighted-count experiment. -/
private theorem logMax_eventually_le_rpow_scratch (f : ℂ → ℂ) (alpha : ℝ)
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
theorem xiCriticalStripZeroCount_eventually_le_rpow_scratch
    (alpha : ℝ) (halpha : 1 < alpha) :
    ∃ (C Rzero : ℝ), 0 < C ∧ 1 ≤ Rzero ∧
      ∀ T, Rzero ≤ T →
        (xiZeroCount 0 1 (-T) T : ℝ) ≤ C * T ^ alpha := by
  have horder : EntireFunction.entireOrder xiFunction < (alpha : EReal) := by
    rw [xiFunction_order]
    exact_mod_cast halpha
  obtain ⟨Rone, hRone⟩ := Filter.eventually_atTop.mp
    (EntireFunction.logMax_eventually_le_rpow_scratch xiFunction alpha horder)
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
  have hJ := xiCriticalStripZeroCount_le_logMax_scratch T hT_pos.le
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

#print axioms xiZeroCount_mul_log_two_le_integratedZeroCount_scratch
#print axioms xiZeroCount_le_logMax_scratch
#print axioms xiCriticalStripZeroCount_le_logMax_scratch
#print axioms xiCriticalStripZeroCount_eventually_le_rpow_scratch

end ArithmeticHodge.Analysis
