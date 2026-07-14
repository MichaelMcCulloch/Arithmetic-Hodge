import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationOneSided

noncomputable section

open YoshidaConstantBounds
open YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseOddAffineKernelEstimate
open YoshidaRegularKernelBound

/-!
# A one-sided global remainder for the negative even perturbation

The degree-six pole-free model has a definite global error sign.  The proof
uses one Taylor remainder on the full interval: the degree-eight lower error
of the regular Yoshida kernel dominates the degree-eight upper error of the
two cosh terms.  There is no interval subdivision or sampled certificate.
-/

private def oneSidedCoshPolynomial6 (u : ℝ) : ℝ :=
  1 + u ^ 2 / 2 + u ^ 4 / 24 + u ^ 6 / 720

private def oneSidedCoshUpper8 (u : ℝ) : ℝ :=
  oneSidedCoshPolynomial6 u + (4 / 3 : ℝ) * u ^ 8 / 40320

private def oneSidedSinhDivPolynomial6 (u : ℝ) : ℝ :=
  1 + u ^ 2 / 6 + u ^ 4 / 120 + u ^ 6 / 5040

private def oneSidedSinhDivUpper8 (u : ℝ) : ℝ :=
  oneSidedSinhDivPolynomial6 u + (4 / 3 : ℝ) * u ^ 8 / 362880

private def oneSidedSechPolynomial6 (u : ℝ) : ℝ :=
  1 - u ^ 2 / 2 + 5 * u ^ 4 / 24 - 61 * u ^ 6 / 720

private def oneSidedCschRegularPolynomial5 (u : ℝ) : ℝ :=
  -u / 6 + 7 * u ^ 3 / 360 - 31 * u ^ 5 / 15120

private def oneSidedCschMultiplier6 (u : ℝ) : ℝ :=
  1 + u * oneSidedCschRegularPolynomial5 u

private def oneSidedSechLowerError (u : ℝ) : ℝ :=
  (3 / 4 : ℝ) *
    (u ^ 8 *
      (61 * u ^ 6 + 2412 * u ^ 4 + 70920 * u ^ 2 + 747720) /
        21772800)

private theorem oneSided_cosh_lt_four_thirds
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u < (7 / 10 : ℝ)) :
    Real.cosh u < (4 / 3 : ℝ) := by
  have huSq : u ^ 2 < (7 / 10 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hu hu0 (by norm_num)
  have hv0 : 0 ≤ u ^ 2 / 2 := by positivity
  have hvQuarter : u ^ 2 / 2 < (1 / 4 : ℝ) := by
    norm_num at huSq ⊢
    nlinarith
  have hv1 : u ^ 2 / 2 < (1 : ℝ) := hvQuarter.trans (by norm_num)
  have hExp : Real.exp (u ^ 2 / 2) ≤ 1 / (1 - u ^ 2 / 2) :=
    Real.exp_bound_div_one_sub_of_interval hv0 hv1
  have hFrac : 1 / (1 - u ^ 2 / 2) < (4 / 3 : ℝ) := by
    rw [div_lt_iff₀ (sub_pos.mpr hv1)]
    nlinarith
  exact (Real.cosh_le_exp_half_sq u).trans_lt (hExp.trans_lt hFrac)

private theorem oneSided_cosh_taylor_bounds
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u < (7 / 10 : ℝ)) :
    oneSidedCoshPolynomial6 u ≤ Real.cosh u ∧
      Real.cosh u ≤ oneSidedCoshUpper8 u := by
  rcases eq_or_lt_of_le hu0 with rfl | hupos
  · norm_num [oneSidedCoshPolynomial6, oneSidedCoshUpper8]
  · rcases taylor_mean_remainder_lagrange_iteratedDeriv
        (f := Real.cosh) (x₀ := 0) (x := u) (n := 7) hupos
        Real.contDiff_cosh.contDiffOn with ⟨w, hw, hTaylor⟩
    have hTaylorEval :
        taylorWithinEval Real.cosh 7 (Icc 0 u) 0 u =
          oneSidedCoshPolynomial6 u := by
      have hder (n : ℕ) :
          iteratedDerivWithin n Real.cosh (Icc 0 u) 0 =
            iteratedDeriv n Real.cosh 0 :=
        Real.iteratedDerivWithin_cosh_Icc n hupos ⟨le_rfl, hu0⟩
      rw [taylor_within_apply]
      simp [hder, Finset.sum_range_succ, oneSidedCoshPolynomial6]
      ring
    rw [hTaylorEval] at hTaylor
    norm_num [Real.iteratedDeriv_even_cosh] at hTaylor
    have hwBound : Real.cosh w < (4 / 3 : ℝ) :=
      oneSided_cosh_lt_four_thirds hw.1.le (hw.2.trans hu)
    have hremUpper :
        Real.cosh w * u ^ 8 / 40320 ≤
          (4 / 3 : ℝ) * u ^ 8 / 40320 := by
      gcongr
    have hrem0 : 0 ≤ Real.cosh w * u ^ 8 / 40320 := by
      positivity
    constructor
    · linarith
    · unfold oneSidedCoshUpper8
      linarith

private theorem oneSided_sinh_div_taylor_bounds
    {u : ℝ} (hu0 : 0 < u) (hu : u < (7 / 10 : ℝ)) :
    oneSidedSinhDivPolynomial6 u ≤ Real.sinh u / u ∧
      Real.sinh u / u ≤ oneSidedSinhDivUpper8 u := by
  rcases taylor_mean_remainder_lagrange_iteratedDeriv
      (f := Real.sinh) (x₀ := 0) (x := u) (n := 8) hu0
      Real.contDiff_sinh.contDiffOn with ⟨w, hw, hTaylor⟩
  have hTaylorEval :
      taylorWithinEval Real.sinh 8 (Icc 0 u) 0 u =
        u + u ^ 3 / 6 + u ^ 5 / 120 + u ^ 7 / 5040 := by
    have hder (n : ℕ) :
        iteratedDerivWithin n Real.sinh (Icc 0 u) 0 =
          iteratedDeriv n Real.sinh 0 :=
      Real.iteratedDerivWithin_sinh_Icc n hu0 ⟨le_rfl, hu0.le⟩
    rw [taylor_within_apply]
    simp [hder, Finset.sum_range_succ]
    ring
  rw [hTaylorEval] at hTaylor
  norm_num [Real.iteratedDeriv_odd_sinh] at hTaylor
  have hdiv :
      Real.sinh u / u - oneSidedSinhDivPolynomial6 u =
        Real.cosh w * u ^ 8 / 362880 := by
    unfold oneSidedSinhDivPolynomial6
    rw [show Real.sinh u / u -
          (1 + u ^ 2 / 6 + u ^ 4 / 120 + u ^ 6 / 5040) =
        (Real.sinh u -
          (u + u ^ 3 / 6 + u ^ 5 / 120 + u ^ 7 / 5040)) / u by
      field_simp [hu0.ne'],
      hTaylor]
    field_simp [hu0.ne']
  have hwBound : Real.cosh w < (4 / 3 : ℝ) :=
    oneSided_cosh_lt_four_thirds hw.1.le (hw.2.trans hu)
  have hrem0 : 0 ≤ Real.cosh w * u ^ 8 / 362880 := by positivity
  have hremUpper :
      Real.cosh w * u ^ 8 / 362880 ≤
        (4 / 3 : ℝ) * u ^ 8 / 362880 := by
    gcongr
  constructor
  · linarith
  · unfold oneSidedSinhDivUpper8
    linarith

private theorem oneSided_sech_lower_envelope
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u < (7 / 10 : ℝ)) :
    oneSidedSechLowerError u ≤
      1 / Real.cosh u - oneSidedSechPolynomial6 u := by
  have hTaylor := oneSided_cosh_taylor_bounds hu0 hu
  have huSq : u ^ 2 < (1 / 2 : ℝ) := by
    have h := pow_lt_pow_left₀ hu hu0 (by norm_num : (2 : ℕ) ≠ 0)
    norm_num at h ⊢
    linarith
  have huSix : u ^ 6 < (1 / 2 : ℝ) ^ 3 := by
    have h := pow_lt_pow_left₀ huSq (sq_nonneg u) (by norm_num : (3 : ℕ) ≠ 0)
    simpa only [show (u ^ 2) ^ 3 = u ^ 6 by ring] using h
  have hP0 : 0 ≤ oneSidedSechPolynomial6 u := by
    unfold oneSidedSechPolynomial6
    have huFour0 : 0 ≤ u ^ 4 := by positivity
    nlinarith
  let N : ℝ :=
    u ^ 8 *
      (61 * u ^ 6 + 2412 * u ^ 4 + 70920 * u ^ 2 + 747720) /
        21772800
  have hN0 : 0 ≤ N := by
    dsimp only [N]
    positivity
  have hNIdentity :
      1 - oneSidedSechPolynomial6 u * oneSidedCoshUpper8 u = N := by
    dsimp only [N]
    unfold oneSidedSechPolynomial6 oneSidedCoshUpper8
      oneSidedCoshPolynomial6
    ring
  have hNumeratorLower :
      N ≤ 1 - oneSidedSechPolynomial6 u * Real.cosh u := by
    rw [← hNIdentity]
    have hmul := mul_le_mul_of_nonneg_left hTaylor.2 hP0
    linarith
  have hNumerator0 :
      0 ≤ 1 - oneSidedSechPolynomial6 u * Real.cosh u :=
    hN0.trans hNumeratorLower
  have hrecip : (3 / 4 : ℝ) ≤ 1 / Real.cosh u := by
    rw [le_div_iff₀ (Real.cosh_pos u)]
    nlinarith [oneSided_cosh_lt_four_thirds hu0 hu]
  have hIdentity :
      1 / Real.cosh u - oneSidedSechPolynomial6 u =
        (1 - oneSidedSechPolynomial6 u * Real.cosh u) / Real.cosh u := by
    field_simp [(Real.cosh_pos u).ne']
  unfold oneSidedSechLowerError
  dsimp only [N] at hN0 hNumeratorLower ⊢
  rw [hIdentity]
  calc
    _ ≤ (3 / 4 : ℝ) *
        (1 - oneSidedSechPolynomial6 u * Real.cosh u) :=
      mul_le_mul_of_nonneg_left hNumeratorLower (by norm_num)
    _ ≤ (1 / Real.cosh u) *
        (1 - oneSidedSechPolynomial6 u * Real.cosh u) :=
      mul_le_mul_of_nonneg_right hrecip hNumerator0
    _ = _ := by ring

private theorem oneSided_csch_nonneg
    {u : ℝ} (hu0 : 0 < u) (hu : u < (7 / 10 : ℝ)) :
    0 ≤ 1 / Real.sinh u - 1 / u - oneSidedCschRegularPolynomial5 u := by
  let B : ℝ := Real.sinh u / u
  have hTaylorRaw := oneSided_sinh_div_taylor_bounds hu0 hu
  have hTaylor :
      oneSidedSinhDivPolynomial6 u ≤ B ∧
        B ≤ oneSidedSinhDivUpper8 u := hTaylorRaw
  have hB1 : (1 : ℝ) ≤ B := by
    dsimp only [B]
    rw [le_div_iff₀ hu0]
    simpa using (Real.self_le_sinh_iff.mpr hu0.le)
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB1
  have huSq : u ^ 2 < (1 / 2 : ℝ) := by
    have h := pow_lt_pow_left₀ hu hu0.le (by norm_num : (2 : ℕ) ≠ 0)
    norm_num at h ⊢
    linarith
  have huSix : u ^ 6 < (1 / 2 : ℝ) ^ 3 := by
    have h := pow_lt_pow_left₀ huSq (sq_nonneg u) (by norm_num : (3 : ℕ) ≠ 0)
    simpa only [show (u ^ 2) ^ 3 = u ^ 6 by ring] using h
  have hQ0 : 0 ≤ oneSidedCschMultiplier6 u := by
    unfold oneSidedCschMultiplier6 oneSidedCschRegularPolynomial5
    have huFour0 : 0 ≤ u ^ 4 := by positivity
    nlinarith
  have hFactorUpper :
      oneSidedCschMultiplier6 u * oneSidedSinhDivUpper8 u - 1 =
        -(u ^ 8 *
          (31 * u ^ 6 + 1380 * u ^ 4 + 56952 * u ^ 2 + 860328)) /
            4115059200 := by
    unfold oneSidedCschMultiplier6 oneSidedCschRegularPolynomial5
      oneSidedSinhDivUpper8 oneSidedSinhDivPolynomial6
    ring
  have hQBup : oneSidedCschMultiplier6 u * oneSidedSinhDivUpper8 u ≤ 1 := by
    rw [← sub_nonpos, hFactorUpper]
    have hnonneg : 0 ≤ u ^ 8 *
        (31 * u ^ 6 + 1380 * u ^ 4 + 56952 * u ^ 2 + 860328) := by
      positivity
    nlinarith
  have hQB : oneSidedCschMultiplier6 u * B ≤ 1 :=
    (mul_le_mul_of_nonneg_left hTaylor.2 hQ0).trans hQBup
  have hQleInv : oneSidedCschMultiplier6 u ≤ 1 / B := by
    rw [le_div_iff₀ hBpos]
    simpa only [one_mul] using hQB
  have hSinhPos : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu0
  have hMainIdentity :
      1 / Real.sinh u - 1 / u - oneSidedCschRegularPolynomial5 u =
        (1 / B - oneSidedCschMultiplier6 u) / u := by
    dsimp only [B]
    unfold oneSidedCschMultiplier6
    field_simp [hu0.ne', hSinhPos.ne']
    ring
  rw [hMainIdentity]
  exact div_nonneg (sub_nonneg.mpr hQleInv) hu0.le

private theorem oneSided_regularKernel_two_mul (u : ℝ) (hu : 0 < u) :
    yoshidaRegularKernel (2 * u) =
      (1 / 4 : ℝ) *
        (1 / Real.cosh u + (1 / Real.sinh u - 1 / u)) := by
  unfold yoshidaRegularKernel
  rw [if_neg (mul_ne_zero (by norm_num) hu.ne')]
  rw [show 2 * u / 2 = u by ring, Real.sinh_two_mul,
    ← Real.cosh_add_sinh]
  field_simp [hu.ne', (Real.sinh_pos_iff.mpr hu).ne',
    (Real.cosh_pos u).ne']
  ring

private theorem oneSided_regularKernelPolynomial6_two_mul (u : ℝ) :
    yoshidaRegularKernelPolynomial6 (2 * u) =
      (1 / 4 : ℝ) *
        (oneSidedSechPolynomial6 u + oneSidedCschRegularPolynomial5 u) := by
  unfold yoshidaRegularKernelPolynomial6 oneSidedSechPolynomial6
    oneSidedCschRegularPolynomial5
  ring

private theorem oneSided_regularKernel_error_lower
    {t : ℝ} (ht0 : 0 ≤ t) (htlog : t ≤ 2 * Real.log 2) :
    (3 / 500 : ℝ) * (t / 2) ^ 8 ≤
      yoshidaRegularKernel t - yoshidaRegularKernelPolynomial6 t := by
  rcases eq_or_lt_of_le ht0 with rfl | htpos
  · norm_num [yoshidaRegularKernel, yoshidaRegularKernelPolynomial6]
  · let u : ℝ := t / 2
    have hu0 : 0 < u := by
      dsimp only [u]
      linarith
    have hu : u < (7 / 10 : ℝ) := by
      dsimp only [u]
      have hlog := strict_log_two_bounds.2
      linarith
    have hSech := oneSided_sech_lower_envelope hu0.le hu
    have hCsch := oneSided_csch_nonneg hu0 hu
    have htEq : t = 2 * u := by
      dsimp only [u]
      ring
    have hDifference :
        yoshidaRegularKernel t - yoshidaRegularKernelPolynomial6 t =
          (1 / 4 : ℝ) *
            ((1 / Real.cosh u - oneSidedSechPolynomial6 u) +
              (1 / Real.sinh u - 1 / u -
                oneSidedCschRegularPolynomial5 u)) := by
      rw [htEq, oneSided_regularKernel_two_mul u hu0,
        oneSided_regularKernelPolynomial6_two_mul]
      ring
    have hLowerPolynomial :
        (3 / 500 : ℝ) * u ^ 8 ≤
          (1 / 4 : ℝ) * oneSidedSechLowerError u := by
      have hidentity :
          (1 / 4 : ℝ) * oneSidedSechLowerError u -
              (3 / 500 : ℝ) * u ^ 8 =
            u ^ 8 *
              ((61 / 116121600 : ℝ) * u ^ 6 +
                (67 / 3225600 : ℝ) * u ^ 4 +
                (197 / 322560 : ℝ) * u ^ 2 +
                (3541 / 8064000 : ℝ)) := by
        unfold oneSidedSechLowerError
        ring
      rw [← sub_nonneg, hidentity]
      positivity
    rw [hDifference]
    change (3 / 500 : ℝ) * u ^ 8 ≤
      (1 / 4 : ℝ) *
        ((1 / Real.cosh u - oneSidedSechPolynomial6 u) +
          (1 / Real.sinh u - 1 / u - oneSidedCschRegularPolynomial5 u))
    nlinarith

/-- The complete degree-six pole-free residual is globally nonpositive.
This is the one-sided fact lost by the older absolute-value envelope. -/
theorem poleFreeKernel_sub_polynomial_nonpos
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    oddLowPoleFreeKernel t - poleFreeKernelPolynomial6 t ≤ 0 := by
  let up : ℝ := yoshidaEndpointA * (2 + t)
  let um : ℝ := yoshidaEndpointA * (2 - t)
  let zp : ℝ := up / 2
  let zm : ℝ := um / 2
  have hup0 : 0 ≤ up := by
    dsimp only [up]
    exact mul_nonneg yoshidaEndpointA_pos.le (by linarith [ht.1])
  have hum0 : 0 ≤ um := by
    dsimp only [um]
    exact mul_nonneg yoshidaEndpointA_pos.le (by linarith [ht.2])
  have hupLog : up ≤ 2 * Real.log 2 := by
    dsimp only [up]
    unfold yoshidaEndpointA
    have hlog0 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
    nlinarith [ht.2]
  have humLog : um ≤ 2 * Real.log 2 := by
    dsimp only [um]
    unfold yoshidaEndpointA
    have hlog0 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
    nlinarith [ht.1]
  have hzp0 : 0 ≤ zp := by dsimp only [zp]; positivity
  have hzm0 : 0 ≤ zm := by dsimp only [zm]; positivity
  have hzp : zp < (7 / 10 : ℝ) := by
    dsimp only [zp, up]
    unfold yoshidaEndpointA
    have hlog := strict_log_two_bounds.2
    have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith [ht.2]
  have hzm : zm < (7 / 10 : ℝ) := by
    dsimp only [zm, um]
    unfold yoshidaEndpointA
    have hlog := strict_log_two_bounds.2
    have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith [ht.1]
  have hcp := (oneSided_cosh_taylor_bounds hzp0 hzp).2
  have hcm := (oneSided_cosh_taylor_bounds hzm0 hzm).2
  have hrp := oneSided_regularKernel_error_lower hup0 hupLog
  have hrm := oneSided_regularKernel_error_lower hum0 humLog
  let ecp : ℝ := Real.cosh zp - oneSidedCoshPolynomial6 zp
  let ecm : ℝ := Real.cosh zm - oneSidedCoshPolynomial6 zm
  let erp : ℝ := yoshidaRegularKernel up -
    yoshidaRegularKernelPolynomial6 up
  let erm : ℝ := yoshidaRegularKernel um -
    yoshidaRegularKernelPolynomial6 um
  have hecp : ecp ≤ (4 / 3 : ℝ) * zp ^ 8 / 40320 := by
    dsimp only [ecp]
    unfold oneSidedCoshUpper8 at hcp
    linarith
  have hecm : ecm ≤ (4 / 3 : ℝ) * zm ^ 8 / 40320 := by
    dsimp only [ecm]
    unfold oneSidedCoshUpper8 at hcm
    linarith
  have herp : (3 / 500 : ℝ) * zp ^ 8 ≤ erp := by
    simpa only [zp] using hrp
  have herm : (3 / 500 : ℝ) * zm ^ 8 ≤ erm := by
    simpa only [zm] using hrm
  have hcomponent (z ec er : ℝ)
      (hec : ec ≤ (4 / 3 : ℝ) * z ^ 8 / 40320)
      (her : (3 / 500 : ℝ) * z ^ 8 ≤ er) :
      2 * ec - er ≤ 0 := by
    have hz8 : 0 ≤ z ^ 8 := by positivity
    nlinarith
  have hinside : 2 * ecp + 2 * ecm - erp - erm ≤ 0 := by
    nlinarith [hcomponent zp ecp erp hecp herp,
      hcomponent zm ecm erm hecm herm]
  have hmodel :
      poleFreeKernelPolynomial6 t =
        yoshidaEndpointA *
          (2 * oneSidedCoshPolynomial6 zp +
            2 * oneSidedCoshPolynomial6 zm -
            yoshidaRegularKernelPolynomial6 up -
            yoshidaRegularKernelPolynomial6 um) := by
    rw [poleFreeKernelPolynomial6_expansion]
    dsimp only [up, um, zp, zm]
    unfold poleFreeCoeff0 poleFreeCoeff2 poleFreeCoeff4 poleFreeCoeff6
      oneSidedCoshPolynomial6 yoshidaRegularKernelPolynomial6
    ring
  have hidentity :
      oddLowPoleFreeKernel t - poleFreeKernelPolynomial6 t =
        yoshidaEndpointA * (2 * ecp + 2 * ecm - erp - erm) := by
    rw [hmodel]
    dsimp only [oddLowPoleFreeKernel,
      factorTwoCenteredSymmetricRegularWeight, up, um, zp, zm,
      ecp, ecm, erp, erm]
    ring
  rw [hidentity]
  exact mul_nonpos_of_nonneg_of_nonpos yoshidaEndpointA_pos.le hinside

private theorem measurable_yoshidaRegularKernel_oneSided :
    Measurable yoshidaRegularKernel := by
  unfold yoshidaRegularKernel
  apply Measurable.ite
  · simpa only [Set.setOf_eq_eq_singleton] using
      measurableSet_singleton (0 : ℝ)
  · exact measurable_const
  · exact ((Real.measurable_exp.comp (measurable_id.div_const 2)).div
      (measurable_const.mul Real.measurable_sinh)).sub
        (measurable_const.div (measurable_const.mul measurable_id))

private theorem measurable_symmetricRegularWeight_oneSided :
    Measurable factorTwoCenteredSymmetricRegularWeight := by
  unfold factorTwoCenteredSymmetricRegularWeight
  exact (((measurable_const.mul
      (Real.measurable_cosh.comp (by fun_prop))).add
        (measurable_const.mul
          (Real.measurable_cosh.comp (by fun_prop)))).sub
      (measurable_yoshidaRegularKernel_oneSided.comp (by fun_prop))).sub
        (measurable_yoshidaRegularKernel_oneSided.comp (by fun_prop))

/-- Public integrability bridge for the exact pole-free analytic error. -/
theorem intervalIntegrable_poleFreeAnalyticError
    (C : ℝ → ℝ) (hC : Continuous C) :
    IntervalIntegrable
      (fun t ↦ (oddLowPoleFreeKernel t - poleFreeKernelPolynomial6 t) * C t)
      volume 0 2 := by
  let f : ℝ → ℝ := fun t ↦
    (oddLowPoleFreeKernel t - poleFreeKernelPolynomial6 t) * C t
  let g : ℝ → ℝ := fun t ↦ (3 / 8000 : ℝ) * |C t|
  have hgIcc : IntegrableOn g (Icc (0 : ℝ) 2) volume := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact (continuous_const.mul hC.abs).continuousOn
  have hg : Integrable g (volume.restrict (Ioc (0 : ℝ) 2)) :=
    hgIcc.mono_set Ioc_subset_Icc_self
  have hfmeas : AEStronglyMeasurable f
      (volume.restrict (Ioc (0 : ℝ) 2)) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [f, oddLowPoleFreeKernel]
    exact ((measurable_const.mul measurable_symmetricRegularWeight_oneSided).sub
      continuous_poleFreeKernelPolynomial6.measurable).mul hC.measurable
  have hfg : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (0 : ℝ) 2)),
      ‖f t‖ ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hk := (abs_poleFreeKernel_sub_polynomial_lt
      (⟨ht.1.le, ht.2⟩ : t ∈ Icc (0 : ℝ) 2)).le
    dsimp only [f, g]
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hk (abs_nonneg (C t))
  have hf : Integrable f (volume.restrict (Ioc (0 : ℝ) 2)) :=
    Integrable.mono' hg hfmeas hfg
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  simpa only [f] using hf

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationOneSided
