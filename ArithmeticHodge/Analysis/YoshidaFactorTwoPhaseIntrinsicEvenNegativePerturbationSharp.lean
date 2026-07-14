import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicLowControlStep23EvenSlopeStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp

noncomputable section

open CenteredEndpointCorrelation
open YoshidaConstantBounds
open YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseOddAffineKernelEstimate
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowControlStep23EvenSlopeStructural
open YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseSymmetricCarleman
open YoshidaRegularKernelBound

/-!
# A sharp rational lower Gram for the negative even perturbation

The uniform quadratic enclosure loses `1 / 250` in the constant direction.
Here the already-global degree-six Taylor model is retained through the
correlation integral.  Its polynomial moments are exact; only the single
global analytic remainder is charged by energy.  No interval subdivision or
sampled certificate occurs.
-/

/-! ## The global Taylor model -/

private def wideCoshPolynomial6 (u : ℝ) : ℝ :=
  1 + u ^ 2 / 2 + u ^ 4 / 24 + u ^ 6 / 720

private def wideCoshUpper8 (u : ℝ) : ℝ :=
  wideCoshPolynomial6 u + (4 / 3 : ℝ) * u ^ 8 / 40320

private def wideSinhDivPolynomial6 (u : ℝ) : ℝ :=
  1 + u ^ 2 / 6 + u ^ 4 / 120 + u ^ 6 / 5040

private def wideSinhDivUpper8 (u : ℝ) : ℝ :=
  wideSinhDivPolynomial6 u + (4 / 3 : ℝ) * u ^ 8 / 362880

private def wideSechPolynomial6 (u : ℝ) : ℝ :=
  1 - u ^ 2 / 2 + 5 * u ^ 4 / 24 - 61 * u ^ 6 / 720

private def wideCschRegularPolynomial5 (u : ℝ) : ℝ :=
  -u / 6 + 7 * u ^ 3 / 360 - 31 * u ^ 5 / 15120

private def wideCschMultiplier6 (u : ℝ) : ℝ :=
  1 + u * wideCschRegularPolynomial5 u

private def wideSechError (u : ℝ) : ℝ :=
  u ^ 8 * (61 * u ^ 4 + 1680 * u ^ 2 + 17820) / 518400

private def wideCschError (u : ℝ) : ℝ :=
  u ^ 7 * (31 * u ^ 4 + 1008 * u ^ 2 + 16212) / 76204800

private theorem cosh_lt_four_thirds
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

private theorem wide_cosh_taylor_bounds
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u < (7 / 10 : ℝ)) :
    wideCoshPolynomial6 u ≤ Real.cosh u ∧
      Real.cosh u ≤ wideCoshUpper8 u := by
  rcases eq_or_lt_of_le hu0 with rfl | hupos
  · norm_num [wideCoshPolynomial6, wideCoshUpper8]
  · rcases taylor_mean_remainder_lagrange_iteratedDeriv
        (f := Real.cosh) (x₀ := 0) (x := u) (n := 7) hupos
        Real.contDiff_cosh.contDiffOn with ⟨w, hw, hTaylor⟩
    have hTaylorEval :
        taylorWithinEval Real.cosh 7 (Icc 0 u) 0 u =
          wideCoshPolynomial6 u := by
      have hder (n : ℕ) :
          iteratedDerivWithin n Real.cosh (Icc 0 u) 0 =
            iteratedDeriv n Real.cosh 0 :=
        Real.iteratedDerivWithin_cosh_Icc n hupos ⟨le_rfl, hu0⟩
      rw [taylor_within_apply]
      simp [hder, Finset.sum_range_succ, wideCoshPolynomial6]
      ring
    rw [hTaylorEval] at hTaylor
    norm_num [Real.iteratedDeriv_even_cosh] at hTaylor
    have hwBound : Real.cosh w < (4 / 3 : ℝ) :=
      cosh_lt_four_thirds hw.1.le (hw.2.trans hu)
    have hrem0 : 0 ≤ Real.cosh w * u ^ 8 / 40320 := by positivity
    have hremUpper :
        Real.cosh w * u ^ 8 / 40320 ≤
          (4 / 3 : ℝ) * u ^ 8 / 40320 := by
      gcongr
    constructor
    · linarith
    · unfold wideCoshUpper8
      linarith

private theorem wide_sinh_div_taylor_bounds
    {u : ℝ} (hu0 : 0 < u) (hu : u < (7 / 10 : ℝ)) :
    wideSinhDivPolynomial6 u ≤ Real.sinh u / u ∧
      Real.sinh u / u ≤ wideSinhDivUpper8 u := by
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
      Real.sinh u / u - wideSinhDivPolynomial6 u =
        Real.cosh w * u ^ 8 / 362880 := by
    unfold wideSinhDivPolynomial6
    rw [show Real.sinh u / u -
          (1 + u ^ 2 / 6 + u ^ 4 / 120 + u ^ 6 / 5040) =
        (Real.sinh u -
          (u + u ^ 3 / 6 + u ^ 5 / 120 + u ^ 7 / 5040)) / u by
      field_simp [hu0.ne'],
      hTaylor]
    field_simp [hu0.ne']
  have hwBound : Real.cosh w < (4 / 3 : ℝ) :=
    cosh_lt_four_thirds hw.1.le (hw.2.trans hu)
  have hrem0 : 0 ≤ Real.cosh w * u ^ 8 / 362880 := by positivity
  have hremUpper :
      Real.cosh w * u ^ 8 / 362880 ≤
        (4 / 3 : ℝ) * u ^ 8 / 362880 := by
    gcongr
  constructor
  · linarith
  · unfold wideSinhDivUpper8
    linarith

private theorem wide_sech_envelope
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u < (7 / 10 : ℝ)) :
    0 ≤ 1 / Real.cosh u - wideSechPolynomial6 u ∧
      1 / Real.cosh u - wideSechPolynomial6 u ≤ wideSechError u := by
  have hTaylor := wide_cosh_taylor_bounds hu0 hu
  have huSq : u ^ 2 < (1 / 2 : ℝ) := by
    have h := pow_lt_pow_left₀ hu hu0 (by norm_num : (2 : ℕ) ≠ 0)
    norm_num at h ⊢
    linarith
  have huSix : u ^ 6 < (1 / 2 : ℝ) ^ 3 := by
    have h := pow_lt_pow_left₀ huSq (sq_nonneg u) (by norm_num : (3 : ℕ) ≠ 0)
    simpa only [show (u ^ 2) ^ 3 = u ^ 6 by ring] using h
  have hP0 : 0 ≤ wideSechPolynomial6 u := by
    unfold wideSechPolynomial6
    have huFour0 : 0 ≤ u ^ 4 := by positivity
    nlinarith
  have hFactorUpper :
      wideSechPolynomial6 u * wideCoshUpper8 u - 1 =
        -(u ^ 8 *
          (61 * u ^ 6 + 2412 * u ^ 4 + 70920 * u ^ 2 + 747720)) /
            21772800 := by
    unfold wideSechPolynomial6 wideCoshUpper8 wideCoshPolynomial6
    ring
  have hPCup : wideSechPolynomial6 u * wideCoshUpper8 u ≤ 1 := by
    rw [← sub_nonpos, hFactorUpper]
    have hnonneg : 0 ≤ u ^ 8 *
        (61 * u ^ 6 + 2412 * u ^ 4 + 70920 * u ^ 2 + 747720) := by
      positivity
    nlinarith
  have hPCosh : wideSechPolynomial6 u * Real.cosh u ≤ 1 :=
    (mul_le_mul_of_nonneg_left hTaylor.2 hP0).trans hPCup
  have hLower : 0 ≤ 1 / Real.cosh u - wideSechPolynomial6 u := by
    rw [sub_nonneg, le_div_iff₀ (Real.cosh_pos u)]
    simpa only [one_mul] using hPCosh
  constructor
  · exact hLower
  · have hIdentity :
        1 / Real.cosh u - wideSechPolynomial6 u =
          (1 - wideSechPolynomial6 u * Real.cosh u) / Real.cosh u := by
      field_simp [(Real.cosh_pos u).ne']
    have hNumerator0 :
        0 ≤ 1 - wideSechPolynomial6 u * Real.cosh u := by
      linarith
    have hDivide :
        (1 - wideSechPolynomial6 u * Real.cosh u) / Real.cosh u ≤
          1 - wideSechPolynomial6 u * Real.cosh u :=
      div_le_self hNumerator0 (Real.one_le_cosh u)
    have hPLower :
        wideSechPolynomial6 u * wideCoshPolynomial6 u ≤
          wideSechPolynomial6 u * Real.cosh u :=
      mul_le_mul_of_nonneg_left hTaylor.1 hP0
    have hErrorIdentity :
        1 - wideSechPolynomial6 u * wideCoshPolynomial6 u =
          wideSechError u := by
      unfold wideSechPolynomial6 wideCoshPolynomial6 wideSechError
      ring
    rw [hIdentity]
    calc
      _ ≤ 1 - wideSechPolynomial6 u * Real.cosh u := hDivide
      _ ≤ 1 - wideSechPolynomial6 u * wideCoshPolynomial6 u := by
        nlinarith
      _ = wideSechError u := hErrorIdentity

private theorem wide_csch_envelope
    {u : ℝ} (hu0 : 0 < u) (hu : u < (7 / 10 : ℝ)) :
    0 ≤ 1 / Real.sinh u - 1 / u - wideCschRegularPolynomial5 u ∧
      1 / Real.sinh u - 1 / u - wideCschRegularPolynomial5 u ≤
        wideCschError u := by
  let A : ℝ := Real.sinh u / u
  have hTaylorRaw := wide_sinh_div_taylor_bounds hu0 hu
  have hTaylor :
      wideSinhDivPolynomial6 u ≤ A ∧ A ≤ wideSinhDivUpper8 u :=
    hTaylorRaw
  have hA1 : (1 : ℝ) ≤ A := by
    dsimp only [A]
    rw [le_div_iff₀ hu0]
    simpa using (Real.self_le_sinh_iff.mpr hu0.le)
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hA1
  have huSq : u ^ 2 < (1 / 2 : ℝ) := by
    have h := pow_lt_pow_left₀ hu hu0.le (by norm_num : (2 : ℕ) ≠ 0)
    norm_num at h ⊢
    linarith
  have huSix : u ^ 6 < (1 / 2 : ℝ) ^ 3 := by
    have h := pow_lt_pow_left₀ huSq (sq_nonneg u) (by norm_num : (3 : ℕ) ≠ 0)
    simpa only [show (u ^ 2) ^ 3 = u ^ 6 by ring] using h
  have hQ0 : 0 ≤ wideCschMultiplier6 u := by
    unfold wideCschMultiplier6 wideCschRegularPolynomial5
    have huFour0 : 0 ≤ u ^ 4 := by positivity
    nlinarith
  have hFactorUpper :
      wideCschMultiplier6 u * wideSinhDivUpper8 u - 1 =
        -(u ^ 8 *
          (31 * u ^ 6 + 1380 * u ^ 4 + 56952 * u ^ 2 + 860328)) /
            4115059200 := by
    unfold wideCschMultiplier6 wideCschRegularPolynomial5
      wideSinhDivUpper8 wideSinhDivPolynomial6
    ring
  have hQAup : wideCschMultiplier6 u * wideSinhDivUpper8 u ≤ 1 := by
    rw [← sub_nonpos, hFactorUpper]
    have hnonneg : 0 ≤ u ^ 8 *
        (31 * u ^ 6 + 1380 * u ^ 4 + 56952 * u ^ 2 + 860328) := by
      positivity
    nlinarith
  have hQA : wideCschMultiplier6 u * A ≤ 1 :=
    (mul_le_mul_of_nonneg_left hTaylor.2 hQ0).trans hQAup
  have hQleInv : wideCschMultiplier6 u ≤ 1 / A := by
    rw [le_div_iff₀ hApos]
    simpa only [one_mul] using hQA
  have hSinhPos : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu0
  have hMainIdentity :
      1 / Real.sinh u - 1 / u - wideCschRegularPolynomial5 u =
        (1 / A - wideCschMultiplier6 u) / u := by
    dsimp only [A]
    unfold wideCschMultiplier6
    field_simp [hu0.ne', hSinhPos.ne']
    ring
  have hLower :
      0 ≤ 1 / Real.sinh u - 1 / u - wideCschRegularPolynomial5 u := by
    rw [hMainIdentity]
    exact div_nonneg (sub_nonneg.mpr hQleInv) hu0.le
  constructor
  · exact hLower
  · have hInvIdentity :
        1 / A - wideCschMultiplier6 u =
          (1 - wideCschMultiplier6 u * A) / A := by
      field_simp [hApos.ne']
    have hNumerator0 : 0 ≤ 1 - wideCschMultiplier6 u * A := by
      linarith
    have hDivideA :
        (1 - wideCschMultiplier6 u * A) / A ≤
          1 - wideCschMultiplier6 u * A :=
      div_le_self hNumerator0 hA1
    have hQLower :
        wideCschMultiplier6 u * wideSinhDivPolynomial6 u ≤
          wideCschMultiplier6 u * A :=
      mul_le_mul_of_nonneg_left hTaylor.1 hQ0
    have hErrorIdentity :
        1 - wideCschMultiplier6 u * wideSinhDivPolynomial6 u =
          u * wideCschError u := by
      unfold wideCschMultiplier6 wideCschRegularPolynomial5
        wideSinhDivPolynomial6 wideCschError
      ring
    have hInner :
        1 / A - wideCschMultiplier6 u ≤ u * wideCschError u := by
      rw [hInvIdentity]
      calc
        _ ≤ 1 - wideCschMultiplier6 u * A := hDivideA
        _ ≤ 1 - wideCschMultiplier6 u * wideSinhDivPolynomial6 u := by
          linarith
        _ = u * wideCschError u := hErrorIdentity
    rw [hMainIdentity]
    rw [div_le_iff₀ hu0]
    simpa only [div_mul_cancel₀ _ hu0.ne', mul_comm] using hInner

private theorem yoshidaRegularKernel_two_mul_wide (u : ℝ) (hu : 0 < u) :
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

private theorem yoshidaRegularKernelPolynomial6_two_mul_wide (u : ℝ) :
    yoshidaRegularKernelPolynomial6 (2 * u) =
      (1 / 4 : ℝ) *
        (wideSechPolynomial6 u + wideCschRegularPolynomial5 u) := by
  unfold yoshidaRegularKernelPolynomial6 wideSechPolynomial6
    wideCschRegularPolynomial5
  ring

private theorem yoshidaRegularKernelPolynomial6_wide_envelope
    {t : ℝ} (ht0 : 0 ≤ t) (htlog : t ≤ 2 * Real.log 2) :
    0 ≤ yoshidaRegularKernel t - yoshidaRegularKernelPolynomial6 t ∧
      yoshidaRegularKernel t - yoshidaRegularKernelPolynomial6 t <
        (1 / 1900 : ℝ) := by
  rcases eq_or_lt_of_le ht0 with rfl | htpos
  · constructor <;>
      norm_num [yoshidaRegularKernel, yoshidaRegularKernelPolynomial6]
  · let u : ℝ := t / 2
    have hu0 : 0 < u := by
      dsimp only [u]
      linarith
    have hu : u < (7 / 10 : ℝ) := by
      dsimp only [u]
      have hlog := strict_log_two_bounds.2
      linarith
    have hSech := wide_sech_envelope hu0.le hu
    have hCsch := wide_csch_envelope hu0 hu
    have htEq : t = 2 * u := by
      dsimp only [u]
      ring
    have hDifference :
        yoshidaRegularKernel t - yoshidaRegularKernelPolynomial6 t =
          (1 / 4 : ℝ) *
            ((1 / Real.cosh u - wideSechPolynomial6 u) +
              (1 / Real.sinh u - 1 / u -
                wideCschRegularPolynomial5 u)) := by
      rw [htEq, yoshidaRegularKernel_two_mul_wide u hu0,
        yoshidaRegularKernelPolynomial6_two_mul_wide]
      ring
    have hError :
        yoshidaRegularKernel t - yoshidaRegularKernelPolynomial6 t ≤
          (1 / 4 : ℝ) * (wideSechError u + wideCschError u) := by
      rw [hDifference]
      nlinarith
    have hSechStrict :
        wideSechError u < wideSechError (7 / 10 : ℝ) := by
      unfold wideSechError
      gcongr
    have hCschStrict :
        wideCschError u < wideCschError (7 / 10 : ℝ) := by
      unfold wideCschError
      gcongr
    have hEndpoint :
        (1 / 4 : ℝ) *
            (wideSechError (7 / 10 : ℝ) +
              wideCschError (7 / 10 : ℝ)) <
          (1 / 1900 : ℝ) := by
      norm_num [wideSechError, wideCschError]
    constructor
    · rw [hDifference]
      nlinarith [hSech.1, hCsch.1]
    · exact hError.trans_lt <| by
        have :
            (1 / 4 : ℝ) * (wideSechError u + wideCschError u) <
              (1 / 4 : ℝ) *
                (wideSechError (7 / 10 : ℝ) +
                  wideCschError (7 / 10 : ℝ)) := by
          nlinarith
        exact this.trans hEndpoint

/-- The global even degree-six model for the pole-free symmetric kernel. -/
def poleFreeKernelPolynomial6 (t : ℝ) : ℝ :=
  let up := yoshidaEndpointA * (2 + t)
  let um := yoshidaEndpointA * (2 - t)
  yoshidaEndpointA *
    (2 * wideCoshPolynomial6 (up / 2) +
      2 * wideCoshPolynomial6 (um / 2) -
      yoshidaRegularKernelPolynomial6 up -
      yoshidaRegularKernelPolynomial6 um)

/-- The global analytic remainder of the pole-free degree-six model. -/
theorem abs_poleFreeKernel_sub_polynomial_lt
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    |oddLowPoleFreeKernel t - poleFreeKernelPolynomial6 t| <
      (3 / 8000 : ℝ) := by
  let up : ℝ := yoshidaEndpointA * (2 + t)
  let um : ℝ := yoshidaEndpointA * (2 - t)
  let zp : ℝ := up / 2
  let zm : ℝ := um / 2
  let E : ℝ := (4 / 3 : ℝ) * (7 / 10 : ℝ) ^ 8 / 40320
  have hAupper : yoshidaEndpointA < (347 / 1000 : ℝ) := by
    unfold yoshidaEndpointA
    linarith [strict_log_two_bounds.2]
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
  have hzp0 : 0 ≤ zp := by
    dsimp only [zp]
    positivity
  have hzm0 : 0 ≤ zm := by
    dsimp only [zm]
    positivity
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
  have hcp := wide_cosh_taylor_bounds hzp0 hzp
  have hcm := wide_cosh_taylor_bounds hzm0 hzm
  have hrp := yoshidaRegularKernelPolynomial6_wide_envelope hup0 hupLog
  have hrm := yoshidaRegularKernelPolynomial6_wide_envelope hum0 humLog
  let ecp : ℝ := Real.cosh zp - wideCoshPolynomial6 zp
  let ecm : ℝ := Real.cosh zm - wideCoshPolynomial6 zm
  let erp : ℝ := yoshidaRegularKernel up -
    yoshidaRegularKernelPolynomial6 up
  let erm : ℝ := yoshidaRegularKernel um -
    yoshidaRegularKernelPolynomial6 um
  have hE0 : 0 ≤ E := by
    dsimp only [E]
    positivity
  have hecp0 : 0 ≤ ecp := by
    dsimp only [ecp]
    linarith [hcp.1]
  have hecm0 : 0 ≤ ecm := by
    dsimp only [ecm]
    linarith [hcm.1]
  have hecpE : ecp ≤ E := by
    have hpow : zp ^ 8 ≤ (7 / 10 : ℝ) ^ 8 :=
      pow_le_pow_left₀ hzp0 hzp.le 8
    dsimp only [ecp, E]
    unfold wideCoshUpper8 at hcp
    linarith
  have hecmE : ecm ≤ E := by
    have hpow : zm ^ 8 ≤ (7 / 10 : ℝ) ^ 8 :=
      pow_le_pow_left₀ hzm0 hzm.le 8
    dsimp only [ecm, E]
    unfold wideCoshUpper8 at hcm
    linarith
  have herp0 : 0 ≤ erp := by
    simpa only [erp] using hrp.1
  have herm0 : 0 ≤ erm := by
    simpa only [erm] using hrm.1
  have herp : erp ≤ (1 / 1900 : ℝ) := hrp.2.le
  have herm : erm ≤ (1 / 1900 : ℝ) := hrm.2.le
  have hdiff :
      oddLowPoleFreeKernel t - poleFreeKernelPolynomial6 t =
        yoshidaEndpointA * (2 * ecp + 2 * ecm - erp - erm) := by
    dsimp only [oddLowPoleFreeKernel, poleFreeKernelPolynomial6,
      factorTwoCenteredSymmetricRegularWeight, up, um, zp, zm,
      ecp, ecm, erp, erm]
    ring
  have hinside :
      |2 * ecp + 2 * ecm - erp - erm| ≤
        4 * E + 2 / 1900 := by
    rw [abs_le]
    constructor
    · calc
        -(4 * E + 2 / 1900) ≤ -(2 / 1900 : ℝ) := by
          linarith
        _ ≤ 2 * ecp + 2 * ecm - erp - erm := by
          linarith
    · calc
        2 * ecp + 2 * ecm - erp - erm ≤ 4 * E := by
          linarith
        _ ≤ 4 * E + 2 / 1900 := by norm_num
  have hscaled :
      |oddLowPoleFreeKernel t - poleFreeKernelPolynomial6 t| ≤
        yoshidaEndpointA * (4 * E + 2 / 1900) := by
    rw [hdiff, abs_mul, abs_of_pos yoshidaEndpointA_pos]
    exact mul_le_mul_of_nonneg_left hinside yoshidaEndpointA_pos.le
  have hrat :
      (347 / 1000 : ℝ) *
          (4 * ((4 / 3 : ℝ) * (7 / 10 : ℝ) ^ 8 / 40320) +
            2 / 1900) <
        (3 / 8000 : ℝ) := by
    norm_num
  have hfactor0 : 0 ≤ 4 * E + 2 / 1900 := by positivity
  calc
    |oddLowPoleFreeKernel t - poleFreeKernelPolynomial6 t| ≤
        yoshidaEndpointA * (4 * E + 2 / 1900) := hscaled
    _ < (347 / 1000 : ℝ) * (4 * E + 2 / 1900) :=
      mul_lt_mul_of_pos_right hAupper (by positivity)
    _ < (3 / 8000 : ℝ) := by
      simpa only [E] using hrat

def poleFreeCoeff0 (a : ℝ) : ℝ :=
  (7 / 2 : ℝ) * a + a ^ 2 / 12 + (9 / 4 : ℝ) * a ^ 3 -
    (7 / 720 : ℝ) * a ^ 4 + a ^ 5 / 16 +
      (31 / 30240 : ℝ) * a ^ 6 + (23 / 480 : ℝ) * a ^ 7

def poleFreeCoeff2 (a : ℝ) : ℝ :=
  (9 / 16 : ℝ) * a ^ 3 - (7 / 960 : ℝ) * a ^ 4 +
    (3 / 32 : ℝ) * a ^ 5 + (31 / 12096 : ℝ) * a ^ 6 +
      (23 / 128 : ℝ) * a ^ 7

def poleFreeCoeff4 (a : ℝ) : ℝ :=
  a ^ 5 / 256 + (31 / 96768 : ℝ) * a ^ 6 +
    (23 / 512 : ℝ) * a ^ 7

def poleFreeCoeff6 (a : ℝ) : ℝ :=
  (23 / 30720 : ℝ) * a ^ 7

theorem poleFreeKernelPolynomial6_expansion (t : ℝ) :
    poleFreeKernelPolynomial6 t =
      poleFreeCoeff0 yoshidaEndpointA +
        poleFreeCoeff2 yoshidaEndpointA * t ^ 2 +
        poleFreeCoeff4 yoshidaEndpointA * t ^ 4 +
        poleFreeCoeff6 yoshidaEndpointA * t ^ 6 := by
  unfold poleFreeKernelPolynomial6 wideCoshPolynomial6
    yoshidaRegularKernelPolynomial6 poleFreeCoeff0 poleFreeCoeff2
    poleFreeCoeff4 poleFreeCoeff6
  ring

theorem poleFree_coefficient_bounds :
    (21 / 100000 : ℝ) ≤ poleFreeCoeff0 yoshidaEndpointA - 79 / 60 ∧
      poleFreeCoeff0 yoshidaEndpointA - 79 / 60 ≤
        (22 / 100000 : ℝ) ∧
      (-11 / 100000 : ℝ) ≤
        poleFreeCoeff2 yoshidaEndpointA - 3 / 125 ∧
      poleFreeCoeff2 yoshidaEndpointA - 3 / 125 ≤
        (-1 / 10000 : ℝ) ∧
      (47 / 1000000 : ℝ) ≤ poleFreeCoeff4 yoshidaEndpointA ∧
      poleFreeCoeff4 yoshidaEndpointA ≤ (48 / 1000000 : ℝ) ∧
      0 ≤ poleFreeCoeff6 yoshidaEndpointA ∧
      poleFreeCoeff6 yoshidaEndpointA ≤ (5 / 10000000 : ℝ) := by
  let L : ℝ := 3465735 / 10000000
  let U : ℝ := 3465737 / 10000000
  have hAL : L ≤ yoshidaEndpointA := by
    dsimp only [L]
    unfold yoshidaEndpointA
    linarith [strict_log_two_fine_bounds.1]
  have hAU : yoshidaEndpointA ≤ U := by
    dsimp only [U]
    unfold yoshidaEndpointA
    linarith [strict_log_two_fine_bounds.2]
  have hL0 : 0 ≤ L := by norm_num [L]
  have hA0 : 0 ≤ yoshidaEndpointA := yoshidaEndpointA_pos.le
  have hLpow (n : ℕ) : L ^ n ≤ yoshidaEndpointA ^ n :=
    pow_le_pow_left₀ hL0 hAL n
  have hUpow (n : ℕ) : yoshidaEndpointA ^ n ≤ U ^ n :=
    pow_le_pow_left₀ hA0 hAU n
  have hc0LowerRat :
      (21 / 100000 : ℝ) <
        (7 / 2 : ℝ) * L + L ^ 2 / 12 + (9 / 4 : ℝ) * L ^ 3 -
          (7 / 720 : ℝ) * U ^ 4 + L ^ 5 / 16 +
          (31 / 30240 : ℝ) * L ^ 6 + (23 / 480 : ℝ) * L ^ 7 -
          79 / 60 := by
    norm_num [L, U]
  have hc0UpperRat :
      (7 / 2 : ℝ) * U + U ^ 2 / 12 + (9 / 4 : ℝ) * U ^ 3 -
          (7 / 720 : ℝ) * L ^ 4 + U ^ 5 / 16 +
          (31 / 30240 : ℝ) * U ^ 6 + (23 / 480 : ℝ) * U ^ 7 -
          79 / 60 <
        (22 / 100000 : ℝ) := by
    norm_num [L, U]
  have hc2LowerRat :
      (-11 / 100000 : ℝ) <
        (9 / 16 : ℝ) * L ^ 3 - (7 / 960 : ℝ) * U ^ 4 +
          (3 / 32 : ℝ) * L ^ 5 + (31 / 12096 : ℝ) * L ^ 6 +
          (23 / 128 : ℝ) * L ^ 7 - 3 / 125 := by
    norm_num [L, U]
  have hc2UpperRat :
      (9 / 16 : ℝ) * U ^ 3 - (7 / 960 : ℝ) * L ^ 4 +
          (3 / 32 : ℝ) * U ^ 5 + (31 / 12096 : ℝ) * U ^ 6 +
          (23 / 128 : ℝ) * U ^ 7 - 3 / 125 <
        (-1 / 10000 : ℝ) := by
    norm_num [L, U]
  have hc4LowerRat :
      (47 / 1000000 : ℝ) <
        L ^ 5 / 256 + (31 / 96768 : ℝ) * L ^ 6 +
          (23 / 512 : ℝ) * L ^ 7 := by
    norm_num [L]
  have hc4UpperRat :
      U ^ 5 / 256 + (31 / 96768 : ℝ) * U ^ 6 +
          (23 / 512 : ℝ) * U ^ 7 <
        (48 / 1000000 : ℝ) := by
    norm_num [U]
  have hc6UpperRat :
      (23 / 30720 : ℝ) * U ^ 7 < (5 / 10000000 : ℝ) := by
    norm_num [U]
  unfold poleFreeCoeff0 poleFreeCoeff2 poleFreeCoeff4 poleFreeCoeff6
  constructor
  · calc
      (21 / 100000 : ℝ) ≤
          (7 / 2 : ℝ) * L + L ^ 2 / 12 + (9 / 4 : ℝ) * L ^ 3 -
            (7 / 720 : ℝ) * U ^ 4 + L ^ 5 / 16 +
            (31 / 30240 : ℝ) * L ^ 6 + (23 / 480 : ℝ) * L ^ 7 -
            79 / 60 := hc0LowerRat.le
      _ ≤ (7 / 2 : ℝ) * yoshidaEndpointA +
          yoshidaEndpointA ^ 2 / 12 +
          (9 / 4 : ℝ) * yoshidaEndpointA ^ 3 -
          (7 / 720 : ℝ) * yoshidaEndpointA ^ 4 +
          yoshidaEndpointA ^ 5 / 16 +
          (31 / 30240 : ℝ) * yoshidaEndpointA ^ 6 +
          (23 / 480 : ℝ) * yoshidaEndpointA ^ 7 - 79 / 60 := by
        gcongr
  constructor
  · calc
      (7 / 2 : ℝ) * yoshidaEndpointA + yoshidaEndpointA ^ 2 / 12 +
          (9 / 4 : ℝ) * yoshidaEndpointA ^ 3 -
          (7 / 720 : ℝ) * yoshidaEndpointA ^ 4 +
          yoshidaEndpointA ^ 5 / 16 +
          (31 / 30240 : ℝ) * yoshidaEndpointA ^ 6 +
          (23 / 480 : ℝ) * yoshidaEndpointA ^ 7 - 79 / 60 ≤
        (7 / 2 : ℝ) * U + U ^ 2 / 12 + (9 / 4 : ℝ) * U ^ 3 -
          (7 / 720 : ℝ) * L ^ 4 + U ^ 5 / 16 +
          (31 / 30240 : ℝ) * U ^ 6 + (23 / 480 : ℝ) * U ^ 7 -
          79 / 60 := by
        gcongr
      _ ≤ (22 / 100000 : ℝ) := hc0UpperRat.le
  constructor
  · calc
      (-11 / 100000 : ℝ) ≤
          (9 / 16 : ℝ) * L ^ 3 - (7 / 960 : ℝ) * U ^ 4 +
            (3 / 32 : ℝ) * L ^ 5 + (31 / 12096 : ℝ) * L ^ 6 +
            (23 / 128 : ℝ) * L ^ 7 - 3 / 125 := hc2LowerRat.le
      _ ≤ (9 / 16 : ℝ) * yoshidaEndpointA ^ 3 -
          (7 / 960 : ℝ) * yoshidaEndpointA ^ 4 +
          (3 / 32 : ℝ) * yoshidaEndpointA ^ 5 +
          (31 / 12096 : ℝ) * yoshidaEndpointA ^ 6 +
          (23 / 128 : ℝ) * yoshidaEndpointA ^ 7 - 3 / 125 := by
        gcongr
  constructor
  · calc
      (9 / 16 : ℝ) * yoshidaEndpointA ^ 3 -
          (7 / 960 : ℝ) * yoshidaEndpointA ^ 4 +
          (3 / 32 : ℝ) * yoshidaEndpointA ^ 5 +
          (31 / 12096 : ℝ) * yoshidaEndpointA ^ 6 +
          (23 / 128 : ℝ) * yoshidaEndpointA ^ 7 - 3 / 125 ≤
        (9 / 16 : ℝ) * U ^ 3 - (7 / 960 : ℝ) * L ^ 4 +
          (3 / 32 : ℝ) * U ^ 5 + (31 / 12096 : ℝ) * U ^ 6 +
          (23 / 128 : ℝ) * U ^ 7 - 3 / 125 := by
        gcongr
      _ ≤ (-1 / 10000 : ℝ) := hc2UpperRat.le
  constructor
  · calc
      (47 / 1000000 : ℝ) ≤
          L ^ 5 / 256 + (31 / 96768 : ℝ) * L ^ 6 +
            (23 / 512 : ℝ) * L ^ 7 := hc4LowerRat.le
      _ ≤ yoshidaEndpointA ^ 5 / 256 +
          (31 / 96768 : ℝ) * yoshidaEndpointA ^ 6 +
          (23 / 512 : ℝ) * yoshidaEndpointA ^ 7 := by
        gcongr
  constructor
  · calc
      yoshidaEndpointA ^ 5 / 256 +
          (31 / 96768 : ℝ) * yoshidaEndpointA ^ 6 +
          (23 / 512 : ℝ) * yoshidaEndpointA ^ 7 ≤
        U ^ 5 / 256 + (31 / 96768 : ℝ) * U ^ 6 +
          (23 / 512 : ℝ) * U ^ 7 := by
        gcongr
      _ ≤ (48 / 1000000 : ℝ) := hc4UpperRat.le
  constructor
  · positivity
  · calc
      (23 / 30720 : ℝ) * yoshidaEndpointA ^ 7 ≤
          (23 / 30720 : ℝ) * U ^ 7 := by
        gcongr
      _ ≤ (5 / 10000000 : ℝ) := hc6UpperRat.le

private theorem integral_polynomial_eleven
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ l r : ℝ) :
    (∫ x : ℝ in l..r,
      a₀ * x ^ 0 + (a₁ * x ^ 1 + (a₂ * x ^ 2 +
        (a₃ * x ^ 3 + (a₄ * x ^ 4 + (a₅ * x ^ 5 +
          (a₆ * x ^ 6 + (a₇ * x ^ 7 + (a₈ * x ^ 8 +
            (a₉ * x ^ 9 + (a₁₀ * x ^ 10 + a₁₁ * x ^ 11))))))))))) =
      a₀ * (r - l) + a₁ * (r ^ 2 - l ^ 2) / 2 +
        a₂ * (r ^ 3 - l ^ 3) / 3 + a₃ * (r ^ 4 - l ^ 4) / 4 +
        a₄ * (r ^ 5 - l ^ 5) / 5 + a₅ * (r ^ 6 - l ^ 6) / 6 +
        a₆ * (r ^ 7 - l ^ 7) / 7 + a₇ * (r ^ 8 - l ^ 8) / 8 +
        a₈ * (r ^ 9 - l ^ 9) / 9 + a₉ * (r ^ 10 - l ^ 10) / 10 +
        a₁₀ * (r ^ 11 - l ^ 11) / 11 +
        a₁₁ * (r ^ 12 - l ^ 12) / 12 := by
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) l r)
    (Continuous.intervalIntegrable (by fun_prop) l r)]
  repeat rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

private theorem monomial_evenCorrelation00_moments :
    (∫ t : ℝ in 0..2, evenStructuralCorrelation00 t) = 2 ∧
      (∫ t : ℝ in 0..2, t ^ 2 * evenStructuralCorrelation00 t) = 4 / 3 ∧
      (∫ t : ℝ in 0..2, t ^ 4 * evenStructuralCorrelation00 t) = 32 / 15 ∧
      (∫ t : ℝ in 0..2, t ^ 6 * evenStructuralCorrelation00 t) = 32 / 7 := by
  constructor
  · rw [show (fun t : ℝ ↦ evenStructuralCorrelation00 t) =
        fun t ↦ (2 : ℝ) * t ^ 0 + ((-1 : ℝ) * t ^ 1 +
          (0 * t ^ 2 + (0 * t ^ 3 + (0 * t ^ 4 + (0 * t ^ 5 +
            (0 * t ^ 6 + (0 * t ^ 7 + (0 * t ^ 8 + (0 * t ^ 9 +
              (0 * t ^ 10 + 0 * t ^ 11)))))))))) by
        funext t
        unfold evenStructuralCorrelation00
        ring,
      integral_polynomial_eleven]
    norm_num
  · constructor
    · rw [show (fun t : ℝ ↦ t ^ 2 * evenStructuralCorrelation00 t) =
          fun t ↦ 0 * t ^ 0 + (0 * t ^ 1 + ((2 : ℝ) * t ^ 2 +
            ((-1 : ℝ) * t ^ 3 + (0 * t ^ 4 + (0 * t ^ 5 +
              (0 * t ^ 6 + (0 * t ^ 7 + (0 * t ^ 8 + (0 * t ^ 9 +
                (0 * t ^ 10 + 0 * t ^ 11)))))))))) by
          funext t
          unfold evenStructuralCorrelation00
          ring,
        integral_polynomial_eleven]
      norm_num
    · constructor
      · rw [show (fun t : ℝ ↦ t ^ 4 * evenStructuralCorrelation00 t) =
            fun t ↦ 0 * t ^ 0 + (0 * t ^ 1 + (0 * t ^ 2 +
              (0 * t ^ 3 + ((2 : ℝ) * t ^ 4 + ((-1 : ℝ) * t ^ 5 +
                (0 * t ^ 6 + (0 * t ^ 7 + (0 * t ^ 8 + (0 * t ^ 9 +
                  (0 * t ^ 10 + 0 * t ^ 11)))))))))) by
            funext t
            unfold evenStructuralCorrelation00
            ring,
          integral_polynomial_eleven]
        norm_num
      · rw [show (fun t : ℝ ↦ t ^ 6 * evenStructuralCorrelation00 t) =
            fun t ↦ 0 * t ^ 0 + (0 * t ^ 1 + (0 * t ^ 2 +
              (0 * t ^ 3 + (0 * t ^ 4 + (0 * t ^ 5 +
                ((2 : ℝ) * t ^ 6 + ((-1 : ℝ) * t ^ 7 +
                  (0 * t ^ 8 + (0 * t ^ 9 +
                    (0 * t ^ 10 + 0 * t ^ 11)))))))))) by
            funext t
            unfold evenStructuralCorrelation00
            ring,
          integral_polynomial_eleven]
        norm_num

def polynomialD0 : ℝ :=
  poleFreeCoeff0 yoshidaEndpointA - 79 / 60

def polynomialD2 : ℝ :=
  poleFreeCoeff2 yoshidaEndpointA - 3 / 125

def polynomialD4 : ℝ := poleFreeCoeff4 yoshidaEndpointA

def polynomialD6 : ℝ := poleFreeCoeff6 yoshidaEndpointA

def poleFreePolynomialDifference (t : ℝ) : ℝ :=
  poleFreeKernelPolynomial6 t - evenStructuralRegularQuadratic t

private def polynomialMoment00 : ℝ :=
  2 * polynomialD0 + (4 / 3 : ℝ) * polynomialD2 +
    (32 / 15 : ℝ) * polynomialD4 + (32 / 7 : ℝ) * polynomialD6

private def polynomialMoment02 : ℝ :=
  (4 / 15 : ℝ) * polynomialD2 +
    (16 / 21 : ℝ) * polynomialD4 + (32 / 15 : ℝ) * polynomialD6

private def polynomialMoment22 : ℝ :=
  (16 / 75 : ℝ) * polynomialD4 + (32 / 35 : ℝ) * polynomialD6

theorem poleFreePolynomialDifference_expansion (t : ℝ) :
    poleFreePolynomialDifference t =
      polynomialD0 + polynomialD2 * t ^ 2 +
        polynomialD4 * t ^ 4 + polynomialD6 * t ^ 6 := by
  rw [show poleFreePolynomialDifference t =
      poleFreeKernelPolynomial6 t - evenStructuralRegularQuadratic t by rfl,
    poleFreeKernelPolynomial6_expansion]
  unfold polynomialD0 polynomialD2 polynomialD4 polynomialD6
    evenStructuralRegularQuadratic
  ring

private theorem integral_polynomialDifference_mul_correlations :
    (∫ t : ℝ in 0..2,
      poleFreePolynomialDifference t * evenStructuralCorrelation00 t) =
        polynomialMoment00 ∧
      (∫ t : ℝ in 0..2,
        poleFreePolynomialDifference t * evenStructuralCorrelation02 t) =
        polynomialMoment02 ∧
      (∫ t : ℝ in 0..2,
        poleFreePolynomialDifference t * evenStructuralCorrelation22 t) =
        polynomialMoment22 := by
  constructor
  · rw [show (fun t : ℝ ↦
        poleFreePolynomialDifference t * evenStructuralCorrelation00 t) =
      fun t ↦ (2 * polynomialD0) * t ^ 0 +
        ((-polynomialD0) * t ^ 1 +
          ((2 * polynomialD2) * t ^ 2 +
            ((-polynomialD2) * t ^ 3 +
              ((2 * polynomialD4) * t ^ 4 +
                ((-polynomialD4) * t ^ 5 +
                  ((2 * polynomialD6) * t ^ 6 +
                    ((-polynomialD6) * t ^ 7 +
                      (0 * t ^ 8 + (0 * t ^ 9 +
                        (0 * t ^ 10 + 0 * t ^ 11)))))))))) by
      funext t
      rw [poleFreePolynomialDifference_expansion]
      unfold evenStructuralCorrelation00
      ring,
    integral_polynomial_eleven]
    unfold polynomialMoment00
    ring
  · constructor
    · rw [show (fun t : ℝ ↦
          poleFreePolynomialDifference t * evenStructuralCorrelation02 t) =
        fun t ↦ 0 * t ^ 0 +
          ((-polynomialD0) * t ^ 1 +
            (((3 / 2 : ℝ) * polynomialD0) * t ^ 2 +
              ((-(1 / 2 : ℝ) * polynomialD0 - polynomialD2) * t ^ 3 +
                (((3 / 2 : ℝ) * polynomialD2) * t ^ 4 +
                  ((-(1 / 2 : ℝ) * polynomialD2 - polynomialD4) * t ^ 5 +
                    (((3 / 2 : ℝ) * polynomialD4) * t ^ 6 +
                      ((-(1 / 2 : ℝ) * polynomialD4 - polynomialD6) * t ^ 7 +
                        (((3 / 2 : ℝ) * polynomialD6) * t ^ 8 +
                          ((-(1 / 2 : ℝ) * polynomialD6) * t ^ 9 +
                            (0 * t ^ 10 + 0 * t ^ 11)))))))))) by
        funext t
        rw [poleFreePolynomialDifference_expansion]
        unfold evenStructuralCorrelation02
        ring,
      integral_polynomial_eleven]
      unfold polynomialMoment02
      ring
    · rw [show (fun t : ℝ ↦
          poleFreePolynomialDifference t * evenStructuralCorrelation22 t) =
        fun t ↦ ((2 / 5 : ℝ) * polynomialD0) * t ^ 0 +
          ((-polynomialD0) * t ^ 1 +
            (((2 / 5 : ℝ) * polynomialD2) * t ^ 2 +
              (((1 / 2 : ℝ) * polynomialD0 - polynomialD2) * t ^ 3 +
                (((2 / 5 : ℝ) * polynomialD4) * t ^ 4 +
                  ((-(3 / 40 : ℝ) * polynomialD0 +
                      (1 / 2 : ℝ) * polynomialD2 - polynomialD4) * t ^ 5 +
                    (((2 / 5 : ℝ) * polynomialD6) * t ^ 6 +
                      ((-(3 / 40 : ℝ) * polynomialD2 +
                          (1 / 2 : ℝ) * polynomialD4 - polynomialD6) * t ^ 7 +
                        (0 * t ^ 8 +
                          (((1 / 2 : ℝ) * polynomialD6 -
                            (3 / 40 : ℝ) * polynomialD4) * t ^ 9 +
                            (0 * t ^ 10 +
                              (-(3 / 40 : ℝ) * polynomialD6) * t ^ 11)))))))))) by
        funext t
        rw [poleFreePolynomialDifference_expansion]
        unfold evenStructuralCorrelation22
        ring,
      integral_polynomial_eleven]
      unfold polynomialMoment22
      ring

private theorem polynomialMoment_bounds :
    (467 / 1250000 : ℝ) ≤ polynomialMoment00 ∧
      polynomialMoment00 ≤ (5399 / 13125000 : ℝ) ∧
      (17 / 2625000 : ℝ) ≤ polynomialMoment02 ∧
      polynomialMoment02 ≤ (6 / 546875 : ℝ) ∧
      (47 / 4687500 : ℝ) ≤ polynomialMoment22 ∧
      polynomialMoment22 ≤ (117 / 10937500 : ℝ) := by
  rcases poleFree_coefficient_bounds with
    ⟨hd0L, hd0U, hd2L, hd2U, hd4L, hd4U, hd6L, hd6U⟩
  unfold polynomialMoment00 polynomialMoment02 polynomialMoment22
    polynomialD0 polynomialD2 polynomialD4 polynomialD6
  constructor
  · norm_num at hd0L hd2L hd4L hd6L ⊢
    linarith
  constructor
  · norm_num at hd0U hd2U hd4U hd6U ⊢
    linarith
  constructor
  · norm_num at hd2L hd4L hd6L ⊢
    linarith
  constructor
  · norm_num at hd2U hd4U hd6U ⊢
    linarith
  constructor
  · norm_num at hd4L hd6L ⊢
    linarith
  · norm_num at hd4U hd6U ⊢
    linarith

/-! ## The single global analytic remainder -/

def poleFreeAnalyticError (C : ℝ → ℝ) : ℝ :=
  ∫ t : ℝ in 0..2,
    (oddLowPoleFreeKernel t - poleFreeKernelPolynomial6 t) * C t

private theorem measurable_yoshidaRegularKernel_sharp :
    Measurable yoshidaRegularKernel := by
  unfold yoshidaRegularKernel
  apply Measurable.ite
  · simpa only [Set.setOf_eq_eq_singleton] using
      measurableSet_singleton (0 : ℝ)
  · exact measurable_const
  · exact ((Real.measurable_exp.comp (measurable_id.div_const 2)).div
      (measurable_const.mul Real.measurable_sinh)).sub
        (measurable_const.div (measurable_const.mul measurable_id))

private theorem measurable_symmetricRegularWeight_sharp :
    Measurable factorTwoCenteredSymmetricRegularWeight := by
  unfold factorTwoCenteredSymmetricRegularWeight
  exact (((measurable_const.mul
      (Real.measurable_cosh.comp (by fun_prop))).add
        (measurable_const.mul
          (Real.measurable_cosh.comp (by fun_prop)))).sub
      (measurable_yoshidaRegularKernel_sharp.comp (by fun_prop))).sub
        (measurable_yoshidaRegularKernel_sharp.comp (by fun_prop))

theorem continuous_poleFreeKernelPolynomial6 :
    Continuous poleFreeKernelPolynomial6 := by
  unfold poleFreeKernelPolynomial6 wideCoshPolynomial6
    yoshidaRegularKernelPolynomial6
  fun_prop

private theorem intervalIntegrable_poleFreeAnalyticError
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
    exact ((measurable_const.mul measurable_symmetricRegularWeight_sharp).sub
      continuous_poleFreeKernelPolynomial6.measurable).mul hC.measurable
  have hfg : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (0 : ℝ) 2)),
      ‖f t‖ ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hk := (abs_poleFreeKernel_sub_polynomial_lt
      (⟨ht.1.le, ht.2⟩ : t ∈ Icc (0 : ℝ) 2)).le
    dsimp only [f, g]
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hk (abs_nonneg (C t))
  constructor
  · exact Integrable.mono' hg hfmeas hfg
  · simp

theorem abs_poleFreeAnalyticError_le
    (C : ℝ → ℝ) (hC : Continuous C) :
    |poleFreeAnalyticError C| ≤
      (3 / 8000 : ℝ) * (∫ t : ℝ in 0..2, |C t|) := by
  let f : ℝ → ℝ := fun t ↦
    (oddLowPoleFreeKernel t - poleFreeKernelPolynomial6 t) * C t
  let g : ℝ → ℝ := fun t ↦ (3 / 8000 : ℝ) * |C t|
  have hf : IntervalIntegrable f volume 0 2 := by
    dsimp only [f]
    exact intervalIntegrable_poleFreeAnalyticError C hC
  have hg : IntervalIntegrable g volume 0 2 := by
    dsimp only [g]
    exact (hC.abs.const_mul (3 / 8000 : ℝ)).intervalIntegrable 0 2
  have hmono : (∫ t : ℝ in 0..2, |f t|) ≤ ∫ t : ℝ in 0..2, g t := by
    apply intervalIntegral.integral_mono_on (by norm_num) hf.abs hg
    intro t ht
    have hk := (abs_poleFreeKernel_sub_polynomial_lt ht).le
    dsimp only [f, g]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hk (abs_nonneg (C t))
  calc
    |poleFreeAnalyticError C| = |∫ t : ℝ in 0..2, f t| := by rfl
    _ ≤ ∫ t : ℝ in 0..2, |f t| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ t : ℝ in 0..2, g t := hmono
    _ = (3 / 8000 : ℝ) * (∫ t : ℝ in 0..2, |C t|) := by
      rw [intervalIntegral.integral_const_mul]

theorem abs_poleFreeAnalyticError_profile_le (c d : ℝ) :
    |poleFreeAnalyticError
        (centeredEndpointCorrelation
          (factorTwoEvenStructuralLowProfile c d))| ≤
      (3 / 8000 : ℝ) * (2 * c ^ 2 + (2 / 5 : ℝ) * d ^ 2) := by
  have herr := abs_poleFreeAnalyticError_le
    (centeredEndpointCorrelation (factorTwoEvenStructuralLowProfile c d))
    (continuous_centeredEndpointCorrelation_of_continuous
      (factorTwoEvenStructuralLowProfile c d)
      (continuous_factorTwoEvenStructuralLowProfile c d))
  have hcorr := integral_abs_centeredEndpointCorrelation_le_energy
    (factorTwoEvenStructuralLowProfile c d)
    (continuous_factorTwoEvenStructuralLowProfile c d)
  have hscaled := mul_le_mul_of_nonneg_left hcorr
    (by norm_num : (0 : ℝ) ≤ 3 / 8000)
  rw [integral_evenStructuralProfile_sq] at hscaled
  exact herr.trans hscaled

theorem continuous_poleFreePolynomialDifference :
    Continuous poleFreePolynomialDifference := by
  unfold poleFreePolynomialDifference evenStructuralRegularQuadratic
  exact continuous_poleFreeKernelPolynomial6.sub (by fun_prop)

theorem evenStructuralRegularError_eq_analytic_add_polynomial
    (C : ℝ → ℝ) (hC : Continuous C) :
    evenStructuralRegularError C =
      poleFreeAnalyticError C +
        ∫ t : ℝ in 0..2, poleFreePolynomialDifference t * C t := by
  have ha : IntervalIntegrable
      (fun t ↦
        (yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t -
          poleFreeKernelPolynomial6 t) * C t) volume 0 2 := by
    simpa only [oddLowPoleFreeKernel] using
      intervalIntegrable_poleFreeAnalyticError C hC
  have hp : IntervalIntegrable
      (fun t ↦ poleFreePolynomialDifference t * C t) volume 0 2 :=
    (continuous_poleFreePolynomialDifference.mul hC).intervalIntegrable 0 2
  unfold evenStructuralRegularError oddStructuralRegularError
    poleFreeAnalyticError oddLowPoleFreeKernel
  rw [← intervalIntegral.integral_add ha hp]
  apply intervalIntegral.integral_congr
  intro t _ht
  unfold poleFreePolynomialDifference evenStructuralRegularQuadratic
    oddStructuralRegularQuadratic
  ring

private theorem integral_polynomialDifference_profile (c d : ℝ) :
    (∫ t : ℝ in 0..2,
      poleFreePolynomialDifference t *
        centeredEndpointCorrelation
          (factorTwoEvenStructuralLowProfile c d) t) =
      polynomialMoment00 * c ^ 2 +
        2 * polynomialMoment02 * c * d +
        polynomialMoment22 * d ^ 2 := by
  have h00 : IntervalIntegrable
      (fun t ↦ poleFreePolynomialDifference t * evenStructuralCorrelation00 t)
      volume 0 2 := by
    exact (continuous_poleFreePolynomialDifference.mul
      (by unfold evenStructuralCorrelation00; fun_prop)).intervalIntegrable 0 2
  have h02 : IntervalIntegrable
      (fun t ↦ poleFreePolynomialDifference t * evenStructuralCorrelation02 t)
      volume 0 2 := by
    exact (continuous_poleFreePolynomialDifference.mul
      (by unfold evenStructuralCorrelation02; fun_prop)).intervalIntegrable 0 2
  have h22 : IntervalIntegrable
      (fun t ↦ poleFreePolynomialDifference t * evenStructuralCorrelation22 t)
      volume 0 2 := by
    exact (continuous_poleFreePolynomialDifference.mul
      (by unfold evenStructuralCorrelation22; fun_prop)).intervalIntegrable 0 2
  simp_rw [centeredEndpointCorrelation_evenStructuralProfile]
  rw [show (fun t : ℝ ↦
      poleFreePolynomialDifference t *
        (c ^ 2 * evenStructuralCorrelation00 t +
          2 * c * d * evenStructuralCorrelation02 t +
          d ^ 2 * evenStructuralCorrelation22 t)) =
      fun t ↦ c ^ 2 *
          (poleFreePolynomialDifference t * evenStructuralCorrelation00 t) +
        (2 * c * d) *
          (poleFreePolynomialDifference t * evenStructuralCorrelation02 t) +
        d ^ 2 *
          (poleFreePolynomialDifference t * evenStructuralCorrelation22 t) by
    funext t
    ring,
    intervalIntegral.integral_add
      ((h00.const_mul (c ^ 2)).add (h02.const_mul (2 * c * d)))
      (h22.const_mul (d ^ 2)),
    intervalIntegral.integral_add (h00.const_mul (c ^ 2))
      (h02.const_mul (2 * c * d))]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_polynomialDifference_mul_correlations.1,
    integral_polynomialDifference_mul_correlations.2.1,
    integral_polynomialDifference_mul_correlations.2.2]
  ring

theorem evenStructuralRegularError_profile_sharp_expansion (c d : ℝ) :
    evenStructuralRegularError
        (centeredEndpointCorrelation
          (factorTwoEvenStructuralLowProfile c d)) =
      poleFreeAnalyticError
          (centeredEndpointCorrelation
            (factorTwoEvenStructuralLowProfile c d)) +
        polynomialMoment00 * c ^ 2 +
        2 * polynomialMoment02 * c * d +
        polynomialMoment22 * d ^ 2 := by
  rw [evenStructuralRegularError_eq_analytic_add_polynomial
    (centeredEndpointCorrelation (factorTwoEvenStructuralLowProfile c d))
    (continuous_centeredEndpointCorrelation_of_continuous
      (factorTwoEvenStructuralLowProfile c d)
      (continuous_factorTwoEvenStructuralLowProfile c d)),
    integral_polynomialDifference_profile]
  ring

/-! ## A Taylor-model Loewner Gram -/

def evenNegativePerturbationTaylor00 : ℝ :=
  -evenStructuralKernelBase00 - polynomialMoment00 - 3 / 4000

def evenNegativePerturbationTaylor02 : ℝ :=
  -evenStructuralKernelBase02 - polynomialMoment02

def evenNegativePerturbationTaylor22 : ℝ :=
  -evenStructuralKernelBase22 - polynomialMoment22 - 3 / 20000

theorem evenNegativePerturbationTaylor_quadratic_le (c d : ℝ) :
    evenNegativePerturbationTaylor00 * c ^ 2 +
        2 * evenNegativePerturbationTaylor02 * c * d +
        evenNegativePerturbationTaylor22 * d ^ 2 ≤
      -factorTwoCenteredSymmetricPerturbation
        (factorTwoEvenStructuralLowProfile c d) := by
  have herr := abs_poleFreeAnalyticError_profile_le c d
  have herrUpper :
      poleFreeAnalyticError
          (centeredEndpointCorrelation
            (factorTwoEvenStructuralLowProfile c d)) ≤
        (3 / 8000 : ℝ) * (2 * c ^ 2 + (2 / 5 : ℝ) * d ^ 2) :=
    (le_abs_self _).trans herr
  rw [factorTwoCenteredSymmetricPerturbation_even_profile_kernel_eq,
    evenStructuralRegularError_profile_sharp_expansion]
  unfold evenNegativePerturbationTaylor00 evenNegativePerturbationTaylor02
    evenNegativePerturbationTaylor22
  nlinarith

private theorem primeRatio_correlation00_sharp_lower :
    (83007 / 100000 : ℝ) <
      evenStructuralCorrelation00
        (factorTwoPrimeShift / yoshidaEndpointA) := by
  have hratio :
      factorTwoPrimeShift / yoshidaEndpointA < (116993 / 100000 : ℝ) := by
    have hApos : 0 < yoshidaEndpointA := yoshidaEndpointA_pos
    rw [div_lt_iff₀ hApos]
    unfold factorTwoPrimeShift yoshidaEndpointA
    have h32 := strict_log_three_halves_kernel_bounds.2
    have h2 := strict_log_two_fine_bounds.1
    nlinarith
  unfold evenStructuralCorrelation00
  linarith

private theorem negativeStructuralBase00_sharp_lower :
    (34153429 / 150000000 : ℝ) < -evenStructuralKernelBase00 := by
  have hL := strict_log_two_fine_bounds.1
  have ha := log_two_div_sqrt_two_kernel_lower
  have hb := log_three_div_sqrt_three_kernel_bounds.1
  have hC := primeRatio_correlation00_sharp_lower
  have hbeta : 0 < Real.log 3 / Real.sqrt 3 := by positivity
  have hprod :
      (63427 / 100000 : ℝ) * (83007 / 100000 : ℝ) <
        (Real.log 3 / Real.sqrt 3) *
          evenStructuralCorrelation00
            (factorTwoPrimeShift / yoshidaEndpointA) := by
    calc
      (63427 / 100000 : ℝ) * (83007 / 100000 : ℝ) <
          (Real.log 3 / Real.sqrt 3) * (83007 / 100000 : ℝ) :=
        mul_lt_mul_of_pos_right hb (by norm_num)
      _ < (Real.log 3 / Real.sqrt 3) *
          evenStructuralCorrelation00
            (factorTwoPrimeShift / yoshidaEndpointA) :=
        mul_lt_mul_of_pos_left hC hbeta
  unfold evenStructuralKernelBase00
  nlinarith

private theorem taylor00_sub_rational_lower :
    (9861 / 350000000 : ℝ) <
      evenNegativePerturbationTaylor00 - 453 / 2000 := by
  have hb := negativeStructuralBase00_sharp_lower
  have hm := polynomialMoment_bounds.2.1
  unfold evenNegativePerturbationTaylor00
  norm_num at hb hm ⊢
  linarith

private theorem taylor02_sub_rational_abs_upper :
    |evenNegativePerturbationTaylor02 - 20477 / 100000| <
      (1417 / 17500000 : ℝ) := by
  have hb := evenSlopeKernel02_bounds
  have hbLower := evenSlopeKernel02_lower
  have hm := polynomialMoment_bounds
  unfold evenNegativePerturbationTaylor02
  unfold evenSlopeKernel02 at hb hbLower
  rw [abs_lt]
  constructor <;> norm_num at hb hbLower hm ⊢ <;> linarith

private theorem taylor22_sub_rational_lower :
    (29689 / 87500000 : ℝ) <
      evenNegativePerturbationTaylor22 - 47 / 250 := by
  have hb := evenSlopeKernel22_lower
  have hm := polynomialMoment_bounds.2.2.2.2.2
  unfold evenNegativePerturbationTaylor22
  unfold evenSlopeKernel22 at hb
  norm_num at hb hm ⊢
  linarith

private theorem rational_sub_taylor_defect_det_pos :
    0 <
      (evenNegativePerturbationTaylor00 - 453 / 2000) *
          (evenNegativePerturbationTaylor22 - 47 / 250) -
        (evenNegativePerturbationTaylor02 - 20477 / 100000) ^ 2 := by
  let d00 := evenNegativePerturbationTaylor00 - 453 / 2000
  let d02 := evenNegativePerturbationTaylor02 - 20477 / 100000
  let d22 := evenNegativePerturbationTaylor22 - 47 / 250
  have h00 : (9861 / 350000000 : ℝ) < d00 := by
    simpa only [d00] using taylor00_sub_rational_lower
  have h02 : |d02| < (1417 / 17500000 : ℝ) := by
    simpa only [d02] using taylor02_sub_rational_abs_upper
  have h22 : (29689 / 87500000 : ℝ) < d22 := by
    simpa only [d22] using taylor22_sub_rational_lower
  have h00pos : 0 < d00 := (by norm_num : (0 : ℝ) < 9861 / 350000000).trans h00
  have h22pos : 0 < d22 := (by norm_num : (0 : ℝ) < 29689 / 87500000).trans h22
  have hprod :
      (9861 / 350000000 : ℝ) * (29689 / 87500000 : ℝ) <
        d00 * d22 := by
    calc
      (9861 / 350000000 : ℝ) * (29689 / 87500000 : ℝ) <
          d00 * (29689 / 87500000 : ℝ) :=
        mul_lt_mul_of_pos_right h00 (by norm_num)
      _ < d00 * d22 := mul_lt_mul_of_pos_left h22 h00pos
  have hsq :
      d02 ^ 2 < (1417 / 17500000 : ℝ) ^ 2 := by
    rw [abs_lt] at h02
    nlinarith [mul_pos (sub_pos.mpr h02.2) (by linarith : 0 < d02 + 1417 / 17500000)]
  have hrat :
      (1417 / 17500000 : ℝ) ^ 2 <
        (9861 / 350000000 : ℝ) * (29689 / 87500000 : ℝ) := by
    norm_num
  dsimp only [d00, d02, d22] at hprod hsq ⊢
  nlinarith

private theorem rational_quadratic_le_taylor (c d : ℝ) :
    (453 / 2000 : ℝ) * c ^ 2 +
        2 * (20477 / 100000 : ℝ) * c * d +
        (47 / 250 : ℝ) * d ^ 2 ≤
      evenNegativePerturbationTaylor00 * c ^ 2 +
        2 * evenNegativePerturbationTaylor02 * c * d +
        evenNegativePerturbationTaylor22 * d ^ 2 := by
  let d00 := evenNegativePerturbationTaylor00 - 453 / 2000
  let d02 := evenNegativePerturbationTaylor02 - 20477 / 100000
  let d22 := evenNegativePerturbationTaylor22 - 47 / 250
  have h00 : 0 < d00 := by
    have h := taylor00_sub_rational_lower
    dsimp only [d00]
    nlinarith
  have hdet : 0 < d00 * d22 - d02 ^ 2 := by
    simpa only [d00, d02, d22] using rational_sub_taylor_defect_det_pos
  have hquad : 0 ≤ d00 * c ^ 2 + 2 * d02 * c * d + d22 * d ^ 2 := by
    by_cases hne : c ≠ 0 ∨ d ≠ 0
    · exact (real_twoByTwo_quadratic_pos d00 d02 d22 c d h00 hdet hne).le
    · push_neg at hne
      rcases hne with ⟨rfl, rfl⟩
      norm_num
  dsimp only [d00, d02, d22] at hquad
  nlinarith

def evenNegativePerturbationSharp00 : ℝ := 453 / 2000

def evenNegativePerturbationSharp02 : ℝ := 20477 / 100000

def evenNegativePerturbationSharp22 : ℝ := 47 / 250

theorem evenNegativePerturbationSharp_principal_minors_pos :
    0 < evenNegativePerturbationSharp00 ∧
      0 < evenNegativePerturbationSharp22 ∧
      0 < evenNegativePerturbationSharp00 *
          evenNegativePerturbationSharp22 -
        evenNegativePerturbationSharp02 ^ 2 := by
  norm_num [evenNegativePerturbationSharp00,
    evenNegativePerturbationSharp02, evenNegativePerturbationSharp22]

/-- The rational Gram lies below the complete negative symmetric
perturbation on the structural `P₀/P₂` plane. -/
theorem evenNegativePerturbationSharp_quadratic_le (c d : ℝ) :
    evenNegativePerturbationSharp00 * c ^ 2 +
        2 * evenNegativePerturbationSharp02 * c * d +
        evenNegativePerturbationSharp22 * d ^ 2 ≤
      -factorTwoCenteredSymmetricPerturbation
        (factorTwoEvenStructuralLowProfile c d) := by
  calc
    evenNegativePerturbationSharp00 * c ^ 2 +
          2 * evenNegativePerturbationSharp02 * c * d +
          evenNegativePerturbationSharp22 * d ^ 2 ≤
        evenNegativePerturbationTaylor00 * c ^ 2 +
          2 * evenNegativePerturbationTaylor02 * c * d +
          evenNegativePerturbationTaylor22 * d ^ 2 := by
      simpa only [evenNegativePerturbationSharp00,
        evenNegativePerturbationSharp02, evenNegativePerturbationSharp22]
        using rational_quadratic_le_taylor c d
    _ ≤ -factorTwoCenteredSymmetricPerturbation
          (factorTwoEvenStructuralLowProfile c d) :=
      evenNegativePerturbationTaylor_quadratic_le c d

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
