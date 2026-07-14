import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
import ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointClean

set_option autoImplicit false

open Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseOddAffineKernelEstimate

noncomputable section

open YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoAdjacentKernel
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoCrossDistribution
open YoshidaFactorTwoEndpointClean
open YoshidaRegularKernelBound
open YoshidaRenormalizedGeometricKernel

/-!
# A structural affine-kernel estimate for the intrinsic odd block

The unregularized symmetric weight has a Cauchy pole at the right endpoint,
so it cannot have a uniform affine enclosure.  The endpoint calculation uses
the pole-free regular weight below.  We compare it to a fixed even quadratic;
all estimates are global Taylor remainders on the whole interval, with no
subdivision or sampled certificate.
-/

/-- The pole-free scalar kernel occurring after both Cauchy poles have been
split off exactly. -/
def oddLowPoleFreeKernel (t : ℝ) : ℝ :=
  yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t

/-- The quadratic which captures the pole-free kernel on the full overlap
interval. -/
def oddLowPoleFreeKernelQuadratic (t : ℝ) : ℝ :=
  (79 / 60 : ℝ) + (3 / 125 : ℝ) * t ^ 2

/-! ## One global Taylor envelope -/

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

/-- The same sixth-order regular-kernel polynomial remains a one-sided
envelope on the larger interval `[0, 2 log 2]`. -/
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
      have hlog := YoshidaConstantBounds.strict_log_two_bounds.2
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

/-! ## The global polynomial model -/

private def oddLowPoleFreeKernelPolynomial6 (t : ℝ) : ℝ :=
  let up := yoshidaEndpointA * (2 + t)
  let um := yoshidaEndpointA * (2 - t)
  yoshidaEndpointA *
    (2 * wideCoshPolynomial6 (up / 2) +
      2 * wideCoshPolynomial6 (um / 2) -
      yoshidaRegularKernelPolynomial6 up -
      yoshidaRegularKernelPolynomial6 um)

private theorem abs_poleFreeKernel_sub_polynomial_lt
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    |oddLowPoleFreeKernel t - oddLowPoleFreeKernelPolynomial6 t| <
      (3 / 8000 : ℝ) := by
  let up : ℝ := yoshidaEndpointA * (2 + t)
  let um : ℝ := yoshidaEndpointA * (2 - t)
  let zp : ℝ := up / 2
  let zm : ℝ := um / 2
  let E : ℝ := (4 / 3 : ℝ) * (7 / 10 : ℝ) ^ 8 / 40320
  have hAupper : yoshidaEndpointA < (347 / 1000 : ℝ) := by
    unfold yoshidaEndpointA
    linarith [YoshidaConstantBounds.strict_log_two_bounds.2]
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
    have hlog := YoshidaConstantBounds.strict_log_two_bounds.2
    have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith [ht.2]
  have hzm : zm < (7 / 10 : ℝ) := by
    dsimp only [zm, um]
    unfold yoshidaEndpointA
    have hlog := YoshidaConstantBounds.strict_log_two_bounds.2
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
      oddLowPoleFreeKernel t - oddLowPoleFreeKernelPolynomial6 t =
        yoshidaEndpointA * (2 * ecp + 2 * ecm - erp - erm) := by
    dsimp only [oddLowPoleFreeKernel, oddLowPoleFreeKernelPolynomial6,
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
      |oddLowPoleFreeKernel t - oddLowPoleFreeKernelPolynomial6 t| ≤
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
    |oddLowPoleFreeKernel t - oddLowPoleFreeKernelPolynomial6 t| ≤
        yoshidaEndpointA * (4 * E + 2 / 1900) := hscaled
    _ < (347 / 1000 : ℝ) * (4 * E + 2 / 1900) :=
      mul_lt_mul_of_pos_right hAupper (by positivity)
    _ < (3 / 8000 : ℝ) := by
      simpa only [E] using hrat

private def poleFreePolynomialCoeff0 (a : ℝ) : ℝ :=
  (7 / 2 : ℝ) * a + a ^ 2 / 12 + (9 / 4 : ℝ) * a ^ 3 -
    (7 / 720 : ℝ) * a ^ 4 + a ^ 5 / 16 +
      (31 / 30240 : ℝ) * a ^ 6 + (23 / 480 : ℝ) * a ^ 7

private def poleFreePolynomialCoeff2 (a : ℝ) : ℝ :=
  (9 / 16 : ℝ) * a ^ 3 - (7 / 960 : ℝ) * a ^ 4 +
    (3 / 32 : ℝ) * a ^ 5 + (31 / 12096 : ℝ) * a ^ 6 +
      (23 / 128 : ℝ) * a ^ 7

private def poleFreePolynomialCoeff4 (a : ℝ) : ℝ :=
  a ^ 5 / 256 + (31 / 96768 : ℝ) * a ^ 6 +
    (23 / 512 : ℝ) * a ^ 7

private def poleFreePolynomialCoeff6 (a : ℝ) : ℝ :=
  (23 / 30720 : ℝ) * a ^ 7

private theorem oddLowPoleFreeKernelPolynomial6_expansion (t : ℝ) :
    oddLowPoleFreeKernelPolynomial6 t =
      poleFreePolynomialCoeff0 yoshidaEndpointA +
        poleFreePolynomialCoeff2 yoshidaEndpointA * t ^ 2 +
        poleFreePolynomialCoeff4 yoshidaEndpointA * t ^ 4 +
        poleFreePolynomialCoeff6 yoshidaEndpointA * t ^ 6 := by
  unfold oddLowPoleFreeKernelPolynomial6 wideCoshPolynomial6
    yoshidaRegularKernelPolynomial6 poleFreePolynomialCoeff0
    poleFreePolynomialCoeff2 poleFreePolynomialCoeff4
    poleFreePolynomialCoeff6
  ring

private theorem poleFree_polynomial_coefficient_bounds :
    (21 / 100000 : ℝ) ≤
        poleFreePolynomialCoeff0 yoshidaEndpointA - 79 / 60 ∧
      poleFreePolynomialCoeff0 yoshidaEndpointA - 79 / 60 ≤
        (22 / 100000 : ℝ) ∧
      (-11 / 100000 : ℝ) ≤
        poleFreePolynomialCoeff2 yoshidaEndpointA - 3 / 125 ∧
      poleFreePolynomialCoeff2 yoshidaEndpointA - 3 / 125 ≤
        (-1 / 10000 : ℝ) ∧
      (47 / 1000000 : ℝ) ≤
        poleFreePolynomialCoeff4 yoshidaEndpointA ∧
      poleFreePolynomialCoeff4 yoshidaEndpointA ≤
        (48 / 1000000 : ℝ) ∧
      0 ≤ poleFreePolynomialCoeff6 yoshidaEndpointA ∧
      poleFreePolynomialCoeff6 yoshidaEndpointA ≤
        (5 / 10000000 : ℝ) := by
  let L : ℝ := 3465735 / 10000000
  let U : ℝ := 3465737 / 10000000
  have hAL : L ≤ yoshidaEndpointA := by
    dsimp only [L]
    unfold yoshidaEndpointA
    linarith [YoshidaConstantBounds.strict_log_two_fine_bounds.1]
  have hAU : yoshidaEndpointA ≤ U := by
    dsimp only [U]
    unfold yoshidaEndpointA
    linarith [YoshidaConstantBounds.strict_log_two_fine_bounds.2]
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
  unfold poleFreePolynomialCoeff0 poleFreePolynomialCoeff2
    poleFreePolynomialCoeff4 poleFreePolynomialCoeff6
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
      (7 / 2 : ℝ) * yoshidaEndpointA +
          yoshidaEndpointA ^ 2 / 12 +
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

private theorem abs_poleFreePolynomial_sub_quadratic_le
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    |oddLowPoleFreeKernelPolynomial6 t - oddLowPoleFreeKernelQuadratic t| ≤
      (1 / 800 : ℝ) := by
  rcases poleFree_polynomial_coefficient_bounds with
    ⟨hc0Lower, hc0Upper, hc2Lower, hc2Upper,
      hc4Lower, hc4Upper, hc6Lower, hc6Upper⟩
  let s : ℝ := t ^ 2
  let d0 : ℝ := poleFreePolynomialCoeff0 yoshidaEndpointA - 79 / 60
  let d2 : ℝ := poleFreePolynomialCoeff2 yoshidaEndpointA - 3 / 125
  let c4 : ℝ := poleFreePolynomialCoeff4 yoshidaEndpointA
  let c6 : ℝ := poleFreePolynomialCoeff6 yoshidaEndpointA
  have hs0 : 0 ≤ s := by
    dsimp only [s]
    positivity
  have hs4 : s ≤ 4 := by
    dsimp only [s]
    have hprod : 0 ≤ t * (2 - t) :=
      mul_nonneg ht.1 (sub_nonneg.mpr ht.2)
    nlinarith
  have hsSq : s ^ 2 ≤ 16 := by
    have h := pow_le_pow_left₀ hs0 hs4 2
    norm_num at h ⊢
    exact h
  have hsCube : s ^ 3 ≤ 64 := by
    have h := pow_le_pow_left₀ hs0 hs4 3
    norm_num at h ⊢
    exact h
  have hformula :
      oddLowPoleFreeKernelPolynomial6 t - oddLowPoleFreeKernelQuadratic t =
        d0 + d2 * s + c4 * s ^ 2 + c6 * s ^ 3 := by
    rw [oddLowPoleFreeKernelPolynomial6_expansion]
    dsimp only [oddLowPoleFreeKernelQuadratic, d0, d2, c4, c6, s]
    ring
  have hd0Lower : (21 / 100000 : ℝ) ≤ d0 := hc0Lower
  have hd0Upper : d0 ≤ (22 / 100000 : ℝ) := hc0Upper
  have hd2Lower : (-11 / 100000 : ℝ) ≤ d2 := hc2Lower
  have hd2Upper : d2 ≤ (-1 / 10000 : ℝ) := hc2Upper
  have hc4L : (47 / 1000000 : ℝ) ≤ c4 := hc4Lower
  have hc4U : c4 ≤ (48 / 1000000 : ℝ) := hc4Upper
  have hc6L : 0 ≤ c6 := hc6Lower
  have hc6U : c6 ≤ (5 / 10000000 : ℝ) := hc6Upper
  have hd2LowerMul :
      (-11 / 100000 : ℝ) * s ≤ d2 * s :=
    mul_le_mul_of_nonneg_right hd2Lower hs0
  have hc4LowerMul :
      (47 / 1000000 : ℝ) * s ^ 2 ≤ c4 * s ^ 2 :=
    mul_le_mul_of_nonneg_right hc4L (sq_nonneg s)
  have hc6Term0 : 0 ≤ c6 * s ^ 3 := by positivity
  have hbaseNonneg :
      0 ≤ (21 / 100000 : ℝ) +
        (-11 / 100000 : ℝ) * s +
        (47 / 1000000 : ℝ) * s ^ 2 := by
    nlinarith [sq_nonneg (s - 55 / 47)]
  have hnonneg : 0 ≤ d0 + d2 * s + c4 * s ^ 2 + c6 * s ^ 3 := by
    linarith
  have hd2TermUpper : d2 * s ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg (hd2Upper.trans (by norm_num)) hs0
  have hc4TermUpper :
      c4 * s ^ 2 ≤ (48 / 1000000 : ℝ) * 16 := by
    calc
      c4 * s ^ 2 ≤ (48 / 1000000 : ℝ) * s ^ 2 :=
        mul_le_mul_of_nonneg_right hc4U (sq_nonneg s)
      _ ≤ (48 / 1000000 : ℝ) * 16 := by gcongr
  have hc6TermUpper :
      c6 * s ^ 3 ≤ (5 / 10000000 : ℝ) * 64 := by
    calc
      c6 * s ^ 3 ≤ (5 / 10000000 : ℝ) * s ^ 3 :=
        mul_le_mul_of_nonneg_right hc6U (by positivity)
      _ ≤ (5 / 10000000 : ℝ) * 64 := by gcongr
  have hupper :
      d0 + d2 * s + c4 * s ^ 2 + c6 * s ^ 3 ≤ (1 / 800 : ℝ) := by
    have hrat :
        (22 / 100000 : ℝ) +
            (48 / 1000000 : ℝ) * 16 +
            (5 / 10000000 : ℝ) * 64 <
          (1 / 800 : ℝ) := by norm_num
    linarith
  rw [hformula, abs_of_nonneg hnonneg]
  exact hupper

/-- Uniform structural enclosure of the pole-free odd endpoint kernel.
The proof uses one analytic Taylor remainder on the entire interval and a
single cubic positivity argument in `t²`; it contains no interval subdivision
or sampled certificate. -/
theorem abs_yoshidaEndpointA_mul_factorTwoCenteredSymmetricRegularWeight_sub_quadratic_le
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    |yoshidaEndpointA * factorTwoCenteredSymmetricRegularWeight t -
        ((79 / 60 : ℝ) + (3 / 125 : ℝ) * t ^ 2)| ≤
      (1 / 500 : ℝ) := by
  have ht : t ∈ Icc (0 : ℝ) 2 := ⟨ht0, ht2⟩
  have hanalytic := abs_poleFreeKernel_sub_polynomial_lt ht
  have hpoly := abs_poleFreePolynomial_sub_quadratic_le ht
  have htriangle := abs_sub_le (oddLowPoleFreeKernel t)
    (oddLowPoleFreeKernelPolynomial6 t) (oddLowPoleFreeKernelQuadratic t)
  have hsum :
      |oddLowPoleFreeKernel t - oddLowPoleFreeKernelQuadratic t| <
        (1 / 500 : ℝ) := by
    calc
      |oddLowPoleFreeKernel t - oddLowPoleFreeKernelQuadratic t| ≤
          |oddLowPoleFreeKernel t - oddLowPoleFreeKernelPolynomial6 t| +
            |oddLowPoleFreeKernelPolynomial6 t -
              oddLowPoleFreeKernelQuadratic t| := htriangle
      _ < (3 / 8000 : ℝ) + 1 / 800 := by linarith
      _ < (1 / 500 : ℝ) := by norm_num
  simpa only [oddLowPoleFreeKernel, oddLowPoleFreeKernelQuadratic] using
    hsum.le

/-! ## The antisymmetric regular kernel -/

/-- The nonsingular part of the centered antisymmetric factor-two weight.
The two Cauchy poles are deliberately omitted; they are retained exactly in
the cross-block calculation. -/
def factorTwoCenteredAntisymmetricRegularWeight (t : ℝ) : ℝ :=
  2 * Real.cosh (yoshidaEndpointA * (2 + t) / 2) -
    2 * Real.cosh (yoshidaEndpointA * (2 - t) / 2) -
    yoshidaRegularKernel (yoshidaEndpointA * (2 + t)) +
    yoshidaRegularKernel (yoshidaEndpointA * (2 - t))

private def oddLowAntisymmetricKernelPolynomial6 (t : ℝ) : ℝ :=
  let up := yoshidaEndpointA * (2 + t)
  let um := yoshidaEndpointA * (2 - t)
  yoshidaEndpointA *
    (2 * wideCoshPolynomial6 (up / 2) -
      2 * wideCoshPolynomial6 (um / 2) -
      yoshidaRegularKernelPolynomial6 up +
      yoshidaRegularKernelPolynomial6 um)

private def antisymmetricPolynomialCoeff1 (a : ℝ) : ℝ :=
  a ^ 2 / 24 + (9 / 4 : ℝ) * a ^ 3 - (7 / 480 : ℝ) * a ^ 4 +
    a ^ 5 / 8 + (31 / 12096 : ℝ) * a ^ 6 +
      (23 / 160 : ℝ) * a ^ 7

private def antisymmetricPolynomialCoeff3 (a : ℝ) : ℝ :=
  -(7 / 5760 : ℝ) * a ^ 4 + a ^ 5 / 32 +
    (31 / 24192 : ℝ) * a ^ 6 + (23 / 192 : ℝ) * a ^ 7

private def antisymmetricPolynomialCoeff5 (a : ℝ) : ℝ :=
  (31 / 967680 : ℝ) * a ^ 6 + (23 / 2560 : ℝ) * a ^ 7

private theorem oddLowAntisymmetricKernelPolynomial6_expansion (t : ℝ) :
    oddLowAntisymmetricKernelPolynomial6 t =
      antisymmetricPolynomialCoeff1 yoshidaEndpointA * t +
        antisymmetricPolynomialCoeff3 yoshidaEndpointA * t ^ 3 +
        antisymmetricPolynomialCoeff5 yoshidaEndpointA * t ^ 5 := by
  unfold oddLowAntisymmetricKernelPolynomial6 wideCoshPolynomial6
    yoshidaRegularKernelPolynomial6 antisymmetricPolynomialCoeff1
    antisymmetricPolynomialCoeff3 antisymmetricPolynomialCoeff5
  ring

private theorem abs_antisymmetricKernel_sub_polynomial_lt
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    |yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
        oddLowAntisymmetricKernelPolynomial6 t| < (1 / 4000 : ℝ) := by
  let up : ℝ := yoshidaEndpointA * (2 + t)
  let um : ℝ := yoshidaEndpointA * (2 - t)
  let zp : ℝ := up / 2
  let zm : ℝ := um / 2
  let E : ℝ := (4 / 3 : ℝ) * (7 / 10 : ℝ) ^ 8 / 40320
  have hAupper : yoshidaEndpointA < (347 / 1000 : ℝ) := by
    unfold yoshidaEndpointA
    linarith [YoshidaConstantBounds.strict_log_two_bounds.2]
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
    have hlog := YoshidaConstantBounds.strict_log_two_bounds.2
    have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith [ht.2]
  have hzm : zm < (7 / 10 : ℝ) := by
    dsimp only [zm, um]
    unfold yoshidaEndpointA
    have hlog := YoshidaConstantBounds.strict_log_two_bounds.2
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
      yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
          oddLowAntisymmetricKernelPolynomial6 t =
        yoshidaEndpointA * (2 * ecp - 2 * ecm - erp + erm) := by
    dsimp only [factorTwoCenteredAntisymmetricRegularWeight,
      oddLowAntisymmetricKernelPolynomial6, up, um, zp, zm,
      ecp, ecm, erp, erm]
    ring
  have hinside :
      |2 * ecp - 2 * ecm - erp + erm| ≤ 2 * E + 1 / 1900 := by
    rw [abs_le]
    constructor
    · rw [← sub_nonneg]
      have hidentity :
          (2 * ecp - 2 * ecm - erp + erm) -
              (-(2 * E + 1 / 1900)) =
            2 * ecp + 2 * (E - ecm) +
              ((1 / 1900 : ℝ) - erp) + erm := by
        ring
      rw [hidentity]
      have hEcm : 0 ≤ E - ecm := sub_nonneg.mpr hecmE
      have hrerp : 0 ≤ (1 / 1900 : ℝ) - erp :=
        sub_nonneg.mpr herp
      exact add_nonneg
        (add_nonneg (add_nonneg (mul_nonneg (by norm_num) hecp0)
          (mul_nonneg (by norm_num) hEcm)) hrerp) herm0
    · rw [← sub_nonneg]
      have hidentity :
          (2 * E + 1 / 1900) -
              (2 * ecp - 2 * ecm - erp + erm) =
            2 * (E - ecp) + 2 * ecm + erp +
              ((1 / 1900 : ℝ) - erm) := by
        ring
      rw [hidentity]
      have hEcp : 0 ≤ E - ecp := sub_nonneg.mpr hecpE
      have hrerm : 0 ≤ (1 / 1900 : ℝ) - erm :=
        sub_nonneg.mpr herm
      exact add_nonneg
        (add_nonneg (add_nonneg (mul_nonneg (by norm_num) hEcp)
          (mul_nonneg (by norm_num) hecm0)) herp0) hrerm
  have hscaled :
      |yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
          oddLowAntisymmetricKernelPolynomial6 t| ≤
        yoshidaEndpointA * (2 * E + 1 / 1900) := by
    rw [hdiff, abs_mul, abs_of_pos yoshidaEndpointA_pos]
    exact mul_le_mul_of_nonneg_left hinside yoshidaEndpointA_pos.le
  have hrat :
      (347 / 1000 : ℝ) *
          (2 * ((4 / 3 : ℝ) * (7 / 10 : ℝ) ^ 8 / 40320) +
            1 / 1900) <
        (1 / 4000 : ℝ) := by
    norm_num
  calc
    |yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
        oddLowAntisymmetricKernelPolynomial6 t| ≤
        yoshidaEndpointA * (2 * E + 1 / 1900) := hscaled
    _ < (347 / 1000 : ℝ) * (2 * E + 1 / 1900) :=
      mul_lt_mul_of_pos_right hAupper (by positivity)
    _ < (1 / 4000 : ℝ) := by
      simpa only [E] using hrat

private theorem antisymmetric_polynomial_coefficient_bounds :
    (-827 / 1000000 : ℝ) ≤
        antisymmetricPolynomialCoeff1 yoshidaEndpointA - 1 / 10 ∧
      antisymmetricPolynomialCoeff1 yoshidaEndpointA - 1 / 10 ≤
        (-826 / 1000000 : ℝ) ∧
      (212 / 1000000 : ℝ) ≤
        antisymmetricPolynomialCoeff3 yoshidaEndpointA ∧
      antisymmetricPolynomialCoeff3 yoshidaEndpointA ≤
        (213 / 1000000 : ℝ) ∧
      (5 / 1000000 : ℝ) ≤
        antisymmetricPolynomialCoeff5 yoshidaEndpointA ∧
      antisymmetricPolynomialCoeff5 yoshidaEndpointA ≤
        (6 / 1000000 : ℝ) := by
  let L : ℝ := 3465735 / 10000000
  let U : ℝ := 3465737 / 10000000
  have hAL : L ≤ yoshidaEndpointA := by
    dsimp only [L]
    unfold yoshidaEndpointA
    linarith [YoshidaConstantBounds.strict_log_two_fine_bounds.1]
  have hAU : yoshidaEndpointA ≤ U := by
    dsimp only [U]
    unfold yoshidaEndpointA
    linarith [YoshidaConstantBounds.strict_log_two_fine_bounds.2]
  have hL0 : 0 ≤ L := by norm_num [L]
  have hA0 : 0 ≤ yoshidaEndpointA := yoshidaEndpointA_pos.le
  have hLpow (n : ℕ) : L ^ n ≤ yoshidaEndpointA ^ n :=
    pow_le_pow_left₀ hL0 hAL n
  have hUpow (n : ℕ) : yoshidaEndpointA ^ n ≤ U ^ n :=
    pow_le_pow_left₀ hA0 hAU n
  have hc1LowerRat :
      (-827 / 1000000 : ℝ) <
        L ^ 2 / 24 + (9 / 4 : ℝ) * L ^ 3 -
          (7 / 480 : ℝ) * U ^ 4 + L ^ 5 / 8 +
          (31 / 12096 : ℝ) * L ^ 6 + (23 / 160 : ℝ) * L ^ 7 -
          1 / 10 := by
    norm_num [L, U]
  have hc1UpperRat :
      U ^ 2 / 24 + (9 / 4 : ℝ) * U ^ 3 -
          (7 / 480 : ℝ) * L ^ 4 + U ^ 5 / 8 +
          (31 / 12096 : ℝ) * U ^ 6 + (23 / 160 : ℝ) * U ^ 7 -
          1 / 10 <
        (-826 / 1000000 : ℝ) := by
    norm_num [L, U]
  have hc3LowerRat :
      (212 / 1000000 : ℝ) <
        -(7 / 5760 : ℝ) * U ^ 4 + L ^ 5 / 32 +
          (31 / 24192 : ℝ) * L ^ 6 + (23 / 192 : ℝ) * L ^ 7 := by
    norm_num [L, U]
  have hc3UpperRat :
      -(7 / 5760 : ℝ) * L ^ 4 + U ^ 5 / 32 +
          (31 / 24192 : ℝ) * U ^ 6 + (23 / 192 : ℝ) * U ^ 7 <
        (213 / 1000000 : ℝ) := by
    norm_num [L, U]
  have hc5LowerRat :
      (5 / 1000000 : ℝ) <
        (31 / 967680 : ℝ) * L ^ 6 + (23 / 2560 : ℝ) * L ^ 7 := by
    norm_num [L]
  have hc5UpperRat :
      (31 / 967680 : ℝ) * U ^ 6 + (23 / 2560 : ℝ) * U ^ 7 <
        (6 / 1000000 : ℝ) := by
    norm_num [U]
  unfold antisymmetricPolynomialCoeff1 antisymmetricPolynomialCoeff3
    antisymmetricPolynomialCoeff5
  constructor
  · calc
      (-827 / 1000000 : ℝ) ≤
          L ^ 2 / 24 + (9 / 4 : ℝ) * L ^ 3 -
            (7 / 480 : ℝ) * U ^ 4 + L ^ 5 / 8 +
            (31 / 12096 : ℝ) * L ^ 6 + (23 / 160 : ℝ) * L ^ 7 -
            1 / 10 := hc1LowerRat.le
      _ ≤ yoshidaEndpointA ^ 2 / 24 +
          (9 / 4 : ℝ) * yoshidaEndpointA ^ 3 -
          (7 / 480 : ℝ) * yoshidaEndpointA ^ 4 +
          yoshidaEndpointA ^ 5 / 8 +
          (31 / 12096 : ℝ) * yoshidaEndpointA ^ 6 +
          (23 / 160 : ℝ) * yoshidaEndpointA ^ 7 - 1 / 10 := by
        gcongr
  constructor
  · calc
      yoshidaEndpointA ^ 2 / 24 +
          (9 / 4 : ℝ) * yoshidaEndpointA ^ 3 -
          (7 / 480 : ℝ) * yoshidaEndpointA ^ 4 +
          yoshidaEndpointA ^ 5 / 8 +
          (31 / 12096 : ℝ) * yoshidaEndpointA ^ 6 +
          (23 / 160 : ℝ) * yoshidaEndpointA ^ 7 - 1 / 10 ≤
        U ^ 2 / 24 + (9 / 4 : ℝ) * U ^ 3 -
          (7 / 480 : ℝ) * L ^ 4 + U ^ 5 / 8 +
          (31 / 12096 : ℝ) * U ^ 6 + (23 / 160 : ℝ) * U ^ 7 -
          1 / 10 := by
        gcongr
      _ ≤ (-826 / 1000000 : ℝ) := hc1UpperRat.le
  constructor
  · calc
      (212 / 1000000 : ℝ) ≤
          -(7 / 5760 : ℝ) * U ^ 4 + L ^ 5 / 32 +
            (31 / 24192 : ℝ) * L ^ 6 +
            (23 / 192 : ℝ) * L ^ 7 := hc3LowerRat.le
      _ ≤ -(7 / 5760 : ℝ) * yoshidaEndpointA ^ 4 +
          yoshidaEndpointA ^ 5 / 32 +
          (31 / 24192 : ℝ) * yoshidaEndpointA ^ 6 +
          (23 / 192 : ℝ) * yoshidaEndpointA ^ 7 := by
        have h4 := hUpow 4
        have h5 := hLpow 5
        have h6 := hLpow 6
        have h7 := hLpow 7
        rw [← sub_nonneg]
        have hidentity :
            (-(7 / 5760 : ℝ) * yoshidaEndpointA ^ 4 +
                yoshidaEndpointA ^ 5 / 32 +
                (31 / 24192 : ℝ) * yoshidaEndpointA ^ 6 +
                (23 / 192 : ℝ) * yoshidaEndpointA ^ 7) -
              (-(7 / 5760 : ℝ) * U ^ 4 + L ^ 5 / 32 +
                (31 / 24192 : ℝ) * L ^ 6 +
                (23 / 192 : ℝ) * L ^ 7) =
              (7 / 5760 : ℝ) * (U ^ 4 - yoshidaEndpointA ^ 4) +
                (1 / 32 : ℝ) * (yoshidaEndpointA ^ 5 - L ^ 5) +
                (31 / 24192 : ℝ) * (yoshidaEndpointA ^ 6 - L ^ 6) +
                (23 / 192 : ℝ) * (yoshidaEndpointA ^ 7 - L ^ 7) := by
          ring
        rw [hidentity]
        have h4' : 0 ≤ U ^ 4 - yoshidaEndpointA ^ 4 :=
          sub_nonneg.mpr h4
        have h5' : 0 ≤ yoshidaEndpointA ^ 5 - L ^ 5 :=
          sub_nonneg.mpr h5
        have h6' : 0 ≤ yoshidaEndpointA ^ 6 - L ^ 6 :=
          sub_nonneg.mpr h6
        have h7' : 0 ≤ yoshidaEndpointA ^ 7 - L ^ 7 :=
          sub_nonneg.mpr h7
        exact add_nonneg
          (add_nonneg
            (add_nonneg (mul_nonneg (by norm_num) h4')
              (mul_nonneg (by norm_num) h5'))
            (mul_nonneg (by norm_num) h6'))
          (mul_nonneg (by norm_num) h7')
  constructor
  · calc
      -(7 / 5760 : ℝ) * yoshidaEndpointA ^ 4 +
          yoshidaEndpointA ^ 5 / 32 +
          (31 / 24192 : ℝ) * yoshidaEndpointA ^ 6 +
          (23 / 192 : ℝ) * yoshidaEndpointA ^ 7 ≤
        -(7 / 5760 : ℝ) * L ^ 4 + U ^ 5 / 32 +
          (31 / 24192 : ℝ) * U ^ 6 +
          (23 / 192 : ℝ) * U ^ 7 := by
        have h4 := hLpow 4
        have h5 := hUpow 5
        have h6 := hUpow 6
        have h7 := hUpow 7
        rw [← sub_nonneg]
        have hidentity :
            (-(7 / 5760 : ℝ) * L ^ 4 + U ^ 5 / 32 +
                (31 / 24192 : ℝ) * U ^ 6 +
                (23 / 192 : ℝ) * U ^ 7) -
              (-(7 / 5760 : ℝ) * yoshidaEndpointA ^ 4 +
                yoshidaEndpointA ^ 5 / 32 +
                (31 / 24192 : ℝ) * yoshidaEndpointA ^ 6 +
                (23 / 192 : ℝ) * yoshidaEndpointA ^ 7) =
              (7 / 5760 : ℝ) * (yoshidaEndpointA ^ 4 - L ^ 4) +
                (1 / 32 : ℝ) * (U ^ 5 - yoshidaEndpointA ^ 5) +
                (31 / 24192 : ℝ) * (U ^ 6 - yoshidaEndpointA ^ 6) +
                (23 / 192 : ℝ) * (U ^ 7 - yoshidaEndpointA ^ 7) := by
          ring
        rw [hidentity]
        have h4' : 0 ≤ yoshidaEndpointA ^ 4 - L ^ 4 :=
          sub_nonneg.mpr h4
        have h5' : 0 ≤ U ^ 5 - yoshidaEndpointA ^ 5 :=
          sub_nonneg.mpr h5
        have h6' : 0 ≤ U ^ 6 - yoshidaEndpointA ^ 6 :=
          sub_nonneg.mpr h6
        have h7' : 0 ≤ U ^ 7 - yoshidaEndpointA ^ 7 :=
          sub_nonneg.mpr h7
        exact add_nonneg
          (add_nonneg
            (add_nonneg (mul_nonneg (by norm_num) h4')
              (mul_nonneg (by norm_num) h5'))
            (mul_nonneg (by norm_num) h6'))
          (mul_nonneg (by norm_num) h7')
      _ ≤ (213 / 1000000 : ℝ) := hc3UpperRat.le
  constructor
  · calc
      (5 / 1000000 : ℝ) ≤
          (31 / 967680 : ℝ) * L ^ 6 +
            (23 / 2560 : ℝ) * L ^ 7 := hc5LowerRat.le
      _ ≤ (31 / 967680 : ℝ) * yoshidaEndpointA ^ 6 +
          (23 / 2560 : ℝ) * yoshidaEndpointA ^ 7 := by
        gcongr
  · calc
      (31 / 967680 : ℝ) * yoshidaEndpointA ^ 6 +
          (23 / 2560 : ℝ) * yoshidaEndpointA ^ 7 ≤
        (31 / 967680 : ℝ) * U ^ 6 + (23 / 2560 : ℝ) * U ^ 7 := by
        gcongr
      _ ≤ (6 / 1000000 : ℝ) := hc5UpperRat.le

private theorem abs_antisymmetricPolynomial_sub_linear_le
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    |oddLowAntisymmetricKernelPolynomial6 t - t / 10| ≤
      (3 / 4000 : ℝ) := by
  rcases antisymmetric_polynomial_coefficient_bounds with
    ⟨hc1Lower, hc1Upper, hc3Lower, hc3Upper, hc5Lower, hc5Upper⟩
  let d1 : ℝ := antisymmetricPolynomialCoeff1 yoshidaEndpointA - 1 / 10
  let c3 : ℝ := antisymmetricPolynomialCoeff3 yoshidaEndpointA
  let c5 : ℝ := antisymmetricPolynomialCoeff5 yoshidaEndpointA
  have hd1Lower : (-827 / 1000000 : ℝ) ≤ d1 := hc1Lower
  have hd1Upper : d1 ≤ (-826 / 1000000 : ℝ) := hc1Upper
  have hc3L : (212 / 1000000 : ℝ) ≤ c3 := hc3Lower
  have hc3U : c3 ≤ (213 / 1000000 : ℝ) := hc3Upper
  have hc5L : (5 / 1000000 : ℝ) ≤ c5 := hc5Lower
  have hc5U : c5 ≤ (6 / 1000000 : ℝ) := hc5Upper
  have ht3 : 0 ≤ t ^ 3 := pow_nonneg ht.1 3
  have ht5 : 0 ≤ t ^ 5 := pow_nonneg ht.1 5
  have htSq : t ^ 2 ≤ 4 := by
    nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
  have htCube : t ^ 3 ≤ 4 * t := by
    nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr htSq)]
  have htFourth : t ^ 4 ≤ 16 := by
    nlinarith [sq_nonneg (t ^ 2 - 4)]
  have htFifth : t ^ 5 ≤ 16 * t := by
    nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr htFourth)]
  have hformula :
      oddLowAntisymmetricKernelPolynomial6 t - t / 10 =
        d1 * t + c3 * t ^ 3 + c5 * t ^ 5 := by
    rw [oddLowAntisymmetricKernelPolynomial6_expansion]
    dsimp only [d1, c3, c5]
    ring
  have hquinticIdentity :
      (750 : ℝ) - 827 * t + 212 * t ^ 3 + 5 * t ^ 5 =
        5 * t ^ 5 +
          212 * (t - 8 / 7) ^ 2 * (t + 16 / 7) +
          (181 / 49 : ℝ) * t + 40162 / 343 := by
    ring
  have hquintic :
      0 ≤ (750 : ℝ) - 827 * t + 212 * t ^ 3 + 5 * t ^ 5 := by
    rw [hquinticIdentity]
    have htPlus : 0 ≤ t + 16 / 7 := by linarith [ht.1]
    exact add_nonneg
      (add_nonneg
        (add_nonneg (mul_nonneg (by norm_num) ht5)
          (mul_nonneg
            (mul_nonneg (by norm_num) (sq_nonneg (t - 8 / 7))) htPlus))
        (mul_nonneg (by norm_num) ht.1))
      (by norm_num)
  have hmodelLower :
      -(3 / 4000 : ℝ) ≤
        (-827 / 1000000 : ℝ) * t +
          (212 / 1000000 : ℝ) * t ^ 3 +
          (5 / 1000000 : ℝ) * t ^ 5 := by
    nlinarith
  have hd1LowerMul :
      (-827 / 1000000 : ℝ) * t ≤ d1 * t :=
    mul_le_mul_of_nonneg_right hd1Lower ht.1
  have hc3LowerMul :
      (212 / 1000000 : ℝ) * t ^ 3 ≤ c3 * t ^ 3 :=
    mul_le_mul_of_nonneg_right hc3L ht3
  have hc5LowerMul :
      (5 / 1000000 : ℝ) * t ^ 5 ≤ c5 * t ^ 5 :=
    mul_le_mul_of_nonneg_right hc5L ht5
  have hlower :
      -(3 / 4000 : ℝ) ≤ d1 * t + c3 * t ^ 3 + c5 * t ^ 5 := by
    linarith
  have hd1UpperMul :
      d1 * t ≤ (-826 / 1000000 : ℝ) * t :=
    mul_le_mul_of_nonneg_right hd1Upper ht.1
  have hc3UpperMul :
      c3 * t ^ 3 ≤ (213 / 1000000 : ℝ) * t ^ 3 :=
    mul_le_mul_of_nonneg_right hc3U ht3
  have hc5UpperMul :
      c5 * t ^ 5 ≤ (6 / 1000000 : ℝ) * t ^ 5 :=
    mul_le_mul_of_nonneg_right hc5U ht5
  have hupper :
      d1 * t + c3 * t ^ 3 + c5 * t ^ 5 ≤ (3 / 4000 : ℝ) := by
    calc
      d1 * t + c3 * t ^ 3 + c5 * t ^ 5 ≤
          (-826 / 1000000 : ℝ) * t +
            (213 / 1000000 : ℝ) * t ^ 3 +
            (6 / 1000000 : ℝ) * t ^ 5 := by
        linarith
      _ ≤ (-826 / 1000000 : ℝ) * t +
            (213 / 1000000 : ℝ) * (4 * t) +
            (6 / 1000000 : ℝ) * (16 * t) := by
        gcongr
      _ ≤ (3 / 4000 : ℝ) := by
        nlinarith [ht.2]
  rw [hformula, abs_le]
  exact ⟨hlower, hupper⟩

/-- Uniform structural enclosure of the regular antisymmetric endpoint
kernel.  The estimate uses one Taylor remainder on the whole interval and one
global quintic square identity; it has no interval subdivision or sampled
certificate. -/
theorem abs_yoshidaEndpointA_mul_factorTwoCenteredAntisymmetricRegularWeight_sub_linear_le_one_thousand
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    |yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
        t / 10| ≤ (1 / 1000 : ℝ) := by
  have ht : t ∈ Icc (0 : ℝ) 2 := ⟨ht0, ht2⟩
  have hanalytic := abs_antisymmetricKernel_sub_polynomial_lt ht
  have hpoly := abs_antisymmetricPolynomial_sub_linear_le ht
  have htriangle := abs_sub_le
    (yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t)
    (oddLowAntisymmetricKernelPolynomial6 t) (t / 10)
  have hstrict :
      |yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
          t / 10| < (1 / 1000 : ℝ) := by
    calc
      |yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
          t / 10| ≤
          |yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
            oddLowAntisymmetricKernelPolynomial6 t| +
          |oddLowAntisymmetricKernelPolynomial6 t - t / 10| := htriangle
      _ < (1 / 4000 : ℝ) + 3 / 4000 := by linarith
      _ = (1 / 1000 : ℝ) := by norm_num
  exact hstrict.le

/-- Compatibility form of the preceding sharper global estimate. -/
theorem abs_yoshidaEndpointA_mul_factorTwoCenteredAntisymmetricRegularWeight_sub_linear_le
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    |yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
        t / 10| ≤ (1 / 800 : ℝ) :=
  (abs_yoshidaEndpointA_mul_factorTwoCenteredAntisymmetricRegularWeight_sub_linear_le_one_thousand
    ht0 ht2).trans (by norm_num)

/-- On the open centered interval, the scaled antisymmetric factor-two
weight is its regular part plus the exact difference of its two dimensionless
Cauchy poles. -/
theorem yoshidaEndpointA_mul_factorTwoAntisymmetricWeight_eq_regular_poles
    {t : ℝ} (ht0 : 0 < t) (ht2 : t < 2) :
    yoshidaEndpointA *
        factorTwoAntisymmetricWeight (yoshidaEndpointA * t) =
      yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
        1 / (2 * (2 + t)) + 1 / (2 * (2 - t)) := by
  have hplus : yoshidaEndpointA * (2 + t) ≠ 0 :=
    mul_ne_zero yoshidaEndpointA_pos.ne' (by linarith)
  have hminus : yoshidaEndpointA * (2 - t) ≠ 0 :=
    mul_ne_zero yoshidaEndpointA_pos.ne' (by linarith)
  unfold factorTwoAntisymmetricWeight
  rw [factorTwoLogLength_eq_two_mul_yoshidaEndpointA]
  rw [show 2 * yoshidaEndpointA + yoshidaEndpointA * t =
        yoshidaEndpointA * (2 + t) by ring,
    show 2 * yoshidaEndpointA - yoshidaEndpointA * t =
        yoshidaEndpointA * (2 - t) by ring,
    factorTwoAdjacentSmoothKernel_eq_cosh_sub_regular_sub_pole hplus,
    factorTwoAdjacentSmoothKernel_eq_cosh_sub_regular_sub_pole hminus]
  unfold factorTwoCenteredAntisymmetricRegularWeight
  have hplus' : 2 + t ≠ 0 := by linarith
  have hminus' : 2 - t ≠ 0 := by linarith
  field_simp [yoshidaEndpointA_pos.ne', hplus', hminus']
  ring

private theorem factorTwoAdjacentSmoothKernel_log_two_eq_local :
    factorTwoAdjacentSmoothKernel (Real.log 2) =
      5 * Real.sqrt 2 / 6 := by
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hexpHalf : Real.exp (Real.log 2 / 2) = Real.sqrt 2 := by
    rw [← Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.exp_log hsqrtPos
  have hexpPos : Real.exp (Real.log 2) = 2 :=
    Real.exp_log (by norm_num)
  have hexpNeg : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
    rw [Real.exp_neg, hexpPos]
    norm_num
  have hexpNegHalf : Real.exp (-(Real.log 2 / 2)) =
      (Real.sqrt 2)⁻¹ := by
    rw [Real.exp_neg, hexpHalf]
  unfold factorTwoAdjacentSmoothKernel oddKernel
  rw [Real.cosh_eq, hexpHalf, hexpNegHalf, hexpPos, hexpNeg]
  field_simp [hsqrtPos.ne']
  nlinarith

/-- The proposed estimate for the *unregularized* weight is already
incompatible with its exact value at the center.  This records the obstruction
without any numerical sampling. -/
theorem unregularized_affine_estimate_obstruction_at_zero :
    (1 / 100 : ℝ) <
      |factorTwoSymmetricWeight (yoshidaEndpointA * 0) -
        ((16 / 15 : ℝ) + 0 / 9)| := by
  simp only [mul_zero, zero_div, add_zero]
  unfold factorTwoSymmetricWeight factorTwoLogLength
  rw [add_zero, sub_zero, factorTwoAdjacentSmoothKernel_log_two_eq_local]
  have hsqrtLower : (7 / 5 : ℝ) < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_nonneg 2]
  rw [abs_of_pos]
  · nlinarith
  · nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseOddAffineKernelEstimate
