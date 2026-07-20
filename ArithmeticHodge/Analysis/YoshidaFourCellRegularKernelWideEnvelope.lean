import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeKernel

set_option autoImplicit false

open Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellRegularKernelWideEnvelope

noncomputable section

open YoshidaEndpointHyperbolicBound
open YoshidaConstantBounds
open YoshidaRegularKernelBound
open YoshidaEndpointEvenProjectedRemainderEnvelopeKernel

/-! ### A full-width analytic regular-kernel envelope

The public sixth-order envelope used above stops at `log 2`, whereas the
four-cell argument reaches `5 log 2 / 4`.  The following Taylor argument
extends the same one-sided polynomial envelope to the larger interval
`[0, 2 log 2]`.  Its uniform error is deliberately modest; after pairing
with the exact correlation `L¹` masses it is already small enough to keep
the coupled `P₁/P₃/P₅` determinant visible. -/

private def fourCellWideCoshPolynomial6 (u : ℝ) : ℝ :=
  1 + u ^ 2 / 2 + u ^ 4 / 24 + u ^ 6 / 720

private def fourCellWideCoshUpper8 (u : ℝ) : ℝ :=
  fourCellWideCoshPolynomial6 u + (4 / 3 : ℝ) * u ^ 8 / 40320

private def fourCellWideSinhDivPolynomial6 (u : ℝ) : ℝ :=
  1 + u ^ 2 / 6 + u ^ 4 / 120 + u ^ 6 / 5040

private def fourCellWideSinhDivUpper8 (u : ℝ) : ℝ :=
  fourCellWideSinhDivPolynomial6 u + (4 / 3 : ℝ) * u ^ 8 / 362880

private def fourCellWideSechPolynomial6 (u : ℝ) : ℝ :=
  1 - u ^ 2 / 2 + 5 * u ^ 4 / 24 - 61 * u ^ 6 / 720

private def fourCellWideCschRegularPolynomial5 (u : ℝ) : ℝ :=
  -u / 6 + 7 * u ^ 3 / 360 - 31 * u ^ 5 / 15120

private def fourCellWideCschMultiplier6 (u : ℝ) : ℝ :=
  1 + u * fourCellWideCschRegularPolynomial5 u

private def fourCellWideSechError (u : ℝ) : ℝ :=
  u ^ 8 * (61 * u ^ 4 + 1680 * u ^ 2 + 17820) / 518400

private def fourCellWideCschError (u : ℝ) : ℝ :=
  u ^ 7 * (31 * u ^ 4 + 1008 * u ^ 2 + 16212) / 76204800

private theorem fourCell_cosh_lt_four_thirds
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

private theorem fourCell_wide_cosh_taylor_bounds
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u < (7 / 10 : ℝ)) :
    fourCellWideCoshPolynomial6 u ≤ Real.cosh u ∧
      Real.cosh u ≤ fourCellWideCoshUpper8 u := by
  rcases eq_or_lt_of_le hu0 with rfl | hupos
  · norm_num [fourCellWideCoshPolynomial6, fourCellWideCoshUpper8]
  · rcases taylor_mean_remainder_lagrange_iteratedDeriv
        (f := Real.cosh) (x₀ := 0) (x := u) (n := 7) hupos
        Real.contDiff_cosh.contDiffOn with ⟨w, hw, hTaylor⟩
    have hTaylorEval :
        taylorWithinEval Real.cosh 7 (Icc 0 u) 0 u =
          fourCellWideCoshPolynomial6 u := by
      have hder (n : ℕ) :
          iteratedDerivWithin n Real.cosh (Icc 0 u) 0 =
            iteratedDeriv n Real.cosh 0 :=
        Real.iteratedDerivWithin_cosh_Icc n hupos ⟨le_rfl, hu0⟩
      rw [taylor_within_apply]
      simp [hder, Finset.sum_range_succ, fourCellWideCoshPolynomial6]
      ring
    rw [hTaylorEval] at hTaylor
    norm_num [Real.iteratedDeriv_even_cosh] at hTaylor
    have hwBound : Real.cosh w < (4 / 3 : ℝ) :=
      fourCell_cosh_lt_four_thirds hw.1.le (hw.2.trans hu)
    have hrem0 : 0 ≤ Real.cosh w * u ^ 8 / 40320 := by positivity
    have hremUpper :
        Real.cosh w * u ^ 8 / 40320 ≤
          (4 / 3 : ℝ) * u ^ 8 / 40320 := by
      gcongr
    constructor
    · linarith
    · unfold fourCellWideCoshUpper8
      linarith

private theorem fourCell_wide_sinh_div_taylor_bounds
    {u : ℝ} (hu0 : 0 < u) (hu : u < (7 / 10 : ℝ)) :
    fourCellWideSinhDivPolynomial6 u ≤ Real.sinh u / u ∧
      Real.sinh u / u ≤ fourCellWideSinhDivUpper8 u := by
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
      Real.sinh u / u - fourCellWideSinhDivPolynomial6 u =
        Real.cosh w * u ^ 8 / 362880 := by
    unfold fourCellWideSinhDivPolynomial6
    rw [show Real.sinh u / u -
          (1 + u ^ 2 / 6 + u ^ 4 / 120 + u ^ 6 / 5040) =
        (Real.sinh u -
          (u + u ^ 3 / 6 + u ^ 5 / 120 + u ^ 7 / 5040)) / u by
      field_simp [hu0.ne'],
      hTaylor]
    field_simp [hu0.ne']
  have hwBound : Real.cosh w < (4 / 3 : ℝ) :=
    fourCell_cosh_lt_four_thirds hw.1.le (hw.2.trans hu)
  have hrem0 : 0 ≤ Real.cosh w * u ^ 8 / 362880 := by positivity
  have hremUpper :
      Real.cosh w * u ^ 8 / 362880 ≤
        (4 / 3 : ℝ) * u ^ 8 / 362880 := by
    gcongr
  constructor
  · linarith
  · unfold fourCellWideSinhDivUpper8
    linarith

private theorem fourCell_wide_sech_envelope
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u < (7 / 10 : ℝ)) :
    0 ≤ 1 / Real.cosh u - fourCellWideSechPolynomial6 u ∧
      1 / Real.cosh u - fourCellWideSechPolynomial6 u ≤
        fourCellWideSechError u := by
  have hTaylor := fourCell_wide_cosh_taylor_bounds hu0 hu
  have huSq : u ^ 2 < (1 / 2 : ℝ) := by
    have h := pow_lt_pow_left₀ hu hu0 (by norm_num : (2 : ℕ) ≠ 0)
    norm_num at h ⊢
    linarith
  have huSix : u ^ 6 < (1 / 2 : ℝ) ^ 3 := by
    have h := pow_lt_pow_left₀ huSq (sq_nonneg u) (by norm_num : (3 : ℕ) ≠ 0)
    simpa only [show (u ^ 2) ^ 3 = u ^ 6 by ring] using h
  have hP0 : 0 ≤ fourCellWideSechPolynomial6 u := by
    unfold fourCellWideSechPolynomial6
    have huFour0 : 0 ≤ u ^ 4 := by positivity
    nlinarith
  have hFactorUpper :
      fourCellWideSechPolynomial6 u * fourCellWideCoshUpper8 u - 1 =
        -(u ^ 8 *
          (61 * u ^ 6 + 2412 * u ^ 4 + 70920 * u ^ 2 + 747720)) /
            21772800 := by
    unfold fourCellWideSechPolynomial6 fourCellWideCoshUpper8
      fourCellWideCoshPolynomial6
    ring
  have hPCup :
      fourCellWideSechPolynomial6 u * fourCellWideCoshUpper8 u ≤ 1 := by
    rw [← sub_nonpos, hFactorUpper]
    have hnonneg : 0 ≤ u ^ 8 *
        (61 * u ^ 6 + 2412 * u ^ 4 + 70920 * u ^ 2 + 747720) := by
      positivity
    nlinarith
  have hPCosh : fourCellWideSechPolynomial6 u * Real.cosh u ≤ 1 :=
    (mul_le_mul_of_nonneg_left hTaylor.2 hP0).trans hPCup
  have hLower : 0 ≤ 1 / Real.cosh u - fourCellWideSechPolynomial6 u := by
    rw [sub_nonneg, le_div_iff₀ (Real.cosh_pos u)]
    simpa only [one_mul] using hPCosh
  constructor
  · exact hLower
  · have hIdentity :
        1 / Real.cosh u - fourCellWideSechPolynomial6 u =
          (1 - fourCellWideSechPolynomial6 u * Real.cosh u) /
            Real.cosh u := by
      field_simp [(Real.cosh_pos u).ne']
    have hNumerator0 :
        0 ≤ 1 - fourCellWideSechPolynomial6 u * Real.cosh u := by
      linarith
    have hDivide :
        (1 - fourCellWideSechPolynomial6 u * Real.cosh u) / Real.cosh u ≤
          1 - fourCellWideSechPolynomial6 u * Real.cosh u :=
      div_le_self hNumerator0 (Real.one_le_cosh u)
    have hPLower :
        fourCellWideSechPolynomial6 u * fourCellWideCoshPolynomial6 u ≤
          fourCellWideSechPolynomial6 u * Real.cosh u :=
      mul_le_mul_of_nonneg_left hTaylor.1 hP0
    have hErrorIdentity :
        1 - fourCellWideSechPolynomial6 u * fourCellWideCoshPolynomial6 u =
          fourCellWideSechError u := by
      unfold fourCellWideSechPolynomial6 fourCellWideCoshPolynomial6
        fourCellWideSechError
      ring
    rw [hIdentity]
    calc
      _ ≤ 1 - fourCellWideSechPolynomial6 u * Real.cosh u := hDivide
      _ ≤ 1 - fourCellWideSechPolynomial6 u *
          fourCellWideCoshPolynomial6 u := by nlinarith
      _ = fourCellWideSechError u := hErrorIdentity

private theorem fourCell_wide_csch_envelope
    {u : ℝ} (hu0 : 0 < u) (hu : u < (7 / 10 : ℝ)) :
    0 ≤ 1 / Real.sinh u - 1 / u - fourCellWideCschRegularPolynomial5 u ∧
      1 / Real.sinh u - 1 / u - fourCellWideCschRegularPolynomial5 u ≤
        fourCellWideCschError u := by
  let A : ℝ := Real.sinh u / u
  have hTaylorRaw := fourCell_wide_sinh_div_taylor_bounds hu0 hu
  have hTaylor :
      fourCellWideSinhDivPolynomial6 u ≤ A ∧
        A ≤ fourCellWideSinhDivUpper8 u := hTaylorRaw
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
  have hQ0 : 0 ≤ fourCellWideCschMultiplier6 u := by
    unfold fourCellWideCschMultiplier6 fourCellWideCschRegularPolynomial5
    have huFour0 : 0 ≤ u ^ 4 := by positivity
    nlinarith
  have hFactorUpper :
      fourCellWideCschMultiplier6 u * fourCellWideSinhDivUpper8 u - 1 =
        -(u ^ 8 *
          (31 * u ^ 6 + 1380 * u ^ 4 + 56952 * u ^ 2 + 860328)) /
            4115059200 := by
    unfold fourCellWideCschMultiplier6 fourCellWideCschRegularPolynomial5
      fourCellWideSinhDivUpper8 fourCellWideSinhDivPolynomial6
    ring
  have hQAup :
      fourCellWideCschMultiplier6 u * fourCellWideSinhDivUpper8 u ≤ 1 := by
    rw [← sub_nonpos, hFactorUpper]
    have hnonneg : 0 ≤ u ^ 8 *
        (31 * u ^ 6 + 1380 * u ^ 4 + 56952 * u ^ 2 + 860328) := by
      positivity
    nlinarith
  have hQA : fourCellWideCschMultiplier6 u * A ≤ 1 :=
    (mul_le_mul_of_nonneg_left hTaylor.2 hQ0).trans hQAup
  have hQleInv : fourCellWideCschMultiplier6 u ≤ 1 / A := by
    rw [le_div_iff₀ hApos]
    simpa only [one_mul] using hQA
  have hSinhPos : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu0
  have hMainIdentity :
      1 / Real.sinh u - 1 / u - fourCellWideCschRegularPolynomial5 u =
        (1 / A - fourCellWideCschMultiplier6 u) / u := by
    dsimp only [A]
    unfold fourCellWideCschMultiplier6
    field_simp [hu0.ne', hSinhPos.ne']
    ring
  have hLower :
      0 ≤ 1 / Real.sinh u - 1 / u - fourCellWideCschRegularPolynomial5 u := by
    rw [hMainIdentity]
    exact div_nonneg (sub_nonneg.mpr hQleInv) hu0.le
  constructor
  · exact hLower
  · have hInvIdentity :
        1 / A - fourCellWideCschMultiplier6 u =
          (1 - fourCellWideCschMultiplier6 u * A) / A := by
      field_simp [hApos.ne']
    have hNumerator0 : 0 ≤ 1 - fourCellWideCschMultiplier6 u * A := by
      linarith
    have hDivideA :
        (1 - fourCellWideCschMultiplier6 u * A) / A ≤
          1 - fourCellWideCschMultiplier6 u * A :=
      div_le_self hNumerator0 hA1
    have hQLower :
        fourCellWideCschMultiplier6 u * fourCellWideSinhDivPolynomial6 u ≤
          fourCellWideCschMultiplier6 u * A :=
      mul_le_mul_of_nonneg_left hTaylor.1 hQ0
    have hErrorIdentity :
        1 - fourCellWideCschMultiplier6 u * fourCellWideSinhDivPolynomial6 u =
          u * fourCellWideCschError u := by
      unfold fourCellWideCschMultiplier6 fourCellWideCschRegularPolynomial5
        fourCellWideSinhDivPolynomial6 fourCellWideCschError
      ring
    have hInner :
        1 / A - fourCellWideCschMultiplier6 u ≤
          u * fourCellWideCschError u := by
      rw [hInvIdentity]
      calc
        _ ≤ 1 - fourCellWideCschMultiplier6 u * A := hDivideA
        _ ≤ 1 - fourCellWideCschMultiplier6 u *
            fourCellWideSinhDivPolynomial6 u := by linarith
        _ = u * fourCellWideCschError u := hErrorIdentity
    rw [hMainIdentity]
    rw [div_le_iff₀ hu0]
    simpa only [div_mul_cancel₀ _ hu0.ne', mul_comm] using hInner

private theorem fourCell_yoshidaRegularKernel_two_mul_wide
    (u : ℝ) (hu : 0 < u) :
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

private theorem fourCell_yoshidaRegularKernelPolynomial6_two_mul_wide
    (u : ℝ) :
    yoshidaRegularKernelPolynomial6 (2 * u) =
      (1 / 4 : ℝ) *
        (fourCellWideSechPolynomial6 u +
          fourCellWideCschRegularPolynomial5 u) := by
  unfold yoshidaRegularKernelPolynomial6 fourCellWideSechPolynomial6
    fourCellWideCschRegularPolynomial5
  ring

/-- The sixth-order regular-kernel polynomial is a one-sided envelope on
the entire four-cell range, with a global rational error. -/
theorem fourCell_yoshidaRegularKernelPolynomial6_wide_envelope
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
    have hSech := fourCell_wide_sech_envelope hu0.le hu
    have hCsch := fourCell_wide_csch_envelope hu0 hu
    have htEq : t = 2 * u := by
      dsimp only [u]
      ring
    have hDifference :
        yoshidaRegularKernel t - yoshidaRegularKernelPolynomial6 t =
          (1 / 4 : ℝ) *
            ((1 / Real.cosh u - fourCellWideSechPolynomial6 u) +
              (1 / Real.sinh u - 1 / u -
                fourCellWideCschRegularPolynomial5 u)) := by
      rw [htEq, fourCell_yoshidaRegularKernel_two_mul_wide u hu0,
        fourCell_yoshidaRegularKernelPolynomial6_two_mul_wide]
      ring
    have hError :
        yoshidaRegularKernel t - yoshidaRegularKernelPolynomial6 t ≤
          (1 / 4 : ℝ) *
            (fourCellWideSechError u + fourCellWideCschError u) := by
      rw [hDifference]
      nlinarith
    have hSechStrict :
        fourCellWideSechError u < fourCellWideSechError (7 / 10 : ℝ) := by
      unfold fourCellWideSechError
      gcongr
    have hCschStrict :
        fourCellWideCschError u < fourCellWideCschError (7 / 10 : ℝ) := by
      unfold fourCellWideCschError
      gcongr
    have hEndpoint :
        (1 / 4 : ℝ) *
            (fourCellWideSechError (7 / 10 : ℝ) +
              fourCellWideCschError (7 / 10 : ℝ)) <
          (1 / 1900 : ℝ) := by
      norm_num [fourCellWideSechError, fourCellWideCschError]
    constructor
    · rw [hDifference]
      nlinarith [hSech.1, hCsch.1]
    · exact hError.trans_lt <| by
        have :
            (1 / 4 : ℝ) *
                (fourCellWideSechError u + fourCellWideCschError u) <
              (1 / 4 : ℝ) *
                (fourCellWideSechError (7 / 10 : ℝ) +
                  fourCellWideCschError (7 / 10 : ℝ)) := by
          nlinarith
        exact this.trans hEndpoint

end

end ArithmeticHodge.Analysis.YoshidaFourCellRegularKernelWideEnvelope

