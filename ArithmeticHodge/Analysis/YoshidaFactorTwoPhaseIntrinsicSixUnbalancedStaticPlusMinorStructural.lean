import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4P3AlternatingSharpStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourC2Structural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusPositiveStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusMinorStructural

noncomputable section

open MeasureTheory Real Set
open CenteredEndpointCorrelation
open ThreeByThreeRankOneSchur
open YoshidaConstantBounds
open YoshidaEndpointEvenExactLowGramPositive
open YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseIntrinsicEvenCleanSharp
open YoshidaFactorTwoPhaseIntrinsicEvenLowEndpointPositive
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicEvenNegativePerturbationSharp
open YoshidaFactorTwoPhaseIntrinsicEvenPositiveEndpointLoewnerUltraSharp
open YoshidaFactorTwoPhaseIntrinsicEvenPositiveEndpointSharp
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicLowAlternatingKernelSharp
open YoshidaFactorTwoPhaseIntrinsicLowControlStep01MidpointReserve
open YoshidaFactorTwoPhaseIntrinsicLowControlStep23EvenSlopeStructural
open YoshidaFactorTwoPhaseIntrinsicLowStaticMinusRationalSchur
open YoshidaFactorTwoPhaseIntrinsicSixP4CleanDiagonalStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4P1AlternatingStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4PlusEndpointExactSchur
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4P3AlternatingSharpStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveP4PivotSecondSharpStructural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourC2Structural
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFiveOddMinorStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticEvenPositiveStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusPositiveStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticSchurReductionStructural
open YoshidaFactorTwoPhaseOddAffineKernelEstimate
open YoshidaFactorTwoPhaseSymmetricCarleman
open YoshidaFactorTwoPhaseLowSchur
open YoshidaRegularKernelBound

/-!
# The second positive static Schur gate

The odd basis is sheared from `(P₁, P₃)` to
`(P₁, P₃ - (25 / 24) P₁)`.  In this basis the polarized
fraction-free cross is tiny, while the determinant is unchanged.  The proof
below keeps this cancellation before applying any rational estimates.
-/

/-! ## An integrated analytic remainder

The earlier even lower Gram charges the maximum degree-six Taylor error at
every translation.  Here the same global Taylor envelope is integrated in
the translation variable before it is charged to the profile energy.  This
is a single interval estimate, with no subdivision or sampling.
-/

private def minorWideCoshPolynomial6 (u : ℝ) : ℝ :=
  1 + u ^ 2 / 2 + u ^ 4 / 24 + u ^ 6 / 720

private def minorWideCoshUpper8 (u : ℝ) : ℝ :=
  minorWideCoshPolynomial6 u + (4 / 3 : ℝ) * u ^ 8 / 40320

private def minorWideSinhDivPolynomial6 (u : ℝ) : ℝ :=
  1 + u ^ 2 / 6 + u ^ 4 / 120 + u ^ 6 / 5040

private def minorWideSinhDivUpper8 (u : ℝ) : ℝ :=
  minorWideSinhDivPolynomial6 u + (4 / 3 : ℝ) * u ^ 8 / 362880

private def minorWideSechPolynomial6 (u : ℝ) : ℝ :=
  1 - u ^ 2 / 2 + 5 * u ^ 4 / 24 - 61 * u ^ 6 / 720

private def minorWideCschRegularPolynomial5 (u : ℝ) : ℝ :=
  -u / 6 + 7 * u ^ 3 / 360 - 31 * u ^ 5 / 15120

private def minorWideCschMultiplier6 (u : ℝ) : ℝ :=
  1 + u * minorWideCschRegularPolynomial5 u

private def minorWideSechError (u : ℝ) : ℝ :=
  u ^ 8 * (61 * u ^ 4 + 1680 * u ^ 2 + 17820) / 518400

private def minorWideCschError (u : ℝ) : ℝ :=
  u ^ 7 * (31 * u ^ 4 + 1008 * u ^ 2 + 16212) / 76204800

private def minorCoshError (u : ℝ) : ℝ :=
  (4 / 3 : ℝ) * u ^ 8 / 40320

private def minorRegularError (u : ℝ) : ℝ :=
  (minorWideSechError u + minorWideCschError u) / 4

/-- The pointwise degree-six remainder envelope used after the symmetric
translation variables have been halved. -/
def integratedPoleFreeEnvelope (u : ℝ) : ℝ :=
  2 * minorCoshError u + minorRegularError u

/-- The translation-integrated pole-free remainder weight.  It is global on
the full interval and does not use subdivision or sampled values. -/
def integratedPoleFreeWeight (t : ℝ) : ℝ :=
  yoshidaEndpointA *
    (integratedPoleFreeEnvelope (yoshidaEndpointA * (2 + t) / 2) +
      integratedPoleFreeEnvelope (yoshidaEndpointA * (2 - t) / 2))

private theorem minor_cosh_lt_four_thirds
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

private theorem minor_wide_cosh_taylor_bounds
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u < (7 / 10 : ℝ)) :
    minorWideCoshPolynomial6 u ≤ Real.cosh u ∧
      Real.cosh u ≤ minorWideCoshUpper8 u := by
  rcases eq_or_lt_of_le hu0 with rfl | hupos
  · norm_num [minorWideCoshPolynomial6, minorWideCoshUpper8]
  · rcases taylor_mean_remainder_lagrange_iteratedDeriv
        (f := Real.cosh) (x₀ := 0) (x := u) (n := 7) hupos
        Real.contDiff_cosh.contDiffOn with ⟨w, hw, hTaylor⟩
    have hTaylorEval :
        taylorWithinEval Real.cosh 7 (Icc 0 u) 0 u =
          minorWideCoshPolynomial6 u := by
      have hder (n : ℕ) :
          iteratedDerivWithin n Real.cosh (Icc 0 u) 0 =
            iteratedDeriv n Real.cosh 0 :=
        Real.iteratedDerivWithin_cosh_Icc n hupos ⟨le_rfl, hu0⟩
      rw [taylor_within_apply]
      simp [hder, Finset.sum_range_succ, minorWideCoshPolynomial6]
      ring
    rw [hTaylorEval] at hTaylor
    norm_num [Real.iteratedDeriv_even_cosh] at hTaylor
    have hwBound : Real.cosh w < (4 / 3 : ℝ) :=
      minor_cosh_lt_four_thirds hw.1.le (hw.2.trans hu)
    have hrem0 : 0 ≤ Real.cosh w * u ^ 8 / 40320 := by positivity
    have hremUpper :
        Real.cosh w * u ^ 8 / 40320 ≤
          (4 / 3 : ℝ) * u ^ 8 / 40320 := by
      gcongr
    constructor
    · linarith
    · unfold minorWideCoshUpper8
      linarith

private theorem minor_wide_sinh_div_taylor_bounds
    {u : ℝ} (hu0 : 0 < u) (hu : u < (7 / 10 : ℝ)) :
    minorWideSinhDivPolynomial6 u ≤ Real.sinh u / u ∧
      Real.sinh u / u ≤ minorWideSinhDivUpper8 u := by
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
      Real.sinh u / u - minorWideSinhDivPolynomial6 u =
        Real.cosh w * u ^ 8 / 362880 := by
    unfold minorWideSinhDivPolynomial6
    rw [show Real.sinh u / u -
          (1 + u ^ 2 / 6 + u ^ 4 / 120 + u ^ 6 / 5040) =
        (Real.sinh u -
          (u + u ^ 3 / 6 + u ^ 5 / 120 + u ^ 7 / 5040)) / u by
      field_simp [hu0.ne'],
      hTaylor]
    field_simp [hu0.ne']
  have hwBound : Real.cosh w < (4 / 3 : ℝ) :=
    minor_cosh_lt_four_thirds hw.1.le (hw.2.trans hu)
  have hrem0 : 0 ≤ Real.cosh w * u ^ 8 / 362880 := by positivity
  have hremUpper :
      Real.cosh w * u ^ 8 / 362880 ≤
        (4 / 3 : ℝ) * u ^ 8 / 362880 := by
    gcongr
  constructor
  · linarith
  · unfold minorWideSinhDivUpper8
    linarith

private theorem minor_wide_sech_envelope
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u < (7 / 10 : ℝ)) :
    0 ≤ 1 / Real.cosh u - minorWideSechPolynomial6 u ∧
      1 / Real.cosh u - minorWideSechPolynomial6 u ≤
        minorWideSechError u := by
  have hTaylor := minor_wide_cosh_taylor_bounds hu0 hu
  have huSq : u ^ 2 < (1 / 2 : ℝ) := by
    have h := pow_lt_pow_left₀ hu hu0 (by norm_num : (2 : ℕ) ≠ 0)
    norm_num at h ⊢
    linarith
  have huSix : u ^ 6 < (1 / 2 : ℝ) ^ 3 := by
    have h := pow_lt_pow_left₀ huSq (sq_nonneg u) (by norm_num : (3 : ℕ) ≠ 0)
    simpa only [show (u ^ 2) ^ 3 = u ^ 6 by ring] using h
  have hP0 : 0 ≤ minorWideSechPolynomial6 u := by
    unfold minorWideSechPolynomial6
    have huFour0 : 0 ≤ u ^ 4 := by positivity
    nlinarith
  have hFactorUpper :
      minorWideSechPolynomial6 u * minorWideCoshUpper8 u - 1 =
        -(u ^ 8 *
          (61 * u ^ 6 + 2412 * u ^ 4 + 70920 * u ^ 2 + 747720)) /
            21772800 := by
    unfold minorWideSechPolynomial6 minorWideCoshUpper8
      minorWideCoshPolynomial6
    ring
  have hPCup : minorWideSechPolynomial6 u * minorWideCoshUpper8 u ≤ 1 := by
    rw [← sub_nonpos, hFactorUpper]
    have hnonneg : 0 ≤ u ^ 8 *
        (61 * u ^ 6 + 2412 * u ^ 4 + 70920 * u ^ 2 + 747720) := by
      positivity
    nlinarith
  have hPCosh : minorWideSechPolynomial6 u * Real.cosh u ≤ 1 :=
    (mul_le_mul_of_nonneg_left hTaylor.2 hP0).trans hPCup
  have hLower : 0 ≤ 1 / Real.cosh u - minorWideSechPolynomial6 u := by
    rw [sub_nonneg, le_div_iff₀ (Real.cosh_pos u)]
    simpa only [one_mul] using hPCosh
  constructor
  · exact hLower
  · have hIdentity :
        1 / Real.cosh u - minorWideSechPolynomial6 u =
          (1 - minorWideSechPolynomial6 u * Real.cosh u) /
            Real.cosh u := by
      field_simp [(Real.cosh_pos u).ne']
    have hNumerator0 :
        0 ≤ 1 - minorWideSechPolynomial6 u * Real.cosh u := by
      linarith
    have hDivide :
        (1 - minorWideSechPolynomial6 u * Real.cosh u) / Real.cosh u ≤
          1 - minorWideSechPolynomial6 u * Real.cosh u :=
      div_le_self hNumerator0 (Real.one_le_cosh u)
    have hPLower :
        minorWideSechPolynomial6 u * minorWideCoshPolynomial6 u ≤
          minorWideSechPolynomial6 u * Real.cosh u :=
      mul_le_mul_of_nonneg_left hTaylor.1 hP0
    have hErrorIdentity :
        1 - minorWideSechPolynomial6 u * minorWideCoshPolynomial6 u =
          minorWideSechError u := by
      unfold minorWideSechPolynomial6 minorWideCoshPolynomial6
        minorWideSechError
      ring
    rw [hIdentity]
    calc
      _ ≤ 1 - minorWideSechPolynomial6 u * Real.cosh u := hDivide
      _ ≤ 1 - minorWideSechPolynomial6 u * minorWideCoshPolynomial6 u := by
        nlinarith
      _ = minorWideSechError u := hErrorIdentity

private theorem minor_wide_csch_envelope
    {u : ℝ} (hu0 : 0 < u) (hu : u < (7 / 10 : ℝ)) :
    0 ≤ 1 / Real.sinh u - 1 / u - minorWideCschRegularPolynomial5 u ∧
      1 / Real.sinh u - 1 / u - minorWideCschRegularPolynomial5 u ≤
        minorWideCschError u := by
  let A : ℝ := Real.sinh u / u
  have hTaylorRaw := minor_wide_sinh_div_taylor_bounds hu0 hu
  have hTaylor :
      minorWideSinhDivPolynomial6 u ≤ A ∧
        A ≤ minorWideSinhDivUpper8 u := hTaylorRaw
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
  have hQ0 : 0 ≤ minorWideCschMultiplier6 u := by
    unfold minorWideCschMultiplier6 minorWideCschRegularPolynomial5
    have huFour0 : 0 ≤ u ^ 4 := by positivity
    nlinarith
  have hFactorUpper :
      minorWideCschMultiplier6 u * minorWideSinhDivUpper8 u - 1 =
        -(u ^ 8 *
          (31 * u ^ 6 + 1380 * u ^ 4 + 56952 * u ^ 2 + 860328)) /
            4115059200 := by
    unfold minorWideCschMultiplier6 minorWideCschRegularPolynomial5
      minorWideSinhDivUpper8 minorWideSinhDivPolynomial6
    ring
  have hQAup : minorWideCschMultiplier6 u * minorWideSinhDivUpper8 u ≤ 1 := by
    rw [← sub_nonpos, hFactorUpper]
    have hnonneg : 0 ≤ u ^ 8 *
        (31 * u ^ 6 + 1380 * u ^ 4 + 56952 * u ^ 2 + 860328) := by
      positivity
    nlinarith
  have hQA : minorWideCschMultiplier6 u * A ≤ 1 :=
    (mul_le_mul_of_nonneg_left hTaylor.2 hQ0).trans hQAup
  have hQleInv : minorWideCschMultiplier6 u ≤ 1 / A := by
    rw [le_div_iff₀ hApos]
    simpa only [one_mul] using hQA
  have hSinhPos : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu0
  have hMainIdentity :
      1 / Real.sinh u - 1 / u - minorWideCschRegularPolynomial5 u =
        (1 / A - minorWideCschMultiplier6 u) / u := by
    dsimp only [A]
    unfold minorWideCschMultiplier6
    field_simp [hu0.ne', hSinhPos.ne']
    ring
  have hLower :
      0 ≤ 1 / Real.sinh u - 1 / u - minorWideCschRegularPolynomial5 u := by
    rw [hMainIdentity]
    exact div_nonneg (sub_nonneg.mpr hQleInv) hu0.le
  constructor
  · exact hLower
  · have hInvIdentity :
        1 / A - minorWideCschMultiplier6 u =
          (1 - minorWideCschMultiplier6 u * A) / A := by
      field_simp [hApos.ne']
    have hNumerator0 : 0 ≤ 1 - minorWideCschMultiplier6 u * A := by
      linarith
    have hDivideA :
        (1 - minorWideCschMultiplier6 u * A) / A ≤
          1 - minorWideCschMultiplier6 u * A :=
      div_le_self hNumerator0 hA1
    have hQLower :
        minorWideCschMultiplier6 u * minorWideSinhDivPolynomial6 u ≤
          minorWideCschMultiplier6 u * A :=
      mul_le_mul_of_nonneg_left hTaylor.1 hQ0
    have hErrorIdentity :
        1 - minorWideCschMultiplier6 u * minorWideSinhDivPolynomial6 u =
          u * minorWideCschError u := by
      unfold minorWideCschMultiplier6 minorWideCschRegularPolynomial5
        minorWideSinhDivPolynomial6 minorWideCschError
      ring
    have hInner :
        1 / A - minorWideCschMultiplier6 u ≤
          u * minorWideCschError u := by
      rw [hInvIdentity]
      calc
        _ ≤ 1 - minorWideCschMultiplier6 u * A := hDivideA
        _ ≤ 1 - minorWideCschMultiplier6 u * minorWideSinhDivPolynomial6 u := by
          nlinarith
        _ = u * minorWideCschError u := hErrorIdentity
    rw [hMainIdentity]
    rw [div_le_iff₀ hu0]
    simpa only [div_mul_cancel₀ _ hu0.ne', mul_comm] using hInner

private theorem minor_yoshidaRegularKernel_two_mul_wide
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

private theorem minor_yoshidaRegularKernelPolynomial6_two_mul_wide
    (u : ℝ) :
    yoshidaRegularKernelPolynomial6 (2 * u) =
      (1 / 4 : ℝ) *
        (minorWideSechPolynomial6 u +
          minorWideCschRegularPolynomial5 u) := by
  unfold yoshidaRegularKernelPolynomial6 minorWideSechPolynomial6
    minorWideCschRegularPolynomial5
  ring

private theorem minor_regularKernel_weighted_envelope
    {t : ℝ} (ht0 : 0 ≤ t) (htlog : t ≤ 2 * Real.log 2) :
    0 ≤ yoshidaRegularKernel t - yoshidaRegularKernelPolynomial6 t ∧
      yoshidaRegularKernel t - yoshidaRegularKernelPolynomial6 t ≤
        minorRegularError (t / 2) := by
  rcases eq_or_lt_of_le ht0 with rfl | htpos
  · constructor <;>
      norm_num [yoshidaRegularKernel, yoshidaRegularKernelPolynomial6,
        minorRegularError, minorWideSechError, minorWideCschError]
  · let u : ℝ := t / 2
    have hu0 : 0 < u := by
      dsimp only [u]
      linarith
    have hu : u < (7 / 10 : ℝ) := by
      dsimp only [u]
      have hlog := strict_log_two_bounds.2
      linarith
    have hSech := minor_wide_sech_envelope hu0.le hu
    have hCsch := minor_wide_csch_envelope hu0 hu
    have htEq : t = 2 * u := by
      dsimp only [u]
      ring
    have hDifference :
        yoshidaRegularKernel t - yoshidaRegularKernelPolynomial6 t =
          (1 / 4 : ℝ) *
            ((1 / Real.cosh u - minorWideSechPolynomial6 u) +
              (1 / Real.sinh u - 1 / u -
                minorWideCschRegularPolynomial5 u)) := by
      rw [htEq, minor_yoshidaRegularKernel_two_mul_wide u hu0,
        minor_yoshidaRegularKernelPolynomial6_two_mul_wide]
      ring
    rw [hDifference]
    constructor
    · nlinarith [hSech.1, hCsch.1]
    · have hsum :
          (1 / Real.cosh u - minorWideSechPolynomial6 u) +
              (1 / Real.sinh u - 1 / u -
                minorWideCschRegularPolynomial5 u) ≤
            minorWideSechError u + minorWideCschError u := by
        linarith [hSech.2, hCsch.2]
      dsimp only [minorRegularError]
      rw [show t / 2 = u by rfl]
      nlinarith

private theorem minor_poleFreeKernel_weighted_envelope
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    |oddLowPoleFreeKernel t - poleFreeKernelPolynomial6 t| ≤
      yoshidaEndpointA *
        (integratedPoleFreeEnvelope
            (yoshidaEndpointA * (2 + t) / 2) +
          integratedPoleFreeEnvelope
            (yoshidaEndpointA * (2 - t) / 2)) := by
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
  have hcp := minor_wide_cosh_taylor_bounds hzp0 hzp
  have hcm := minor_wide_cosh_taylor_bounds hzm0 hzm
  have hrp := minor_regularKernel_weighted_envelope hup0 hupLog
  have hrm := minor_regularKernel_weighted_envelope hum0 humLog
  let ecp : ℝ := Real.cosh zp - minorWideCoshPolynomial6 zp
  let ecm : ℝ := Real.cosh zm - minorWideCoshPolynomial6 zm
  let erp : ℝ := yoshidaRegularKernel up -
    yoshidaRegularKernelPolynomial6 up
  let erm : ℝ := yoshidaRegularKernel um -
    yoshidaRegularKernelPolynomial6 um
  have hecp0 : 0 ≤ ecp := by
    dsimp only [ecp]
    linarith [hcp.1]
  have hecm0 : 0 ≤ ecm := by
    dsimp only [ecm]
    linarith [hcm.1]
  have hecpE : ecp ≤ minorCoshError zp := by
    dsimp only [ecp, minorCoshError]
    unfold minorWideCoshUpper8 at hcp
    linarith
  have hecmE : ecm ≤ minorCoshError zm := by
    dsimp only [ecm, minorCoshError]
    unfold minorWideCoshUpper8 at hcm
    linarith
  have herp0 : 0 ≤ erp := by simpa only [erp] using hrp.1
  have herm0 : 0 ≤ erm := by simpa only [erm] using hrm.1
  have herpE : erp ≤ minorRegularError zp := by
    have hz : up / 2 = zp := by rfl
    simpa only [erp, hz] using hrp.2
  have hermE : erm ≤ minorRegularError zm := by
    have hz : um / 2 = zm := by rfl
    simpa only [erm, hz] using hrm.2
  have hpPoly :
      yoshidaRegularKernelPolynomial6 up =
        (1 / 4 : ℝ) *
          (minorWideSechPolynomial6 zp +
            minorWideCschRegularPolynomial5 zp) := by
    rw [show up = 2 * zp by dsimp only [zp]; ring,
      minor_yoshidaRegularKernelPolynomial6_two_mul_wide]
  have hmPoly :
      yoshidaRegularKernelPolynomial6 um =
        (1 / 4 : ℝ) *
          (minorWideSechPolynomial6 zm +
            minorWideCschRegularPolynomial5 zm) := by
    rw [show um = 2 * zm by dsimp only [zm]; ring,
      minor_yoshidaRegularKernelPolynomial6_two_mul_wide]
  have hdiff :
      oddLowPoleFreeKernel t - poleFreeKernelPolynomial6 t =
        yoshidaEndpointA * (2 * ecp + 2 * ecm - erp - erm) := by
    rw [poleFreeKernelPolynomial6_expansion]
    dsimp only [oddLowPoleFreeKernel,
      factorTwoCenteredSymmetricRegularWeight, up, um, zp, zm,
      ecp, ecm, erp, erm]
    rw [hpPoly, hmPoly]
    unfold minorWideCoshPolynomial6 minorWideSechPolynomial6
      minorWideCschRegularPolynomial5 poleFreeCoeff0 poleFreeCoeff2
      poleFreeCoeff4 poleFreeCoeff6
    dsimp only [zp, zm, up, um]
    ring_nf
  have hinside :
      |2 * ecp + 2 * ecm - erp - erm| ≤
        integratedPoleFreeEnvelope zp + integratedPoleFreeEnvelope zm := by
    rw [abs_le]
    unfold integratedPoleFreeEnvelope
    constructor
    · have hnonneg :
          0 ≤ minorCoshError zp ∧ 0 ≤ minorCoshError zm ∧
            0 ≤ minorRegularError zp ∧ 0 ≤ minorRegularError zm := by
        unfold minorCoshError minorRegularError minorWideSechError
          minorWideCschError
        constructor
        · positivity
        constructor
        · positivity
        constructor <;> positivity
      nlinarith
    · nlinarith
  rw [hdiff, abs_mul, abs_of_pos yoshidaEndpointA_pos]
  exact mul_le_mul_of_nonneg_left hinside yoshidaEndpointA_pos.le

/-- The two-copy degree-eight `cosh` remainder charged to one translated
endpoint in the joint symmetric/alternating kernel estimate. -/
def jointCoshEnvelope (u : ℝ) : ℝ :=
  u ^ 8 / 15120

/-- The regular-kernel part of the pole-free envelope at one translated
endpoint. -/
def jointRegularEnvelope (u : ℝ) : ℝ :=
  integratedPoleFreeEnvelope u - jointCoshEnvelope u

theorem jointCoshEnvelope_nonneg (u : ℝ) :
    0 ≤ jointCoshEnvelope u := by
  unfold jointCoshEnvelope
  positivity

private theorem jointCoshEnvelope_eq_two_minorCoshError (u : ℝ) :
    jointCoshEnvelope u = 2 * minorCoshError u := by
  unfold jointCoshEnvelope minorCoshError
  ring

private theorem jointRegularEnvelope_eq_minorRegularError (u : ℝ) :
    jointRegularEnvelope u = minorRegularError u := by
  unfold jointRegularEnvelope integratedPoleFreeEnvelope
  rw [jointCoshEnvelope_eq_two_minorCoshError]
  ring

theorem jointRegularEnvelope_nonneg
    {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ jointRegularEnvelope u := by
  rw [jointRegularEnvelope_eq_minorRegularError]
  unfold minorRegularError minorWideSechError minorWideCschError
  positivity

theorem integratedPoleFreeEnvelope_eq_jointEnvelope (u : ℝ) :
    integratedPoleFreeEnvelope u =
      jointCoshEnvelope u + jointRegularEnvelope u := by
  unfold jointRegularEnvelope
  ring

private theorem minor_jointKernelError_decomposition
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    ∃ ecp ecm erp erm : ℝ,
      0 ≤ ecp ∧ 0 ≤ ecm ∧ 0 ≤ erp ∧ 0 ≤ erm ∧
      2 * ecp ≤ jointCoshEnvelope
        (yoshidaEndpointA * (2 + t) / 2) ∧
      2 * ecm ≤ jointCoshEnvelope
        (yoshidaEndpointA * (2 - t) / 2) ∧
      erp ≤ jointRegularEnvelope
        (yoshidaEndpointA * (2 + t) / 2) ∧
      erm ≤ jointRegularEnvelope
        (yoshidaEndpointA * (2 - t) / 2) ∧
      oddLowPoleFreeKernel t - poleFreeKernelPolynomial6 t =
        yoshidaEndpointA * (2 * ecp + 2 * ecm - erp - erm) ∧
      yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
          intrinsicAlternatingKernelPolynomial6 t =
        yoshidaEndpointA * (2 * ecp - 2 * ecm - erp + erm) := by
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
  have hcp := minor_wide_cosh_taylor_bounds hzp0 hzp
  have hcm := minor_wide_cosh_taylor_bounds hzm0 hzm
  have hrp := minor_regularKernel_weighted_envelope hup0 hupLog
  have hrm := minor_regularKernel_weighted_envelope hum0 humLog
  let ecp : ℝ := Real.cosh zp - minorWideCoshPolynomial6 zp
  let ecm : ℝ := Real.cosh zm - minorWideCoshPolynomial6 zm
  let erp : ℝ := yoshidaRegularKernel up -
    yoshidaRegularKernelPolynomial6 up
  let erm : ℝ := yoshidaRegularKernel um -
    yoshidaRegularKernelPolynomial6 um
  have hecp0 : 0 ≤ ecp := by
    dsimp only [ecp]
    linarith [hcp.1]
  have hecm0 : 0 ≤ ecm := by
    dsimp only [ecm]
    linarith [hcm.1]
  have hecpE : ecp ≤ minorCoshError zp := by
    dsimp only [ecp, minorCoshError]
    unfold minorWideCoshUpper8 at hcp
    linarith
  have hecmE : ecm ≤ minorCoshError zm := by
    dsimp only [ecm, minorCoshError]
    unfold minorWideCoshUpper8 at hcm
    linarith
  have herp0 : 0 ≤ erp := by simpa only [erp] using hrp.1
  have herm0 : 0 ≤ erm := by simpa only [erm] using hrm.1
  have herpE : erp ≤ minorRegularError zp := by
    have hz : up / 2 = zp := by rfl
    simpa only [erp, hz] using hrp.2
  have hermE : erm ≤ minorRegularError zm := by
    have hz : um / 2 = zm := by rfl
    simpa only [erm, hz] using hrm.2
  have hecpJ : 2 * ecp ≤ jointCoshEnvelope zp := by
    rw [jointCoshEnvelope_eq_two_minorCoshError]
    exact mul_le_mul_of_nonneg_left hecpE (by norm_num)
  have hecmJ : 2 * ecm ≤ jointCoshEnvelope zm := by
    rw [jointCoshEnvelope_eq_two_minorCoshError]
    exact mul_le_mul_of_nonneg_left hecmE (by norm_num)
  have herpJ : erp ≤ jointRegularEnvelope zp := by
    rwa [jointRegularEnvelope_eq_minorRegularError]
  have hermJ : erm ≤ jointRegularEnvelope zm := by
    rwa [jointRegularEnvelope_eq_minorRegularError]
  have hpPoly :
      yoshidaRegularKernelPolynomial6 up =
        (1 / 4 : ℝ) *
          (minorWideSechPolynomial6 zp +
            minorWideCschRegularPolynomial5 zp) := by
    rw [show up = 2 * zp by dsimp only [zp]; ring,
      minor_yoshidaRegularKernelPolynomial6_two_mul_wide]
  have hmPoly :
      yoshidaRegularKernelPolynomial6 um =
        (1 / 4 : ℝ) *
          (minorWideSechPolynomial6 zm +
            minorWideCschRegularPolynomial5 zm) := by
    rw [show um = 2 * zm by dsimp only [zm]; ring,
      minor_yoshidaRegularKernelPolynomial6_two_mul_wide]
  have hsymm :
      oddLowPoleFreeKernel t - poleFreeKernelPolynomial6 t =
        yoshidaEndpointA * (2 * ecp + 2 * ecm - erp - erm) := by
    rw [poleFreeKernelPolynomial6_expansion]
    dsimp only [oddLowPoleFreeKernel,
      factorTwoCenteredSymmetricRegularWeight, up, um, zp, zm,
      ecp, ecm, erp, erm]
    rw [hpPoly, hmPoly]
    unfold minorWideCoshPolynomial6 minorWideSechPolynomial6
      minorWideCschRegularPolynomial5 poleFreeCoeff0 poleFreeCoeff2
      poleFreeCoeff4 poleFreeCoeff6
    dsimp only [zp, zm, up, um]
    ring_nf
  have halt :
      yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
          intrinsicAlternatingKernelPolynomial6 t =
        yoshidaEndpointA * (2 * ecp - 2 * ecm - erp + erm) := by
    rw [intrinsicAlternatingKernelPolynomial6_expansion]
    dsimp only [factorTwoCenteredAntisymmetricRegularWeight, up, um, zp, zm,
      ecp, ecm, erp, erm]
    rw [hpPoly, hmPoly]
    unfold minorWideCoshPolynomial6 minorWideSechPolynomial6
      minorWideCschRegularPolynomial5 intrinsicAlternatingKernelCoeff1
      intrinsicAlternatingKernelCoeff3 intrinsicAlternatingKernelCoeff5
    dsimp only [zp, zm, up, um]
    ring_nf
  refine ⟨ecp, ecm, erp, erm, hecp0, hecm0, herp0, herm0, ?_, ?_,
    ?_, ?_, hsymm, halt⟩
  · simpa only [zp, up] using hecpJ
  · simpa only [zm, um] using hecmJ
  · simpa only [zp, up] using herpJ
  · simpa only [zm, um] using hermJ

/-- A pointwise joint error bound which preserves the cancellation between
the symmetric and alternating correlation profiles. -/
theorem abs_jointSymmetricAlternatingKernelError_le
    (Ce Ca : ℝ → ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    |(oddLowPoleFreeKernel t - poleFreeKernelPolynomial6 t) * Ce t +
        (yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
          intrinsicAlternatingKernelPolynomial6 t) * Ca t| ≤
      yoshidaEndpointA *
        (integratedPoleFreeEnvelope
            (yoshidaEndpointA * (2 + t) / 2) * |Ce t + Ca t| +
          integratedPoleFreeEnvelope
            (yoshidaEndpointA * (2 - t) / 2) * |Ce t - Ca t|) := by
  rcases minor_jointKernelError_decomposition ht with
    ⟨ecp, ecm, erp, erm, hecp0, hecm0, herp0, herm0,
      hecpE, hecmE, herpE, hermE, hsymm, halt⟩
  let zp : ℝ := yoshidaEndpointA * (2 + t) / 2
  let zm : ℝ := yoshidaEndpointA * (2 - t) / 2
  have hzp0 : 0 ≤ zp := by
    dsimp only [zp]
    exact div_nonneg
      (mul_nonneg yoshidaEndpointA_pos.le (by linarith [ht.1])) (by norm_num)
  have hzm0 : 0 ≤ zm := by
    dsimp only [zm]
    exact div_nonneg
      (mul_nonneg yoshidaEndpointA_pos.le (by linarith [ht.2])) (by norm_num)
  have hecpE' : 2 * ecp ≤ jointCoshEnvelope zp := by
    simpa only [zp] using hecpE
  have hecmE' : 2 * ecm ≤ jointCoshEnvelope zm := by
    simpa only [zm] using hecmE
  have herpE' : erp ≤ jointRegularEnvelope zp := by
    simpa only [zp] using herpE
  have hermE' : erm ≤ jointRegularEnvelope zm := by
    simpa only [zm] using hermE
  have hpabs :
      |2 * ecp - erp| ≤ integratedPoleFreeEnvelope zp := by
    rw [integratedPoleFreeEnvelope_eq_jointEnvelope, abs_le]
    constructor <;>
      nlinarith [jointCoshEnvelope_nonneg zp,
        jointRegularEnvelope_nonneg hzp0]
  have hmabs :
      |2 * ecm - erm| ≤ integratedPoleFreeEnvelope zm := by
    rw [integratedPoleFreeEnvelope_eq_jointEnvelope, abs_le]
    constructor <;>
      nlinarith [jointCoshEnvelope_nonneg zm,
        jointRegularEnvelope_nonneg hzm0]
  have hshared :
      (oddLowPoleFreeKernel t - poleFreeKernelPolynomial6 t) * Ce t +
          (yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
            intrinsicAlternatingKernelPolynomial6 t) * Ca t =
        yoshidaEndpointA *
          ((2 * ecp - erp) * (Ce t + Ca t) +
            (2 * ecm - erm) * (Ce t - Ca t)) := by
    rw [hsymm, halt]
    ring
  have htriangle :
      |(2 * ecp - erp) * (Ce t + Ca t) +
          (2 * ecm - erm) * (Ce t - Ca t)| ≤
        |2 * ecp - erp| * |Ce t + Ca t| +
          |2 * ecm - erm| * |Ce t - Ca t| := by
    calc
      _ ≤ |(2 * ecp - erp) * (Ce t + Ca t)| +
          |(2 * ecm - erm) * (Ce t - Ca t)| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul]
  rw [hshared, abs_mul, abs_of_pos yoshidaEndpointA_pos]
  apply mul_le_mul_of_nonneg_left _ yoshidaEndpointA_pos.le
  exact htriangle.trans (add_le_add
    (mul_le_mul_of_nonneg_right hpabs (abs_nonneg _))
    (mul_le_mul_of_nonneg_right hmabs (abs_nonneg _)))

/-- A signed joint lower bound.  Positive profile parts are charged only to
the regular error, while negative profile parts are charged only to the
degree-eight `cosh` error. -/
theorem jointSymmetricAlternatingKernelError_lower_of_signed_decomposition
    (Ce Ca Pp Np Pm Nm : ℝ → ℝ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 2)
    (hplus : Ce t + Ca t = Pp t - Np t)
    (hminus : Ce t - Ca t = Pm t - Nm t)
    (hPp0 : 0 ≤ Pp t) (hNp0 : 0 ≤ Np t)
    (hPm0 : 0 ≤ Pm t) (hNm0 : 0 ≤ Nm t) :
    -yoshidaEndpointA *
        (jointRegularEnvelope (yoshidaEndpointA * (2 + t) / 2) * Pp t +
          jointCoshEnvelope (yoshidaEndpointA * (2 + t) / 2) * Np t +
          jointRegularEnvelope (yoshidaEndpointA * (2 - t) / 2) * Pm t +
          jointCoshEnvelope (yoshidaEndpointA * (2 - t) / 2) * Nm t) ≤
      (oddLowPoleFreeKernel t - poleFreeKernelPolynomial6 t) * Ce t +
        (yoshidaEndpointA * factorTwoCenteredAntisymmetricRegularWeight t -
          intrinsicAlternatingKernelPolynomial6 t) * Ca t := by
  rcases minor_jointKernelError_decomposition ht with
    ⟨ecp, ecm, erp, erm, hecp0, hecm0, herp0, herm0,
      hecpE, hecmE, herpE, hermE, hsymm, halt⟩
  let zp : ℝ := yoshidaEndpointA * (2 + t) / 2
  let zm : ℝ := yoshidaEndpointA * (2 - t) / 2
  have hecpE' : 2 * ecp ≤ jointCoshEnvelope zp := by
    simpa only [zp] using hecpE
  have hecmE' : 2 * ecm ≤ jointCoshEnvelope zm := by
    simpa only [zm] using hecmE
  have herpE' : erp ≤ jointRegularEnvelope zp := by
    simpa only [zp] using herpE
  have hermE' : erm ≤ jointRegularEnvelope zm := by
    simpa only [zm] using hermE
  have hp :
      -(jointRegularEnvelope zp * Pp t + jointCoshEnvelope zp * Np t) ≤
        (2 * ecp - erp) * (Ce t + Ca t) := by
    rw [hplus]
    have h1 : 0 ≤ 2 * ecp * Pp t :=
      mul_nonneg (mul_nonneg (by norm_num) hecp0) hPp0
    have h2 : 0 ≤ erp * Np t := mul_nonneg herp0 hNp0
    have h3 : 0 ≤ (jointRegularEnvelope zp - erp) * Pp t :=
      mul_nonneg (sub_nonneg.mpr herpE') hPp0
    have h4 : 0 ≤ (jointCoshEnvelope zp - 2 * ecp) * Np t :=
      mul_nonneg (sub_nonneg.mpr hecpE') hNp0
    nlinarith
  have hm :
      -(jointRegularEnvelope zm * Pm t + jointCoshEnvelope zm * Nm t) ≤
        (2 * ecm - erm) * (Ce t - Ca t) := by
    rw [hminus]
    have h1 : 0 ≤ 2 * ecm * Pm t :=
      mul_nonneg (mul_nonneg (by norm_num) hecm0) hPm0
    have h2 : 0 ≤ erm * Nm t := mul_nonneg herm0 hNm0
    have h3 : 0 ≤ (jointRegularEnvelope zm - erm) * Pm t :=
      mul_nonneg (sub_nonneg.mpr hermE') hPm0
    have h4 : 0 ≤ (jointCoshEnvelope zm - 2 * ecm) * Nm t :=
      mul_nonneg (sub_nonneg.mpr hecmE') hNm0
    nlinarith
  have hinside :
      -(jointRegularEnvelope zp * Pp t + jointCoshEnvelope zp * Np t +
          jointRegularEnvelope zm * Pm t + jointCoshEnvelope zm * Nm t) ≤
        (2 * ecp - erp) * (Ce t + Ca t) +
          (2 * ecm - erm) * (Ce t - Ca t) := by
    linarith
  rw [hsymm, halt]
  dsimp only [zp, zm] at hinside ⊢
  calc
    _ = yoshidaEndpointA *
        (-(jointRegularEnvelope (yoshidaEndpointA * (2 + t) / 2) * Pp t +
          jointCoshEnvelope (yoshidaEndpointA * (2 + t) / 2) * Np t +
          jointRegularEnvelope (yoshidaEndpointA * (2 - t) / 2) * Pm t +
          jointCoshEnvelope (yoshidaEndpointA * (2 - t) / 2) * Nm t)) := by ring
    _ ≤ yoshidaEndpointA *
        ((2 * ecp - erp) * (Ce t + Ca t) +
          (2 * ecm - erm) * (Ce t - Ca t)) :=
      mul_le_mul_of_nonneg_left hinside yoshidaEndpointA_pos.le
    _ = _ := by ring

theorem integratedPoleFreeEnvelope_expansion (u : ℝ) :
    integratedPoleFreeEnvelope u =
      (193 / 3628800 : ℝ) * u ^ 7 +
        (419 / 48384 : ℝ) * u ^ 8 +
        (1 / 302400 : ℝ) * u ^ 9 +
        (7 / 8640 : ℝ) * u ^ 10 +
        (31 / 304819200 : ℝ) * u ^ 11 +
        (61 / 2073600 : ℝ) * u ^ 12 := by
  unfold integratedPoleFreeEnvelope minorCoshError minorRegularError
    minorWideSechError minorWideCschError
  ring

theorem integratedPoleFreeEnvelope_nonneg
    {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ integratedPoleFreeEnvelope u := by
  unfold integratedPoleFreeEnvelope minorCoshError minorRegularError
    minorWideSechError minorWideCschError
  positivity

private theorem integral_integratedPoleFreeEnvelope (b : ℝ) :
    (∫ u : ℝ in 0..b, integratedPoleFreeEnvelope u) =
      (193 / 29030400 : ℝ) * b ^ 8 +
        (419 / 435456 : ℝ) * b ^ 9 +
        (1 / 3024000 : ℝ) * b ^ 10 +
        (7 / 95040 : ℝ) * b ^ 11 +
        (31 / 3657830400 : ℝ) * b ^ 12 +
        (61 / 26956800 : ℝ) * b ^ 13 := by
  rw [show (fun u : ℝ ↦ integratedPoleFreeEnvelope u) =
      fun u ↦
        (193 / 3628800 : ℝ) * u ^ 7 +
          ((419 / 48384 : ℝ) * u ^ 8 +
            ((1 / 302400 : ℝ) * u ^ 9 +
              ((7 / 8640 : ℝ) * u ^ 10 +
                ((31 / 304819200 : ℝ) * u ^ 11 +
                  (61 / 2073600 : ℝ) * u ^ 12)))) by
    funext u
    rw [integratedPoleFreeEnvelope_expansion]
    ring]
  repeat' first
    | rw [intervalIntegral.integral_add
        (Continuous.intervalIntegrable (by fun_prop) 0 b)
        (Continuous.intervalIntegrable (by fun_prop) 0 b)]
    | rw [intervalIntegral.integral_const_mul]
  repeat' rw [integral_pow]
  norm_num
  ring

private theorem minor_integratedEnvelope_total_lt :
    2 * (∫ u : ℝ in 0..2 * yoshidaEndpointA,
      integratedPoleFreeEnvelope u) < (1 / 10000 : ℝ) := by
  have hA : 2 * yoshidaEndpointA < (694 / 1000 : ℝ) := by
    unfold yoshidaEndpointA
    linarith [strict_log_two_bounds.2]
  have hA0 : 0 ≤ 2 * yoshidaEndpointA :=
    mul_nonneg (by norm_num) yoshidaEndpointA_pos.le
  have hp8 := pow_lt_pow_left₀ hA hA0 (by norm_num : (8 : ℕ) ≠ 0)
  have hp9 := pow_lt_pow_left₀ hA hA0 (by norm_num : (9 : ℕ) ≠ 0)
  have hp10 := pow_lt_pow_left₀ hA hA0 (by norm_num : (10 : ℕ) ≠ 0)
  have hp11 := pow_lt_pow_left₀ hA hA0 (by norm_num : (11 : ℕ) ≠ 0)
  have hp12 := pow_lt_pow_left₀ hA hA0 (by norm_num : (12 : ℕ) ≠ 0)
  have hp13 := pow_lt_pow_left₀ hA hA0 (by norm_num : (13 : ℕ) ≠ 0)
  rw [integral_integratedPoleFreeEnvelope]
  norm_num at hp8 hp9 hp10 hp11 hp12 hp13 ⊢
  linarith

private theorem minor_integratedEnvelope_total_lt_three_div_40000 :
    2 * (∫ u : ℝ in 0..2 * yoshidaEndpointA,
      integratedPoleFreeEnvelope u) < (3 / 40000 : ℝ) := by
  have hA : 2 * yoshidaEndpointA < (6932 / 10000 : ℝ) := by
    unfold yoshidaEndpointA
    nlinarith [strict_log_two_bounds.2]
  have hA0 : 0 ≤ 2 * yoshidaEndpointA :=
    mul_nonneg (by norm_num) yoshidaEndpointA_pos.le
  have hp8 := pow_lt_pow_left₀ hA hA0 (by norm_num : (8 : ℕ) ≠ 0)
  have hp9 := pow_lt_pow_left₀ hA hA0 (by norm_num : (9 : ℕ) ≠ 0)
  have hp10 := pow_lt_pow_left₀ hA hA0 (by norm_num : (10 : ℕ) ≠ 0)
  have hp11 := pow_lt_pow_left₀ hA hA0 (by norm_num : (11 : ℕ) ≠ 0)
  have hp12 := pow_lt_pow_left₀ hA hA0 (by norm_num : (12 : ℕ) ≠ 0)
  have hp13 := pow_lt_pow_left₀ hA hA0 (by norm_num : (13 : ℕ) ≠ 0)
  rw [integral_integratedPoleFreeEnvelope]
  norm_num at hp8 hp9 hp10 hp11 hp12 hp13 ⊢
  linarith

private theorem integratedPoleFreeWeight_integral_eq :
    (∫ t : ℝ in 0..2, integratedPoleFreeWeight t) =
      2 * (∫ u : ℝ in 0..2 * yoshidaEndpointA,
        integratedPoleFreeEnvelope u) := by
  unfold integratedPoleFreeWeight
  let A : ℝ := yoshidaEndpointA
  let F : ℝ → ℝ := integratedPoleFreeEnvelope
  have hA : 0 < A := by simpa only [A] using yoshidaEndpointA_pos
  have hc : A / 2 ≠ 0 := div_ne_zero hA.ne' (by norm_num)
  have hplus := intervalIntegral.integral_comp_add_mul
    (a := (0 : ℝ)) (b := 2) F hc A
  have hminus := intervalIntegral.integral_comp_sub_mul
    (a := (0 : ℝ)) (b := 2) F hc A
  have hF : Continuous F := by
    dsimp only [F]
    unfold integratedPoleFreeEnvelope minorCoshError minorRegularError
      minorWideSechError minorWideCschError
    fun_prop
  have hadj := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hF.intervalIntegrable (0 : ℝ) A)
    (hF.intervalIntegrable A (2 * A))
  have hidentity :
      (∫ t : ℝ in 0..2,
        A * (F (A * (2 + t) / 2) + F (A * (2 - t) / 2))) =
        2 * (∫ u : ℝ in 0..2 * A, F u) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add
        (Continuous.intervalIntegrable (by fun_prop) 0 2)
        (Continuous.intervalIntegrable (by fun_prop) 0 2)]
    have hpArg :
        (fun t : ℝ ↦ F (A * (2 + t) / 2)) =
          fun t ↦ F (A + (A / 2) * t) := by
      funext t
      congr 1
      ring
    have hmArg :
        (fun t : ℝ ↦ F (A * (2 - t) / 2)) =
          fun t ↦ F (A - (A / 2) * t) := by
      funext t
      congr 1
      ring
    rw [hpArg, hmArg, hplus, hminus]
    simp only [smul_eq_mul] at hadj ⊢
    norm_num at hadj ⊢
    field_simp [hA.ne'] at hadj ⊢
    convert hadj using 1
    ring
  rw [show yoshidaEndpointA = A by rfl]
  change (∫ t : ℝ in 0..2,
      A * (F (A * (2 + t) / 2) + F (A * (2 - t) / 2))) =
        2 * (∫ u : ℝ in 0..2 * A, F u)
  exact hidentity

theorem integratedPoleFreeWeight_integral_lt :
    (∫ t : ℝ in 0..2, integratedPoleFreeWeight t) <
      (1 / 10000 : ℝ) := by
  rw [integratedPoleFreeWeight_integral_eq]
  exact minor_integratedEnvelope_total_lt

theorem integratedPoleFreeWeight_integral_lt_three_div_40000 :
    (∫ t : ℝ in 0..2, integratedPoleFreeWeight t) <
      (3 / 40000 : ℝ) := by
  rw [integratedPoleFreeWeight_integral_eq]
  exact minor_integratedEnvelope_total_lt_three_div_40000

theorem continuous_integratedPoleFreeWeight :
    Continuous integratedPoleFreeWeight := by
  unfold integratedPoleFreeWeight integratedPoleFreeEnvelope minorCoshError
    minorRegularError minorWideSechError minorWideCschError
  fun_prop

theorem integratedPoleFreeWeight_nonneg
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    0 ≤ integratedPoleFreeWeight t := by
  have hp : 0 ≤ yoshidaEndpointA * (2 + t) / 2 := by
    have hpt : 0 ≤ 2 + t := by linarith [ht.1]
    exact div_nonneg (mul_nonneg yoshidaEndpointA_pos.le hpt) (by norm_num)
  have hm : 0 ≤ yoshidaEndpointA * (2 - t) / 2 := by
    have hmt : 0 ≤ 2 - t := by linarith [ht.2]
    exact div_nonneg (mul_nonneg yoshidaEndpointA_pos.le hmt) (by norm_num)
  unfold integratedPoleFreeWeight
  exact mul_nonneg yoshidaEndpointA_pos.le
    (add_nonneg (integratedPoleFreeEnvelope_nonneg hp)
      (integratedPoleFreeEnvelope_nonneg hm))

private theorem measurable_yoshidaRegularKernel_minor :
    Measurable yoshidaRegularKernel := by
  unfold yoshidaRegularKernel
  apply Measurable.ite
  · simpa only [Set.setOf_eq_eq_singleton] using
      measurableSet_singleton (0 : ℝ)
  · exact measurable_const
  · exact ((Real.measurable_exp.comp (measurable_id.div_const 2)).div
      (measurable_const.mul Real.measurable_sinh)).sub
        (measurable_const.div (measurable_const.mul measurable_id))

private theorem measurable_symmetricRegularWeight_minor :
    Measurable factorTwoCenteredSymmetricRegularWeight := by
  unfold factorTwoCenteredSymmetricRegularWeight
  exact (((measurable_const.mul
      (Real.measurable_cosh.comp (by fun_prop))).add
        (measurable_const.mul
          (Real.measurable_cosh.comp (by fun_prop)))).sub
      (measurable_yoshidaRegularKernel_minor.comp (by fun_prop))).sub
        (measurable_yoshidaRegularKernel_minor.comp (by fun_prop))

/-- A reusable, non-sampled majorant for every continuous correlation.  The
right side retains the correlation pointwise, so endpoint arguments can
insert whichever structural energy estimate is appropriate. -/
theorem abs_poleFreeAnalyticError_le_integratedPoleFreeWeight
    (C : ℝ → ℝ) (hC : Continuous C) :
    |poleFreeAnalyticError C| ≤
      ∫ t : ℝ in 0..2, integratedPoleFreeWeight t * |C t| := by
  let f : ℝ → ℝ := fun t ↦
    (oddLowPoleFreeKernel t - poleFreeKernelPolynomial6 t) * C t
  let g : ℝ → ℝ := fun t ↦ integratedPoleFreeWeight t * |C t|
  have hg : IntervalIntegrable g volume 0 2 :=
    (continuous_integratedPoleFreeWeight.mul hC.abs).intervalIntegrable 0 2
  have hfmeas : AEStronglyMeasurable f
      (volume.restrict (Ioc (0 : ℝ) 2)) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [f, oddLowPoleFreeKernel]
    exact ((measurable_const.mul measurable_symmetricRegularWeight_minor).sub
      continuous_poleFreeKernelPolynomial6.measurable).mul hC.measurable
  have hfg : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (0 : ℝ) 2)),
      ‖f t‖ ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htIcc : t ∈ Icc (0 : ℝ) 2 := ⟨ht.1.le, ht.2⟩
    have hk := minor_poleFreeKernel_weighted_envelope htIcc
    dsimp only [f, g, integratedPoleFreeWeight]
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hk (abs_nonneg _)
  have hf : IntervalIntegrable f volume 0 2 := by
    have hg' : Integrable g (volume.restrict (Ioc (0 : ℝ) 2)) := hg.1
    constructor
    · exact Integrable.mono' hg' hfmeas hfg
    · simp
  have habs :
      |(∫ t : ℝ in 0..2, f t)| ≤ ∫ t : ℝ in 0..2, |f t| :=
    intervalIntegral.abs_integral_le_integral_abs (by norm_num)
  have hmono :
      (∫ t : ℝ in 0..2, |f t|) ≤ ∫ t : ℝ in 0..2, g t := by
    apply intervalIntegral.integral_mono_on (by norm_num) hf.abs hg
    intro t ht
    have hk := minor_poleFreeKernel_weighted_envelope ht
    dsimp only [f, g, integratedPoleFreeWeight]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hk (abs_nonneg _)
  unfold poleFreeAnalyticError
  change |(∫ t : ℝ in 0..2, f t)| ≤ ∫ t : ℝ in 0..2, g t
  exact habs.trans hmono

theorem abs_poleFreeAnalyticError_profile_refined_le
    (c d : ℝ) :
    |poleFreeAnalyticError
        (centeredEndpointCorrelation
          (factorTwoEvenStructuralLowProfile c d))| ≤
      (1 / 10000 : ℝ) * (2 * c ^ 2 + (2 / 5 : ℝ) * d ^ 2) := by
  let C : ℝ → ℝ := centeredEndpointCorrelation
    (factorTwoEvenStructuralLowProfile c d)
  let energy : ℝ := 2 * c ^ 2 + (2 / 5 : ℝ) * d ^ 2
  let W : ℝ → ℝ := integratedPoleFreeWeight
  have hprofile : Continuous (factorTwoEvenStructuralLowProfile c d) :=
    continuous_factorTwoEvenStructuralLowProfile c d
  have hC : Continuous C := by
    dsimp only [C]
    exact continuous_centeredEndpointCorrelation_of_continuous
      (factorTwoEvenStructuralLowProfile c d) hprofile
  have henergy : 0 ≤ energy := by
    dsimp only [energy]
    positivity
  have hW : Continuous W := by
    simpa only [W] using continuous_integratedPoleFreeWeight
  have hbase : |poleFreeAnalyticError C| ≤
      ∫ t : ℝ in 0..2, W t * |C t| := by
    simpa only [W] using
      abs_poleFreeAnalyticError_le_integratedPoleFreeWeight C hC
  have hmono :
      (∫ t : ℝ in 0..2, W t * |C t|) ≤
        ∫ t : ℝ in 0..2, W t * energy := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((hW.mul hC.abs).intervalIntegrable 0 2)
      ((hW.mul continuous_const).intervalIntegrable 0 2)
    intro t ht
    have htIcc : t ∈ Icc (0 : ℝ) 2 := ht
    have hcorr := abs_centeredEndpointCorrelation_le_energy
      (factorTwoEvenStructuralLowProfile c d) hprofile htIcc.1 htIcc.2
    have hcorr' : |C t| ≤ energy := by
      dsimp only [C, energy]
      rw [integral_evenStructuralProfile_sq] at hcorr
      exact hcorr
    exact mul_le_mul_of_nonneg_left hcorr'
      (by simpa only [W] using integratedPoleFreeWeight_nonneg htIcc)
  have hWint : (∫ t : ℝ in 0..2, W t) < (1 / 10000 : ℝ) := by
    simpa only [W] using integratedPoleFreeWeight_integral_lt
  have hgEq :
      (∫ t : ℝ in 0..2, W t * energy) =
        energy * (∫ t : ℝ in 0..2, W t) := by
    rw [show (fun t : ℝ ↦ W t * energy) =
        fun t ↦ energy * W t by
      funext t
      ring,
      intervalIntegral.integral_const_mul]
  have hscaled :
      energy * (∫ t : ℝ in 0..2, W t) ≤
        energy * (1 / 10000 : ℝ) :=
    mul_le_mul_of_nonneg_left hWint.le henergy
  change |poleFreeAnalyticError C| ≤ (1 / 10000 : ℝ) * energy
  rw [mul_comm]
  exact hbase.trans (hmono.trans (hgEq.trans_le hscaled))

/-- The same profile majorant with the sharper integrated envelope mass.
This retains the correlation energy and gains the small weak-direction
reserve needed by later singular retunings. -/
theorem abs_poleFreeAnalyticError_profile_three_div_forty_thousand_le
    (c d : ℝ) :
    |poleFreeAnalyticError
        (centeredEndpointCorrelation
          (factorTwoEvenStructuralLowProfile c d))| ≤
      (3 / 40000 : ℝ) * (2 * c ^ 2 + (2 / 5 : ℝ) * d ^ 2) := by
  let C : ℝ → ℝ := centeredEndpointCorrelation
    (factorTwoEvenStructuralLowProfile c d)
  let energy : ℝ := 2 * c ^ 2 + (2 / 5 : ℝ) * d ^ 2
  let W : ℝ → ℝ := integratedPoleFreeWeight
  have hprofile : Continuous (factorTwoEvenStructuralLowProfile c d) :=
    continuous_factorTwoEvenStructuralLowProfile c d
  have hC : Continuous C := by
    dsimp only [C]
    exact continuous_centeredEndpointCorrelation_of_continuous
      (factorTwoEvenStructuralLowProfile c d) hprofile
  have henergy : 0 ≤ energy := by
    dsimp only [energy]
    positivity
  have hW : Continuous W := by
    simpa only [W] using continuous_integratedPoleFreeWeight
  have hbase : |poleFreeAnalyticError C| ≤
      ∫ t : ℝ in 0..2, W t * |C t| := by
    simpa only [W] using
      abs_poleFreeAnalyticError_le_integratedPoleFreeWeight C hC
  have hmono :
      (∫ t : ℝ in 0..2, W t * |C t|) ≤
        ∫ t : ℝ in 0..2, W t * energy := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((hW.mul hC.abs).intervalIntegrable 0 2)
      ((hW.mul continuous_const).intervalIntegrable 0 2)
    intro t ht
    have htIcc : t ∈ Icc (0 : ℝ) 2 := ht
    have hcorr := abs_centeredEndpointCorrelation_le_energy
      (factorTwoEvenStructuralLowProfile c d) hprofile htIcc.1 htIcc.2
    have hcorr' : |C t| ≤ energy := by
      dsimp only [C, energy]
      rw [integral_evenStructuralProfile_sq] at hcorr
      exact hcorr
    exact mul_le_mul_of_nonneg_left hcorr'
      (by simpa only [W] using integratedPoleFreeWeight_nonneg htIcc)
  have hWint : (∫ t : ℝ in 0..2, W t) < (3 / 40000 : ℝ) := by
    simpa only [W] using
      integratedPoleFreeWeight_integral_lt_three_div_40000
  have hgEq :
      (∫ t : ℝ in 0..2, W t * energy) =
        energy * (∫ t : ℝ in 0..2, W t) := by
    rw [show (fun t : ℝ ↦ W t * energy) =
        fun t ↦ energy * W t by
      funext t
      ring,
      intervalIntegral.integral_const_mul]
  have hscaled :
      energy * (∫ t : ℝ in 0..2, W t) ≤
        energy * (3 / 40000 : ℝ) :=
    mul_le_mul_of_nonneg_left hWint.le henergy
  change |poleFreeAnalyticError C| ≤ (3 / 40000 : ℝ) * energy
  rw [mul_comm]
  exact hbase.trans (hmono.trans (hgEq.trans_le hscaled))

/-- A cancellation-preserving lower bound for the positive endpoint in the
weak aligned direction `P₀ - P₂`. -/
theorem factorTwoIntrinsicP4_positive_weak_gt_six_thousand_seven_hundred_ninety_div_million :
    (6790 / 1000000 : ℝ) <
      factorTwoStructuralPhaseLow00 1 -
        2 * factorTwoStructuralPhaseLow02 1 +
        factorTwoStructuralPhaseLow22 1 := by
  have hclean :=
    cleanWeak_gt_thirteen_thousand_two_hundred_forty_three_div_million
  have hm00 := step01Midpoint00_lt
  have hm02 := step01Midpoint02_gt
  have hm22 := step01Midpoint22_lt
  have herr :=
    abs_poleFreeAnalyticError_profile_three_div_forty_thousand_le 1 (-1)
  have hneg := evenNegativePerturbation_profile_eq 1 (-1)
  have hkernel := factorTwoCenteredSymmetricPerturbation_even_profile_kernel_eq
    1 (-1)
  have hreg := evenStructuralRegularError_profile_sharp_expansion 1 (-1)
  rw [hkernel] at hneg
  simp only [step01Midpoint00, step01Midpoint02, step01Midpoint22,
    evenNegativePerturbationTaylor00, evenNegativePerturbationTaylor02,
    evenNegativePerturbationTaylor22] at hm00 hm02 hm22
  rw [abs_le] at herr
  unfold evenNegativePerturbation00 evenNegativePerturbation02
    evenNegativePerturbation22 at hneg
  unfold factorTwoStructuralPhaseLow00 factorTwoStructuralPhaseLow02
    factorTwoStructuralPhaseLow22 at ⊢
  norm_num at hneg hreg herr ⊢
  nlinarith

/-! ## A sharpened lower even Gram -/

private def minorPlusLower00 : ℝ := 13891 / 100000
private def minorPlusLower02 : ℝ := 13544 / 100000
private def minorPlusLower22 : ℝ := 13828 / 100000
private def minorPlusP4Lower : ℝ := 3439 / 25000

private def minorEvenPositivePerturbationTaylor00 : ℝ :=
  evenPositivePerturbationTaylor00 + 11 / 20000

private def minorEvenPositivePerturbationTaylor02 : ℝ :=
  evenPositivePerturbationTaylor02

private def minorEvenPositivePerturbationTaylor22 : ℝ :=
  evenPositivePerturbationTaylor22 + 11 / 100000

private theorem minor_integral_polynomialDifference_evenProfile
    (c d : ℝ) :
    (∫ t : ℝ in 0..2,
      poleFreePolynomialDifference t *
        centeredEndpointCorrelation
          (factorTwoEvenStructuralLowProfile c d) t) =
      evenPositivePolynomialMoment00 * c ^ 2 +
        2 * evenPositivePolynomialMoment02 * c * d +
        evenPositivePolynomialMoment22 * d ^ 2 := by
  have h00 : IntervalIntegrable
      (fun t ↦ poleFreePolynomialDifference t * evenStructuralCorrelation00 t)
      volume 0 2 :=
    (continuous_poleFreePolynomialDifference.mul
      (by unfold evenStructuralCorrelation00; fun_prop)).intervalIntegrable 0 2
  have h02 : IntervalIntegrable
      (fun t ↦ poleFreePolynomialDifference t * evenStructuralCorrelation02 t)
      volume 0 2 :=
    (continuous_poleFreePolynomialDifference.mul
      (by unfold evenStructuralCorrelation02; fun_prop)).intervalIntegrable 0 2
  have h22 : IntervalIntegrable
      (fun t ↦ poleFreePolynomialDifference t * evenStructuralCorrelation22 t)
      volume 0 2 :=
    (continuous_poleFreePolynomialDifference.mul
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
  rw [integral_polynomialDifference_mul_evenCorrelations.1,
    integral_polynomialDifference_mul_evenCorrelations.2.1,
    integral_polynomialDifference_mul_evenCorrelations.2.2]
  ring

private theorem minorEvenPositivePerturbationTaylor_quadratic_le
    (c d : ℝ) :
    minorEvenPositivePerturbationTaylor00 * c ^ 2 +
        2 * minorEvenPositivePerturbationTaylor02 * c * d +
        minorEvenPositivePerturbationTaylor22 * d ^ 2 ≤
      factorTwoCenteredSymmetricPerturbation
        (factorTwoEvenStructuralLowProfile c d) := by
  have herr := abs_poleFreeAnalyticError_profile_refined_le c d
  have herrLower :
      -(1 / 10000 : ℝ) * (2 * c ^ 2 + (2 / 5 : ℝ) * d ^ 2) ≤
        poleFreeAnalyticError
          (centeredEndpointCorrelation
            (factorTwoEvenStructuralLowProfile c d)) := by
    simpa only [neg_mul] using neg_le_of_abs_le herr
  rw [factorTwoCenteredSymmetricPerturbation_even_profile_kernel_eq,
    evenStructuralRegularError_eq_analytic_add_polynomial
      (centeredEndpointCorrelation (factorTwoEvenStructuralLowProfile c d))
      (continuous_centeredEndpointCorrelation_of_continuous
        (factorTwoEvenStructuralLowProfile c d)
        (continuous_factorTwoEvenStructuralLowProfile c d)),
    minor_integral_polynomialDifference_evenProfile]
  unfold minorEvenPositivePerturbationTaylor00
    minorEvenPositivePerturbationTaylor02
    minorEvenPositivePerturbationTaylor22
    evenPositivePerturbationTaylor00 evenPositivePerturbationTaylor02
    evenPositivePerturbationTaylor22
  nlinarith

private def minorPlusModelDefect00 : ℝ :=
  yoshidaEndpointEvenLowGram00 + minorEvenPositivePerturbationTaylor00 -
    minorPlusLower00

private def minorPlusModelDefect02 : ℝ :=
  yoshidaEndpointEvenLowGram02 + minorEvenPositivePerturbationTaylor02 -
    minorPlusLower02

private def minorPlusModelDefect22 : ℝ :=
  yoshidaEndpointEvenLowGram22 + minorEvenPositivePerturbationTaylor22 -
    minorPlusLower22

private theorem minorPlusModelDefect_bounds :
    (57 / 1000000 : ℝ) < minorPlusModelDefect00 ∧
      |minorPlusModelDefect02| < (51 / 1000000 : ℝ) ∧
      (53 / 1000000 : ℝ) < minorPlusModelDefect22 := by
  have hc00 := intrinsicEven_cleanGram00_gt
  have hc02 := intrinsicEven_cleanGram02_bounds
  have hc22 := intrinsicEven_cleanGram22_gt
  have ht := evenPositivePerturbationTaylor_ultra_bounds
  unfold minorPlusModelDefect00 minorPlusModelDefect02
    minorPlusModelDefect22 minorEvenPositivePerturbationTaylor00
    minorEvenPositivePerturbationTaylor02
    minorEvenPositivePerturbationTaylor22 minorPlusLower00 minorPlusLower02
    minorPlusLower22
  constructor
  · nlinarith
  constructor
  · rw [abs_lt]
    constructor <;> nlinarith
  · nlinarith

private theorem minorPlusModelDefect_det_pos :
    0 < minorPlusModelDefect00 * minorPlusModelDefect22 -
      minorPlusModelDefect02 ^ 2 := by
  rcases minorPlusModelDefect_bounds with ⟨h00, h02, h22⟩
  have h00pos : 0 < minorPlusModelDefect00 :=
    (by norm_num : (0 : ℝ) < 57 / 1000000).trans h00
  have hprod :
      (57 / 1000000 : ℝ) * (53 / 1000000) <
        minorPlusModelDefect00 * minorPlusModelDefect22 :=
    mul_lt_mul h00 h22.le (by norm_num) h00pos.le
  have h02' := abs_lt.mp h02
  have hsq : minorPlusModelDefect02 ^ 2 < (51 / 1000000 : ℝ) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr h02'.2)
      (by linarith : 0 < minorPlusModelDefect02 + 51 / 1000000)]
  have hrat :
      (51 / 1000000 : ℝ) ^ 2 <
        (57 / 1000000) * (53 / 1000000) := by
    norm_num
  nlinarith

private theorem minorPlusModelDefect_quadratic_pos
    (c d : ℝ) (hne : c ≠ 0 ∨ d ≠ 0) :
    0 < minorPlusModelDefect00 * c ^ 2 +
      2 * minorPlusModelDefect02 * c * d +
      minorPlusModelDefect22 * d ^ 2 := by
  exact real_twoByTwo_quadratic_pos _ _ _ c d
    ((by norm_num : (0 : ℝ) < 57 / 1000000).trans
      minorPlusModelDefect_bounds.1)
    minorPlusModelDefect_det_pos hne

private theorem minorPlusCombinedModel_quadratic_le_exact (c d : ℝ) :
    (yoshidaEndpointEvenLowGram00 + minorEvenPositivePerturbationTaylor00) *
          c ^ 2 +
        2 * (yoshidaEndpointEvenLowGram02 +
          minorEvenPositivePerturbationTaylor02) * c * d +
        (yoshidaEndpointEvenLowGram22 + minorEvenPositivePerturbationTaylor22) *
          d ^ 2 ≤
      factorTwoStructuralPhaseLow00 1 * c ^ 2 +
        2 * factorTwoStructuralPhaseLow02 1 * c * d +
        factorTwoStructuralPhaseLow22 1 * d ^ 2 := by
  have hpert := minorEvenPositivePerturbationTaylor_quadratic_le c d
  have hclean :
      yoshidaEndpointOddCleanQuadratic (factorTwoEvenStructuralLowProfile c d) =
        yoshidaEndpointEvenLowGram00 * c ^ 2 +
          2 * yoshidaEndpointEvenLowGram02 * c * d +
          yoshidaEndpointEvenLowGram22 * d ^ 2 := by
    simpa only [factorTwoEvenStructuralLowProfile] using
      yoshidaEndpointEvenLowGram_quadratic_eq_clean c d
  rw [factorTwoStructuralPhaseLow_endpoint_quadratic, hclean]
  nlinarith

private theorem minorPlusLowRemainder_quadratic_nonneg (c d : ℝ) :
    0 ≤ (factorTwoStructuralPhaseLow00 1 - minorPlusLower00) * c ^ 2 +
      2 * (factorTwoStructuralPhaseLow02 1 - minorPlusLower02) * c * d +
      (factorTwoStructuralPhaseLow22 1 - minorPlusLower22) * d ^ 2 := by
  by_cases hne : c ≠ 0 ∨ d ≠ 0
  · have hstrict := minorPlusModelDefect_quadratic_pos c d hne
    have hmodel := minorPlusCombinedModel_quadratic_le_exact c d
    unfold minorPlusModelDefect00 minorPlusModelDefect02
      minorPlusModelDefect22 at hstrict
    nlinarith
  · push_neg at hne
    rcases hne with ⟨rfl, rfl⟩
    norm_num

private theorem minorPlusP4Lower_lt_exact :
    minorPlusP4Lower < factorTwoIntrinsicSixUnbalancedEPlus44 := by
  have hclean :=
    one_thousand_five_hundred_seventy_one_five_thousandths_lt_clean_p4
  have hpert := factorTwoCenteredSymmetricPerturbation_p4_lower
  unfold factorTwoIntrinsicSixUnbalancedEPlus44 minorPlusP4Lower
    factorTwoIntrinsicP4PhaseDiagonal
  norm_num at hclean hpert ⊢
  nlinarith

private theorem minorPlusEvenRemainder_quadratic_nonneg
    (c0 c2 c4 : ℝ) :
    0 ≤
      (factorTwoIntrinsicSixUnbalancedEPlus00 - minorPlusLower00) * c0 ^ 2 +
        2 * (factorTwoIntrinsicSixUnbalancedEPlus02 - minorPlusLower02) *
          c0 * c2 +
        (factorTwoIntrinsicSixUnbalancedEPlus22 - minorPlusLower22) * c2 ^ 2 +
        (factorTwoIntrinsicSixUnbalancedEPlus44 - minorPlusP4Lower) * c4 ^ 2 := by
  have hlow := minorPlusLowRemainder_quadratic_nonneg c0 c2
  have htail :
      0 ≤ (factorTwoIntrinsicSixUnbalancedEPlus44 - minorPlusP4Lower) *
        c4 ^ 2 :=
    mul_nonneg (sub_nonneg.mpr minorPlusP4Lower_lt_exact.le) (sq_nonneg c4)
  simpa only [factorTwoIntrinsicSixUnbalancedEPlus00,
    factorTwoIntrinsicSixUnbalancedEPlus02,
    factorTwoIntrinsicSixUnbalancedEPlus22] using add_nonneg hlow htail

/-! ## A five-dimensional rational congruence certificate -/

private def minorFiveQuadratic
    (a00 a01 a02 a03 a04 a11 a12 a13 a14 a22 a23 a24 a33 a34 a44
      x0 x1 x2 x3 x4 : ℝ) : ℝ :=
  a00 * x0 ^ 2 + 2 * a01 * x0 * x1 + 2 * a02 * x0 * x2 +
    2 * a03 * x0 * x3 + 2 * a04 * x0 * x4 + a11 * x1 ^ 2 +
    2 * a12 * x1 * x2 + 2 * a13 * x1 * x3 + 2 * a14 * x1 * x4 +
    a22 * x2 ^ 2 + 2 * a23 * x2 * x3 + 2 * a24 * x2 * x4 +
    a33 * x3 ^ 2 + 2 * a34 * x3 * x4 + a44 * x4 ^ 2

private def minorLowerFiveQuadratic
    (S D s1 d1 s3 d3 a41 a43 o11 o13 o33 s d p u v : ℝ) : ℝ :=
  (54807 / 100000 : ℝ) * s ^ 2 +
    2 * (63 / 100000 : ℝ) * s * d +
    (631 / 100000 : ℝ) * d ^ 2 + 2 * S * s * p - 2 * D * d * p +
    minorPlusP4Lower * p ^ 2 +
    2 * ((s1 / 2 - 1207 / 10000) * s +
      (d1 / 2 - 53 / 10000) * d + (a41 / 2 - 169 / 5000) * p) *
      (u - (25 / 24 : ℝ) * v) +
    2 * ((s3 / 2 - 687 / 10000) * s +
      (d3 / 2 + 13 / 10000) * d + (a43 / 2 - 253 / 5000) * p) * v +
    o11 * (u - (25 / 24 : ℝ) * v) ^ 2 +
    2 * o13 * (u - (25 / 24 : ℝ) * v) * v + o33 * v ^ 2

private def minorT00 : ℝ := 54807 / 100000
private def minorT01 : ℝ := 8193 / 100000000

private def minorT02 (S : ℝ) : ℝ :=
  -72341 / 375000 + S

private def minorT03 (S s1 : ℝ) : ℝ :=
  -33240533 / 68000000 + (27 / 25) * S + s1 / 2

private def minorT04 (S s1 s3 : ℝ) : ℝ :=
  -33784021 / 68400000 + (83 / 32) * S - (359 / 720) * s1 + s3 / 2

private def minorT11 : ℝ := 630928807 / 100000000000

private def minorT12 (S D : ℝ) : ℝ :=
  22050023 / 1125000000 - S / 1000 - D

private def minorT13 (S D s1 d1 : ℝ) : ℝ :=
  880683533 / 68000000000 - (27 / 25000) * S - s1 / 2000 -
    (27 / 25) * D + d1 / 2

private def minorT14 (S D s1 d1 s3 d3 : ℝ) : ℝ :=
  2144825021 / 68400000000 - (83 / 32000) * S +
    (359 / 720000) * s1 - s3 / 2000 - (83 / 32) * D -
    (359 / 720) * d1 + d3 / 2

private def minorT22 (S D : ℝ) : ℝ :=
  13492963 / 50625000 - (32 / 45) * S - (56 / 9) * D

private def minorT23 (S D s1 d1 a41 : ℝ) : ℝ :=
  250417709 / 765000000 - (1059 / 1000) * S - (8 / 45) * s1 -
    (2653 / 425) * D + (14 / 9) * d1 + a41 / 2

private def minorT24 (S D s1 d1 s3 d3 a41 a43 : ℝ) : ℝ :=
  1254873029 / 2052000000 - (173 / 90) * S + (359 / 2025) * s1 -
    (8 / 45) * s3 - (16439 / 1368) * D - (2513 / 1620) * d1 +
    (14 / 9) * d3 - (359 / 720) * a41 + a43 / 2

private def minorT33 (S D s1 d1 a41 o11 : ℝ) : ℝ :=
  600565366679 / 1156000000000 - (729 / 500) * S - (27 / 40) * s1 -
    (2646 / 425) * D + (49 / 17) * d1 + (27 / 25) * a41 + o11

private def minorT34
    (S D s1 d1 s3 d3 a41 a43 o11 o13 : ℝ) : ℝ :=
  186410386043 / 232560000000 - (18117 / 6400) * S -
    (523 / 3200) * s1 - (27 / 80) * s3 - (121337 / 10336) * D +
    (124771 / 232560) * d1 + (49 / 34) * d3 +
    (6067 / 8000) * a41 + (27 / 50) * a43 -
    (359 / 360) * o11 + o13

private def minorT44
    (S D s1 d1 s3 d3 a41 a43 o11 o13 o33 : ℝ) : ℝ :=
  118763043007 / 83174400000 - (83 / 16) * S + (359 / 360) * s1 - s3 -
    (6225 / 304) * D - (1795 / 456) * d1 + (75 / 19) * d3 -
    (29797 / 11520) * a41 + (83 / 32) * a43 +
    (128881 / 129600) * o11 - (359 / 180) * o13 + o33

set_option maxHeartbeats 800000 in
private theorem minorLowerFiveQuadratic_congruence
    (S D s1 d1 s3 d3 a41 a43 o11 o13 o33 x0 x1 x2 x3 x4 : ℝ) :
    minorLowerFiveQuadratic S D s1 d1 s3 d3 a41 a43 o11 o13 o33
        (x0 - x1 / 1000 - (16 / 45) * x2 - (27 / 40) * x3 - x4)
        (x1 + (28 / 9) * x2 + (49 / 17) * x3 + (75 / 19) * x4)
        (x2 + (27 / 25) * x3 + (83 / 32) * x4)
        (x3 + (2 / 45) * x4) x4 =
      minorFiveQuadratic minorT00 minorT01 (minorT02 S) (minorT03 S s1)
        (minorT04 S s1 s3) minorT11 (minorT12 S D)
        (minorT13 S D s1 d1) (minorT14 S D s1 d1 s3 d3)
        (minorT22 S D) (minorT23 S D s1 d1 a41)
        (minorT24 S D s1 d1 s3 d3 a41 a43)
        (minorT33 S D s1 d1 a41 o11)
        (minorT34 S D s1 d1 s3 d3 a41 a43 o11 o13)
        (minorT44 S D s1 d1 s3 d3 a41 a43 o11 o13 o33)
        x0 x1 x2 x3 x4 := by
  unfold minorLowerFiveQuadratic minorFiveQuadratic minorT00 minorT01 minorT02
    minorT03 minorT04 minorT11 minorT12 minorT13 minorT14 minorT22 minorT23
    minorT24 minorT33 minorT34 minorT44 minorPlusP4Lower
  ring

private def minorS : ℝ := factorTwoIntrinsicP4PlusCrossSum
private def minorD : ℝ := factorTwoIntrinsicP4PlusCrossDifference
private def minorS1 : ℝ :=
  factorTwoIntrinsicAlternating01 + factorTwoIntrinsicAlternating21
private def minorD1 : ℝ :=
  factorTwoIntrinsicAlternating01 - factorTwoIntrinsicAlternating21
private def minorS3 : ℝ :=
  factorTwoIntrinsicAlternating03 + factorTwoIntrinsicAlternating23
private def minorD3 : ℝ :=
  factorTwoIntrinsicAlternating03 - factorTwoIntrinsicAlternating23
private def minorA41 : ℝ := factorTwoIntrinsicFourP45Cross41
private def minorA43 : ℝ := factorTwoIntrinsicFourP45Cross43
private def minorO11 : ℝ := factorTwoIntrinsicOddPhaseLow11 (-1)
private def minorO13 : ℝ := factorTwoIntrinsicOddPhaseLow13 (-1)
private def minorO33 : ℝ := factorTwoIntrinsicOddPhaseLow33 (-1)

private theorem minorActualDiagonalBounds :
    (27 / 50 : ℝ) < minorT00 ∧
      (63 / 10000 : ℝ) < minorT11 ∧
      (397 / 50000 : ℝ) < minorT22 minorS minorD ∧
      (12 / 125 : ℝ) <
        minorT33 minorS minorD minorS1 minorD1 minorA41 minorO11 ∧
      (149 / 50000 : ℝ) <
        minorT44 minorS minorD minorS1 minorD1 minorS3 minorD3
          minorA41 minorA43 minorO11 minorO13 minorO33 := by
  have hS := factorTwoIntrinsicP4PlusCrossCoordinate_lower_bounds.1
  have hSU := factorTwoIntrinsicP4PlusCrossSum_bounds.2
  have hD := factorTwoIntrinsicP4PlusCrossCoordinate_lower_bounds.2
  have hDU := factorTwoIntrinsicP4PlusCrossDifference_bounds.2
  have hJ := factorTwoIntrinsicAlternatingSharpBounds
  unfold FactorTwoIntrinsicAlternatingSharpBounds at hJ
  have h41 := factorTwoIntrinsicFourP45Cross41_bounds
  have h43 := factorTwoIntrinsicFourP45Cross43_bounds
  have hO := factorTwoIntrinsicOddPhaseLow_minus_entry_bounds
  unfold minorS minorD minorS1 minorD1 minorS3 minorD3 minorA41 minorA43
    minorO11 minorO13 minorO33
  constructor
  · norm_num [minorT00]
  constructor
  · norm_num [minorT11]
  constructor
  · unfold minorT22
    linarith
  constructor
  · unfold minorT33
    linarith
  · unfold minorT44
    linarith

private theorem minorActualOffDiagonalBounds :
    |minorT01| < (41 / 500000 : ℝ) ∧
      |minorT02 minorS| < (51 / 100000 : ℝ) ∧
      |minorT03 minorS minorS1| < (237 / 500000 : ℝ) ∧
      |minorT04 minorS minorS1 minorS3| < (5891 / 1000000 : ℝ) ∧
      |minorT12 minorS minorD| < (79 / 500000 : ℝ) ∧
      |minorT13 minorS minorD minorS1 minorD1| < (41 / 250000 : ℝ) ∧
      |minorT14 minorS minorD minorS1 minorD1 minorS3 minorD3| <
        (107 / 250000 : ℝ) ∧
      |minorT23 minorS minorD minorS1 minorD1 minorA41| <
        (1893 / 1000000 : ℝ) ∧
      |minorT24 minorS minorD minorS1 minorD1 minorS3 minorD3
          minorA41 minorA43| < (1813 / 500000 : ℝ) ∧
      |minorT34 minorS minorD minorS1 minorD1 minorS3 minorD3
          minorA41 minorA43 minorO11 minorO13| < (897 / 100000 : ℝ) := by
  have hS := factorTwoIntrinsicP4PlusCrossCoordinate_lower_bounds.1
  have hSU := factorTwoIntrinsicP4PlusCrossSum_bounds.2
  have hD := factorTwoIntrinsicP4PlusCrossCoordinate_lower_bounds.2
  have hDU := factorTwoIntrinsicP4PlusCrossDifference_bounds.2
  have hJ := factorTwoIntrinsicAlternatingSharpBounds
  unfold FactorTwoIntrinsicAlternatingSharpBounds at hJ
  have h41 := factorTwoIntrinsicFourP45Cross41_bounds
  have h43 := factorTwoIntrinsicFourP45Cross43_bounds
  have hO := factorTwoIntrinsicOddPhaseLow_minus_entry_bounds
  unfold minorS minorD minorS1 minorD1 minorS3 minorD3 minorA41 minorA43
    minorO11 minorO13
  constructor
  · rw [abs_lt]
    norm_num [minorT01]
  constructor
  · rw [abs_lt]
    unfold minorT02
    constructor <;> linarith
  constructor
  · rw [abs_lt]
    unfold minorT03
    constructor <;> linarith
  constructor
  · rw [abs_lt]
    unfold minorT04
    constructor <;> linarith
  constructor
  · rw [abs_lt]
    unfold minorT12
    constructor <;> linarith
  constructor
  · rw [abs_lt]
    unfold minorT13
    constructor <;> linarith
  constructor
  · rw [abs_lt]
    unfold minorT14
    constructor <;> linarith
  constructor
  · rw [abs_lt]
    unfold minorT23
    constructor <;> linarith
  constructor
  · rw [abs_lt]
    unfold minorT24
    constructor <;> linarith
  · rw [abs_lt]
    unfold minorT34
    constructor <;> linarith

private def minorAbsoluteComparison
    (x0 x1 x2 x3 x4 : ℝ) : ℝ :=
  (27 / 50 : ℝ) * x0 ^ 2 + (63 / 10000 : ℝ) * x1 ^ 2 +
    (397 / 50000 : ℝ) * x2 ^ 2 + (12 / 125 : ℝ) * x3 ^ 2 +
    (149 / 50000 : ℝ) * x4 ^ 2 -
    2 * (41 / 500000 : ℝ) * |x0 * x1| -
    2 * (51 / 100000 : ℝ) * |x0 * x2| -
    2 * (237 / 500000 : ℝ) * |x0 * x3| -
    2 * (5891 / 1000000 : ℝ) * |x0 * x4| -
    2 * (79 / 500000 : ℝ) * |x1 * x2| -
    2 * (41 / 250000 : ℝ) * |x1 * x3| -
    2 * (107 / 250000 : ℝ) * |x1 * x4| -
    2 * (1893 / 1000000 : ℝ) * |x2 * x3| -
    2 * (1813 / 500000 : ℝ) * |x2 * x4| -
    2 * (897 / 100000 : ℝ) * |x3 * x4|

private def minorAbsoluteComparisonSOS
    (x0 x1 x2 x3 x4 : ℝ) : ℝ :=
  (26049 / 200000000 : ℝ) * x4 ^ 2 +
  ((63371 / 500000 : ℝ) * x0 ^ 2 +
    (10613 / 10000000 : ℝ) * x1 ^ 2 +
    (173 / 2000000 : ℝ) * x2 ^ 2 +
    (3973 / 2625000 : ℝ) * x3 ^ 2 +
    ((41 / 500000 : ℝ) / ((3 / 200) * (1 / 10))) *
      ((1 / 10 : ℝ) * |x0| - (3 / 200 : ℝ) * |x1|) ^ 2 +
    ((51 / 100000 : ℝ) / ((3 / 200) * (49 / 100))) *
      ((49 / 100 : ℝ) * |x0| - (3 / 200 : ℝ) * |x2|) ^ 2 +
    ((237 / 500000 : ℝ) / ((3 / 200) * (21 / 200))) *
      ((21 / 200 : ℝ) * |x0| - (3 / 200 : ℝ) * |x3|) ^ 2 +
    ((5891 / 1000000 : ℝ) / (3 / 200)) *
      (|x0| - (3 / 200 : ℝ) * |x4|) ^ 2 +
    ((79 / 500000 : ℝ) / ((1 / 10) * (49 / 100))) *
      ((49 / 100 : ℝ) * |x1| - (1 / 10 : ℝ) * |x2|) ^ 2 +
    ((41 / 250000 : ℝ) / ((1 / 10) * (21 / 200))) *
      ((21 / 200 : ℝ) * |x1| - (1 / 10 : ℝ) * |x3|) ^ 2 +
    ((107 / 250000 : ℝ) / (1 / 10)) *
      (|x1| - (1 / 10 : ℝ) * |x4|) ^ 2 +
    ((1893 / 1000000 : ℝ) / ((49 / 100) * (21 / 200))) *
      ((21 / 200 : ℝ) * |x2| - (49 / 100 : ℝ) * |x3|) ^ 2 +
    ((1813 / 500000 : ℝ) / (49 / 100)) *
      (|x2| - (49 / 100 : ℝ) * |x4|) ^ 2 +
    ((897 / 100000 : ℝ) / (21 / 200)) *
      (|x3| - (21 / 200 : ℝ) * |x4|) ^ 2)

private theorem minorAbsoluteComparison_eq_sos
    (x0 x1 x2 x3 x4 : ℝ) :
    minorAbsoluteComparison x0 x1 x2 x3 x4 =
      minorAbsoluteComparisonSOS x0 x1 x2 x3 x4 := by
  unfold minorAbsoluteComparison minorAbsoluteComparisonSOS
  simp only [abs_mul]
  ring_nf
  simp only [sq_abs]
  ring

private theorem minorAbsoluteComparison_ge_last_square
    (x0 x1 x2 x3 x4 : ℝ) :
    (26049 / 200000000 : ℝ) * x4 ^ 2 ≤
      minorAbsoluteComparison x0 x1 x2 x3 x4 := by
  rw [minorAbsoluteComparison_eq_sos]
  unfold minorAbsoluteComparisonSOS
  exact le_add_of_nonneg_right (by positivity)

private theorem minor_cross_lower_of_abs_le
    {a radius x y : ℝ} (h : |a| ≤ radius) :
    -2 * radius * |x * y| ≤ 2 * a * x * y := by
  have hmul : |a * x * y| ≤ radius * |x * y| := by
    calc
      |a * x * y| = |a| * (|x| * |y|) := by simp only [abs_mul, mul_assoc]
      _ ≤ radius * (|x| * |y|) :=
        mul_le_mul_of_nonneg_right h
          (mul_nonneg (abs_nonneg x) (abs_nonneg y))
      _ = radius * |x * y| := by rw [abs_mul]
  have hneg : -|a * x * y| ≤ a * x * y := neg_abs_le _
  nlinarith

private theorem minorActualTransformedQuadratic_ge_comparison
    (x0 x1 x2 x3 x4 : ℝ) :
    minorAbsoluteComparison x0 x1 x2 x3 x4 ≤
      minorFiveQuadratic minorT00 minorT01 (minorT02 minorS)
        (minorT03 minorS minorS1) (minorT04 minorS minorS1 minorS3)
        minorT11 (minorT12 minorS minorD)
        (minorT13 minorS minorD minorS1 minorD1)
        (minorT14 minorS minorD minorS1 minorD1 minorS3 minorD3)
        (minorT22 minorS minorD)
        (minorT23 minorS minorD minorS1 minorD1 minorA41)
        (minorT24 minorS minorD minorS1 minorD1 minorS3 minorD3
          minorA41 minorA43)
        (minorT33 minorS minorD minorS1 minorD1 minorA41 minorO11)
        (minorT34 minorS minorD minorS1 minorD1 minorS3 minorD3
          minorA41 minorA43 minorO11 minorO13)
        (minorT44 minorS minorD minorS1 minorD1 minorS3 minorD3
          minorA41 minorA43 minorO11 minorO13 minorO33)
        x0 x1 x2 x3 x4 := by
  rcases minorActualDiagonalBounds with ⟨h00, h11, h22, h33, h44⟩
  rcases minorActualOffDiagonalBounds with
    ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34⟩
  have hd00 := mul_le_mul_of_nonneg_right h00.le (sq_nonneg x0)
  have hd11 := mul_le_mul_of_nonneg_right h11.le (sq_nonneg x1)
  have hd22 := mul_le_mul_of_nonneg_right h22.le (sq_nonneg x2)
  have hd33 := mul_le_mul_of_nonneg_right h33.le (sq_nonneg x3)
  have hd44 := mul_le_mul_of_nonneg_right h44.le (sq_nonneg x4)
  have hc01 := minor_cross_lower_of_abs_le (x := x0) (y := x1) h01.le
  have hc02 := minor_cross_lower_of_abs_le (x := x0) (y := x2) h02.le
  have hc03 := minor_cross_lower_of_abs_le (x := x0) (y := x3) h03.le
  have hc04 := minor_cross_lower_of_abs_le (x := x0) (y := x4) h04.le
  have hc12 := minor_cross_lower_of_abs_le (x := x1) (y := x2) h12.le
  have hc13 := minor_cross_lower_of_abs_le (x := x1) (y := x3) h13.le
  have hc14 := minor_cross_lower_of_abs_le (x := x1) (y := x4) h14.le
  have hc23 := minor_cross_lower_of_abs_le (x := x2) (y := x3) h23.le
  have hc24 := minor_cross_lower_of_abs_le (x := x2) (y := x4) h24.le
  have hc34 := minor_cross_lower_of_abs_le (x := x3) (y := x4) h34.le
  unfold minorAbsoluteComparison minorFiveQuadratic
  linarith

private def minorExactFiveQuadratic
    (c0 c2 c4 c1 c3 : ℝ) : ℝ :=
  symmetricQuadratic
      factorTwoIntrinsicSixUnbalancedEPlus00
      factorTwoIntrinsicSixUnbalancedEPlus02
      factorTwoIntrinsicSixUnbalancedEPlus04
      factorTwoIntrinsicSixUnbalancedEPlus22
      factorTwoIntrinsicSixUnbalancedEPlus24
      factorTwoIntrinsicSixUnbalancedEPlus44 c0 c2 c4 +
    2 * (c0 * factorTwoIntrinsicSixUnbalancedKPlus01 +
      c2 * factorTwoIntrinsicSixUnbalancedKPlus21 +
      c4 * factorTwoIntrinsicSixUnbalancedKPlus41) * c1 +
    2 * (c0 * factorTwoIntrinsicSixUnbalancedKPlus03 +
      c2 * factorTwoIntrinsicSixUnbalancedKPlus23 +
      c4 * factorTwoIntrinsicSixUnbalancedKPlus43) * c3 +
    factorTwoIntrinsicSixUnbalancedOMinus11 * c1 ^ 2 +
    2 * factorTwoIntrinsicSixUnbalancedOMinus13 * c1 * c3 +
    factorTwoIntrinsicSixUnbalancedOMinus33 * c3 ^ 2

set_option maxHeartbeats 800000 in
private theorem minorLowerFiveQuadratic_le_exact
    (s d p u v : ℝ) :
    minorLowerFiveQuadratic minorS minorD minorS1 minorD1 minorS3 minorD3
        minorA41 minorA43 minorO11 minorO13 minorO33 s d p u v ≤
      minorExactFiveQuadratic (s + d) (s - d) p
        (u - (25 / 24 : ℝ) * v) v := by
  have hrem := minorPlusEvenRemainder_quadratic_nonneg (s + d) (s - d) p
  have heq :
      minorExactFiveQuadratic (s + d) (s - d) p
          (u - (25 / 24 : ℝ) * v) v =
        minorLowerFiveQuadratic minorS minorD minorS1 minorD1 minorS3 minorD3
          minorA41 minorA43 minorO11 minorO13 minorO33 s d p u v +
        ((factorTwoIntrinsicSixUnbalancedEPlus00 - minorPlusLower00) *
            (s + d) ^ 2 +
          2 * (factorTwoIntrinsicSixUnbalancedEPlus02 - minorPlusLower02) *
            (s + d) * (s - d) +
          (factorTwoIntrinsicSixUnbalancedEPlus22 - minorPlusLower22) *
            (s - d) ^ 2 +
          (factorTwoIntrinsicSixUnbalancedEPlus44 - minorPlusP4Lower) * p ^ 2) := by
    unfold minorExactFiveQuadratic minorLowerFiveQuadratic symmetricQuadratic
      minorS minorD minorS1 minorD1 minorS3 minorD3 minorA41 minorA43
      minorO11 minorO13 minorO33 factorTwoIntrinsicP4PlusCrossSum
      factorTwoIntrinsicP4PlusCrossDifference
      factorTwoIntrinsicSixUnbalancedEPlus04
      factorTwoIntrinsicSixUnbalancedEPlus24
      factorTwoIntrinsicSixUnbalancedKPlus01
      factorTwoIntrinsicSixUnbalancedKPlus03
      factorTwoIntrinsicSixUnbalancedKPlus21
      factorTwoIntrinsicSixUnbalancedKPlus23
      factorTwoIntrinsicSixUnbalancedKPlus41
      factorTwoIntrinsicSixUnbalancedKPlus43
      factorTwoIntrinsicSixUnbalancedOMinus11
      factorTwoIntrinsicSixUnbalancedOMinus13
      factorTwoIntrinsicSixUnbalancedOMinus33
      minorPlusLower00 minorPlusLower02 minorPlusLower22 minorPlusP4Lower
    ring
  rw [heq]
  exact le_add_of_nonneg_right hrem

def factorTwoIntrinsicSixUnbalancedMinorPlusAbsoluteComparison
    (x0 x1 x2 x3 x4 : ℝ) : ℝ :=
  minorAbsoluteComparison x0 x1 x2 x3 x4

def factorTwoIntrinsicSixUnbalancedMinorPlusTransformedFiveQuadratic
    (x0 x1 x2 x3 x4 : ℝ) : ℝ :=
  minorFiveQuadratic minorT00 minorT01 (minorT02 minorS)
    (minorT03 minorS minorS1) (minorT04 minorS minorS1 minorS3)
    minorT11 (minorT12 minorS minorD)
    (minorT13 minorS minorD minorS1 minorD1)
    (minorT14 minorS minorD minorS1 minorD1 minorS3 minorD3)
    (minorT22 minorS minorD)
    (minorT23 minorS minorD minorS1 minorD1 minorA41)
    (minorT24 minorS minorD minorS1 minorD1 minorS3 minorD3
      minorA41 minorA43)
    (minorT33 minorS minorD minorS1 minorD1 minorA41 minorO11)
    (minorT34 minorS minorD minorS1 minorD1 minorS3 minorD3
      minorA41 minorA43 minorO11 minorO13)
    (minorT44 minorS minorD minorS1 minorD1 minorS3 minorD3
      minorA41 minorA43 minorO11 minorO13 minorO33)
    x0 x1 x2 x3 x4

theorem factorTwoIntrinsicSixUnbalancedMinorPlusAbsoluteComparison_le_transformed
    (x0 x1 x2 x3 x4 : ℝ) :
    factorTwoIntrinsicSixUnbalancedMinorPlusAbsoluteComparison x0 x1 x2 x3 x4 ≤
      factorTwoIntrinsicSixUnbalancedMinorPlusTransformedFiveQuadratic
        x0 x1 x2 x3 x4 := by
  simpa only [factorTwoIntrinsicSixUnbalancedMinorPlusAbsoluteComparison,
    factorTwoIntrinsicSixUnbalancedMinorPlusTransformedFiveQuadratic] using
    minorActualTransformedQuadratic_ge_comparison x0 x1 x2 x3 x4

def factorTwoIntrinsicSixUnbalancedMinorPlusLowerFiveQuadratic
    (s d p u v : ℝ) : ℝ :=
  minorLowerFiveQuadratic minorS minorD minorS1 minorD1 minorS3 minorD3
    minorA41 minorA43 minorO11 minorO13 minorO33 s d p u v

def factorTwoIntrinsicSixUnbalancedMinorPlusExactFiveQuadratic
    (c0 c2 c4 c1 c3 : ℝ) : ℝ :=
  minorExactFiveQuadratic c0 c2 c4 c1 c3

theorem factorTwoIntrinsicSixUnbalancedMinorPlusLowerFive_le_exact
    (s d p u v : ℝ) :
    factorTwoIntrinsicSixUnbalancedMinorPlusLowerFiveQuadratic s d p u v ≤
      factorTwoIntrinsicSixUnbalancedMinorPlusExactFiveQuadratic
        (s + d) (s - d) p (u - (25 / 24 : ℝ) * v) v := by
  simpa only [factorTwoIntrinsicSixUnbalancedMinorPlusLowerFiveQuadratic,
    factorTwoIntrinsicSixUnbalancedMinorPlusExactFiveQuadratic] using
    minorLowerFiveQuadratic_le_exact s d p u v

/-- The public absolute comparison transports through the exact five-variable
congruence and is absorbed by the correlated exact form.  This exposes the
private congruence in the form needed by later retunings without exposing its
auxiliary coefficients. -/
theorem factorTwoIntrinsicSixUnbalancedMinorPlusAbsoluteComparison_le_exact_congruence
    (x0 x1 x2 x3 x4 : ℝ) :
    (27 / 50 : ℝ) * x0 ^ 2 + (63 / 10000 : ℝ) * x1 ^ 2 +
        (397 / 50000 : ℝ) * x2 ^ 2 + (12 / 125 : ℝ) * x3 ^ 2 +
        (149 / 50000 : ℝ) * x4 ^ 2 -
        2 * (41 / 500000 : ℝ) * |x0 * x1| -
        2 * (51 / 100000 : ℝ) * |x0 * x2| -
        2 * (237 / 500000 : ℝ) * |x0 * x3| -
        2 * (5891 / 1000000 : ℝ) * |x0 * x4| -
        2 * (79 / 500000 : ℝ) * |x1 * x2| -
        2 * (41 / 250000 : ℝ) * |x1 * x3| -
        2 * (107 / 250000 : ℝ) * |x1 * x4| -
        2 * (1893 / 1000000 : ℝ) * |x2 * x3| -
        2 * (1813 / 500000 : ℝ) * |x2 * x4| -
        2 * (897 / 100000 : ℝ) * |x3 * x4| ≤
      factorTwoIntrinsicSixUnbalancedMinorPlusExactFiveQuadratic
        ((x0 - x1 / 1000 - (16 / 45 : ℝ) * x2 -
            (27 / 40 : ℝ) * x3 - x4) +
          (x1 + (28 / 9 : ℝ) * x2 + (49 / 17 : ℝ) * x3 +
            (75 / 19 : ℝ) * x4))
        ((x0 - x1 / 1000 - (16 / 45 : ℝ) * x2 -
            (27 / 40 : ℝ) * x3 - x4) -
          (x1 + (28 / 9 : ℝ) * x2 + (49 / 17 : ℝ) * x3 +
            (75 / 19 : ℝ) * x4))
        (x2 + (27 / 25 : ℝ) * x3 + (83 / 32 : ℝ) * x4)
        ((x3 + (2 / 45 : ℝ) * x4) - (25 / 24 : ℝ) * x4) x4 := by
  have hcomparison :=
    minorActualTransformedQuadratic_ge_comparison x0 x1 x2 x3 x4
  have hcongruence := minorLowerFiveQuadratic_congruence
    minorS minorD minorS1 minorD1 minorS3 minorD3 minorA41 minorA43
    minorO11 minorO13 minorO33 x0 x1 x2 x3 x4
  have hlower := minorLowerFiveQuadratic_le_exact
    (x0 - x1 / 1000 - (16 / 45 : ℝ) * x2 -
      (27 / 40 : ℝ) * x3 - x4)
    (x1 + (28 / 9 : ℝ) * x2 + (49 / 17 : ℝ) * x3 +
      (75 / 19 : ℝ) * x4)
    (x2 + (27 / 25 : ℝ) * x3 + (83 / 32 : ℝ) * x4)
    (x3 + (2 / 45 : ℝ) * x4) x4
  rw [hcongruence] at hlower
  simpa only [minorAbsoluteComparison,
    factorTwoIntrinsicSixUnbalancedMinorPlusExactFiveQuadratic] using
    hcomparison.trans hlower

private theorem minorExactFiveQuadratic_ge_sheared_last_square
    (s d p u v : ℝ) :
    (26049 / 200000000 : ℝ) * v ^ 2 ≤
      minorExactFiveQuadratic (s + d) (s - d) p
        (u - (25 / 24 : ℝ) * v) v := by
  let x4 : ℝ := v
  let x3 : ℝ := u - (2 / 45 : ℝ) * x4
  let x2 : ℝ := p - (27 / 25 : ℝ) * x3 - (83 / 32 : ℝ) * x4
  let x1 : ℝ := d - (28 / 9 : ℝ) * x2 - (49 / 17 : ℝ) * x3 -
    (75 / 19 : ℝ) * x4
  let x0 : ℝ := s + x1 / 1000 + (16 / 45 : ℝ) * x2 +
    (27 / 40 : ℝ) * x3 + x4
  have hs :
      x0 - x1 / 1000 - (16 / 45 : ℝ) * x2 - (27 / 40 : ℝ) * x3 - x4 =
        s := by
    dsimp only [x0]
    ring
  have hd :
      x1 + (28 / 9 : ℝ) * x2 + (49 / 17 : ℝ) * x3 +
          (75 / 19 : ℝ) * x4 = d := by
    dsimp only [x1]
    ring
  have hp : x2 + (27 / 25 : ℝ) * x3 + (83 / 32 : ℝ) * x4 = p := by
    dsimp only [x2]
    ring
  have hu : x3 + (2 / 45 : ℝ) * x4 = u := by
    dsimp only [x3]
    ring
  have hv : x4 = v := by rfl
  have hlast := minorAbsoluteComparison_ge_last_square x0 x1 x2 x3 x4
  have hge := minorActualTransformedQuadratic_ge_comparison x0 x1 x2 x3 x4
  have hcong := minorLowerFiveQuadratic_congruence
    minorS minorD minorS1 minorD1 minorS3 minorD3 minorA41 minorA43
    minorO11 minorO13 minorO33 x0 x1 x2 x3 x4
  rw [hs, hd, hp, hu, hv] at hcong
  have hlower := minorLowerFiveQuadratic_le_exact s d p u v
  rw [hcong] at hlower
  simpa only [hv] using hlast.trans (hge.trans hlower)

def plusShearCross : ℝ :=
  factorTwoIntrinsicSixUnbalancedTPlus13 -
    (25 / 24 : ℝ) * factorTwoIntrinsicSixUnbalancedTPlus11

def plusShearDiagonal : ℝ :=
  factorTwoIntrinsicSixUnbalancedTPlus33 -
    2 * (25 / 24 : ℝ) * factorTwoIntrinsicSixUnbalancedTPlus13 +
    (25 / 24 : ℝ) ^ 2 * factorTwoIntrinsicSixUnbalancedTPlus11

theorem factorTwoIntrinsicSixUnbalancedTPlusMinor_eq_shear :
    factorTwoIntrinsicSixUnbalancedTPlusMinor =
      factorTwoIntrinsicSixUnbalancedTPlus11 * plusShearDiagonal -
        plusShearCross ^ 2 := by
  unfold factorTwoIntrinsicSixUnbalancedTPlusMinor leadingMinorTwo
    plusShearDiagonal plusShearCross
  ring

theorem plusShearDiagonal_eq_fractionFree :
    plusShearDiagonal =
      factorTwoIntrinsicSixUnbalancedEPlusDet *
          symmetricQuadratic
            factorTwoIntrinsicSixUnbalancedOMinus11
            factorTwoIntrinsicSixUnbalancedOMinus13
            factorTwoIntrinsicSixUnbalancedOMinus15
            factorTwoIntrinsicSixUnbalancedOMinus33
            factorTwoIntrinsicSixUnbalancedOMinus35
            factorTwoIntrinsicSixUnbalancedOMinus55
            (-(25 / 24 : ℝ)) 1 0 -
        adjugateQuadratic
          factorTwoIntrinsicSixUnbalancedEPlus00
          factorTwoIntrinsicSixUnbalancedEPlus02
          factorTwoIntrinsicSixUnbalancedEPlus04
          factorTwoIntrinsicSixUnbalancedEPlus22
          factorTwoIntrinsicSixUnbalancedEPlus24
          factorTwoIntrinsicSixUnbalancedEPlus44
          (factorTwoIntrinsicSixUnbalancedKPlus03 -
            (25 / 24 : ℝ) * factorTwoIntrinsicSixUnbalancedKPlus01)
          (factorTwoIntrinsicSixUnbalancedKPlus23 -
            (25 / 24 : ℝ) * factorTwoIntrinsicSixUnbalancedKPlus21)
          (factorTwoIntrinsicSixUnbalancedKPlus43 -
            (25 / 24 : ℝ) * factorTwoIntrinsicSixUnbalancedKPlus41) := by
  have h := factorTwoIntrinsicSixUnbalancedTPlusQuadratic_eq_fractionFree
    (-(25 / 24 : ℝ)) 1 0
  unfold plusShearDiagonal
  simp only [factorTwoIntrinsicSixUnbalancedTPlusQuadratic,
    symmetricQuadratic, mul_zero, add_zero,
    zero_pow (by norm_num : 2 ≠ 0)] at h ⊢
  convert h using 1 <;> ring_nf

private theorem minorExactFiveQuadratic_ge_raw_last_square
    (c0 c2 c4 c1 c3 : ℝ) :
    (26049 / 200000000 : ℝ) * c3 ^ 2 ≤
      minorExactFiveQuadratic c0 c2 c4 c1 c3 := by
  have h := minorExactFiveQuadratic_ge_sheared_last_square
    ((c0 + c2) / 2) ((c0 - c2) / 2) c4
    (c1 + (25 / 24 : ℝ) * c3) c3
  convert h using 1
  all_goals ring

set_option maxHeartbeats 800000 in
private theorem minorExactFiveQuadratic_completion
    (y1 y3 : ℝ) :
    let det := factorTwoIntrinsicSixUnbalancedEPlusDet
    let ell0 := factorTwoIntrinsicSixUnbalancedKPlus01 * y1 +
      factorTwoIntrinsicSixUnbalancedKPlus03 * y3
    let ell2 := factorTwoIntrinsicSixUnbalancedKPlus21 * y1 +
      factorTwoIntrinsicSixUnbalancedKPlus23 * y3
    let ell4 := factorTwoIntrinsicSixUnbalancedKPlus41 * y1 +
      factorTwoIntrinsicSixUnbalancedKPlus43 * y3
    let vec := adjugateVector
      factorTwoIntrinsicSixUnbalancedEPlus00
      factorTwoIntrinsicSixUnbalancedEPlus02
      factorTwoIntrinsicSixUnbalancedEPlus04
      factorTwoIntrinsicSixUnbalancedEPlus22
      factorTwoIntrinsicSixUnbalancedEPlus24
      factorTwoIntrinsicSixUnbalancedEPlus44 ell0 ell2 ell4
    minorExactFiveQuadratic (-vec 0) (-vec 1) (-vec 2)
        (det * y1) (det * y3) =
      det * factorTwoIntrinsicSixUnbalancedTPlusQuadratic y1 y3 0 := by
  dsimp only
  rw [factorTwoIntrinsicSixUnbalancedTPlusQuadratic_eq_fractionFree]
  simp only [mul_zero, add_zero]
  unfold minorExactFiveQuadratic symmetricQuadratic adjugateQuadratic
    factorTwoIntrinsicSixUnbalancedEPlusDet symmetricDeterminant
  simp only [adjugateVector]
  ring

/-- Quantitative structural coercivity of the sheared `P₃` direction.
This is the weighted diagonal-dominance residual transported through the
fraction-free even completion. -/
theorem plusShearDiagonal_ge_weighted_det :
    (26049 / 200000000 : ℝ) *
        factorTwoIntrinsicSixUnbalancedEPlusDet ≤
      plusShearDiagonal := by
  let det : ℝ := factorTwoIntrinsicSixUnbalancedEPlusDet
  let ell0 : ℝ :=
    -(25 / 24 : ℝ) * factorTwoIntrinsicSixUnbalancedKPlus01 +
      factorTwoIntrinsicSixUnbalancedKPlus03
  let ell2 : ℝ :=
    -(25 / 24 : ℝ) * factorTwoIntrinsicSixUnbalancedKPlus21 +
      factorTwoIntrinsicSixUnbalancedKPlus23
  let ell4 : ℝ :=
    -(25 / 24 : ℝ) * factorTwoIntrinsicSixUnbalancedKPlus41 +
      factorTwoIntrinsicSixUnbalancedKPlus43
  let vec := adjugateVector
    factorTwoIntrinsicSixUnbalancedEPlus00
    factorTwoIntrinsicSixUnbalancedEPlus02
    factorTwoIntrinsicSixUnbalancedEPlus04
    factorTwoIntrinsicSixUnbalancedEPlus22
    factorTwoIntrinsicSixUnbalancedEPlus24
    factorTwoIntrinsicSixUnbalancedEPlus44 ell0 ell2 ell4
  have hd : 0 < det := by
    simpa only [det] using factorTwoIntrinsicSixUnbalancedEPlus_positive.2.2
  have hlower := minorExactFiveQuadratic_ge_raw_last_square
    (-vec 0) (-vec 1) (-vec 2) (det * (-(25 / 24 : ℝ))) det
  have hcompletion := minorExactFiveQuadratic_completion (-(25 / 24 : ℝ)) 1
  dsimp only [det, ell0, ell2, ell4, vec] at hlower hcompletion
  ring_nf at hlower hcompletion
  rw [hcompletion] at hlower
  have hshear :
      factorTwoIntrinsicSixUnbalancedTPlusQuadratic
          (-25 / 24 : ℝ) 1 0 = plusShearDiagonal := by
    unfold factorTwoIntrinsicSixUnbalancedTPlusQuadratic plusShearDiagonal
      symmetricQuadratic
    ring
  rw [hshear] at hlower
  have hscaled :
      det * ((26049 / 200000000 : ℝ) * det) ≤
        det * plusShearDiagonal := by
    nlinarith
  exact le_of_mul_le_mul_left hscaled hd

theorem plusShearDiagonal_pos : 0 < plusShearDiagonal := by
  have hd := factorTwoIntrinsicSixUnbalancedEPlus_positive.2.2
  have h := plusShearDiagonal_ge_weighted_det
  have hcoef : (0 : ℝ) < 26049 / 200000000 := by norm_num
  exact (mul_pos hcoef hd).trans_le h

/-- The second positive Sylvester gate, proved by a global Taylor envelope,
a rational congruence, and an exact weighted SOS certificate. -/
theorem factorTwoIntrinsicSixUnbalancedTPlusMinor_pos :
    0 < factorTwoIntrinsicSixUnbalancedTPlusMinor := by
  let det : ℝ := factorTwoIntrinsicSixUnbalancedEPlusDet
  let a : ℝ := factorTwoIntrinsicSixUnbalancedTPlus11
  let b : ℝ := factorTwoIntrinsicSixUnbalancedTPlus13
  let ell0 : ℝ := -b * factorTwoIntrinsicSixUnbalancedKPlus01 +
    a * factorTwoIntrinsicSixUnbalancedKPlus03
  let ell2 : ℝ := -b * factorTwoIntrinsicSixUnbalancedKPlus21 +
    a * factorTwoIntrinsicSixUnbalancedKPlus23
  let ell4 : ℝ := -b * factorTwoIntrinsicSixUnbalancedKPlus41 +
    a * factorTwoIntrinsicSixUnbalancedKPlus43
  let vec := adjugateVector
    factorTwoIntrinsicSixUnbalancedEPlus00
    factorTwoIntrinsicSixUnbalancedEPlus02
    factorTwoIntrinsicSixUnbalancedEPlus04
    factorTwoIntrinsicSixUnbalancedEPlus22
    factorTwoIntrinsicSixUnbalancedEPlus24
    factorTwoIntrinsicSixUnbalancedEPlus44 ell0 ell2 ell4
  have hd : 0 < det := by
    simpa only [det] using factorTwoIntrinsicSixUnbalancedEPlus_positive.2.2
  have ha : 0 < a := by
    simpa only [a] using factorTwoIntrinsicSixUnbalancedTPlus11_pos
  have hlower := minorExactFiveQuadratic_ge_raw_last_square
    (-vec 0) (-vec 1) (-vec 2) (det * (-b)) (det * a)
  have hcompletion := minorExactFiveQuadratic_completion (-b) a
  dsimp only [det, a, b, ell0, ell2, ell4, vec] at hlower hcompletion
  ring_nf at hlower hcompletion
  rw [hcompletion] at hlower
  have hminorIdentity :
      factorTwoIntrinsicSixUnbalancedTPlusQuadratic
          (-factorTwoIntrinsicSixUnbalancedTPlus13)
          factorTwoIntrinsicSixUnbalancedTPlus11 0 =
        factorTwoIntrinsicSixUnbalancedTPlus11 *
          factorTwoIntrinsicSixUnbalancedTPlusMinor := by
    unfold factorTwoIntrinsicSixUnbalancedTPlusQuadratic
      factorTwoIntrinsicSixUnbalancedTPlusMinor leadingMinorTwo
      symmetricQuadratic
    ring
  rw [hminorIdentity] at hlower
  have hleft :
      0 < (26049 / 200000000 : ℝ) *
        (factorTwoIntrinsicSixUnbalancedEPlusDet *
          factorTwoIntrinsicSixUnbalancedTPlus11) ^ 2 := by
    positivity
  ring_nf at hleft
  have hproduct :
      0 < factorTwoIntrinsicSixUnbalancedEPlusDet *
        (factorTwoIntrinsicSixUnbalancedTPlus11 *
          factorTwoIntrinsicSixUnbalancedTPlusMinor) :=
    hleft.trans_le hlower
  have hfactor :
      0 < factorTwoIntrinsicSixUnbalancedEPlusDet *
        factorTwoIntrinsicSixUnbalancedTPlus11 := mul_pos hd ha
  have hproduct' :
      0 < (factorTwoIntrinsicSixUnbalancedEPlusDet *
          factorTwoIntrinsicSixUnbalancedTPlus11) *
        factorTwoIntrinsicSixUnbalancedTPlusMinor := by
    nlinarith
  exact ((mul_pos_iff.mp hproduct').resolve_right (fun hneg ↦
    (not_lt_of_ge hfactor.le) hneg.1)).2

/-- A cancellation-aware quantitative bound for the exposed shear cross. -/
theorem plusShearCross_sq_lt :
    plusShearCross ^ 2 <
      factorTwoIntrinsicSixUnbalancedTPlus11 * plusShearDiagonal := by
  have h := factorTwoIntrinsicSixUnbalancedTPlusMinor_pos
  rw [factorTwoIntrinsicSixUnbalancedTPlusMinor_eq_shear] at h
  linarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusMinorStructural
