import ArithmeticHodge.Analysis.YoshidaEndpointEvenTailRepresenter
import ArithmeticHodge.Analysis.YoshidaConstantBounds
import Mathlib.Analysis.Calculus.Taylor

set_option autoImplicit false

open Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeKernel

open YoshidaEndpointHyperbolicBound
open YoshidaConstantBounds
open YoshidaRegularKernelBound

noncomputable section

/-- Sixth-order Taylor envelope for the regular Yoshida kernel on
`[0, log 2]`.  The odd powers come from the regularized cosecant term. -/
def yoshidaRegularKernelPolynomial6 (t : ℝ) : ℝ :=
  (1 / 4 : ℝ) - t / 48 - t ^ 2 / 32 + 7 * t ^ 3 / 11520 +
    5 * t ^ 4 / 1536 - 31 * t ^ 5 / 1935360 -
      61 * t ^ 6 / 184320

/-- Even Taylor polynomial used for the fixed endpoint cosh factor. -/
def yoshidaEndpointCoshPolynomial6 (x : ℝ) : ℝ :=
  1 + yoshidaEndpointA ^ 2 * x ^ 2 / 8 +
    yoshidaEndpointA ^ 4 * x ^ 4 / 384 +
      yoshidaEndpointA ^ 6 * x ^ 6 / 46080

private def kernelSechPolynomial6 (u : ℝ) : ℝ :=
  1 - u ^ 2 / 2 + 5 * u ^ 4 / 24 - 61 * u ^ 6 / 720

private def kernelCschRegularPolynomial5 (u : ℝ) : ℝ :=
  -u / 6 + 7 * u ^ 3 / 360 - 31 * u ^ 5 / 15120

private def kernelCschMultiplier6 (u : ℝ) : ℝ :=
  1 + u * kernelCschRegularPolynomial5 u

private def kernelCoshLower6 (u : ℝ) : ℝ :=
  1 + u ^ 2 / 2 + u ^ 4 / 24 + u ^ 6 / 720

private def kernelCoshUpper8 (u : ℝ) : ℝ :=
  kernelCoshLower6 u + (16 / 15 : ℝ) * u ^ 8 / 40320

private def kernelSinhDivLower6 (u : ℝ) : ℝ :=
  1 + u ^ 2 / 6 + u ^ 4 / 120 + u ^ 6 / 5040

private def kernelSinhDivUpper8 (u : ℝ) : ℝ :=
  kernelSinhDivLower6 u + (16 / 15 : ℝ) * u ^ 8 / 362880

private def kernelSechError (u : ℝ) : ℝ :=
  u ^ 8 * (61 * u ^ 4 + 1680 * u ^ 2 + 17820) / 518400

private def kernelCschError (u : ℝ) : ℝ :=
  u ^ 7 * (31 * u ^ 4 + 1008 * u ^ 2 + 16212) / 76204800

private theorem cosh_lt_sixteen_fifteenths
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u < (1733 / 5000 : ℝ)) :
    Real.cosh u < (16 / 15 : ℝ) := by
  have huSq : u ^ 2 < (1733 / 5000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hu hu0 (by norm_num)
  have hv0 : 0 ≤ u ^ 2 / 2 := by positivity
  have hv16 : u ^ 2 / 2 < (1 / 16 : ℝ) := by
    norm_num at huSq ⊢
    nlinarith
  have hv1 : u ^ 2 / 2 < (1 : ℝ) := hv16.trans (by norm_num)
  have hExp : Real.exp (u ^ 2 / 2) ≤ 1 / (1 - u ^ 2 / 2) :=
    Real.exp_bound_div_one_sub_of_interval hv0 hv1
  have hFrac : 1 / (1 - u ^ 2 / 2) < (16 / 15 : ℝ) := by
    rw [div_lt_iff₀ (sub_pos.mpr hv1)]
    nlinarith
  exact (Real.cosh_le_exp_half_sq u).trans_lt (hExp.trans_lt hFrac)

private theorem kernel_cosh_taylor_bounds
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u < (1733 / 5000 : ℝ)) :
    kernelCoshLower6 u ≤ Real.cosh u ∧
      Real.cosh u ≤ kernelCoshUpper8 u := by
  rcases eq_or_lt_of_le hu0 with rfl | hupos
  · norm_num [kernelCoshLower6, kernelCoshUpper8]
  · rcases taylor_mean_remainder_lagrange_iteratedDeriv
        (f := Real.cosh) (x₀ := 0) (x := u) (n := 7) hupos
        Real.contDiff_cosh.contDiffOn with ⟨w, hw, hTaylor⟩
    have hTaylorEval :
        taylorWithinEval Real.cosh 7 (Icc 0 u) 0 u =
          kernelCoshLower6 u := by
      have hder (n : ℕ) :
          iteratedDerivWithin n Real.cosh (Icc 0 u) 0 =
            iteratedDeriv n Real.cosh 0 :=
        Real.iteratedDerivWithin_cosh_Icc n hupos ⟨le_rfl, hu0⟩
      rw [taylor_within_apply]
      simp [hder, Finset.sum_range_succ, kernelCoshLower6]
      ring
    rw [hTaylorEval] at hTaylor
    norm_num [Real.iteratedDeriv_even_cosh] at hTaylor
    have hw0 : 0 ≤ w := hw.1.le
    have hwBound : Real.cosh w < (16 / 15 : ℝ) :=
      cosh_lt_sixteen_fifteenths hw0 (hw.2.trans hu)
    have hrem0 : 0 ≤ Real.cosh w * u ^ 8 / 40320 := by positivity
    have hremUpper :
        Real.cosh w * u ^ 8 / 40320 ≤
          (16 / 15 : ℝ) * u ^ 8 / 40320 := by
      gcongr
    constructor
    · linarith
    · unfold kernelCoshUpper8
      linarith

private theorem kernel_sinh_div_taylor_bounds
    {u : ℝ} (hu0 : 0 < u) (hu : u < (1733 / 5000 : ℝ)) :
    kernelSinhDivLower6 u ≤ Real.sinh u / u ∧
      Real.sinh u / u ≤ kernelSinhDivUpper8 u := by
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
      Real.sinh u / u - kernelSinhDivLower6 u =
        Real.cosh w * u ^ 8 / 362880 := by
    unfold kernelSinhDivLower6
    rw [show Real.sinh u / u -
          (1 + u ^ 2 / 6 + u ^ 4 / 120 + u ^ 6 / 5040) =
        (Real.sinh u -
          (u + u ^ 3 / 6 + u ^ 5 / 120 + u ^ 7 / 5040)) / u by
      field_simp [hu0.ne'],
      hTaylor]
    field_simp [hu0.ne']
  have hw0 : 0 ≤ w := hw.1.le
  have hwBound : Real.cosh w < (16 / 15 : ℝ) :=
    cosh_lt_sixteen_fifteenths hw0 (hw.2.trans hu)
  have hrem0 : 0 ≤ Real.cosh w * u ^ 8 / 362880 := by positivity
  have hremUpper :
      Real.cosh w * u ^ 8 / 362880 ≤
        (16 / 15 : ℝ) * u ^ 8 / 362880 := by
    gcongr
  constructor
  · linarith
  · unfold kernelSinhDivUpper8
    linarith

private theorem kernel_sech_envelope
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u < (1733 / 5000 : ℝ)) :
    0 ≤ 1 / Real.cosh u - kernelSechPolynomial6 u ∧
      1 / Real.cosh u - kernelSechPolynomial6 u ≤ kernelSechError u := by
  have hTaylor := kernel_cosh_taylor_bounds hu0 hu
  have huHalf : u < (1 / 2 : ℝ) := hu.trans (by norm_num)
  have huSq : u ^ 2 < (1 / 2 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ huHalf hu0 (by norm_num)
  have huSix : u ^ 6 < (1 / 2 : ℝ) ^ 6 :=
    pow_lt_pow_left₀ huHalf hu0 (by norm_num)
  have hS0 : 0 ≤ kernelSechPolynomial6 u := by
    unfold kernelSechPolynomial6
    have huFour0 : 0 ≤ u ^ 4 := by positivity
    nlinarith
  have hFactorUpper :
      kernelSechPolynomial6 u * kernelCoshUpper8 u - 1 =
        -(u ^ 8 *
          (122 * u ^ 6 + 6105 * u ^ 4 + 177120 * u ^ 2 + 1869660)) /
            54432000 := by
    unfold kernelSechPolynomial6 kernelCoshUpper8 kernelCoshLower6
    ring
  have hSCup : kernelSechPolynomial6 u * kernelCoshUpper8 u ≤ 1 := by
    have hnonneg : 0 ≤ u ^ 8 *
        (122 * u ^ 6 + 6105 * u ^ 4 + 177120 * u ^ 2 + 1869660) := by
      positivity
    nlinarith
  have hSCosh : kernelSechPolynomial6 u * Real.cosh u ≤ 1 :=
    (mul_le_mul_of_nonneg_left hTaylor.2 hS0).trans hSCup
  have hLower : 0 ≤ 1 / Real.cosh u - kernelSechPolynomial6 u := by
    rw [sub_nonneg, le_div_iff₀ (Real.cosh_pos u)]
    simpa only [one_mul] using hSCosh
  constructor
  · exact hLower
  · have hIdentity :
        1 / Real.cosh u - kernelSechPolynomial6 u =
          (1 - kernelSechPolynomial6 u * Real.cosh u) / Real.cosh u := by
      field_simp [(Real.cosh_pos u).ne']
    have hNumerator0 :
        0 ≤ 1 - kernelSechPolynomial6 u * Real.cosh u := by
      linarith
    have hDivide :
        (1 - kernelSechPolynomial6 u * Real.cosh u) / Real.cosh u ≤
          1 - kernelSechPolynomial6 u * Real.cosh u :=
      div_le_self hNumerator0 (Real.one_le_cosh u)
    have hSLower :
        kernelSechPolynomial6 u * kernelCoshLower6 u ≤
          kernelSechPolynomial6 u * Real.cosh u :=
      mul_le_mul_of_nonneg_left hTaylor.1 hS0
    have hErrorIdentity :
        1 - kernelSechPolynomial6 u * kernelCoshLower6 u =
          kernelSechError u := by
      unfold kernelSechPolynomial6 kernelCoshLower6 kernelSechError
      ring
    rw [hIdentity]
    calc
      _ ≤ 1 - kernelSechPolynomial6 u * Real.cosh u := hDivide
      _ ≤ 1 - kernelSechPolynomial6 u * kernelCoshLower6 u := by
        linarith
      _ = kernelSechError u := hErrorIdentity

private theorem kernel_csch_envelope
    {u : ℝ} (hu0 : 0 < u) (hu : u < (1733 / 5000 : ℝ)) :
    0 ≤ 1 / Real.sinh u - 1 / u - kernelCschRegularPolynomial5 u ∧
      1 / Real.sinh u - 1 / u - kernelCschRegularPolynomial5 u ≤
        kernelCschError u := by
  let A : ℝ := Real.sinh u / u
  have hTaylorRaw := kernel_sinh_div_taylor_bounds hu0 hu
  have hTaylor :
      kernelSinhDivLower6 u ≤ A ∧ A ≤ kernelSinhDivUpper8 u :=
    hTaylorRaw
  have hA1 : (1 : ℝ) ≤ A := by
    dsimp only [A]
    rw [le_div_iff₀ hu0]
    simpa using (Real.self_le_sinh_iff.mpr hu0.le)
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hA1
  have huHalf : u < (1 / 2 : ℝ) := hu.trans (by norm_num)
  have huSq : u ^ 2 < (1 / 2 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ huHalf hu0.le (by norm_num)
  have huSix : u ^ 6 < (1 / 2 : ℝ) ^ 6 :=
    pow_lt_pow_left₀ huHalf hu0.le (by norm_num)
  have hQ0 : 0 ≤ kernelCschMultiplier6 u := by
    unfold kernelCschMultiplier6 kernelCschRegularPolynomial5
    have huFour0 : 0 ≤ u ^ 4 := by positivity
    nlinarith
  have hFactorUpper :
      kernelCschMultiplier6 u * kernelSinhDivUpper8 u - 1 =
        -(u ^ 8 *
          (62 * u ^ 6 + 3597 * u ^ 4 + 141120 * u ^ 2 + 2158380)) /
            10287648000 := by
    unfold kernelCschMultiplier6 kernelCschRegularPolynomial5
      kernelSinhDivUpper8 kernelSinhDivLower6
    ring
  have hQAup : kernelCschMultiplier6 u * kernelSinhDivUpper8 u ≤ 1 := by
    have hnonneg : 0 ≤ u ^ 8 *
        (62 * u ^ 6 + 3597 * u ^ 4 + 141120 * u ^ 2 + 2158380) := by
      positivity
    nlinarith
  have hQA : kernelCschMultiplier6 u * A ≤ 1 :=
    (mul_le_mul_of_nonneg_left hTaylor.2 hQ0).trans hQAup
  have hQleInv : kernelCschMultiplier6 u ≤ 1 / A := by
    rw [le_div_iff₀ hApos]
    simpa only [one_mul] using hQA
  have hSinhPos : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu0
  have hMainIdentity :
      1 / Real.sinh u - 1 / u - kernelCschRegularPolynomial5 u =
        (1 / A - kernelCschMultiplier6 u) / u := by
    dsimp only [A]
    unfold kernelCschMultiplier6
    field_simp [hu0.ne', hSinhPos.ne']
    ring
  have hLower :
      0 ≤ 1 / Real.sinh u - 1 / u - kernelCschRegularPolynomial5 u := by
    rw [hMainIdentity]
    exact div_nonneg (sub_nonneg.mpr hQleInv) hu0.le
  constructor
  · exact hLower
  · have hInvIdentity :
        1 / A - kernelCschMultiplier6 u =
          (1 - kernelCschMultiplier6 u * A) / A := by
      field_simp [hApos.ne']
    have hNumerator0 : 0 ≤ 1 - kernelCschMultiplier6 u * A := by
      linarith
    have hDivideA :
        (1 - kernelCschMultiplier6 u * A) / A ≤
          1 - kernelCschMultiplier6 u * A :=
      div_le_self hNumerator0 hA1
    have hQLower :
        kernelCschMultiplier6 u * kernelSinhDivLower6 u ≤
          kernelCschMultiplier6 u * A :=
      mul_le_mul_of_nonneg_left hTaylor.1 hQ0
    have hErrorIdentity :
        1 - kernelCschMultiplier6 u * kernelSinhDivLower6 u =
          u * kernelCschError u := by
      unfold kernelCschMultiplier6 kernelCschRegularPolynomial5
        kernelSinhDivLower6 kernelCschError
      ring
    have hInner :
        1 / A - kernelCschMultiplier6 u ≤ u * kernelCschError u := by
      rw [hInvIdentity]
      calc
        _ ≤ 1 - kernelCschMultiplier6 u * A := hDivideA
        _ ≤ 1 - kernelCschMultiplier6 u * kernelSinhDivLower6 u := by
          linarith
        _ = u * kernelCschError u := hErrorIdentity
    rw [hMainIdentity]
    rw [div_le_iff₀ hu0]
    simpa only [div_mul_cancel₀ _ hu0.ne', mul_comm] using hInner

private theorem yoshidaRegularKernel_two_mul (u : ℝ) (hu : 0 < u) :
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

private theorem yoshidaRegularKernelPolynomial6_two_mul (u : ℝ) :
    yoshidaRegularKernelPolynomial6 (2 * u) =
      (1 / 4 : ℝ) *
        (kernelSechPolynomial6 u + kernelCschRegularPolynomial5 u) := by
  unfold yoshidaRegularKernelPolynomial6 kernelSechPolynomial6
    kernelCschRegularPolynomial5
  ring

private theorem yoshidaRegularKernelPolynomial6_envelope_core
    {t : ℝ} (ht0 : 0 ≤ t) (htlog : t ≤ Real.log 2) :
    0 ≤ yoshidaRegularKernel t - yoshidaRegularKernelPolynomial6 t ∧
      yoshidaRegularKernel t - yoshidaRegularKernelPolynomial6 t <
        (1 / 500000 : ℝ) := by
  rcases eq_or_lt_of_le ht0 with rfl | htpos
  · constructor <;>
      norm_num [yoshidaRegularKernel, yoshidaRegularKernelPolynomial6]
  · let u : ℝ := t / 2
    have hu0 : 0 < u := by
      dsimp only [u]
      linarith
    have hu : u < (1733 / 5000 : ℝ) := by
      dsimp only [u]
      have hlog := strict_log_two_fine_bounds.2
      linarith
    have hSech := kernel_sech_envelope hu0.le hu
    have hCsch := kernel_csch_envelope hu0 hu
    have htEq : t = 2 * u := by
      dsimp only [u]
      ring
    have hDifference :
        yoshidaRegularKernel t - yoshidaRegularKernelPolynomial6 t =
          (1 / 4 : ℝ) *
            ((1 / Real.cosh u - kernelSechPolynomial6 u) +
              (1 / Real.sinh u - 1 / u -
                kernelCschRegularPolynomial5 u)) := by
      rw [htEq, yoshidaRegularKernel_two_mul u hu0,
        yoshidaRegularKernelPolynomial6_two_mul]
      ring
    have hError :
        yoshidaRegularKernel t - yoshidaRegularKernelPolynomial6 t ≤
          (1 / 4 : ℝ) * (kernelSechError u + kernelCschError u) := by
      rw [hDifference]
      nlinarith
    have hSechStrict :
        kernelSechError u < kernelSechError (1733 / 5000 : ℝ) := by
      unfold kernelSechError
      gcongr
    have hCschStrict :
        kernelCschError u < kernelCschError (1733 / 5000 : ℝ) := by
      unfold kernelCschError
      gcongr
    have hEndpoint :
        (1 / 4 : ℝ) *
            (kernelSechError (1733 / 5000 : ℝ) +
              kernelCschError (1733 / 5000 : ℝ)) <
          (1 / 500000 : ℝ) := by
      norm_num [kernelSechError, kernelCschError]
    constructor
    · rw [hDifference]
      nlinarith [hSech.1, hCsch.1]
    · exact hError.trans_lt <| by
        have :
            (1 / 4 : ℝ) * (kernelSechError u + kernelCschError u) <
              (1 / 4 : ℝ) *
                (kernelSechError (1733 / 5000 : ℝ) +
                  kernelCschError (1733 / 5000 : ℝ)) := by
          nlinarith
        exact this.trans hEndpoint

/-- The degree-six regular-kernel envelope is normalized at the removable
singularity. -/
theorem yoshidaRegularKernelPolynomial6_zero :
    yoshidaRegularKernelPolynomial6 0 = (1 / 4 : ℝ) := by
  norm_num [yoshidaRegularKernelPolynomial6]

private theorem abs_cosh_sub_evenTaylor6_lt
    {z : ℝ} (hz0 : 0 ≤ z) (hz : z < (1733 / 10000 : ℝ)) :
    |Real.cosh z - (1 + z ^ 2 / 2 + z ^ 4 / 24 + z ^ 6 / 720)| <
      (1 / 48000000000 : ℝ) := by
  rcases eq_or_lt_of_le hz0 with rfl | hzpos
  · norm_num
  · rcases taylor_mean_remainder_lagrange_iteratedDeriv
        (f := Real.cosh) (x₀ := 0) (x := z) (n := 7) hzpos
        Real.contDiff_cosh.contDiffOn with ⟨w, hw, hTaylor⟩
    have hTaylorEval :
        taylorWithinEval Real.cosh 7 (Icc 0 z) 0 z =
          1 + z ^ 2 / 2 + z ^ 4 / 24 + z ^ 6 / 720 := by
      have hder (n : ℕ) :
          iteratedDerivWithin n Real.cosh (Icc 0 z) 0 =
            iteratedDeriv n Real.cosh 0 :=
        Real.iteratedDerivWithin_cosh_Icc n hzpos ⟨le_rfl, hz0⟩
      rw [taylor_within_apply]
      simp [hder, Finset.sum_range_succ]
      ring
    rw [hTaylorEval] at hTaylor
    norm_num [Real.iteratedDeriv_even_cosh] at hTaylor
    have hw0 : 0 ≤ w := hw.1.le
    have hwUpper : w < (1733 / 10000 : ℝ) := hw.2.trans hz
    have hu0 : 0 ≤ w ^ 2 / 2 := by positivity
    have hu61 : w ^ 2 / 2 < (1 / 61 : ℝ) := by
      have hwSq : w ^ 2 < (1733 / 10000 : ℝ) ^ 2 :=
        pow_lt_pow_left₀ hwUpper hw0 (by norm_num)
      norm_num at hwSq ⊢
      nlinarith
    have hu1 : w ^ 2 / 2 < (1 : ℝ) := hu61.trans (by norm_num)
    have hExp : Real.exp (w ^ 2 / 2) ≤ 1 / (1 - w ^ 2 / 2) :=
      Real.exp_bound_div_one_sub_of_interval hu0 hu1
    have hFrac : 1 / (1 - w ^ 2 / 2) < (61 / 60 : ℝ) := by
      rw [div_lt_iff₀ (sub_pos.mpr hu1)]
      nlinarith
    have hCosh : Real.cosh w < (61 / 60 : ℝ) :=
      (Real.cosh_le_exp_half_sq w).trans_lt (hExp.trans_lt hFrac)
    have hzPow : z ^ 8 < (1733 / 10000 : ℝ) ^ 8 :=
      pow_lt_pow_left₀ hz hz0 (by norm_num)
    have hrem0 : 0 ≤ Real.cosh w * z ^ 8 / 40320 := by positivity
    have hremUpper :
        Real.cosh w * z ^ 8 / 40320 <
          (61 / 60 : ℝ) * (1733 / 10000 : ℝ) ^ 8 / 40320 := by
      gcongr
    have hrat :
        (61 / 60 : ℝ) * (1733 / 10000 : ℝ) ^ 8 / 40320 <
          (1 / 48000000000 : ℝ) := by
      norm_num
    rw [hTaylor, abs_of_nonneg hrem0]
    exact hremUpper.trans hrat

private theorem abs_cosh_sub_yoshidaEndpointCoshPolynomial6_lt_core
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    |Real.cosh (yoshidaEndpointA * x / 2) -
        yoshidaEndpointCoshPolynomial6 x| <
      (1 / 48000000000 : ℝ) := by
  let z : ℝ := |yoshidaEndpointA * x / 2|
  have hxAbs : |x| ≤ 1 := abs_le.mpr hx
  have hz0 : 0 ≤ z := abs_nonneg _
  have ha : yoshidaEndpointA < (1733 / 5000 : ℝ) := by
    unfold yoshidaEndpointA
    linarith [strict_log_two_fine_bounds.2]
  have hz : z < (1733 / 10000 : ℝ) := by
    dsimp only [z]
    rw [abs_div, abs_mul, abs_of_nonneg yoshidaEndpointA_pos.le]
    norm_num
    have hmul := mul_le_mul_of_nonneg_left hxAbs yoshidaEndpointA_pos.le
    nlinarith
  have hpoly :
      1 + z ^ 2 / 2 + z ^ 4 / 24 + z ^ 6 / 720 =
        yoshidaEndpointCoshPolynomial6 x := by
    have hzSq : z ^ 2 = (yoshidaEndpointA * x / 2) ^ 2 := by
      dsimp only [z]
      exact sq_abs _
    rw [show z ^ 4 = (z ^ 2) ^ 2 by ring,
      show z ^ 6 = (z ^ 2) ^ 3 by ring, hzSq]
    unfold yoshidaEndpointCoshPolynomial6
    ring
  have hcosh : Real.cosh z = Real.cosh (yoshidaEndpointA * x / 2) := by
    dsimp only [z]
    exact Real.cosh_abs _
  rw [← hcosh, ← hpoly]
  exact abs_cosh_sub_evenTaylor6_lt hz0 hz

/-- The fixed endpoint cosh factor is uniformly captured by its even
degree-six Taylor polynomial. -/
theorem abs_cosh_sub_yoshidaEndpointCoshPolynomial6_lt
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    |Real.cosh (yoshidaEndpointA * x / 2) -
        yoshidaEndpointCoshPolynomial6 x| <
      (1 / 48000000000 : ℝ) := by
  exact abs_cosh_sub_yoshidaEndpointCoshPolynomial6_lt_core hx

/-- On the full endpoint interval the sixth-order polynomial lies below the
regular kernel, with a uniform rational error. -/
theorem yoshidaRegularKernelPolynomial6_envelope
    {t : ℝ} (ht0 : 0 ≤ t) (htlog : t ≤ Real.log 2) :
    0 ≤ yoshidaRegularKernel t - yoshidaRegularKernelPolynomial6 t ∧
      yoshidaRegularKernel t - yoshidaRegularKernelPolynomial6 t <
        (1 / 500000 : ℝ) := by
  exact yoshidaRegularKernelPolynomial6_envelope_core ht0 htlog

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
