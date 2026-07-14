import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseDiskSchur

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseProfileStaticSplit

noncomputable section

open YoshidaEndpointOddCleanPositive
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointChannelRadius
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseDiskSchur
open YoshidaFactorTwoPhaseFullProfile

/-!
# Profile-level static parity split

The two phase-free parity splits interpolate the entire closed phase disk.
This is the scalar profile analogue of the unnormalized Hadamard reduction
used by the concrete Toeplitz matrix, but it does not choose a basis or a
finite cutoff.
-/

/-- Pure scalar form of the static-split interpolation.  The first split
pairs the positive endpoint of the even diagonal with the negative endpoint
of the odd diagonal; the second split uses the opposite pairing. -/
theorem scalar_phase_nonneg_of_static_splits
    (QE PE QO PO J a b : ℝ)
    (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hPlus : ∀ r s : ℝ,
      0 ≤ r ^ 2 * (QE + PE) + s ^ 2 * (QO - PO) + r * s * J)
    (hMinus : ∀ r s : ℝ,
      0 ≤ r ^ 2 * (QE - PE) + s ^ 2 * (QO + PO) + r * s * J) :
    0 ≤ QE + QO + a * (PE + PO) + b * J := by
  have haUpper : a ≤ 1 := by
    nlinarith [sq_nonneg b, sq_nonneg (a - 1)]
  have haLower : -1 ≤ a := by
    nlinarith [sq_nonneg b, sq_nonneg (a + 1)]
  have hLambda : 0 ≤ (1 + a) / 2 := by linarith
  have hMu : 0 ≤ (1 - a) / 2 := by linarith
  let u : ℝ := Real.sqrt ((1 + a) / 2)
  let v : ℝ := Real.sqrt ((1 - a) / 2)
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hv : 0 ≤ v := Real.sqrt_nonneg _
  have huSq : u ^ 2 = (1 + a) / 2 := by
    exact Real.sq_sqrt hLambda
  have hvSq : v ^ 2 = (1 - a) / 2 := by
    exact Real.sq_sqrt hMu
  let c : ℝ := 2 * u * v
  have hc : 0 ≤ c := by
    dsimp only [c]
    positivity
  have hcSq : c ^ 2 = 1 - a ^ 2 := by
    dsimp only [c]
    rw [mul_pow, mul_pow, huSq, hvSq]
    ring
  have hbSq : b ^ 2 ≤ c ^ 2 := by
    rw [hcSq]
    linarith
  have hbUpper : b ≤ c := by
    by_contra hbc
    have hcb : c < b := lt_of_not_ge hbc
    have hb0 : 0 < b := hc.trans_lt hcb
    have hprod : 0 < (b - c) * (b + c) :=
      mul_pos (sub_pos.mpr hcb) (add_pos_of_pos_of_nonneg hb0 hc)
    nlinarith
  have hbLower : -c ≤ b := by
    by_contra hbc
    have hbc' : b < -c := lt_of_not_ge hbc
    have hneg : 0 < -b - c := by linarith
    have hsum : 0 < -b + c := by linarith
    have hprod : 0 < (-b - c) * (-b + c) := mul_pos hneg hsum
    nlinarith
  let D : ℝ := QE + QO + a * (PE + PO)
  have hPositiveCross : 0 ≤ D + c * J := by
    have h₁ := hPlus u v
    have h₂ := hMinus v u
    dsimp only [D, c] at h₁ h₂ ⊢
    rw [huSq, hvSq] at h₁ h₂
    nlinarith
  have hNegativeCross : 0 ≤ D - c * J := by
    have h₁ := hPlus u (-v)
    have h₂ := hMinus v (-u)
    dsimp only [D, c] at h₁ h₂ ⊢
    rw [neg_sq, huSq, hvSq] at h₁ h₂
    nlinarith
  change 0 ≤ D + b * J
  by_cases hJ : 0 ≤ J
  · have hscaled := mul_le_mul_of_nonneg_right hbLower hJ
    nlinarith
  · have hJ' : J ≤ 0 := le_of_not_ge hJ
    have hscaled := mul_le_mul_of_nonpos_right hbUpper hJ'
    nlinarith

/-- If both static parity splits are nonnegative for every independent
rescaling of two fixed profiles, then their complete same-seed phase is
nonnegative everywhere in the closed disk. -/
theorem factorTwoEndpointChannelPhase_nonneg_of_profile_static_splits
    (e o : ℝ → ℝ) (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hPlus : ∀ r s : ℝ,
      0 ≤ r ^ 2 * factorTwoEndpointPhaseDiagonal e 1 +
        s ^ 2 * factorTwoEndpointPhaseDiagonal o (-1) +
        r * s * factorTwoCenteredAlternatingCoupling e o)
    (hMinus : ∀ r s : ℝ,
      0 ≤ r ^ 2 * factorTwoEndpointPhaseDiagonal e (-1) +
        s ^ 2 * factorTwoEndpointPhaseDiagonal o 1 +
        r * s * factorTwoCenteredAlternatingCoupling e o) :
    0 ≤ factorTwoEndpointChannelPhase e o a b := by
  have h := scalar_phase_nonneg_of_static_splits
    (yoshidaEndpointOddCleanQuadratic e)
    (factorTwoCenteredSymmetricPerturbation e)
    (yoshidaEndpointOddCleanQuadratic o)
    (factorTwoCenteredSymmetricPerturbation o)
    (factorTwoCenteredAlternatingCoupling e o)
    a b hab
  have hResult := h (by
    intro r s
    simpa only [factorTwoEndpointPhaseDiagonal, one_mul, neg_one_mul,
      sub_eq_add_neg] using hPlus r s) (by
    intro r s
    simpa only [factorTwoEndpointPhaseDiagonal, one_mul, neg_one_mul,
      sub_eq_add_neg] using hMinus r s)
  rw [factorTwoEndpointChannelPhase_eq_diagonals]
  unfold factorTwoEndpointPhaseDiagonal
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseProfileStaticSplit
