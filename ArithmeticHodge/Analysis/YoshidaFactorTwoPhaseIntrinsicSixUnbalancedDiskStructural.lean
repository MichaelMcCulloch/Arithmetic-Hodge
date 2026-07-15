import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticSplitStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedDiskStructural

noncomputable section

open YoshidaEndpointOddResidualRegularity
open YoshidaFactorTwoPhaseDiskSchur
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicFourP45Reduction
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixSchurReduction
open YoshidaFactorTwoPhaseIntrinsicSixStaticPlusObstruction
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticSplitStructural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLowSchur

/-!
# Closed-disk completion of the unbalanced intrinsic six-mode split

The projective chart misses the phase point `(-1, 0)`.  The argument below
instead interpolates the two corrected endpoint forms directly.  Their fixed
bilinear transfers occur with opposite signs and cancel before the disk
estimate is used.
-/

/-- Scalar square-root interpolation with an arbitrary transferred bilinear
term.  The transfer is absent from the conclusion because its two endpoint
copies cancel exactly. -/
theorem scalar_phase_nonneg_of_unbalanced_static_splits
    (QE PE QO PO J H a b : ℝ)
    (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hPlus : ∀ r s : ℝ,
      0 ≤ r ^ 2 * (QE + PE) + s ^ 2 * (QO - PO) +
        r * s * (J - 2 * H))
    (hMinus : ∀ r s : ℝ,
      0 ≤ r ^ 2 * (QE - PE) + s ^ 2 * (QO + PO) +
        r * s * (J + 2 * H)) :
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

/-- Coordinate meaning of the complete intrinsic six-mode phase.  The odd
static form carries the opposite endpoint convention, hence its argument is
`-a`. -/
theorem factorTwoEndpointChannelPhase_intrinsicSix_eq_static_coordinates
    (c0 c2 c4 c1 c3 c5 a b : ℝ) :
    factorTwoEndpointChannelPhase
        (factorTwoEvenStructuralLowProfile c0 c2 +
          factorTwoIntrinsicSixEvenTail c4)
        (factorTwoIntrinsicSixOddTail c1 c3 c5) a b =
      factorTwoIntrinsicSixStaticEven a c0 c2 c4 +
        factorTwoIntrinsicSixStaticOdd (-a) c1 c3 c5 +
        b * factorTwoIntrinsicSixStaticAlternating
          c0 c2 c4 c1 c3 c5 := by
  have hdecomp := factorTwoEndpointChannelPhase_add_add_eq_low_mixed_tail
    (factorTwoEvenStructuralLowProfile c0 c2)
    (fun y ↦ c4 * factorTwoCenteredP4 y)
    (factorTwoOddStructuralLowProfile c1 c3)
    (fun y ↦ c5 * factorTwoCenteredP5 y)
    (continuous_factorTwoEvenStructuralLowProfile c0 c2)
    (continuous_const.mul continuous_factorTwoCenteredP4)
    (continuous_factorTwoOddStructuralLowProfile c1 c3)
    (continuous_const.mul continuous_factorTwoCenteredP5) a b
  have hlow := factorTwoEndpointChannelPhase_intrinsicLow_expansion
    c0 c2 c1 c3 a b
  have hmixed := factorTwoIntrinsicFourP45Mixed_eq_cross_entries
    c0 c2 c1 c3 c4 c5 a b
  have htail := factorTwoEndpointChannelPhase_P4_P5_expansion
    c4 c5 a b
  unfold factorTwoIntrinsicSixEvenTail factorTwoIntrinsicSixOddTail
  rw [hdecomp, hlow, htail]
  rw [show factorTwoEndpointLowTailMixed
      (factorTwoEvenStructuralLowProfile c0 c2)
      (fun y ↦ c4 * factorTwoCenteredP4 y)
      (factorTwoOddStructuralLowProfile c1 c3)
      (fun y ↦ c5 * factorTwoCenteredP5 y) a b =
        factorTwoIntrinsicFourP45Mixed c0 c2 c1 c3 c4 c5 a b by rfl,
    hmixed]
  unfold factorTwoIntrinsicSixStaticEven
    factorTwoIntrinsicSixStaticOdd
    factorTwoIntrinsicSixStaticAlternating
    factorTwoIntrinsicOddPhaseQuadratic
    factorTwoIntrinsicAlternatingRow0
    factorTwoIntrinsicAlternatingRow2
    factorTwoIntrinsicP45Alternating
  ring

/-- The two corrected unbalanced endpoint forms close the complete intrinsic
six-mode phase on the whole closed phase disk.  In particular, no projective
chart exception remains at `(-1, 0)`. -/
theorem factorTwoEndpointChannelPhase_intrinsicSix_nonneg_of_unbalanced_static
    (hplus : FactorTwoIntrinsicSixUnbalancedStaticPlusNonnegative)
    (hminus : FactorTwoIntrinsicSixUnbalancedStaticMinusNonnegative)
    (c0 c2 c4 c1 c3 c5 a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    0 ≤ factorTwoEndpointChannelPhase
      (factorTwoEvenStructuralLowProfile c0 c2 +
        factorTwoIntrinsicSixEvenTail c4)
      (factorTwoIntrinsicSixOddTail c1 c3 c5) a b := by
  let EPlus := factorTwoIntrinsicSixStaticEven 1 c0 c2 c4
  let EMinus := factorTwoIntrinsicSixStaticEven (-1) c0 c2 c4
  let OMinus := factorTwoIntrinsicSixStaticOdd 1 c1 c3 c5
  let OPlus := factorTwoIntrinsicSixStaticOdd (-1) c1 c3 c5
  let QE := (EPlus + EMinus) / 2
  let PE := (EPlus - EMinus) / 2
  let QO := (OMinus + OPlus) / 2
  let PO := (OPlus - OMinus) / 2
  let J := factorTwoIntrinsicSixStaticAlternating c0 c2 c4 c1 c3 c5
  let H := factorTwoIntrinsicSixUnbalancedTransfer c0 c2 c4 c1 c3 c5
  have hPlusScalar : ∀ r s : ℝ,
      0 ≤ r ^ 2 * (QE + PE) + s ^ 2 * (QO - PO) +
        r * s * (J - 2 * H) := by
    intro r s
    have h := hplus
      (r * c0) (r * c2) (r * c4)
      (s * c1) (s * c3) (s * c5)
    have hscale :
        factorTwoIntrinsicSixUnbalancedStaticPlus
            (r * c0) (r * c2) (r * c4)
            (s * c1) (s * c3) (s * c5) =
          r ^ 2 * EPlus + s ^ 2 * OMinus + r * s * (J - 2 * H) := by
      dsimp only [EPlus, OMinus, J, H]
      unfold factorTwoIntrinsicSixUnbalancedStaticPlus
        factorTwoIntrinsicSixStaticEven
        factorTwoIntrinsicSixStaticOdd
        factorTwoIntrinsicSixStaticAlternating
        factorTwoIntrinsicSixUnbalancedTransfer
        factorTwoIntrinsicOddPhaseQuadratic
      ring
    rw [hscale] at h
    dsimp only [QE, PE, QO, PO]
    nlinarith
  have hMinusScalar : ∀ r s : ℝ,
      0 ≤ r ^ 2 * (QE - PE) + s ^ 2 * (QO + PO) +
        r * s * (J + 2 * H) := by
    intro r s
    have h := hminus
      (r * c0) (r * c2) (r * c4)
      (s * c1) (s * c3) (s * c5)
    have hscale :
        factorTwoIntrinsicSixUnbalancedStaticMinus
            (r * c0) (r * c2) (r * c4)
            (s * c1) (s * c3) (s * c5) =
          r ^ 2 * EMinus + s ^ 2 * OPlus + r * s * (J + 2 * H) := by
      dsimp only [EMinus, OPlus, J, H]
      unfold factorTwoIntrinsicSixUnbalancedStaticMinus
        factorTwoIntrinsicSixStaticEven
        factorTwoIntrinsicSixStaticOdd
        factorTwoIntrinsicSixStaticAlternating
        factorTwoIntrinsicSixUnbalancedTransfer
        factorTwoIntrinsicOddPhaseQuadratic
      ring
    rw [hscale] at h
    dsimp only [QE, PE, QO, PO]
    nlinarith
  have hScalar := scalar_phase_nonneg_of_unbalanced_static_splits
    QE PE QO PO J H a b hab hPlusScalar hMinusScalar
  have hEvenAffine :
      (EPlus + EMinus) / 2 + a * ((EPlus - EMinus) / 2) =
        factorTwoIntrinsicSixStaticEven a c0 c2 c4 := by
    dsimp only [EPlus, EMinus]
    unfold factorTwoIntrinsicSixStaticEven
      factorTwoStructuralPhaseLow00
      factorTwoStructuralPhaseLow02
      factorTwoStructuralPhaseLow22
      factorTwoIntrinsicFourP45Cross04
      factorTwoIntrinsicFourP45Cross24
      factorTwoIntrinsicP4PhaseDiagonal
    ring
  have hOddAffine :
      (OMinus + OPlus) / 2 + a * ((OPlus - OMinus) / 2) =
        factorTwoIntrinsicSixStaticOdd (-a) c1 c3 c5 := by
    dsimp only [OMinus, OPlus]
    unfold factorTwoIntrinsicSixStaticOdd
      factorTwoIntrinsicOddPhaseQuadratic
      factorTwoIntrinsicOddPhaseLow11
      factorTwoIntrinsicOddPhaseLow13
      factorTwoIntrinsicOddPhaseLow33
      factorTwoIntrinsicFourP45Cross15
      factorTwoIntrinsicFourP45Cross35
      factorTwoIntrinsicP5PhaseDiagonal
    ring
  have hCoordinates :
      QE + QO + a * (PE + PO) + b * J =
        factorTwoIntrinsicSixStaticEven a c0 c2 c4 +
          factorTwoIntrinsicSixStaticOdd (-a) c1 c3 c5 +
          b * factorTwoIntrinsicSixStaticAlternating
            c0 c2 c4 c1 c3 c5 := by
    calc
      QE + QO + a * (PE + PO) + b * J =
          ((EPlus + EMinus) / 2 + a * ((EPlus - EMinus) / 2)) +
            ((OMinus + OPlus) / 2 + a * ((OPlus - OMinus) / 2)) +
            b * J := by
              dsimp only [QE, PE, QO, PO]
              ring
      _ = factorTwoIntrinsicSixStaticEven a c0 c2 c4 +
            factorTwoIntrinsicSixStaticOdd (-a) c1 c3 c5 +
            b * factorTwoIntrinsicSixStaticAlternating
              c0 c2 c4 c1 c3 c5 := by
              rw [hEvenAffine, hOddAffine]
  rw [factorTwoEndpointChannelPhase_intrinsicSix_eq_static_coordinates]
  rw [← hCoordinates]
  exact hScalar

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedDiskStructural
