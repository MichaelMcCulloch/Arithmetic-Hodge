import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineComplementSchurStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineBalancedPencilStructural

noncomputable section

open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicNineComplementSchurStructural
open YoshidaFactorTwoPhaseIntrinsicNineFullMixedDecompositionStructural
open YoshidaFactorTwoPhaseIntrinsicNineUnbalancedStaticDiskStructural
open YoshidaFactorTwoPhaseP678CombinedResidualSchurStructural

/-!
# The corrected cutoff-nine balanced pencil

The singular square cannot be allocated separately from its signed remainder
on the constant mode.  The honest target is instead domination of the
already-certified `P6/P7/P8` pencil by the complete low-plus-residual phase
pencil.  After the exact mixed decomposition, this is precisely the scalar
quadratic pencil whose determinant is the remaining balanced-complement
bound.
-/

/-- Nonnegativity of the complete phase pencil after subtracting the
allocated `P6/P7/P8` pencil gives exactly the balanced survivor determinant.
No converse use of complement addition is made. -/
theorem factorTwoIntrinsicNineRemainingMixed_sq_le_balanced_complement_of_full_pencil
    (eR oR : ℝ → ℝ) (heRc : Continuous eR) (hoRc : Continuous oR)
    (heLocal : LocallyLipschitzOn (Icc (-1) 1) eR)
    (hoLocal : LocallyLipschitzOn (Icc (-1) 1) oR)
    (hoRo : Function.Odd oR)
    (heGap : centeredLegendreMomentsVanishBelow eR 9)
    (hoGap : centeredLegendreMomentsVanishBelow oR 9)
    (c0 c2 c4 c6 c8 c1 c3 c5 c7 a b : ℝ)
    (hpencil : ∀ c d : ℝ,
      0 ≤
        factorTwoEndpointChannelPhase
            (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8)
            (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) a b * c ^ 2 +
          2 * factorTwoEndpointLowTailMixed
              (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8) eR
              (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) oR a b * c * d +
          factorTwoEndpointChannelPhase eR oR a b * d ^ 2 -
        ((15 / 16 : ℝ) *
              factorTwoIntrinsicNineP678LowReserve c6 c7 c8 * c ^ 2 +
          2 * factorTwoP678ResidualCombinedForwardMixed
              eR oR c6 c7 c8 a b * c * d +
          (14 / 15 : ℝ) *
              factorTwoIntrinsicNineResidualReserve eR oR * d ^ 2)) :
    factorTwoIntrinsicNineRemainingMixed eR oR
          c0 c2 c4 c6 c8 c1 c3 c5 c7 a b ^ 2 ≤
      (factorTwoEndpointChannelPhase
            (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8)
            (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) a b -
          (15 / 16 : ℝ) *
            factorTwoIntrinsicNineP678LowReserve c6 c7 c8) *
        (factorTwoEndpointChannelPhase eR oR a b -
          (14 / 15 : ℝ) *
            factorTwoIntrinsicNineResidualReserve eR oR) := by
  let L := factorTwoEndpointChannelPhase
    (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8)
    (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) a b
  let T := factorTwoEndpointChannelPhase eR oR a b
  let X := factorTwoIntrinsicNineP678LowReserve c6 c7 c8
  let Y := factorTwoIntrinsicNineResidualReserve eR oR
  let X' := (15 / 16 : ℝ) * X
  let Y' := (14 / 15 : ℝ) * Y
  let M := factorTwoEndpointLowTailMixed
    (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8) eR
    (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) oR a b
  let Z := factorTwoP678ResidualCombinedForwardMixed
    eR oR c6 c7 c8 a b
  let S := factorTwoIntrinsicNineRemainingMixed eR oR
    c0 c2 c4 c6 c8 c1 c3 c5 c7 a b
  have hmix : M = Z + S := by
    simpa only [M, Z, S] using
      factorTwoEndpointLowTailMixed_intrinsicNine_eq_P678_add_remaining
        eR oR heRc hoRc heLocal hoLocal hoRo heGap hoGap
        c0 c2 c4 c6 c8 c1 c3 c5 c7 a b
  have hq : ∀ c d : ℝ,
      0 ≤ (L - X') * c ^ 2 + 2 * S * c * d + (T - Y') * d ^ 2 := by
    intro c d
    have h := hpencil c d
    change 0 ≤ L * c ^ 2 + 2 * M * c * d + T * d ^ 2 -
      (X' * c ^ 2 + 2 * Z * c * d + Y' * d ^ 2) at h
    rw [hmix] at h
    nlinarith
  have hdet :=
    ((real_quadratic_pencil_nonneg_iff (L - X') (T - Y') S).mp hq).2.2
  simpa only [L, T, X', Y', X, Y, S] using hdet

/-- Direct outer-Schur handoff from the corrected full-pencil dominance.
This packages the exact target consumed by the already-proved sharp
`P6/P7/P8` determinant without weakening it to separate absolute bounds. -/
theorem factorTwoEndpointLowTailMixed_intrinsicNine_sq_le_of_balanced_full_pencil
    (eR oR : ℝ → ℝ) (heRc : Continuous eR) (hoRc : Continuous oR)
    (heLocal : LocallyLipschitzOn (Icc (-1) 1) eR)
    (hoLocal : LocallyLipschitzOn (Icc (-1) 1) oR)
    (heRe : Function.Even eR) (hoRo : Function.Odd oR)
    (heGap : centeredLegendreMomentsVanishBelow eR 9)
    (hoGap : centeredLegendreMomentsVanishBelow oR 9)
    (c0 c2 c4 c6 c8 c1 c3 c5 c7 a b : ℝ)
    (hab : a ^ 2 + b ^ 2 ≤ 1)
    (hlowComplement :
      0 ≤ factorTwoEndpointChannelPhase
          (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8)
          (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) a b -
        factorTwoIntrinsicNineP678LowReserve c6 c7 c8)
    (htailComplement :
      0 ≤ factorTwoEndpointChannelPhase eR oR a b -
        factorTwoIntrinsicNineResidualReserve eR oR)
    (hpencil : ∀ c d : ℝ,
      0 ≤
        factorTwoEndpointChannelPhase
            (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8)
            (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) a b * c ^ 2 +
          2 * factorTwoEndpointLowTailMixed
              (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8) eR
              (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) oR a b * c * d +
          factorTwoEndpointChannelPhase eR oR a b * d ^ 2 -
        ((15 / 16 : ℝ) *
              factorTwoIntrinsicNineP678LowReserve c6 c7 c8 * c ^ 2 +
          2 * factorTwoP678ResidualCombinedForwardMixed
              eR oR c6 c7 c8 a b * c * d +
          (14 / 15 : ℝ) *
              factorTwoIntrinsicNineResidualReserve eR oR * d ^ 2)) :
    factorTwoEndpointLowTailMixed
          (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8) eR
          (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) oR a b ^ 2 ≤
      factorTwoEndpointChannelPhase
          (factorTwoIntrinsicNineEvenProfile c0 c2 c4 c6 c8)
          (factorTwoIntrinsicNineOddProfile c1 c3 c5 c7) a b *
        factorTwoEndpointChannelPhase eR oR a b := by
  apply factorTwoEndpointLowTailMixed_intrinsicNine_sq_le_of_balanced_complement
    eR oR heRc hoRc heLocal hoLocal heRe hoRo heGap hoGap
      c0 c2 c4 c6 c8 c1 c3 c5 c7 a b hab
      hlowComplement htailComplement
  exact
    factorTwoIntrinsicNineRemainingMixed_sq_le_balanced_complement_of_full_pencil
      eR oR heRc hoRc heLocal hoLocal hoRo heGap hoGap
        c0 c2 c4 c6 c8 c1 c3 c5 c7 a b hpencil

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineBalancedPencilStructural
