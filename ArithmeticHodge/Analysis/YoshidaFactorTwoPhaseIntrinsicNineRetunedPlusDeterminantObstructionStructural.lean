import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineRetunedPlusGatesPositive

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineRetunedPlusDeterminantObstructionStructural

noncomputable section

open ThreeByThreeRankOneSchur
open YoshidaFactorTwoPhaseIntrinsicFourP45MixedExpansion
open YoshidaFactorTwoPhaseIntrinsicNineRetunedPlusGatesPositive
open YoshidaFactorTwoPhaseIntrinsicNineStaticFinalThreePositiveStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4Schur
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticEvenPositiveStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticPlusDeterminantStructural
open YoshidaFactorTwoPhaseIntrinsicSixUnbalancedStaticSchurReductionStructural

/-!
# A structural obstruction to the retuned positive final-three gate

The first two retuned positive gates are genuinely positive.  A candidate
obstruction to the third is the rational six-mode vector

`(c₀,c₂,c₄;c₁,c₃,c₅) = (-157/8, 24, -23/4; 0, 0, 1)`

has negative retuned positive quadratic.  The proof below separates the
single analytic fixed-profile estimate from two exact algebraic steps:

* the retuned transfer changes the old exact six-mode form by exactly
  `-14947/50000` on this vector;
* an inverse-free adjugate completion turns negativity of the six-mode form
  into `T⁺₂₂ < 0`.

Thus the exact algebra below reduces falsification of the proposed retuned
certificate route to one fixed-profile analytic upper bound.  It makes no
claim about that bound or about the Riemann hypothesis itself.
-/

private def retunedPlusP5Quadratic (c0 c2 c4 : ℝ) : ℝ :=
  symmetricQuadratic
      factorTwoIntrinsicSixUnbalancedEPlus00
      factorTwoIntrinsicSixUnbalancedEPlus02
      factorTwoIntrinsicSixUnbalancedEPlus04
      factorTwoIntrinsicSixUnbalancedEPlus22
      factorTwoIntrinsicSixUnbalancedEPlus24
      factorTwoIntrinsicSixUnbalancedEPlus44 c0 c2 c4 +
    2 * (c0 * factorTwoIntrinsicNineRetunedBPlus 2 0 +
      c2 * factorTwoIntrinsicNineRetunedBPlus 2 1 +
      c4 * factorTwoIntrinsicNineRetunedBPlus 2 2) +
    factorTwoIntrinsicSixUnbalancedOMinus55

/-- The exact retuned positive form at the explicit rational witness. -/
def factorTwoIntrinsicNineRetunedPlusWitnessForm : ℝ :=
  retunedPlusP5Quadratic (-157 / 8) 24 (-23 / 4)

/-- On the fixed witness, retuning subtracts exactly `14947/50000` from the
old kernel-checked six-mode form. -/
theorem factorTwoIntrinsicNineRetunedPlusWitnessForm_eq_old_sub :
    factorTwoIntrinsicNineRetunedPlusWitnessForm =
      factorTwoIntrinsicSixUnbalancedMinorPlusExactSixQuadratic
          (-157 / 8) 24 (-23 / 4) 0 0 1 -
        (14947 / 50000 : ℝ) := by
  rw [factorTwoIntrinsicSixUnbalancedMinorPlusExactSixQuadratic_eq_staticPlus,
    factorTwoIntrinsicSixUnbalancedStaticPlus_eq_block]
  unfold factorTwoIntrinsicNineRetunedPlusWitnessForm retunedPlusP5Quadratic
    factorTwoIntrinsicNineRetunedBPlus factorTwoIntrinsicNineRetunedKPlus
    factorTwoIntrinsicNineRetunedEvenBasis
    factorTwoIntrinsicNineRetunedOddBasis factorTwoIntrinsicNineRetunedH
    factorTwoIntrinsicSixUnbalancedKPlus05
    factorTwoIntrinsicSixUnbalancedKPlus25
    factorTwoIntrinsicSixUnbalancedKPlus45
    factorTwoIntrinsicFourP45Cross05
    factorTwoIntrinsicFourP45Cross25 factorTwoIntrinsicP45Alternating
  simp [symmetricQuadratic]
  ring

/-- The fixed old-form cap is exactly the analytic inequality needed for the
retuned witness.  Keeping it as an argument isolates the structural algebra
while the one-profile estimate is proved in the old determinant module. -/
theorem factorTwoIntrinsicNineRetunedPlusWitnessForm_neg_of_old_cap
    (hcap :
      factorTwoIntrinsicSixUnbalancedMinorPlusExactSixQuadratic
          (-157 / 8) 24 (-23 / 4) 0 0 1 < (14947 / 50000 : ℝ)) :
    factorTwoIntrinsicNineRetunedPlusWitnessForm < 0 := by
  rw [factorTwoIntrinsicNineRetunedPlusWitnessForm_eq_old_sub]
  linarith

private def retunedPlusP5AdjugateVector : Fin 3 → ℝ :=
  adjugateVector
    factorTwoIntrinsicSixUnbalancedEPlus00
    factorTwoIntrinsicSixUnbalancedEPlus02
    factorTwoIntrinsicSixUnbalancedEPlus04
    factorTwoIntrinsicSixUnbalancedEPlus22
    factorTwoIntrinsicSixUnbalancedEPlus24
    factorTwoIntrinsicSixUnbalancedEPlus44
    (factorTwoIntrinsicNineRetunedBPlus 2 0)
    (factorTwoIntrinsicNineRetunedBPlus 2 1)
    (factorTwoIntrinsicNineRetunedBPlus 2 2)

set_option maxHeartbeats 800000 in
private theorem retunedPlusP5_fractionFree_completion (c0 c2 c4 : ℝ) :
    let d := factorTwoIntrinsicSixUnbalancedEPlusDet
    symmetricQuadratic
        factorTwoIntrinsicSixUnbalancedEPlus00
        factorTwoIntrinsicSixUnbalancedEPlus02
        factorTwoIntrinsicSixUnbalancedEPlus04
        factorTwoIntrinsicSixUnbalancedEPlus22
        factorTwoIntrinsicSixUnbalancedEPlus24
        factorTwoIntrinsicSixUnbalancedEPlus44
        (d * c0 + retunedPlusP5AdjugateVector 0)
        (d * c2 + retunedPlusP5AdjugateVector 1)
        (d * c4 + retunedPlusP5AdjugateVector 2) +
      d * factorTwoIntrinsicNineRetunedTPlus 2 2 =
        d ^ 2 * retunedPlusP5Quadratic c0 c2 c4 := by
  dsimp only
  unfold retunedPlusP5Quadratic retunedPlusP5AdjugateVector
    factorTwoIntrinsicNineRetunedTPlus
  change
    symmetricQuadratic
        factorTwoIntrinsicSixUnbalancedEPlus00
        factorTwoIntrinsicSixUnbalancedEPlus02
        factorTwoIntrinsicSixUnbalancedEPlus04
        factorTwoIntrinsicSixUnbalancedEPlus22
        factorTwoIntrinsicSixUnbalancedEPlus24
        factorTwoIntrinsicSixUnbalancedEPlus44
        (_ * c0 + adjugateVector
          factorTwoIntrinsicSixUnbalancedEPlus00
          factorTwoIntrinsicSixUnbalancedEPlus02
          factorTwoIntrinsicSixUnbalancedEPlus04
          factorTwoIntrinsicSixUnbalancedEPlus22
          factorTwoIntrinsicSixUnbalancedEPlus24
          factorTwoIntrinsicSixUnbalancedEPlus44
          (factorTwoIntrinsicNineRetunedBPlus 2 0)
          (factorTwoIntrinsicNineRetunedBPlus 2 1)
          (factorTwoIntrinsicNineRetunedBPlus 2 2) 0)
        (_ * c2 + adjugateVector
          factorTwoIntrinsicSixUnbalancedEPlus00
          factorTwoIntrinsicSixUnbalancedEPlus02
          factorTwoIntrinsicSixUnbalancedEPlus04
          factorTwoIntrinsicSixUnbalancedEPlus22
          factorTwoIntrinsicSixUnbalancedEPlus24
          factorTwoIntrinsicSixUnbalancedEPlus44
          (factorTwoIntrinsicNineRetunedBPlus 2 0)
          (factorTwoIntrinsicNineRetunedBPlus 2 1)
          (factorTwoIntrinsicNineRetunedBPlus 2 2) 1)
        (_ * c4 + adjugateVector
          factorTwoIntrinsicSixUnbalancedEPlus00
          factorTwoIntrinsicSixUnbalancedEPlus02
          factorTwoIntrinsicSixUnbalancedEPlus04
          factorTwoIntrinsicSixUnbalancedEPlus22
          factorTwoIntrinsicSixUnbalancedEPlus24
          factorTwoIntrinsicSixUnbalancedEPlus44
          (factorTwoIntrinsicNineRetunedBPlus 2 0)
          (factorTwoIntrinsicNineRetunedBPlus 2 1)
          (factorTwoIntrinsicNineRetunedBPlus 2 2) 2) +
      factorTwoIntrinsicSixUnbalancedEPlusDet *
        (factorTwoIntrinsicSixUnbalancedEPlusDet *
            factorTwoIntrinsicSixUnbalancedOMinus55 -
          unbalancedThreeAdjugatePair
            factorTwoIntrinsicSixUnbalancedEPlus00
            factorTwoIntrinsicSixUnbalancedEPlus02
            factorTwoIntrinsicSixUnbalancedEPlus04
            factorTwoIntrinsicSixUnbalancedEPlus22
            factorTwoIntrinsicSixUnbalancedEPlus24
            factorTwoIntrinsicSixUnbalancedEPlus44
            (factorTwoIntrinsicNineRetunedBPlus 2 0)
            (factorTwoIntrinsicNineRetunedBPlus 2 1)
            (factorTwoIntrinsicNineRetunedBPlus 2 2)
            (factorTwoIntrinsicNineRetunedBPlus 2 0)
            (factorTwoIntrinsicNineRetunedBPlus 2 1)
            (factorTwoIntrinsicNineRetunedBPlus 2 2)) = _
  simp only [adjugateVector]
  unfold factorTwoIntrinsicSixUnbalancedEPlusDet symmetricQuadratic
    symmetricDeterminant unbalancedThreeAdjugatePair
  ring

/-- Any negative value of the explicit retuned witness forces the diagonal
`P₅` entry of the fraction-free Schur block to be negative. -/
theorem factorTwoIntrinsicNineRetunedTPlus22_neg_of_witness_neg
    (hwitness : factorTwoIntrinsicNineRetunedPlusWitnessForm < 0) :
    factorTwoIntrinsicNineRetunedTPlus 2 2 < 0 := by
  let d : ℝ := factorTwoIntrinsicSixUnbalancedEPlusDet
  have hd : 0 < d := by
    simpa only [d] using factorTwoIntrinsicSixUnbalancedEPlus_positive.2.2
  have hEven :
      0 ≤ symmetricQuadratic
        factorTwoIntrinsicSixUnbalancedEPlus00
        factorTwoIntrinsicSixUnbalancedEPlus02
        factorTwoIntrinsicSixUnbalancedEPlus04
        factorTwoIntrinsicSixUnbalancedEPlus22
        factorTwoIntrinsicSixUnbalancedEPlus24
        factorTwoIntrinsicSixUnbalancedEPlus44
        (d * (-157 / 8) + retunedPlusP5AdjugateVector 0)
        (d * 24 + retunedPlusP5AdjugateVector 1)
        (d * (-23 / 4) + retunedPlusP5AdjugateVector 2) := by
    exact symmetricQuadratic_nonneg
      factorTwoIntrinsicSixUnbalancedEPlus00
      factorTwoIntrinsicSixUnbalancedEPlus02
      factorTwoIntrinsicSixUnbalancedEPlus04
      factorTwoIntrinsicSixUnbalancedEPlus22
      factorTwoIntrinsicSixUnbalancedEPlus24
      factorTwoIntrinsicSixUnbalancedEPlus44
      factorTwoIntrinsicSixUnbalancedEPlus_positive.1
      factorTwoIntrinsicSixUnbalancedEPlus_positive.2.1
      factorTwoIntrinsicSixUnbalancedEPlus_positive.2.2 _ _ _
  have hcompletion := retunedPlusP5_fractionFree_completion
    (-157 / 8) 24 (-23 / 4)
  dsimp only [d] at hEven hcompletion
  have hscaled :
      factorTwoIntrinsicSixUnbalancedEPlusDet ^ 2 *
          factorTwoIntrinsicNineRetunedPlusWitnessForm < 0 :=
    mul_neg_of_pos_of_neg (sq_pos_of_pos hd) hwitness
  change factorTwoIntrinsicSixUnbalancedEPlusDet ^ 2 *
      retunedPlusP5Quadratic (-157 / 8) 24 (-23 / 4) < 0 at hscaled
  rw [← hcompletion] at hscaled
  have hproduct :
      factorTwoIntrinsicSixUnbalancedEPlusDet *
          factorTwoIntrinsicNineRetunedTPlus 2 2 < 0 := by
    nlinarith
  by_contra hnot
  have hTnonneg : 0 ≤ factorTwoIntrinsicNineRetunedTPlus 2 2 :=
    le_of_not_gt hnot
  exact (not_lt_of_ge (mul_nonneg hd.le hTnonneg)) hproduct

/-- A negative `T⁺₂₂`, together with the already-proved first two gates,
forces the full `3 x 3` determinant to be negative. -/
theorem factorTwoIntrinsicNineRetunedTPlusDet_neg_of_TPlus22_neg
    (h22 : factorTwoIntrinsicNineRetunedTPlus 2 2 < 0) :
    symmetricDeterminant
      (factorTwoIntrinsicNineRetunedTPlus 0 0)
      (factorTwoIntrinsicNineRetunedTPlus 0 1)
      (factorTwoIntrinsicNineRetunedTPlus 0 2)
      (factorTwoIntrinsicNineRetunedTPlus 1 1)
      (factorTwoIntrinsicNineRetunedTPlus 1 2)
      (factorTwoIntrinsicNineRetunedTPlus 2 2) < 0 := by
  let a : ℝ := factorTwoIntrinsicNineRetunedTPlus 0 0
  let b : ℝ := factorTwoIntrinsicNineRetunedTPlus 0 1
  let c : ℝ := factorTwoIntrinsicNineRetunedTPlus 0 2
  let e : ℝ := factorTwoIntrinsicNineRetunedTPlus 1 2
  let f : ℝ := factorTwoIntrinsicNineRetunedTPlus 2 2
  let m : ℝ := leadingMinorTwo a b
    (factorTwoIntrinsicNineRetunedTPlus 1 1)
  have ha : 0 < a := by
    simpa only [a] using factorTwoIntrinsicNineRetunedTPlus00_pos
  have hm : 0 < m := by
    simpa only [m, a, b] using factorTwoIntrinsicNineRetunedTPlusMinor_pos
  have hf : f < 0 := by simpa only [f] using h22
  have hborderScaled :
      0 ≤ a *
        (a * e ^ 2 - 2 * b * c * e +
          factorTwoIntrinsicNineRetunedTPlus 1 1 * c ^ 2) := by
    have hid :
        a *
            (a * e ^ 2 - 2 * b * c * e +
              factorTwoIntrinsicNineRetunedTPlus 1 1 * c ^ 2) =
          (a * e - b * c) ^ 2 + m * c ^ 2 := by
      unfold m leadingMinorTwo
      ring
    rw [hid]
    positivity
  have hborder :
      0 ≤ a * e ^ 2 - 2 * b * c * e +
        factorTwoIntrinsicNineRetunedTPlus 1 1 * c ^ 2 := by
    by_contra hnot
    have hneg :
        a * e ^ 2 - 2 * b * c * e +
            factorTwoIntrinsicNineRetunedTPlus 1 1 * c ^ 2 < 0 :=
      lt_of_not_ge hnot
    exact (not_lt_of_ge hborderScaled)
      (mul_neg_of_pos_of_neg ha hneg)
  have hfm : f * m < 0 := mul_neg_of_neg_of_pos hf hm
  change symmetricDeterminant a b c
      (factorTwoIntrinsicNineRetunedTPlus 1 1) e f < 0
  rw [show symmetricDeterminant a b c
        (factorTwoIntrinsicNineRetunedTPlus 1 1) e f =
      f * m -
        (a * e ^ 2 - 2 * b * c * e +
          factorTwoIntrinsicNineRetunedTPlus 1 1 * c ^ 2) by
    dsimp only [m]
    unfold symmetricDeterminant leadingMinorTwo
    ring]
  nlinarith

/-- Conditional route falsification from the sole outstanding analytic
fixed-profile cap. -/
theorem not_factorTwoIntrinsicNineRetunedPlusFinalThreeGates_of_old_cap
    (hcap :
      factorTwoIntrinsicSixUnbalancedMinorPlusExactSixQuadratic
          (-157 / 8) 24 (-23 / 4) 0 0 1 < (14947 / 50000 : ℝ)) :
    ¬ FactorTwoIntrinsicNineRetunedPlusFinalThreeGates := by
  have hwitness := factorTwoIntrinsicNineRetunedPlusWitnessForm_neg_of_old_cap
    hcap
  have h22 := factorTwoIntrinsicNineRetunedTPlus22_neg_of_witness_neg hwitness
  have hdet := factorTwoIntrinsicNineRetunedTPlusDet_neg_of_TPlus22_neg h22
  intro hgates
  exact (not_lt_of_ge hgates.2.2.1.le) hdet

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineRetunedPlusDeterminantObstructionStructural
