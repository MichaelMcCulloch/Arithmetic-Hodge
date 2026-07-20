import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineBalancedStaticNestedSchurStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineBalancedStaticObstructionStructural

noncomputable section

open ThreeByThreeRankOneSchur
open YoshidaFactorTwoPhaseIntrinsicNineBalancedStaticNestedSchurStructural
open YoshidaFactorTwoPhaseIntrinsicNineStaticNestedSchurStructural

/-!
# A transfer-independent obstruction to the frozen-core balanced split

The two rational directions below use only the new `P6` coordinate.  They
share the same odd coordinates, so every occurrence of the three relevant
tail-transfer entries cancels between the plus and minus endpoints.  Thus a
single negative scalar sum rules out every shared extension of the certified
six-mode transfer.
-/

/-- Rational plus-endpoint direction in
`(P0,P2,P4;P1,P3,P5;P6,P8,P7)` order. -/
def factorTwoIntrinsicNineBalancedP6PlusWitness
    (h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 : ℝ) : ℝ :=
  factorTwoIntrinsicNineBalancedPlusBlock
    h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
    (6 / 5) (87 / 10) (-69 / 5)
    (38 / 5) (-33 / 5) (-17 / 10) 1 0 0

/-- Rational minus-endpoint direction paired with the plus witness. -/
def factorTwoIntrinsicNineBalancedP6MinusWitness
    (h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 : ℝ) : ℝ :=
  factorTwoIntrinsicNineBalancedMinusBlock
    h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87
    16 (-187 / 10) (23 / 10)
    (38 / 5) (-33 / 5) (-17 / 10) 1 0 0

/-- The fixed scalar left after cancellation of every transfer parameter. -/
def factorTwoIntrinsicNineBalancedP6WitnessSum : ℝ :=
  factorTwoIntrinsicNineBalancedP6PlusWitness
      0 0 0 0 0 0 0 0 0 0 0 +
    factorTwoIntrinsicNineBalancedP6MinusWitness
      0 0 0 0 0 0 0 0 0 0 0

/-- The paired witness sum is independent of all eleven entries of the
shared tail transfer. -/
theorem factorTwoIntrinsicNineBalancedP6Witness_sum_eq
    (h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 : ℝ) :
    factorTwoIntrinsicNineBalancedP6PlusWitness
          h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 +
        factorTwoIntrinsicNineBalancedP6MinusWitness
          h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 =
      factorTwoIntrinsicNineBalancedP6WitnessSum := by
  unfold factorTwoIntrinsicNineBalancedP6WitnessSum
    factorTwoIntrinsicNineBalancedP6PlusWitness
    factorTwoIntrinsicNineBalancedP6MinusWitness
    factorTwoIntrinsicNineBalancedPlusBlock
    factorTwoIntrinsicNineBalancedMinusBlock
    factorTwoIntrinsicNinePlusBlock factorTwoIntrinsicNineMinusBlock
    factorTwoIntrinsicNineReserveQuadratic
  simp only [factorTwoIntrinsicNineDPlus, factorTwoIntrinsicNineDMinus,
    factorTwoIntrinsicNineFPlus, factorTwoIntrinsicNineFMinus,
    factorTwoIntrinsicNineGPlus, factorTwoIntrinsicNineGMinus,
    factorTwoIntrinsicNineKPlus61, factorTwoIntrinsicNineKPlus63,
    factorTwoIntrinsicNineKPlus65, factorTwoIntrinsicNineKMinus61,
    factorTwoIntrinsicNineKMinus63, factorTwoIntrinsicNineKMinus65,
    factorTwoIntrinsicNineKPlusEntry, factorTwoIntrinsicNineKMinusEntry,
    symmetricQuadratic]
  ring

/-- A negative paired scalar forbids simultaneous positivity of the two
balanced endpoint gates for every shared transfer. -/
theorem not_exists_balanced_W_pair_of_P6WitnessSum_neg
    (hneg : factorTwoIntrinsicNineBalancedP6WitnessSum < 0) :
    ¬ ∃ h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 : ℝ,
      FactorTwoIntrinsicNineBalancedWPlusNonnegative
          h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 ∧
        FactorTwoIntrinsicNineBalancedWMinusNonnegative
          h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 := by
  rintro ⟨h07, h27, h47, h61, h63, h65, h67, h81, h83, h85, h87,
    hPlus, hMinus⟩
  have hp := factorTwoIntrinsicNineBalancedPlusBlock_nonnegative_of_W
    h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 hPlus
    (6 / 5) (87 / 10) (-69 / 5)
    (38 / 5) (-33 / 5) (-17 / 10) 1 0 0
  have hm := factorTwoIntrinsicNineBalancedMinusBlock_nonnegative_of_W
    h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87 hMinus
    16 (-187 / 10) (23 / 10)
    (38 / 5) (-33 / 5) (-17 / 10) 1 0 0
  rw [← factorTwoIntrinsicNineBalancedP6Witness_sum_eq
    h07 h27 h47 h61 h63 h65 h67 h81 h83 h85 h87] at hneg
  unfold factorTwoIntrinsicNineBalancedP6PlusWitness
    factorTwoIntrinsicNineBalancedP6MinusWitness at hneg
  linarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineBalancedStaticObstructionStructural
