import ArithmeticHodge.Analysis.MultiplicativeWeilTwoSeedFactorTwo

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-!
# The minimal independent two-cell target

The adjacent two-seed criterion is usually stated with an additional scalar
`c`.  Because the second seed is already arbitrary, that scalar is redundant:
apply the coefficient-one statement to `c • g`.  This file records the exact
equivalence, including the support transport, so the analytic target can be
attacked as positivity of one honest two-cell block.
-/

/-- Positivity of the coefficient-one adjacent two-cell block for two
independent seeds in the same ratio-at-most-two support interval. -/
def BombieriIndependentTwoCellNonneg : Prop :=
  ∀ (f g : BombieriTest) {a b : ℝ},
    0 < a → a ≤ b →
    tsupport f ⊆ Set.Icc a b →
    tsupport g ⊆ Set.Icc a b →
    b / a ≤ 2 →
    0 ≤ (bombieriFunctional
      (bombieriQuadraticTest
        (f + normalizedDilation 2 (by norm_num) g))).re

/-- The sharp adjacent contraction, with the two independent seeds kept in
one common support cell. -/
def BombieriAdjacentTwoSeedContraction : Prop :=
  ∀ (f g : BombieriTest) {a b : ℝ},
    0 < a → a ≤ b →
    tsupport f ⊆ Set.Icc a b →
    tsupport g ⊆ Set.Icc a b →
    b / a ≤ 2 →
    Complex.normSq (factorTwoTwoSeedGlobalCrossSymbol f g) ≤
      (bombieriFunctional (bombieriQuadraticTest f)).re *
        (bombieriFunctional (bombieriQuadraticTest g)).re

private theorem normalizedDilation_smul_seed
    (c : ℂ) (g : BombieriTest) :
    normalizedDilation 2 (by norm_num) (c • g) =
      c • normalizedDilation 2 (by norm_num) g := by
  ext x
  simp only [normalizedDilation_apply, TestFunction.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  ring

private theorem tsupport_smul_seed_subset
    (c : ℂ) (g : BombieriTest) :
    tsupport (c • g : BombieriTest) ⊆ tsupport g := by
  change tsupport (fun x : ℝ ↦ c * g x) ⊆ tsupport g
  exact tsupport_smul_subset_right (fun _ : ℝ ↦ c) (g : ℝ → ℂ)

/-- Coefficient-one positivity supplies every complex scalar direction by
absorbing the scalar into the second seed. -/
theorem bombieriFunctional_twoSeedFactorTwo_nonneg_of_independentTwoCell
    (h : BombieriIndependentTwoCellNonneg)
    (f g : BombieriTest) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hf : tsupport f ⊆ Set.Icc a b)
    (hg : tsupport g ⊆ Set.Icc a b)
    (hratio : b / a ≤ 2) :
    ∀ c : ℂ,
      0 ≤ (bombieriFunctional
        (bombieriQuadraticTest
          (f + c • normalizedDilation 2 (by norm_num) g))).re := by
  intro c
  have hcg : tsupport (c • g : BombieriTest) ⊆ Set.Icc a b :=
    (tsupport_smul_seed_subset c g).trans hg
  have hcell := h f (c • g) ha hab hf hcg hratio
  rw [normalizedDilation_smul_seed] at hcell
  exact hcell

/-- The coefficient-one two-cell statement is exactly the sharp two-seed
contraction.  No same-seed numerical-radius inference enters the proof. -/
theorem bombieriIndependentTwoCellNonneg_iff_adjacentTwoSeedContraction :
    BombieriIndependentTwoCellNonneg ↔
      BombieriAdjacentTwoSeedContraction := by
  constructor
  · intro h f g a b ha hab hf hg hratio
    exact (bombieriFunctional_twoSeedFactorTwo_nonneg_iff
      f g ha hab hf hratio ha hab hg hratio).1
        (bombieriFunctional_twoSeedFactorTwo_nonneg_of_independentTwoCell
          h f g ha hab hf hg hratio)
  · intro h f g a b ha hab hf hg hratio
    have hall := (bombieriFunctional_twoSeedFactorTwo_nonneg_iff
      f g ha hab hf hratio ha hab hg hratio).2
        (h f g ha hab hf hg hratio)
    simpa only [one_smul] using hall 1

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
