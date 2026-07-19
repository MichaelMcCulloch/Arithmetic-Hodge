import ArithmeticHodge.Analysis.MultiplicativeWeilCoherentCorrectedPotentialStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilQuarterLogLatticeFarChebyshevStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilCoherentFejerBoundaryDefectStructural

set_option autoImplicit false

open Complex Finset MeasureTheory Real Set
open scoped BigOperators ContDiff

namespace ArithmeticHodge.Analysis.MultiplicativeWeilCoherentFarResidualCorrectedPotentialStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilCoherentCorrectedPotentialStructural
open MultiplicativeWeilCorrectedChebyshevPotentialStructural
open MultiplicativeWeilCoherentFejerBoundaryDefectStructural
open MultiplicativeWeilFejerLocalizationStructural
open MultiplicativeWeilFejerLinearResidualStructural
open MultiplicativeWeilQuarterLogLatticeFejerAssemblyStructural
open MultiplicativeWeilQuarterLogLatticeFarChebyshevStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural

/-!
# The collective coherent far residual

The genuinely separated part of the order-three Fejer residual has coefficient
two at every lag at least three.  This module identifies its recursive linear
lag sum with a finite ordered-pair sum and then rewrites that entire sum through
the coherent corrected-Chebyshev potential formula.
-/

/-- Ordered pairs of positions in a finite line for which the first position
is at least three quarter-lattice steps to the right of the second. -/
def consecutiveFarPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p ↦ p.2.val + 3 ≤ p.1.val)

@[simp]
theorem mem_consecutiveFarPairs_iff {n : ℕ} {p : Fin n × Fin n} :
    p ∈ consecutiveFarPairs n ↔ p.2.val + 3 ≤ p.1.val := by
  simp [consecutiveFarPairs]

/-- The actual far-lag part of the order-three Fejer residual.  The high cell
is placed first to match the support orientation of the potential formula. -/
def consecutiveFarResidualRealSum
    (A : ℤ → BombieriTest) (lo : ℤ) (n : ℕ) : ℝ :=
  ∑ p ∈ consecutiveFarPairs n,
    2 * bombieriGlobalCrossRealValue
      (A (lo + (p.1.val : ℤ))) (A (lo + (p.2.val : ℤ)))

/-- Complex lift of the far residual sum. -/
def consecutiveFarResidualComplexSum
    (A : ℤ → BombieriTest) (lo : ℤ) (n : ℕ) : ℂ :=
  ∑ p ∈ consecutiveFarPairs n,
    (2 : ℂ) * bombieriTwoBlockGlobalCrossSymbol
      (A (lo + (p.1.val : ℤ))) (A (lo + (p.2.val : ℤ)))

/-- Collective Chebyshev-error pairing for all ordered far pairs. -/
def consecutiveFarChebyshevErrorSum
    (parent : BombieriTest) (eta : ℤ → ℝ → ℝ)
    (lo : ℤ) (n : ℕ) : ℂ :=
  ∑ p ∈ consecutiveFarPairs n,
    (2 : ℂ) *
      ∫ x : ℝ in Set.Ioi 0,
        ((Chebyshev.psi x - x : ℝ) : ℂ) *
          ∫ y : ℝ in Set.Ioi 0,
            coherentStarCorrelationDerivativeIntegrand parent
              (eta (lo + (p.1.val : ℤ)))
              (eta (lo + (p.2.val : ℤ))) x y

/-- Collective corrected-archimedean-potential pairing for all ordered far
pairs. -/
def consecutiveFarCorrectedPotentialSum
    (parent : BombieriTest) (eta : ℤ → ℝ → ℝ)
    (lo : ℤ) (n : ℕ) : ℂ :=
  ∑ p ∈ consecutiveFarPairs n,
    (2 : ℂ) *
      ∫ x : ℝ in Set.Ioi 0,
        ((correctedChebyshevPotential x : ℝ) : ℂ) *
          ∫ y : ℝ in Set.Ioi 0,
            coherentStarCorrelationDerivativeIntegrand parent
              (eta (lo + (p.1.val : ℤ)))
              (eta (lo + (p.2.val : ℤ))) x y

/-- Every far coefficient used above is literally the production Fejer
residual coefficient. -/
theorem far_residual_coefficient_eq_two
    {i j : ℕ} (hfar : j + 3 ≤ i) :
    bombieriFejerThreeResidualLagWeight (i - j) = 2 := by
  apply bombieriFejerThreeResidualLagWeight_of_three_le
  omega

private theorem headWeightedLagCross_ofFn
    (w : ℕ → ℝ) (f : BombieriTest) (k : ℕ)
    {n : ℕ} (a : Fin n → BombieriTest) :
    bombieriHeadWeightedLagCross w f k (List.ofFn a) =
      ∑ i : Fin n,
        w (k + i.val) * bombieriGlobalCrossRealValue f (a i) := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
      rw [List.ofFn_succ]
      simp only [bombieriHeadWeightedLagCross, Fin.sum_univ_succ]
      rw [ih]
      congr 1
      apply Finset.sum_congr rfl
      intro i _hi
      simp only [Fin.val_succ]
      congr 2
      omega

private theorem bombieriGlobalCrossRealValue_comm
    (f g : BombieriTest) :
    bombieriGlobalCrossRealValue f g =
      bombieriGlobalCrossRealValue g f := by
  unfold bombieriGlobalCrossRealValue
  have H := congrArg Complex.re
    (bombieriTwoBlockGlobalCrossSymbol_conj_swap f g)
  simpa using H.symm

private theorem weightedLinearLagCross_ofFn_eq_orderedPairs
    (w : ℕ → ℝ) {n : ℕ} (a : Fin n → BombieriTest) :
    bombieriWeightedLinearLagCross w (List.ofFn a) =
      ∑ hi : Fin n, ∑ lo : Fin n,
        if lo.val < hi.val then
          w (hi.val - lo.val) *
            bombieriGlobalCrossRealValue (a hi) (a lo)
        else 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.ofFn_succ]
      simp only [bombieriWeightedLinearLagCross,
        headWeightedLagCross_ofFn, Fin.sum_univ_succ]
      rw [ih (fun i ↦ a i.succ)]
      simp only [Fin.val_zero, Fin.val_succ, Nat.not_lt_zero, ↓reduceIte,
        Finset.sum_const_zero, zero_add]
      rw [Finset.sum_add_distrib]
      congr 1
      · apply Finset.sum_congr rfl
        intro hi _hhi
        simp only [Nat.zero_lt_succ, ↓reduceIte, Nat.sub_zero]
        rw [bombieriGlobalCrossRealValue_comm]
        congr 2
        omega
      · apply Finset.sum_congr rfl
        intro hi _hhi
        apply Finset.sum_congr rfl
        intro lo _hlo
        simp only [Nat.succ_lt_succ_iff, Nat.succ_sub_succ_eq_sub]

/-- The recursive production far-lag functional is exactly the filtered
ordered far-pair sum. -/
theorem weightedLinearLagCross_far_integerBlock_eq_consecutiveFarResidualRealSum
    (A : ℤ → BombieriTest) (lo : ℤ) (n : ℕ) :
    bombieriWeightedLinearLagCross
        bombieriFejerThreeResidualFarLagWeight
        (List.ofFn (integerBlock A lo n)) =
      consecutiveFarResidualRealSum A lo n := by
  rw [weightedLinearLagCross_ofFn_eq_orderedPairs]
  unfold consecutiveFarResidualRealSum consecutiveFarPairs
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro hi _hhi
  apply Finset.sum_congr rfl
  intro low _hlow
  simp only [integerBlock]
  by_cases hfar : low.val + 3 ≤ hi.val
  · have hlt : low.val < hi.val := by omega
    have hdiff : 3 ≤ hi.val - low.val := by omega
    simp [hlt, hfar, hdiff,
      bombieriFejerThreeResidualFarLagWeight]
  · by_cases hlt : low.val < hi.val
    · have hdiff : ¬ 3 ≤ hi.val - low.val := by omega
      simp [hlt, hfar, hdiff,
        bombieriFejerThreeResidualFarLagWeight]
    · simp [hlt, hfar]

/-- The complex finite far residual is the sum of its collective
Chebyshev-error and corrected-potential pairings. -/
theorem consecutiveFarResidualComplexSum_eq_correctedPotential
    (parent : BombieriTest) (A : ℤ → BombieriTest)
    (eta : ℤ → ℝ → ℝ) (lo : ℤ) (n : ℕ)
    (hcoh : ∀ k z,
      A k z = (eta k z : ℂ) * parent z)
    (hsmooth : ∀ k, ContDiff ℝ ∞ (eta k))
    (hsupport : ∀ k,
      tsupport (A k) ⊆ Set.Icc
        (quarterLogLatticePoint k) (quarterLogLatticePoint (k + 2))) :
    consecutiveFarResidualComplexSum A lo n =
      consecutiveFarChebyshevErrorSum parent eta lo n +
        consecutiveFarCorrectedPotentialSum parent eta lo n := by
  unfold consecutiveFarResidualComplexSum
  unfold consecutiveFarChebyshevErrorSum
  unfold consecutiveFarCorrectedPotentialSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hfar : p.2.val + 3 ≤ p.1.val :=
    mem_consecutiveFarPairs_iff.mp hp
  let hi : ℤ := lo + (p.1.val : ℤ)
  let hj : ℤ := lo + (p.2.val : ℤ)
  have hsepIndex : hj + 2 < hi := by
    dsimp only [hi, hj]
    omega
  have hsep : quarterLogLatticePoint (hj + 2) <
      quarterLogLatticePoint hi :=
    quarterLogLatticePoint_strictMono hsepIndex
  have H :=
    bombieriTwoBlockGlobalCrossSymbol_eq_coherent_correctedPotential
      parent (A hi) (A hj) (eta hi) (eta hj)
      (hsmooth hi) (hcoh hi) (hcoh hj)
      (quarterLogLatticePoint_pos hj)
      (quarterLogLatticePoint_pos (hj + 2))
      (hsupport hi) (hsupport hj) hsep
  dsimp only [hi, hj] at H
  rw [H]
  ring

/-- Real-part form, matching the real Fejer residual convention. -/
theorem consecutiveFarResidualRealSum_eq_correctedPotential_re
    (parent : BombieriTest) (A : ℤ → BombieriTest)
    (eta : ℤ → ℝ → ℝ) (lo : ℤ) (n : ℕ)
    (hcoh : ∀ k z,
      A k z = (eta k z : ℂ) * parent z)
    (hsmooth : ∀ k, ContDiff ℝ ∞ (eta k))
    (hsupport : ∀ k,
      tsupport (A k) ⊆ Set.Icc
        (quarterLogLatticePoint k) (quarterLogLatticePoint (k + 2))) :
    consecutiveFarResidualRealSum A lo n =
      (consecutiveFarChebyshevErrorSum parent eta lo n +
        consecutiveFarCorrectedPotentialSum parent eta lo n).re := by
  rw [← consecutiveFarResidualComplexSum_eq_correctedPotential
    parent A eta lo n hcoh hsmooth hsupport]
  unfold consecutiveFarResidualRealSum
  unfold consecutiveFarResidualComplexSum
  change (∑ p ∈ consecutiveFarPairs n,
      2 * bombieriGlobalCrossRealValue
        (A (lo + (p.1.val : ℤ))) (A (lo + (p.2.val : ℤ)))) =
    Complex.reCLM (∑ p ∈ consecutiveFarPairs n,
      (2 : ℂ) * bombieriTwoBlockGlobalCrossSymbol
        (A (lo + (p.1.val : ℤ))) (A (lo + (p.2.val : ℤ))))
  rw [map_sum Complex.reCLM]
  apply Finset.sum_congr rfl
  intro p _hp
  simp [bombieriGlobalCrossRealValue, Complex.mul_re]

/-- Direct production form: the recursive far residual in the coherent
integer block is exactly the real collective corrected-potential expression. -/
theorem weightedLinearLagCross_far_integerBlock_eq_correctedPotential_re
    (parent : BombieriTest) (A : ℤ → BombieriTest)
    (eta : ℤ → ℝ → ℝ) (lo : ℤ) (n : ℕ)
    (hcoh : ∀ k z,
      A k z = (eta k z : ℂ) * parent z)
    (hsmooth : ∀ k, ContDiff ℝ ∞ (eta k))
    (hsupport : ∀ k,
      tsupport (A k) ⊆ Set.Icc
        (quarterLogLatticePoint k) (quarterLogLatticePoint (k + 2))) :
    bombieriWeightedLinearLagCross
        bombieriFejerThreeResidualFarLagWeight
        (List.ofFn (integerBlock A lo n)) =
      (consecutiveFarChebyshevErrorSum parent eta lo n +
        consecutiveFarCorrectedPotentialSum parent eta lo n).re := by
  rw [weightedLinearLagCross_far_integerBlock_eq_consecutiveFarResidualRealSum,
    consecutiveFarResidualRealSum_eq_correctedPotential_re
      parent A eta lo n hcoh hsmooth hsupport]

end

end ArithmeticHodge.Analysis.MultiplicativeWeilCoherentFarResidualCorrectedPotentialStructural
