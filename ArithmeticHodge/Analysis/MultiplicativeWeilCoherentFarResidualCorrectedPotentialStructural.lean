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
open MultiplicativeWeilDirectedCorrelationDerivativeStructural
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

/-! ## One collective far mask -/

/-- The oriented first-slot partition-boundary mask appearing directly in
the separated corrected-potential formula. -/
def consecutiveFarOrientedBoundaryMask
    (eta : ℤ → ℝ → ℝ) (lo : ℤ) (n : ℕ) (x y : ℝ) : ℝ :=
  ∑ p ∈ consecutiveFarPairs n,
    2 * deriv (eta (lo + (p.1.val : ℤ))) (x * y) *
      eta (lo + (p.2.val : ℤ)) y

/-- The matching first-slot value mask multiplying the derivative of the
common parent. -/
def consecutiveFarOrientedValueMask
    (eta : ℤ → ℝ → ℝ) (lo : ℤ) (n : ℕ) (x y : ℝ) : ℝ :=
  ∑ p ∈ consecutiveFarPairs n,
    2 * eta (lo + (p.1.val : ℤ)) (x * y) *
      eta (lo + (p.2.val : ℤ)) y

/-- One integrand containing every far pair, with the partition derivative
and parent derivative still separated. -/
def consecutiveFarCollectiveDerivativeIntegrand
    (parent : BombieriTest) (eta : ℤ → ℝ → ℝ)
    (lo : ℤ) (n : ℕ) (x y : ℝ) : ℂ :=
  (((y * consecutiveFarOrientedBoundaryMask eta lo n x y : ℝ) : ℂ) *
      (starRingEnd ℂ (parent (x * y)) * parent y) +
    ((y * consecutiveFarOrientedValueMask eta lo n x y : ℝ) : ℂ) *
      (starRingEnd ℂ (deriv parent (x * y)) * parent y))

/-- Its symmetric completion, containing the derivative in both possible
slots of every unordered far pair. -/
def consecutiveFarSymmetricBoundaryMask
    (eta : ℤ → ℝ → ℝ) (lo : ℤ) (n : ℕ) (x y : ℝ) : ℝ :=
  ∑ p ∈ consecutiveFarPairs n,
    (deriv (eta (lo + (p.1.val : ℤ))) (x * y) *
        eta (lo + (p.2.val : ℤ)) y +
      deriv (eta (lo + (p.2.val : ℤ))) (x * y) *
        eta (lo + (p.1.val : ℤ)) y)

/-- The opposite first-slot derivative supplied by the symmetric quadratic
cross test but absent from the support-oriented separated formula. -/
def consecutiveFarReverseBoundaryMask
    (eta : ℤ → ℝ → ℝ) (lo : ℤ) (n : ℕ) (x y : ℝ) : ℝ :=
  ∑ p ∈ consecutiveFarPairs n,
    deriv (eta (lo + (p.2.val : ℤ))) (x * y) *
      eta (lo + (p.1.val : ℤ)) y

theorem consecutiveFarSymmetricBoundaryMask_eq_half_oriented_add_reverse
    (eta : ℤ → ℝ → ℝ) (lo : ℤ) (n : ℕ) (x y : ℝ) :
    consecutiveFarSymmetricBoundaryMask eta lo n x y =
      (1 / 2 : ℝ) * consecutiveFarOrientedBoundaryMask eta lo n x y +
        consecutiveFarReverseBoundaryMask eta lo n x y := by
  unfold consecutiveFarSymmetricBoundaryMask
    consecutiveFarOrientedBoundaryMask consecutiveFarReverseBoundaryMask
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro p _hp
  ring

/-- The coefficient-two sum of pairwise coherent derivative integrands is
pointwise one collective two-mask integrand. -/
theorem sum_coherentStarCorrelationDerivativeIntegrand_eq_collective
    (parent : BombieriTest) (eta : ℤ → ℝ → ℝ)
    (lo : ℤ) (n : ℕ) (x y : ℝ) :
    (∑ p ∈ consecutiveFarPairs n,
      (2 : ℂ) * coherentStarCorrelationDerivativeIntegrand parent
        (eta (lo + (p.1.val : ℤ)))
        (eta (lo + (p.2.val : ℤ))) x y) =
      consecutiveFarCollectiveDerivativeIntegrand
        parent eta lo n x y := by
  unfold coherentStarCorrelationDerivativeIntegrand
    consecutiveFarCollectiveDerivativeIntegrand
    consecutiveFarOrientedBoundaryMask consecutiveFarOrientedValueMask
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [Finset.sum_mul, Finset.sum_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  ring

private theorem coherentStarCorrelationDerivativeIntegrand_integrableOn
    (parent f h : BombieriTest) (eta theta : ℝ → ℝ)
    (heta : ContDiff ℝ ∞ eta)
    (hf : ∀ z, f z = (eta z : ℂ) * parent z)
    (hh : ∀ z, h z = (theta z : ℂ) * parent z)
    (x : ℝ) :
    IntegrableOn
      (coherentStarCorrelationDerivativeIntegrand parent eta theta x)
      (Set.Ioi 0) := by
  have hfderiv : Continuous (deriv f) :=
    f.contDiff.continuous_deriv (by simp)
  have hcontinuous : Continuous (fun y : ℝ ↦
      ((y : ℂ) * starRingEnd ℂ (deriv f (x * y))) * h y) := by
    fun_prop
  have hcompact : HasCompactSupport (fun y : ℝ ↦
      ((y : ℂ) * starRingEnd ℂ (deriv f (x * y))) * h y) := by
    simpa only [Pi.mul_apply] using h.hasCompactSupport.mul_left
      (f := fun y : ℝ ↦ (y : ℂ) *
        starRingEnd ℂ (deriv f (x * y)))
  have hgeneric : IntegrableOn (fun y : ℝ ↦
      ((y : ℂ) * starRingEnd ℂ (deriv f (x * y))) * h y)
      (Set.Ioi 0) :=
    (hcontinuous.integrable_of_hasCompactSupport hcompact).integrableOn
  refine hgeneric.congr_fun ?_ measurableSet_Ioi
  intro y _hy
  unfold coherentStarCorrelationDerivativeIntegrand
  change ((y : ℂ) * starRingEnd ℂ (deriv f (x * y))) * h y = _
  rw [deriv_eq_of_eq_realWeight_mul f parent eta heta hf (x * y), hh y]
  simp only [map_add, map_mul, starRingEnd_apply]
  simp only [RCLike.star_def, Complex.conj_ofReal]
  push_cast
  ring

/-- The finite far-pair sum commutes through the physical `y`-integral and
becomes one collective two-mask integral. -/
theorem sum_integral_coherentDerivative_eq_integral_collective
    (parent : BombieriTest) (A : ℤ → BombieriTest)
    (eta : ℤ → ℝ → ℝ) (lo : ℤ) (n : ℕ)
    (hcoh : ∀ k z,
      A k z = (eta k z : ℂ) * parent z)
    (hsmooth : ∀ k, ContDiff ℝ ∞ (eta k))
    (x : ℝ) :
    (∑ p ∈ consecutiveFarPairs n,
      (2 : ℂ) * ∫ y : ℝ in Set.Ioi 0,
        coherentStarCorrelationDerivativeIntegrand parent
          (eta (lo + (p.1.val : ℤ)))
          (eta (lo + (p.2.val : ℤ))) x y) =
      ∫ y : ℝ in Set.Ioi 0,
        consecutiveFarCollectiveDerivativeIntegrand
          parent eta lo n x y := by
  have hfun :
      (fun y : ℝ ↦ consecutiveFarCollectiveDerivativeIntegrand
        parent eta lo n x y) =
      (fun y : ℝ ↦ ∑ p ∈ consecutiveFarPairs n,
        (2 : ℂ) * coherentStarCorrelationDerivativeIntegrand parent
          (eta (lo + (p.1.val : ℤ)))
          (eta (lo + (p.2.val : ℤ))) x y) := by
    funext y
    exact (sum_coherentStarCorrelationDerivativeIntegrand_eq_collective
      parent eta lo n x y).symm
  rw [hfun]
  rw [MeasureTheory.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro p _hp
    exact (MeasureTheory.integral_const_mul (2 : ℂ)
      (fun y : ℝ ↦ coherentStarCorrelationDerivativeIntegrand parent
        (eta (lo + (p.1.val : ℤ)))
        (eta (lo + (p.2.val : ℤ))) x y)).symm
  · intro p _hp
    exact (coherentStarCorrelationDerivativeIntegrand_integrableOn
      parent (A (lo + (p.1.val : ℤ))) (A (lo + (p.2.val : ℤ)))
      (eta (lo + (p.1.val : ℤ))) (eta (lo + (p.2.val : ℤ)))
      (hsmooth _) (hcoh _) (hcoh _) x).const_mul (2 : ℂ)

private theorem headSymmetricLagBoundaryMask_ofFn
    (w : ℕ → ℝ) (eta : ℝ → ℝ) (k : ℕ)
    {n : ℕ} (a : Fin n → ℝ → ℝ) (x y : ℝ) :
    headSymmetricLagBoundaryMask w eta k (List.ofFn a) x y =
      ∑ i : Fin n,
        pairSymmetricLagBoundaryMask (w (k + i.val)) eta (a i) x y := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
      rw [List.ofFn_succ]
      simp only [headSymmetricLagBoundaryMask, Fin.sum_univ_succ]
      rw [ih]
      congr 1
      apply Finset.sum_congr rfl
      intro i _hi
      simp only [Fin.val_succ]
      congr 2
      omega

private theorem symmetricLinearLagBoundaryMask_ofFn_eq_orderedPairs
    (w : ℕ → ℝ) {n : ℕ} (a : Fin n → ℝ → ℝ) (x y : ℝ) :
    symmetricLinearLagBoundaryMask w (List.ofFn a) x y =
      ∑ hi : Fin n, ∑ low : Fin n,
        if low.val < hi.val then
          pairSymmetricLagBoundaryMask (w (hi.val - low.val))
            (a low) (a hi) x y
        else 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.ofFn_succ]
      simp only [symmetricLinearLagBoundaryMask,
        headSymmetricLagBoundaryMask_ofFn, Fin.sum_univ_succ]
      rw [ih (fun i ↦ a i.succ)]
      simp only [Fin.val_zero, Fin.val_succ, Nat.not_lt_zero, ↓reduceIte,
        Finset.sum_const_zero, zero_add]
      rw [Finset.sum_add_distrib]
      congr 1
      · apply Finset.sum_congr rfl
        intro hi _hhi
        simp only [Nat.zero_lt_succ, ↓reduceIte, Nat.sub_zero]
        congr 2
        omega
      · apply Finset.sum_congr rfl
        intro hi _hhi
        apply Finset.sum_congr rfl
        intro low _hlow
        simp only [Nat.succ_lt_succ_iff, Nat.succ_sub_succ_eq_sub]

/-- The symmetric completion of the ordered separated boundary is exactly
the production far residual boundary mask. -/
theorem consecutiveFarSymmetricBoundaryMask_eq_residualFarBoundaryMask
    (eta : ℤ → ℝ → ℝ) (lo : ℤ) (n : ℕ) (x y : ℝ) :
    consecutiveFarSymmetricBoundaryMask eta lo n x y =
      residualFarBoundaryMask
        (List.ofFn (integerBlock eta lo n)) x y := by
  unfold residualFarBoundaryMask
  rw [symmetricLinearLagBoundaryMask_ofFn_eq_orderedPairs]
  unfold consecutiveFarSymmetricBoundaryMask consecutiveFarPairs
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro hi _hhi
  apply Finset.sum_congr rfl
  intro low _hlow
  simp only [integerBlock]
  by_cases hfar : low.val + 3 ≤ hi.val
  · have hlt : low.val < hi.val := by omega
    have hdiff : 3 ≤ hi.val - low.val := by omega
    simp [hlt, hfar, hdiff, pairSymmetricLagBoundaryMask,
      bombieriFejerThreeResidualFarLagWeight]
    ring
  · by_cases hlt : low.val < hi.val
    · have hdiff : ¬ 3 ≤ hi.val - low.val := by omega
      simp [hlt, hfar, hdiff, pairSymmetricLagBoundaryMask,
        bombieriFejerThreeResidualFarLagWeight]
    · simp [hlt, hfar]

private theorem reverse_far_boundary_summand_eq_zero
    (parent : BombieriTest) (A : ℤ → BombieriTest)
    (eta : ℤ → ℝ → ℝ) (lo : ℤ) {n : ℕ}
    (hcoh : ∀ k z,
      A k z = (eta k z : ℂ) * parent z)
    (hsmooth : ∀ k, ContDiff ℝ ∞ (eta k))
    (hsupport : ∀ k,
      tsupport (A k) ⊆ Set.Icc
        (quarterLogLatticePoint k) (quarterLogLatticePoint (k + 2)))
    (hi low : Fin n) (hfar : low.val + 3 ≤ hi.val)
    (x y : ℝ) (hx : 1 < x) :
    (((y * deriv (eta (lo + (low.val : ℤ))) (x * y) *
        eta (lo + (hi.val : ℤ)) y : ℝ) : ℂ) *
      (starRingEnd ℂ (parent (x * y)) * parent y)) = 0 := by
  let ki : ℤ := lo + (hi.val : ℤ)
  let kj : ℤ := lo + (low.val : ℤ)
  by_cases hpy : parent y = 0
  · simp [hpy]
  by_cases hetai : eta ki y = 0
  · simp [ki, hetai]
  have hAiy : A ki y ≠ 0 := by
    rw [hcoh ki y]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hetai) hpy
  have hySupport : y ∈ tsupport (A ki) :=
    subset_tsupport (A ki) (Function.mem_support.mpr hAiy)
  have hyBounds := hsupport ki hySupport
  have hypos : 0 < y :=
    (quarterLogLatticePoint_pos ki).trans_le hyBounds.1
  have hyxy : y < x * y := by
    nlinarith
  have hsepIndex : kj + 2 < ki := by
    dsimp only [ki, kj]
    omega
  have hsep : quarterLogLatticePoint (kj + 2) <
      quarterLogLatticePoint ki :=
    quarterLogLatticePoint_strictMono hsepIndex
  have hzUpper : quarterLogLatticePoint (kj + 2) < x * y :=
    (hsep.trans_le hyBounds.1).trans hyxy
  have hzNot : x * y ∉ tsupport (A kj) := by
    intro hz
    exact (not_lt_of_ge (hsupport kj hz).2) hzUpper
  by_cases hpz : parent (x * y) = 0
  · simp [hpz]
  have hAzero : A kj (x * y) = 0 := by
    by_contra hne
    exact hzNot (subset_tsupport (A kj) (Function.mem_support.mpr hne))
  have hetaZero : eta kj (x * y) = 0 := by
    rw [hcoh kj (x * y)] at hAzero
    exact Complex.ofReal_eq_zero.mp
      ((mul_eq_zero.mp hAzero).resolve_right hpz)
  have hderivA : deriv (A kj) (x * y) = 0 :=
    deriv_of_notMem_tsupport hzNot
  have hproduct := deriv_eq_of_eq_realWeight_mul
    (A kj) parent (eta kj) (hsmooth kj) (hcoh kj) (x * y)
  rw [hderivA, hetaZero] at hproduct
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hproduct
  have hstarProduct := congrArg (starRingEnd ℂ) hproduct.symm
  simp only [map_mul, starRingEnd_apply, map_zero] at hstarProduct
  rw [RCLike.star_def, Complex.conj_ofReal] at hstarProduct
  change (((y * deriv (eta kj) (x * y) * eta ki y : ℝ) : ℂ) *
      (starRingEnd ℂ (parent (x * y)) * parent y)) = 0
  push_cast at hstarProduct ⊢
  calc
    _ = (((deriv (eta kj) (x * y) : ℝ) : ℂ) *
          starRingEnd ℂ (parent (x * y))) *
        ((y : ℂ) * ((eta ki y : ℝ) : ℂ)) * parent y := by ring
    _ = 0 := by rw [hstarProduct]; simp

/-- Strict support separation kills the reverse boundary after multiplication
by the common-parent kernel. -/
theorem consecutiveFarReverseBoundaryMask_integrand_eq_zero
    (parent : BombieriTest) (A : ℤ → BombieriTest)
    (eta : ℤ → ℝ → ℝ) (lo : ℤ) (n : ℕ)
    (hcoh : ∀ k z,
      A k z = (eta k z : ℂ) * parent z)
    (hsmooth : ∀ k, ContDiff ℝ ∞ (eta k))
    (hsupport : ∀ k,
      tsupport (A k) ⊆ Set.Icc
        (quarterLogLatticePoint k) (quarterLogLatticePoint (k + 2)))
    (x y : ℝ) (hx : 1 < x) :
    (((y * consecutiveFarReverseBoundaryMask eta lo n x y : ℝ) : ℂ) *
      (starRingEnd ℂ (parent (x * y)) * parent y)) = 0 := by
  unfold consecutiveFarReverseBoundaryMask
  push_cast
  rw [Finset.mul_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro p hp
  have hfar := mem_consecutiveFarPairs_iff.mp hp
  simpa only [Complex.ofReal_mul, mul_assoc] using
    (reverse_far_boundary_summand_eq_zero
      parent A eta lo hcoh hsmooth hsupport p.1 p.2 hfar x y hx)

/-- Hence the oriented boundary from the coefficient-two complex lift is
exactly twice the production symmetric far boundary. -/
theorem consecutiveFarOrientedBoundaryMask_integrand_eq_two_residualFar
    (parent : BombieriTest) (A : ℤ → BombieriTest)
    (eta : ℤ → ℝ → ℝ) (lo : ℤ) (n : ℕ)
    (hcoh : ∀ k z,
      A k z = (eta k z : ℂ) * parent z)
    (hsmooth : ∀ k, ContDiff ℝ ∞ (eta k))
    (hsupport : ∀ k,
      tsupport (A k) ⊆ Set.Icc
        (quarterLogLatticePoint k) (quarterLogLatticePoint (k + 2)))
    (x y : ℝ) (hx : 1 < x) :
    (((y * consecutiveFarOrientedBoundaryMask eta lo n x y : ℝ) : ℂ) *
        (starRingEnd ℂ (parent (x * y)) * parent y)) =
      (2 : ℂ) *
        (((y * residualFarBoundaryMask
          (List.ofFn (integerBlock eta lo n)) x y : ℝ) : ℂ) *
            (starRingEnd ℂ (parent (x * y)) * parent y)) := by
  rw [← consecutiveFarSymmetricBoundaryMask_eq_residualFarBoundaryMask]
  rw [consecutiveFarSymmetricBoundaryMask_eq_half_oriented_add_reverse]
  have hreverse := consecutiveFarReverseBoundaryMask_integrand_eq_zero
    parent A eta lo n hcoh hsmooth hsupport x y hx
  push_cast at hreverse ⊢
  ring_nf at hreverse ⊢
  rw [hreverse]
  ring

/-- On `x > 1`, the collective derivative integrand has twice the production
far residual boundary plus the still-surviving parent derivative. -/
theorem consecutiveFarCollectiveDerivativeIntegrand_eq_residualFarBoundary
    (parent : BombieriTest) (A : ℤ → BombieriTest)
    (eta : ℤ → ℝ → ℝ) (lo : ℤ) (n : ℕ)
    (hcoh : ∀ k z,
      A k z = (eta k z : ℂ) * parent z)
    (hsmooth : ∀ k, ContDiff ℝ ∞ (eta k))
    (hsupport : ∀ k,
      tsupport (A k) ⊆ Set.Icc
        (quarterLogLatticePoint k) (quarterLogLatticePoint (k + 2)))
    (x y : ℝ) (hx : 1 < x) :
    consecutiveFarCollectiveDerivativeIntegrand parent eta lo n x y =
      (2 : ℂ) *
        (((y * residualFarBoundaryMask
          (List.ofFn (integerBlock eta lo n)) x y : ℝ) : ℂ) *
            (starRingEnd ℂ (parent (x * y)) * parent y)) +
      (((y * consecutiveFarOrientedValueMask eta lo n x y : ℝ) : ℂ) *
        (starRingEnd ℂ (deriv parent (x * y)) * parent y)) := by
  unfold consecutiveFarCollectiveDerivativeIntegrand
  rw [consecutiveFarOrientedBoundaryMask_integrand_eq_two_residualFar
    parent A eta lo n hcoh hsmooth hsupport x y hx]

/-- Sharp collective inner-integral identity: all coefficient-two far pairs
become one integral whose cutoff component is exactly twice the production
`residualFarBoundaryMask`. -/
theorem sum_integral_coherentDerivative_eq_integral_residualFarBoundary
    (parent : BombieriTest) (A : ℤ → BombieriTest)
    (eta : ℤ → ℝ → ℝ) (lo : ℤ) (n : ℕ)
    (hcoh : ∀ k z,
      A k z = (eta k z : ℂ) * parent z)
    (hsmooth : ∀ k, ContDiff ℝ ∞ (eta k))
    (hsupport : ∀ k,
      tsupport (A k) ⊆ Set.Icc
        (quarterLogLatticePoint k) (quarterLogLatticePoint (k + 2)))
    (x : ℝ) (hx : 1 < x) :
    (∑ p ∈ consecutiveFarPairs n,
      (2 : ℂ) * ∫ y : ℝ in Set.Ioi 0,
        coherentStarCorrelationDerivativeIntegrand parent
          (eta (lo + (p.1.val : ℤ)))
          (eta (lo + (p.2.val : ℤ))) x y) =
      ∫ y : ℝ in Set.Ioi 0,
        ((2 : ℂ) *
            (((y * residualFarBoundaryMask
              (List.ofFn (integerBlock eta lo n)) x y : ℝ) : ℂ) *
                (starRingEnd ℂ (parent (x * y)) * parent y)) +
          (((y * consecutiveFarOrientedValueMask eta lo n x y : ℝ) : ℂ) *
            (starRingEnd ℂ (deriv parent (x * y)) * parent y))) := by
  rw [sum_integral_coherentDerivative_eq_integral_collective
    parent A eta lo n hcoh hsmooth x]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y _hy
  exact consecutiveFarCollectiveDerivativeIntegrand_eq_residualFarBoundary
    parent A eta lo n hcoh hsmooth hsupport x y hx

end

end ArithmeticHodge.Analysis.MultiplicativeWeilCoherentFarResidualCorrectedPotentialStructural
