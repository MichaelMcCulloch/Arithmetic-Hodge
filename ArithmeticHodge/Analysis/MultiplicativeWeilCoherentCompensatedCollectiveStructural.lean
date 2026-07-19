import ArithmeticHodge.Analysis.MultiplicativeWeilCoherentCompensatedCutoffCrossStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilCoherentFarResidualCorrectedPotentialStructural

set_option autoImplicit false

open Complex Finset MeasureTheory Real Set
open scoped BigOperators ContDiff

namespace ArithmeticHodge.Analysis.MultiplicativeWeilCoherentCompensatedCollectiveStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilCoherentCompensatedCutoffCrossStructural
open MultiplicativeWeilCoherentFarResidualCorrectedPotentialStructural

/-!
# Collective compensated coherent cutoff crosses

The coefficient-two sum over all production far pairs separates into the
correlation derivatives of the compensated companions and an explicit
rank-one remainder.  The latter groups by high cell against one lower
far-tail Bombieri test.
-/

/-- The sum of cells at least three positions below a fixed high position. -/
def lowFarTail
    (A : ℤ → BombieriTest) (lo : ℤ) (n : ℕ) (hi : Fin n) :
    BombieriTest :=
  ∑ low : Fin n,
    if low.val + 3 ≤ hi.val then
      A (lo + (low.val : ℤ))
    else 0

/-- Summing the exact compensated pair identity over every production far
pair separates the coefficient-two cutoff sum into companion correlation
derivatives and one explicit conjugated-mass rank-one remainder. -/
theorem sum_far_coherentCutoff_eq_companions_add_rankOne
    (parent : BombieriTest)
    (A U rho : ℤ → BombieriTest)
    (eta : ℤ → ℝ → ℝ) (mass : ℤ → ℂ)
    (lo : ℤ) (n : ℕ)
    (hcoh : ∀ k z,
      A k z = (eta k z : ℂ) * parent z)
    (hU : ∀ k z,
      deriv (U k) z =
        ((deriv (eta k) z : ℝ) : ℂ) * parent z -
          mass k * rho k z)
    (x : ℝ) :
    (∑ p ∈ consecutiveFarPairs n,
      (2 : ℂ) * ∫ y : ℝ in Set.Ioi 0,
        coherentCutoffBoundaryIntegrand parent
          (eta (lo + (p.1.val : ℤ)))
          (eta (lo + (p.2.val : ℤ))) x y) =
      (∑ p ∈ consecutiveFarPairs n,
        (2 : ℂ) * deriv (fun z : ℝ ↦
          starRingEnd ℂ
            (bombieriDirectedCorrelation
              (U (lo + (p.1.val : ℤ)))
              (A (lo + (p.2.val : ℤ))) z)) x) +
      ∑ p ∈ consecutiveFarPairs n,
        (2 : ℂ) * starRingEnd ℂ (mass (lo + (p.1.val : ℤ))) *
          ∫ y : ℝ in Set.Ioi 0,
            rankOneSourceIntegrand
              (rho (lo + (p.1.val : ℤ)))
              (A (lo + (p.2.val : ℤ))) x y := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  have H := integral_coherentCutoffBoundary_eq_companion_add_rankOne
    parent
    (rho (lo + (p.1.val : ℤ)))
    (A (lo + (p.2.val : ℤ)))
    (U (lo + (p.1.val : ℤ)))
    (eta (lo + (p.1.val : ℤ)))
    (eta (lo + (p.2.val : ℤ)))
    (mass (lo + (p.1.val : ℤ)))
    (hcoh (lo + (p.2.val : ℤ)))
    (hU (lo + (p.1.val : ℤ))) x
  rw [H]
  ring

private theorem rankOneSourceIntegrand_integrableOn
    (rho h : BombieriTest) (x : ℝ) :
    IntegrableOn (rankOneSourceIntegrand rho h x) (Set.Ioi 0) := by
  have hcontinuous : Continuous (rankOneSourceIntegrand rho h x) := by
    unfold rankOneSourceIntegrand
    fun_prop
  have hcompact : HasCompactSupport (rankOneSourceIntegrand rho h x) := by
    unfold rankOneSourceIntegrand
    simpa only [Pi.mul_apply] using h.hasCompactSupport.mul_left
      (f := fun y : ℝ ↦
        (y : ℂ) * starRingEnd ℂ (rho (x * y)))
  exact (hcontinuous.integrable_of_hasCompactSupport hcompact).integrableOn

private theorem rankOneSourceIntegrand_lowFarTail
    (A rho : ℤ → BombieriTest) (lo : ℤ) (n : ℕ)
    (hi : Fin n) (x y : ℝ) :
    rankOneSourceIntegrand (rho (lo + (hi.val : ℤ)))
        (lowFarTail A lo n hi) x y =
      ∑ low : Fin n,
        if low.val + 3 ≤ hi.val then
          rankOneSourceIntegrand (rho (lo + (hi.val : ℤ)))
            (A (lo + (low.val : ℤ))) x y
        else 0 := by
  unfold rankOneSourceIntegrand lowFarTail
  let ev : BombieriTest →+ ℂ :=
    { toFun := fun f ↦ f y
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  change ((y : ℂ) * starRingEnd ℂ
      (rho (lo + (hi.val : ℤ)) (x * y))) *
      ev (∑ low : Fin n,
        if low.val + 3 ≤ hi.val then
          A (lo + (low.val : ℤ))
        else 0) = _
  rw [map_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro low _hlow
  by_cases hfar : low.val + 3 ≤ hi.val
  · simp [hfar, ev]
  · simp [hfar, ev]

/-- The rank-one remainder groups by high cell: each conjugated mass couples
its compensating bump to the sum of all lower cells at far lag. -/
theorem sum_far_rankOne_eq_sum_high_lowFarTail
    (A rho : ℤ → BombieriTest) (mass : ℤ → ℂ)
    (lo : ℤ) (n : ℕ) (x : ℝ) :
    (∑ p ∈ consecutiveFarPairs n,
      (2 : ℂ) * starRingEnd ℂ (mass (lo + (p.1.val : ℤ))) *
        ∫ y : ℝ in Set.Ioi 0,
          rankOneSourceIntegrand
            (rho (lo + (p.1.val : ℤ)))
            (A (lo + (p.2.val : ℤ))) x y) =
      ∑ hi : Fin n,
        (2 : ℂ) * starRingEnd ℂ (mass (lo + (hi.val : ℤ))) *
          ∫ y : ℝ in Set.Ioi 0,
            rankOneSourceIntegrand
              (rho (lo + (hi.val : ℤ)))
              (lowFarTail A lo n hi) x y := by
  unfold consecutiveFarPairs
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro hi _hhi
  have hinner :
      (∑ low : Fin n,
        if low.val + 3 ≤ hi.val then
          ∫ y : ℝ in Set.Ioi 0,
            rankOneSourceIntegrand
              (rho (lo + (hi.val : ℤ)))
              (A (lo + (low.val : ℤ))) x y
        else 0) =
      ∫ y : ℝ in Set.Ioi 0,
        rankOneSourceIntegrand
          (rho (lo + (hi.val : ℤ)))
          (lowFarTail A lo n hi) x y := by
    rw [show (fun y : ℝ ↦
        rankOneSourceIntegrand
          (rho (lo + (hi.val : ℤ)))
          (lowFarTail A lo n hi) x y) =
      (fun y : ℝ ↦ ∑ low : Fin n,
        if low.val + 3 ≤ hi.val then
          rankOneSourceIntegrand
            (rho (lo + (hi.val : ℤ)))
            (A (lo + (low.val : ℤ))) x y
        else 0) by
          funext y
          exact rankOneSourceIntegrand_lowFarTail A rho lo n hi x y]
    rw [MeasureTheory.integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro low _hlow
      by_cases hfar : low.val + 3 ≤ hi.val
      · simp [hfar]
      · simp [hfar]
    · intro low _hlow
      by_cases hfar : low.val + 3 ≤ hi.val
      · simpa [hfar] using
          rankOneSourceIntegrand_integrableOn
            (rho (lo + (hi.val : ℤ)))
            (A (lo + (low.val : ℤ))) x
      · simp [hfar]
  let c : ℂ :=
    (2 : ℂ) * starRingEnd ℂ (mass (lo + (hi.val : ℤ)))
  change (∑ low : Fin n,
      if low.val + 3 ≤ hi.val then
        c * ∫ y : ℝ in Set.Ioi 0,
          rankOneSourceIntegrand
            (rho (lo + (hi.val : ℤ)))
            (A (lo + (low.val : ℤ))) x y
      else 0) =
    c * ∫ y : ℝ in Set.Ioi 0,
      rankOneSourceIntegrand
        (rho (lo + (hi.val : ℤ)))
        (lowFarTail A lo n hi) x y
  calc
    (∑ low : Fin n,
        if low.val + 3 ≤ hi.val then
          c * ∫ y : ℝ in Set.Ioi 0,
            rankOneSourceIntegrand
              (rho (lo + (hi.val : ℤ)))
              (A (lo + (low.val : ℤ))) x y
        else 0) =
      c * ∑ low : Fin n,
        if low.val + 3 ≤ hi.val then
          ∫ y : ℝ in Set.Ioi 0,
            rankOneSourceIntegrand
              (rho (lo + (hi.val : ℤ)))
              (A (lo + (low.val : ℤ))) x y
        else 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro low _hlow
          by_cases hfar : low.val + 3 ≤ hi.val
          · simp [hfar]
          · simp [hfar]
    _ = _ := congrArg (fun z : ℂ ↦ c * z) hinner

end

end ArithmeticHodge.Analysis.MultiplicativeWeilCoherentCompensatedCollectiveStructural
