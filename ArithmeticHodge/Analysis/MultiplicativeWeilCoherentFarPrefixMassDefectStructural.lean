import ArithmeticHodge.Analysis.MultiplicativeWeilCoherentFarResidualCorrectedPotentialStructural

set_option autoImplicit false

open Complex Finset MeasureTheory Real Set Filter
open scoped BigOperators ContDiff Distributions

namespace ArithmeticHodge.Analysis.MultiplicativeWeilCoherentFarPrefixMassDefectStructural

noncomputable section

open MultiplicativeWeil

/-!
# Ordinary-mass defect of the cumulative far prefix

Regrouping the coefficient-two far boundary by its high cell replaces the
individual low weights by a cumulative low prefix.  Partition unity cancels
the unweighted sum of cell derivative masses, but the cumulative prefix is
not constant in the high index.  The exact surviving term is the negative
near cumulative mass below.
-/

/-- Sum of low-cell weights at least three positions left of `hi`. -/
def farLowPrefix {n : ℕ}
    (eta : Fin n → ℝ → ℝ) (hi : Fin n) (y : ℝ) : ℝ :=
  ∑ low : Fin n,
    if low.val + 3 ≤ hi.val then eta low y else 0

/-- Complementary derivative mass through the two cells adjacent to
`low`. -/
def farCumulativeNearMass {n : ℕ}
    (mass : Fin n → ℂ) (low : Fin n) : ℂ :=
  ∑ hi : Fin n,
    if hi.val ≤ low.val + 2 then mass hi else 0

/-- Ordinary mass of the derivative source in one coherent cell. -/
def coherentCellDerivativeMass {n : ℕ}
    (parent : BombieriTest) (eta : Fin n → ℝ → ℝ)
    (hi : Fin n) : ℂ :=
  ∫ z : ℝ in Set.Ioi 0,
    ((deriv (eta hi) z : ℝ) : ℂ) * parent z

/-- Coefficient-two far derivative source after regrouping by high cell. -/
def coherentFarPrefixSource {n : ℕ}
    (parent : BombieriTest) (eta : Fin n → ℝ → ℝ)
    (y z : ℝ) : ℂ :=
  (2 : ℂ) * ∑ hi : Fin n,
    ((farLowPrefix eta hi y : ℝ) : ℂ) *
      (((deriv (eta hi) z : ℝ) : ℂ) * parent z)

private theorem farTailMass_eq_neg_cumulativeNearMass
    {n : ℕ} (mass : Fin n → ℂ)
    (hmass : ∑ hi, mass hi = 0) (low : Fin n) :
    (∑ hi : Fin n,
      if low.val + 3 ≤ hi.val then mass hi else 0) =
      -farCumulativeNearMass mass low := by
  have hsplit :
      (∑ hi : Fin n,
          if low.val + 3 ≤ hi.val then mass hi else 0) +
        farCumulativeNearMass mass low = 0 := by
    unfold farCumulativeNearMass
    rw [← Finset.sum_add_distrib]
    calc
      (∑ hi : Fin n,
          ((if low.val + 3 ≤ hi.val then mass hi else 0) +
            (if hi.val ≤ low.val + 2 then mass hi else 0))) =
          ∑ hi : Fin n, mass hi := by
            apply Finset.sum_congr rfl
            intro hi _hhi
            by_cases hfar : low.val + 3 ≤ hi.val
            · have hnear : ¬ hi.val ≤ low.val + 2 := by omega
              simp [hfar, hnear]
            · have hnear : hi.val ≤ low.val + 2 := by omega
              simp [hfar, hnear]
      _ = 0 := hmass
  exact eq_neg_of_add_eq_zero_left hsplit

private theorem sum_lowPrefix_mul_mass_eq_neg_cumulativeNear
    {n : ℕ} (mass : Fin n → ℂ) (weight : Fin n → ℂ)
    (hmass : ∑ hi, mass hi = 0) :
    (∑ hi : Fin n,
        (∑ low : Fin n,
          if low.val + 3 ≤ hi.val then weight low else 0) * mass hi) =
      -∑ low : Fin n,
        weight low * farCumulativeNearMass mass low := by
  calc
    (∑ hi : Fin n,
        (∑ low : Fin n,
          if low.val + 3 ≤ hi.val then weight low else 0) * mass hi) =
      ∑ hi : Fin n, ∑ low : Fin n,
        if low.val + 3 ≤ hi.val then weight low * mass hi else 0 := by
          apply Finset.sum_congr rfl
          intro hi _hhi
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro low _hlow
          by_cases hfar : low.val + 3 ≤ hi.val <;> simp [hfar]
    _ = ∑ low : Fin n, ∑ hi : Fin n,
        if low.val + 3 ≤ hi.val then weight low * mass hi else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ low : Fin n, weight low *
        (∑ hi : Fin n,
          if low.val + 3 ≤ hi.val then mass hi else 0) := by
          apply Finset.sum_congr rfl
          intro low _hlow
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro hi _hhi
          by_cases hfar : low.val + 3 ≤ hi.val <;> simp [hfar]
    _ = ∑ low : Fin n,
        weight low * (-farCumulativeNearMass mass low) := by
          apply Finset.sum_congr rfl
          intro low _hlow
          rw [farTailMass_eq_neg_cumulativeNearMass mass hmass low]
    _ = ∑ low : Fin n,
        -(weight low * farCumulativeNearMass mass low) := by
          apply Finset.sum_congr rfl
          intro low _hlow
          ring
    _ = -∑ low : Fin n,
        weight low * farCumulativeNearMass mass low := by
          rw [Finset.sum_neg_distrib]

private theorem derivativeWeight_integrableOn
    (parent : BombieriTest) (eta : ℝ → ℝ)
    (heta : ContDiff ℝ ∞ eta) :
    IntegrableOn
      (fun z : ℝ ↦ ((deriv eta z : ℝ) : ℂ) * parent z)
      (Set.Ioi 0) := by
  have hcontinuous : Continuous
      (fun z : ℝ ↦ ((deriv eta z : ℝ) : ℂ) * parent z) := by
    have hderiv : Continuous (deriv eta) :=
      heta.continuous_deriv (by simp)
    fun_prop
  have hcompact : HasCompactSupport
      (fun z : ℝ ↦ ((deriv eta z : ℝ) : ℂ) * parent z) := by
    simpa only [Pi.mul_apply] using parent.hasCompactSupport.mul_left
      (f := fun z : ℝ ↦ ((deriv eta z : ℝ) : ℂ))
  exact (hcontinuous.integrable_of_hasCompactSupport hcompact).integrableOn

private theorem sum_hasDerivAt
    {n : ℕ} (eta : Fin n → ℝ → ℝ)
    (hsmooth : ∀ i, ContDiff ℝ ∞ (eta i)) (z : ℝ) :
    HasDerivAt (fun w : ℝ ↦ ∑ i : Fin n, eta i w)
      (∑ i : Fin n, deriv (eta i) z) z := by
  exact HasDerivAt.fun_sum fun i _hi ↦
    ((hsmooth i).differentiable (by simp) z).hasDerivAt

private theorem sum_deriv_mul_parent_eq_zero_of_partitionOn
    {n : ℕ} (parent : BombieriTest) (eta : Fin n → ℝ → ℝ)
    (hsmooth : ∀ i, ContDiff ℝ ∞ (eta i))
    (hpartition : ∀ z ∈ tsupport parent, ∑ i : Fin n, eta i z = 1)
    (z : ℝ) :
    (((∑ i : Fin n, deriv (eta i) z : ℝ) : ℂ) * parent z) = 0 := by
  by_cases hp : parent z = 0
  · simp [hp]
  have hzSupport : z ∈ Function.support (parent : ℝ → ℂ) :=
    Function.mem_support.mpr hp
  have heventSupport : ∀ᶠ w in nhds z,
      w ∈ Function.support (parent : ℝ → ℂ) :=
    parent.contDiff.continuous.isOpen_support.mem_nhds hzSupport
  have heventPartition :
      (fun w : ℝ ↦ ∑ i : Fin n, eta i w) =ᶠ[nhds z]
        (fun _w : ℝ ↦ 1) := by
    filter_upwards [heventSupport] with w hw
    exact hpartition w (subset_tsupport parent hw)
  have hderivZero : (∑ i : Fin n, deriv (eta i) z) = 0 := by
    calc
      (∑ i : Fin n, deriv (eta i) z) =
          deriv (fun w : ℝ ↦ ∑ i : Fin n, eta i w) z :=
            (sum_hasDerivAt eta hsmooth z).deriv.symm
      _ = deriv (fun _w : ℝ ↦ 1) z :=
        heventPartition.deriv_eq
      _ = 0 := by simp
  rw [hderivZero]
  simp

/-- Partition unity on the parent support forces cancellation of the total
unweighted cell derivative mass. -/
theorem sum_coherentCellDerivativeMass_eq_zero_of_partitionOn
    {n : ℕ} (parent : BombieriTest) (eta : Fin n → ℝ → ℝ)
    (hsmooth : ∀ i, ContDiff ℝ ∞ (eta i))
    (hpartition : ∀ z ∈ tsupport parent, ∑ i : Fin n, eta i z = 1) :
    ∑ i : Fin n, coherentCellDerivativeMass parent eta i = 0 := by
  unfold coherentCellDerivativeMass
  rw [← MeasureTheory.integral_finset_sum]
  · apply integral_eq_zero_of_ae
    filter_upwards with z
    rw [← Finset.sum_mul]
    have hzero := sum_deriv_mul_parent_eq_zero_of_partitionOn
      parent eta hsmooth hpartition z
    calc
      (∑ i : Fin n, ((deriv (eta i) z : ℝ) : ℂ)) * parent z =
          (((∑ i : Fin n, deriv (eta i) z : ℝ) : ℂ) *
            parent z) := by
              congr 1
              push_cast
              rfl
      _ = 0 := hzero
  · intro i _hi
    exact derivativeWeight_integrableOn parent (eta i) (hsmooth i)

private theorem integral_coherentFarPrefixSource_eq_weightedMass
    {n : ℕ} (parent : BombieriTest) (eta : Fin n → ℝ → ℝ)
    (hsmooth : ∀ i, ContDiff ℝ ∞ (eta i)) (y : ℝ) :
    (∫ z : ℝ in Set.Ioi 0, coherentFarPrefixSource parent eta y z) =
      (2 : ℂ) * ∑ hi : Fin n,
        ((farLowPrefix eta hi y : ℝ) : ℂ) *
          coherentCellDerivativeMass parent eta hi := by
  unfold coherentFarPrefixSource
  calc
    (∫ z : ℝ in Set.Ioi 0,
        (2 : ℂ) *
          ∑ hi : Fin n,
            ((farLowPrefix eta hi y : ℝ) : ℂ) *
              (((deriv (eta hi) z : ℝ) : ℂ) * parent z)) =
        (2 : ℂ) * ∫ z : ℝ in Set.Ioi 0,
          ∑ hi : Fin n,
            ((farLowPrefix eta hi y : ℝ) : ℂ) *
              (((deriv (eta hi) z : ℝ) : ℂ) * parent z) := by
      exact integral_const_mul (2 : ℂ) _
    _ = (2 : ℂ) * ∑ hi : Fin n,
        ((farLowPrefix eta hi y : ℝ) : ℂ) *
          coherentCellDerivativeMass parent eta hi := by
      congr 1
      rw [MeasureTheory.integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro hi _hhi
        exact integral_const_mul ((farLowPrefix eta hi y : ℝ) : ℂ)
          (fun z : ℝ ↦
            ((deriv (eta hi) z : ℝ) : ℂ) * parent z)
      · intro hi _hhi
        exact (derivativeWeight_integrableOn
          parent (eta hi) (hsmooth hi)).const_mul _

private theorem ofReal_farLowPrefix
    {n : ℕ} (eta : Fin n → ℝ → ℝ) (hi : Fin n) (y : ℝ) :
    ((farLowPrefix eta hi y : ℝ) : ℂ) =
      ∑ low : Fin n,
        if low.val + 3 ≤ hi.val then (eta low y : ℂ) else 0 := by
  unfold farLowPrefix
  push_cast
  apply Finset.sum_congr rfl
  intro low _hlow
  by_cases hfar : low.val + 3 ≤ hi.val <;> simp [hfar]

/-- Sharp coefficient-two mass formula.  Total derivative-mass cancellation
leaves the negative cumulative near defect rather than zero. -/
theorem integral_coherentFarPrefixSource_eq_neg_cumulativeNear
    {n : ℕ} (parent : BombieriTest) (eta : Fin n → ℝ → ℝ)
    (hsmooth : ∀ i, ContDiff ℝ ∞ (eta i))
    (hpartition : ∀ z ∈ tsupport parent, ∑ i : Fin n, eta i z = 1)
    (y : ℝ) :
    (∫ z : ℝ in Set.Ioi 0, coherentFarPrefixSource parent eta y z) =
      -(2 : ℂ) * ∑ low : Fin n, (eta low y : ℂ) *
        farCumulativeNearMass (coherentCellDerivativeMass parent eta) low := by
  rw [integral_coherentFarPrefixSource_eq_weightedMass
    parent eta hsmooth y]
  have hmass := sum_coherentCellDerivativeMass_eq_zero_of_partitionOn
    parent eta hsmooth hpartition
  have hcomb := sum_lowPrefix_mul_mass_eq_neg_cumulativeNear
    (coherentCellDerivativeMass parent eta)
    (fun low ↦ (eta low y : ℂ)) hmass
  have hweighted :
      (∑ hi : Fin n,
          ((farLowPrefix eta hi y : ℝ) : ℂ) *
            coherentCellDerivativeMass parent eta hi) =
        -∑ low : Fin n, (eta low y : ℂ) *
          farCumulativeNearMass
            (coherentCellDerivativeMass parent eta) low := by
    simpa only [ofReal_farLowPrefix] using hcomb
  rw [hweighted]
  ring

private theorem fourCell_lowPrefix_mass_eq_singleFarPair
    (mass weight : Fin 4 → ℂ) :
    (∑ hi : Fin 4,
        (∑ low : Fin 4,
          if low.val + 3 ≤ hi.val then weight low else 0) * mass hi) =
      weight ⟨0, by omega⟩ * mass ⟨3, by omega⟩ := by
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ]
  norm_num
  left
  congr

/-- The first nonempty padded block already has a surviving mass: for four
cells the cumulative far source is exactly the single `0 → 3` pair. -/
theorem integral_fourCell_coherentFarPrefixSource_eq_singlePair
    (parent : BombieriTest) (eta : Fin 4 → ℝ → ℝ)
    (hsmooth : ∀ i, ContDiff ℝ ∞ (eta i)) (y : ℝ) :
    (∫ z : ℝ in Set.Ioi 0, coherentFarPrefixSource parent eta y z) =
      (2 : ℂ) * (eta ⟨0, by omega⟩ y : ℂ) *
        coherentCellDerivativeMass parent eta ⟨3, by omega⟩ := by
  rw [integral_coherentFarPrefixSource_eq_weightedMass
    parent eta hsmooth y]
  have hfour := fourCell_lowPrefix_mass_eq_singleFarPair
    (coherentCellDerivativeMass parent eta)
    (fun low ↦ (eta low y : ℂ))
  have hweighted :
      (∑ hi : Fin 4,
          ((farLowPrefix eta hi y : ℝ) : ℂ) *
            coherentCellDerivativeMass parent eta hi) =
        (eta ⟨0, by omega⟩ y : ℂ) *
          coherentCellDerivativeMass parent eta ⟨3, by omega⟩ := by
    simpa only [ofReal_farLowPrefix] using hfour
  rw [hweighted]
  ring

end

end ArithmeticHodge.Analysis.MultiplicativeWeilCoherentFarPrefixMassDefectStructural
