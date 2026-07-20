import ArithmeticHodge.Analysis.YoshidaFourCellOddCoreBlockPiconeStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddCoreBlockPiconeIntegralStructural

noncomputable section

open UnitIntervalLogEnergyAffine
open YoshidaFourCellOddCoreBlockPiconeStructural
open YoshidaFourCellOddCoreGroundStatePiconeStructural
open YoshidaFourCellOddEndpointStripCoercivityStructural
open YoshidaFourCellOddStripCapacityClosureStructural
open YoshidaFourCellOddStripEmbeddingStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaFourCellRawParityFoldStructural
open YoshidaFourCellRegularParityFoldStructural
open YoshidaRegularKernelBound
open YoshidaEndpointTriangleFoldLipschitz
open YoshidaEndpointPositiveDistanceFold
open YoshidaConstantBounds
open YoshidaFactorTwoIntegrableLagRepresenterStructural
open CenteredEndpointCorrelation

/-!
# Integral block Picone decomposition of the odd four-cell core

This file transports the pointwise strip-parity Picone identities to the
actual integral defining `fourCellOddCoreLocalQuadratic`.  The lower interval
is `A = [0,3/5)` and the endpoint strip is `B = [3/5,1]`.

The first result below is an exact, public `A/B` partition of the coupled
raw square.  It is followed by a profile-parameterized Picone transform.
The profile is required to be positive on the closed positive half and its
strip-even part positive on the normalized strip.  Those are form-domain
conditions, not assumptions about the sign of the target quadratic.
-/

def lowerRawSet : Set ℝ := Ico 0 (3 / 5)

def endpointRawSet : Set ℝ := Icc (3 / 5) 1

def positiveHalfSet : Set ℝ := Icc 0 1

private theorem positiveHalfSet_eq_lower_union_endpoint :
    positiveHalfSet = lowerRawSet ∪ endpointRawSet := by
  ext x
  simp only [positiveHalfSet, lowerRawSet, endpointRawSet, mem_Icc,
    mem_Ico, mem_union]
  constructor
  · intro hx
    by_cases hxc : x < 3 / 5
    · exact Or.inl ⟨hx.1, hxc⟩
    · exact Or.inr ⟨le_of_not_gt hxc, hx.2⟩
  · rintro (hx | hx)
    · exact ⟨hx.1, hx.2.le.trans (by norm_num)⟩
    · exact ⟨by linarith [hx.1], hx.2⟩

private theorem lowerRawSet_disjoint_endpointRawSet :
    Disjoint lowerRawSet endpointRawSet := by
  rw [Set.disjoint_left]
  intro x hxA hxB
  exact (not_lt_of_ge hxB.1) hxA.2

/-- Convert an iterated interval integral over a closed square to the
corresponding product set integral. -/
theorem intervalIntegral_integral_eq_setIntegral_square
    (F : ℝ × ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hF : IntegrableOn F (Icc a b ×ˢ Icc a b)
      ((volume : Measure ℝ).prod volume)) :
    (∫ x : ℝ in a..b, ∫ y : ℝ in a..b, F (x, y)) =
      ∫ p : ℝ × ℝ in Icc a b ×ˢ Icc a b, F p := by
  calc
    (∫ x : ℝ in a..b, ∫ y : ℝ in a..b, F (x, y)) =
        ∫ x : ℝ in Icc a b, ∫ y : ℝ in Icc a b, F (x, y) := by
      rw [intervalIntegral.integral_of_le hab,
        ← integral_Icc_eq_integral_Ioc]
      apply setIntegral_congr_fun measurableSet_Icc
      intro x _hx
      change (∫ y : ℝ in a..b, F (x, y)) =
        ∫ y : ℝ in Icc a b, F (x, y)
      rw [intervalIntegral.integral_of_le hab,
        ← integral_Icc_eq_integral_Ioc]
    _ = ∫ p : ℝ × ℝ in Icc a b ×ˢ Icc a b, F p :=
      (setIntegral_prod F hF).symm

/-- Abstract exact square partition for a symmetric integrand. -/
theorem setIntegral_positiveHalfSquare_eq_lower_cross_endpoint
    (K : ℝ × ℝ → ℝ)
    (hK : IntegrableOn K (positiveHalfSet ×ˢ positiveHalfSet)
      ((volume : Measure ℝ).prod volume))
    (hsymm : ∀ p : ℝ × ℝ, K p.swap = K p) :
    (∫ p : ℝ × ℝ in positiveHalfSet ×ˢ positiveHalfSet, K p
        ∂((volume : Measure ℝ).prod volume)) =
      (∫ p : ℝ × ℝ in lowerRawSet ×ˢ lowerRawSet, K p
        ∂((volume : Measure ℝ).prod volume)) +
      2 * (∫ p : ℝ × ℝ in endpointRawSet ×ˢ lowerRawSet, K p
        ∂((volume : Measure ℝ).prod volume)) +
      ∫ p : ℝ × ℝ in endpointRawSet ×ˢ endpointRawSet, K p
        ∂((volume : Measure ℝ).prod volume) := by
  have hAsub : lowerRawSet ⊆ positiveHalfSet := by
    intro x hx
    exact ⟨hx.1, hx.2.le.trans (by norm_num)⟩
  have hBsub : endpointRawSet ⊆ positiveHalfSet := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  have hAA := hK.mono_set (Set.prod_mono hAsub hAsub)
  have hAB := hK.mono_set (Set.prod_mono hAsub hBsub)
  have hBA := hK.mono_set (Set.prod_mono hBsub hAsub)
  have hBB := hK.mono_set (Set.prod_mono hBsub hBsub)
  have hAmeas : MeasurableSet lowerRawSet := measurableSet_Ico
  have hBmeas : MeasurableSet endpointRawSet := measurableSet_Icc
  have hUmeas : MeasurableSet positiveHalfSet := measurableSet_Icc
  have houter :
      (∫ p : ℝ × ℝ in positiveHalfSet ×ˢ positiveHalfSet, K p
        ∂((volume : Measure ℝ).prod volume)) =
      (∫ p : ℝ × ℝ in lowerRawSet ×ˢ positiveHalfSet, K p
        ∂((volume : Measure ℝ).prod volume)) +
      ∫ p : ℝ × ℝ in endpointRawSet ×ˢ positiveHalfSet, K p
        ∂((volume : Measure ℝ).prod volume) := by
    rw [show positiveHalfSet ×ˢ positiveHalfSet =
        (lowerRawSet ×ˢ positiveHalfSet) ∪
          (endpointRawSet ×ˢ positiveHalfSet) by
      rw [positiveHalfSet_eq_lower_union_endpoint, union_prod]]
    exact setIntegral_union
      (lowerRawSet_disjoint_endpointRawSet.set_prod_left
        positiveHalfSet positiveHalfSet)
      (hBmeas.prod hUmeas)
      (hK.mono_set (Set.prod_mono hAsub (Subset.rfl)))
      (hK.mono_set (Set.prod_mono hBsub (Subset.rfl)))
  have hleft :
      (∫ p : ℝ × ℝ in lowerRawSet ×ˢ positiveHalfSet, K p
        ∂((volume : Measure ℝ).prod volume)) =
      (∫ p : ℝ × ℝ in lowerRawSet ×ˢ lowerRawSet, K p
        ∂((volume : Measure ℝ).prod volume)) +
      ∫ p : ℝ × ℝ in lowerRawSet ×ˢ endpointRawSet, K p
        ∂((volume : Measure ℝ).prod volume) := by
    rw [show lowerRawSet ×ˢ positiveHalfSet =
        (lowerRawSet ×ˢ lowerRawSet) ∪
          (lowerRawSet ×ˢ endpointRawSet) by
      rw [positiveHalfSet_eq_lower_union_endpoint, prod_union]]
    exact setIntegral_union
      (lowerRawSet_disjoint_endpointRawSet.set_prod_right
        lowerRawSet lowerRawSet)
      (hAmeas.prod hBmeas) hAA hAB
  have hright :
      (∫ p : ℝ × ℝ in endpointRawSet ×ˢ positiveHalfSet, K p
        ∂((volume : Measure ℝ).prod volume)) =
      (∫ p : ℝ × ℝ in endpointRawSet ×ˢ lowerRawSet, K p
        ∂((volume : Measure ℝ).prod volume)) +
      ∫ p : ℝ × ℝ in endpointRawSet ×ˢ endpointRawSet, K p
        ∂((volume : Measure ℝ).prod volume) := by
    rw [show endpointRawSet ×ˢ positiveHalfSet =
        (endpointRawSet ×ˢ lowerRawSet) ∪
          (endpointRawSet ×ˢ endpointRawSet) by
      rw [positiveHalfSet_eq_lower_union_endpoint, prod_union]]
    exact setIntegral_union
      (lowerRawSet_disjoint_endpointRawSet.set_prod_right
        endpointRawSet endpointRawSet)
      (hBmeas.prod hBmeas) hBA hBB
  have hcross :
      (∫ p : ℝ × ℝ in lowerRawSet ×ˢ endpointRawSet, K p
        ∂((volume : Measure ℝ).prod volume)) =
      ∫ p : ℝ × ℝ in endpointRawSet ×ˢ lowerRawSet, K p
        ∂((volume : Measure ℝ).prod volume) := by
    have hswap := MeasureTheory.setIntegral_prod_swap
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      endpointRawSet lowerRawSet K
    calc
      (∫ p : ℝ × ℝ in lowerRawSet ×ˢ endpointRawSet, K p
          ∂((volume : Measure ℝ).prod volume)) =
        ∫ p : ℝ × ℝ in lowerRawSet ×ˢ endpointRawSet, K p.swap
          ∂((volume : Measure ℝ).prod volume) := by
            apply setIntegral_congr_fun (hAmeas.prod hBmeas)
            intro p _hp
            exact (hsymm p).symm
      _ = _ := hswap
  rw [houter, hleft, hright, hcross]
  ring

/-- The reflected odd raw density is genuinely product-integrable on the
closed positive square. -/
theorem integrableOn_reflectedRawKernel_of_lipschitzOnWith_odd
    {C : NNReal} (w : ℝ → ℝ) (hw : Continuous w)
    (hC : LipschitzOnWith C w (Icc (-1 : ℝ) 1))
    (hodd : Function.Odd w) :
    IntegrableOn
      (fun p : ℝ × ℝ ↦ (w p.1 + w p.2) ^ 2 / (p.1 + p.2))
      (positiveHalfSet ×ˢ positiveHalfSet)
      ((volume : Measure ℝ).prod volume) := by
  let P : Set (ℝ × ℝ) := positiveHalfSet ×ˢ positiveHalfSet
  let J : ℝ × ℝ → ℝ := fun p ↦
    (w p.1 + w p.2) ^ 2 / (p.1 + p.2)
  let D : ℝ × ℝ → ℝ := fun p ↦
    (C : ℝ) ^ 2 * (p.1 + p.2)
  have hw0 : w 0 = 0 := by
    have h := hodd 0
    norm_num at h ⊢
    linarith
  have hD : IntegrableOn D P ((volume : Measure ℝ).prod volume) := by
    exact (by fun_prop : Continuous D).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have hJmeas : AEStronglyMeasurable J
      (((volume : Measure ℝ).prod volume).restrict P) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [J]
    exact (((hw.measurable.comp measurable_fst).add
      (hw.measurable.comp measurable_snd)).pow_const 2).div
        (measurable_fst.add measurable_snd)
  have hdom : ∀ᵐ p ∂(((volume : Measure ℝ).prod volume).restrict P),
      ‖J p‖ ≤ D p := by
    filter_upwards [ae_restrict_mem
      (measurableSet_Icc.prod measurableSet_Icc)] with p hp
    have hxmem : p.1 ∈ Icc (-1 : ℝ) 1 :=
      ⟨by linarith [hp.1.1], hp.1.2⟩
    have hymem : p.2 ∈ Icc (-1 : ℝ) 1 :=
      ⟨by linarith [hp.2.1], hp.2.2⟩
    have hzero : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
    have hxbound : |w p.1| ≤ (C : ℝ) * p.1 := by
      have h := hC.dist_le_mul p.1 hxmem 0 hzero
      rw [Real.dist_eq, Real.dist_eq, hw0, sub_zero, sub_zero,
        abs_of_nonneg hp.1.1] at h
      exact h
    have hybound : |w p.2| ≤ (C : ℝ) * p.2 := by
      have h := hC.dist_le_mul p.2 hymem 0 hzero
      rw [Real.dist_eq, Real.dist_eq, hw0, sub_zero, sub_zero,
        abs_of_nonneg hp.2.1] at h
      exact h
    have hsum0 : 0 ≤ p.1 + p.2 := add_nonneg hp.1.1 hp.2.1
    have habs : |w p.1 + w p.2| ≤ (C : ℝ) * (p.1 + p.2) := by
      calc
        |w p.1 + w p.2| ≤ |w p.1| + |w p.2| := abs_add_le _ _
        _ ≤ (C : ℝ) * p.1 + (C : ℝ) * p.2 :=
          add_le_add hxbound hybound
        _ = (C : ℝ) * (p.1 + p.2) := by ring
    dsimp only [J, D]
    rw [Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (sq_nonneg _) hsum0)]
    by_cases hsum : p.1 + p.2 = 0
    · have hx0 : p.1 = 0 := by linarith [hp.1.1, hp.2.1]
      have hy0 : p.2 = 0 := by linarith [hp.1.1, hp.2.1]
      simp [hx0, hy0, hw0]
    · have hsumPos : 0 < p.1 + p.2 :=
        lt_of_le_of_ne hsum0 (Ne.symm hsum)
      rw [div_le_iff₀ hsumPos]
      have hright0 : 0 ≤ (C : ℝ) * (p.1 + p.2) :=
        mul_nonneg C.property hsum0
      have hsq :=
        (sq_le_sq₀ (abs_nonneg (w p.1 + w p.2)) hright0).2 habs
      rw [sq_abs, mul_pow] at hsq
      nlinarith
  simpa only [P, J] using hD.mono' hJmeas hdom

/-- Product integrability of the coupled same/reflected raw density. -/
theorem integrableOn_fourCellOddCoupledRawPair
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w)
    (hodd : Function.Odd w) :
    IntegrableOn (fourCellOddCoupledRawPair w)
      (positiveHalfSet ×ˢ positiveHalfSet)
      ((volume : Measure ℝ).prod volume) := by
  have hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w :=
    hw.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  obtain ⟨C, hC⟩ := hlocal.exists_lipschitzOnWith_of_compact isCompact_Icc
  have hsameFull :=
    integrableOn_centeredLogDifferenceKernel_prod_of_lipschitzOnWith w hC
  have hsub : positiveHalfSet ⊆ Icc (-1 : ℝ) 1 := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  have hsame : IntegrableOn
      (fun p : ℝ × ℝ ↦ centeredLogDifferenceKernel w p.1 p.2)
      (positiveHalfSet ×ˢ positiveHalfSet)
      ((volume : Measure ℝ).prod volume) :=
    hsameFull.mono_set (Set.prod_mono hsub hsub)
  have hreflected :=
    integrableOn_reflectedRawKernel_of_lipschitzOnWith_odd
      w hw.continuous hC hodd
  apply hsame.add hreflected |>.congr
  filter_upwards [ae_restrict_mem
    (measurableSet_Icc.prod measurableSet_Icc)] with p hp
  unfold fourCellOddCoupledRawPair centeredLogDifferenceKernel
  rfl

/-- Reflected-plus raw energy on the endpoint square, in product-set form. -/
def endpointReflectedRawSetIntegral (w : ℝ → ℝ) : ℝ :=
  ∫ p : ℝ × ℝ in endpointRawSet ×ˢ endpointRawSet,
    (w p.1 + w p.2) ^ 2 / (p.1 + p.2)
      ∂((volume : Measure ℝ).prod volume)

/-- Exact `A/B` partition of the raw form after removing the endpoint
same-sign square.  Unlike the older budget lemma, this is an equality and
retains the entire endpoint reflected-plus block. -/
theorem fullRaw_sub_endpointRaw_eq_partition
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w)
    (hodd : Function.Odd w) :
    fourCellPositiveHalfRawSameSignEnergy w +
        fourCellPositiveHalfRawReflectedEnergy w (-1) -
        fourCellOddEndpointStripRawEnergy w =
      (∫ p : ℝ × ℝ in lowerRawSet ×ˢ lowerRawSet,
        fourCellOddCoupledRawPair w p
          ∂((volume : Measure ℝ).prod volume)) +
      2 * (∫ p : ℝ × ℝ in endpointRawSet ×ˢ lowerRawSet,
        fourCellOddCoupledRawPair w p
          ∂((volume : Measure ℝ).prod volume)) +
      endpointReflectedRawSetIntegral w := by
  let S : ℝ × ℝ → ℝ := fun p ↦
    centeredLogDifferenceKernel w p.1 p.2
  let J : ℝ × ℝ → ℝ := fun p ↦
    (w p.1 + w p.2) ^ 2 / (p.1 + p.2)
  let K : ℝ × ℝ → ℝ := fun p ↦ S p + J p
  have hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w :=
    hw.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  obtain ⟨C, hC⟩ := hlocal.exists_lipschitzOnWith_of_compact isCompact_Icc
  have hsameFull :=
    integrableOn_centeredLogDifferenceKernel_prod_of_lipschitzOnWith w hC
  have hUsub : positiveHalfSet ⊆ Icc (-1 : ℝ) 1 := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  have hS : IntegrableOn S (positiveHalfSet ×ˢ positiveHalfSet)
      ((volume : Measure ℝ).prod volume) := by
    simpa only [S] using
      hsameFull.mono_set (Set.prod_mono hUsub hUsub)
  have hJ : IntegrableOn J (positiveHalfSet ×ˢ positiveHalfSet)
      ((volume : Measure ℝ).prod volume) := by
    simpa only [J] using
      integrableOn_reflectedRawKernel_of_lipschitzOnWith_odd
        w hw.continuous hC hodd
  have hK : IntegrableOn K (positiveHalfSet ×ˢ positiveHalfSet)
      ((volume : Measure ℝ).prod volume) := hS.add hJ
  have hKdef : K = fourCellOddCoupledRawPair w := by
    funext p
    dsimp only [K, S, J]
    unfold fourCellOddCoupledRawPair centeredLogDifferenceKernel
    rfl
  have hsymm : ∀ p : ℝ × ℝ, K p.swap = K p := by
    intro p
    rcases p with ⟨x, y⟩
    dsimp only [K, S, J, Prod.swap_prod_mk]
    unfold centeredLogDifferenceKernel
    rw [show y - x = -(x - y) by ring, abs_neg]
    ring
  have hpartition :=
    setIntegral_positiveHalfSquare_eq_lower_cross_endpoint K hK hsymm
  have hSiter := intervalIntegral_integral_eq_setIntegral_square
    S 0 1 (by norm_num) hS
  have hJiter := intervalIntegral_integral_eq_setIntegral_square
    J 0 1 (by norm_num) hJ
  have hfull :
      (∫ p : ℝ × ℝ in positiveHalfSet ×ˢ positiveHalfSet, K p
        ∂((volume : Measure ℝ).prod volume)) =
      fourCellPositiveHalfRawSameSignEnergy w +
        fourCellPositiveHalfRawReflectedEnergy w (-1) := by
    rw [show (∫ p : ℝ × ℝ in positiveHalfSet ×ˢ positiveHalfSet,
        K p ∂((volume : Measure ℝ).prod volume)) =
      (∫ p : ℝ × ℝ in positiveHalfSet ×ˢ positiveHalfSet,
        S p ∂((volume : Measure ℝ).prod volume)) +
      ∫ p : ℝ × ℝ in positiveHalfSet ×ˢ positiveHalfSet,
        J p ∂((volume : Measure ℝ).prod volume) by
      exact integral_add hS hJ]
    unfold fourCellPositiveHalfRawSameSignEnergy
      fourCellPositiveHalfRawReflectedEnergy
    simp only [neg_mul, one_mul, sub_neg_eq_add]
    dsimp only [positiveHalfSet, S, J] at hSiter hJiter ⊢
    unfold centeredLogDifferenceKernel at hSiter ⊢
    exact congrArg₂ (fun a b : ℝ ↦ a + b) hSiter.symm hJiter.symm
  have hBsub : endpointRawSet ⊆ positiveHalfSet := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  have hSBB := hS.mono_set (Set.prod_mono hBsub hBsub)
  have hSBBiter := intervalIntegral_integral_eq_setIntegral_square
    S (3 / 5) 1 (by norm_num) hSBB
  have hendpointSame :
      (∫ p : ℝ × ℝ in endpointRawSet ×ˢ endpointRawSet, S p
        ∂((volume : Measure ℝ).prod volume)) =
      fourCellOddEndpointStripRawEnergy w := by
    rw [fourCellOddEndpointStripRawEnergy_eq_physicalSquare]
    dsimp only [endpointRawSet, S] at hSBBiter ⊢
    unfold centeredLogDifferenceKernel at hSBBiter
    exact hSBBiter.symm
  have hBBsplit :
      (∫ p : ℝ × ℝ in endpointRawSet ×ˢ endpointRawSet, K p
        ∂((volume : Measure ℝ).prod volume)) =
      fourCellOddEndpointStripRawEnergy w +
        endpointReflectedRawSetIntegral w := by
    rw [show (∫ p : ℝ × ℝ in endpointRawSet ×ˢ endpointRawSet,
        K p ∂((volume : Measure ℝ).prod volume)) =
      (∫ p : ℝ × ℝ in endpointRawSet ×ˢ endpointRawSet,
        S p ∂((volume : Measure ℝ).prod volume)) +
      ∫ p : ℝ × ℝ in endpointRawSet ×ˢ endpointRawSet,
        J p ∂((volume : Measure ℝ).prod volume) by
      exact integral_add
        (hS.mono_set (Set.prod_mono hBsub hBsub))
        (hJ.mono_set (Set.prod_mono hBsub hBsub))]
    rw [hendpointSame]
    rfl
  rw [hfull, hBBsplit] at hpartition
  rw [hKdef] at hpartition
  linarith

/-- Exact raw-cancellation reserve after the strip parity split and the
`A/B` partition. -/
theorem rawStripCancellationReserve_eq_partition
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w)
    (hodd : Function.Odd w) :
    fourCellOddRawStripCancellationReserve w =
      (1 / 2 : ℝ) *
        (∫ p : ℝ × ℝ in lowerRawSet ×ˢ lowerRawSet,
          fourCellOddCoupledRawPair w p
            ∂((volume : Measure ℝ).prod volume)) +
      (∫ p : ℝ × ℝ in endpointRawSet ×ˢ lowerRawSet,
        fourCellOddCoupledRawPair w p
          ∂((volume : Measure ℝ).prod volume)) +
      (1 / 2 : ℝ) * endpointReflectedRawSetIntegral w +
      (1 / 2 : ℝ) * fourCellOddEndpointStripEvenRawEnergy w := by
  have hpartition := fullRaw_sub_endpointRaw_eq_partition w hw hodd
  have hstrip := fourCellOddEndpointStrip_rawEnergy_eq_even_add_odd w hw
  unfold fourCellOddRawStripCancellationReserve
  rw [show fourCellOddEndpointStripOddRawEnergy w =
      fourCellOddEndpointStripRawEnergy w -
        fourCellOddEndpointStripEvenRawEnergy w by linarith]
  linarith

/-! ## Profile-parameterized integral raw Picone block -/

/-- Positivity data needed for the integral block transform.  It is stated
for a general prospective ground profile so an exact inverse-defined
Galerkin ground can replace the current rational profile without changing
the integral algebra. -/
structure BlockPiconeGroundSigns (phi : ℝ → ℝ) : Prop where
  positiveHalf : ∀ x ∈ positiveHalfSet, 0 < phi x
  stripEven : ∀ z ∈ Icc (-1 : ℝ) 1,
    0 < fourCellOddEndpointStripEven phi z

def rawPiconeSquareIntegrand
    (phi w : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  phi p.1 * phi p.2 *
    (positiveHalfSameReserveWeight p.1 p.2 *
        (w p.1 / phi p.1 - w p.2 / phi p.2) ^ 2 +
      positiveHalfReflectedReserveWeight p.1 p.2 *
        (w p.1 / phi p.1 + w p.2 / phi p.2) ^ 2)

def rawPiconeRowIntegrand
    (phi w : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (positiveHalfSameReserveWeight p.1 p.2 +
      positiveHalfReflectedReserveWeight p.1 p.2) *
    (phi p.1 - phi p.2) *
      (w p.1 ^ 2 / phi p.1 - w p.2 ^ 2 / phi p.2)

theorem fourCellOddCoupledRawPair_eq_picone
    {phi w : ℝ → ℝ} {p : ℝ × ℝ}
    (hphiX : phi p.1 ≠ 0) (hphiY : phi p.2 ≠ 0) :
    fourCellOddCoupledRawPair w p =
      2 * (rawPiconeSquareIntegrand phi w p +
        rawPiconeRowIntegrand phi w p) := by
  have hpicone := picone_two_channel_identity
    (kSub := positiveHalfSameReserveWeight p.1 p.2)
    (kAdd := positiveHalfReflectedReserveWeight p.1 p.2)
    (phiX := phi p.1) (phiY := phi p.2)
    (wX := w p.1) (wY := w p.2) hphiX hphiY
  unfold fourCellOddCoupledRawPair rawPiconeSquareIntegrand
    rawPiconeRowIntegrand
  unfold positiveHalfSameReserveWeight
    positiveHalfReflectedReserveWeight at hpicone ⊢
  by_cases hdiff : |p.1 - p.2| = 0 <;>
    by_cases hsum : p.1 + p.2 = 0 <;>
    simp only [hdiff, hsum, mul_zero, inv_zero, zero_mul,
      one_div] at hpicone ⊢
  all_goals
    field_simp [hdiff, hsum] at hpicone ⊢
    linear_combination 2 * hpicone

def endpointEvenPiconeWeight (z s : ℝ) : ℝ :=
  1 / (10 * |z - s|)

def endpointEvenPiconeSquareIntegrand
    (phi w : ℝ → ℝ) (z s : ℝ) : ℝ :=
  endpointEvenPiconeWeight z s *
    fourCellOddEndpointStripEven phi z *
    fourCellOddEndpointStripEven phi s *
      (fourCellOddEndpointStripEven w z /
          fourCellOddEndpointStripEven phi z -
        fourCellOddEndpointStripEven w s /
          fourCellOddEndpointStripEven phi s) ^ 2

def endpointEvenPiconeRowIntegrand
    (phi w : ℝ → ℝ) (z s : ℝ) : ℝ :=
  endpointEvenPiconeWeight z s *
    (fourCellOddEndpointStripEven phi z -
      fourCellOddEndpointStripEven phi s) *
      (fourCellOddEndpointStripEven w z ^ 2 /
          fourCellOddEndpointStripEven phi z -
        fourCellOddEndpointStripEven w s ^ 2 /
          fourCellOddEndpointStripEven phi s)

theorem endpointEvenHalfRawIntegrand_eq_picone
    {phi w : ℝ → ℝ} {z s : ℝ}
    (hphiZ : fourCellOddEndpointStripEven phi z ≠ 0)
    (hphiS : fourCellOddEndpointStripEven phi s ≠ 0) :
    (1 / 10 : ℝ) *
        ((fourCellOddEndpointStripEven w z -
          fourCellOddEndpointStripEven w s) ^ 2 / |z - s|) =
      endpointEvenPiconeSquareIntegrand phi w z s +
        endpointEvenPiconeRowIntegrand phi w z s := by
  have hpicone := picone_sub_sq_identity
    (phiX := fourCellOddEndpointStripEven phi z)
    (phiY := fourCellOddEndpointStripEven phi s)
    (wX := fourCellOddEndpointStripEven w z)
    (wY := fourCellOddEndpointStripEven w s) hphiZ hphiS
  unfold endpointEvenPiconeSquareIntegrand
    endpointEvenPiconeRowIntegrand endpointEvenPiconeWeight
  rw [hpicone]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

def endpointReflectedPiconeSquareIntegrand
    (phi w : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  positiveHalfReflectedReserveWeight p.1 p.2 * phi p.1 * phi p.2 *
    (w p.1 / phi p.1 + w p.2 / phi p.2) ^ 2

def endpointReflectedPiconeRowIntegrand
    (phi w : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  positiveHalfReflectedReserveWeight p.1 p.2 *
    (phi p.1 - phi p.2) *
      (w p.1 ^ 2 / phi p.1 - w p.2 ^ 2 / phi p.2)

theorem endpointReflectedHalfRawIntegrand_eq_picone
    {phi w : ℝ → ℝ} {p : ℝ × ℝ}
    (hphiX : phi p.1 ≠ 0) (hphiY : phi p.2 ≠ 0) :
    (1 / 2 : ℝ) * ((w p.1 + w p.2) ^ 2 / (p.1 + p.2)) =
      endpointReflectedPiconeSquareIntegrand phi w p +
        endpointReflectedPiconeRowIntegrand phi w p := by
  have hpicone := picone_add_sq_identity
    (phiX := phi p.1) (phiY := phi p.2)
    (wX := w p.1) (wY := w p.2) hphiX hphiY
  unfold endpointReflectedPiconeSquareIntegrand
    endpointReflectedPiconeRowIntegrand
    positiveHalfReflectedReserveWeight
  rw [hpicone]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Exact transformed raw block before separating quotient squares from the
signed row. -/
def integratedRawBlockPicone
    (phi w : ℝ → ℝ) : ℝ :=
  (∫ p : ℝ × ℝ in lowerRawSet ×ˢ lowerRawSet,
      (rawPiconeSquareIntegrand phi w p +
        rawPiconeRowIntegrand phi w p)
        ∂((volume : Measure ℝ).prod volume)) +
    2 * (∫ p : ℝ × ℝ in endpointRawSet ×ˢ lowerRawSet,
      (rawPiconeSquareIntegrand phi w p +
        rawPiconeRowIntegrand phi w p)
        ∂((volume : Measure ℝ).prod volume)) +
    (∫ p : ℝ × ℝ in endpointRawSet ×ˢ endpointRawSet,
      (endpointReflectedPiconeSquareIntegrand phi w p +
        endpointReflectedPiconeRowIntegrand phi w p)
        ∂((volume : Measure ℝ).prod volume)) +
    (∫ z : ℝ in -1..1, ∫ s : ℝ in -1..1,
      endpointEvenPiconeSquareIntegrand phi w z s +
        endpointEvenPiconeRowIntegrand phi w z s)

theorem rawStripCancellationReserve_eq_integratedRawBlockPicone
    (phi w : ℝ → ℝ) (hw : ContDiff ℝ 1 w)
    (hodd : Function.Odd w) (hphi : BlockPiconeGroundSigns phi) :
    fourCellOddRawStripCancellationReserve w =
      integratedRawBlockPicone phi w := by
  rw [rawStripCancellationReserve_eq_partition w hw hodd]
  have hAA :
      (∫ p : ℝ × ℝ in lowerRawSet ×ˢ lowerRawSet,
        fourCellOddCoupledRawPair w p
          ∂((volume : Measure ℝ).prod volume)) =
      2 * (∫ p : ℝ × ℝ in lowerRawSet ×ˢ lowerRawSet,
        (rawPiconeSquareIntegrand phi w p +
          rawPiconeRowIntegrand phi w p)
          ∂((volume : Measure ℝ).prod volume)) := by
    calc
      _ = ∫ p : ℝ × ℝ in lowerRawSet ×ˢ lowerRawSet,
          2 * (rawPiconeSquareIntegrand phi w p +
            rawPiconeRowIntegrand phi w p)
            ∂((volume : Measure ℝ).prod volume) := by
        apply setIntegral_congr_fun (measurableSet_Ico.prod measurableSet_Ico)
        intro p hp
        apply fourCellOddCoupledRawPair_eq_picone
        · exact (hphi.positiveHalf p.1
            ⟨hp.1.1, hp.1.2.le.trans (by norm_num)⟩).ne'
        · exact (hphi.positiveHalf p.2
            ⟨hp.2.1, hp.2.2.le.trans (by norm_num)⟩).ne'
      _ = _ := by rw [integral_const_mul]
  have hBA :
      (∫ p : ℝ × ℝ in endpointRawSet ×ˢ lowerRawSet,
        fourCellOddCoupledRawPair w p
          ∂((volume : Measure ℝ).prod volume)) =
      2 * (∫ p : ℝ × ℝ in endpointRawSet ×ˢ lowerRawSet,
        (rawPiconeSquareIntegrand phi w p +
          rawPiconeRowIntegrand phi w p)
          ∂((volume : Measure ℝ).prod volume)) := by
    calc
      _ = ∫ p : ℝ × ℝ in endpointRawSet ×ˢ lowerRawSet,
          2 * (rawPiconeSquareIntegrand phi w p +
            rawPiconeRowIntegrand phi w p)
            ∂((volume : Measure ℝ).prod volume) := by
        apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Ico)
        intro p hp
        apply fourCellOddCoupledRawPair_eq_picone
        · exact (hphi.positiveHalf p.1
            ⟨by linarith [hp.1.1], hp.1.2⟩).ne'
        · exact (hphi.positiveHalf p.2
            ⟨hp.2.1, hp.2.2.le.trans (by norm_num)⟩).ne'
      _ = _ := by rw [integral_const_mul]
  have hBB : (1 / 2 : ℝ) * endpointReflectedRawSetIntegral w =
      ∫ p : ℝ × ℝ in endpointRawSet ×ˢ endpointRawSet,
        (endpointReflectedPiconeSquareIntegrand phi w p +
          endpointReflectedPiconeRowIntegrand phi w p)
          ∂((volume : Measure ℝ).prod volume) := by
    unfold endpointReflectedRawSetIntegral
    rw [← integral_const_mul]
    apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
    intro p hp
    apply endpointReflectedHalfRawIntegrand_eq_picone
    · exact (hphi.positiveHalf p.1
        ⟨by linarith [hp.1.1], hp.1.2⟩).ne'
    · exact (hphi.positiveHalf p.2
        ⟨by linarith [hp.2.1], hp.2.2⟩).ne'
  have hEven : (1 / 2 : ℝ) *
      fourCellOddEndpointStripEvenRawEnergy w =
      ∫ z : ℝ in -1..1, ∫ s : ℝ in -1..1,
        endpointEvenPiconeSquareIntegrand phi w z s +
          endpointEvenPiconeRowIntegrand phi w z s := by
    unfold fourCellOddEndpointStripEvenRawEnergy centeredRawLogEnergy
    rw [show (1 / 2 : ℝ) * (1 / 5 *
        (∫ z : ℝ in -1..1, ∫ s : ℝ in -1..1,
          (fourCellOddEndpointStripEven w z -
            fourCellOddEndpointStripEven w s) ^ 2 / |z - s|)) =
        (1 / 10 : ℝ) *
          (∫ z : ℝ in -1..1, ∫ s : ℝ in -1..1,
            (fourCellOddEndpointStripEven w z -
              fourCellOddEndpointStripEven w s) ^ 2 / |z - s|) by ring,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro z hz
    change (1 / 10 : ℝ) *
        (∫ s : ℝ in -1..1,
          (fourCellOddEndpointStripEven w z -
            fourCellOddEndpointStripEven w s) ^ 2 / |z - s|) =
      ∫ s : ℝ in -1..1,
        endpointEvenPiconeSquareIntegrand phi w z s +
          endpointEvenPiconeRowIntegrand phi w z s
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    have hzIcc : z ∈ Icc (-1 : ℝ) 1 := by
      simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hz
    have hsIcc : s ∈ Icc (-1 : ℝ) 1 := by
      simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hs
    apply endpointEvenHalfRawIntegrand_eq_picone
    · exact (hphi.stripEven z hzIcc).ne'
    · exact (hphi.stripEven s hsIcc).ne'
  rw [hAA, hBA, hBB, hEven]
  unfold integratedRawBlockPicone
  ring

/-! ## Integral folded-regular Picone block -/

private theorem fourCellOperatorHalfWidth_nonneg :
    0 ≤ fourCellOperatorHalfWidth := by
  unfold fourCellOperatorHalfWidth
  positivity

private theorem fourCellOperatorHalfWidth_le_log_three_div_two :
    fourCellOperatorHalfWidth ≤ Real.log 3 / 2 := by
  have h := five_mul_log_two_div_four_lt_log_three
  unfold fourCellOperatorHalfWidth
  linarith

/-- Bounded regular kernels times continuous densities are integrable on
the positive square. -/
theorem integrableOn_regularKernel_mul_continuous
    (distance psi : ℝ × ℝ → ℝ) (hpsi : Continuous psi)
    (hdistance : Measurable distance)
    (hdistanceRange : ∀ p ∈ positiveHalfSet ×ˢ positiveHalfSet,
      0 ≤ distance p ∧ distance p ≤ 2) :
    IntegrableOn
      (fun p ↦ yoshidaRegularKernel
          (fourCellOperatorHalfWidth * distance p) * psi p)
      (positiveHalfSet ×ˢ positiveHalfSet)
      ((volume : Measure ℝ).prod volume) := by
  let K : ℝ × ℝ → ℝ := fun p ↦ yoshidaRegularKernel
    (fourCellOperatorHalfWidth * distance p) * psi p
  let g : ℝ × ℝ → ℝ := fun p ↦ (1 / 4 : ℝ) * |psi p|
  have hKMeas : Measurable K := by
    dsimp only [K]
    exact (measurable_yoshidaRegularKernel.comp
      (measurable_const.mul hdistance)).mul hpsi.measurable
  have hg : IntegrableOn g (positiveHalfSet ×ˢ positiveHalfSet)
      ((volume : Measure ℝ).prod volume) := by
    apply ContinuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
    exact (continuous_const.mul hpsi.abs).continuousOn
  apply hg.mono'
  · exact hKMeas.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem
        (measurableSet_Icc.prod measurableSet_Icc)] with p hp
    have hd := hdistanceRange p hp
    have harg0 : 0 ≤ fourCellOperatorHalfWidth * distance p :=
      mul_nonneg fourCellOperatorHalfWidth_nonneg hd.1
    have harg3 : fourCellOperatorHalfWidth * distance p ≤ Real.log 3 := by
      have had := mul_le_mul_of_nonneg_left hd.2
        fourCellOperatorHalfWidth_nonneg
      linarith [fourCellOperatorHalfWidth_le_log_three_div_two]
    have hnonneg :=
      yoshidaRegularKernel_nonneg_of_le_log_three harg0 harg3
    have hupper := yoshidaRegularKernel_le_quarter harg0
    dsimp only [K, g]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnonneg]
    exact mul_le_mul_of_nonneg_right hupper (abs_nonneg (psi p))

def foldedRegularOriginalIntegrand
    (w : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  -2 * fourCellOperatorHalfWidth *
    fourCellOddFoldedRegularDifferenceKernel p.1 p.2 * w p.1 * w p.2

/-- Exact odd parity fold of the signed regular correlation into the
positive-square difference kernel. -/
theorem neg_regularCorrelation_eq_foldedRegularSetIntegral
    (w : ℝ → ℝ) (hw : Continuous w) (hodd : Function.Odd w) :
    -2 * fourCellOperatorHalfWidth *
        (∫ t : ℝ in 0..2,
          yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
            centeredEndpointCorrelation w t) =
      ∫ p : ℝ × ℝ in positiveHalfSet ×ˢ positiveHalfSet,
        foldedRegularOriginalIntegrand w p
          ∂((volume : Measure ℝ).prod volume) := by
  let D : ℝ × ℝ → ℝ := fun p ↦
    yoshidaRegularKernel
      (fourCellOperatorHalfWidth * |p.1 - p.2|)
  let R : ℝ × ℝ → ℝ := fun p ↦
    yoshidaRegularKernel
      (fourCellOperatorHalfWidth * (p.1 + p.2))
  let A : ℝ × ℝ → ℝ := fun p ↦
    D p * (w p.1 - w p.2) ^ 2
  let B : ℝ × ℝ → ℝ := fun p ↦
    R p * (w p.1 + w p.2) ^ 2
  let M : ℝ × ℝ → ℝ := fun p ↦
    (D p + R p) * ((w p.1 ^ 2 + w p.2 ^ 2) / 2)
  let H : ℝ × ℝ → ℝ := fun p ↦
    foldedRegularOriginalIntegrand w p
  have hdiffMeas : Measurable (fun p : ℝ × ℝ ↦ |p.1 - p.2|) :=
    (measurable_fst.sub measurable_snd).abs
  have hsumMeas : Measurable (fun p : ℝ × ℝ ↦ p.1 + p.2) :=
    measurable_fst.add measurable_snd
  have hdiffRange : ∀ p ∈ positiveHalfSet ×ˢ positiveHalfSet,
      0 ≤ |p.1 - p.2| ∧ |p.1 - p.2| ≤ 2 := by
    intro p hp
    constructor
    · exact abs_nonneg _
    · rw [abs_le]
      constructor <;> linarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]
  have hsumRange : ∀ p ∈ positiveHalfSet ×ˢ positiveHalfSet,
      0 ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ 2 := by
    intro p hp
    constructor <;> linarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]
  have hA : IntegrableOn A (positiveHalfSet ×ˢ positiveHalfSet)
      ((volume : Measure ℝ).prod volume) := by
    simpa only [A, D] using integrableOn_regularKernel_mul_continuous
      (fun p : ℝ × ℝ ↦ |p.1 - p.2|)
      (fun p ↦ (w p.1 - w p.2) ^ 2)
      (by fun_prop) hdiffMeas hdiffRange
  have hB : IntegrableOn B (positiveHalfSet ×ˢ positiveHalfSet)
      ((volume : Measure ℝ).prod volume) := by
    simpa only [B, R] using integrableOn_regularKernel_mul_continuous
      (fun p : ℝ × ℝ ↦ p.1 + p.2)
      (fun p ↦ (w p.1 + w p.2) ^ 2)
      (by fun_prop) hsumMeas hsumRange
  have hDmass : IntegrableOn
      (fun p ↦ D p * ((w p.1 ^ 2 + w p.2 ^ 2) / 2))
      (positiveHalfSet ×ˢ positiveHalfSet)
      ((volume : Measure ℝ).prod volume) := by
    simpa only [D] using integrableOn_regularKernel_mul_continuous
      (fun p : ℝ × ℝ ↦ |p.1 - p.2|)
      (fun p ↦ (w p.1 ^ 2 + w p.2 ^ 2) / 2)
      (by fun_prop) hdiffMeas hdiffRange
  have hRmass : IntegrableOn
      (fun p ↦ R p * ((w p.1 ^ 2 + w p.2 ^ 2) / 2))
      (positiveHalfSet ×ˢ positiveHalfSet)
      ((volume : Measure ℝ).prod volume) := by
    simpa only [R] using integrableOn_regularKernel_mul_continuous
      (fun p : ℝ × ℝ ↦ p.1 + p.2)
      (fun p ↦ (w p.1 ^ 2 + w p.2 ^ 2) / 2)
      (by fun_prop) hsumMeas hsumRange
  have hM : IntegrableOn M (positiveHalfSet ×ˢ positiveHalfSet)
      ((volume : Measure ℝ).prod volume) := by
    have hadd := hDmass.add hRmass
    apply hadd.congr_fun _
      (measurableSet_Icc.prod measurableSet_Icc)
    intro p _hp
    change D p * ((w p.1 ^ 2 + w p.2 ^ 2) / 2) +
      R p * ((w p.1 ^ 2 + w p.2 ^ 2) / 2) = M p
    dsimp only [M]
    ring
  have hcompletion :=
    neg_two_mul_regularCorrelation_eq_positiveHalfCompletion_odd
      w hw hodd fourCellOperatorHalfWidth
      fourCellOperatorHalfWidth_nonneg
      fourCellOperatorHalfWidth_le_log_three_div_two
  rw [hcompletion]
  unfold fourCellPositiveHalfRegularSameSignSquare
    fourCellPositiveHalfRegularReflectedSquare
    fourCellPositiveHalfRegularRowMass
  dsimp only [positiveHalfSet, A, B, M] at hA hB hM
  have hpoint (p : ℝ × ℝ) :
      fourCellOperatorHalfWidth * (A p + B p) -
          2 * fourCellOperatorHalfWidth * M p = H p := by
    dsimp only [A, B, M, H, D, R, foldedRegularOriginalIntegrand,
      fourCellOddFoldedRegularDifferenceKernel]
    ring
  have hAB : IntegrableOn (fun p ↦ A p + B p)
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
      ((volume : Measure ℝ).prod volume) := hA.add hB
  have hleft :
      fourCellOperatorHalfWidth *
          ((∫ p : ℝ × ℝ in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
              A p ∂((volume : Measure ℝ).prod volume)) +
            ∫ p : ℝ × ℝ in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
              B p ∂((volume : Measure ℝ).prod volume)) -
          2 * fourCellOperatorHalfWidth *
            ∫ p : ℝ × ℝ in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
              M p ∂((volume : Measure ℝ).prod volume) =
        ∫ p : ℝ × ℝ in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
          (fourCellOperatorHalfWidth * (A p + B p) -
            2 * fourCellOperatorHalfWidth * M p)
            ∂((volume : Measure ℝ).prod volume) := by
    rw [integral_sub (hAB.const_mul fourCellOperatorHalfWidth)
        (hM.const_mul (2 * fourCellOperatorHalfWidth)),
      integral_const_mul, integral_const_mul,
      integral_add hA hB]
  unfold positiveHalfSet
  simp only [neg_one_mul, sub_neg_eq_add]
  change fourCellOperatorHalfWidth *
      ((∫ p : ℝ × ℝ in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
          A p ∂((volume : Measure ℝ).prod volume)) +
        ∫ p : ℝ × ℝ in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
          B p ∂((volume : Measure ℝ).prod volume)) -
      2 * fourCellOperatorHalfWidth *
        ∫ p : ℝ × ℝ in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
          M p ∂((volume : Measure ℝ).prod volume) =
    ∫ p : ℝ × ℝ in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      H p ∂((volume : Measure ℝ).prod volume)
  rw [hleft]
  apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
  intro p _hp
  exact hpoint p

def regularPiconeSquareIntegrand
    (phi w : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  fourCellOperatorHalfWidth *
    fourCellOddFoldedRegularDifferenceKernel p.1 p.2 *
    phi p.1 * phi p.2 *
      (w p.1 / phi p.1 - w p.2 / phi p.2) ^ 2

def regularPiconeRowIntegrand
    (phi w : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  fourCellOperatorHalfWidth *
      fourCellOddFoldedRegularDifferenceKernel p.1 p.2 *
    (phi p.1 - phi p.2) *
      (w p.1 ^ 2 / phi p.1 - w p.2 ^ 2 / phi p.2) -
    fourCellOperatorHalfWidth *
      fourCellOddFoldedRegularDifferenceKernel p.1 p.2 * w p.1 ^ 2 -
    fourCellOperatorHalfWidth *
      fourCellOddFoldedRegularDifferenceKernel p.1 p.2 * w p.2 ^ 2

theorem foldedRegularOriginalIntegrand_eq_picone
    {phi w : ℝ → ℝ} {p : ℝ × ℝ}
    (hphiX : phi p.1 ≠ 0) (hphiY : phi p.2 ≠ 0) :
    foldedRegularOriginalIntegrand w p =
      regularPiconeSquareIntegrand phi w p +
        regularPiconeRowIntegrand phi w p := by
  simpa only [foldedRegularOriginalIntegrand,
    regularPiconeSquareIntegrand, regularPiconeRowIntegrand] using
    (show -2 * fourCellOperatorHalfWidth *
          fourCellOddFoldedRegularDifferenceKernel p.1 p.2 * w p.1 * w p.2 =
        fourCellOperatorHalfWidth *
            fourCellOddFoldedRegularDifferenceKernel p.1 p.2 *
            phi p.1 * phi p.2 *
              (w p.1 / phi p.1 - w p.2 / phi p.2) ^ 2 +
          (fourCellOperatorHalfWidth *
              fourCellOddFoldedRegularDifferenceKernel p.1 p.2 *
            (phi p.1 - phi p.2) *
              (w p.1 ^ 2 / phi p.1 - w p.2 ^ 2 / phi p.2) -
            fourCellOperatorHalfWidth *
              fourCellOddFoldedRegularDifferenceKernel p.1 p.2 * w p.1 ^ 2 -
            fourCellOperatorHalfWidth *
              fourCellOddFoldedRegularDifferenceKernel p.1 p.2 * w p.2 ^ 2) by
      have hsub := picone_sub_sq_identity
        (phiX := phi p.1) (phiY := phi p.2)
        (wX := w p.1) (wY := w p.2) hphiX hphiY
      rw [foldedRegularCorrelation_eq_dirichlet_sub_rows, hsub]
      ring)

def integratedRegularPicone (phi w : ℝ → ℝ) : ℝ :=
  ∫ p : ℝ × ℝ in positiveHalfSet ×ˢ positiveHalfSet,
    (regularPiconeSquareIntegrand phi w p +
      regularPiconeRowIntegrand phi w p)
      ∂((volume : Measure ℝ).prod volume)

theorem neg_regularCorrelation_eq_integratedRegularPicone
    (phi w : ℝ → ℝ) (hw : Continuous w)
    (hodd : Function.Odd w) (hphi : BlockPiconeGroundSigns phi) :
    -2 * fourCellOperatorHalfWidth *
        (∫ t : ℝ in 0..2,
          yoshidaRegularKernel (fourCellOperatorHalfWidth * t) *
            centeredEndpointCorrelation w t) =
      integratedRegularPicone phi w := by
  rw [neg_regularCorrelation_eq_foldedRegularSetIntegral w hw hodd]
  unfold integratedRegularPicone
  apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
  intro p hp
  apply foldedRegularOriginalIntegrand_eq_picone
  · exact (hphi.positiveHalf p.1 hp.1).ne'
  · exact (hphi.positiveHalf p.2 hp.2).ne'

/-! ## Exact transformed core and separated signed row -/

/-- Prime, endpoint-potential, and scalar-mass terms that are already
one-dimensional and local. -/
def fourCellOddRetainedLocalDiagonal (w : ℝ → ℝ) : ℝ :=
  fourCellOddRetainedPrimePotentialQuadratic w -
    (2 * (Real.log (2 * fourCellOperatorHalfWidth) +
      Real.eulerMascheroniConstant + Real.log Real.pi) + 3 / 200) *
      (∫ x : ℝ in 0..1, w x ^ 2)

/-- Unconditional exact integral decomposition of the actual odd core.  No
positivity premise about the core or its row occurs: every nonlocal term has
been Picone transformed, but square and row pieces remain paired until the
form-domain theorem below justifies integral linearity. -/
theorem fourCellOddCoreLocalQuadratic_eq_integratedBlockPicone
    (phi w : ℝ → ℝ) (hw : ContDiff ℝ 1 w)
    (hodd : Function.Odd w) (hphi : BlockPiconeGroundSigns phi) :
    fourCellOddCoreLocalQuadratic w =
      integratedRawBlockPicone phi w +
        integratedRegularPicone phi w +
        fourCellOddRetainedLocalDiagonal w := by
  have hregular := neg_regularCorrelation_eq_integratedRegularPicone
    phi w hw.continuous hodd hphi
  rw [fourCellOddCoreLocalQuadratic_eq_retained_sub_signed]
  unfold fourCellOddRetainedEndpointQuadratic
    fourCellOddSignedMassRegularQuadratic
    fourCellOddRetainedLocalDiagonal
  rw [rawStripCancellationReserve_eq_integratedRawBlockPicone
      phi w hw hodd hphi]
  linear_combination hregular

/-- Sum of all quotient-square integrals produced by the raw endpoint block
and the folded regular kernel. -/
def integratedBlockPiconeSquare (phi w : ℝ → ℝ) : ℝ :=
  (∫ p : ℝ × ℝ in lowerRawSet ×ˢ lowerRawSet,
      rawPiconeSquareIntegrand phi w p
        ∂((volume : Measure ℝ).prod volume)) +
    2 * (∫ p : ℝ × ℝ in endpointRawSet ×ˢ lowerRawSet,
      rawPiconeSquareIntegrand phi w p
        ∂((volume : Measure ℝ).prod volume)) +
    (∫ p : ℝ × ℝ in endpointRawSet ×ˢ endpointRawSet,
      endpointReflectedPiconeSquareIntegrand phi w p
        ∂((volume : Measure ℝ).prod volume)) +
    (∫ z : ℝ in -1..1, ∫ s : ℝ in -1..1,
      endpointEvenPiconeSquareIntegrand phi w z s) +
    ∫ p : ℝ × ℝ in positiveHalfSet ×ˢ positiveHalfSet,
      regularPiconeSquareIntegrand phi w p
        ∂((volume : Measure ℝ).prod volume)

/-! ## Positivity of the separated quotient squares -/

theorem rawPiconeSquareIntegrand_nonneg
    {phi w : ℝ → ℝ} (hphi : BlockPiconeGroundSigns phi)
    {p : ℝ × ℝ} (hp : p ∈ positiveHalfSet ×ˢ positiveHalfSet) :
    0 ≤ rawPiconeSquareIntegrand phi w p := by
  have hphiX : 0 ≤ phi p.1 := (hphi.positiveHalf p.1 hp.1).le
  have hphiY : 0 ≤ phi p.2 := (hphi.positiveHalf p.2 hp.2).le
  have hkSub : 0 ≤ positiveHalfSameReserveWeight p.1 p.2 :=
    positiveHalfSameReserveWeight_nonneg p.1 p.2
  have hkAdd : 0 ≤ positiveHalfReflectedReserveWeight p.1 p.2 := by
    unfold positiveHalfReflectedReserveWeight
    exact div_nonneg (by norm_num) (mul_nonneg (by norm_num)
      (add_nonneg hp.1.1 hp.2.1))
  unfold rawPiconeSquareIntegrand
  exact mul_nonneg (mul_nonneg hphiX hphiY)
    (add_nonneg
      (mul_nonneg hkSub (sq_nonneg _))
      (mul_nonneg hkAdd (sq_nonneg _)))

theorem endpointReflectedPiconeSquareIntegrand_nonneg
    {phi w : ℝ → ℝ} (hphi : BlockPiconeGroundSigns phi)
    {p : ℝ × ℝ} (hp : p ∈ endpointRawSet ×ˢ endpointRawSet) :
    0 ≤ endpointReflectedPiconeSquareIntegrand phi w p := by
  have hpX : p.1 ∈ positiveHalfSet :=
    ⟨by linarith [hp.1.1], hp.1.2⟩
  have hpY : p.2 ∈ positiveHalfSet :=
    ⟨by linarith [hp.2.1], hp.2.2⟩
  have hphiX : 0 ≤ phi p.1 := (hphi.positiveHalf p.1 hpX).le
  have hphiY : 0 ≤ phi p.2 := (hphi.positiveHalf p.2 hpY).le
  have hkAdd : 0 ≤ positiveHalfReflectedReserveWeight p.1 p.2 := by
    unfold positiveHalfReflectedReserveWeight
    exact div_nonneg (by norm_num) (mul_nonneg (by norm_num)
      (add_nonneg hpX.1 hpY.1))
  unfold endpointReflectedPiconeSquareIntegrand
  positivity

theorem endpointEvenPiconeSquareIntegrand_nonneg
    {phi w : ℝ → ℝ} (hphi : BlockPiconeGroundSigns phi)
    {z s : ℝ} (hz : z ∈ Icc (-1 : ℝ) 1)
    (hs : s ∈ Icc (-1 : ℝ) 1) :
    0 ≤ endpointEvenPiconeSquareIntegrand phi w z s := by
  have hphiZ : 0 ≤ fourCellOddEndpointStripEven phi z :=
    (hphi.stripEven z hz).le
  have hphiS : 0 ≤ fourCellOddEndpointStripEven phi s :=
    (hphi.stripEven s hs).le
  have hweight : 0 ≤ endpointEvenPiconeWeight z s := by
    unfold endpointEvenPiconeWeight
    positivity
  unfold endpointEvenPiconeSquareIntegrand
  positivity

theorem regularPiconeSquareIntegrand_nonneg
    {phi w : ℝ → ℝ} (hphi : BlockPiconeGroundSigns phi)
    {p : ℝ × ℝ} (hp : p ∈ positiveHalfSet ×ˢ positiveHalfSet) :
    0 ≤ regularPiconeSquareIntegrand phi w p := by
  have hwidth : 0 ≤ fourCellOperatorHalfWidth := by
    unfold fourCellOperatorHalfWidth
    positivity
  have hkernel :
      0 ≤ fourCellOddFoldedRegularDifferenceKernel p.1 p.2 :=
    fourCellOddFoldedRegularDifferenceKernel_nonneg
      hp.1.1 hp.1.2 hp.2.1 hp.2.2
  have hphiX : 0 ≤ phi p.1 := (hphi.positiveHalf p.1 hp.1).le
  have hphiY : 0 ≤ phi p.2 := (hphi.positiveHalf p.2 hp.2).le
  unfold regularPiconeSquareIntegrand
  positivity

/-- Every term in the separated square functional is nonnegative.  This is
the structural lower-bound step: the remaining obstruction is exactly the
single integrated signed row together with the retained local diagonal. -/
theorem integratedBlockPiconeSquare_nonneg
    (phi w : ℝ → ℝ) (hphi : BlockPiconeGroundSigns phi) :
    0 ≤ integratedBlockPiconeSquare phi w := by
  have hAA : 0 ≤ ∫ p : ℝ × ℝ in lowerRawSet ×ˢ lowerRawSet,
      rawPiconeSquareIntegrand phi w p
        ∂((volume : Measure ℝ).prod volume) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem
      (measurableSet_Ico.prod measurableSet_Ico)] with p hp
    apply rawPiconeSquareIntegrand_nonneg hphi
    exact
      ⟨⟨hp.1.1, hp.1.2.le.trans (by norm_num)⟩,
        ⟨hp.2.1, hp.2.2.le.trans (by norm_num)⟩⟩
  have hBA : 0 ≤ ∫ p : ℝ × ℝ in endpointRawSet ×ˢ lowerRawSet,
      rawPiconeSquareIntegrand phi w p
        ∂((volume : Measure ℝ).prod volume) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem
      (measurableSet_Icc.prod measurableSet_Ico)] with p hp
    apply rawPiconeSquareIntegrand_nonneg hphi
    exact
      ⟨⟨by linarith [hp.1.1], hp.1.2⟩,
        ⟨hp.2.1, hp.2.2.le.trans (by norm_num)⟩⟩
  have hBB : 0 ≤ ∫ p : ℝ × ℝ in endpointRawSet ×ˢ endpointRawSet,
      endpointReflectedPiconeSquareIntegrand phi w p
        ∂((volume : Measure ℝ).prod volume) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem
      (measurableSet_Icc.prod measurableSet_Icc)] with p hp
    exact endpointReflectedPiconeSquareIntegrand_nonneg hphi hp
  have hEven : 0 ≤ ∫ z : ℝ in -1..1, ∫ s : ℝ in -1..1,
      endpointEvenPiconeSquareIntegrand phi w z s := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro z hz
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro s hs
    apply endpointEvenPiconeSquareIntegrand_nonneg hphi
    · simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hz
    · simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hs
  have hRegular : 0 ≤ ∫ p : ℝ × ℝ in
      positiveHalfSet ×ˢ positiveHalfSet,
      regularPiconeSquareIntegrand phi w p
        ∂((volume : Measure ℝ).prod volume) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem
      (measurableSet_Icc.prod measurableSet_Icc)] with p hp
    exact regularPiconeSquareIntegrand_nonneg hphi hp
  unfold integratedBlockPiconeSquare
  positivity

/-- The single signed integrated diagonal row left after every quotient
square is removed.  Its sign is intentionally not asserted. -/
def integratedBlockPiconeRow (phi w : ℝ → ℝ) : ℝ :=
  (∫ p : ℝ × ℝ in lowerRawSet ×ˢ lowerRawSet,
      rawPiconeRowIntegrand phi w p
        ∂((volume : Measure ℝ).prod volume)) +
    2 * (∫ p : ℝ × ℝ in endpointRawSet ×ˢ lowerRawSet,
      rawPiconeRowIntegrand phi w p
        ∂((volume : Measure ℝ).prod volume)) +
    (∫ p : ℝ × ℝ in endpointRawSet ×ˢ endpointRawSet,
      endpointReflectedPiconeRowIntegrand phi w p
        ∂((volume : Measure ℝ).prod volume)) +
    (∫ z : ℝ in -1..1, ∫ s : ℝ in -1..1,
      endpointEvenPiconeRowIntegrand phi w z s) +
    ∫ p : ℝ × ℝ in positiveHalfSet ×ˢ positiveHalfSet,
      regularPiconeRowIntegrand phi w p
        ∂((volume : Measure ℝ).prod volume)

/-- Technical form-domain conditions needed only to split integrals of
`square + row`.  These are integrability statements, not sign or target
assumptions. -/
structure BlockPiconeIntegralFormDomain
    (phi w : ℝ → ℝ) : Prop where
  rawSquareAA : IntegrableOn (rawPiconeSquareIntegrand phi w)
    (lowerRawSet ×ˢ lowerRawSet) ((volume : Measure ℝ).prod volume)
  rawRowAA : IntegrableOn (rawPiconeRowIntegrand phi w)
    (lowerRawSet ×ˢ lowerRawSet) ((volume : Measure ℝ).prod volume)
  rawSquareBA : IntegrableOn (rawPiconeSquareIntegrand phi w)
    (endpointRawSet ×ˢ lowerRawSet) ((volume : Measure ℝ).prod volume)
  rawRowBA : IntegrableOn (rawPiconeRowIntegrand phi w)
    (endpointRawSet ×ˢ lowerRawSet) ((volume : Measure ℝ).prod volume)
  endpointReflectedSquare : IntegrableOn
    (endpointReflectedPiconeSquareIntegrand phi w)
    (endpointRawSet ×ˢ endpointRawSet)
    ((volume : Measure ℝ).prod volume)
  endpointReflectedRow : IntegrableOn
    (endpointReflectedPiconeRowIntegrand phi w)
    (endpointRawSet ×ˢ endpointRawSet)
    ((volume : Measure ℝ).prod volume)
  endpointEvenSquareInner : ∀ z : ℝ, IntervalIntegrable
    (endpointEvenPiconeSquareIntegrand phi w z) volume (-1) 1
  endpointEvenRowInner : ∀ z : ℝ, IntervalIntegrable
    (endpointEvenPiconeRowIntegrand phi w z) volume (-1) 1
  endpointEvenSquareOuter : IntervalIntegrable
    (fun z : ℝ ↦ ∫ s : ℝ in -1..1,
      endpointEvenPiconeSquareIntegrand phi w z s) volume (-1) 1
  endpointEvenRowOuter : IntervalIntegrable
    (fun z : ℝ ↦ ∫ s : ℝ in -1..1,
      endpointEvenPiconeRowIntegrand phi w z s) volume (-1) 1
  regularSquare : IntegrableOn (regularPiconeSquareIntegrand phi w)
    (positiveHalfSet ×ˢ positiveHalfSet)
    ((volume : Measure ℝ).prod volume)
  regularRow : IntegrableOn (regularPiconeRowIntegrand phi w)
    (positiveHalfSet ×ˢ positiveHalfSet)
    ((volume : Measure ℝ).prod volume)

theorem integratedRaw_add_regular_eq_square_add_row
    (phi w : ℝ → ℝ)
    (hform : BlockPiconeIntegralFormDomain phi w) :
    integratedRawBlockPicone phi w + integratedRegularPicone phi w =
      integratedBlockPiconeSquare phi w +
        integratedBlockPiconeRow phi w := by
  have hEvenInner (z : ℝ) :
      (∫ s : ℝ in -1..1,
        endpointEvenPiconeSquareIntegrand phi w z s +
          endpointEvenPiconeRowIntegrand phi w z s) =
      (∫ s : ℝ in -1..1,
        endpointEvenPiconeSquareIntegrand phi w z s) +
      ∫ s : ℝ in -1..1,
        endpointEvenPiconeRowIntegrand phi w z s :=
    intervalIntegral.integral_add
      (hform.endpointEvenSquareInner z)
      (hform.endpointEvenRowInner z)
  have hEven :
      (∫ z : ℝ in -1..1, ∫ s : ℝ in -1..1,
        endpointEvenPiconeSquareIntegrand phi w z s +
          endpointEvenPiconeRowIntegrand phi w z s) =
      (∫ z : ℝ in -1..1, ∫ s : ℝ in -1..1,
        endpointEvenPiconeSquareIntegrand phi w z s) +
      ∫ z : ℝ in -1..1, ∫ s : ℝ in -1..1,
        endpointEvenPiconeRowIntegrand phi w z s := by
    rw [show (fun z : ℝ ↦ ∫ s : ℝ in -1..1,
        endpointEvenPiconeSquareIntegrand phi w z s +
          endpointEvenPiconeRowIntegrand phi w z s) =
      fun z ↦ (∫ s : ℝ in -1..1,
          endpointEvenPiconeSquareIntegrand phi w z s) +
        ∫ s : ℝ in -1..1,
          endpointEvenPiconeRowIntegrand phi w z s by
      funext z
      exact hEvenInner z]
    exact intervalIntegral.integral_add
      hform.endpointEvenSquareOuter hform.endpointEvenRowOuter
  unfold integratedRawBlockPicone integratedRegularPicone
    integratedBlockPiconeSquare integratedBlockPiconeRow
  rw [integral_add hform.rawSquareAA hform.rawRowAA,
    integral_add hform.rawSquareBA hform.rawRowBA,
    integral_add hform.endpointReflectedSquare
      hform.endpointReflectedRow,
    integral_add hform.regularSquare hform.regularRow,
    hEven]
  ring

/-- Exact square-plus-signed-row decomposition of the actual core on the
Picone form domain. -/
theorem fourCellOddCoreLocalQuadratic_eq_square_add_integratedRow
    (phi w : ℝ → ℝ) (hw : ContDiff ℝ 1 w)
    (hodd : Function.Odd w) (hphi : BlockPiconeGroundSigns phi)
    (hform : BlockPiconeIntegralFormDomain phi w) :
    fourCellOddCoreLocalQuadratic w =
      integratedBlockPiconeSquare phi w +
        integratedBlockPiconeRow phi w +
        fourCellOddRetainedLocalDiagonal w := by
  rw [fourCellOddCoreLocalQuadratic_eq_integratedBlockPicone
      phi w hw hodd hphi,
    integratedRaw_add_regular_eq_square_add_row phi w hform]

/-- Structural lower bound for the actual odd core.  All quotient-square
integrals have been discarded with their proved sign; the right frontier is
the explicit integrated Picone row plus the already local diagonal terms. -/
theorem integratedBlockPiconeRow_add_retained_le_fourCellOddCoreLocalQuadratic
    (phi w : ℝ → ℝ) (hw : ContDiff ℝ 1 w)
    (hodd : Function.Odd w) (hphi : BlockPiconeGroundSigns phi)
    (hform : BlockPiconeIntegralFormDomain phi w) :
    integratedBlockPiconeRow phi w +
        fourCellOddRetainedLocalDiagonal w ≤
      fourCellOddCoreLocalQuadratic w := by
  rw [fourCellOddCoreLocalQuadratic_eq_square_add_integratedRow
      phi w hw hodd hphi hform]
  linarith [integratedBlockPiconeSquare_nonneg phi w hphi]

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddCoreBlockPiconeIntegralStructural
