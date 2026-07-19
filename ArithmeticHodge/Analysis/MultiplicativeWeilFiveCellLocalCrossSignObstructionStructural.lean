import ArithmeticHodge.Analysis.MultiplicativeWeilAllLengthEndpointReserveStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilFourCellMixedSignObstructionStructural

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace

namespace ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellLocalCrossSignObstructionStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilAllLengthEndpointReserveStructural
open MultiplicativeWeilFourCellEnergyAbsorptionStructural
open MultiplicativeWeilFourCellMixedSignObstructionStructural
open MultiplicativeWeilMonotoneCellEnergyFrameStructural
open MultiplicativeWeilMonotoneNullSuffixVariationStructural
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural

/-!
# Sign obstruction to a universal five-cell local-cross reserve

The remote endpoint prime cost is even under an independent sign change of
the upper endpoint cell, whereas the mixed local critical form is odd.  Thus
the positive geometric-energy lower bound exposed by the five-cell estimate
cannot hold for every real common parent.  Any viable all-length argument
must use additional minimal-block constraints or a coupled determinant
reserve instead of assigning a universal positive sign to this cross.
-/

/-- The exact geometric-energy condition proposed for the five-cell remote
endpoint cross. -/
def FiveCellLocalCrossGeometricReserve (parent : BombieriTest) (k : ℤ) : Prop :=
  fourCellPrimeEnergyCoefficient * Real.sqrt
      (bombieriCriticalLogEnergy (monotoneQuarterCell parent k) *
        bombieriCriticalLogEnergy (monotoneQuarterCell parent (k + 4))) ≤
    (bombieriLocalCriticalForm
      (monotoneQuarterCell parent k)
      (monotoneQuarterCell parent (k + 4))).re

private theorem remoteCell_eq_zero_of_tsupport_le
    (parent : BombieriTest) (j : ℤ)
    (hupper : ∀ x ∈ tsupport parent, x ≤ quarterLogLatticePoint j) :
    monotoneQuarterCell parent j = 0 := by
  apply TestFunction.ext
  intro x
  by_cases hx : x ∈ tsupport parent
  · rw [monotoneQuarterCell_apply,
      monotoneQuarterWeight_eq_zero_of_le j (hupper x hx)]
    simp
  · have hpx : parent x = 0 := by
      by_contra hp
      exact hx (subset_tsupport parent (Function.mem_support.mpr hp))
    change (monotoneQuarterWeight j x : ℂ) * parent x = 0
    rw [hpx, mul_zero]

private theorem remoteCell_eq_zero_of_lattice_le_tsupport
    (parent : BombieriTest) (j : ℤ)
    (hlower : ∀ x ∈ tsupport parent,
      quarterLogLatticePoint (j + 2) ≤ x) :
    monotoneQuarterCell parent j = 0 := by
  apply TestFunction.ext
  intro x
  by_cases hx : x ∈ tsupport parent
  · rw [monotoneQuarterCell_apply,
      monotoneQuarterWeight_eq_zero_of_le_left j (hlower x hx)]
    simp
  · have hpx : parent x = 0 := by
      by_contra hp
      exact hx (subset_tsupport parent (Function.mem_support.mpr hp))
    change (monotoneQuarterWeight j x : ℂ) * parent x = 0
    rw [hpx, mul_zero]

private theorem monotoneQuarterWeight_pos_on_first_interval
    (j : ℤ) {x : ℝ}
    (hx : x ∈ Set.Ioo (quarterLogLatticePoint j)
      (quarterLogLatticePoint (j + 1))) :
    0 < monotoneQuarterWeight j x := by
  unfold monotoneQuarterWeight
  rw [monotoneQuarterStep_eq_zero_of_le (j + 1) hx.2.le]
  simpa only [sub_zero] using
    monotoneQuarterStep_pos_of_lattice_lt j hx.1

private theorem endpointCell_ne_zero_of_first_interval
    (parent : BombieriTest) (j : ℤ) (hne : parent ≠ 0)
    (hsupport : tsupport parent ⊆ Set.Ioo
      (quarterLogLatticePoint j) (quarterLogLatticePoint (j + 1))) :
    monotoneQuarterCell parent j ≠ 0 := by
  intro hzero
  obtain ⟨x, hx⟩ : ∃ x : ℝ, parent x ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    ext y
    simpa using h y
  have hxt : x ∈ tsupport parent :=
    subset_tsupport parent (Function.mem_support.mpr hx)
  have hweight := monotoneQuarterWeight_pos_on_first_interval j
    (hsupport hxt)
  have happly := congrArg (fun f : BombieriTest ↦ f x) hzero
  simp only [monotoneQuarterCell_apply, TestFunction.coe_zero,
    Pi.zero_apply] at happly
  exact hx (mul_eq_zero.mp happly |>.resolve_left
    (Complex.ofReal_ne_zero.mpr hweight.ne'))

/-- The physical critical energy is strictly positive on every nonzero
Bombieri test. -/
theorem bombieriCriticalLogEnergy_pos_of_ne_zero
    (g : BombieriTest) (hg : g ≠ 0) :
    0 < bombieriCriticalLogEnergy g := by
  obtain ⟨x, hx⟩ : ∃ x : ℝ, g x ≠ 0 := by
    by_contra h
    push_neg at h
    apply hg
    ext y
    simpa using h y
  let h : ℝ → ℝ := fun y ↦ ‖g y‖ ^ 2
  have hcont : Continuous h := by fun_prop
  have hcompact : HasCompactSupport h := by
    simpa only [h, pow_two] using g.hasCompactSupport.norm.mul_left
      (f := fun y : ℝ ↦ ‖g y‖)
  have hnonneg : 0 ≤ h := fun y ↦ sq_nonneg ‖g y‖
  have hxne : h x ≠ 0 := by
    dsimp only [h]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  have hpos : 0 < ∫ y : ℝ, h y :=
    hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero
      hcompact hnonneg hxne
  have hset : (∫ y : ℝ in Set.Ioi 0, h y) = ∫ y : ℝ, h y := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hynpos : ¬ 0 < y := by simpa using hy
    have hgy : g y = 0 := by
      by_contra hne
      have hmem := g.tsupport_subset
        (subset_tsupport g (Function.mem_support.mpr hne))
      exact hynpos (by simpa [positiveHalfLine] using hmem)
    simp [h, hgy]
  rw [bombieriCriticalLogEnergy_eq_integral_Ioi_norm_sq]
  change 0 < ∫ y : ℝ in Set.Ioi 0, h y
  rw [hset]
  exact hpos

private theorem criticalLogEnergy_neg (g : BombieriTest) :
    bombieriCriticalLogEnergy (-g) = bombieriCriticalLogEnergy g := by
  rw [bombieriCriticalLogEnergy_eq_integral_Ioi_norm_sq,
    bombieriCriticalLogEnergy_eq_integral_Ioi_norm_sq]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _hx
  simp

private theorem conjugate_fixed_add
    {f g : BombieriTest}
    (hf : bombieriConjugateTest f = f)
    (hg : bombieriConjugateTest g = g) :
    bombieriConjugateTest (f + g) = f + g := by
  rw [bombieriConjugateTest_add, hf, hg]

private theorem conjugate_fixed_sub
    {f g : BombieriTest}
    (hf : bombieriConjugateTest f = f)
    (hg : bombieriConjugateTest g = g) :
    bombieriConjugateTest (f - g) = f - g := by
  apply TestFunction.ext
  intro x
  have hfx := congrArg (fun q : BombieriTest ↦ q x) hf
  have hgx := congrArg (fun q : BombieriTest ↦ q x) hg
  simp only [bombieriConjugateTest_apply, TestFunction.coe_sub,
    Pi.sub_apply, map_sub] at hfx hgx ⊢
  rw [hfx, hgx]

/-- Even on conjugation-fixed parents, the proposed universal positive
five-cell local-cross reserve is impossible.  Two independently localized
endpoint bumps give honest common parents whose upper signs are opposite;
the energy cost is unchanged while the local cross reverses. -/
theorem not_universal_real_fiveCellLocalCrossGeometricReserve :
    ¬ (∀ parent : BombieriTest,
      bombieriConjugateTest parent = parent → ∀ k : ℤ,
        FiveCellLocalCrossGeometricReserve parent k) := by
  intro hall
  let k : ℤ := 0
  obtain ⟨lower, upper, hlowerNe, hupperNe,
      hlowerFixed, hupperFixed, hlowerSupport, hupperSupport, _hsep⟩ :=
    exists_nonzero_endpoint_localized_halfSeparated_pair k
  let f : BombieriTest := monotoneQuarterCell lower k
  let g : BombieriTest := monotoneQuarterCell upper (k + 4)
  have hfNe : f ≠ 0 := by
    exact endpointCell_ne_zero_of_first_interval lower k hlowerNe hlowerSupport
  have hgNe : g ≠ 0 := by
    exact endpointCell_ne_zero_of_first_interval upper (k + 4) hupperNe
      hupperSupport
  have hlowerRight : monotoneQuarterCell lower (k + 4) = 0 := by
    apply remoteCell_eq_zero_of_tsupport_le lower (k + 4)
    intro x hx
    exact (hlowerSupport hx).2.le.trans
      (quarterLogLatticePoint_mono (by omega))
  have hupperLeft : monotoneQuarterCell upper k = 0 := by
    apply remoteCell_eq_zero_of_lattice_le_tsupport upper k
    intro x hx
    exact (quarterLogLatticePoint_mono (m := k + 2) (n := k + 4)
      (by omega)).trans (hupperSupport hx).1.le
  have hplusLeft : monotoneQuarterCell (lower + upper) k = f := by
    rw [monotoneQuarterCell_add, hupperLeft, add_zero]
  have hplusRight : monotoneQuarterCell (lower + upper) (k + 4) = g := by
    rw [monotoneQuarterCell_add, hlowerRight, zero_add]
  have hminusLeft : monotoneQuarterCell (lower - upper) k = f := by
    have hneg : monotoneQuarterCell (-upper) k =
        -monotoneQuarterCell upper k := by
      simpa only [neg_smul, one_smul] using
        monotoneQuarterCell_smul (-1 : ℂ) upper k
    rw [sub_eq_add_neg, monotoneQuarterCell_add, hneg,
      hupperLeft, neg_zero, add_zero]
  have hminusRight : monotoneQuarterCell (lower - upper) (k + 4) = -g := by
    have hneg : monotoneQuarterCell (-upper) (k + 4) =
        -monotoneQuarterCell upper (k + 4) := by
      simpa only [neg_smul, one_smul] using
        monotoneQuarterCell_smul (-1 : ℂ) upper (k + 4)
    rw [sub_eq_add_neg, monotoneQuarterCell_add, hneg,
      hlowerRight, zero_add]
  have hEleft : 0 < bombieriCriticalLogEnergy f :=
    bombieriCriticalLogEnergy_pos_of_ne_zero f hfNe
  have hEright : 0 < bombieriCriticalLogEnergy g :=
    bombieriCriticalLogEnergy_pos_of_ne_zero g hgNe
  have hcost : 0 < fourCellPrimeEnergyCoefficient * Real.sqrt
      (bombieriCriticalLogEnergy f * bombieriCriticalLogEnergy g) := by
    have hcoeff : 0 < fourCellPrimeEnergyCoefficient := by
      unfold fourCellPrimeEnergyCoefficient
      positivity
    exact mul_pos hcoeff (Real.sqrt_pos.2 (mul_pos hEleft hEright))
  have hplus := hall (lower + upper)
    (conjugate_fixed_add hlowerFixed hupperFixed) k
  have hminus := hall (lower - upper)
    (conjugate_fixed_sub hlowerFixed hupperFixed) k
  unfold FiveCellLocalCrossGeometricReserve at hplus hminus
  rw [hplusLeft, hplusRight] at hplus
  rw [hminusLeft, hminusRight, criticalLogEnergy_neg, map_neg] at hminus
  simp only [Complex.neg_re] at hminus
  linarith

end

end ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellLocalCrossSignObstructionStructural
