import ArithmeticHodge.Analysis.MultiplicativeWeilBelowThreePrimeReductionStructural

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneFourCellPrimeGeometryStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilBelowThreePrimeReductionStructural
open MultiplicativeWeilMinimalNegativeBlockStructural
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural

/-!
# Exact prime-two geometry of four monotone quarter cells

Four consecutive cells telescope to the band multiplier

`s_k - s_(k+4)`.

The only points which can meet their factor-two dilates lie in the first
transition interval.  On that interval multiplication by two carries the
last transition back to the first, so the two band factors are exactly
`s_k` and `1 - s_k`.  This exposes the sharp `1 / 4` mask in the surviving
prime-two correlation.
-/

/-- Four consecutive canonical cells beginning at `k`. -/
def monotoneQuarterFourBlock
    (parent : BombieriTest) (k : ℤ) : BombieriTest :=
  monotoneQuarterFiniteBlock parent k 0 4

/-- Bridge to the below-three module's offset-indexed four-cell block. -/
theorem monotoneQuarterFourBlock_eq_belowThreeFourCellBlock
    (parent : BombieriTest) (k : ℤ) :
    monotoneQuarterFourBlock parent k =
      monotoneQuarterFourCellBlock parent k 0 := rfl

/-- Four cells telescope to their two boundary steps. -/
theorem monotoneQuarterFourBlock_apply
    (parent : BombieriTest) (k : ℤ) (x : ℝ) :
    monotoneQuarterFourBlock parent k x =
      (((monotoneQuarterStep k x -
        monotoneQuarterStep (k + 4) x : ℝ) : ℂ) * parent x) := by
  unfold monotoneQuarterFourBlock monotoneQuarterFiniteBlock
  simp only [Nat.zero_add]
  rw [sum_range_monotoneQuarterCell_eq_cutoff_sub]
  simp only [TestFunction.coe_sub, Pi.sub_apply,
    monotoneQuarterCutoff_apply]
  push_cast
  ring

/-- Factor two transports the last boundary transition exactly to the first. -/
theorem monotoneQuarterStep_add_four_two_mul
    (k : ℤ) (x : ℝ) :
    monotoneQuarterStep (k + 4) (2 * x) =
      monotoneQuarterStep k x := by
  unfold monotoneQuarterStep
  rw [show k + 4 + 1 = (k + 1) + 4 by ring,
    quarterLogLatticePoint_add_four,
    quarterLogLatticePoint_add_four]
  congr 1
  field_simp

/-- On the first transition interval the lower band factor is `s_k`. -/
theorem monotoneQuarterFourBlock_apply_firstTransition
    (parent : BombieriTest) (k : ℤ) {x : ℝ}
    (hx : x ∈ Set.Icc (quarterLogLatticePoint k)
      (quarterLogLatticePoint (k + 1))) :
    monotoneQuarterFourBlock parent k x =
      ((monotoneQuarterStep k x : ℝ) : ℂ) * parent x := by
  rw [monotoneQuarterFourBlock_apply,
    monotoneQuarterStep_eq_zero_of_le (k + 4)
      (hx.2.trans (quarterLogLatticePoint_mono (by omega)))]
  simp

/-- On the doubled first transition interval the upper band factor is
the complementary mask `1 - s_k`. -/
theorem monotoneQuarterFourBlock_apply_two_mul_firstTransition
    (parent : BombieriTest) (k : ℤ) {x : ℝ}
    (hx : x ∈ Set.Icc (quarterLogLatticePoint k)
      (quarterLogLatticePoint (k + 1))) :
    monotoneQuarterFourBlock parent k (2 * x) =
      (((1 - monotoneQuarterStep k x : ℝ) : ℂ) * parent (2 * x)) := by
  rw [monotoneQuarterFourBlock_apply,
    monotoneQuarterStep_eq_one_of_le k]
  · rw [monotoneQuarterStep_add_four_two_mul]
  · calc
      quarterLogLatticePoint (k + 1) ≤ quarterLogLatticePoint (k + 4) :=
        quarterLogLatticePoint_mono (by omega)
      _ = 2 * quarterLogLatticePoint k := by
        rw [quarterLogLatticePoint_add_four]
      _ ≤ 2 * x := mul_le_mul_of_nonneg_left hx.1 (by norm_num)

/-- Below the first band boundary the whole four-cell block vanishes. -/
theorem monotoneQuarterFourBlock_apply_eq_zero_of_le
    (parent : BombieriTest) (k : ℤ) {x : ℝ}
    (hx : x ≤ quarterLogLatticePoint k) :
    monotoneQuarterFourBlock parent k x = 0 := by
  rw [monotoneQuarterFourBlock_apply,
    monotoneQuarterStep_eq_zero_of_le k hx,
    monotoneQuarterStep_eq_zero_of_le (k + 4)
      (hx.trans (quarterLogLatticePoint_mono (by omega)))]
  simp

/-- At and above the end of the first transition, doubling has already left
the four-cell band. -/
theorem monotoneQuarterFourBlock_apply_two_mul_eq_zero_of_right
    (parent : BombieriTest) (k : ℤ) {x : ℝ}
    (hx : quarterLogLatticePoint (k + 1) ≤ x) :
    monotoneQuarterFourBlock parent k (2 * x) = 0 := by
  have hlast : quarterLogLatticePoint (k + 5) ≤ 2 * x := by
    rw [show k + 5 = (k + 1) + 4 by ring,
      quarterLogLatticePoint_add_four]
    exact mul_le_mul_of_nonneg_left hx (by norm_num)
  rw [monotoneQuarterFourBlock_apply,
    monotoneQuarterStep_eq_one_of_le k
      ((quarterLogLatticePoint_mono (by omega)).trans hlast),
    monotoneQuarterStep_eq_one_of_le (k + 4)
      (by simpa only [add_assoc] using hlast)]
  simp

/-- The prime-two product of a four-cell block is an explicit complementary-
mask product on the only possible interaction interval. -/
theorem monotoneQuarterFourBlock_two_mul_product_firstTransition
    (parent : BombieriTest) (k : ℤ) {x : ℝ}
    (hx : x ∈ Set.Icc (quarterLogLatticePoint k)
      (quarterLogLatticePoint (k + 1))) :
    monotoneQuarterFourBlock parent k (2 * x) *
        starRingEnd ℂ (monotoneQuarterFourBlock parent k x) =
      ((monotoneQuarterStep k x *
          (1 - monotoneQuarterStep k x) : ℝ) : ℂ) *
        parent (2 * x) * starRingEnd ℂ (parent x) := by
  rw [monotoneQuarterFourBlock_apply_firstTransition parent k hx,
    monotoneQuarterFourBlock_apply_two_mul_firstTransition parent k hx]
  have hstar : starRingEnd ℂ
      (((monotoneQuarterStep k x : ℝ) : ℂ)) =
        ((monotoneQuarterStep k x : ℝ) : ℂ) := by simp
  simp only [map_mul, hstar]
  push_cast
  ring

/-- The complementary endpoint mask has the sharp universal upper bound
`1 / 4`. -/
theorem monotoneQuarterStep_mul_one_sub_le_quarter
    (k : ℤ) (x : ℝ) :
    monotoneQuarterStep k x * (1 - monotoneQuarterStep k x) ≤
      (1 / 4 : ℝ) := by
  have hs0 := monotoneQuarterStep_nonneg k x
  have hs1 := monotoneQuarterStep_le_one k x
  nlinarith [sq_nonneg (monotoneQuarterStep k x - 1 / 2)]

/-- The complementary endpoint mask is nonnegative. -/
theorem monotoneQuarterStep_mul_one_sub_nonnegative
    (k : ℤ) (x : ℝ) :
    0 ≤ monotoneQuarterStep k x *
      (1 - monotoneQuarterStep k x) := by
  exact mul_nonneg (monotoneQuarterStep_nonneg k x)
    (sub_nonneg.mpr (monotoneQuarterStep_le_one k x))

/-- The complete factor-two correlation of four cells is supported on one
quarter transition and carries the exact complementary mask `s * (1-s)`.
This is the physical form of the unique prime-two cost in the below-three
reduction. -/
theorem criticalDilationCorrelation_fourBlock_eq_complementaryMaskIntegral
    (parent : BombieriTest) (k : ℤ) :
    criticalDilationCorrelation (monotoneQuarterFourBlock parent k) 2 =
      ((Real.sqrt 2 : ℝ) : ℂ) *
        ∫ x : ℝ in Set.Icc (quarterLogLatticePoint k)
            (quarterLogLatticePoint (k + 1)),
          ((monotoneQuarterStep k x *
              (1 - monotoneQuarterStep k x) : ℝ) : ℂ) *
            parent (2 * x) * starRingEnd ℂ (parent x) := by
  let F : ℝ → ℂ := fun x ↦
    ((Real.sqrt 2 : ℝ) : ℂ) *
      monotoneQuarterFourBlock parent k (2 * x) *
        starRingEnd ℂ (monotoneQuarterFourBlock parent k x)
  have hsubset : Set.Icc (quarterLogLatticePoint k)
      (quarterLogLatticePoint (k + 1)) ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    exact (quarterLogLatticePoint_pos k).trans_le hx.1
  have hlocalize :
      (∫ x : ℝ in Set.Ioi 0, F x) =
        ∫ x : ℝ in Set.Icc (quarterLogLatticePoint k)
          (quarterLogLatticePoint (k + 1)), F x := by
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero
      measurableSet_Ioi hsubset
    intro x hx
    by_cases hleft : x ≤ quarterLogLatticePoint k
    · dsimp only [F]
      rw [monotoneQuarterFourBlock_apply_eq_zero_of_le parent k hleft,
        map_zero, mul_zero]
    · have hright : quarterLogLatticePoint (k + 1) ≤ x := by
        have hxNot : ¬ (quarterLogLatticePoint k ≤ x ∧
            x ≤ quarterLogLatticePoint (k + 1)) := by
          simpa only [Set.mem_Icc] using hx.2
        have hkx : quarterLogLatticePoint k ≤ x := le_of_not_ge hleft
        exact le_of_not_gt (fun hlt ↦ hxNot ⟨hkx, hlt.le⟩)
      dsimp only [F]
      rw [monotoneQuarterFourBlock_apply_two_mul_eq_zero_of_right
        parent k hright, mul_zero, zero_mul]
  unfold criticalDilationCorrelation
  change (∫ x : ℝ in Set.Ioi 0, F x) = _
  rw [hlocalize]
  calc
    (∫ x : ℝ in Set.Icc (quarterLogLatticePoint k)
          (quarterLogLatticePoint (k + 1)), F x) =
        ∫ x : ℝ in Set.Icc (quarterLogLatticePoint k)
          (quarterLogLatticePoint (k + 1)),
            ((Real.sqrt 2 : ℝ) : ℂ) *
              (((monotoneQuarterStep k x *
                  (1 - monotoneQuarterStep k x) : ℝ) : ℂ) *
                parent (2 * x) * starRingEnd ℂ (parent x)) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x hx
      dsimp only [F]
      calc
        ((Real.sqrt 2 : ℝ) : ℂ) *
              monotoneQuarterFourBlock parent k (2 * x) *
                starRingEnd ℂ (monotoneQuarterFourBlock parent k x) =
            ((Real.sqrt 2 : ℝ) : ℂ) *
              (monotoneQuarterFourBlock parent k (2 * x) *
                starRingEnd ℂ (monotoneQuarterFourBlock parent k x)) := by ring
        _ = _ := by rw [
          monotoneQuarterFourBlock_two_mul_product_firstTransition
            parent k hx]
    _ = _ := MeasureTheory.integral_const_mul
      (μ := volume.restrict (Set.Icc (quarterLogLatticePoint k)
        (quarterLogLatticePoint (k + 1)))) _ _

/-- The exact mixed half-block term left by the below-three reduction is the
same one-transition complementary-mask integral.  Thus the active four-cell
inequality can be attacked without any remaining prime sum or abstract
quadratic cross. -/
theorem fourCell_halfCross_eq_complementaryMaskIntegral
    (parent : BombieriTest) (k : ℤ) :
    bombieriQuadraticCrossTest
        (monotoneQuarterFiniteBlock parent k 0 2)
        (monotoneQuarterFiniteBlock parent k 2 2) 2 =
      ∫ x : ℝ in Set.Icc (quarterLogLatticePoint k)
          (quarterLogLatticePoint (k + 1)),
        ((monotoneQuarterStep k x *
            (1 - monotoneQuarterStep k x) : ℝ) : ℂ) *
          parent (2 * x) * starRingEnd ℂ (parent x) := by
  have hhalf :=
    criticalDilationCorrelation_fourCell_eq_sqrt_two_mul_halfCross
      parent k 0
  have hmask :=
    criticalDilationCorrelation_fourBlock_eq_complementaryMaskIntegral
      parent k
  change criticalDilationCorrelation (monotoneQuarterFourBlock parent k) 2 =
      ((Real.sqrt 2 : ℝ) : ℂ) *
        bombieriQuadraticCrossTest
          (monotoneQuarterFiniteBlock parent k 0 2)
          (monotoneQuarterFiniteBlock parent k 2 2) 2 at hhalf
  have hsqrt : (((Real.sqrt 2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne'
  apply (mul_left_cancel₀ hsqrt)
  calc
    ((Real.sqrt 2 : ℝ) : ℂ) *
          bombieriQuadraticCrossTest
            (monotoneQuarterFiniteBlock parent k 0 2)
            (monotoneQuarterFiniteBlock parent k 2 2) 2 =
        criticalDilationCorrelation (monotoneQuarterFourBlock parent k) 2 :=
      hhalf.symm
    _ = _ := hmask

/-- The complementary mask gives the sharp elementary `1 / 4` bound for the
surviving mixed half-block prime correlation.  The remaining four-cell
problem is therefore whether the local critical half-cross controls this
explicit parent overlap. -/
theorem norm_fourCell_halfCross_le_quarter_parentOverlap
    (parent : BombieriTest) (k : ℤ) :
    ‖bombieriQuadraticCrossTest
        (monotoneQuarterFiniteBlock parent k 0 2)
        (monotoneQuarterFiniteBlock parent k 2 2) 2‖ ≤
      ∫ x : ℝ in Set.Icc (quarterLogLatticePoint k)
          (quarterLogLatticePoint (k + 1)),
        (1 / 4 : ℝ) * ‖parent (2 * x)‖ * ‖parent x‖ := by
  let G : ℝ → ℂ := fun x ↦
    ((monotoneQuarterStep k x *
        (1 - monotoneQuarterStep k x) : ℝ) : ℂ) *
      parent (2 * x) * starRingEnd ℂ (parent x)
  let D : ℝ → ℝ := fun x ↦
    (1 / 4 : ℝ) * ‖parent (2 * x)‖ * ‖parent x‖
  have hGcont : Continuous G := by
    dsimp only [G]
    have hs : Continuous (monotoneQuarterStep k) :=
      (monotoneQuarterStep_contDiff k).continuous
    have hw : Continuous (fun x : ℝ ↦
        monotoneQuarterStep k x *
          (1 - monotoneQuarterStep k x)) :=
      hs.mul (continuous_const.sub hs)
    have hwc : Continuous (fun x : ℝ ↦
        ((monotoneQuarterStep k x *
          (1 - monotoneQuarterStep k x) : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp hw
    have hp : Continuous (parent : ℝ → ℂ) := parent.contDiff.continuous
    have hpTwo : Continuous (fun x : ℝ ↦ parent (2 * x)) :=
      hp.comp (by fun_prop)
    have hpStar : Continuous (fun x : ℝ ↦
        starRingEnd ℂ (parent x)) := by
      exact Complex.continuous_conj.comp hp
    exact (hwc.mul hpTwo).mul hpStar
  have hDcont : Continuous D := by
    dsimp only [D]
    fun_prop
  have hGint : IntegrableOn G (Set.Icc (quarterLogLatticePoint k)
      (quarterLogLatticePoint (k + 1))) :=
    hGcont.continuousOn.integrableOn_compact isCompact_Icc
  have hDint : IntegrableOn D (Set.Icc (quarterLogLatticePoint k)
      (quarterLogLatticePoint (k + 1))) :=
    hDcont.continuousOn.integrableOn_compact isCompact_Icc
  rw [fourCell_halfCross_eq_complementaryMaskIntegral]
  change ‖∫ x : ℝ in Set.Icc (quarterLogLatticePoint k)
      (quarterLogLatticePoint (k + 1)), G x‖ ≤
    ∫ x : ℝ in Set.Icc (quarterLogLatticePoint k)
      (quarterLogLatticePoint (k + 1)), D x
  calc
    ‖∫ x : ℝ in Set.Icc (quarterLogLatticePoint k)
          (quarterLogLatticePoint (k + 1)), G x‖ ≤
        ∫ x : ℝ in Set.Icc (quarterLogLatticePoint k)
          (quarterLogLatticePoint (k + 1)), ‖G x‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ in Set.Icc (quarterLogLatticePoint k)
          (quarterLogLatticePoint (k + 1)), D x := by
      apply integral_mono_ae hGint.norm hDint
      filter_upwards with x
      have hw0 := monotoneQuarterStep_mul_one_sub_nonnegative k x
      have hw := monotoneQuarterStep_mul_one_sub_le_quarter k x
      dsimp only [G, D]
      have hstarNorm : ‖starRingEnd ℂ (parent x)‖ = ‖parent x‖ := by
        simp
      rw [norm_mul, norm_mul, hstarNorm, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hw0]
      calc
        monotoneQuarterStep k x *
              (1 - monotoneQuarterStep k x) *
              ‖parent (2 * x)‖ * ‖parent x‖ =
            (monotoneQuarterStep k x *
              (1 - monotoneQuarterStep k x)) *
              (‖parent (2 * x)‖ * ‖parent x‖) := by ring
        _ ≤ (1 / 4 : ℝ) *
              (‖parent (2 * x)‖ * ‖parent x‖) :=
          mul_le_mul_of_nonneg_right hw
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ = (1 / 4 : ℝ) * ‖parent (2 * x)‖ * ‖parent x‖ := by ring

end

end ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneFourCellPrimeGeometryStructural
