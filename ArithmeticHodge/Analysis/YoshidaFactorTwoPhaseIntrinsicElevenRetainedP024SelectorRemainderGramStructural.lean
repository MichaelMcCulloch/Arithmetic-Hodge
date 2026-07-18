import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorQuotientStructural

set_option autoImplicit false

open Matrix MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorRemainderGramStructural

open ShiftedLegendreLogEnergyOrthogonalProjection
open ShiftedLegendreOrthogonality
open YoshidaEndpointPotentialBound
open YoshidaFactorTwoPhaseIntrinsicElevenConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorPoleRemainderStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorQuotientStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorSOSStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedSelectorHomogeneityStructural
open YoshidaFactorTwoPhaseIntrinsicElevenSelectorGramStructural

noncomputable section

/-!
# Positive shifted-remainder Grams for the retained P024 selector

The quotient left by exact endpoint-pole extraction is not bounded entry by
entry.  Instead it is retained as the weighted Gram of the mass-shifted
remainder rows.  This preserves all cancellations and, in the alternating
channel, the favorable positive quotient block.
-/

theorem continuous_retainedP024SelectorWholeEvenPoleRow
    (i : Fin 3 ⊕ Fin 3) :
    Continuous (retainedP024SelectorWholeEvenPoleRow i) := by
  rcases i with i | i
  · simp only [retainedP024SelectorWholeEvenPoleRow]
    unfold retainedP024EvenMode centeredPolynomialLift
    fun_prop
  · simp only [retainedP024SelectorWholeEvenPoleRow]
    fun_prop

theorem continuous_retainedP024SelectorAlternatingPoleRow (i : Fin 3) :
    Continuous (retainedP024SelectorAlternatingPoleRow i) := by
  unfold retainedP024SelectorAlternatingPoleRow
  fun_prop

theorem retainedP024SelectorWholeEvenResidual_div_sqrt_memLp_two
    (i : Fin 3 ⊕ Fin 3) :
    MemLp (fun x ↦
      factorTwoIntrinsicElevenSelectorResidual
          (retainedP024SelectorWholeEvenRepresenter i)
          (retainedP024SelectorWholeEvenPolynomial i) x /
        Real.sqrt (factorTwoIntrinsicElevenRetainedEvenWeight x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  rcases i with i | i
  · exact retainedP024BaseSelectorResidual_div_sqrt_memLp_two i
  · let p := shiftedLegendreReal (2 * i.1)
    let qPlus := ![retainedP024SelectorPlus0, retainedP024SelectorPlus2,
      retainedP024SelectorPlus4] i
    let qMinus := ![retainedP024SelectorMinus0, retainedP024SelectorMinus2,
      retainedP024SelectorMinus4] i
    have hPlus :=
      factorTwoIntrinsicElevenRetainedEvenSelectorResidual_div_sqrt_memLp_two
        (1 / 512 : ℝ) p 0 qPlus 1 0
    have hMinus :=
      factorTwoIntrinsicElevenRetainedEvenSelectorResidual_div_sqrt_memLp_two
        (1 / 512 : ℝ) p 0 qMinus (-1) 0
    have hHalf := (hPlus.sub hMinus).const_mul (1 / 2 : ℝ)
    apply (memLp_congr_ae (μ := volume.restrict (Ioc (-1 : ℝ) 1)) ?_).mpr
      hHalf
    filter_upwards [] with x
    simp only [retainedP024SelectorWholeEvenRepresenter,
      retainedP024SelectorWholeEvenPolynomial]
    rw [retainedP024SymmetricSelectorResidual_eq_endpoint_half_sub
      (1 / 512 : ℝ) p qPlus qMinus x]
    dsimp only [p, qPlus, qMinus, Pi.sub_apply]
    ring

theorem retainedP024SelectorAlternatingResidual_div_sqrt_memLp_two
    (i : Fin 3) :
    MemLp (fun x ↦
      factorTwoIntrinsicElevenSelectorResidual
          (retainedOddAlternatingRepresenterAt
            (1 / 512 : ℝ) (retainedP024EvenMode i))
          (retainedP024SelectorAlternatingPolynomial i) x /
        Real.sqrt (factorTwoIntrinsicElevenRetainedOddWeight x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  simpa only [retainedOddAlternatingRepresenterAt] using
    factorTwoIntrinsicElevenRetainedOddSelectorResidual_div_sqrt_memLp_two
      (1 / 512 : ℝ) (retainedP024EvenMode i) 0
      (retainedP024SelectorAlternatingPolynomial i) 0 1

/-- Every mass-shifted even remainder is an honest element of the retained
weighted dual space. -/
theorem retainedP024SelectorWholeEvenShiftedRemainder_div_sqrt_memLp_two
    (i : Fin 3 ⊕ Fin 3) :
    MemLp (fun x ↦
      retainedP024SelectorWholeEvenShiftedRemainder i x /
        Real.sqrt (factorTwoIntrinsicElevenRetainedEvenWeight x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  have hresidual :=
    retainedP024SelectorWholeEvenResidual_div_sqrt_memLp_two i
  have hpole := sqrt_retainedEvenWeight_mul_memLp_two
    (retainedP024SelectorWholeEvenPoleRow i)
    (continuous_retainedP024SelectorWholeEvenPoleRow i)
  have hsub := hresidual.sub hpole
  apply (memLp_congr_ae (μ := volume.restrict (Ioc (-1 : ℝ) 1)) ?_).mpr hsub
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    MeasureTheory.ae_restrict_of_ae
      (MeasureTheory.Measure.ae_ne volume (1 : ℝ))] with x hx hx1
  have hxIcc : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
  have hxIoo : x ∈ Ioo (-1 : ℝ) 1 :=
    ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
  change retainedP024SelectorWholeEvenShiftedRemainder i x /
      Real.sqrt (factorTwoIntrinsicElevenRetainedEvenWeight x) =
    factorTwoIntrinsicElevenSelectorResidual
          (retainedP024SelectorWholeEvenRepresenter i)
          (retainedP024SelectorWholeEvenPolynomial i) x /
        Real.sqrt (factorTwoIntrinsicElevenRetainedEvenWeight x) -
      Real.sqrt (factorTwoIntrinsicElevenRetainedEvenWeight x) *
        retainedP024SelectorWholeEvenPoleRow i x
  rw [retainedP024SelectorWholeEvenResidual_eq_pole_add_remainder i hxIoo]
  have hW := factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc hxIcc
  have hsqrt : 0 < Real.sqrt
      (factorTwoIntrinsicElevenRetainedEvenWeight x) := Real.sqrt_pos.2 hW
  unfold retainedP024SelectorWholeEvenShiftedRemainder
  rw [retainedP024RetainedEvenWeight_eq_affine] at hW hsqrt ⊢
  field_simp [ne_of_gt hsqrt]
  rw [Real.sq_sqrt hW.le]
  ring

/-- Every mass-shifted alternating remainder is an honest element of the
retained weighted dual space. -/
theorem retainedP024SelectorAlternatingShiftedRemainder_div_sqrt_memLp_two
    (i : Fin 3) :
    MemLp (fun x ↦
      retainedP024SelectorAlternatingShiftedRemainder i x /
        Real.sqrt (factorTwoIntrinsicElevenRetainedOddWeight x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  have hresidual :=
    retainedP024SelectorAlternatingResidual_div_sqrt_memLp_two i
  have hpole := sqrt_retainedOddWeight_mul_memLp_two
    (retainedP024SelectorAlternatingPoleRow i)
    (continuous_retainedP024SelectorAlternatingPoleRow i)
  have hsub := hresidual.sub hpole
  apply (memLp_congr_ae (μ := volume.restrict (Ioc (-1 : ℝ) 1)) ?_).mpr hsub
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    MeasureTheory.ae_restrict_of_ae
      (MeasureTheory.Measure.ae_ne volume (1 : ℝ))] with x hx hx1
  have hxIcc : x ∈ Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
  have hxIoo : x ∈ Ioo (-1 : ℝ) 1 :=
    ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
  change retainedP024SelectorAlternatingShiftedRemainder i x /
      Real.sqrt (factorTwoIntrinsicElevenRetainedOddWeight x) =
    factorTwoIntrinsicElevenSelectorResidual
          (retainedOddAlternatingRepresenterAt
            (1 / 512 : ℝ) (retainedP024EvenMode i))
          (retainedP024SelectorAlternatingPolynomial i) x /
        Real.sqrt (factorTwoIntrinsicElevenRetainedOddWeight x) -
      Real.sqrt (factorTwoIntrinsicElevenRetainedOddWeight x) *
        retainedP024SelectorAlternatingPoleRow i x
  rw [retainedP024SelectorAlternatingResidual_eq_pole_add_remainder i hxIoo]
  have hW := factorTwoIntrinsicElevenRetainedOddWeight_pos_on_Icc hxIcc
  have hsqrt : 0 < Real.sqrt
      (factorTwoIntrinsicElevenRetainedOddWeight x) := Real.sqrt_pos.2 hW
  unfold retainedP024SelectorAlternatingShiftedRemainder
  rw [retainedP024RetainedOddWeight_eq_affine] at hW hsqrt ⊢
  field_simp [ne_of_gt hsqrt]
  rw [Real.sq_sqrt hW.le]
  ring

/-- Weighted Gram of all six mass-shifted retained-even remainders. -/
def retainedP024SelectorWholeEvenShiftedRemainderGram :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  factorTwoIntrinsicElevenSelectorGram
    factorTwoIntrinsicElevenRetainedEvenWeight
    retainedP024SelectorWholeEvenShiftedRemainder
    (fun _ ↦ (0 : ℝ[X]))

/-- Weighted Gram of the three mass-shifted alternating remainders. -/
def retainedP024SelectorAlternatingShiftedRemainderGram :
    Matrix (Fin 3) (Fin 3) ℝ :=
  factorTwoIntrinsicElevenSelectorGram
    factorTwoIntrinsicElevenRetainedOddWeight
    retainedP024SelectorAlternatingShiftedRemainder
    (fun _ ↦ (0 : ℝ[X]))

theorem retainedP024SelectorWholeEvenShiftedRemainderGram_apply
    (i j : Fin 3 ⊕ Fin 3) :
    retainedP024SelectorWholeEvenShiftedRemainderGram i j =
      ∫ x : ℝ in -1..1,
        retainedP024SelectorWholeEvenShiftedRemainder i x *
          retainedP024SelectorWholeEvenShiftedRemainder j x /
            factorTwoIntrinsicElevenRetainedEvenWeight x := by
  simp [retainedP024SelectorWholeEvenShiftedRemainderGram,
    factorTwoIntrinsicElevenSelectorGram,
    factorTwoIntrinsicElevenSelectorCrossDual,
    factorTwoIntrinsicElevenSelectorResidual, centeredPolynomialLift]

theorem retainedP024SelectorAlternatingShiftedRemainderGram_apply
    (i j : Fin 3) :
    retainedP024SelectorAlternatingShiftedRemainderGram i j =
      ∫ x : ℝ in -1..1,
        retainedP024SelectorAlternatingShiftedRemainder i x *
          retainedP024SelectorAlternatingShiftedRemainder j x /
            factorTwoIntrinsicElevenRetainedOddWeight x := by
  simp [retainedP024SelectorAlternatingShiftedRemainderGram,
    factorTwoIntrinsicElevenSelectorGram,
    factorTwoIntrinsicElevenSelectorCrossDual,
    factorTwoIntrinsicElevenSelectorResidual, centeredPolynomialLift]

theorem intervalIntegrable_retainedP024SelectorWholeEvenShiftedRemainderCross
    (i j : Fin 3 ⊕ Fin 3) :
    IntervalIntegrable (fun x ↦
      retainedP024SelectorWholeEvenShiftedRemainder i x *
        retainedP024SelectorWholeEvenShiftedRemainder j x /
          factorTwoIntrinsicElevenRetainedEvenWeight x)
      volume (-1) 1 := by
  have hi : MemLp (fun x ↦
      factorTwoIntrinsicElevenSelectorResidual
          (retainedP024SelectorWholeEvenShiftedRemainder i) 0 x /
        Real.sqrt (factorTwoIntrinsicElevenRetainedEvenWeight x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    simpa [factorTwoIntrinsicElevenSelectorResidual, centeredPolynomialLift] using
      retainedP024SelectorWholeEvenShiftedRemainder_div_sqrt_memLp_two i
  have hj : MemLp (fun x ↦
      factorTwoIntrinsicElevenSelectorResidual
          (retainedP024SelectorWholeEvenShiftedRemainder j) 0 x /
        Real.sqrt (factorTwoIntrinsicElevenRetainedEvenWeight x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    simpa [factorTwoIntrinsicElevenSelectorResidual, centeredPolynomialLift] using
      retainedP024SelectorWholeEvenShiftedRemainder_div_sqrt_memLp_two j
  simpa [factorTwoIntrinsicElevenSelectorResidual, centeredPolynomialLift] using
    intervalIntegrable_selectorCross_of_memLp
      factorTwoIntrinsicElevenRetainedEvenWeight
      (retainedP024SelectorWholeEvenShiftedRemainder i)
      (retainedP024SelectorWholeEvenShiftedRemainder j)
      (0 : ℝ[X]) (0 : ℝ[X])
      (fun x hx ↦ factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc hx)
      hi hj

theorem intervalIntegrable_retainedP024SelectorAlternatingShiftedRemainderCross
    (i j : Fin 3) :
    IntervalIntegrable (fun x ↦
      retainedP024SelectorAlternatingShiftedRemainder i x *
        retainedP024SelectorAlternatingShiftedRemainder j x /
          factorTwoIntrinsicElevenRetainedOddWeight x)
      volume (-1) 1 := by
  have hi : MemLp (fun x ↦
      factorTwoIntrinsicElevenSelectorResidual
          (retainedP024SelectorAlternatingShiftedRemainder i) 0 x /
        Real.sqrt (factorTwoIntrinsicElevenRetainedOddWeight x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    simpa [factorTwoIntrinsicElevenSelectorResidual, centeredPolynomialLift] using
      retainedP024SelectorAlternatingShiftedRemainder_div_sqrt_memLp_two i
  have hj : MemLp (fun x ↦
      factorTwoIntrinsicElevenSelectorResidual
          (retainedP024SelectorAlternatingShiftedRemainder j) 0 x /
        Real.sqrt (factorTwoIntrinsicElevenRetainedOddWeight x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    simpa [factorTwoIntrinsicElevenSelectorResidual, centeredPolynomialLift] using
      retainedP024SelectorAlternatingShiftedRemainder_div_sqrt_memLp_two j
  simpa [factorTwoIntrinsicElevenSelectorResidual, centeredPolynomialLift] using
    intervalIntegrable_selectorCross_of_memLp
      factorTwoIntrinsicElevenRetainedOddWeight
      (retainedP024SelectorAlternatingShiftedRemainder i)
      (retainedP024SelectorAlternatingShiftedRemainder j)
      (0 : ℝ[X]) (0 : ℝ[X])
      (fun x hx ↦ factorTwoIntrinsicElevenRetainedOddWeight_pos_on_Icc hx)
      hi hj

/-- The first four, nonquotient terms in the extracted retained-even row
pairing. -/
def retainedP024SelectorWholeEvenNonquotientIntegrand
    (i j : Fin 3 ⊕ Fin 3) (x : ℝ) : ℝ :=
  retainedP024PoleSlope * yoshidaEndpointPotential x *
      retainedP024SelectorWholeEvenPoleRow i x *
      retainedP024SelectorWholeEvenPoleRow j x +
    retainedP024SelectorWholeEvenPoleRow i x *
      retainedP024SelectorWholeEvenRemainder j x +
    retainedP024SelectorWholeEvenPoleRow j x *
      retainedP024SelectorWholeEvenRemainder i x -
    retainedP024EvenMass *
      retainedP024SelectorWholeEvenPoleRow i x *
      retainedP024SelectorWholeEvenPoleRow j x

/-- The first four, nonquotient terms in the extracted alternating row
pairing. -/
def retainedP024SelectorAlternatingNonquotientIntegrand
    (i j : Fin 3) (x : ℝ) : ℝ :=
  retainedP024PoleSlope * yoshidaEndpointPotential x *
      retainedP024SelectorAlternatingPoleRow i x *
      retainedP024SelectorAlternatingPoleRow j x +
    retainedP024SelectorAlternatingPoleRow i x *
      retainedP024SelectorAlternatingRemainder j x +
    retainedP024SelectorAlternatingPoleRow j x *
      retainedP024SelectorAlternatingRemainder i x -
    retainedP024OddMass *
      retainedP024SelectorAlternatingPoleRow i x *
      retainedP024SelectorAlternatingPoleRow j x

def retainedP024SelectorWholeEvenNonquotientGram :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ := fun i j ↦
  ∫ x : ℝ in -1..1,
    retainedP024SelectorWholeEvenNonquotientIntegrand i j x

def retainedP024SelectorAlternatingNonquotientGram :
    Matrix (Fin 3) (Fin 3) ℝ := fun i j ↦
  ∫ x : ℝ in -1..1,
    retainedP024SelectorAlternatingNonquotientIntegrand i j x

theorem intervalIntegrable_retainedP024SelectorWholeEvenResidualCross
    (i j : Fin 3 ⊕ Fin 3) :
    IntervalIntegrable (fun x ↦
      factorTwoIntrinsicElevenSelectorResidual
          (retainedP024SelectorWholeEvenRepresenter i)
          (retainedP024SelectorWholeEvenPolynomial i) x *
        factorTwoIntrinsicElevenSelectorResidual
          (retainedP024SelectorWholeEvenRepresenter j)
          (retainedP024SelectorWholeEvenPolynomial j) x /
        factorTwoIntrinsicElevenRetainedEvenWeight x) volume (-1) 1 :=
  intervalIntegrable_selectorCross_of_memLp
    factorTwoIntrinsicElevenRetainedEvenWeight
    (retainedP024SelectorWholeEvenRepresenter i)
    (retainedP024SelectorWholeEvenRepresenter j)
    (retainedP024SelectorWholeEvenPolynomial i)
    (retainedP024SelectorWholeEvenPolynomial j)
    (fun _x hx ↦ factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc hx)
    (retainedP024SelectorWholeEvenResidual_div_sqrt_memLp_two i)
    (retainedP024SelectorWholeEvenResidual_div_sqrt_memLp_two j)

theorem intervalIntegrable_retainedP024SelectorAlternatingResidualCross
    (i j : Fin 3) :
    IntervalIntegrable (fun x ↦
      factorTwoIntrinsicElevenSelectorResidual
          (retainedOddAlternatingRepresenterAt
            (1 / 512 : ℝ) (retainedP024EvenMode i))
          (retainedP024SelectorAlternatingPolynomial i) x *
        factorTwoIntrinsicElevenSelectorResidual
          (retainedOddAlternatingRepresenterAt
            (1 / 512 : ℝ) (retainedP024EvenMode j))
          (retainedP024SelectorAlternatingPolynomial j) x /
        factorTwoIntrinsicElevenRetainedOddWeight x) volume (-1) 1 :=
  intervalIntegrable_selectorCross_of_memLp
    factorTwoIntrinsicElevenRetainedOddWeight
    (retainedOddAlternatingRepresenterAt
      (1 / 512 : ℝ) (retainedP024EvenMode i))
    (retainedOddAlternatingRepresenterAt
      (1 / 512 : ℝ) (retainedP024EvenMode j))
    (retainedP024SelectorAlternatingPolynomial i)
    (retainedP024SelectorAlternatingPolynomial j)
    (fun _x hx ↦ factorTwoIntrinsicElevenRetainedOddWeight_pos_on_Icc hx)
    (retainedP024SelectorAlternatingResidual_div_sqrt_memLp_two i)
    (retainedP024SelectorAlternatingResidual_div_sqrt_memLp_two j)

theorem intervalIntegrable_retainedP024SelectorWholeEvenNonquotient
    (i j : Fin 3 ⊕ Fin 3) :
    IntervalIntegrable
      (retainedP024SelectorWholeEvenNonquotientIntegrand i j)
      volume (-1) 1 := by
  have hdiff :=
    (intervalIntegrable_retainedP024SelectorWholeEvenResidualCross i j).sub
      (intervalIntegrable_retainedP024SelectorWholeEvenShiftedRemainderCross i j)
  apply hdiff.congr_ae
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    MeasureTheory.ae_restrict_of_ae
      (MeasureTheory.Measure.ae_ne volume (1 : ℝ))] with x hx hx1
  rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
  have hxIoo : x ∈ Ioo (-1 : ℝ) 1 :=
    ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
  rw [retainedP024SelectorWholeEvenResidual_mul_div_weight_eq i j hxIoo]
  unfold retainedP024SelectorWholeEvenNonquotientIntegrand
  ring

theorem intervalIntegrable_retainedP024SelectorAlternatingNonquotient
    (i j : Fin 3) :
    IntervalIntegrable
      (retainedP024SelectorAlternatingNonquotientIntegrand i j)
      volume (-1) 1 := by
  have hdiff :=
    (intervalIntegrable_retainedP024SelectorAlternatingResidualCross i j).sub
      (intervalIntegrable_retainedP024SelectorAlternatingShiftedRemainderCross i j)
  apply hdiff.congr_ae
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    MeasureTheory.ae_restrict_of_ae
      (MeasureTheory.Measure.ae_ne volume (1 : ℝ))] with x hx hx1
  rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
  have hxIoo : x ∈ Ioo (-1 : ℝ) 1 :=
    ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
  rw [retainedP024SelectorAlternatingResidual_mul_div_weight_eq i j hxIoo]
  unfold retainedP024SelectorAlternatingNonquotientIntegrand
  ring

/-- Exact separation of the complete even selector Gram into its analytic
nonquotient part and a positive shifted-remainder Gram. -/
theorem retainedP024SelectorWholeEvenGram_eq_nonquotient_add_remainder :
    retainedP024SelectorWholeEvenGram =
      retainedP024SelectorWholeEvenNonquotientGram +
        retainedP024SelectorWholeEvenShiftedRemainderGram := by
  rw [retainedP024SelectorWholeEvenGram_eq_extracted]
  ext i j
  simp only [Matrix.add_apply, retainedP024SelectorWholeEvenExtractedGram,
    retainedP024SelectorWholeEvenNonquotientGram]
  rw [retainedP024SelectorWholeEvenShiftedRemainderGram_apply,
    ← intervalIntegral.integral_add
      (intervalIntegrable_retainedP024SelectorWholeEvenNonquotient i j)
      (intervalIntegrable_retainedP024SelectorWholeEvenShiftedRemainderCross i j)]
  rfl

/-- Exact separation of the alternating selector Gram into its analytic
nonquotient part and a positive shifted-remainder Gram. -/
theorem retainedP024SelectorAlternatingGram_eq_nonquotient_add_remainder :
    retainedP024SelectorAlternatingGram =
      retainedP024SelectorAlternatingNonquotientGram +
        retainedP024SelectorAlternatingShiftedRemainderGram := by
  rw [retainedP024SelectorAlternatingGram_eq_extracted]
  ext i j
  simp only [Matrix.add_apply, retainedP024SelectorAlternatingExtractedGram,
    retainedP024SelectorAlternatingNonquotientGram]
  rw [retainedP024SelectorAlternatingShiftedRemainderGram_apply,
    ← intervalIntegral.integral_add
      (intervalIntegrable_retainedP024SelectorAlternatingNonquotient i j)
      (intervalIntegrable_retainedP024SelectorAlternatingShiftedRemainderCross i j)]
  rfl

/-- Signed affine lift of an alternating `3 x 3` Gram.  Its upper block is
subtracted from the constant coefficient of the phase pencil, while its lower
block is added to the quadratic coefficient. -/
def retainedP024AlternatingSignedLift
    (G : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  Matrix.fromBlocks (-G) 0 0 G

theorem retainedP024SelectorAlternatingSignedLiftGram_eq_parts :
    retainedP024SelectorAlternatingSignedLiftGram =
      retainedP024AlternatingSignedLift
          retainedP024SelectorAlternatingNonquotientGram +
        retainedP024AlternatingSignedLift
          retainedP024SelectorAlternatingShiftedRemainderGram := by
  unfold retainedP024SelectorAlternatingSignedLiftGram
  rw [retainedP024SelectorAlternatingGram_eq_nonquotient_add_remainder]
  unfold retainedP024AlternatingSignedLift
  ext i j
  rcases i with i | i <;> rcases j with j | j
  all_goals simp <;> module

/-- Fully separated structural identity for the fixed asymmetric SOS Gram.
The last term is favorable on the lower affine block and therefore remains an
explicit positive Gram rather than being discarded through a scalar bound. -/
theorem retainedP024SelectorAsymmetricSOSGram_eq_nonquotient_remainders :
    retainedP024SelectorAsymmetricSOSGram =
      retainedP024SharpLowSOSGram -
          retainedP024SelectorWholeEvenNonquotientGram -
        retainedP024SelectorWholeEvenShiftedRemainderGram +
        retainedP024AlternatingSignedLift
          retainedP024SelectorAlternatingNonquotientGram +
        retainedP024AlternatingSignedLift
          retainedP024SelectorAlternatingShiftedRemainderGram := by
  rw [retainedP024SelectorAsymmetricSOSGram_eq_structural,
    retainedP024SelectorWholeEvenGram_eq_nonquotient_add_remainder,
    retainedP024SelectorAlternatingSignedLiftGram_eq_parts]
  module

theorem retainedP024SelectorWholeEvenShiftedRemainderGram_posSemidef :
    retainedP024SelectorWholeEvenShiftedRemainderGram.PosSemidef := by
  have hHermitian :
      retainedP024SelectorWholeEvenShiftedRemainderGram.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simpa [retainedP024SelectorWholeEvenShiftedRemainderGram,
      factorTwoIntrinsicElevenSelectorGram] using
      (factorTwoIntrinsicElevenSelectorCrossDual_comm
        factorTwoIntrinsicElevenRetainedEvenWeight
        (retainedP024SelectorWholeEvenShiftedRemainder i)
        (retainedP024SelectorWholeEvenShiftedRemainder j)
        (0 : ℝ[X]) (0 : ℝ[X])).symm
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHermitian
  intro c
  have hInt : ∀ i j, IntervalIntegrable (fun x ↦
      factorTwoIntrinsicElevenSelectorResidual
          (retainedP024SelectorWholeEvenShiftedRemainder i) 0 x *
        factorTwoIntrinsicElevenSelectorResidual
          (retainedP024SelectorWholeEvenShiftedRemainder j) 0 x /
        factorTwoIntrinsicElevenRetainedEvenWeight x) volume (-1) 1 := by
    intro i j
    simpa [factorTwoIntrinsicElevenSelectorResidual, centeredPolynomialLift] using
      intervalIntegrable_retainedP024SelectorWholeEvenShiftedRemainderCross i j
  have hquad := factorTwoIntrinsicElevenSelectorDual_sum_eq_matrixQuadratic
    factorTwoIntrinsicElevenRetainedEvenWeight
    retainedP024SelectorWholeEvenShiftedRemainder
    (fun _ ↦ (0 : ℝ[X]))
    hInt c
  change 0 ≤ star c ⬝ᵥ
    (factorTwoIntrinsicElevenSelectorGram
      factorTwoIntrinsicElevenRetainedEvenWeight
      retainedP024SelectorWholeEvenShiftedRemainder
      (fun _ ↦ (0 : ℝ[X])) *ᵥ c)
  rw [← hquad]
  exact factorTwoIntrinsicElevenSelectorDual_nonneg _ _ _
    (fun x hx ↦ factorTwoIntrinsicElevenRetainedEvenWeight_pos_on_Icc hx)

theorem retainedP024SelectorAlternatingShiftedRemainderGram_posSemidef :
    retainedP024SelectorAlternatingShiftedRemainderGram.PosSemidef := by
  have hHermitian :
      retainedP024SelectorAlternatingShiftedRemainderGram.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simpa [retainedP024SelectorAlternatingShiftedRemainderGram,
      factorTwoIntrinsicElevenSelectorGram] using
      (factorTwoIntrinsicElevenSelectorCrossDual_comm
        factorTwoIntrinsicElevenRetainedOddWeight
        (retainedP024SelectorAlternatingShiftedRemainder i)
        (retainedP024SelectorAlternatingShiftedRemainder j)
        (0 : ℝ[X]) (0 : ℝ[X])).symm
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHermitian
  intro c
  have hInt : ∀ i j, IntervalIntegrable (fun x ↦
      factorTwoIntrinsicElevenSelectorResidual
          (retainedP024SelectorAlternatingShiftedRemainder i) 0 x *
        factorTwoIntrinsicElevenSelectorResidual
          (retainedP024SelectorAlternatingShiftedRemainder j) 0 x /
        factorTwoIntrinsicElevenRetainedOddWeight x) volume (-1) 1 := by
    intro i j
    simpa [factorTwoIntrinsicElevenSelectorResidual, centeredPolynomialLift] using
      intervalIntegrable_retainedP024SelectorAlternatingShiftedRemainderCross i j
  have hquad := factorTwoIntrinsicElevenSelectorDual_sum_eq_matrixQuadratic
    factorTwoIntrinsicElevenRetainedOddWeight
    retainedP024SelectorAlternatingShiftedRemainder
    (fun _ ↦ (0 : ℝ[X]))
    hInt c
  change 0 ≤ star c ⬝ᵥ
    (factorTwoIntrinsicElevenSelectorGram
      factorTwoIntrinsicElevenRetainedOddWeight
      retainedP024SelectorAlternatingShiftedRemainder
      (fun _ ↦ (0 : ℝ[X])) *ᵥ c)
  rw [← hquad]
  exact factorTwoIntrinsicElevenSelectorDual_nonneg _ _ _
    (fun x hx ↦ factorTwoIntrinsicElevenRetainedOddWeight_pos_on_Icc hx)

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorRemainderGramStructural
