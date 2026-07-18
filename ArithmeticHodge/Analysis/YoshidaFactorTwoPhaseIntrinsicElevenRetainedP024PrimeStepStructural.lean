import ArithmeticHodge.Analysis.ShiftedLegendreCenteredLowModeThreeL2
import ArithmeticHodge.Analysis.ShiftedLegendreJacobiRecurrenceStructural
import ArithmeticHodge.Analysis.ShiftedLegendreLogEnergyOrthogonalProjection
import ArithmeticHodge.Analysis.YoshidaFactorTwoFixedLagRepresenterStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEnvelope

set_option autoImplicit false

open Matrix MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024PrimeStepStructural

open ShiftedLegendreCenteredLowModeThreeL2
open ShiftedLegendreCenteredLowModes
open ShiftedLegendreJacobiRecurrenceStructural
open ShiftedLegendreLogEnergyOrthogonalProjection
open ShiftedLegendreOrthogonality
open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoFixedLagRepresenterStructural
open YoshidaFactorTwoPhaseEnvelope

noncomputable section

/-!
# Exact folded retained-prime step profiles

The retained `p = 3` atom has dimensionless lag strictly between one and
two.  Its two translated supports are therefore disjoint.  For the retained
`P₀/P₂/P₄` core, the positive half of every alternating step row is one
explicit polynomial on `[tau - 1, 1]` and zero elsewhere.
-/

/-- Dimensionless lag of the retained `p = 3` atom. -/
def retainedPrimeLag : ℝ :=
  factorTwoPrimeShift / yoshidaEndpointA

/-- The canonical even `P₀/P₂/P₄` modes used by the retained step
block. -/
def retainedPrimeEvenMode (i : Fin 3) : ℝ[X] :=
  shiftedLegendreReal (2 * i.1)

/-- Alternating retained-prime step row for one canonical even mode. -/
def retainedPrimeOddStepRow (i : Fin 3) (x : ℝ) : ℝ :=
  factorTwoFixedLagJ retainedPrimeLag
    (centeredPolynomialLift (retainedPrimeEvenMode i)) x

/-- Centered degree four, obtained from the all-degree Jacobi recurrence
rather than from a coefficient expansion. -/
theorem centeredShiftedLegendreReal_four :
    centeredShiftedLegendreReal 4 =
      (1 / 8 : ℝ) •
        ((35 : ℝ) • X ^ 4 - (30 : ℝ) • X ^ 2 + 3) := by
  apply Polynomial.funext
  intro x
  have h := congrArg (fun p : ℝ[X] ↦ p.eval x)
    (centeredShiftedLegendreReal_threeTerm 2)
  simp only [Polynomial.eval_smul, Polynomial.eval_sub,
    Polynomial.eval_neg, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat,
    smul_eq_mul] at h ⊢
  rw [eval_centeredShiftedLegendreReal_three,
    eval_centeredShiftedLegendreReal_two] at h
  norm_num at h ⊢
  linear_combination (1 / 4 : ℝ) * h

/-- The three polynomial pieces underlying the retained prime-step rows. -/
def retainedP024PrimeStepPolynomial (i : Fin 3) (x : ℝ) : ℝ :=
  ![1,
    (3 * x ^ 2 - 1) / 2,
    (35 * x ^ 4 - 30 * x ^ 2 + 3) / 8] i

/-- The same three pieces in boundary-depth coordinates
`u = x - (tau - 1)`. -/
def retainedP024PrimeStepDepthPolynomial (i : Fin 3) (u : ℝ) : ℝ :=
  ![1,
    1 - 3 * u + (3 / 2 : ℝ) * u ^ 2,
    1 - 10 * u + (45 / 2 : ℝ) * u ^ 2 -
      (35 / 2 : ℝ) * u ^ 3 + (35 / 8 : ℝ) * u ^ 4] i

theorem retainedP024PrimeStepPolynomial_sub_lag
    (i : Fin 3) (x : ℝ) :
    retainedP024PrimeStepPolynomial i (x - retainedPrimeLag) =
      retainedP024PrimeStepDepthPolynomial i
        (x - (retainedPrimeLag - 1)) := by
  fin_cases i <;>
    simp [retainedP024PrimeStepPolynomial,
      retainedP024PrimeStepDepthPolynomial] <;>
    ring

theorem centeredPolynomialLift_retainedP024EvenMode
    (i : Fin 3) (x : ℝ) :
    centeredPolynomialLift (retainedPrimeEvenMode i) x =
      retainedP024PrimeStepPolynomial i x := by
  have htransport (n : ℕ) :
      centeredPolynomialLift (shiftedLegendreReal n) x =
        (centeredShiftedLegendreReal n).eval x := by
    exact (eval_centeredShiftedLegendreReal n x).symm
  fin_cases i
  · change centeredPolynomialLift (shiftedLegendreReal 0) x = 1
    rw [htransport]
    simp
  · change centeredPolynomialLift (shiftedLegendreReal 2) x =
      (3 * x ^ 2 - 1) / 2
    rw [htransport, eval_centeredShiftedLegendreReal_two]
  · change centeredPolynomialLift (shiftedLegendreReal 4) x =
      (35 * x ^ 4 - 30 * x ^ 2 + 3) / 8
    rw [htransport, centeredShiftedLegendreReal_four]
    simp [Polynomial.smul_eq_C_mul]
    ring

/-- The dimensionless retained-prime lag is genuinely larger than one, so
the two translated supports do not touch. -/
theorem one_lt_retainedP024PrimeLag :
    1 < retainedPrimeLag := by
  have hsqrt2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2sq : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt2lt : Real.sqrt 2 < (3 / 2 : ℝ) := by nlinarith
  have hlog := Real.strictMonoOn_log hsqrt2pos (by norm_num) hsqrt2lt
  have hlogsqrt : Real.log (Real.sqrt 2) = Real.log 2 / 2 := by
    rw [Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hlogsqrt] at hlog
  rw [show retainedPrimeLag =
      factorTwoPrimeShift / yoshidaEndpointA by rfl,
    lt_div_iff₀ yoshidaEndpointA_pos]
  unfold factorTwoPrimeShift yoshidaEndpointA
  simpa only [one_mul] using hlog

/-- On the positive half-line, a retained alternating prime-step row is the
negative translated polynomial on its surviving interval and zero outside. -/
theorem retainedP024OddPrimeStepRow_eq_indicator_of_nonneg
    (i : Fin 3) {x : ℝ} (hx : 0 ≤ x) :
    retainedPrimeOddStepRow i x =
      (Icc (retainedPrimeLag - 1) 1).indicator
        (fun z ↦ -retainedP024PrimeStepPolynomial i
          (z - retainedPrimeLag)) x := by
  have hlag := one_lt_retainedP024PrimeLag
  have hnotRight :
      x ∉ Icc (-1 : ℝ) (1 - retainedPrimeLag) := by
    intro hmem
    linarith [hmem.2]
  have hsupport :
      Icc (-1 + retainedPrimeLag) 1 =
        Icc (retainedPrimeLag - 1) 1 := by
    congr 1
    ring
  unfold retainedPrimeOddStepRow factorTwoFixedLagJ
    factorTwoFixedLagRightRepresenter factorTwoFixedLagLeftRepresenter
  rw [Set.indicator_of_notMem hnotRight, zero_sub, hsupport]
  by_cases hmem : x ∈ Icc (retainedPrimeLag - 1) 1
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem,
      centeredPolynomialLift_retainedP024EvenMode]
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem,
      neg_zero]

/-- Boundary-depth form of the positive-half retained step row. -/
theorem retainedPrimeOddStepRow_eq_depth_indicator_of_nonneg
    (i : Fin 3) {x : ℝ} (hx : 0 ≤ x) :
    retainedPrimeOddStepRow i x =
      (Icc (retainedPrimeLag - 1) 1).indicator
        (fun z ↦ -retainedP024PrimeStepDepthPolynomial i
          (z - (retainedPrimeLag - 1))) x := by
  rw [retainedP024OddPrimeStepRow_eq_indicator_of_nonneg i hx]
  by_cases hmem : x ∈ Icc (retainedPrimeLag - 1) 1
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem,
      retainedP024PrimeStepPolynomial_sub_lag]
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024PrimeStepStructural
