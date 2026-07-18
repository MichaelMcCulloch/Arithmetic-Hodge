import ArithmeticHodge.Analysis.AffineWeightQuotient
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorSOSStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoReflectedPoleEntropyStructural

set_option autoImplicit false

open Matrix MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorPoleRemainderStructural

open ShiftedLegendreLogEnergyOrthogonalProjection
open ShiftedLegendreOrthogonality
open YoshidaEndpointEvenConstantCross
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointPotentialBound
open YoshidaFactorTwoPhaseIntrinsicElevenCompleteRepresentersStructural
open YoshidaFactorTwoPhaseIntrinsicElevenConcreteSelectorsStructural
open YoshidaFactorTwoPhaseIntrinsicElevenConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorSOSStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedRepresentersStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedSelectorHomogeneityStructural
open YoshidaFactorTwoForwardPolePolynomialReductionStructural
open YoshidaFactorTwoReflectedPoleEntropyStructural
open YoshidaFactorTwoReflectedPolePolynomialReductionStructural

noncomputable section

/-!
# Endpoint-trace pole extraction for the retained P024 selector

The retained multiplication weights have common potential slope `63 / 128`.
For the three even shifted-Legendre rows, the singular parts of the base,
symmetric, and alternating selector residuals have the simple endpoint-trace
profiles displayed below.  The nonconstant parts of the reflected-pole
potential coefficients contain a factor `1 - x^2`; multiplying that factor
by the endpoint potential is a continuous `negMulLog` row.
-/

/-- Common coefficient of the endpoint potential in both retained weights. -/
def retainedP024PoleSlope : ℝ := 63 / 128

/-- The three even shifted-Legendre modes used by the P024 selector. -/
def retainedP024EvenMode (i : Fin 3) : ℝ[X] :=
  shiftedLegendreReal (2 * i.1)

/-- Quotient after removing the constant endpoint trace `2` from the
symmetric reflected-pole potential coefficient. -/
def retainedP024KPotentialTraceQuotient (i : Fin 3) (x : ℝ) : ℝ :=
  ![0, 9, (245 * x ^ 2 + 435) / 4] i

/-- Quotient after removing the endpoint trace `-2x` from the alternating
reflected-pole potential coefficient. -/
def retainedP024JPotentialTraceQuotient (i : Fin 3) (x : ℝ) : ℝ :=
  ![0, 3 * x, x * (35 * x ^ 2 + 565) / 4] i

/-- Exact factorization of the symmetric reflected-pole coefficient after
its common endpoint trace is removed. -/
theorem retainedP024KPotentialSelector_eq_trace_add
    (i : Fin 3) (x : ℝ) :
    reflectedPoleKPotentialSelector (retainedP024EvenMode i) x =
      2 + (1 - x ^ 2) * retainedP024KPotentialTraceQuotient i x := by
  fin_cases i <;>
    norm_num [retainedP024EvenMode, retainedP024KPotentialTraceQuotient,
      reflectedPoleKPotentialSelector, shiftedLegendreReal,
      Polynomial.shiftedLegendre, Polynomial.eval_map,
      Polynomial.eval_finset_sum, Finset.sum_range_succ, Nat.choose] <;>
    ring

/-- Exact factorization of the alternating reflected-pole coefficient after
its common endpoint trace is removed. -/
theorem retainedP024JPotentialSelector_eq_trace_add
    (i : Fin 3) (x : ℝ) :
    reflectedPoleJPotentialSelector (retainedP024EvenMode i) x =
      -2 * x + (1 - x ^ 2) * retainedP024JPotentialTraceQuotient i x := by
  fin_cases i <;>
    norm_num [retainedP024EvenMode, retainedP024JPotentialTraceQuotient,
      reflectedPoleJPotentialSelector, shiftedLegendreReal,
      Polynomial.shiftedLegendre, Polynomial.eval_map,
      Polynomial.eval_finset_sum, Finset.sum_range_succ, Nat.choose] <;>
    ring

/-- Continuous extension of the potential times the nonconstant symmetric
reflected-pole coefficient. -/
def retainedP024KPotentialTraceRemainder (i : Fin 3) (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.negMulLog (1 - x ^ 2) *
    retainedP024KPotentialTraceQuotient i x

/-- Continuous extension of the potential times the nonconstant alternating
reflected-pole coefficient. -/
def retainedP024JPotentialTraceRemainder (i : Fin 3) (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.negMulLog (1 - x ^ 2) *
    retainedP024JPotentialTraceQuotient i x

theorem continuous_retainedP024KPotentialTraceRemainder (i : Fin 3) :
    Continuous (retainedP024KPotentialTraceRemainder i) := by
  fin_cases i <;>
    unfold retainedP024KPotentialTraceRemainder <;>
    simp [retainedP024KPotentialTraceQuotient] <;>
    fun_prop

theorem continuous_retainedP024JPotentialTraceRemainder (i : Fin 3) :
    Continuous (retainedP024JPotentialTraceRemainder i) := by
  fin_cases i <;>
    unfold retainedP024JPotentialTraceRemainder <;>
    simp [retainedP024JPotentialTraceQuotient] <;>
    fun_prop

theorem retainedP024KPotentialTraceRemainder_eq
    (i : Fin 3) (x : ℝ) :
    retainedP024KPotentialTraceRemainder i x =
      yoshidaEndpointPotential x *
        (reflectedPoleKPotentialSelector (retainedP024EvenMode i) x - 2) := by
  rw [retainedP024KPotentialSelector_eq_trace_add]
  unfold retainedP024KPotentialTraceRemainder yoshidaEndpointPotential
    Real.negMulLog
  ring

theorem retainedP024JPotentialTraceRemainder_eq
    (i : Fin 3) (x : ℝ) :
    retainedP024JPotentialTraceRemainder i x =
      yoshidaEndpointPotential x *
        (reflectedPoleJPotentialSelector (retainedP024EvenMode i) x +
          2 * x) := by
  rw [retainedP024JPotentialSelector_eq_trace_add]
  unfold retainedP024JPotentialTraceRemainder yoshidaEndpointPotential
    Real.negMulLog
  ring

/-- Pole profile of the combined base--symmetric retained-even row. -/
def retainedP024SelectorWholeEvenPoleRow :
    Fin 3 ⊕ Fin 3 → ℝ → ℝ
  | Sum.inl i => fun x ↦
      (511 / 252 : ℝ) * centeredPolynomialLift (retainedP024EvenMode i) x
  | Sum.inr _ => fun _ ↦ -(511 / 504 : ℝ)

/-- Pole profile of an alternating retained-odd row. -/
def retainedP024SelectorAlternatingPoleRow (_i : Fin 3) (x : ℝ) : ℝ :=
  (511 / 504 : ℝ) * x

/-- Fixed alternating selector polynomial attached to the `i`th row. -/
def retainedP024SelectorAlternatingPolynomial (i : Fin 3) : ℝ[X] :=
  ![retainedP024SelectorAlt0, retainedP024SelectorAlt2,
    retainedP024SelectorAlt4] i

/-- Bounded part of a base retained-even selector residual after its
`(511/512) V P_i` pole is removed. -/
def retainedP024SelectorBaseRemainder (i : Fin 3) (x : ℝ) : ℝ :=
  factorTwoIntrinsicElevenCleanSurvivorRepresenter
      (retainedP024EvenMode i) x -
    yoshidaEndpointPotential x *
      centeredPolynomialLift (retainedP024EvenMode i) x -
    centeredPolynomialLift (retainedP024SelectorBasePolynomial i) x

/-- Bounded part of a symmetric retained-even selector residual after the
constant endpoint trace of its reflected pole is removed. -/
def retainedP024SelectorSymmetricRemainder (i : Fin 3) (x : ℝ) : ℝ :=
  factorTwoIntrinsicElevenAnalyticEvenRepresenter
      (retainedP024EvenMode i) 0 1 0 x +
    factorTwoIntrinsicElevenForwardEvenRepresenter
      (retainedP024EvenMode i) 0 1 0 x +
    factorTwoIntrinsicElevenPrimeEvenRepresenter
      (retainedP024EvenMode i) 0 1 0 x -
    centeredPolynomialLift
      (retainedP024SymmetricSelector
        (![retainedP024SelectorPlus0, retainedP024SelectorPlus2,
          retainedP024SelectorPlus4] i)
        (![retainedP024SelectorMinus0, retainedP024SelectorMinus2,
          retainedP024SelectorMinus4] i)) x -
    (511 / 2048 : ℝ) *
      (retainedP024KPotentialTraceRemainder i x +
        reflectedPoleKEntropyRemainder (retainedP024EvenMode i) x)

/-- Combined bounded remainder for the six retained-even rows. -/
def retainedP024SelectorWholeEvenRemainder :
    Fin 3 ⊕ Fin 3 → ℝ → ℝ
  | Sum.inl i => retainedP024SelectorBaseRemainder i
  | Sum.inr i => retainedP024SelectorSymmetricRemainder i

/-- Bounded part of an alternating retained-odd selector residual after the
linear endpoint trace of its reflected pole is removed. -/
def retainedP024SelectorAlternatingRemainder (i : Fin 3) (x : ℝ) : ℝ :=
  factorTwoIntrinsicElevenAnalyticOddRepresenter
      (retainedP024EvenMode i) 0 0 1 x +
    factorTwoIntrinsicElevenForwardOddRepresenter
      (retainedP024EvenMode i) 0 0 1 x +
    factorTwoIntrinsicElevenPrimeOddRepresenter
      (retainedP024EvenMode i) 0 0 1 x -
    centeredPolynomialLift (retainedP024SelectorAlternatingPolynomial i) x -
    (511 / 2048 : ℝ) *
      (retainedP024JPotentialTraceRemainder i x +
        reflectedPoleJEntropyRemainder (retainedP024EvenMode i) x)

private theorem factorTwoIntrinsicElevenCleanSurvivorRepresenter_zero
    (x : ℝ) :
    factorTwoIntrinsicElevenCleanSurvivorRepresenter (0 : ℝ[X]) x = 0 := by
  unfold factorTwoIntrinsicElevenCleanSurvivorRepresenter
    yoshidaEndpointEvenRegularRepresenter
    yoshidaEndpointCoshMoment yoshidaEndpointSinhMoment
  simp [centeredPolynomialLift]

private def HasP024IocAbsBound (f : ℝ → ℝ) : Prop :=
  ∃ B : ℝ, 0 < B ∧ ∀ x ∈ Ioc (-1 : ℝ) 1, |f x| ≤ B

private theorem hasP024IocAbsBound_add
    {f g : ℝ → ℝ} (hf : HasP024IocAbsBound f)
    (hg : HasP024IocAbsBound g) :
    HasP024IocAbsBound (fun x ↦ f x + g x) := by
  obtain ⟨B, hB, hf⟩ := hf
  obtain ⟨C, hC, hg⟩ := hg
  refine ⟨B + C, add_pos hB hC, ?_⟩
  intro x hx
  exact (abs_add_le _ _).trans (add_le_add (hf x hx) (hg x hx))

private theorem hasP024IocAbsBound_sub
    {f g : ℝ → ℝ} (hf : HasP024IocAbsBound f)
    (hg : HasP024IocAbsBound g) :
    HasP024IocAbsBound (fun x ↦ f x - g x) := by
  obtain ⟨B, hB, hf⟩ := hf
  obtain ⟨C, hC, hg⟩ := hg
  refine ⟨B + C, add_pos hB hC, ?_⟩
  intro x hx
  exact (abs_sub _ _).trans (add_le_add (hf x hx) (hg x hx))

private theorem hasP024IocAbsBound_const_mul
    (c : ℝ) {f : ℝ → ℝ} (hf : HasP024IocAbsBound f) :
    HasP024IocAbsBound (fun x ↦ c * f x) := by
  obtain ⟨B, hB, hf⟩ := hf
  refine ⟨|c| * B + 1, by positivity, ?_⟩
  intro x hx
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left (hf x hx) (abs_nonneg c)).trans
    (le_add_of_nonneg_right (by norm_num))

private theorem hasP024IocAbsBound_of_continuous
    (f : ℝ → ℝ) (hf : Continuous f) : HasP024IocAbsBound f := by
  obtain ⟨B, hB, hbound⟩ := exists_abs_bound_of_continuousOn_Icc f hf.continuousOn
  exact ⟨B, hB, fun x hx ↦ hbound x ⟨hx.1.le, hx.2⟩⟩

/-- The endpoint-potential pole has been removed exactly from each base
selector row, leaving a uniformly bounded remainder. -/
theorem exists_retainedP024SelectorBaseRemainder_abs_bound (i : Fin 3) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ Ioc (-1 : ℝ) 1,
      |retainedP024SelectorBaseRemainder i x| ≤ B := by
  have hclean : HasP024IocAbsBound (fun x ↦
      factorTwoIntrinsicElevenCleanSurvivorRepresenter
          (retainedP024EvenMode i) x -
        yoshidaEndpointPotential x *
          centeredPolynomialLift (retainedP024EvenMode i) x) :=
    exists_cleanSurvivor_sub_potential_abs_bound (retainedP024EvenMode i)
  have hpoly : HasP024IocAbsBound
      (centeredPolynomialLift (retainedP024SelectorBasePolynomial i)) :=
    exists_centeredPolynomialLift_abs_bound _
  simpa only [retainedP024SelectorBaseRemainder] using
    hasP024IocAbsBound_sub hclean hpoly

/-- Every symmetric retained P024 remainder is uniformly bounded after its
constant endpoint trace has been extracted. -/
theorem exists_retainedP024SelectorSymmetricRemainder_abs_bound (i : Fin 3) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ Ioc (-1 : ℝ) 1,
      |retainedP024SelectorSymmetricRemainder i x| ≤ B := by
  have hA : HasP024IocAbsBound
      (factorTwoIntrinsicElevenAnalyticEvenRepresenter
        (retainedP024EvenMode i) 0 1 0) :=
    exists_analyticEvenRepresenter_abs_bound _ _ _ _
  have hF : HasP024IocAbsBound
      (factorTwoIntrinsicElevenForwardEvenRepresenter
        (retainedP024EvenMode i) 0 1 0) :=
    exists_forwardEvenRepresenter_abs_bound _ _ _ _
  have hP : HasP024IocAbsBound
      (factorTwoIntrinsicElevenPrimeEvenRepresenter
        (retainedP024EvenMode i) 0 1 0) :=
    exists_primeEvenRepresenter_abs_bound _ _ _ _
  have hpoly : HasP024IocAbsBound (centeredPolynomialLift
      (retainedP024SymmetricSelector
        (![retainedP024SelectorPlus0, retainedP024SelectorPlus2,
          retainedP024SelectorPlus4] i)
        (![retainedP024SelectorMinus0, retainedP024SelectorMinus2,
          retainedP024SelectorMinus4] i))) :=
    exists_centeredPolynomialLift_abs_bound _
  have htrace : HasP024IocAbsBound
      (retainedP024KPotentialTraceRemainder i) :=
    hasP024IocAbsBound_of_continuous _
      (continuous_retainedP024KPotentialTraceRemainder i)
  have hentropy : HasP024IocAbsBound
      (reflectedPoleKEntropyRemainder (retainedP024EvenMode i)) :=
    hasP024IocAbsBound_of_continuous _
      (continuous_reflectedPoleKEntropyRemainder _)
  have hsum := hasP024IocAbsBound_add
    (hasP024IocAbsBound_add hA hF) hP
  have hcontinuous := hasP024IocAbsBound_const_mul (511 / 2048 : ℝ)
    (hasP024IocAbsBound_add htrace hentropy)
  simpa only [retainedP024SelectorSymmetricRemainder] using
    hasP024IocAbsBound_sub
      (hasP024IocAbsBound_sub hsum hpoly) hcontinuous

/-- Every alternating retained P024 remainder is uniformly bounded after
its linear endpoint trace has been extracted. -/
theorem exists_retainedP024SelectorAlternatingRemainder_abs_bound (i : Fin 3) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ Ioc (-1 : ℝ) 1,
      |retainedP024SelectorAlternatingRemainder i x| ≤ B := by
  have hA : HasP024IocAbsBound
      (factorTwoIntrinsicElevenAnalyticOddRepresenter
        (retainedP024EvenMode i) 0 0 1) :=
    exists_analyticOddRepresenter_abs_bound _ _ _ _
  have hF : HasP024IocAbsBound
      (factorTwoIntrinsicElevenForwardOddRepresenter
        (retainedP024EvenMode i) 0 0 1) :=
    exists_forwardOddRepresenter_abs_bound _ _ _ _
  have hP : HasP024IocAbsBound
      (factorTwoIntrinsicElevenPrimeOddRepresenter
        (retainedP024EvenMode i) 0 0 1) :=
    exists_primeOddRepresenter_abs_bound _ _ _ _
  have hpoly : HasP024IocAbsBound
      (centeredPolynomialLift (retainedP024SelectorAlternatingPolynomial i)) :=
    exists_centeredPolynomialLift_abs_bound _
  have htrace : HasP024IocAbsBound
      (retainedP024JPotentialTraceRemainder i) :=
    hasP024IocAbsBound_of_continuous _
      (continuous_retainedP024JPotentialTraceRemainder i)
  have hentropy : HasP024IocAbsBound
      (reflectedPoleJEntropyRemainder (retainedP024EvenMode i)) :=
    hasP024IocAbsBound_of_continuous _
      (continuous_reflectedPoleJEntropyRemainder _)
  have hsum := hasP024IocAbsBound_add
    (hasP024IocAbsBound_add hA hF) hP
  have hcontinuous := hasP024IocAbsBound_const_mul (511 / 2048 : ℝ)
    (hasP024IocAbsBound_add htrace hentropy)
  simpa only [retainedP024SelectorAlternatingRemainder] using
    hasP024IocAbsBound_sub
      (hasP024IocAbsBound_sub hsum hpoly) hcontinuous

/-- Every combined even remainder row is uniformly bounded. -/
theorem exists_retainedP024SelectorWholeEvenRemainder_abs_bound
    (k : Fin 3 ⊕ Fin 3) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ Ioc (-1 : ℝ) 1,
      |retainedP024SelectorWholeEvenRemainder k x| ≤ B := by
  rcases k with i | i
  · simpa only [retainedP024SelectorWholeEvenRemainder] using
      exists_retainedP024SelectorBaseRemainder_abs_bound i
  · simpa only [retainedP024SelectorWholeEvenRemainder] using
      exists_retainedP024SelectorSymmetricRemainder_abs_bound i

/-- Subtracting any fixed multiple of the even pole row preserves uniform
boundedness of the extracted remainder. -/
theorem exists_retainedP024SelectorWholeEvenRemainder_sub_pole_abs_bound
    (c : ℝ) (k : Fin 3 ⊕ Fin 3) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ Ioc (-1 : ℝ) 1,
      |retainedP024SelectorWholeEvenRemainder k x -
        c * retainedP024SelectorWholeEvenPoleRow k x| ≤ B := by
  have hrem : HasP024IocAbsBound
      (retainedP024SelectorWholeEvenRemainder k) :=
    exists_retainedP024SelectorWholeEvenRemainder_abs_bound k
  have hpole : HasP024IocAbsBound
      (retainedP024SelectorWholeEvenPoleRow k) := by
    apply hasP024IocAbsBound_of_continuous
    rcases k with i | i
    · simp only [retainedP024SelectorWholeEvenPoleRow]
      unfold retainedP024EvenMode centeredPolynomialLift
      fun_prop
    · simp only [retainedP024SelectorWholeEvenPoleRow]
      fun_prop
  exact hasP024IocAbsBound_sub hrem
    (hasP024IocAbsBound_const_mul c hpole)

/-- Subtracting any fixed multiple of the alternating pole row preserves
uniform boundedness of the extracted remainder. -/
theorem exists_retainedP024SelectorAlternatingRemainder_sub_pole_abs_bound
    (c : ℝ) (i : Fin 3) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ Ioc (-1 : ℝ) 1,
      |retainedP024SelectorAlternatingRemainder i x -
        c * retainedP024SelectorAlternatingPoleRow i x| ≤ B := by
  have hrem : HasP024IocAbsBound
      (retainedP024SelectorAlternatingRemainder i) :=
    exists_retainedP024SelectorAlternatingRemainder_abs_bound i
  have hpole : HasP024IocAbsBound
      (retainedP024SelectorAlternatingPoleRow i) :=
    hasP024IocAbsBound_of_continuous _ (by
      unfold retainedP024SelectorAlternatingPoleRow
      fun_prop)
  exact hasP024IocAbsBound_sub hrem
    (hasP024IocAbsBound_const_mul c hpole)

/-- Exact endpoint-trace pole extraction for every row of the combined
retained-even residual Gram.  The identity is stated on the open interval
because the raw logarithmic selectors use Lean's value `log 0 = 0` at the
two measure-zero endpoints. -/
theorem retainedP024SelectorWholeEvenResidual_eq_pole_add_remainder
    (k : Fin 3 ⊕ Fin 3) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    factorTwoIntrinsicElevenSelectorResidual
        (retainedP024SelectorWholeEvenRepresenter k)
        (retainedP024SelectorWholeEvenPolynomial k) x =
      retainedP024PoleSlope * yoshidaEndpointPotential x *
          retainedP024SelectorWholeEvenPoleRow k x +
        retainedP024SelectorWholeEvenRemainder k x := by
  rcases k with i | i
  · simp only [retainedP024SelectorWholeEvenRepresenter,
      retainedP024SelectorWholeEvenPolynomial,
      retainedP024SelectorWholeEvenPoleRow,
      retainedP024SelectorWholeEvenRemainder]
    unfold
      retainedP024SelectorBaseRemainder retainedP024PoleSlope
      retainedP024EvenMode
      retainedEvenBaseRepresenterAt
      factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
      factorTwoIntrinsicElevenPotentialPoleEvenRepresenter
      factorTwoIntrinsicElevenEvenMixedRepresenter
      factorTwoIntrinsicElevenAnalyticEvenRepresenter
      factorTwoIntrinsicElevenForwardEvenRepresenter
      factorTwoIntrinsicElevenReflectedEvenRepresenter
      factorTwoIntrinsicElevenPrimeEvenRepresenter
      factorTwoIntrinsicElevenSelectorResidual
    simp [centeredPolynomialLift, reflectedPoleKLogSelector,
      reflectedPoleJLogSelector, forwardPoleKLogSelector,
      forwardPoleLLogSelector]
    ring
  · simp only [retainedP024SelectorWholeEvenRepresenter,
      retainedP024SelectorWholeEvenPolynomial,
      retainedP024SelectorWholeEvenPoleRow,
      retainedP024SelectorWholeEvenRemainder]
    unfold retainedP024SelectorSymmetricRemainder
    rw [retainedP024KPotentialTraceRemainder_eq]
    unfold retainedP024PoleSlope
      retainedEvenSymmetricRepresenterAt retainedEvenBaseRepresenterAt
      factorTwoIntrinsicElevenRetainedEvenMixedRepresenterAt
      factorTwoIntrinsicElevenPotentialPoleEvenRepresenter
      factorTwoIntrinsicElevenEvenMixedRepresenter
      factorTwoIntrinsicElevenReflectedEvenRepresenter
      factorTwoIntrinsicElevenSelectorResidual retainedP024EvenMode
    dsimp only
    rw [reflectedPoleKLogSelector_eq_potential_add_entropy
        (shiftedLegendreReal (2 * i.1)) hx]
    unfold factorTwoIntrinsicElevenAnalyticEvenRepresenter
      factorTwoIntrinsicElevenForwardEvenRepresenter
      factorTwoIntrinsicElevenPrimeEvenRepresenter
    ring

/-- Exact endpoint-trace pole extraction for every alternating retained-odd
selector row. -/
theorem retainedP024SelectorAlternatingResidual_eq_pole_add_remainder
    (i : Fin 3) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    factorTwoIntrinsicElevenSelectorResidual
        (retainedOddAlternatingRepresenterAt
          (1 / 512 : ℝ) (retainedP024EvenMode i))
        (retainedP024SelectorAlternatingPolynomial i) x =
      retainedP024PoleSlope * yoshidaEndpointPotential x *
          retainedP024SelectorAlternatingPoleRow i x +
        retainedP024SelectorAlternatingRemainder i x := by
  unfold retainedP024SelectorAlternatingPoleRow
    retainedP024SelectorAlternatingRemainder
  rw [retainedP024JPotentialTraceRemainder_eq]
  unfold
    retainedOddAlternatingRepresenterAt
    retainedP024PoleSlope
    factorTwoIntrinsicElevenRetainedOddMixedRepresenterAt
    factorTwoIntrinsicElevenPotentialPoleOddRepresenter
    factorTwoIntrinsicElevenOddMixedRepresenter
    factorTwoIntrinsicElevenReflectedOddRepresenter
    factorTwoIntrinsicElevenSelectorResidual retainedP024EvenMode
  dsimp only
  rw [reflectedPoleJLogSelector_eq_potential_add_entropy
      (shiftedLegendreReal (2 * i.1)) hx,
    factorTwoIntrinsicElevenCleanSurvivorRepresenter_zero]
  simp [centeredPolynomialLift]
  ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorPoleRemainderStructural
