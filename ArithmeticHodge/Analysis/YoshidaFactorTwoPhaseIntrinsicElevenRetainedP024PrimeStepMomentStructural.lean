import ArithmeticHodge.Analysis.YoshidaEndpointPotentialPolynomialPrefixStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024PrimeStepStructural

set_option autoImplicit false

open Finset MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024PrimeStepMomentStructural

open ShiftedLegendreCenteredLowModes
open ShiftedLegendreLogEnergyOrthogonalProjection
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialPolynomialPrefixStructural
open YoshidaFactorTwoPhaseEnvelope
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024PrimeStepStructural

noncomputable section

/-!
# Exact retained-prime step moments

Parity and the disjoint endpoint supports fold every retained prime-step
pairing to one polynomial prefix integral.  The resulting formulas are
all-degree in the polynomial factor and use the structural prefix-moment
functional; no matrix entry or polynomial degree is enumerated.
-/

/-- The retained odd-channel affine endpoint weight, kept cycle-free from
the downstream selector modules. -/
def retainedPrimeOddWeight (x : ℝ) : ℝ :=
  1 / 30 + (63 / 128 : ℝ) * yoshidaEndpointPotential x

/-- The negative endpoint cutoff of the retained prime step. -/
def retainedPrimeCutoff : ℝ :=
  1 - retainedPrimeLag

/-- Polynomial carried by retained step row `i` on the negative endpoint
piece. -/
def retainedPrimeNegativeStepPolynomial (i : Fin 3) : ℝ[X] :=
  (centeredShiftedLegendreReal (2 * i.1)).comp
    (X + C retainedPrimeLag)

theorem retainedPrimeCutoff_mem_neg_one_zero :
    retainedPrimeCutoff ∈ Icc (-1 : ℝ) 0 := by
  have hτ := factorTwoPrimeShift_div_endpointA_mem_one_two
  unfold retainedPrimeCutoff retainedPrimeLag
  constructor <;> linarith [hτ.1, hτ.2]

theorem retainedPrimeCutoff_mem_neg_one_one :
    retainedPrimeCutoff ∈ Icc (-1 : ℝ) 1 :=
  ⟨retainedPrimeCutoff_mem_neg_one_zero.1,
    retainedPrimeCutoff_mem_neg_one_zero.2.trans (by norm_num)⟩

/-- The retained affine odd weight is even. -/
theorem even_retainedPrimeOddWeight :
    Function.Even retainedPrimeOddWeight := by
  intro x
  simp only [retainedPrimeOddWeight, yoshidaEndpointPotential, neg_sq]

/-- Evaluation of the negative-support polynomial agrees with the translated
step piece. -/
theorem eval_retainedPrimeNegativeStepPolynomial
    (i : Fin 3) (x : ℝ) :
    (retainedPrimeNegativeStepPolynomial i).eval x =
      retainedP024PrimeStepPolynomial i (retainedPrimeLag + x) := by
  rw [← centeredPolynomialLift_retainedP024EvenMode]
  unfold retainedPrimeNegativeStepPolynomial
  rw [Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C,
    eval_centeredShiftedLegendreReal]
  unfold centeredPolynomialLift retainedPrimeEvenMode
  congr 1
  ring

/-- Restricting an interval-integrable function by a measurable prefix
preserves interval integrability. -/
theorem intervalIntegrable_indicator_Iic
    {g : ℝ → ℝ} {a u c : ℝ}
    (hg : IntervalIntegrable g volume a u) :
    IntervalIntegrable ({x : ℝ | x ≤ c}.indicator g) volume a u := by
  apply hg.mono_fun
  · exact hg.def'.aestronglyMeasurable.indicator measurableSet_Iic
  · filter_upwards [] with x
    by_cases hx : x ≤ c <;> simp [hx]

/-- An even interval-integrable profile folds from `[-1,1]` to twice its
negative half. -/
theorem integral_neg_one_one_eq_two_mul_neg_one_zero_of_even
    (f : ℝ → ℝ) (hf : IntervalIntegrable f volume (-1) 0)
    (heven : Function.Even f) :
    (∫ x : ℝ in -1..1, f x) = 2 * ∫ x : ℝ in -1..0, f x := by
  have hcomp : IntervalIntegrable (fun x : ℝ ↦ f (-x)) volume 0 1 := by
    simpa only [neg_zero, neg_neg] using
      ((IntervalIntegrable.iff_comp_neg (f := f) (a := (-1 : ℝ))
        (b := 0)).mp hf).symm
  have hpos : IntervalIntegrable f volume 0 1 := by
    apply hcomp.congr
    intro x _hx
    exact heven x
  have hreflect :
      (∫ x : ℝ in 0..1, f (-x)) = ∫ x : ℝ in -1..0, f x := by
    convert intervalIntegral.integral_comp_neg
      (f := f) (a := (0 : ℝ)) (b := 1) using 1;
    norm_num
  have hposEq :
      (∫ x : ℝ in 0..1, f x) = ∫ x : ℝ in -1..0, f x := by
    rw [← hreflect]
    apply intervalIntegral.integral_congr
    intro x _hx
    exact (heven x).symm
  rw [(intervalIntegral.integral_add_adjacent_intervals hf hpos).symm,
    hposEq]
  ring

/-- Pointwise cutoff-indicator form of a polynomial-step integrand on the
negative half interval. -/
theorem retainedPrimePolynomialStep_eq_cutoffIndicator
    (p : ℝ[X]) (i : Fin 3) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 0) :
    retainedPrimeOddWeight x * p.eval x * retainedPrimeOddStepRow i x =
      ({y : ℝ | y ≤ retainedPrimeCutoff}.indicator
        (fun y ↦ retainedPrimeOddWeight y *
          (p * retainedPrimeNegativeStepPolynomial i).eval y)) x := by
  rw [retainedP024OddPrimeStepRow_eq_indicator_of_nonpos i hx.2]
  by_cases hmem : x ∈ Icc (-1 : ℝ) retainedPrimeCutoff
  · have hmem' : x ∈ Icc (-1 : ℝ) (1 - retainedPrimeLag) := by
      simpa only [retainedPrimeCutoff] using hmem
    have hle : x ∈ {y : ℝ | y ≤ retainedPrimeCutoff} := hmem.2
    rw [Set.indicator_of_mem hmem', Set.indicator_of_mem hle,
      Polynomial.eval_mul, eval_retainedPrimeNegativeStepPolynomial]
    ring
  · have hnle : ¬x ≤ retainedPrimeCutoff := by
      intro hle
      exact hmem ⟨hx.1, hle⟩
    have hmem' : x ∉ Icc (-1 : ℝ) (1 - retainedPrimeLag) := by
      simpa only [retainedPrimeCutoff] using hmem
    have hnle' : x ∉ {y : ℝ | y ≤ retainedPrimeCutoff} := hnle
    rw [Set.indicator_of_notMem hmem',
      Set.indicator_of_notMem hnle', mul_zero]

/-- Pointwise cutoff-indicator form of a step-step integrand on the negative
half interval. -/
theorem retainedPrimeStepStep_eq_cutoffIndicator
    (i j : Fin 3) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 0) :
    retainedPrimeOddWeight x * retainedPrimeOddStepRow i x *
        retainedPrimeOddStepRow j x =
      ({y : ℝ | y ≤ retainedPrimeCutoff}.indicator
        (fun y ↦ retainedPrimeOddWeight y *
          (retainedPrimeNegativeStepPolynomial i *
            retainedPrimeNegativeStepPolynomial j).eval y)) x := by
  rw [retainedP024OddPrimeStepRow_eq_indicator_of_nonpos i hx.2,
    retainedP024OddPrimeStepRow_eq_indicator_of_nonpos j hx.2]
  by_cases hmem : x ∈ Icc (-1 : ℝ) retainedPrimeCutoff
  · have hmem' : x ∈ Icc (-1 : ℝ) (1 - retainedPrimeLag) := by
      simpa only [retainedPrimeCutoff] using hmem
    have hle : x ∈ {y : ℝ | y ≤ retainedPrimeCutoff} := hmem.2
    rw [Set.indicator_of_mem hmem', Set.indicator_of_mem hmem',
      Set.indicator_of_mem hle, Polynomial.eval_mul,
      eval_retainedPrimeNegativeStepPolynomial,
      eval_retainedPrimeNegativeStepPolynomial]
    ring
  · have hnle : ¬x ≤ retainedPrimeCutoff := by
      intro hle
      exact hmem ⟨hx.1, hle⟩
    have hmem' : x ∉ Icc (-1 : ℝ) (1 - retainedPrimeLag) := by
      simpa only [retainedPrimeCutoff] using hmem
    have hnle' : x ∉ {y : ℝ | y ≤ retainedPrimeCutoff} := hnle
    rw [Set.indicator_of_notMem hmem',
      Set.indicator_of_notMem hmem',
      Set.indicator_of_notMem hnle']
    ring

/-- Polynomial-step integrands are interval-integrable on the negative
half. -/
theorem intervalIntegrable_retainedPrimeOddWeight_mul_eval_mul_step_neg_half
    (p : ℝ[X]) (i : Fin 3) :
    IntervalIntegrable
      (fun x : ℝ ↦ retainedPrimeOddWeight x * p.eval x *
        retainedPrimeOddStepRow i x)
      volume (-1) 0 := by
  let g : ℝ → ℝ := fun x ↦ retainedPrimeOddWeight x *
    (p * retainedPrimeNegativeStepPolynomial i).eval x
  have hg : IntervalIntegrable g volume (-1) 0 := by
    simpa only [g, retainedPrimeOddWeight] using
      intervalIntegrable_affineEndpointPotential_mul_eval
        (1 / 30) (63 / 128)
        (p * retainedPrimeNegativeStepPolynomial i)
        (by norm_num : (0 : ℝ) ∈ Icc (-1 : ℝ) 1)
  have hInd := intervalIntegrable_indicator_Iic
    (c := retainedPrimeCutoff) hg
  apply hInd.congr
  intro x hx
  have hxIcc : x ∈ Icc (-1 : ℝ) 0 := by
    have hx' := Set.uIoc_subset_uIcc hx
    simpa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] using hx'
  exact (retainedPrimePolynomialStep_eq_cutoffIndicator p i hxIcc).symm

/-- Step-step integrands are interval-integrable on the negative half. -/
theorem intervalIntegrable_retainedPrimeOddWeight_mul_step_mul_step_neg_half
    (i j : Fin 3) :
    IntervalIntegrable
      (fun x : ℝ ↦ retainedPrimeOddWeight x *
        retainedPrimeOddStepRow i x * retainedPrimeOddStepRow j x)
      volume (-1) 0 := by
  let g : ℝ → ℝ := fun x ↦ retainedPrimeOddWeight x *
    (retainedPrimeNegativeStepPolynomial i *
      retainedPrimeNegativeStepPolynomial j).eval x
  have hg : IntervalIntegrable g volume (-1) 0 := by
    simpa only [g, retainedPrimeOddWeight] using
      intervalIntegrable_affineEndpointPotential_mul_eval
        (1 / 30) (63 / 128)
        (retainedPrimeNegativeStepPolynomial i *
          retainedPrimeNegativeStepPolynomial j)
        (by norm_num : (0 : ℝ) ∈ Icc (-1 : ℝ) 1)
  have hInd := intervalIntegrable_indicator_Iic
    (c := retainedPrimeCutoff) hg
  apply hInd.congr
  intro x hx
  have hxIcc : x ∈ Icc (-1 : ℝ) 0 := by
    have hx' := Set.uIoc_subset_uIcc hx
    simpa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] using hx'
  exact (retainedPrimeStepStep_eq_cutoffIndicator i j hxIcc).symm

/-- On the negative half, an odd-channel polynomial-step pairing is exactly
one retained-weight polynomial prefix functional. -/
theorem integral_retainedPrimeOddWeight_mul_eval_mul_step_neg_half
    (p : ℝ[X]) (i : Fin 3) :
    (∫ x : ℝ in -1..0,
      retainedPrimeOddWeight x * p.eval x *
        retainedPrimeOddStepRow i x) =
      affineEndpointPotentialPolynomialPrefixIntegral
        (1 / 30) (63 / 128)
        (p * retainedPrimeNegativeStepPolynomial i)
        retainedPrimeCutoff := by
  let g : ℝ → ℝ := fun x ↦
    retainedPrimeOddWeight x *
      (p * retainedPrimeNegativeStepPolynomial i).eval x
  have hpoint : EqOn
      (fun x : ℝ ↦ retainedPrimeOddWeight x * p.eval x *
        retainedPrimeOddStepRow i x)
      ({x : ℝ | x ≤ retainedPrimeCutoff}.indicator g)
      (Set.uIcc (-1 : ℝ) 0) := by
    intro x hx
    have hxIcc : x ∈ Icc (-1 : ℝ) 0 := by
      simpa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] using hx
    simpa only [g] using
      retainedPrimePolynomialStep_eq_cutoffIndicator p i hxIcc
  rw [intervalIntegral.integral_congr hpoint,
    intervalIntegral.integral_indicator retainedPrimeCutoff_mem_neg_one_zero]
  exact integral_affineEndpointPotential_mul_eval_eq_prefixIntegral
    (1 / 30) (63 / 128)
    (p * retainedPrimeNegativeStepPolynomial i)
    retainedPrimeCutoff_mem_neg_one_one

/-- On the negative half, a step-step pairing is exactly one retained-weight
polynomial prefix functional. -/
theorem integral_retainedPrimeOddWeight_mul_step_mul_step_neg_half
    (i j : Fin 3) :
    (∫ x : ℝ in -1..0,
      retainedPrimeOddWeight x * retainedPrimeOddStepRow i x *
        retainedPrimeOddStepRow j x) =
      affineEndpointPotentialPolynomialPrefixIntegral
        (1 / 30) (63 / 128)
        (retainedPrimeNegativeStepPolynomial i *
          retainedPrimeNegativeStepPolynomial j)
        retainedPrimeCutoff := by
  let g : ℝ → ℝ := fun x ↦
    retainedPrimeOddWeight x *
      (retainedPrimeNegativeStepPolynomial i *
        retainedPrimeNegativeStepPolynomial j).eval x
  have hpoint : EqOn
      (fun x : ℝ ↦ retainedPrimeOddWeight x *
        retainedPrimeOddStepRow i x * retainedPrimeOddStepRow j x)
      ({x : ℝ | x ≤ retainedPrimeCutoff}.indicator g)
      (Set.uIcc (-1 : ℝ) 0) := by
    intro x hx
    have hxIcc : x ∈ Icc (-1 : ℝ) 0 := by
      simpa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] using hx
    simpa only [g] using
      retainedPrimeStepStep_eq_cutoffIndicator i j hxIcc
  rw [intervalIntegral.integral_congr hpoint,
    intervalIntegral.integral_indicator retainedPrimeCutoff_mem_neg_one_zero]
  exact integral_affineEndpointPotential_mul_eval_eq_prefixIntegral
    (1 / 30) (63 / 128)
    (retainedPrimeNegativeStepPolynomial i *
      retainedPrimeNegativeStepPolynomial j)
    retainedPrimeCutoff_mem_neg_one_one

/-- Every odd polynomial against a retained prime step has one exact full
interval prefix-functional formula. -/
theorem integral_retainedPrimeOddWeight_mul_eval_mul_step
    (p : ℝ[X]) (hp : Function.Odd (fun x : ℝ ↦ p.eval x))
    (i : Fin 3) :
    (∫ x : ℝ in -1..1,
      retainedPrimeOddWeight x * p.eval x *
        retainedPrimeOddStepRow i x) =
      2 * affineEndpointPotentialPolynomialPrefixIntegral
        (1 / 30) (63 / 128)
        (p * retainedPrimeNegativeStepPolynomial i)
        retainedPrimeCutoff := by
  let f : ℝ → ℝ := fun x ↦ retainedPrimeOddWeight x * p.eval x *
    retainedPrimeOddStepRow i x
  have hf : IntervalIntegrable f volume (-1) 0 :=
    intervalIntegrable_retainedPrimeOddWeight_mul_eval_mul_step_neg_half p i
  have hfeven : Function.Even f := by
    intro x
    have hpneg : p.eval (-x) = -p.eval x := hp x
    dsimp only [f]
    rw [even_retainedPrimeOddWeight x, hpneg,
      odd_retainedPrimeOddStepRow i x]
    ring
  change (∫ x : ℝ in -1..1, f x) = _
  rw [integral_neg_one_one_eq_two_mul_neg_one_zero_of_even f hf hfeven]
  change 2 * (∫ x : ℝ in -1..0,
    retainedPrimeOddWeight x * p.eval x *
      retainedPrimeOddStepRow i x) = _
  rw [integral_retainedPrimeOddWeight_mul_eval_mul_step_neg_half]

/-- Every pair of retained prime steps has one exact full-interval
prefix-functional formula. -/
theorem integral_retainedPrimeOddWeight_mul_step_mul_step
    (i j : Fin 3) :
    (∫ x : ℝ in -1..1,
      retainedPrimeOddWeight x * retainedPrimeOddStepRow i x *
        retainedPrimeOddStepRow j x) =
      2 * affineEndpointPotentialPolynomialPrefixIntegral
        (1 / 30) (63 / 128)
        (retainedPrimeNegativeStepPolynomial i *
          retainedPrimeNegativeStepPolynomial j)
        retainedPrimeCutoff := by
  let f : ℝ → ℝ := fun x ↦ retainedPrimeOddWeight x *
    retainedPrimeOddStepRow i x * retainedPrimeOddStepRow j x
  have hf : IntervalIntegrable f volume (-1) 0 :=
    intervalIntegrable_retainedPrimeOddWeight_mul_step_mul_step_neg_half i j
  have hfeven : Function.Even f := by
    intro x
    dsimp only [f]
    rw [even_retainedPrimeOddWeight x,
      odd_retainedPrimeOddStepRow i x,
      odd_retainedPrimeOddStepRow j x]
    ring
  change (∫ x : ℝ in -1..1, f x) = _
  rw [integral_neg_one_one_eq_two_mul_neg_one_zero_of_even f hf hfeven]
  change 2 * (∫ x : ℝ in -1..0,
    retainedPrimeOddWeight x * retainedPrimeOddStepRow i x *
      retainedPrimeOddStepRow j x) = _
  rw [integral_retainedPrimeOddWeight_mul_step_mul_step_neg_half]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024PrimeStepMomentStructural
