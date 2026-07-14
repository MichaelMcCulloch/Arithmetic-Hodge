import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteEvenPerturbationFormula
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteOddPerturbationFormula
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteAlternatingFormula

set_option autoImplicit false
set_option maxRecDepth 100000

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcretePerturbationMoments

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaClippedMomentBridge
open YoshidaCoercivityNumerics
open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseAlternatingCoercivity
open YoshidaFactorTwoPhaseConcreteAlternatingFormula
open YoshidaFactorTwoPhaseConcreteEvenPerturbationAdaptation
open YoshidaFactorTwoPhaseConcreteEvenPerturbationFormula
open YoshidaFactorTwoPhaseConcreteLowMatrix
open YoshidaFactorTwoPhaseConcreteOddPerturbationFormula
open YoshidaFactorTwoPhaseEndpointAdaptedLow
open YoshidaWeightedTailBounds

/-!
# Scalar perturbation moments for the concrete factor-two blocks

The three concrete phase blocks use only two real linear functionals.  This
file names those functionals and reduces every trigonometric branch to a
small collection of one-dimensional Fourier moments.  These identities are
intended as the exact interface for interval or rational enclosure code; no
numerical estimate is asserted here.
-/

/-- The complete symmetric perturbation functional, including the retained
`p = 2` and `p = 3` atoms. -/
def factorTwoSymmetricPerturbationFunctional (C : ℝ → ℝ) : ℝ :=
  yoshidaEndpointA *
      (∫ t : ℝ in 0..2,
        factorTwoSymmetricWeight (yoshidaEndpointA * t) * C t) -
    (Real.log 2 / Real.sqrt 2) * C 0 -
    (Real.log 3 / Real.sqrt 3) *
      C (factorTwoPrimeShift / yoshidaEndpointA)

/-- The complete alternating perturbation functional, normalized so that it
acts directly on the ordered even--odd correlation. -/
def factorTwoAntisymmetricPerturbationFunctional (C : ℝ → ℝ) : ℝ :=
  -2 * yoshidaEndpointA *
      (∫ t : ℝ in 0..2,
        factorTwoAntisymmetricWeight (yoshidaEndpointA * t) * C t) +
    2 * (Real.log 3 / Real.sqrt 3) *
      C (factorTwoPrimeShift / yoshidaEndpointA)

theorem factorTwoSymmetricPerturbationFunctional_eq_even
    (C : ℝ → ℝ) :
    factorTwoSymmetricPerturbationFunctional C =
      factorTwoCanonicalEvenPerturbationEntryFormula C := by
  rfl

theorem factorTwoSymmetricPerturbationFunctional_eq_odd
    (C : ℝ → ℝ) :
    factorTwoSymmetricPerturbationFunctional C =
      factorTwoConcreteOddPerturbationEntryFormula C := by
  rfl

@[simp] theorem factorTwoSymmetricPerturbationFunctional_zero :
    factorTwoSymmetricPerturbationFunctional (fun _ ↦ 0) = 0 := by
  simp [factorTwoSymmetricPerturbationFunctional]

@[simp] theorem factorTwoAntisymmetricPerturbationFunctional_zero :
    factorTwoAntisymmetricPerturbationFunctional (fun _ ↦ 0) = 0 := by
  simp [factorTwoAntisymmetricPerturbationFunctional]

/-- Scalar homogeneity of the symmetric functional. -/
theorem factorTwoSymmetricPerturbationFunctional_const_mul
    (c : ℝ) (C : ℝ → ℝ) :
    factorTwoSymmetricPerturbationFunctional (fun t ↦ c * C t) =
      c * factorTwoSymmetricPerturbationFunctional C := by
  unfold factorTwoSymmetricPerturbationFunctional
  rw [show (fun t : ℝ ↦
      factorTwoSymmetricWeight (yoshidaEndpointA * t) * (c * C t)) =
      fun t ↦ c *
        (factorTwoSymmetricWeight (yoshidaEndpointA * t) * C t) by
    funext t
    ring,
    intervalIntegral.integral_const_mul]
  ring

/-- Scalar homogeneity of the antisymmetric functional. -/
theorem factorTwoAntisymmetricPerturbationFunctional_const_mul
    (c : ℝ) (C : ℝ → ℝ) :
    factorTwoAntisymmetricPerturbationFunctional (fun t ↦ c * C t) =
      c * factorTwoAntisymmetricPerturbationFunctional C := by
  unfold factorTwoAntisymmetricPerturbationFunctional
  rw [show (fun t : ℝ ↦
      factorTwoAntisymmetricWeight (yoshidaEndpointA * t) * (c * C t)) =
      fun t ↦ c *
        (factorTwoAntisymmetricWeight (yoshidaEndpointA * t) * C t) by
    funext t
    ring,
    intervalIntegral.integral_const_mul]
  ring

/-- Additivity on the natural interval-integrable domain. -/
theorem factorTwoSymmetricPerturbationFunctional_add
    (C D : ℝ → ℝ)
    (hC : IntervalIntegrable
      (fun t ↦ factorTwoSymmetricWeight (yoshidaEndpointA * t) * C t)
      volume 0 2)
    (hD : IntervalIntegrable
      (fun t ↦ factorTwoSymmetricWeight (yoshidaEndpointA * t) * D t)
      volume 0 2) :
    factorTwoSymmetricPerturbationFunctional (fun t ↦ C t + D t) =
      factorTwoSymmetricPerturbationFunctional C +
        factorTwoSymmetricPerturbationFunctional D := by
  unfold factorTwoSymmetricPerturbationFunctional
  rw [show (fun t : ℝ ↦
      factorTwoSymmetricWeight (yoshidaEndpointA * t) * (C t + D t)) =
      fun t ↦
        factorTwoSymmetricWeight (yoshidaEndpointA * t) * C t +
          factorTwoSymmetricWeight (yoshidaEndpointA * t) * D t by
    funext t
    ring,
    intervalIntegral.integral_add hC hD]
  ring

/-- Additivity on the natural interval-integrable domain. -/
theorem factorTwoAntisymmetricPerturbationFunctional_add
    (C D : ℝ → ℝ)
    (hC : IntervalIntegrable
      (fun t ↦ factorTwoAntisymmetricWeight (yoshidaEndpointA * t) * C t)
      volume 0 2)
    (hD : IntervalIntegrable
      (fun t ↦ factorTwoAntisymmetricWeight (yoshidaEndpointA * t) * D t)
      volume 0 2) :
    factorTwoAntisymmetricPerturbationFunctional (fun t ↦ C t + D t) =
      factorTwoAntisymmetricPerturbationFunctional C +
        factorTwoAntisymmetricPerturbationFunctional D := by
  unfold factorTwoAntisymmetricPerturbationFunctional
  rw [show (fun t : ℝ ↦
      factorTwoAntisymmetricWeight (yoshidaEndpointA * t) * (C t + D t)) =
      fun t ↦
        factorTwoAntisymmetricWeight (yoshidaEndpointA * t) * C t +
          factorTwoAntisymmetricWeight (yoshidaEndpointA * t) * D t by
    funext t
    ring,
    intervalIntegral.integral_add hC hD]
  ring

theorem factorTwoSymmetricPerturbationFunctional_sub
    (C D : ℝ → ℝ)
    (hC : IntervalIntegrable
      (fun t ↦ factorTwoSymmetricWeight (yoshidaEndpointA * t) * C t)
      volume 0 2)
    (hD : IntervalIntegrable
      (fun t ↦ factorTwoSymmetricWeight (yoshidaEndpointA * t) * D t)
      volume 0 2) :
    factorTwoSymmetricPerturbationFunctional (fun t ↦ C t - D t) =
      factorTwoSymmetricPerturbationFunctional C -
        factorTwoSymmetricPerturbationFunctional D := by
  unfold factorTwoSymmetricPerturbationFunctional
  rw [show (fun t : ℝ ↦
      factorTwoSymmetricWeight (yoshidaEndpointA * t) * (C t - D t)) =
      fun t ↦
        factorTwoSymmetricWeight (yoshidaEndpointA * t) * C t -
          factorTwoSymmetricWeight (yoshidaEndpointA * t) * D t by
    funext t
    ring,
    intervalIntegral.integral_sub hC hD]
  ring

theorem factorTwoAntisymmetricPerturbationFunctional_sub
    (C D : ℝ → ℝ)
    (hC : IntervalIntegrable
      (fun t ↦ factorTwoAntisymmetricWeight (yoshidaEndpointA * t) * C t)
      volume 0 2)
    (hD : IntervalIntegrable
      (fun t ↦ factorTwoAntisymmetricWeight (yoshidaEndpointA * t) * D t)
      volume 0 2) :
    factorTwoAntisymmetricPerturbationFunctional (fun t ↦ C t - D t) =
      factorTwoAntisymmetricPerturbationFunctional C -
        factorTwoAntisymmetricPerturbationFunctional D := by
  unfold factorTwoAntisymmetricPerturbationFunctional
  rw [show (fun t : ℝ ↦
      factorTwoAntisymmetricWeight (yoshidaEndpointA * t) * (C t - D t)) =
      fun t ↦
        factorTwoAntisymmetricWeight (yoshidaEndpointA * t) * C t -
          factorTwoAntisymmetricWeight (yoshidaEndpointA * t) * D t by
    funext t
    ring,
    intervalIntegral.integral_sub hC hD]
  ring

/-- The common integer Fourier frequency. -/
def factorTwoNaturalFrequency (n : ℕ) : ℝ := Real.pi * (n : ℝ)

theorem factorTwoCanonicalEvenFrequency_eq_natural
    (n : FactorTwoCanonicalEvenIndex) :
    factorTwoCanonicalEvenFrequency n = factorTwoNaturalFrequency n.1 := by
  simp [factorTwoCanonicalEvenFrequency, factorTwoNaturalFrequency,
    YoshidaClippedEvenMomentBridge.clippedEvenFrequency]

/-- Symmetric sine-transform moment. -/
def factorTwoSymmetricSinMoment (n : ℕ) : ℝ :=
  factorTwoSymmetricPerturbationFunctional
    (fun t ↦ Real.sin (factorTwoNaturalFrequency n * t))

/-- Symmetric endpoint-adapted cosine moment. -/
def factorTwoSymmetricAffineCosMoment (n : ℕ) : ℝ :=
  factorTwoSymmetricPerturbationFunctional
    (fun t ↦ (2 - t) * Real.cos (factorTwoNaturalFrequency n * t))

/-- Antisymmetric cosine moment with its endpoint value removed. -/
def factorTwoAntisymmetricOneSubCosMoment (n : ℕ) : ℝ :=
  factorTwoAntisymmetricPerturbationFunctional
    (fun t ↦ 1 - Real.cos (factorTwoNaturalFrequency n * t))

/-- Antisymmetric endpoint-adapted sine moment. -/
def factorTwoAntisymmetricAffineSinMoment (n : ℕ) : ℝ :=
  factorTwoAntisymmetricPerturbationFunctional
    (fun t ↦ (2 - t) * Real.sin (factorTwoNaturalFrequency n * t))

/-- The even diagonal combination is kept together because its two summands
jointly encode one exact correlation branch. -/
def factorTwoSymmetricEvenDiagonalMoment (n : ℕ) : ℝ :=
  factorTwoSymmetricPerturbationFunctional
    (fun t ↦
      (2 - t) * Real.cos (factorTwoNaturalFrequency n * t) -
        Real.sin (factorTwoNaturalFrequency n * t) /
          factorTwoNaturalFrequency n)

/-- The odd diagonal differs from the even diagonal only in the sign of its
sine correction. -/
def factorTwoSymmetricOddDiagonalMoment (n : ℕ) : ℝ :=
  factorTwoSymmetricPerturbationFunctional
    (fun t ↦
      (2 - t) * Real.cos (factorTwoNaturalFrequency n * t) +
        Real.sin (factorTwoNaturalFrequency n * t) /
          factorTwoNaturalFrequency n)

/-- Difference of the two frequency-weighted sine transforms occurring in
the canonical even off-diagonal branch. -/
def factorTwoSymmetricWeightedSinDifferenceMoment (n m : ℕ) : ℝ :=
  factorTwoSymmetricPerturbationFunctional
    (fun t ↦
      factorTwoNaturalFrequency m *
          Real.sin (factorTwoNaturalFrequency m * t) -
        factorTwoNaturalFrequency n *
          Real.sin (factorTwoNaturalFrequency n * t))

/-- Cross-weighted sine transform occurring in the canonical odd
off-diagonal branch. -/
def factorTwoSymmetricCrossSinMoment (n m : ℕ) : ℝ :=
  factorTwoSymmetricPerturbationFunctional
    (fun t ↦
      factorTwoNaturalFrequency n *
          Real.sin (factorTwoNaturalFrequency m * t) -
        factorTwoNaturalFrequency m *
          Real.sin (factorTwoNaturalFrequency n * t))

/-- Difference of two antisymmetric cosine transforms.  Writing it as a
single moment preserves the endpoint cancellation at `t = 2`. -/
def factorTwoAntisymmetricCosDifferenceMoment (n m : ℕ) : ℝ :=
  factorTwoAntisymmetricPerturbationFunctional
    (fun t ↦
      Real.cos (factorTwoNaturalFrequency n * t) -
        Real.cos (factorTwoNaturalFrequency m * t))

theorem factorTwoSymmetricPerturbationFunctional_congr
    {C D : ℝ → ℝ} (h : ∀ t, C t = D t) :
    factorTwoSymmetricPerturbationFunctional C =
      factorTwoSymmetricPerturbationFunctional D := by
  congr 1
  funext t
  exact h t

theorem factorTwoAntisymmetricPerturbationFunctional_congr
    {C D : ℝ → ℝ} (h : ∀ t, C t = D t) :
    factorTwoAntisymmetricPerturbationFunctional C =
      factorTwoAntisymmetricPerturbationFunctional D := by
  congr 1
  funext t
  exact h t

private theorem intervalIntegrable_of_const_mul
    {f : ℝ → ℝ} {c : ℝ} (hc : c ≠ 0)
    (h : IntervalIntegrable (fun t ↦ c * f t) volume 0 2) :
    IntervalIntegrable f volume 0 2 := by
  have h' := h.const_mul c⁻¹
  refine h'.congr ?_
  intro t _ht
  field_simp [hc]

/-- Every explicit canonical even correlation retains the endpoint zero
needed by the singular symmetric weight. -/
theorem intervalIntegrable_factorTwoSymmetric_canonicalEvenFormula
    (n m : FactorTwoCanonicalEvenIndex) :
    IntervalIntegrable
      (fun t ↦ factorTwoSymmetricWeight (yoshidaEndpointA * t) *
        factorTwoCanonicalEvenCorrelationFormula n m t)
      volume 0 2 := by
  have h := intervalIntegrable_factorTwoCenteredSymmetricKernel
    (factorTwoCenteredCanonicalEvenProfile n)
    (factorTwoCenteredCanonicalEvenProfile m)
    (continuous_factorTwoCenteredCanonicalEvenProfile n)
    (continuous_factorTwoCenteredCanonicalEvenProfile m)
  refine h.congr ?_
  intro t ht
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
  change factorTwoSymmetricWeight (yoshidaEndpointA * t) *
      factorTwoCenteredCorrelationBilinear
        (factorTwoCenteredCanonicalEvenProfile n)
        (factorTwoCenteredCanonicalEvenProfile m) t = _
  rw [factorTwoCenteredCorrelationBilinear_canonicalEven_eq_formula
    n m (le_of_lt ht.1) ht.2]

/-- The primitive symmetric sine moment is genuinely interval-integrable
for every positive canonical frequency. -/
theorem intervalIntegrable_factorTwoSymmetricSinMoment
    (n : FactorTwoCanonicalEvenIndex) (hn : n.1 ≠ 0) :
    IntervalIntegrable
      (fun t ↦ factorTwoSymmetricWeight (yoshidaEndpointA * t) *
        Real.sin (factorTwoNaturalFrequency n.1 * t))
      volume 0 2 := by
  let z : FactorTwoCanonicalEvenIndex := ⟨0, by omega⟩
  let c : ℝ := (((-1 : ℝ) ^ (n.1 + 1) /
    (Real.sqrt 2 * factorTwoNaturalFrequency n.1)) / yoshidaA)
  have hw : factorTwoNaturalFrequency n.1 ≠ 0 := by
    unfold factorTwoNaturalFrequency
    exact mul_ne_zero Real.pi_ne_zero (Nat.cast_ne_zero.mpr hn)
  have hc : c ≠ 0 := by
    dsimp only [c]
    exact div_ne_zero
      (div_ne_zero (pow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0))
        (mul_ne_zero (by positivity) hw)) yoshidaA_pos.ne'
  have h := intervalIntegrable_factorTwoSymmetric_canonicalEvenFormula z n
  have hcorr : factorTwoCanonicalEvenCorrelationFormula z n =
      factorTwoCanonicalEvenZeroPositiveCorrelationFormula n := by
    funext t
    simp [factorTwoCanonicalEvenCorrelationFormula, z, hn]
  rw [hcorr] at h
  apply intervalIntegrable_of_const_mul hc
  refine h.congr ?_
  intro t _ht
  unfold factorTwoCanonicalEvenZeroPositiveCorrelationFormula
  rw [factorTwoCanonicalEvenFrequency_eq_natural]
  dsimp only [c]
  field_simp [hw, yoshidaA_pos.ne']

/-- The endpoint-adapted cosine primitive is interval-integrable for every
canonical frequency, including the zero mode. -/
theorem intervalIntegrable_factorTwoSymmetricAffineCosMoment
    (n : FactorTwoCanonicalEvenIndex) :
    IntervalIntegrable
      (fun t ↦ factorTwoSymmetricWeight (yoshidaEndpointA * t) *
        ((2 - t) * Real.cos (factorTwoNaturalFrequency n.1 * t)))
      volume 0 2 := by
  by_cases hn : n.1 = 0
  · have h := intervalIntegrable_factorTwoSymmetric_canonicalEvenFormula n n
    have hcorr : factorTwoCanonicalEvenCorrelationFormula n n =
        factorTwoCanonicalEvenZeroZeroCorrelationFormula := by
      funext t
      simp [factorTwoCanonicalEvenCorrelationFormula, hn]
    rw [hcorr] at h
    apply intervalIntegrable_of_const_mul
      (show (1 / (2 * yoshidaA) : ℝ) ≠ 0 by
        exact div_ne_zero one_ne_zero
          (mul_ne_zero (by norm_num) yoshidaA_pos.ne'))
    refine h.congr ?_
    intro t _ht
    unfold factorTwoCanonicalEvenZeroZeroCorrelationFormula
    rw [hn]
    simp [factorTwoNaturalFrequency]
    ring
  · have hw : factorTwoNaturalFrequency n.1 ≠ 0 := by
      unfold factorTwoNaturalFrequency
      exact mul_ne_zero Real.pi_ne_zero (Nat.cast_ne_zero.mpr hn)
    have h := intervalIntegrable_factorTwoSymmetric_canonicalEvenFormula n n
    have hcorr : factorTwoCanonicalEvenCorrelationFormula n n =
        factorTwoCanonicalEvenDiagonalCorrelationFormula n := by
      funext t
      simp [factorTwoCanonicalEvenCorrelationFormula, hn]
    rw [hcorr] at h
    have hdiff : IntervalIntegrable
        (fun t ↦ factorTwoSymmetricWeight (yoshidaEndpointA * t) *
          ((2 - t) * Real.cos (factorTwoNaturalFrequency n.1 * t) -
            Real.sin (factorTwoNaturalFrequency n.1 * t) /
              factorTwoNaturalFrequency n.1)) volume 0 2 := by
      apply intervalIntegrable_of_const_mul
        (show (1 / (2 * yoshidaA) : ℝ) ≠ 0 by
          exact div_ne_zero one_ne_zero
            (mul_ne_zero (by norm_num) yoshidaA_pos.ne'))
      refine h.congr ?_
      intro t _ht
      unfold factorTwoCanonicalEvenDiagonalCorrelationFormula
      rw [factorTwoCanonicalEvenFrequency_eq_natural]
      field_simp [yoshidaA_pos.ne']
    have hsin := intervalIntegrable_factorTwoSymmetricSinMoment n hn
    have hsinDiv : IntervalIntegrable
        (fun t ↦ factorTwoSymmetricWeight (yoshidaEndpointA * t) *
          (Real.sin (factorTwoNaturalFrequency n.1 * t) /
            factorTwoNaturalFrequency n.1)) volume 0 2 := by
      have hs := hsin.const_mul (factorTwoNaturalFrequency n.1)⁻¹
      refine hs.congr ?_
      intro t _ht
      field_simp [hw]
    refine (hdiff.add hsinDiv).congr ?_
    intro t _ht
    ring

private theorem intervalIntegrable_factorTwoSymmetricSin_const
    (n : FactorTwoCanonicalEvenIndex) (hn : n.1 ≠ 0) (c : ℝ) :
    IntervalIntegrable
      (fun t ↦ factorTwoSymmetricWeight (yoshidaEndpointA * t) *
        (c * Real.sin (factorTwoNaturalFrequency n.1 * t)))
      volume 0 2 := by
  have h := (intervalIntegrable_factorTwoSymmetricSinMoment n hn).const_mul c
  refine h.congr ?_
  intro t _ht
  ring

/-! The following identities are the `O(N)` compression step: all paired
helpers reduce to per-frequency primitive moments. -/

theorem factorTwoSymmetricEvenDiagonalMoment_eq_primitives
    (n : FactorTwoCanonicalEvenIndex) (hn : n.1 ≠ 0) :
    factorTwoSymmetricEvenDiagonalMoment n.1 =
      factorTwoSymmetricAffineCosMoment n.1 -
        (1 / factorTwoNaturalFrequency n.1) *
          factorTwoSymmetricSinMoment n.1 := by
  unfold factorTwoSymmetricEvenDiagonalMoment
    factorTwoSymmetricAffineCosMoment factorTwoSymmetricSinMoment
  rw [show (fun t : ℝ ↦
      (2 - t) * Real.cos (factorTwoNaturalFrequency n.1 * t) -
        Real.sin (factorTwoNaturalFrequency n.1 * t) /
          factorTwoNaturalFrequency n.1) =
      fun t ↦
        (2 - t) * Real.cos (factorTwoNaturalFrequency n.1 * t) -
          (1 / factorTwoNaturalFrequency n.1) *
            Real.sin (factorTwoNaturalFrequency n.1 * t) by
    funext t
    ring]
  rw [factorTwoSymmetricPerturbationFunctional_sub
    _ _ (intervalIntegrable_factorTwoSymmetricAffineCosMoment n)
    (intervalIntegrable_factorTwoSymmetricSin_const n hn _),
    factorTwoSymmetricPerturbationFunctional_const_mul]

theorem factorTwoSymmetricOddDiagonalMoment_eq_primitives
    (n : FactorTwoCanonicalEvenIndex) (hn : n.1 ≠ 0) :
    factorTwoSymmetricOddDiagonalMoment n.1 =
      factorTwoSymmetricAffineCosMoment n.1 +
        (1 / factorTwoNaturalFrequency n.1) *
          factorTwoSymmetricSinMoment n.1 := by
  unfold factorTwoSymmetricOddDiagonalMoment
    factorTwoSymmetricAffineCosMoment factorTwoSymmetricSinMoment
  rw [show (fun t : ℝ ↦
      (2 - t) * Real.cos (factorTwoNaturalFrequency n.1 * t) +
        Real.sin (factorTwoNaturalFrequency n.1 * t) /
          factorTwoNaturalFrequency n.1) =
      fun t ↦
        (2 - t) * Real.cos (factorTwoNaturalFrequency n.1 * t) +
          (1 / factorTwoNaturalFrequency n.1) *
            Real.sin (factorTwoNaturalFrequency n.1 * t) by
    funext t
    ring]
  rw [factorTwoSymmetricPerturbationFunctional_add
    _ _ (intervalIntegrable_factorTwoSymmetricAffineCosMoment n)
    (intervalIntegrable_factorTwoSymmetricSin_const n hn _),
    factorTwoSymmetricPerturbationFunctional_const_mul]

theorem factorTwoSymmetricWeightedSinDifferenceMoment_eq_primitives
    (n m : FactorTwoCanonicalEvenIndex) (hn : n.1 ≠ 0)
    (hm : m.1 ≠ 0) :
    factorTwoSymmetricWeightedSinDifferenceMoment n.1 m.1 =
      factorTwoNaturalFrequency m.1 * factorTwoSymmetricSinMoment m.1 -
        factorTwoNaturalFrequency n.1 * factorTwoSymmetricSinMoment n.1 := by
  unfold factorTwoSymmetricWeightedSinDifferenceMoment
    factorTwoSymmetricSinMoment
  rw [factorTwoSymmetricPerturbationFunctional_sub
    _ _ (intervalIntegrable_factorTwoSymmetricSin_const m hm _)
    (intervalIntegrable_factorTwoSymmetricSin_const n hn _),
    factorTwoSymmetricPerturbationFunctional_const_mul,
    factorTwoSymmetricPerturbationFunctional_const_mul]

theorem factorTwoSymmetricCrossSinMoment_eq_primitives
    (n m : FactorTwoCanonicalEvenIndex) (hn : n.1 ≠ 0)
    (hm : m.1 ≠ 0) :
    factorTwoSymmetricCrossSinMoment n.1 m.1 =
      factorTwoNaturalFrequency n.1 * factorTwoSymmetricSinMoment m.1 -
        factorTwoNaturalFrequency m.1 * factorTwoSymmetricSinMoment n.1 := by
  unfold factorTwoSymmetricCrossSinMoment factorTwoSymmetricSinMoment
  rw [factorTwoSymmetricPerturbationFunctional_sub
    _ _ (intervalIntegrable_factorTwoSymmetricSin_const m hm _)
    (intervalIntegrable_factorTwoSymmetricSin_const n hn _),
    factorTwoSymmetricPerturbationFunctional_const_mul,
    factorTwoSymmetricPerturbationFunctional_const_mul]

/-! ## Canonical even branches -/

theorem factorTwoSymmetric_even_zero_zero :
    factorTwoSymmetricPerturbationFunctional
        factorTwoCanonicalEvenZeroZeroCorrelationFormula =
      (1 / (2 * yoshidaA)) * factorTwoSymmetricAffineCosMoment 0 := by
  calc
    _ = factorTwoSymmetricPerturbationFunctional
        (fun t ↦ (1 / (2 * yoshidaA)) *
          ((2 - t) * Real.cos (factorTwoNaturalFrequency 0 * t))) := by
      apply factorTwoSymmetricPerturbationFunctional_congr
      intro t
      simp [factorTwoCanonicalEvenZeroZeroCorrelationFormula,
        factorTwoNaturalFrequency]
      ring
    _ = _ := by
      rw [factorTwoSymmetricPerturbationFunctional_const_mul]
      rfl

theorem factorTwoSymmetric_even_zero_positive
    (m : FactorTwoCanonicalEvenIndex) (hm : m.1 ≠ 0) :
    factorTwoSymmetricPerturbationFunctional
        (factorTwoCanonicalEvenZeroPositiveCorrelationFormula m) =
      (((-1 : ℝ) ^ (m.1 + 1) /
          (Real.sqrt 2 * factorTwoNaturalFrequency m.1)) / yoshidaA) *
        factorTwoSymmetricSinMoment m.1 := by
  calc
    _ = factorTwoSymmetricPerturbationFunctional
        (fun t ↦ (((-1 : ℝ) ^ (m.1 + 1) /
            (Real.sqrt 2 * factorTwoNaturalFrequency m.1)) / yoshidaA) *
          Real.sin (factorTwoNaturalFrequency m.1 * t)) := by
      apply factorTwoSymmetricPerturbationFunctional_congr
      intro t
      rw [factorTwoCanonicalEvenZeroPositiveCorrelationFormula,
        factorTwoCanonicalEvenFrequency_eq_natural]
      have hw : factorTwoNaturalFrequency m.1 ≠ 0 := by
        unfold factorTwoNaturalFrequency
        exact mul_ne_zero Real.pi_ne_zero (Nat.cast_ne_zero.mpr hm)
      field_simp [hw, yoshidaA_pos.ne']
    _ = _ := by
      rw [factorTwoSymmetricPerturbationFunctional_const_mul]
      rfl

theorem factorTwoSymmetric_even_positive_zero
    (n : FactorTwoCanonicalEvenIndex) (hn : n.1 ≠ 0) :
    factorTwoSymmetricPerturbationFunctional
        (factorTwoCanonicalEvenPositiveZeroCorrelationFormula n) =
      (((-1 : ℝ) ^ (n.1 + 1) /
          (Real.sqrt 2 * factorTwoNaturalFrequency n.1)) / yoshidaA) *
        factorTwoSymmetricSinMoment n.1 := by
  calc
    _ = factorTwoSymmetricPerturbationFunctional
        (fun t ↦ (((-1 : ℝ) ^ (n.1 + 1) /
            (Real.sqrt 2 * factorTwoNaturalFrequency n.1)) / yoshidaA) *
          Real.sin (factorTwoNaturalFrequency n.1 * t)) := by
      apply factorTwoSymmetricPerturbationFunctional_congr
      intro t
      rw [factorTwoCanonicalEvenPositiveZeroCorrelationFormula,
        factorTwoCanonicalEvenFrequency_eq_natural]
      have hw : factorTwoNaturalFrequency n.1 ≠ 0 := by
        unfold factorTwoNaturalFrequency
        exact mul_ne_zero Real.pi_ne_zero (Nat.cast_ne_zero.mpr hn)
      field_simp [hw, yoshidaA_pos.ne']
    _ = _ := by
      rw [factorTwoSymmetricPerturbationFunctional_const_mul]
      rfl

theorem factorTwoSymmetric_even_diagonal
    (n : FactorTwoCanonicalEvenIndex) (hn : n.1 ≠ 0) :
    factorTwoSymmetricPerturbationFunctional
        (factorTwoCanonicalEvenDiagonalCorrelationFormula n) =
      (1 / (2 * yoshidaA)) *
        (factorTwoSymmetricAffineCosMoment n.1 -
          (1 / factorTwoNaturalFrequency n.1) *
            factorTwoSymmetricSinMoment n.1) := by
  calc
    _ = factorTwoSymmetricPerturbationFunctional
        (fun t ↦ (1 / (2 * yoshidaA)) *
          ((2 - t) * Real.cos (factorTwoNaturalFrequency n.1 * t) -
            Real.sin (factorTwoNaturalFrequency n.1 * t) /
              factorTwoNaturalFrequency n.1)) := by
      apply factorTwoSymmetricPerturbationFunctional_congr
      intro t
      rw [factorTwoCanonicalEvenDiagonalCorrelationFormula,
        factorTwoCanonicalEvenFrequency_eq_natural]
      field_simp [yoshidaA_pos.ne']
    _ = (1 / (2 * yoshidaA)) *
        factorTwoSymmetricEvenDiagonalMoment n.1 := by
      rw [factorTwoSymmetricPerturbationFunctional_const_mul]
      rfl
    _ = _ := by
      rw [factorTwoSymmetricEvenDiagonalMoment_eq_primitives n hn]

theorem factorTwoSymmetric_even_off_diagonal
    (n m : FactorTwoCanonicalEvenIndex) (hn : n.1 ≠ 0)
    (hm : m.1 ≠ 0) (hnm : n ≠ m) :
    factorTwoSymmetricPerturbationFunctional
        (factorTwoCanonicalEvenOffDiagonalCorrelationFormula n m) =
      (((-1 : ℝ) ^ (n.1 + m.1) /
          (factorTwoNaturalFrequency n.1 ^ 2 -
            factorTwoNaturalFrequency m.1 ^ 2)) / yoshidaA) *
        (factorTwoNaturalFrequency m.1 * factorTwoSymmetricSinMoment m.1 -
          factorTwoNaturalFrequency n.1 * factorTwoSymmetricSinMoment n.1) := by
  have hval : n.1 ≠ m.1 := fun h ↦ hnm (Fin.ext h)
  have hden : factorTwoNaturalFrequency n.1 ^ 2 -
      factorTwoNaturalFrequency m.1 ^ 2 ≠ 0 := by
    rw [show factorTwoNaturalFrequency n.1 ^ 2 -
        factorTwoNaturalFrequency m.1 ^ 2 =
      Real.pi ^ 2 * ((n.1 : ℝ) ^ 2 - (m.1 : ℝ) ^ 2) by
      unfold factorTwoNaturalFrequency
      ring]
    apply mul_ne_zero (pow_ne_zero 2 Real.pi_ne_zero)
    apply sub_ne_zero.mpr
    intro hsquares
    have hcast : (n.1 : ℝ) = (m.1 : ℝ) := by
      have hn0 : 0 ≤ (n.1 : ℝ) := by positivity
      have hm0 : 0 ≤ (m.1 : ℝ) := by positivity
      nlinarith
    apply hval
    exact_mod_cast hcast
  calc
    _ = factorTwoSymmetricPerturbationFunctional
        (fun t ↦ (((-1 : ℝ) ^ (n.1 + m.1) /
            (factorTwoNaturalFrequency n.1 ^ 2 -
              factorTwoNaturalFrequency m.1 ^ 2)) / yoshidaA) *
          (factorTwoNaturalFrequency m.1 *
              Real.sin (factorTwoNaturalFrequency m.1 * t) -
            factorTwoNaturalFrequency n.1 *
              Real.sin (factorTwoNaturalFrequency n.1 * t))) := by
      apply factorTwoSymmetricPerturbationFunctional_congr
      intro t
      rw [factorTwoCanonicalEvenOffDiagonalCorrelationFormula,
        factorTwoCanonicalEvenFrequency_eq_natural,
        factorTwoCanonicalEvenFrequency_eq_natural]
      field_simp [hden, yoshidaA_pos.ne']
    _ = (((-1 : ℝ) ^ (n.1 + m.1) /
          (factorTwoNaturalFrequency n.1 ^ 2 -
            factorTwoNaturalFrequency m.1 ^ 2)) / yoshidaA) *
        factorTwoSymmetricWeightedSinDifferenceMoment n.1 m.1 := by
      rw [factorTwoSymmetricPerturbationFunctional_const_mul]
      rfl
    _ = _ := by
      rw [factorTwoSymmetricWeightedSinDifferenceMoment_eq_primitives
        n m hn hm]

/-- Enclosure-ready scalar-moment formula for every canonical even entry. -/
def factorTwoCanonicalEvenPerturbationMomentFormula
    (n m : FactorTwoCanonicalEvenIndex) : ℝ :=
  if n.1 = 0 then
    if m.1 = 0 then
      (1 / (2 * yoshidaA)) * factorTwoSymmetricAffineCosMoment 0
    else
      (((-1 : ℝ) ^ (m.1 + 1) /
          (Real.sqrt 2 * factorTwoNaturalFrequency m.1)) / yoshidaA) *
        factorTwoSymmetricSinMoment m.1
  else if m.1 = 0 then
    (((-1 : ℝ) ^ (n.1 + 1) /
        (Real.sqrt 2 * factorTwoNaturalFrequency n.1)) / yoshidaA) *
      factorTwoSymmetricSinMoment n.1
  else if n = m then
    (1 / (2 * yoshidaA)) *
      (factorTwoSymmetricAffineCosMoment n.1 -
        (1 / factorTwoNaturalFrequency n.1) *
          factorTwoSymmetricSinMoment n.1)
  else
    (((-1 : ℝ) ^ (n.1 + m.1) /
        (factorTwoNaturalFrequency n.1 ^ 2 -
          factorTwoNaturalFrequency m.1 ^ 2)) / yoshidaA) *
      (factorTwoNaturalFrequency m.1 * factorTwoSymmetricSinMoment m.1 -
        factorTwoNaturalFrequency n.1 * factorTwoSymmetricSinMoment n.1)

theorem factorTwoSymmetric_canonicalEven_eq_moments
    (n m : FactorTwoCanonicalEvenIndex) :
    factorTwoSymmetricPerturbationFunctional
        (factorTwoCanonicalEvenCorrelationFormula n m) =
      factorTwoCanonicalEvenPerturbationMomentFormula n m := by
  by_cases hn : n.1 = 0
  · by_cases hm : m.1 = 0
    · have hcorr : factorTwoCanonicalEvenCorrelationFormula n m =
          factorTwoCanonicalEvenZeroZeroCorrelationFormula := by
        funext t
        simp [factorTwoCanonicalEvenCorrelationFormula, hn, hm]
      rw [hcorr, factorTwoSymmetric_even_zero_zero]
      simp [factorTwoCanonicalEvenPerturbationMomentFormula, hn, hm]
    · have hcorr : factorTwoCanonicalEvenCorrelationFormula n m =
          factorTwoCanonicalEvenZeroPositiveCorrelationFormula m := by
        funext t
        simp [factorTwoCanonicalEvenCorrelationFormula, hn, hm]
      rw [hcorr, factorTwoSymmetric_even_zero_positive m hm]
      simp [factorTwoCanonicalEvenPerturbationMomentFormula, hn, hm]
  · by_cases hm : m.1 = 0
    · have hcorr : factorTwoCanonicalEvenCorrelationFormula n m =
          factorTwoCanonicalEvenPositiveZeroCorrelationFormula n := by
        funext t
        simp [factorTwoCanonicalEvenCorrelationFormula, hn, hm]
      rw [hcorr, factorTwoSymmetric_even_positive_zero n hn]
      simp [factorTwoCanonicalEvenPerturbationMomentFormula, hn, hm]
    · by_cases hnm : n = m
      · have hcorr : factorTwoCanonicalEvenCorrelationFormula n m =
            factorTwoCanonicalEvenDiagonalCorrelationFormula n := by
          funext t
          simp [factorTwoCanonicalEvenCorrelationFormula, hm, hnm]
        rw [hcorr, factorTwoSymmetric_even_diagonal n hn]
        simp [factorTwoCanonicalEvenPerturbationMomentFormula, hm, hnm]
      · have hcorr : factorTwoCanonicalEvenCorrelationFormula n m =
            factorTwoCanonicalEvenOffDiagonalCorrelationFormula n m := by
          funext t
          simp [factorTwoCanonicalEvenCorrelationFormula, hn, hm, hnm]
        rw [hcorr, factorTwoSymmetric_even_off_diagonal n m hn hm hnm]
        simp [factorTwoCanonicalEvenPerturbationMomentFormula, hn, hm, hnm]

theorem factorTwoCanonicalEvenPerturbationEntry_eq_moments
    (n m : FactorTwoCanonicalEvenIndex) :
    factorTwoCanonicalEvenPerturbationEntry n m =
      factorTwoCanonicalEvenPerturbationMomentFormula n m := by
  rw [factorTwoCanonicalEvenPerturbationEntry_apply,
    ← factorTwoSymmetricPerturbationFunctional_eq_even,
    factorTwoSymmetric_canonicalEven_eq_moments]

/-- Direct scalar-moment formula for the endpoint-adapted concrete even
matrix. -/
theorem factorTwoConcreteEvenPerturbationMatrix_eq_moments
    (i j : YoshidaEvenIndex) :
    factorTwoConcreteEvenPerturbationMatrix i j =
      factorTwoCanonicalEvenPerturbationMomentFormula
          (factorTwoCanonicalEvenLowIndex i)
          (factorTwoCanonicalEvenLowIndex j) -
        endpointEvenLowTraceRatio j *
          factorTwoCanonicalEvenPerturbationMomentFormula
            (factorTwoCanonicalEvenLowIndex i)
            factorTwoCanonicalEvenTopIndex -
        endpointEvenLowTraceRatio i *
          factorTwoCanonicalEvenPerturbationMomentFormula
            factorTwoCanonicalEvenTopIndex
            (factorTwoCanonicalEvenLowIndex j) +
        endpointEvenLowTraceRatio i * endpointEvenLowTraceRatio j *
          factorTwoCanonicalEvenPerturbationMomentFormula
            factorTwoCanonicalEvenTopIndex
            factorTwoCanonicalEvenTopIndex := by
  rw [factorTwoConcreteEvenPerturbationMatrix_eq_canonical_update,
    factorTwoCanonicalEvenPerturbationEntry_eq_moments,
    factorTwoCanonicalEvenPerturbationEntry_eq_moments,
    factorTwoCanonicalEvenPerturbationEntry_eq_moments,
    factorTwoCanonicalEvenPerturbationEntry_eq_moments]

/-! ## Canonical odd branches -/

/-- Every retained odd frequency is also a canonical frequency in
`0, ..., 200`. -/
def factorTwoOddCanonicalFrequencyIndex
    (i : YoshidaOddIndex) : FactorTwoCanonicalEvenIndex :=
  ⟨i.1 + 1, by omega⟩

@[simp] theorem factorTwoOddCanonicalFrequencyIndex_val
    (i : YoshidaOddIndex) :
    (factorTwoOddCanonicalFrequencyIndex i).1 = i.1 + 1 := rfl

theorem factorTwoSymmetric_odd_diagonal (i : YoshidaOddIndex) :
    factorTwoSymmetricPerturbationFunctional
        (factorTwoConcreteOddDiagonalCorrelationFormula i) =
      (1 / (2 * yoshidaA)) *
        (factorTwoSymmetricAffineCosMoment (i.1 + 1) +
          (1 / factorTwoNaturalFrequency (i.1 + 1)) *
            factorTwoSymmetricSinMoment (i.1 + 1)) := by
  let n := factorTwoOddCanonicalFrequencyIndex i
  have hn : n.1 ≠ 0 := by
    dsimp only [n, factorTwoOddCanonicalFrequencyIndex]
    omega
  have hw : factorTwoNaturalFrequency (i.1 + 1) ≠ 0 := by
    unfold factorTwoNaturalFrequency
    exact mul_ne_zero Real.pi_ne_zero (by positivity)
  calc
    _ = factorTwoSymmetricPerturbationFunctional
        (fun t ↦ (1 / (2 * yoshidaA)) *
          ((2 - t) *
              Real.cos (factorTwoNaturalFrequency (i.1 + 1) * t) +
            Real.sin (factorTwoNaturalFrequency (i.1 + 1) * t) /
              factorTwoNaturalFrequency (i.1 + 1))) := by
      apply factorTwoSymmetricPerturbationFunctional_congr
      intro t
      unfold factorTwoConcreteOddDiagonalCorrelationFormula
        clippedOddFrequency factorTwoNaturalFrequency
      field_simp [yoshidaA_pos.ne', hw]
    _ = (1 / (2 * yoshidaA)) *
        factorTwoSymmetricOddDiagonalMoment (i.1 + 1) := by
      rw [factorTwoSymmetricPerturbationFunctional_const_mul]
      rfl
    _ = _ := by
      simpa only [factorTwoOddCanonicalFrequencyIndex_val] using
        congrArg (fun x ↦ (1 / (2 * yoshidaA)) * x)
          (factorTwoSymmetricOddDiagonalMoment_eq_primitives n hn)

theorem factorTwoSymmetric_odd_off_diagonal
    (i j : YoshidaOddIndex) (hij : i ≠ j) :
    factorTwoSymmetricPerturbationFunctional
        (factorTwoConcreteOddOffDiagonalCorrelationFormula i j) =
      (((-1 : ℝ) ^ ((i.1 + 1) + (j.1 + 1)) /
          (factorTwoNaturalFrequency (i.1 + 1) ^ 2 -
            factorTwoNaturalFrequency (j.1 + 1) ^ 2)) / yoshidaA) *
        (factorTwoNaturalFrequency (i.1 + 1) *
            factorTwoSymmetricSinMoment (j.1 + 1) -
          factorTwoNaturalFrequency (j.1 + 1) *
            factorTwoSymmetricSinMoment (i.1 + 1)) := by
  let n := factorTwoOddCanonicalFrequencyIndex i
  let m := factorTwoOddCanonicalFrequencyIndex j
  have hn : n.1 ≠ 0 := by
    dsimp only [n, factorTwoOddCanonicalFrequencyIndex]
    omega
  have hm : m.1 ≠ 0 := by
    dsimp only [m, factorTwoOddCanonicalFrequencyIndex]
    omega
  have hval : i.1 + 1 ≠ j.1 + 1 := by
    intro h
    apply hij
    apply Fin.ext
    omega
  have hden : factorTwoNaturalFrequency (i.1 + 1) ^ 2 -
      factorTwoNaturalFrequency (j.1 + 1) ^ 2 ≠ 0 := by
    rw [show factorTwoNaturalFrequency (i.1 + 1) ^ 2 -
        factorTwoNaturalFrequency (j.1 + 1) ^ 2 =
      Real.pi ^ 2 * (((i.1 + 1 : ℕ) : ℝ) ^ 2 -
        ((j.1 + 1 : ℕ) : ℝ) ^ 2) by
      unfold factorTwoNaturalFrequency
      ring]
    apply mul_ne_zero (pow_ne_zero 2 Real.pi_ne_zero)
    apply sub_ne_zero.mpr
    intro hsquares
    have hcast : ((i.1 + 1 : ℕ) : ℝ) = ((j.1 + 1 : ℕ) : ℝ) := by
      have hi0 : 0 ≤ ((i.1 + 1 : ℕ) : ℝ) := by positivity
      have hj0 : 0 ≤ ((j.1 + 1 : ℕ) : ℝ) := by positivity
      nlinarith
    apply hval
    exact_mod_cast hcast
  calc
    _ = factorTwoSymmetricPerturbationFunctional
        (fun t ↦ (((-1 : ℝ) ^ ((i.1 + 1) + (j.1 + 1)) /
            (factorTwoNaturalFrequency (i.1 + 1) ^ 2 -
              factorTwoNaturalFrequency (j.1 + 1) ^ 2)) / yoshidaA) *
          (factorTwoNaturalFrequency (i.1 + 1) *
              Real.sin (factorTwoNaturalFrequency (j.1 + 1) * t) -
            factorTwoNaturalFrequency (j.1 + 1) *
              Real.sin (factorTwoNaturalFrequency (i.1 + 1) * t))) := by
      apply factorTwoSymmetricPerturbationFunctional_congr
      intro t
      unfold factorTwoConcreteOddOffDiagonalCorrelationFormula
        clippedOddFrequency factorTwoNaturalFrequency
      field_simp [yoshidaA_pos.ne', hden]
    _ = (((-1 : ℝ) ^ ((i.1 + 1) + (j.1 + 1)) /
          (factorTwoNaturalFrequency (i.1 + 1) ^ 2 -
            factorTwoNaturalFrequency (j.1 + 1) ^ 2)) / yoshidaA) *
        factorTwoSymmetricCrossSinMoment (i.1 + 1) (j.1 + 1) := by
      rw [factorTwoSymmetricPerturbationFunctional_const_mul]
      rfl
    _ = _ := by
      simpa only [factorTwoOddCanonicalFrequencyIndex_val] using
        congrArg
          (fun x ↦ (((-1 : ℝ) ^ ((i.1 + 1) + (j.1 + 1)) /
            (factorTwoNaturalFrequency (i.1 + 1) ^ 2 -
              factorTwoNaturalFrequency (j.1 + 1) ^ 2)) / yoshidaA) * x)
          (factorTwoSymmetricCrossSinMoment_eq_primitives n m hn hm)

/-- Enclosure-ready scalar-moment formula for the concrete odd block. -/
def factorTwoConcreteOddPerturbationMomentFormula
    (i j : YoshidaOddIndex) : ℝ :=
  if i = j then
    (1 / (2 * yoshidaA)) *
      (factorTwoSymmetricAffineCosMoment (i.1 + 1) +
        (1 / factorTwoNaturalFrequency (i.1 + 1)) *
          factorTwoSymmetricSinMoment (i.1 + 1))
  else
    (((-1 : ℝ) ^ ((i.1 + 1) + (j.1 + 1)) /
        (factorTwoNaturalFrequency (i.1 + 1) ^ 2 -
          factorTwoNaturalFrequency (j.1 + 1) ^ 2)) / yoshidaA) *
      (factorTwoNaturalFrequency (i.1 + 1) *
          factorTwoSymmetricSinMoment (j.1 + 1) -
        factorTwoNaturalFrequency (j.1 + 1) *
          factorTwoSymmetricSinMoment (i.1 + 1))

theorem factorTwoConcreteOddPerturbationMatrix_eq_moments
    (i j : YoshidaOddIndex) :
    factorTwoConcreteOddPerturbationMatrix i j =
      factorTwoConcreteOddPerturbationMomentFormula i j := by
  rw [factorTwoConcreteOddPerturbationMatrix_apply,
    ← factorTwoSymmetricPerturbationFunctional_eq_odd]
  by_cases hij : i = j
  · subst j
    have hcorr : factorTwoConcreteOddCorrelationFormula i i =
        factorTwoConcreteOddDiagonalCorrelationFormula i := by
      funext t
      simp [factorTwoConcreteOddCorrelationFormula]
    rw [hcorr, factorTwoSymmetric_odd_diagonal]
    simp [factorTwoConcreteOddPerturbationMomentFormula]
  · have hcorr : factorTwoConcreteOddCorrelationFormula i j =
        factorTwoConcreteOddOffDiagonalCorrelationFormula i j := by
      funext t
      simp [factorTwoConcreteOddCorrelationFormula, hij]
    rw [hcorr, factorTwoSymmetric_odd_off_diagonal i j hij]
    simp [factorTwoConcreteOddPerturbationMomentFormula, hij]

/-! ## Canonical and endpoint-adapted alternating branches -/

/-- Every explicit canonical even--odd correlation retains the endpoint
cancellation required by the antisymmetric weight. -/
theorem intervalIntegrable_factorTwoAntisymmetric_canonicalCrossFormula
    (n : FactorTwoCanonicalEvenIndex) (m : ℕ) (hm : m ≠ 0) :
    IntervalIntegrable
      (fun t ↦ factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
        factorTwoCanonicalEvenOddCrossFormula n m t)
      volume 0 2 := by
  have h := intervalIntegrable_factorTwoCenteredAlternatingKernel
    (factorTwoCenteredCanonicalEvenProfile n)
    (factorTwoCenteredCanonicalOddProfile m)
    (continuous_factorTwoCenteredCanonicalEvenProfile n)
    (continuous_factorTwoCenteredCanonicalOddProfile m)
  have hscaled := h.const_mul (-1 / 2 : ℝ)
  refine hscaled.congr ?_
  intro t ht
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
  change (-1 / 2 : ℝ) *
      (factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
        (factorTwoCenteredCrossCorrelation
            (factorTwoCenteredCanonicalOddProfile m)
            (factorTwoCenteredCanonicalEvenProfile n) t -
          factorTwoCenteredCrossCorrelation
            (factorTwoCenteredCanonicalEvenProfile n)
            (factorTwoCenteredCanonicalOddProfile m) t)) = _
  rw [factorTwoCenteredCrossCorrelation_swap_of_even_odd
      (factorTwoCenteredCanonicalEvenProfile_even n)
      (factorTwoCenteredCanonicalOddProfile_odd m),
    factorTwoCenteredCrossCorrelation_canonicalEven_odd_eq_formula
      n m hm t (le_of_lt ht.1) ht.2]
  ring

/-- Primitive endpoint-cancelled cosine moments are interval-integrable for
all positive integer frequencies. -/
theorem intervalIntegrable_factorTwoAntisymmetricOneSubCosMoment
    (m : ℕ) (hm : m ≠ 0) :
    IntervalIntegrable
      (fun t ↦ factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
        (1 - Real.cos (factorTwoNaturalFrequency m * t)))
      volume 0 2 := by
  let z : FactorTwoCanonicalEvenIndex := ⟨0, by omega⟩
  let c : ℝ := (-1 : ℝ) ^ m /
    (Real.sqrt 2 * yoshidaA * factorTwoNaturalFrequency m)
  have hw : factorTwoNaturalFrequency m ≠ 0 := by
    unfold factorTwoNaturalFrequency
    exact mul_ne_zero Real.pi_ne_zero (Nat.cast_ne_zero.mpr hm)
  have hc : c ≠ 0 := by
    dsimp only [c]
    exact div_ne_zero (pow_ne_zero _ (by norm_num))
      (mul_ne_zero (mul_ne_zero (by positivity) yoshidaA_pos.ne') hw)
  have h :=
    intervalIntegrable_factorTwoAntisymmetric_canonicalCrossFormula z m hm
  apply intervalIntegrable_of_const_mul hc
  refine h.congr ?_
  intro t _ht
  unfold factorTwoCanonicalEvenOddCrossFormula
  dsimp only
  rw [if_pos (show z.1 = 0 by rfl)]
  dsimp only [z, c]
  unfold factorTwoNaturalFrequency
  ring

/-- Primitive endpoint-adapted sine moments are interval-integrable for all
positive canonical frequencies. -/
theorem intervalIntegrable_factorTwoAntisymmetricAffineSinMoment
    (n : FactorTwoCanonicalEvenIndex) (hn : n.1 ≠ 0) :
    IntervalIntegrable
      (fun t ↦ factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
        ((2 - t) * Real.sin (factorTwoNaturalFrequency n.1 * t)))
      volume 0 2 := by
  have h := intervalIntegrable_factorTwoAntisymmetric_canonicalCrossFormula
    n n.1 hn
  apply intervalIntegrable_of_const_mul
    (show (-1 / (2 * yoshidaA) : ℝ) ≠ 0 by
      exact div_ne_zero (by norm_num)
        (mul_ne_zero (by norm_num) yoshidaA_pos.ne'))
  refine h.congr ?_
  intro t _ht
  unfold factorTwoCanonicalEvenOddCrossFormula
  dsimp only
  rw [if_neg hn, if_pos rfl]
  unfold factorTwoNaturalFrequency
  ring

theorem factorTwoAntisymmetricCosDifferenceMoment_eq_primitives
    (n : FactorTwoCanonicalEvenIndex) (m : ℕ)
    (hn : n.1 ≠ 0) (hm : m ≠ 0) :
    factorTwoAntisymmetricCosDifferenceMoment n.1 m =
      factorTwoAntisymmetricOneSubCosMoment m -
        factorTwoAntisymmetricOneSubCosMoment n.1 := by
  unfold factorTwoAntisymmetricCosDifferenceMoment
    factorTwoAntisymmetricOneSubCosMoment
  rw [show (fun t : ℝ ↦
      Real.cos (factorTwoNaturalFrequency n.1 * t) -
        Real.cos (factorTwoNaturalFrequency m * t)) =
      fun t ↦
        (1 - Real.cos (factorTwoNaturalFrequency m * t)) -
          (1 - Real.cos (factorTwoNaturalFrequency n.1 * t)) by
    funext t
    ring]
  rw [factorTwoAntisymmetricPerturbationFunctional_sub _ _
    (intervalIntegrable_factorTwoAntisymmetricOneSubCosMoment m hm)
    (intervalIntegrable_factorTwoAntisymmetricOneSubCosMoment n.1 hn)]

theorem factorTwoAntisymmetric_canonical_zero
    (n : FactorTwoCanonicalEvenIndex) (m : ℕ)
    (hn : n.1 = 0) :
    factorTwoAntisymmetricPerturbationFunctional
        (factorTwoCanonicalEvenOddCrossFormula n m) =
      ((-1 : ℝ) ^ m /
          (Real.sqrt 2 * yoshidaA * factorTwoNaturalFrequency m)) *
        factorTwoAntisymmetricOneSubCosMoment m := by
  calc
    _ = factorTwoAntisymmetricPerturbationFunctional
        (fun t ↦ ((-1 : ℝ) ^ m /
            (Real.sqrt 2 * yoshidaA * factorTwoNaturalFrequency m)) *
          (1 - Real.cos (factorTwoNaturalFrequency m * t))) := by
      apply factorTwoAntisymmetricPerturbationFunctional_congr
      intro t
      unfold factorTwoCanonicalEvenOddCrossFormula
      rw [if_pos hn]
      unfold factorTwoNaturalFrequency
      ring
    _ = _ := by
      rw [factorTwoAntisymmetricPerturbationFunctional_const_mul]
      rfl

theorem factorTwoAntisymmetric_canonical_diagonal
    (n : FactorTwoCanonicalEvenIndex) (m : ℕ)
    (hn : n.1 ≠ 0) (hnm : n.1 = m) :
    factorTwoAntisymmetricPerturbationFunctional
        (factorTwoCanonicalEvenOddCrossFormula n m) =
      (-1 / (2 * yoshidaA)) *
        factorTwoAntisymmetricAffineSinMoment m := by
  calc
    _ = factorTwoAntisymmetricPerturbationFunctional
        (fun t ↦ (-1 / (2 * yoshidaA)) *
          ((2 - t) * Real.sin (factorTwoNaturalFrequency m * t))) := by
      apply factorTwoAntisymmetricPerturbationFunctional_congr
      intro t
      unfold factorTwoCanonicalEvenOddCrossFormula
      rw [if_neg hn, if_pos hnm]
      unfold factorTwoNaturalFrequency
      ring
    _ = _ := by
      rw [factorTwoAntisymmetricPerturbationFunctional_const_mul]
      rfl

theorem factorTwoAntisymmetric_canonical_off_diagonal
    (n : FactorTwoCanonicalEvenIndex) (m : ℕ)
    (hn : n.1 ≠ 0) (hm : m ≠ 0) (hnm : n.1 ≠ m) :
    factorTwoAntisymmetricPerturbationFunctional
        (factorTwoCanonicalEvenOddCrossFormula n m) =
      (((-1 : ℝ) ^ (n.1 + m) * factorTwoNaturalFrequency m) /
          (yoshidaA * (factorTwoNaturalFrequency m ^ 2 -
            factorTwoNaturalFrequency n.1 ^ 2))) *
        (factorTwoAntisymmetricOneSubCosMoment m -
          factorTwoAntisymmetricOneSubCosMoment n.1) := by
  have hden : factorTwoNaturalFrequency m ^ 2 -
      factorTwoNaturalFrequency n.1 ^ 2 ≠ 0 := by
    rw [show factorTwoNaturalFrequency m ^ 2 -
        factorTwoNaturalFrequency n.1 ^ 2 =
      Real.pi ^ 2 * ((m : ℝ) ^ 2 - (n.1 : ℝ) ^ 2) by
      unfold factorTwoNaturalFrequency
      ring]
    apply mul_ne_zero (pow_ne_zero 2 Real.pi_ne_zero)
    apply sub_ne_zero.mpr
    intro hsquares
    have hcast : (m : ℝ) = (n.1 : ℝ) := by
      have hm0 : 0 ≤ (m : ℝ) := by positivity
      have hn0 : 0 ≤ (n.1 : ℝ) := by positivity
      nlinarith
    apply hnm
    exact_mod_cast hcast.symm
  calc
    _ = factorTwoAntisymmetricPerturbationFunctional
        (fun t ↦ (((-1 : ℝ) ^ (n.1 + m) *
            factorTwoNaturalFrequency m) /
            (yoshidaA * (factorTwoNaturalFrequency m ^ 2 -
              factorTwoNaturalFrequency n.1 ^ 2))) *
          (Real.cos (factorTwoNaturalFrequency n.1 * t) -
            Real.cos (factorTwoNaturalFrequency m * t))) := by
      apply factorTwoAntisymmetricPerturbationFunctional_congr
      intro t
      unfold factorTwoCanonicalEvenOddCrossFormula
      rw [if_neg hn, if_neg hnm]
      unfold factorTwoNaturalFrequency
      field_simp [yoshidaA_pos.ne', Real.pi_ne_zero, hden]
    _ = (((-1 : ℝ) ^ (n.1 + m) * factorTwoNaturalFrequency m) /
          (yoshidaA * (factorTwoNaturalFrequency m ^ 2 -
            factorTwoNaturalFrequency n.1 ^ 2))) *
        factorTwoAntisymmetricCosDifferenceMoment n.1 m := by
      rw [factorTwoAntisymmetricPerturbationFunctional_const_mul]
      rfl
    _ = _ := by
      rw [factorTwoAntisymmetricCosDifferenceMoment_eq_primitives
        n m hn hm]

/-- `O(N)` per-frequency moment formula for a canonical even--odd entry. -/
def factorTwoCanonicalAlternatingMomentFormula
    (n : FactorTwoCanonicalEvenIndex) (m : ℕ) : ℝ :=
  if n.1 = 0 then
    ((-1 : ℝ) ^ m /
        (Real.sqrt 2 * yoshidaA * factorTwoNaturalFrequency m)) *
      factorTwoAntisymmetricOneSubCosMoment m
  else if n.1 = m then
    (-1 / (2 * yoshidaA)) * factorTwoAntisymmetricAffineSinMoment m
  else
    (((-1 : ℝ) ^ (n.1 + m) * factorTwoNaturalFrequency m) /
        (yoshidaA * (factorTwoNaturalFrequency m ^ 2 -
          factorTwoNaturalFrequency n.1 ^ 2))) *
      (factorTwoAntisymmetricOneSubCosMoment m -
        factorTwoAntisymmetricOneSubCosMoment n.1)

theorem factorTwoAntisymmetric_canonical_eq_moments
    (n : FactorTwoCanonicalEvenIndex) (m : ℕ) (hm : m ≠ 0) :
    factorTwoAntisymmetricPerturbationFunctional
        (factorTwoCanonicalEvenOddCrossFormula n m) =
      factorTwoCanonicalAlternatingMomentFormula n m := by
  by_cases hn : n.1 = 0
  · rw [factorTwoAntisymmetric_canonical_zero n m hn]
    simp [factorTwoCanonicalAlternatingMomentFormula, hn]
  · by_cases hnm : n.1 = m
    · rw [factorTwoAntisymmetric_canonical_diagonal n m hn hnm]
      simp [factorTwoCanonicalAlternatingMomentFormula, hnm, hm]
    · rw [factorTwoAntisymmetric_canonical_off_diagonal n m hn hm hnm]
      simp [factorTwoCanonicalAlternatingMomentFormula, hn, hnm]

private theorem intervalIntegrable_factorTwoAntisymmetricCanonical_const
    (n : FactorTwoCanonicalEvenIndex) (m : ℕ) (hm : m ≠ 0) (c : ℝ) :
    IntervalIntegrable
      (fun t ↦ factorTwoAntisymmetricWeight (yoshidaEndpointA * t) *
        (c * factorTwoCanonicalEvenOddCrossFormula n m t))
      volume 0 2 := by
  have h :=
    (intervalIntegrable_factorTwoAntisymmetric_canonicalCrossFormula
      n m hm).const_mul c
  refine h.congr ?_
  intro t _ht
  ring

/-- The endpoint adaptation is one rank-one subtraction at the scalar-moment
level. -/
def factorTwoAdaptedAlternatingMomentFormula
    (i : YoshidaEvenIndex) (m : ℕ) : ℝ :=
  factorTwoCanonicalAlternatingMomentFormula
      (factorTwoCanonicalEvenLowIndex i) m -
    endpointEvenLowTraceRatio i *
      factorTwoCanonicalAlternatingMomentFormula
        factorTwoCanonicalEvenTopIndex m

theorem factorTwoAntisymmetric_adapted_eq_moments
    (i : YoshidaEvenIndex) (m : ℕ) (hm : m ≠ 0) :
    factorTwoAntisymmetricPerturbationFunctional
        (factorTwoAdaptedEvenOddCrossFormula i m) =
      factorTwoAdaptedAlternatingMomentFormula i m := by
  change factorTwoAntisymmetricPerturbationFunctional
      (fun t ↦
        factorTwoCanonicalEvenOddCrossFormula
            (factorTwoCanonicalEvenLowIndex i) m t -
          endpointEvenLowTraceRatio i *
            factorTwoCanonicalEvenOddCrossFormula
              factorTwoCanonicalEvenTopIndex m t) = _
  rw [factorTwoAntisymmetricPerturbationFunctional_sub
    _ _
    (intervalIntegrable_factorTwoAntisymmetric_canonicalCrossFormula
      (factorTwoCanonicalEvenLowIndex i) m hm)
    (intervalIntegrable_factorTwoAntisymmetricCanonical_const
      factorTwoCanonicalEvenTopIndex m hm (endpointEvenLowTraceRatio i)),
    factorTwoAntisymmetricPerturbationFunctional_const_mul,
    factorTwoAntisymmetric_canonical_eq_moments _ m hm,
    factorTwoAntisymmetric_canonical_eq_moments _ m hm]
  rfl

/-- Direct `O(N)` scalar-moment formula for the concrete alternating block. -/
theorem factorTwoConcreteAlternatingMatrix_eq_moments
    (i : YoshidaEvenIndex) (j : YoshidaOddIndex) :
    factorTwoConcreteAlternatingMatrix i j =
      factorTwoAdaptedAlternatingMomentFormula i (j.1 + 1) := by
  rw [factorTwoConcreteAlternatingMatrix_apply]
  change factorTwoAntisymmetricPerturbationFunctional
      (factorTwoAdaptedEvenOddCrossFormula i (j.1 + 1)) = _
  exact factorTwoAntisymmetric_adapted_eq_moments i (j.1 + 1) (by omega)

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcretePerturbationMoments
