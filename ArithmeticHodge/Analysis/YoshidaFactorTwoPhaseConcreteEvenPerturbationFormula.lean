import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteEvenPerturbationAdaptation
import ArithmeticHodge.Analysis.YoshidaClippedEvenMomentBridge

set_option autoImplicit false
set_option maxRecDepth 100000

open Matrix MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteEvenPerturbationFormula

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaClippedEvenMomentBridge
open YoshidaCoercivityNumerics
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointScaledCorrelation
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseConcreteEvenPerturbationAdaptation
open YoshidaFactorTwoPhaseConcreteLowMatrix
open YoshidaFactorTwoPhaseEndpointAdaptedLow
open YoshidaFactorTwoPhaseEnvelope
open YoshidaWeightedTailBounds

/-!
# Exact canonical even perturbation entries

The endpoint-adapted even block uses canonical cosine frequencies `0, ..., 200`.
This file pulls their centered correlations back to the clipped physical
interval and records every zero, diagonal, and off-diagonal branch as an
explicit unit-interval formula.  The final theorem applies the complete
factor-two perturbation functional without separating its smooth term from
the retained `p = 2` and `p = 3` atoms.
-/

/-- The real clipped representative corresponding to a canonical even
frequency, including the separately normalized zero mode. -/
def factorTwoCanonicalEvenClippedRealMode
    (n : FactorTwoCanonicalEvenIndex) (x : ℝ) : ℝ :=
  if n.1 = 0 then clippedEvenZeroRealMode yoshidaA x
  else clippedEvenRealMode yoshidaA n.1 x

/-- The canonical centered profile is the clipped real profile after the
physical rescaling `x ↦ yoshidaA * x`. -/
theorem factorTwoCenteredCanonicalEvenProfile_eq_clipped
    (n : FactorTwoCanonicalEvenIndex) (x : ℝ) :
    factorTwoCenteredCanonicalEvenProfile n x =
      factorTwoCanonicalEvenClippedRealMode n (yoshidaA * x) := by
  by_cases hn : n.1 = 0
  · simp [factorTwoCenteredCanonicalEvenProfile,
      factorTwoCanonicalEvenClippedRealMode, clippedEvenZeroRealMode, hn]
  · simp only [factorTwoCenteredCanonicalEvenProfile,
      factorTwoCanonicalEvenClippedRealMode, hn, if_false,
      clippedEvenRealMode]
    congr 2
    field_simp [yoshidaA_pos.ne']

/-- Ordered clipped correlation for all canonical even frequencies. -/
def factorTwoCanonicalEvenClippedCorrelation
    (n m : FactorTwoCanonicalEvenIndex) (u : ℝ) : ℝ :=
  if n.1 = 0 then
    if m.1 = 0 then clippedEvenZeroCorrelation yoshidaA u
    else clippedEvenZeroPositiveCorrelation yoshidaA m.1 u
  else if m.1 = 0 then
    clippedEvenPositiveZeroCorrelation yoshidaA n.1 u
  else
    clippedEvenCorrelation yoshidaA n.1 m.1 u

/-- Centered rescaling divides the ordered clipped correlation by
`yoshidaA`. -/
theorem factorTwoCenteredCrossCorrelation_canonicalEven_eq_clipped
    (n m : FactorTwoCanonicalEvenIndex) (t : ℝ) :
    factorTwoCenteredCrossCorrelation
        (factorTwoCenteredCanonicalEvenProfile n)
        (factorTwoCenteredCanonicalEvenProfile m) t =
      factorTwoCanonicalEvenClippedCorrelation n m (yoshidaA * t) /
        yoshidaA := by
  let F : ℝ → ℝ := fun y ↦
    factorTwoCanonicalEvenClippedRealMode n (yoshidaA * t + y) *
      factorTwoCanonicalEvenClippedRealMode m y
  have hpoint :
      (fun x : ℝ ↦
        factorTwoCenteredCanonicalEvenProfile n (t + x) *
          factorTwoCenteredCanonicalEvenProfile m x) =
        fun x ↦ F (yoshidaA * x) := by
    funext x
    rw [factorTwoCenteredCanonicalEvenProfile_eq_clipped,
      factorTwoCenteredCanonicalEvenProfile_eq_clipped]
    dsimp only [F]
    congr 2
    ring
  have hscale :
      (∫ x : ℝ in -1..1 - t, F (yoshidaA * x)) =
        yoshidaA⁻¹ *
          ∫ y : ℝ in yoshidaA * (-1)..yoshidaA * (1 - t), F y := by
    simpa only [smul_eq_mul] using
      (intervalIntegral.integral_comp_mul_left
        (a := (-1 : ℝ)) (b := 1 - t) F yoshidaA_pos.ne')
  calc
    factorTwoCenteredCrossCorrelation
        (factorTwoCenteredCanonicalEvenProfile n)
        (factorTwoCenteredCanonicalEvenProfile m) t =
        ∫ x : ℝ in -1..1 - t, F (yoshidaA * x) := by
      unfold factorTwoCenteredCrossCorrelation
      rw [hpoint]
    _ = yoshidaA⁻¹ *
          ∫ y : ℝ in yoshidaA * (-1)..yoshidaA * (1 - t), F y :=
      hscale
    _ = yoshidaA⁻¹ *
          ∫ y : ℝ in -yoshidaA..yoshidaA - yoshidaA * t, F y := by
      congr 2 <;> ring
    _ = factorTwoCanonicalEvenClippedCorrelation n m (yoshidaA * t) /
          yoshidaA := by
      dsimp only [F]
      unfold factorTwoCanonicalEvenClippedCorrelation
        factorTwoCanonicalEvenClippedRealMode
      by_cases hn : n.1 = 0 <;> by_cases hm : m.1 = 0 <;>
        simp only [hn, hm, if_pos, if_false] <;>
        simp [clippedEvenZeroCorrelation,
          clippedEvenZeroPositiveCorrelation,
          clippedEvenPositiveZeroCorrelation, clippedEvenCorrelation,
          div_eq_mul_inv, mul_comm]

/-- Canonical frequency after scaling to the unit interval. -/
def factorTwoCanonicalEvenFrequency (n : FactorTwoCanonicalEvenIndex) : ℝ :=
  clippedEvenFrequency 1 n.1

theorem clippedEvenFrequency_yoshidaA_eq
    (n : FactorTwoCanonicalEvenIndex) :
    clippedEvenFrequency yoshidaA n.1 =
      factorTwoCanonicalEvenFrequency n / yoshidaA := by
  unfold factorTwoCanonicalEvenFrequency clippedEvenFrequency
  field_simp [yoshidaA_pos.ne']

theorem clippedEvenFrequency_yoshidaA_mul
    (n : FactorTwoCanonicalEvenIndex) (t : ℝ) :
    clippedEvenFrequency yoshidaA n.1 * (yoshidaA * t) =
      factorTwoCanonicalEvenFrequency n * t := by
  rw [clippedEvenFrequency_yoshidaA_eq]
  field_simp [yoshidaA_pos.ne']

/-- The zero/zero canonical even correlation branch. -/
def factorTwoCanonicalEvenZeroZeroCorrelationFormula (t : ℝ) : ℝ :=
  ((2 - t) / 2) / yoshidaA

/-- A zero/positive canonical even correlation branch. -/
def factorTwoCanonicalEvenZeroPositiveCorrelationFormula
    (m : FactorTwoCanonicalEvenIndex) (t : ℝ) : ℝ :=
  (((-1 : ℝ) ^ (m.1 + 1) *
      Real.sin (factorTwoCanonicalEvenFrequency m * t) /
        (Real.sqrt 2 * factorTwoCanonicalEvenFrequency m)) / yoshidaA)

/-- A positive/zero canonical even correlation branch. -/
def factorTwoCanonicalEvenPositiveZeroCorrelationFormula
    (n : FactorTwoCanonicalEvenIndex) (t : ℝ) : ℝ :=
  (((-1 : ℝ) ^ (n.1 + 1) *
      Real.sin (factorTwoCanonicalEvenFrequency n * t) /
        (Real.sqrt 2 * factorTwoCanonicalEvenFrequency n)) / yoshidaA)

/-- A positive-frequency diagonal canonical even correlation branch. -/
def factorTwoCanonicalEvenDiagonalCorrelationFormula
    (n : FactorTwoCanonicalEvenIndex) (t : ℝ) : ℝ :=
  ((((2 - t) * Real.cos (factorTwoCanonicalEvenFrequency n * t) -
      Real.sin (factorTwoCanonicalEvenFrequency n * t) /
        factorTwoCanonicalEvenFrequency n) / 2) / yoshidaA)

/-- A positive-frequency off-diagonal canonical even correlation branch. -/
def factorTwoCanonicalEvenOffDiagonalCorrelationFormula
    (n m : FactorTwoCanonicalEvenIndex) (t : ℝ) : ℝ :=
  (((-1 : ℝ) ^ (n.1 + m.1) *
      (factorTwoCanonicalEvenFrequency m *
          Real.sin (factorTwoCanonicalEvenFrequency m * t) -
        factorTwoCanonicalEvenFrequency n *
          Real.sin (factorTwoCanonicalEvenFrequency n * t)) /
      (factorTwoCanonicalEvenFrequency n ^ 2 -
        factorTwoCanonicalEvenFrequency m ^ 2)) / yoshidaA)

/-- A single explicit branch formula covering all canonical even
frequencies `0, ..., 200`. -/
def factorTwoCanonicalEvenCorrelationFormula
    (n m : FactorTwoCanonicalEvenIndex) (t : ℝ) : ℝ :=
  if n.1 = 0 then
    if m.1 = 0 then factorTwoCanonicalEvenZeroZeroCorrelationFormula t
    else factorTwoCanonicalEvenZeroPositiveCorrelationFormula m t
  else if m.1 = 0 then
    factorTwoCanonicalEvenPositiveZeroCorrelationFormula n t
  else if n = m then
    factorTwoCanonicalEvenDiagonalCorrelationFormula n t
  else
    factorTwoCanonicalEvenOffDiagonalCorrelationFormula n m t

private theorem factorTwoCanonicalEvenFrequency_ne_zero
    {n : FactorTwoCanonicalEvenIndex} (hn : n.1 ≠ 0) :
    factorTwoCanonicalEvenFrequency n ≠ 0 := by
  unfold factorTwoCanonicalEvenFrequency clippedEvenFrequency
  positivity

private theorem factorTwoCanonicalEvenFrequency_sq_sub_ne_zero
    {n m : FactorTwoCanonicalEvenIndex} (hnm : n ≠ m) :
    factorTwoCanonicalEvenFrequency n ^ 2 -
        factorTwoCanonicalEvenFrequency m ^ 2 ≠ 0 := by
  have hval : n.1 ≠ m.1 := by
    intro h
    apply hnm
    exact Fin.ext h
  unfold factorTwoCanonicalEvenFrequency clippedEvenFrequency
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  intro h
  field_simp at h
  apply hval
  have hpipos : 0 < Real.pi ^ 2 := sq_pos_of_ne_zero hpi
  have hsquares : (n.1 : ℝ) ^ 2 = (m.1 : ℝ) ^ 2 := by
    nlinarith [h, hpipos]
  have hnonnegN : 0 ≤ (n.1 : ℝ) := by positivity
  have hnonnegM : 0 ≤ (m.1 : ℝ) := by positivity
  have : (n.1 : ℝ) = (m.1 : ℝ) := by nlinarith
  exact_mod_cast this

/-- The ordered clipped correlation, after centered rescaling, equals the
explicit five-branch unit-frequency formula. -/
theorem factorTwoCanonicalEvenClippedCorrelation_div_eq_formula
    (n m : FactorTwoCanonicalEvenIndex) (t : ℝ) :
    factorTwoCanonicalEvenClippedCorrelation n m (yoshidaA * t) /
        yoshidaA =
      factorTwoCanonicalEvenCorrelationFormula n m t := by
  by_cases hn : n.1 = 0
  · by_cases hm : m.1 = 0
    · simp only [factorTwoCanonicalEvenClippedCorrelation,
        factorTwoCanonicalEvenCorrelationFormula, hn, hm, if_pos]
      rw [clippedEvenZeroCorrelation_eq yoshidaA_pos]
      unfold factorTwoCanonicalEvenZeroZeroCorrelationFormula
      field_simp [yoshidaA_pos.ne']
    · simp only [factorTwoCanonicalEvenClippedCorrelation,
        factorTwoCanonicalEvenCorrelationFormula, hn, hm, if_pos, if_false]
      rw [clippedEvenZeroPositiveCorrelation_eq yoshidaA_pos hm,
        clippedEvenFrequency_yoshidaA_mul,
        clippedEvenFrequency_yoshidaA_eq]
      unfold factorTwoCanonicalEvenZeroPositiveCorrelationFormula
      field_simp [yoshidaA_pos.ne',
        factorTwoCanonicalEvenFrequency_ne_zero hm]
  · by_cases hm : m.1 = 0
    · simp only [factorTwoCanonicalEvenClippedCorrelation,
        factorTwoCanonicalEvenCorrelationFormula, hn, hm, if_pos, if_false]
      rw [clippedEvenPositiveZeroCorrelation_eq yoshidaA_pos hn,
        clippedEvenFrequency_yoshidaA_mul,
        clippedEvenFrequency_yoshidaA_eq]
      unfold factorTwoCanonicalEvenPositiveZeroCorrelationFormula
      field_simp [yoshidaA_pos.ne',
        factorTwoCanonicalEvenFrequency_ne_zero hn]
    · by_cases hnm : n = m
      · subst m
        simp only [factorTwoCanonicalEvenClippedCorrelation,
          factorTwoCanonicalEvenCorrelationFormula, hn, if_false, if_pos]
        rw [clippedEvenCorrelation_diag yoshidaA_pos hn,
          clippedEvenFrequency_yoshidaA_mul,
          clippedEvenFrequency_yoshidaA_eq]
        unfold factorTwoCanonicalEvenDiagonalCorrelationFormula
        field_simp [yoshidaA_pos.ne',
          factorTwoCanonicalEvenFrequency_ne_zero hn]
      · have hval : n.1 ≠ m.1 := by
          intro h
          apply hnm
          exact Fin.ext h
        simp only [factorTwoCanonicalEvenClippedCorrelation,
          factorTwoCanonicalEvenCorrelationFormula, hn, hm, hnm,
          if_false]
        rw [clippedEvenCorrelation_offdiag yoshidaA_pos hn hm hval,
          clippedEvenFrequency_yoshidaA_mul,
          clippedEvenFrequency_yoshidaA_mul,
          clippedEvenFrequency_yoshidaA_eq,
          clippedEvenFrequency_yoshidaA_eq]
        unfold factorTwoCanonicalEvenOffDiagonalCorrelationFormula
        field_simp [yoshidaA_pos.ne',
          factorTwoCanonicalEvenFrequency_sq_sub_ne_zero hnm]

/-- The symmetric centered correlation is exactly the explicit canonical
even formula.  The interval hypotheses describe its production domain. -/
theorem factorTwoCenteredCorrelationBilinear_canonicalEven_eq_formula
    (n m : FactorTwoCanonicalEvenIndex) {t : ℝ}
    (_ht0 : 0 ≤ t) (_ht2 : t ≤ 2) :
    factorTwoCenteredCorrelationBilinear
        (factorTwoCenteredCanonicalEvenProfile n)
        (factorTwoCenteredCanonicalEvenProfile m) t =
      factorTwoCanonicalEvenCorrelationFormula n m t := by
  have hcomm :
      factorTwoCanonicalEvenClippedCorrelation n m (yoshidaA * t) =
        factorTwoCanonicalEvenClippedCorrelation m n (yoshidaA * t) := by
    by_cases hn : n.1 = 0
    · by_cases hm : m.1 = 0
      · simp [factorTwoCanonicalEvenClippedCorrelation, hn, hm]
      · simp only [factorTwoCanonicalEvenClippedCorrelation, hn, hm,
          if_pos, if_false]
        rw [clippedEvenZeroPositiveCorrelation_eq yoshidaA_pos hm,
          clippedEvenPositiveZeroCorrelation_eq yoshidaA_pos hm]
    · by_cases hm : m.1 = 0
      · simp only [factorTwoCanonicalEvenClippedCorrelation, hn, hm,
          if_pos, if_false]
        rw [clippedEvenPositiveZeroCorrelation_eq yoshidaA_pos hn,
          clippedEvenZeroPositiveCorrelation_eq yoshidaA_pos hn]
      · by_cases hnm : n = m
        · subst m
          rfl
        · have hval : n.1 ≠ m.1 := by
            intro h
            apply hnm
            exact Fin.ext h
          simp only [factorTwoCanonicalEvenClippedCorrelation, hn, hm,
            if_false]
          rw [clippedEvenCorrelation_offdiag yoshidaA_pos hn hm hval,
            clippedEvenCorrelation_offdiag yoshidaA_pos hm hn
              (Ne.symm hval)]
          rw [add_comm m.1 n.1]
          have hden :
              clippedEvenFrequency yoshidaA n.1 ^ 2 -
                  clippedEvenFrequency yoshidaA m.1 ^ 2 ≠ 0 := by
            rw [clippedEvenFrequency_yoshidaA_eq,
              clippedEvenFrequency_yoshidaA_eq]
            intro h
            apply factorTwoCanonicalEvenFrequency_sq_sub_ne_zero hnm
            field_simp [yoshidaA_pos.ne'] at h
            simpa using h
          rw [show
              clippedEvenFrequency yoshidaA n.1 *
                    Real.sin (clippedEvenFrequency yoshidaA n.1 *
                      (yoshidaA * t)) -
                  clippedEvenFrequency yoshidaA m.1 *
                    Real.sin (clippedEvenFrequency yoshidaA m.1 *
                      (yoshidaA * t)) =
                -(clippedEvenFrequency yoshidaA m.1 *
                    Real.sin (clippedEvenFrequency yoshidaA m.1 *
                      (yoshidaA * t)) -
                  clippedEvenFrequency yoshidaA n.1 *
                    Real.sin (clippedEvenFrequency yoshidaA n.1 *
                      (yoshidaA * t))) by ring]
          rw [show
              clippedEvenFrequency yoshidaA m.1 ^ 2 -
                  clippedEvenFrequency yoshidaA n.1 ^ 2 =
                -(clippedEvenFrequency yoshidaA n.1 ^ 2 -
                  clippedEvenFrequency yoshidaA m.1 ^ 2) by ring]
          field_simp [hden]
  unfold factorTwoCenteredCorrelationBilinear
  rw [factorTwoCenteredCrossCorrelation_canonicalEven_eq_clipped,
    factorTwoCenteredCrossCorrelation_canonicalEven_eq_clipped,
    ← hcomm]
  rw [factorTwoCanonicalEvenClippedCorrelation_div_eq_formula]
  ring

/-- The complete perturbation functional applied to an explicit canonical
even correlation formula. -/
def factorTwoCanonicalEvenPerturbationEntryFormula (C : ℝ → ℝ) : ℝ :=
  yoshidaEndpointA *
      (∫ t : ℝ in 0..2,
        factorTwoSymmetricWeight (yoshidaEndpointA * t) * C t) -
    (Real.log 2 / Real.sqrt 2) * C 0 -
    (Real.log 3 / Real.sqrt 3) *
      C (factorTwoPrimeShift / yoshidaEndpointA)

/-- Every canonical even perturbation entry is the weighted integral of its
explicit five-branch correlation, together with the exact `p = 2` and `p = 3`
atoms. -/
theorem factorTwoCanonicalEvenPerturbationEntry_apply
    (n m : FactorTwoCanonicalEvenIndex) :
    factorTwoCanonicalEvenPerturbationEntry n m =
      factorTwoCanonicalEvenPerturbationEntryFormula
        (factorTwoCanonicalEvenCorrelationFormula n m) := by
  have hint :
      (∫ t : ℝ in 0..2,
        factorTwoSymmetricWeight (yoshidaEndpointA * t) *
          factorTwoCenteredCorrelationBilinear
            (factorTwoCenteredCanonicalEvenProfile n)
            (factorTwoCenteredCanonicalEvenProfile m) t) =
        ∫ t : ℝ in 0..2,
          factorTwoSymmetricWeight (yoshidaEndpointA * t) *
            factorTwoCanonicalEvenCorrelationFormula n m t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
    change factorTwoSymmetricWeight (yoshidaEndpointA * t) *
        factorTwoCenteredCorrelationBilinear
          (factorTwoCenteredCanonicalEvenProfile n)
          (factorTwoCenteredCanonicalEvenProfile m) t =
      factorTwoSymmetricWeight (yoshidaEndpointA * t) *
        factorTwoCanonicalEvenCorrelationFormula n m t
    rw [factorTwoCenteredCorrelationBilinear_canonicalEven_eq_formula
      n m ht.1 ht.2]
  have hzero :=
    factorTwoCenteredCorrelationBilinear_canonicalEven_eq_formula
      n m (t := 0) (by norm_num) (by norm_num)
  have hprime :=
    factorTwoCenteredCorrelationBilinear_canonicalEven_eq_formula
      n m
      (by linarith [factorTwoPrimeShift_div_endpointA_mem_one_two.1])
      factorTwoPrimeShift_div_endpointA_mem_one_two.2
  unfold factorTwoCanonicalEvenPerturbationEntry
    factorTwoCenteredSymmetricPerturbationBilinear
    factorTwoCanonicalEvenPerturbationEntryFormula
  rw [hint, hzero, hprime]

/-- Every endpoint-adapted concrete even entry is the four-term pullback of
the explicit canonical perturbation formulas. -/
theorem factorTwoConcreteEvenPerturbationMatrix_apply
    (i j : YoshidaEvenIndex) :
    factorTwoConcreteEvenPerturbationMatrix i j =
      factorTwoCanonicalEvenPerturbationEntryFormula
          (factorTwoCanonicalEvenCorrelationFormula
            (factorTwoCanonicalEvenLowIndex i)
            (factorTwoCanonicalEvenLowIndex j)) -
        endpointEvenLowTraceRatio j *
          factorTwoCanonicalEvenPerturbationEntryFormula
            (factorTwoCanonicalEvenCorrelationFormula
              (factorTwoCanonicalEvenLowIndex i)
              factorTwoCanonicalEvenTopIndex) -
        endpointEvenLowTraceRatio i *
          factorTwoCanonicalEvenPerturbationEntryFormula
            (factorTwoCanonicalEvenCorrelationFormula
              factorTwoCanonicalEvenTopIndex
              (factorTwoCanonicalEvenLowIndex j)) +
        endpointEvenLowTraceRatio i * endpointEvenLowTraceRatio j *
          factorTwoCanonicalEvenPerturbationEntryFormula
            (factorTwoCanonicalEvenCorrelationFormula
              factorTwoCanonicalEvenTopIndex
              factorTwoCanonicalEvenTopIndex) := by
  rw [factorTwoConcreteEvenPerturbationMatrix_eq_canonical_update,
    factorTwoCanonicalEvenPerturbationEntry_apply,
    factorTwoCanonicalEvenPerturbationEntry_apply,
    factorTwoCanonicalEvenPerturbationEntry_apply,
    factorTwoCanonicalEvenPerturbationEntry_apply]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteEvenPerturbationFormula
