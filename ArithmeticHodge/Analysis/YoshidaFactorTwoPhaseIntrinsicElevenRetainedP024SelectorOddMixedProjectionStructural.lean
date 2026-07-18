import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorOddProjectionStructural

set_option autoImplicit false

open Matrix MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorOddMixedProjectionStructural

open FiniteWeightedSelectorProjection
open ShiftedLegendreLogEnergyOrthogonalProjection
open ShiftedLegendreOrthogonality
open YoshidaEndpointPotentialBound
open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoFixedLagRepresenterStructural
open YoshidaFactorTwoPhaseEnvelope
open YoshidaFactorTwoPhaseIntrinsicElevenConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorOddProjectionStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorPoleRemainderStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorQuotientStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorRemainderGramStructural

noncomputable section

/-!
# Mixed polynomial and prime-step projection for the favorable odd remainder

The odd retained representers contain the fixed prime-lag step profiles.
Adding those three exact rows to a finite odd shifted-Legendre family captures
that finite-rank discontinuous component without approximating it by a long
polynomial expansion.
-/

/-- The fixed prime lag in centered endpoint coordinates. -/
def retainedP024PrimeLag : ℝ :=
  factorTwoPrimeShift / yoshidaEndpointA

/-- Raw alternating prime-step profile attached to the `i`th P024 mode. -/
def retainedP024OddPrimeStepRow (i : Fin 3) (x : ℝ) : ℝ :=
  factorTwoFixedLagJ retainedP024PrimeLag
    (centeredPolynomialLift (retainedP024EvenMode i)) x

theorem retainedP024PrimeLag_mem_Icc :
    retainedP024PrimeLag ∈ Icc (0 : ℝ) 2 := by
  have h := factorTwoPrimeShift_div_endpointA_mem_one_two
  unfold retainedP024PrimeLag
  exact ⟨(by linarith [h.1]), h.2⟩

theorem measurable_retainedP024OddPrimeStepRow (i : Fin 3) :
    Measurable (retainedP024OddPrimeStepRow i) := by
  have hp : Continuous
      (centeredPolynomialLift (retainedP024EvenMode i)) := by
    unfold centeredPolynomialLift
    fun_prop
  have hright : Measurable (fun z : ℝ ↦
      centeredPolynomialLift (retainedP024EvenMode i)
        (retainedP024PrimeLag + z)) :=
    (hp.comp (continuous_const.add continuous_id)).measurable
  have hleft : Measurable (fun z : ℝ ↦
      centeredPolynomialLift (retainedP024EvenMode i)
        (z - retainedP024PrimeLag)) :=
    (hp.comp (continuous_id.sub continuous_const)).measurable
  unfold retainedP024OddPrimeStepRow factorTwoFixedLagJ
    factorTwoFixedLagRightRepresenter factorTwoFixedLagLeftRepresenter
  exact (hright.indicator measurableSet_Icc).sub
    (hleft.indicator measurableSet_Icc)

private theorem exists_centeredPolynomialLift_abs_bound (p : ℝ[X]) :
    ∃ M : ℝ, 0 < M ∧
      ∀ z ∈ Icc (-1 : ℝ) 1, |centeredPolynomialLift p z| ≤ M := by
  have hp : Continuous (centeredPolynomialLift p) := by
    unfold centeredPolynomialLift
    fun_prop
  obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)) hp.continuousOn
  refine ⟨|M| + 1, by positivity, ?_⟩
  intro z hz
  have hzBound := hM z hz
  rw [Real.norm_eq_abs] at hzBound
  linarith [le_abs_self M]

theorem exists_retainedP024OddPrimeStepRow_abs_bound (i : Fin 3) :
    ∃ B : ℝ, 0 < B ∧
      ∀ x ∈ Ioc (-1 : ℝ) 1,
        |retainedP024OddPrimeStepRow i x| ≤ B := by
  obtain ⟨M, hMpos, hM⟩ :=
    exists_centeredPolynomialLift_abs_bound (retainedP024EvenMode i)
  refine ⟨2 * M, mul_pos (by norm_num) hMpos, ?_⟩
  intro x hx
  have hτ := retainedP024PrimeLag_mem_Icc
  have hright :
      |factorTwoFixedLagRightRepresenter retainedP024PrimeLag
          (centeredPolynomialLift (retainedP024EvenMode i)) x| ≤ M := by
    unfold factorTwoFixedLagRightRepresenter
    by_cases hs : x ∈ Icc (-1 : ℝ) (1 - retainedP024PrimeLag)
    · rw [Set.indicator_of_mem hs]
      apply hM
      exact ⟨by linarith [hs.1, hτ.1], by linarith [hs.2]⟩
    · rw [Set.indicator_of_notMem hs, abs_zero]
      exact hMpos.le
  have hleft :
      |factorTwoFixedLagLeftRepresenter retainedP024PrimeLag
          (centeredPolynomialLift (retainedP024EvenMode i)) x| ≤ M := by
    unfold factorTwoFixedLagLeftRepresenter
    by_cases hs : x ∈ Icc (-1 + retainedP024PrimeLag) 1
    · rw [Set.indicator_of_mem hs]
      apply hM
      exact ⟨by linarith [hs.1], by linarith [hs.2, hτ.1]⟩
    · rw [Set.indicator_of_notMem hs, abs_zero]
      exact hMpos.le
  unfold retainedP024OddPrimeStepRow factorTwoFixedLagJ
  exact (abs_sub _ _).trans ((add_le_add hright hleft).trans_eq (by ring))

/-- The weighted prime-step comparison row used by the finite Gram. -/
def retainedP024OddPrimeStepWeightedRow (i : Fin 3) (x : ℝ) : ℝ :=
  factorTwoIntrinsicElevenRetainedOddWeight x *
    retainedP024OddPrimeStepRow i x

theorem retainedP024OddPrimeStepWeightedRow_div_sqrt_memLp_two
    (i : Fin 3) :
    MemLp (fun x ↦
      retainedP024OddPrimeStepWeightedRow i x /
        Real.sqrt (factorTwoIntrinsicElevenRetainedOddWeight x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  obtain ⟨B, hBpos, hB⟩ := exists_retainedP024OddPrimeStepRow_abs_bound i
  have hWmeas : Measurable factorTwoIntrinsicElevenRetainedOddWeight := by
    unfold factorTwoIntrinsicElevenRetainedOddWeight yoshidaEndpointPotential
    fun_prop
  have hGmeas : Measurable (retainedP024OddPrimeStepWeightedRow i) := by
    unfold retainedP024OddPrimeStepWeightedRow
    exact hWmeas.mul (measurable_retainedP024OddPrimeStepRow i)
  apply div_sqrt_memLp_two_of_abs_le_const_mul_weight
    factorTwoIntrinsicElevenRetainedOddWeight
    (retainedP024OddPrimeStepWeightedRow i)
    hWmeas hGmeas.aestronglyMeasurable B
    (fun x hx ↦ factorTwoIntrinsicElevenRetainedOddWeight_pos_on_Icc
      ⟨hx.1.le, hx.2⟩)
  · intro x hx
    have hW := factorTwoIntrinsicElevenRetainedOddWeight_pos_on_Icc
      ⟨hx.1.le, hx.2⟩
    unfold retainedP024OddPrimeStepWeightedRow
    rw [abs_mul, abs_of_pos hW]
    nlinarith [hB x hx]
  · simpa using sqrt_retainedOddWeight_mul_memLp_two
      (fun _x : ℝ ↦ (1 : ℝ)) continuous_const

/-- Raw comparison family: finitely many centered shifted-Legendre modes,
followed by the three exact prime-step rows. -/
def retainedP024OddMixedProjectionRow
    {κ : Type*} (ν : κ → ℕ) : κ ⊕ Fin 3 → ℝ → ℝ
  | Sum.inl k => centeredPolynomialLift (shiftedLegendreReal (ν k))
  | Sum.inr i => retainedP024OddPrimeStepRow i

/-- Weighted version of the mixed comparison family. -/
def retainedP024OddMixedProjectionWeightedRow
    {κ : Type*} (ν : κ → ℕ) (k : κ ⊕ Fin 3) (x : ℝ) : ℝ :=
  factorTwoIntrinsicElevenRetainedOddWeight x *
    retainedP024OddMixedProjectionRow ν k x

def retainedP024OddMixedProjectionCrossGram
    {κ : Type*} [Fintype κ] (ν : κ → ℕ) :
    Matrix (Fin 3) (κ ⊕ Fin 3) ℝ :=
  finiteWeightedCrossGram
    factorTwoIntrinsicElevenRetainedOddWeight
    retainedP024SelectorAlternatingShiftedRemainder
    (retainedP024OddMixedProjectionWeightedRow ν)

def retainedP024OddMixedProjectionModeGram
    {κ : Type*} [Fintype κ] (ν : κ → ℕ) :
    Matrix (κ ⊕ Fin 3) (κ ⊕ Fin 3) ℝ :=
  finiteWeightedGram
    factorTwoIntrinsicElevenRetainedOddWeight
    (retainedP024OddMixedProjectionWeightedRow ν)

def retainedP024OddMixedProjectionLowerGram
    {κ : Type*} [Fintype κ]
    (ν : κ → ℕ) (C : Matrix (Fin 3) (κ ⊕ Fin 3) ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  retainedP024OddMixedProjectionCrossGram ν * Cᴴ +
    C * (retainedP024OddMixedProjectionCrossGram ν)ᴴ -
    C * retainedP024OddMixedProjectionModeGram ν * Cᴴ

theorem retainedP024OddMixedProjectionWeightedRow_div_sqrt_memLp_two
    {κ : Type*} (ν : κ → ℕ) (k : κ ⊕ Fin 3) :
    MemLp (fun x ↦
      retainedP024OddMixedProjectionWeightedRow ν k x /
        Real.sqrt (factorTwoIntrinsicElevenRetainedOddWeight x)) 2
      (volume.restrict (Ioc (-1 : ℝ) 1)) := by
  rcases k with k | i
  · simpa [retainedP024OddMixedProjectionWeightedRow,
      retainedP024OddMixedProjectionRow,
      retainedP024OddProjectionWeightedRow] using
      retainedP024OddProjectionWeightedRow_div_sqrt_memLp_two ν k
  · simpa [retainedP024OddMixedProjectionWeightedRow,
      retainedP024OddMixedProjectionRow,
      retainedP024OddPrimeStepWeightedRow] using
      retainedP024OddPrimeStepWeightedRow_div_sqrt_memLp_two i

/-- The mixed polynomial/prime-step family gives an inverse-free Loewner
lower bound for the favorable odd shifted-remainder Gram. -/
theorem retainedP024OddMixedProjectionLowerGram_le
    {κ : Type*} [Fintype κ]
    (ν : κ → ℕ) (C : Matrix (Fin 3) (κ ⊕ Fin 3) ℝ) :
    (retainedP024SelectorAlternatingShiftedRemainderGram -
      retainedP024OddMixedProjectionLowerGram ν C).PosSemidef := by
  simpa [retainedP024SelectorAlternatingShiftedRemainderGram,
    retainedP024OddMixedProjectionLowerGram,
    retainedP024OddMixedProjectionCrossGram,
    retainedP024OddMixedProjectionModeGram,
    finiteWeightedGram] using
    finiteWeightedProjectionResidual_posSemidef
      factorTwoIntrinsicElevenRetainedOddWeight
      retainedP024SelectorAlternatingShiftedRemainder
      (retainedP024OddMixedProjectionWeightedRow ν)
      (fun x hx ↦ factorTwoIntrinsicElevenRetainedOddWeight_pos_on_Icc hx)
      retainedP024SelectorAlternatingShiftedRemainder_div_sqrt_memLp_two
      (retainedP024OddMixedProjectionWeightedRow_div_sqrt_memLp_two ν) C

/-! ## Fixed eleven-mode plus prime-step certificate family -/

/-- Odd shifted-Legendre degrees `1,3,...,21`. -/
def retainedP024OddMixedProjectionDegree (k : Fin 11) : ℕ :=
  2 * k.1 + 1

/-- Rational polynomial-mode coefficients, rounded with denominator `10^4`.
The signs use the repository's centered shifted-Legendre convention. -/
def retainedP024OddMixedProjectionPolynomialCoefficient :
    Matrix (Fin 3) (Fin 11) ℝ :=
  ![![-5.8823, 4.2921, -3.5116, 2.2212, -0.7047, 0.0307,
      -0.2006, 0.0671, -0.1404, 0.0457, -0.0906],
    ![-2.4594, 1.5929, -3.2712, 3.1651, -1.8179, 0.7009,
      -0.4768, 0.1884, -0.1763, 0.0583, -0.0875],
    ![-28.2454, -14.9867, 5.3193, 2.5476, -3.6083, 2.1396,
      -1.1679, 0.5313, -0.2966, 0.1038, -0.0834]]

/-- Rational prime-step coefficients, rounded with denominator `10^4`. -/
def retainedP024OddMixedProjectionPrimeCoefficient :
    Matrix (Fin 3) (Fin 3) ℝ :=
  ![![4.9634, 1.5489, 1.3462],
    ![2.8047, 1.2096, 3.8379],
    ![19.4933, -30.2666, 18.6233]]

/-- Combined exact rational coefficient matrix for the mixed projection. -/
def retainedP024OddMixedProjectionCoefficient :
    Matrix (Fin 3) (Fin 11 ⊕ Fin 3) ℝ := fun i k ↦
  Sum.elim
    (retainedP024OddMixedProjectionPolynomialCoefficient i)
    (retainedP024OddMixedProjectionPrimeCoefficient i) k

/-- The fixed sound lower Gram selected for the P024 closure. -/
def retainedP024OddMixedProjectionCertificateGram :
    Matrix (Fin 3) (Fin 3) ℝ :=
  retainedP024OddMixedProjectionLowerGram
    retainedP024OddMixedProjectionDegree
    retainedP024OddMixedProjectionCoefficient

theorem retainedP024OddMixedProjectionCertificateGram_le :
    (retainedP024SelectorAlternatingShiftedRemainderGram -
      retainedP024OddMixedProjectionCertificateGram).PosSemidef := by
  exact retainedP024OddMixedProjectionLowerGram_le
    retainedP024OddMixedProjectionDegree
    retainedP024OddMixedProjectionCoefficient

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorOddMixedProjectionStructural
