import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowMatrix
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEnvelope

set_option autoImplicit false

open Matrix MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteEvenPerturbationAdaptation

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaCoercivityNumerics
open YoshidaClippedEvenMomentBridge
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointScaledCorrelation
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseConcreteLowMatrix
open YoshidaFactorTwoPhaseEndpointAdaptedLow
open YoshidaFactorTwoPhaseEnvelope
open YoshidaFactorTwoPhaseLowSchur
open YoshidaWeightedTailBounds

/-!
# Endpoint adaptation of the concrete even perturbation block

The endpoint-adapted low modes use frequencies `0, ..., 199`, with one
shared correction in frequency `200`.  This file records the corresponding
four-term congruence formula for the complete factor-two perturbation.
-/

/-- The canonical even frequencies needed by endpoint adaptation. -/
abbrev FactorTwoCanonicalEvenIndex := Fin 201

/-- Embed a low even frequency into the canonical range `0, ..., 200`. -/
def factorTwoCanonicalEvenLowIndex
    (i : YoshidaEvenIndex) : FactorTwoCanonicalEvenIndex :=
  ⟨i.1, by omega⟩

/-- The shared endpoint-correction frequency. -/
def factorTwoCanonicalEvenTopIndex : FactorTwoCanonicalEvenIndex :=
  ⟨200, by omega⟩

/-- A globally continuous representative of the normalized centered even
mode.  Frequency zero has the canonical `1 / sqrt (2A)` normalization. -/
def factorTwoCenteredCanonicalEvenProfile
    (n : FactorTwoCanonicalEvenIndex) : ℝ → ℝ :=
  if n.1 = 0 then
    fun _ ↦ (Real.sqrt (2 * yoshidaA))⁻¹
  else
    fun x ↦ (Real.sqrt yoshidaA)⁻¹ *
      Real.cos (Real.pi * (n.1 : ℝ) * x)

theorem continuous_factorTwoCenteredCanonicalEvenProfile
    (n : FactorTwoCanonicalEvenIndex) :
    Continuous (factorTwoCenteredCanonicalEvenProfile n) := by
  unfold factorTwoCenteredCanonicalEvenProfile
  split_ifs <;> fun_prop

/-- The complete symmetric perturbation entry in the canonical centered
even basis on frequencies `0, ..., 200`. -/
def factorTwoCanonicalEvenPerturbationEntry
    (n m : FactorTwoCanonicalEvenIndex) : ℝ :=
  factorTwoCenteredSymmetricPerturbationBilinear
    (factorTwoCenteredCanonicalEvenProfile n)
    (factorTwoCenteredCanonicalEvenProfile m)

/-- On the centered endpoint interval, an adapted low mode is its canonical
mode minus its trace ratio times frequency `200`. -/
theorem factorTwoCenteredAdaptedEvenLowProfile_eq_canonical_sub
    (i : YoshidaEvenIndex) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    factorTwoCenteredAdaptedEvenLowProfile i x =
      factorTwoCenteredCanonicalEvenProfile
          (factorTwoCanonicalEvenLowIndex i) x -
        endpointEvenLowTraceRatio i *
          factorTwoCenteredCanonicalEvenProfile
            factorTwoCanonicalEvenTopIndex x := by
  have hAx : yoshidaA * x ∈ Set.Icc (-yoshidaA) yoshidaA := by
    constructor
    · nlinarith [yoshidaA_pos, hx.1]
    · nlinarith [yoshidaA_pos, hx.2]
  have harg (n : ℕ) :
      Real.pi * (n : ℝ) * (yoshidaA * x) / yoshidaA =
        Real.pi * (n : ℝ) * x := by
    field_simp [yoshidaA_pos.ne']
  have hcenterC (n : ℕ) :
      (Real.pi : ℂ) * (n : ℂ) * (x : ℂ) =
        ((Real.pi * (n : ℝ) * x : ℝ) : ℂ) := by
    push_cast
    rfl
  have htopArgC :
      (Real.pi : ℂ) * 200 *
          ((yoshidaA : ℂ) * (x : ℂ)) / (yoshidaA : ℂ) =
        ((Real.pi * 200 * x : ℝ) : ℂ) := by
    push_cast
    field_simp [yoshidaA_pos.ne']
  have htopCenterC :
      (Real.pi : ℂ) * 200 * (x : ℂ) =
        ((Real.pi * 200 * x : ℝ) : ℂ) := by
    push_cast
    rfl
  have hpowC (n : ℕ) :
      (-1 : ℂ) ^ n = (((-1 : ℝ) ^ n : ℝ) : ℂ) := by
    norm_cast
  have hinvSqrtTwo : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
    have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
    have hsquare : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    field_simp [hsqrt]
    nlinarith
  by_cases hi : i.1 = 0
  · simp [factorTwoCenteredAdaptedEvenLowProfile, centeredRescale,
      endpointAdaptedEvenLowMode, yoshidaClippedEvenLowMode, hi,
      endpointEvenLowTraceRatio, factorTwoCenteredCanonicalEvenProfile,
      factorTwoCanonicalEvenLowIndex, factorTwoCanonicalEvenTopIndex,
      yoshidaClippedEvenZeroMode_apply_of_mem hAx,
      yoshidaClippedEvenMode_apply_of_mem yoshidaA_pos 200 hAx,
      hinvSqrtTwo]
    left
    rw [htopArgC, Complex.cos_ofReal_re]
  · simp [factorTwoCenteredAdaptedEvenLowProfile, centeredRescale,
      endpointAdaptedEvenLowMode, yoshidaClippedEvenLowMode, hi,
      endpointEvenLowTraceRatio, factorTwoCenteredCanonicalEvenProfile,
      factorTwoCanonicalEvenLowIndex, factorTwoCanonicalEvenTopIndex,
      yoshidaClippedEvenMode_apply_of_mem yoshidaA_pos i.1 hAx,
      yoshidaClippedEvenMode_apply_of_mem yoshidaA_pos 200 hAx,
      harg]
    rw [hcenterC i.1, htopArgC, hpowC,
      Complex.cos_ofReal_re, Complex.cos_ofReal_im]
    simp
    rw [htopCenterC, hpowC i.1, Complex.cos_ofReal_re]
    simp
    left
    norm_cast

private theorem factorTwoCenteredCrossCorrelation_congr_Icc
    {u u' v v' : ℝ → ℝ}
    (hu : ∀ x ∈ Set.Icc (-1 : ℝ) 1, u x = u' x)
    (hv : ∀ x ∈ Set.Icc (-1 : ℝ) 1, v x = v' x)
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    factorTwoCenteredCrossCorrelation u v t =
      factorTwoCenteredCrossCorrelation u' v' t := by
  unfold factorTwoCenteredCrossCorrelation
  apply intervalIntegral.integral_congr
  intro x hx
  rw [Set.uIcc_of_le (by linarith : (-1 : ℝ) ≤ 1 - t)] at hx
  have hxIcc : x ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  have htxIcc : t + x ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  change u (t + x) * v x = u' (t + x) * v' x
  rw [hu (t + x) htxIcc, hv x hxIcc]

private theorem factorTwoCenteredCorrelationBilinear_congr_Icc
    {u u' v v' : ℝ → ℝ}
    (hu : ∀ x ∈ Set.Icc (-1 : ℝ) 1, u x = u' x)
    (hv : ∀ x ∈ Set.Icc (-1 : ℝ) 1, v x = v' x)
    {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    factorTwoCenteredCorrelationBilinear u v t =
      factorTwoCenteredCorrelationBilinear u' v' t := by
  unfold factorTwoCenteredCorrelationBilinear
  rw [factorTwoCenteredCrossCorrelation_congr_Icc hu hv ht0 ht2,
    factorTwoCenteredCrossCorrelation_congr_Icc hv hu ht0 ht2]

private theorem factorTwoCenteredSymmetricPerturbationBilinear_congr_Icc
    {u u' v v' : ℝ → ℝ}
    (hu : ∀ x ∈ Set.Icc (-1 : ℝ) 1, u x = u' x)
    (hv : ∀ x ∈ Set.Icc (-1 : ℝ) 1, v x = v' x) :
    factorTwoCenteredSymmetricPerturbationBilinear u v =
      factorTwoCenteredSymmetricPerturbationBilinear u' v' := by
  have hint :
      (∫ t : ℝ in 0..2,
          factorTwoSymmetricWeight (yoshidaEndpointA * t) *
            factorTwoCenteredCorrelationBilinear u v t) =
        ∫ t : ℝ in 0..2,
          factorTwoSymmetricWeight (yoshidaEndpointA * t) *
            factorTwoCenteredCorrelationBilinear u' v' t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
    change factorTwoSymmetricWeight (yoshidaEndpointA * t) *
        factorTwoCenteredCorrelationBilinear u v t =
      factorTwoSymmetricWeight (yoshidaEndpointA * t) *
        factorTwoCenteredCorrelationBilinear u' v' t
    rw [factorTwoCenteredCorrelationBilinear_congr_Icc hu hv ht.1 ht.2]
  have htau := factorTwoPrimeShift_div_endpointA_mem_one_two
  have htau0 : 0 ≤ factorTwoPrimeShift / yoshidaEndpointA :=
    le_trans (by norm_num) htau.1
  unfold factorTwoCenteredSymmetricPerturbationBilinear
  rw [hint,
    factorTwoCenteredCorrelationBilinear_congr_Icc hu hv
      (by norm_num) (by norm_num),
    factorTwoCenteredCorrelationBilinear_congr_Icc hu hv htau0 htau.2]

private theorem factorTwoCenteredSymmetricPerturbationBilinear_comm
    (u v : ℝ → ℝ) :
    factorTwoCenteredSymmetricPerturbationBilinear u v =
      factorTwoCenteredSymmetricPerturbationBilinear v u := by
  unfold factorTwoCenteredSymmetricPerturbationBilinear
  simp_rw [factorTwoCenteredCorrelationBilinear_comm u v]

private theorem factorTwoCenteredSymmetricPerturbationBilinear_add_right
    (u v w : ℝ → ℝ)
    (hu : Continuous u) (hv : Continuous v) (hw : Continuous w) :
    factorTwoCenteredSymmetricPerturbationBilinear u (v + w) =
      factorTwoCenteredSymmetricPerturbationBilinear u v +
        factorTwoCenteredSymmetricPerturbationBilinear u w := by
  rw [factorTwoCenteredSymmetricPerturbationBilinear_comm u (v + w),
    factorTwoCenteredSymmetricPerturbationBilinear_add_left v w u hv hw hu,
    factorTwoCenteredSymmetricPerturbationBilinear_comm v u,
    factorTwoCenteredSymmetricPerturbationBilinear_comm w u]

private theorem factorTwoCenteredSymmetricPerturbationBilinear_smul_right
    (c : ℝ) (u v : ℝ → ℝ) :
    factorTwoCenteredSymmetricPerturbationBilinear u (c • v) =
      c * factorTwoCenteredSymmetricPerturbationBilinear u v := by
  rw [factorTwoCenteredSymmetricPerturbationBilinear_comm u (c • v),
    factorTwoCenteredSymmetricPerturbationBilinear_smul_left,
    factorTwoCenteredSymmetricPerturbationBilinear_comm v u]

/-- Endpoint adaptation is a two-vector congruence update of the canonical
even perturbation block. -/
theorem factorTwoConcreteEvenPerturbationMatrix_eq_canonical_update
    (i j : YoshidaEvenIndex) :
    factorTwoConcreteEvenPerturbationMatrix i j =
      factorTwoCanonicalEvenPerturbationEntry
          (factorTwoCanonicalEvenLowIndex i)
          (factorTwoCanonicalEvenLowIndex j) -
        endpointEvenLowTraceRatio j *
          factorTwoCanonicalEvenPerturbationEntry
            (factorTwoCanonicalEvenLowIndex i)
            factorTwoCanonicalEvenTopIndex -
        endpointEvenLowTraceRatio i *
          factorTwoCanonicalEvenPerturbationEntry
            factorTwoCanonicalEvenTopIndex
            (factorTwoCanonicalEvenLowIndex j) +
        endpointEvenLowTraceRatio i * endpointEvenLowTraceRatio j *
          factorTwoCanonicalEvenPerturbationEntry
            factorTwoCanonicalEvenTopIndex
            factorTwoCanonicalEvenTopIndex := by
  let ci := factorTwoCenteredCanonicalEvenProfile
    (factorTwoCanonicalEvenLowIndex i)
  let cj := factorTwoCenteredCanonicalEvenProfile
    (factorTwoCanonicalEvenLowIndex j)
  let h := factorTwoCenteredCanonicalEvenProfile
    factorTwoCanonicalEvenTopIndex
  let ki := endpointEvenLowTraceRatio i
  let kj := endpointEvenLowTraceRatio j
  have hci : Continuous ci :=
    continuous_factorTwoCenteredCanonicalEvenProfile _
  have hcj : Continuous cj :=
    continuous_factorTwoCenteredCanonicalEvenProfile _
  have hh : Continuous h :=
    continuous_factorTwoCenteredCanonicalEvenProfile _
  have hui : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      factorTwoCenteredAdaptedEvenLowProfile i x =
        (ci + (-ki) • h) x := by
    intro x hx
    simpa only [ci, h, ki, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      neg_mul, sub_eq_add_neg] using
        factorTwoCenteredAdaptedEvenLowProfile_eq_canonical_sub i hx
  have huj : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      factorTwoCenteredAdaptedEvenLowProfile j x =
        (cj + (-kj) • h) x := by
    intro x hx
    simpa only [cj, h, kj, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      neg_mul, sub_eq_add_neg] using
        factorTwoCenteredAdaptedEvenLowProfile_eq_canonical_sub j hx
  change factorTwoCenteredSymmetricPerturbationBilinear
      (factorTwoCenteredAdaptedEvenLowProfile i)
      (factorTwoCenteredAdaptedEvenLowProfile j) = _
  rw [factorTwoCenteredSymmetricPerturbationBilinear_congr_Icc hui huj]
  rw [factorTwoCenteredSymmetricPerturbationBilinear_add_left
      ci ((-ki) • h) (cj + (-kj) • h)
      hci (hh.const_smul (-ki)) (hcj.add (hh.const_smul (-kj))),
    factorTwoCenteredSymmetricPerturbationBilinear_add_right
      ci cj ((-kj) • h) hci hcj (hh.const_smul (-kj)),
    factorTwoCenteredSymmetricPerturbationBilinear_add_right
      ((-ki) • h) cj ((-kj) • h)
      (hh.const_smul (-ki)) hcj (hh.const_smul (-kj)),
    factorTwoCenteredSymmetricPerturbationBilinear_smul_right,
    factorTwoCenteredSymmetricPerturbationBilinear_smul_left,
    factorTwoCenteredSymmetricPerturbationBilinear_smul_smul]
  dsimp only [factorTwoCanonicalEvenPerturbationEntry, ci, cj, h, ki, kj]
  ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteEvenPerturbationAdaptation
