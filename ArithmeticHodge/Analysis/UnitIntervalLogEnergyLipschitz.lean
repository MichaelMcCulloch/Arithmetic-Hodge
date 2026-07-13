import ArithmeticHodge.Analysis.UnitIntervalLogEnergyProjection

set_option autoImplicit false

open MeasureTheory Real
open scoped unitInterval

namespace ArithmeticHodge.Analysis.UnitIntervalLogEnergyLipschitz

open UnitIntervalLogEnergyProjection

noncomputable section

/-- A Lipschitz profile has finite raw logarithmic difference energy. -/
theorem integrable_unitIntervalRawLogEnergyIntegrand_of_lipschitzWith
    {C : NNReal} (f : unitInterval → ℝ) (hf : LipschitzWith C f) :
    Integrable (unitIntervalRawLogEnergyIntegrand f) := by
  let D : unitInterval × unitInterval → ℝ := fun z ↦
    (C : ℝ) ^ 2 * |(z.1 : ℝ) - (z.2 : ℝ)|
  have hDcont : Continuous D := by
    dsimp only [D]
    fun_prop
  have hDint : Integrable D :=
    hDcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace D)
  have henergyMeas : AEStronglyMeasurable
      (unitIntervalRawLogEnergyIntegrand f) := by
    apply Measurable.aestronglyMeasurable
    unfold unitIntervalRawLogEnergyIntegrand
    have hfst : Measurable (fun z : unitInterval × unitInterval ↦ f z.1) :=
      hf.continuous.measurable.comp measurable_fst
    have hsnd : Measurable (fun z : unitInterval × unitInterval ↦ f z.2) :=
      hf.continuous.measurable.comp measurable_snd
    have hden : Measurable (fun z : unitInterval × unitInterval ↦
        |(z.1 : ℝ) - (z.2 : ℝ)|) := by
      fun_prop
    exact ((hfst.sub hsnd).pow_const 2).div hden
  refine hDint.mono' henergyMeas ?_
  filter_upwards [] with z
  unfold unitIntervalRawLogEnergyIntegrand
  dsimp only [D]
  have hdist : |f z.1 - f z.2| ≤
      (C : ℝ) * |(z.1 : ℝ) - (z.2 : ℝ)| := by
    simpa only [Real.dist_eq, Subtype.dist_eq] using hf.dist_le_mul z.1 z.2
  rw [Real.norm_eq_abs, abs_of_nonneg
    (div_nonneg (sq_nonneg _) (abs_nonneg _))]
  by_cases hxy : |(z.1 : ℝ) - (z.2 : ℝ)| = 0
  · rw [hxy]
    simp only [div_zero, mul_zero, le_refl]
  · have hxyPos : 0 < |(z.1 : ℝ) - (z.2 : ℝ)| :=
      lt_of_le_of_ne (abs_nonneg _) (Ne.symm hxy)
    rw [div_le_iff₀ hxyPos]
    have hCnonneg : 0 ≤ (C : ℝ) := C.property
    have hsq := (sq_le_sq₀ (abs_nonneg (f z.1 - f z.2))
      (mul_nonneg hCnonneg (abs_nonneg _))).2 hdist
    rw [sq_abs, mul_pow] at hsq
    nlinarith

end

end ArithmeticHodge.Analysis.UnitIntervalLogEnergyLipschitz
