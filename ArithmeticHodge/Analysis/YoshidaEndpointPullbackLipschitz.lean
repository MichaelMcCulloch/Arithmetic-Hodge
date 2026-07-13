import ArithmeticHodge.Analysis.UnitIntervalLogEnergyAffine
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

set_option autoImplicit false

open Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointPullbackLipschitz

open UnitIntervalLogEnergyAffine

noncomputable section

/-- Local Lipschitz regularity on the centered compact interval supplies a
global Lipschitz constant for the unit-interval pullback. -/
theorem exists_lipschitzWith_centeredPullback
    (w : ℝ → ℝ) (hw : LocallyLipschitzOn (Icc (-1) 1) w) :
    ∃ C : NNReal, LipschitzWith C
      (fun t : unitInterval ↦ centeredPullback w (t : ℝ)) := by
  obtain ⟨K, hK⟩ := hw.exists_lipschitzOnWith_of_compact isCompact_Icc
  refine ⟨K * 2, LipschitzWith.of_dist_le_mul fun s t ↦ ?_⟩
  have hs : 2 * (s : ℝ) - 1 ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [s.property.1, s.property.2]
  have ht : 2 * (t : ℝ) - 1 ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [t.property.1, t.property.2]
  have h := hK.dist_le_mul (2 * (s : ℝ) - 1) hs
    (2 * (t : ℝ) - 1) ht
  unfold centeredPullback
  simp only [Real.dist_eq, Subtype.dist_eq, NNReal.coe_mul, NNReal.coe_ofNat]
  simp only [Real.dist_eq] at h
  rw [show (2 * (s : ℝ) - 1) - (2 * (t : ℝ) - 1) =
    2 * ((s : ℝ) - (t : ℝ)) by ring,
    abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h
  simpa only [mul_assoc] using h

end

end ArithmeticHodge.Analysis.YoshidaEndpointPullbackLipschitz
