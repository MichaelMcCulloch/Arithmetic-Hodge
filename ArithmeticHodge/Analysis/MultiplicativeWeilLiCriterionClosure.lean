import ArithmeticHodge.Analysis.MultiplicativeWeilCriterion
import ArithmeticHodge.Analysis.MultiplicativeWeilLiDominantSeries

/-!
# Closing the Bombieri converse from spectral Li approximation

The remaining analytic approximation is isolated in one sequence-level
property.  Full paired Li negativity then produces the concrete nonzero
Bombieri witness required by the criterion.
-/

set_option autoImplicit false

open Complex Filter Real Set Topology

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- Smooth Bombieri tests can approximate every fixed paired Li zero sum. -/
def BombieriLiSpectralApproximation
    (zeros : ZetaZeroEnumeration) : Prop :=
  ∀ n : ℕ, ∃ g : ℕ → BombieriTest,
    Tendsto
      (fun j ↦ ∑' k : ℕ,
        spectralTerm (g j : ℝ → ℂ) (zeros.zero k).val)
      atTop
      (𝓝 (∑' k : ℕ,
        (liFunction n (zeros.zero k).val +
          liFunction n (1 - (zeros.zero k).val))))

/-- The spectral approximation property plus the dominant-series theorem
discharges the entire off-critical witness obligation. -/
theorem bombieriOffCriticalSpectralNegativity_of_liApproximation
    (zeros : ZetaZeroEnumeration)
    (happrox : BombieriLiSpectralApproximation zeros) :
    BombieriOffCriticalSpectralNegativity zeros := by
  intro hnot
  obtain ⟨n, _hn, hnegative⟩ :=
    not_RH_exists_large_liFunction_paired_tsum_re_negative
      zeros hnot 0
  obtain ⟨g, hg⟩ := happrox n
  have hgre : Tendsto
      (fun j ↦ (∑' k : ℕ,
        spectralTerm (g j : ℝ → ℂ) (zeros.zero k).val).re)
      atTop
      (𝓝 ((∑' k : ℕ,
        (liFunction n (zeros.zero k).val +
          liFunction n (1 - (zeros.zero k).val))).re)) := by
    exact (Complex.reCLM.continuous.tendsto _).comp hg
  have hevent : ∀ᶠ j : ℕ in atTop,
      (∑' k : ℕ,
        spectralTerm (g j : ℝ → ℂ) (zeros.zero k).val).re < 0 :=
    hgre.eventually (Iio_mem_nhds hnegative)
  obtain ⟨j, hj⟩ := hevent.exists
  refine ⟨g j, ?_, hj⟩
  intro hzero
  have hcoe : (g j : ℝ → ℂ) = 0 := by
    rw [hzero]
    rfl
  simp [hcoe, spectralTerm, mellin, coefficientConjugate] at hj

end

end ArithmeticHodge.Analysis.MultiplicativeWeil

