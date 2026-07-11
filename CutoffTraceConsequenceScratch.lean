import ArithmeticHodge.Spectral.CutoffHilbertSpace

open MeasureTheory
open RCLike
open scoped ENNReal InnerProductSpace

namespace ArithmeticHodge.Spectral.Cutoff

set_option autoImplicit false

-- Standard characterization of the current identity-cutoff model.

theorem vacuumWeights_tsum_eq_norm_sq_scratch
    (X : Type*) [inst : Adelic.AdeleClassSpaceData X] (Λ : ℝ) :
    ∑' i, vacuumWeightOf X Λ i = ‖vacuumVector X Λ‖ ^ 2 := by
  set b := cutoffEigenbasis X Λ
  set Ω := vacuumVector X Λ
  have hparseval_hasSum := b.hasSum_inner_mul_inner Ω Ω
  have hinner_self : @inner ℂ _ _ Ω Ω = ((‖Ω‖ : ℝ) ^ 2 : ℂ) :=
    inner_self_eq_norm_sq_to_K Ω
  have hterm : ∀ i, @inner ℂ _ _ Ω (b i) * @inner ℂ _ _ (b i) Ω =
      ((vacuumWeightOf X Λ i : ℝ) : ℂ) := by
    intro i
    simp only [vacuumWeightOf, vacuumAmplitudeOf]
    conv_lhs => rw [show @inner ℂ _ _ (b i) Ω =
      starRingEnd ℂ (@inner ℂ _ _ Ω (b i)) from
      (inner_conj_symm (𝕜 := ℂ) (b i) Ω).symm]
    rw [RCLike.mul_conj]
    simp only [← Complex.sq_norm, Complex.ofReal_pow, b, Ω]
    rfl
  simp_rw [hterm] at hparseval_hasSum
  rw [hinner_self, ← Complex.ofReal_pow] at hparseval_hasSum
  have hreal_hasSum : HasSum (fun i => vacuumWeightOf X Λ i) (‖Ω‖ ^ 2) :=
    Complex.hasSum_ofReal.mp hparseval_hasSum
  simpa [Ω] using hreal_hasSum.tsum_eq

theorem norm_rawVacuumVector_eq_measure_rpow_scratch
    (X : Type*) [inst : Adelic.AdeleClassSpaceData X] (Λ : ℝ) :
    ‖rawVacuumVector X Λ‖ =
      (cutoffMeasure X Λ).real (cutoffSet X Λ) ^ ((1 : ℝ) / 2) := by
  rw [rawVacuumVector,
    norm_indicatorConstLp (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  norm_num

theorem eventually_norm_vacuumVector_eq_one_scratch
    (X : Type*) [inst : Adelic.AdeleClassSpaceData X] :
    ∀ᶠ Λ : ℝ in Filter.atTop, ‖vacuumVector X Λ‖ = 1 := by
  obtain ⟨c, hc, hgrowth⟩ := inst.heightFn_volume_growth
  refine Filter.eventually_atTop.2
    ⟨max 1 (1 / c), fun Λ hΛ => ?_⟩
  have hΛ_one : 1 ≤ Λ := (le_max_left 1 (1 / c)).trans hΛ
  have hΛ_c : 1 / c ≤ Λ := (le_max_right 1 (1 / c)).trans hΛ
  have hc_ne : c ≠ 0 := hc.ne'
  have hcΛ : 1 ≤ c * Λ := by
    calc
      1 = c * (1 / c) := by field_simp
      _ ≤ c * Λ := mul_le_mul_of_nonneg_left hΛ_c hc.le
  have hgrowth_cutoff : ENNReal.ofReal (c * Λ) ≤
      inst.haarMeasure (cutoffSet X Λ) := by
    simpa [cutoffSet, max_eq_right hΛ_one] using hgrowth Λ hΛ_one
  have hcutoff_measure : (cutoffMeasure X Λ) (cutoffSet X Λ) =
      inst.haarMeasure (cutoffSet X Λ) := by
    rw [cutoffMeasure, Measure.restrict_apply (cutoffSet_measurable X Λ),
      Set.inter_self]
  have hmeasure_one : (1 : ENNReal) ≤
      (cutoffMeasure X Λ) (cutoffSet X Λ) := by
    rw [hcutoff_measure]
    exact (ENNReal.one_le_ofReal.mpr hcΛ).trans hgrowth_cutoff
  have hmeasure_finite :
      (cutoffMeasure X Λ) (cutoffSet X Λ) ≠ ⊤ := by
    rw [hcutoff_measure]
    exact (cutoffSet_measure_lt_top X Λ).ne
  have hmeasure_real : 1 ≤
      (cutoffMeasure X Λ).real (cutoffSet X Λ) := by
    change (1 : ENNReal).toReal ≤
      ((cutoffMeasure X Λ) (cutoffSet X Λ)).toReal
    exact ENNReal.toReal_mono hmeasure_finite hmeasure_one
  have hraw : 1 ≤ ‖rawVacuumVector X Λ‖ := by
    rw [norm_rawVacuumVector_eq_measure_rpow_scratch]
    exact Real.one_le_rpow hmeasure_real (by norm_num)
  have hraw_pos : 0 < ‖rawVacuumVector X Λ‖ := zero_lt_one.trans_le hraw
  rw [vacuumVector, norm_smul, Real.norm_eq_abs,
    max_eq_right hraw, abs_of_pos (inv_pos.mpr hraw_pos)]
  exact inv_mul_cancel₀ hraw_pos.ne'

theorem eventually_spectralPairingOf_eq_fourierCos_zero_scratch
    (X : Type*) [inst : Adelic.AdeleClassSpaceData X] (h : ℝ → ℝ) :
    ∀ᶠ Λ : ℝ in Filter.atTop,
      spectralPairingOf X Λ h = Analysis.fourierCos h 0 := by
  filter_upwards [eventually_norm_vacuumVector_eq_one_scratch X] with Λ hnorm
  rw [spectralPairingOf_eq_zero_frequency,
    vacuumWeights_tsum_eq_norm_sq_scratch, hnorm, one_pow, mul_one]

theorem spectralPairingOf_tendsto_fourierCos_zero_scratch
    (X : Type*) [inst : Adelic.AdeleClassSpaceData X] (h : ℝ → ℝ) :
    Filter.Tendsto (fun Λ : ℝ => spectralPairingOf X Λ h)
      Filter.atTop (nhds (Analysis.fourierCos h 0)) := by
  have heq : (fun _ : ℝ => Analysis.fourierCos h 0) =ᶠ[Filter.atTop]
      (fun Λ : ℝ => spectralPairingOf X Λ h) := by
    filter_upwards [eventually_spectralPairingOf_eq_fourierCos_zero_scratch X h]
      with Λ hΛ
    exact hΛ.symm
  exact (tendsto_const_nhds : Filter.Tendsto
    (fun _ : ℝ => Analysis.fourierCos h 0) Filter.atTop
      (nhds (Analysis.fourierCos h 0))).congr' heq

theorem fourierCos_zero_eq_integral_scratch (h : ℝ → ℝ) :
    Analysis.fourierCos h 0 = ∫ x : ℝ, h x := by
  simp [Analysis.fourierCos]

-- Consequences of the custom global trace-formula axiom
-- `selberg_unfolding_bound`, reached through `spectralPairingOf_tendsto_weil`.

theorem selberg_tendsto_forces_weil_eq_fourierCos_zero_scratch
    (X : Type*) [inst : Adelic.AdeleClassSpaceData X]
    (h : ℝ → ℝ) (hcont : Continuous h)
    (hdecay : ∀ x, ‖h x‖ ≤ 1 / (1 + x ^ 2)) :
    Analysis.weilFunctionalFull h (Analysis.fourierCos h) =
      Analysis.fourierCos h 0 := by
  exact tendsto_nhds_unique
    (spectralPairingOf_tendsto_weil X h hcont hdecay)
    (spectralPairingOf_tendsto_fourierCos_zero_scratch X h)

theorem selberg_tendsto_forces_weil_eq_integral_scratch
    (X : Type*) [inst : Adelic.AdeleClassSpaceData X]
    (h : ℝ → ℝ) (hcont : Continuous h)
    (hdecay : ∀ x, ‖h x‖ ≤ 1 / (1 + x ^ 2)) :
    Analysis.weilFunctionalFull h (Analysis.fourierCos h) =
      ∫ x : ℝ, h x := by
  rw [selberg_tendsto_forces_weil_eq_fourierCos_zero_scratch X h hcont hdecay,
    fourierCos_zero_eq_integral_scratch]

#print axioms vacuumWeights_tsum_eq_norm_sq_scratch
#print axioms norm_rawVacuumVector_eq_measure_rpow_scratch
#print axioms eventually_norm_vacuumVector_eq_one_scratch
#print axioms eventually_spectralPairingOf_eq_fourierCos_zero_scratch
#print axioms spectralPairingOf_tendsto_fourierCos_zero_scratch
#print axioms selberg_tendsto_forces_weil_eq_fourierCos_zero_scratch
#print axioms fourierCos_zero_eq_integral_scratch
#print axioms selberg_tendsto_forces_weil_eq_integral_scratch

end ArithmeticHodge.Spectral.Cutoff
