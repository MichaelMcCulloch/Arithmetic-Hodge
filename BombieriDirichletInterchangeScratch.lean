import ArithmeticHodge.Analysis.MultiplicativeWeilMellinFourier
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

private lemma norm_LSeriesTerm_vertical_eq
    (a : ℕ → ℂ) (σ t : ℝ) (n : ℕ) :
    ‖LSeries.term a (σ + t * I) n‖ = ‖LSeries.term a σ n‖ := by
  simp only [LSeries.norm_term_eq, add_re, ofReal_re, mul_re, I_re,
    ofReal_im, I_im, mul_zero, zero_mul, sub_zero, add_zero]

private lemma continuous_LSeriesTerm_vertical
    (a : ℕ → ℂ) (σ : ℝ) (n : ℕ) :
    Continuous (fun t : ℝ ↦ LSeries.term a (σ + t * I) n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simpa using (continuous_const : Continuous (fun _ : ℝ ↦ (0 : ℂ)))
  · simp_rw [LSeries.term_of_ne_zero hn]
    letI : NeZero (n : ℂ) := ⟨Nat.cast_ne_zero.mpr hn⟩
    apply Continuous.div₀ continuous_const
    · exact (continuous_const_cpow (n : ℂ)).comp (by fun_prop)
    · intro t
      exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr hn))

/-- Absolute convergence on the real point gives continuity of the L-series
on the whole vertical line through that point. -/
lemma LSeries_vertical_continuous_scratch
    (a : ℕ → ℂ) (σ : ℝ) (ha : LSeriesSummable a σ) :
    Continuous (fun t : ℝ ↦ LSeries a (σ + t * I)) := by
  unfold LSeries
  apply continuous_tsum (continuous_LSeriesTerm_vertical a σ)
    (summable_norm_iff.mpr ha)
  intro n t
  exact (norm_LSeriesTerm_vertical_eq a σ t n).le

/-- The usual uniform vertical-line bound by the absolutely convergent
Dirichlet majorant. -/
lemma norm_LSeries_vertical_le_scratch
    (a : ℕ → ℂ) (σ t : ℝ) (ha : LSeriesSummable a σ) :
    ‖LSeries a (σ + t * I)‖ ≤ ∑' n : ℕ, ‖LSeries.term a σ n‖ := by
  unfold LSeries
  refine (norm_tsum_le_tsum_norm ?_).trans_eq ?_
  · exact summable_norm_iff.mpr <|
      (LSeriesSummable_iff_of_re_eq_re (by simp) :
        LSeriesSummable a σ ↔ LSeriesSummable a (σ + t * I)).mp ha
  · exact tsum_congr (norm_LSeriesTerm_vertical_eq a σ t)

/-- The Mellin transform of a Bombieri test times an absolutely convergent
L-series is integrable on the corresponding vertical line. -/
lemma bombieriMellin_mul_LSeries_integrable_scratch
    (f : BombieriTest) (a : ℕ → ℂ) (σ : ℝ)
    (ha : LSeriesSummable a σ) :
    Integrable (fun t : ℝ ↦
      mellin (f : ℝ → ℂ) (σ + t * I) * LSeries a (σ + t * I)) := by
  refine (f.mellin_verticalIntegrable σ).mul_bdd
    (c := ∑' n : ℕ, ‖LSeries.term a σ n‖)
    (LSeries_vertical_continuous_scratch a σ ha).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun t ↦
    norm_LSeries_vertical_le_scratch a σ t ha

/-- Sampling a compactly supported Bombieri test at the positive integers
has finite support, regardless of the coefficient sequence. -/
lemma bombieri_coeff_eval_summable_scratch
    (f : BombieriTest) (a : ℕ → ℂ) :
    Summable (fun n : ℕ ↦ a n * f n) := by
  apply summable_of_hasFiniteSupport
  obtain ⟨B, hB⟩ := f.hasCompactSupport.bddAbove
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt B
  refine (Set.finite_Iic N).subset ?_
  intro n hn
  have hfn : f (n : ℝ) ≠ 0 := by
    intro hzero
    exact hn (by simp [hzero])
  have htsupport : (n : ℝ) ∈ tsupport (f : ℝ → ℂ) :=
    subset_tsupport (f : ℝ → ℂ) (Function.mem_support.mpr hfn)
  exact_mod_cast (hB htsupport).trans hN.le

/-- The absolutely convergent Dirichlet series may be interchanged with the
vertical Mellin integral.  No strict half-plane margin is needed: absolute
convergence at the real point `σ` is exactly the uniform majorant on its
vertical line. -/
theorem bombieriMellin_integral_mul_LSeries_scratch
    (f : BombieriTest) (a : ℕ → ℂ) (σ : ℝ)
    (ha : LSeriesSummable a σ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, mellin (f : ℝ → ℂ) (σ + t * I) *
          LSeries a (σ + t * I) =
      ∑' n : ℕ, a n * f n := by
  let M : ℝ → ℂ := fun t ↦
    mellin (f : ℝ → ℂ) (σ + t * I)
  let F : ℕ → ℝ → ℂ := fun n t ↦
    M t * LSeries.term a (σ + t * I) n
  have hM : Integrable M := by
    simpa only [M] using f.mellin_verticalIntegrable σ
  have hFint (n : ℕ) : Integrable (F n) := by
    refine hM.mul_bdd (c := ‖LSeries.term a σ n‖)
      (continuous_LSeriesTerm_vertical a σ n).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun t ↦
      (norm_LSeriesTerm_vertical_eq a σ t n).le
  have hIntNorm (n : ℕ) :
      ∫ t : ℝ, ‖F n t‖ =
        ‖LSeries.term a σ n‖ * ∫ t : ℝ, ‖M t‖ := by
    calc
      ∫ t : ℝ, ‖F n t‖ =
          ∫ t : ℝ, ‖LSeries.term a σ n‖ * ‖M t‖ := by
        apply integral_congr_ae
        filter_upwards [] with t
        rw [show ‖F n t‖ = ‖M t‖ *
            ‖LSeries.term a (σ + t * I) n‖ by simp only [F, norm_mul],
          norm_LSeriesTerm_vertical_eq a σ t n, mul_comm]
      _ = ‖LSeries.term a σ n‖ * ∫ t : ℝ, ‖M t‖ :=
        MeasureTheory.integral_const_mul _ _
  have hFsum : Summable (fun n : ℕ ↦ ∫ t : ℝ, ‖F n t‖) := by
    rw [show (fun n : ℕ ↦ ∫ t : ℝ, ‖F n t‖) =
        fun n : ℕ ↦ ‖LSeries.term a σ n‖ * ∫ t : ℝ, ‖M t‖ by
      funext n
      exact hIntNorm n]
    exact (summable_norm_iff.mpr ha).mul_right _
  have hinterchange :
      (∑' n : ℕ, ∫ t : ℝ, F n t) =
        ∫ t : ℝ, ∑' n : ℕ, F n t :=
    MeasureTheory.integral_tsum_of_summable_integral_norm hFint hFsum
  have htsum (t : ℝ) :
      (∑' n : ℕ, F n t) = M t * LSeries a (σ + t * I) := by
    simp only [F, LSeries, tsum_mul_left]
  have hf0 : f (0 : ℝ) = 0 := by
    by_contra hf0
    have hsupport : (0 : ℝ) ∈ Function.support (f : ℝ → ℂ) := hf0
    have htsupport : (0 : ℝ) ∈ tsupport (f : ℝ → ℂ) :=
      subset_tsupport (f : ℝ → ℂ) hsupport
    exact (lt_irrefl (0 : ℝ)) (f.tsupport_subset htsupport)
  let c : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  change c * ∫ t : ℝ, M t * LSeries a (σ + t * I) = _
  calc
    c * ∫ t : ℝ, M t * LSeries a (σ + t * I) =
        c * ∫ t : ℝ, ∑' n : ℕ, F n t := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t ↦ (htsum t).symm
    _ = c * ∑' n : ℕ, ∫ t : ℝ, F n t := by
      rw [hinterchange]
    _ = ∑' n : ℕ, c * ∫ t : ℝ, F n t := by
      rw [tsum_mul_left]
    _ = ∑' n : ℕ, a n * f n := by
      apply tsum_congr
      intro n
      rcases eq_or_ne n 0 with rfl | hn
      · simp [F, M, hf0]
      · simpa only [c, F, M] using
          bombieriMellin_integral_mul_LSeriesTerm f a σ hn

/-- Has-sum form of the same identity, making the convergence of the sampled
coefficient series explicit rather than relying on totalized `tsum`. -/
theorem bombieri_coeff_eval_hasSum_verticalIntegral_scratch
    (f : BombieriTest) (a : ℕ → ℂ) (σ : ℝ)
    (ha : LSeriesSummable a σ) :
    HasSum (fun n : ℕ ↦ a n * f n)
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, mellin (f : ℝ → ℂ) (σ + t * I) *
          LSeries a (σ + t * I)) := by
  rw [bombieriMellin_integral_mul_LSeries_scratch f a σ ha]
  exact (bombieri_coeff_eval_summable_scratch f a).hasSum

/-- In particular, the von Mangoldt Dirichlet series may be integrated
termwise on every vertical line strictly to the right of `Re(s)=1`. -/
theorem bombieriMellin_integral_mul_vonMangoldt_LSeries_scratch
    (f : BombieriTest) (σ : ℝ) (hσ : 1 < σ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, mellin (f : ℝ → ℂ) (σ + t * I) *
          LSeries (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ))
            (σ + t * I) =
      ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * f n := by
  apply bombieriMellin_integral_mul_LSeries_scratch
  simpa using ArithmeticFunction.LSeriesSummable_vonMangoldt
    (show 1 < (σ : ℂ).re by simpa)

end

end ArithmeticHodge.Analysis.MultiplicativeWeil

#print axioms ArithmeticHodge.Analysis.MultiplicativeWeil.LSeries_vertical_continuous_scratch
#print axioms ArithmeticHodge.Analysis.MultiplicativeWeil.norm_LSeries_vertical_le_scratch
#print axioms ArithmeticHodge.Analysis.MultiplicativeWeil.bombieriMellin_mul_LSeries_integrable_scratch
#print axioms ArithmeticHodge.Analysis.MultiplicativeWeil.bombieri_coeff_eval_summable_scratch
#print axioms ArithmeticHodge.Analysis.MultiplicativeWeil.bombieriMellin_integral_mul_LSeries_scratch
#print axioms ArithmeticHodge.Analysis.MultiplicativeWeil.bombieri_coeff_eval_hasSum_verticalIntegral_scratch
#print axioms ArithmeticHodge.Analysis.MultiplicativeWeil.bombieriMellin_integral_mul_vonMangoldt_LSeries_scratch
