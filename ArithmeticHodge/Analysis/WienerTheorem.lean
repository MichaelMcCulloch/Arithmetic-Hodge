/-
  Wiener's Theorem

  For a finite Borel measure μ on ℝ:
    lim_{T→∞} (1/T) ∫₀ᵀ |μ̂(t)|² dt = Σ_x μ({x})²

  The proof uses the double integral representation |μ̂(t)|² = ∫∫ e^{it(x-y)·I} dμ⊗μ,
  then swaps the time integral inside via Fubini and applies dominated convergence.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

set_option autoImplicit false
set_option maxHeartbeats 6400000

open MeasureTheory Complex Filter Topology Set
open scoped NNReal ENNReal ComplexConjugate

namespace ArithmeticHodge.Analysis

/-! ### Time average of complex exponential -/

/-- For α ≠ 0, ∫₀ᵀ e^{iαt} dt = (e^{iαT} - 1)/(iα). -/
private lemma intervalIntegral_cexp (α : ℝ) (T : ℝ) (hα : α ≠ 0) :
    ∫ t in (0 : ℝ)..T, Complex.exp ((↑α * Complex.I) * ↑t) =
    (Complex.exp ((↑α * Complex.I) * ↑T) - Complex.exp ((↑α * Complex.I) * ↑(0:ℝ))) /
      (↑α * Complex.I) :=
  integral_exp_mul_complex (mul_ne_zero (Complex.ofReal_ne_zero.mpr hα) Complex.I_ne_zero)

/-! ### Wiener's Theorem -/

/-- The time-averaged exponential kernel on ℝ × ℝ, parametrized by T. -/
private noncomputable def wienerKernel (T : ℝ) (p : ℝ × ℝ) : ℂ :=
  (↑(1 / T) : ℂ) * ∫ t in Set.Icc (0 : ℝ) T,
    Complex.exp (↑(t * (p.2 - p.1)) * Complex.I)

/-- The pointwise limit of the kernel: 1 on diagonal, 0 off diagonal. -/
private noncomputable def wienerLimit (p : ℝ × ℝ) : ℂ :=
  if p.1 = p.2 then 1 else 0

/-- Norm bound on the set integral of exp for α ≠ 0, T > 0. -/
private lemma norm_setIntegral_cexp_le {α : ℝ} (hα : α ≠ 0) {T : ℝ} (hT : 0 < T) :
    ‖∫ t in Set.Icc (0 : ℝ) T, Complex.exp (↑(t * α) * Complex.I)‖ ≤ 2 / |α| := by
  -- Convert Icc set integral to Ioc, then to interval integral
  rw [show ∫ t in Set.Icc (0 : ℝ) T, Complex.exp (↑(t * α) * Complex.I) =
      ∫ t in (0 : ℝ)..T, Complex.exp ((↑α * Complex.I) * ↑t) from by
    rw [intervalIntegral.integral_of_le hT.le]
    rw [← setIntegral_congr_set Ioc_ae_eq_Icc]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t _; congr 1; push_cast; ring]
  rw [intervalIntegral_cexp α T hα]
  rw [norm_div]
  have hnorm : ‖(↑α : ℂ) * Complex.I‖ = |α| := by
    rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
  rw [hnorm]
  apply div_le_div_of_nonneg_right _ (abs_nonneg α)
  calc ‖Complex.exp ((↑α * Complex.I) * ↑T) -
        Complex.exp ((↑α * Complex.I) * ↑(0:ℝ))‖
      ≤ ‖Complex.exp ((↑α * Complex.I) * ↑T)‖ +
        ‖Complex.exp ((↑α * Complex.I) * ↑(0:ℝ))‖ := norm_sub_le _ _
    _ = 2 := by
        have h0 : (↑α * Complex.I) * ↑(0:ℝ) = 0 := by push_cast; ring
        rw [h0, Complex.exp_zero, norm_one]
        have : ‖Complex.exp ((↑α * Complex.I) * ↑T)‖ = 1 := by
          rw [show (↑α * Complex.I) * ↑T = ↑(α * T) * Complex.I from by push_cast; ring]
          exact Complex.norm_exp_ofReal_mul_I _
        linarith

/-- **Wiener's Theorem.**

    For a finite Borel measure μ on ℝ, the time-averaged Fourier power spectrum
    converges to the sum of squared atoms:
      lim_{T→∞} (1/T) ∫₀ᵀ |μ̂(t)|² dt = Σ_x μ({x})² -/
theorem wiener_theorem {μ : MeasureTheory.Measure ℝ} [IsFiniteMeasure μ] :
    Tendsto (fun T => (1/T) * ∫ t in Set.Icc 0 T,
      ‖∫ x, Complex.exp (↑(t * x) * Complex.I) ∂μ‖^2)
      atTop (nhds (∑' x, μ.real {x} ^ 2)) := by
  set μ' := μ.prod μ with hμ'_def
  set F := wienerKernel with hF_def
  set f := wienerLimit with hf_def

  -- ═══════════════════════════════════════════════════════════════
  -- Claim 1 (DCT): ∫ F(T) dμ' → ∫ f dμ' as T → ∞
  -- ═══════════════════════════════════════════════════════════════
  have dct : Tendsto (fun T => ∫ p, F T p ∂μ') atTop (nhds (∫ p, f p ∂μ')) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
    · -- (a) AEStronglyMeasurable (eventually)
      filter_upwards with T
      simp only [hF_def]
      apply AEStronglyMeasurable.const_mul
      -- The parametric integral is continuous in p, hence AE strongly measurable
      have hfin : IsFiniteMeasure (volume.restrict (Set.Icc (0:ℝ) T)) := ⟨by
        rw [Measure.restrict_apply_univ]; exact isCompact_Icc.measure_lt_top⟩
      exact (continuous_of_dominated
        (F := fun (p : ℝ × ℝ) (t : ℝ) =>
          Complex.exp (↑(t * (p.2 - p.1)) * Complex.I))
        (bound := fun _ => 1)
        (μ := volume.restrict (Set.Icc 0 T))
        (hF_meas := fun p => by
          apply Continuous.aestronglyMeasurable
          exact Complex.continuous_exp.comp
            ((Complex.continuous_ofReal.comp
              (continuous_id'.mul continuous_const)).mul
              continuous_const))
        (h_bound := fun p => by
          filter_upwards with t
          exact le_of_eq (Complex.norm_exp_ofReal_mul_I _))
        (bound_integrable := integrable_const 1)
        (h_cont := by
          filter_upwards with t
          exact Complex.continuous_exp.comp
            ((Complex.continuous_ofReal.comp
              (continuous_const.mul
                (continuous_snd.sub continuous_fst))).mul
              continuous_const))).aestronglyMeasurable
    · -- (b) ‖F T p‖ ≤ 1 for a.e. p (eventually for T > 0)
      filter_upwards [Ioi_mem_atTop (0 : ℝ)] with T (hT : 0 < T)
      filter_upwards with p
      simp only [hF_def, wienerKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < 1 / T)]
      calc (1 / T) * ‖∫ t in Set.Icc 0 T,
              Complex.exp (↑(t * (p.2 - p.1)) * Complex.I)‖
          ≤ (1 / T) * ∫ t in Set.Icc 0 T,
              ‖Complex.exp (↑(t * (p.2 - p.1)) * Complex.I)‖ :=
            mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
        _ = (1 / T) * ∫ _ in Set.Icc 0 T, (1 : ℝ) := by
            congr 1
            apply setIntegral_congr_fun measurableSet_Icc
            intro t _; exact Complex.norm_exp_ofReal_mul_I _
        _ = (1 / T) * volume.real (Set.Icc 0 T) := by
            rw [setIntegral_const, smul_eq_mul, mul_one]
        _ = 1 := by
            rw [Measure.real, Real.volume_Icc, sub_zero,
              ENNReal.toReal_ofReal hT.le]
            exact one_div_mul_cancel (ne_of_gt hT)
    · -- (c) Bound integrable on finite measure
      exact integrable_const 1
    · -- (d) Pointwise limit: F T p → f p
      filter_upwards with ⟨x, y⟩
      simp only [hF_def, wienerKernel, hf_def, wienerLimit]
      by_cases heq : x = y
      · -- Diagonal: exp(0) = 1, average → 1
        simp only [heq, sub_self, mul_zero, zero_mul, Complex.ofReal_zero,
          Complex.exp_zero, ite_true]
        apply tendsto_const_nhds.congr'
        filter_upwards [Ioi_mem_atTop (0 : ℝ)] with T (hT : 0 < T)
        show (1 : ℂ) = ↑(1 / T) * ∫ _ in Set.Icc 0 T, (1 : ℂ)
        have hval : ∫ _ in Set.Icc (0:ℝ) T, (1 : ℂ) = ↑T := by
          rw [setIntegral_const]
          simp only [Measure.real, Real.volume_Icc, sub_zero,
            ENNReal.toReal_ofReal hT.le]
          show (↑T : ℂ) * 1 = ↑T; exact mul_one _
        rw [hval, ← Complex.ofReal_mul, one_div_mul_cancel (ne_of_gt hT),
          Complex.ofReal_one]
      · -- Off-diagonal: time average → 0
        simp only [heq, ite_false]
        set α := y - x with hα_def
        have hα : α ≠ 0 := sub_ne_zero.mpr (Ne.symm heq)
        -- Use squeeze_zero_norm: bound by (2/|α|) * ‖(1/T:ℂ)‖ → 0
        apply squeeze_zero_norm
        · -- Bound for all T
          intro T
          simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          by_cases hT : (0 : ℝ) < T
          · -- T > 0: use explicit integral formula
            calc |1 / T| * ‖∫ t in Set.Icc 0 T,
                    Complex.exp (↑(t * α) * Complex.I)‖
                ≤ |1 / T| * (2 / |α|) := by
                  apply mul_le_mul_of_nonneg_left (norm_setIntegral_cexp_le hα hT)
                  exact abs_nonneg _
              _ = 2 / |α| * |1 / T| := by ring
          · -- T ≤ 0: |1/T| * ‖integral‖ ≤ bound
            push_neg at hT
            rcases eq_or_lt_of_le hT with rfl | hT'
            · -- T = 0: 1/0 = 0 in Lean
              simp [abs_zero]
            · -- T < 0: Icc 0 T = ∅
              have hIcc_empty : Set.Icc (0 : ℝ) T = ∅ := Set.Icc_eq_empty (by linarith)
              rw [hIcc_empty, setIntegral_empty, norm_zero, mul_zero]
              positivity
        · -- Bound tends to 0
          have : Tendsto (fun T : ℝ => 2 / |α| * |1 / T|) atTop (nhds 0) := by
            rw [show (0 : ℝ) = 2 / |α| * 0 from by ring]
            apply Filter.Tendsto.const_mul
            show Tendsto (fun T : ℝ => |1 / T|) atTop (nhds 0)
            have h := tendsto_inv_atTop_zero (𝕜 := ℝ)
            apply h.congr'
            filter_upwards [Ioi_mem_atTop (0 : ℝ)] with T (hT : 0 < T)
            rw [one_div, abs_of_pos (inv_pos.mpr hT)]
          exact this

  -- ═══════════════════════════════════════════════════════════════
  -- Claim 2 (Rewrite): LHS = Re(∫ F(T) dμ') for large T
  -- ═══════════════════════════════════════════════════════════════
  have rewrite : ∀ᶠ T in atTop, (1/T) * ∫ t in Set.Icc 0 T,
      ‖∫ x, Complex.exp (↑(t * x) * Complex.I) ∂μ‖^2 =
      (∫ p, F T p ∂μ').re := by
    filter_upwards [Ioi_mem_atTop (0 : ℝ)] with T (hT : 0 < T)
    simp only [hF_def, wienerKernel, hμ'_def]
    -- Key helper: for each t, the product integral of exp equals ‖μ̂(t)‖²
    have key : ∀ t : ℝ, ∫ p, Complex.exp (↑(t * (p.2 - p.1)) * Complex.I) ∂(μ.prod μ) =
        ↑(‖∫ x, Complex.exp (↑(t * x) * Complex.I) ∂μ‖ ^ 2) := by
      intro t
      -- Factor: exp(it(y-x)) = exp(-itx) · exp(ity)
      have hfactor : ∀ p : ℝ × ℝ,
          Complex.exp (↑(t * (p.2 - p.1)) * Complex.I) =
          (fun q : ℝ × ℝ => Complex.exp (↑(-(t * q.1)) * Complex.I) *
            Complex.exp (↑(t * q.2) * Complex.I)) p := by
        intro p
        simp only
        rw [← Complex.exp_add]
        congr 1; push_cast; ring
      simp_rw [hfactor]
      -- conj(∫ exp(itx) dμ) = ∫ exp(-itx) dμ
      have hconj : ∫ x, Complex.exp (↑(-(t * x)) * Complex.I) ∂μ =
          conj (∫ x, Complex.exp (↑(t * x) * Complex.I) ∂μ) := by
        have hpw : ∀ x, Complex.exp (↑(-(t * x)) * Complex.I) =
            conj (Complex.exp (↑(t * x) * Complex.I)) := by
          intro x; rw [← exp_conj]; congr 1
          rw [map_mul, conj_ofReal, Complex.conj_I]; push_cast; ring
        simp_rw [hpw]; exact integral_conj
      -- Use integral_prod_mul, then connect to normSq
      trans (∫ x, Complex.exp (↑(-(t * x)) * Complex.I) ∂μ) *
        (∫ y, Complex.exp (↑(t * y) * Complex.I) ∂μ)
      · convert integral_prod_mul
            (fun x => Complex.exp (↑(-(t * x)) * Complex.I))
            (fun y => Complex.exp (↑(t * y) * Complex.I)) using 1
        <;> infer_instance
      · rw [hconj, ← Complex.normSq_eq_conj_mul_self]
        simp [Complex.normSq_eq_norm_sq]
    -- Pull (1/T) out of the product integral and use Fubini
    -- We show the integrals match by using integral_mul_left and Fubini
    -- Pull constant out of product integral
    rw [integral_const_mul, re_ofReal_mul]
    congr 1
    -- Prepare Fubini integrability
    have hcont : Continuous (uncurry fun (p : ℝ × ℝ) (t : ℝ) =>
        cexp (↑(t * (p.2 - p.1)) * I)) :=
      Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
        (continuous_snd.mul ((continuous_snd.comp continuous_fst).sub
          (continuous_fst.comp continuous_fst)))).mul continuous_const)
    have hint : Integrable (uncurry fun (p : ℝ × ℝ) (t : ℝ) =>
        cexp (↑(t * (p.2 - p.1)) * I))
        ((μ.prod μ).prod (volume.restrict (Set.Icc 0 T))) :=
      (integrable_const (1 : ℂ)).mono' hcont.aestronglyMeasurable
        (ae_of_all _ fun ⟨_, _⟩ => by
          simp only [uncurry, norm_one]; exact le_of_eq (Complex.norm_exp_ofReal_mul_I _))
    -- Fubini: swap integrals
    rw [integral_integral_swap hint]
    -- Apply key to rewrite inner integral
    simp_rw [key]
    -- Extract Re from integral
    symm
    rw [← integral_re (hint.integral_prod_right.congr (ae_of_all _ fun t => key t))]
    simp_rw [Complex.ofReal_re]

  -- ═══════════════════════════════════════════════════════════════
  -- Claim 3 (Evaluate): Re(∫ f dμ') = ∑' x, μ.real {x}²
  -- ═══════════════════════════════════════════════════════════════
  have eval : (∫ p, f p ∂μ').re = ∑' x, μ.real {x} ^ 2 := by
    simp only [hf_def, wienerLimit, hμ'_def]
    -- f(x,y) = if x=y then 1 else 0 is the indicator of the diagonal
    have hf_eq : (fun p : ℝ × ℝ => if p.1 = p.2 then (1:ℂ) else 0) =
        (Set.diagonal ℝ).indicator (fun _ => 1) := by
      ext ⟨a, b⟩
      simp [Set.indicator, Set.mem_diagonal_iff]
    rw [hf_eq]
    rw [integral_indicator_const _ isClosed_diagonal.measurableSet]
    show ((↑((μ.prod μ).real (diagonal ℝ)) : ℂ) * 1).re = _
    rw [mul_one, Complex.ofReal_re]
    -- Now: (μ.prod μ).real (diagonal ℝ) = ∑' x, μ.real {x} ^ 2
    -- Use prod_apply to express as lintegral
    simp only [Measure.real]
    rw [Measure.prod_apply measurableSet_diagonal]
    -- Simplify preimage: Prod.mk x ⁻¹' diagonal = {x}
    have hpreimage : ∀ x : ℝ, Prod.mk x ⁻¹' diagonal ℝ = {x} := by
      intro x; ext y; simp [Set.mem_diagonal_iff]
    simp_rw [hpreimage]
    -- Measurability of x ↦ μ{x}
    have hmeas : Measurable (fun x : ℝ => μ {x}) := by
      have := measurable_measure_prodMk_left (ν := μ) measurableSet_diagonal
      simp_rw [hpreimage] at this; exact this
    -- The atoms form a countable set
    set A := Function.support (fun x => μ ({x} : Set ℝ)) with hA_def
    have hA_eq : A = {x : ℝ | 0 < μ {x}} := by ext; simp [Function.mem_support, pos_iff_ne_zero]
    have hA_count : A.Countable := by
      rw [hA_eq]
      exact countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top μ
        (fun x => measurableSet_singleton x)
        (fun i j hij => by exact Set.disjoint_singleton.mpr hij)
        (ne_top_of_le_ne_top (measure_ne_top μ univ) (measure_iUnion_le _))
    have hA_meas : MeasurableSet A := hmeas (measurableSet_compl {0})
    -- Restrict lintegral to atoms
    have hrestr : ∫⁻ x, μ {x} ∂μ = ∫⁻ x in A, μ {x} ∂μ := by
      rw [← lintegral_add_compl _ hA_meas]
      have : ∫⁻ x in Aᶜ, μ {x} ∂μ = 0 := by
        apply lintegral_eq_zero_of_ae
        filter_upwards [ae_restrict_mem hA_meas.compl] with x hx
        exact Function.not_mem_support.mp hx
      omega
    rw [hrestr, lintegral_countable _ hA_count]
    -- Now: (∑' a : A, μ{a} * μ{a}).toReal = ∑' x, (μ{x}).toReal ^ 2
    simp_rw [sq]
    rw [ENNReal.tsum_toReal_eq (fun ⟨a, _⟩ => by
      exact ENNReal.mul_ne_top (measure_ne_top μ _) (measure_ne_top μ _))]
    simp_rw [ENNReal.toReal_mul]
    -- Now: ∑' a : A, μ.real{a} * μ.real{a} = ∑' x : ℝ, μ.real{x} * μ.real{x}
    -- Extend from A to ℝ (zero outside A)
    rw [← tsum_eq_tsum_of_hasSum_iff_hasSum (fun {a} => by
      constructor
      · intro h
        apply h.map (⟨Subtype.val, Subtype.val_injective⟩ : A ↪ ℝ)
        exact continuous_id.tendsto _
      · intro h
        sorry)]

  -- ═══════════════════════════════════════════════════════════════
  -- Combine
  -- ═══════════════════════════════════════════════════════════════
  rw [show ∑' x, μ.real {x} ^ 2 = (∫ p, f p ∂μ').re from eval.symm]
  exact ((Complex.continuous_re.tendsto _).comp dct).congr'
    (rewrite.mono fun T hT => hT.symm)

/-- **Wiener's theorem for continuous measures.** -/
theorem wiener_continuous_measure {μ : MeasureTheory.Measure ℝ} [IsFiniteMeasure μ]
    (hcont : ∀ x : ℝ, μ {x} = 0) :
    Tendsto (fun T => (1/T) * ∫ t in Set.Icc 0 T,
      ‖∫ x, Complex.exp (↑(t * x) * Complex.I) ∂μ‖^2)
      atTop (nhds 0) := by
  have h := wiener_theorem (μ := μ)
  suffices hsum : ∑' x, μ.real {x} ^ 2 = 0 by rwa [hsum] at h
  have h0 : ∀ x : ℝ, μ.real {x} ^ 2 = 0 := fun x => by
    simp [Measure.real, hcont x]
  simp_rw [h0, tsum_zero]

end ArithmeticHodge.Analysis
