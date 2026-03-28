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
    -- Prepare Fubini integrability
    have hcont : Continuous (Function.uncurry fun (p : ℝ × ℝ) (t : ℝ) =>
        cexp (↑(t * (p.2 - p.1)) * I)) :=
      Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
        (continuous_snd.mul ((continuous_snd.comp continuous_fst).sub
          (continuous_fst.comp continuous_fst)))).mul continuous_const)
    haveI : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) T)) :=
      ⟨by simp [Real.volume_Icc, ENNReal.ofReal_lt_top]⟩
    have hint : Integrable (Function.uncurry fun (p : ℝ × ℝ) (t : ℝ) =>
        cexp (↑(t * (p.2 - p.1)) * I))
        ((μ.prod μ).prod (volume.restrict (Set.Icc 0 T))) :=
      by
        constructor
        · exact hcont.aestronglyMeasurable
        · show ∫⁻ x, ↑‖Function.uncurry (fun p t => cexp (↑(t * (p.2 - p.1)) * I)) x‖₊
              ∂(μ.prod μ).prod (volume.restrict (Set.Icc 0 T)) < ⊤
          calc ∫⁻ x, ↑‖Function.uncurry (fun p t => cexp (↑(t * (p.2 - p.1)) * I)) x‖₊
                ∂(μ.prod μ).prod (volume.restrict (Set.Icc 0 T))
              = ∫⁻ _, 1 ∂(μ.prod μ).prod (volume.restrict (Set.Icc 0 T)) := by
                congr 1; ext ⟨⟨a, b⟩, t⟩
                simp only [Function.uncurry, Complex.nnnorm_exp_ofReal_mul_I, ENNReal.coe_one]
            _ = ((μ.prod μ).prod (volume.restrict (Set.Icc 0 T))) Set.univ := by
                simp [lintegral_const]
            _ < ⊤ := measure_lt_top _ _
    -- Pull constant out and use Fubini
    have hpull := integral_const_mul (↑(1 / T) : ℂ)
      (fun p : ℝ × ℝ => ∫ t in Set.Icc 0 T, cexp (↑(t * (p.2 - p.1)) * I))
      (μ := μ.prod μ)
    rw [show (∫ (p : ℝ × ℝ), ↑(1 / T) *
        (∫ (t : ℝ) in Set.Icc 0 T, cexp (↑(t * (p.2 - p.1)) * I)) ∂μ.prod μ) =
        ↑(1 / T) * ∫ (p : ℝ × ℝ),
        (∫ (t : ℝ) in Set.Icc 0 T, cexp (↑(t * (p.2 - p.1)) * I)) ∂μ.prod μ from hpull,
      re_ofReal_mul]
    congr 1
    -- Fubini: swap integrals
    rw [integral_integral_swap hint]
    -- Apply key to rewrite inner integral
    simp_rw [key]
    -- Extract Re from integral: (∫ t, ↑(r t)).re = ∫ t, r t
    symm
    rw [integral_ofReal (𝕜 := ℂ), Complex.ofReal_re]

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
      intro x; ext y; simp [Set.mem_diagonal_iff, eq_comm]
    simp_rw [hpreimage]
    -- Measurability of x ↦ μ{x}
    have hmeas : Measurable (fun x : ℝ => μ {x}) := by
      have := measurable_measure_prodMk_left (ν := μ) measurableSet_diagonal
      simp_rw [hpreimage] at this; exact this
    -- Convert lintegral to Bochner integral via integral_toReal
    rw [← integral_toReal hmeas.aemeasurable
      (ae_of_all _ fun x => measure_lt_top μ _)]
    -- Now: ∫ x, (μ{x}).toReal ∂μ = ∑' x, (μ{x}).toReal ^ 2
    -- = ∫ x, μ.real{x} ∂μ = ∑' x, μ.real{x}²
    -- The atoms form a countable set
    have hA_count : {x : ℝ | 0 < μ {x}}.Countable :=
      Measure.countable_meas_pos_of_disjoint_iUnion
        (fun x => measurableSet_singleton x)
        (fun i j hij => Set.disjoint_singleton.mpr hij)
    -- The function x ↦ μ.real{x} vanishes outside atoms
    -- Use the Bochner integral computation for functions with countable support
    -- ∫ x, f(x) dμ = ∑ over atoms a: f(a) · μ.real{a}
    -- With f(x) = μ.real{x} = (μ{x}).toReal, this gives ∑' a, μ.real{a}²
    have hmeas_real : Measurable (fun x : ℝ => (μ {x}).toReal) :=
      ENNReal.measurable_toReal.comp hmeas
    have hA_meas : MeasurableSet {x : ℝ | (μ {x}).toReal ≠ 0} :=
      hmeas_real (measurableSet_singleton (0 : ℝ)).compl
    -- The support equals the atoms set
    have hsupp_eq : {x : ℝ | (μ {x}).toReal ≠ 0} = {x : ℝ | 0 < μ {x}} := by
      ext x
      simp only [Set.mem_setOf_eq, ne_eq, ENNReal.toReal_eq_zero_iff, not_or, pos_iff_ne_zero]
      exact ⟨fun h => h.1, fun h => ⟨h, (measure_ne_top μ _)⟩⟩
    -- Restrict to atoms: ∫ f dμ = ∫_A f dμ
    have hrestr : ∫ x, (μ {x}).toReal ∂μ = ∫ x in {x | 0 < μ {x}}, (μ {x}).toReal ∂μ := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      simp only [Set.mem_setOf_eq, not_lt] at hx
      have : μ {x} = 0 := le_antisymm hx (zero_le _)
      simp [this]
    rw [hrestr]
    -- Use integral over countable set = tsum
    have hintble : IntegrableOn (fun x => (μ {x}).toReal) {x | 0 < μ {x}} μ :=
      ⟨hmeas_real.aestronglyMeasurable.restrict,
       (hasFiniteIntegral_const (μ Set.univ).toReal).mono
         (ae_of_all _ fun x => by
           simp only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
           exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (Set.subset_univ _)))⟩
    rw [setIntegral_countable _ hA_count hintble]
    -- Now: ∑' x : {x | 0 < μ{x}}, μ.real{↑x} • (μ{↑x}).toReal = ∑' x, μ.real{x}²
    simp_rw [Measure.real, smul_eq_mul, sq]
    -- Extend from atoms to all of ℝ via tsum_subtype
    have := tsum_subtype {x : ℝ | 0 < μ {x}} (fun x => (μ {x}).toReal * (μ {x}).toReal)
    rw [this]; clear this
    congr 1; ext x
    by_cases hx : (0 : ℝ≥0∞) < μ {x}
    · simp [Set.indicator, hx]
    · push_neg at hx
      have hx0 : μ {x} = 0 := le_antisymm hx (zero_le _)
      simp [Set.indicator, hx0, show ¬(0 < μ {x}) from not_lt.mpr hx]

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
