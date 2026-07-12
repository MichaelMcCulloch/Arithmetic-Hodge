import ArithmeticHodge.Analysis.MultiplicativeWeilDigammaSummation

set_option autoImplicit false

open Complex MeasureTheory Real

namespace ArithmeticHodge.Analysis.YoshidaDigammaDistribution

noncomputable section

open MultiplicativeWeil

/-!
# Abstract digamma distribution against weighted spectral products

This module lifts Bombieri's harmonic-subtracted digamma interchange from a
specific smooth Mellin transform to an arbitrary integrable spectral product
`M`.  In addition to ordinary integrability, the weighted-decay hypothesis is
integrability of `(1 + v ^ 2) * ‖M v‖`; the resulting interface reduces the
local critical kernel to Cauchy-kernel values and the zero-frequency Fourier
integral.
-/

/-- The harmonic-subtracted digamma-series term against an abstract spectral
product. -/
def digammaSeriesTerm (M : ℝ → ℂ) (n : ℕ) (v : ℝ) : ℂ :=
  ((bombieriDigammaKernel (n + 1) v : ℂ) -
      (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ)) * M v

private theorem continuous_digammaSeriesCoefficient (n : ℕ) :
    Continuous (fun v : ℝ ↦
      ((bombieriDigammaKernel (n + 1) v : ℂ) -
        (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ))) := by
  have hden (v : ℝ) :
      (2 * (n + 1 : ℕ) + 1 / 2 : ℝ) ^ 2 + v ^ 2 ≠ 0 := by
    positivity
  have hreal : Continuous (fun v : ℝ ↦
      bombieriDigammaKernel (n + 1) v) := by
    unfold bombieriDigammaKernel
    exact continuous_const.div
      ((continuous_const.pow 2).add (continuous_id.pow 2)) hden
  exact (Complex.continuous_ofReal.comp hreal).sub continuous_const

private theorem digammaSeriesTerm_integrable
    (M : ℝ → ℂ) (hM : Integrable M)
    (hW : Integrable (fun v : ℝ ↦ (1 + v ^ 2) * ‖M v‖))
    (n : ℕ) :
    Integrable (digammaSeriesTerm M n) := by
  let p : ℝ := (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹
  have hmajor : Integrable (fun v : ℝ ↦
      p * ((1 + v ^ 2) * ‖M v‖)) := hW.const_mul p
  apply hmajor.mono'
  · exact (continuous_digammaSeriesCoefficient n).aestronglyMeasurable.mul hM.1
  · filter_upwards [] with v
    simp only [digammaSeriesTerm, norm_mul]
    rw [← Complex.ofReal_inv, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    calc
      |bombieriDigammaKernel (n + 1) v -
            ((n + 1 : ℕ) : ℝ)⁻¹| * ‖M v‖ ≤
          ((1 + v ^ 2) / (((n + 1 : ℕ) : ℝ) ^ 2)) * ‖M v‖ :=
        mul_le_mul_of_nonneg_right
          (abs_bombieriDigammaKernel_sub_inv_le n v) (norm_nonneg _)
      _ = p * ((1 + v ^ 2) * ‖M v‖) := by
        simp only [p, div_eq_mul_inv]
        ring

private theorem summable_integral_norm_digammaSeriesTerm
    (M : ℝ → ℂ) (hM : Integrable M)
    (hW : Integrable (fun v : ℝ ↦ (1 + v ^ 2) * ‖M v‖)) :
    Summable (fun n : ℕ ↦ ∫ v : ℝ, ‖digammaSeriesTerm M n v‖) := by
  let W : ℝ → ℝ := fun v ↦ (1 + v ^ 2) * ‖M v‖
  let C : ℝ := ∫ v : ℝ, W v
  have hW' : Integrable W := by simpa only [W] using hW
  have hC : 0 ≤ C := integral_nonneg fun v ↦ by
    exact mul_nonneg (by positivity) (norm_nonneg _)
  have hp : Summable (fun n : ℕ ↦
      (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
    exact (summable_nat_add_iff 1).2
      (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2))
  have hmajor : Summable (fun n : ℕ ↦
      (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ * C) := hp.mul_right C
  apply hmajor.of_nonneg_of_le
  · intro n
    exact integral_nonneg fun v ↦ norm_nonneg _
  · intro n
    have hterm := digammaSeriesTerm_integrable M hM hW n
    have hmajorInt : Integrable (fun v : ℝ ↦
        (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ * W v) := hW'.const_mul _
    calc
      (∫ v : ℝ, ‖digammaSeriesTerm M n v‖) ≤
          ∫ v : ℝ, (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ * W v := by
        apply integral_mono hterm.norm hmajorInt
        intro v
        simp only [digammaSeriesTerm, norm_mul]
        rw [← Complex.ofReal_inv, ← Complex.ofReal_sub,
          Complex.norm_real, Real.norm_eq_abs]
        calc
          |bombieriDigammaKernel (n + 1) v -
                ((n + 1 : ℕ) : ℝ)⁻¹| * ‖M v‖ ≤
              ((1 + v ^ 2) / (((n + 1 : ℕ) : ℝ) ^ 2)) * ‖M v‖ :=
            mul_le_mul_of_nonneg_right
              (abs_bombieriDigammaKernel_sub_inv_le n v) (norm_nonneg _)
          _ = (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ * W v := by
            simp only [W, div_eq_mul_inv]
            ring
      _ = (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ * C := by
        rw [MeasureTheory.integral_const_mul]

/-- Absolute convergence justifies interchanging the abstract spectral
product's harmonic-subtracted digamma series with its whole-line integral. -/
theorem integral_tsum_digammaSeriesTerm
    (M : ℝ → ℂ) (hM : Integrable M)
    (hW : Integrable (fun v : ℝ ↦ (1 + v ^ 2) * ‖M v‖)) :
    ∫ v : ℝ, ∑' n : ℕ, digammaSeriesTerm M n v =
      ∑' n : ℕ, ∫ v : ℝ, digammaSeriesTerm M n v := by
  exact (MeasureTheory.integral_tsum_of_summable_integral_norm
    (digammaSeriesTerm_integrable M hM hW)
    (summable_integral_norm_digammaSeriesTerm M hM hW)).symm

/-- The pointwise harmonic-subtracted digamma series against `M` is itself
Bochner integrable. -/
theorem digammaSeries_integrable
    (M : ℝ → ℂ) (hM : Integrable M)
    (hW : Integrable (fun v : ℝ ↦ (1 + v ^ 2) * ‖M v‖)) :
    Integrable (fun v : ℝ ↦
      (∑' n : ℕ,
          ((bombieriDigammaKernel (n + 1) v : ℂ) -
            (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ))) * M v) := by
  have hinternal : Integrable (fun v : ℝ ↦
      ∑' n : ℕ, digammaSeriesTerm M n v) := by
    let W : ℝ → ℝ := fun v ↦ (1 + v ^ 2) * ‖M v‖
    let p : ℕ → ℝ := fun n ↦ (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹
    let S : ℝ := ∑' n : ℕ, p n
    have hW' : Integrable W := by simpa only [W] using hW
    have hp : Summable p := by
      exact (summable_nat_add_iff 1).2
        (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2))
    have hsF (v : ℝ) : Summable (fun n : ℕ ↦ digammaSeriesTerm M n v) := by
      simpa only [digammaSeriesTerm] using
        (summable_bombieriDigammaKernel_sub_inv v).mul_right (M v)
    have hmeas : AEStronglyMeasurable (fun v : ℝ ↦
        ∑' n : ℕ, digammaSeriesTerm M n v) := by
      apply aestronglyMeasurable_of_tendsto_ae Filter.atTop
        (fun N : ℕ ↦ (Finset.range N).aestronglyMeasurable_fun_sum fun n _ ↦
          (digammaSeriesTerm_integrable M hM hW n).1)
      filter_upwards [] with v
      exact (hsF v).hasSum.tendsto_sum_nat
    refine (hW'.const_mul S).mono' hmeas ?_
    filter_upwards [] with v
    have hterm (n : ℕ) :
        ‖digammaSeriesTerm M n v‖ ≤ p n * W v := by
      simp only [digammaSeriesTerm, norm_mul]
      rw [← Complex.ofReal_inv, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs]
      calc
        |bombieriDigammaKernel (n + 1) v -
              ((n + 1 : ℕ) : ℝ)⁻¹| * ‖M v‖ ≤
            ((1 + v ^ 2) / (((n + 1 : ℕ) : ℝ) ^ 2)) * ‖M v‖ :=
          mul_le_mul_of_nonneg_right
            (abs_bombieriDigammaKernel_sub_inv_le n v) (norm_nonneg _)
        _ = p n * W v := by
          simp only [p, W, div_eq_mul_inv]
          ring
    calc
      ‖∑' n : ℕ, digammaSeriesTerm M n v‖ ≤
          ∑' n : ℕ, ‖digammaSeriesTerm M n v‖ :=
        norm_tsum_le_tsum_norm (hsF v).norm
      _ ≤ ∑' n : ℕ, p n * W v :=
        (hsF v).norm.tsum_le_tsum hterm (hp.mul_right (W v))
      _ = S * W v := by rw [tsum_mul_right]
  refine hinternal.congr ?_
  filter_upwards [] with v
  rw [← (summable_bombieriDigammaKernel_sub_inv v).tsum_mul_right]
  apply tsum_congr
  intro n
  rfl

private theorem continuous_bombieriDigammaKernel_zero :
    Continuous (fun v : ℝ ↦ (bombieriDigammaKernel 0 v : ℂ)) := by
  have hden (v : ℝ) : (1 / 4 : ℝ) + v ^ 2 ≠ 0 := by positivity
  have hreal : Continuous (fun v : ℝ ↦ bombieriDigammaKernel 0 v) := by
    unfold bombieriDigammaKernel
    norm_num
    exact (continuous_const.add (continuous_id.pow 2)).inv₀ hden
  exact Complex.continuous_ofReal.comp hreal

private theorem norm_bombieriDigammaKernel_zero_le (v : ℝ) :
    ‖(bombieriDigammaKernel 0 v : ℂ)‖ ≤ 4 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  unfold bombieriDigammaKernel
  norm_num
  have hden : 0 < (1 / 4 : ℝ) + v ^ 2 := by positivity
  rw [abs_of_pos hden]
  rw [inv_le_comm₀ hden (by norm_num : (0 : ℝ) < 4)]
  nlinarith [sq_nonneg v]

private theorem initialDigammaTerm_integrable
    (M : ℝ → ℂ) (hM : Integrable M) :
    Integrable (fun v : ℝ ↦
      (bombieriDigammaKernel 0 v : ℂ) * M v) :=
  hM.bdd_mul continuous_bombieriDigammaKernel_zero.aestronglyMeasurable
    (by filter_upwards [] with v; exact norm_bombieriDigammaKernel_zero_le v)

private theorem digamma_re_mul_eq
    (M : ℝ → ℂ) (v : ℝ) :
    ((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re : ℂ) * M v =
      -((bombieriDigammaKernel 0 v : ℂ) * M v +
        (Real.eulerMascheroniConstant : ℂ) * M v +
        (∑' n : ℕ,
            ((bombieriDigammaKernel (n + 1) v : ℂ) -
              (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ))) * M v) := by
  have hc := summable_bombieriDigammaKernel_sub_inv v
  have habs : Summable (fun n : ℕ ↦
      |bombieriDigammaKernel (n + 1) v - ((n + 1 : ℕ) : ℝ)⁻¹|) := by
    simpa only [← Complex.ofReal_inv, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs] using hc.norm
  have hreal : Summable (fun n : ℕ ↦
      bombieriDigammaKernel (n + 1) v - ((n + 1 : ℕ) : ℝ)⁻¹) :=
    habs.of_abs
  have hdig :
      ((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re : ℂ) =
        -((bombieriDigammaKernel 0 v : ℂ) +
          (Real.eulerMascheroniConstant : ℂ) +
          ∑' n : ℕ,
            ((bombieriDigammaKernel (n + 1) v : ℂ) -
              (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ))) := by
    rw [digamma_quarter_vertical_re_eq]
    push_cast
    rfl
  rw [hdig]
  ring

/-- Weighted integrability suffices for the full real-part digamma kernel
against an abstract spectral product. -/
theorem digamma_re_mul_integrable
    (M : ℝ → ℂ) (hM : Integrable M)
    (hW : Integrable (fun v : ℝ ↦ (1 + v ^ 2) * ‖M v‖)) :
    Integrable (fun v : ℝ ↦
      ((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re : ℂ) * M v) := by
  have hA := initialDigammaTerm_integrable M hM
  have hB := hM.const_mul (Real.eulerMascheroniConstant : ℂ)
  have hC := digammaSeries_integrable M hM hW
  refine (((hA.add hB).add hC).neg).congr ?_
  filter_upwards [] with v
  exact (digamma_re_mul_eq M v).symm

/-- The Bombieri local critical kernel, including `-log π`, is integrable
against every abstract spectral product with the weighted moment bound. -/
theorem localCriticalKernel_mul_integrable
    (M : ℝ → ℂ) (hM : Integrable M)
    (hW : Integrable (fun v : ℝ ↦ (1 + v ^ 2) * ‖M v‖)) :
    Integrable (fun v : ℝ ↦
      (((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re -
        Real.log Real.pi : ℝ) : ℂ) * M v) := by
  refine ((digamma_re_mul_integrable M hM hW).sub
    (hM.const_mul (Real.log Real.pi : ℂ))).congr ?_
  filter_upwards [] with v
  simp only [Pi.sub_apply]
  push_cast
  ring

/-- Abstract evaluation of the Bombieri local critical kernel once every
Cauchy summand and the unweighted Fourier integral have been identified. -/
theorem localCriticalKernel_integral_eq_cauchySeries
    (M : ℝ → ℂ) (hM : Integrable M)
    (hW : Integrable (fun v : ℝ ↦ (1 + v ^ 2) * ‖M v‖))
    (A : ℕ → ℂ) (H0 : ℂ)
    (hA : ∀ k : ℕ,
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ v : ℝ, (bombieriDigammaKernel k v : ℂ) * M v = A k)
    (hH0 : ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ v : ℝ, M v = H0) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ,
          (((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re -
            Real.log Real.pi : ℝ) : ℂ) * M v =
      -(A 0 + (Real.eulerMascheroniConstant : ℂ) * H0 +
          ∑' n : ℕ,
            (A (n + 1) - (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) * H0)) -
        (Real.log Real.pi : ℂ) * H0 := by
  let c : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  let K0 : ℝ → ℂ := fun v ↦ (bombieriDigammaKernel 0 v : ℂ) * M v
  let B : ℝ → ℂ := fun v ↦
    (Real.eulerMascheroniConstant : ℂ) * M v
  let C : ℝ → ℂ := fun v ↦
    (∑' n : ℕ,
      ((bombieriDigammaKernel (n + 1) v : ℂ) -
        (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ))) * M v
  let D : ℝ → ℂ := fun v ↦ (Real.log Real.pi : ℂ) * M v
  have hK0 : Integrable K0 := by
    simpa only [K0] using initialDigammaTerm_integrable M hM
  have hB : Integrable B := by
    simpa only [B] using
      (hM.const_mul (Real.eulerMascheroniConstant : ℂ))
  have hC : Integrable C := by
    simpa only [C] using (digammaSeries_integrable M hM hW)
  have hD : Integrable D := by
    simpa only [D] using (hM.const_mul (Real.log Real.pi : ℂ))
  have hseries :
      c * ∫ v : ℝ, C v =
        ∑' n : ℕ,
          (A (n + 1) - (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) * H0) := by
    have hpoint (v : ℝ) : C v =
        ∑' n : ℕ, digammaSeriesTerm M n v := by
      dsimp only [C]
      rw [← (summable_bombieriDigammaKernel_sub_inv v).tsum_mul_right]
      apply tsum_congr
      intro n
      rfl
    calc
      c * ∫ v : ℝ, C v =
          c * ∫ v : ℝ, ∑' n : ℕ, digammaSeriesTerm M n v := by
        congr 1
        apply integral_congr_ae
        filter_upwards [] with v
        exact hpoint v
      _ = c * ∑' n : ℕ, ∫ v : ℝ, digammaSeriesTerm M n v := by
        rw [integral_tsum_digammaSeriesTerm M hM hW]
      _ = ∑' n : ℕ,
          c * ∫ v : ℝ, digammaSeriesTerm M n v := by
        rw [tsum_mul_left]
      _ = _ := by
        apply tsum_congr
        intro n
        let r : ℂ := (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ)
        let Kn : ℝ → ℂ := fun v ↦
          (bombieriDigammaKernel (n + 1) v : ℂ) * M v
        have hrM : Integrable (fun v : ℝ ↦ r * M v) := hM.const_mul r
        have hKn : Integrable Kn := by
          refine ((digammaSeriesTerm_integrable M hM hW n).add hrM).congr ?_
          filter_upwards [] with v
          simp only [digammaSeriesTerm, Kn, r, Pi.add_apply]
          ring
        have hsplit :
            (∫ v : ℝ, digammaSeriesTerm M n v) =
              (∫ v : ℝ, Kn v) - r * ∫ v : ℝ, M v := by
          calc
            (∫ v : ℝ, digammaSeriesTerm M n v) =
                ∫ v : ℝ, Kn v - r * M v := by
              apply integral_congr_ae
              filter_upwards [] with v
              simp only [digammaSeriesTerm, Kn, r]
              ring
            _ = (∫ v : ℝ, Kn v) - ∫ v : ℝ, r * M v :=
              MeasureTheory.integral_sub hKn hrM
            _ = (∫ v : ℝ, Kn v) - r * ∫ v : ℝ, M v := by
              have hrint : (∫ v : ℝ, r * M v) =
                  r * ∫ v : ℝ, M v := by
                simpa using
                  (MeasureTheory.integral_const_mul (μ := volume) r M)
              exact congrArg (fun z : ℂ ↦ (∫ v : ℝ, Kn v) - z) hrint
        rw [hsplit]
        calc
          c * ((∫ v : ℝ, Kn v) - r * ∫ v : ℝ, M v) =
              c * (∫ v : ℝ, Kn v) - r * (c * ∫ v : ℝ, M v) := by ring
          _ = A (n + 1) - r * H0 := by
            rw [show c * (∫ v : ℝ, Kn v) = A (n + 1) by
              simpa only [c, Kn] using hA (n + 1),
              show c * (∫ v : ℝ, M v) = H0 by simpa only [c] using hH0]
          _ = A (n + 1) - (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) * H0 := by rfl
  have hdigamma :
      (∫ v : ℝ,
        ((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re : ℂ) * M v) =
        -(((∫ v : ℝ, K0 v) + (∫ v : ℝ, B v)) + ∫ v : ℝ, C v) := by
    have hKB : (∫ v : ℝ, K0 v + B v) =
        (∫ v : ℝ, K0 v) + ∫ v : ℝ, B v := by
      simpa only [Pi.add_apply] using MeasureTheory.integral_add hK0 hB
    have hKBC : (∫ v : ℝ, (K0 v + B v) + C v) =
        (∫ v : ℝ, K0 v + B v) + ∫ v : ℝ, C v := by
      simpa only [Pi.add_apply] using
        MeasureTheory.integral_add (hK0.add hB) hC
    calc
      (∫ v : ℝ,
          ((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re : ℂ) * M v) =
          ∫ v : ℝ, -(K0 v + B v + C v) := by
        apply integral_congr_ae
        filter_upwards [] with v
        simpa only [K0, B, C] using digamma_re_mul_eq M v
      _ = -(∫ v : ℝ, K0 v + B v + C v) :=
        MeasureTheory.integral_neg _
      _ = -(((∫ v : ℝ, K0 v) + (∫ v : ℝ, B v)) +
          ∫ v : ℝ, C v) := by rw [hKBC, hKB]
  have hlocal :
      (∫ v : ℝ,
          (((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re -
            Real.log Real.pi : ℝ) : ℂ) * M v) =
        (∫ v : ℝ,
          ((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re : ℂ) * M v) -
          ∫ v : ℝ, D v := by
    calc
      _ = ∫ v : ℝ,
          ((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re : ℂ) * M v -
            D v := by
        apply integral_congr_ae
        filter_upwards [] with v
        simp only [D]
        push_cast
        ring
      _ = _ := MeasureTheory.integral_sub
        (digamma_re_mul_integrable M hM hW) hD
  change c * (∫ v : ℝ,
      (((Complex.digamma ((1 / 4 : ℝ) + (v / 2) * I)).re -
        Real.log Real.pi : ℝ) : ℂ) * M v) = _
  rw [hlocal, hdigamma]
  have hBint : (∫ v : ℝ, B v) =
      (Real.eulerMascheroniConstant : ℂ) * ∫ v : ℝ, M v := by
    simpa only [B] using
      MeasureTheory.integral_const_mul
        (Real.eulerMascheroniConstant : ℂ) M
  have hDint : (∫ v : ℝ, D v) =
      (Real.log Real.pi : ℂ) * ∫ v : ℝ, M v := by
    simpa only [D] using
      MeasureTheory.integral_const_mul (Real.log Real.pi : ℂ) M
  rw [hBint, hDint]
  let x : ℂ := ∫ v : ℝ, K0 v
  let y : ℂ := ∫ v : ℝ, M v
  let z : ℂ := ∫ v : ℝ, C v
  change c * (-((x + (Real.eulerMascheroniConstant : ℂ) * y) + z) -
      (Real.log Real.pi : ℂ) * y) = _
  have hK0eval : c * x = A 0 := by
    simpa only [c, K0] using hA 0
  have hMeval : c * y = H0 := by
    simpa only [c] using hH0
  have hzeval : c * z =
      ∑' n : ℕ,
        (A (n + 1) - (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) * H0) := hseries
  calc
    c * (-((x + (Real.eulerMascheroniConstant : ℂ) * y) + z) -
        (Real.log Real.pi : ℂ) * y) =
        -(c * x + (Real.eulerMascheroniConstant : ℂ) * (c * y) + c * z) -
          (Real.log Real.pi : ℂ) * (c * y) := by ring
    _ = -(A 0 + (Real.eulerMascheroniConstant : ℂ) * H0 +
          ∑' n : ℕ,
            (A (n + 1) - (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) * H0)) -
        (Real.log Real.pi : ℂ) * H0 := by
      rw [hK0eval, hMeval, hzeval]

end

end ArithmeticHodge.Analysis.YoshidaDigammaDistribution
