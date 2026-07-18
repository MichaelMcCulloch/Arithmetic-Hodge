import ArithmeticHodge.Analysis.MultiplicativeWeilFarSupportSeparationStructural
import ArithmeticHodge.Analysis.YoshidaRenormalizedGeometricKernel

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ComplexConjugate FourierTransform SchwartzMap

namespace ArithmeticHodge.Analysis.MultiplicativeWeilFarCauchyMomentStructural

noncomputable section

open MultiplicativeWeil
open YoshidaBombieriCrossDistribution
open YoshidaBombieriCrossMoments
open YoshidaCauchyPairing
open YoshidaRenormalizedGeometricKernel
open MultiplicativeWeilFarSupportSeparationStructural

/-!
# Exact Cauchy moments between separated multiplicative cells

Positive normalized dilation translates the critical logarithmic pullback.
Consequently every bilateral critical moment acquires one exact exponential
factor.  When the dilated cell is weakly to the right of the first cell, the
cross-correlation vanishes on the nonpositive half-line.  The absolute value
in every Cauchy weight can then be removed, and each Cauchy value factors as a
rank-one product of critical moments.
-/

/-- Translation law for every real critical moment under a positive
normalized multiplicative dilation. -/
theorem bombieriCriticalMoment_normalizedDilation
    (g : BombieriTest) (r : ℝ) (hr : 0 < r) (s : ℝ) :
    bombieriCriticalMoment (normalizedDilation r hr g) s =
      ((Real.exp (s * Real.log r) : ℝ) : ℂ) *
        bombieriCriticalMoment g s := by
  let F : ℝ → ℂ := fun x ↦
    ((Real.exp (s * x) : ℝ) : ℂ) *
      g.logarithmicPullbackSchwartz (1 / 2) x
  unfold bombieriCriticalMoment
  simp_rw [normalizedDilation_logarithmicPullbackSchwartz_critical]
  calc
    (∫ x : ℝ, ((Real.exp (s * x) : ℝ) : ℂ) *
        g.logarithmicPullbackSchwartz (1 / 2)
          (x - Real.log r)) =
        ∫ x : ℝ, ((Real.exp (s * Real.log r) : ℝ) : ℂ) *
          F (x + (-Real.log r)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp only [F]
      rw [show x + -Real.log r = x - Real.log r by ring]
      have hexp : Real.exp (s * x) =
          Real.exp (s * Real.log r) *
            Real.exp (s * (x - Real.log r)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hexp]
      push_cast
      ring
    _ = ((Real.exp (s * Real.log r) : ℝ) : ℂ) *
        ∫ x : ℝ, F (x + (-Real.log r)) := by
      exact MeasureTheory.integral_const_mul _ _
    _ = ((Real.exp (s * Real.log r) : ℝ) : ℂ) *
        ∫ x : ℝ, F x := by
      rw [MeasureTheory.integral_add_right_eq_self]

/-- Under concrete cell separation, every Cauchy cross value is one exact
rank-one moment product.  The sign and order match the convention that the
first cell is conjugate-linear and the second cell is linear. -/
theorem bombieriCauchyCrossValue_normalizedDilation_eq_moments_of_support
    (f g : BombieriTest) {af bf ag bg r : ℝ}
    (haf : 0 < af) (hag : 0 < ag) (hbg : 0 < bg)
    (hr : 0 < r)
    (hfsupport : tsupport f ⊆ Set.Icc af bf)
    (hgsupport : tsupport g ⊆ Set.Icc ag bg)
    (hsep : bg ≤ r * af) (k : ℕ) :
    bombieriCauchyCrossValue f (normalizedDilation r hr g) k =
      ((Real.exp (-oddRate k * Real.log r) : ℝ) : ℂ) *
        starRingEnd ℂ (bombieriCriticalMoment f (oddRate k)) *
          bombieriCriticalMoment g (-oddRate k) := by
  let a : ℝ := oddRate k
  have hnonpos (u : ℝ) (hu : u ≤ 0) :
      bombieriCriticalCrossCorrelation f
          (normalizedDilation r hr g) u = 0 :=
    bombieriCriticalCrossCorrelation_normalizedDilation_eq_zero_of_nonpos
      f g haf hag hbg hr hfsupport hgsupport hsep hu
  have hremoveAbs :
      bombieriCauchyCrossValue f (normalizedDilation r hr g) k =
        ∫ u : ℝ, ((Real.exp (-a * u) : ℝ) : ℂ) *
          bombieriCriticalCrossCorrelation f
            (normalizedDilation r hr g) u := by
    rw [bombieriCauchyCrossValue]
    apply integral_congr_ae
    filter_upwards [] with u
    by_cases hu : 0 < u
    · rw [abs_of_pos hu]
      rfl
    · have hzero := hnonpos u (le_of_not_gt hu)
      rw [hzero, mul_zero, mul_zero]
  rw [hremoveAbs]
  have hfactor := integral_exp_mul_bombieriCriticalCrossCorrelation
    (-a) f (normalizedDilation r hr g)
  rw [show -(-a) = a by ring] at hfactor
  rw [hfactor, bombieriCriticalMoment_normalizedDilation]
  dsimp only [a]
  simp only [starRingEnd_apply]
  ring

/-- Shifted tail specialization used by the far local-critical expansion. -/
theorem bombieriCauchyCrossValue_normalizedDilation_tail_eq_moments_of_support
    (f g : BombieriTest) {af bf ag bg r : ℝ}
    (haf : 0 < af) (hag : 0 < ag) (hbg : 0 < bg)
    (hr : 0 < r)
    (hfsupport : tsupport f ⊆ Set.Icc af bf)
    (hgsupport : tsupport g ⊆ Set.Icc ag bg)
    (hsep : bg ≤ r * af) (k : ℕ) :
    bombieriCauchyCrossValue f
        (normalizedDilation r hr g) (k + 1) =
      ((Real.exp (-oddRate (k + 1) * Real.log r) : ℝ) : ℂ) *
        starRingEnd ℂ (bombieriCriticalMoment f (oddRate (k + 1))) *
          bombieriCriticalMoment g (-oddRate (k + 1)) :=
  bombieriCauchyCrossValue_normalizedDilation_eq_moments_of_support
    f g haf hag hbg hr hfsupport hgsupport hsep (k + 1)

/-! ## Genuine summability of the separated tail -/

private def farCauchyRenormalizedSpectralTerm
    (f h : BombieriTest) (n : ℕ) (v : ℝ) : ℂ :=
  ((bombieriDigammaKernel (n + 1) v : ℂ) -
      (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ)) *
    bombieriCriticalSpectralProduct f h v

private theorem farCauchyRenormalizedSpectralTerm_integrable
    (f h : BombieriTest) (n : ℕ) :
    Integrable (farCauchyRenormalizedSpectralTerm f h n) := by
  let M : ℝ → ℂ := bombieriCriticalSpectralProduct f h
  let p : ℝ := (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹
  have hM : Integrable M := by
    simpa only [M] using bombieriCriticalSpectralProduct_integrable f h
  have hW : Integrable (fun v : ℝ ↦
      (1 + v ^ 2) * ‖M v‖) := by
    simpa only [M] using
      bombieriCriticalSpectralProduct_weighted_integrable f h
  have hmajor : Integrable (fun v : ℝ ↦
      p * ((1 + v ^ 2) * ‖M v‖)) := hW.const_mul p
  have hcoeff : Continuous (fun v : ℝ ↦
      (bombieriDigammaKernel (n + 1) v : ℂ) -
        (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ)) := by
    have hden (v : ℝ) :
        (2 * ((n + 1 : ℕ) : ℝ) + 1 / 2) ^ 2 + v ^ 2 ≠ 0 := by
      positivity
    have hreal : Continuous (fun v : ℝ ↦
        bombieriDigammaKernel (n + 1) v) := by
      unfold bombieriDigammaKernel
      exact continuous_const.div
        ((continuous_const.pow 2).add (continuous_id.pow 2)) hden
    exact (Complex.continuous_ofReal.comp hreal).sub continuous_const
  apply hmajor.mono'
  · exact hcoeff.aestronglyMeasurable.mul hM.1
  · filter_upwards [] with v
    simp only [farCauchyRenormalizedSpectralTerm, M, norm_mul]
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

private theorem summable_integral_norm_farCauchyRenormalizedSpectralTerm
    (f h : BombieriTest) :
    Summable (fun n : ℕ ↦
      ∫ v : ℝ, ‖farCauchyRenormalizedSpectralTerm f h n v‖) := by
  let M : ℝ → ℂ := bombieriCriticalSpectralProduct f h
  let W : ℝ → ℝ := fun v ↦ (1 + v ^ 2) * ‖M v‖
  let C : ℝ := ∫ v : ℝ, W v
  have hW : Integrable W := by
    simpa only [W, M] using
      bombieriCriticalSpectralProduct_weighted_integrable f h
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
    have hterm := farCauchyRenormalizedSpectralTerm_integrable f h n
    have hmajorInt : Integrable (fun v : ℝ ↦
        (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ * W v) :=
      hW.const_mul _
    calc
      (∫ v : ℝ, ‖farCauchyRenormalizedSpectralTerm f h n v‖) ≤
          ∫ v : ℝ, (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ * W v := by
        apply integral_mono hterm.norm hmajorInt
        intro v
        simp only [farCauchyRenormalizedSpectralTerm, norm_mul]
        rw [← Complex.ofReal_inv, ← Complex.ofReal_sub,
          Complex.norm_real, Real.norm_eq_abs]
        calc
          |bombieriDigammaKernel (n + 1) v -
                ((n + 1 : ℕ) : ℝ)⁻¹| *
              ‖bombieriCriticalSpectralProduct f h v‖ ≤
              ((1 + v ^ 2) / (((n + 1 : ℕ) : ℝ) ^ 2)) *
                ‖bombieriCriticalSpectralProduct f h v‖ :=
            mul_le_mul_of_nonneg_right
              (abs_bombieriDigammaKernel_sub_inv_le n v) (norm_nonneg _)
          _ = (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ * W v := by
            simp only [W, M, div_eq_mul_inv]
            ring
      _ = (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹ * C := by
        rw [MeasureTheory.integral_const_mul]

private theorem summable_integral_farCauchyRenormalizedSpectralTerm
    (f h : BombieriTest) :
    Summable (fun n : ℕ ↦
      ∫ v : ℝ, farCauchyRenormalizedSpectralTerm f h n v) := by
  have hnorm : Summable (fun n : ℕ ↦
      ‖∫ v : ℝ, farCauchyRenormalizedSpectralTerm f h n v‖) := by
    apply (summable_integral_norm_farCauchyRenormalizedSpectralTerm f h).of_nonneg_of_le
    · intro n
      exact norm_nonneg _
    · intro n
      exact norm_integral_le_integral_norm _
  exact hnorm.of_norm

private theorem bombieriCauchyCrossValue_tail_eq_renormalizedSpectralTerm
    (f h : BombieriTest)
    (hzero : bombieriCriticalCrossCorrelation f h 0 = 0)
    (n : ℕ) :
    bombieriCauchyCrossValue f h (n + 1) =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ, farCauchyRenormalizedSpectralTerm f h n v) := by
  let M : ℝ → ℂ := bombieriCriticalSpectralProduct f h
  let q : ℂ := (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ)
  let c : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  have hM : Integrable M := by
    simpa only [M] using bombieriCriticalSpectralProduct_integrable f h
  have hqM : Integrable (fun v : ℝ ↦ q * M v) := hM.const_mul q
  have hrenorm := farCauchyRenormalizedSpectralTerm_integrable f h n
  have hkernel : Integrable (fun v : ℝ ↦
      (bombieriDigammaKernel (n + 1) v : ℂ) * M v) := by
    refine (hrenorm.add hqM).congr ?_
    filter_upwards [] with v
    change farCauchyRenormalizedSpectralTerm f h n v + q * M v =
      (bombieriDigammaKernel (n + 1) v : ℂ) * M v
    unfold farCauchyRenormalizedSpectralTerm
    dsimp only [M, q]
    ring
  have hmean := normalized_integral_bombieriCriticalSpectralProduct_eq_zeroCorrelation
    f h
  rw [hzero] at hmean
  have hkernelValue := normalized_bombieriDigammaKernel_crossProduct
    f h (n + 1)
  have hintegral :
      (∫ v : ℝ, farCauchyRenormalizedSpectralTerm f h n v) =
        (∫ v : ℝ,
          (bombieriDigammaKernel (n + 1) v : ℂ) * M v) -
          q * ∫ v : ℝ, M v := by
    rw [show farCauchyRenormalizedSpectralTerm f h n =
        fun v : ℝ ↦
          (bombieriDigammaKernel (n + 1) v : ℂ) * M v - q * M v by
      funext v
      simp only [farCauchyRenormalizedSpectralTerm, M, q]
      ring]
    rw [integral_sub hkernel hqM]
    congr 1
    exact MeasureTheory.integral_const_mul q M
  change bombieriCauchyCrossValue f h (n + 1) =
    c * ∫ v : ℝ, farCauchyRenormalizedSpectralTerm f h n v
  change c * (∫ v : ℝ,
      (bombieriDigammaKernel (n + 1) v : ℂ) * M v) = _ at hkernelValue
  change c * (∫ v : ℝ, M v) = 0 at hmean
  calc
    bombieriCauchyCrossValue f h (n + 1) =
        c * ∫ v : ℝ,
          (bombieriDigammaKernel (n + 1) v : ℂ) * M v :=
      hkernelValue.symm
    _ = c * (∫ v : ℝ,
          (bombieriDigammaKernel (n + 1) v : ℂ) * M v) -
        q * (c * ∫ v : ℝ, M v) := by
      rw [hmean, mul_zero, sub_zero]
    _ = c * ((∫ v : ℝ,
          (bombieriDigammaKernel (n + 1) v : ℂ) * M v) -
        q * ∫ v : ℝ, M v) := by ring
    _ = c * ∫ v : ℝ,
        farCauchyRenormalizedSpectralTerm f h n v := by
      exact (congrArg (fun z : ℂ ↦ c * z) hintegral).symm

/-- The raw shifted Cauchy tail is genuinely summable after support
separation.  Zero-lag cancellation removes its otherwise harmonic leading
term, leaving the summable quadratic digamma remainder. -/
theorem summable_bombieriCauchyCrossValue_normalizedDilation_tail_of_support
    (f g : BombieriTest) {af bf ag bg r : ℝ}
    (haf : 0 < af) (hag : 0 < ag) (hbg : 0 < bg)
    (hr : 0 < r)
    (hfsupport : tsupport f ⊆ Set.Icc af bf)
    (hgsupport : tsupport g ⊆ Set.Icc ag bg)
    (hsep : bg ≤ r * af) :
    Summable (fun k : ℕ ↦ bombieriCauchyCrossValue f
      (normalizedDilation r hr g) (k + 1)) := by
  let h : BombieriTest := normalizedDilation r hr g
  have hzero : bombieriCriticalCrossCorrelation f h 0 = 0 := by
    dsimp only [h]
    exact bombieriCriticalCrossCorrelation_normalizedDilation_eq_zero_of_nonpos
      f g haf hag hbg hr hfsupport hgsupport hsep le_rfl
  have hs :=
    (summable_integral_farCauchyRenormalizedSpectralTerm f h).mul_left
      (((1 / (2 * Real.pi) : ℝ) : ℂ))
  exact hs.congr fun k ↦
    (bombieriCauchyCrossValue_tail_eq_renormalizedSpectralTerm
      f h hzero k).symm

/-- Hence the explicit shifted moment-product tail is also genuinely
summable. -/
theorem summable_farCauchyMomentTail_of_support
    (f g : BombieriTest) {af bf ag bg r : ℝ}
    (haf : 0 < af) (hag : 0 < ag) (hbg : 0 < bg)
    (hr : 0 < r)
    (hfsupport : tsupport f ⊆ Set.Icc af bf)
    (hgsupport : tsupport g ⊆ Set.Icc ag bg)
    (hsep : bg ≤ r * af) :
    Summable (fun k : ℕ ↦
      ((Real.exp (-oddRate (k + 1) * Real.log r) : ℝ) : ℂ) *
        starRingEnd ℂ
          (bombieriCriticalMoment f (oddRate (k + 1))) *
        bombieriCriticalMoment g (-oddRate (k + 1))) := by
  exact
    (summable_bombieriCauchyCrossValue_normalizedDilation_tail_of_support
      f g haf hag hbg hr hfsupport hgsupport hsep).congr fun k ↦
        bombieriCauchyCrossValue_normalizedDilation_tail_eq_moments_of_support
          f g haf hag hbg hr hfsupport hgsupport hsep k

/-- Exact summation bridge from the far Cauchy tail to its rank-one moment
series. -/
theorem tsum_bombieriCauchyCrossValue_normalizedDilation_tail_eq_moments
    (f g : BombieriTest) {af bf ag bg r : ℝ}
    (haf : 0 < af) (hag : 0 < ag) (hbg : 0 < bg)
    (hr : 0 < r)
    (hfsupport : tsupport f ⊆ Set.Icc af bf)
    (hgsupport : tsupport g ⊆ Set.Icc ag bg)
    (hsep : bg ≤ r * af) :
    (∑' k : ℕ, bombieriCauchyCrossValue f
        (normalizedDilation r hr g) (k + 1)) =
      ∑' k : ℕ,
        ((Real.exp (-oddRate (k + 1) * Real.log r) : ℝ) : ℂ) *
          starRingEnd ℂ
            (bombieriCriticalMoment f (oddRate (k + 1))) *
          bombieriCriticalMoment g (-oddRate (k + 1)) := by
  apply tsum_congr
  intro k
  exact bombieriCauchyCrossValue_normalizedDilation_tail_eq_moments_of_support
    f g haf hag hbg hr hfsupport hgsupport hsep k

end

end ArithmeticHodge.Analysis.MultiplicativeWeilFarCauchyMomentStructural
