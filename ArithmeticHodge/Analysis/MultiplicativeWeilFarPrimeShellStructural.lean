import ArithmeticHodge.Analysis.MultiplicativeWeilTwoSeedFactorTwo

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ArithmeticFunction ContDiff Distributions

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-!
# The prime shell between separated multiplicative cells

If `f` is supported in `[af, bf]`, `g` is supported in `[ag, bg]`, and
`r > bg / af`, then `normalizedDilation r hr g` lies strictly to the left of
`f`.  At every positive integer the directed correlation from the dilated
cell back to `f` therefore vanishes.  The polarized prime cross is exactly the
remaining, `r⁻¹ᐟ²`-scaled directed-correlation shell.
-/

/-- Dilation in the first slot rescales a two-seed directed correlation
without a change of variables. -/
theorem bombieriDirectedCorrelation_normalizedDilation_left_twoSeed
    (f g : BombieriTest) (r : ℝ) (hr : 0 < r) (x : ℝ) :
    bombieriDirectedCorrelation
        (normalizedDilation r hr g) f x =
      ((Real.sqrt r : ℝ) : ℂ) *
        bombieriDirectedCorrelation g f (r * x) := by
  unfold bombieriDirectedCorrelation
  calc
    (∫ y : ℝ in Set.Ioi 0,
        normalizedDilation r hr g (x * y) * starRingEnd ℂ (f y)) =
        ∫ y : ℝ in Set.Ioi 0,
          ((Real.sqrt r : ℝ) : ℂ) *
            (g ((r * x) * y) * starRingEnd ℂ (f y)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y _hy
      change normalizedDilation r hr g (x * y) *
          starRingEnd ℂ (f y) =
        ((Real.sqrt r : ℝ) : ℂ) *
          (g ((r * x) * y) * starRingEnd ℂ (f y))
      rw [normalizedDilation_apply]
      rw [show r * (x * y) = (r * x) * y by ring]
      ring
    _ = ((Real.sqrt r : ℝ) : ℂ) *
        ∫ y : ℝ in Set.Ioi 0,
          g ((r * x) * y) * starRingEnd ℂ (f y) := by
      exact MeasureTheory.integral_const_mul
        (μ := volume.restrict (Set.Ioi 0)) _ _

/-- After multiplication by `sqrt r`, dilation in the second slot rescales a
two-seed directed correlation by the inverse dilation. -/
theorem sqrt_mul_bombieriDirectedCorrelation_normalizedDilation_right_twoSeed
    (f g : BombieriTest) (r : ℝ) (hr : 0 < r) (x : ℝ) :
    ((Real.sqrt r : ℝ) : ℂ) *
        bombieriDirectedCorrelation f
          (normalizedDilation r hr g) x =
      bombieriDirectedCorrelation f g (r⁻¹ * x) := by
  let F : ℝ → ℂ := fun y ↦
    f ((r⁻¹ * x) * y) * starRingEnd ℂ (g y)
  have hscale := integral_comp_mul_right_Ioi F 0 hr
  have hscale' :
      (∫ y : ℝ in Set.Ioi 0, F (y * r)) =
        (((r⁻¹ : ℝ) : ℂ) *
          ∫ y : ℝ in Set.Ioi 0, F y) := by
    simpa only [zero_mul, Complex.real_smul] using hscale
  unfold bombieriDirectedCorrelation
  calc
    ((Real.sqrt r : ℝ) : ℂ) *
        ∫ y : ℝ in Set.Ioi 0,
          f (x * y) *
            starRingEnd ℂ (normalizedDilation r hr g y) =
        ((Real.sqrt r : ℝ) : ℂ) *
          (((Real.sqrt r : ℝ) : ℂ) *
            ∫ y : ℝ in Set.Ioi 0, F (y * r)) := by
      congr 1
      calc
        (∫ y : ℝ in Set.Ioi 0,
            f (x * y) *
              starRingEnd ℂ (normalizedDilation r hr g y)) =
            ∫ y : ℝ in Set.Ioi 0,
              ((Real.sqrt r : ℝ) : ℂ) * F (y * r) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro y _hy
          change f (x * y) *
              starRingEnd ℂ (normalizedDilation r hr g y) =
            ((Real.sqrt r : ℝ) : ℂ) * F (y * r)
          rw [normalizedDilation_apply]
          have hconj :
              starRingEnd ℂ
                  (((Real.sqrt r : ℝ) : ℂ) * g (r * y)) =
                ((Real.sqrt r : ℝ) : ℂ) *
                  starRingEnd ℂ (g (r * y)) := by
            rw [map_mul, Complex.conj_ofReal]
          rw [hconj]
          dsimp only [F]
          have harg : (r⁻¹ * x) * (y * r) = x * y := by
            field_simp [hr.ne']
          rw [harg]
          ring_nf
        _ = ((Real.sqrt r : ℝ) : ℂ) *
            ∫ y : ℝ in Set.Ioi 0, F (y * r) := by
          exact MeasureTheory.integral_const_mul
            (μ := volume.restrict (Set.Ioi 0)) _ _
    _ = (r : ℂ) * ∫ y : ℝ in Set.Ioi 0, F (y * r) := by
      rw [← mul_assoc]
      congr 1
      norm_cast
      simpa [pow_two] using Real.sq_sqrt hr.le
    _ = (r : ℂ) *
        (((r⁻¹ : ℝ) : ℂ) * ∫ y : ℝ in Set.Ioi 0, F y) := by
      rw [hscale']
    _ = ∫ y : ℝ in Set.Ioi 0, F y := by
      rw [Complex.ofReal_inv]
      field_simp [hr.ne']

/-- Once the dilated `g`-cell lies strictly to the left of the `f`-cell, the
reverse directed correlation vanishes at every lag at least one. -/
theorem bombieriDirectedCorrelation_normalizedDilation_left_eq_zero_of_far
    (f g : BombieriTest) {af bf ag bg r x : ℝ}
    (hr : 0 < r) (haf : 0 < af)
    (hf : tsupport f ⊆ Set.Icc af bf)
    (hg : tsupport g ⊆ Set.Icc ag bg)
    (hsep : bg / af < r) (hx : 1 ≤ x) :
    bombieriDirectedCorrelation
        (normalizedDilation r hr g) f x = 0 := by
  unfold bombieriDirectedCorrelation
  apply integral_eq_zero_of_ae
  filter_upwards [] with y
  change normalizedDilation r hr g (x * y) *
      starRingEnd ℂ (f y) = 0
  rw [normalizedDilation_apply]
  by_cases hgy : g (r * (x * y)) = 0
  · simp [hgy]
  by_cases hfy : f y = 0
  · simp [hfy]
  exfalso
  have hgm := hg
    (subset_tsupport g (Function.mem_support.mpr hgy))
  have hfm := hf
    (subset_tsupport f (Function.mem_support.mpr hfy))
  have hy : 0 < y := haf.trans_le hfm.1
  have hraf : bg < r * af := by
    exact (div_lt_iff₀ haf).mp hsep
  have hry : r * af ≤ r * (x * y) := by
    apply mul_le_mul_of_nonneg_left _ hr.le
    calc
      af ≤ y := hfm.1
      _ ≤ x * y := by nlinarith
  exact (not_le_of_gt hraf) (hry.trans hgm.2)

/-- Pointwise version at a positive integer index. -/
theorem bombieriDirectedCorrelation_normalizedDilation_left_nat_eq_zero_of_far
    (f g : BombieriTest) {af bf ag bg r : ℝ}
    (hr : 0 < r) (haf : 0 < af)
    (hf : tsupport f ⊆ Set.Icc af bf)
    (hg : tsupport g ⊆ Set.Icc ag bg)
    (hsep : bg / af < r) (k : ℕ) :
    bombieriDirectedCorrelation
        (normalizedDilation r hr g) f (k + 1 : ℕ) = 0 := by
  apply bombieriDirectedCorrelation_normalizedDilation_left_eq_zero_of_far
    f g hr haf hf hg hsep
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero k)

/-- The complex polarization of one Mangoldt summand is the Hermitian
directed-correlation shell at that integer. -/
theorem vonMangoldtPrimeSummand_polarization_eq_directedShell
    (f h : BombieriTest) (k : ℕ) :
    (((vonMangoldtPrimeSummand
          (bombieriQuadraticCrossTest f h) k).re / 2 : ℝ) : ℂ) -
        (((vonMangoldtPrimeSummand
          (bombieriQuadraticCrossTest f (Complex.I • h)) k).re / 2 : ℝ) : ℂ) *
          Complex.I =
      (ArithmeticFunction.vonMangoldt (k + 1) : ℂ) *
        (bombieriDirectedCorrelation h f (k + 1 : ℕ) +
          starRingEnd ℂ
            (bombieriDirectedCorrelation f h (k + 1 : ℕ))) := by
  have hn : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  unfold vonMangoldtPrimeSummand primeKernel
  rw [transpose_bombieriQuadraticCrossTest_apply_eq_conj f h hn,
    transpose_bombieriQuadraticCrossTest_apply_eq_conj
      f (Complex.I • h) hn]
  rw [bombieriQuadraticCrossTest_apply,
    bombieriQuadraticCrossTest_apply]
  simp only [bombieriDirectedCorrelation_smul_left,
    bombieriDirectedCorrelation_smul_right, starRingEnd_apply,
    map_add, map_mul]
  simp only [Complex.star_def]
  apply Complex.ext
  · simp
    ring
  · simp
    ring

/-- The Mangoldt-weighted Hermitian shell formed from two directed
correlations.  Its summability will follow from the finite support of the
corresponding prime summands. -/
def bombieriPrimeDirectedShell (f h : BombieriTest) : ℂ :=
  ∑' k : ℕ, (ArithmeticFunction.vonMangoldt (k + 1) : ℂ) *
    (bombieriDirectedCorrelation h f (k + 1 : ℕ) +
      starRingEnd ℂ
        (bombieriDirectedCorrelation f h (k + 1 : ℕ)))

private def bombieriPrimePolarizationSummand
    (f h : BombieriTest) (k : ℕ) : ℂ :=
  (((vonMangoldtPrimeSummand
        (bombieriQuadraticCrossTest f h) k).re / 2 : ℝ) : ℂ) -
    (((vonMangoldtPrimeSummand
      (bombieriQuadraticCrossTest f (Complex.I • h)) k).re / 2 : ℝ) : ℂ) *
      Complex.I

private theorem bombieriPrimePolarizationSummand_summable
    (f h : BombieriTest) :
    Summable (bombieriPrimePolarizationSummand f h) := by
  let s₁ : ℕ → ℂ := vonMangoldtPrimeSummand
    (bombieriQuadraticCrossTest f h)
  let s₂ : ℕ → ℂ := vonMangoldtPrimeSummand
    (bombieriQuadraticCrossTest f (Complex.I • h))
  have hs₁ : Summable s₁ :=
    vonMangoldtPrimeSummand_summable (bombieriQuadraticCrossTest f h)
  have hs₂ : Summable s₂ :=
    vonMangoldtPrimeSummand_summable
      (bombieriQuadraticCrossTest f (Complex.I • h))
  have hr₁ : Summable (fun k ↦ (s₁ k).re / 2) :=
    (Complex.hasSum_re hs₁.hasSum).summable.div_const 2
  have hr₂ : Summable (fun k ↦ (s₂ k).re / 2) :=
    (Complex.hasSum_re hs₂.hasSum).summable.div_const 2
  have hc₁ : Summable (fun k ↦ (((s₁ k).re / 2 : ℝ) : ℂ)) :=
    Complex.summable_ofReal.mpr hr₁
  have hc₂ : Summable (fun k ↦ (((s₂ k).re / 2 : ℝ) : ℂ)) :=
    Complex.summable_ofReal.mpr hr₂
  simpa only [bombieriPrimePolarizationSummand, s₁, s₂] using
    hc₁.sub (hc₂.mul_right Complex.I)

private theorem tsum_bombieriPrimePolarizationSummand
    (f h : BombieriTest) :
    (∑' k : ℕ, bombieriPrimePolarizationSummand f h k) =
      bombieriPolarizedPrimeCross f h := by
  let s₁ : ℕ → ℂ := vonMangoldtPrimeSummand
    (bombieriQuadraticCrossTest f h)
  let s₂ : ℕ → ℂ := vonMangoldtPrimeSummand
    (bombieriQuadraticCrossTest f (Complex.I • h))
  have hs₁ : Summable s₁ :=
    vonMangoldtPrimeSummand_summable (bombieriQuadraticCrossTest f h)
  have hs₂ : Summable s₂ :=
    vonMangoldtPrimeSummand_summable
      (bombieriQuadraticCrossTest f (Complex.I • h))
  have hr₁ : Summable (fun k ↦ (s₁ k).re / 2) :=
    (Complex.hasSum_re hs₁.hasSum).summable.div_const 2
  have hr₂ : Summable (fun k ↦ (s₂ k).re / 2) :=
    (Complex.hasSum_re hs₂.hasSum).summable.div_const 2
  have hc₁ : Summable (fun k ↦ (((s₁ k).re / 2 : ℝ) : ℂ)) :=
    Complex.summable_ofReal.mpr hr₁
  have hc₂ : Summable (fun k ↦ (((s₂ k).re / 2 : ℝ) : ℂ)) :=
    Complex.summable_ofReal.mpr hr₂
  have htsum₁ :
      (∑' k : ℕ, (((s₁ k).re / 2 : ℝ) : ℂ)) =
        ((((∑' k : ℕ, s₁ k).re / 2 : ℝ)) : ℂ) := by
    calc
      (∑' k : ℕ, (((s₁ k).re / 2 : ℝ) : ℂ)) =
          (((∑' k : ℕ, (s₁ k).re / 2) : ℝ) : ℂ) := by
        rw [Complex.ofReal_tsum]
      _ = (((∑' k : ℕ, (s₁ k).re) / 2 : ℝ) : ℂ) := by
        rw [tsum_div_const]
      _ = ((((∑' k : ℕ, s₁ k).re / 2 : ℝ)) : ℂ) := by
        rw [Complex.re_tsum hs₁]
  have htsum₂ :
      (∑' k : ℕ, (((s₂ k).re / 2 : ℝ) : ℂ)) =
        ((((∑' k : ℕ, s₂ k).re / 2 : ℝ)) : ℂ) := by
    calc
      (∑' k : ℕ, (((s₂ k).re / 2 : ℝ) : ℂ)) =
          (((∑' k : ℕ, (s₂ k).re / 2) : ℝ) : ℂ) := by
        rw [Complex.ofReal_tsum]
      _ = (((∑' k : ℕ, (s₂ k).re) / 2 : ℝ) : ℂ) := by
        rw [tsum_div_const]
      _ = ((((∑' k : ℕ, s₂ k).re / 2 : ℝ)) : ℂ) := by
        rw [Complex.re_tsum hs₂]
  rw [show (∑' k : ℕ, bombieriPrimePolarizationSummand f h k) =
      (∑' k : ℕ, (((s₁ k).re / 2 : ℝ) : ℂ)) -
        (∑' k : ℕ, (((s₂ k).re / 2 : ℝ) : ℂ)) * Complex.I by
    change tsum (fun k : ℕ ↦
        (((s₁ k).re / 2 : ℝ) : ℂ) -
          (((s₂ k).re / 2 : ℝ) : ℂ) * Complex.I) = _
    rw [hc₁.tsum_sub (hc₂.mul_right Complex.I),
      hc₂.tsum_mul_right Complex.I]]
  rw [htsum₁, htsum₂]
  rfl

/-- Support-free shell formula for the polarized prime cross. -/
theorem bombieriPolarizedPrimeCross_eq_primeDirectedShell
    (f h : BombieriTest) :
    bombieriPolarizedPrimeCross f h =
      bombieriPrimeDirectedShell f h := by
  rw [← tsum_bombieriPrimePolarizationSummand f h]
  unfold bombieriPrimeDirectedShell
  apply tsum_congr
  intro k
  exact vonMangoldtPrimeSummand_polarization_eq_directedShell f h k

/-- The directed shell is genuinely summable (indeed finite), rather than
depending on the totalized value of a nonsummable series. -/
theorem bombieriPrimeDirectedShell_summable (f h : BombieriTest) :
    Summable (fun k : ℕ ↦
      (ArithmeticFunction.vonMangoldt (k + 1) : ℂ) *
        (bombieriDirectedCorrelation h f (k + 1 : ℕ) +
          starRingEnd ℂ
            (bombieriDirectedCorrelation f h (k + 1 : ℕ)))) := by
  exact (bombieriPrimePolarizationSummand_summable f h).congr fun k ↦
    vonMangoldtPrimeSummand_polarization_eq_directedShell f h k

/-- The reverse Mangoldt shell from a dilated cell back into the original
cell. -/
def bombieriReverseDilationPrimeShell
    (f g : BombieriTest) (r : ℝ) (hr : 0 < r) : ℂ :=
  ∑' k : ℕ, (ArithmeticFunction.vonMangoldt (k + 1) : ℂ) *
    bombieriDirectedCorrelation
      (normalizedDilation r hr g) f (k + 1 : ℕ)

/-- Strict cell separation kills the complete reverse Mangoldt shell,
pointwise before summation. -/
theorem bombieriReverseDilationPrimeShell_eq_zero_of_far
    (f g : BombieriTest) {af bf ag bg r : ℝ}
    (hr : 0 < r) (haf : 0 < af)
    (hf : tsupport f ⊆ Set.Icc af bf)
    (hg : tsupport g ⊆ Set.Icc ag bg)
    (hsep : bg / af < r) :
    bombieriReverseDilationPrimeShell f g r hr = 0 := by
  unfold bombieriReverseDilationPrimeShell
  calc
    (∑' k : ℕ, (ArithmeticFunction.vonMangoldt (k + 1) : ℂ) *
        bombieriDirectedCorrelation
          (normalizedDilation r hr g) f (k + 1 : ℕ)) =
        ∑' _k : ℕ, (0 : ℂ) := by
      apply tsum_congr
      intro k
      rw [bombieriDirectedCorrelation_normalizedDilation_left_nat_eq_zero_of_far
        f g hr haf hf hg hsep k, mul_zero]
    _ = 0 := tsum_zero

/-- The surviving separated prime shell, written entirely in the undilated
cell coordinates.  The factor `1 / sqrt r` is the normalized-dilation
Jacobian. -/
def bombieriSeparatedFarPrimeShell
    (f g : BombieriTest) (r : ℝ) : ℂ :=
  ∑' k : ℕ, (ArithmeticFunction.vonMangoldt (k + 1) : ℂ) *
    ((((Real.sqrt r)⁻¹ : ℝ) : ℂ) *
      starRingEnd ℂ
        (bombieriDirectedCorrelation f g
          (r⁻¹ * (k + 1 : ℕ))))

private theorem primeDirectedShell_dilation_summand_eq_of_far
    (f g : BombieriTest) {af bf ag bg r : ℝ}
    (hr : 0 < r) (haf : 0 < af)
    (hf : tsupport f ⊆ Set.Icc af bf)
    (hg : tsupport g ⊆ Set.Icc ag bg)
    (hsep : bg / af < r) (k : ℕ) :
    (ArithmeticFunction.vonMangoldt (k + 1) : ℂ) *
        (bombieriDirectedCorrelation
            (normalizedDilation r hr g) f (k + 1 : ℕ) +
          starRingEnd ℂ
            (bombieriDirectedCorrelation f
              (normalizedDilation r hr g) (k + 1 : ℕ))) =
      (ArithmeticFunction.vonMangoldt (k + 1) : ℂ) *
        ((((Real.sqrt r)⁻¹ : ℝ) : ℂ) *
          starRingEnd ℂ
            (bombieriDirectedCorrelation f g
              (r⁻¹ * (k + 1 : ℕ)))) := by
  have hreverse :
      bombieriDirectedCorrelation
          (normalizedDilation r hr g) f (k + 1 : ℕ) = 0 :=
    bombieriDirectedCorrelation_normalizedDilation_left_nat_eq_zero_of_far
      f g hr haf hf hg hsep k
  have hforward :=
    sqrt_mul_bombieriDirectedCorrelation_normalizedDilation_right_twoSeed
      f g r hr (k + 1 : ℕ)
  have hsqrt : ((Real.sqrt r : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hr).ne'
  have hforward' :
      bombieriDirectedCorrelation f
          (normalizedDilation r hr g) (k + 1 : ℕ) =
        ((Real.sqrt r : ℝ) : ℂ)⁻¹ *
          bombieriDirectedCorrelation f g
            (r⁻¹ * (k + 1 : ℕ)) := by
    apply (mul_left_cancel₀ hsqrt)
    rw [hforward]
    field_simp [hsqrt]
  rw [hreverse, zero_add, hforward', map_mul]
  rw [starRingEnd_apply, star_inv₀, Complex.star_def,
    Complex.conj_ofReal, ← Complex.ofReal_inv]

/-- Exact prime-shell formula for multiplicatively separated cells.  No
truncation or numerical estimate is involved: the reverse orientation is
zero term by term, and the only surviving terms carry the exact
`r⁻¹ᐟ²` normalization. -/
theorem bombieriPolarizedPrimeCross_normalizedDilation_eq_farPrimeShell
    (f g : BombieriTest) {af bf ag bg r : ℝ}
    (hr : 0 < r) (haf : 0 < af)
    (hf : tsupport f ⊆ Set.Icc af bf)
    (hg : tsupport g ⊆ Set.Icc ag bg)
    (hsep : bg / af < r) :
    bombieriPolarizedPrimeCross f (normalizedDilation r hr g) =
      bombieriSeparatedFarPrimeShell f g r := by
  rw [bombieriPolarizedPrimeCross_eq_primeDirectedShell]
  unfold bombieriPrimeDirectedShell bombieriSeparatedFarPrimeShell
  apply tsum_congr
  intro k
  exact primeDirectedShell_dilation_summand_eq_of_far
    f g hr haf hf hg hsep k

/-- The separated shell is summable under the same strict support
separation. -/
theorem bombieriSeparatedFarPrimeShell_summable
    (f g : BombieriTest) {af bf ag bg r : ℝ}
    (hr : 0 < r) (haf : 0 < af)
    (hf : tsupport f ⊆ Set.Icc af bf)
    (hg : tsupport g ⊆ Set.Icc ag bg)
    (hsep : bg / af < r) :
    Summable (fun k : ℕ ↦
      (ArithmeticFunction.vonMangoldt (k + 1) : ℂ) *
        ((((Real.sqrt r)⁻¹ : ℝ) : ℂ) *
          starRingEnd ℂ
            (bombieriDirectedCorrelation f g
              (r⁻¹ * (k + 1 : ℕ))))) := by
  have hshell := bombieriPrimeDirectedShell_summable
    f (normalizedDilation r hr g)
  exact hshell.congr fun k ↦
    primeDirectedShell_dilation_summand_eq_of_far
      f g hr haf hf hg hsep k

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
