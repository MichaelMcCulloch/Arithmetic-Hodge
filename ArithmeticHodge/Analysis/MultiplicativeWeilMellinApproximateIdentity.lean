import ArithmeticHodge.Analysis.MultiplicativeWeilApproximateIdentity

/-!
# Mellin control for smooth multiplicative bumps

A nonnegative unit-mass bump supported in a logarithmic `epsilon`-ball around
one has Mellin transform within `2 * ‖s - 1‖ * epsilon` of one.  This is the
quantitative approximate-identity estimate needed to smooth Li cutoffs while
preserving their spectral values.
-/

set_option autoImplicit false

open Complex MeasureTheory Real Set Topology
open scoped ContDiff Distributions

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- A nonnegative unit-mass Bombieri bump supported logarithmically within
`epsilon` of one has Mellin transform uniformly close to one. -/
theorem norm_mellin_sub_one_le_of_unit_mass_log_support
    (eta : BombieriTest) (epsilon : ℝ) (_hepsilon : 0 < epsilon)
    (hsupport : tsupport (eta : ℝ → ℂ) ⊆
      Ioo (Real.exp (-epsilon)) (Real.exp epsilon))
    (hreal : ∀ x, 0 ≤ (eta x).re ∧ (eta x).im = 0)
    (hmass : (∫ x : ℝ, (eta x).re) = 1)
    (s : ℂ) (hsmall : ‖s - 1‖ * epsilon ≤ 1) :
    ‖mellin (eta : ℝ → ℂ) s - 1‖ ≤ 2 * ‖s - 1‖ * epsilon := by
  let C : ℝ := 2 * ‖s - 1‖ * epsilon
  have hzero_out (x : ℝ)
      (hx : x ∉ Ioo (Real.exp (-epsilon)) (Real.exp epsilon)) :
      eta x = 0 := by
    by_contra hne
    exact hx (hsupport (subset_tsupport eta (Function.mem_support.mpr hne)))
  have hetaInt : Integrable (eta : ℝ → ℂ) :=
    eta.contDiff.continuous.integrable_of_hasCompactSupport eta.hasCompactSupport
  have hetaIntegral : (∫ x : ℝ, eta x) = 1 := by
    apply Complex.ext
    · norm_num
      calc
        (∫ x : ℝ, eta x).re = ∫ x : ℝ, (eta x).re := by
          symm
          simpa only [RCLike.re_to_complex] using integral_re hetaInt
        _ = 1 := hmass
    · norm_num
      calc
        (∫ x : ℝ, eta x).im = ∫ x : ℝ, (eta x).im := by
          symm
          simpa only [RCLike.im_to_complex] using integral_im hetaInt
        _ = 0 := by simp only [(hreal _).2, integral_zero]
  have hetaSetIntegral : (∫ x : ℝ in Ioi 0, eta x) = 1 := by
    rw [← hetaIntegral, ← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      symm
      apply hzero_out
      intro hxi
      exact hx ((Real.exp_pos (-epsilon)).trans hxi.1)
  have hpowInt : IntegrableOn
      (fun x : ℝ ↦ (x : ℂ) ^ (s - 1) * eta x) (Ioi 0) := by
    simpa only [MellinConvergent, smul_eq_mul] using eta.mellinConvergent s
  have hetaSetInt : IntegrableOn (eta : ℝ → ℂ) (Ioi 0) := hetaInt.integrableOn
  have hdiff : mellin (eta : ℝ → ℂ) s - 1 =
      ∫ x : ℝ in Ioi 0, ((x : ℂ) ^ (s - 1) - 1) * eta x := by
    calc
      mellin (eta : ℝ → ℂ) s - 1 =
          mellin (eta : ℝ → ℂ) s - ∫ x : ℝ in Ioi 0, eta x := by
        rw [hetaSetIntegral]
      _ = (∫ x : ℝ in Ioi 0,
          (x : ℂ) ^ (s - 1) * eta x) -
            ∫ x : ℝ in Ioi 0, eta x := by
        rfl
      _ = ∫ x : ℝ in Ioi 0,
          ((x : ℂ) ^ (s - 1) * eta x - eta x) := by
        rw [integral_sub hpowInt hetaSetInt]
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
  have hpoint (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
      ‖((x : ℂ) ^ (s - 1) - 1) * eta x‖ ≤ C * (eta x).re := by
    by_cases hxe : eta x = 0
    · simp [hxe, C]
    have hxt : x ∈ Ioo (Real.exp (-epsilon)) (Real.exp epsilon) :=
      hsupport (subset_tsupport eta (Function.mem_support.mpr hxe))
    have hlog : |Real.log x| < epsilon := by
      rw [abs_lt]
      exact ⟨(Real.lt_log_iff_exp_lt hx).mpr hxt.1,
        (Real.log_lt_iff_lt_exp hx).mpr hxt.2⟩
    have hclog : Complex.log (x : ℂ) = (Real.log x : ℂ) := by
      apply Complex.ext
      · rw [Complex.log_re, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hx]
        simp
      · rw [Complex.log_im, Complex.arg_ofReal_of_nonneg hx.le]
        simp
    have hzsmall : ‖Complex.log (x : ℂ) * (s - 1)‖ ≤ 1 := by
      rw [hclog, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc
        |Real.log x| * ‖s - 1‖ ≤ epsilon * ‖s - 1‖ :=
          mul_le_mul_of_nonneg_right hlog.le (norm_nonneg _)
        _ = ‖s - 1‖ * epsilon := mul_comm _ _
        _ ≤ 1 := hsmall
    have hcpow : (x : ℂ) ^ (s - 1) =
        Complex.exp (Complex.log (x : ℂ) * (s - 1)) := by
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
    have hexp := Complex.norm_exp_sub_one_le hzsmall
    rw [← hcpow] at hexp
    have hfactor : ‖(x : ℂ) ^ (s - 1) - 1‖ ≤ C := by
      calc
        ‖(x : ℂ) ^ (s - 1) - 1‖ ≤
            2 * ‖Complex.log (x : ℂ) * (s - 1)‖ := hexp
        _ = 2 * |Real.log x| * ‖s - 1‖ := by
          rw [hclog, norm_mul, Complex.norm_real, Real.norm_eq_abs]
          ring
        _ ≤ C := by
          dsimp only [C]
          nlinarith [hlog, norm_nonneg (s - 1)]
    have hetaNorm : ‖eta x‖ = (eta x).re := by
      have hetaEq : eta x = ((eta x).re : ℂ) := by
        apply Complex.ext <;> simp [(hreal x).2]
      rw [hetaEq, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hreal x).1]
      simp
    rw [norm_mul, hetaNorm]
    exact mul_le_mul_of_nonneg_right hfactor (hreal x).1
  rw [hdiff]
  calc
    ‖∫ x : ℝ in Ioi 0, ((x : ℂ) ^ (s - 1) - 1) * eta x‖ ≤
        ∫ x : ℝ in Ioi 0, ‖((x : ℂ) ^ (s - 1) - 1) * eta x‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ in Ioi 0, C * (eta x).re := by
      apply integral_mono_ae
      · have hdiffInt : IntegrableOn
            (fun x : ℝ ↦ ((x : ℂ) ^ (s - 1) - 1) * eta x)
            (Ioi 0) := by
          apply (hpowInt.sub hetaSetInt).congr
          filter_upwards [] with x
          simp only [Pi.sub_apply]
          ring
        exact hdiffInt.norm
      · exact (hetaInt.re.const_mul C).integrableOn
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact hpoint x hx
    _ = C * ∫ x : ℝ in Ioi 0, (eta x).re := by
      exact integral_const_mul C _
    _ = C := by
      have hreSet : (∫ x : ℝ in Ioi 0, (eta x).re) = 1 := by
        have hre := integral_re hetaSetInt
        change (∫ x : ℝ in Ioi 0, (eta x).re) =
          (∫ x : ℝ in Ioi 0, eta x).re at hre
        rw [hre, hetaSetIntegral]
        rfl
      rw [hreSet, mul_one]
    _ = 2 * ‖s - 1‖ * epsilon := rfl

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
