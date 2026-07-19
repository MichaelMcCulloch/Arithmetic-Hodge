import ArithmeticHodge.Analysis.MultiplicativeWeilFixedLogLatticeFarChebyshevStructural

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped Interval

namespace ArithmeticHodge.Analysis.MultiplicativeWeilCorrectedChebyshevPotentialStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilDirectedCorrelationPhysicalStructural
open MultiplicativeWeilDirectedCorrelationSmoothStructural
open MultiplicativeWeilMangoldtDiscrepancyAbelStructural
open MultiplicativeWeilFixedLogLatticeFarChebyshevStructural

/-!
# The corrected Chebyshev potential for separated Bombieri crosses

The nonsingular archimedean kernel in the separated physical cross is an
exact derivative.  Integration by parts therefore combines it with the
Chebyshev discrepancy through the potential

`Phi(t) = (1 / 2) * log (1 - t⁻²)`.

This is an exact structural identity, not a sign estimate.  In particular,
the two resulting pairings must remain coupled in any positivity argument.
-/

local instance : Module ℝ ℂ :=
  Module.complexToReal ℂ

/-- The archimedean potential whose derivative is the separated Cauchy
kernel. -/
def correctedChebyshevPotential (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (1 - t⁻¹ ^ 2)

/-- Derivative of the corrected Chebyshev potential to the right of its
pole. -/
theorem hasDerivAt_correctedChebyshevPotential
    {t : ℝ} (ht : 1 < t) :
    HasDerivAt correctedChebyshevPotential
      (1 / (t * (t ^ 2 - 1))) t := by
  have ht0 : t ≠ 0 := ne_of_gt (zero_lt_one.trans ht)
  have harg : 1 - t⁻¹ ^ 2 ≠ 0 := by
    have hinv : t⁻¹ < 1 := (inv_lt_one₀ (zero_lt_one.trans ht)).2 ht
    have hinv0 : 0 ≤ t⁻¹ := (inv_pos.mpr (zero_lt_one.trans ht)).le
    nlinarith [mul_self_lt_mul_self hinv0 hinv]
  unfold correctedChebyshevPotential
  convert (((hasDerivAt_const t (1 : ℝ)).sub
      (((hasDerivAt_id t).inv ht0).pow 2)).log harg).const_mul
        (1 / 2 : ℝ) using 1
  simp
  field_simp [ht0, harg]

/-- After dilation, the potential derivative is exactly the physical
archimedean kernel. -/
theorem hasDerivAt_correctedChebyshevPotential_mul
    {r x : ℝ} (hrx : 1 < r * x) :
    HasDerivAt
      (fun y : ℝ ↦ ((correctedChebyshevPotential (r * y) : ℝ) : ℂ))
      (((x * ((r * x) ^ 2 - 1))⁻¹ : ℝ) : ℂ) x := by
  have hr0 : r ≠ 0 := by
    intro h
    rw [h, zero_mul] at hrx
    linarith
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, mul_zero] at hrx
    linarith
  have hden : (r * x) ^ 2 - 1 ≠ 0 := by
    nlinarith [sq_nonneg (r * x - 1)]
  have hreal :=
    (hasDerivAt_correctedChebyshevPotential hrx).comp x
      ((hasDerivAt_const x r).mul (hasDerivAt_id x))
  have hcomplex := hreal.ofReal_comp
  convert hcomplex using 1
  norm_cast
  field_simp [hr0, hx0, hden]
  ring

/-- On compact support strictly to the right of the pole, integration by
parts replaces the inverse physical kernel by the negative potential
pairing. -/
theorem integral_inverseKernel_mul_eq_neg_integral_potential_mul_deriv
    (H : ℝ → ℂ) (hH : ContDiff ℝ 1 H)
    {a b r : ℝ} (hr : 0 < r) (hab : a ≤ b)
    (hsupport : tsupport H ⊆ Set.Icc a b) (hsep : 1 < r * a) :
    (∫ x : ℝ in Set.Ioi 0,
        (((x * ((r * x) ^ 2 - 1))⁻¹ : ℝ) : ℂ) * H x) =
      -∫ x : ℝ in Set.Ioi 0,
        ((correctedChebyshevPotential (r * x) : ℝ) : ℂ) * deriv H x := by
  let A : ℝ := (r⁻¹ + a) / 2
  let B : ℝ := b + 1
  have hpole : r⁻¹ < a := by
    rw [inv_lt_iff_one_lt_mul₀ hr]
    simpa only [mul_comm] using hsep
  have hA0 : 0 < A := by
    dsimp only [A]
    have hinv : 0 < r⁻¹ := inv_pos.mpr hr
    linarith
  have hAa : A < a := by
    dsimp only [A]
    linarith
  have haB : a < B := by
    dsimp only [B]
    linarith
  have hbB : b < B := by
    dsimp only [B]
    linarith
  have hAB : A ≤ B := (hAa.trans haB).le
  have hpoleA : r⁻¹ < A := by
    dsimp only [A]
    linarith
  have hAr : 1 < r * A := by
    have := (inv_lt_iff_one_lt_mul₀ hr).mp hpoleA
    simpa only [mul_comm] using this
  have hsupportAB : tsupport H ⊆ Set.Icc A B := by
    intro x hx
    have hx' := hsupport hx
    exact ⟨hAa.le.trans hx'.1, hx'.2.trans (by dsimp only [B]; linarith)⟩
  have hzero (x : ℝ) (hx : x ∉ Set.Icc A B) : H x = 0 := by
    by_contra hne
    exact hx (hsupportAB (subset_tsupport H (Function.mem_support.mpr hne)))
  have hderivZero (x : ℝ) (hx : x ∉ Set.Icc A B) : deriv H x = 0 := by
    apply deriv_of_notMem_tsupport
    intro hxmem
    exact hx (hsupportAB hxmem)
  have hleft :
      (∫ x : ℝ in Set.Ioi 0,
          (((x * ((r * x) ^ 2 - 1))⁻¹ : ℝ) : ℂ) * H x) =
        ∫ x : ℝ in Set.Icc A B,
          (((x * ((r * x) ^ 2 - 1))⁻¹ : ℝ) : ℂ) * H x := by
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
    · intro x hx
      exact hA0.trans_le hx.1
    · intro x hx
      rw [hzero x hx.2, mul_zero]
  have hright :
      (∫ x : ℝ in Set.Ioi 0,
          ((correctedChebyshevPotential (r * x) : ℝ) : ℂ) * deriv H x) =
        ∫ x : ℝ in Set.Icc A B,
          ((correctedChebyshevPotential (r * x) : ℝ) : ℂ) * deriv H x := by
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
    · intro x hx
      exact hA0.trans_le hx.1
    · intro x hx
      rw [hderivZero x hx.2, mul_zero]
  have hu (x : ℝ) (hx : x ∈ [[A, B]]) :
      HasDerivAt
        (fun y : ℝ ↦ ((correctedChebyshevPotential (r * y) : ℝ) : ℂ))
        (((x * ((r * x) ^ 2 - 1))⁻¹ : ℝ) : ℂ) x := by
    rw [uIcc_of_le hAB] at hx
    apply hasDerivAt_correctedChebyshevPotential_mul
    exact hAr.trans_le (mul_le_mul_of_nonneg_left hx.1 hr.le)
  have hv (x : ℝ) (_hx : x ∈ [[A, B]]) :
      HasDerivAt H (deriv H x) x :=
    (hH.differentiable (by norm_num) x).hasDerivAt
  have hu' : IntervalIntegrable
      (fun x : ℝ ↦ (((x * ((r * x) ^ 2 - 1))⁻¹ : ℝ) : ℂ))
      volume A B := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hAB]
    intro x hx
    have hxpos : 0 < x := hA0.trans_le hx.1
    have hrx : 1 < r * x :=
      hAr.trans_le (mul_le_mul_of_nonneg_left hx.1 hr.le)
    have hden : x * ((r * x) ^ 2 - 1) ≠ 0 := by
      apply mul_ne_zero hxpos.ne'
      nlinarith [sq_nonneg (r * x - 1)]
    have hbase : ContinuousAt
        (fun y : ℝ ↦ y * ((r * y) ^ 2 - 1)) x := by
      fun_prop
    have hinv : ContinuousAt
        (fun y : ℝ ↦ (y * ((r * y) ^ 2 - 1))⁻¹) x :=
      hbase.inv₀ hden
    exact
      (Complex.ofRealCLM.continuous.continuousAt.comp hinv).continuousWithinAt
  have hv' : IntervalIntegrable (deriv H) volume A B :=
    (hH.continuous_deriv (by norm_num)).intervalIntegrable A B
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun x : ℝ ↦ ((correctedChebyshevPotential (r * x) : ℝ) : ℂ))
    (v := H)
    (u' := fun x : ℝ ↦ (((x * ((r * x) ^ 2 - 1))⁻¹ : ℝ) : ℂ))
    (v' := deriv H) hu hv hu' hv'
  have hHA : H A = 0 := by
    by_contra hne
    have hmem := hsupport
      (subset_tsupport H (Function.mem_support.mpr hne))
    exact (not_le_of_gt hAa) hmem.1
  have hHB : H B = 0 := by
    by_contra hne
    have hmem := hsupport
      (subset_tsupport H (Function.mem_support.mpr hne))
    exact (not_le_of_gt hbB) hmem.2
  rw [hHA, hHB] at hparts
  simp only [mul_zero, sub_zero, zero_sub] at hparts
  rw [hleft, hright, integral_Icc_eq_integral_Ioc,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hAB,
    ← intervalIntegral.integral_of_le hAB]
  have hneg := congrArg Neg.neg hparts
  simpa only [neg_neg] using hneg.symm

/-- The complete separated global cross is the Chebyshev-error pairing plus
the corrected archimedean-potential pairing. -/
theorem sqrt_mul_bombieriTwoBlockGlobalCrossSymbol_normalizedDilation_eq_chebyshevError_add_correctedPotential
    (f g : BombieriTest) {af bf ag bg r : ℝ}
    (hr : 0 < r) (haf : 0 < af) (hag : 0 < ag) (hbg : 0 < bg)
    (hf : tsupport f ⊆ Set.Icc af bf)
    (hg : tsupport g ⊆ Set.Icc ag bg)
    (hsep : bg / af < r) :
    ((Real.sqrt r : ℝ) : ℂ) *
        bombieriTwoBlockGlobalCrossSymbol f (normalizedDilation r hr g) =
      (∫ x : ℝ in Set.Ioi 0,
        ((Chebyshev.psi (r * x) - r * x : ℝ) : ℂ) *
          deriv (fun y : ℝ ↦
            starRingEnd ℂ (bombieriDirectedCorrelation f g y)) x) +
      ∫ x : ℝ in Set.Ioi 0,
        ((correctedChebyshevPotential (r * x) : ℝ) : ℂ) *
          deriv (fun y : ℝ ↦
            starRingEnd ℂ (bombieriDirectedCorrelation f g y)) x := by
  let H : ℝ → ℂ := fun x ↦
    starRingEnd ℂ (bombieriDirectedCorrelation f g x)
  have hsupportBase : tsupport H ⊆ Set.Icc (af / bg) (bf / ag) := by
    have hsupp : Function.support H ⊆ Set.Icc (af / bg) (bf / ag) := by
      intro x hx
      by_contra hout
      exact hx
        (star_bombieriDirectedCorrelation_eq_zero_outside_supportQuotient
          f g haf hag hbg hf hg hout)
    exact isClosed_Icc.closure_subset_iff.mpr hsupp
  have hsupport :
      tsupport H ⊆ Set.Icc (af / bg) (max (af / bg) (bf / ag)) := by
    intro x hx
    have hx' := hsupportBase hx
    exact ⟨hx'.1, hx'.2.trans (le_max_right _ _)⟩
  have hsep' : 1 < r * (af / bg) := by
    have hcross : bg < r * af := by
      exact (div_lt_iff₀ haf).mp hsep
    calc
      (1 : ℝ) = bg / bg := by field_simp [hbg.ne']
      _ < (r * af) / bg := (div_lt_div_iff_of_pos_right hbg).2 hcross
      _ = r * (af / bg) := by ring
  have hpotential :=
    integral_inverseKernel_mul_eq_neg_integral_potential_mul_deriv
      H (star_bombieriDirectedCorrelation_contDiff_one f g) hr
      (le_max_left _ _) hsupport hsep'
  have hkernel :
      (∫ x : ℝ in Set.Ioi 0,
          H x / ((x * ((r * x) ^ 2 - 1) : ℝ) : ℂ)) =
        ∫ x : ℝ in Set.Ioi 0,
          (((x * ((r * x) ^ 2 - 1))⁻¹ : ℝ) : ℂ) * H x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _hx
    change H x / ((x * ((r * x) ^ 2 - 1) : ℝ) : ℂ) =
      (((x * ((r * x) ^ 2 - 1))⁻¹ : ℝ) : ℂ) * H x
    simp only [div_eq_mul_inv, Complex.ofReal_inv]
    ring
  rw [
    sqrt_mul_bombieriTwoBlockGlobalCrossSymbol_normalizedDilation_eq_chebyshevError_sub_kernel
      f g hr haf hag hbg hf hg hsep]
  change _ - (∫ x : ℝ in Set.Ioi 0,
      H x / ((x * ((r * x) ^ 2 - 1) : ℝ) : ℂ)) = _
  rw [hkernel, hpotential]
  have hderiv : deriv H = deriv (fun y : ℝ ↦
      starRingEnd ℂ (bombieriDirectedCorrelation f g y)) := by
    rfl
  rw [sub_neg_eq_add, hderiv]
  rfl

/-- Every fixed-lattice far lag has the corrected-potential form, with all
support-separation hypotheses discharged. -/
theorem sqrt_mul_bombieriTwoBlockGlobalCrossSymbol_fixedLogLattice_far_eq_chebyshevError_add_correctedPotential
    (f g : BombieriTest) (k : ℤ) (hk : 3 ≤ k)
    (hf : tsupport f ⊆ Set.Icc 1 2)
    (hg : tsupport g ⊆ Set.Icc 1 2) :
    ((Real.sqrt (fixedLogLatticePoint k) : ℝ) : ℂ) *
        bombieriTwoBlockGlobalCrossSymbol f
          (normalizedDilation (fixedLogLatticePoint k)
            (fixedLogLatticePoint_pos k) g) =
      (∫ x : ℝ in Set.Ioi 0,
        ((Chebyshev.psi (fixedLogLatticePoint k * x) -
            fixedLogLatticePoint k * x : ℝ) : ℂ) *
          deriv (fun y : ℝ ↦
            starRingEnd ℂ (bombieriDirectedCorrelation f g y)) x) +
      ∫ x : ℝ in Set.Ioi 0,
        ((correctedChebyshevPotential
            (fixedLogLatticePoint k * x) : ℝ) : ℂ) *
          deriv (fun y : ℝ ↦
            starRingEnd ℂ (bombieriDirectedCorrelation f g y)) x := by
  apply
    sqrt_mul_bombieriTwoBlockGlobalCrossSymbol_normalizedDilation_eq_chebyshevError_add_correctedPotential
      f g (fixedLogLatticePoint_pos k)
      (by norm_num) (by norm_num) (by norm_num) hf hg
  simpa only [div_one] using two_lt_fixedLogLatticePoint_of_three_le hk

/-- Actual physical fixed-lattice cells inherit the corrected-potential
formula.  The right-hand side depends only on the integer lag and the two
normalized base seeds. -/
theorem sqrt_mul_bombieriTwoBlockGlobalCrossSymbol_fixedLogLatticeRescale_far_eq_chebyshevError_add_correctedPotential
    (n m : ℤ) (f g : BombieriTest) (hfar : 3 ≤ n - m)
    (hf : tsupport f ⊆ Set.Icc 1 2)
    (hg : tsupport g ⊆ Set.Icc 1 2) :
    ((Real.sqrt (fixedLogLatticePoint (n - m)) : ℝ) : ℂ) *
        bombieriTwoBlockGlobalCrossSymbol
          (fixedLogLatticeRescale n f)
          (fixedLogLatticeRescale m g) =
      (∫ x : ℝ in Set.Ioi 0,
        ((Chebyshev.psi (fixedLogLatticePoint (n - m) * x) -
            fixedLogLatticePoint (n - m) * x : ℝ) : ℂ) *
          deriv (fun y : ℝ ↦
            starRingEnd ℂ (bombieriDirectedCorrelation f g y)) x) +
      ∫ x : ℝ in Set.Ioi 0,
        ((correctedChebyshevPotential
            (fixedLogLatticePoint (n - m) * x) : ℝ) : ℂ) *
          deriv (fun y : ℝ ↦
            starRingEnd ℂ (bombieriDirectedCorrelation f g y)) x := by
  rw [bombieriTwoBlockGlobalCrossSymbol_fixedLogLatticeRescale]
  exact
    sqrt_mul_bombieriTwoBlockGlobalCrossSymbol_fixedLogLattice_far_eq_chebyshevError_add_correctedPotential
      f g (n - m) hfar hf hg

end

end ArithmeticHodge.Analysis.MultiplicativeWeilCorrectedChebyshevPotentialStructural
