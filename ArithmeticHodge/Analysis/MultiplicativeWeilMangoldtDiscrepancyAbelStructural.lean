import ArithmeticHodge.Analysis.MultiplicativeWeilDirectedCorrelationSmoothStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilFarPhysicalKernelStructural
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev

set_option autoImplicit false

open Complex Finset MeasureTheory Real Set TopologicalSpace
open scoped ArithmeticFunction ContDiff Interval

namespace ArithmeticHodge.Analysis.MultiplicativeWeilMangoldtDiscrepancyAbelStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilDirectedCorrelationSmoothStructural
open MultiplicativeWeilFarPhysicalKernelStructural

/-!
# Abel form of the smoothed Mangoldt discrepancy

A compactly supported `C¹` weight turns the Mangoldt sum into the exact
pairing of its derivative with `Chebyshev.psi - id`.  This is a finite Abel
summation argument: compact support supplies a finite endpoint beyond every
nonzero summand, and no asymptotic prime-number theorem is used.
-/

private theorem vonMangoldtWeighted_hasFiniteSupport
    (H : ℝ → ℂ) (hcompact : HasCompactSupport H) :
    Function.HasFiniteSupport
      (fun n : ℕ ↦ ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * H n) := by
  refine (show {n : ℕ | H n ≠ 0}.Finite by
    rw [Set.finite_iff_bddAbove]
    obtain ⟨B, hB⟩ := hcompact.bddAbove
    obtain ⟨N : ℕ, hN⟩ := exists_nat_gt B
    refine ⟨N, ?_⟩
    intro n hn
    have hnmem : (n : ℝ) ∈ tsupport H :=
      subset_tsupport H (Function.mem_support.mpr hn)
    exact_mod_cast (hB hnmem).trans hN.le).subset ?_
  intro n hn
  exact right_ne_zero_of_mul hn

/-- Exact Abel summation for an arbitrary compactly supported complex `C¹`
weight on the positive half-line. -/
theorem integral_sub_tsum_vonMangoldt_eq_integral_chebyshevError
    (H : ℝ → ℂ) (hH : ContDiff ℝ 1 H)
    (hcompact : HasCompactSupport H) :
    (∫ x : ℝ in Set.Ioi 0, H x) -
        ∑' n : ℕ,
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * H n =
      ∫ x : ℝ in Set.Ioi 0,
        ((Chebyshev.psi x - x : ℝ) : ℂ) * deriv H x := by
  let c : ℕ → ℂ := fun n ↦
    ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
  obtain ⟨B, hB⟩ := hcompact.bddAbove
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (max B 2)
  have hBN : B < (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hN
  have h2N : (2 : ℝ) < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hzero (x : ℝ) (hx : (N : ℝ) ≤ x) : H x = 0 := by
    by_contra hx0
    have hxmem : x ∈ tsupport H :=
      subset_tsupport H (Function.mem_support.mpr hx0)
    exact (not_lt_of_ge (hB hxmem)) (hBN.trans_le hx)
  have hderivZero (x : ℝ) (hx : (N : ℝ) ≤ x) : deriv H x = 0 := by
    apply deriv_of_notMem_tsupport
    intro hxmem
    exact (not_lt_of_ge (hB hxmem)) (hBN.trans_le hx)
  have hHN : H N = 0 := hzero N le_rfl
  have hpsi (x : ℝ) :
      (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, c k) =
        ((Chebyshev.psi x : ℝ) : ℂ) := by
    dsimp only [c]
    rw [Chebyshev.psi_eq_sum_Icc]
    push_cast
    rfl
  have hAbel := sum_mul_eq_sub_integral_mul₀ c (by simp [c]) (N : ℝ)
    (fun x _hx ↦ hH.differentiable (by norm_num) x)
    ((hH.continuous_deriv (by norm_num)).integrableOn_Icc)
  simp_rw [hpsi] at hAbel
  simp only [Nat.floor_natCast] at hAbel
  rw [hHN, zero_mul, zero_sub] at hAbel
  have hprime :
      (∑' n : ℕ,
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * H n) =
        ∑ n ∈ Finset.Icc 0 N, H n * c n := by
    rw [tsum_eq_sum (s := Finset.Icc 0 N) (by
      intro n hn
      have hnN : N < n := by
        apply lt_of_not_ge
        intro hle
        exact hn (Finset.mem_Icc.mpr ⟨Nat.zero_le n, hle⟩)
      rw [hzero n (by exact_mod_cast hnN.le), mul_zero])]
    apply Finset.sum_congr rfl
    intro n hn
    dsimp only [c]
    ring
  have hAbelIntegral :
      (∫ x : ℝ in Set.Ioc 1 (N : ℝ),
          deriv H x * ((Chebyshev.psi x : ℝ) : ℂ)) =
        ∫ x : ℝ in Set.Ioc 0 (N : ℝ),
          deriv H x * ((Chebyshev.psi x : ℝ) : ℂ) := by
    symm
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioc
    · intro x hx
      exact ⟨zero_lt_one.trans hx.1, hx.2⟩
    · intro x hx
      have hxle : x ≤ 1 := by
        by_contra hxgt
        exact hx.2 ⟨lt_of_not_ge hxgt, hx.1.2⟩
      rw [Chebyshev.psi_eq_zero_of_lt_two (hxle.trans_lt (by norm_num)),
        Complex.ofReal_zero, mul_zero]
  have hAbel' :
      (∑ n ∈ Finset.Icc 0 N, H n * c n) =
        -∫ x : ℝ in Set.Ioc 0 (N : ℝ),
          deriv H x * ((Chebyshev.psi x : ℝ) : ℂ) :=
    hAbel.trans (congrArg Neg.neg hAbelIntegral)
  have hmainIntegral :
      (∫ x : ℝ in Set.Ioi 0, H x) =
        ∫ x : ℝ in Set.Ioc 0 (N : ℝ), H x := by
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
    · exact Set.Ioc_subset_Ioi_self
    · intro x hx
      have hxN : (N : ℝ) < x := by
        by_contra hxle
        exact hx.2 ⟨hx.1, le_of_not_gt hxle⟩
      exact hzero x hxN.le
  have herrorIntegral :
      (∫ x : ℝ in Set.Ioi 0,
          ((Chebyshev.psi x - x : ℝ) : ℂ) * deriv H x) =
        ∫ x : ℝ in Set.Ioc 0 (N : ℝ),
          ((Chebyshev.psi x - x : ℝ) : ℂ) * deriv H x := by
    apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
    · exact Set.Ioc_subset_Ioi_self
    · intro x hx
      have hxN : (N : ℝ) < x := by
        by_contra hxle
        exact hx.2 ⟨hx.1, le_of_not_gt hxle⟩
      rw [hderivZero x hxN.le, mul_zero]
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun x : ℝ ↦ (x : ℂ)) (v := H)
    (u' := fun _x : ℝ ↦ (1 : ℂ)) (v' := deriv H)
    (fun x _hx ↦ by simpa using (hasDerivAt_id x).ofReal_comp)
    (fun x _hx ↦ (hH.differentiable (by norm_num) x).hasDerivAt)
    (continuous_const.intervalIntegrable 0 N)
    ((hH.continuous_deriv (by norm_num)).intervalIntegrable 0 N)
  rw [intervalIntegral.integral_of_le hN0,
    intervalIntegral.integral_of_le hN0] at hparts
  simp only [hHN, Complex.ofReal_zero, Complex.ofReal_natCast,
    zero_mul, one_mul, sub_zero] at hparts
  have hpsiInt : IntegrableOn
      (fun x : ℝ ↦ ((Chebyshev.psi x : ℝ) : ℂ) * deriv H x)
      (Set.Ioc 0 (N : ℝ)) := by
    have hsumInt := integrableOn_mul_sum_Icc
      (m := 0) (a := 0) (b := (N : ℝ)) c (by norm_num)
      ((hH.continuous_deriv (by norm_num)).integrableOn_Icc)
    have hsumInt' : IntegrableOn
        (fun x : ℝ ↦
          deriv H x * ((Chebyshev.psi x : ℝ) : ℂ))
        (Set.Icc 0 (N : ℝ)) := by
      apply hsumInt.congr_fun
      · intro x hx
        change deriv H x *
            (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, c k) =
          deriv H x * ((Chebyshev.psi x : ℝ) : ℂ)
        rw [hpsi]
      · exact measurableSet_Icc
    exact (hsumInt'.mono_set Set.Ioc_subset_Icc_self).congr_fun
      (fun x hx ↦ by ring) measurableSet_Ioc
  have hxInt : IntegrableOn
      (fun x : ℝ ↦ (x : ℂ) * deriv H x) (Set.Ioc 0 (N : ℝ)) := by
    exact ((Complex.ofRealCLM.continuous.mul
      (hH.continuous_deriv (by norm_num))).integrableOn_Icc).mono_set
        Set.Ioc_subset_Icc_self
  rw [hmainIntegral, hprime, herrorIntegral]
  rw [show (∫ x : ℝ in Set.Ioc 0 (N : ℝ),
      ((Chebyshev.psi x - x : ℝ) : ℂ) * deriv H x) =
      (∫ x : ℝ in Set.Ioc 0 (N : ℝ),
        ((Chebyshev.psi x : ℝ) : ℂ) * deriv H x) -
      ∫ x : ℝ in Set.Ioc 0 (N : ℝ), (x : ℂ) * deriv H x by
    rw [← integral_sub hpsiInt hxInt]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    push_cast
    ring]
  rw [show (∑ n ∈ Finset.Icc 0 N, H n * c n) =
      -∫ x : ℝ in Set.Ioc 0 (N : ℝ),
        ((Chebyshev.psi x : ℝ) : ℂ) * deriv H x by
    rw [hAbel']
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    ring]
  ring_nf at hparts
  have hparts' :
      (∫ x : ℝ in Set.Ioc 0 (N : ℝ), (x : ℂ) * deriv H x) =
        -∫ x : ℝ in Set.Ioc 0 (N : ℝ), H x := by
    simpa only using hparts
  rw [hparts']
  ring

private theorem integral_chebyshevError_deriv_comp_inv_mul
    (H : ℝ → ℂ) {r : ℝ} (hr : 0 < r) :
    (∫ t : ℝ in Set.Ioi 0,
        ((Chebyshev.psi t - t : ℝ) : ℂ) *
          deriv (fun y : ℝ ↦ H (r⁻¹ * y)) t) =
      ∫ x : ℝ in Set.Ioi 0,
        ((Chebyshev.psi (r * x) - r * x : ℝ) : ℂ) * deriv H x := by
  let F : ℝ → ℂ := fun t ↦
    ((Chebyshev.psi t - t : ℝ) : ℂ) *
      deriv (fun y : ℝ ↦ H (r⁻¹ * y)) t
  let G : ℝ → ℂ := fun x ↦
    ((Chebyshev.psi (r * x) - r * x : ℝ) : ℂ) * deriv H x
  have hpoint (x : ℝ) :
      F (r * x) = ((r⁻¹ : ℝ) : ℂ) * G x := by
    dsimp only [F, G]
    have hd :
        deriv (fun y : ℝ ↦ H (r⁻¹ * y)) (r * x) =
          r⁻¹ • deriv H (r⁻¹ * (r * x)) := by
      simpa only using deriv_comp_mul_left r⁻¹ H (r * x)
    rw [hd]
    have harg : r⁻¹ * (r * x) = x := by
      field_simp [hr.ne']
    rw [harg]
    simp only [Complex.real_smul]
    ring
  have hchange := integral_comp_mul_left_Ioi F 0 hr
  have hscaled :
      ((r⁻¹ : ℝ) : ℂ) *
          (∫ x : ℝ in Set.Ioi 0, G x) =
        ((r⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ in Set.Ioi 0, F t := by
    calc
      ((r⁻¹ : ℝ) : ℂ) *
          (∫ x : ℝ in Set.Ioi 0, G x) =
          ∫ x : ℝ in Set.Ioi 0,
            ((r⁻¹ : ℝ) : ℂ) * G x := by
              exact (integral_const_mul
                (μ := volume.restrict (Set.Ioi 0)) _ _).symm
      _ = ∫ x : ℝ in Set.Ioi 0, F (r * x) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        exact (hpoint x).symm
      _ = ((r⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ in Set.Ioi 0, F t := by
        simpa only [mul_zero, Complex.real_smul] using hchange
  have hcancel : ((r⁻¹ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (inv_ne_zero hr.ne')
  have hresult := mul_left_cancel₀ hcancel hscaled
  simpa only [F, G] using hresult.symm

/-- Dilation-covariant Abel form, reindexed exactly as the separated prime
shell. -/
theorem scaled_integral_sub_tsum_vonMangoldt_eq_integral_chebyshevError
    (H : ℝ → ℂ) (hH : ContDiff ℝ 1 H)
    (hcompact : HasCompactSupport H) {r : ℝ} (hr : 0 < r) :
    (r : ℂ) * (∫ x : ℝ in Set.Ioi 0, H x) -
        ∑' n : ℕ,
          ((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) : ℂ) *
            H (r⁻¹ * (n + 1 : ℕ)) =
      ∫ x : ℝ in Set.Ioi 0,
        ((Chebyshev.psi (r * x) - r * x : ℝ) : ℂ) * deriv H x := by
  let P : ℝ → ℂ := fun t ↦ H (r⁻¹ * t)
  have hP : ContDiff ℝ 1 P := by
    dsimp only [P]
    exact hH.comp (by fun_prop)
  have hPcompact : HasCompactSupport P := by
    simpa only [P, smul_eq_mul] using
      hcompact.comp_smul (inv_ne_zero hr.ne')
  have hbase :=
    integral_sub_tsum_vonMangoldt_eq_integral_chebyshevError
      P hP hPcompact
  have hmain :
      (∫ t : ℝ in Set.Ioi 0, P t) =
        (r : ℂ) * ∫ x : ℝ in Set.Ioi 0, H x := by
    have hscale := integral_comp_mul_left_Ioi H 0 (inv_pos.mpr hr)
    simpa only [P, mul_zero, inv_inv, Complex.real_smul] using hscale
  let F : ℕ → ℂ := fun n ↦
    ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * P n
  have hFsummable : Summable F := by
    exact summable_of_hasFiniteSupport
      (vonMangoldtWeighted_hasFiniteSupport P hPcompact)
  have hFzero : F 0 = 0 := by simp [F]
  have hsplit := hFsummable.sum_add_tsum_nat_add 1
  have hprime :
      (∑' n : ℕ,
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * P n) =
        ∑' n : ℕ,
          ((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) : ℂ) *
            H (r⁻¹ * (n + 1 : ℕ)) := by
    have hshift : (∑' n : ℕ, F n) = ∑' n : ℕ, F (n + 1) := by
      simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        hFzero] using hsplit.symm
    simpa only [F, P, Nat.cast_add, Nat.cast_one] using hshift
  have herror := integral_chebyshevError_deriv_comp_inv_mul H hr
  rw [hmain, hprime, herror] at hbase
  exact hbase

/-- Final separated physical identity: the global zero-side cross is an exact
Chebyshev-error pairing minus the nonsingular archimedean kernel. -/
theorem sqrt_mul_bombieriTwoBlockGlobalCrossSymbol_normalizedDilation_eq_chebyshevError_sub_kernel
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
            starRingEnd ℂ (bombieriDirectedCorrelation f g y)) x) -
      ∫ x : ℝ in Set.Ioi 0,
        starRingEnd ℂ (bombieriDirectedCorrelation f g x) /
          ((x * ((r * x) ^ 2 - 1) : ℝ) : ℂ) := by
  rw [
    sqrt_mul_bombieriTwoBlockGlobalCrossSymbol_normalizedDilation_eq_physicalDiscrepancy_sub_kernel
      f g hr haf hag hbg hf hg hsep,
    scaled_integral_sub_tsum_vonMangoldt_eq_integral_chebyshevError
      (fun x : ℝ ↦
        starRingEnd ℂ (bombieriDirectedCorrelation f g x))
      (star_bombieriDirectedCorrelation_contDiff_one f g)
      (star_bombieriDirectedCorrelation_hasCompactSupport f g) hr]

end

end ArithmeticHodge.Analysis.MultiplicativeWeilMangoldtDiscrepancyAbelStructural
