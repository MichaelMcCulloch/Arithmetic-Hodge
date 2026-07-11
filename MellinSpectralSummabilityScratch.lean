import ArithmeticHodge.Analysis.MultiplicativeWeilZeros
import ArithmeticHodge.Analysis.EntireFunction.ZeroSummability
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false

open Complex Filter Topology Real Set MeasureTheory
open scoped ContDiff Distributions SchwartzMap FourierTransform

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- The project logarithmic pullback is exactly the Fourier-side function in
Mathlib's Mellin--Fourier identity. -/
theorem mellin_eq_fourier_logarithmicPullbackSchwartz
    (f : BombieriTest) (s : ℂ) :
    mellin (f : ℝ → ℂ) s =
      𝓕 (f.logarithmicPullbackSchwartz s.re) (s.im / (2 * Real.pi)) := by
  rw [mellin_eq_fourier]
  congr 1

private theorem logarithmicPullback_eq_weight_smul_core
    (f : BombieriTest) (sigma : ℝ) :
    BombieriTest.logarithmicPullback sigma f = fun u ↦
      Real.exp ((-sigma) * u) • BombieriTest.logarithmicPullback 0 f u := by
  funext u
  simp only [BombieriTest.logarithmicPullback, zero_mul, neg_zero,
    Real.exp_zero, Complex.real_smul]
  push_cast
  ring

private theorem logarithmicPullback_tsupport_eq_core
    (f : BombieriTest) (sigma : ℝ) :
    tsupport (BombieriTest.logarithmicPullback sigma f) =
      tsupport (BombieriTest.logarithmicPullback 0 f) := by
  rw [tsupport, tsupport]
  congr 1
  ext u
  simp only [Function.mem_support, BombieriTest.logarithmicPullback,
    zero_mul, neg_zero, Real.exp_zero]
  have hw : (Real.exp (-sigma * u) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  constructor
  · intro h hfu
    have hfzero : f (Real.exp (-u)) = 0 := by simpa using hfu
    apply h
    rw [hfzero, mul_zero]
  · intro h hprod
    apply h
    simpa using (mul_eq_zero.mp hprod).resolve_left hw

private theorem norm_iteratedDeriv_exp_weight_le
    {sigma u R : ℝ} (hsigma0 : 0 ≤ sigma) (hsigma1 : sigma ≤ 1)
    (hR0 : 0 ≤ R) (hu : u ∈ Metric.closedBall (0 : ℝ) R) (i : ℕ) :
    ‖iteratedDeriv i (fun v : ℝ ↦ Real.exp ((-sigma) * v)) u‖ ≤
      Real.exp R := by
  have hformula := congrFun (iteratedDeriv_exp_const_mul i (-sigma)) u
  rw [hformula, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg,
    abs_of_pos (Real.exp_pos _)]
  have hsigma_abs : |sigma| ≤ 1 := by
    rw [abs_of_nonneg hsigma0]
    exact hsigma1
  have hpow : |sigma| ^ i ≤ 1 := pow_le_one₀ (abs_nonneg sigma) hsigma_abs
  have huabs : |u| ≤ R := by
    simpa [Real.dist_eq] using (Metric.mem_closedBall.mp hu)
  have hexponent : (-sigma) * u ≤ R := by
    calc
      (-sigma) * u ≤ |(-sigma) * u| := le_abs_self _
      _ = |sigma| * |u| := by rw [abs_mul, abs_neg]
      _ ≤ 1 * R := mul_le_mul hsigma_abs huabs (abs_nonneg u) zero_le_one
      _ = R := one_mul R
  exact (mul_le_mul hpow (Real.exp_le_exp.mpr hexponent)
    (Real.exp_pos _).le (by positivity)).trans_eq (one_mul _)

private theorem norm_iteratedDeriv_two_logarithmicPullback_le
    (f : BombieriTest) {sigma R u : ℝ}
    (hsigma0 : 0 ≤ sigma) (hsigma1 : sigma ≤ 1)
    (hR0 : 0 ≤ R) (hu : u ∈ Metric.closedBall (0 : ℝ) R) :
    ‖iteratedDeriv 2 (BombieriTest.logarithmicPullback sigma f) u‖ ≤
      ∑ i ∈ Finset.range 3,
        (Nat.choose 2 i : ℝ) * Real.exp R *
          SchwartzMap.seminorm ℂ 0 (2 - i)
            (f.logarithmicPullbackSchwartz 0) := by
  let weight : ℝ → ℝ := fun v ↦ Real.exp ((-sigma) * v)
  let core : ℝ → ℂ := BombieriTest.logarithmicPullback 0 f
  have hw : ContDiffWithinAt ℝ (2 : ℕ) weight Set.univ u := by
    dsimp only [weight]
    fun_prop
  have hc : ContDiffWithinAt ℝ (2 : ℕ) core Set.univ u := by
    exact (f.logarithmicPullback_contDiff 0).of_le
      (WithTop.coe_mono (show (2 : ℕ∞) ≤ ⊤ from le_top))
      |>.contDiffAt.contDiffWithinAt
  have hproduct : iteratedDeriv 2
      (fun v ↦ weight v • core v) u =
      ∑ i ∈ Finset.range 3,
        Nat.choose 2 i • iteratedDeriv i weight u •
          iteratedDeriv (2 - i) core u := by
    simpa only [iteratedDerivWithin_univ] using
      (iteratedDerivWithin_smul (n := 2) (x := u) (s := Set.univ)
        (Set.mem_univ u) uniqueDiffOn_univ hw hc)
  rw [logarithmicPullback_eq_weight_smul_core f sigma]
  change ‖iteratedDeriv 2 (fun v ↦ weight v • core v) u‖ ≤ _
  rw [hproduct]
  calc
    ‖∑ i ∈ Finset.range 3,
        Nat.choose 2 i • iteratedDeriv i weight u •
          iteratedDeriv (2 - i) core u‖ ≤
        ∑ i ∈ Finset.range 3,
          ‖Nat.choose 2 i • iteratedDeriv i weight u •
            iteratedDeriv (2 - i) core u‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range 3,
        (Nat.choose 2 i : ℝ) * Real.exp R *
          SchwartzMap.seminorm ℂ 0 (2 - i)
            (f.logarithmicPullbackSchwartz 0) := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        ‖Nat.choose 2 i • (iteratedDeriv i weight u •
            iteratedDeriv (2 - i) core u)‖ ≤
            (Nat.choose 2 i : ℝ) *
              ‖iteratedDeriv i weight u •
                iteratedDeriv (2 - i) core u‖ := norm_nsmul_le
        _ = (Nat.choose 2 i : ℝ) * ‖iteratedDeriv i weight u‖ *
              ‖iteratedDeriv (2 - i) core u‖ := by
          rw [Complex.real_smul, norm_mul, Complex.norm_real]
          ring
        _ ≤ (Nat.choose 2 i : ℝ) * Real.exp R *
              SchwartzMap.seminorm ℂ 0 (2 - i)
                (f.logarithmicPullbackSchwartz 0) := by
          have hweight := norm_iteratedDeriv_exp_weight_le
            hsigma0 hsigma1 hR0 hu i
          have hcore := SchwartzMap.le_seminorm' ℂ 0 (2 - i)
            (f.logarithmicPullbackSchwartz 0) u
          simp only [pow_zero, one_mul] at hcore
          change ‖iteratedDeriv (2 - i) core u‖ ≤
            SchwartzMap.seminorm ℂ 0 (2 - i)
              (f.logarithmicPullbackSchwartz 0) at hcore
          gcongr

private theorem norm_logarithmicPullback_le
    (f : BombieriTest) {sigma R u : ℝ}
    (hsigma0 : 0 ≤ sigma) (hsigma1 : sigma ≤ 1)
    (hR0 : 0 ≤ R) (hu : u ∈ Metric.closedBall (0 : ℝ) R) :
    ‖BombieriTest.logarithmicPullback sigma f u‖ ≤
      Real.exp R * SchwartzMap.seminorm ℂ 0 0
        (f.logarithmicPullbackSchwartz 0) := by
  rw [logarithmicPullback_eq_weight_smul_core f sigma]
  change ‖Real.exp ((-sigma) * u) •
      BombieriTest.logarithmicPullback 0 f u‖ ≤ _
  rw [Complex.real_smul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hweight := norm_iteratedDeriv_exp_weight_le
    hsigma0 hsigma1 hR0 hu 0
  simp only [iteratedDeriv_zero, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), pow_zero, one_mul] at hweight
  have hcore := SchwartzMap.le_seminorm' ℂ 0 0
    (f.logarithmicPullbackSchwartz 0) u
  simp only [pow_zero, one_mul, iteratedDeriv_zero] at hcore
  exact mul_le_mul hweight hcore (norm_nonneg _) (Real.exp_pos _).le

private theorem integral_norm_le_indicator_const
    {g : ℝ → ℂ} {R C : ℝ}
    (hg : Integrable g)
    (hsupport : Function.support g ⊆ Metric.closedBall (0 : ℝ) R)
    (hC : 0 ≤ C)
    (hbound : ∀ u ∈ Metric.closedBall (0 : ℝ) R, ‖g u‖ ≤ C) :
    (∫ u : ℝ, ‖g u‖) ≤
      ∫ u : ℝ, (Metric.closedBall (0 : ℝ) R).indicator (fun _ ↦ C) u := by
  have hK : IsCompact (Metric.closedBall (0 : ℝ) R) :=
    ProperSpace.isCompact_closedBall 0 R
  have hmajorant : Integrable
      ((Metric.closedBall (0 : ℝ) R).indicator (fun _ ↦ C)) :=
    (integrableOn_const hK.measure_ne_top).integrable_indicator hK.measurableSet
  apply integral_mono hg.norm hmajorant
  intro u
  by_cases hu : u ∈ Metric.closedBall (0 : ℝ) R
  · simpa [hu] using hbound u hu
  · have hgu : g u = 0 := by
      by_contra hne
      exact hu (hsupport (Function.mem_support.mpr hne))
    simp [hu, hgu, hC]

private theorem secondDerivSchwartz_apply
    (h : SchwartzMap ℝ ℂ) (u : ℝ) :
    SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ h) u =
      iteratedDeriv 2 h u := by
  change deriv (deriv (h : ℝ → ℂ)) u = iteratedDeriv 2 (h : ℝ → ℂ) u
  simp only [show 2 = Nat.succ (Nat.succ 0) by norm_num,
    iteratedDeriv_succ', iteratedDeriv_zero]

/-- The zeroth and second logarithmic-pullback derivatives have `L¹` norms
bounded uniformly for real Mellin parameters in the critical strip. -/
theorem exists_uniform_logarithmicPullback_integral_bounds
    (f : BombieriTest) :
    ∃ C0 C2 : ℝ, 0 ≤ C0 ∧ 0 ≤ C2 ∧
      ∀ sigma : ℝ, 0 ≤ sigma → sigma ≤ 1 →
        (∫ u : ℝ, ‖f.logarithmicPullbackSchwartz sigma u‖) ≤ C0 ∧
        (∫ u : ℝ,
          ‖SchwartzMap.derivCLM ℂ ℂ
            (SchwartzMap.derivCLM ℂ ℂ
              (f.logarithmicPullbackSchwartz sigma)) u‖) ≤ C2 := by
  obtain ⟨R, hRpos, hRsupport⟩ :=
    (f.logarithmicPullback_hasCompactSupport 0).isBounded.subset_closedBall_lt
      0 (0 : ℝ)
  let D0 : ℝ := Real.exp R * SchwartzMap.seminorm ℂ 0 0
    (f.logarithmicPullbackSchwartz 0)
  let D2 : ℝ := ∑ i ∈ Finset.range 3,
    (Nat.choose 2 i : ℝ) * Real.exp R *
      SchwartzMap.seminorm ℂ 0 (2 - i)
        (f.logarithmicPullbackSchwartz 0)
  let majorant (D : ℝ) : ℝ → ℝ :=
    (Metric.closedBall (0 : ℝ) R).indicator (fun _ ↦ D)
  let C0 : ℝ := ∫ u : ℝ, majorant D0 u
  let C2 : ℝ := ∫ u : ℝ, majorant D2 u
  have hD0 : 0 ≤ D0 := by
    dsimp only [D0]
    positivity
  have hD2 : 0 ≤ D2 := by
    dsimp only [D2]
    apply Finset.sum_nonneg
    intro i hi
    positivity
  have hC0 : 0 ≤ C0 := by
    dsimp only [C0, majorant]
    exact integral_nonneg fun u ↦ Set.indicator_nonneg (fun _ _ ↦ hD0) u
  have hC2 : 0 ≤ C2 := by
    dsimp only [C2, majorant]
    exact integral_nonneg fun u ↦ Set.indicator_nonneg (fun _ _ ↦ hD2) u
  refine ⟨C0, C2, hC0, hC2, ?_⟩
  intro sigma hsigma0 hsigma1
  let H : SchwartzMap ℝ ℂ := f.logarithmicPullbackSchwartz sigma
  let H1 : SchwartzMap ℝ ℂ := SchwartzMap.derivCLM ℂ ℂ H
  let H2 : SchwartzMap ℝ ℂ := SchwartzMap.derivCLM ℂ ℂ H1
  have hHsupport : Function.support (H : ℝ → ℂ) ⊆
      Metric.closedBall (0 : ℝ) R := by
    intro u hu
    apply hRsupport
    rw [← logarithmicPullback_tsupport_eq_core f sigma]
    exact subset_tsupport (H : ℝ → ℂ) hu
  have hH2support : Function.support (H2 : ℝ → ℂ) ⊆
      Metric.closedBall (0 : ℝ) R := by
    intro u hu
    apply hRsupport
    rw [← logarithmicPullback_tsupport_eq_core f sigma]
    exact (SchwartzMap.tsupport_derivCLM_subset ℂ H)
      ((SchwartzMap.tsupport_derivCLM_subset ℂ H1)
        (subset_tsupport (H2 : ℝ → ℂ) hu))
  constructor
  · change (∫ u : ℝ, ‖H u‖) ≤ C0
    have hbound0 : ∀ u ∈ Metric.closedBall (0 : ℝ) R, ‖H u‖ ≤ D0 := by
      intro u hu
      exact norm_logarithmicPullback_le f hsigma0 hsigma1 hRpos.le hu
    exact (integral_norm_le_indicator_const H.integrable hHsupport hD0 hbound0).trans_eq rfl
  · change (∫ u : ℝ, ‖H2 u‖) ≤ C2
    have hbound2 : ∀ u ∈ Metric.closedBall (0 : ℝ) R, ‖H2 u‖ ≤ D2 := by
      intro u hu
      rw [show H2 u = iteratedDeriv 2
          (BombieriTest.logarithmicPullback sigma f) u by
        exact secondDerivSchwartz_apply H u]
      exact norm_iteratedDeriv_two_logarithmicPullback_le
        f hsigma0 hsigma1 hRpos.le hu
    exact (integral_norm_le_indicator_const H2.integrable hH2support hD2 hbound2).trans_eq rfl

private theorem fourier_secondDerivSchwartz
    (H : SchwartzMap ℝ ℂ) (w : ℝ) :
    𝓕 (SchwartzMap.derivCLM ℂ ℂ
      (SchwartzMap.derivCLM ℂ ℂ H) : ℝ → ℂ) w =
      (2 * (Real.pi : ℂ) * Complex.I * (w : ℂ)) ^ 2 *
        𝓕 (H : ℝ → ℂ) w := by
  let H1 : SchwartzMap ℝ ℂ := SchwartzMap.derivCLM ℂ ℂ H
  have hfourier1 := Real.fourier_deriv H.integrable H.differentiable H1.integrable
  have hfourier2 := Real.fourier_deriv H1.integrable H1.differentiable
    (SchwartzMap.derivCLM ℂ ℂ H1).integrable
  simp only [smul_eq_mul] at hfourier1 hfourier2
  change 𝓕 (deriv (H1 : ℝ → ℂ)) w = _
  rw [congrFun hfourier2 w]
  change (2 * (Real.pi : ℂ) * Complex.I * (w : ℂ)) *
      𝓕 (deriv (H : ℝ → ℂ)) w = _
  rw [congrFun hfourier1 w]
  ring

private theorem norm_fourierSchwartz_le_integral_norm
    (H : SchwartzMap ℝ ℂ) (w : ℝ) :
    ‖𝓕 (H : ℝ → ℂ) w‖ ≤ ∫ u : ℝ, ‖H u‖ := by
  rw [Real.fourier_eq]
  calc
    ‖∫ u : ℝ, Real.fourierChar (-inner ℝ u w) • (H u : ℂ)‖ ≤
        ∫ u : ℝ, ‖Real.fourierChar (-inner ℝ u w) • (H u : ℂ)‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ u : ℝ, ‖H u‖ := by
      congr 1
      funext u
      simp

/-- Uniform inverse-square decay of Mellin transforms throughout the open
critical strip.  The constant depends only on the bundled test function. -/
theorem exists_mellin_norm_le_inv_norm_sq
    (f : BombieriTest) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : NontrivialZetaZero,
      ‖mellin (f : ℝ → ℂ) rho.val‖ ≤
        C * ‖rho.val‖⁻¹ ^ (2 : ℝ) := by
  obtain ⟨C0, C2, hC0, hC2, hbounds⟩ :=
    exists_uniform_logarithmicPullback_integral_bounds f
  refine ⟨C0 + C2, add_nonneg hC0 hC2, ?_⟩
  intro rho
  let H : SchwartzMap ℝ ℂ := f.logarithmicPullbackSchwartz rho.val.re
  let H2 : SchwartzMap ℝ ℂ := SchwartzMap.derivCLM ℂ ℂ
    (SchwartzMap.derivCLM ℂ ℂ H)
  let w : ℝ := rho.val.im / (2 * Real.pi)
  have hb := hbounds rho.val.re rho.re_pos.le rho.re_lt_one.le
  have hM0 : ‖𝓕 (H : ℝ → ℂ) w‖ ≤ C0 :=
    (norm_fourierSchwartz_le_integral_norm H w).trans hb.1
  have hM2 : ‖𝓕 (H2 : ℝ → ℂ) w‖ ≤ C2 :=
    (norm_fourierSchwartz_le_integral_norm H2 w).trans hb.2
  have hcoeff :
      2 * (Real.pi : ℂ) * Complex.I * (w : ℂ) =
        (rho.val.im : ℂ) * Complex.I := by
    dsimp only [w]
    push_cast
    field_simp [Real.pi_ne_zero]
  have hsecond : ‖𝓕 (H2 : ℝ → ℂ) w‖ =
      rho.val.im ^ 2 * ‖𝓕 (H : ℝ → ℂ) w‖ := by
    rw [fourier_secondDerivSchwartz H w, norm_mul, norm_pow, hcoeff,
      norm_mul, Complex.norm_real, norm_I, mul_one, Real.norm_eq_abs, sq_abs]
  have him_bound : rho.val.im ^ 2 *
      ‖𝓕 (H : ℝ → ℂ) w‖ ≤ C2 := by
    rw [← hsecond]
    exact hM2
  have hcombined : (1 + rho.val.im ^ 2) *
      ‖𝓕 (H : ℝ → ℂ) w‖ ≤ C0 + C2 := by
    nlinarith [hM0]
  have hnormsq : ‖rho.val‖ ^ 2 ≤ 1 + rho.val.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [rho.re_pos, rho.re_lt_one]
  have hrho_ne : rho.val ≠ 0 := by
    intro hrho
    have := rho.re_pos
    rw [hrho] at this
    norm_num at this
  have hnorm_pos : 0 < ‖rho.val‖ := norm_pos_iff.mpr hrho_ne
  have hnormmul : ‖rho.val‖ ^ 2 *
      ‖𝓕 (H : ℝ → ℂ) w‖ ≤ C0 + C2 :=
    (mul_le_mul_of_nonneg_right hnormsq (norm_nonneg _)).trans hcombined
  rw [mellin_eq_fourier_logarithmicPullbackSchwartz]
  change ‖𝓕 (H : ℝ → ℂ) w‖ ≤ _
  have hdiv : ‖𝓕 (H : ℝ → ℂ) w‖ ≤
      (C0 + C2) / ‖rho.val‖ ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hnorm_pos)).2
    nlinarith
  calc
    ‖𝓕 (H : ℝ → ℂ) w‖ ≤
        (C0 + C2) / ‖rho.val‖ ^ 2 := hdiv
    _ = (C0 + C2) * ‖rho.val‖⁻¹ ^ (2 : ℝ) := by
      rw [Real.rpow_two, div_eq_mul_inv, inv_pow]

private theorem nontrivialZero_ne_zero (rho : NontrivialZetaZero) :
    rho.val ≠ 0 := by
  intro h
  have := rho.re_pos
  rw [h] at this
  norm_num at this

private theorem nontrivialZero_ne_one (rho : NontrivialZetaZero) :
    rho.val ≠ 1 := by
  intro h
  have := rho.re_lt_one
  rw [h] at this
  norm_num at this

/-- In the open critical strip, the polynomial-Gamma factor relating xi and
zeta is analytic and nonvanishing, so the two zero multiplicities agree. -/
theorem analyticOrderNatAt_xiFunction_eq_riemannZeta
    (rho : NontrivialZetaZero) :
    analyticOrderNatAt xiFunction rho.val =
      analyticOrderNatAt riemannZeta rho.val := by
  let a : ℂ → ℂ := fun z ↦
    (1 / 2 : ℂ) * z * (z - 1) * Gammaℝ z
  have hrho0 : rho.val ≠ 0 := nontrivialZero_ne_zero rho
  have hrho1 : rho.val ≠ 1 := nontrivialZero_ne_one rho
  have hGamma_ne : Gammaℝ rho.val ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos rho.re_pos
  have gammaR_differentiableAt_of_re_pos : ∀ z : ℂ, 0 < z.re →
      DifferentiableAt ℂ Gammaℝ z := by
    intro z hz
    rw [show Gammaℝ = fun w : ℂ ↦
        (Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2) by
      funext w
      exact Complex.Gammaℝ_def w]
    apply DifferentiableAt.mul
    · exact (differentiableAt_id.neg.div_const 2).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    · have hhalf : DifferentiableAt ℂ (fun w : ℂ ↦ w / 2) z :=
        differentiableAt_id.div_const 2
      apply (Complex.differentiableAt_Gamma (z / 2) ?_).comp z hhalf
      intro m hm
      have hre : (z / 2).re = (-m : ℂ).re := congrArg Complex.re hm
      norm_num at hre
      have hm_nonneg : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
  let U : Set ℂ := {z | 0 < z.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const continuous_re
  have hGamma_an : AnalyticAt ℂ Gammaℝ rho.val := by
    have hdiff : DifferentiableOn ℂ Gammaℝ U := fun z hz ↦
      (gammaR_differentiableAt_of_re_pos z hz).differentiableWithinAt
    exact hdiff.analyticOnNhd hUopen rho.val rho.re_pos
  have ha_an : AnalyticAt ℂ a rho.val := by
    dsimp only [a]
    exact (((analyticAt_const.mul analyticAt_id).mul
      (analyticAt_id.sub analyticAt_const)).mul hGamma_an)
  have ha_ne : a rho.val ≠ 0 := by
    dsimp only [a]
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) hrho0) (sub_ne_zero.mpr hrho1))
      hGamma_ne
  have hzeta_an : AnalyticAt ℂ riemannZeta rho.val := by
    have hdiff : DifferentiableOn ℂ riemannZeta ({1}ᶜ : Set ℂ) :=
      fun z hz ↦ (differentiableAt_riemannZeta hz).differentiableWithinAt
    exact hdiff.analyticOnNhd isOpen_compl_singleton rho.val hrho1
  have hlocal : xiFunction =ᶠ[nhds rho.val] fun z ↦ a z * riemannZeta z := by
    filter_upwards [eventually_ne_nhds hrho0, eventually_ne_nhds hrho1,
      hGamma_an.continuousAt.eventually_ne hGamma_ne] with z hz0 hz1 hzGamma
    dsimp only [a]
    rw [xiFunction_eq_mul_completedZeta z hz0 hz1,
      riemannZeta_def_of_ne_zero hz0]
    field_simp
  have ha_order : analyticOrderAt a rho.val = 0 :=
    ha_an.analyticOrderAt_eq_zero.mpr ha_ne
  have horder : analyticOrderAt xiFunction rho.val =
      analyticOrderAt riemannZeta rho.val := by
    calc
      analyticOrderAt xiFunction rho.val =
          analyticOrderAt (fun z ↦ a z * riemannZeta z) rho.val :=
        analyticOrderAt_congr hlocal
      _ = analyticOrderAt a rho.val +
          analyticOrderAt riemannZeta rho.val :=
        analyticOrderAt_mul ha_an hzeta_an
      _ = analyticOrderAt riemannZeta rho.val := by rw [ha_order, zero_add]
  simp only [analyticOrderNatAt]
  rw [horder]

/-- The arbitrary exact-multiplicity zero enumeration inherits the
inverse-square summability of the xi divisor. -/
theorem zetaZeroEnumeration_summable_inv_norm_sq
    (zeros : ZetaZeroEnumeration) :
    Summable (fun n ↦ ‖(zeros.zero n).val‖⁻¹ ^ (2 : ℝ)) := by
  let XiZero := {z : ℂ // xiFunction z = 0 ∧ z ≠ 0}
  let toXi : NontrivialZetaZero → XiZero := fun rho ↦
    ⟨rho.val, (xiFunction_zero_iff rho.re_pos rho.re_lt_one).2 rho.is_zero,
      nontrivialZero_ne_zero rho⟩
  have htoXi : Function.Injective toXi := by
    intro rho sigma h
    have hv : rho.val = sigma.val :=
      congrArg (fun z : XiZero ↦ (z : ℂ)) h
    cases rho
    cases sigma
    simp_all
  have hxi : Summable (fun z : XiZero ↦
      (analyticOrderNatAt xiFunction (z : ℂ) : ℝ) *
        ‖(z : ℂ)‖⁻¹ ^ (2 : ℝ)) := by
    apply EntireFunction.summable_zero_multiplicity_rpow_of_order_lt
      xiFunction differentiable_xiFunction xiFunction_ne_const_zero
    rw [xiFunction_order]
    exact EReal.coe_lt_coe_iff.mpr (by norm_num)
  have hzeta : Summable (fun rho : NontrivialZetaZero ↦
      (analyticOrderNatAt riemannZeta rho.val : ℝ) *
        ‖rho.val‖⁻¹ ^ (2 : ℝ)) := by
    have hcomp := hxi.comp_injective htoXi
    change Summable (fun rho : NontrivialZetaZero ↦
      (analyticOrderNatAt xiFunction rho.val : ℝ) *
        ‖rho.val‖⁻¹ ^ (2 : ℝ)) at hcomp
    simpa only [analyticOrderNatAt_xiFunction_eq_riemannZeta] using hcomp
  rw [summable_partition
    (fun n : ℕ ↦ Real.rpow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _)
    (s := fun rho : NontrivialZetaZero ↦ {n : ℕ | zeros.zero n = rho})]
  constructor
  · intro rho
    exact (zeros.fiberFinite rho).summable
      (fun n : ℕ ↦ ‖(zeros.zero n).val‖⁻¹ ^ (2 : ℝ))
  · apply hzeta.congr
    intro rho
    letI : Fintype {n : ℕ | zeros.zero n = rho} :=
      (zeros.fiberFinite rho).fintype
    rw [tsum_fintype]
    have hconst : ∀ n : {n : ℕ | zeros.zero n = rho},
        ‖(zeros.zero n).val‖⁻¹ ^ (2 : ℝ) =
          ‖rho.val‖⁻¹ ^ (2 : ℝ) := by
      intro n
      rw [n.property]
    simp_rw [hconst]
    have hcard : Fintype.card {n : ℕ | zeros.zero n = rho} =
        analyticOrderNatAt riemannZeta rho.val := by
      rw [Fintype.card_eq_nat_card]
      exact zeros.fiberCard rho
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hcard]
  · intro n
    refine ⟨zeros.zero n, rfl, ?_⟩
    intro rho hrho
    exact hrho.symm

/-- The Mellin zero series in Bombieri's explicit formula is absolutely
summable for every compactly supported smooth multiplicative test. -/
theorem zetaZeroEnumeration_mellin_summable
    (zeros : ZetaZeroEnumeration) (f : BombieriTest) :
    Summable (fun n ↦ mellin (f : ℝ → ℂ) (zeros.zero n).val) := by
  obtain ⟨C, hC, hbound⟩ := exists_mellin_norm_le_inv_norm_sq f
  have hinv := zetaZeroEnumeration_summable_inv_norm_sq zeros
  have hnorm : Summable
      (fun n ↦ ‖mellin (f : ℝ → ℂ) (zeros.zero n).val‖) := by
    apply (hinv.mul_left C).of_nonneg_of_le
    · intro n
      exact norm_nonneg _
    · intro n
      exact hbound (zeros.zero n)
  exact hnorm.of_norm

#print axioms mellin_eq_fourier_logarithmicPullbackSchwartz
#print axioms exists_uniform_logarithmicPullback_integral_bounds
#print axioms exists_mellin_norm_le_inv_norm_sq
#print axioms analyticOrderNatAt_xiFunction_eq_riemannZeta
#print axioms zetaZeroEnumeration_summable_inv_norm_sq
#print axioms zetaZeroEnumeration_mellin_summable

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
