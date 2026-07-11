import ArithmeticHodge.Analysis.MultiplicativeWeilZeroSummability
import ArithmeticHodge.Analysis.ResidueRectangle
import ArithmeticHodge.Analysis.XiZeroFreeHeight
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Uniform Mellin decay and horizontal Bombieri contours

Bombieri tests have Mellin transforms that decay uniformly to arbitrary
polynomial order on every fixed vertical strip. These estimates control the
horizontal sides of the xi rectangle once `xi'/xi` has a polynomial bound.
-/

set_option autoImplicit false

open Complex Filter MeasureTheory Real Set Topology
open scoped ContDiff Distributions FourierTransform Interval Real SchwartzMap

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- The top horizontal interval-integral term in a symmetric rectangle. -/
def bombieriHorizontalUpper
    (f : BombieriTest) (L : ℂ → ℂ) (a b T : ℝ) : ℂ :=
  ∫ σ : ℝ in a..b,
    mellin (f : ℝ → ℂ) (σ + T * I) * L (σ + T * I)

/-- The bottom horizontal interval-integral term in a symmetric rectangle. -/
def bombieriHorizontalLower
    (f : BombieriTest) (L : ℂ → ℂ) (a b T : ℝ) : ℂ :=
  ∫ σ : ℝ in a..b,
    mellin (f : ℝ → ℂ) (σ - T * I) * L (σ - T * I)

/-- The preceding definitions are literally the bottom and top terms in the
repository's `rectIntegral` convention. -/
theorem rectIntegral_bombieri_horizontal_decomposition
    (f : BombieriTest) (L : ℂ → ℂ) (a b T : ℝ) :
    rectIntegral
        (fun s ↦ mellin (f : ℝ → ℂ) s * L s)
        ((a : ℂ) - T * I) ((b : ℂ) + T * I) =
      bombieriHorizontalLower f L a b T -
        bombieriHorizontalUpper f L a b T +
      I * (∫ y : ℝ in -T..T,
        mellin (f : ℝ → ℂ) (b + y * I) * L (b + y * I)) -
      I * (∫ y : ℝ in -T..T,
        mellin (f : ℝ → ℂ) (a + y * I) * L (a + y * I)) := by
  simp [rectIntegral, bombieriHorizontalLower, bombieriHorizontalUpper,
    smul_eq_mul, sub_eq_add_neg]

private theorem logarithmicPullback_eq_weight_smul
    (f : BombieriTest) (sigma : ℝ) :
    BombieriTest.logarithmicPullback sigma f = fun u ↦
      Real.exp ((-sigma) * u) • BombieriTest.logarithmicPullback 0 f u := by
  funext u
  simp only [BombieriTest.logarithmicPullback, zero_mul, neg_zero,
    Real.exp_zero, Complex.real_smul]
  push_cast
  ring

private theorem logarithmicPullback_tsupport_eq
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

private theorem norm_iteratedDeriv_exp_weight_le_on_Icc
    {a b sigma u R : ℝ} (hsigma0 : a ≤ sigma) (hsigma1 : sigma ≤ b)
    (hu : u ∈ Metric.closedBall (0 : ℝ) R) (i : ℕ) :
    ‖iteratedDeriv i (fun v : ℝ ↦ Real.exp ((-sigma) * v)) u‖ ≤
      (|a| + |b| + 1) ^ i * Real.exp ((|a| + |b| + 1) * R) := by
  have hformula := congrFun (iteratedDeriv_exp_const_mul i (-sigma)) u
  rw [hformula, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg,
    abs_of_pos (Real.exp_pos _)]
  have hsigma_abs : |sigma| ≤ |a| + |b| := by
    rw [abs_le]
    constructor
    · calc
        -(|a| + |b|) ≤ -|a| := by linarith [abs_nonneg b]
        _ ≤ a := neg_abs_le a
        _ ≤ sigma := hsigma0
    · calc
        sigma ≤ b := hsigma1
        _ ≤ |b| := le_abs_self b
        _ ≤ |a| + |b| := by linarith [abs_nonneg a]
  have hsigma_bound : |sigma| ≤ |a| + |b| + 1 := by linarith
  have hscale_nonneg : 0 ≤ |a| + |b| + 1 := by positivity
  have hpow : |sigma| ^ i ≤ (|a| + |b| + 1) ^ i :=
    pow_le_pow_left₀ (abs_nonneg sigma) hsigma_bound i
  have huabs : |u| ≤ R := by
    simpa [Real.dist_eq] using (Metric.mem_closedBall.mp hu)
  have hexponent : (-sigma) * u ≤ (|a| + |b| + 1) * R := by
    calc
      (-sigma) * u ≤ |(-sigma) * u| := le_abs_self _
      _ = |sigma| * |u| := by rw [abs_mul, abs_neg]
      _ ≤ (|a| + |b| + 1) * R :=
        mul_le_mul hsigma_bound huabs (abs_nonneg u) hscale_nonneg
  exact mul_le_mul hpow (Real.exp_le_exp.mpr hexponent)
    (Real.exp_pos _).le (pow_nonneg hscale_nonneg i)

private theorem norm_iteratedDeriv_two_logarithmicPullback_le_on_Icc
    (f : BombieriTest) {a b sigma R u : ℝ}
    (hsigma0 : a ≤ sigma) (hsigma1 : sigma ≤ b)
    (hu : u ∈ Metric.closedBall (0 : ℝ) R) :
    ‖iteratedDeriv 2 (BombieriTest.logarithmicPullback sigma f) u‖ ≤
      ∑ i ∈ Finset.range 3,
        (Nat.choose 2 i : ℝ) *
          ((|a| + |b| + 1) ^ i * Real.exp ((|a| + |b| + 1) * R)) *
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
  rw [logarithmicPullback_eq_weight_smul f sigma]
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
        (Nat.choose 2 i : ℝ) *
          ((|a| + |b| + 1) ^ i * Real.exp ((|a| + |b| + 1) * R)) *
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
        _ ≤ (Nat.choose 2 i : ℝ) *
              ((|a| + |b| + 1) ^ i * Real.exp ((|a| + |b| + 1) * R)) *
              SchwartzMap.seminorm ℂ 0 (2 - i)
                (f.logarithmicPullbackSchwartz 0) := by
          have hweight := norm_iteratedDeriv_exp_weight_le_on_Icc
            hsigma0 hsigma1 hu i
          have hcore := SchwartzMap.le_seminorm' ℂ 0 (2 - i)
            (f.logarithmicPullbackSchwartz 0) u
          simp only [pow_zero, one_mul] at hcore
          change ‖iteratedDeriv (2 - i) core u‖ ≤
            SchwartzMap.seminorm ℂ 0 (2 - i)
              (f.logarithmicPullbackSchwartz 0) at hcore
          gcongr

private theorem norm_iteratedDeriv_logarithmicPullback_le_on_Icc
    (f : BombieriTest) (k : ℕ) {a b sigma R u : ℝ}
    (hsigma0 : a ≤ sigma) (hsigma1 : sigma ≤ b)
    (hu : u ∈ Metric.closedBall (0 : ℝ) R) :
    ‖iteratedDeriv k (BombieriTest.logarithmicPullback sigma f) u‖ ≤
      ∑ i ∈ Finset.range (k + 1),
        (Nat.choose k i : ℝ) *
          ((|a| + |b| + 1) ^ i * Real.exp ((|a| + |b| + 1) * R)) *
          SchwartzMap.seminorm ℂ 0 (k - i)
            (f.logarithmicPullbackSchwartz 0) := by
  let weight : ℝ → ℝ := fun v ↦ Real.exp ((-sigma) * v)
  let core : ℝ → ℂ := BombieriTest.logarithmicPullback 0 f
  have hw : ContDiffWithinAt ℝ k weight Set.univ u := by
    dsimp only [weight]
    fun_prop
  have hc : ContDiffWithinAt ℝ k core Set.univ u := by
    exact (f.logarithmicPullback_contDiff 0).of_le
      (WithTop.coe_mono (show (k : ℕ∞) ≤ ⊤ from le_top))
      |>.contDiffAt.contDiffWithinAt
  have hproduct : iteratedDeriv k
      (fun v ↦ weight v • core v) u =
      ∑ i ∈ Finset.range (k + 1),
        Nat.choose k i • iteratedDeriv i weight u •
          iteratedDeriv (k - i) core u := by
    simpa only [iteratedDerivWithin_univ] using
      (iteratedDerivWithin_smul (n := k) (x := u) (s := Set.univ)
        (Set.mem_univ u) uniqueDiffOn_univ hw hc)
  rw [logarithmicPullback_eq_weight_smul f sigma]
  change ‖iteratedDeriv k (fun v ↦ weight v • core v) u‖ ≤ _
  rw [hproduct]
  calc
    ‖∑ i ∈ Finset.range (k + 1),
        Nat.choose k i • iteratedDeriv i weight u •
          iteratedDeriv (k - i) core u‖ ≤
        ∑ i ∈ Finset.range (k + 1),
          ‖Nat.choose k i • iteratedDeriv i weight u •
            iteratedDeriv (k - i) core u‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (k + 1),
        (Nat.choose k i : ℝ) *
          ((|a| + |b| + 1) ^ i * Real.exp ((|a| + |b| + 1) * R)) *
          SchwartzMap.seminorm ℂ 0 (k - i)
            (f.logarithmicPullbackSchwartz 0) := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        ‖Nat.choose k i • (iteratedDeriv i weight u •
            iteratedDeriv (k - i) core u)‖ ≤
            (Nat.choose k i : ℝ) *
              ‖iteratedDeriv i weight u •
                iteratedDeriv (k - i) core u‖ := norm_nsmul_le
        _ = (Nat.choose k i : ℝ) * ‖iteratedDeriv i weight u‖ *
              ‖iteratedDeriv (k - i) core u‖ := by
          rw [Complex.real_smul, norm_mul, Complex.norm_real]
          ring
        _ ≤ (Nat.choose k i : ℝ) *
              ((|a| + |b| + 1) ^ i * Real.exp ((|a| + |b| + 1) * R)) *
              SchwartzMap.seminorm ℂ 0 (k - i)
                (f.logarithmicPullbackSchwartz 0) := by
          have hweight := norm_iteratedDeriv_exp_weight_le_on_Icc
            hsigma0 hsigma1 hu i
          have hcore := SchwartzMap.le_seminorm' ℂ 0 (k - i)
            (f.logarithmicPullbackSchwartz 0) u
          simp only [pow_zero, one_mul] at hcore
          change ‖iteratedDeriv (k - i) core u‖ ≤
            SchwartzMap.seminorm ℂ 0 (k - i)
              (f.logarithmicPullbackSchwartz 0) at hcore
          gcongr

private theorem norm_logarithmicPullback_le_on_Icc
    (f : BombieriTest) {a b sigma R u : ℝ}
    (hsigma0 : a ≤ sigma) (hsigma1 : sigma ≤ b)
    (hu : u ∈ Metric.closedBall (0 : ℝ) R) :
    ‖BombieriTest.logarithmicPullback sigma f u‖ ≤
      Real.exp ((|a| + |b| + 1) * R) *
        SchwartzMap.seminorm ℂ 0 0
          (f.logarithmicPullbackSchwartz 0) := by
  rw [logarithmicPullback_eq_weight_smul f sigma]
  change ‖Real.exp ((-sigma) * u) •
      BombieriTest.logarithmicPullback 0 f u‖ ≤ _
  rw [Complex.real_smul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hweight := norm_iteratedDeriv_exp_weight_le_on_Icc
    hsigma0 hsigma1 hu 0
  simp only [iteratedDeriv_zero, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    pow_zero, one_mul] at hweight
  have hcore := SchwartzMap.le_seminorm' ℂ 0 0
    (f.logarithmicPullbackSchwartz 0) u
  simp only [pow_zero, one_mul, iteratedDeriv_zero] at hcore
  exact mul_le_mul hweight hcore (norm_nonneg _) (Real.exp_pos _).le

private theorem integral_norm_le_indicator_const
    {g : ℝ → ℂ} {R C : ℝ}
    (hg : Integrable g)
    (hsupport : Function.support g ⊆ Metric.closedBall (0 : ℝ) R)
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
    simp [hu, hgu]

private theorem secondDerivSchwartz_apply
    (h : SchwartzMap ℝ ℂ) (u : ℝ) :
    SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ h) u =
      iteratedDeriv 2 h u := by
  change deriv (deriv (h : ℝ → ℂ)) u = iteratedDeriv 2 (h : ℝ → ℂ) u
  simp only [show 2 = Nat.succ (Nat.succ 0) by norm_num,
    iteratedDeriv_succ', iteratedDeriv_zero]

private def schwartzIteratedDeriv
    (k : ℕ) (H : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  match k with
  | 0 => H
  | k + 1 => schwartzIteratedDeriv k (SchwartzMap.derivCLM ℂ ℂ H)

private theorem schwartzIteratedDeriv_apply
    (k : ℕ) (H : SchwartzMap ℝ ℂ) (u : ℝ) :
    schwartzIteratedDeriv k H u = iteratedDeriv k (H : ℝ → ℂ) u := by
  induction k generalizing H with
  | zero => rfl
  | succ k ih =>
      rw [schwartzIteratedDeriv, ih]
      have hfun :
          ((SchwartzMap.derivCLM ℂ ℂ H : SchwartzMap ℝ ℂ) : ℝ → ℂ) =
            deriv (H : ℝ → ℂ) := by
        funext x
        exact SchwartzMap.derivCLM_apply ℂ H x
      rw [hfun, ← iteratedDeriv_succ']

private theorem schwartzIteratedDeriv_tsupport_subset
    (k : ℕ) (H : SchwartzMap ℝ ℂ) :
    tsupport (schwartzIteratedDeriv k H : ℝ → ℂ) ⊆
      tsupport (H : ℝ → ℂ) := by
  induction k generalizing H with
  | zero => exact Set.Subset.rfl
  | succ k ih =>
      exact (ih (SchwartzMap.derivCLM ℂ ℂ H)).trans
        (SchwartzMap.tsupport_derivCLM_subset ℂ H)

private theorem exists_uniform_logarithmicPullback_integral_bounds_on_Icc
    (f : BombieriTest) (a b : ℝ) :
    ∃ C0 C2 : ℝ, 0 ≤ C0 ∧ 0 ≤ C2 ∧
      ∀ sigma : ℝ, a ≤ sigma → sigma ≤ b →
        (∫ u : ℝ, ‖f.logarithmicPullbackSchwartz sigma u‖) ≤ C0 ∧
        (∫ u : ℝ,
          ‖SchwartzMap.derivCLM ℂ ℂ
            (SchwartzMap.derivCLM ℂ ℂ
              (f.logarithmicPullbackSchwartz sigma)) u‖) ≤ C2 := by
  obtain ⟨R, _hRpos, hRsupport⟩ :=
    (f.logarithmicPullback_hasCompactSupport 0).isBounded.subset_closedBall_lt
      0 (0 : ℝ)
  let D0 : ℝ := Real.exp ((|a| + |b| + 1) * R) *
    SchwartzMap.seminorm ℂ 0 0 (f.logarithmicPullbackSchwartz 0)
  let D2 : ℝ := ∑ i ∈ Finset.range 3,
    (Nat.choose 2 i : ℝ) *
      ((|a| + |b| + 1) ^ i * Real.exp ((|a| + |b| + 1) * R)) *
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
    rw [← logarithmicPullback_tsupport_eq f sigma]
    exact subset_tsupport (H : ℝ → ℂ) hu
  have hH2support : Function.support (H2 : ℝ → ℂ) ⊆
      Metric.closedBall (0 : ℝ) R := by
    intro u hu
    apply hRsupport
    rw [← logarithmicPullback_tsupport_eq f sigma]
    exact (SchwartzMap.tsupport_derivCLM_subset ℂ H)
      ((SchwartzMap.tsupport_derivCLM_subset ℂ H1)
        (subset_tsupport (H2 : ℝ → ℂ) hu))
  constructor
  · change (∫ u : ℝ, ‖H u‖) ≤ C0
    have hbound0 : ∀ u ∈ Metric.closedBall (0 : ℝ) R, ‖H u‖ ≤ D0 := by
      intro u hu
      exact norm_logarithmicPullback_le_on_Icc
        f hsigma0 hsigma1 hu
    exact (integral_norm_le_indicator_const H.integrable hHsupport hbound0).trans_eq rfl
  · change (∫ u : ℝ, ‖H2 u‖) ≤ C2
    have hbound2 : ∀ u ∈ Metric.closedBall (0 : ℝ) R, ‖H2 u‖ ≤ D2 := by
      intro u hu
      rw [show H2 u = iteratedDeriv 2
          (BombieriTest.logarithmicPullback sigma f) u by
        exact secondDerivSchwartz_apply H u]
      exact norm_iteratedDeriv_two_logarithmicPullback_le_on_Icc
        f hsigma0 hsigma1 hu
    exact (integral_norm_le_indicator_const H2.integrable hH2support hbound2).trans_eq rfl

private theorem exists_uniform_logarithmicPullback_integral_bound_order_on_Icc
    (f : BombieriTest) (a b : ℝ) (k : ℕ) :
    ∃ Ck : ℝ, 0 ≤ Ck ∧
      ∀ sigma : ℝ, a ≤ sigma → sigma ≤ b →
        (∫ u : ℝ,
          ‖schwartzIteratedDeriv k
            (f.logarithmicPullbackSchwartz sigma) u‖) ≤ Ck := by
  obtain ⟨R, _hRpos, hRsupport⟩ :=
    (f.logarithmicPullback_hasCompactSupport 0).isBounded.subset_closedBall_lt
      0 (0 : ℝ)
  let Dk : ℝ := ∑ i ∈ Finset.range (k + 1),
    (Nat.choose k i : ℝ) *
      ((|a| + |b| + 1) ^ i * Real.exp ((|a| + |b| + 1) * R)) *
      SchwartzMap.seminorm ℂ 0 (k - i)
        (f.logarithmicPullbackSchwartz 0)
  let majorant : ℝ → ℝ :=
    (Metric.closedBall (0 : ℝ) R).indicator (fun _ ↦ Dk)
  let Ck : ℝ := ∫ u : ℝ, majorant u
  have hDk : 0 ≤ Dk := by
    dsimp only [Dk]
    apply Finset.sum_nonneg
    intro i hi
    positivity
  have hCk : 0 ≤ Ck := by
    dsimp only [Ck, majorant]
    exact integral_nonneg fun u ↦ Set.indicator_nonneg (fun _ _ ↦ hDk) u
  refine ⟨Ck, hCk, ?_⟩
  intro sigma hsigma0 hsigma1
  let H : SchwartzMap ℝ ℂ := f.logarithmicPullbackSchwartz sigma
  let Hk : SchwartzMap ℝ ℂ := schwartzIteratedDeriv k H
  have hHksupport : Function.support (Hk : ℝ → ℂ) ⊆
      Metric.closedBall (0 : ℝ) R := by
    intro u hu
    apply hRsupport
    rw [← logarithmicPullback_tsupport_eq f sigma]
    exact schwartzIteratedDeriv_tsupport_subset k H
      (subset_tsupport (Hk : ℝ → ℂ) hu)
  change (∫ u : ℝ, ‖Hk u‖) ≤ Ck
  have hbound : ∀ u ∈ Metric.closedBall (0 : ℝ) R, ‖Hk u‖ ≤ Dk := by
    intro u hu
    rw [show Hk u = iteratedDeriv k
        (BombieriTest.logarithmicPullback sigma f) u by
      exact schwartzIteratedDeriv_apply k H u]
    exact norm_iteratedDeriv_logarithmicPullback_le_on_Icc
      f k hsigma0 hsigma1 hu
  exact (integral_norm_le_indicator_const Hk.integrable hHksupport hbound).trans_eq rfl

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

private theorem fourier_schwartzIteratedDeriv
    (k : ℕ) (H : SchwartzMap ℝ ℂ) (w : ℝ) :
    𝓕 (schwartzIteratedDeriv k H : ℝ → ℂ) w =
      (2 * (Real.pi : ℂ) * Complex.I * (w : ℂ)) ^ k *
        𝓕 (H : ℝ → ℂ) w := by
  induction k generalizing H with
  | zero => simp [schwartzIteratedDeriv]
  | succ k ih =>
      change 𝓕 (schwartzIteratedDeriv k
        (SchwartzMap.derivCLM ℂ ℂ H) : ℝ → ℂ) w = _
      rw [ih]
      have hfourier := Real.fourier_deriv H.integrable H.differentiable
        (SchwartzMap.derivCLM ℂ ℂ H).integrable
      simp only [smul_eq_mul] at hfourier
      have hfun :
          ((SchwartzMap.derivCLM ℂ ℂ H : SchwartzMap ℝ ℂ) : ℝ → ℂ) =
            deriv (H : ℝ → ℂ) := by
        funext x
        exact SchwartzMap.derivCLM_apply ℂ H x
      rw [hfun]
      rw [congrFun hfourier w, pow_succ]
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

/-- Uniform inverse-square Mellin decay on any fixed closed vertical strip.
This is the horizontal-edge uniformity not exposed by the pointwise
`bombieriMellin_vertical_rapidDecay` API. -/
theorem BombieriTest.exists_uniform_mellin_norm_le_inv_one_add_sq
    (f : BombieriTest) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ sigma : ℝ, a ≤ sigma → sigma ≤ b →
      ∀ t : ℝ, ‖mellin (f : ℝ → ℂ) (sigma + t * I)‖ ≤
        C / (1 + t ^ 2) := by
  obtain ⟨C0, C2, hC0, hC2, hbounds⟩ :=
    exists_uniform_logarithmicPullback_integral_bounds_on_Icc f a b
  refine ⟨C0 + C2, add_nonneg hC0 hC2, ?_⟩
  intro sigma hsigma0 hsigma1 t
  let H : SchwartzMap ℝ ℂ := f.logarithmicPullbackSchwartz sigma
  let H2 : SchwartzMap ℝ ℂ := SchwartzMap.derivCLM ℂ ℂ
    (SchwartzMap.derivCLM ℂ ℂ H)
  let w : ℝ := t / (2 * Real.pi)
  have hb := hbounds sigma hsigma0 hsigma1
  have hM0 : ‖𝓕 (H : ℝ → ℂ) w‖ ≤ C0 :=
    (norm_fourierSchwartz_le_integral_norm H w).trans hb.1
  have hM2 : ‖𝓕 (H2 : ℝ → ℂ) w‖ ≤ C2 :=
    (norm_fourierSchwartz_le_integral_norm H2 w).trans hb.2
  have hcoeff :
      2 * (Real.pi : ℂ) * Complex.I * (w : ℂ) =
        (t : ℂ) * Complex.I := by
    dsimp only [w]
    push_cast
    field_simp [Real.pi_ne_zero]
  have hsecond : ‖𝓕 (H2 : ℝ → ℂ) w‖ =
      t ^ 2 * ‖𝓕 (H : ℝ → ℂ) w‖ := by
    rw [fourier_secondDerivSchwartz H w, norm_mul, norm_pow, hcoeff,
      norm_mul, Complex.norm_real, norm_I, mul_one, Real.norm_eq_abs, sq_abs]
  have ht_bound : t ^ 2 * ‖𝓕 (H : ℝ → ℂ) w‖ ≤ C2 := by
    rw [← hsecond]
    exact hM2
  have hcombined : (1 + t ^ 2) * ‖𝓕 (H : ℝ → ℂ) w‖ ≤ C0 + C2 := by
    nlinarith [hM0]
  dsimp only [H, w] at hcombined
  rw [bombieriMellin_vertical_eq_fourier]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 1 + t ^ 2)).2
  calc
    ‖𝓕 (f.logarithmicPullbackSchwartz sigma) (t / (2 * Real.pi))‖ *
        (1 + t ^ 2) =
      (1 + t ^ 2) *
        ‖𝓕 (f.logarithmicPullbackSchwartz sigma) (t / (2 * Real.pi))‖ :=
      mul_comm _ _
    _ ≤ C0 + C2 := hcombined

/-- Mellin transforms of a Bombieri test decay uniformly faster than every
polynomial on any fixed closed vertical strip. -/
theorem BombieriTest.exists_uniform_mellin_norm_le_inv_one_add_abs_pow
    (f : BombieriTest) (a b : ℝ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ sigma : ℝ, a ≤ sigma → sigma ≤ b →
      ∀ t : ℝ, ‖mellin (f : ℝ → ℂ) (sigma + t * I)‖ ≤
        C / (1 + |t| ^ k) := by
  obtain ⟨C0, hC0, hbound0⟩ :=
    exists_uniform_logarithmicPullback_integral_bound_order_on_Icc
      f a b 0
  obtain ⟨Ck, hCk, hboundk⟩ :=
    exists_uniform_logarithmicPullback_integral_bound_order_on_Icc
      f a b k
  refine ⟨C0 + Ck, add_nonneg hC0 hCk, ?_⟩
  intro sigma hsigma0 hsigma1 t
  let H : SchwartzMap ℝ ℂ := f.logarithmicPullbackSchwartz sigma
  let Hk : SchwartzMap ℝ ℂ := schwartzIteratedDeriv k H
  let w : ℝ := t / (2 * Real.pi)
  have hb0 : (∫ u : ℝ, ‖H u‖) ≤ C0 := by
    simpa only [schwartzIteratedDeriv] using
      hbound0 sigma hsigma0 hsigma1
  have hbk : (∫ u : ℝ, ‖Hk u‖) ≤ Ck :=
    hboundk sigma hsigma0 hsigma1
  have hM0 : ‖𝓕 (H : ℝ → ℂ) w‖ ≤ C0 :=
    (norm_fourierSchwartz_le_integral_norm H w).trans hb0
  have hMk : ‖𝓕 (Hk : ℝ → ℂ) w‖ ≤ Ck :=
    (norm_fourierSchwartz_le_integral_norm Hk w).trans hbk
  have hcoeff :
      2 * (Real.pi : ℂ) * Complex.I * (w : ℂ) =
        (t : ℂ) * Complex.I := by
    dsimp only [w]
    push_cast
    field_simp [Real.pi_ne_zero]
  have hiter : ‖𝓕 (Hk : ℝ → ℂ) w‖ =
      |t| ^ k * ‖𝓕 (H : ℝ → ℂ) w‖ := by
    rw [fourier_schwartzIteratedDeriv k H w, norm_mul, norm_pow,
      hcoeff, norm_mul, Complex.norm_real, norm_I, mul_one, Real.norm_eq_abs]
  have hk_bound : |t| ^ k * ‖𝓕 (H : ℝ → ℂ) w‖ ≤ Ck := by
    rw [← hiter]
    exact hMk
  have hcombined : (1 + |t| ^ k) * ‖𝓕 (H : ℝ → ℂ) w‖ ≤
      C0 + Ck := by
    nlinarith [hM0]
  dsimp only [H, w] at hcombined
  rw [bombieriMellin_vertical_eq_fourier]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 1 + |t| ^ k)).2
  calc
    ‖𝓕 (f.logarithmicPullbackSchwartz sigma) (t / (2 * Real.pi))‖ *
        (1 + |t| ^ k) =
      (1 + |t| ^ k) *
        ‖𝓕 (f.logarithmicPullbackSchwartz sigma) (t / (2 * Real.pi))‖ :=
      mul_comm _ _
    _ ≤ C0 + Ck := hcombined

/-- Arbitrary-order uniform Mellin decay turns any correspondingly smaller
uniform horizontal growth bound into vanishing of both horizontal terms. -/
theorem bombieriHorizontalPair_tendsto_zero_of_decay_order
    (f : BombieriTest) (L : ℂ → ℂ) (a b : ℝ) (T B : ℕ → ℝ) (k : ℕ)
    (hab : a ≤ b)
    (hB_small : Tendsto (fun n ↦ B n / (1 + |T n| ^ k)) atTop (nhds 0))
    (hL : ∀ n σ, σ ∈ Set.Icc a b →
      ‖L (σ + T n * I)‖ ≤ B n ∧ ‖L (σ - T n * I)‖ ≤ B n) :
    Tendsto (fun n ↦ bombieriHorizontalUpper f L a b (T n)) atTop (nhds 0) ∧
      Tendsto (fun n ↦ bombieriHorizontalLower f L a b (T n)) atTop (nhds 0) := by
  obtain ⟨C, hC, hM⟩ :=
    f.exists_uniform_mellin_norm_le_inv_one_add_abs_pow a b k
  have hmajor :
      Tendsto (fun n ↦ (C * |b - a|) * (B n / (1 + |T n| ^ k)))
        atTop (nhds 0) := by
    simpa using hB_small.const_mul (C * |b - a|)
  constructor
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero
      (fun n ↦ norm_nonneg (bombieriHorizontalUpper f L a b (T n)))
      (fun n ↦ ?_) hmajor
    unfold bombieriHorizontalUpper
    calc
      ‖∫ σ : ℝ in a..b,
          mellin (f : ℝ → ℂ) (σ + T n * I) * L (σ + T n * I)‖ ≤
          (C * (B n / (1 + |T n| ^ k))) * |b - a| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro σ hσ
        rw [uIoc_of_le hab] at hσ
        have hσIcc : σ ∈ Set.Icc a b := ⟨hσ.1.le, hσ.2⟩
        rw [norm_mul]
        calc
          ‖mellin (f : ℝ → ℂ) (σ + T n * I)‖ *
              ‖L (σ + T n * I)‖ ≤
              (C / (1 + |T n| ^ k)) * B n := by
            exact mul_le_mul (hM σ hσIcc.1 hσIcc.2 (T n))
              (hL n σ hσIcc).1 (norm_nonneg _)
              (div_nonneg hC (by positivity))
          _ = C * (B n / (1 + |T n| ^ k)) := by ring
      _ = (C * |b - a|) * (B n / (1 + |T n| ^ k)) := by ring
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero
      (fun n ↦ norm_nonneg (bombieriHorizontalLower f L a b (T n)))
      (fun n ↦ ?_) hmajor
    unfold bombieriHorizontalLower
    calc
      ‖∫ σ : ℝ in a..b,
          mellin (f : ℝ → ℂ) (σ - T n * I) * L (σ - T n * I)‖ ≤
          (C * (B n / (1 + |T n| ^ k))) * |b - a| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro σ hσ
        rw [uIoc_of_le hab] at hσ
        have hσIcc : σ ∈ Set.Icc a b := ⟨hσ.1.le, hσ.2⟩
        rw [norm_mul]
        have hMneg :
            ‖mellin (f : ℝ → ℂ) (σ - T n * I)‖ ≤
              C / (1 + |T n| ^ k) := by
          simpa [sub_eq_add_neg] using hM σ hσIcc.1 hσIcc.2 (-T n)
        calc
          ‖mellin (f : ℝ → ℂ) (σ - T n * I)‖ *
              ‖L (σ - T n * I)‖ ≤
              (C / (1 + |T n| ^ k)) * B n := by
            exact mul_le_mul hMneg (hL n σ hσIcc).2
              (norm_nonneg _) (div_nonneg hC (by positivity))
          _ = C * (B n / (1 + |T n| ^ k)) := by ring
      _ = (C * |b - a|) * (B n / (1 + |T n| ^ k)) := by ring

private theorem one_add_abs_pow_four_div_one_add_abs_pow_six_tendsto_zero
    (T : ℕ → ℝ)
    (hT : Tendsto (fun n ↦ |T n|) atTop atTop) :
    Tendsto (fun n ↦ (1 + |T n|) ^ 4 / (1 + |T n| ^ 6))
      atTop (nhds 0) := by
  have hpow : Tendsto (fun n ↦ |T n| ^ 4 / |T n| ^ 6)
      atTop (nhds 0) :=
    (tendsto_pow_div_pow_atTop_zero (show 4 < 6 by omega)).comp hT
  have hmajor : Tendsto (fun n ↦ 16 * (|T n| ^ 4 / |T n| ^ 6))
      atTop (nhds 0) := by
    simpa using hpow.const_mul 16
  apply squeeze_zero'
  · filter_upwards [] with n
    positivity
  · filter_upwards [(tendsto_atTop.1 hT 1)] with n hn
    have hTpos : 0 < |T n| := zero_lt_one.trans_le hn
    have hnum : 0 ≤ (1 + |T n|) ^ 4 := by positivity
    have hdenom : |T n| ^ 6 ≤ 1 + |T n| ^ 6 := by linarith
    have hfirst :
        (1 + |T n|) ^ 4 / (1 + |T n| ^ 6) ≤
          (1 + |T n|) ^ 4 / |T n| ^ 6 :=
      div_le_div_of_nonneg_left hnum (pow_pos hTpos 6) hdenom
    have hbase : 1 + |T n| ≤ 2 * |T n| := by linarith
    have hfour : (1 + |T n|) ^ 4 ≤ 16 * |T n| ^ 4 := by
      calc
        (1 + |T n|) ^ 4 ≤ (2 * |T n|) ^ 4 :=
          pow_le_pow_left₀ (by positivity) hbase 4
        _ = 16 * |T n| ^ 4 := by ring
    have hsecond :
        (1 + |T n|) ^ 4 / |T n| ^ 6 ≤
          (16 * |T n| ^ 4) / |T n| ^ 6 :=
      div_le_div_of_nonneg_right hfour (pow_nonneg (abs_nonneg _) 6)
    calc
      (1 + |T n|) ^ 4 / (1 + |T n| ^ 6) ≤
          (1 + |T n|) ^ 4 / |T n| ^ 6 := hfirst
      _ ≤ (16 * |T n| ^ 4) / |T n| ^ 6 := hsecond
      _ = 16 * (|T n| ^ 4 / |T n| ^ 6) := by ring
  · exact hmajor

/-- Sixth-order uniform Mellin decay absorbs a uniform fourth-order growth
bound on the remaining factor. -/
theorem bombieriHorizontalPair_tendsto_zero_of_growth_four
    (f : BombieriTest) (L : ℂ → ℂ) (a b C : ℝ) (T : ℕ → ℝ)
    (hab : a ≤ b) (hT : Tendsto (fun n ↦ |T n|) atTop atTop)
    (hL : ∀ n σ, σ ∈ Set.Icc a b →
      ‖L (σ + T n * I)‖ ≤ C * (1 + |T n|) ^ 4 ∧
      ‖L (σ - T n * I)‖ ≤ C * (1 + |T n|) ^ 4) :
    Tendsto (fun n ↦ bombieriHorizontalUpper f L a b (T n)) atTop (nhds 0) ∧
      Tendsto (fun n ↦ bombieriHorizontalLower f L a b (T n)) atTop (nhds 0) := by
  apply bombieriHorizontalPair_tendsto_zero_of_decay_order
    f L a b T (fun n ↦ C * (1 + |T n|) ^ 4) 6 hab
  · have hlim :=
      one_add_abs_pow_four_div_one_add_abs_pow_six_tendsto_zero T hT
    simpa only [mul_div_assoc, mul_zero] using hlim.const_mul C
  · exact hL

/-- A uniform inverse-square Mellin bound and a subquadratic uniform
logarithmic-derivative bound force both horizontal terms to vanish. -/
theorem bombieriHorizontalPair_tendsto_zero_of_subquadratic_bound
    (f : BombieriTest) (L : ℂ → ℂ) (a b : ℝ) (T B : ℕ → ℝ)
    (hab : a ≤ b)
    (hM : ∃ C : ℝ, 0 ≤ C ∧ ∀ n σ, σ ∈ Set.Icc a b →
      ‖mellin (f : ℝ → ℂ) (σ + T n * I)‖ ≤ C / (1 + (T n) ^ 2) ∧
      ‖mellin (f : ℝ → ℂ) (σ - T n * I)‖ ≤ C / (1 + (T n) ^ 2))
    (hB_subquadratic :
      Tendsto (fun n ↦ B n / (1 + (T n) ^ 2)) atTop (nhds 0))
    (hL : ∀ n σ, σ ∈ Set.Icc a b →
      ‖L (σ + T n * I)‖ ≤ B n ∧ ‖L (σ - T n * I)‖ ≤ B n) :
    Tendsto (fun n ↦ bombieriHorizontalUpper f L a b (T n)) atTop (nhds 0) ∧
      Tendsto (fun n ↦ bombieriHorizontalLower f L a b (T n)) atTop (nhds 0) := by
  obtain ⟨C, hC, hM⟩ := hM
  have hmajor :
      Tendsto (fun n ↦ (C * |b - a|) * (B n / (1 + (T n) ^ 2)))
        atTop (nhds 0) := by
    simpa using hB_subquadratic.const_mul (C * |b - a|)
  constructor
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero
      (fun n ↦ norm_nonneg (bombieriHorizontalUpper f L a b (T n)))
      (fun n ↦ ?_) hmajor
    unfold bombieriHorizontalUpper
    calc
      ‖∫ σ : ℝ in a..b,
          mellin (f : ℝ → ℂ) (σ + T n * I) * L (σ + T n * I)‖ ≤
          (C * (B n / (1 + (T n) ^ 2))) * |b - a| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro σ hσ
        rw [uIoc_of_le hab] at hσ
        have hσIcc : σ ∈ Set.Icc a b := ⟨hσ.1.le, hσ.2⟩
        rw [norm_mul]
        calc
          ‖mellin (f : ℝ → ℂ) (σ + T n * I)‖ *
              ‖L (σ + T n * I)‖ ≤
              (C / (1 + (T n) ^ 2)) * B n := by
            exact mul_le_mul (hM n σ hσIcc).1 (hL n σ hσIcc).1
              (norm_nonneg _) (div_nonneg hC (by positivity))
          _ = C * (B n / (1 + (T n) ^ 2)) := by ring
      _ = (C * |b - a|) * (B n / (1 + (T n) ^ 2)) := by ring
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero
      (fun n ↦ norm_nonneg (bombieriHorizontalLower f L a b (T n)))
      (fun n ↦ ?_) hmajor
    unfold bombieriHorizontalLower
    calc
      ‖∫ σ : ℝ in a..b,
          mellin (f : ℝ → ℂ) (σ - T n * I) * L (σ - T n * I)‖ ≤
          (C * (B n / (1 + (T n) ^ 2))) * |b - a| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro σ hσ
        rw [uIoc_of_le hab] at hσ
        have hσIcc : σ ∈ Set.Icc a b := ⟨hσ.1.le, hσ.2⟩
        rw [norm_mul]
        calc
          ‖mellin (f : ℝ → ℂ) (σ - T n * I)‖ *
              ‖L (σ - T n * I)‖ ≤
              (C / (1 + (T n) ^ 2)) * B n := by
            exact mul_le_mul (hM n σ hσIcc).2 (hL n σ hσIcc).2
              (norm_nonneg _) (div_nonneg hC (by positivity))
          _ = C * (B n / (1 + (T n) ^ 2)) := by ring
      _ = (C * |b - a|) * (B n / (1 + (T n) ^ 2)) := by ring

private theorem one_add_log_sq_div_one_add_sq_tendsto_zero
    (T : ℕ → ℝ)
    (hT : Tendsto (fun n ↦ |T n|) atTop atTop) :
    Tendsto
      (fun n ↦ (1 + Real.log (1 + |T n|) ^ 2) / (1 + (T n) ^ 2))
      atTop (nhds 0) := by
  let X : ℕ → ℝ := fun n ↦ 1 + |T n|
  have hX : Tendsto X atTop atTop := by
    exact tendsto_atTop_mono (fun n ↦ by dsimp [X]; linarith) hT
  have hone : Tendsto (fun n ↦ 1 / X n) atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop hX
  have hlog : Tendsto (fun n ↦ Real.log (X n) ^ 2 / X n)
      atTop (nhds 0) := by
    simpa only [Function.comp_apply, one_mul, add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp hX
  have hmajor : Tendsto
      (fun n ↦ (1 + Real.log (X n) ^ 2) / X n) atTop (nhds 0) := by
    simpa only [add_div, zero_add] using hone.add hlog
  apply squeeze_zero'
  · filter_upwards [] with n
    positivity
  · filter_upwards [(tendsto_atTop.1 hT 1)] with n hn
    have hXpos : 0 < X n := by dsimp [X]; positivity
    have hnum : 0 ≤ 1 + Real.log (X n) ^ 2 := by positivity
    have hdenom : X n ≤ 1 + (T n) ^ 2 := by
      dsimp [X]
      rw [← sq_abs]
      nlinarith [abs_nonneg (T n)]
    exact div_le_div_of_nonneg_left hnum hXpos hdenom
  · simpa only [X] using hmajor

/-- For a Bombieri test, the only remaining horizontal-edge input is a
uniform subquadratic bound for `xi'/xi` along the chosen paired heights. -/
theorem bombieriXiHorizontalPair_tendsto_zero_of_subquadratic_logDeriv
    (f : BombieriTest) (a b : ℝ) (T B : ℕ → ℝ)
    (hab : a ≤ b)
    (hB_subquadratic :
      Tendsto (fun n ↦ B n / (1 + (T n) ^ 2)) atTop (nhds 0))
    (hxi : ∀ n σ, σ ∈ Set.Icc a b →
      ‖logDeriv xiFunction (σ + T n * I)‖ ≤ B n ∧
      ‖logDeriv xiFunction (σ - T n * I)‖ ≤ B n) :
    Tendsto
        (fun n ↦ bombieriHorizontalUpper f (logDeriv xiFunction) a b (T n))
        atTop (nhds 0) ∧
      Tendsto
        (fun n ↦ bombieriHorizontalLower f (logDeriv xiFunction) a b (T n))
        atTop (nhds 0) := by
  obtain ⟨C, hC, hM⟩ :=
    f.exists_uniform_mellin_norm_le_inv_one_add_sq a b
  apply bombieriHorizontalPair_tendsto_zero_of_subquadratic_bound
    f (logDeriv xiFunction) a b T B hab
    ⟨C, hC, ?_⟩ hB_subquadratic hxi
  intro n σ hσ
  constructor
  · exact hM σ hσ.1 hσ.2 (T n)
  · simpa [sub_eq_add_neg] using hM σ hσ.1 hσ.2 (-T n)

/-- The classical uniform `O(log² T)` logarithmic-derivative estimate is a
concrete sufficient input for horizontal vanishing. -/
theorem bombieriXiHorizontalPair_tendsto_zero_of_log_sq_bound
    (f : BombieriTest) (a b C : ℝ) (T : ℕ → ℝ)
    (hab : a ≤ b)
    (hT : Tendsto (fun n ↦ |T n|) atTop atTop)
    (hxi : ∀ n σ, σ ∈ Set.Icc a b →
      ‖logDeriv xiFunction (σ + T n * I)‖ ≤
          C * (1 + Real.log (1 + |T n|) ^ 2) ∧
      ‖logDeriv xiFunction (σ - T n * I)‖ ≤
          C * (1 + Real.log (1 + |T n|) ^ 2)) :
    Tendsto
        (fun n ↦ bombieriHorizontalUpper f (logDeriv xiFunction) a b (T n))
        atTop (nhds 0) ∧
      Tendsto
        (fun n ↦ bombieriHorizontalLower f (logDeriv xiFunction) a b (T n))
        atTop (nhds 0) := by
  apply bombieriXiHorizontalPair_tendsto_zero_of_subquadratic_logDeriv
    f a b T (fun n ↦ C * (1 + Real.log (1 + |T n|) ^ 2)) hab
  · have hlim := one_add_log_sq_div_one_add_sq_tendsto_zero T hT
    simpa only [mul_div_assoc, mul_zero] using hlim.const_mul C
  · exact hxi

/-- The signed sum of the bottom and top terms occurring in `rectIntegral`
also vanishes once the two individual horizontal terms do. -/
theorem bombieriXiHorizontalDifference_tendsto_zero
    (f : BombieriTest) (a b : ℝ) (T : ℕ → ℝ)
    (hupper : Tendsto
      (fun n ↦ bombieriHorizontalUpper f (logDeriv xiFunction) a b (T n))
      atTop (nhds 0))
    (hlower : Tendsto
      (fun n ↦ bombieriHorizontalLower f (logDeriv xiFunction) a b (T n))
      atTop (nhds 0)) :
    Tendsto
      (fun n ↦ bombieriHorizontalLower f (logDeriv xiFunction) a b (T n) -
        bombieriHorizontalUpper f (logDeriv xiFunction) a b (T n))
      atTop (nhds 0) := by
  simpa using hlower.sub hupper


end

end ArithmeticHodge.Analysis.MultiplicativeWeil

