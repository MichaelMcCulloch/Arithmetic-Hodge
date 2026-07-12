import ArithmeticHodge.Analysis.YoshidaClippedPeriodicCore
import ArithmeticHodge.Analysis.YoshidaClippedCircleFaithful
import ArithmeticHodge.Analysis.YoshidaWeightedTailBounds
import ArithmeticHodge.Analysis.MultiplicativeWeilDilation

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ContDiff

namespace ArithmeticHodge.Analysis

noncomputable section

open ArithmeticHodge.Analysis.YoshidaWeightedTailBounds

/-!
# Restricted-support pullbacks in Yoshida's periodic core

This module periodizes globally smooth supported critical pullbacks and proves
that the normalized Bombieri class with multiplicative support ratio at most
two lands in Yoshida's fixed periodic source core.  It also proves that the
canonical finite low-mode subtraction leaves a periodic-core residual.

These are source-membership and carrier-closure results only.  They do not
prove Yoshida's infinite tail coercivity estimate, positivity of the local
critical form, or positivity of the Bombieri functional.
-/

private def periodicFinsum (a : ℝ) (H : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑ᶠ k : ℤ, H (x + (k : ℝ) * (2 * a))

private theorem locallyFinite_support_comp_add_intPeriod
    {a : ℝ} (ha : 0 < a) (H : ℝ → ℂ)
    (hsupport : ∀ x ∉ Set.Icc (-a) a, H x = 0) :
    LocallyFinite fun k : ℤ ↦
      Function.support (fun x : ℝ ↦ H (x + (k : ℝ) * (2 * a))) := by
  intro x
  let T : ℝ := 2 * a
  have hT : 0 < T := by dsimp [T]; positivity
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (a + |x| + 1) / T < N :=
    exists_nat_gt ((a + |x| + 1) / T)
  refine ⟨Set.Ioo (x - 1) (x + 1),
    Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
  refine (Set.finite_Icc (-(N : ℤ)) (N : ℤ)).subset ?_
  intro k hk
  rcases hk with ⟨y, hySupport, hy⟩
  have hyIcc : y + (k : ℝ) * T ∈ Set.Icc (-a) a := by
    by_contra hout
    exact hySupport (hsupport _ hout)
  have hbound : a + |x| + 1 < (N : ℝ) * T := by
    exact (div_lt_iff₀ hT).mp hN
  have hkUpperReal : (k : ℝ) < (N : ℝ) := by
    apply lt_of_mul_lt_mul_right (a := T) (b := (k : ℝ)) (c := (N : ℝ))
    · nlinarith [hyIcc.2, hy.1, neg_le_abs x]
    · exact hT.le
  have hkLowerReal : (-(N : ℤ) : ℝ) < (k : ℝ) := by
    apply lt_of_mul_lt_mul_right (a := T)
    · push_cast
      nlinarith [hyIcc.1, hy.2, le_abs_self x]
    · exact hT.le
  constructor
  · exact_mod_cast hkLowerReal.le
  · exact_mod_cast hkUpperReal.le

private theorem periodicFinsum_contDiff
    {a : ℝ} (ha : 0 < a) {H : ℝ → ℂ}
    (hH : ContDiff ℝ ∞ H)
    (hsupport : ∀ x ∉ Set.Icc (-a) a, H x = 0) :
    ContDiff ℝ ∞ (periodicFinsum a H) := by
  unfold periodicFinsum
  apply ContMDiff.contDiff
  apply contMDiff_finsum
  · intro k
    apply ContDiff.contMDiff
    exact hH.comp (by fun_prop)
  · exact locallyFinite_support_comp_add_intPeriod ha H hsupport

private theorem periodicFinsum_periodic
    {a : ℝ} (H : ℝ → ℂ) :
    Function.Periodic (periodicFinsum a H) (2 * a) := by
  intro x
  unfold periodicFinsum
  let e : ℤ ≃ ℤ := Equiv.addRight 1
  calc
    (∑ᶠ k : ℤ, H (x + 2 * a + (k : ℝ) * (2 * a))) =
        ∑ᶠ k : ℤ, H (x + ((e k : ℤ) : ℝ) * (2 * a)) := by
          apply finsum_congr
          intro k
          simp only [e, Equiv.coe_addRight]
          push_cast
          congr 1
          ring
    _ = ∑ᶠ k : ℤ, H (x + (k : ℝ) * (2 * a)) :=
      finsum_comp_equiv (M := ℂ) e
        (f := fun k : ℤ ↦ H (x + (k : ℝ) * (2 * a)))

private theorem periodicFinsum_eq_on_Icc
    {a : ℝ} (ha : 0 < a) {H : ℝ → ℂ}
    (hH : Continuous H)
    (hsupport : ∀ x ∉ Set.Icc (-a) a, H x = 0) :
    Set.EqOn (periodicFinsum a H) H (Set.Icc (-a) a) := by
  intro x hx
  have hHa : H a = 0 := by
    have hzero : Set.EqOn H (fun _ : ℝ ↦ (0 : ℂ)) (Set.Ioi a) := by
      intro y hy
      exact hsupport y (by simp only [Set.mem_Icc, not_and_or]; exact Or.inr (not_le.mpr hy))
    exact hzero.closure hH continuous_const (by simp)
  have hHnegA : H (-a) = 0 := by
    have hzero : Set.EqOn H (fun _ : ℝ ↦ (0 : ℂ)) (Set.Iio (-a)) := by
      intro y hy
      exact hsupport y (by simp only [Set.mem_Icc, not_and_or]; exact Or.inl (not_le.mpr hy))
    exact hzero.closure hH continuous_const (by simp)
  unfold periodicFinsum
  rw [finsum_eq_sum_of_support_subset _ (s := {0})]
  · simp
  · intro k hk
    simp only [Finset.coe_singleton, Set.mem_singleton_iff]
    by_contra hk0
    apply hk
    change H (x + (k : ℝ) * (2 * a)) = 0
    rcases lt_or_gt_of_ne hk0 with hkneg | hkpos
    · have hkLe : k ≤ -1 := by omega
      have hkLeReal : (k : ℝ) ≤ -1 := by exact_mod_cast hkLe
      let y := x + (k : ℝ) * (2 * a)
      by_cases hy : y ∈ Set.Icc (-a) a
      · have hyeq : y = -a := by
          dsimp only [y] at hy ⊢
          nlinarith [hx.2, hy.1]
        rw [show x + (k : ℝ) * (2 * a) = -a by exact hyeq, hHnegA]
      · exact hsupport y hy
    · have hkGe : 1 ≤ k := by omega
      have hkGeReal : (1 : ℝ) ≤ k := by exact_mod_cast hkGe
      let y := x + (k : ℝ) * (2 * a)
      by_cases hy : y ∈ Set.Icc (-a) a
      · have hyeq : y = a := by
          dsimp only [y] at hy ⊢
          nlinarith [hx.1, hy.2]
        rw [show x + (k : ℝ) * (2 * a) = a by exact hyeq, hHa]
      · exact hsupport y hy

/-- A globally smooth critical pullback supported on the clipped interval
belongs to Yoshida's periodic source core after clipping. -/
theorem yoshidaCriticalPullbackCrop_mem_periodicCore
    {a : ℝ} (ha : 0 < a)
    (f : MultiplicativeWeil.BombieriTest)
    (hf : YoshidaCriticalPullbackSupported a f) :
    yoshidaCriticalPullbackCropLinear a f ∈
      yoshidaClippedPeriodicCoreSubmodule a := by
  let H : ℝ → ℂ := f.logarithmicPullbackSchwartz (1 / 2)
  refine ⟨periodicFinsum a H,
    periodicFinsum_contDiff ha
      (f.logarithmicPullback_contDiff (1 / 2)) hf,
    periodicFinsum_periodic H, ?_⟩
  intro x hx
  have hperiod := periodicFinsum_eq_on_Icc ha
    (f.logarithmicPullback_contDiff (1 / 2)).continuous hf hx
  have hHfun : H = f.logarithmicPullback (1 / 2) := by
    funext y
    exact MultiplicativeWeil.BombieriTest.logarithmicPullbackSchwartz_apply _ _ _
  rw [hHfun]
  rw [hperiod, yoshidaCriticalPullbackCropLinear_apply_of_mem f hx]
  exact
    (MultiplicativeWeil.BombieriTest.logarithmicPullbackSchwartz_apply
      f (1 / 2) x).symm

private theorem yoshidaA_pos_bridge : 0 < yoshidaA := by
  rw [yoshidaA]
  exact div_pos (Real.log_pos (by norm_num)) (by norm_num)

/-- Multiplicative support ratio at most two becomes support in Yoshida's
fixed additive interval after normalized logarithmic centering. -/
theorem logCenteredNormalizedDilation_criticalPullbackSupported_yoshidaA
    (g : MultiplicativeWeil.BombieriTest) {l r : ℝ}
    (hl : 0 < l) (hlr : l ≤ r)
    (hsupport : tsupport g ⊆ Set.Icc l r)
    (hratio : r / l ≤ 2) :
    YoshidaCriticalPullbackSupported yoshidaA
      (MultiplicativeWeil.normalizedDilation
        (MultiplicativeWeil.logarithmicCenter l r)
        (MultiplicativeWeil.logarithmicCenter_pos l r) g) := by
  intro u hu
  apply
    MultiplicativeWeil.logCenteredNormalizedDilation_logarithmicPullback_eq_zero_outside
      g hl hlr hsupport
  intro huSmall
  apply hu
  have hwidth :
      MultiplicativeWeil.logarithmicHalfWidth l r ≤ yoshidaA := by
    simpa only [yoshidaA] using
      MultiplicativeWeil.logarithmicHalfWidth_le_log_two_half
        hl hlr hratio
  exact ⟨(neg_le_neg hwidth).trans huSmall.1,
    huSmall.2.trans hwidth⟩

/-- The actual normalized support-ratio-at-most-two Bombieri pullback lands
in Yoshida's fixed periodic source core. -/
theorem logCenteredNormalizedDilation_crop_mem_yoshidaPeriodicCore
    (g : MultiplicativeWeil.BombieriTest) {l r : ℝ}
    (hl : 0 < l) (hlr : l ≤ r)
    (hsupport : tsupport g ⊆ Set.Icc l r)
    (hratio : r / l ≤ 2) :
    yoshidaCriticalPullbackCropLinear yoshidaA
        (MultiplicativeWeil.normalizedDilation
          (MultiplicativeWeil.logarithmicCenter l r)
          (MultiplicativeWeil.logarithmicCenter_pos l r) g) ∈
      yoshidaClippedPeriodicCoreSubmodule yoshidaA :=
  yoshidaCriticalPullbackCrop_mem_periodicCore yoshidaA_pos_bridge _
    (logCenteredNormalizedDilation_criticalPullbackSupported_yoshidaA
      g hl hlr hsupport hratio)

/-- Every finite even low-mode combination remains in the periodic core. -/
theorem yoshidaClippedEvenLow_sum_mem_periodicCore
    {a : ℝ} (ha : 0 < a) (cEven : YoshidaEvenIndex → ℂ) :
    (∑ i, cEven i • yoshidaClippedEvenLowMode a i) ∈
      yoshidaClippedPeriodicCoreSubmodule a := by
  exact (yoshidaClippedPeriodicCoreSubmodule a).sum_mem fun i _ ↦
    (yoshidaClippedPeriodicCoreSubmodule a).smul_mem _
      (yoshidaClippedEvenLowMode_mem_periodicCore ha i)

/-- Every finite odd low-mode combination remains in the periodic core. -/
theorem yoshidaClippedOddLow_sum_mem_periodicCore
    {a : ℝ} (ha : 0 < a) (cOdd : YoshidaOddIndex → ℂ) :
    (∑ i, cOdd i • yoshidaClippedOddLowMode a i) ∈
      yoshidaClippedPeriodicCoreSubmodule a := by
  exact (yoshidaClippedPeriodicCoreSubmodule a).sum_mem fun i _ ↦
    (yoshidaClippedPeriodicCoreSubmodule a).smul_mem _
      (yoshidaClippedOddLowMode_mem_periodicCore ha i)

/-- Canonical subtraction of both certified low blocks preserves periodic-core
membership, so the residual remains in Yoshida's source carrier. -/
theorem yoshidaClipped_low_residual_mem_periodicCore
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a)
    (hf : f ∈ yoshidaClippedPeriodicCoreSubmodule a)
    (cEven : YoshidaEvenIndex → ℂ) (cOdd : YoshidaOddIndex → ℂ) :
    f - (∑ i, cEven i • yoshidaClippedEvenLowMode a i) -
        (∑ i, cOdd i • yoshidaClippedOddLowMode a i) ∈
      yoshidaClippedPeriodicCoreSubmodule a :=
  (yoshidaClippedPeriodicCoreSubmodule a).sub_mem
    ((yoshidaClippedPeriodicCoreSubmodule a).sub_mem hf
      (yoshidaClippedEvenLow_sum_mem_periodicCore ha cEven))
    (yoshidaClippedOddLow_sum_mem_periodicCore ha cOdd)

/-- The canonical low/tail decomposition of a periodic-core function can be
chosen with its clipped residual still inside the periodic source core. -/
theorem exists_yoshidaPeriodicCore_low_coefficients_residual_tails
    {a : ℝ} (ha : 0 < a) (f : YoshidaClippedSmooth a)
    (hf : f ∈ yoshidaClippedPeriodicCoreSubmodule a) :
    letI : Fact (0 < 2 * a) := ⟨by positivity⟩
    let F := YoshidaClippedCircleBridge.yoshidaClippedCircleL2 ha f
    ∃ cEven : YoshidaEvenIndex → ℂ,
      ∃ cOdd : YoshidaOddIndex → ℂ,
        ∃ residual : YoshidaClippedSmooth a,
          f =
              (∑ i, cEven i • yoshidaClippedEvenLowMode a i) +
                (∑ i, cOdd i • yoshidaClippedOddLowMode a i) +
                residual ∧
            residual ∈ yoshidaClippedPeriodicCoreSubmodule a ∧
            YoshidaClippedCircleBridge.yoshidaClippedCircleL2 ha residual =
              (evenTailRemainder (T := 2 * a) 199
                (evenPart_mem (T := 2 * a) F) : CircleL2 (T := 2 * a)) +
              (oddTailRemainder (T := 2 * a) 10
                (oddPart_mem (T := 2 * a) F) : CircleL2 (T := 2 * a)) := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  let F := YoshidaClippedCircleBridge.yoshidaClippedCircleL2 ha f
  obtain ⟨cEven, cOdd, residual, hdecomp, htail⟩ :=
    YoshidaClippedCircleFaithful.exists_yoshidaClipped_low_coefficients_residual_tails
      ha f
  refine ⟨cEven, cOdd, residual, hdecomp, ?_, htail⟩
  have hresidual :
      residual =
        f - (∑ i, cEven i • yoshidaClippedEvenLowMode a i) -
          (∑ i, cOdd i • yoshidaClippedOddLowMode a i) := by
    rw [hdecomp]
    abel
  rw [hresidual]
  exact yoshidaClipped_low_residual_mem_periodicCore
    ha f hf cEven cOdd

end

end ArithmeticHodge.Analysis
