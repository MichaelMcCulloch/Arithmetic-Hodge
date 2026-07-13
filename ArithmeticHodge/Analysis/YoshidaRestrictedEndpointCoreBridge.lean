import ArithmeticHodge.Analysis.MultiplicativeWeilDilation
import ArithmeticHodge.Analysis.YoshidaClippedPeriodicCore
import ArithmeticHodge.Analysis.YoshidaEndpointParameter

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ContDiff

namespace ArithmeticHodge.Analysis

open YoshidaEndpointHyperbolicBound

noncomputable section

/-!
# Certificate-free restricted-support periodization at the endpoint

This module isolates the structural part of restricted-support transport.
It periodizes a globally smooth supported critical pullback and places the
normalized support-ratio-at-most-two crop in the exact endpoint periodic core.
No Fourier cutoff, tail estimate, enclosure, or finite certificate is imported.
-/

private def endpointPeriodicFinsum (a : ℝ) (H : ℝ → ℂ) (x : ℝ) : ℂ :=
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

private theorem endpointPeriodicFinsum_contDiff
    {a : ℝ} (ha : 0 < a) {H : ℝ → ℂ}
    (hH : ContDiff ℝ ∞ H)
    (hsupport : ∀ x ∉ Set.Icc (-a) a, H x = 0) :
    ContDiff ℝ ∞ (endpointPeriodicFinsum a H) := by
  unfold endpointPeriodicFinsum
  apply ContMDiff.contDiff
  apply contMDiff_finsum
  · intro k
    apply ContDiff.contMDiff
    exact hH.comp (by fun_prop)
  · exact locallyFinite_support_comp_add_intPeriod ha H hsupport

private theorem endpointPeriodicFinsum_periodic
    {a : ℝ} (H : ℝ → ℂ) :
    Function.Periodic (endpointPeriodicFinsum a H) (2 * a) := by
  intro x
  unfold endpointPeriodicFinsum
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

private theorem endpointPeriodicFinsum_eq_on_Icc
    {a : ℝ} (ha : 0 < a) {H : ℝ → ℂ}
    (hH : Continuous H)
    (hsupport : ∀ x ∉ Set.Icc (-a) a, H x = 0) :
    Set.EqOn (endpointPeriodicFinsum a H) H (Set.Icc (-a) a) := by
  intro x hx
  have hHa : H a = 0 := by
    have hzero : Set.EqOn H (fun _ : ℝ ↦ (0 : ℂ)) (Set.Ioi a) := by
      intro y hy
      exact hsupport y (by
        simp only [Set.mem_Icc, not_and_or]
        exact Or.inr (not_le.mpr hy))
    exact hzero.closure hH continuous_const (by simp)
  have hHnegA : H (-a) = 0 := by
    have hzero : Set.EqOn H (fun _ : ℝ ↦ (0 : ℂ)) (Set.Iio (-a)) := by
      intro y hy
      exact hsupport y (by
        simp only [Set.mem_Icc, not_and_or]
        exact Or.inl (not_le.mpr hy))
    exact hzero.closure hH continuous_const (by simp)
  unfold endpointPeriodicFinsum
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
belongs to the periodic source core, without importing any spectral layer. -/
theorem yoshidaCriticalPullbackCrop_mem_periodicCore_structural
    {a : ℝ} (ha : 0 < a)
    (f : MultiplicativeWeil.BombieriTest)
    (hf : YoshidaCriticalPullbackSupported a f) :
    yoshidaCriticalPullbackCropLinear a f ∈
      yoshidaClippedPeriodicCoreSubmodule a := by
  let H : ℝ → ℂ := f.logarithmicPullbackSchwartz (1 / 2)
  refine ⟨endpointPeriodicFinsum a H,
    endpointPeriodicFinsum_contDiff ha
      (f.logarithmicPullback_contDiff (1 / 2)) hf,
    endpointPeriodicFinsum_periodic H, ?_⟩
  intro x hx
  have hperiod := endpointPeriodicFinsum_eq_on_Icc ha
    (f.logarithmicPullback_contDiff (1 / 2)).continuous hf hx
  have hHfun : H = f.logarithmicPullback (1 / 2) := by
    funext y
    exact MultiplicativeWeil.BombieriTest.logarithmicPullbackSchwartz_apply _ _ _
  rw [hHfun]
  rw [hperiod, yoshidaCriticalPullbackCropLinear_apply_of_mem f hx]
  exact
    (MultiplicativeWeil.BombieriTest.logarithmicPullbackSchwartz_apply
      f (1 / 2) x).symm

/-- Multiplicative support ratio at most two becomes support in the exact
endpoint interval after normalized logarithmic centering. -/
theorem logCenteredNormalizedDilation_criticalPullbackSupported_yoshidaEndpointA
    (g : MultiplicativeWeil.BombieriTest) {l r : ℝ}
    (hl : 0 < l) (hlr : l ≤ r)
    (hsupport : tsupport g ⊆ Set.Icc l r)
    (hratio : r / l ≤ 2) :
    YoshidaCriticalPullbackSupported yoshidaEndpointA
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
      MultiplicativeWeil.logarithmicHalfWidth l r ≤ yoshidaEndpointA := by
    simpa only [yoshidaEndpointA] using
      MultiplicativeWeil.logarithmicHalfWidth_le_log_two_half
        hl hlr hratio
  exact ⟨(neg_le_neg hwidth).trans huSmall.1,
    huSmall.2.trans hwidth⟩

/-- The normalized support-ratio-at-most-two Bombieri pullback lands in the
exact endpoint periodic core through a certificate-free dependency path. -/
theorem logCenteredNormalizedDilation_crop_mem_yoshidaEndpointPeriodicCore
    (g : MultiplicativeWeil.BombieriTest) {l r : ℝ}
    (hl : 0 < l) (hlr : l ≤ r)
    (hsupport : tsupport g ⊆ Set.Icc l r)
    (hratio : r / l ≤ 2) :
    yoshidaCriticalPullbackCropLinear yoshidaEndpointA
        (MultiplicativeWeil.normalizedDilation
          (MultiplicativeWeil.logarithmicCenter l r)
          (MultiplicativeWeil.logarithmicCenter_pos l r) g) ∈
      yoshidaClippedPeriodicCoreSubmodule yoshidaEndpointA :=
  yoshidaCriticalPullbackCrop_mem_periodicCore_structural yoshidaEndpointA_pos _
    (logCenteredNormalizedDilation_criticalPullbackSupported_yoshidaEndpointA
      g hl hlr hsupport hratio)

end

end ArithmeticHodge.Analysis
