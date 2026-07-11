import ArithmeticHodge.Analysis.YoshidaFourierModes

set_option autoImplicit false

noncomputable section

open AddCircle MeasureTheory Set
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace ArithmeticHodge.Analysis

variable {T : ℝ} [hT : Fact (0 < T)]

theorem fourierLp_sub_neg_mem_yoshidaOddLowSubmodule
    {k : ℕ} (hkpos : 1 ≤ k) (hkle : k ≤ 10) :
    fourierLp (T := T) 2 (k : ℤ) - fourierLp 2 (-(k : ℤ)) ∈
      yoshidaOddLowSubmodule (T := T) := by
  let i : YoshidaOddIndex := ⟨k - 1, by omega⟩
  have hi : i.1 + 1 = k := by
    dsimp [i]
    omega
  have hmode :
      yoshidaOddMode (T := T) k ∈
        yoshidaOddLowSubmodule (T := T) := by
    apply Submodule.subset_span
    exact ⟨i, by simp [yoshidaOddLowMode, hi]⟩
  let a : ℂ := -Complex.I / (Real.sqrt 2 : ℂ)
  let r : ℂ := ((Real.sqrt T)⁻¹ : ℂ)
  have ha : a ≠ 0 := by
    dsimp [a]
    exact div_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr (by positivity))
  have hr : r ≠ 0 := by
    dsimp [r]
    exact inv_ne_zero
      (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hT.out).ne')
  have har : a * r ≠ 0 := mul_ne_zero ha hr
  have heq :
      (a * r)⁻¹ • yoshidaOddMode (T := T) k =
        fourierLp 2 (k : ℤ) - fourierLp 2 (-(k : ℤ)) := by
    rw [yoshidaOddMode, lebesgueNormalizedExponential,
      lebesgueNormalizedExponential]
    change (a * r)⁻¹ •
      (a • (r • fourierLp 2 (k : ℤ) -
        r • fourierLp 2 (-(k : ℤ)))) = _
    rw [← smul_sub]
    simp only [smul_smul]
    have hscalar : (a * r)⁻¹ * (a * r) = 1 :=
      inv_mul_cancel₀ har
    rw [hscalar, one_smul]
  rw [← heq]
  exact Submodule.smul_mem _ _ hmode

theorem fourierLp_sub_reflected_mem_yoshidaOddLowSubmodule
    {n : ℤ} (hn : n ∈ Finset.Icc (-(10 : ℤ)) 10) :
    fourierLp (T := T) 2 n - fourierLp 2 (-n) ∈
      yoshidaOddLowSubmodule (T := T) := by
  rcases lt_trichotomy n 0 with hnneg | hnzero | hnpos
  · let k := (-n).toNat
    have hkcast : (k : ℤ) = -n := by
      exact Int.toNat_of_nonneg (neg_nonneg.mpr hnneg.le)
    have hkpos : 1 ≤ k := by omega
    have hkle : k ≤ 10 := by
      simp only [Finset.mem_Icc] at hn
      omega
    have hraw := fourierLp_sub_neg_mem_yoshidaOddLowSubmodule
      (T := T) hkpos hkle
    have hnegraw :=
      Submodule.neg_mem (yoshidaOddLowSubmodule (T := T)) hraw
    convert hnegraw using 1
    simp [hkcast]
  · subst n
    simp
  · let k := n.toNat
    have hkcast : (k : ℤ) = n := Int.toNat_of_nonneg hnpos.le
    have hkpos : 1 ≤ k := by omega
    have hkle : k ≤ 10 := by
      simp only [Finset.mem_Icc] at hn
      omega
    simpa only [hkcast] using
      (fourierLp_sub_neg_mem_yoshidaOddLowSubmodule
        (T := T) hkpos hkle)

theorem fourierLp_add_neg_mem_yoshidaEvenLowSubmodule
    {k : ℕ} (hkpos : 1 ≤ k) (hkle : k ≤ 199) :
    fourierLp (T := T) 2 (k : ℤ) + fourierLp 2 (-(k : ℤ)) ∈
      yoshidaEvenLowSubmodule (T := T) := by
  let i : YoshidaEvenIndex := ⟨k, by omega⟩
  have hi : i.1 = k := rfl
  have hik : i.1 ≠ 0 := by omega
  have hmode :
      yoshidaEvenMode (T := T) k ∈
        yoshidaEvenLowSubmodule (T := T) := by
    apply Submodule.subset_span
    refine ⟨i, ?_⟩
    change yoshidaEvenLowMode (T := T) i =
      yoshidaEvenMode (T := T) k
    rw [yoshidaEvenLowMode, if_neg hik, hi]
  let b : ℂ := (Real.sqrt 2 : ℂ)⁻¹
  let r : ℂ := ((Real.sqrt T)⁻¹ : ℂ)
  have hb : b ≠ 0 := by
    dsimp [b]
    exact inv_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity))
  have hr : r ≠ 0 := by
    dsimp [r]
    exact inv_ne_zero
      (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hT.out).ne')
  have hbr : b * r ≠ 0 := mul_ne_zero hb hr
  have heq :
      (b * r)⁻¹ • yoshidaEvenMode (T := T) k =
        fourierLp 2 (k : ℤ) + fourierLp 2 (-(k : ℤ)) := by
    rw [yoshidaEvenMode, lebesgueNormalizedExponential,
      lebesgueNormalizedExponential]
    change (b * r)⁻¹ •
      (b • (r • fourierLp 2 (k : ℤ) +
        r • fourierLp 2 (-(k : ℤ)))) = _
    rw [← smul_add]
    simp only [smul_smul]
    have hscalar : (b * r)⁻¹ * (b * r) = 1 :=
      inv_mul_cancel₀ hbr
    rw [hscalar, one_smul]
  rw [← heq]
  exact Submodule.smul_mem _ _ hmode

theorem fourierLp_zero_add_zero_mem_yoshidaEvenLowSubmodule :
    fourierLp (T := T) 2 0 + fourierLp 2 0 ∈
      yoshidaEvenLowSubmodule (T := T) := by
  let i : YoshidaEvenIndex := ⟨0, by omega⟩
  have hmode :
      yoshidaEvenZeroMode (T := T) ∈
        yoshidaEvenLowSubmodule (T := T) := by
    apply Submodule.subset_span
    refine ⟨i, ?_⟩
    change yoshidaEvenLowMode (T := T) i =
      yoshidaEvenZeroMode (T := T)
    rw [yoshidaEvenLowMode, if_pos rfl]
  let r : ℂ := ((Real.sqrt T)⁻¹ : ℂ)
  have hr : r ≠ 0 := by
    dsimp [r]
    exact inv_ne_zero
      (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hT.out).ne')
  have heq :
      r⁻¹ • yoshidaEvenZeroMode (T := T) = fourierLp 2 0 := by
    rw [yoshidaEvenZeroMode, lebesgueNormalizedExponential]
    change r⁻¹ • (r • fourierLp 2 0) = _
    simp [hr]
  have he0 :
      fourierLp (T := T) 2 0 ∈
        yoshidaEvenLowSubmodule (T := T) := by
    rw [← heq]
    exact Submodule.smul_mem _ _ hmode
  exact Submodule.add_mem _ he0 he0

theorem fourierLp_add_reflected_mem_yoshidaEvenLowSubmodule
    {n : ℤ} (hn : n ∈ Finset.Icc (-(199 : ℤ)) 199) :
    fourierLp (T := T) 2 n + fourierLp 2 (-n) ∈
      yoshidaEvenLowSubmodule (T := T) := by
  rcases lt_trichotomy n 0 with hnneg | hnzero | hnpos
  · let k := (-n).toNat
    have hkcast : (k : ℤ) = -n :=
      Int.toNat_of_nonneg (neg_nonneg.mpr hnneg.le)
    have hkpos : 1 ≤ k := by omega
    have hkle : k ≤ 199 := by
      simp only [Finset.mem_Icc] at hn
      omega
    have hraw := fourierLp_add_neg_mem_yoshidaEvenLowSubmodule
      (T := T) hkpos hkle
    convert hraw using 1
    simp [hkcast, add_comm]
  · subst n
    simpa using
      fourierLp_zero_add_zero_mem_yoshidaEvenLowSubmodule (T := T)
  · let k := n.toNat
    have hkcast : (k : ℤ) = n := Int.toNat_of_nonneg hnpos.le
    have hkpos : 1 ≤ k := by omega
    have hkle : k ≤ 199 := by
      simp only [Finset.mem_Icc] at hn
      omega
    simpa only [hkcast] using
      (fourierLp_add_neg_mem_yoshidaEvenLowSubmodule
        (T := T) hkpos hkle)

theorem oddPart_lowFourierProjection_ten_mem_yoshidaOddLowSubmodule
    (f : CircleL2 (T := T)) :
    oddPart (T := T) (lowFourierProjection (T := T) 10 f) ∈
      yoshidaOddLowSubmodule (T := T) := by
  change oddPartCLM (T := T) (lowFourierProjection (T := T) 10 f) ∈
    yoshidaOddLowSubmodule (T := T)
  rw [lowFourierProjection, map_sum]
  exact Submodule.sum_mem _ fun n _ ↦ by
    rw [map_smul, oddPartCLM_apply, oddPart, reflectionL2_fourierLp]
    exact Submodule.smul_mem _ _
      (Submodule.smul_mem _ _
        (fourierLp_sub_reflected_mem_yoshidaOddLowSubmodule n.property))

theorem evenPart_lowFourierProjection_oneNinetyNine_mem_yoshidaEvenLowSubmodule
    (f : CircleL2 (T := T)) :
    evenPart (T := T) (lowFourierProjection (T := T) 199 f) ∈
      yoshidaEvenLowSubmodule (T := T) := by
  change evenPartCLM (T := T) (lowFourierProjection (T := T) 199 f) ∈
    yoshidaEvenLowSubmodule (T := T)
  rw [lowFourierProjection, map_sum]
  exact Submodule.sum_mem _ fun n _ ↦ by
    rw [map_smul, evenPartCLM_apply, evenPart, reflectionL2_fourierLp]
    exact Submodule.smul_mem _ _
      (Submodule.smul_mem _ _
        (fourierLp_add_reflected_mem_yoshidaEvenLowSubmodule n.property))

def evenLowFourierProjection
    (N : ℕ) (f : CircleL2 (T := T)) : CircleL2 (T := T) :=
  evenPart (T := T) (lowFourierProjection (T := T) N f)

def oddLowFourierProjection
    (N : ℕ) (f : CircleL2 (T := T)) : CircleL2 (T := T) :=
  oddPart (T := T) (lowFourierProjection (T := T) N f)

theorem reflectionL2_lowFourierProjection_mem_finiteFourierSubmodule
    (N : ℕ) (f : CircleL2 (T := T)) :
    reflectionL2 (T := T) (lowFourierProjection (T := T) N f) ∈
      finiteFourierSubmodule (T := T) N := by
  rw [lowFourierProjection, map_sum]
  exact Submodule.sum_mem _ fun n _ ↦ by
    rw [map_smul, reflectionL2_fourierLp]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span
        ⟨⟨-(n : ℤ), neg_mem_lowIndex n.property⟩, rfl⟩)

theorem evenLowFourierProjection_mem_finiteFourierSubmodule
    (N : ℕ) (f : CircleL2 (T := T)) :
    evenLowFourierProjection (T := T) N f ∈
      finiteFourierSubmodule (T := T) N := by
  rw [evenLowFourierProjection, evenPart]
  exact Submodule.smul_mem _ _
    (Submodule.add_mem _
      (lowFourierProjection_mem_finiteFourierSubmodule N f)
      (reflectionL2_lowFourierProjection_mem_finiteFourierSubmodule N f))

theorem oddLowFourierProjection_mem_finiteFourierSubmodule
    (N : ℕ) (f : CircleL2 (T := T)) :
    oddLowFourierProjection (T := T) N f ∈
      finiteFourierSubmodule (T := T) N := by
  rw [oddLowFourierProjection, oddPart]
  exact Submodule.smul_mem _ _
    (Submodule.sub_mem _
      (lowFourierProjection_mem_finiteFourierSubmodule N f)
      (reflectionL2_lowFourierProjection_mem_finiteFourierSubmodule N f))

theorem oddLowFourierProjection_ten_mem_yoshidaOddLowSubmodule
    (f : CircleL2 (T := T)) :
    oddLowFourierProjection (T := T) 10 f ∈
      yoshidaOddLowSubmodule (T := T) :=
  oddPart_lowFourierProjection_ten_mem_yoshidaOddLowSubmodule f

theorem parityFinite_le_yoshidaOddLowSubmodule :
    oddL2Submodule (T := T) ⊓ finiteFourierSubmodule (T := T) 10 ≤
      yoshidaOddLowSubmodule (T := T) := by
  intro f hf
  have hlow :=
    oddLowFourierProjection_ten_mem_yoshidaOddLowSubmodule (T := T) f
  rw [oddLowFourierProjection,
    lowFourierProjection_eq_self_of_mem_finiteFourierSubmodule 10 hf.2,
    oddPart_eq_self_of_mem hf.1] at hlow
  exact hlow

theorem yoshidaOddLowSubmodule_eq_parity_finite :
    yoshidaOddLowSubmodule (T := T) =
      oddL2Submodule (T := T) ⊓ finiteFourierSubmodule (T := T) 10 :=
  le_antisymm (yoshidaOddLowSubmodule_le_parity_finite (T := T))
    (parityFinite_le_yoshidaOddLowSubmodule (T := T))

theorem evenLowFourierProjection_oneNinetyNine_mem_yoshidaEvenLowSubmodule
    (f : CircleL2 (T := T)) :
    evenLowFourierProjection (T := T) 199 f ∈
      yoshidaEvenLowSubmodule (T := T) :=
  evenPart_lowFourierProjection_oneNinetyNine_mem_yoshidaEvenLowSubmodule f

theorem parityFinite_le_yoshidaEvenLowSubmodule :
    evenL2Submodule (T := T) ⊓ finiteFourierSubmodule (T := T) 199 ≤
      yoshidaEvenLowSubmodule (T := T) := by
  intro f hf
  have hlow :=
    evenLowFourierProjection_oneNinetyNine_mem_yoshidaEvenLowSubmodule
      (T := T) f
  rw [evenLowFourierProjection,
    lowFourierProjection_eq_self_of_mem_finiteFourierSubmodule 199 hf.2,
    evenPart_eq_self_of_mem hf.1] at hlow
  exact hlow

theorem yoshidaEvenLowSubmodule_eq_parity_finite :
    yoshidaEvenLowSubmodule (T := T) =
      evenL2Submodule (T := T) ⊓ finiteFourierSubmodule (T := T) 199 :=
  le_antisymm (yoshidaEvenLowSubmodule_le_parity_finite (T := T))
    (parityFinite_le_yoshidaEvenLowSubmodule (T := T))

theorem fourierCoeff_evenLowFourierProjection
    (N : ℕ) {f : CircleL2 (T := T)}
    (hf : f ∈ evenL2Submodule (T := T)) (m : LowIndex N) :
    fourierCoeff (evenLowFourierProjection (T := T) N f) (m : ℤ) =
      fourierCoeff f m := by
  rw [evenLowFourierProjection, fourierCoeff_evenPart,
    fourierCoeff_lowFourierProjection N f m,
    fourierCoeff_lowFourierProjection N f
      ⟨-(m : ℤ), neg_mem_lowIndex m.property⟩,
    fourierCoeff_even_of_mem hf]
  module

theorem fourierCoeff_oddLowFourierProjection
    (N : ℕ) {f : CircleL2 (T := T)}
    (hf : f ∈ oddL2Submodule (T := T)) (m : LowIndex N) :
    fourierCoeff (oddLowFourierProjection (T := T) N f) (m : ℤ) =
      fourierCoeff f m := by
  rw [oddLowFourierProjection, fourierCoeff_oddPart,
    fourierCoeff_lowFourierProjection N f m,
    fourierCoeff_lowFourierProjection N f
      ⟨-(m : ℤ), neg_mem_lowIndex m.property⟩,
    fourierCoeff_odd_of_mem hf]
  module

theorem evenLowFourierProjection_mem_even
    (N : ℕ) (f : CircleL2 (T := T)) :
    evenLowFourierProjection (T := T) N f ∈
      evenL2Submodule (T := T) :=
  evenPart_mem _

theorem oddLowFourierProjection_mem_odd
    (N : ℕ) (f : CircleL2 (T := T)) :
    oddLowFourierProjection (T := T) N f ∈
      oddL2Submodule (T := T) :=
  oddPart_mem _

theorem sub_evenLowFourierProjection_mem_tail
    (N : ℕ) {f : CircleL2 (T := T)}
    (hf : f ∈ evenL2Submodule (T := T)) :
    f - evenLowFourierProjection (T := T) N f ∈
      evenFourierTailSubmodule (T := T) N := by
  constructor
  · exact Submodule.sub_mem _ hf
      (evenLowFourierProjection_mem_even N f)
  · change f - evenLowFourierProjection (T := T) N f ∈
      fourierTailSubmodule (T := T) N
    rw [mem_fourierTailSubmodule_iff]
    intro n hn
    rw [← fourierCoeffCLM_apply (T := T) n, map_sub,
      fourierCoeffCLM_apply, fourierCoeffCLM_apply,
      fourierCoeff_evenLowFourierProjection N hf ⟨n, hn⟩, sub_self]

theorem sub_oddLowFourierProjection_mem_tail
    (N : ℕ) {f : CircleL2 (T := T)}
    (hf : f ∈ oddL2Submodule (T := T)) :
    f - oddLowFourierProjection (T := T) N f ∈
      oddFourierTailSubmodule (T := T) N := by
  constructor
  · exact Submodule.sub_mem _ hf
      (oddLowFourierProjection_mem_odd N f)
  · change f - oddLowFourierProjection (T := T) N f ∈
      fourierTailSubmodule (T := T) N
    rw [mem_fourierTailSubmodule_iff]
    intro n hn
    rw [← fourierCoeffCLM_apply (T := T) n, map_sub,
      fourierCoeffCLM_apply, fourierCoeffCLM_apply,
      fourierCoeff_oddLowFourierProjection N hf ⟨n, hn⟩, sub_self]

def evenTailRemainder
    (N : ℕ) {f : CircleL2 (T := T)}
    (hf : f ∈ evenL2Submodule (T := T)) :
    evenFourierTailSubmodule (T := T) N :=
  ⟨f - evenLowFourierProjection (T := T) N f,
    sub_evenLowFourierProjection_mem_tail N hf⟩

def oddTailRemainder
    (N : ℕ) {f : CircleL2 (T := T)}
    (hf : f ∈ oddL2Submodule (T := T)) :
    oddFourierTailSubmodule (T := T) N :=
  ⟨f - oddLowFourierProjection (T := T) N f,
    sub_oddLowFourierProjection_mem_tail N hf⟩

def yoshidaOddLowComponent (f : CircleL2 (T := T)) :
    yoshidaOddLowSubmodule (T := T) :=
  ⟨oddLowFourierProjection (T := T) 10 f,
    oddLowFourierProjection_ten_mem_yoshidaOddLowSubmodule f⟩

def yoshidaEvenLowComponent (f : CircleL2 (T := T)) :
    yoshidaEvenLowSubmodule (T := T) :=
  ⟨evenLowFourierProjection (T := T) 199 f,
    evenLowFourierProjection_oneNinetyNine_mem_yoshidaEvenLowSubmodule f⟩

theorem even_finite_low_add_tail
    (N : ℕ) {f : CircleL2 (T := T)}
    (hf : f ∈ evenL2Submodule (T := T)) :
    f = evenLowFourierProjection (T := T) N f +
      (evenTailRemainder (T := T) N hf : CircleL2 (T := T)) := by
  change f = evenLowFourierProjection (T := T) N f +
    (f - evenLowFourierProjection (T := T) N f)
  abel

theorem odd_finite_low_add_tail
    (N : ℕ) {f : CircleL2 (T := T)}
    (hf : f ∈ oddL2Submodule (T := T)) :
    f = oddLowFourierProjection (T := T) N f +
      (oddTailRemainder (T := T) N hf : CircleL2 (T := T)) := by
  change f = oddLowFourierProjection (T := T) N f +
    (f - oddLowFourierProjection (T := T) N f)
  abel

theorem yoshida_odd_ten_modeSpan_add_tail
    {f : CircleL2 (T := T)}
    (hf : f ∈ oddL2Submodule (T := T)) :
    f = (yoshidaOddLowComponent (T := T) f : CircleL2 (T := T)) +
      (oddTailRemainder (T := T) 10 hf : CircleL2 (T := T)) :=
  odd_finite_low_add_tail 10 hf

theorem yoshida_even_twoHundred_modeSpan_add_tail
    {f : CircleL2 (T := T)}
    (hf : f ∈ evenL2Submodule (T := T)) :
    f = (yoshidaEvenLowComponent (T := T) f : CircleL2 (T := T)) +
      (evenTailRemainder (T := T) 199 hf : CircleL2 (T := T)) :=
  even_finite_low_add_tail 199 hf

theorem exists_yoshidaOddLowMode_coefficients
    (f : CircleL2 (T := T)) :
    ∃ c : YoshidaOddIndex → ℂ,
      ∑ i, c i • yoshidaOddLowMode (T := T) i =
        (yoshidaOddLowComponent (T := T) f : CircleL2 (T := T)) := by
  exact (Submodule.mem_span_range_iff_exists_fun ℂ).mp
    (yoshidaOddLowComponent (T := T) f).property

theorem exists_yoshidaEvenLowMode_coefficients
    (f : CircleL2 (T := T)) :
    ∃ c : YoshidaEvenIndex → ℂ,
      ∑ i, c i • yoshidaEvenLowMode (T := T) i =
        (yoshidaEvenLowComponent (T := T) f : CircleL2 (T := T)) := by
  exact (Submodule.mem_span_range_iff_exists_fun ℂ).mp
    (yoshidaEvenLowComponent (T := T) f).property

theorem exists_yoshida_odd_ten_coefficients_add_tail
    {f : CircleL2 (T := T)}
    (hf : f ∈ oddL2Submodule (T := T)) :
    ∃ c : YoshidaOddIndex → ℂ,
      f = (∑ i, c i • yoshidaOddLowMode (T := T) i) +
        (oddTailRemainder (T := T) 10 hf : CircleL2 (T := T)) := by
  obtain ⟨c, hc⟩ :=
    exists_yoshidaOddLowMode_coefficients (T := T) f
  refine ⟨c, ?_⟩
  rw [hc]
  exact yoshida_odd_ten_modeSpan_add_tail hf

theorem exists_yoshida_even_twoHundred_coefficients_add_tail
    {f : CircleL2 (T := T)}
    (hf : f ∈ evenL2Submodule (T := T)) :
    ∃ c : YoshidaEvenIndex → ℂ,
      f = (∑ i, c i • yoshidaEvenLowMode (T := T) i) +
        (evenTailRemainder (T := T) 199 hf : CircleL2 (T := T)) := by
  obtain ⟨c, hc⟩ :=
    exists_yoshidaEvenLowMode_coefficients (T := T) f
  refine ⟨c, ?_⟩
  rw [hc]
  exact yoshida_even_twoHundred_modeSpan_add_tail hf


end ArithmeticHodge.Analysis
