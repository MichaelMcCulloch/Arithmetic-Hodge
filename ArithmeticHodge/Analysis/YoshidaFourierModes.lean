import ArithmeticHodge.Analysis.CenteredAddCircleFourierParity

set_option autoImplicit false

noncomputable section

open AddCircle MeasureTheory Set
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace ArithmeticHodge.Analysis

variable {T : ℝ} [hT : Fact (0 < T)]

/-- `T^(-1/2)` times the probability-Haar orthonormal exponential. Its
Lebesgue `L²` norm is one because `volume = T • haarAddCircle`. -/
def lebesgueNormalizedExponential (n : ℤ) : CircleL2 (T := T) :=
  ((Real.sqrt T)⁻¹ : ℂ) • fourierLp 2 n

@[simp]
theorem reflectionL2_lebesgueNormalizedExponential (n : ℤ) :
    reflectionL2 (T := T) (lebesgueNormalizedExponential (T := T) n) =
      lebesgueNormalizedExponential (T := T) (-n) := by
  simp [lebesgueNormalizedExponential]

/-- The square of the volume/Lebesgue `L²` norm, expressed in terms of the
probability-Haar norm carried by `CircleL2`. -/
def lebesgueNormSq (f : CircleL2 (T := T)) : ℝ :=
  T * ‖f‖ ^ 2

theorem integral_norm_sq_volume_eq_lebesgueNormSq (f : CircleL2 (T := T)) :
    ∫ x : AddCircle T, ‖f x‖ ^ 2 = lebesgueNormSq (T := T) f := by
  have hhaar : ∫ x : AddCircle T, ‖f x‖ ^ 2 ∂haarAddCircle = ‖f‖ ^ 2 := by
    have h := congr_arg RCLike.re
      (@L2.inner_def (AddCircle T) ℂ ℂ _ _ _ _ _ f f)
    rw [← integral_re] at h
    · simpa only [← norm_sq_eq_re_inner] using h.symm
    · exact L2.integrable_inner f f
  rw [AddCircle.volume_eq_smul_haarAddCircle, integral_smul_measure,
    ENNReal.toReal_ofReal hT.out.le, hhaar]
  rfl

theorem lebesgueNormSq_lebesgueNormalizedExponential (n : ℤ) :
    lebesgueNormSq (T := T) (lebesgueNormalizedExponential (T := T) n) = 1 := by
  have hTpos : 0 < T := hT.out
  have hsqrt : Real.sqrt T ≠ 0 := (Real.sqrt_pos.2 hTpos).ne'
  rw [lebesgueNormSq, lebesgueNormalizedExponential, norm_smul,
    (orthonormal_fourier (T := T)).1 n]
  have hnorm : ‖((Real.sqrt T)⁻¹ : ℂ)‖ = (Real.sqrt T)⁻¹ := by
    simp [Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.2 hTpos)]
  rw [mul_one, hnorm]
  field_simp
  exact (Real.sq_sqrt hTpos.le).symm

theorem integral_norm_sq_volume_lebesgueNormalizedExponential (n : ℤ) :
    ∫ x : AddCircle T, ‖(lebesgueNormalizedExponential (T := T) n) x‖ ^ 2 = 1 := by
  rw [integral_norm_sq_volume_eq_lebesgueNormSq,
    lebesgueNormSq_lebesgueNormalizedExponential]

/-- Yoshida's Lebesgue-normalized odd (sine) mode. -/
def yoshidaOddMode (n : ℕ) : CircleL2 (T := T) :=
  (-Complex.I / (Real.sqrt 2 : ℂ)) •
    (lebesgueNormalizedExponential (T := T) (n : ℤ) -
      lebesgueNormalizedExponential (T := T) (-(n : ℤ)))

/-- Yoshida's Lebesgue-normalized positive-frequency even (cosine) mode. -/
def yoshidaEvenMode (n : ℕ) : CircleL2 (T := T) :=
  ((Real.sqrt 2 : ℂ)⁻¹) •
    (lebesgueNormalizedExponential (T := T) (n : ℤ) +
      lebesgueNormalizedExponential (T := T) (-(n : ℤ)))

/-- Yoshida's zero-frequency even mode has no `sqrt 2` factor. -/
def yoshidaEvenZeroMode : CircleL2 (T := T) :=
  lebesgueNormalizedExponential (T := T) 0

theorem yoshidaOddMode_mem_odd (n : ℕ) :
    yoshidaOddMode (T := T) n ∈ oddL2Submodule (T := T) := by
  rw [mem_oddL2Submodule_iff]
  simp [yoshidaOddMode]
  module

theorem yoshidaEvenMode_mem_even (n : ℕ) :
    yoshidaEvenMode (T := T) n ∈ evenL2Submodule (T := T) := by
  rw [mem_evenL2Submodule_iff]
  simp [yoshidaEvenMode, add_comm]

theorem yoshidaEvenZeroMode_mem_even :
    yoshidaEvenZeroMode (T := T) ∈ evenL2Submodule (T := T) := by
  rw [mem_evenL2Submodule_iff]
  simp [yoshidaEvenZeroMode]

theorem inner_lebesgueNormalizedExponential_eq_zero {m n : ℤ} (hmn : m ≠ n) :
    ⟪lebesgueNormalizedExponential (T := T) m,
      lebesgueNormalizedExponential (T := T) n⟫_ℂ = 0 := by
  rw [lebesgueNormalizedExponential, lebesgueNormalizedExponential,
    inner_smul_left, inner_smul_right, (orthonormal_fourier (T := T)).2 hmn]
  simp

theorem lebesgueNormSq_yoshidaOddMode {n : ℕ} (hn : n ≠ 0) :
    lebesgueNormSq (T := T) (yoshidaOddMode (T := T) n) = 1 := by
  have hTpos : 0 < T := hT.out
  have hsqrtT : Real.sqrt T ≠ 0 := (Real.sqrt_pos.2 hTpos).ne'
  have hsqrtTwo : Real.sqrt 2 ≠ 0 := by positivity
  have hfreq : (n : ℤ) ≠ -(n : ℤ) := by omega
  have horth := inner_lebesgueNormalizedExponential_eq_zero (T := T) hfreq
  rw [lebesgueNormSq, yoshidaOddMode, norm_smul, mul_pow,
    norm_sub_sq (𝕜 := ℂ), horth]
  simp only [map_zero, mul_zero, sub_zero,
    lebesgueNormalizedExponential, norm_smul,
    (orthonormal_fourier (T := T)).1]
  have hnormT : ‖((Real.sqrt T)⁻¹ : ℂ)‖ = (Real.sqrt T)⁻¹ := by
    simp [Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.2 hTpos)]
  have hnormTwo : ‖(-Complex.I / (Real.sqrt 2 : ℂ))‖ = (Real.sqrt 2)⁻¹ := by
    rw [norm_div, norm_neg, Complex.norm_I]
    simp [Real.norm_eq_abs,
      abs_of_pos (Real.sqrt_pos.2 (show (0 : ℝ) < 2 by norm_num))]
  rw [hnormT, hnormTwo]
  field_simp
  nlinarith [Real.sq_sqrt hTpos.le,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem lebesgueNormSq_yoshidaEvenMode {n : ℕ} (hn : n ≠ 0) :
    lebesgueNormSq (T := T) (yoshidaEvenMode (T := T) n) = 1 := by
  have hTpos : 0 < T := hT.out
  have hsqrtT : Real.sqrt T ≠ 0 := (Real.sqrt_pos.2 hTpos).ne'
  have hsqrtTwo : Real.sqrt 2 ≠ 0 := by positivity
  have hfreq : (n : ℤ) ≠ -(n : ℤ) := by omega
  have horth := inner_lebesgueNormalizedExponential_eq_zero (T := T) hfreq
  rw [lebesgueNormSq, yoshidaEvenMode, norm_smul, mul_pow,
    norm_add_sq (𝕜 := ℂ), horth]
  simp only [map_zero, mul_zero, add_zero,
    lebesgueNormalizedExponential, norm_smul,
    (orthonormal_fourier (T := T)).1]
  have hnormT : ‖((Real.sqrt T)⁻¹ : ℂ)‖ = (Real.sqrt T)⁻¹ := by
    simp [Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.2 hTpos)]
  have hnormTwo : ‖((Real.sqrt 2 : ℂ)⁻¹)‖ = (Real.sqrt 2)⁻¹ := by
    simp [Real.norm_eq_abs,
      abs_of_pos (Real.sqrt_pos.2 (show (0 : ℝ) < 2 by norm_num))]
  rw [hnormT, hnormTwo]
  field_simp
  nlinarith [Real.sq_sqrt hTpos.le,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem lebesgueNormSq_yoshidaEvenZeroMode :
    lebesgueNormSq (T := T) (yoshidaEvenZeroMode (T := T)) = 1 := by
  exact lebesgueNormSq_lebesgueNormalizedExponential 0

theorem fourierCoeff_lebesgueNormalizedExponential (m n : ℤ) :
    fourierCoeff (lebesgueNormalizedExponential (T := T) n) m =
      ((Real.sqrt T)⁻¹ : ℂ) • (if m = n then 1 else 0) := by
  calc
    fourierCoeff (lebesgueNormalizedExponential (T := T) n) m =
        fourierCoeffCLM (T := T) m
          (lebesgueNormalizedExponential (T := T) n) := by
      rw [fourierCoeffCLM_apply]
    _ = ((Real.sqrt T)⁻¹ : ℂ) •
        fourierCoeffCLM (T := T) m (fourierLp 2 n) := by
      rw [lebesgueNormalizedExponential, map_smul]
    _ = ((Real.sqrt T)⁻¹ : ℂ) • (if m = n then 1 else 0) := by
      rw [fourierCoeffCLM_apply, fourierCoeff_fourierLp]

theorem fourierCoeff_yoshidaOddMode (m : ℤ) (n : ℕ) :
    fourierCoeff (yoshidaOddMode (T := T) n) m =
      (-Complex.I / (Real.sqrt 2 : ℂ)) •
        (((Real.sqrt T)⁻¹ : ℂ) • (if m = (n : ℤ) then 1 else 0) -
          ((Real.sqrt T)⁻¹ : ℂ) • (if m = -(n : ℤ) then 1 else 0)) := by
  calc
    fourierCoeff (yoshidaOddMode (T := T) n) m =
        fourierCoeffCLM (T := T) m (yoshidaOddMode (T := T) n) := by
      rw [fourierCoeffCLM_apply]
    _ = (-Complex.I / (Real.sqrt 2 : ℂ)) •
        (fourierCoeffCLM (T := T) m
            (lebesgueNormalizedExponential (T := T) (n : ℤ)) -
          fourierCoeffCLM (T := T) m
            (lebesgueNormalizedExponential (T := T) (-(n : ℤ)))) := by
      rw [yoshidaOddMode, map_smul, map_sub]
    _ = _ := by
      rw [fourierCoeffCLM_apply, fourierCoeffCLM_apply,
        fourierCoeff_lebesgueNormalizedExponential,
        fourierCoeff_lebesgueNormalizedExponential]

theorem fourierCoeff_yoshidaEvenMode (m : ℤ) (n : ℕ) :
    fourierCoeff (yoshidaEvenMode (T := T) n) m =
      ((Real.sqrt 2 : ℂ)⁻¹) •
        (((Real.sqrt T)⁻¹ : ℂ) • (if m = (n : ℤ) then 1 else 0) +
          ((Real.sqrt T)⁻¹ : ℂ) • (if m = -(n : ℤ) then 1 else 0)) := by
  calc
    fourierCoeff (yoshidaEvenMode (T := T) n) m =
        fourierCoeffCLM (T := T) m (yoshidaEvenMode (T := T) n) := by
      rw [fourierCoeffCLM_apply]
    _ = ((Real.sqrt 2 : ℂ)⁻¹) •
        (fourierCoeffCLM (T := T) m
            (lebesgueNormalizedExponential (T := T) (n : ℤ)) +
          fourierCoeffCLM (T := T) m
            (lebesgueNormalizedExponential (T := T) (-(n : ℤ)))) := by
      rw [yoshidaEvenMode, map_smul, map_add]
    _ = _ := by
      rw [fourierCoeffCLM_apply, fourierCoeffCLM_apply,
        fourierCoeff_lebesgueNormalizedExponential,
        fourierCoeff_lebesgueNormalizedExponential]

theorem fourierCoeff_yoshidaEvenZeroMode (m : ℤ) :
    fourierCoeff (yoshidaEvenZeroMode (T := T)) m =
      ((Real.sqrt T)⁻¹ : ℂ) • (if m = 0 then 1 else 0) := by
  exact fourierCoeff_lebesgueNormalizedExponential m 0

/-- The ten odd Yoshida low modes are frequencies `1, ..., 10`. -/
abbrev YoshidaOddIndex := Fin 10

/-- The two hundred even Yoshida low modes are frequencies `0, ..., 199`. -/
abbrev YoshidaEvenIndex := Fin 200

def yoshidaOddLowMode (i : YoshidaOddIndex) : CircleL2 (T := T) :=
  yoshidaOddMode (T := T) (i.1 + 1)

def yoshidaEvenLowMode (i : YoshidaEvenIndex) : CircleL2 (T := T) :=
  if i.1 = 0 then yoshidaEvenZeroMode (T := T)
  else yoshidaEvenMode (T := T) i.1

theorem yoshidaOddLowMode_mem_odd (i : YoshidaOddIndex) :
    yoshidaOddLowMode (T := T) i ∈ oddL2Submodule (T := T) :=
  yoshidaOddMode_mem_odd _

theorem yoshidaEvenLowMode_mem_even (i : YoshidaEvenIndex) :
    yoshidaEvenLowMode (T := T) i ∈ evenL2Submodule (T := T) := by
  by_cases hi : i.1 = 0
  · simp [yoshidaEvenLowMode, hi, yoshidaEvenZeroMode_mem_even (T := T)]
  · simp [yoshidaEvenLowMode, hi, yoshidaEvenMode_mem_even (T := T)]

theorem lebesgueNormSq_yoshidaOddLowMode (i : YoshidaOddIndex) :
    lebesgueNormSq (T := T) (yoshidaOddLowMode (T := T) i) = 1 := by
  exact lebesgueNormSq_yoshidaOddMode (by omega)

theorem lebesgueNormSq_yoshidaEvenLowMode (i : YoshidaEvenIndex) :
    lebesgueNormSq (T := T) (yoshidaEvenLowMode (T := T) i) = 1 := by
  by_cases hi : i.1 = 0
  · simp [yoshidaEvenLowMode, hi, lebesgueNormSq_yoshidaEvenZeroMode (T := T)]
  · simp [yoshidaEvenLowMode, hi, lebesgueNormSq_yoshidaEvenMode (T := T) hi]

def yoshidaOddLowSubmodule : Submodule ℂ (CircleL2 (T := T)) :=
  Submodule.span ℂ (Set.range (yoshidaOddLowMode (T := T)))

def yoshidaEvenLowSubmodule : Submodule ℂ (CircleL2 (T := T)) :=
  Submodule.span ℂ (Set.range (yoshidaEvenLowMode (T := T)))

theorem lebesgueNormalizedExponential_mem_finiteFourierSubmodule
    (N : ℕ) {n : ℤ} (hn : n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)) :
    lebesgueNormalizedExponential (T := T) n ∈
      finiteFourierSubmodule (T := T) N := by
  exact Submodule.smul_mem _ _ (fourierLp_mem_finiteFourierSubmodule N hn)

theorem yoshidaOddLowMode_mem_finite (i : YoshidaOddIndex) :
    yoshidaOddLowMode (T := T) i ∈ finiteFourierSubmodule (T := T) 10 := by
  have hpos : (i.1 + 1 : ℤ) ∈ Finset.Icc (-(10 : ℤ)) 10 := by
    simp only [Finset.mem_Icc]
    constructor <;> omega
  have hneg : (-(i.1 + 1 : ℤ)) ∈ Finset.Icc (-(10 : ℤ)) 10 := by
    simp only [Finset.mem_Icc] at hpos ⊢
    omega
  rw [yoshidaOddLowMode, yoshidaOddMode]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _
    (lebesgueNormalizedExponential_mem_finiteFourierSubmodule 10 hpos)
    (lebesgueNormalizedExponential_mem_finiteFourierSubmodule 10 hneg))

theorem yoshidaEvenLowMode_mem_finite (i : YoshidaEvenIndex) :
    yoshidaEvenLowMode (T := T) i ∈ finiteFourierSubmodule (T := T) 199 := by
  by_cases hi : i.1 = 0
  · rw [yoshidaEvenLowMode, if_pos hi, yoshidaEvenZeroMode,
      lebesgueNormalizedExponential]
    exact Submodule.smul_mem _ _
      (fourierLp_mem_finiteFourierSubmodule 199 (by simp))
  · have hpos : (i.1 : ℤ) ∈ Finset.Icc (-(199 : ℤ)) 199 := by
      simp only [Finset.mem_Icc]
      constructor <;> omega
    have hneg : (-(i.1 : ℤ)) ∈ Finset.Icc (-(199 : ℤ)) 199 := by
      simp only [Finset.mem_Icc] at hpos ⊢
      omega
    rw [yoshidaEvenLowMode, if_neg hi, yoshidaEvenMode]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _
      (lebesgueNormalizedExponential_mem_finiteFourierSubmodule 199 hpos)
      (lebesgueNormalizedExponential_mem_finiteFourierSubmodule 199 hneg))

theorem yoshidaOddLowSubmodule_le_parity_finite :
    yoshidaOddLowSubmodule (T := T) ≤
      oddL2Submodule (T := T) ⊓ finiteFourierSubmodule (T := T) 10 := by
  rw [yoshidaOddLowSubmodule]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  exact ⟨yoshidaOddLowMode_mem_odd i, yoshidaOddLowMode_mem_finite i⟩

theorem yoshidaEvenLowSubmodule_le_parity_finite :
    yoshidaEvenLowSubmodule (T := T) ≤
      evenL2Submodule (T := T) ⊓ finiteFourierSubmodule (T := T) 199 := by
  rw [yoshidaEvenLowSubmodule]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  exact ⟨yoshidaEvenLowMode_mem_even i, yoshidaEvenLowMode_mem_finite i⟩

end ArithmeticHodge.Analysis
