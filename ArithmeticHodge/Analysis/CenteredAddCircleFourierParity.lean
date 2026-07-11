import ArithmeticHodge.Analysis.CenteredAddCircleFourierProjection
import Mathlib.MeasureTheory.Measure.Haar.Unique

set_option autoImplicit false

noncomputable section

open AddCircle MeasureTheory Set
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace ArithmeticHodge.Analysis

variable {T : ℝ} [hT : Fact (0 < T)]

def circleNegMeasurePreserving :
    MeasurePreserving
      (Neg.neg : AddCircle T → AddCircle T)
      haarAddCircle haarAddCircle := by
  haveI : Measure.IsAddHaarMeasure
      (Measure.map
        (Neg.neg : AddCircle T → AddCircle T)
        haarAddCircle) :=
    (AddEquiv.neg
      (AddCircle T)).isAddHaarMeasure_map
        haarAddCircle continuous_neg continuous_neg
  haveI : IsProbabilityMeasure
      (Measure.map
        (Neg.neg : AddCircle T → AddCircle T)
        haarAddCircle) :=
    Measure.isProbabilityMeasure_map
      continuous_neg.aemeasurable
  exact ⟨measurable_neg,
    Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure
      (Measure.map
        (Neg.neg : AddCircle T → AddCircle T)
        haarAddCircle)
      haarAddCircle⟩

def reflectionL2 :
    CircleL2 (T := T) →L[ℂ] CircleL2 (T := T) :=
  (Lp.compMeasurePreservingₗᵢ ℂ Neg.neg
    (circleNegMeasurePreserving
      (T := T))).toContinuousLinearMap

theorem reflectionL2_ae
    (f : CircleL2 (T := T)) :
    reflectionL2 f =ᵐ[haarAddCircle]
      fun x ↦ f (-x) := by
  exact Lp.coeFn_compMeasurePreserving f
    (circleNegMeasurePreserving (T := T))

@[simp] theorem reflectionL2_involutive
    (f : CircleL2 (T := T)) :
    reflectionL2 (reflectionL2 f) = f := by
  change Lp.compMeasurePreserving Neg.neg
      (circleNegMeasurePreserving (T := T))
      (Lp.compMeasurePreserving Neg.neg
        (circleNegMeasurePreserving (T := T)) f) = f
  rw [← Lp.compMeasurePreserving_comp_apply f
    (circleNegMeasurePreserving (T := T))
    (circleNegMeasurePreserving (T := T))]
  have hfun :
      (Neg.neg ∘ Neg.neg :
        AddCircle T → AddCircle T) = id := by
    funext x
    simp
  simpa only [hfun] using
    Lp.compMeasurePreserving_id_apply f

def evenL2Submodule :
    Submodule ℂ (CircleL2 (T := T)) :=
  LinearMap.ker
    (reflectionL2 (T := T) -
      ContinuousLinearMap.id ℂ
        (CircleL2 (T := T))).toLinearMap

def oddL2Submodule :
    Submodule ℂ (CircleL2 (T := T)) :=
  LinearMap.ker
    (reflectionL2 (T := T) +
      ContinuousLinearMap.id ℂ
        (CircleL2 (T := T))).toLinearMap

theorem mem_evenL2Submodule_iff
    (f : CircleL2 (T := T)) :
    f ∈ evenL2Submodule (T := T) ↔
      reflectionL2 (T := T) f = f := by
  rw [evenL2Submodule, LinearMap.mem_ker]
  change reflectionL2 (T := T) f - f = 0 ↔ _
  exact sub_eq_zero

theorem mem_oddL2Submodule_iff
    (f : CircleL2 (T := T)) :
    f ∈ oddL2Submodule (T := T) ↔
      reflectionL2 (T := T) f = -f := by
  rw [oddL2Submodule, LinearMap.mem_ker]
  change reflectionL2 (T := T) f + f = 0 ↔ _
  exact add_eq_zero_iff_eq_neg

theorem evenL2Submodule_isClosed :
    IsClosed
      (evenL2Submodule (T := T) :
        Set (CircleL2 (T := T))) :=
  ContinuousLinearMap.isClosed_ker _

theorem oddL2Submodule_isClosed :
    IsClosed
      (oddL2Submodule (T := T) :
        Set (CircleL2 (T := T))) :=
  ContinuousLinearMap.isClosed_ker _

def evenFourierTailSubmodule (N : ℕ) :
    Submodule ℂ (CircleL2 (T := T)) :=
  evenL2Submodule (T := T) ⊓
    fourierTailSubmodule (T := T) N

def oddFourierTailSubmodule (N : ℕ) :
    Submodule ℂ (CircleL2 (T := T)) :=
  oddL2Submodule (T := T) ⊓
    fourierTailSubmodule (T := T) N

theorem evenFourierTailSubmodule_isClosed
    (N : ℕ) :
    IsClosed
      (evenFourierTailSubmodule (T := T) N :
        Set (CircleL2 (T := T))) := by
  simpa only [evenFourierTailSubmodule,
    Submodule.coe_inf] using
      (evenL2Submodule_isClosed
        (T := T)).inter
          (fourierTailSubmodule_isClosed
            (T := T) N)

theorem oddFourierTailSubmodule_isClosed
    (N : ℕ) :
    IsClosed
      (oddFourierTailSubmodule (T := T) N :
        Set (CircleL2 (T := T))) := by
  simpa only [oddFourierTailSubmodule,
    Submodule.coe_inf] using
      (oddL2Submodule_isClosed
        (T := T)).inter
          (fourierTailSubmodule_isClosed
            (T := T) N)

noncomputable instance instCompleteSpaceEvenFourierTail
    (N : ℕ) :
    CompleteSpace
      (evenFourierTailSubmodule (T := T) N) :=
  (evenFourierTailSubmodule_isClosed
    (T := T) N).completeSpace_coe

noncomputable instance instCompleteSpaceOddFourierTail
    (N : ℕ) :
    CompleteSpace
      (oddFourierTailSubmodule (T := T) N) :=
  (oddFourierTailSubmodule_isClosed
    (T := T) N).completeSpace_coe

def evenPart (f : CircleL2 (T := T)) :
    CircleL2 (T := T) :=
  (2 : ℂ)⁻¹ •
    (f + reflectionL2 (T := T) f)

def oddPart (f : CircleL2 (T := T)) :
    CircleL2 (T := T) :=
  (2 : ℂ)⁻¹ •
    (f - reflectionL2 (T := T) f)

def evenPartCLM :
    CircleL2 (T := T) →L[ℂ] CircleL2 (T := T) :=
  (2 : ℂ)⁻¹ •
    (ContinuousLinearMap.id ℂ
      (CircleL2 (T := T)) +
        reflectionL2 (T := T))

def oddPartCLM :
    CircleL2 (T := T) →L[ℂ] CircleL2 (T := T) :=
  (2 : ℂ)⁻¹ •
    (ContinuousLinearMap.id ℂ
      (CircleL2 (T := T)) -
        reflectionL2 (T := T))

@[simp] theorem evenPartCLM_apply
    (f : CircleL2 (T := T)) :
    evenPartCLM (T := T) f =
      evenPart (T := T) f := by
  simp [evenPartCLM, evenPart]

@[simp] theorem oddPartCLM_apply
    (f : CircleL2 (T := T)) :
    oddPartCLM (T := T) f =
      oddPart (T := T) f := by
  simp [oddPartCLM, oddPart]

theorem evenPart_mem (f : CircleL2 (T := T)) :
    evenPart (T := T) f ∈
      evenL2Submodule (T := T) := by
  rw [mem_evenL2Submodule_iff]
  simp [evenPart, add_comm]

theorem oddPart_mem (f : CircleL2 (T := T)) :
    oddPart (T := T) f ∈
      oddL2Submodule (T := T) := by
  rw [mem_oddL2Submodule_iff]
  simp [oddPart]
  module

theorem evenPart_add_oddPart
    (f : CircleL2 (T := T)) :
    evenPart (T := T) f +
      oddPart (T := T) f = f := by
  simp [evenPart, oddPart]
  module

omit hT in
theorem fourier_apply_neg
    (n : ℤ) (x : AddCircle T) :
    fourier n (-x) = fourier (-n) x := by
  simp only [fourier_apply,
    smul_neg, neg_smul]

@[simp] theorem reflectionL2_fourierLp (n : ℤ) :
    reflectionL2 (T := T)
      (fourierLp 2 n) =
        fourierLp 2 (-n) := by
  apply Lp.ext
  have hcomp :=
    (circleNegMeasurePreserving
      (T := T)).quasiMeasurePreserving.tendsto_ae
        (coeFn_fourierLp (T := T) 2 n)
  filter_upwards
    [reflectionL2_ae (T := T)
      (fourierLp 2 n),
    hcomp,
    coeFn_fourierLp (T := T) 2 (-n)]
      with x href hn hneg
  rw [href, hn, hneg, fourier_apply_neg]

theorem fourierCoeff_reflectionL2
    (f : CircleL2 (T := T)) (n : ℤ) :
    fourierCoeff
      (reflectionL2 (T := T) f) n =
        fourierCoeff f (-n) := by
  rw [← fourierCoeffCLM_apply,
    ← fourierCoeffCLM_apply]
  change
    ⟪fourierLp 2 n,
      reflectionL2 (T := T) f⟫_ℂ =
        ⟪fourierLp 2 (-n), f⟫_ℂ
  have h :=
    (Lp.compMeasurePreservingₗᵢ ℂ Neg.neg
      (circleNegMeasurePreserving
        (T := T))).inner_map_map
          (fourierLp 2 n)
          (reflectionL2 (T := T) f)
  change
    ⟪reflectionL2 (T := T)
        (fourierLp 2 n),
      reflectionL2 (T := T)
        (reflectionL2 (T := T) f)⟫_ℂ =
      ⟪fourierLp 2 n,
        reflectionL2 (T := T) f⟫_ℂ at h
  rw [reflectionL2_fourierLp,
    reflectionL2_involutive] at h
  exact h.symm

theorem fourierCoeff_even_of_mem
    {f : CircleL2 (T := T)}
    (hf : f ∈ evenL2Submodule (T := T))
    (n : ℤ) :
    fourierCoeff f (-n) =
      fourierCoeff f n := by
  calc
    fourierCoeff f (-n) =
        fourierCoeff
          (reflectionL2 (T := T) f) n :=
      (fourierCoeff_reflectionL2 f n).symm
    _ = fourierCoeff f n := by
      rw [(mem_evenL2Submodule_iff f).mp hf]

theorem fourierCoeff_odd_of_mem
    {f : CircleL2 (T := T)}
    (hf : f ∈ oddL2Submodule (T := T))
    (n : ℤ) :
    fourierCoeff f (-n) =
      -fourierCoeff f n := by
  calc
    fourierCoeff f (-n) =
        fourierCoeff
          (reflectionL2 (T := T) f) n :=
      (fourierCoeff_reflectionL2 f n).symm
    _ = fourierCoeff (-f) n := by
      rw [(mem_oddL2Submodule_iff f).mp hf]
    _ = -fourierCoeff f n := by
      rw [← fourierCoeffCLM_apply,
        ← fourierCoeffCLM_apply]
      exact map_neg
        (fourierCoeffCLM (T := T) n) f

theorem fourierCoeff_evenPart
    (f : CircleL2 (T := T)) (n : ℤ) :
    fourierCoeff (evenPart (T := T) f) n =
      (2 : ℂ)⁻¹ •
        (fourierCoeff f n +
          fourierCoeff f (-n)) := by
  calc
    fourierCoeff (evenPart (T := T) f) n =
        fourierCoeffCLM (T := T) n
          (evenPart (T := T) f) := by
      rw [fourierCoeffCLM_apply]
    _ = (2 : ℂ)⁻¹ •
        (fourierCoeffCLM (T := T) n f +
          fourierCoeffCLM (T := T) n
            (reflectionL2 (T := T) f)) := by
      rw [evenPart, map_smul, map_add]
    _ = (2 : ℂ)⁻¹ •
        (fourierCoeff f n +
          fourierCoeff f (-n)) := by
      rw [fourierCoeffCLM_apply,
        fourierCoeffCLM_apply,
        fourierCoeff_reflectionL2]

theorem fourierCoeff_oddPart
    (f : CircleL2 (T := T)) (n : ℤ) :
    fourierCoeff (oddPart (T := T) f) n =
      (2 : ℂ)⁻¹ •
        (fourierCoeff f n -
          fourierCoeff f (-n)) := by
  calc
    fourierCoeff (oddPart (T := T) f) n =
        fourierCoeffCLM (T := T) n
          (oddPart (T := T) f) := by
      rw [fourierCoeffCLM_apply]
    _ = (2 : ℂ)⁻¹ •
        (fourierCoeffCLM (T := T) n f -
          fourierCoeffCLM (T := T) n
            (reflectionL2 (T := T) f)) := by
      rw [oddPart, map_smul, map_sub]
    _ = (2 : ℂ)⁻¹ •
        (fourierCoeff f n -
          fourierCoeff f (-n)) := by
      rw [fourierCoeffCLM_apply,
        fourierCoeffCLM_apply,
        fourierCoeff_reflectionL2]

theorem evenPart_eq_self_of_mem
    {f : CircleL2 (T := T)}
    (hf : f ∈ evenL2Submodule (T := T)) :
    evenPart (T := T) f = f := by
  rw [evenPart,
    (mem_evenL2Submodule_iff f).mp hf]
  module

theorem oddPart_eq_self_of_mem
    {f : CircleL2 (T := T)}
    (hf : f ∈ oddL2Submodule (T := T)) :
    oddPart (T := T) f = f := by
  rw [oddPart,
    (mem_oddL2Submodule_iff f).mp hf]
  module

theorem neg_mem_lowIndex
    {N : ℕ} {n : ℤ}
    (hn : n ∈
      Finset.Icc (-(N : ℤ)) (N : ℤ)) :
    -n ∈ Finset.Icc
      (-(N : ℤ)) (N : ℤ) := by
  simp only [Finset.mem_Icc] at hn ⊢
  omega

end ArithmeticHodge.Analysis
