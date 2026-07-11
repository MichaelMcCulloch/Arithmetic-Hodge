import ArithmeticHodge.Analysis.CenteredAddCircleFourierBasic

set_option autoImplicit false

noncomputable section

open AddCircle MeasureTheory Set
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace ArithmeticHodge.Analysis

variable {T : ℝ} [hT : Fact (0 < T)]

abbrev CircleL2 :=
  Lp ℂ 2 (@haarAddCircle T hT)

def fourierCoeffCLM (n : ℤ) :
    StrongDual ℂ (CircleL2 (T := T)) :=
  innerSL ℂ (fourierLp 2 n)

@[simp] theorem fourierCoeffCLM_apply
    (n : ℤ) (f : CircleL2 (T := T)) :
    fourierCoeffCLM n f = fourierCoeff f n := by
  rw [fourierCoeffCLM, innerSL_apply_apply,
    ← fourierBasis_repr,
    fourierBasis.repr_apply_apply,
    coe_fourierBasis]

abbrev LowIndex (N : ℕ) :=
  {n : ℤ //
    n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)}

def fourierTailSubmodule (N : ℕ) :
    Submodule ℂ (CircleL2 (T := T)) :=
  ⨅ n : LowIndex N,
    LinearMap.ker
      (fourierCoeffCLM (T := T) n).toLinearMap

theorem mem_fourierTailSubmodule_iff
    (N : ℕ) (f : CircleL2 (T := T)) :
    f ∈ fourierTailSubmodule (T := T) N ↔
      ∀ n : ℤ,
        n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) →
          fourierCoeff f n = 0 := by
  constructor
  · intro hf n hn
    have h := (Submodule.mem_iInf _).mp hf
      ⟨n, hn⟩
    rw [LinearMap.mem_ker] at h
    change fourierCoeffCLM (T := T) n f = 0 at h
    simpa using h
  · intro hf
    refine (Submodule.mem_iInf _).mpr ?_
    intro n
    rw [LinearMap.mem_ker]
    change fourierCoeffCLM (T := T)
      (n : ℤ) f = 0
    simpa using hf n n.property

theorem fourierTailSubmodule_isClosed (N : ℕ) :
    IsClosed
      (fourierTailSubmodule (T := T) N :
        Set (CircleL2 (T := T))) := by
  rw [show
      (fourierTailSubmodule (T := T) N :
        Set (CircleL2 (T := T))) =
        ⋂ n : LowIndex N,
          (LinearMap.ker
            (fourierCoeffCLM
              (T := T) n).toLinearMap :
            Set _) by
      ext f
      simp [fourierTailSubmodule]]
  exact isClosed_iInter fun n ↦
    ContinuousLinearMap.isClosed_ker
      (fourierCoeffCLM (T := T) n)

def lowFourierProjection
    (N : ℕ) (f : CircleL2 (T := T)) :
    CircleL2 (T := T) :=
  ∑ n : LowIndex N,
    fourierCoeff f n • fourierLp 2 (n : ℤ)

def lowFourierProjectionCLM (N : ℕ) :
    CircleL2 (T := T) →L[ℂ]
      CircleL2 (T := T) :=
  ∑ n : LowIndex N,
    (fourierCoeffCLM (T := T)
      (n : ℤ)).smulRight
        (fourierLp 2 (n : ℤ))

@[simp] theorem lowFourierProjectionCLM_apply
    (N : ℕ) (f : CircleL2 (T := T)) :
    lowFourierProjectionCLM (T := T) N f =
      lowFourierProjection (T := T) N f := by
  simp [lowFourierProjectionCLM,
    lowFourierProjection,
    ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply]

def finiteFourierSubmodule (N : ℕ) :
    Submodule ℂ (CircleL2 (T := T)) :=
  Submodule.span ℂ
    (Set.range fun n : LowIndex N ↦
      fourierLp 2 (n : ℤ))

theorem lowFourierProjection_mem_finiteFourierSubmodule
    (N : ℕ) (f : CircleL2 (T := T)) :
    lowFourierProjection (T := T) N f ∈
      finiteFourierSubmodule (T := T) N := by
  rw [lowFourierProjection]
  exact Submodule.sum_mem _ fun n _ ↦
    Submodule.smul_mem _ _
      (Submodule.subset_span
        (Set.mem_range_self n))

theorem fourierLp_mem_finiteFourierSubmodule
    (N : ℕ) {n : ℤ}
    (hn : n ∈
      Finset.Icc (-(N : ℤ)) (N : ℤ)) :
    fourierLp (T := T) 2 n ∈
      finiteFourierSubmodule (T := T) N :=
  Submodule.subset_span ⟨⟨n, hn⟩, rfl⟩

theorem fourierCoeff_fourierLp (m n : ℤ) :
    fourierCoeff
      (fourierLp (T := T) 2 n) m =
        if m = n then 1 else 0 := by
  rw [← fourierBasis_repr,
    ← coe_fourierBasis,
    fourierBasis.repr_self,
    lp.single_apply, Pi.single_apply]

theorem lowFourierProjection_fourierLp
    (N : ℕ) (m : LowIndex N) :
    lowFourierProjection (T := T) N
      (fourierLp 2 (m : ℤ)) =
        fourierLp 2 (m : ℤ) := by
  rw [lowFourierProjection]
  simp only [fourierCoeff_fourierLp]
  rw [Fintype.sum_eq_single m]
  · simp
  · intro b hbm
    have hne : (b : ℤ) ≠ (m : ℤ) :=
      fun h ↦ hbm (Subtype.ext h)
    rw [if_neg hne, zero_smul]

theorem lowFourierProjection_eq_self_of_mem_finiteFourierSubmodule
    (N : ℕ) {f : CircleL2 (T := T)}
    (hf : f ∈
      finiteFourierSubmodule (T := T) N) :
    lowFourierProjection (T := T) N f = f := by
  rw [← lowFourierProjectionCLM_apply]
  refine Submodule.span_induction
    (p := fun x _ ↦
      lowFourierProjectionCLM (T := T) N x = x)
    ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨m, rfl⟩
    rw [lowFourierProjectionCLM_apply,
      lowFourierProjection_fourierLp]
  · exact map_zero _
  · intro x y _ _ hx hy
    rw [map_add, hx, hy]
  · intro c x _ hx
    rw [map_smul, hx]

theorem fourierCoeff_lowFourierProjection
    (N : ℕ) (f : CircleL2 (T := T))
    (m : LowIndex N) :
    fourierCoeff
      (lowFourierProjection (T := T) N f)
      (m : ℤ) = fourierCoeff f m := by
  rw [← fourierCoeffCLM_apply]
  simp only [lowFourierProjection,
    map_sum, map_smul]
  rw [Fintype.sum_eq_single m]
  · rw [fourierCoeffCLM_apply,
      fourierCoeff_fourierLp, if_pos rfl,
      smul_eq_mul, mul_one]
  · intro b hbm
    have hmb : (m : ℤ) ≠ (b : ℤ) :=
      fun h ↦ hbm (Subtype.ext h.symm)
    rw [fourierCoeffCLM_apply,
      fourierCoeff_fourierLp, if_neg hmb,
      smul_zero]

theorem sub_lowFourierProjection_mem_tail
    (N : ℕ) (f : CircleL2 (T := T)) :
    f - lowFourierProjection (T := T) N f ∈
      fourierTailSubmodule (T := T) N := by
  rw [mem_fourierTailSubmodule_iff]
  intro n hn
  rw [← fourierCoeffCLM_apply (T := T) n
      (f - lowFourierProjection (T := T) N f),
    map_sub, fourierCoeffCLM_apply,
    fourierCoeffCLM_apply,
    fourierCoeff_lowFourierProjection
      (m := ⟨n, hn⟩), sub_self]

end ArithmeticHodge.Analysis
