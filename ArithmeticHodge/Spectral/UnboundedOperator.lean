/-
  Unbounded Operator API for Hilbert Spaces

  Mathlib has `ContinuousLinearMap` for bounded operators but no theory of
  unbounded operators. This file provides the minimal infrastructure needed
  for Stone's theorem:

  1. `UnboundedOperator` — a linear map on a dense subspace
  2. `IsSymmetric` — ⟨Tx, y⟩ = ⟨x, Ty⟩ for all x, y in the domain
  3. `IsSelfAdjoint` — symmetric + domain condition
  4. Symmetric operators have real eigenvalues (PROVED)
  5. Stone's theorem stated with proper types
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.MetricSpace.Basic

open scoped InnerProductSpace

namespace ArithmeticHodge.Spectral

-- ============================================================
-- Unbounded Operators on Hilbert Spaces
-- ============================================================

/-- An unbounded operator on a Hilbert space H is a linear map defined
    on a submodule (the domain) of H. -/
structure UnboundedOperator (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] where
  domain : Submodule ℂ H
  toFun : domain → H

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Dense domain. -/
def UnboundedOperator.IsDenselyDefined (T : UnboundedOperator H) : Prop :=
  Dense (T.domain : Set H)

/-- T is symmetric if ⟨Tx, y⟩ = ⟨x, Ty⟩ for all x, y ∈ Dom(T). -/
def UnboundedOperator.IsSymmetric (T : UnboundedOperator H) : Prop :=
  ∀ (x y : T.domain), ⟪T.toFun x, (y : H)⟫_ℂ = ⟪(x : H), T.toFun y⟫_ℂ

/-- T is self-adjoint if symmetric and Dom(T*) ⊆ Dom(T). -/
def UnboundedOperator.IsSelfAdjoint (T : UnboundedOperator H) : Prop :=
  T.IsSymmetric ∧
  ∀ (y : H), (∃ (C : ℝ), ∀ (x : T.domain), ‖⟪T.toFun x, y⟫_ℂ‖ ≤ C * ‖(x : H)‖) →
    y ∈ T.domain

theorem UnboundedOperator.IsSelfAdjoint.symmetric {T : UnboundedOperator H}
    (h : T.IsSelfAdjoint) : T.IsSymmetric := h.1

-- ============================================================
-- Symmetric Operators Have Real Eigenvalues (PROVED)
-- ============================================================

/-- **Eigenvalues of symmetric operators are real.**
    Proof: conj(μ)⟨x,x⟩ = ⟨μx,x⟩ = ⟨Tx,x⟩ = ⟨x,Tx⟩ = ⟨x,μx⟩ = μ⟨x,x⟩.
    Since x ≠ 0, ⟨x,x⟩ ≠ 0, so conj(μ) = μ, i.e., μ ∈ ℝ. -/
theorem symmetric_eigenvalue_real {T : UnboundedOperator H}
    (hT : T.IsSymmetric) (x : T.domain) (hx : (x : H) ≠ 0) (μ : ℂ)
    (heig : T.toFun x = μ • (x : H)) :
    (starRingEnd ℂ) μ = μ := by
  have hxx : ⟪(x : H), (x : H)⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hx
  -- ⟨Tx, x⟩ = ⟨μ•x, x⟩ = conj(μ) * ⟨x,x⟩  (conjugate-linear in 1st arg)
  have h1 : ⟪T.toFun x, (x : H)⟫_ℂ = (starRingEnd ℂ) μ * ⟪(x : H), (x : H)⟫_ℂ := by
    rw [heig, inner_smul_left]
  -- ⟨x, Tx⟩ = ⟨x, μ•x⟩ = μ * ⟨x,x⟩  (linear in 2nd arg)
  have h2 : ⟪(x : H), T.toFun x⟫_ℂ = μ * ⟪(x : H), (x : H)⟫_ℂ := by
    rw [heig, inner_smul_right]
  -- By symmetry: conj(μ) * ⟨x,x⟩ = μ * ⟨x,x⟩
  have h3 := hT x x
  rw [h1, h2] at h3
  exact mul_right_cancel₀ hxx h3

/-- **Eigenvectors for distinct eigenvalues are orthogonal.**
    If Tx = μx, Ty = νy with μ ≠ ν, then ⟨x,y⟩ = 0. -/
theorem symmetric_eigenvectors_orthogonal {T : UnboundedOperator H}
    (hT : T.IsSymmetric) (x y : T.domain)
    (μ ν : ℂ) (hμ : T.toFun x = μ • (x : H)) (hν : T.toFun y = ν • (y : H))
    (hne : μ ≠ ν) :
    ⟪(x : H), (y : H)⟫_ℂ = 0 := by
  -- ⟨Tx, y⟩ = conj(μ) * ⟨x,y⟩
  have h1 : ⟪T.toFun x, (y : H)⟫_ℂ = (starRingEnd ℂ) μ * ⟪(x : H), (y : H)⟫_ℂ := by
    rw [hμ, inner_smul_left]
  -- ⟨x, Ty⟩ = ν * ⟨x,y⟩
  have h2 : ⟪(x : H), T.toFun y⟫_ℂ = ν * ⟪(x : H), (y : H)⟫_ℂ := by
    rw [hν, inner_smul_right]
  -- By symmetry: conj(μ) * ⟨x,y⟩ = ν * ⟨x,y⟩
  have h3 := hT x y
  rw [h1, h2] at h3
  -- So (conj(μ) - ν) * ⟨x,y⟩ = 0
  by_contra hxy
  -- If ⟨x,y⟩ ≠ 0, then conj(μ) = ν
  have hconj : (starRingEnd ℂ) μ = ν := mul_right_cancel₀ hxy h3
  -- Both eigenvalues are real (by symmetric_eigenvalue_real)
  -- So if x ≠ 0: conj(μ) = μ, hence μ = ν, contradiction.
  have hxne : (x : H) ≠ 0 := by
    intro hx0; simp [hx0] at hxy
  have hμ_real := symmetric_eigenvalue_real hT x hxne μ hμ
  rw [hμ_real] at hconj
  exact hne hconj

-- ============================================================
-- The Generator of a Unitary Group
-- ============================================================

/-- The generator domain: {x ∈ H : lim_{t→0} t⁻¹(U(t)x - x) exists}. -/
noncomputable def generatorDomain (U : ℝ → H →L[ℂ] H) : Submodule ℂ H where
  carrier := {x : H | ∃ y : H, Filter.Tendsto
    (fun t : ℝ => t⁻¹ • (U t x - x)) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds y)}
  add_mem' := by intro _ _ ha hb; obtain ⟨ya, _⟩ := ha; obtain ⟨yb, _⟩ := hb
                 exact ⟨ya + yb, sorry⟩
  zero_mem' := ⟨0, by
    simp only [Set.mem_setOf_eq, map_zero, sub_self, smul_zero]
    exact tendsto_const_nhds⟩
  smul_mem' := by intro c _ hx; obtain ⟨y, _⟩ := hx; exact ⟨c • y, sorry⟩

/-- The generator as an unbounded operator. -/
noncomputable def generatorOp (U : ℝ → H →L[ℂ] H) : UnboundedOperator H where
  domain := generatorDomain U
  toFun := fun ⟨_, hx⟩ => hx.choose

/-- The generator domain is dense in H. -/
theorem generator_domain_dense
    (U_op : ℝ → H →L[ℂ] H)
    (hzero : U_op 0 = ContinuousLinearMap.id ℂ H)
    (hcont : ∀ x, Continuous (fun t => U_op t x)) :
    (generatorOp U_op).IsDenselyDefined :=
  sorry -- [INFRASTRUCTURE] Mollification: T⁻¹ ∫₀ᵀ U(t)x dt ∈ Dom(D), → x as T → 0

/-- The generator of a unitary group is symmetric. -/
theorem generator_is_symmetric
    (U_op : ℝ → H →L[ℂ] H)
    (hiso : ∀ t x y, ⟪U_op t x, U_op t y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hadd : ∀ s t, U_op (s + t) = (U_op s).comp (U_op t))
    (hzero : U_op 0 = ContinuousLinearMap.id ℂ H) :
    (generatorOp U_op).IsSymmetric :=
  sorry -- [INFRASTRUCTURE] ⟨U(t)x, y⟩ = ⟨x, U(-t)y⟩ + limit manipulation

-- ============================================================
-- Stone's Theorem (Full Unbounded Statement)
-- ============================================================

/-- **Stone's Theorem** (with unbounded operator types).

    The generator of a strongly continuous unitary group is self-adjoint.

    Proved in this file:
    ✓ UnboundedOperator, IsSymmetric, IsSelfAdjoint structures
    ✓ Symmetric eigenvalues are real
    ✓ Distinct eigenvectors are orthogonal
    ✓ Generator domain is a submodule (zero_mem proved, add/smul sorry'd)

    Sorry'd (all known math):
    - Generator symmetry [limit + inner product continuity]
    - Dense domain [mollification via Bochner integral]
    - Self-adjointness [deficiency indices (0,0) via Cayley transform] -/
theorem stones_theorem_full
    (U_op : ℝ → H →L[ℂ] H)
    (hiso : ∀ t x y, ⟪U_op t x, U_op t y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hadd : ∀ s t, U_op (s + t) = (U_op s).comp (U_op t))
    (hzero : U_op 0 = ContinuousLinearMap.id ℂ H)
    (hcont : ∀ x, Continuous (fun t => U_op t x)) :
    let D := generatorOp U_op
    D.IsDenselyDefined ∧ D.IsSelfAdjoint :=
  ⟨generator_domain_dense U_op hzero hcont,
   generator_is_symmetric U_op hiso hadd hzero,
   fun _ _ => sorry⟩ -- [INFRASTRUCTURE] Deficiency indices

end ArithmeticHodge.Spectral
