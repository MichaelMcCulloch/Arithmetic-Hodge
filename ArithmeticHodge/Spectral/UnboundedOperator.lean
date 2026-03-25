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
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

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
  add_mem' := by
    intro a b ha hb; obtain ⟨ya, hya⟩ := ha; obtain ⟨yb, hyb⟩ := hb
    exact ⟨ya + yb, by
      have : ∀ t : ℝ, t⁻¹ • (U t (a + b) - (a + b)) =
          t⁻¹ • (U t a - a) + t⁻¹ • (U t b - b) := by
        intro t; simp [map_add, add_sub_add_comm, smul_add]
      simp_rw [this]
      exact hya.add hyb⟩
  zero_mem' := ⟨0, by
    simp only [map_zero, sub_self, smul_zero]
    exact tendsto_const_nhds⟩
  smul_mem' := by
    intro c a hx; obtain ⟨y, hy⟩ := hx
    exact ⟨c • y, by
      have key : ∀ t : ℝ, t⁻¹ • (U t (c • a) - c • a) =
          c • (t⁻¹ • (U t a - a)) := by
        intro t
        rw [map_smul, ← smul_sub c]
        haveI : IsScalarTower ℝ ℂ H := RestrictScalars.isScalarTower ℝ ℂ H
        exact (smul_algebra_smul_comm t⁻¹ c _).symm
      simp_rw [key]
      exact hy.const_smul c⟩

/-- The generator as an unbounded operator.
    We define A = -i · lim_{t→0} t⁻¹(U(t)x - x) so that U(t) = exp(iAt)
    and A is self-adjoint (not merely skew-adjoint). -/
noncomputable def generatorOp (U : ℝ → H →L[ℂ] H) : UnboundedOperator H where
  domain := generatorDomain U
  toFun := fun ⟨_, hx⟩ => (-Complex.I) • hx.choose

/-- The generator domain is dense in H. -/
theorem generator_domain_dense
    (U_op : ℝ → H →L[ℂ] H)
    (hzero : U_op 0 = ContinuousLinearMap.id ℂ H)
    (hcont : ∀ x, Continuous (fun t => U_op t x)) :
    (generatorOp U_op).IsDenselyDefined :=
  sorry -- [INFRASTRUCTURE] Mollification: T⁻¹ ∫₀ᵀ U(t)x dt ∈ Dom(D), → x as T → 0

/-- Auxiliary: U(-t) is the adjoint of U(t) for a unitary group. -/
theorem unitary_adjoint_eq
    (U_op : ℝ → H →L[ℂ] H)
    (hiso : ∀ t x y, ⟪U_op t x, U_op t y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hadd : ∀ s t, U_op (s + t) = (U_op s).comp (U_op t))
    (hzero : U_op 0 = ContinuousLinearMap.id ℂ H)
    (t : ℝ) (x y : H) :
    ⟪U_op t x, y⟫_ℂ = ⟪x, U_op (-t) y⟫_ℂ := by
  have h1 := hiso t x (U_op (-t) y)
  rw [show U_op t (U_op (-t) y) = (U_op t).comp (U_op (-t)) y from rfl] at h1
  rw [← hadd, add_neg_cancel] at h1
  simp [hzero, ContinuousLinearMap.id_apply] at h1
  exact h1

/-- The raw derivative is skew-symmetric: ⟨D x, y⟩ = -⟨x, D y⟩.
    This uses unitarity and the substitution t ↦ -t. -/
theorem raw_generator_skew_symmetric
    (U_op : ℝ → H →L[ℂ] H)
    (hiso : ∀ t x y, ⟪U_op t x, U_op t y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hadd : ∀ s t, U_op (s + t) = (U_op s).comp (U_op t))
    (hzero : U_op 0 = ContinuousLinearMap.id ℂ H)
    (x y : (generatorDomain U_op)) :
    let dx := x.2.choose
    let dy := y.2.choose
    ⟪dx, (y : H)⟫_ℂ = -⟪(x : H), dy⟫_ℂ := by
  haveI : IsScalarTower ℝ ℂ H := RestrictScalars.isScalarTower ℝ ℂ H
  have hdx := x.2.choose_spec
  have hdy := y.2.choose_spec
  -- Negation preserves nhdsWithin 0 {0}ᶜ
  have neg_map : Filter.Tendsto (fun t : ℝ => -t)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhdsWithin 0 {(0 : ℝ)}ᶜ) := by
    refine Filter.Tendsto.inf ?_ ?_
    · exact (continuous_neg.tendsto 0).mono_right (by simp)
    · exact Filter.tendsto_principal_principal.mpr fun t ht =>
        Set.mem_compl_singleton_iff.mpr (neg_ne_zero.mpr (Set.mem_compl_singleton_iff.mp ht))
  -- Composing hdy with negation: lim_{t→0} (-t)⁻¹•(U(-t)y - y) = dy
  have hdy_neg := hdy.comp neg_map
  -- t⁻¹•(U(-t)y - y) = -((-t)⁻¹•(U(-t)y - y)) so lim = -dy
  have neg_lim : Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (U_op (-t) (y : H) - (y : H)))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (-y.2.choose)) := by
    refine Filter.Tendsto.congr' ?_ hdy_neg.neg
    filter_upwards [self_mem_nhdsWithin] with t (ht : t ∈ {(0 : ℝ)}ᶜ)
    -- Goal: -((-t)⁻¹ • (U(-t)y - y)) = t⁻¹ • (U(-t)y - y)
    simp only [Function.comp, inv_neg, neg_smul, neg_neg]
  -- By continuity of inner product and uniqueness of limits
  -- lim ⟪t⁻¹•(U(t)x-x), y⟫ = ⟪dx, y⟫
  have lim1 : Filter.Tendsto
      (fun t : ℝ => @inner ℂ H _ (t⁻¹ • (U_op t (x : H) - (x : H))) (y : H))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ⟪x.2.choose, (y : H)⟫_ℂ) :=
    Filter.Tendsto.inner hdx tendsto_const_nhds
  -- lim ⟪x, t⁻¹•(U(-t)y-y)⟫ = ⟪x, -dy⟫
  have lim2 : Filter.Tendsto
      (fun t : ℝ => @inner ℂ H _ (x : H) (t⁻¹ • (U_op (-t) (y : H) - (y : H))))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ⟪(x : H), -y.2.choose⟫_ℂ) :=
    Filter.Tendsto.inner tendsto_const_nhds neg_lim
  -- The two sequences agree for t ≠ 0
  have agree : ∀ᶠ t in nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ,
      ⟪t⁻¹ • (U_op t (x : H) - (x : H)), (y : H)⟫_ℂ =
      ⟪(x : H), t⁻¹ • (U_op (-t) (y : H) - (y : H))⟫_ℂ := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : t ∈ {(0 : ℝ)}ᶜ)
    -- Convert ℝ-smul to ℂ-smul for inner product manipulation
    rw [← algebraMap_smul ℂ (t⁻¹ : ℝ) (U_op t (x : H) - (x : H)),
        ← algebraMap_smul ℂ (t⁻¹ : ℝ) (U_op (-t) (y : H) - (y : H)),
        inner_smul_left, inner_sub_left, inner_smul_right, inner_sub_right]
    have hadj := unitary_adjoint_eq U_op hiso hadd hzero t (x : H) (y : H)
    rw [hadj]
    have hconj : (starRingEnd ℂ) ((algebraMap ℝ ℂ) t⁻¹) = (algebraMap ℝ ℂ) t⁻¹ :=
      RCLike.conj_ofReal _
    rw [hconj]
  -- By uniqueness of limits
  have key : ⟪x.2.choose, (y : H)⟫_ℂ = ⟪(x : H), -y.2.choose⟫_ℂ :=
    tendsto_nhds_unique (lim1.congr' agree) lim2
  show ⟪x.2.choose, (y : H)⟫_ℂ = -⟪(x : H), y.2.choose⟫_ℂ
  rw [key, inner_neg_right]

/-- The generator of a unitary group is symmetric.
    Uses A = -i · D_raw, so ⟨Ax, y⟩ = conj(-i)⟨D x, y⟩ = i·(-⟨x, D y⟩) = ⟨x, Ay⟩. -/
theorem generator_is_symmetric
    (U_op : ℝ → H →L[ℂ] H)
    (hiso : ∀ t x y, ⟪U_op t x, U_op t y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hadd : ∀ s t, U_op (s + t) = (U_op s).comp (U_op t))
    (hzero : U_op 0 = ContinuousLinearMap.id ℂ H) :
    (generatorOp U_op).IsSymmetric := by
  intro x y
  -- generatorOp maps x to (-I) • x.2.choose
  show ⟪(-Complex.I) • x.2.choose, (y : H)⟫_ℂ = ⟪(x : H), (-Complex.I) • y.2.choose⟫_ℂ
  rw [inner_smul_left, inner_smul_right]
  -- conj(-I) • ⟨dx, y⟩ = (-I) • ⟨x, dy⟩
  -- conj(-I) = I, so I • ⟨dx, y⟩ = (-I) • ⟨x, dy⟩
  -- By skew-symmetry: ⟨dx, y⟩ = -⟨x, dy⟩, so I • (-⟨x, dy⟩) = (-I) • ⟨x, dy⟩ ✓
  have hskew := raw_generator_skew_symmetric U_op hiso hadd hzero x y
  -- Goal: ⟪(-I) • dx, ↑y⟫ = ⟪↑x, (-I) • dy⟫
  -- where dx = x.2.choose, dy = y.2.choose
  -- Goal already has inner_smul applied:
  -- (starRingEnd ℂ) (-I) * ⟪dx, y⟫ = (-I) * ⟪x, dy⟫
  simp only [hskew, map_neg, starRingEnd_apply, neg_mul, neg_neg]
  congr 1
  rw [show star Complex.I = -Complex.I from Complex.conj_I]
  ring

-- ============================================================
-- Stone's Theorem (Full Unbounded Statement)
-- ============================================================

/-- **Stone's Theorem** (with unbounded operator types).

    The generator of a strongly continuous unitary group is self-adjoint.

    Proved in this file:
    ✓ UnboundedOperator, IsSymmetric, IsSelfAdjoint structures
    ✓ Symmetric eigenvalues are real
    ✓ Distinct eigenvectors are orthogonal
    ✓ Generator domain is a submodule (zero_mem, add_mem, smul_mem all proved)
    ✓ Generator = -i·(raw derivative) is symmetric (via skew-symmetry + conjugation)
    ✓ U(-t) is adjoint of U(t) for unitary groups
    ✓ Raw derivative is skew-symmetric (limit substitution t↦-t)

    Sorry'd (known math, requires substantial Mathlib infrastructure):
    - Dense domain [mollification via Bochner interval integral + FTC]
    - Dom(A*) ⊆ Dom(A) [deficiency indices (0,0) via Cayley transform] -/
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
