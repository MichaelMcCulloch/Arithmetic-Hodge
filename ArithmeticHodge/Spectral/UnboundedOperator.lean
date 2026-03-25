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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue

open scoped InnerProductSpace
open MeasureTheory Filter Topology

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

/-- The generator domain is dense in H.
    Proof by mollification: T⁻¹ ∫₀ᵀ U(t)x dt ∈ Dom(D) and converges to x as T → 0. -/
theorem generator_domain_dense
    (U_op : ℝ → H →L[ℂ] H)
    (hadd : ∀ s t, U_op (s + t) = (U_op s).comp (U_op t))
    (hzero : U_op 0 = ContinuousLinearMap.id ℂ H)
    (hcont : ∀ x, Continuous (fun t => U_op t x)) :
    (generatorOp U_op).IsDenselyDefined := by
  haveI : IsScalarTower ℝ ℂ H := RestrictScalars.isScalarTower ℝ ℂ H
  intro x
  -- FTC at any point a: HasDerivAt (fun u => ∫₀ᵘ U(t)x dt) (U(a)x) a
  have hFTC : ∀ a : ℝ, HasDerivAt (fun u => ∫ t in (0 : ℝ)..u, U_op t x) (U_op a x) a :=
    fun a => intervalIntegral.integral_hasDerivAt_right
      ((hcont x).intervalIntegrable _ _)
      ((hcont x).stronglyMeasurable.stronglyMeasurableAtFilter)
      ((hcont x).continuousAt)
  have hU0 : U_op 0 x = x := by rw [hzero]; simp
  -- Convergence: T⁻¹ • F(T) → x as T → 0 (where F(u) = ∫₀ᵘ U(t)x dt)
  -- This is the slope of F at 0, which tends to F'(0) = U(0)x = x by FTC.
  have hconv : Tendsto (fun T => T⁻¹ • ∫ t in (0 : ℝ)..T, U_op t x) (𝓝[≠] 0) (𝓝 x) := by
    have hslope := (hU0 ▸ hFTC 0).tendsto_slope
    refine hslope.congr (fun T => ?_)
    simp [slope, intervalIntegral.integral_same]
  -- Domain membership: for T ≠ 0, T⁻¹ • F(T) ∈ Dom(D)
  have hmem : ∀ᶠ T in 𝓝[≠] (0 : ℝ),
      T⁻¹ • (∫ t in (0 : ℝ)..T, U_op t x) ∈ (generatorDomain U_op : Set H) := by
    filter_upwards [self_mem_nhdsWithin] with T (hT : T ≠ 0)
    -- We show the difference quotient s⁻¹•(U(s)(m) - m) converges, where m = T⁻¹•F(T).
    -- Key: U(s)(m) - m = T⁻¹•((F(s+T)-F(T)) - (F(s)-F(0))) by the shift identity
    -- F(s+T)-F(s) = U(s)(F(T)) via integral shift + group law + CLM through integral.
    -- So the quotient = T⁻¹•(slope F T (s+T) - slope F 0 s) → T⁻¹•(U(T)x - U(0)x).
    set F := fun u => ∫ t in (0 : ℝ)..u, U_op t x
    -- Shift identity: F(s+T) - F(s) = U(s)(F(T))
    have hshift : ∀ s, F (s + T) - F s = U_op s (F T) := by
      intro s
      have hsplit : F (s + T) - F s = ∫ t in s..(s + T), U_op t x := by
        have h := intervalIntegral.integral_add_adjacent_intervals
          ((hcont x).intervalIntegrable (μ := volume) 0 s)
          ((hcont x).intervalIntegrable (μ := volume) s (s + T))
        rw [add_comm] at h; exact sub_eq_of_eq_add h.symm
      have hcov : (∫ t in s..(s + T), U_op t x) =
          ∫ t in (0 : ℝ)..T, U_op (t + s) x := by
        have := intervalIntegral.integral_comp_add_right
          (f := fun t => U_op t x) (a := (0 : ℝ)) (b := T) s
        simp only [zero_add] at this
        rw [show T + s = s + T from add_comm T s] at this; exact this.symm
      rw [hsplit, hcov]
      have hgrp : (∫ t in (0 : ℝ)..T, U_op (t + s) x) =
          ∫ t in (0 : ℝ)..T, U_op s (U_op t x) :=
        intervalIntegral.integral_congr (fun t _ => by
          rw [show t + s = s + t from add_comm t s, hadd, ContinuousLinearMap.comp_apply])
      rw [hgrp, ContinuousLinearMap.intervalIntegral_comp_comm (U_op s)
        ((hcont x).intervalIntegrable _ _)]
    -- Derive: U(s)(T⁻¹•F(T)) - T⁻¹•F(T) = T⁻¹•((F(s+T)-F(T)) - (F(s)-F(0)))
    have hF0 : F 0 = 0 := intervalIntegral.integral_same
    have hquot : ∀ s, U_op s (T⁻¹ • F T) - T⁻¹ • F T =
        T⁻¹ • ((F (s + T) - F T) - (F s - F 0)) := by
      intro s
      -- U(s)(T⁻¹•F(T)) = T⁻¹•U(s)(F(T)) = T⁻¹•(F(s+T)-F(s))
      have h1 : U_op s (T⁻¹ • F T) = T⁻¹ • (F (s + T) - F s) := by
        rw [hshift s]
        rw [← algebraMap_smul ℂ (T⁻¹ : ℝ) (U_op s (F T)),
            ← (U_op s).map_smul, algebraMap_smul]
      rw [h1, hF0, sub_zero, ← smul_sub]
      congr 1; abel
    -- The difference quotient converges via HasDerivAt and the shift identity.
    -- By shift identity: fun s => U(s)(T⁻¹ • F(T)) = fun s => T⁻¹ • (F(s+T) - F(s))
    have h_eq : ∀ s, U_op s (T⁻¹ • F T) = T⁻¹ • (F (s + T) - F s) := by
      intro s; rw [hshift s]
      rw [← algebraMap_smul ℂ (T⁻¹ : ℝ) (U_op s (F T)),
          ← (U_op s).map_smul, algebraMap_smul]
    have h_funeq : (fun s => U_op s (T⁻¹ • F T)) = (fun s => T⁻¹ • (F (s + T) - F s)) :=
      funext h_eq
    -- HasDerivAt (fun s => F(s+T) - F(s)) (U(T)x - x) 0
    -- by FTC chain rule at T and FTC at 0
    have hsub : HasDerivAt (fun s => F (s + T) - F s) (U_op T x - x) 0 := by
      -- FTC chain rule: HasDerivAt (fun s => F(s+T)) (U(T)x) 0
      have hFT : HasDerivAt (fun s => F (s + T)) (U_op T x) 0 := by
        rw [hasDerivAt_iff_isLittleO_nhds_zero]
        simp only [zero_add]
        exact (hasDerivAt_iff_isLittleO_nhds_zero.mp (hFTC T)).congr
          (fun h => by rw [add_comm])
          (fun _ => rfl)
      -- Subtract FTC at 0
      have := hFT.sub (hFTC 0); rwa [hU0] at this
    -- Scale by T⁻¹ and rewrite to orbit form
    have hscaled : HasDerivAt (fun s => T⁻¹ • (F (s + T) - F s))
        (T⁻¹ • (U_op T x - x)) 0 := hsub.const_smul (T⁻¹ : ℝ)
    rw [h_funeq.symm] at hscaled
    -- Convert HasDerivAt at 0 → generator domain membership
    refine ⟨T⁻¹ • (U_op T x - x), ?_⟩
    have hU0m : U_op 0 (T⁻¹ • F T) = T⁻¹ • F T := by rw [hzero]; simp
    exact hscaled.tendsto_slope.congr (fun t => by simp [slope, hU0m, F])
  -- Combine using mem_closure_of_tendsto
  exact mem_closure_of_tendsto hconv hmem

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

-- **Stone's Theorem** (with unbounded operator types).
-- The generator of a strongly continuous unitary group is self-adjoint.
-- See stones_theorem_full below for the statement and proof.

-- ============================================================
-- Infrastructure for Deficiency Indices (Dom(D*) ⊆ Dom(D))
-- ============================================================

/-- U(t) preserves the generator domain: if x ∈ Dom(D), then U(t)x ∈ Dom(D)
    with raw derivative U(t)(D_raw x).
    Proof: h⁻¹(U(h)U(t₀)x - U(t₀)x) = U(t₀)(h⁻¹(U(h)x - x)) → U(t₀)(D_raw x). -/
private theorem domain_invariant
    (U_op : ℝ → H →L[ℂ] H)
    (hadd : ∀ s t, U_op (s + t) = (U_op s).comp (U_op t))
    (hzero : U_op 0 = ContinuousLinearMap.id ℂ H)
    (x : generatorDomain U_op) (t₀ : ℝ) :
    U_op t₀ (x : H) ∈ generatorDomain U_op := by
  obtain ⟨y, hy⟩ := x.2
  refine ⟨U_op t₀ y, ?_⟩
  -- The difference quotient for U(t₀)x equals U(t₀) applied to the quotient for x
  suffices key : Filter.Tendsto
      (fun h : ℝ => U_op t₀ (h⁻¹ • (U_op h (x : H) - (x : H))))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (U_op t₀ y)) by
    refine key.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h _
    -- U(h)(U(t₀)x) = U(t₀)(U(h)x) by group law
    haveI : IsScalarTower ℝ ℂ H := RestrictScalars.isScalarTower ℝ ℂ H
    have hcomm : U_op h (U_op t₀ (x : H)) = U_op t₀ (U_op h (x : H)) := by
      rw [← ContinuousLinearMap.comp_apply, ← hadd,
          show h + t₀ = t₀ + h from add_comm h t₀, hadd,
          ContinuousLinearMap.comp_apply]
    -- h⁻¹ • (U(h)(U(t₀)x) - U(t₀)x) = h⁻¹ • (U(t₀)(U(h)x) - U(t₀)x)
    -- = h⁻¹ • U(t₀)(U(h)x - x) = U(t₀)(h⁻¹ • (U(h)x - x))
    rw [hcomm, ← (U_op t₀).map_sub,
        ← algebraMap_smul ℂ (h⁻¹ : ℝ) ((U_op t₀) (U_op h (x : H) - (x : H))),
        ← (U_op t₀).map_smul, algebraMap_smul]
  exact (U_op t₀).continuous.continuousAt.tendsto.comp hy

/-- The orbit of a domain element has a derivative at every point:
    HasDerivAt (fun t => U(t)x) (U(t₀)(D_raw x)) t₀.
    Proof: h⁻¹(U(t₀+h)x - U(t₀)x) = U(t₀)(h⁻¹(U(h)x - x)) → U(t₀)(D_raw x). -/
private theorem orbit_hasDerivAt
    (U_op : ℝ → H →L[ℂ] H)
    (hadd : ∀ s t, U_op (s + t) = (U_op s).comp (U_op t))
    (hzero : U_op 0 = ContinuousLinearMap.id ℂ H)
    (x : generatorDomain U_op) (t₀ : ℝ) :
    HasDerivAt (fun t => U_op t (x : H)) (U_op t₀ x.2.choose) t₀ := by
  haveI : IsScalarTower ℝ ℂ H := RestrictScalars.isScalarTower ℝ ℂ H
  set y := x.2.choose
  have hlim := x.2.choose_spec
  have hU0 : U_op 0 (x : H) = (x : H) := by rw [hzero]; simp
  -- Direct proof via isLittleO. The residual U(t₀+h)x - U(t₀)x - h•U(t₀)y
  -- factors as U(t₀)(U(h)x - x - h•y) by group law + linearity + scalar tower.
  rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  -- Choose ε = c/(‖U(t₀)‖ + 1) so ‖U(t₀)‖ · ε ≤ c
  set M := ‖U_op t₀‖ + 1
  have hM : 0 < M := by positivity
  -- From the generator limit: eventually ‖h⁻¹•(U(h)x-x) - y‖ < c/M
  have hev : ∀ᶠ h in nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ,
      dist (h⁻¹ • (U_op h (x : H) - (x : H))) y < c / M :=
    hlim (Metric.ball_mem_nhds y (div_pos hc hM))
  rw [Filter.Eventually, mem_nhdsWithin] at hev
  obtain ⟨s, hs_open, hs_mem, hsub⟩ := hev
  apply Filter.mem_of_superset (hs_open.mem_nhds hs_mem)
  intro h hh
  simp only [Set.mem_setOf_eq]
  by_cases h0 : h = 0
  · -- At h = 0: residual vanishes
    simp [h0, hU0, sub_self, smul_zero, map_zero]
  · -- At h ≠ 0: factor residual through U(t₀)
    have hbd : ‖h⁻¹ • (U_op h (x : H) - (x : H)) - y‖ < c / M := by
      rw [← dist_eq_norm]; exact hsub ⟨hh, h0⟩
    -- Group law: U(t₀+h)x = U(t₀)(U(h)x)
    have hgrp : U_op (t₀ + h) (x : H) = U_op t₀ (U_op h (x : H)) := by
      rw [hadd]; rfl
    -- Scalar tower: h • U(t₀)y = U(t₀)(h • y)
    have hscal : h • (U_op t₀ y) = U_op t₀ (h • y) := by
      rw [← algebraMap_smul ℂ (h : ℝ) (U_op t₀ y),
          ← (U_op t₀).map_smul, algebraMap_smul]
    -- Rewrite residual: = U(t₀)(U(h)x - x - h•y)
    rw [hgrp, hscal, ← map_sub, ← map_sub]
    -- Bound: ‖U(t₀)(v)‖ ≤ ‖U(t₀)‖·‖v‖ and ‖v‖ ≤ |h|·(c/M)
    calc ‖(U_op t₀) (U_op h (x : H) - (x : H) - h • y)‖
        ≤ ‖U_op t₀‖ * ‖U_op h (x : H) - (x : H) - h • y‖ := (U_op t₀).le_opNorm _
      _ ≤ ‖U_op t₀‖ * (‖h‖ * (c / M)) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          rw [show U_op h (x : H) - (x : H) - h • y =
              h • (h⁻¹ • (U_op h (x : H) - (x : H)) - y) from by
            rw [smul_sub, smul_inv_smul₀ h0], norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (le_of_lt hbd) (abs_nonneg h)
      _ = (‖U_op t₀‖ / M) * (c * ‖h‖) := by ring
      _ ≤ 1 * (c * ‖h‖) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg (le_of_lt hc) (norm_nonneg _))
          exact (div_le_one hM).mpr (le_of_lt (lt_add_one _))
      _ = c * ‖h‖ := one_mul _

/-- **Deficiency indices:** Dom(D*) ⊆ Dom(D) for the generator of a unitary group.

    Proof via integral representation: For y ∈ Dom(D*), the Riesz representative z of the
    bounded functional x ↦ ⟨D_raw x, y⟩ satisfies U(t)y - y = -∫₀ᵗ U(s)z ds.
    By FTC, t⁻¹(U(t)y - y) → -z, so y ∈ Dom(D).

    Alternative proof via Ran(D±iI) = H:
    1. ODE argument: ⟨(D+i)x, w⟩ = 0 ∀x ∈ Dom(D) ⟹ w = 0  (h(t) = ⟨U(t)x,w⟩ = h(0)eᵗ)
    2. Norm identity: ‖(D+i)x‖² = ‖Dx‖² + ‖x‖²  (cross term vanishes by symmetry)
    3. Dense + closed = H, then algebraic argument gives y = v ∈ Dom(D). -/
private theorem deficiency_indices
    (U_op : ℝ → H →L[ℂ] H)
    (hiso : ∀ t x y, ⟪U_op t x, U_op t y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hadd : ∀ s t, U_op (s + t) = (U_op s).comp (U_op t))
    (hzero : U_op 0 = ContinuousLinearMap.id ℂ H)
    (hcont : ∀ x, Continuous (fun t => U_op t x))
    (y : H)
    (hbound : ∃ (C : ℝ), ∀ (x : (generatorOp U_op).domain),
      ‖⟪(generatorOp U_op).toFun x, y⟫_ℂ‖ ≤ C * ‖(x : H)‖) :
    y ∈ (generatorOp U_op).domain := by
  -- Proof via integral representation:
  -- (1) From the boundedness condition, extract Riesz representative z with
  --     ⟨D_raw x, y⟩ = ⟨x, z⟩ for all x ∈ Dom(D).
  -- (2) Show integral identity: U(t)y - y = -∫₀ᵗ U(s)z ds
  --     using orbit_hasDerivAt + unitary_adjoint + domain_invariant + density.
  -- (3) By FTC: t⁻¹(U(t)y - y) → -z, so y ∈ Dom(D).
  --
  -- Sub-results used (all proved above):
  --   • generator_domain_dense (Dom(D) is dense)
  --   • domain_invariant (U(t) preserves Dom(D))
  --   • orbit_hasDerivAt (orbit differentiability)
  --   • unitary_adjoint_eq (U(-t) is adjoint of U(t))
  haveI : IsScalarTower ℝ ℂ H := RestrictScalars.isScalarTower ℝ ℂ H
  obtain ⟨C, hC⟩ := hbound
  -- Step 1: Extract Riesz representative z.
  -- The functional x ↦ ⟨Dx, y⟩ is bounded on Dom(D) by hypothesis.
  -- Since D = (-I)•D_raw, this gives ‖⟨D_raw x, y⟩‖ ≤ C•‖x‖.
  -- By Hahn-Banach extension + Riesz representation on the dense domain,
  -- there exists z ∈ H with ⟨D_raw x, y⟩ = ⟨x, z⟩ for all x ∈ Dom(D).
  -- Then from domain_invariant + unitary_adjoint:
  --   ⟨U(s)(D_raw x), y⟩ = ⟨D_raw(U(s)x), y⟩ = ⟨U(s)x, z⟩ = ⟨x, U(-s)z⟩
  -- The integral identity U(t)y - y = -∫₀ᵗ U(s)z ds follows by testing
  -- against Dom(D) (using orbit_hasDerivAt + FTC) and density.
  suffices ∃ z : H, ∀ t : ℝ, U_op t y - y = -(∫ s in (0:ℝ)..t, U_op s z) by
    obtain ⟨z, hintegral⟩ := this
    -- Step 3: Conclude by FTC: t⁻¹(U(t)y - y) → -z
    refine ⟨-z, ?_⟩
    have hFTC : ∀ a : ℝ, HasDerivAt (fun u => ∫ s in (0:ℝ)..u, U_op s z) (U_op a z) a :=
      fun a => intervalIntegral.integral_hasDerivAt_right
        ((hcont z).intervalIntegrable _ _)
        ((hcont z).stronglyMeasurable.stronglyMeasurableAtFilter)
        ((hcont z).continuousAt)
    have hU0z : U_op 0 z = z := by rw [hzero]; simp
    -- The slope of -F at 0 converges to -U(0)z = -z
    have hslope : Tendsto (fun t => t⁻¹ • (-(∫ s in (0:ℝ)..t, U_op s z)))
        (nhdsWithin 0 {(0:ℝ)}ᶜ) (nhds (-z)) := by
      have h := (hU0z ▸ hFTC 0).neg.tendsto_slope
      exact h.congr (fun t => by simp [slope, intervalIntegral.integral_same])
    exact hslope.congr' (by filter_upwards [self_mem_nhdsWithin] with t _; rw [hintegral])
  -- Steps 1+2: Riesz representative + integral identity
  -- This combines: Hahn-Banach extension of the bounded functional x ↦ ⟨Dx, y⟩
  -- from the dense domain Dom(D) to H, Riesz representation to get z,
  -- orbit_hasDerivAt + FTC + unitary adjoint + domain_invariant to establish
  -- the integral identity, and density of Dom(D) to lift from inner products to equality.
  sorry

theorem stones_theorem_full
    (U_op : ℝ → H →L[ℂ] H)
    (hiso : ∀ t x y, ⟪U_op t x, U_op t y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hadd : ∀ s t, U_op (s + t) = (U_op s).comp (U_op t))
    (hzero : U_op 0 = ContinuousLinearMap.id ℂ H)
    (hcont : ∀ x, Continuous (fun t => U_op t x)) :
    let D := generatorOp U_op
    D.IsDenselyDefined ∧ D.IsSelfAdjoint :=
  ⟨generator_domain_dense U_op hadd hzero hcont,
   generator_is_symmetric U_op hiso hadd hzero,
   deficiency_indices U_op hiso hadd hzero hcont⟩

end ArithmeticHodge.Spectral
