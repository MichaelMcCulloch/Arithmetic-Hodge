import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Real.Basic

set_option autoImplicit false

open scoped BigOperators
open Polynomial

namespace ArithmeticHodge.Analysis

noncomputable section

/-!
# Linear independence of finite Cauchy feature families

This is the strictness step behind finite Stieltjes--Loewner Gram kernels.
The proof is Lagrange interpolation, not a determinant evaluation or a
numerical spectral calculation.
-/

/-- The Cauchy feature attached to a node, sampled at the pole family. -/
def cauchyFeature
    {ι : Type*} (node pole : ι → ℝ) (i : ι) : ι → ℝ :=
  fun k ↦ (pole k + node i)⁻¹

theorem linearIndependent_cauchyFeature
    {ι : Type*} [Fintype ι]
    (node pole : ι → ℝ)
    (hnode : Function.Injective node)
    (hpole : Function.Injective pole)
    (hdisjoint : ∀ i k, pole k + node i ≠ 0) :
    LinearIndependent ℝ (cauchyFeature node pole) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  let reflectedNode : ι → ℝ := fun i ↦ -node i
  have hreflected : Function.Injective reflectedNode := by
    intro i j hij
    apply hnode
    dsimp [reflectedNode] at hij
    linarith
  have hreflectedOn : Set.InjOn reflectedNode
      ((Finset.univ : Finset ι) : Set ι) :=
    hreflected.injOn
  have hpoleOn : Set.InjOn pole
      ((Finset.univ : Finset ι) : Set ι) := hpole.injOn
  have hweight (i : ι) :
      Lagrange.nodalWeight Finset.univ reflectedNode i ≠ 0 :=
    Lagrange.nodalWeight_ne_zero hreflectedOn (Finset.mem_univ i)
  let value : ι → ℝ := fun i ↦
    c i / Lagrange.nodalWeight Finset.univ reflectedNode i
  let interpolant : ℝ[X] :=
    Lagrange.interpolate Finset.univ reflectedNode value
  have hcoordinate (k : ι) :
      ∑ i, c i * (pole k + node i)⁻¹ = 0 := by
    have hk := congrFun hc k
    simpa only [cauchyFeature, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply] using hk
  have hpole_ne_reflected (k i : ι) :
      pole k ≠ reflectedNode i := by
    intro h
    apply hdisjoint i k
    dsimp [reflectedNode] at h
    linarith
  have hterm (k i : ι) :
      Lagrange.nodalWeight Finset.univ reflectedNode i *
          (pole k - reflectedNode i)⁻¹ * value i =
        c i * (pole k + node i)⁻¹ := by
    have hw :
        Lagrange.nodalWeight Finset.univ (fun i ↦ -node i) i ≠ 0 := by
      simpa only [reflectedNode] using hweight i
    dsimp [value, reflectedNode]
    field_simp [hw, hdisjoint i k]
    ring
  have heval (k : ι) : Polynomial.eval (pole k) interpolant = 0 := by
    rw [show interpolant =
        Lagrange.interpolate Finset.univ reflectedNode value by rfl]
    rw [Lagrange.eval_interpolate_not_at_node value
      (fun i _ ↦ hpole_ne_reflected k i)]
    rw [show (∑ i ∈ Finset.univ,
          Lagrange.nodalWeight Finset.univ reflectedNode i *
            (pole k - reflectedNode i)⁻¹ * value i) = 0 by
      simpa only [Finset.sum_filter, Finset.mem_univ, if_true,
        hterm k] using hcoordinate k]
    ring
  have hinterpolant_zero : interpolant = 0 := by
    apply Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero
      Finset.univ hpoleOn
    · exact Lagrange.degree_interpolate_lt value hreflectedOn
    · intro k _
      exact heval k
  intro i
  have hvalue : value i = 0 := by
    rw [← Lagrange.eval_interpolate_at_node value hreflectedOn
      (Finset.mem_univ i)]
    rw [← show interpolant =
      Lagrange.interpolate Finset.univ reflectedNode value by rfl]
    rw [hinterpolant_zero]
    simp
  dsimp [value] at hvalue
  exact (div_eq_zero_iff.mp hvalue).resolve_right (hweight i)

end

end ArithmeticHodge.Analysis
