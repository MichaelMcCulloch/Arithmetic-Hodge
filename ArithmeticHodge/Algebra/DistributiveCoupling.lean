/-
  LAYER 0: The Distributive Coupling — Algebraic Infrastructure

  This layer establishes the algebraic properties of ℤ that underlie
  the entire chain. Everything here is provable from Mathlib's existing
  algebra library — no sorry's needed.

  Key facts:
  - The distributive law couples + and × perfectly (ring axiom)
  - ℤ is a PID (class number 1 — no hidden multiplicative structure)
  - ℤ is a UFD (unique factorization into primes)
  - ℤ is a Euclidean domain (division algorithm exists)
-/

import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Ring.Basic

namespace ArithmeticHodge.Algebra

-- ============================================================
-- The Distributive Law as the Coupling of + and ×
-- ============================================================

/-- The distributive law is the sole axiom coupling addition and multiplication.
    In a commutative ring, it holds perfectly and symmetrically.
    This is the "Markov blanket" between additive and multiplicative structure. -/
theorem perfect_distribution {R : Type*} [CommRing R] (a b c : R) :
    a * (b + c) = a * b + a * c :=
  mul_add a b c

/-- Right distribution follows from commutativity + left distribution. -/
theorem perfect_distribution_right {R : Type*} [CommRing R] (a b c : R) :
    (a + b) * c = a * c + b * c :=
  add_mul a b c

/-- Distribution over subtraction — the coupling respects negation. -/
theorem distribution_sub {R : Type*} [CommRing R] (a b c : R) :
    a * (b - c) = a * b - a * c :=
  mul_sub a b c

/-- Distribution over finite sums — the coupling extends to all finite combinations. -/
theorem distribution_sum {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    (a : R) (f : ι → R) :
    a * (∑ i, f i) = ∑ i, a * f i :=
  Finset.mul_sum Finset.univ f a

-- ============================================================
-- Structural Properties of ℤ
-- ============================================================

/-- ℤ is a principal ideal domain: class number 1. -/
instance : IsPrincipalIdealRing ℤ := inferInstance

/-- ℤ is a unique factorization domain. -/
instance : UniqueFactorizationMonoid ℤ := inferInstance

/-- ℤ is a Euclidean domain. -/
instance : EuclideanDomain ℤ := inferInstance

-- ============================================================
-- The Ring Axioms Are Complete
-- ============================================================

/-- The distributive law holds universally — no exceptional inputs. -/
theorem distribution_universal (R : Type*) [CommRing R] :
    ∀ a b c : R, a * (b + c) = a * b + a * c :=
  fun a b c => mul_add a b c

/-- Commutativity of multiplication. -/
theorem mul_comm_Z : ∀ a b : ℤ, a * b = b * a :=
  fun a b => mul_comm a b

-- ============================================================
-- Absorption and Annihilation
-- ============================================================

/-- Zero absorbs multiplication — a consequence of distribution. -/
theorem zero_absorbs {R : Type*} [CommRing R] (a : R) : 0 * a = 0 :=
  zero_mul a

/-- Negation interacts correctly with multiplication — forced by distribution. -/
theorem neg_one_mul' {R : Type*} [CommRing R] (a : R) : (-1) * a = -a :=
  neg_one_mul a

-- ============================================================
-- Properties of ℤ as a Ring
-- ============================================================

/-- ℤ is an integral domain. -/
instance : IsDomain ℤ := inferInstance

/-- ℤ has characteristic zero. -/
instance : CharZero ℤ := inferInstance

end ArithmeticHodge.Algebra
