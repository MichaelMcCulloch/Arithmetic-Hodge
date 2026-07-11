# Yoshida even-block interval-Schur soundness

Date: 2026-07-11

Status: strict-compiling generic checker prototype. No 200-stage Yoshida data
artifact has yet been generated, so this is infrastructure rather than the
even-block certificate or a proof of ratio-two positivity.

## Result

The probe `/tmp/YoshidaIntervalSchurProbe.lean` implements exact rational
outward interval arithmetic, a sound scalar-pivot Schur theorem, and a
recursive interval certificate that proves positive definiteness for every
contained exact Hermitian rational matrix after casting to `ℂ`.

Root independently ran

```text
lake env lean -DwarningAsError=true /tmp/YoshidaIntervalSchurProbe.lean
```

with exit zero. Every audited theorem depends only on
`[propext, Classical.choice, Quot.sound]`; the probe contains no `sorry`,
`admit`, custom axiom, `unsafe`, or `native_decide`.

Artifact hashes at verification time:

```text
fc88b4e04874ca5913a2eb35b562add13af93c895e82ae8f78d670d1fb832f2b  YoshidaIntervalSchurProbe.lean
cd441c8a7d15bf877a4b3633cdedd946c06d30db951f3408e9b6d3ec91aedb28  yoshida-interval-schur-soundness.md
```

The `/tmp` paths are not durable. Production promotion must copy and review
the exact definitions before reboot.

## Exact interval layer

The interval structure stores rational endpoints and validity:

```lean
structure RatInterval where
  lo : ℚ
  hi : ℚ
  valid : lo ≤ hi

def RatInterval.Contains (I : RatInterval) (x : ℚ) : Prop :=
  I.lo ≤ x ∧ x ≤ I.hi
```

The checked outward operations are:

- `RatInterval.point`;
- `RatInterval.sub` and `sub_contains`;
- four-corner `RatInterval.mul` and `mul_contains`;
- positive reciprocal `RatInterval.posInv` and `posInv_contains`;
- `RatInterval.div` and `div_contains`, requiring `0 < denominator.lo`;
- `RatInterval.pos_of_contains`.

No multiplication monotonicity is assumed across unknown signs. The
four-corner minimum and maximum proof handles every sign pattern explicitly.
Division cannot cross zero because the lower endpoint positivity proof is a
constructor input.

## Exact matrix layer

The generic block theorem is polymorphic over `RCLike`:

```lean
theorem posDef_fromBlocks₁₁_of_schur
    {𝕜 m n : Type*} [RCLike 𝕜]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m m 𝕜) (B : Matrix m n 𝕜) (D : Matrix n n 𝕜)
    (hA : A.PosDef) (hS : (D - Bᴴ * A⁻¹ * B).PosDef) :
    (Matrix.fromBlocks A B Bᴴ D).PosDef
```

Its scalar specialization proves positivity from a positive pivot and a
positive Schur complement:

```lean
theorem posDef_from_scalar_pivot
    (p : 𝕜) (b : n → 𝕜) (D : Matrix n n 𝕜)
    (hp : 0 < p) (hS : (scalarSchur p b D).PosDef) :
    (Matrix.fromBlocks (singletonPivot p) (pivotRow b)
      (pivotRow b)ᴴ D).PosDef
```

`intervalScalarSchur` computes the enclosure

```text
D[i,j] - (B[i] * B[j]) / P,
```

and `intervalScalarSchur_contains` proves that it contains the exact rational
Schur update under the componentwise input containment hypotheses.

## Recursive universal certificate

The nested index avoids repeatedly deleting an arbitrary finite index:

```text
SchurIndex 0       = Empty
SchurIndex (k + 1) = Unit ⊕ SchurIndex k.
```

The recommended certificate is

```lean
inductive RationalIntervalUniversalCert : (k : ℕ) →
    Matrix (SchurIndex k) (SchurIndex k) RatInterval → Prop
```

At each `step`, it stores a pivot interval `P`, coupling row `B`, tail interval
matrix `D`, a proof `0 < P.lo`, and the recursive certificate for
`intervalScalarSchur P B D`. Its universal soundness theorem is:

```lean
theorem RationalIntervalUniversalCert.complexPosDef_of_contains
    (cert : RationalIntervalUniversalCert k I)
    (hIA : IntervalMatrixContains I A) (hA : A.IsHermitian) :
    (A.map fun q ↦ (q : ℂ)).PosDef
```

This theorem validates all exact Hermitian matrices inside the top interval
box. It does not trust an external floating-point inertia calculation and it
does not assume the analytic Yoshida Gram lies in that box.

## Live regression

The probe constructs the exact matrix

```text
[[2, 1],
 [1, 2]]
```

on `SchurIndex 2`. Point intervals compute the second pivot `3/2` using the
actual interval operations. The final theorem is derived through the
universal recursive checker and has only the standard axioms.

## 200-stage generation protocol

1. Reindex the exact rational comparison matrix from `Fin 200` to
   `SchurIndex 200` and prove the `Matrix.submatrix` equality.
2. Emit each interval stage as a named definition/theorem, not one 200-deep
   term, to bound elaborator depth and enable `.olean` caching.
3. At every stage, kernel-check `0 < P.lo` and the equality between the
   computed interval Schur matrix and the normalized rational literals for
   the next stage.
4. Prove componentwise containment of the exact top rational matrix and its
   Hermitian property.
5. Invoke `complexPosDef_of_contains`, then transport positive definiteness
   back across the finite-index equivalence.
6. Use `norm_num` or `decide +kernel`; never `native_decide`.

## Remaining risks

- No generated Yoshida 200-stage term has tested compile time or memory.
- The `Fin 200 ≃ SchurIndex 200` reindex proof is not yet instantiated.
- Endpoint generation remains external discovery until exact rational
  containment is replayed in Lean.
- The checker proves positivity of the rational comparison matrix; certified
  analytic enclosures connecting that matrix to the corrected Gram remain a
  separate obligation.

Before producing all 200 stages, benchmark generated 10-, 25-, and 50-stage
prefixes from the actual even matrix. The 10-stage prefix is also the first
useful regression for agreement between the generator and the Lean checker.
