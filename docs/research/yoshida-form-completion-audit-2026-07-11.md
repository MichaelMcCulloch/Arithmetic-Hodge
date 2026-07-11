# Yoshida form-completion audit

Date: 2026-07-11

Status: critical architecture correction with a strict-compiling generic
complete-square prototype. This note changes the intended application of the
existing coercive-correction infrastructure; it does not invalidate those
generic theorems.

## Finding

Yoshida does not apply Riesz representation to the high Fourier tail equipped
with its ordinary `L²([-a,a])` norm. He first proves the Hermitian form is
positive and coercive on the algebraic high tail, equips that tail with the
form norm

```text
‖v‖_form = sqrt((v,v)),
```

and completes it. The low-mode pairing is then proved bounded in this form
norm, and Riesz representation is applied in that completion.

This distinction is necessary. The Fourier multiplier of the local form
grows logarithmically with frequency, so the form is not a bounded
sesquilinear form on ordinary circle `L²`. Therefore an application of
`ComplexCoerciveRieszCorrection` with `H = circle L²` would require a false
continuity premise.

The existing generic real/complex Lax--Milgram modules remain mathematically
correct and useful. The superseded part is only the proposed direct
instantiation on Haar `L²` for Yoshida's unbounded local form.

## Primary-source route

The source is Hiroyuki Yoshida, *On Hermitian Forms attached to Zeta
Functions*, especially sections 3, 4, and 6:

- DOI: <https://doi.org/10.2969/aspm/02110281>
- PDF: <https://projecteuclid.org/download/pdf_1/euclid.aspm/1534359132>

The relevant construction is:

1. Lemma 3 proves, for sufficiently high Fourier tails, a lower bound

   ```text
   (phi,phi) >= mu * ‖phi‖_L2^2.
   ```

2. Section 4 treats the positive form itself as the pre-Hilbert inner
   product, completes the algebraic tail, and extends its pairing.
3. The coercive lower bound makes a form-norm Cauchy sequence also `L²`
   Cauchy, yielding the canonical injection of the completion into `L²`.
4. Proposition 3 proves boundedness of each low-mode pairing in the form
   norm and applies Riesz representation in the completed tail.
5. Section 6 specializes this to the odd 10-mode and even 200-mode blocks.

The exact source estimates have the form

```text
|ell_i(v)|^2 <= S_i / mu          when ‖v‖_form = 1,
```

so the Riesz representative satisfies

```text
‖v_i‖_form^2 = ‖ell_i‖^2 <= S_i / mu.
```

This is why the odd and even correction budgets are `1/40` and `1/2000`.

## Source-faithful algebraic boundary

Once the tail completion `K` is a complex Hilbert space, no Lax--Milgram
theorem is needed. For `ell : StrongDual ℂ K`, use the ordinary Riesz
equivalence:

```lean
noncomputable def hilbertTailRieszCorrection
    (ell : StrongDual ℂ K) : K :=
  (InnerProductSpace.toDual ℂ K).symm ell
```

It satisfies

```lean
⟪hilbertTailRieszCorrection ell, x⟫_ℂ = ell x
‖hilbertTailRieszCorrection ell‖ = ‖ell‖.
```

For a finite low Gram `A` and low-tail functionals `ell i`, define

```lean
hilbertTailCorrectedGram A ell i j =
  A i j - ⟪v_i, v_j⟫_ℂ.
```

The exact completion-of-the-square identity is

```text
c* A c
  + sum_i conj(c_i) ell_i(x)
  + sum_i c_i conj(ell_i(x))
  + <x,x>
= c* G c + <x + sum_i c_i v_i, x + sum_i c_i v_i>.
```

Thus `G.PosDef` implies strict positivity of the original finite-low plus
tail form for every nonzero pair `(c,x)`. Correction entries obey

```text
norm(<v_i,v_j>) <= norm(ell_i) * norm(ell_j).
```

This is precisely the algebra used in Yoshida (6.12)--(6.15) and
(6.20)--(6.23), without representing the unbounded local form as a bounded
map on `L²`.

## Strict Lean prototype

The source-faithful generic layer strict-compiles in
`/tmp/HilbertTailSchurProbe.lean`, SHA-256
`e8bc4416f7da4c1434dfcf4400a515af2f029712a6cd1eeac6178b4a38031576`.
It contains:

- `hilbertTailRieszCorrection` and its evaluation/norm theorems;
- `hilbertTailCorrectedGram`;
- `hilbertTail_complete_square`;
- `hilbertTail_quadratic_re_pos`;
- `norm_hilbertTail_correction_pairing_le`.

Root ran

```text
lake env lean -DwarningAsError=true /tmp/HilbertTailSchurProbe.lean
```

with exit zero. The positivity theorem uses only
`[propext, Classical.choice, Quot.sound]`, and the probe has no forbidden
proof mechanism.

## Lean construction still needed

The remaining representation layer should use a type synonym for the
algebraic tail so it can carry the form-derived norm without colliding with
its pre-existing `L²` norm. Given an algebraic sesquilinear form `B`, Hermitian
symmetry, and strict positivity:

1. build `InnerProductSpace.Core ℂ FormNormTail` with `inner = B`;
2. install its generated normed-group, normed-space, and inner-product
   structures locally;
3. use `UniformSpace.Completion FormNormTail` as Yoshida's completed tail;
4. extend the low-mode functional from the dense algebraic tail using its
   form-norm bound;
5. use Lemma 3's coercivity to construct and prove injective the canonical
   map from the form completion to circle `L²` when the downstream statement
   needs an `L²` representative.

Mathlib already supplies the completion inner-product instance in
`Mathlib.Analysis.InnerProductSpace.Completion` and the Riesz equivalence in
`Mathlib.Analysis.InnerProductSpace.Dual`.

## Plan consequence

Do not execute the previous `HermitianTailCorrection` plan as the next
Yoshida application layer. Replace it with:

1. the generic `HilbertTailSchur` module represented by the strict probe;
2. a form-norm type synonym and inner-product-core construction;
3. completion and bounded-functional extension;
4. the concrete Fourier-tail coercivity and coupling estimates.

The prior coercive-Riesz modules remain in production as reviewed generic
infrastructure, but they are no longer the critical route to Yoshida's
section 6 argument.
