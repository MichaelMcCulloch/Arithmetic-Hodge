# Gate 3 support-localization cross-term audit

Status: source-level route audit.  The identities below identify the next
formal target; they are not yet exported Lean theorems.

## Question tested

Once the three finite certificates specialize the existing conditional
support-ratio-at-most-two theorem, can it be promoted to all Bombieri tests by
decomposing a test into disjoint narrow multiplicative support bands and
summing the positivity of the pieces?

The answer is **not by a diagonal-only argument**.  Disjoint support bands are
not orthogonal for the production autocorrelation.  A multiplicative shift by
a prime maps one band directly into another, producing cross terms in
`primeSum`.

## First exact obstruction: a dyadic pair

Choose `0 < ε` with `exp (2*ε) < 3/2`, and a real nonnegative Bombieri bump
`η` with `tsupport η ⊆ Ioo (exp (-ε)) (exp ε)` and `η 1 = 1`.  Such bumps are supplied
by `exists_bombieri_bump_log_near_one`.  Define

```lean
h := normalizedDilation (1 / 2) (by norm_num) η
```

Put `a = exp (-ε)` and `b = exp ε`.  Then
`h x = sqrt (1/2) * η ((1/2)*x)`, so
`tsupport h ⊆ Ioo (2*a) (2*b)`.  Moreover
`b/a = exp (2*ε) < 3/2`, hence `b < 2*a`.  Consequently:

- `tsupport η` and `tsupport h` are disjoint;
- each individual support has ratio `exp (2*ε) < 2`, hence its quadratic
  prime sum is zero by
  `primeSum_bombieriQuadraticTest_eq_zero_of_support_ratio_le_two`;
- `tsupport (η+h) ⊆ Icc a (2*b)`.  This interval hull has endpoint ratio
  `R = 2*exp (2*ε) < 3`, so the quadratic support is contained in
  `[1/R,R]`; `Λ(1)=0`, and direct and transpose evaluations vanish at every
  integer `n ≥ 3`; hence only the integer `2` can contribute to the prime
  sum; and
- at the dyadic shift,

  ```text
  bombieriQuadraticTest (η + h) 2
    = sqrt (1/2) * integral y in Ioi 0, normSq (η y).
  ```

The two diagonal autocorrelations vanish at `2`.  Of the two mixed
orientations, `η(2y) ≠ 0` forces `y ∈ (a/2,b/2)`, whereas `h(y) ≠ 0` forces
`y ∈ (2*a,2*b)`; these intervals are disjoint because `b/2 < 2*a`.  Thus
`η(2y) * conj(h(y))` vanishes, while
`h(2y) * conj(η(y)) = sqrt(1/2) * normSq(η(y))`.

For `q = bombieriQuadraticTest (η+h)`, the relevant natural-number index is
`1`, because `primeKernel q k` evaluates at `k+1`.  Quadratic transpose
symmetry gives

```text
primeKernel q 1 = q 2 + transpose q 2 = q 2 + conj (q 2) = 2 * q 2.
```

Together with `Λ(2)=log 2`, the expected exact complex identity is

```text
primeSum q
  = ((2 * log 2 * sqrt (1/2) *
      integral y in Ioi 0, normSq (η y) : ℝ) : ℂ),
(primeSum q).im = 0,
0 < (primeSum q).re.
```

This proves that the production prime contribution is not additive across
even disjoint ratio-two bands.  Since `bombieriFunctional` subtracts
`primeSum`, the omitted dyadic interaction has a strictly negative sign in
the full quadratic functional.

This audit does **not** claim that the full quadratic cross term is negative.
The polar and archimedean cross terms may compensate for the prime term.  That
compensation is precisely what a valid local-to-global theorem must control.

## Necessary production pairing

The next infrastructure should polarize the actual production quadratic,
not merely its local critical-form restriction:

```lean
def bombieriQuadraticValue (g : BombieriTest) : ℂ :=
  bombieriFunctional (bombieriQuadraticTest g)

def bombieriProductionPairing (f g : BombieriTest) : ℂ :=
  (1 / 4 : ℂ) *
    (bombieriQuadraticValue (f + g) -
      bombieriQuadraticValue (f - g) -
      Complex.I *
        (bombieriQuadraticValue (f + Complex.I • g) -
          bombieriQuadraticValue (f - Complex.I • g)))
```

The minus-`I` sign is the Mathlib convention: the reconstructed pairing is
conjugate-linear in its first argument and linear in its second.  Before using
it, prove Hermitian sesquilinearity and the diagonal reconstruction
`bombieriProductionPairing g g = bombieriQuadraticValue g`.

The first make-or-break theorem is the two-band Schur inequality for the
dyadic pair:

```text
normSq (bombieriProductionPairing η h)
  <= (bombieriQuadraticValue η).re * (bombieriQuadraticValue h).re.
```

Ratio-two strict positivity supplies nonnegative (indeed positive for
nonzero tests) diagonal values, and normalized-dilation invariance makes the
two diagonal values equal.  Under Hermitian sesquilinearity and diagonal
reconstruction, the displayed determinant inequality is necessary and
sufficient for nonnegativity on every phase combination `η + c • h`.  It
should be attacked before any general partition-of-unity machinery is built.

For a finite index type `Fin n`, an exact decomposition
`g = ∑ i, p i`, and the pairing reconstruction identity, the genuinely
sufficient statement is positivity of the entire localization Gram matrix

```text
(fun i j => bombieriProductionPairing (p i) (p j)).PosSemidef.
```

Pairwise Cauchy--Schwarz inequalities do not suffice for three or more bands.
A diagonal-dominance or operator-norm estimate would be sufficient, but no
such production estimate currently exists in the repository.  Proving Gram
positivity for arbitrary ratio-two pieces is close to restating the
all-support problem, so the dyadic two-band inequality is the correct
adversarial test of whether this route has new content.

## Existing source support

- Functional and subtractive prime term:
  `MultiplicativeWeilFunctional.lean`, `bombieriFunctional_apply`.
- Actual autocorrelation definition:
  `MultiplicativeWeil.lean`, `autocorrelation`.
- Autocorrelation and its ratio support:
  `MultiplicativeWeilQuadratic.lean`, `bombieriQuadraticTest_apply`.
- Prime kernel, summand, and finite sum:
  `MultiplicativeWeilPrime.lean`.
- Ratio-two endpoint vanishing:
  `MultiplicativeWeilQuadraticEndpoint.lean`.
- Normalized dilation and support transport:
  `MultiplicativeWeilDilation.lean`.
- Quadratic transpose/conjugation and reality:
  `MultiplicativeWeilQuadraticReality.lean`,
  `transpose_bombieriQuadraticTest_apply_eq_conj`.
- Local critical form and ratio-two identification:
  `MultiplicativeWeilLocalCriticalForm.lean` and
  `MultiplicativeWeilQuadraticEndpoint.lean`.
- Suitable bumps:
  `MultiplicativeWeilApproximateIdentity.lean`.
- Terminal RH equivalence:
  `MultiplicativeWeilLiCriterionClosure.lean`,
  `riemannHypothesis_iff_bombieriQuadratic_re_nonnegative`.

Still absent are production polarization/sesquilinearity, the dyadic
cross-prime identity, a finite smooth log-support decomposition, and any
Schur/operator control on the full localization Gram.
