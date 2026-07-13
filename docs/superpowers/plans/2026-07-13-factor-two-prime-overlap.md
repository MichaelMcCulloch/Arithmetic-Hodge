# Factor-Two Prime-Overlap Plan

**Status:** Complete and verified.  Both coupled endpoint inequalities and the
mixed phase pencil remain open.

**Gate-3 obligation:** Determine the sign and exact size of the retained
`p = 2,3` correction in the two signed factor-two endpoints.  If the overlap
bound failed, the proposed positive folded-energy route would be eliminated;
if it succeeded, the endpoint problem would reduce to two exact local-form
inequalities with no unresolved prime sign.

## Structural reduction

For a ratio-at-most-two seed, write

```text
C0 = Re C(0)
c  = Re C(log(3/2))
Q+ = C0 + 2c
Q- = C0 - 2c.
```

The logarithmic pullback is supported in an interval of length at most
`L = log 2`.  Since `L <= 2 log(3/2)`, the two subintervals contributing to
the shifted correlation are disjoint.  Cauchy--Schwarz on those two cells
therefore gives

```text
2 * norm C(log(3/2)) <= C0,
```

and hence `Q+ >= 0` and `Q- >= 0`.

With `alpha = log 2 / sqrt 2` and `beta = log 3 / sqrt 3`, prove
`beta < 2 alpha` structurally and rewrite the real retained-prime symbol as

```text
Re P = ((2 alpha + beta) / 4) Q+
     + ((2 alpha - beta) / 4) Q-.
```

Both coefficients are strictly positive.  This also yields the scalar mass
envelope

```text
(alpha - beta/2) C0 <= Re P <= (alpha + beta/2) C0.
```

## Endpoint consequence

Substitute the exact folded overlap `W = Re P` into the already proved local
form identities:

```text
D - R = (1/2) Re B(g - D2g, g - D2g) + W
D + R = (1/2) Re B(g + D2g, g + D2g) - W.
```

Thus the prime sector helps the antisymmetric endpoint and is the exact loss
in the symmetric endpoint.  Export both corresponding nonnegativity iff
statements.  Do not infer either endpoint from a scalar mass bound alone.

## Validation

- Strict-check the focused module and root umbrella, then run the sequential
  full build.
- Audit all public theorems for axioms and recursively inspect the source
  closure for forbidden or quarantined dependencies.
- Recheck the archived and fallback inventories byte-for-byte.
- Record the result in the terminal-distance audit, stage only the production
  module, umbrella import, plan, and audit, then commit and push `main`.

## Next make-or-break lemma

Prove or strictly reverse

```text
W(g) <= (1/2) Re B(g + D2g, g + D2g).
```

The lower endpoint remains the companion obligation
`-W(g) <= (1/2) Re B(g - D2g, g - D2g)`.  Numerical exploration may select a
route or witness, but neither sampled positivity nor a finite certificate is
admissible in the terminal dependency path.
