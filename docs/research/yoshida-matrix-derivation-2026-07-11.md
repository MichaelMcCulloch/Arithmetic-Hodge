# Yoshida finite-matrix derivation and exact odd certificate

Date: 2026-07-11

Status: research result with a strict-compiling exact algebraic certificate.
This note does not prove Yoshida positivity or RH: analytic entry enclosures,
tail estimates, and the comparison from the true Gram matrix remain open
formal obligations.

## Primary source and trust boundary

The source is Hiroyuki Yoshida, *On Hermitian Forms attached to Zeta
Functions*, Advanced Studies in Pure Mathematics 21 (1992), 281--325:

- DOI: <https://doi.org/10.2969/aspm/02110281>
- PDF: <https://projecteuclid.org/download/pdf_1/euclid.aspm/1534359132>

Yoshida supplies the analytic strategy, normalized bases, tail estimates,
odd comparison rule, and even interval-elimination rule. He does not print
the finite matrix entries, triangular factors, interval trace, rounding
policy, or machine-checkable certificates. Numerical evaluation is therefore
used only to discover rational witnesses. Every final enclosure and matrix
identity must be replayed in Lean without `native_decide` or a new axiom.

## Source normalizations

Set

```text
a = log(2)/2,
L = 2a = log(2),
kappa_n = 2*pi*n/L.
```

Yoshida's Lebesgue-normalized odd and even modes on `[-a,a]` are

```text
o_n(x) = a^(-1/2) sin(pi*n*x/a),                 n >= 1,
e_0(x) = (2a)^(-1/2),
e_n(x) = a^(-1/2) cos(pi*n*x/a),                 n >= 1.
```

The odd low block is `o_1,...,o_10`, with tail starting at `o_11`. The even
low block is `e_0,...,e_199`, with tail starting at `e_200`. The exact tail
coercivity targets needed downstream are `3/2` for the odd block and
`102/25` for the even block. Replacing the latter by `4` is too weak for the
printed `1/2000` correction budget.

## Correlation reduction

For a same-parity basis `b_n`, define

```text
R_nm(u) = integral_{-a}^{a-u} b_n(u+x) b_m(x) dx,  0 <= u <= L.
```

Direct integration gives the exact odd formulas

```text
R^o_nn(u) = ((L-u) cos(kappa_n*u) + sin(kappa_n*u)/kappa_n) / L,

R^o_nm(u) = (2*(-1)^(n+m)/L)
  * (kappa_n sin(kappa_m*u) - kappa_m sin(kappa_n*u))
  / (kappa_n^2-kappa_m^2),                         n != m,
```

and the exact even formulas

```text
R^e_00(u) = (L-u)/L,

R^e_0m(u) = 2*(-1)^(m+1) sin(kappa_m*u)
  / (L*sqrt(2)*kappa_m),                           m >= 1,

R^e_nn(u) = ((L-u) cos(kappa_n*u) - sin(kappa_n*u)/kappa_n) / L,

R^e_nm(u) = (2*(-1)^(n+m)/L)
  * (kappa_m sin(kappa_m*u) - kappa_n sin(kappa_n*u))
  / (kappa_n^2-kappa_m^2),                         0 < n != m.
```

Every correlation vanishes at `u=L`; this removes the only possible prime
boundary contribution at support `[-log 2, log 2]`.

## Stable moment representation

Raw evaluation of the apparent singularity at zero was numerically unstable.
Use

```text
A(u) = exp(u/2)/(exp(u)-exp(-u)),
W(u) = 2*(exp(u/2)+exp(-u/2)-A(u)),
Wplus(u) = W(u)+1/u,
Wplus(0) = 7/2.
```

The removable expansion begins

```text
Wplus(u) = 7/2 + u/24 + 9*u^2/16 - 7*u^3/5760 + u^4/256 + ... .
```

Define

```text
S_n = integral_0^L
  (Wplus(u)*sin(kappa_n*u) - kappa_n*sinc(kappa_n*u)) du,

D_n = integral_0^L (
  Wplus(u)*((L-u)/L)*cos(kappa_n*u)
  + 2*sin(kappa_n*u/2)^2/u
  + cos(kappa_n*u)/L) du
  - (log L + gamma + log 2 + log pi).
```

Then every odd/even entry is algebraic in only these two moment sequences:

```text
G^o_nn = D_n + S_n/(L*kappa_n),
G^o_nm = (2*(-1)^(n+m)/L)
  * (kappa_n*S_m-kappa_m*S_n)/(kappa_n^2-kappa_m^2),

G^e_00 = D_0,
G^e_0m = 2*(-1)^(m+1)*S_m/(L*sqrt(2)*kappa_m),
G^e_nn = D_n - S_n/(L*kappa_n),
G^e_nm = (2*(-1)^(n+m)/L)
  * (kappa_m*S_m-kappa_n*S_n)/(kappa_n^2-kappa_m^2).
```

Thus the even block requires certified enclosures for 199 sine moments and
200 diagonal moments, rather than 20,100 unrelated transcendental integrals.

## Exact odd 10-by-10 certificate

Let `U` be Yoshida's odd real comparison matrix with correction radius
`1/40`. Stable discovery gives a minimum eigenvalue near
`0.0180104303104621`. Fix the deliberately pessimistic dyadic matrix

```text
A_ij = floor(512*U_ij)/512 - 2/512.
```

This reserves two dyadic grid units of analytic comparison slack. The exact
unit-lower `LDL^T` factorization has positive pivots

```text
63/512,
3029/4608,
11133845/10855936,
3652354649/2850264320,
5477401595643/3740011160576,
4415794839266231/2804429616969216,
3675102233535782813/2260886957704310272,
3010672614966895352697/1881652343570320800256,
358843898432320643688653/256910729810508403430144,
32550872422740888070024259/45932018999337042392147584.
```

The complete matrix, unit-lower factor, and pivots currently live in the
strict probe `/tmp/YoshidaMatrixDerivationProbe.lean`, SHA-256
`ee408119554084877e804bb7206ee439ee8017cd089b8a45dfd8400fb2f029ef`.
It proves

```lean
theorem yoshidaOddComparison10Certificate : Matrix.PosDef
    ((Rat.castHom ℂ).mapMatrix yoshidaOddComparison10)
```

using production `rationalLDL_posDef_complex`. Root independently ran

```text
lake env lean -DwarningAsError=true /tmp/YoshidaMatrixDerivationProbe.lean
```

with exit zero. The theorem depends only on
`[propext, Classical.choice, Quot.sound]`.

The existing certificate casts the rational matrix to `ℂ`, while the generic
absolute-entry comparison naturally consumes a real matrix. A separate strict
prototype `/tmp/RationalRealBridgeProbe.lean` now proves the analogous
`rationalLDL_posDef_real` theorem after importing
`Mathlib.Data.Real.StarOrdered`; it also uses only the standard three axioms.
The production certificate should therefore expose both the real and complex
positive-definiteness results from the same exact `A/L/d` payload.

The next production task must copy this payload into a tracked module, add the
real rational-LDL bridge, and replay both strict proofs; the `/tmp` locations
are not durable artifacts.

## Exact remaining odd comparison obligations

For all 55 independent entries, Lean must prove

```text
A_ii <= G^o_ii - 1/40,
abs(G^o_ij) + 1/40 <= -A_ij,                       i != j.
```

A generic absolute-entry comparison theorem then transfers `A.PosDef` to the
corrected complex Gram. These analytic inequalities, not the LDL arithmetic,
are the remaining odd finite-block bottleneck.

## Even interval-Schur target

Initialize a rational interval box of radius `1/2000` around each certified
base entry. At stage `k`, require a positive pivot interval and update

```text
I^(k+1)_ij = I^k_ij - I^k_ik * I^k_kj / I^k_kk.
```

The soundness theorem must follow from exact block congruence, not from an
external numeric trace. Discovery with an additional uniform analytic radius
`10^-5` still succeeds; radius `10^-4` fails at stage 54. Production moment
enclosures should therefore target `10^-6` when practical.

## Formal work order

1. Promote the exact odd `A/L/d` payload into a tracked Lean module.
2. Prove the generic absolute-entry comparison theorem.
3. Formalize sound rational interval arithmetic and interval-Schur
   elimination for the even block.
4. Prove certified `S_n,D_n` enclosures using removable integrands and exact
   Taylor or quadrature remainders.
5. Derive the 55 odd inequalities and the even initial interval box.
6. Combine these with the separately reviewed tail coercivity, coupling, and
   Riesz-correction theorems.

Until steps 2--6 compile, the exact odd certificate is an algebraic milestone,
not a proof of Yoshida ratio-two positivity or RH.
