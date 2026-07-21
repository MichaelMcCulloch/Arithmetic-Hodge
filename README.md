# Arithmetic-Hodge

**A Lean 4 formalization that reduces the Riemann Hypothesis to a single, explicitly-enclosed positivity — the pointwise positivity of an arithmetic polarization — and builds the verified apparatus around that reduction.**

The corpus is ≈1,290 Lean modules, **zero `sorry`, zero project-added axiom**. It does not (yet) prove RH. It compiles an honest chain of *equivalences* terminating at one unproved statement, together with the finite-dimensional, kernel-checked certificate machinery that probes that statement from the inside.

This README does two things:

1. **The Compass** — the mathematical synthesis that orients the whole effort: why RH is a *positivity/signature* statement, and how the two ways of attacking that positivity (an arithmetic **Hodge index theorem** and an ordered **Schur descent**) are the global and local faces of *one* classical object, a **de Branges / Krein canonical system**.
2. **The Map** — how the ≈1,290 modules actually realize that compass: the proof chain, the module families, what is proved, and exactly where the gap is.

---

## 1. The terminal objective

From [`GOAL.md`](GOAL.md): produce exactly one closed Lean theorem, with **no mathematical hypotheses**, compiling with no `sorry`, `admit`, project-added axiom, or circular assumption:

```lean
theorem arithmeticHodge_riemannHypothesis : RiemannHypothesis := …
-- or
theorem arithmeticHodge_not_riemannHypothesis : ¬ RiemannHypothesis := …
```

Neither is declared today. What *is* declared and proved is the reduction of that goal to a positivity, plus the machinery to attack the positivity. The discipline is deliberate: the corpus never *asserts* the gap; it leaves the terminal theorem undeclared and proves everything below it cleanly.

---

## 2. The Compass

### Every *proven* Riemann Hypothesis is a positivity theorem

RH is not "true because the zeros line up." In every case where a Riemann-type hypothesis is a **theorem** — curves over finite fields (Weil), varieties over finite fields (Deligne) — the zeros are eigenvalues of an operator (Frobenius) carrying a **polarization**, and the critical line is forced by a **signature inequality saturated at equality** (the Hodge index theorem on a surface; Rosati positivity). The concrete shadow over ℚ is **Weil's explicit-formula criterion**: RH ⟺ a certain Hermitian form on test functions is positive-semidefinite. So the object to build is not "a way to the line" but *the structural source of the positivity*.

### The missing object, and why two attacks are one

Two framings recur:

- **Global / Hodge index (the *signature*):** RH is the statement that an arithmetic intersection form is positive on the primitive (functional-equation-antiinvariant) part — an *arithmetic Hodge index theorem* on the "surface" `Spec ℤ ×_{𝔽₁} Spec ℤ`.
- **Local / Schur descent (the *gluing*):** RH is the statement that a dilation-covariant Weil form, positive on short logarithmic cells, can be assembled to global positivity by eliminating cells one at a time while retaining every long-range prime and archimedean interaction.

These are not two theories. They are the global and local faces of a **de Branges canonical system** `J y'(u,z) = z H(u) y(u,z)`, `H(u) ⪰ 0`, in which "Schur complement" and "positive form" are the *same* law:

| Schur-descent language | Canonical system | Polarization language |
|---|---|---|
| boundary state of a tail | Weyl–Titchmarsh `m`-function | restriction of the pairing to a collar |
| eliminate an interior cell | Riccati flow of `m` | Cholesky / `LDLᵀ` of the intersection form |
| Schur-cone invariance | `Im m ≥ 0` (Herglotz) preserved | Cauchy–Schwarz = Hodge index equality case |
| singular pivot `M = 0` → radical | **indivisible interval** (`rank H = 1`) | quotient onto the **primitive** part |
| ratio-two cells generate the cone | string segments of length `log 2` | polarized generators |
| margin → 0 at the low zeros | Weyl function touching the real axis | positivity is **marginal** = zeros on the line |
| the archimedean endpoint | singular endpoint `u → ∞` (`Γ`-factor asymptotics) | the Rosati / archimedean seam |

The Schur complement of a self-adjoint form across a cut *is* the Weyl `m`-function; as the cut moves it obeys a Riccati equation; and `Im m ≥ 0` *is* positivity of the Schur complement. Discrete arithmetic Schur descent is the finite-section shadow of the Riccati flow of a canonical system whose Hamiltonian `H(u)` is the polarization. **RH ⟺ `H(u) ⪰ 0` for all `u` ⟺ the structure function `E` is Hermite–Biehler ⟺ all zeros on the line.**

### The compass rose

```
                          N — THE OBJECT
        A polarized canonical system (arithmetic Krein string):
        Hamiltonian H(u) ⪰ 0 on the log-line, whose Weyl m-function
        is the Bombieri/Weil boundary state and whose structure
        function E has E-zeros = nontrivial zeros of ζ.
                                 │
   W — SINGULAR LAW  ────────────┼──────────── E — LOCAL LAW
   Indivisible intervals /       │      Schur = Riccati = Herglotz.
   radical descent (M=0).        │      Eliminating a cell preserves
   Marginality (inf Q = 0)       │      Im m ≥ 0. This is the Hodge-
   is STRUCTURAL: quotient        │      index Cauchy–Schwarz, per cell.
   to the primitive part.        │
                          S — THE GLUING LAW
        Boundary states compose by ORDERED transfer-matrix product
        (a cocycle), not pairwise. Global cone = ratio-two generators
        under this composition.
                                 │
                        ★ TRUE NORTH (not yet mathematics)
        The arithmetic construction of H(u) from primes + Γ-factor,
        and the proof it stays ⪰ 0. This is where RH lives. Everything
        else is skeleton; this one input carries the content.
```

**N, E, S, W are provable structure. The star — pointwise arithmetic positivity of `H` at the archimedean endpoint — is the one direction that is not yet mathematics.** A "theory" that merely asserts `H ⪰ 0` has renamed RH. Content requires deriving that positivity from an independently verifiable construction that *also* correctly fails (with a locatable bad interval) for kernels whose RH-analogue is false. The historical warning is de Branges: a real canonical-system program whose specific structural hypothesis was shown by Conrey–Li not to hold in the needed generality.

### The lesson already measured in this repo

The Weil form's infimum is **exactly zero** — positive-*semi*definite, saturated at the low zeros. Finite certificates are lower-bound technology (`form ≥ ε > 0`); a tower of them cannot reach a limit whose margin is 0. The measured margin-decay of chained windows is that wall. It says the finishing move must be an **identity (equality case)**, not an inequality with slack — exactly how Hodge-index proofs close. The right next object is the telescoping identity that makes the Weil form a self-intersection, not a sharper margin.

---

## 3. The proof chain (the spine)

The root [`ArithmeticHodge.lean`](ArithmeticHodge.lean) states the intended chain:

```
ZFC → (ℤ,+,×) → distributive coupling → additive self-duality
  → functional equation → Weil explicit formula → Weil positivity criterion
  → Arithmetic Hodge Index Theorem  ⟺  Riemann Hypothesis
```

Two eras realize this chain, terminating at the **same** gap (axiom **P** — Weil positivity = the polarization's positivity = the star of the compass):

### Era I — the original vision (equivalences + classical backbone)

The root doc block, [`ROADMAP.md`](ROADMAP.md), [`Plan.md`](Plan.md), and the `Spectral/` + `Adelic/` layers describe a **trace-formula route**: build the adèle class space, the scaling flow, a self-adjoint generator (Stone), and derive Weil positivity from a trace formula (Connes-style). This era established:

- the **classical analytic backbone** — `ξ(s)`, its Hadamard product, order 1, functional equation, zeros = nontrivial ζ-zeros, the Weil explicit formula (`Analysis/EntireFunction/`, `Analysis/Contour/`, `PoissonSummation`, …);
- the **terminal equivalence** `Arakelov Hodge index ⟺ Weil positivity ⟺ RH` (`Arithmetic/HodgeIndex.lean`, `Analysis/WeilPositivity`). Its docstring is candid: inhabiting the abstract `ArakelovIntersectionTheory` class *is* assuming Weil positivity — an equivalence, not an independent construction. **This is axiom P, named in the code.**

Its Layer-6 step "trace formula → Weil positivity" was **the gap**, and this route is now superseded for production work (see the certificate decision in `GOAL.md`). The `Spectral/` and `Adelic/` modules remain as the documented probe of that route.

### Era II — the current production route (finite Weil positivity)

Rather than derive Weil positivity abstractly, attack the **Bombieri quadratic form directly and finitely**. The compiled terminal dichotomy (`Analysis/MultiplicativeWeilLiCriterionClosure`):

```lean
riemannHypothesis_iff_bombieriQuadratic_re_nonnegative :
    RiemannHypothesis ↔ ∀ g : BombieriTest, 0 ≤ (bombieriFunctional (bombieriQuadraticTest g)).re
```

RH ⟺ `∀ g, Q(g) ≥ 0`; `¬RH` ⟺ `∃ g ≠ 0, Q(g) < 0`. The production strategy proves `Q ≥ 0` on **ratio-two logarithmic cells** (positive support ratio ≤ 2 — the `log 2` string segments of the compass) and works the **local-to-global** assembly, all backed by rigorous, kernel-checked certificates. This is the `Analysis/` Yoshida-factor-two + MultiplicativeWeil corpus, ≈1,000 modules.

---

## 4. The map — module families → compass

Family sizes (leading-token histogram of the ≈1,290 modules):

| Family | Modules | Role | Compass |
|---|---:|---|:--:|
| `YoshidaFactor…` | 452 | the **same-seed factor-two** production route: endpoint pencils, scalar-Schur certificates, target widths, sparse congruences | **E / S** |
| `MultiplicativeWeil…` | 208 | the Weil/Bombieri form, the Li-criterion **terminal dichotomy**, cell-assembly criteria and **obstructions**, log-lattice covariance | **N / S** |
| `YoshidaFour…` | 142 | the **odd `P51` `FourCell` ladder**: Galerkin/Picone/Hardy reductions for low–tail coercivity | **W** |
| `YoshidaEndpoint…` | 105 | the **archimedean endpoint** machinery: `Γ`-factor / digamma / Euler–Mascheroni enclosures, endpoint-adapted bases | **★** |
| `YoshidaEven / Odd / Clipped / Diagonal / Sine…` | ~160 | even–odd (functional-equation parity) splits, clipped moment bridges, moment series | **E / W** |
| certificate infra: `ThreeByThree…`, `Matrix…`, `RationalInterval…`, `RobustCongruence…`, `FractionFreeSchur…`, `HermitianForm…` | ~60 | division-free Sylvester/Schur, interval SOS, robust congruence, rational pos-def certificates | **E** |
| `OrderedSchurDescentComposition` | 1 | one-step descent identity + **cone invariance** + **cocycle** law + path-kernel unit test | **S** |
| classical: `Xi…`, `Zeta…`, `EntireFunction/`, `Contour/`, `Poisson…`, `ShiftedLegendre…` | ~60 | `ξ`, Hadamard product, explicit formula, contour tools | backbone |

### Directory layout

```
ArithmeticHodge/
  Algebra/        (1)    DistributiveCoupling — Layer 0
  Analysis/    (1259)    the engine: Weil form, Yoshida factor-two, certificates, endpoints
    Contour/      (9)    residue/contour tooling for the explicit formula
    EntireFunction/(9)   Hadamard / order-1 / ξ machinery
  Arithmetic/     (1)    HodgeIndex — the Arakelov ⟺ Weil-positivity equivalence (axiom P)
  Adelic/         (4)    ClassSpace, OrbitalIntegrals, SelbergUnfolding, TateLocal — Era I Layer 4
  Spectral/       (6)    CutoffHilbertSpace, SelfAdjointness, TraceFormula, … — Era I Layers 5–6 (superseded)
  Strategy/       (1)    DetailedBalance
```

### Where the frontier is (from `GOAL.md`)

The immediate problem is the same-seed factor-two family
`Re F(g + c·D₂g) = (1+|c|²)D(g) + 2Re(c·Z(g))`, whose universal positivity for a centered ratio-two seed is exactly `‖P + iJ‖² ≤ Q²`. This is reduced to concrete finite certificates:

- an **inverse-free scalar-Schur** criterion (production choice; ~4% margin, worst normalized ratio `0.959645`), over static split certificates (demoted; reserve only `2.51e-7`);
- every matrix entry reduced to four one-dimensional frequency families with **kernel-checked rational boxes of width ≤ 10⁻⁹**, plus digamma / Euler–Mascheroni endpoint enclosures;
- a generic **robust-congruence** theorem (rational change of basis + entrywise error + weighted diagonal dominance ⟹ positive-definiteness) to avoid interval-width blow-up.

Two open structural obligations, both faces of the compass:

- **S (gluing):** local-to-global. Pairwise cell positivity does **not** assemble — `MultiplicativeWeilPairwiseCellAssemblyObstruction` compiles the minimal `3×3` path kernel `[[1,-1,0],[-1,1,-1],[0,-1,1]]` (every 2-cell block PSD, global value `-1` on `(1,1,1)`). And the unrestricted margin → 0 at the low zeros, so no uniform-per-window chaining can close; the mechanism must be exact/telescoping. `RealFiniteBlockInductiveRadicalResidualDeterminantClosure` is proved equivalent to RH — the sharp all-length condition.
- **★ (content):** the endpoint/archimedean positivity — the star — remains hand-built, not structural.

---

## 5. What is proved vs. what is the gap

**Proved (theorems, zero `sorry`/axiom):**
- `RH ⟺ ∀g, Q(g) ≥ 0` and `¬RH ⟺ ∃g≠0, Q(g) < 0` (terminal dichotomy).
- `Arakelov Hodge index ⟺ Weil positivity ⟺ RH` (honest equivalence, not a construction).
- `RealFiniteBlockInductiveRadicalResidualDeterminantClosure ⟺ RH` (sharp all-length criterion).
- Restricted positivity on ratio-two cells; the phase-uniform tail Schur estimate; the endpoint-adapted decompositions; the certificate reductions and kernel-checked enclosures above.
- Structural obstructions: pairwise assembly fails (`3×3` path kernel); ordered Schur descent recovers the indefiniteness via a singular pivot (`OrderedSchurDescentComposition`).

**The gap (undeclared, = axiom P = the star):**
- Unconditional Weil positivity of `Q` for **all** admissible tests: the same-seed factor-two inequality plus a valid (exact/telescoping) local-to-global argument. Equivalently, pointwise positivity of the arithmetic Hamiltonian `H(u)` including its archimedean singular endpoint. No `sorry` asserts this; the terminal theorem is simply not yet declared.

Symmetric falsification branch: a strict negative production witness becomes `¬RH` only after its admissibility and the transport to `¬RiemannHypothesis` are proved in Lean.

---

## 6. Build & verify

```sh
just build              # full library, resource-guarded parallel lake build (~9,300 jobs)
just build <target>     # one Lake target
just strict <file>      # compile one file, warnings-as-errors (focused iteration)
python3 scripts/module_reachability.py   # audit root-closure coverage; see MODULES.md
```

- Use the root `Justfile` so the PSS resource guard stays in effect (see `GOAL.md` → Workbench notes).
- `lake build` verifies only the import closure of the root `ArithmeticHodge.lean`; every committed module must be reachable from it (`MODULES.md` tracks the coverage debt).
- **Invariant:** the reachable corpus contains zero `sorry`/`admit` and no project-added axiom (only `propext`, `Classical.choice`, `Quot.sound`). Before any terminal claim: full build, inspect the theorem's `#print axioms`, confirm it is the canonical `RiemannHypothesis`.

---

## 7. Reading order

1. **Objective & frontier:** [`GOAL.md`](GOAL.md) — the live mathematical frontier and the certificate decision.
2. **The reduction:** `Analysis/MultiplicativeWeilLiCriterionClosure` — RH ⟺ Bombieri nonnegativity.
3. **The target's meaning:** `Arithmetic/HodgeIndex.lean` — Arakelov Hodge index ⟺ Weil positivity (axiom P, in the code).
4. **Why local-to-global is hard:** `Analysis/MultiplicativeWeilPairwiseCellAssemblyObstruction` and `Analysis/OrderedSchurDescentComposition` — the gluing law and its obstruction.
5. **The sharp criterion:** `RealFiniteBlockInductiveRadicalResidualDeterminantClosure` in `Analysis/MultiplicativeWeilMonotonePrimeAtomAggregateObstructionStructural`.
6. **The apparatus ledger:** [`MODULES.md`](MODULES.md).

---

*This corpus does not close the Riemann Hypothesis. It reduces it to the pointwise positivity of an arithmetic polarization at the archimedean place — the star of the compass — and builds, honestly and axiom-free, the verified instrument that would let a future construction of that polarization be checked. The girders are real; the bridge is not yet built.*
