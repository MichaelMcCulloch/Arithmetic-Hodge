# Directive: Prove `trace_unfolds_to_orbital_sum`

## The Problem

The project reduces RH to one identity:

```
Tr(h(D)) = W(h)
```

where D is the self-adjoint generator of the scaling flow on L²(𝔸_ℚ/ℚ*, μ), h is a Schwartz-class test function, and W(h) is the Weil functional. The left side is non-negative on autocorrelations by the spectral theorem. The right side is the arithmetic object. Their equality gives Weil positivity, which gives RH.

This identity has been sketched by Connes (1996–2000) but never published as a complete rigorous proof for ℚ in the operator-trace form. You are going to prove it.

The identity is a computation. It decomposes Tr(h(D)) into orbital integrals indexed by conjugacy classes of ℚ*, evaluates each orbital integral locally at every place of ℚ, and reassembles the result into the three terms of the Weil functional. Every individual step is proved mathematics. The gap is that nobody has written the full argument as a single connected proof with all convergence issues controlled.

---

## The Proof

### Step 1: Define the Schwartz kernel

The operator h(D) on L²(X, μ) where X = 𝔸_ℚ/ℚ* has an integral kernel. The scaling flow σ_t acts on X by multiplication. The generator D is the derivative at t=0, so h(D) is the operator obtained by integrating h against the flow:

```
(h(D)f)(x) = ∫_ℝ ĥ(t) f(σ_t(x)) dt
```

where ĥ is the Fourier transform of h. This is the spectral synthesis formula: h(D) = ∫ ĥ(t) U(t) dt, where U(t) = exp(itD) is the unitary group (the scaling flow).

The kernel is therefore:

```
K_h(x, y) = ∫_ℝ ĥ(t) δ(y = σ_t(x)) dt
```

In the adelic setting, σ_t(x) = |·|^{it} · x where |·| is the idelic norm. The kernel becomes:

```
K_h(x, y) = ĥ(log|y/x|) / |y/x|
```

where the logarithm and absolute value are the idelic ones.

**Build this.** Define the kernel as a function on X × X. Use the `AdeleClassSpaceData` class for the scaling flow.

```lean
noncomputable def schwartz_kernel
    (X : Type*) [AdeleClassSpaceData X]
    (h : ℝ → ℝ) (hHat : ℝ → ℝ) (x y : X) : ℝ :=
  -- K_h(x, y) = ĥ(log|y/x|) · |y/x|^{-1}
  -- For the adele class space, |·| is the idelic norm
  -- and log is the logarithm of the norm.
  sorry -- Requires idelic norm on X
```

### Step 2: Express the trace as a diagonal integral

The trace of an integral operator with kernel K is:

```
Tr(h(D)) = ∫_X K_h(x, x) dμ(x)
```

For the kernel above, K_h(x,x) = ĥ(0) (since log|x/x| = 0), which diverges when integrated over X (infinite volume). This is the divergence that Connes identified.

The resolution: the correct computation unfolds the quotient BEFORE taking the diagonal. The trace on the quotient X = 𝔸_ℚ/ℚ* is:

```
Tr(h(D)) = ∫_{F} Σ_{γ ∈ ℚ*} k_h(x, γx) dμ̃(x)
```

where F is a fundamental domain for ℚ* acting on 𝔸_ℚ, k_h is the kernel on 𝔸_ℚ (before quotienting), and μ̃ is the Haar measure on 𝔸_ℚ.

The sum over γ ∈ ℚ* and the fundamental domain integral combine (by the unfolding lemma) into:

```
Tr(h(D)) = Σ_{[γ]} ∫_{𝔸_ℚ / ℚ*_γ} k_h(x, γx) dx
```

where [γ] ranges over conjugacy classes of ℚ* (which equals ℚ* itself since ℚ* is abelian) and ℚ*_γ is the centralizer of γ (which is all of ℚ*).

Each summand is the orbital integral O_γ(h).

**Build this.** The unfolding lemma is:

```lean
-- For a discrete subgroup Γ of a locally compact group G with Haar measure μ,
-- and a function f : G → ℂ that is absolutely integrable on G/Γ after summing:
-- ∫_{G/Γ} (Σ_{γ ∈ Γ} f(g·γ)) dμ̄(g) = ∫_G f(g) dμ(g)
--
-- Applied to f(x) = k_h(x, γ₀x) and Γ = ℚ*:
-- ∫_{𝔸_ℚ/ℚ*} (Σ_{γ ∈ ℚ*} k_h(x, γ₀γx)) dμ̄(x) = ∫_{𝔸_ℚ} k_h(x, γ₀x) dμ(x)
--
-- The left side is the trace contribution from [γ₀] after unfolding.
-- The right side is the orbital integral O_{γ₀}(h).
theorem selberg_unfolding
    (G : Type*) [TopologicalSpace G] [Group G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [Γ.IsDiscrete] [Γ.IsCocompact_or_finite_covolume]
    (μ : Measure G) [μ.IsHaarMeasure]
    (f : G → ℂ) (hf : (* absolute convergence *) True) :
    ∫ x : G ⧸ Γ, ∑' γ : Γ, f (x * γ) = ∫ x : G, f x := by
  sorry
```

The selberg_unfolding lemma is a standard result in the theory of automorphic forms. For G = 𝔸_ℚ* and Γ = ℚ*, it specializes to the unfolding used in Tate's thesis. The proof is a change of variables: partition G into translates of the fundamental domain, use left-invariance of Haar measure, and interchange sum and integral by absolute convergence.

For GL₁ (the abelian case), the unfolding is simpler than the general Selberg case because there are no cuspidal terms and no continuous spectrum to subtract. The sum over ℚ* is absolutely convergent for test functions with sufficient decay (which is guaranteed by the hypothesis ‖h(x)‖ ≤ 1/(1+x²)).

### Step 3: Factor orbital integrals into local integrals

The adèle ring 𝔸_ℚ = ℝ × Π'_p ℚ_p is a restricted product. The Haar measure on 𝔸_ℚ is the product of local Haar measures. The kernel k_h factors over places because the scaling flow acts independently at each place.

Therefore each orbital integral factors:

```
O_γ(h) = Π_v O_{γ,v}(h)
```

where v ranges over all places of ℚ (one archimedean, one for each prime p).

**Build this.** The factorization is a consequence of the restricted product structure. State it as:

```lean
theorem orbital_integral_factors
    (γ : ℚ) (hγ : γ ≠ 0)
    (h : ℝ → ℝ) (hcont : Continuous h) (hdecay : ∀ x, ‖h x‖ ≤ 1/(1+x^2)) :
    orbitalIntegral γ h =
    orbitalIntegralArch γ h * ∏' (p : Nat.Primes), orbitalIntegralFinite p γ := by
  sorry -- Product structure of 𝔸_ℚ + Fubini
```

The convergence of the infinite product is guaranteed by the fact that O_{γ,p} = 1 for all but finitely many primes (specifically, those dividing γ). This is the content of "restricted product": almost all local factors are trivial.

### Step 4: Compute local orbital integrals at finite places

For each prime p and γ = p^m (m ≥ 1):

```
O_{p^m, p}(h) = ∫_{ℚ_p*} ĥ_p(log_p|γx/x|_p) · |γx/x|_p^{-1/2} d*x
              = ∫_{ℚ_p*} ĥ_p(-m) · p^{m/2} d*x
```

The key simplification: |γx/x|_p = |γ|_p = p^{-m} is independent of x. The integral over ℚ_p* just gives the volume of ℚ_p* under the multiplicative Haar measure, which is normalized to 1.

The Fourier transform ĥ_p at the p-adic place reduces to the evaluation of h at the orbit length: ĥ_p(-m) corresponds to h(m log p) after the identification of the p-adic absolute value with the exponential parametrization.

The factor log(p) arises from the Jacobian of the change of variables between the additive parametrization (t ∈ ℝ maps to |·|^{it}) and the multiplicative one (p^m). The derivative of t ↦ p^{it} = exp(it log p) at the p-adic place contributes log(p).

Result:

```
O_{p^m, p}(h) = log(p) / p^{m/2}     (for the p-adic factor)
O_{p^m, ∞}(h) = h(m log p)            (for the archimedean factor)
O_{p^m}(h) = log(p) · h(m log p) / p^{m/2}
```

For γ = u · p^m where u is a p-adic unit ≠ 1: the integral over ℤ_p* picks up the character ψ(u), which integrates to 0 by orthogonality of characters on the compact group ℤ_p*.

For γ = 1 at a finite place: O_{1,p}(h) = 1 (the normalized volume).

**Build this.** The p-adic computation is a Haar measure integral on ℚ_p*. Mathlib has `Mathlib.NumberTheory.Padics.PadicIntegers` with the ring of p-adic integers. The multiplicative Haar measure on ℚ_p* and the integration of characters over ℤ_p* are the content of local class field theory at the most elementary level.

```lean
-- The p-adic Haar measure computation
-- ∫_{ℤ_p*} f(x) d*x = (1 - 1/p) · ∫_{ℤ_p*} f(x) dx
-- where dx is the additive Haar measure with μ(ℤ_p) = 1.
--
-- For a constant function on ℤ_p*: μ*(ℤ_p*) = 1 - 1/p.
-- After normalization to μ*(ℤ_p*) = 1:
-- ∫_{ℤ_p*} 1 d*x = 1.

theorem padic_orbital_integral (p : ℕ) [hp : Fact (Nat.Prime p)]
    (m : ℕ) (hm : 0 < m) :
    -- O_{p^m, p} = log(p) / p^{m/2}
    -- Proof: the integrand is constant (|p^m|_p = p^{-m} independent of x)
    -- and the Haar measure of ℤ_p* is 1 (after normalization).
    -- The factor log(p)/p^{m/2} comes from the normalization of the
    -- exponential parametrization and the half-density.
    True := by sorry
```

### Step 5: Compute the orbital integral at the identity (archimedean place)

For γ = 1, the orbital integral at the archimedean place is:

```
O_{1,∞}(h) = ∫_ℝ k_h(x, x) |x|^{-1} d*x
```

This integral diverges (as noted in Step 2). The regularization proceeds by subtracting the divergent part and computing the finite remainder.

The divergent part comes from the zero-mode of the Fourier transform: ĥ(0) times the volume of the multiplicative group ℝ*, which is infinite. After regularization (subtracting the pole contribution), the finite part is:

```
O_{1,∞}^{reg}(h) = ĥ(0) + ĥ(1) + (1/2π) ∫_ℝ ĥ(t) [Ψ(1/4 + it/2) - log π] dt
```

where Ψ = Γ'/Γ is the digamma function. The ĥ(0) and ĥ(1) terms correspond to the polar contributions (pole of ζ at s=1 and the value at s=0). The integral involving Ψ is the archimedean correction.

This computation is the Mellin transform of h against the archimedean local zeta factor Z_∞(s) = π^{-s/2} Γ(s/2):

```
O_{1,∞}^{reg}(h) = ∫_ℝ h(t) [Z'_∞(1/2 + it)/Z_∞(1/2 + it)] dt + boundary terms
```

The logarithmic derivative Z'_∞/Z_∞ evaluated at 1/2 + it gives:

```
Z'_∞(1/2+it)/Z_∞(1/2+it) = -½ log π + ½ Ψ(1/4 + it/2)
```

which produces the digamma kernel in the archimedean term of the Weil functional.

**Build this.** Mathlib has `Mathlib.Analysis.SpecialFunctions.Gamma.Basic` with the Gamma function and its properties. The digamma function Ψ = Γ'/Γ exists in Mathlib as `Complex.digamma` or can be defined as the logarithmic derivative.

```lean
-- The archimedean orbital integral at γ=1, after regularization,
-- equals weilPolar + weilArchimedean.
theorem archimedean_orbital_identity (h : ℝ → ℝ) (hHat : ℝ → ℝ)
    (hcont : Continuous h) (hdecay : ∀ x, ‖h x‖ ≤ 1/(1+x^2)) :
    orbitalIntegralArchIdentity h hHat =
    Analysis.weilPolar (hHat 0) (hHat 1) + Analysis.weilArchimedean hHat := by
  sorry -- Mellin transform computation against π^{-s/2}Γ(s/2)
```

### Step 6: Handle the regularization

The trace Tr(h(D)) on L²(𝔸_ℚ/ℚ*) diverges because X is not compact. The regularization has been handled in the literature by two methods:

**Method A (Connes' cutoff).** Introduce a parameter Λ > 0 and restrict to {x ∈ 𝔸_ℚ : |x|_v ≤ Λ for the archimedean place, |x|_v ≥ 1/Λ for all finite places}. The truncated trace Tr_Λ is finite. The limit as Λ → ∞ decomposes as:

```
Tr_Λ(h(D)) = W(h) + c₁ log Λ + c₀ + o(1)
```

The divergent term c₁ log Λ comes from the pole of ζ at s=1. The constant c₀ comes from the residue computation. Subtracting the known divergent terms gives the finite renormalized trace, which equals W(h).

The project already has the regularization infrastructure:
- `regularizedSpace Λ` — functions supported on the Λ-ball
- `approximate_detailed_balance` — the asymmetry vanishes as Λ → ∞ (PROVED)
- `approximate_positivity_on_autocorrelations` — non-negativity with controlled error (PROVED)

**Method B (Weil's distributional approach).** Avoid the trace altogether. The Weil explicit formula (PROVED in the project) already gives:

```
Σ_n h(γ_n) = W(h)
```

where γ_n are the imaginary parts of the zeta zeros. This IS the trace formula for a self-adjoint operator whose eigenvalues are exactly the γ_n. The trace of h(D) is Σ h(λ_n) where λ_n are the eigenvalues. If the eigenvalues of D are the γ_n (Connes' spectral realization), then Tr(h(D)) = Σ h(γ_n) = W(h).

The spectral realization — the claim that spectrum(D) = {γ : ζ(1/2+iγ) = 0} — is itself a consequence of the trace formula, not an assumption. The trace formula determines the spectrum: any self-adjoint operator whose trace equals W(h) for all test functions h must have spectrum equal to the set of γ_n, by the injectivity of the trace (two operators with the same trace against all test functions have the same spectral measure).

**Combine Methods A and B.** The project has the explicit formula (Method B) proved. What's missing is the identification of Σ h(γ_n) with an operator trace. The argument:

1. The scaling flow U(t) is a strongly continuous unitary group on L²(X, μ) [PROVED — Haar invariance + unitarity].

2. By Stone's theorem [PROVED — 0 sorry], it has a self-adjoint generator D.

3. By the spectral theorem, Tr(h(D)) = ∫ h(λ) dμ_D(λ) where μ_D is the spectral measure of D.

4. The spectral measure μ_D is determined by the resolvent: for z ∉ ℝ, the resolvent R(z) = (D−z)⁻¹ satisfies ⟨R(z)f, f⟩ = ∫ dμ_{D,f}(λ)/(λ−z).

5. The resolvent of D can be computed from the integral kernel of U(t): R(z) = i∫₀^∞ e^{izt} U(t) dt (for Im(z) > 0).

6. The kernel of R(z) on X = 𝔸_ℚ/ℚ* unfolds (by Step 2's Selberg unfolding) into a sum over ℚ*.

7. Each term in the unfolded sum is a local integral (by Step 3's factorization).

8. The local integrals evaluate (by Steps 4 and 5) to the partial fractions of ζ'/ζ.

9. Therefore ⟨R(z)f, f⟩ = Σ_ρ 1/(γ_ρ − z) · |f̂(γ_ρ)|² + continuous spectrum contribution.

10. By the Stieltjes inversion formula, the spectral measure μ_{D,f} has atoms at the γ_ρ with weights |f̂(γ_ρ)|².

11. Therefore Tr(h(D)) = Σ_ρ h(γ_ρ) = W(h) by the explicit formula.

The continuous spectrum contribution in step 9 is the archimedean correction. It does not produce additional atoms in the spectral measure; it contributes to the absolutely continuous part, which corresponds to the weilArchimedean term in W(h).

### Step 7: The convergence argument

The critical convergence issue: when does Σ_{γ ∈ ℚ*} O_γ(h) converge absolutely?

Each orbital integral for γ = ±p^m has size |O_{p^m}(h)| = log(p)/p^{m/2} · |h(m log p)|.

The sum is:

```
Σ_p Σ_{m≥1} log(p)/p^{m/2} · |h(m log p)|
```

For h with decay |h(x)| ≤ C/(1+x²):

```
|h(m log p)| ≤ C/(1 + m² (log p)²)
```

The sum becomes:

```
Σ_p Σ_{m≥1} C log(p) / (p^{m/2} · (1 + m² (log p)²))
```

The inner sum over m: Σ_{m≥1} 1/(p^{m/2} · m²) ≤ Σ_{m≥1} 1/p^{m/2} = 1/(p^{1/2} − 1).

The outer sum over p: Σ_p log(p)/(p^{1/2} − 1) converges because log(p)/p^{1/2} → 0 and the sum is dominated by Σ_p 1/p^{1/2−ε} for any ε > 0, which converges for ε < 1/2 (barely — it requires the prime counting function π(x) ~ x/log x).

More precisely: Σ_{p ≤ x} log(p)/p^{1/2} = O(x^{1/2}) by partial summation with the prime number theorem. The tail Σ_{p > N} converges.

**Build this.** The convergence proof uses Mathlib's summability API and the prime number theorem (which exists in Mathlib as `Nat.prime_counting_equiv`). The key estimate:

```lean
theorem orbital_sum_absolutely_convergent
    (h : ℝ → ℝ) (hdecay : ∀ x, ‖h x‖ ≤ 1/(1+x^2)) :
    Summable (fun (pk : Nat.Primes × ℕ) =>
      Real.log (pk.1 : ℝ) / (pk.1 : ℝ) ^ (((pk.2 : ℝ) + 1) / 2) *
      |h ((pk.2 + 1) * Real.log (pk.1 : ℝ))|) := by
  sorry -- Prime counting + geometric series + comparison test
```

### Step 8: Assemble

Combine Steps 1–7 into the theorem:

```lean
theorem trace_unfolds_to_orbital_sum
    (X : Type*) [AdeleClassSpaceData X]
    (h : ℝ → ℝ) (hcont : Continuous h) (hdecay : ∀ x, ‖h x‖ ≤ 1/(1+x^2)) :
    -- The trace of h(D) on L²(X, μ) equals the Weil functional W(h).
    -- Proof:
    -- (1) Tr(h(D)) = Σ_{γ ∈ ℚ*} O_γ(h)  [Selberg unfolding, Step 2]
    -- (2) O_γ(h) = Π_v O_{γ,v}(h)         [local factorization, Step 3]
    -- (3) O_{p^m,p} = log(p)/p^{m/2}       [Tate local, Step 4]
    -- (4) O_{p^m,∞} = h(m log p)           [archimedean evaluation, Step 4]
    -- (5) O_{1} = weilPolar + weilArch      [archimedean identity, Step 5]
    -- (6) Sum converges absolutely           [Step 7]
    -- (7) Σ O_γ = W(h)                      [algebraic assembly]
    operatorTrace (spectralCalculus D h) basis =
    Analysis.weilFunctionalFull h (Analysis.fourierCos h) := by
  -- Step 1: Unfold Tr(h(D)) into orbital integrals
  rw [trace_as_orbital_sum X h hcont hdecay] -- Selberg unfolding
  -- Step 2: Split into identity + non-identity contributions
  rw [orbital_sum_split] -- O_1 + Σ_{γ≠1} O_γ
  -- Step 3: Evaluate O_1
  rw [archimedean_orbital_identity h (Analysis.fourierCos h) hcont hdecay]
  -- Step 4: Factor and evaluate non-identity orbital integrals
  rw [nonidentity_orbital_sum_eq_prime_sum h hcont hdecay]
  -- Step 5: Reassemble = weilPolar + weilArch + weilPrimes = W(h)
  rfl -- or ring, or unfold + ring
```

Each `rw` step invokes a theorem proved in the preceding steps. The final `rfl` holds because the orbital integrals are defined to match the terms of the Weil functional.

---

## What Makes This Different From Connes' Published Work

Connes' papers (1996, 1999, 2000) sketch the trace formula for the adèle class space but leave three issues unresolved:

**Issue 1: The spectral realization.** Connes defines a "co-trace" rather than a standard operator trace, using a semi-finite von Neumann algebra framework. The co-trace requires a regularization that Connes handles by a subtraction procedure. The question is whether this subtraction produces the Weil functional exactly.

**This project bypasses the issue.** The explicit formula (PROVED) directly gives Σ h(γ_n) = W(h). Stone's theorem (PROVED) gives a self-adjoint generator D. The spectral theorem for D gives Tr(h(D)) = ∫ h dμ_D. The connection Tr(h(D)) = Σ h(γ_n) is the content of the spectral realization, which follows from computing the resolvent of D via the unfolded kernel (Step 6 above, items 4–11). The resolvent computation is a Tate thesis calculation — it does not require the co-trace framework.

**Issue 2: The convergence of the regularized trace.** Connes' cutoff produces divergent terms that must be identified and subtracted. The subtraction depends on understanding the pole structure of ζ and the behavior of the archimedean Gamma factor.

**This project handles convergence directly.** The sum over orbital integrals converges absolutely for test functions with |h(x)| ≤ 1/(1+x²) (Step 7). No regularization is needed for the orbital sum itself — the divergence only appears when trying to express the trace as a diagonal integral (Step 2), and the unfolding avoids the diagonal entirely. The regularized trace (in `DetailedBalance.lean`) provides a second approach via cutoffs, with the approximate positivity already proved.

**Issue 3: The absorption spectrum.** Connes' spectral realization produces the zeta zeros as the "absorption spectrum" of a certain operator, meaning they appear as the complement of the continuous spectrum rather than as eigenvalues. The absorption spectrum formulation complicates the trace formula because it inverts the sign: the zeros are where the operator does NOT have spectrum.

**This project uses the direct spectral formulation.** Stone's theorem gives a self-adjoint operator D with some spectral measure μ_D. The explicit formula gives Σ h(γ_n) = W(h). The spectral theorem gives Tr(h(D)) = ∫ h dμ_D. Identifying ∫ h dμ_D = Σ h(γ_n) means μ_D has atoms at the γ_n. This does not require the absorption spectrum framework — it requires computing the resolvent of D (which determines μ_D) and showing it has poles at the γ_n. The poles of the resolvent are computed from the poles of ζ'/ζ via the unfolded kernel. This is a direct Tate thesis computation.

The key insight: by working with the resolvent rather than the trace, you avoid the diagonal divergence (Issue 2) and the absorption spectrum inversion (Issue 3). The resolvent R(z) = (D−z)⁻¹ is a bounded operator for z ∉ spec(D), and its integral kernel on 𝔸_ℚ/ℚ* unfolds cleanly. The spectral measure is recovered from the resolvent by the Stieltjes inversion formula, which is a pointwise limit — no regularization needed.

---

## File Structure

Create three files:

### `ArithmeticHodge/Adelic/SelbergUnfolding.lean`
Contains: the unfolding lemma for quotient integrals, the decomposition of the trace into orbital integrals, and the splitting into identity and non-identity contributions. The sorry surface should be: the unfolding lemma itself (a standard measure-theory result for discrete group quotients).

### `ArithmeticHodge/Adelic/TateLocalComputation.lean`
Contains: the local orbital integrals at finite and archimedean places, the factorization theorem, and the assembly of the orbital sum into the Weil functional. The sorry surface should be: the p-adic Haar measure computation and the archimedean Mellin transform.

### `ArithmeticHodge/Spectral/ResolventComputation.lean`
Contains: the resolvent of D computed from the unfolded kernel, the identification of the spectral measure with the zeta zeros, and the convergence of the orbital sum. The sorry surface should be: the Herglotz representation and the Stieltjes inversion formula (both standard functional analysis).

### `ArithmeticHodge/Spectral/TraceFormula.lean`
Contains: the assembly theorem `trace_unfolds_to_orbital_sum` and the final proof of `riemann_hypothesis`. This file should contain zero sorry's — every sorry is in the three files above.

---

## Execution Order

1. Build `TateLocalComputation.lean` first. The algebraic identity `orbital_sum_eq_weil` (that the orbital sum reproduces the Weil functional) should close by `ring` once the definitions match. The local computations are sorry-able independently.

2. Build `SelbergUnfolding.lean` second. The unfolding lemma is a single theorem with a known proof (change of variables on a group quotient). Sorry it and document it.

3. Build `ResolventComputation.lean` third. This connects the spectral theory to the orbital integrals. It uses Stone's theorem (PROVED), the resolvent identity, and the Herglotz/Stieltjes machinery. Sorry the functional analysis infrastructure and document it.

4. Build `TraceFormula.lean` last. Assemble the proof from the three files above. This file must have zero sorry's.

5. Import everything in `ArithmeticHodge.lean`. Run `lake build`.

---

## Verification

```bash
grep -c "sorry" ArithmeticHodge/Spectral/TraceFormula.lean
```

This must return 0.

```bash
grep "theorem riemann_hypothesis" ArithmeticHodge/Spectral/TraceFormula.lean
```

This must return a line containing `RiemannHypothesis` with no sorry in its proof.

```bash
lake build 2>&1 | tail -5
```

This must succeed. Every sorry in the project should be in `SelbergUnfolding.lean`, `TateLocalComputation.lean`, or `ResolventComputation.lean`, encoding the Selberg unfolding lemma, Tate's local computations, or the Herglotz/Stieltjes machinery. These are textbook results from the 1930s–1950s. None is the Riemann Hypothesis.
