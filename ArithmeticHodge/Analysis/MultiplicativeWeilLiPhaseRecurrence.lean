import ArithmeticHodge.Analysis.MultiplicativeWeilLiAlgebra
import ArithmeticHodge.Analysis.MultiplicativeWeilLiOffCritical
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Sequences

/-!
# Finite phase recurrence for the Bombieri--Li witness

This module isolates the compact-group arithmetic in the off-critical
Li-negativity argument.  It contains no analytic assertion about the zeta
zeros: the inputs below are a finite family of phases and, later, a finite
family of dominant complex bases.
-/

set_option autoImplicit false

open Complex Filter Function Metric Real Set Topology

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- In a compact normed additive group, multiples of any point return
arbitrarily close to zero at arbitrarily large positive times. -/
theorem exists_large_nsmul_norm_lt
    {A : Type*} [NormedAddCommGroup A] [CompactSpace A]
    (x : A) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ ‖n • x‖ < ε := by
  obtain ⟨a, φ, hφ, hlim⟩ :=
    CompactSpace.tendsto_subseq (fun n : ℕ => n • x)
  have hshift :
      Tendsto (fun k : ℕ => (φ (k + N) • x) - (φ k • x)) atTop (𝓝 0) := by
    have hright : Tendsto (fun k : ℕ => φ k • x) atTop (𝓝 a) := hlim
    have hleft : Tendsto (fun k : ℕ => φ (k + N) • x) atTop (𝓝 a) := by
      simpa [Function.comp_def] using hlim.comp (tendsto_add_atTop_nat N)
    simpa using hleft.sub hright
  have hevent : ∀ᶠ k : ℕ in atTop,
      ‖(φ (k + N) • x) - (φ k • x)‖ < ε := by
    simpa only [mem_ball, dist_zero_right] using
      hshift.eventually (ball_mem_nhds (0 : A) hε)
  obtain ⟨k, hk⟩ := hevent.exists
  let n := φ (k + N) - φ k
  have hφle : φ k ≤ φ (k + N) := hφ.monotone (Nat.le_add_right k N)
  have hNn : N ≤ n := by
    dsimp [n]
    apply Nat.le_sub_of_add_le
    simpa [Nat.add_comm] using hφ.add_le_nat N k
  refine ⟨n, hNn, ?_⟩
  change ‖(φ (k + N) - φ k) • x‖ < ε
  rw [sub_nsmul x hφle]
  simpa only [sub_eq_add_neg] using hk

/-- Simultaneous recurrence for a finite family of additive-circle phases. -/
theorem exists_large_simultaneous_phase_recurrence
    {ι : Type*} [Fintype ι] (θ : ι → UnitAddCircle)
    {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ ∀ i : ι, ‖n • θ i‖ < ε := by
  obtain ⟨n, hNn, hn⟩ :=
    exists_large_nsmul_norm_lt (A := ι → UnitAddCircle) θ hε N
  refine ⟨n, hNn, ?_⟩
  have hn' : ∀ i : ι, ‖(n • θ) i‖ < ε :=
    (pi_norm_lt_iff hε).mp hn
  simpa using hn'

/-- The multiplicative form of finite phase recurrence: all the associated
unit complex numbers have an arbitrarily large common power as close to one
as prescribed. -/
theorem exists_large_simultaneous_circle_pow_close_one
    {ι : Type*} [Fintype ι] (θ : ι → UnitAddCircle)
    {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ ∀ i : ι,
      ‖(AddCircle.toCircle (θ i) : ℂ) ^ n - 1‖ < ε := by
  have hcontinuous : Continuous
      (fun t : UnitAddCircle => (AddCircle.toCircle t : ℂ)) :=
    continuous_subtype_val.comp AddCircle.continuous_toCircle
  obtain ⟨δ, hδ, hcontrol⟩ :=
    (Metric.continuousAt_iff.mp hcontinuous.continuousAt) ε hε
  obtain ⟨n, hNn, hn⟩ :=
    exists_large_simultaneous_phase_recurrence θ hδ N
  refine ⟨n, hNn, fun i => ?_⟩
  have hreturn : dist (n • θ i) 0 < δ := by
    simpa only [dist_zero_right] using hn i
  have hi := hcontrol hreturn
  simpa only [AddCircle.toCircle_nsmul, AddCircle.toCircle_zero,
    Circle.coe_one, dist_eq_norm] using hi

/-- The same simultaneous recurrence stated intrinsically for a finite family
of points of the complex unit circle. -/
theorem exists_large_simultaneous_circle_pow_close_one'
    {ι : Type*} [Fintype ι] (u : ι → Circle)
    {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ ∀ i : ι,
      ‖(u i : ℂ) ^ n - 1‖ < ε := by
  let e : UnitAddCircle ≃ₜ Circle :=
    AddCircle.homeomorphCircle one_ne_zero
  let θ : ι → UnitAddCircle := fun i => e.symm (u i)
  obtain ⟨n, hNn, hn⟩ :=
    exists_large_simultaneous_circle_pow_close_one θ hε N
  refine ⟨n, hNn, fun i => ?_⟩
  have hphase : AddCircle.toCircle (θ i) = u i := by
    rw [← AddCircle.homeomorphCircle_apply one_ne_zero]
    exact e.apply_symm_apply (u i)
  simpa only [hphase] using hn i

/-- A nonempty finite family of equal-modulus expanding complex bases has
arbitrarily late powers for which the real part of its finite Li-model sum is
strictly negative.  This is the dominant finite-sum core of Bombieri's
off-critical argument. -/
theorem exists_large_finite_expanding_sum_re_negative
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (θ : ι → UnitAddCircle) {M : ℝ} (hM : 1 < M) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧
      (∑ i : ι, (1 -
        ((M : ℂ) * (AddCircle.toCircle (θ i) : ℂ)) ^ n)).re < 0 := by
  obtain ⟨k, hk⟩ :=
    ((tendsto_pow_atTop_atTop_of_one_lt hM).eventually_gt_atTop (2 : ℝ)).exists
  obtain ⟨n, hn, hclose⟩ :=
    exists_large_simultaneous_circle_pow_close_one θ
      (by norm_num : (0 : ℝ) < 1 / 2) (max N k)
  have hNn : N ≤ n := (le_max_left N k).trans hn
  have hkn : k ≤ n := (le_max_right N k).trans hn
  have hMn : 2 < M ^ n :=
    hk.trans_le (pow_le_pow_right₀ hM.le hkn)
  refine ⟨n, hNn, ?_⟩
  change Complex.reCLM (∑ i : ι, (1 -
    ((M : ℂ) * (AddCircle.toCircle (θ i) : ℂ)) ^ n)) < 0
  rw [map_sum Complex.reCLM]
  apply Finset.sum_neg
  · intro i _hi
    change (1 - ((M : ℂ) *
      (AddCircle.toCircle (θ i) : ℂ)) ^ n).re < 0
    let u : ℂ := (AddCircle.toCircle (θ i) : ℂ) ^ n
    have huclose : ‖u - 1‖ < 1 / 2 := by
      simpa only [u] using hclose i
    have hureabs : |u.re - 1| < 1 / 2 := by
      have hrele : |u.re - 1| ≤ ‖u - 1‖ := by
        simpa only [Complex.sub_re, Complex.one_re] using
          Complex.abs_re_le_norm (u - 1)
      exact hrele.trans_lt huclose
    have hure : 1 / 2 < u.re := by
      have := (abs_lt.mp hureabs).1
      linarith
    have hMpos : 0 < M := by linarith
    have hMnp : 0 < M ^ n := pow_pos hMpos n
    have hprod : 1 < M ^ n * u.re := by
      calc
        1 < M ^ n * (1 / 2 : ℝ) := by linarith
        _ < M ^ n * u.re := mul_lt_mul_of_pos_left hure hMnp
    have hneg : 1 - M ^ n * u.re < 0 := sub_neg.mpr hprod
    rw [mul_pow, show (M : ℂ) ^ n = (M ^ n : ℝ) by norm_cast]
    simpa only [Complex.sub_re, Complex.one_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, u] using hneg
  · exact Finset.univ_nonempty

/-- Direct `liFunction` form of the finite dominant-family negativity theorem.
If finitely many Li bases all have the same expanding modulus `M`, their
finite Li sum has strictly negative real part at arbitrarily large indices. -/
theorem exists_large_finite_li_sum_re_negative
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (rho : ι → ℂ) (θ : ι → UnitAddCircle)
    {M : ℝ} (hM : 1 < M)
    (hbase : ∀ i : ι,
      1 - 1 / rho i =
        (M : ℂ) * (AddCircle.toCircle (θ i) : ℂ))
    (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧
      (∑ i : ι, liFunction n (rho i)).re < 0 := by
  obtain ⟨n, hNn, hn⟩ :=
    exists_large_finite_expanding_sum_re_negative θ hM N
  refine ⟨n, hNn, ?_⟩
  simpa only [liFunction, hbase] using hn

/-- Intrinsic equal-modulus version.  No phase parametrization is required in
the statement: it is constructed by normalizing each Li base onto `Circle`.
Thus any nonempty finite family of Li bases with one common modulus `M > 1`
has negative finite Li sums at arbitrarily large indices. -/
theorem exists_large_finite_equal_norm_li_sum_re_negative
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (rho : ι → ℂ) {M : ℝ} (hM : 1 < M)
    (hnorm : ∀ i : ι, ‖1 - 1 / rho i‖ = M)
    (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧
      (∑ i : ι, liFunction n (rho i)).re < 0 := by
  have hMpos : 0 < M := by linarith
  have hMne : M ≠ 0 := hMpos.ne'
  have hMcne : (M : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hMne
  let u : ι → Circle := fun i =>
    ⟨(1 - 1 / rho i) / (M : ℂ), by
      change (1 - 1 / rho i) / (M : ℂ) ∈
        Metric.sphere (0 : ℂ) 1
      rw [mem_sphere_zero_iff_norm, norm_div, hnorm i,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hMpos,
        div_self hMne]⟩
  let e : UnitAddCircle ≃ₜ Circle :=
    AddCircle.homeomorphCircle one_ne_zero
  let θ : ι → UnitAddCircle := fun i => e.symm (u i)
  have hphase (i : ι) :
      (AddCircle.toCircle (θ i) : ℂ) = (u i : ℂ) := by
    apply congrArg ((↑) : Circle → ℂ)
    rw [← AddCircle.homeomorphCircle_apply one_ne_zero]
    exact e.apply_symm_apply (u i)
  apply exists_large_finite_li_sum_re_negative rho θ hM
  · intro i
    rw [hphase i]
    change 1 - 1 / rho i = (M : ℂ) *
      ((1 - 1 / rho i) / (M : ℂ))
    rw [mul_comm, div_mul_cancel₀ _ hMcne]

/-- Failure of RH therefore supplies one nontrivial zero whose individual Li
term has negative real part at arbitrarily large indices.  This is deliberately
an individual-term statement, not yet a statement about the full zero sum. -/
theorem not_RH_exists_large_li_term_re_negative
    (hnot : ¬ RiemannHypothesis) (N : ℕ) :
    ∃ rho : NontrivialZetaZero, ∃ n : ℕ,
      N ≤ n ∧ (liFunction n rho.val).re < 0 := by
  obtain ⟨rho, hrho⟩ := not_RH_exists_li_base_gt_one hnot
  obtain ⟨n, hNn, hn⟩ :=
    exists_large_finite_equal_norm_li_sum_re_negative
      (ι := Unit) (fun _ => rho.val) hrho (fun _ => rfl) N
  refine ⟨rho, n, hNn, ?_⟩
  simpa using hn

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
