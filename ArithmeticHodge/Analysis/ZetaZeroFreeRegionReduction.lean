import ArithmeticHodge.Analysis.MultiplicativeWeilLiOffCritical
import ArithmeticHodge.Analysis.EntireFunction.Order
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Liouville
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# A quantitative reduction toward the zeta zero-free region

The classical `3-4-1` Euler-product inequality is combined with horizontal
mean-value and Cauchy estimates.  This isolates the exact majorants which
would imply a de la Vallee-Poussin zero-free region.  The currently proved
zeta and derivative estimates are polynomial in the height, so this module
does not claim the still-missing logarithmic-strength zero-free region.
-/

set_option autoImplicit false

open Complex Filter Real Set Topology
open scoped LSeries.notation

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- The `3 + 4 cos θ + cos 2θ ≥ 0` Euler-product argument, specialized to
the Riemann zeta function. This is the positivity engine in the classical
de la Vallée-Poussin zero-free-region proof. -/
theorem riemannZeta_trigProduct_norm_ge_one
    {x : ℝ} (hx : 0 < x) (t : ℝ) :
    1 ≤ ‖riemannZeta (1 + x) ^ 3 *
      riemannZeta (1 + x + I * t) ^ 4 *
      riemannZeta (1 + x + 2 * I * t)‖ := by
  have h := DirichletCharacter.norm_LSeries_product_ge_one
    (1 : DirichletCharacter ℂ 1) hx t
  simp only [one_pow] at h
  rw [DirichletCharacter.modOne_eq_one] at h
  have h0 : 1 < ((1 + x : ℂ)).re := by simp; linarith
  have h1 : 1 < ((1 + x : ℂ) + I * t).re := by simp; linarith
  have h2 : 1 < ((1 + x : ℂ) + 2 * I * t).re := by simp; linarith
  rw [LSeries_one_eq_riemannZeta h0,
    LSeries_one_eq_riemannZeta h1,
    LSeries_one_eq_riemannZeta h2] at h
  exact h

/-- A zero on the horizontal line controls the neighboring zeta value by a
uniform derivative bound on the intervening segment. This is the local
analytic step used after Euler-product positivity. -/
theorem riemannZeta_norm_le_gap_mul_derivBound
    {beta t x D : ℝ}
    (ht : t ≠ 0) (hbeta : beta ≤ 1 + x)
    (hzero : riemannZeta (beta + t * I) = 0)
    (hD : ∀ z ∈ segment ℝ ((beta : ℂ) + t * I)
        (((1 + x : ℝ) : ℂ) + t * I),
      ‖deriv riemannZeta z‖ ≤ D) :
    ‖riemannZeta (((1 + x : ℝ) : ℂ) + t * I)‖ ≤
      D * (1 + x - beta) := by
  let rho : ℂ := (beta : ℂ) + t * I
  let s : ℂ := ((1 + x : ℝ) : ℂ) + t * I
  have hsegIm : segment ℝ rho s ⊆ {z : ℂ | z.im = t} := by
    rw [segment_subset_iff]
    intro a b ha hb hab
    simp [rho, s, hab, ← add_mul]
  have hdiff : ∀ z ∈ segment ℝ rho s,
      DifferentiableAt ℂ riemannZeta z := by
    intro z hz
    apply differentiableAt_riemannZeta
    intro hz1
    have him := hsegIm hz
    rw [hz1] at him
    exact ht him.symm
  have hbound : ∀ z ∈ segment ℝ rho s,
      ‖deriv riemannZeta z‖ ≤ D := by
    simpa only [rho, s] using hD
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
    hdiff hbound (convex_segment rho s)
      (left_mem_segment ℝ rho s) (right_mem_segment ℝ rho s)
  have hzero' : riemannZeta rho = 0 := by simpa only [rho] using hzero
  rw [hzero', sub_zero] at hmv
  have hdist : ‖s - rho‖ = 1 + x - beta := by
    rw [show s - rho = (((1 + x - beta : ℝ) : ℂ)) by
      dsimp only [s, rho]
      push_cast
      ring]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : 0 ≤ 1 + x - beta)]
  rw [hdist] at hmv
  simpa only [s] using hmv

/-- Euler-product positivity plus the horizontal mean-value estimate forces
a quantitative fourth-power repulsion inequality for every hypothetical
zero `beta + i t`. -/
theorem riemannZeta_zero_repulsion_product
    {beta t x D : ℝ}
    (hx : 0 < x) (ht : t ≠ 0) (hbeta : beta ≤ 1 + x)
    (hzero : riemannZeta (beta + t * I) = 0)
    (hD : ∀ z ∈ segment ℝ ((beta : ℂ) + t * I)
        (((1 + x : ℝ) : ℂ) + t * I),
      ‖deriv riemannZeta z‖ ≤ D) :
    1 ≤ ‖riemannZeta (1 + x)‖ ^ 3 *
      (D * (1 + x - beta)) ^ 4 *
      ‖riemannZeta (1 + x + 2 * I * t)‖ := by
  have hprod := riemannZeta_trigProduct_norm_ge_one hx t
  have hlocal := riemannZeta_norm_le_gap_mul_derivBound
    ht hbeta hzero hD
  have hlocal' : ‖riemannZeta (1 + x + I * t)‖ ≤
      D * (1 + x - beta) := by
    convert hlocal using 1 <;> push_cast <;> ring
  calc
    1 ≤ ‖riemannZeta (1 + x) ^ 3 *
        riemannZeta (1 + x + I * t) ^ 4 *
        riemannZeta (1 + x + 2 * I * t)‖ := hprod
    _ = ‖riemannZeta (1 + x)‖ ^ 3 *
        ‖riemannZeta (1 + x + I * t)‖ ^ 4 *
        ‖riemannZeta (1 + x + 2 * I * t)‖ := by
      simp only [norm_mul, norm_pow]
    _ ≤ ‖riemannZeta (1 + x)‖ ^ 3 *
        (D * (1 + x - beta)) ^ 4 *
      ‖riemannZeta (1 + x + 2 * I * t)‖ := by
      gcongr

/-- Replacing the two zeta values by explicit majorants isolates the exact
analytic quantity needed for a zero-free region. -/
theorem riemannZeta_zero_gap_quartic_of_bounds
    {beta t x A B D : ℝ}
    (hx : 0 < x) (ht : t ≠ 0) (hbeta : beta ≤ 1 + x)
    (hzero : riemannZeta (beta + t * I) = 0)
    (hD : ∀ z ∈ segment ℝ ((beta : ℂ) + t * I)
        (((1 + x : ℝ) : ℂ) + t * I),
      ‖deriv riemannZeta z‖ ≤ D)
    (hA : ‖riemannZeta (1 + x)‖ ≤ A)
    (hB : ‖riemannZeta (1 + x + 2 * I * t)‖ ≤ B) :
    1 ≤ (A ^ 3 * D ^ 4 * B) * (1 + x - beta) ^ 4 := by
  have hrep := riemannZeta_zero_repulsion_product
    hx ht hbeta hzero hD
  have hAnonneg : 0 ≤ A := (norm_nonneg (riemannZeta (1 + x))).trans hA
  have hA3 : ‖riemannZeta (1 + x)‖ ^ 3 ≤ A ^ 3 :=
    pow_le_pow_left₀ (norm_nonneg _) hA 3
  calc
    1 ≤ ‖riemannZeta (1 + x)‖ ^ 3 *
        (D * (1 + x - beta)) ^ 4 *
        ‖riemannZeta (1 + x + 2 * I * t)‖ := hrep
    _ ≤ A ^ 3 * (D * (1 + x - beta)) ^ 4 * B := by
      calc
        ‖riemannZeta (1 + x)‖ ^ 3 *
            (D * (1 + x - beta)) ^ 4 *
            ‖riemannZeta (1 + x + 2 * I * t)‖ ≤
            A ^ 3 * (D * (1 + x - beta)) ^ 4 *
              ‖riemannZeta (1 + x + 2 * I * t)‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_right hA3 (by positivity)
        _ ≤ A ^ 3 * (D * (1 + x - beta)) ^ 4 * B :=
          mul_le_mul_of_nonneg_left hB
            (mul_nonneg (pow_nonneg hAnonneg 3) (by positivity))
    _ = (A ^ 3 * D ^ 4 * B) * (1 + x - beta) ^ 4 := by ring

/-- Pure order algebra converting a fourth-power repulsion estimate into a
linear lower bound for the gap. -/
theorem gap_ge_inv_of_quartic_majorant
    {gap kappa ell : ℝ} (hgap : 0 ≤ gap) (hell : 0 < ell)
    (hrep : 1 ≤ kappa * gap ^ 4) (hkappa : kappa ≤ ell ^ 4) :
    1 / ell ≤ gap := by
  have hpow : 1 ≤ (ell * gap) ^ 4 := by
    calc
      1 ≤ kappa * gap ^ 4 := hrep
      _ ≤ ell ^ 4 * gap ^ 4 :=
        mul_le_mul_of_nonneg_right hkappa (pow_nonneg hgap 4)
      _ = (ell * gap) ^ 4 := by ring
  have hellgap : 0 ≤ ell * gap := mul_nonneg hell.le hgap
  have hone : 1 ≤ ell * gap := by
    apply (pow_le_pow_iff_left₀ (show (0 : ℝ) ≤ 1 by norm_num)
      hellgap (by norm_num : (4 : ℕ) ≠ 0)).mp
    simpa only [one_pow] using hpow
  apply (div_le_iff₀ hell).2
  simpa only [one_mul, mul_comm] using hone

/-- Precise de la Vallée-Poussin reduction: if the zeta values and horizontal
derivative bound combine to at most `L^4`, then a zero satisfies
`1 - beta ≥ 1/L - x`. A logarithmic majorant `L = C log (|t|+2)` and a
matching choice of `x` give the classical region. -/
theorem riemannZeta_zero_re_le_of_majorants
    {beta t x A B D ell : ℝ}
    (hx : 0 < x) (ht : t ≠ 0) (hbeta : beta ≤ 1 + x)
    (hzero : riemannZeta (beta + t * I) = 0)
    (hD : ∀ z ∈ segment ℝ ((beta : ℂ) + t * I)
        (((1 + x : ℝ) : ℂ) + t * I),
      ‖deriv riemannZeta z‖ ≤ D)
    (hA : ‖riemannZeta (1 + x)‖ ≤ A)
    (hB : ‖riemannZeta (1 + x + 2 * I * t)‖ ≤ B)
    (hell : 0 < ell) (hmajor : A ^ 3 * D ^ 4 * B ≤ ell ^ 4) :
    1 / ell - x ≤ 1 - beta := by
  have hquartic := riemannZeta_zero_gap_quartic_of_bounds
    hx ht hbeta hzero hD hA hB
  have hgap : 0 ≤ 1 + x - beta := by linarith
  have hlower : 1 / ell ≤ 1 + x - beta :=
    gap_ge_inv_of_quartic_majorant hgap hell hquartic hmajor
  linarith

/-- The currently available convexity bound implies a polynomial bound for
`ζ'` on the right half of the critical strip. Cauchy's estimate is applied on
a fixed radius-`1/4` circle. This is useful, but is deliberately weaker than
the logarithmic derivative estimate required for the classical region. -/
theorem exists_riemannZeta_deriv_polynomial_bound :
    ∃ exponent C : ℝ, 0 < C ∧ ∀ z : ℂ,
      1 / 2 ≤ z.re → z.re ≤ 2 → 3 ≤ |z.im| →
        ‖deriv riemannZeta z‖ ≤ C * (2 * |z.im|) ^ exponent := by
  obtain ⟨A, C, hC, hzeta⟩ :=
    ArithmeticHodge.Analysis.EntireFunction.zeta_vertical_strip_bound
      (1 / 4) (9 / 4) (by norm_num) (Or.inl (by norm_num))
  refine ⟨|A|, 4 * C, mul_pos (by norm_num) hC, ?_⟩
  intro z hzlo hzhi him
  have hd : DiffContOnCl ℂ riemannZeta (Metric.ball z (1 / 4)) := by
    apply DifferentiableOn.diffContOnCl
    intro w hw
    apply DifferentiableAt.differentiableWithinAt
    apply differentiableAt_riemannZeta
    intro hw1
    have hwclosed : w ∈ Metric.closedBall z (1 / 4) :=
      Metric.closure_ball_subset_closedBall hw
    have hdist : ‖w - z‖ ≤ 1 / 4 := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hwclosed
    have him_le : |z.im| ≤ ‖w - z‖ := by
      rw [hw1]
      calc
        |z.im| = |((1 : ℂ) - z).im| := by simp
        _ ≤ ‖(1 : ℂ) - z‖ := Complex.abs_im_le_norm _
    linarith
  have hsphere : ∀ w ∈ Metric.sphere z (1 / 4),
      ‖riemannZeta w‖ ≤ C * (2 * |z.im|) ^ |A| := by
    intro w hw
    have hdist : ‖w - z‖ = 1 / 4 := by
      simpa only [Metric.mem_sphere, dist_eq_norm] using hw
    have hreDiff : |w.re - z.re| ≤ 1 / 4 := by
      calc
        |w.re - z.re| = |(w - z).re| := by simp
        _ ≤ ‖w - z‖ := Complex.abs_re_le_norm _
        _ = 1 / 4 := hdist
    have himDiff : |w.im - z.im| ≤ 1 / 4 := by
      calc
        |w.im - z.im| = |(w - z).im| := by simp
        _ ≤ ‖w - z‖ := Complex.abs_im_le_norm _
        _ = 1 / 4 := hdist
    have hwrelo : 1 / 4 ≤ w.re := by
      rw [abs_le] at hreDiff
      linarith
    have hwrehi : w.re ≤ 9 / 4 := by
      rw [abs_le] at hreDiff
      linarith
    have hzabs_le : |z.im| ≤ |w.im - z.im| + |w.im| := by
      calc
        |z.im| = |(z.im - w.im) + w.im| := by ring_nf
        _ ≤ |z.im - w.im| + |w.im| := abs_add_le _ _
        _ = |w.im - z.im| + |w.im| := by rw [abs_sub_comm]
    have hwimlo : 2 ≤ |w.im| := by linarith
    have hwabs_le : |w.im| ≤ |w.im - z.im| + |z.im| := by
      calc
        |w.im| = |(w.im - z.im) + z.im| := by ring_nf
        _ ≤ |w.im - z.im| + |z.im| := abs_add_le _ _
    have hwimhi : |w.im| ≤ 2 * |z.im| := by
      have hzabs : 0 ≤ |z.im| := abs_nonneg _
      linarith
    have hbase : 1 ≤ |w.im| := by linarith
    have hza := hzeta w hwrelo hwrehi hwimlo
    calc
      ‖riemannZeta w‖ ≤ C * |w.im| ^ A := hza
      _ ≤ C * |w.im| ^ |A| :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hbase (le_abs_self A)) hC.le
      _ ≤ C * (2 * |z.im|) ^ |A| := by
        apply mul_le_mul_of_nonneg_left _ hC.le
        exact Real.rpow_le_rpow (abs_nonneg _) hwimhi (abs_nonneg A)
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (show (0 : ℝ) < 1 / 4 by norm_num) hd hsphere
  calc
    ‖deriv riemannZeta z‖ ≤
        (C * (2 * |z.im|) ^ |A|) / (1 / 4) := hcauchy
    _ = (4 * C) * (2 * |z.im|) ^ |A| := by ring

/-- The preceding derivative estimate is uniform along every horizontal
segment from a right-half critical-strip zero to `Re(s)=1+x`, for
`0 < x ≤ 1`. -/
theorem exists_riemannZeta_horizontal_deriv_polynomial_bound :
    ∃ exponent C : ℝ, 0 < C ∧
      ∀ beta x t : ℝ, 1 / 2 ≤ beta → beta ≤ 1 →
        0 < x → x ≤ 1 → 3 ≤ |t| →
        ∀ z ∈ segment ℝ ((beta : ℂ) + t * I)
            (((1 + x : ℝ) : ℂ) + t * I),
          ‖deriv riemannZeta z‖ ≤ C * (2 * |t|) ^ exponent := by
  obtain ⟨exponent, C, hC, hderiv⟩ :=
    exists_riemannZeta_deriv_polynomial_bound
  refine ⟨exponent, C, hC, ?_⟩
  intro beta x t hbeta0 hbeta1 hx0 hx1 ht z hz
  have hsegment :
      segment ℝ ((beta : ℂ) + t * I)
          (((1 + x : ℝ) : ℂ) + t * I) ⊆
        {w : ℂ | 1 / 2 ≤ w.re ∧ w.re ≤ 2 ∧ w.im = t} := by
    rw [segment_subset_iff]
    intro a b ha hb hab
    simp only [Set.mem_setOf_eq, add_re, smul_re, ofReal_re, mul_re,
      I_re, ofReal_im, I_im, mul_zero, sub_self, add_zero, add_im,
      smul_im, mul_im, mul_one, smul_eq_mul]
    constructor
    · have ha' := mul_le_mul_of_nonneg_left hbeta0 ha
      have hb' := mul_le_mul_of_nonneg_left
        (by linarith : (1 / 2 : ℝ) ≤ 1 + x) hb
      nlinarith
    constructor
    · have ha' := mul_le_mul_of_nonneg_left hbeta1 ha
      have hb' := mul_le_mul_of_nonneg_left
        (by linarith : 1 + x ≤ 2) hb
      nlinarith
    · rw [← add_mul, hab, one_mul]
      simp
  have hzcoords := hsegment hz
  have hzim : 3 ≤ |z.im| := by
    simpa only [hzcoords.2.2] using ht
  simpa only [hzcoords.2.2] using
    hderiv z hzcoords.1 hzcoords.2.1 hzim

/-- The second zeta factor in the `3-4-1` product has a uniform polynomial
bound at doubled height, directly from the production convexity estimate. -/
theorem exists_riemannZeta_doubled_height_polynomial_bound :
    ∃ exponent C : ℝ, 0 < C ∧
      ∀ x t : ℝ, 0 < x → x ≤ 1 → 3 ≤ |t| →
        ‖riemannZeta (1 + x + 2 * I * t)‖ ≤
          C * (2 * |t|) ^ exponent := by
  obtain ⟨A, C, hC, hzeta⟩ :=
    ArithmeticHodge.Analysis.EntireFunction.zeta_vertical_strip_bound
      (1 / 2) 2 (by norm_num) (Or.inl (by norm_num))
  refine ⟨|A|, C, hC, ?_⟩
  intro x t hx0 hx1 ht
  let s : ℂ := 1 + x + 2 * I * t
  have hsrelo : 1 / 2 ≤ s.re := by simp [s]; linarith
  have hsrehi : s.re ≤ 2 := by simp [s]; linarith
  have hsim : |s.im| = 2 * |t| := by
    rw [show s.im = 2 * t by simp [s]]
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hsimlo : 2 ≤ |s.im| := by rw [hsim]; linarith [abs_nonneg t]
  have hza := hzeta s hsrelo hsrehi hsimlo
  have hbase : 1 ≤ |s.im| := by linarith
  calc
    ‖riemannZeta (1 + x + 2 * I * t)‖ = ‖riemannZeta s‖ := rfl
    _ ≤ C * |s.im| ^ A := hza
    _ ≤ C * |s.im| ^ |A| :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hbase (le_abs_self A)) hC.le
    _ = C * (2 * |t|) ^ |A| := by rw [hsim]

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
