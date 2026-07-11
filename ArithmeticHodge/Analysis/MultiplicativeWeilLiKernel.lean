import ArithmeticHodge.Analysis.MultiplicativeWeil
import ArithmeticHodge.Analysis.MultiplicativeWeilLiAlgebra
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Data.Nat.Choose.Sum

/-!
# Bombieri's Li kernel and its Mellin transform

The logarithmic polynomial supported on `(0,1)` is evaluated by reducing its
Mellin transform to complex Laplace moments.  The resulting finite binomial
sum is exactly Li's rational function `liFunction n s` on `Re(s) > 0`.
-/

set_option autoImplicit false

open Complex Filter MeasureTheory Real Set Topology

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- The logarithmic monomial occurring in Bombieri's inverse Mellin kernel. -/
def liLogAtom (m : ℕ) (x : ℝ) : ℂ :=
  if x ∈ Ioo (0 : ℝ) 1 then ((Real.log x) ^ m : ℝ) else 0

private theorem laplacePow_integrableOn
    (m : ℕ) (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ m * Complex.exp (-(s * t)))
      (Ioi 0) := by
  have hreal := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := (m : ℝ)) (b := s.re)
    (by have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m; linarith) (by norm_num) hs
  refine hreal.congr' (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change 0 < t at ht
  simp [Complex.norm_exp, Real.norm_eq_abs, abs_of_pos ht,
    Real.rpow_natCast, Real.rpow_one]

private theorem integral_laplacePow
    (m : ℕ) (s : ℂ) (hs : 0 < s.re) :
    (∫ t : ℝ in Ioi 0,
        (t : ℂ) ^ m * Complex.exp (-(s * t))) =
      (Nat.factorial m : ℂ) / s ^ (m + 1) := by
  induction m with
  | zero =>
      have hbase := integral_exp_mul_complex_Ioi
        (a := -s) (by simpa using (neg_lt_zero.mpr hs)) 0
      simpa [div_eq_mul_inv] using hbase
  | succ m ih =>
      let u : ℝ → ℂ := fun t ↦ (t : ℂ) ^ (m + 1)
      let u' : ℝ → ℂ := fun t ↦
        ((m + 1 : ℕ) : ℂ) * (t : ℂ) ^ m
      let v : ℝ → ℂ := fun t ↦ Complex.exp (-(s * t))
      let v' : ℝ → ℂ := fun t ↦
        Complex.exp (-(s * t)) * (-s)
      have hu : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt u (u' t) t := by
        intro t _ht
        dsimp only [u, u']
        simpa using Complex.ofRealCLM.hasDerivAt.pow (m + 1)
      have hv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt v (v' t) t := by
        intro t _ht
        dsimp only [v, v']
        simpa using ((Complex.ofRealCLM.hasDerivAt.const_mul s).neg.cexp)
      have huv' : IntegrableOn (u * v') (Ioi (0 : ℝ)) := by
        have h := (laplacePow_integrableOn (m + 1) s hs).const_mul (-s)
        refine IntegrableOn.congr_fun h ?_ measurableSet_Ioi
        intro t _ht
        dsimp only [u, v', Pi.mul_apply]
        ring
      have hu'v : IntegrableOn (u' * v) (Ioi (0 : ℝ)) := by
        have h := (laplacePow_integrableOn m s hs).const_mul
          (((m + 1 : ℕ) : ℂ))
        refine IntegrableOn.congr_fun h ?_ measurableSet_Ioi
        intro t _ht
        dsimp only [u', v, Pi.mul_apply]
        ring
      have hzero : Tendsto (u * v) (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (0 : ℂ)) := by
        have hcont : ContinuousAt (u * v) 0 := by
          dsimp only [u, v]
          fun_prop
        simpa [u, v] using hcont.tendsto.mono_left inf_le_left
      have hinfty : Tendsto (u * v) atTop (nhds (0 : ℂ)) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        have hreal := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
          ((m + 1 : ℕ) : ℝ) s.re hs
        apply hreal.congr'
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
        dsimp only [u, v, Pi.mul_apply]
        simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ht, Complex.norm_exp, Complex.neg_re, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        rw [Real.rpow_natCast]
        ring
      have hparts := integral_Ioi_mul_deriv_eq_deriv_mul
        hu hv huv' hu'v hzero hinfty
      have hleft :
          (∫ t : ℝ in Ioi 0, u t * v' t) =
            (-s) * ∫ t : ℝ in Ioi 0,
              (t : ℂ) ^ (m + 1) * Complex.exp (-(s * t)) := by
        calc
          _ = ∫ t : ℝ in Ioi 0,
              (-s) * ((t : ℂ) ^ (m + 1) * Complex.exp (-(s * t))) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro t _ht
            dsimp only [u, v']
            ring
          _ = _ := MeasureTheory.integral_const_mul
            (r := -s) (f := fun t : ℝ ↦
              (t : ℂ) ^ (m + 1) * Complex.exp (-(s * t)))
      have hright :
          (∫ t : ℝ in Ioi 0, u' t * v t) =
            (((m + 1 : ℕ) : ℂ)) * ∫ t : ℝ in Ioi 0,
              (t : ℂ) ^ m * Complex.exp (-(s * t)) := by
        calc
          _ = ∫ t : ℝ in Ioi 0,
              (((m + 1 : ℕ) : ℂ)) *
                ((t : ℂ) ^ m * Complex.exp (-(s * t))) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro t _ht
            dsimp only [u', v]
            ring
          _ = _ := MeasureTheory.integral_const_mul
            (r := (((m + 1 : ℕ) : ℂ))) (f := fun t : ℝ ↦
              (t : ℂ) ^ m * Complex.exp (-(s * t)))
      have hparts' :
          (-s) * (∫ t : ℝ in Ioi 0,
              (t : ℂ) ^ (m + 1) * Complex.exp (-(s * t))) =
            -((((m + 1 : ℕ) : ℂ)) * ∫ t : ℝ in Ioi 0,
              (t : ℂ) ^ m * Complex.exp (-(s * t))) := by
        calc
          _ = ∫ t : ℝ in Ioi 0, u t * v' t := hleft.symm
          _ = 0 - 0 - ∫ t : ℝ in Ioi 0, u' t * v t := hparts
          _ = _ := by rw [hright]; ring
      have hs0 : s ≠ 0 := by
        intro hszero
        rw [hszero] at hs
        norm_num at hs
      have hrec :
          s * (∫ t : ℝ in Ioi 0,
              (t : ℂ) ^ (m + 1) * Complex.exp (-(s * t))) =
            (((m + 1 : ℕ) : ℂ)) * ∫ t : ℝ in Ioi 0,
              (t : ℂ) ^ m * Complex.exp (-(s * t)) := by
        calc
          _ = -((-s) * ∫ t : ℝ in Ioi 0,
                (t : ℂ) ^ (m + 1) * Complex.exp (-(s * t))) := by ring
          _ = -(-((((m + 1 : ℕ) : ℂ)) * ∫ t : ℝ in Ioi 0,
                (t : ℂ) ^ m * Complex.exp (-(s * t)))) := by rw [hparts']
          _ = _ := by ring
      rw [ih] at hrec
      apply (mul_left_cancel₀ hs0)
      rw [hrec]
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      field_simp [hs0]
      ring

private theorem negExp_image_Ioi :
    (fun t : ℝ ↦ Real.exp (-t)) '' Ioi 0 = Ioo 0 1 := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht)⟩
  · intro hx
    refine ⟨-Real.log x, neg_pos.mpr (Real.log_neg hx.1 hx.2), ?_⟩
    simp [Real.exp_log hx.1]

private theorem integral_Ioo_cpow_logPow
    (m : ℕ) (s : ℂ) :
    (∫ x : ℝ in Ioo 0 1,
        (x : ℂ) ^ (s - 1) * ((Real.log x) ^ m : ℝ)) =
      (-1 : ℂ) ^ m * ∫ t : ℝ in Ioi 0,
        (t : ℂ) ^ m * Complex.exp (-(s * t)) := by
  let φ : ℝ → ℝ := fun t ↦ Real.exp (-t)
  let φ' : ℝ → ℝ := fun t ↦ -Real.exp (-t)
  let g : ℝ → ℂ := fun x ↦
    (x : ℂ) ^ (s - 1) * ((Real.log x) ^ m : ℝ)
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivWithinAt φ (φ' t) (Ioi 0) t := by
    intro t _ht
    have htderiv : HasDerivAt φ (φ' t) t := by
      dsimp only [φ, φ']
      simpa using (hasDerivAt_id t).neg.exp
    exact htderiv.hasDerivWithinAt
  have hinj : Set.InjOn φ (Ioi (0 : ℝ)) := by
    intro a _ha b _hb hab
    dsimp only [φ] at hab
    exact neg_injective (Real.exp_injective hab)
  have himage : φ '' Ioi (0 : ℝ) = Ioo 0 1 := by
    exact negExp_image_Ioi
  have hchange := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi hderiv hinj g
  rw [himage] at hchange
  calc
    _ = ∫ t : ℝ in Ioi 0, |φ' t| • g (φ t) := hchange
    _ = ∫ t : ℝ in Ioi 0,
        (-1 : ℂ) ^ m *
          ((t : ℂ) ^ m * Complex.exp (-(s * t))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change 0 < t at ht
      dsimp only [φ, φ', g]
      rw [abs_neg, abs_of_pos (Real.exp_pos _), Real.log_exp]
      simp only [Complex.real_smul]
      rw [Complex.cpow_def_of_ne_zero
        (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))]
      have hlog : Complex.log ((Real.exp (-t) : ℝ) : ℂ) = ((-t : ℝ) : ℂ) := by
        rw [Complex.ofReal_exp]
        rw [Complex.log_exp] <;> simp [Real.pi_pos, Real.pi_nonneg]
      rw [hlog]
      push_cast
      rw [neg_pow]
      calc
        _ = (-1 : ℂ) ^ m * (t : ℂ) ^ m *
            (Complex.exp (-(t : ℂ)) *
              Complex.exp (-(t : ℂ) * (s - 1))) := by ring
        _ = (-1 : ℂ) ^ m * (t : ℂ) ^ m *
            Complex.exp (-(t : ℂ) + (-(t : ℂ) * (s - 1))) := by
          rw [Complex.exp_add]
        _ = _ := by
          rw [show -(t : ℂ) + (-(t : ℂ) * (s - 1)) = -(s * t) by ring]
          ring
    _ = _ := MeasureTheory.integral_const_mul
      (r := ((-1 : ℂ) ^ m)) (f := fun t : ℝ ↦
        (t : ℂ) ^ m * Complex.exp (-(s * t)))

/-- A logarithmic monomial has a genuine Mellin integral throughout the
right half-plane. -/
theorem liLogAtom_mellinConvergent
    (m : ℕ) (s : ℂ) (hs : 0 < s.re) :
    MellinConvergent (liLogAtom m) s := by
  let φ : ℝ → ℝ := fun t ↦ Real.exp (-t)
  let φ' : ℝ → ℝ := fun t ↦ -Real.exp (-t)
  let g : ℝ → ℂ := fun x ↦
    (x : ℂ) ^ (s - 1) * ((Real.log x) ^ m : ℝ)
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivWithinAt φ (φ' t) (Ioi 0) t := by
    intro t _ht
    have htderiv : HasDerivAt φ (φ' t) t := by
      dsimp only [φ, φ']
      simpa using (hasDerivAt_id t).neg.exp
    exact htderiv.hasDerivWithinAt
  have hinj : Set.InjOn φ (Ioi (0 : ℝ)) := by
    intro a _ha b _hb hab
    dsimp only [φ] at hab
    exact neg_injective (Real.exp_injective hab)
  have himage : φ '' Ioi (0 : ℝ) = Ioo 0 1 := negExp_image_Ioi
  have htransformed : IntegrableOn (fun t : ℝ ↦ |φ' t| • g (φ t)) (Ioi 0) := by
    have h := (laplacePow_integrableOn m s hs).const_mul ((-1 : ℂ) ^ m)
    refine IntegrableOn.congr_fun h ?_ measurableSet_Ioi
    intro t ht
    change 0 < t at ht
    dsimp only [φ, φ', g]
    symm
    rw [abs_neg, abs_of_pos (Real.exp_pos _), Real.log_exp]
    simp only [Complex.real_smul]
    rw [Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))]
    have hlog : Complex.log ((Real.exp (-t) : ℝ) : ℂ) = ((-t : ℝ) : ℂ) := by
      rw [Complex.ofReal_exp]
      rw [Complex.log_exp] <;> simp [Real.pi_pos, Real.pi_nonneg]
    rw [hlog]
    push_cast
    rw [neg_pow]
    calc
      _ = (-1 : ℂ) ^ m * (t : ℂ) ^ m *
          (Complex.exp (-(t : ℂ)) *
            Complex.exp (-(t : ℂ) * (s - 1))) := by ring
      _ = (-1 : ℂ) ^ m * (t : ℂ) ^ m *
          Complex.exp (-(t : ℂ) + (-(t : ℂ) * (s - 1))) := by
        rw [Complex.exp_add]
      _ = _ := by
        rw [show -(t : ℂ) + (-(t : ℂ) * (s - 1)) = -(s * t) by ring]
        ring
  have hgIoo : IntegrableOn g (Ioo 0 1) := by
    rw [← himage]
    exact (integrableOn_image_iff_integrableOn_abs_deriv_smul
      measurableSet_Ioi hderiv hinj g).mpr htransformed
  have hindIoi : IntegrableOn ((Ioo (0 : ℝ) 1).indicator g) (Ioi 0) :=
    (hgIoo.integrable_indicator measurableSet_Ioo).integrableOn
  change IntegrableOn (fun x : ℝ ↦
    (x : ℂ) ^ (s - 1) * liLogAtom m x) (Ioi 0)
  refine IntegrableOn.congr_fun hindIoi ?_ measurableSet_Ioi
  intro x _hxpos
  by_cases hx : x ∈ Ioo (0 : ℝ) 1
  · rw [Set.indicator_of_mem hx]
    simp only [g, liLogAtom, if_pos hx]
  · rw [Set.indicator_of_notMem hx]
    simp only [liLogAtom, if_neg hx, mul_zero]

/-- Exact Mellin transform of one logarithmic atom. -/
theorem mellin_liLogAtom (m : ℕ) (s : ℂ) (hs : 0 < s.re) :
    mellin (liLogAtom m) s =
      ((-1 : ℂ) ^ m * (Nat.factorial m : ℂ)) / s ^ (m + 1) := by
  unfold mellin
  simp only [smul_eq_mul]
  have hrestrict :
      (∫ x : ℝ in Ioi 0,
          (x : ℂ) ^ (s - 1) * liLogAtom m x) =
        ∫ x : ℝ in Ioo 0 1,
          (x : ℂ) ^ (s - 1) * ((Real.log x) ^ m : ℝ) := by
    rw [← integral_indicator measurableSet_Ioi,
      ← integral_indicator measurableSet_Ioo]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ Ioo (0 : ℝ) 1
    · have hxpos : x ∈ Ioi (0 : ℝ) := hx.1
      rw [Set.indicator_of_mem hxpos, Set.indicator_of_mem hx]
      simp only [liLogAtom, if_pos hx]
    · rw [Set.indicator_of_notMem hx]
      by_cases hpos : x ∈ Ioi (0 : ℝ)
      · rw [Set.indicator_of_mem hpos]
        simp only [liLogAtom, if_neg hx, mul_zero]
      · rw [Set.indicator_of_notMem hpos]
  rw [hrestrict, integral_Ioo_cpow_logPow,
    integral_laplacePow m s hs]
  ring

/-- Bombieri's polynomial
`P_n(u) = ∑_{j=1}^n choose(n,j) u^(j-1)/(j-1)!`, reindexed by `m = j-1`. -/
def liPolynomial (n : ℕ) (u : ℝ) : ℝ :=
  ∑ m ∈ Finset.range n,
    (Nat.choose n (m + 1) : ℝ) * u ^ m / (Nat.factorial m : ℝ)

/-- The source-level inverse Mellin kernel, with endpoint values suppressed
because they do not affect the Lebesgue integral. -/
def liKernel (n : ℕ) (x : ℝ) : ℂ :=
  if x ∈ Ioo (0 : ℝ) 1 then liPolynomial n (Real.log x) else 0

private theorem liKernel_eq_sum_liLogAtom (n : ℕ) (x : ℝ) :
    liKernel n x =
      ∑ m ∈ Finset.range n,
        ((Nat.choose n (m + 1) : ℂ) / (Nat.factorial m : ℂ)) *
          liLogAtom m x := by
  by_cases hx : x ∈ Ioo (0 : ℝ) 1
  · simp only [liKernel, liPolynomial, liLogAtom, if_pos hx]
    push_cast
    apply Finset.sum_congr rfl
    intro m _hm
    ring
  · simp [liKernel, liLogAtom, hx]

private theorem li_binomial_sum (n : ℕ) (z : ℂ) :
    (∑ m ∈ Finset.range n,
      (Nat.choose n (m + 1) : ℂ) * (-1 : ℂ) ^ m * z ^ (m + 1)) =
      1 - (1 - z) ^ n := by
  have h := add_pow (-z) 1 n
  rw [Finset.sum_range_succ'] at h
  simp only [one_pow, mul_one, Nat.choose_zero_right, Nat.cast_one, pow_zero] at h
  calc
    _ = ∑ m ∈ Finset.range n,
        -((-z) ^ (m + 1) * (Nat.choose n (m + 1) : ℂ)) := by
      apply Finset.sum_congr rfl
      intro m _hm
      rw [neg_pow, pow_succ]
      ring
    _ = -(∑ m ∈ Finset.range n,
        ((-z) ^ (m + 1) * (Nat.choose n (m + 1) : ℂ))) := by
      rw [Finset.sum_neg_distrib]
    _ = 1 - (1 - z) ^ n := by
      rw [show (1 - z) ^ n = (-z + 1) ^ n by ring]
      rw [h]
      ring

/-- The full Li kernel genuinely converges in the half-plane where its source
Mellin calculation is valid. -/
theorem liKernel_mellinConvergent
    (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    MellinConvergent (liKernel n) s := by
  change IntegrableOn (fun x : ℝ ↦
    (x : ℂ) ^ (s - 1) * liKernel n x) (Ioi 0)
  have hintegrand :
      (fun x : ℝ ↦ (x : ℂ) ^ (s - 1) * liKernel n x) =
        fun x : ℝ ↦ ∑ m ∈ Finset.range n,
          (x : ℂ) ^ (s - 1) *
            (((Nat.choose n (m + 1) : ℂ) / (Nat.factorial m : ℂ)) *
              liLogAtom m x) := by
    funext x
    rw [liKernel_eq_sum_liLogAtom]
    rw [Finset.mul_sum]
  rw [hintegrand]
  apply integrable_finset_sum
  intro m _hm
  have hconv := liLogAtom_mellinConvergent m s hs
  change IntegrableOn (fun x : ℝ ↦
    (x : ℂ) ^ (s - 1) * liLogAtom m x) (Ioi 0) at hconv
  let c : ℂ :=
    (Nat.choose n (m + 1) : ℂ) / (Nat.factorial m : ℂ)
  have hc := hconv.const_mul c
  refine IntegrableOn.congr_fun hc ?_ measurableSet_Ioi
  intro x _hx
  dsimp only [c]
  ring

/-- Bombieri's full inverse Mellin calculation. -/
theorem mellin_liKernel (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    mellin (liKernel n) s = liFunction n s := by
  have hsum : mellin (liKernel n) s =
      ∑ m ∈ Finset.range n,
        ((Nat.choose n (m + 1) : ℂ) / (Nat.factorial m : ℂ)) *
          mellin (liLogAtom m) s := by
    unfold mellin
    simp only [smul_eq_mul]
    have hintegrand :
        (fun x : ℝ ↦ (x : ℂ) ^ (s - 1) * liKernel n x) =
          fun x : ℝ ↦ ∑ m ∈ Finset.range n,
            (x : ℂ) ^ (s - 1) *
              (((Nat.choose n (m + 1) : ℂ) / (Nat.factorial m : ℂ)) *
                liLogAtom m x) := by
      funext x
      rw [liKernel_eq_sum_liLogAtom]
      rw [Finset.mul_sum]
    rw [hintegrand]
    rw [MeasureTheory.integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro m _hm
      let c : ℂ :=
        (Nat.choose n (m + 1) : ℂ) / (Nat.factorial m : ℂ)
      calc
        (∫ x : ℝ in Ioi 0,
            (x : ℂ) ^ (s - 1) * (c * liLogAtom m x)) =
          ∫ x : ℝ in Ioi 0,
            c * ((x : ℂ) ^ (s - 1) * liLogAtom m x) := by
              apply setIntegral_congr_fun measurableSet_Ioi
              intro x _hx
              ring
        _ = c * ∫ x : ℝ in Ioi 0,
            (x : ℂ) ^ (s - 1) * liLogAtom m x :=
          MeasureTheory.integral_const_mul
            (r := c) (f := fun x : ℝ ↦
              (x : ℂ) ^ (s - 1) * liLogAtom m x)
        _ = c * mellin (liLogAtom m) s := by
          rfl
    · intro m hm
      have hconv := liLogAtom_mellinConvergent m s hs
      change IntegrableOn (fun x : ℝ ↦
        (x : ℂ) ^ (s - 1) * liLogAtom m x) (Ioi 0) at hconv
      let c : ℂ :=
        (Nat.choose n (m + 1) : ℂ) / (Nat.factorial m : ℂ)
      have hc := hconv.const_mul c
      refine IntegrableOn.congr_fun hc ?_ measurableSet_Ioi
      intro x _hx
      dsimp only [c]
      ring
  rw [hsum]
  simp_rw [mellin_liLogAtom _ _ hs]
  rw [show liFunction n s = 1 - (1 - s⁻¹) ^ n by
    simp [liFunction, div_eq_mul_inv]]
  rw [← li_binomial_sum n s⁻¹]
  apply Finset.sum_congr rfl
  intro m _hm
  have hfact : (Nat.factorial m : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero m
  field_simp [hfact]
  ring

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
