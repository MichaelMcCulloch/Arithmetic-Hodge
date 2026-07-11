import ArithmeticHodge.Analysis.MultiplicativeWeilLiCutoff
import ArithmeticHodge.Analysis.MultiplicativeWeilLiSeries

set_option autoImplicit false

open Complex Filter MeasureTheory Real Set Topology

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-- The endpoint polynomial in the upper incomplete Laplace moment. -/
def liLaplaceTailPolynomial : ℕ → ℂ → ℝ → ℂ
  | 0, s, _L => 1 / s
  | m + 1, s, L =>
      (L : ℂ) ^ (m + 1) / s +
        (((m + 1 : ℕ) : ℂ) / s) *
          liLaplaceTailPolynomial m s L

/-- The Mellin mass removed from the `m`-th logarithmic atom by cutting at
`epsilon`. -/
def liCutoffLogMoment
    (m : ℕ) (epsilon : ℝ) (s : ℂ) : ℂ :=
  (-1 : ℂ) ^ m * (epsilon : ℂ) ^ s *
    liLaplaceTailPolynomial m s (-Real.log epsilon)

/-- The total endpoint correction for Bombieri's Li polynomial. -/
def liKernelCutoffCorrection
    (n : ℕ) (epsilon : ℝ) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.range n,
    ((Nat.choose n (m + 1) : ℂ) / (Nat.factorial m : ℂ)) *
      liCutoffLogMoment m epsilon s

/-- The removed atom has the exact decay factor `epsilon ^ s.re`; everything
else is a finite polynomial in `-log epsilon` and `1 / s`. -/
theorem norm_liCutoffLogMoment_eq
    (m : ℕ) (epsilon : ℝ) (s : ℂ) (hepsilon : 0 < epsilon) :
    ‖liCutoffLogMoment m epsilon s‖ =
      epsilon ^ s.re *
        ‖liLaplaceTailPolynomial m s (-Real.log epsilon)‖ := by
  unfold liCutoffLogMoment
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hepsilon]
  simp

/-- A finite-sum bound for the entire cutoff correction.  In particular, on
any region with `s.re` bounded below and the displayed polynomial sum bounded,
the correction decays uniformly with the cutoff. -/
theorem norm_liKernelCutoffCorrection_le
    (n : ℕ) (epsilon : ℝ) (s : ℂ) (hepsilon : 0 < epsilon) :
    ‖liKernelCutoffCorrection n epsilon s‖ ≤
      epsilon ^ s.re *
        ∑ m ∈ Finset.range n,
          ‖(Nat.choose n (m + 1) : ℂ) / (Nat.factorial m : ℂ)‖ *
            ‖liLaplaceTailPolynomial m s (-Real.log epsilon)‖ := by
  rw [liKernelCutoffCorrection]
  calc
    ‖∑ m ∈ Finset.range n,
        ((Nat.choose n (m + 1) : ℂ) / (Nat.factorial m : ℂ)) *
          liCutoffLogMoment m epsilon s‖ ≤
        ∑ m ∈ Finset.range n,
          ‖((Nat.choose n (m + 1) : ℂ) / (Nat.factorial m : ℂ)) *
            liCutoffLogMoment m epsilon s‖ := norm_sum_le _ _
    _ = ∑ m ∈ Finset.range n,
        epsilon ^ s.re *
          (‖(Nat.choose n (m + 1) : ℂ) / (Nat.factorial m : ℂ)‖ *
            ‖liLaplaceTailPolynomial m s (-Real.log epsilon)‖) := by
      apply Finset.sum_congr rfl
      intro m _hm
      rw [norm_mul, norm_liCutoffLogMoment_eq m epsilon s hepsilon]
      ring
    _ = epsilon ^ s.re *
        ∑ m ∈ Finset.range n,
          ‖(Nat.choose n (m + 1) : ℂ) / (Nat.factorial m : ℂ)‖ *
            ‖liLaplaceTailPolynomial m s (-Real.log epsilon)‖ := by
      rw [Finset.mul_sum]

private theorem laplaceTail_integrableOn
    (m : ℕ) (s : ℂ) (hs : 0 < s.re) (L : ℝ) (hL : 0 ≤ L) :
    IntegrableOn (fun t : ℝ ↦
      (t : ℂ) ^ m * Complex.exp (-(s * t))) (Ioi L) := by
  have hreal := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := (m : ℝ)) (b := s.re)
    (by have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m; linarith)
    (by norm_num) hs
  have hcomplex : IntegrableOn (fun t : ℝ ↦
      (t : ℂ) ^ m * Complex.exp (-(s * t))) (Ioi 0) := by
    refine hreal.congr' (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    simp [Complex.norm_exp, Real.norm_eq_abs, abs_of_pos ht,
      Real.rpow_natCast, Real.rpow_one]
  exact hcomplex.mono_set (Ioi_subset_Ioi hL)

/-- Exact upper incomplete Laplace moment, expressed through the recursive
endpoint polynomial. -/
theorem integral_laplaceTail_eq
    (m : ℕ) (s : ℂ) (hs : 0 < s.re) (L : ℝ) (hL : 0 ≤ L) :
    (∫ t : ℝ in Ioi L,
      (t : ℂ) ^ m * Complex.exp (-(s * t))) =
        Complex.exp (-(s * L)) * liLaplaceTailPolynomial m s L := by
  induction m with
  | zero =>
      have hbase := integral_exp_mul_complex_Ioi
        (a := -s) (by simpa using (neg_lt_zero.mpr hs)) L
      simpa [liLaplaceTailPolynomial, div_eq_mul_inv] using hbase
  | succ m ih =>
      let u : ℝ → ℂ := fun t ↦ (t : ℂ) ^ (m + 1)
      let u' : ℝ → ℂ := fun t ↦
        ((m + 1 : ℕ) : ℂ) * (t : ℂ) ^ m
      let v : ℝ → ℂ := fun t ↦ Complex.exp (-(s * t))
      let v' : ℝ → ℂ := fun t ↦
        Complex.exp (-(s * t)) * (-s)
      have hu : ∀ t ∈ Ioi L, HasDerivAt u (u' t) t := by
        intro t _ht
        dsimp only [u, u']
        simpa using Complex.ofRealCLM.hasDerivAt.pow (m + 1)
      have hv : ∀ t ∈ Ioi L, HasDerivAt v (v' t) t := by
        intro t _ht
        dsimp only [v, v']
        simpa using ((Complex.ofRealCLM.hasDerivAt.const_mul s).neg.cexp)
      have huv' : IntegrableOn (u * v') (Ioi L) := by
        have h := (laplaceTail_integrableOn
          (m + 1) s hs L hL).const_mul (-s)
        refine IntegrableOn.congr_fun h ?_ measurableSet_Ioi
        intro t _ht
        dsimp only [u, v', Pi.mul_apply]
        ring
      have hu'v : IntegrableOn (u' * v) (Ioi L) := by
        have h := (laplaceTail_integrableOn m s hs L hL).const_mul
          (((m + 1 : ℕ) : ℂ))
        refine IntegrableOn.congr_fun h ?_ measurableSet_Ioi
        intro t _ht
        dsimp only [u', v, Pi.mul_apply]
        ring
      have hLboundary :
          (L : ℂ) ^ (m + 1) * Complex.exp (-(s * L)) =
            u L * v L := by rfl
      have hzero : Tendsto (u * v) (nhdsWithin L (Ioi L))
          (nhds ((L : ℂ) ^ (m + 1) * Complex.exp (-(s * L)))) := by
        have hcont : ContinuousAt (u * v) L := by
          dsimp only [u, v]
          fun_prop
        simpa only [hLboundary] using hcont.tendsto.mono_left inf_le_left
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
          (∫ t : ℝ in Ioi L, u t * v' t) =
            (-s) * ∫ t : ℝ in Ioi L,
              (t : ℂ) ^ (m + 1) * Complex.exp (-(s * t)) := by
        calc
          _ = ∫ t : ℝ in Ioi L,
              (-s) * ((t : ℂ) ^ (m + 1) * Complex.exp (-(s * t))) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro t _ht
            dsimp only [u, v']
            ring
          _ = _ := MeasureTheory.integral_const_mul
            (r := -s) (f := fun t : ℝ ↦
              (t : ℂ) ^ (m + 1) * Complex.exp (-(s * t)))
      have hright :
          (∫ t : ℝ in Ioi L, u' t * v t) =
            (((m + 1 : ℕ) : ℂ)) * ∫ t : ℝ in Ioi L,
              (t : ℂ) ^ m * Complex.exp (-(s * t)) := by
        calc
          _ = ∫ t : ℝ in Ioi L,
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
          (-s) * (∫ t : ℝ in Ioi L,
              (t : ℂ) ^ (m + 1) * Complex.exp (-(s * t))) =
            -((L : ℂ) ^ (m + 1) * Complex.exp (-(s * L))) -
              (((m + 1 : ℕ) : ℂ)) * ∫ t : ℝ in Ioi L,
                (t : ℂ) ^ m * Complex.exp (-(s * t)) := by
        calc
          _ = ∫ t : ℝ in Ioi L, u t * v' t := hleft.symm
          _ = 0 - ((L : ℂ) ^ (m + 1) * Complex.exp (-(s * L))) -
              ∫ t : ℝ in Ioi L, u' t * v t := hparts
          _ = _ := by rw [hright]; ring
      have hs0 : s ≠ 0 := by
        intro hszero
        rw [hszero] at hs
        norm_num at hs
      have hrec :
          s * (∫ t : ℝ in Ioi L,
              (t : ℂ) ^ (m + 1) * Complex.exp (-(s * t))) =
            (L : ℂ) ^ (m + 1) * Complex.exp (-(s * L)) +
              (((m + 1 : ℕ) : ℂ)) * ∫ t : ℝ in Ioi L,
                (t : ℂ) ^ m * Complex.exp (-(s * t)) := by
        linear_combination -hparts'
      rw [ih] at hrec
      apply (mul_left_cancel₀ hs0)
      rw [hrec]
      simp only [liLaplaceTailPolynomial]
      field_simp [hs0]

private theorem negExp_image_Ici_negLog
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    (fun t : ℝ ↦ Real.exp (-t)) '' Ici (-Real.log epsilon) =
      Ioc 0 epsilon := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    change -Real.log epsilon ≤ t at ht
    refine ⟨Real.exp_pos _, ?_⟩
    rw [← Real.exp_log hepsilon, Real.exp_le_exp]
    linarith
  · intro hx
    refine ⟨-Real.log x, ?_, ?_⟩
    · change -Real.log epsilon ≤ -Real.log x
      have hlog := Real.strictMonoOn_log.monotoneOn hx.1 hepsilon hx.2
      linarith
    · simp [Real.exp_log hx.1]

private theorem exp_neg_mul_negLog_eq_cpow
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (s : ℂ) :
    Complex.exp (-(s * ((-Real.log epsilon : ℝ) : ℂ))) =
      (epsilon : ℂ) ^ s := by
  rw [Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr hepsilon.ne')]
  have hlog : Complex.log (epsilon : ℂ) = (Real.log epsilon : ℝ) := by
    rw [show (epsilon : ℂ) = Complex.exp (Real.log epsilon : ℝ) by
      rw [← Complex.ofReal_exp, Real.exp_log hepsilon]]
    rw [Complex.log_exp] <;> simp [Real.pi_pos, Real.pi_nonneg]
  rw [hlog, Complex.ofReal_neg]
  congr 1
  ring

/-- Exact Mellin mass of the logarithmic atom below the cutoff. -/
theorem integral_Ioc_cpow_logPow_eq_cutoffMoment
    (m : ℕ) (epsilon : ℝ) (s : ℂ)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hs : 0 < s.re) :
    (∫ x : ℝ in Ioc 0 epsilon,
      (x : ℂ) ^ (s - 1) * ((Real.log x) ^ m : ℝ)) =
        liCutoffLogMoment m epsilon s := by
  let φ : ℝ → ℝ := fun t ↦ Real.exp (-t)
  let φ' : ℝ → ℝ := fun t ↦ -Real.exp (-t)
  let g : ℝ → ℂ := fun x ↦
    (x : ℂ) ^ (s - 1) * ((Real.log x) ^ m : ℝ)
  let L : ℝ := -Real.log epsilon
  have hLpos : 0 < L := by
    dsimp only [L]
    exact neg_pos.mpr (Real.log_neg hepsilon0 hepsilon1)
  have hderiv : ∀ t ∈ Ici L, HasDerivWithinAt φ (φ' t) (Ici L) t := by
    intro t _ht
    have htderiv : HasDerivAt φ (φ' t) t := by
      dsimp only [φ, φ']
      simpa using (hasDerivAt_id t).neg.exp
    exact htderiv.hasDerivWithinAt
  have hinj : Set.InjOn φ (Ici L) := by
    intro a _ha b _hb hab
    dsimp only [φ] at hab
    exact neg_injective (Real.exp_injective hab)
  have himage : φ '' Ici L = Ioc 0 epsilon := by
    exact negExp_image_Ici_negLog hepsilon0
  have hchange := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ici hderiv hinj g
  rw [himage] at hchange
  calc
    _ = ∫ t : ℝ in Ici L, |φ' t| • g (φ t) := hchange
    _ = ∫ t : ℝ in Ici L,
        (-1 : ℂ) ^ m *
          ((t : ℂ) ^ m * Complex.exp (-(s * t))) := by
      apply setIntegral_congr_fun measurableSet_Ici
      intro t _ht
      dsimp only [φ, φ', g]
      rw [abs_neg, abs_of_pos (Real.exp_pos _), Real.log_exp]
      simp only [Complex.real_smul]
      rw [Complex.cpow_def_of_ne_zero
        (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))]
      have hlog : Complex.log ((Real.exp (-t) : ℝ) : ℂ) =
          ((-t : ℝ) : ℂ) := by
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
          rw [show -(t : ℂ) + (-(t : ℂ) * (s - 1)) =
            -(s * t) by ring]
          ring
    _ = (-1 : ℂ) ^ m * ∫ t : ℝ in Ici L,
        (t : ℂ) ^ m * Complex.exp (-(s * t)) :=
      MeasureTheory.integral_const_mul
        (r := ((-1 : ℂ) ^ m)) (f := fun t : ℝ ↦
          (t : ℂ) ^ m * Complex.exp (-(s * t)))
    _ = (-1 : ℂ) ^ m * ∫ t : ℝ in Ioi L,
        (t : ℂ) ^ m * Complex.exp (-(s * t)) := by
      rw [integral_Ici_eq_integral_Ioi]
    _ = (-1 : ℂ) ^ m *
        (Complex.exp (-(s * L)) *
          liLaplaceTailPolynomial m s L) := by
      rw [integral_laplaceTail_eq m s hs L hLpos.le]
    _ = liCutoffLogMoment m epsilon s := by
      rw [show Complex.exp (-(s * L)) = (epsilon : ℂ) ^ s by
        exact exp_neg_mul_negLog_eq_cpow hepsilon0 s]
      dsimp only [L, liCutoffLogMoment]
      ring

/-- A single logarithmic atom with the same lower cutoff as `liKernelCutoff`. -/
def liLogAtomCutoff (m : ℕ) (epsilon x : ℝ) : ℂ :=
  if x ∈ Ioo epsilon 1 then ((Real.log x) ^ m : ℝ) else 0

private theorem liLogAtomCutoff_integrand_eq_indicator
    (m : ℕ) (epsilon : ℝ) (s : ℂ) (hepsilon : 0 ≤ epsilon) :
    (fun x : ℝ ↦
      (x : ℂ) ^ (s - 1) * liLogAtomCutoff m epsilon x) =
      (Ioi epsilon).indicator
        (fun x : ℝ ↦ (x : ℂ) ^ (s - 1) * liLogAtom m x) := by
  funext x
  by_cases hx : x ∈ Ioi epsilon
  · rw [Set.indicator_of_mem hx]
    have hxpos : 0 < x := hepsilon.trans_lt hx
    by_cases hx1 : x < 1
    · have hcut : x ∈ Ioo epsilon 1 := ⟨hx, hx1⟩
      have hfull : x ∈ Ioo (0 : ℝ) 1 := ⟨hxpos, hx1⟩
      simp only [liLogAtomCutoff, liLogAtom,
        if_pos hcut, if_pos hfull]
    · have hcut : ¬x ∈ Ioo epsilon 1 := fun h ↦ hx1 h.2
      have hfull : ¬x ∈ Ioo (0 : ℝ) 1 := fun h ↦ hx1 h.2
      simp [liLogAtomCutoff, liLogAtom, hcut, hfull]
  · rw [Set.indicator_of_notMem hx]
    have hcut : ¬x ∈ Ioo epsilon 1 := fun h ↦ hx h.1
    simp [liLogAtomCutoff, hcut]

/-- Each cutoff logarithmic atom has a genuine Mellin integral. -/
theorem liLogAtomCutoff_mellinConvergent
    (m : ℕ) (epsilon : ℝ) (s : ℂ)
    (hepsilon : 0 ≤ epsilon) (hs : 0 < s.re) :
    MellinConvergent (liLogAtomCutoff m epsilon) s := by
  have hfull := liLogAtom_mellinConvergent m s hs
  change Integrable (fun x : ℝ ↦
    (x : ℂ) ^ (s - 1) * liLogAtom m x)
      (volume.restrict (Ioi 0)) at hfull
  change Integrable (fun x : ℝ ↦
    (x : ℂ) ^ (s - 1) * liLogAtomCutoff m epsilon x)
      (volume.restrict (Ioi 0))
  rw [liLogAtomCutoff_integrand_eq_indicator m epsilon s hepsilon]
  exact hfull.indicator measurableSet_Ioi

/-- Exact cutoff formula for one logarithmic atom. -/
theorem mellin_liLogAtomCutoff_eq
    (m : ℕ) (epsilon : ℝ) (s : ℂ)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hs : 0 < s.re) :
    mellin (liLogAtomCutoff m epsilon) s =
      mellin (liLogAtom m) s - liCutoffLogMoment m epsilon s := by
  let f : ℝ → ℂ := fun x ↦
    (x : ℂ) ^ (s - 1) * liLogAtom m x
  have hfull : IntegrableOn f (Ioi 0) := by
    simpa only [f, MellinConvergent, smul_eq_mul] using
      liLogAtom_mellinConvergent m s hs
  have hlowInt : IntegrableOn f (Ioc 0 epsilon) :=
    hfull.mono_set Ioc_subset_Ioi_self
  have hhighInt : IntegrableOn f (Ioi epsilon) :=
    hfull.mono_set (Ioi_subset_Ioi hepsilon0.le)
  have hsplit :
      (∫ x : ℝ in Ioi 0, f x) =
        (∫ x : ℝ in Ioc 0 epsilon, f x) +
          ∫ x : ℝ in Ioi epsilon, f x := by
    rw [← Ioc_union_Ioi_eq_Ioi hepsilon0.le]
    exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      hlowInt hhighInt
  have hlow :
      (∫ x : ℝ in Ioc 0 epsilon, f x) =
        liCutoffLogMoment m epsilon s := by
    rw [← integral_Ioc_cpow_logPow_eq_cutoffMoment
      m epsilon s hepsilon0 hepsilon1 hs]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    dsimp only [f]
    have hfullmem : x ∈ Ioo (0 : ℝ) 1 :=
      ⟨hx.1, hx.2.trans_lt hepsilon1⟩
    simp only [liLogAtom, if_pos hfullmem]
  have hcut :
      mellin (liLogAtomCutoff m epsilon) s =
        ∫ x : ℝ in Ioi epsilon, f x := by
    unfold mellin
    simp only [smul_eq_mul]
    rw [liLogAtomCutoff_integrand_eq_indicator
      m epsilon s hepsilon0.le]
    rw [integral_indicator measurableSet_Ioi]
    rw [Measure.restrict_restrict measurableSet_Ioi]
    rw [inter_eq_left.mpr (Ioi_subset_Ioi hepsilon0.le)]
  rw [hcut]
  change (∫ x : ℝ in Ioi epsilon, f x) =
    (∫ x : ℝ in Ioi 0, f x) - liCutoffLogMoment m epsilon s
  rw [hlow] at hsplit
  rw [eq_sub_iff_add_eq, add_comm]
  exact hsplit.symm

private theorem liKernelCutoff_eq_sum_logAtoms
    (n : ℕ) (epsilon x : ℝ) :
    liKernelCutoff n epsilon x =
      ∑ m ∈ Finset.range n,
        ((Nat.choose n (m + 1) : ℂ) / (Nat.factorial m : ℂ)) *
          liLogAtomCutoff m epsilon x := by
  by_cases hx : x ∈ Ioo epsilon 1
  · simp only [liKernelCutoff, liPolynomial, liLogAtomCutoff,
      if_pos hx]
    push_cast
    apply Finset.sum_congr rfl
    intro m _hm
    ring
  · simp [liKernelCutoff, liLogAtomCutoff, hx]

private theorem mellin_liKernelCutoff_eq_sum
    (n : ℕ) (epsilon : ℝ) (s : ℂ)
    (hepsilon : 0 ≤ epsilon) (hs : 0 < s.re) :
    mellin (liKernelCutoff n epsilon) s =
      ∑ m ∈ Finset.range n,
        ((Nat.choose n (m + 1) : ℂ) / (Nat.factorial m : ℂ)) *
          mellin (liLogAtomCutoff m epsilon) s := by
  unfold mellin
  simp only [smul_eq_mul]
  have hintegrand :
      (fun x : ℝ ↦ (x : ℂ) ^ (s - 1) * liKernelCutoff n epsilon x) =
        fun x : ℝ ↦ ∑ m ∈ Finset.range n,
          (x : ℂ) ^ (s - 1) *
            (((Nat.choose n (m + 1) : ℂ) / (Nat.factorial m : ℂ)) *
              liLogAtomCutoff m epsilon x) := by
    funext x
    rw [liKernelCutoff_eq_sum_logAtoms]
    rw [Finset.mul_sum]
  rw [hintegrand]
  rw [MeasureTheory.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro m _hm
    let c : ℂ :=
      (Nat.choose n (m + 1) : ℂ) / (Nat.factorial m : ℂ)
    calc
      (∫ x : ℝ in Ioi 0,
          (x : ℂ) ^ (s - 1) *
            (c * liLogAtomCutoff m epsilon x)) =
        ∫ x : ℝ in Ioi 0,
          c * ((x : ℂ) ^ (s - 1) *
            liLogAtomCutoff m epsilon x) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x _hx
          ring
      _ = c * ∫ x : ℝ in Ioi 0,
          (x : ℂ) ^ (s - 1) * liLogAtomCutoff m epsilon x :=
        MeasureTheory.integral_const_mul
          (r := c) (f := fun x : ℝ ↦
            (x : ℂ) ^ (s - 1) * liLogAtomCutoff m epsilon x)
      _ = c * mellin (liLogAtomCutoff m epsilon) s := by
        rfl
  · intro m _hm
    have hconv := liLogAtomCutoff_mellinConvergent
      m epsilon s hepsilon hs
    change IntegrableOn (fun x : ℝ ↦
      (x : ℂ) ^ (s - 1) * liLogAtomCutoff m epsilon x)
        (Ioi 0) at hconv
    let c : ℂ :=
      (Nat.choose n (m + 1) : ℂ) / (Nat.factorial m : ℂ)
    have hc := hconv.const_mul c
    refine IntegrableOn.congr_fun hc ?_ measurableSet_Ioi
    intro x _hx
    dsimp only [c]
    ring

/-- RED target: the cutoff Mellin transform is the full Li function minus an
explicit endpoint polynomial. -/
theorem mellin_liKernelCutoff_eq_liFunction_sub_correction
    (n : ℕ) (epsilon : ℝ) (s : ℂ)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hs : 0 < s.re) :
    mellin (liKernelCutoff n epsilon) s =
      liFunction n s - liKernelCutoffCorrection n epsilon s := by
  rw [mellin_liKernelCutoff_eq_sum n epsilon s hepsilon0.le hs]
  simp_rw [mellin_liLogAtomCutoff_eq
    _ epsilon s hepsilon0 hepsilon1 hs]
  have hfull :
      (∑ m ∈ Finset.range n,
        ((Nat.choose n (m + 1) : ℂ) / (Nat.factorial m : ℂ)) *
          mellin (liLogAtom m) s) = liFunction n s := by
    rw [← mellin_liKernel n s hs]
    simpa only [liKernelCutoff, liKernel, liLogAtomCutoff, liLogAtom]
      using (mellin_liKernelCutoff_eq_sum
        n 0 s (le_refl 0) hs).symm
  rw [liKernelCutoffCorrection]
  calc
    (∑ m ∈ Finset.range n,
        ((Nat.choose n (m + 1) : ℂ) / (Nat.factorial m : ℂ)) *
          (mellin (liLogAtom m) s -
            liCutoffLogMoment m epsilon s)) =
        (∑ m ∈ Finset.range n,
          ((Nat.choose n (m + 1) : ℂ) / (Nat.factorial m : ℂ)) *
            mellin (liLogAtom m) s) -
          ∑ m ∈ Finset.range n,
            ((Nat.choose n (m + 1) : ℂ) / (Nat.factorial m : ℂ)) *
              liCutoffLogMoment m epsilon s := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro m _hm
      ring
    _ = liFunction n s -
        ∑ m ∈ Finset.range n,
          ((Nat.choose n (m + 1) : ℂ) / (Nat.factorial m : ℂ)) *
            liCutoffLogMoment m epsilon s := by
      rw [hfull]

/-- Quantitative cutoff error bound, in the form needed for uniform estimates
on zero-free regions. -/
theorem norm_mellin_liKernelCutoff_sub_liFunction_le
    (n : ℕ) (epsilon : ℝ) (s : ℂ)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hs : 0 < s.re) :
    ‖mellin (liKernelCutoff n epsilon) s - liFunction n s‖ ≤
      epsilon ^ s.re *
        ∑ m ∈ Finset.range n,
          ‖(Nat.choose n (m + 1) : ℂ) / (Nat.factorial m : ℂ)‖ *
            ‖liLaplaceTailPolynomial m s (-Real.log epsilon)‖ := by
  rw [mellin_liKernelCutoff_eq_liFunction_sub_correction
    n epsilon s hepsilon0 hepsilon1 hs]
  have hdiff :
      liFunction n s - liKernelCutoffCorrection n epsilon s -
          liFunction n s =
        -liKernelCutoffCorrection n epsilon s := by
    ring
  rw [hdiff, norm_neg]
  exact norm_liKernelCutoffCorrection_le n epsilon s hepsilon0

end

end ArithmeticHodge.Analysis.MultiplicativeWeil

