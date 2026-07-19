import ArithmeticHodge.Analysis.MultiplicativeWeilFixedLogLatticeFarChebyshevStructural

set_option autoImplicit false

open Complex MeasureTheory Real Set TopologicalSpace
open scoped ArithmeticFunction

namespace ArithmeticHodge.Analysis.MultiplicativeWeilSeparatedCellCrossStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilDirectedCorrelationPhysicalStructural
open MultiplicativeWeilFarPhysicalKernelStructural
open MultiplicativeWeilFixedLogLatticeFarChebyshevStructural
open MultiplicativeWeilMangoldtDiscrepancyAbelStructural

/-!
# The actual cross between separated logarithmic cells

Strict support separation kills only the reverse directed prime shell.  The
surviving shell is not banded in logarithmic lag: its integer sampling window
moves linearly with the dilation parameter.  This module records that support
statement exactly and isolates the only genuinely decaying part of the full
cross, namely the nonsingular archimedean kernel.  The remaining leading term
is the pairing with `Chebyshev.psi - id`.
-/

/-- One term of the surviving Mangoldt shell in undilated cell coordinates. -/
def separatedFarPrimeShellTerm
    (f g : BombieriTest) (r : ℝ) (k : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt (k + 1) : ℂ) *
    ((((Real.sqrt r)⁻¹ : ℝ) : ℂ) *
      starRingEnd ℂ
        (bombieriDirectedCorrelation f g
          (r⁻¹ * (k + 1 : ℕ))))

/-- A separated prime-shell term can survive only when its rescaled integer
sample lies in the physical support quotient of the two cells. -/
theorem separatedFarPrimeShellTerm_eq_zero_of_not_mem_supportQuotient
    (f g : BombieriTest) {af bf ag bg r : ℝ}
    (haf : 0 < af) (hag : 0 < ag) (hbg : 0 < bg)
    (hf : tsupport f ⊆ Set.Icc af bf)
    (hg : tsupport g ⊆ Set.Icc ag bg)
    (k : ℕ)
    (hk : r⁻¹ * (k + 1 : ℕ) ∉ Set.Icc (af / bg) (bf / ag)) :
    separatedFarPrimeShellTerm f g r k = 0 := by
  unfold separatedFarPrimeShellTerm
  rw [star_bombieriDirectedCorrelation_eq_zero_outside_supportQuotient
    f g haf hag hbg hf hg hk, mul_zero, mul_zero]

/-- Consequently the infinite notation for the far prime shell is exactly
the sum of the preceding terms. -/
theorem bombieriSeparatedFarPrimeShell_eq_tsum_terms
    (f g : BombieriTest) (r : ℝ) :
    bombieriSeparatedFarPrimeShell f g r =
      ∑' k : ℕ, separatedFarPrimeShellTerm f g r k := by
  rfl

/-- The surviving shell has a finite moving window: any natural cutoff above
`r * (bf / ag)` contains every potentially nonzero term.  Thus support
separation gives finiteness, but not a fixed logarithmic bandwidth. -/
theorem bombieriSeparatedFarPrimeShell_eq_sum_range
    (f g : BombieriTest) {af bf ag bg r : ℝ}
    (hr : 0 < r) (haf : 0 < af) (hag : 0 < ag) (hbg : 0 < bg)
    (hf : tsupport f ⊆ Set.Icc af bf)
    (hg : tsupport g ⊆ Set.Icc ag bg)
    (N : ℕ) (hN : r * (bf / ag) < N) :
    bombieriSeparatedFarPrimeShell f g r =
      ∑ k ∈ Finset.range N, separatedFarPrimeShellTerm f g r k := by
  rw [bombieriSeparatedFarPrimeShell_eq_tsum_terms]
  apply tsum_eq_sum
  intro k hk
  rw [Finset.mem_range] at hk
  apply separatedFarPrimeShellTerm_eq_zero_of_not_mem_supportQuotient
    f g haf hag hbg hf hg k
  intro hmem
  have hupper := hmem.2
  have hrinv : 0 < r⁻¹ := inv_pos.mpr hr
  have hscaled : (k + 1 : ℕ) ≤ r * (bf / ag) := by
    calc
      ((k + 1 : ℕ) : ℝ) = r * (r⁻¹ * (k + 1 : ℕ)) := by
        field_simp [hr.ne']
      _ ≤ r * (bf / ag) := mul_le_mul_of_nonneg_left hupper hr.le
  have hNk : N ≤ k := Nat.le_of_not_gt hk
  have hkN : (N : ℝ) < (k + 1 : ℕ) := by
    exact_mod_cast (hNk.trans_lt (Nat.lt_succ_self k))
  linarith

/-! ## The only decaying part of the complete cross -/

/-- The physical nonsingular archimedean correction in a separated cross. -/
def separatedArchimedeanKernel
    (f g : BombieriTest) (r : ℝ) : ℂ :=
  ∫ x : ℝ in Set.Ioi 0,
    starRingEnd ℂ (bombieriDirectedCorrelation f g x) /
      ((x * ((r * x) ^ 2 - 1) : ℝ) : ℂ)

/-- The `L¹` mass controlling the separated archimedean correction. -/
def separatedCorrelationNormMass (f g : BombieriTest) : ℝ :=
  ∫ x : ℝ in Set.Ioi 0,
    ‖starRingEnd ℂ (bombieriDirectedCorrelation f g x)‖

/-- The arithmetic leading term of the separated cross after Abel summation. -/
def separatedChebyshevErrorPairing
    (f g : BombieriTest) (r : ℝ) : ℂ :=
  ∫ x : ℝ in Set.Ioi 0,
    ((Chebyshev.psi (r * x) - r * x : ℝ) : ℂ) *
      deriv (fun y : ℝ ↦
        starRingEnd ℂ (bombieriDirectedCorrelation f g y)) x

/-- The complete separated cross is exactly its Chebyshev-error pairing
minus the archimedean correction. -/
theorem sqrt_mul_globalCross_eq_chebyshevError_sub_archimedeanKernel
    (f g : BombieriTest) {af bf ag bg r : ℝ}
    (hr : 0 < r) (haf : 0 < af) (hag : 0 < ag) (hbg : 0 < bg)
    (hf : tsupport f ⊆ Set.Icc af bf)
    (hg : tsupport g ⊆ Set.Icc ag bg)
    (hsep : bg / af < r) :
    ((Real.sqrt r : ℝ) : ℂ) *
        bombieriTwoBlockGlobalCrossSymbol f
          (normalizedDilation r hr g) =
      separatedChebyshevErrorPairing f g r -
        separatedArchimedeanKernel f g r := by
  simpa only [separatedChebyshevErrorPairing,
    separatedArchimedeanKernel] using
    (sqrt_mul_bombieriTwoBlockGlobalCrossSymbol_normalizedDilation_eq_chebyshevError_sub_kernel
      f g hr haf hag hbg hf hg hsep)

/-- Quantitative support bound for the decaying archimedean correction.  If
`L = af / bg` is the lower endpoint of the correlation quotient, then the
scaled correction is `O((L * ((rL)^2 - 1))⁻¹)`, hence `O(r⁻²)` at
fixed cells. -/
theorem norm_separatedArchimedeanKernel_le
    (f g : BombieriTest) {af bf ag bg r : ℝ}
    (hr : 0 < r) (haf : 0 < af) (hag : 0 < ag) (hbg : 0 < bg)
    (hf : tsupport f ⊆ Set.Icc af bf)
    (hg : tsupport g ⊆ Set.Icc ag bg)
    (hsep : bg / af < r) :
    ‖separatedArchimedeanKernel f g r‖ ≤
      (af / bg * ((r * (af / bg)) ^ 2 - 1))⁻¹ *
        separatedCorrelationNormMass f g := by
  let H : ℝ → ℂ := fun x ↦
    starRingEnd ℂ (bombieriDirectedCorrelation f g x)
  let L : ℝ := af / bg
  let D : ℝ := L * ((r * L) ^ 2 - 1)
  let C : ℝ := D⁻¹
  have hL : 0 < L := by
    dsimp only [L]
    exact div_pos haf hbg
  have hrL : 1 < r * L := by
    have hcross : bg < r * af := (div_lt_iff₀ haf).mp hsep
    calc
      (1 : ℝ) = bg / bg := by field_simp [hbg.ne']
      _ < (r * af) / bg := (div_lt_div_iff_of_pos_right hbg).2 hcross
      _ = r * L := by simp only [L]; ring
  have hD : 0 < D := by
    dsimp only [D]
    exact mul_pos hL (by nlinarith [sq_nonneg (r * L - 1)])
  have hC : 0 ≤ C := (inv_pos.mpr hD).le
  have hHInt : IntegrableOn H (Set.Ioi 0) := by
    simpa only [H] using
      (star_bombieriDirectedCorrelation_integrableOn_Ioi
        f g haf hag hbg hf hg)
  have hdomInt : IntegrableOn (fun x : ℝ ↦ C * ‖H x‖) (Set.Ioi 0) :=
    hHInt.norm.const_mul C
  have hpoint (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
      ‖H x / ((x * ((r * x) ^ 2 - 1) : ℝ) : ℂ)‖ ≤
        C * ‖H x‖ := by
    by_cases hHx : H x = 0
    · simp [hHx]
    have hxmem : x ∈ Set.Icc (af / bg) (bf / ag) := by
      by_contra hout
      exact hHx (by
        dsimp only [H]
        exact star_bombieriDirectedCorrelation_eq_zero_outside_supportQuotient
          f g haf hag hbg hf hg hout)
    have hLx : L ≤ x := by simpa only [L] using hxmem.1
    have hxpos : 0 < x := hL.trans_le hLx
    have hrLle : r * L ≤ r * x :=
      mul_le_mul_of_nonneg_left hLx hr.le
    have hrx : 1 < r * x := hrL.trans_le hrLle
    have hsquare : (r * L) ^ 2 ≤ (r * x) ^ 2 := by
      exact (sq_le_sq₀ (zero_le_one.trans hrL.le)
        (zero_le_one.trans hrx.le)).2 hrLle
    have hdenL : 0 < (r * L) ^ 2 - 1 := by
      nlinarith [sq_nonneg (r * L - 1)]
    have hdenx : 0 < (r * x) ^ 2 - 1 := by
      nlinarith [sq_nonneg (r * x - 1)]
    have hdenLe : D ≤ x * ((r * x) ^ 2 - 1) := by
      dsimp only [D]
      exact mul_le_mul hLx (by linarith) hdenL.le hxpos.le
    have hinv : (x * ((r * x) ^ 2 - 1))⁻¹ ≤ C := by
      dsimp only [C]
      exact (inv_le_inv₀ (mul_pos hxpos hdenx) hD).2 hdenLe
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (mul_pos hxpos hdenx)]
    have hmul := mul_le_mul_of_nonneg_right hinv (norm_nonneg (H x))
    simpa only [div_eq_mul_inv, mul_comm] using hmul
  have hkernelMeas : AEStronglyMeasurable
      (fun x : ℝ ↦
        H x / ((x * ((r * x) ^ 2 - 1) : ℝ) : ℂ))
      (volume.restrict (Set.Ioi 0)) := by
    have hden : AEStronglyMeasurable
        (fun x : ℝ ↦ ((x * ((r * x) ^ 2 - 1) : ℝ) : ℂ))
        (volume.restrict (Set.Ioi 0)) := by
      exact (by fun_prop : Continuous
        (fun x : ℝ ↦ ((x * ((r * x) ^ 2 - 1) : ℝ) : ℂ))).aestronglyMeasurable
    simpa only [div_eq_mul_inv] using
      hHInt.1.mul hden.aemeasurable.inv.aestronglyMeasurable
  have hkernelInt : IntegrableOn
      (fun x : ℝ ↦
        H x / ((x * ((r * x) ^ 2 - 1) : ℝ) : ℂ))
      (Set.Ioi 0) := by
    apply hdomInt.mono' hkernelMeas
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hpoint x hx
  calc
    ‖separatedArchimedeanKernel f g r‖ =
        ‖∫ x : ℝ in Set.Ioi 0,
          H x / ((x * ((r * x) ^ 2 - 1) : ℝ) : ℂ)‖ := by
      rfl
    _ ≤ ∫ x : ℝ in Set.Ioi 0,
        ‖H x / ((x * ((r * x) ^ 2 - 1) : ℝ) : ℂ)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ in Set.Ioi 0, C * ‖H x‖ := by
      apply integral_mono_ae hkernelInt.norm hdomInt
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact hpoint x hx
    _ = C * separatedCorrelationNormMass f g := by
      rw [MeasureTheory.integral_const_mul]
      rfl
    _ = (af / bg * ((r * (af / bg)) ^ 2 - 1))⁻¹ *
        separatedCorrelationNormMass f g := by
      rfl

/-- Sharp structural conclusion for the *full* separated cross: after the
critical `sqrt r` normalization, everything except the Chebyshev-error
pairing has the preceding `O(r⁻²)` bound.  No sign or decay is asserted for
the arithmetic pairing. -/
theorem norm_sqrt_mul_globalCross_sub_chebyshevError_le
    (f g : BombieriTest) {af bf ag bg r : ℝ}
    (hr : 0 < r) (haf : 0 < af) (hag : 0 < ag) (hbg : 0 < bg)
    (hf : tsupport f ⊆ Set.Icc af bf)
    (hg : tsupport g ⊆ Set.Icc ag bg)
    (hsep : bg / af < r) :
    ‖((Real.sqrt r : ℝ) : ℂ) *
          bombieriTwoBlockGlobalCrossSymbol f
            (normalizedDilation r hr g) -
        separatedChebyshevErrorPairing f g r‖ ≤
      (af / bg * ((r * (af / bg)) ^ 2 - 1))⁻¹ *
        separatedCorrelationNormMass f g := by
  rw [sqrt_mul_globalCross_eq_chebyshevError_sub_archimedeanKernel
    f g hr haf hag hbg hf hg hsep]
  have hbound := norm_separatedArchimedeanKernel_le
    f g hr haf hag hbg hf hg hsep
  simpa only [sub_sub_cancel_left, norm_neg] using hbound

/-- Concrete fixed-half-octave specialization.  At every lag `k ≥ 3`, the
archimedean part of the cross between `[1,2]` base cells has an explicit
quadratically decaying bound; the Chebyshev-error pairing is the entire
remaining obstruction to any global far-cell contraction. -/
theorem norm_fixedLogLattice_globalCross_sub_chebyshevError_le
    (f g : BombieriTest) (k : ℤ) (hk : 3 ≤ k)
    (hf : tsupport f ⊆ Set.Icc 1 2)
    (hg : tsupport g ⊆ Set.Icc 1 2) :
    ‖((Real.sqrt (fixedLogLatticePoint k) : ℝ) : ℂ) *
          bombieriTwoBlockGlobalCrossSymbol f
            (normalizedDilation (fixedLogLatticePoint k)
              (fixedLogLatticePoint_pos k) g) -
        separatedChebyshevErrorPairing f g
          (fixedLogLatticePoint k)‖ ≤
      ((1 / 2 : ℝ) *
          ((fixedLogLatticePoint k * (1 / 2 : ℝ)) ^ 2 - 1))⁻¹ *
        separatedCorrelationNormMass f g := by
  apply norm_sqrt_mul_globalCross_sub_chebyshevError_le
    f g (fixedLogLatticePoint_pos k)
      (by norm_num) (by norm_num) (by norm_num) hf hg
  simpa only [div_one] using two_lt_fixedLogLatticePoint_of_three_le hk

end

end ArithmeticHodge.Analysis.MultiplicativeWeilSeparatedCellCrossStructural
