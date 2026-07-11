import ArithmeticHodge.Analysis.FourierTransform

open MeasureTheory Real Complex Filter Convolution Set

namespace ArithmeticHodge.Analysis

/-!
This file audits the two remaining Fourier-transform scaffolds without changing
their production statements.  The first obstruction is elementary: an
autocorrelation need not be pointwise nonnegative.  Only its Fourier transform
is nonnegative.
-/

/-- A signed compactly supported block used to test pointwise claims about
autocorrelations. -/
private noncomputable def signedBlock (x : ℝ) : ℝ :=
  (Ioc (0 : ℝ) 1).indicator (fun _ => 1) x -
    (Ioc (1 : ℝ) 2).indicator (fun _ => 1) x

private theorem signedBlock_integrable : Integrable signedBlock volume := by
  unfold signedBlock
  exact
    ((integrableOn_const (s := Ioc (0 : ℝ) 1) (by simp [Real.volume_Ioc])).integrable_indicator
      measurableSet_Ioc).sub
      ((integrableOn_const (s := Ioc (1 : ℝ) 2) (by simp [Real.volume_Ioc])).integrable_indicator
        measurableSet_Ioc)

private theorem signedBlock_sq_integrable :
    Integrable (fun x => signedBlock x ^ 2) volume := by
  have hpoint : (fun x => signedBlock x ^ 2) =
      (Ioc (0 : ℝ) 2).indicator (fun _ => 1) := by
    funext x
    by_cases h0 : 0 < x
    · by_cases h1 : x ≤ 1
      · have h2 : x ≤ 2 := by linarith
        simp [signedBlock, Set.mem_Ioc, h0, h1, h2]
      · have h1' : 1 < x := lt_of_not_ge h1
        by_cases h2 : x ≤ 2
        · simp [signedBlock, Set.mem_Ioc, h0, h1, h1', h2]
        · have h2' : ¬ x ≤ 2 := h2
          simp [signedBlock, Set.mem_Ioc, h0, h1, h1', h2']
    · have h0' : ¬ 0 < x := h0
      have h1' : ¬ 1 < x := by linarith
      simp [signedBlock, Set.mem_Ioc, h0', h1']
  rw [hpoint]
  exact
    (integrableOn_const (s := Ioc (0 : ℝ) 2) (by simp [Real.volume_Ioc])).integrable_indicator
      measurableSet_Ioc

/-- The autocorrelation of `signedBlock`. -/
private noncomputable def signedBlockAutocorrelation (x : ℝ) : ℝ :=
  ∫ y : ℝ, signedBlock y * signedBlock (y + x)

private theorem signedBlock_isAutocorrelation :
    IsAutocorrelation signedBlockAutocorrelation := by
  exact ⟨signedBlock, signedBlock_integrable, signedBlock_sq_integrable, fun _ => rfl⟩

/-- A concrete autocorrelation taking a negative value.  This formally rules
out the pointwise-nonnegativity step suggested in the forward scaffold. -/
theorem autocorrelation_not_pointwise_nonnegative_scratch :
    signedBlockAutocorrelation 1 = -1 := by
  unfold signedBlockAutocorrelation
  have hpoint : ∀ y : ℝ,
      signedBlock y * signedBlock (y + 1) =
        -(Ioc (0 : ℝ) 1).indicator (fun _ => 1) y := by
    intro y
    by_cases h0 : 0 < y
    · by_cases h1 : y ≤ 1
      · have hy1 : 1 < y + 1 := by linarith
        have hy2 : y + 1 ≤ 2 := by linarith
        simp [signedBlock, Set.mem_Ioc, h0, h1, hy1, hy2]
      · have hy1 : ¬ y + 1 ≤ 2 := by linarith
        simp [signedBlock, Set.mem_Ioc, h0, h1, hy1]
    · have h0' : ¬ 0 < y := h0
      by_cases hm1 : 0 < y + 1
      · have hm2 : y + 1 ≤ 1 := by linarith
        have hy1 : ¬ 1 < y := by linarith
        simp [signedBlock, Set.mem_Ioc, h0', hm1, hm2, hy1]
      · have hm1' : ¬ 0 < y + 1 := hm1
        have hy1 : ¬ 1 < y := by linarith
        simp [signedBlock, Set.mem_Ioc, h0', hm1', hy1]
  simp_rw [hpoint]
  rw [integral_neg]
  simp

/-- Consequently, even the exact `IsAutocorrelation` predicate used by the
forward theorem does not imply nonnegative values on the real axis. -/
theorem exists_autocorrelation_with_negative_value_scratch :
    ∃ f : ℝ → ℝ, IsAutocorrelation f ∧ f 1 < 0 := by
  refine ⟨signedBlockAutocorrelation, signedBlock_isAutocorrelation, ?_⟩
  rw [autocorrelation_not_pointwise_nonnegative_scratch]
  norm_num

/-- On the same example, the autocorrelation value cannot be replaced by its
Fourier value: the former is negative and the latter is nonnegative. -/
theorem autocorrelation_value_ne_fourier_value_scratch :
    signedBlockAutocorrelation 1 ≠ fourierCos signedBlockAutocorrelation 1 := by
  have hfourier : 0 ≤ fourierCos signedBlockAutocorrelation 1 :=
    fourierCos_autocorrelation_nonneg signedBlock signedBlock_integrable
      signedBlock_sq_integrable signedBlockAutocorrelation (fun _ => rfl) 1
  rw [autocorrelation_not_pointwise_nonnegative_scratch]
  linarith

/-- The transform-side spectral identity that the forward Weil argument
actually needs.  This differs from the current `weil_explicit_formula`, whose
summands are `f (zeros n)` rather than `fourierCos f (zeros n)`. -/
def FourierSpectralExplicitFormula : Prop :=
  ∀ (f : ℝ → ℝ), Continuous f →
    (∀ x : ℝ, ‖f x‖ ≤ 1 / (1 + x ^ 2)) →
    RiemannHypothesis →
    ∃ zeros : ℕ → ℝ,
      Summable (fun n => fourierCos f (zeros n)) ∧
      ∑' n, fourierCos f (zeros n) =
        weilFunctionalFull f (fourierCos f)

/-- With the correctly oriented spectral identity, the forward implication is
an immediate sum of the already-proved nonnegative Fourier values. -/
theorem rh_implies_weil_positivity_from_fourier_spectral_explicit_scratch
    (hexplicit : FourierSpectralExplicitFormula) :
    RiemannHypothesis → WeilPositivity := by
  intro hRH f hf_auto hf_cont hf_decay
  obtain ⟨g, hg, hg_sq, hf⟩ := hf_auto
  obtain ⟨zeros, _hsum, hexpl⟩ := hexplicit f hf_cont hf_decay hRH
  rw [← hexpl]
  exact tsum_nonneg fun n =>
    fourierCos_autocorrelation_nonneg g hg hg_sq f hf (zeros n)

/-!
Bombieri's Theorem 2 does not state negativity of the single Gaussian family
used in `bombieriAutocorrelation_weil_neg`; it states the explicit formula and
the all-test-functions Weil criterion.  The exact production conclusion is of
course vacuous under RH, as the next clean lemma records.  It supplies no
non-circular backward argument.
-/

private theorem rh_nontrivial_zero_re_scratch
    (hRH : RiemannHypothesis) (rho : NontrivialZetaZero) :
    rho.val.re = 1 / 2 := by
  apply hRH rho.val rho.is_zero
  · rintro ⟨n, hn⟩
    have hre := rho.re_pos
    rw [hn] at hre
    norm_num [Complex.mul_re] at hre
    have hn_nonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  · intro hn
    have hre := rho.re_lt_one
    rw [hn] at hre
    norm_num at hre

/-- RH proves the Gaussian-negativity statement only by eliminating its
off-critical-line premise. -/
theorem rh_implies_bombieri_gaussian_neg_vacuously_scratch
    (hRH : RiemannHypothesis) (rho : NontrivialZetaZero)
    (hσ : rho.val.re ≠ 1 / 2) :
    weilFunctionalFull (bombieriAutocorrelation rho.val.re)
      (fourierCos (bombieriAutocorrelation rho.val.re)) < 0 := by
  exact (hσ (rh_nontrivial_zero_re_scratch hRH rho)).elim

#print axioms autocorrelation_not_pointwise_nonnegative_scratch
#print axioms exists_autocorrelation_with_negative_value_scratch
#print axioms autocorrelation_value_ne_fourier_value_scratch
#print axioms rh_implies_weil_positivity_from_fourier_spectral_explicit_scratch
#print axioms rh_implies_bombieri_gaussian_neg_vacuously_scratch
#print axioms exists_autocorrelation_with_negative_value

end ArithmeticHodge.Analysis
