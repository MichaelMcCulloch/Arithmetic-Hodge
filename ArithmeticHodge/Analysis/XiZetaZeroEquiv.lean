import ArithmeticHodge.Analysis.XiZetaMultiplicityBridge
import ArithmeticHodge.Analysis.MultiplicativeWeilZeroFiberSum

/-!
# Xi and nontrivial zeta zeros

This file identifies completed-xi zeros with nontrivial zeta zeros, transports
finite critical-rectangle sums across that equivalence, and proves convergence
of the finite divisor sums occurring in the contour argument.
-/

set_option autoImplicit false

open Complex Filter Topology

namespace ArithmeticHodge.Analysis

/-- The subtype of complex zeros of the completed xi function. -/
abbrev XiZeroSubtype := {z : ℂ // xiFunction z = 0}

/-- Xi zeros are exactly nontrivial zeta zeros, with the underlying complex
number unchanged. -/
def xiZeroEquivNontrivialZetaZero :
    XiZeroSubtype ≃ NontrivialZetaZero where
  toFun z := by
    have hre := xiFunction_zero_re z.property
    exact ⟨z.val, (xiFunction_zero_iff hre.1 hre.2).mp z.property,
      hre.1, hre.2⟩
  invFun rho :=
    ⟨rho.val,
      (xiFunction_zero_iff rho.re_pos rho.re_lt_one).mpr rho.is_zero⟩
  left_inv z := by
    apply Subtype.ext
    rfl
  right_inv rho := by
    cases rho
    rfl

@[simp]
theorem xiZeroEquivNontrivialZetaZero_apply_val
    (z : XiZeroSubtype) :
    (xiZeroEquivNontrivialZetaZero z).val = z.val := rfl

@[simp]
theorem xiZeroEquivNontrivialZetaZero_symm_apply_val
    (rho : NontrivialZetaZero) :
    (xiZeroEquivNontrivialZetaZero.symm rho).val = rho.val := rfl

@[simp]
theorem xiZeroEquivNontrivialZetaZero_symm_apply_coe
    (rho : NontrivialZetaZero) :
    ((xiZeroEquivNontrivialZetaZero.symm rho : XiZeroSubtype) : ℂ) =
      rho.val := rfl

private noncomputable def xiZeroRectangleToNontrivialEmbedding
    (sigmaLower sigmaUpper heightLower heightUpper : ℝ) :
    {z : ℂ // z ∈ xiZerosInRectangle
      sigmaLower sigmaUpper heightLower heightUpper} ↪ NontrivialZetaZero where
  toFun z := xiZeroEquivNontrivialZetaZero
    ⟨z.val,
      (mem_xiZerosInRectangle_iff
        sigmaLower sigmaUpper heightLower heightUpper z.val).mp z.property |>.2⟩
  inj' := by
    intro z w hzw
    apply Subtype.ext
    exact congrArg NontrivialZetaZero.val hzw

/-- The finite set of nontrivial zeta zeros corresponding to the distinct xi
zeros in a closed rectangle. -/
noncomputable def nontrivialZetaZerosInRectangle
    (sigmaLower sigmaUpper heightLower heightUpper : ℝ) :
    Finset NontrivialZetaZero :=
  (xiZerosInRectangle sigmaLower sigmaUpper heightLower heightUpper).attach.map
    (xiZeroRectangleToNontrivialEmbedding
      sigmaLower sigmaUpper heightLower heightUpper)

@[simp]
theorem mem_nontrivialZetaZerosInRectangle_iff
    (sigmaLower sigmaUpper heightLower heightUpper : ℝ)
    (rho : NontrivialZetaZero) :
    rho ∈ nontrivialZetaZerosInRectangle
        sigmaLower sigmaUpper heightLower heightUpper ↔
      rho.val ∈ xiZerosInRectangle
        sigmaLower sigmaUpper heightLower heightUpper := by
  classical
  rw [nontrivialZetaZerosInRectangle, Finset.mem_map]
  constructor
  · rintro ⟨z, _hz, rfl⟩
    exact z.property
  · intro hrho
    let z : {z : ℂ // z ∈ xiZerosInRectangle
        sigmaLower sigmaUpper heightLower heightUpper} := ⟨rho.val, hrho⟩
    refine ⟨z, Finset.mem_attach _ _, ?_⟩
    cases rho
    rfl

/-- In the critical strip, membership in the finite rectangle set is exactly
the elementary imaginary-height cutoff. -/
@[simp]
theorem mem_nontrivialZetaZerosInCriticalRectangle_iff
    (T : ℝ) (rho : NontrivialZetaZero) :
    rho ∈ nontrivialZetaZerosInRectangle 0 1 (-T) T ↔
      |rho.val.im| ≤ T := by
  rw [mem_nontrivialZetaZerosInRectangle_iff,
    mem_xiZerosInRectangle_iff]
  constructor
  · intro hrho
    have hrect := hrho.1
    rw [xiZeroRectangle, mem_reProdIm] at hrect
    exact abs_le.mpr hrect.2
  · intro him
    refine ⟨?_, (xiFunction_zero_iff rho.re_pos rho.re_lt_one).mpr rho.is_zero⟩
    rw [xiZeroRectangle, mem_reProdIm]
    exact ⟨⟨rho.re_pos.le, rho.re_lt_one.le⟩, abs_le.mp him⟩

/-- Any height cutoff tending to infinity gives a cofinal exhaustion of the
nontrivial-zero subtype by the finite critical rectangles. -/
theorem tendsto_nontrivialZetaZerosInCriticalRectangle_atTop
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) :
    Tendsto
      (fun n => nontrivialZetaZerosInRectangle 0 1 (-T n) (T n))
      atTop atTop := by
  apply tendsto_atTop.2
  intro S
  filter_upwards [(eventually_all_finset S).2
    (fun rho _hrho => hT.eventually_ge_atTop |rho.val.im|)] with n hn
  intro rho hrho
  rw [mem_nontrivialZetaZerosInCriticalRectangle_iff]
  exact hn rho hrho

/-- Reindex any finite sum over the distinct xi zeros in a rectangle as a sum
over the corresponding finite set of nontrivial zeta zeros. -/
theorem sum_xiZerosInRectangle_eq_sum_nontrivialZetaZerosInRectangle
    {M : Type*} [AddCommMonoid M]
    (sigmaLower sigmaUpper heightLower heightUpper : ℝ) (F : ℂ → M) :
    ∑ z ∈ xiZerosInRectangle sigmaLower sigmaUpper heightLower heightUpper,
        F z =
      ∑ rho ∈ nontrivialZetaZerosInRectangle
          sigmaLower sigmaUpper heightLower heightUpper,
        F rho.val := by
  classical
  rw [nontrivialZetaZerosInRectangle, Finset.sum_map]
  exact (Finset.sum_attach
    (xiZerosInRectangle sigmaLower sigmaUpper heightLower heightUpper) F).symm

/-- The contour zero sum can be reindexed over nontrivial zeta zeros and its
xi multiplicities replaced by analytic zeta multiplicities. -/
theorem sum_xiZeroMultiplicity_eq_sum_zetaMultiplicity
    {M : Type*} [AddCommMonoid M]
    (T : ℝ) (F : ℂ → M) :
    ∑ z ∈ xiZerosInRectangle 0 1 (-T) T,
        xiZeroMultiplicity z • F z =
      ∑ rho ∈ nontrivialZetaZerosInRectangle 0 1 (-T) T,
        analyticOrderNatAt riemannZeta rho.val • F rho.val := by
  rw [sum_xiZerosInRectangle_eq_sum_nontrivialZetaZerosInRectangle]
  apply Finset.sum_congr rfl
  intro rho _hrho
  rw [xiZeroMultiplicity_eq_analyticOrderNatAt_riemannZeta]

/-- Consequently, every summable distinct-zero family is the limit of its
finite critical-rectangle sums along any heights tending to infinity. -/
theorem tendsto_sum_nontrivialZetaZerosInCriticalRectangle
    (G : NontrivialZetaZero → ℂ) (hG : Summable G)
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) :
    Tendsto
      (fun n => ∑ rho ∈
        nontrivialZetaZerosInRectangle 0 1 (-T n) (T n), G rho)
      atTop (nhds (∑' rho : NontrivialZetaZero, G rho)) := by
  exact hG.hasSum.comp
    (tendsto_nontrivialZetaZerosInCriticalRectangle_atTop hT)

namespace MultiplicativeWeil

/-- The finite analytic-multiplicity-weighted Mellin zero sums over expanding
critical rectangles converge to the distinct-zero `tsum`. -/
theorem tendsto_finite_zetaMultiplicity_mellin_sum
    (f : BombieriTest) {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) :
    Tendsto
      (fun n => ∑ rho ∈
        nontrivialZetaZerosInRectangle 0 1 (-T n) (T n),
          (analyticOrderNatAt riemannZeta rho.val : ℂ) *
            mellin (f : ℝ → ℂ) rho.val)
      atTop
      (nhds (∑' rho : NontrivialZetaZero,
        (analyticOrderNatAt riemannZeta rho.val : ℂ) *
          mellin (f : ℝ → ℂ) rho.val)) := by
  classical
  let zeros : ZetaZeroEnumeration :=
    Classical.choice nonempty_zetaZeroEnumeration
  have hsum : Summable (fun rho : NontrivialZetaZero =>
      (analyticOrderNatAt riemannZeta rho.val : ℂ) *
        mellin (f : ℝ → ℂ) rho.val) :=
    zeros.distinct_multiplicity_summable
      (fun rho => mellin (f : ℝ → ℂ) rho.val)
      (zeros.mellin_summable f)
  exact tendsto_sum_nontrivialZetaZerosInCriticalRectangle _ hsum hT

/-- Equivalently, the finite xi-divisor Mellin sums produced by the contour
formula converge to the analytic-multiplicity-weighted distinct zeta-zero
`tsum`. -/
theorem tendsto_finite_xiMultiplicity_mellin_sum
    (f : BombieriTest) {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) :
    Tendsto
      (fun n => ∑ z ∈ xiZerosInRectangle 0 1 (-T n) (T n),
        (xiZeroMultiplicity z : ℂ) * mellin (f : ℝ → ℂ) z)
      atTop
      (nhds (∑' rho : NontrivialZetaZero,
        (analyticOrderNatAt riemannZeta rho.val : ℂ) *
          mellin (f : ℝ → ℂ) rho.val)) := by
  have hzeta := tendsto_finite_zetaMultiplicity_mellin_sum f hT
  apply hzeta.congr'
  exact Filter.Eventually.of_forall fun n => by
    simpa only [nsmul_eq_mul] using
      (sum_xiZeroMultiplicity_eq_sum_zetaMultiplicity
        (M := ℂ) (T n) (fun z => mellin (f : ℝ → ℂ) z)).symm

end MultiplicativeWeil

end ArithmeticHodge.Analysis
