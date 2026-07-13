import ArithmeticHodge.Analysis.YoshidaClippedPeriodicCore

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.YoshidaPointwiseOddPeriodicCore

open ArithmeticHodge.Analysis

noncomputable section

/-- The structural periodic odd carrier, defined by literal pointwise oddness
instead of importing a Fourier certificate layer. -/
def yoshidaPointwiseOddPeriodicCoreSubmodule (a : ℝ) :
    Submodule ℂ (YoshidaClippedPeriodicCore a) where
  carrier := {f | Function.Odd
    (((f : YoshidaClippedPeriodicCore a) : YoshidaClippedSmooth a) : ℝ → ℂ)}
  zero_mem' := by
    intro x
    simp
  add_mem' := by
    intro f g hf hg x
    simp only [Submodule.coe_add, Pi.add_apply]
    rw [hf x, hg x]
    ring
  smul_mem' := by
    intro c f hf x
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [hf x]
    ring

/-- A periodic odd profile vanishes at both identified endpoints. -/
theorem pointwiseOddPeriodicCore_endpoints_zero
    {a : ℝ} (ha : 0 < a)
    (f : yoshidaPointwiseOddPeriodicCoreSubmodule a) :
    (((f.1 : YoshidaClippedPeriodicCore a) : YoshidaClippedSmooth a) a = 0) ∧
      (((f.1 : YoshidaClippedPeriodicCore a) : YoshidaClippedSmooth a) (-a) = 0) := by
  let g : YoshidaClippedPeriodicCore a := f.1
  let h : ℝ → ℂ :=
    (((g : YoshidaClippedPeriodicCore a) : YoshidaClippedSmooth a) : ℝ → ℂ)
  have hodd : Function.Odd h := by
    exact f.property
  have hnegMem : -a ∈ Icc (-a) a := by
    constructor <;> linarith
  have hposMem : a ∈ Icc (-a) a := by
    constructor <;> linarith
  have hend : h a = h (-a) := by
    calc
      h a = periodicExtension g a := by
        exact (periodicExtension_apply_of_mem g hposMem).symm
      _ = periodicExtension g (-a + 2 * a) := by
        congr 1
        ring
      _ = periodicExtension g (-a) := periodicExtension_periodic g (-a)
      _ = h (-a) := periodicExtension_apply_of_mem g hnegMem
  have hself : h a = -h a := by
    exact hend.trans (hodd a)
  have hzero : h a = 0 := CharZero.eq_neg_self_iff.mp hself
  change h a = 0 ∧ h (-a) = 0
  constructor
  · exact hzero
  · rw [hodd a, hzero, neg_zero]

end

end ArithmeticHodge.Analysis.YoshidaPointwiseOddPeriodicCore
