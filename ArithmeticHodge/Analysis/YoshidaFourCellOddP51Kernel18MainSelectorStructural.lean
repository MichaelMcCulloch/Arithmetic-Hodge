import ArithmeticHodge.Analysis.YoshidaFourCellOddP51Kernel18RowDecompositionStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellOddP51Kernel18MainSelectorStructural

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointOcticPotential
open YoshidaFourCellOddFiniteLegendreSolveStructural
open YoshidaFourCellOddP51GalerkinRieszStructural
open YoshidaFourCellOddP51Kernel18RowDecompositionStructural
open YoshidaFourCellOddP51RawMassCancellationStructural
open YoshidaFourCellOddP51TailBudgetAssemblyStructural

/-!
# Low-mode selector for the degree-eighteen P51 main row

Every genuine `P53+` residual is orthogonal on the positive half interval to
`P1,P3,...,P51`.  Consequently an arbitrary selector in this complete
low-mode space can be subtracted from the exact piecewise main representer
without changing its pairing with the tail.  This turns the universal main
row estimate into one scalar `L²` estimate for the selector residual.
-/

/-- An arbitrary element of the complete positive-half low-mode space
`P1,P3,...,P51`. -/
def fourCellOddP51LowSelector
    (c : ℝ) (a : FourCellOddP51RetainedIndex → ℝ) (x : ℝ) : ℝ :=
  c * centeredP1 x + fourCellOddP51RetainedProfile a x

/-- The part of the exact degree-eighteen main row left after subtracting a
chosen complete low-mode selector. -/
def fourCellOddP51Kernel18MainSelectorResidual
    (c : ℝ) (a : FourCellOddP51RetainedIndex → ℝ) (x : ℝ) : ℝ :=
  fourCellOddP51Kernel18MainRepresenter x -
    fourCellOddP51LowSelector c a x

theorem continuous_fourCellOddP51LowSelector
    (c : ℝ) (a : FourCellOddP51RetainedIndex → ℝ) :
    Continuous (fourCellOddP51LowSelector c a) := by
  unfold fourCellOddP51LowSelector
  exact (continuous_const.mul (by
    unfold centeredP1
    fun_prop)).add
      (contDiff_fourCellOddFiniteRetainedProfile 24 a).continuous

/-- The complete low selector pairs to zero with every genuine `P53+`
residual.  All twenty-six low odd coordinates are eliminated at once. -/
theorem integral_zero_one_fourCellOddP51LowSelector_mul_P53Plus_eq_zero
    (c : ℝ) (a : FourCellOddP51RetainedIndex → ℝ)
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r)
    (hodd : Function.Odd r)
    (htail : FourCellOddP53PlusMomentConditions r) :
    (∫ x : ℝ in 0..1, fourCellOddP51LowSelector c a x * r x) = 0 := by
  have hP1 := integral_zero_one_centeredP1_mul_P53Plus_eq_zero
    r hr.continuous hodd htail.1
  have hretained :=
    integral_zero_one_fourCellOddFiniteRetainedProfile_mul_tail_eq_zero
      24 a r hr.continuous htail.2
  have hretained' : (∫ x : ℝ in 0..1,
      fourCellOddP51RetainedProfile a x * r x) = 0 := by
    simpa only [fourCellOddP51RetainedProfile] using hretained
  have hP1I : IntervalIntegrable
      (fun x : ℝ ↦ c * (centeredP1 x * r x)) volume 0 1 := by
    exact (continuous_const.mul
      ((by unfold centeredP1; fun_prop : Continuous centeredP1).mul
        hr.continuous)).intervalIntegrable _ _
  have hretainedI : IntervalIntegrable
      (fun x : ℝ ↦ fourCellOddP51RetainedProfile a x * r x)
      volume 0 1 := by
    exact ((contDiff_fourCellOddFiniteRetainedProfile 24 a).continuous.mul
      hr.continuous).intervalIntegrable _ _
  rw [show (fun x : ℝ ↦ fourCellOddP51LowSelector c a x * r x) =
      fun x ↦ c * (centeredP1 x * r x) +
        fourCellOddP51RetainedProfile a x * r x by
    funext x
    unfold fourCellOddP51LowSelector
    ring,
    intervalIntegral.integral_add hP1I hretainedI,
    intervalIntegral.integral_const_mul, hP1, hretained']
  ring

private theorem memLp_two_restrict_zero_one_of_continuous
    (r : ℝ → ℝ) (hr : Continuous r) :
    MemLp r 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have hrMeas : AEStronglyMeasurable r
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    hr.aestronglyMeasurable.restrict
  rw [memLp_two_iff_integrable_sq_norm hrMeas]
  have hcompact : IntegrableOn (fun x : ℝ ↦ ‖r x‖ ^ 2)
      (Icc (0 : ℝ) 1) :=
    (hr.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  exact hcompact.mono_set Ioc_subset_Icc_self

/-- Subtracting a complete low selector does not change the exact main-row
pairing on a genuine `P53+` residual.  The `MemLp` hypothesis is precisely
what is needed to justify the interval integral for a merely measurable
selector residual. -/
theorem integral_zero_one_fourCellOddP51Kernel18Main_eq_selectorResidual
    (c : ℝ) (a : FourCellOddP51RetainedIndex → ℝ)
    (hres : MemLp (fourCellOddP51Kernel18MainSelectorResidual c a) 2
      (volume.restrict (Ioc (0 : ℝ) 1)))
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r)
    (hodd : Function.Odd r)
    (htail : FourCellOddP53PlusMomentConditions r) :
    (∫ x : ℝ in 0..1,
        fourCellOddP51Kernel18MainRepresenter x * r x) =
      ∫ x : ℝ in 0..1,
        fourCellOddP51Kernel18MainSelectorResidual c a x * r x := by
  let R := fourCellOddP51Kernel18MainSelectorResidual c a
  let S := fourCellOddP51LowSelector c a
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  have hrLp : MemLp r 2 μ := by
    dsimp only [μ]
    exact memLp_two_restrict_zero_one_of_continuous r hr.continuous
  have hresProdI : IntervalIntegrable (fun x : ℝ ↦ R x * r x)
      volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    simpa only [μ, R] using hres.integrable_mul hrLp
  have hselectorProdI : IntervalIntegrable (fun x : ℝ ↦ S x * r x)
      volume 0 1 :=
    ((continuous_fourCellOddP51LowSelector c a).mul hr.continuous)
      |>.intervalIntegrable _ _
  have hselectorZero : (∫ x : ℝ in 0..1, S x * r x) = 0 := by
    dsimp only [S]
    exact integral_zero_one_fourCellOddP51LowSelector_mul_P53Plus_eq_zero
      c a r hr hodd htail
  rw [show (fun x : ℝ ↦
      fourCellOddP51Kernel18MainRepresenter x * r x) =
      fun x ↦ R x * r x + S x * r x by
    funext x
    dsimp only [R, S]
    unfold fourCellOddP51Kernel18MainSelectorResidual
    ring,
    intervalIntegral.integral_add hresProdI hselectorProdI,
    hselectorZero, add_zero]

/-- A concrete selector certificate for the `9/10` main-row budget.  It is a
single positive-half `L²` scalar inequality, with no quantification over the
infinite-dimensional tail. -/
def FourCellOddP51Kernel18MainSelectorCertificate
    (kappa c : ℝ) (a : FourCellOddP51RetainedIndex → ℝ) : Prop :=
  MemLp (fourCellOddP51Kernel18MainSelectorResidual c a) 2
      (volume.restrict (Ioc (0 : ℝ) 1)) ∧
    (∫ x : ℝ in 0..1,
        fourCellOddP51Kernel18MainSelectorResidual c a x ^ 2) ≤
      (9 / 10 : ℝ) * (fourCellOddP51GalerkinPivot * kappa)

/-- One selector certificate proves the complete universal `9/10` main-row
tail budget. -/
theorem fourCellOddP51Kernel18MainTailPairBudget_of_selectorCertificate
    (kappa c : ℝ) (a : FourCellOddP51RetainedIndex → ℝ)
    (hcertificate :
      FourCellOddP51Kernel18MainSelectorCertificate kappa c a) :
    FourCellOddP51TailPairBudget (9 / 10) kappa
      fourCellOddP51Kernel18MainRepresenter := by
  intro r hr hodd htail
  rw [integral_zero_one_fourCellOddP51Kernel18Main_eq_selectorResidual
    c a hcertificate.1 r hr hodd htail]
  have hcauchy := sq_intervalIntegral_mul_le_zero_one_of_memLp
    (fourCellOddP51Kernel18MainSelectorResidual c a) r
    hcertificate.1 hr.continuous
  have hmass : 0 ≤ ∫ x : ℝ in 0..1, r x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num)
      (fun x _hx ↦ sq_nonneg (r x))
  calc
    (∫ x : ℝ in 0..1,
        fourCellOddP51Kernel18MainSelectorResidual c a x * r x) ^ 2 ≤
        (∫ x : ℝ in 0..1,
          fourCellOddP51Kernel18MainSelectorResidual c a x ^ 2) *
            ∫ x : ℝ in 0..1, r x ^ 2 := hcauchy
    _ ≤ ((9 / 10 : ℝ) *
        (fourCellOddP51GalerkinPivot * kappa)) *
          ∫ x : ℝ in 0..1, r x ^ 2 :=
      mul_le_mul_of_nonneg_right hcertificate.2 hmass
    _ = (9 / 10 : ℝ) *
        (fourCellOddP51GalerkinPivot *
          (kappa * (∫ x : ℝ in 0..1, r x ^ 2))) := by ring

end

end ArithmeticHodge.Analysis.YoshidaFourCellOddP51Kernel18MainSelectorStructural
