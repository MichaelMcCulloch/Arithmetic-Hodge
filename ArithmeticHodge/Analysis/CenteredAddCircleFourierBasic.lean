import Mathlib.Analysis.Fourier.AddCircle

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace ArithmeticHodge.Analysis

abbrev CenteredAddCircle (a : ℝ) := AddCircle (2 * a)

def centeredLift (a : ℝ) [Fact (0 < 2 * a)] (f : ℝ → ℂ) :
    CenteredAddCircle a → ℂ :=
  AddCircle.liftIoc (2 * a) (-a) f

def centeredFourierCoeff {a : ℝ} (ha : 0 < a)
    (f : ℝ → ℂ) (n : ℤ) : ℂ :=
  fourierCoeffOn (neg_lt_self ha) f n

theorem centeredLift_apply_Ioc
    {a x : ℝ} [Fact (0 < 2 * a)] (f : ℝ → ℂ)
    (hx : x ∈ Set.Ioc (-a) a) :
    centeredLift a f (x : CenteredAddCircle a) = f x := by
  apply AddCircle.liftIoc_coe_apply
  simpa only [show -a + 2 * a = a by ring] using hx

theorem centeredFourierCoeff_eq_integral
    {a : ℝ} (ha : 0 < a) (f : ℝ → ℂ) (n : ℤ) :
    centeredFourierCoeff ha f n =
      (1 / (2 * a) : ℝ) • ∫ x in -a..a,
        fourier (-n) (x : CenteredAddCircle a) • f x := by
  letI : NormedSpace ℝ ℂ := NormedSpace.complexToReal
  rw [centeredFourierCoeff, fourierCoeffOn_eq_integral]
  have hperiod : a - -a = 2 * a := by ring
  rw [hperiod]
  apply Complex.ext <;> rfl

theorem centeredLift_memLp
    {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ}
    (hL2 : MeasureTheory.MemLp f 2
      (volume.restrict (Set.Ioc (-a) a))) :
    letI : Fact (0 < 2 * a) := ⟨by positivity⟩
    MeasureTheory.MemLp (centeredLift a f) 2
      AddCircle.haarAddCircle := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  have hL2' : MeasureTheory.MemLp f 2
      (volume.restrict (Set.Ioc (-a) (-a + 2 * a))) := by
    simpa only [show -a + 2 * a = a by ring] using hL2
  exact hL2'.memLp_liftIoc.haarAddCircle

theorem centeredLift_toLp_fourierCoeff
    {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ}
    (hL2 : MeasureTheory.MemLp f 2
      (volume.restrict (Set.Ioc (-a) a))) (n : ℤ) :
    letI : Fact (0 < 2 * a) := ⟨by positivity⟩
    let hF := centeredLift_memLp ha hL2
    fourierCoeff (hF.toLp (centeredLift a f)) n =
      centeredFourierCoeff ha f n := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  let hF := centeredLift_memLp ha hL2
  calc
    fourierCoeff (hF.toLp (centeredLift a f)) n =
        fourierCoeff (centeredLift a f) n :=
      congrFun (fourierCoeff_congr_ae hF.coeFn_toLp) n
    _ = centeredFourierCoeff ha f n := by
      simpa only [centeredLift, centeredFourierCoeff,
        show -a + 2 * a = a by ring] using
          (fourierCoeff_liftIoc_eq (T := 2 * a) (a := -a) f n)

theorem hasSum_centered_fourier_series_L2
    {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ}
    (hL2 : MeasureTheory.MemLp f 2
      (volume.restrict (Set.Ioc (-a) a))) :
    letI : Fact (0 < 2 * a) := ⟨by positivity⟩
    let hF := centeredLift_memLp ha hL2
    HasSum
      (fun n : ℤ => centeredFourierCoeff ha f n • fourierLp 2 n)
      (hF.toLp (centeredLift a f)) := by
  letI : Fact (0 < 2 * a) := ⟨by positivity⟩
  let hF := centeredLift_memLp ha hL2
  simpa only [centeredLift_toLp_fourierCoeff ha hL2] using
    (hasSum_fourier_series_L2 (hF.toLp (centeredLift a f)))

end ArithmeticHodge.Analysis
