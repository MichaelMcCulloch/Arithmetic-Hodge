import ArithmeticHodge.Analysis.YoshidaEndpointEvenLowPotential
import ArithmeticHodge.Analysis.YoshidaEndpointEvenP2LogEnergy
import ArithmeticHodge.Analysis.YoshidaEndpointPotentialIntegrable

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenLowProfile

open UnitIntervalLogEnergyAffine
open YoshidaEndpointEvenLowPotential
open YoshidaEndpointEvenP2LogEnergy
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialIntegrable

noncomputable section

/-- The fixed structural `{P₀,P₂}` profile. -/
def yoshidaEndpointEvenLowProfile (c b : ℝ) : ℝ → ℝ := fun x ↦
  c + b * centeredEvenP2 x

theorem continuous_yoshidaEndpointEvenLowProfile (c b : ℝ) :
    Continuous (yoshidaEndpointEvenLowProfile c b) := by
  unfold yoshidaEndpointEvenLowProfile centeredEvenP2
  fun_prop

theorem yoshidaEndpointEvenLowProfile_even (c b : ℝ) :
    Function.Even (yoshidaEndpointEvenLowProfile c b) := by
  intro x
  unfold yoshidaEndpointEvenLowProfile centeredEvenP2
  ring

/-- Exact centered mass of the fixed low profile. -/
theorem integral_yoshidaEndpointEvenLowProfile_sq (c b : ℝ) :
    (∫ x : ℝ in -1..1, yoshidaEndpointEvenLowProfile c b x ^ 2) =
      2 * c ^ 2 + (2 / 5 : ℝ) * b ^ 2 := by
  have hP2 : (∫ x : ℝ in -1..1, centeredEvenP2 x) = 0 := by
    simpa only [centeredEvenP0, one_mul] using
      integral_centeredEvenP0_mul_p2
  have hP2Int : IntervalIntegrable centeredEvenP2 volume (-1) 1 :=
    Continuous.intervalIntegrable (by
      unfold centeredEvenP2
      fun_prop) (-1) 1
  have hP2SqInt : IntervalIntegrable (fun x ↦ centeredEvenP2 x ^ 2)
      volume (-1) 1 := Continuous.intervalIntegrable (by
        unfold centeredEvenP2
        fun_prop) (-1) 1
  rw [show (fun x : ℝ ↦ yoshidaEndpointEvenLowProfile c b x ^ 2) =
      fun x ↦ c ^ 2 +
        ((2 * c * b) * centeredEvenP2 x + b ^ 2 * centeredEvenP2 x ^ 2) by
    funext x
    unfold yoshidaEndpointEvenLowProfile
    ring]
  rw [intervalIntegral.integral_add
      (Continuous.intervalIntegrable continuous_const (-1) 1)
      ((hP2Int.const_mul (2 * c * b)).add
        (hP2SqInt.const_mul (b ^ 2))),
    intervalIntegral.integral_add
      (hP2Int.const_mul (2 * c * b)) (hP2SqInt.const_mul (b ^ 2)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  rw [hP2, integral_centeredEvenP2_sq]
  norm_num
  ring

/-- Constants disappear from the logarithmic difference form, leaving the
exact degree-two eigenvalue. -/
theorem centeredRawLogEnergy_yoshidaEndpointEvenLowProfile (c b : ℝ) :
    centeredRawLogEnergy (yoshidaEndpointEvenLowProfile c b) =
      (12 / 5 : ℝ) * b ^ 2 := by
  have hpoint (x y : ℝ) :
      (yoshidaEndpointEvenLowProfile c b x -
          yoshidaEndpointEvenLowProfile c b y) ^ 2 / |x - y| =
        b ^ 2 *
          ((centeredEvenP2 x - centeredEvenP2 y) ^ 2 / |x - y|) := by
    unfold yoshidaEndpointEvenLowProfile
    ring
  unfold centeredRawLogEnergy
  simp_rw [hpoint]
  rw [show (fun x : ℝ ↦ ∫ y : ℝ in -1..1,
      b ^ 2 * ((centeredEvenP2 x - centeredEvenP2 y) ^ 2 / |x - y|)) =
      fun x ↦ b ^ 2 * ∫ y : ℝ in -1..1,
        (centeredEvenP2 x - centeredEvenP2 y) ^ 2 / |x - y| by
    funext x
    rw [intervalIntegral.integral_const_mul],
    intervalIntegral.integral_const_mul]
  change b ^ 2 * centeredRawLogEnergy centeredEvenP2 =
    (12 / 5 : ℝ) * b ^ 2
  rw [centeredRawLogEnergy_centeredEvenP2]
  ring

/-- Exact endpoint-potential Gram form on `{P₀,P₂}`. -/
theorem integral_endpointPotential_mul_yoshidaEndpointEvenLowProfile_sq
    (c b : ℝ) :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x *
        yoshidaEndpointEvenLowProfile c b x ^ 2) =
      (2 - 2 * Real.log 2) * c ^ 2 +
        (2 / 3 : ℝ) * c * b +
        (41 / 75 - (2 / 5 : ℝ) * Real.log 2) * b ^ 2 := by
  let P : ℝ → ℝ := centeredEvenP2
  have hPcont : Continuous P := by
    dsimp only [P]
    unfold centeredEvenP2
    fun_prop
  have hV : IntervalIntegrable yoshidaEndpointPotential volume (-1) 1 := by
    simpa only [one_pow, mul_one] using
      intervalIntegrable_endpointPotential_mul_sq
        (fun _ : ℝ ↦ 1) continuous_const
  have hVPsq : IntervalIntegrable
      (fun x ↦ yoshidaEndpointPotential x * P x ^ 2) volume (-1) 1 :=
    intervalIntegrable_endpointPotential_mul_sq P hPcont
  have hVplus : IntervalIntegrable
      (fun x ↦ yoshidaEndpointPotential x * (P x + 1) ^ 2) volume (-1) 1 :=
    intervalIntegrable_endpointPotential_mul_sq
      (fun x ↦ P x + 1) (hPcont.add continuous_const)
  have hVP : IntervalIntegrable
      (fun x ↦ yoshidaEndpointPotential x * P x) volume (-1) 1 := by
    have hcomb := ((hVplus.sub hVPsq).sub hV).const_mul (1 / 2 : ℝ)
    apply hcomb.congr
    intro x _hx
    ring
  rw [show (fun x : ℝ ↦ yoshidaEndpointPotential x *
      yoshidaEndpointEvenLowProfile c b x ^ 2) =
      fun x ↦ c ^ 2 * yoshidaEndpointPotential x +
        ((2 * c * b) * (yoshidaEndpointPotential x * P x) +
          b ^ 2 * (yoshidaEndpointPotential x * P x ^ 2)) by
    funext x
    dsimp only [P]
    unfold yoshidaEndpointEvenLowProfile
    ring]
  rw [intervalIntegral.integral_add (hV.const_mul (c ^ 2))
      ((hVP.const_mul (2 * c * b)).add (hVPsq.const_mul (b ^ 2))),
    intervalIntegral.integral_add (hVP.const_mul (2 * c * b))
      (hVPsq.const_mul (b ^ 2)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  dsimp only [P]
  rw [integral_endpointPotential_one,
    integral_endpointPotential_mul_centeredEvenP2,
    integral_endpointPotential_mul_centeredEvenP2_sq]
  ring

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenLowProfile
