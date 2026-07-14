import ArithmeticHodge.Analysis.RationalInterval
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.RatInterval

open scoped BigOperators

/-! Width and magnitude estimates for exact rational intervals. -/

/-- Endpoint width of a rational interval. -/
def width (I : RatInterval) : ℚ := I.upper - I.lower

/-- A symmetric endpoint magnitude bound. -/
def AbsBound (I : RatInterval) (B : ℚ) : Prop :=
  -B ≤ I.lower ∧ I.upper ≤ B

theorem width_nonneg {I : RatInterval} (hI : I.Valid) :
    0 ≤ width I := by
  exact sub_nonneg.mpr hI

/-- Every real point enclosed by an interval is within its rational
half-width of the rational midpoint. -/
theorem abs_sub_center_le_halfWidth
    {I : RatInterval} {x : ℝ} (hx : I.Contains x) :
    |x - ((((I.lower + I.upper) / 2 : ℚ) : ℝ))| ≤
      ((((I.upper - I.lower) / 2 : ℚ) : ℝ)) := by
  unfold Contains at hx
  rw [abs_le]
  norm_num at hx ⊢
  constructor <;> linarith [hx.1, hx.2]

theorem width_pure (q : ℚ) : width (pure q) = 0 := by
  change q - q = 0
  ring

theorem width_add (I J : RatInterval) :
    width (I + J) = width I + width J := by
  change
    (I.upper + J.upper) - (I.lower + J.lower) =
      (I.upper - I.lower) + (J.upper - J.lower)
  ring

theorem width_sub (I J : RatInterval) :
    width (I - J) = width I + width J := by
  change
    (I.upper - J.lower) - (I.lower - J.upper) =
      (I.upper - I.lower) + (J.upper - J.lower)
  ring

/-- Multiplication by a point interval scales width by the absolute value of
the point. -/
theorem width_pure_mul (q : ℚ) {I : RatInterval} (hI : I.Valid) :
    width (pure q * I) = |q| * width I := by
  by_cases hq : 0 ≤ q
  · have hprod : q * I.lower ≤ q * I.upper :=
      mul_le_mul_of_nonneg_left hI hq
    change
      max (max (q * I.lower) (q * I.upper))
            (max (q * I.lower) (q * I.upper)) -
          min (min (q * I.lower) (q * I.upper))
            (min (q * I.lower) (q * I.upper)) =
        |q| * (I.upper - I.lower)
    rw [max_self, min_self, max_eq_right hprod, min_eq_left hprod,
      abs_of_nonneg hq]
    ring
  · have hq' : q ≤ 0 := le_of_not_ge hq
    have hprod : q * I.upper ≤ q * I.lower :=
      mul_le_mul_of_nonpos_left hI hq'
    change
      max (max (q * I.lower) (q * I.upper))
            (max (q * I.lower) (q * I.upper)) -
          min (min (q * I.lower) (q * I.upper))
            (min (q * I.lower) (q * I.upper)) =
        |q| * (I.upper - I.lower)
    rw [max_self, min_self, max_eq_left hprod, min_eq_right hprod,
      abs_of_nonpos hq']
    ring

/-- Right multiplication by a point interval has the same exact width
formula. -/
theorem width_mul_pure (q : ℚ) {I : RatInterval} (hI : I.Valid) :
    width (I * pure q) = |q| * width I := by
  by_cases hq : 0 ≤ q
  · have hprod : I.lower * q ≤ I.upper * q :=
      mul_le_mul_of_nonneg_right hI hq
    change
      max (max (I.lower * q) (I.lower * q))
            (max (I.upper * q) (I.upper * q)) -
          min (min (I.lower * q) (I.lower * q))
            (min (I.upper * q) (I.upper * q)) =
        |q| * (I.upper - I.lower)
    simp only [max_self, min_self]
    rw [max_eq_right hprod, min_eq_left hprod, abs_of_nonneg hq]
    ring
  · have hq' : q ≤ 0 := le_of_not_ge hq
    have hprod : I.upper * q ≤ I.lower * q :=
      mul_le_mul_of_nonpos_right hI hq'
    change
      max (max (I.lower * q) (I.lower * q))
            (max (I.upper * q) (I.upper * q)) -
          min (min (I.lower * q) (I.lower * q))
            (min (I.upper * q) (I.upper * q)) =
        |q| * (I.upper - I.lower)
    simp only [max_self, min_self]
    rw [max_eq_left hprod, min_eq_right hprod, abs_of_nonpos hq']
    ring

theorem valid_pure (q : ℚ) : (pure q).Valid := by
  exact le_rfl

theorem valid_add {I J : RatInterval} (hI : I.Valid) (hJ : J.Valid) :
    (I + J).Valid := by
  change I.lower + J.lower ≤ I.upper + J.upper
  exact add_le_add hI hJ

theorem valid_sub {I J : RatInterval} (hI : I.Valid) (hJ : J.Valid) :
    (I - J).Valid := by
  change I.lower - J.upper ≤ I.upper - J.lower
  exact sub_le_sub hI hJ

theorem valid_mul {I J : RatInterval} (_hI : I.Valid) (_hJ : J.Valid) :
    (I * J).Valid := by
  change
    min (min (I.lower * J.lower) (I.lower * J.upper))
        (min (I.upper * J.lower) (I.upper * J.upper)) ≤
      max (max (I.lower * J.lower) (I.lower * J.upper))
        (max (I.upper * J.lower) (I.upper * J.upper))
  exact (min_le_left _ _).trans ((min_le_left _ _).trans
    ((le_max_left _ _).trans (le_max_left _ _)))

/-- The lower endpoint of a product is nonnegative when both input intervals
have nonnegative lower endpoints. -/
theorem mul_lower_nonneg_of_nonneg
    {I J : RatInterval} (hIlower : 0 ≤ I.lower) (hJlower : 0 ≤ J.lower)
    (hI : I.Valid) (hJ : J.Valid) : 0 ≤ (I * J).lower := by
  have hIupper : 0 ≤ I.upper := hIlower.trans hI
  have hJupper : 0 ≤ J.upper := hJlower.trans hJ
  change 0 ≤ min (min (I.lower * J.lower) (I.lower * J.upper))
    (min (I.upper * J.lower) (I.upper * J.upper))
  simp only [le_min_iff]
  exact ⟨⟨mul_nonneg hIlower hJlower, mul_nonneg hIlower hJupper⟩,
    ⟨mul_nonneg hIupper hJlower, mul_nonneg hIupper hJupper⟩⟩

/-- The lower endpoint of a product is positive when both input intervals
have positive lower endpoints. -/
theorem mul_lower_pos_of_pos
    {I J : RatInterval} (hIlower : 0 < I.lower) (hJlower : 0 < J.lower)
    (hI : I.Valid) (hJ : J.Valid) : 0 < (I * J).lower := by
  have hIupper : 0 < I.upper := hIlower.trans_le hI
  have hJupper : 0 < J.upper := hJlower.trans_le hJ
  change 0 < min (min (I.lower * J.lower) (I.lower * J.upper))
    (min (I.upper * J.lower) (I.upper * J.upper))
  simp only [lt_min_iff]
  exact ⟨⟨mul_pos hIlower hJlower, mul_pos hIlower hJupper⟩,
    ⟨mul_pos hIupper hJlower, mul_pos hIupper hJupper⟩⟩

theorem absBound_pure {q B : ℚ} (hq : |q| ≤ B) :
    (pure q).AbsBound B := by
  rw [abs_le] at hq
  exact hq

theorem absBound_add
    {I J : RatInterval} {BI BJ : ℚ}
    (hI : I.AbsBound BI) (hJ : J.AbsBound BJ) :
    (I + J).AbsBound (BI + BJ) := by
  unfold AbsBound at hI hJ ⊢
  constructor
  · change -(BI + BJ) ≤ I.lower + J.lower
    linarith [hI.1, hJ.1]
  · change I.upper + J.upper ≤ BI + BJ
    linarith [hI.2, hJ.2]

theorem absBound_sub
    {I J : RatInterval} {BI BJ : ℚ}
    (hI : I.AbsBound BI) (hJ : J.AbsBound BJ) :
    (I - J).AbsBound (BI + BJ) := by
  unfold AbsBound at hI hJ ⊢
  constructor
  · change -(BI + BJ) ≤ I.lower - J.upper
    linarith [hI.1, hJ.2]
  · change I.upper - J.lower ≤ BI + BJ
    linarith [hI.2, hJ.1]

private theorem endpoint_abs_le_of_absBound
    {I : RatInterval} {B : ℚ} (hI : I.Valid) (hB : I.AbsBound B) :
    |I.lower| ≤ B ∧ |I.upper| ≤ B := by
  rw [abs_le, abs_le]
  exact ⟨⟨hB.1, hI.trans hB.2⟩, ⟨hB.1.trans hI, hB.2⟩⟩

private theorem center_abs_le_of_absBound
    {I : RatInterval} {B : ℚ} (hI : I.Valid) (hB : I.AbsBound B) :
    |(I.lower + I.upper) / 2| ≤ B := by
  unfold Valid at hI
  unfold AbsBound at hB
  rw [abs_le]
  constructor <;> linarith [hB.1, hB.2, hI]

theorem absBound_mul
    {I J : RatInterval} {BI BJ : ℚ}
    (hI : I.Valid) (hJ : J.Valid)
    (hBI : I.AbsBound BI) (hBJ : J.AbsBound BJ)
    (hBI0 : 0 ≤ BI) (_hBJ0 : 0 ≤ BJ) :
    (I * J).AbsBound (BI * BJ) := by
  have hIends := endpoint_abs_le_of_absBound hI hBI
  have hJends := endpoint_abs_le_of_absBound hJ hBJ
  have corner_abs (x y : ℚ) (hx : |x| ≤ BI) (hy : |y| ≤ BJ) :
      |x * y| ≤ BI * BJ := by
    rw [abs_mul]
    gcongr
  have hll := corner_abs I.lower J.lower hIends.1 hJends.1
  have hlu := corner_abs I.lower J.upper hIends.1 hJends.2
  have hul := corner_abs I.upper J.lower hIends.2 hJends.1
  have huu := corner_abs I.upper J.upper hIends.2 hJends.2
  rw [abs_le] at hll hlu hul huu
  constructor
  · change
      -(BI * BJ) ≤
        min (min (I.lower * J.lower) (I.lower * J.upper))
          (min (I.upper * J.lower) (I.upper * J.upper))
    exact le_min (le_min hll.1 hlu.1) (le_min hul.1 huu.1)
  · change
      max (max (I.lower * J.lower) (I.lower * J.upper))
          (max (I.upper * J.lower) (I.upper * J.upper)) ≤ BI * BJ
    exact max_le (max_le hll.2 hlu.2) (max_le hul.2 huu.2)

private theorem lower_sub_center_abs
    {I : RatInterval} (hI : I.Valid) :
    |I.lower - (I.lower + I.upper) / 2| = width I / 2 := by
  unfold Valid at hI
  rw [abs_of_nonpos]
  · unfold width
    ring
  · linarith [hI]

private theorem upper_sub_center_abs
    {I : RatInterval} (hI : I.Valid) :
    |I.upper - (I.lower + I.upper) / 2| = width I / 2 := by
  unfold Valid at hI
  rw [abs_of_nonneg]
  · unfold width
    ring
  · linarith [hI]

/-- Multiplication is Lipschitz in interval width under symmetric endpoint
magnitude bounds.  This estimate avoids unfolding the four-corner hull in
downstream certificate proofs. -/
theorem width_mul_le
    {I J : RatInterval} {BI BJ : ℚ}
    (hI : I.Valid) (hJ : J.Valid)
    (hBI : I.AbsBound BI) (hBJ : J.AbsBound BJ)
    (hBI0 : 0 ≤ BI) (hBJ0 : 0 ≤ BJ) :
    width (I * J) ≤ BJ * width I + BI * width J := by
  let cI : ℚ := (I.lower + I.upper) / 2
  let cJ : ℚ := (J.lower + J.upper) / 2
  let rI : ℚ := width I / 2
  let rJ : ℚ := width J / 2
  let R : ℚ := rI * BJ + BI * rJ
  have hrI : 0 ≤ rI := by
    dsimp only [rI]
    exact div_nonneg (width_nonneg hI) (by norm_num)
  have hrJ : 0 ≤ rJ := by
    dsimp only [rJ]
    exact div_nonneg (width_nonneg hJ) (by norm_num)
  have hR : 0 ≤ R := by
    dsimp only [R]
    positivity
  have hIends := endpoint_abs_le_of_absBound hI hBI
  have hJends := endpoint_abs_le_of_absBound hJ hBJ
  have hcI : |cI| ≤ BI := by
    simpa only [cI] using center_abs_le_of_absBound hI hBI
  have hIl : |I.lower - cI| = rI := by
    simpa only [cI, rI] using lower_sub_center_abs hI
  have hIu : |I.upper - cI| = rI := by
    simpa only [cI, rI] using upper_sub_center_abs hI
  have hJl : |J.lower - cJ| = rJ := by
    simpa only [cJ, rJ] using lower_sub_center_abs hJ
  have hJu : |J.upper - cJ| = rJ := by
    simpa only [cJ, rJ] using upper_sub_center_abs hJ
  have corner_abs (x y : ℚ)
      (hx : |x - cI| ≤ rI) (hy : |y| ≤ BJ)
      (hyc : |y - cJ| ≤ rJ) :
      |x * y - cI * cJ| ≤ R := by
    calc
      |x * y - cI * cJ| =
          |(x - cI) * y + cI * (y - cJ)| := by
        congr 1
        ring
      _ ≤ |(x - cI) * y| + |cI * (y - cJ)| := abs_add_le _ _
      _ = |x - cI| * |y| + |cI| * |y - cJ| := by
        rw [abs_mul, abs_mul]
      _ ≤ rI * BJ + BI * rJ := by gcongr
      _ = R := by rfl
  have hll := corner_abs I.lower J.lower hIl.le hJends.1 hJl.le
  have hlu := corner_abs I.lower J.upper hIl.le hJends.2 hJu.le
  have hul := corner_abs I.upper J.lower hIu.le hJends.1 hJl.le
  have huu := corner_abs I.upper J.upper hIu.le hJends.2 hJu.le
  rw [abs_le] at hll hlu hul huu
  have hlower :
      cI * cJ - R ≤
        min (min (I.lower * J.lower) (I.lower * J.upper))
          (min (I.upper * J.lower) (I.upper * J.upper)) := by
    apply le_min
    · exact le_min (by linarith [hll.1]) (by linarith [hlu.1])
    · exact le_min (by linarith [hul.1]) (by linarith [huu.1])
  have hupper :
      max (max (I.lower * J.lower) (I.lower * J.upper))
          (max (I.upper * J.lower) (I.upper * J.upper)) ≤
        cI * cJ + R := by
    apply max_le
    · exact max_le (by linarith [hll.2]) (by linarith [hlu.2])
    · exact max_le (by linarith [hul.2]) (by linarith [huu.2])
  change
    max (max (I.lower * J.lower) (I.lower * J.upper))
          (max (I.upper * J.lower) (I.upper * J.upper)) -
        min (min (I.lower * J.lower) (I.lower * J.upper))
          (min (I.upper * J.lower) (I.upper * J.upper)) ≤
      BJ * width I + BI * width J
  have htwoR : 2 * R = BJ * width I + BI * width J := by
    dsimp only [R, rI, rJ]
    ring
  rw [← htwoR]
  linarith

/-! ## Positive reciprocals and quotients -/

/-- Inversion preserves validity when the interval is strictly positive. -/
theorem valid_inv_of_pos {I : RatInterval} (hI : I.Valid)
    (hlower : 0 < I.lower) : I⁻¹.Valid := by
  have hupper : 0 < I.upper := hlower.trans_le hI
  change I.upper⁻¹ ≤ I.lower⁻¹
  exact (inv_le_inv₀ hupper hlower).2 hI

/-- The reciprocal of a positive interval has the sharp symmetric magnitude
bound given by the reciprocal of its lower endpoint. -/
theorem absBound_inv_of_pos {I : RatInterval} (hI : I.Valid)
    (hlower : 0 < I.lower) : I⁻¹.AbsBound I.lower⁻¹ := by
  have hupper : 0 < I.upper := hlower.trans_le hI
  constructor
  · change -I.lower⁻¹ ≤ I.upper⁻¹
    exact (neg_nonpos.mpr (inv_nonneg.mpr hlower.le)).trans
      (inv_nonneg.mpr hupper.le)
  · exact le_rfl

/-- A certified positive lower bound `m` gives the endpoint-independent
reciprocal magnitude bound `m⁻¹`. -/
theorem absBound_inv_of_lower {I : RatInterval} {m : ℚ}
    (hI : I.Valid) (hm : 0 < m) (hmlower : m ≤ I.lower) :
    I⁻¹.AbsBound m⁻¹ := by
  have hlower : 0 < I.lower := hm.trans_le hmlower
  have hupper : 0 < I.upper := hlower.trans_le hI
  constructor
  · change -m⁻¹ ≤ I.upper⁻¹
    exact (neg_nonpos.mpr (inv_nonneg.mpr hm.le)).trans
      (inv_nonneg.mpr hupper.le)
  · change I.lower⁻¹ ≤ m⁻¹
    exact (inv_le_inv₀ hlower hm).2 hmlower

/-- Exact width formula for the reciprocal of a positive interval. -/
theorem width_inv_eq_of_pos {I : RatInterval} (hI : I.Valid)
    (hlower : 0 < I.lower) :
    width I⁻¹ = width I / (I.lower * I.upper) := by
  have hupper : 0 < I.upper := hlower.trans_le hI
  change I.lower⁻¹ - I.upper⁻¹ =
    (I.upper - I.lower) / (I.lower * I.upper)
  exact inv_sub_inv hlower.ne' hupper.ne'

/-- If `m` is a certified positive lower bound for an interval, reciprocal
width grows by at most the Lipschitz factor `m⁻²`. -/
theorem width_inv_le_of_lower {I : RatInterval} {m : ℚ}
    (hI : I.Valid) (hm : 0 < m) (hmlower : m ≤ I.lower) :
    width I⁻¹ ≤ width I / (m * m) := by
  rw [width_inv_eq_of_pos hI (hm.trans_le hmlower)]
  have hmupper : m ≤ I.upper := hmlower.trans hI
  have hdenom : m * m ≤ I.lower * I.upper :=
    mul_le_mul hmlower hmupper hm.le (hm.le.trans hmlower)
  exact div_le_div₀ (width_nonneg hI) le_rfl (mul_pos hm hm) hdenom

/-- Division by a strictly positive valid interval preserves validity. -/
theorem valid_div_of_pos {I J : RatInterval} (hI : I.Valid) (hJ : J.Valid)
    (hJlower : 0 < J.lower) : (I / J).Valid := by
  change (I * J⁻¹).Valid
  exact valid_mul hI (valid_inv_of_pos hJ hJlower)

/-- A positive denominator turns a numerator magnitude bound `B` into the
sharp quotient magnitude bound `B / J.lower`. -/
theorem absBound_div_of_pos
    {I J : RatInterval} {B : ℚ}
    (hI : I.Valid) (hJ : J.Valid) (hBI : I.AbsBound B)
    (hB : 0 ≤ B) (hJlower : 0 < J.lower) :
    (I / J).AbsBound (B * J.lower⁻¹) := by
  change (I * J⁻¹).AbsBound (B * J.lower⁻¹)
  exact absBound_mul hI (valid_inv_of_pos hJ hJlower) hBI
    (absBound_inv_of_pos hJ hJlower) hB (inv_nonneg.mpr hJlower.le)

/-- Quotient magnitude bound using any certified positive denominator floor
`m`. -/
theorem absBound_div_of_lower
    {I J : RatInterval} {B m : ℚ}
    (hI : I.Valid) (hJ : J.Valid) (hBI : I.AbsBound B)
    (hB : 0 ≤ B) (hm : 0 < m) (hmlower : m ≤ J.lower) :
    (I / J).AbsBound (B * m⁻¹) := by
  have hJlower : 0 < J.lower := hm.trans_le hmlower
  change (I * J⁻¹).AbsBound (B * m⁻¹)
  exact absBound_mul hI (valid_inv_of_pos hJ hJlower) hBI
    (absBound_inv_of_lower hJ hm hmlower) hB (inv_nonneg.mpr hm.le)

/-- Sharp structural quotient-width estimate using the actual positive
denominator endpoints. -/
theorem width_div_le
    {I J : RatInterval} {B : ℚ}
    (hI : I.Valid) (hJ : J.Valid) (hBI : I.AbsBound B)
    (hB : 0 ≤ B) (hJlower : 0 < J.lower) :
    width (I / J) ≤
      J.lower⁻¹ * width I +
        B * (width J / (J.lower * J.upper)) := by
  change width (I * J⁻¹) ≤ _
  calc
    width (I * J⁻¹) ≤
        J.lower⁻¹ * width I + B * width J⁻¹ :=
      width_mul_le hI (valid_inv_of_pos hJ hJlower) hBI
        (absBound_inv_of_pos hJ hJlower) hB
        (inv_nonneg.mpr hJlower.le)
    _ = J.lower⁻¹ * width I +
        B * (width J / (J.lower * J.upper)) := by
      rw [width_inv_eq_of_pos hJ hJlower]

/-- Quotient-width estimate using any certified positive denominator floor
`m`.  This avoids exposing the denominator's upper endpoint downstream. -/
theorem width_div_le_of_lower
    {I J : RatInterval} {B m : ℚ}
    (hI : I.Valid) (hJ : J.Valid) (hBI : I.AbsBound B)
    (hB : 0 ≤ B) (hm : 0 < m) (hmlower : m ≤ J.lower) :
    width (I / J) ≤
      m⁻¹ * width I + B * (width J / (m * m)) := by
  have hJlower : 0 < J.lower := hm.trans_le hmlower
  change width (I * J⁻¹) ≤ _
  calc
    width (I * J⁻¹) ≤
        m⁻¹ * width I + B * width J⁻¹ :=
      width_mul_le hI (valid_inv_of_pos hJ hJlower) hBI
        (absBound_inv_of_lower hJ hm hmlower) hB (inv_nonneg.mpr hm.le)
    _ ≤ m⁻¹ * width I + B * (width J / (m * m)) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (width_inv_le_of_lower hJ hm hmlower) hB)

/-! ## Outward rounding -/

/-- Round both endpoints outward to the grid with spacing `scale⁻¹`. -/
def outwardRoundedInterval (scale : ℚ) (I : RatInterval) : RatInterval :=
  ⟨((I.lower * scale).floor : ℚ) / scale,
    ((I.upper * scale).ceil : ℚ) / scale⟩

theorem outwardRoundedInterval_lower_le
    {scale : ℚ} (hscale : 0 < scale) (I : RatInterval) :
    (outwardRoundedInterval scale I).lower ≤ I.lower := by
  change ((I.lower * scale).floor : ℚ) / scale ≤ I.lower
  exact (div_le_iff₀ hscale).2 (Rat.floor_le (I.lower * scale))

theorem outwardRoundedInterval_le_upper
    {scale : ℚ} (hscale : 0 < scale) (I : RatInterval) :
    I.upper ≤ (outwardRoundedInterval scale I).upper := by
  change I.upper ≤ ((I.upper * scale).ceil : ℚ) / scale
  exact (le_div_iff₀ hscale).2 Rat.le_ceil

private theorem outwardRoundedInterval_lower_error_le
    {scale : ℚ} (hscale : 0 < scale) (I : RatInterval) :
    I.lower - 1 / scale ≤ (outwardRoundedInterval scale I).lower := by
  change I.lower - 1 / scale ≤
    ((I.lower * scale).floor : ℚ) / scale
  rw [le_div_iff₀ hscale]
  calc
    (I.lower - 1 / scale) * scale = I.lower * scale - 1 := by
      field_simp [hscale.ne']
    _ ≤ ((I.lower * scale).floor : ℚ) := by
      exact (Int.sub_one_lt_floor (I.lower * scale)).le

private theorem outwardRoundedInterval_upper_error_le
    {scale : ℚ} (hscale : 0 < scale) (I : RatInterval) :
    (outwardRoundedInterval scale I).upper ≤ I.upper + 1 / scale := by
  change ((I.upper * scale).ceil : ℚ) / scale ≤
    I.upper + 1 / scale
  rw [div_le_iff₀ hscale]
  calc
    ((I.upper * scale).ceil : ℚ) ≤ I.upper * scale + 1 := by
      exact (Rat.ceil_lt (x := I.upper * scale)).le
    _ = (I.upper + 1 / scale) * scale := by
      field_simp [hscale.ne']

/-- Endpoint error bounds compose directly into a width error bound. -/
theorem width_le_add_of_endpoint_errors
    {I J : RatInterval} {lowerError upperError : ℚ}
    (hlower : I.lower - lowerError ≤ J.lower)
    (hupper : J.upper ≤ I.upper + upperError) :
    width J ≤ width I + lowerError + upperError := by
  unfold width
  linarith

/-- Outward rounding preserves validity. -/
theorem valid_outwardRoundedInterval
    {scale : ℚ} (hscale : 0 < scale) {I : RatInterval} (hI : I.Valid) :
    (outwardRoundedInterval scale I).Valid := by
  exact (outwardRoundedInterval_lower_le hscale I).trans
    (hI.trans (outwardRoundedInterval_le_upper hscale I))

/-- Outward rounding adds at most one grid cell at each endpoint. -/
theorem width_outwardRoundedInterval_le
    {scale : ℚ} (hscale : 0 < scale) (I : RatInterval) :
    width (outwardRoundedInterval scale I) ≤ width I + 2 / scale := by
  have hlower := outwardRoundedInterval_lower_error_le hscale I
  have hupper := outwardRoundedInterval_upper_error_le hscale I
  calc
    width (outwardRoundedInterval scale I) ≤
        width I + 1 / scale + 1 / scale :=
      width_le_add_of_endpoint_errors hlower hupper
    _ = width I + 2 / scale := by ring

/-! ## Widths of recursively accumulated interval sums -/

/-- Any interval recursion built from `pure 0` and right addition has width
equal to the sum of its term widths. -/
theorem width_recursive_add_eq_sum
    (head term : ℕ → RatInterval)
    (hzero : head 0 = pure 0)
    (hsucc : ∀ n, head (n + 1) = head n + term n)
    (n : ℕ) :
    width (head n) = ∑ i ∈ Finset.range n, width (term i) := by
  induction n with
  | zero =>
      rw [hzero, width_pure]
      simp
  | succ n ih =>
      rw [hsucc, width_add, ih, Finset.sum_range_succ]

/-- Pointwise term-width estimates sum through an additive interval
recursion. -/
theorem width_recursive_add_le_sum
    (head term : ℕ → RatInterval)
    (hzero : head 0 = pure 0)
    (hsucc : ∀ n, head (n + 1) = head n + term n)
    {bound : ℕ → ℚ} (n : ℕ)
    (hterm : ∀ i, i < n → width (term i) ≤ bound i) :
    width (head n) ≤ ∑ i ∈ Finset.range n, bound i := by
  rw [width_recursive_add_eq_sum head term hzero hsucc n]
  exact Finset.sum_le_sum fun i hi ↦ hterm i (Finset.mem_range.mp hi)

/-- A uniform term-width estimate accumulates linearly in the recursion
length. -/
theorem width_recursive_add_le_const_mul
    (head term : ℕ → RatInterval)
    (hzero : head 0 = pure 0)
    (hsucc : ∀ n, head (n + 1) = head n + term n)
    {W : ℚ} (n : ℕ)
    (hterm : ∀ i, i < n → width (term i) ≤ W) :
    width (head n) ≤ (n : ℚ) * W := by
  simpa using width_recursive_add_le_sum head term hzero hsucc n hterm

end ArithmeticHodge.Analysis.RatInterval
