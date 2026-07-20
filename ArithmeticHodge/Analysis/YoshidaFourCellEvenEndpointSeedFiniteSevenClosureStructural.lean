import ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedUniversalClosureStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedFiniteSevenClosureStructural

noncomputable section

open ShiftedLegendreLogEnergyOrthogonalProjection
open ShiftedLegendreOrthogonality
open YoshidaFourCellEvenEndpointCoshSchurStructural
open YoshidaFourCellEvenPolarSchurStructural
open YoshidaFourCellParityHalfFoldStructural
open YoshidaFourCellParityOperatorStructural

/-!
# The finite seven-coordinate endpoint border

After quotienting the `P₀,P₂,…,P₁₂` block by its single wide-cosh
coordinate, the endpoint-row Schur complement is a six-dimensional
symmetric form.  This file records a rational congruence certificate for a
candidate center matrix for that form.  The certificate is an exact `LDLᵀ`
identity over `ℚ`; it contains no modal search or sampled positivity check.

The deliberately separate box theorem below is the analytic handoff: once
the twenty-one true quotient entries are proved to lie in their displayed
rational boxes, the endpoint border is nonnegative.  This file does not
assert those analytic enclosures.  It closes the finite-dimensional algebra
conditional on exactly those explicit proof obligations.
-/

/-- Rational center of the six-coordinate cosh-quotient bordered form.
The coordinate order is the image of `P₂,P₄,P₆,P₈,P₁₀,P₁₂` after solving
the positive-cosh equation for `P₀`. -/
def fourCellEvenFiniteSevenBorderCenter
    (x₂ x₄ x₆ x₈ x₁₀ x₁₂ : ℝ) : ℝ :=
  (2111977675374 / 1000000000000000 : ℝ) * x₂ ^ 2 +
    2 * (1890449921460 / 1000000000000000 : ℝ) * x₂ * x₄ +
    2 * (1052053921205 / 1000000000000000 : ℝ) * x₂ * x₆ +
    2 * (77967838024 / 1000000000000000 : ℝ) * x₂ * x₈ +
    2 * (143965754572 / 1000000000000000 : ℝ) * x₂ * x₁₀ +
    2 * (368171241285 / 1000000000000000 : ℝ) * x₂ * x₁₂ +
    (1728212144335 / 1000000000000000 : ℝ) * x₄ ^ 2 +
    2 * (1217630782157 / 1000000000000000 : ℝ) * x₄ * x₆ +
    2 * (213431716983 / 1000000000000000 : ℝ) * x₄ * x₈ +
    2 * (184254796445 / 1000000000000000 : ℝ) * x₄ * x₁₀ +
    2 * (346732076476 / 1000000000000000 : ℝ) * x₄ * x₁₂ +
    (2723234397896 / 1000000000000000 : ℝ) * x₆ ^ 2 +
    2 * (742541479585 / 1000000000000000 : ℝ) * x₆ * x₈ +
    2 * (598571709567 / 1000000000000000 : ℝ) * x₆ * x₁₀ +
    2 * (302011253841 / 1000000000000000 : ℝ) * x₆ * x₁₂ +
    (2950453847668 / 1000000000000000 : ℝ) * x₈ ^ 2 +
    2 * (855847573644 / 1000000000000000 : ℝ) * x₈ * x₁₀ +
    2 * (227312970022 / 1000000000000000 : ℝ) * x₈ * x₁₂ +
    (2455103917679 / 1000000000000000 : ℝ) * x₁₀ ^ 2 +
    2 * (402562607163 / 1000000000000000 : ℝ) * x₁₀ * x₁₂ +
    (2235373831399 / 1000000000000000 : ℝ) * x₁₂ ^ 2

private def d₀ : ℝ :=
  1055983837687 / 500000000000000

private def d₁ : ℝ :=
  7610615979943180457469 / 211196767537400000000000000

private def d₂ : ℝ :=
  6577122390944146981631741462398339 /
    76106159799431804574690000000000000000

private def d₃ : ℝ :=
  735318966977516478956269309340263325931920963 /
    1315424478188829396326348292479667800000000000000

private def d₄ : ℝ :=
  259285819298316985634746073700097311789232686177798407621 /
    3676594834887582394781346546701316629659604815000000000000000

private def d₅ : ℝ :=
  414256396954949114352286325803946568864211281292204112707483366877707 /
    259285819298316985634746073700097311789232686177798407621000000000000000

private def l₁₀ : ℝ := 945224960730 / 1055983837687
private def l₂₀ : ℝ := 45741474835 / 91824681538
private def l₂₁ : ℝ :=
  291370799871133704471209 / 38053079899715902287345
private def l₃₀ : ℝ := 38983919012 / 1055983837687
private def l₃₁ : ℝ :=
  50561098983131864180267 / 12684359966571967429115
private def l₃₂ : ℝ :=
  -30149879132840827058191662720898164 /
    6577122390944146981631741462398339
private def l₄₀ : ℝ := 71982877286 / 1055983837687
private def l₄₁ : ℝ :=
  11698012470088917333031 / 7610615979943180457469
private def l₄₂ : ℝ :=
  7819471589274491059046251844776960 /
    6577122390944146981631741462398339
private def l₄₃ : ℝ :=
  7239644683960450211018444167111204324072750981 /
    3676594834887582394781346546701316629659604815
private def l₅₀ : ℝ := 368171241285 / 2111967675374
private def l₅₁ : ℝ :=
  18138821680779375212962 / 38053079899715902287345
private def l₅₂ : ℝ :=
  -982849372115929242310359135449353 /
    6577122390944146981631741462398339
private def l₅₃ : ℝ :=
  113194768554484298261554618898459521889105618 /
    735318966977516478956269309340263325931920963
private def l₅₄ : ℝ :=
  724180648642859662528056617546971092585938941673101110395 /
    259285819298316985634746073700097311789232686177798407621

/-- Exact rational `LDLᵀ` sum of squares for the center after removing
`10⁻⁸` times the Euclidean diagonal. -/
private def fourCellEvenFiniteSevenBorderSOS
    (x₂ x₄ x₆ x₈ x₁₀ x₁₂ : ℝ) : ℝ :=
  d₀ * (x₂ + l₁₀ * x₄ + l₂₀ * x₆ + l₃₀ * x₈ +
      l₄₀ * x₁₀ + l₅₀ * x₁₂) ^ 2 +
    d₁ * (x₄ + l₂₁ * x₆ + l₃₁ * x₈ + l₄₁ * x₁₀ +
      l₅₁ * x₁₂) ^ 2 +
    d₂ * (x₆ + l₃₂ * x₈ + l₄₂ * x₁₀ + l₅₂ * x₁₂) ^ 2 +
    d₃ * (x₈ + l₄₃ * x₁₀ + l₅₃ * x₁₂) ^ 2 +
    d₄ * (x₁₀ + l₅₄ * x₁₂) ^ 2 +
    d₅ * x₁₂ ^ 2

set_option maxHeartbeats 800000 in
private theorem finiteSevenBorderCenter_eq_diagonal_add_sos
    (x₂ x₄ x₆ x₈ x₁₀ x₁₂ : ℝ) :
    fourCellEvenFiniteSevenBorderCenter x₂ x₄ x₆ x₈ x₁₀ x₁₂ =
      (1 / 100000000 : ℝ) *
        (x₂ ^ 2 + x₄ ^ 2 + x₆ ^ 2 + x₈ ^ 2 + x₁₀ ^ 2 + x₁₂ ^ 2) +
      fourCellEvenFiniteSevenBorderSOS x₂ x₄ x₆ x₈ x₁₀ x₁₂ := by
  unfold fourCellEvenFiniteSevenBorderCenter
    fourCellEvenFiniteSevenBorderSOS
    d₀ d₁ d₂ d₃ d₄ d₅
    l₁₀ l₂₀ l₂₁ l₃₀ l₃₁ l₃₂ l₄₀ l₄₁ l₄₂ l₄₃
    l₅₀ l₅₁ l₅₂ l₅₃ l₅₄
  ring

/-- The rational center has a certified Euclidean margin of `10⁻⁸`.
This is the finite bordered Schur certificate itself. -/
theorem one_div_hundredMillion_sum_sq_le_finiteSevenBorderCenter
    (x₂ x₄ x₆ x₈ x₁₀ x₁₂ : ℝ) :
    (1 / 100000000 : ℝ) *
        (x₂ ^ 2 + x₄ ^ 2 + x₆ ^ 2 + x₈ ^ 2 + x₁₀ ^ 2 + x₁₂ ^ 2) ≤
      fourCellEvenFiniteSevenBorderCenter x₂ x₄ x₆ x₈ x₁₀ x₁₂ := by
  rw [finiteSevenBorderCenter_eq_diagonal_add_sos]
  have hd₀ : 0 ≤ d₀ := by norm_num [d₀]
  have hd₁ : 0 ≤ d₁ := by norm_num [d₁]
  have hd₂ : 0 ≤ d₂ := by norm_num [d₂]
  have hd₃ : 0 ≤ d₃ := by norm_num [d₃]
  have hd₄ : 0 ≤ d₄ := by norm_num [d₄]
  have hd₅ : 0 ≤ d₅ := by norm_num [d₅]
  have hsos : 0 ≤ fourCellEvenFiniteSevenBorderSOS
      x₂ x₄ x₆ x₈ x₁₀ x₁₂ := by
    unfold fourCellEvenFiniteSevenBorderSOS
    positivity
  linarith only [hsos]

/-! ## Robust analytic handoff -/

/-- Symmetric entrywise perturbation of the certified rational center. -/
def fourCellEvenFiniteSevenBorderPerturbation
    (e₂₂ e₂₄ e₂₆ e₂₈ e₂₁₀ e₂₁₂
      e₄₄ e₄₆ e₄₈ e₄₁₀ e₄₁₂
      e₆₆ e₆₈ e₆₁₀ e₆₁₂
      e₈₈ e₈₁₀ e₈₁₂ e₁₀₁₀ e₁₀₁₂ e₁₂₁₂ : ℝ)
    (x₂ x₄ x₆ x₈ x₁₀ x₁₂ : ℝ) : ℝ :=
  e₂₂ * x₂ ^ 2 + 2 * e₂₄ * x₂ * x₄ + 2 * e₂₆ * x₂ * x₆ +
    2 * e₂₈ * x₂ * x₈ + 2 * e₂₁₀ * x₂ * x₁₀ +
    2 * e₂₁₂ * x₂ * x₁₂ + e₄₄ * x₄ ^ 2 +
    2 * e₄₆ * x₄ * x₆ + 2 * e₄₈ * x₄ * x₈ +
    2 * e₄₁₀ * x₄ * x₁₀ + 2 * e₄₁₂ * x₄ * x₁₂ +
    e₆₆ * x₆ ^ 2 + 2 * e₆₈ * x₆ * x₈ +
    2 * e₆₁₀ * x₆ * x₁₀ + 2 * e₆₁₂ * x₆ * x₁₂ +
    e₈₈ * x₈ ^ 2 + 2 * e₈₁₀ * x₈ * x₁₀ +
    2 * e₈₁₂ * x₈ * x₁₂ + e₁₀₁₀ * x₁₀ ^ 2 +
    2 * e₁₀₁₂ * x₁₀ * x₁₂ + e₁₂₁₂ * x₁₂ ^ 2

/-- Every independent entry is allowed an absolute error of `10⁻⁹`.
This is small enough to preserve the certified `10⁻⁸` margin even after all
six diagonal and fifteen off-diagonal errors are charged simultaneously. -/
def fourCellEvenFiniteSevenBorderEntryBox
    (e₂₂ e₂₄ e₂₆ e₂₈ e₂₁₀ e₂₁₂
      e₄₄ e₄₆ e₄₈ e₄₁₀ e₄₁₂
      e₆₆ e₆₈ e₆₁₀ e₆₁₂
      e₈₈ e₈₁₀ e₈₁₂ e₁₀₁₀ e₁₀₁₂ e₁₂₁₂ : ℝ) : Prop :=
  |e₂₂| ≤ (1 / 1000000000 : ℝ) ∧
  |e₂₄| ≤ (1 / 1000000000 : ℝ) ∧
  |e₂₆| ≤ (1 / 1000000000 : ℝ) ∧
  |e₂₈| ≤ (1 / 1000000000 : ℝ) ∧
  |e₂₁₀| ≤ (1 / 1000000000 : ℝ) ∧
  |e₂₁₂| ≤ (1 / 1000000000 : ℝ) ∧
  |e₄₄| ≤ (1 / 1000000000 : ℝ) ∧
  |e₄₆| ≤ (1 / 1000000000 : ℝ) ∧
  |e₄₈| ≤ (1 / 1000000000 : ℝ) ∧
  |e₄₁₀| ≤ (1 / 1000000000 : ℝ) ∧
  |e₄₁₂| ≤ (1 / 1000000000 : ℝ) ∧
  |e₆₆| ≤ (1 / 1000000000 : ℝ) ∧
  |e₆₈| ≤ (1 / 1000000000 : ℝ) ∧
  |e₆₁₀| ≤ (1 / 1000000000 : ℝ) ∧
  |e₆₁₂| ≤ (1 / 1000000000 : ℝ) ∧
  |e₈₈| ≤ (1 / 1000000000 : ℝ) ∧
  |e₈₁₀| ≤ (1 / 1000000000 : ℝ) ∧
  |e₈₁₂| ≤ (1 / 1000000000 : ℝ) ∧
  |e₁₀₁₀| ≤ (1 / 1000000000 : ℝ) ∧
  |e₁₀₁₂| ≤ (1 / 1000000000 : ℝ) ∧
  |e₁₂₁₂| ≤ (1 / 1000000000 : ℝ)

private theorem diagonal_entry_error_lower
    {e x : ℝ} (he : |e| ≤ (1 / 1000000000 : ℝ)) :
    -(1 / 1000000000 : ℝ) * x ^ 2 ≤ e * x ^ 2 := by
  have helower : -(1 / 1000000000 : ℝ) ≤ e := (abs_le.mp he).1
  exact mul_le_mul_of_nonneg_right helower (sq_nonneg x)

private theorem offDiagonal_entry_error_lower
    {e x y : ℝ} (he : |e| ≤ (1 / 1000000000 : ℝ)) :
    -(1 / 1000000000 : ℝ) * (x ^ 2 + y ^ 2) ≤
      2 * e * x * y := by
  have hxy : 2 * |x| * |y| ≤ x ^ 2 + y ^ 2 := by
    simpa only [sq_abs] using two_mul_le_add_sq |x| |y|
  have hsum : 0 ≤ x ^ 2 + y ^ 2 := add_nonneg (sq_nonneg x) (sq_nonneg y)
  have hexy : |e| * (2 * |x| * |y|) ≤
      |e| * (x ^ 2 + y ^ 2) :=
    mul_le_mul_of_nonneg_left hxy (abs_nonneg e)
  have heps : |e| * (x ^ 2 + y ^ 2) ≤
      (1 / 1000000000 : ℝ) * (x ^ 2 + y ^ 2) :=
    mul_le_mul_of_nonneg_right he hsum
  have habs : |2 * e * x * y| ≤
      (1 / 1000000000 : ℝ) * (x ^ 2 + y ^ 2) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith only [hexy, heps]
  convert (neg_le_neg habs).trans (neg_abs_le (2 * e * x * y)) using 1
  ring

set_option maxHeartbeats 800000 in
/-- Simultaneous entrywise error costs at most `6·10⁻⁹` times Euclidean
mass.  The factor six is structural: one diagonal and five off-diagonal
charges meet each quotient coordinate. -/
theorem finiteSevenBorderPerturbation_lower_of_entryBox
    (e₂₂ e₂₄ e₂₆ e₂₈ e₂₁₀ e₂₁₂
      e₄₄ e₄₆ e₄₈ e₄₁₀ e₄₁₂
      e₆₆ e₆₈ e₆₁₀ e₆₁₂
      e₈₈ e₈₁₀ e₈₁₂ e₁₀₁₀ e₁₀₁₂ e₁₂₁₂ : ℝ)
    (hbox : fourCellEvenFiniteSevenBorderEntryBox
      e₂₂ e₂₄ e₂₆ e₂₈ e₂₁₀ e₂₁₂
      e₄₄ e₄₆ e₄₈ e₄₁₀ e₄₁₂
      e₆₆ e₆₈ e₆₁₀ e₆₁₂
      e₈₈ e₈₁₀ e₈₁₂ e₁₀₁₀ e₁₀₁₂ e₁₂₁₂)
    (x₂ x₄ x₆ x₈ x₁₀ x₁₂ : ℝ) :
    -(6 / 1000000000 : ℝ) *
        (x₂ ^ 2 + x₄ ^ 2 + x₆ ^ 2 + x₈ ^ 2 + x₁₀ ^ 2 + x₁₂ ^ 2) ≤
      fourCellEvenFiniteSevenBorderPerturbation
        e₂₂ e₂₄ e₂₆ e₂₈ e₂₁₀ e₂₁₂
        e₄₄ e₄₆ e₄₈ e₄₁₀ e₄₁₂
        e₆₆ e₆₈ e₆₁₀ e₆₁₂
        e₈₈ e₈₁₀ e₈₁₂ e₁₀₁₀ e₁₀₁₂ e₁₂₁₂
        x₂ x₄ x₆ x₈ x₁₀ x₁₂ := by
  rcases hbox with
    ⟨h₂₂, h₂₄, h₂₆, h₂₈, h₂₁₀, h₂₁₂,
      h₄₄, h₄₆, h₄₈, h₄₁₀, h₄₁₂,
      h₆₆, h₆₈, h₆₁₀, h₆₁₂,
      h₈₈, h₈₁₀, h₈₁₂, h₁₀₁₀, h₁₀₁₂, h₁₂₁₂⟩
  have hd₂₂ := diagonal_entry_error_lower (x := x₂) h₂₂
  have hd₄₄ := diagonal_entry_error_lower (x := x₄) h₄₄
  have hd₆₆ := diagonal_entry_error_lower (x := x₆) h₆₆
  have hd₈₈ := diagonal_entry_error_lower (x := x₈) h₈₈
  have hd₁₀₁₀ := diagonal_entry_error_lower (x := x₁₀) h₁₀₁₀
  have hd₁₂₁₂ := diagonal_entry_error_lower (x := x₁₂) h₁₂₁₂
  have ho₂₄ := offDiagonal_entry_error_lower (x := x₂) (y := x₄) h₂₄
  have ho₂₆ := offDiagonal_entry_error_lower (x := x₂) (y := x₆) h₂₆
  have ho₂₈ := offDiagonal_entry_error_lower (x := x₂) (y := x₈) h₂₈
  have ho₂₁₀ := offDiagonal_entry_error_lower (x := x₂) (y := x₁₀) h₂₁₀
  have ho₂₁₂ := offDiagonal_entry_error_lower (x := x₂) (y := x₁₂) h₂₁₂
  have ho₄₆ := offDiagonal_entry_error_lower (x := x₄) (y := x₆) h₄₆
  have ho₄₈ := offDiagonal_entry_error_lower (x := x₄) (y := x₈) h₄₈
  have ho₄₁₀ := offDiagonal_entry_error_lower (x := x₄) (y := x₁₀) h₄₁₀
  have ho₄₁₂ := offDiagonal_entry_error_lower (x := x₄) (y := x₁₂) h₄₁₂
  have ho₆₈ := offDiagonal_entry_error_lower (x := x₆) (y := x₈) h₆₈
  have ho₆₁₀ := offDiagonal_entry_error_lower (x := x₆) (y := x₁₀) h₆₁₀
  have ho₆₁₂ := offDiagonal_entry_error_lower (x := x₆) (y := x₁₂) h₆₁₂
  have ho₈₁₀ := offDiagonal_entry_error_lower (x := x₈) (y := x₁₀) h₈₁₀
  have ho₈₁₂ := offDiagonal_entry_error_lower (x := x₈) (y := x₁₂) h₈₁₂
  have ho₁₀₁₂ := offDiagonal_entry_error_lower (x := x₁₀) (y := x₁₂) h₁₀₁₂
  unfold fourCellEvenFiniteSevenBorderPerturbation
  linarith only [hd₂₂, hd₄₄, hd₆₆, hd₈₈, hd₁₀₁₀, hd₁₂₁₂,
    ho₂₄, ho₂₆, ho₂₈, ho₂₁₀, ho₂₁₂,
    ho₄₆, ho₄₈, ho₄₁₀, ho₄₁₂,
    ho₆₈, ho₆₁₀, ho₆₁₂, ho₈₁₀, ho₈₁₂, ho₁₀₁₂]

/-- Robust seven-coordinate bordered Schur closure.  Any true quotient form
whose twenty-one independent entries are within `10⁻⁹` of the rational
center is nonnegative, uniformly in all six quotient coordinates. -/
theorem finiteSevenBorderCenter_add_perturbation_nonnegative_of_entryBox
    (e₂₂ e₂₄ e₂₆ e₂₈ e₂₁₀ e₂₁₂
      e₄₄ e₄₆ e₄₈ e₄₁₀ e₄₁₂
      e₆₆ e₆₈ e₆₁₀ e₆₁₂
      e₈₈ e₈₁₀ e₈₁₂ e₁₀₁₀ e₁₀₁₂ e₁₂₁₂ : ℝ)
    (hbox : fourCellEvenFiniteSevenBorderEntryBox
      e₂₂ e₂₄ e₂₆ e₂₈ e₂₁₀ e₂₁₂
      e₄₄ e₄₆ e₄₈ e₄₁₀ e₄₁₂
      e₆₆ e₆₈ e₆₁₀ e₆₁₂
      e₈₈ e₈₁₀ e₈₁₂ e₁₀₁₀ e₁₀₁₂ e₁₂₁₂)
    (x₂ x₄ x₆ x₈ x₁₀ x₁₂ : ℝ) :
    0 ≤ fourCellEvenFiniteSevenBorderCenter x₂ x₄ x₆ x₈ x₁₀ x₁₂ +
      fourCellEvenFiniteSevenBorderPerturbation
        e₂₂ e₂₄ e₂₆ e₂₈ e₂₁₀ e₂₁₂
        e₄₄ e₄₆ e₄₈ e₄₁₀ e₄₁₂
        e₆₆ e₆₈ e₆₁₀ e₆₁₂
        e₈₈ e₈₁₀ e₈₁₂ e₁₀₁₀ e₁₀₁₂ e₁₂₁₂
        x₂ x₄ x₆ x₈ x₁₀ x₁₂ := by
  let M : ℝ :=
    x₂ ^ 2 + x₄ ^ 2 + x₆ ^ 2 + x₈ ^ 2 + x₁₀ ^ 2 + x₁₂ ^ 2
  have hM : 0 ≤ M := by
    dsimp only [M]
    positivity
  have hcenter := one_div_hundredMillion_sum_sq_le_finiteSevenBorderCenter
    x₂ x₄ x₆ x₈ x₁₀ x₁₂
  have herror := finiteSevenBorderPerturbation_lower_of_entryBox
    e₂₂ e₂₄ e₂₆ e₂₈ e₂₁₀ e₂₁₂
    e₄₄ e₄₆ e₄₈ e₄₁₀ e₄₁₂
    e₆₆ e₆₈ e₆₁₀ e₆₁₂
    e₈₈ e₈₁₀ e₈₁₂ e₁₀₁₀ e₁₀₁₂ e₁₂₁₂ hbox
    x₂ x₄ x₆ x₈ x₁₀ x₁₂
  dsimp only [M] at hM
  linarith only [hM, hcenter, herror]

/-! ## The actual analytic quotient entries -/

/-- The centered shifted-Legendre mode used to name the seven finite
coordinates without introducing separate mode-specific definitions. -/
def fourCellEvenFiniteSevenCenteredMode (n : ℕ) : ℝ → ℝ :=
  centeredPolynomialLift (shiftedLegendreReal n)

/-- Its positive-half wide-cosh coordinate. -/
def fourCellEvenFiniteSevenCoshCoordinate (n : ℕ) : ℝ :=
  fourCellPositiveCoshMoment (fourCellEvenFiniteSevenCenteredMode n)
    (fourCellOperatorHalfWidth / 2)

private theorem fourCellEvenFiniteSevenCenteredMode_zero (x : ℝ) :
    fourCellEvenFiniteSevenCenteredMode 0 x = 1 := by
  unfold fourCellEvenFiniteSevenCenteredMode centeredPolynomialLift
    shiftedLegendreReal
  norm_num [Polynomial.shiftedLegendre, Polynomial.eval_map,
    Polynomial.eval_finset_sum, Finset.sum_range_succ, Nat.choose]

/-- The quotient denominator is strictly positive; it is an integral of a
strictly positive cosh factor against the constant mode. -/
theorem fourCellEvenFiniteSevenCoshCoordinate_zero_pos :
    0 < fourCellEvenFiniteSevenCoshCoordinate 0 := by
  unfold fourCellEvenFiniteSevenCoshCoordinate fourCellPositiveCoshMoment
  simp_rw [fourCellEvenFiniteSevenCenteredMode_zero, mul_one]
  apply intervalIntegral.integral_pos (by norm_num)
  · fun_prop
  · intro x _hx
    exact (Real.cosh_pos _).le
  · exact ⟨0, by norm_num, Real.cosh_pos _⟩

/-- Quotient a nonconstant mode by the single `P₀` wide-cosh direction.
For `n = 2,4,…,12` these are the six coordinates used by the certificate. -/
def fourCellEvenFiniteSevenQuotientMode (n : ℕ) (x : ℝ) : ℝ :=
  fourCellEvenFiniteSevenCenteredMode n x -
    (fourCellEvenFiniteSevenCoshCoordinate n /
      fourCellEvenFiniteSevenCoshCoordinate 0) *
        fourCellEvenFiniteSevenCenteredMode 0 x

/-- Each quotient mode has exactly zero wide-cosh coordinate.  This is an
integral identity, not a numerical near-orthogonality assertion. -/
theorem fourCellEvenFiniteSevenQuotientMode_coshCoordinate_zero (n : ℕ) :
    fourCellPositiveCoshMoment
        (fourCellEvenFiniteSevenQuotientMode n)
        (fourCellOperatorHalfWidth / 2) = 0 := by
  unfold fourCellEvenFiniteSevenQuotientMode fourCellPositiveCoshMoment
  rw [show (fun x : ℝ ↦
      Real.cosh ((fourCellOperatorHalfWidth / 2) * x) *
        (fourCellEvenFiniteSevenCenteredMode n x -
          (fourCellEvenFiniteSevenCoshCoordinate n /
            fourCellEvenFiniteSevenCoshCoordinate 0) *
              fourCellEvenFiniteSevenCenteredMode 0 x)) =
      fun x ↦
        Real.cosh ((fourCellOperatorHalfWidth / 2) * x) *
          fourCellEvenFiniteSevenCenteredMode n x -
        (fourCellEvenFiniteSevenCoshCoordinate n /
          fourCellEvenFiniteSevenCoshCoordinate 0) *
            (Real.cosh ((fourCellOperatorHalfWidth / 2) * x) *
              fourCellEvenFiniteSevenCenteredMode 0 x) by
    funext x
    ring]
  rw [intervalIntegral.integral_sub
    (Continuous.intervalIntegrable (by
      unfold fourCellEvenFiniteSevenCenteredMode centeredPolynomialLift
      fun_prop) 0 1)
    (Continuous.intervalIntegrable (by
      unfold fourCellEvenFiniteSevenCenteredMode centeredPolynomialLift
      fun_prop) 0 1),
    intervalIntegral.integral_const_mul]
  change fourCellEvenFiniteSevenCoshCoordinate n -
      fourCellEvenFiniteSevenCoshCoordinate n /
        fourCellEvenFiniteSevenCoshCoordinate 0 *
          fourCellEvenFiniteSevenCoshCoordinate 0 = 0
  field_simp [fourCellEvenFiniteSevenCoshCoordinate_zero_pos.ne']
  ring

/-- Polarization of the true polar-free even quadratic. -/
def fourCellEvenFiniteSevenPolarFreePolarization
    (u v : ℝ → ℝ) : ℝ :=
  (fourCellEvenPolarFreeOperator (u + v) -
      fourCellEvenPolarFreeOperator u -
      fourCellEvenPolarFreeOperator v) / 2

/-- The true endpoint bordered polarization on the finite cosh quotient.
The coefficient `251/250` is exactly the finite-row factor retained by the
cutoff-fourteen tail absorption theorem. -/
def fourCellEvenFiniteSevenBorderPolarization
    (u v : ℝ → ℝ) : ℝ :=
  fourCellEvenExactBracket fourCellEvenEndpointCoshSeed *
      fourCellEvenFiniteSevenPolarFreePolarization u v -
    (251 / 250 : ℝ) * fourCellEvenEndpointSeedRow u *
      fourCellEvenEndpointSeedRow v

/-- One true entry of the six-dimensional quotient border. -/
def fourCellEvenFiniteSevenTrueBorderEntry (m n : ℕ) : ℝ :=
  fourCellEvenFiniteSevenBorderPolarization
    (fourCellEvenFiniteSevenQuotientMode m)
    (fourCellEvenFiniteSevenQuotientMode n)

/-- The true six-coordinate matrix quadratic, before proving any analytic
entry enclosure. -/
def fourCellEvenFiniteSevenTrueBorderMatrixQuadratic
    (x₂ x₄ x₆ x₈ x₁₀ x₁₂ : ℝ) : ℝ :=
  fourCellEvenFiniteSevenTrueBorderEntry 2 2 * x₂ ^ 2 +
    2 * fourCellEvenFiniteSevenTrueBorderEntry 2 4 * x₂ * x₄ +
    2 * fourCellEvenFiniteSevenTrueBorderEntry 2 6 * x₂ * x₆ +
    2 * fourCellEvenFiniteSevenTrueBorderEntry 2 8 * x₂ * x₈ +
    2 * fourCellEvenFiniteSevenTrueBorderEntry 2 10 * x₂ * x₁₀ +
    2 * fourCellEvenFiniteSevenTrueBorderEntry 2 12 * x₂ * x₁₂ +
    fourCellEvenFiniteSevenTrueBorderEntry 4 4 * x₄ ^ 2 +
    2 * fourCellEvenFiniteSevenTrueBorderEntry 4 6 * x₄ * x₆ +
    2 * fourCellEvenFiniteSevenTrueBorderEntry 4 8 * x₄ * x₈ +
    2 * fourCellEvenFiniteSevenTrueBorderEntry 4 10 * x₄ * x₁₀ +
    2 * fourCellEvenFiniteSevenTrueBorderEntry 4 12 * x₄ * x₁₂ +
    fourCellEvenFiniteSevenTrueBorderEntry 6 6 * x₆ ^ 2 +
    2 * fourCellEvenFiniteSevenTrueBorderEntry 6 8 * x₆ * x₈ +
    2 * fourCellEvenFiniteSevenTrueBorderEntry 6 10 * x₆ * x₁₀ +
    2 * fourCellEvenFiniteSevenTrueBorderEntry 6 12 * x₆ * x₁₂ +
    fourCellEvenFiniteSevenTrueBorderEntry 8 8 * x₈ ^ 2 +
    2 * fourCellEvenFiniteSevenTrueBorderEntry 8 10 * x₈ * x₁₀ +
    2 * fourCellEvenFiniteSevenTrueBorderEntry 8 12 * x₈ * x₁₂ +
    fourCellEvenFiniteSevenTrueBorderEntry 10 10 * x₁₀ ^ 2 +
    2 * fourCellEvenFiniteSevenTrueBorderEntry 10 12 * x₁₀ * x₁₂ +
    fourCellEvenFiniteSevenTrueBorderEntry 12 12 * x₁₂ ^ 2

/-- The exact analytic obligations left by the finite certificate: each true
entry, after subtracting the displayed rational center, must fit the common
`10⁻⁹` box. -/
def fourCellEvenFiniteSevenTrueBorderEntryBox : Prop :=
  fourCellEvenFiniteSevenBorderEntryBox
    (fourCellEvenFiniteSevenTrueBorderEntry 2 2 -
      2111977675374 / 1000000000000000)
    (fourCellEvenFiniteSevenTrueBorderEntry 2 4 -
      1890449921460 / 1000000000000000)
    (fourCellEvenFiniteSevenTrueBorderEntry 2 6 -
      1052053921205 / 1000000000000000)
    (fourCellEvenFiniteSevenTrueBorderEntry 2 8 -
      77967838024 / 1000000000000000)
    (fourCellEvenFiniteSevenTrueBorderEntry 2 10 -
      143965754572 / 1000000000000000)
    (fourCellEvenFiniteSevenTrueBorderEntry 2 12 -
      368171241285 / 1000000000000000)
    (fourCellEvenFiniteSevenTrueBorderEntry 4 4 -
      1728212144335 / 1000000000000000)
    (fourCellEvenFiniteSevenTrueBorderEntry 4 6 -
      1217630782157 / 1000000000000000)
    (fourCellEvenFiniteSevenTrueBorderEntry 4 8 -
      213431716983 / 1000000000000000)
    (fourCellEvenFiniteSevenTrueBorderEntry 4 10 -
      184254796445 / 1000000000000000)
    (fourCellEvenFiniteSevenTrueBorderEntry 4 12 -
      346732076476 / 1000000000000000)
    (fourCellEvenFiniteSevenTrueBorderEntry 6 6 -
      2723234397896 / 1000000000000000)
    (fourCellEvenFiniteSevenTrueBorderEntry 6 8 -
      742541479585 / 1000000000000000)
    (fourCellEvenFiniteSevenTrueBorderEntry 6 10 -
      598571709567 / 1000000000000000)
    (fourCellEvenFiniteSevenTrueBorderEntry 6 12 -
      302011253841 / 1000000000000000)
    (fourCellEvenFiniteSevenTrueBorderEntry 8 8 -
      2950453847668 / 1000000000000000)
    (fourCellEvenFiniteSevenTrueBorderEntry 8 10 -
      855847573644 / 1000000000000000)
    (fourCellEvenFiniteSevenTrueBorderEntry 8 12 -
      227312970022 / 1000000000000000)
    (fourCellEvenFiniteSevenTrueBorderEntry 10 10 -
      2455103917679 / 1000000000000000)
    (fourCellEvenFiniteSevenTrueBorderEntry 10 12 -
      402562607163 / 1000000000000000)
    (fourCellEvenFiniteSevenTrueBorderEntry 12 12 -
      2235373831399 / 1000000000000000)

set_option maxHeartbeats 800000 in
/-- Once the named analytic entry box is proved, the true quotient border is
nonnegative for all seven-coordinate profiles. -/
theorem finiteSevenTrueBorderMatrixQuadratic_nonnegative_of_entryBox
    (hbox : fourCellEvenFiniteSevenTrueBorderEntryBox)
    (x₂ x₄ x₆ x₈ x₁₀ x₁₂ : ℝ) :
    0 ≤ fourCellEvenFiniteSevenTrueBorderMatrixQuadratic
      x₂ x₄ x₆ x₈ x₁₀ x₁₂ := by
  have h := finiteSevenBorderCenter_add_perturbation_nonnegative_of_entryBox
    (fourCellEvenFiniteSevenTrueBorderEntry 2 2 -
      2111977675374 / 1000000000000000)
    (fourCellEvenFiniteSevenTrueBorderEntry 2 4 -
      1890449921460 / 1000000000000000)
    (fourCellEvenFiniteSevenTrueBorderEntry 2 6 -
      1052053921205 / 1000000000000000)
    (fourCellEvenFiniteSevenTrueBorderEntry 2 8 -
      77967838024 / 1000000000000000)
    (fourCellEvenFiniteSevenTrueBorderEntry 2 10 -
      143965754572 / 1000000000000000)
    (fourCellEvenFiniteSevenTrueBorderEntry 2 12 -
      368171241285 / 1000000000000000)
    (fourCellEvenFiniteSevenTrueBorderEntry 4 4 -
      1728212144335 / 1000000000000000)
    (fourCellEvenFiniteSevenTrueBorderEntry 4 6 -
      1217630782157 / 1000000000000000)
    (fourCellEvenFiniteSevenTrueBorderEntry 4 8 -
      213431716983 / 1000000000000000)
    (fourCellEvenFiniteSevenTrueBorderEntry 4 10 -
      184254796445 / 1000000000000000)
    (fourCellEvenFiniteSevenTrueBorderEntry 4 12 -
      346732076476 / 1000000000000000)
    (fourCellEvenFiniteSevenTrueBorderEntry 6 6 -
      2723234397896 / 1000000000000000)
    (fourCellEvenFiniteSevenTrueBorderEntry 6 8 -
      742541479585 / 1000000000000000)
    (fourCellEvenFiniteSevenTrueBorderEntry 6 10 -
      598571709567 / 1000000000000000)
    (fourCellEvenFiniteSevenTrueBorderEntry 6 12 -
      302011253841 / 1000000000000000)
    (fourCellEvenFiniteSevenTrueBorderEntry 8 8 -
      2950453847668 / 1000000000000000)
    (fourCellEvenFiniteSevenTrueBorderEntry 8 10 -
      855847573644 / 1000000000000000)
    (fourCellEvenFiniteSevenTrueBorderEntry 8 12 -
      227312970022 / 1000000000000000)
    (fourCellEvenFiniteSevenTrueBorderEntry 10 10 -
      2455103917679 / 1000000000000000)
    (fourCellEvenFiniteSevenTrueBorderEntry 10 12 -
      402562607163 / 1000000000000000)
    (fourCellEvenFiniteSevenTrueBorderEntry 12 12 -
      2235373831399 / 1000000000000000)
    (by simpa only [fourCellEvenFiniteSevenTrueBorderEntryBox] using hbox)
    x₂ x₄ x₆ x₈ x₁₀ x₁₂
  unfold fourCellEvenFiniteSevenTrueBorderMatrixQuadratic at ⊢
  unfold fourCellEvenFiniteSevenBorderCenter
    fourCellEvenFiniteSevenBorderPerturbation at h
  nlinarith only [h]

end

end ArithmeticHodge.Analysis.YoshidaFourCellEvenEndpointSeedFiniteSevenClosureStructural
