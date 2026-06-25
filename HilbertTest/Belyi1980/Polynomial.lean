import Mathlib

/-!
Checked elementary pieces from Belyi's 1980 paper
`On Galois Extensions of a Maximal Cyclotomic Field`.

The full paper uses algebraic curves and descent.  This file isolates the
explicit polynomial construction on the projective line:

  `x ↦ x^m * (1 - x)^n`

and proves the derivative formula and the algebraic cancellation at the middle
critical point `m / (m + n)`.
-/

namespace Belyi1980

noncomputable section

open Real

/-- The unscaled Belyi polynomial used after normalizing a rational triple to
`{0, m/(m+n), 1}`. -/
def auxPolynomial (m n : Nat) (x : Real) : Real :=
  x ^ m * (1 - x) ^ n

/-- The scaled polynomial whose middle critical value is normalized to `1`. -/
def normalizedAuxPolynomial (m n : Nat) (x : Real) : Real :=
  (((m + n : Nat) : Real) ^ (m + n) / ((m : Real) ^ m * (n : Real) ^ n)) *
    auxPolynomial m n x

/-- Derivative formula for `x^m * (1 - x)^n`. -/
theorem hasDerivAt_auxPolynomial
    (m n : Nat) (x : Real) :
    HasDerivAt (fun y : Real => auxPolynomial m n y)
      ((m : Real) * x ^ (m - 1) * (1 - x) ^ n -
        (n : Real) * x ^ m * (1 - x) ^ (n - 1)) x := by
  unfold auxPolynomial
  have hxpow : HasDerivAt (fun y : Real => y ^ m) ((m : Real) * x ^ (m - 1)) x := by
    simpa using hasDerivAt_pow m x
  have honeSub : HasDerivAt (fun y : Real => 1 - y) (-1 : Real) x := by
    simpa using (hasDerivAt_const (c := (1 : Real)) (x := x)).sub (hasDerivAt_id x)
  have hright : HasDerivAt (fun y : Real => (1 - y) ^ n)
      ((n : Real) * (1 - x) ^ (n - 1) * (-1 : Real)) x := by
    simpa [one_mul] using honeSub.pow n
  convert hxpow.mul hright using 1
  ring

/-- The middle critical point makes the linear factor in the derivative vanish. -/
theorem middle_linear_factor_zero
    {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    (m : Real) * (1 - (m : Real) / ((m + n : Nat) : Real)) -
        (n : Real) * ((m : Real) / ((m + n : Nat) : Real)) = 0 := by
  have hden : ((m + n : Nat) : Real) ≠ 0 := by
    exact_mod_cast (Nat.succ_le_iff.mp (Nat.succ_le_of_lt (Nat.add_pos_left hm n))).ne'
  field_simp [hden]
  ring

/-- The derivative expression of the auxiliary polynomial vanishes at the
middle critical point. -/
theorem derivativeValue_auxPolynomial_middle_eq_zero
    {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    (m : Real) * ((m : Real) / ((m + n : Nat) : Real)) ^ (m - 1) *
          (1 - (m : Real) / ((m + n : Nat) : Real)) ^ n -
        (n : Real) * ((m : Real) / ((m + n : Nat) : Real)) ^ m *
          (1 - (m : Real) / ((m + n : Nat) : Real)) ^ (n - 1) = 0 := by
  let x : Real := (m : Real) / ((m + n : Nat) : Real)
  have hlin : (m : Real) * (1 - x) - (n : Real) * x = 0 := by
    dsimp [x]
    exact middle_linear_factor_zero hm hn
  have hxm : x ^ m = x ^ (m - 1) * x := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega]
    rw [pow_succ]
  have hyn : (1 - x) ^ n = (1 - x) ^ (n - 1) * (1 - x) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [pow_succ]
  change (m : Real) * x ^ (m - 1) * (1 - x) ^ n -
        (n : Real) * x ^ m * (1 - x) ^ (n - 1) = 0
  rw [hxm, hyn]
  calc
    (m : Real) * x ^ (m - 1) * ((1 - x) ^ (n - 1) * (1 - x)) -
        (n : Real) * (x ^ (m - 1) * x) * (1 - x) ^ (n - 1)
        = x ^ (m - 1) * (1 - x) ^ (n - 1) *
            ((m : Real) * (1 - x) - (n : Real) * x) := by ring
    _ = 0 := by rw [hlin, mul_zero]

/-- The middle point is a critical point of the auxiliary polynomial. -/
theorem hasDerivAt_auxPolynomial_middle_zero
    {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    HasDerivAt (fun y : Real => auxPolynomial m n y) 0
      ((m : Real) / ((m + n : Nat) : Real)) := by
  have hder := hasDerivAt_auxPolynomial m n
    ((m : Real) / ((m + n : Nat) : Real))
  have hzero := derivativeValue_auxPolynomial_middle_eq_zero hm hn
  rw [hzero] at hder
  simpa using hder

/-- The middle point is strictly between zero and one. -/
theorem middle_mem_unit_interval
    {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    0 < (m : Real) / ((m + n : Nat) : Real) ∧
      (m : Real) / ((m + n : Nat) : Real) < 1 := by
  have hmreal : 0 < (m : Real) := by exact_mod_cast hm
  have hnreal : 0 < (n : Real) := by exact_mod_cast hn
  have hden : 0 < ((m + n : Nat) : Real) := by exact_mod_cast Nat.add_pos_left hm n
  constructor
  · positivity
  · rw [div_lt_one hden]
    exact_mod_cast Nat.lt_add_of_pos_right hn

/-- At the normalized middle point, `1 - m/(m+n) = n/(m+n)`. -/
theorem one_sub_middle_eq_right_ratio
    {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    1 - (m : Real) / ((m + n : Nat) : Real) =
      (n : Real) / ((m + n : Nat) : Real) := by
  have hden : ((m + n : Nat) : Real) ≠ 0 := by
    exact_mod_cast (Nat.succ_le_iff.mp (Nat.succ_le_of_lt (Nat.add_pos_left hm n))).ne'
  field_simp [hden]

/-- Belyi's scaling sends the middle critical point to `1`. -/
theorem normalizedAuxPolynomial_middle_eq_one
    {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    normalizedAuxPolynomial m n ((m : Real) / ((m + n : Nat) : Real)) = 1 := by
  have hden : ((m + n : Nat) : Real) ≠ 0 := by
    exact_mod_cast (Nat.succ_le_iff.mp (Nat.succ_le_of_lt (Nat.add_pos_left hm n))).ne'
  have hmne : (m : Real) ≠ 0 := by exact_mod_cast hm.ne'
  have hnne : (n : Real) ≠ 0 := by exact_mod_cast hn.ne'
  unfold normalizedAuxPolynomial auxPolynomial
  rw [one_sub_middle_eq_right_ratio hm hn]
  rw [div_pow, div_pow]
  rw [Nat.cast_add, pow_add]
  field_simp [hden, hmne, hnne]

/-- The absolute value of the middle critical value
`(m/(m+n))^m * (n/(m+n))^n` is positive. -/
theorem middle_power_product_pos
    {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    0 <
      ((m : Real) / ((m + n : Nat) : Real)) ^ m *
        ((n : Real) / ((m + n : Nat) : Real)) ^ n := by
  have hden : 0 < ((m + n : Nat) : Real) := by
    exact_mod_cast Nat.add_pos_left hm n
  have hmreal : 0 < (m : Real) := by exact_mod_cast hm
  have hnreal : 0 < (n : Real) := by exact_mod_cast hn
  positivity

/-- The middle critical value is at most `1/4`, a compressed AM-GM version of
the case analysis used in Mochizuki's proof of Lemma 2.1. -/
theorem middle_power_product_le_quarter
    {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    ((m : Real) / ((m + n : Nat) : Real)) ^ m *
        ((n : Real) / ((m + n : Nat) : Real)) ^ n <= 1 / 4 := by
  let a : Real := (m : Real) / ((m + n : Nat) : Real)
  let b : Real := (n : Real) / ((m + n : Nat) : Real)
  have hden_pos : 0 < ((m + n : Nat) : Real) := by
    exact_mod_cast Nat.add_pos_left hm n
  have ha_nonneg : 0 <= a := by
    dsimp [a]
    positivity
  have hb_nonneg : 0 <= b := by
    dsimp [b]
    positivity
  have ha_le_one : a <= 1 := by
    dsimp [a]
    rw [div_le_one hden_pos]
    exact_mod_cast Nat.le_add_right m n
  have hb_le_one : b <= 1 := by
    dsimp [b]
    rw [div_le_one hden_pos]
    exact_mod_cast Nat.le_add_left n m
  have ha_pow_le : a ^ m <= a := by
    exact pow_le_of_le_one ha_nonneg ha_le_one hm.ne'
  have hb_pow_le : b ^ n <= b := by
    exact pow_le_of_le_one hb_nonneg hb_le_one hn.ne'
  have hpowprod_le : a ^ m * b ^ n <= a * b := by
    exact mul_le_mul ha_pow_le hb_pow_le (pow_nonneg hb_nonneg n) ha_nonneg
  have hab_le_quarter : a * b <= 1 / 4 := by
    dsimp [a, b]
    have hamgm : 4 * (m : Real) * (n : Real) <= ((m : Real) + (n : Real)) ^ 2 := by
      simpa using four_mul_le_sq_add (m : Real) (n : Real)
    rw [Nat.cast_add]
    have hden_sum_pos : 0 < (m : Real) + (n : Real) := by
      rwa [← Nat.cast_add]
    have hprod_eq :
        (m : Real) / ((m : Real) + (n : Real)) *
            ((n : Real) / ((m : Real) + (n : Real))) =
          ((m : Real) * (n : Real)) /
            (((m : Real) + (n : Real)) * ((m : Real) + (n : Real))) := by
      field_simp [ne_of_gt hden_sum_pos]
    rw [hprod_eq]
    rw [div_le_iff₀ (mul_pos hden_sum_pos hden_sum_pos)]
    nlinarith
  exact le_trans hpowprod_le hab_le_quarter

end

end Belyi1980
