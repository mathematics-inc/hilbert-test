import Mathlib

/-!
Algebraic polynomial layer for Mochizuki, Lemma 2.1.

The elementary real-inequality file works with the function
`x ↦ x^m * (x - 1)^n`.  This file records the corresponding polynomial over
`ℚ[X]`, including the endpoint values and the factored formal derivative used
to identify the critical points `{0, m/(m+n), 1, ∞}` on `P^1`.
-/

namespace NoncriticalBelyi

noncomputable section

open Polynomial

/-- The polynomial `x^m * (x - 1)^n` from Mochizuki, Lemma 2.1. -/
def paperPolynomial (m n : ℕ) : ℚ[X] :=
  X ^ m * (X - 1) ^ n

/-- The paper polynomial sends `0` to `0` when `m > 0`. -/
theorem paperPolynomial_eval_zero
    {m n : ℕ} (hm : 0 < m) :
    (paperPolynomial m n).eval 0 = 0 := by
  simp [paperPolynomial, zero_pow hm.ne']

/-- The paper polynomial sends `1` to `0` when `n > 0`. -/
theorem paperPolynomial_eval_one
    {m n : ℕ} (hn : 0 < n) :
    (paperPolynomial m n).eval 1 = 0 := by
  simp [paperPolynomial, zero_pow hn.ne']

/-- Formal derivative of `X^m * (X - 1)^n`. -/
theorem derivative_paperPolynomial
    (m n : ℕ) :
    derivative (paperPolynomial m n) =
      C (m : ℚ) * X ^ (m - 1) * (X - 1) ^ n +
        C (n : ℚ) * X ^ m * (X - 1) ^ (n - 1) := by
  unfold paperPolynomial
  simp [Polynomial.derivative_mul, Polynomial.derivative_pow]
  ring

/-- Factored derivative formula from Mochizuki, Lemma 2.1. -/
theorem derivative_paperPolynomial_factor
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    derivative (paperPolynomial m n) =
      X ^ (m - 1) * (X - 1) ^ (n - 1) *
        (C (((m + n : ℕ) : ℚ)) * X - C (m : ℚ)) := by
  rw [derivative_paperPolynomial]
  have hxm : (X : ℚ[X]) ^ m = X ^ (m - 1) * X := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega]
    rw [pow_succ]
  have hyn : (X - 1 : ℚ[X]) ^ n = (X - 1) ^ (n - 1) * (X - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [pow_succ]
  rw [hxm, hyn]
  norm_num [Nat.cast_add]
  ring

/-- The middle point `m/(m+n)` is a zero of the formal derivative. -/
theorem derivative_paperPolynomial_eval_middle_eq_zero
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (derivative (paperPolynomial m n)).eval
      ((m : ℚ) / (((m + n : ℕ) : ℚ))) = 0 := by
  rw [derivative_paperPolynomial_factor hm hn]
  simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C]
  have hden : (((m + n : ℕ) : ℚ)) ≠ 0 := by
    exact_mod_cast (Nat.add_pos_left hm n).ne'
  have hlin :
      (((m + n : ℕ) : ℚ)) * ((m : ℚ) / (((m + n : ℕ) : ℚ))) -
          (m : ℚ) = 0 := by
    field_simp [hden]
  rw [hlin, mul_zero]

/-- Packaged algebraic data from Lemma 2.1: the two endpoint values, the
factored derivative, and the middle critical-point evaluation. -/
theorem paperPolynomial_basic_data
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (paperPolynomial m n).eval 0 = 0 ∧
      (paperPolynomial m n).eval 1 = 0 ∧
      derivative (paperPolynomial m n) =
        X ^ (m - 1) * (X - 1) ^ (n - 1) *
          (C (((m + n : ℕ) : ℚ)) * X - C (m : ℚ)) ∧
      (derivative (paperPolynomial m n)).eval
        ((m : ℚ) / (((m + n : ℕ) : ℚ))) = 0 := by
  exact ⟨paperPolynomial_eval_zero hm,
    paperPolynomial_eval_one hn,
    derivative_paperPolynomial_factor hm hn,
    derivative_paperPolynomial_eval_middle_eq_zero hm hn⟩

end

end NoncriticalBelyi
