import HilbertTest.NoncriticalBelyi.Elementary
import HilbertTest.NoncriticalBelyi.Polynomial

/-!
Hilbert-facing targets for the checked elementary part of Mochizuki's
`Noncritical Belyi Maps`, Lemma 2.1.
-/

namespace HilbertTest
namespace HilbertSteps
namespace MochizukiElementary

open Real Polynomial

theorem hilbert_beta_ge_two_of_condition
    {beta C : Real}
    (hC : 2 <= C)
    (h1 : beta / 1 >= C) :
    2 <= beta := by
  exact NoncriticalBelyi.beta_ge_two_of_condition hC h1

theorem hilbert_beta_gt_alpha_of_scale
    {alpha beta C : Real}
    (hC : 2 <= C)
    (halpha_pos : 0 < alpha)
    (hscale : beta / alpha >= C) :
    alpha < beta := by
  exact NoncriticalBelyi.beta_gt_alpha_of_scale hC halpha_pos hscale

theorem hilbert_ratio_sub_one_ge_ratio
    {alpha beta : Real}
    (halpha : 1 < alpha)
    (hbeta : alpha <= beta) :
    beta / alpha <= (beta - 1) / (alpha - 1) := by
  exact NoncriticalBelyi.ratio_sub_one_ge_ratio halpha hbeta

theorem hilbert_belyi_aux_ratio_lower_bound
    {m n : Nat} {alpha beta : Real}
    (hm : 1 <= m)
    (hn : 1 <= n)
    (halpha : 1 < alpha)
    (hbeta : alpha <= beta) :
    (beta / alpha) <=
      (beta / alpha) ^ m * ((beta - 1) / (alpha - 1)) ^ n := by
  exact NoncriticalBelyi.belyi_aux_ratio_lower_bound hm hn halpha hbeta

theorem hilbert_belyi_aux_ratio_ge_quadratic
    {m n : Nat} {alpha beta : Real}
    (hm : 1 <= m)
    (hn : 1 <= n)
    (halpha : 1 < alpha)
    (hbeta : alpha <= beta) :
    (beta / alpha) ^ 2 <=
      (beta / alpha) ^ m * ((beta - 1) / (alpha - 1)) ^ n := by
  exact NoncriticalBelyi.belyi_aux_ratio_ge_quadratic hm hn halpha hbeta

theorem hilbert_belyi_aux_beta_gt_one
    {m n : Nat} {beta : Real}
    (hm : 1 <= m)
    (hn : 1 <= n)
    (hbeta : 2 <= beta) :
    1 < NoncriticalBelyi.belyiAux m n beta := by
  exact NoncriticalBelyi.belyi_aux_beta_gt_one hm hn hbeta

theorem hilbert_beta_le_belyi_aux_of_beta_ge_two
    {m n : Nat} {beta : Real}
    (hm : 1 <= m)
    (hn : 1 <= n)
    (hbeta : 2 <= beta) :
    beta <= NoncriticalBelyi.belyiAux m n beta := by
  exact NoncriticalBelyi.beta_le_belyi_aux_of_beta_ge_two hm hn hbeta

theorem hilbert_beta_le_two_mul_belyi_aux_of_beta_ge_two
    {m n : Nat} {beta : Real}
    (hm : 1 <= m)
    (hn : 1 <= n)
    (hbeta : 2 <= beta) :
    beta <= 2 * NoncriticalBelyi.belyiAux m n beta := by
  exact NoncriticalBelyi.beta_le_two_mul_belyi_aux_of_beta_ge_two hm hn hbeta

theorem hilbert_belyi_aux_pos_of_gt_one
    {m n : Nat} {x : Real}
    (hx : 1 < x) :
    0 < NoncriticalBelyi.belyiAux m n x := by
  exact NoncriticalBelyi.belyi_aux_pos_of_gt_one hx

theorem hilbert_belyi_aux_beta_ge_four_mul_of_scale
    {m n : Nat} {alpha beta C : Real}
    (hm : 1 <= m)
    (hn : 1 <= n)
    (hC : 2 <= C)
    (halpha : 1 < alpha)
    (hscale : beta / alpha >= C) :
    4 * NoncriticalBelyi.belyiAux m n alpha <=
      NoncriticalBelyi.belyiAux m n beta := by
  exact NoncriticalBelyi.belyi_aux_beta_ge_four_mul_of_scale
    hm hn hC halpha hscale

theorem hilbert_belyi_aux_beta_gt_of_scale
    {m n : Nat} {alpha beta C : Real}
    (hm : 1 <= m)
    (hn : 1 <= n)
    (hC : 2 <= C)
    (halpha : 1 < alpha)
    (hscale : beta / alpha >= C) :
    NoncriticalBelyi.belyiAux m n alpha <
      NoncriticalBelyi.belyiAux m n beta := by
  exact NoncriticalBelyi.belyi_aux_beta_gt_of_scale
    hm hn hC halpha hscale

theorem hilbert_belyi_aux_strict_mono_on_gt_one
    {m n : Nat} {alpha beta : Real}
    (hm : 1 <= m)
    (hn : 1 <= n)
    (halpha : 1 < alpha)
    (hbeta : alpha < beta) :
    NoncriticalBelyi.belyiAux m n alpha <
      NoncriticalBelyi.belyiAux m n beta := by
  exact NoncriticalBelyi.belyi_aux_strict_mono_on_gt_one
    hm hn halpha hbeta

theorem hilbert_half_square_ge_self_of_ge_two
    {y : Real} (hy : 2 <= y) :
    y <= (1 / 2) * y ^ 2 := by
  exact NoncriticalBelyi.half_square_ge_self_of_ge_two hy

theorem hilbert_offset_ratio_ge_half_denominator_ratio
    {A B t : Real}
    (hA_nonneg : 0 <= A)
    (hB_pos : 0 < B)
    (ht_nonneg : 0 <= t)
    (ht_le_B : t <= B) :
    A / (2 * B) <= (A + t) / (B + t) := by
  exact NoncriticalBelyi.offset_ratio_ge_half_denominator_ratio
    hA_nonneg hB_pos ht_nonneg ht_le_B

theorem hilbert_offset_ratio_ge_div_two_offset
    {A B t : Real}
    (hA_nonneg : 0 <= A)
    (hB_nonneg : 0 <= B)
    (ht_pos : 0 < t)
    (hB_le_t : B <= t) :
    A / (2 * t) <= (A + t) / (B + t) := by
  exact NoncriticalBelyi.offset_ratio_ge_div_two_offset
    hA_nonneg hB_nonneg ht_pos hB_le_t

theorem hilbert_two_mul_le_div_two_offset_of_offset_le_quarter
    {A t : Real}
    (hA_nonneg : 0 <= A)
    (ht_pos : 0 < t)
    (ht_le_quarter : t <= 1 / 4) :
    2 * A <= A / (2 * t) := by
  exact NoncriticalBelyi.two_mul_le_div_two_offset_of_offset_le_quarter
    hA_nonneg ht_pos ht_le_quarter

theorem hilbert_abs_belyi_aux_le_one_on_unit_interval
    {m n : Nat} {x : Real}
    (hm : 1 <= m)
    (hn : 1 <= n)
    (hx0 : 0 <= x)
    (hx1 : x <= 1) :
    |NoncriticalBelyi.belyiAux m n x| <= 1 := by
  exact NoncriticalBelyi.abs_belyi_aux_le_one_on_unit_interval hm hn hx0 hx1

theorem hilbert_belyi_aux_beta_gt_unit_interval_value
    {m n : Nat} {beta x : Real}
    (hm : 1 <= m)
    (hn : 1 <= n)
    (hbeta : 2 <= beta)
    (hx0 : 0 <= x)
    (hx1 : x <= 1) :
    NoncriticalBelyi.belyiAux m n x <
      NoncriticalBelyi.belyiAux m n beta := by
  exact NoncriticalBelyi.belyi_aux_beta_gt_unit_interval_value
    hm hn hbeta hx0 hx1

theorem hilbert_belyi_aux_beta_ne_unit_interval_value
    {m n : Nat} {beta x : Real}
    (hm : 1 <= m)
    (hn : 1 <= n)
    (hbeta : 2 <= beta)
    (hx0 : 0 <= x)
    (hx1 : x <= 1) :
    NoncriticalBelyi.belyiAux m n beta ≠
      NoncriticalBelyi.belyiAux m n x := by
  exact NoncriticalBelyi.belyi_aux_beta_ne_unit_interval_value
    hm hn hbeta hx0 hx1

theorem hilbert_paperPolynomial_eval_zero
    {m n : Nat} (hm : 0 < m) :
    (NoncriticalBelyi.paperPolynomial m n).eval 0 = 0 := by
  exact NoncriticalBelyi.paperPolynomial_eval_zero hm

theorem hilbert_paperPolynomial_eval_one
    {m n : Nat} (hn : 0 < n) :
    (NoncriticalBelyi.paperPolynomial m n).eval 1 = 0 := by
  exact NoncriticalBelyi.paperPolynomial_eval_one hn

theorem hilbert_derivative_paperPolynomial
    (m n : Nat) :
    derivative (NoncriticalBelyi.paperPolynomial m n) =
      C (m : ℚ) * X ^ (m - 1) * (X - 1) ^ n +
        C (n : ℚ) * X ^ m * (X - 1) ^ (n - 1) := by
  exact NoncriticalBelyi.derivative_paperPolynomial m n

theorem hilbert_derivative_paperPolynomial_factor
    {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    derivative (NoncriticalBelyi.paperPolynomial m n) =
      X ^ (m - 1) * (X - 1) ^ (n - 1) *
        (C (((m + n : Nat) : ℚ)) * X - C (m : ℚ)) := by
  exact NoncriticalBelyi.derivative_paperPolynomial_factor hm hn

theorem hilbert_derivative_paperPolynomial_eval_middle_eq_zero
    {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    (derivative (NoncriticalBelyi.paperPolynomial m n)).eval
      ((m : ℚ) / (((m + n : Nat) : ℚ))) = 0 := by
  exact NoncriticalBelyi.derivative_paperPolynomial_eval_middle_eq_zero hm hn

theorem hilbert_derivative_paperPolynomial_eval_eq_zero_iff
    {m n : Nat} (hm : 1 < m) (hn : 1 < n) (x : ℚ) :
    (derivative (NoncriticalBelyi.paperPolynomial m n)).eval x = 0 ↔
      x = 0 ∨ x = 1 ∨ x = (m : ℚ) / (((m + n : Nat) : ℚ)) := by
  exact NoncriticalBelyi.derivative_paperPolynomial_eval_eq_zero_iff hm hn x

theorem hilbert_paperPolynomial_basic_data
    {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    (NoncriticalBelyi.paperPolynomial m n).eval 0 = 0 ∧
      (NoncriticalBelyi.paperPolynomial m n).eval 1 = 0 ∧
      derivative (NoncriticalBelyi.paperPolynomial m n) =
        X ^ (m - 1) * (X - 1) ^ (n - 1) *
          (C (((m + n : Nat) : ℚ)) * X - C (m : ℚ)) ∧
      (derivative (NoncriticalBelyi.paperPolynomial m n)).eval
        ((m : ℚ) / (((m + n : Nat) : ℚ))) = 0 := by
  exact NoncriticalBelyi.paperPolynomial_basic_data hm hn

end MochizukiElementary
end HilbertSteps
end HilbertTest
