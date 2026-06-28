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

theorem hilbert_ratio_ge_one
    {alpha beta : Real}
    (halpha : 0 < alpha)
    (hbeta : alpha <= beta) :
    1 <= beta / alpha := by
  exact NoncriticalBelyi.ratio_ge_one halpha hbeta

theorem hilbert_shifted_ratio_ge_one
    {alpha beta : Real}
    (halpha : 1 < alpha)
    (hbeta : alpha <= beta) :
    1 <= (beta - 1) / (alpha - 1) := by
  exact NoncriticalBelyi.shifted_ratio_ge_one halpha hbeta

theorem hilbert_pow_two_ge_self_of_ge_one
    {x : Real}
    (hx : 1 <= x) :
    x <= x ^ 2 := by
  exact NoncriticalBelyi.pow_two_ge_self_of_ge_one hx

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

theorem hilbert_belyi_aux_zero
    {m n : Nat}
    (hm : 1 <= m) :
    NoncriticalBelyi.belyiAux m n 0 = 0 := by
  exact NoncriticalBelyi.belyi_aux_zero hm

theorem hilbert_belyi_aux_one
    {m n : Nat}
    (hn : 1 <= n) :
    NoncriticalBelyi.belyiAux m n 1 = 0 := by
  exact NoncriticalBelyi.belyi_aux_one hn

theorem hilbert_belyi_aux_pos_on_open_unit_interval_of_even
    {m n : Nat} {x : Real}
    (hm : 1 <= m)
    (hn_even : Even n)
    (hx0 : 0 < x)
    (hx1 : x < 1) :
    0 < NoncriticalBelyi.belyiAux m n x := by
  exact NoncriticalBelyi.belyi_aux_pos_on_open_unit_interval_of_even
    hm hn_even hx0 hx1

theorem hilbert_abs_belyi_aux_middle_eq_power_product
    {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    |NoncriticalBelyi.belyiAux m n ((m : Real) / ((m + n : Nat) : Real))| =
      ((m : Real) / ((m + n : Nat) : Real)) ^ m *
        ((n : Real) / ((m + n : Nat) : Real)) ^ n := by
  exact NoncriticalBelyi.abs_belyi_aux_middle_eq_power_product hm hn

theorem hilbert_abs_belyi_aux_middle_pos
    {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    0 <
      |NoncriticalBelyi.belyiAux m n
        ((m : Real) / ((m + n : Nat) : Real))| := by
  exact NoncriticalBelyi.abs_belyi_aux_middle_pos hm hn

theorem hilbert_abs_belyi_aux_middle_le_quarter
    {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    |NoncriticalBelyi.belyiAux m n
        ((m : Real) / ((m + n : Nat) : Real))| <= 1 / 4 := by
  exact NoncriticalBelyi.abs_belyi_aux_middle_le_quarter hm hn

theorem hilbert_belyi_aux_middle_neg_of_odd
    {m n : Nat}
    (hm : 0 < m)
    (hn : 0 < n)
    (hn_odd : Odd n) :
    NoncriticalBelyi.belyiAux m n
      ((m : Real) / ((m + n : Nat) : Real)) < 0 := by
  exact NoncriticalBelyi.belyi_aux_middle_neg_of_odd hm hn hn_odd

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

theorem hilbert_belyi_aux_half_ratio_ge_scale
    {m n : Nat} {alpha beta C : Real}
    (hm : 1 <= m)
    (hn : 1 <= n)
    (hC : 2 <= C)
    (halpha : 1 < alpha)
    (hscale : beta / alpha >= C) :
    beta / alpha <=
      NoncriticalBelyi.belyiAux m n beta /
        (2 * NoncriticalBelyi.belyiAux m n alpha) := by
  exact NoncriticalBelyi.belyi_aux_half_ratio_ge_scale
    hm hn hC halpha hscale

theorem hilbert_belyi_aux_ratio_ge_scale_of_gt_one
    {m n : Nat} {alpha beta C : Real}
    (hm : 1 <= m)
    (hn : 1 <= n)
    (hC : 2 <= C)
    (halpha : 1 < alpha)
    (hscale : beta / alpha >= C) :
    C <=
      NoncriticalBelyi.belyiAux m n beta /
        NoncriticalBelyi.belyiAux m n alpha := by
  exact NoncriticalBelyi.belyi_aux_ratio_ge_scale_of_gt_one
    hm hn hC halpha hscale

theorem hilbert_belyi_aux_shifted_ratio_ge_scale_of_offset_le_value
    {m n : Nat} {alpha beta C f0 : Real}
    (hm : 1 <= m)
    (hn : 1 <= n)
    (hC : 2 <= C)
    (halpha : 1 < alpha)
    (hscale : beta / alpha >= C)
    (hf0_nonneg : 0 <= f0)
    (hf0_le_value : f0 <= NoncriticalBelyi.belyiAux m n alpha) :
    C <=
      (NoncriticalBelyi.belyiAux m n beta + f0) /
        (NoncriticalBelyi.belyiAux m n alpha + f0) := by
  exact NoncriticalBelyi.belyi_aux_shifted_ratio_ge_scale_of_offset_le_value
    hm hn hC halpha hscale hf0_nonneg hf0_le_value

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

theorem hilbert_value_le_shifted_div_offset_of_offset_le_one
    {A t : Real}
    (hA_nonneg : 0 <= A)
    (ht_pos : 0 < t)
    (ht_le_one : t <= 1) :
    A <= (A + t) / t := by
  exact NoncriticalBelyi.value_le_shifted_div_offset_of_offset_le_one
    hA_nonneg ht_pos ht_le_one

theorem hilbert_value_le_div_of_pos_le_one
    {A B : Real}
    (hA_nonneg : 0 <= A)
    (hB_pos : 0 < B)
    (hB_le_one : B <= 1) :
    A <= A / B := by
  exact NoncriticalBelyi.value_le_div_of_pos_le_one
    hA_nonneg hB_pos hB_le_one

theorem hilbert_belyi_aux_ratio_ge_scale_of_value_le_one
    {m n : Nat} {alpha beta C : Real}
    (hm : 1 <= m)
    (hn : 1 <= n)
    (hC : 2 <= C)
    (hC_le_beta : C <= beta)
    (hvalue_pos : 0 < NoncriticalBelyi.belyiAux m n alpha)
    (hvalue_le_one : NoncriticalBelyi.belyiAux m n alpha <= 1) :
    C <=
      NoncriticalBelyi.belyiAux m n beta /
        NoncriticalBelyi.belyiAux m n alpha := by
  exact NoncriticalBelyi.belyi_aux_ratio_ge_scale_of_value_le_one
    hm hn hC hC_le_beta hvalue_pos hvalue_le_one

theorem hilbert_belyi_aux_shifted_zero_ratio_ge_scale
    {m n : Nat} {beta C f0 : Real}
    (hm : 1 <= m)
    (hn : 1 <= n)
    (hC : 2 <= C)
    (hC_le_beta : C <= beta)
    (hf0_pos : 0 < f0)
    (hf0_le_quarter : f0 <= 1 / 4) :
    C <= (NoncriticalBelyi.belyiAux m n beta + f0) / (0 + f0) := by
  exact NoncriticalBelyi.belyi_aux_shifted_zero_ratio_ge_scale
    hm hn hC hC_le_beta hf0_pos hf0_le_quarter

theorem hilbert_belyi_aux_shifted_ratio_ge_scale_of_value_le_offset
    {m n : Nat} {alpha beta C f0 : Real}
    (hm : 1 <= m)
    (hn : 1 <= n)
    (hC : 2 <= C)
    (halpha : 1 < alpha)
    (hscale : beta / alpha >= C)
    (hf0_pos : 0 < f0)
    (hf0_le_quarter : f0 <= 1 / 4)
    (hvalue_le_f0 : NoncriticalBelyi.belyiAux m n alpha <= f0) :
    C <=
      (NoncriticalBelyi.belyiAux m n beta + f0) /
        (NoncriticalBelyi.belyiAux m n alpha + f0) := by
  exact NoncriticalBelyi.belyi_aux_shifted_ratio_ge_scale_of_value_le_offset
    hm hn hC halpha hscale hf0_pos hf0_le_quarter hvalue_le_f0

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

theorem hilbert_belyi_aux_beta_not_mem_image_of_finite_real_set
    {m n : Nat} {beta C : Real}
    (hm : 1 <= m)
    (hn : 1 <= n)
    (hC : 2 <= C)
    {S : Finset Real}
    (h_one_mem : 1 ∈ S)
    (hS_shape : ∀ x ∈ S, (0 <= x ∧ x <= 1) ∨ 1 < x)
    (hscale : ∀ x ∈ S, x ≠ 0 → beta / x >= C) :
    NoncriticalBelyi.belyiAux m n beta ∉
      S.image (fun x => NoncriticalBelyi.belyiAux m n x) := by
  exact NoncriticalBelyi.belyi_aux_beta_not_mem_image_of_finite_real_set
    hm hn hC h_one_mem hS_shape hscale

theorem hilbert_belyi_aux_finite_shifted_ratio_ge_scale
    {m n : Nat} {beta C : Real}
    (hm : 1 <= m)
    (hn : 1 <= n)
    (hC : 2 <= C)
    {S : Finset Real}
    (h_one_mem : 1 ∈ S)
    (hscale : ∀ x ∈ S, x ≠ 0 → beta / x >= C)
    {f0 : Real}
    (hf0_pos : 0 < f0)
    (hf0_le_quarter : f0 <= 1 / 4)
    (hcases : ∀ x ∈ S, NoncriticalBelyi.belyiAux m n x + f0 ≠ 0 →
      NoncriticalBelyi.belyiAux m n x = 0 ∨
        (1 < x ∧ f0 <= NoncriticalBelyi.belyiAux m n x) ∨
        (1 < x ∧ NoncriticalBelyi.belyiAux m n x <= f0)) :
    ∀ x ∈ S, NoncriticalBelyi.belyiAux m n x + f0 ≠ 0 →
      C <=
        (NoncriticalBelyi.belyiAux m n beta + f0) /
          (NoncriticalBelyi.belyiAux m n x + f0) := by
  exact NoncriticalBelyi.belyi_aux_finite_shifted_ratio_ge_scale
    hm hn hC h_one_mem hscale hf0_pos hf0_le_quarter hcases

theorem hilbert_belyi_aux_finite_ratio_ge_scale
    {m n : Nat} {beta C : Real}
    (hm : 1 <= m)
    (hn : 1 <= n)
    (hC : 2 <= C)
    {S : Finset Real}
    (h_one_mem : 1 ∈ S)
    (hscale : ∀ x ∈ S, x ≠ 0 → beta / x >= C)
    (hcases : ∀ x ∈ S, NoncriticalBelyi.belyiAux m n x ≠ 0 →
      1 < x ∨
        (0 < NoncriticalBelyi.belyiAux m n x ∧
          NoncriticalBelyi.belyiAux m n x <= 1)) :
    ∀ x ∈ S, NoncriticalBelyi.belyiAux m n x ≠ 0 →
      C <=
        NoncriticalBelyi.belyiAux m n beta /
          NoncriticalBelyi.belyiAux m n x := by
  exact NoncriticalBelyi.belyi_aux_finite_ratio_ge_scale
    hm hn hC h_one_mem hscale hcases

theorem hilbert_belyi_aux_even_shape_ratio_cases
    {m n : Nat}
    (hm : 1 <= m)
    (hn : 1 <= n)
    (hn_even : Even n)
    {S : Finset Real}
    (hS_shape : ∀ x ∈ S,
      x = 0 ∨ x = 1 ∨ (0 < x ∧ x < 1) ∨ 1 < x) :
    ∀ x ∈ S, NoncriticalBelyi.belyiAux m n x ≠ 0 →
      1 < x ∨
        (0 < NoncriticalBelyi.belyiAux m n x ∧
          NoncriticalBelyi.belyiAux m n x <= 1) := by
  exact NoncriticalBelyi.belyi_aux_even_shape_ratio_cases
    hm hn hn_even hS_shape

theorem hilbert_belyi_aux_finite_ratio_ge_scale_of_even_shape
    {m n : Nat} {beta C : Real}
    (hm : 1 <= m)
    (hn : 1 <= n)
    (hn_even : Even n)
    (hC : 2 <= C)
    {S : Finset Real}
    (h_one_mem : 1 ∈ S)
    (hscale : ∀ x ∈ S, x ≠ 0 → beta / x >= C)
    (hS_shape : ∀ x ∈ S,
      x = 0 ∨ x = 1 ∨ (0 < x ∧ x < 1) ∨ 1 < x) :
    ∀ x ∈ S, NoncriticalBelyi.belyiAux m n x ≠ 0 →
      C <=
        NoncriticalBelyi.belyiAux m n beta /
          NoncriticalBelyi.belyiAux m n x := by
  exact NoncriticalBelyi.belyi_aux_finite_ratio_ge_scale_of_even_shape
    hm hn hn_even hC h_one_mem hscale hS_shape

theorem hilbert_belyi_aux_odd_middle_shape_shifted_cases
    {m n : Nat}
    (hm : 1 <= m)
    (hn : 1 <= n)
    (hn_odd : Odd n)
    {S : Finset Real}
    (hS_shape : ∀ x ∈ S,
      x = 0 ∨ x = 1 ∨
        x = (m : Real) / ((m + n : Nat) : Real) ∨ 1 < x) :
    ∀ x ∈ S,
      NoncriticalBelyi.belyiAux m n x +
          |NoncriticalBelyi.belyiAux m n
            ((m : Real) / ((m + n : Nat) : Real))| ≠ 0 →
        NoncriticalBelyi.belyiAux m n x = 0 ∨
          (1 < x ∧
            |NoncriticalBelyi.belyiAux m n
              ((m : Real) / ((m + n : Nat) : Real))| <=
                NoncriticalBelyi.belyiAux m n x) ∨
          (1 < x ∧
            NoncriticalBelyi.belyiAux m n x <=
              |NoncriticalBelyi.belyiAux m n
                ((m : Real) / ((m + n : Nat) : Real))|) := by
  exact NoncriticalBelyi.belyi_aux_odd_middle_shape_shifted_cases
    hm hn hn_odd hS_shape

theorem hilbert_belyi_aux_finite_shifted_ratio_ge_scale_of_odd_middle_shape
    {m n : Nat} {beta C : Real}
    (hm : 1 <= m)
    (hn : 1 <= n)
    (hn_odd : Odd n)
    (hC : 2 <= C)
    {S : Finset Real}
    (h_one_mem : 1 ∈ S)
    (hscale : ∀ x ∈ S, x ≠ 0 → beta / x >= C)
    (hS_shape : ∀ x ∈ S,
      x = 0 ∨ x = 1 ∨
        x = (m : Real) / ((m + n : Nat) : Real) ∨ 1 < x) :
    ∀ x ∈ S,
      NoncriticalBelyi.belyiAux m n x +
          |NoncriticalBelyi.belyiAux m n
            ((m : Real) / ((m + n : Nat) : Real))| ≠ 0 →
        C <=
          (NoncriticalBelyi.belyiAux m n beta +
              |NoncriticalBelyi.belyiAux m n
                ((m : Real) / ((m + n : Nat) : Real))|) /
            (NoncriticalBelyi.belyiAux m n x +
              |NoncriticalBelyi.belyiAux m n
                ((m : Real) / ((m + n : Nat) : Real))|) := by
  exact NoncriticalBelyi.belyi_aux_finite_shifted_ratio_ge_scale_of_odd_middle_shape
    hm hn hn_odd hC h_one_mem hscale hS_shape

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

theorem hilbert_derivative_paperPolynomial_eval_eq_zero_imp
    {m n : Nat} (hm : 0 < m) (hn : 0 < n) (x : ℚ)
    (hzero : (derivative (NoncriticalBelyi.paperPolynomial m n)).eval x = 0) :
    x = 0 ∨ x = 1 ∨ x = (m : ℚ) / (((m + n : Nat) : ℚ)) := by
  exact NoncriticalBelyi.derivative_paperPolynomial_eval_eq_zero_imp
    hm hn x hzero

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
