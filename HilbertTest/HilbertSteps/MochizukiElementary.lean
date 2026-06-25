import HilbertTest.NoncriticalBelyi.Elementary

/-!
Hilbert-facing targets for the checked elementary part of Mochizuki's
`Noncritical Belyi Maps`, Lemma 2.1.
-/

namespace HilbertTest
namespace HilbertSteps
namespace MochizukiElementary

open Real

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

theorem hilbert_abs_belyi_aux_le_one_on_unit_interval
    {m n : Nat} {x : Real}
    (hm : 1 <= m)
    (hn : 1 <= n)
    (hx0 : 0 <= x)
    (hx1 : x <= 1) :
    |NoncriticalBelyi.belyiAux m n x| <= 1 := by
  exact NoncriticalBelyi.abs_belyi_aux_le_one_on_unit_interval hm hn hx0 hx1

end MochizukiElementary
end HilbertSteps
end HilbertTest
