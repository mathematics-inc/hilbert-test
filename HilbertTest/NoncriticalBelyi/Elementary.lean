import Mathlib

/-!
Lean formalization notes for `noncritical-belyi-maps_backtranslated.tex`.

This file contains checked arithmetic lemmas from Lemma 2.1 of Mochizuki's
``Noncritical Belyi Maps''.  The later statements in the TeX file quantify over
smooth proper connected curves, morphisms to projective space, ramification, and
Belyi maps.  Those declarations require a substantial algebraic-geometry API
that is not exposed as a direct Lean benchmark problem in the Hilbert repository,
so the verified development here isolates the elementary real-polynomial
subgoals that the paper uses before the geometric reductions.
-/

namespace NoncriticalBelyi

open Real

section Lemma21Arithmetic

variable {m n : Nat} {alpha beta C x : Real}

def belyiAux (m n : Nat) (x : Real) : Real :=
  x ^ m * (x - 1) ^ n

theorem beta_ge_two_of_condition
    (hC : 2 <= C)
    (h1 : beta / 1 >= C) :
    2 <= beta := by
  nlinarith

theorem beta_gt_alpha_of_scale
    (hC : 2 <= C)
    (halpha_pos : 0 < alpha)
    (hscale : beta / alpha >= C) :
    alpha < beta := by
  have hbeta_ge : beta >= C * alpha := by
    rw [ge_iff_le] at hscale
    have halpha_ne : alpha ≠ 0 := ne_of_gt halpha_pos
    have h := mul_le_mul_of_nonneg_right hscale (le_of_lt halpha_pos)
    rwa [div_mul_cancel₀ beta halpha_ne] at h
  have : 2 * alpha <= beta := by
    nlinarith
  nlinarith

theorem ratio_sub_one_ge_ratio
    (halpha : 1 < alpha)
    (hbeta : alpha <= beta) :
    beta / alpha <= (beta - 1) / (alpha - 1) := by
  have halpha_pos : 0 < alpha := by nlinarith
  have hden_pos : 0 < alpha - 1 := by nlinarith
  rw [div_le_div_iff₀ halpha_pos hden_pos]
  nlinarith

theorem ratio_ge_one
    (halpha : 0 < alpha)
    (hbeta : alpha <= beta) :
    1 <= beta / alpha := by
  rw [le_div_iff₀ halpha]
  simpa using hbeta

theorem shifted_ratio_ge_one
    (halpha : 1 < alpha)
    (hbeta : alpha <= beta) :
    1 <= (beta - 1) / (alpha - 1) := by
  have hden : 0 < alpha - 1 := by nlinarith
  rw [le_div_iff₀ hden]
  nlinarith

theorem pow_two_ge_self_of_ge_one
    (hy : 1 <= x) :
    x <= x ^ 2 := by
  nlinarith [sq_nonneg x]

theorem belyi_aux_ratio_lower_bound
    (hm : 1 <= m)
    (_hn : 1 <= n)
    (halpha : 1 < alpha)
    (hbeta : alpha <= beta) :
    (beta / alpha) <=
      (beta / alpha) ^ m * ((beta - 1) / (alpha - 1)) ^ n := by
  have hratio_one : 1 <= beta / alpha :=
    ratio_ge_one (by nlinarith) hbeta
  have hshift_one : 1 <= (beta - 1) / (alpha - 1) :=
    shifted_ratio_ge_one halpha hbeta
  have hratio_nonneg : 0 <= beta / alpha := by nlinarith
  have hshift_nonneg : 0 <= (beta - 1) / (alpha - 1) := by nlinarith
  have hratio_pow : (beta / alpha) <= (beta / alpha) ^ m := by
    exact le_self_pow₀ hratio_one (by omega)
  have hone_shift_pow : 1 <= ((beta - 1) / (alpha - 1)) ^ n := by
    exact one_le_pow₀ hshift_one
  calc
    beta / alpha <= (beta / alpha) ^ m := hratio_pow
    _ <= (beta / alpha) ^ m * ((beta - 1) / (alpha - 1)) ^ n := by
      nlinarith [mul_le_mul_of_nonneg_left hone_shift_pow (pow_nonneg hratio_nonneg m)]

theorem belyi_aux_ratio_ge_quadratic
    (hm : 1 <= m)
    (hn : 1 <= n)
    (halpha : 1 < alpha)
    (hbeta : alpha <= beta) :
    (beta / alpha) ^ 2 <=
      (beta / alpha) ^ m * ((beta - 1) / (alpha - 1)) ^ n := by
  have hratio_one : 1 <= beta / alpha :=
    ratio_ge_one (by nlinarith) hbeta
  have hshift_one : 1 <= (beta - 1) / (alpha - 1) :=
    shifted_ratio_ge_one halpha hbeta
  have hratio_nonneg : 0 <= beta / alpha := by nlinarith
  have hshift_ge_ratio :
      beta / alpha <= (beta - 1) / (alpha - 1) :=
    ratio_sub_one_ge_ratio halpha hbeta
  have hone_shift_pow : 1 <= ((beta - 1) / (alpha - 1)) ^ n := by
    exact one_le_pow₀ hshift_one
  have hratio_pow : (beta / alpha) ^ 1 <= (beta / alpha) ^ m := by
    exact pow_le_pow_right₀ hratio_one hm
  have hshift_pow :
      beta / alpha <= ((beta - 1) / (alpha - 1)) ^ n := by
    exact le_trans hshift_ge_ratio (le_self_pow₀ hshift_one (by omega))
  have hshift_pow' :
      (beta / alpha) ^ 1 <= ((beta - 1) / (alpha - 1)) ^ n := by
    simpa using hshift_pow
  calc
    (beta / alpha) ^ 2
        = (beta / alpha) ^ 1 * (beta / alpha) ^ 1 := by ring
    _ <= (beta / alpha) ^ m * ((beta - 1) / (alpha - 1)) ^ n := by
      exact mul_le_mul hratio_pow hshift_pow' (by positivity) (pow_nonneg hratio_nonneg m)

theorem belyi_aux_beta_gt_one
    (hm : 1 <= m)
    (_hn : 1 <= n)
    (hbeta : 2 <= beta) :
    1 < belyiAux m n beta := by
  unfold belyiAux
  have hbeta_one : 1 <= beta := by nlinarith
  have hshift_one : 1 <= beta - 1 := by nlinarith
  have hbeta_pow : 2 <= beta ^ m := by
    have hmono : beta ^ 1 <= beta ^ m := pow_le_pow_right₀ hbeta_one hm
    have : 2 <= beta ^ 1 := by simpa using hbeta
    exact le_trans this hmono
  have hshift_pow : 1 <= (beta - 1) ^ n := one_le_pow₀ hshift_one
  nlinarith [mul_le_mul hbeta_pow hshift_pow (by positivity) (by nlinarith)]

theorem beta_le_belyi_aux_of_beta_ge_two
    (hm : 1 <= m)
    (_hn : 1 <= n)
    (hbeta : 2 <= beta) :
    beta <= belyiAux m n beta := by
  unfold belyiAux
  have hbeta_one : 1 <= beta := by nlinarith
  have hbeta_nonneg : 0 <= beta := by nlinarith
  have hshift_one : 1 <= beta - 1 := by nlinarith
  have hbeta_pow : beta <= beta ^ m := by
    have hmono : beta ^ 1 <= beta ^ m := pow_le_pow_right₀ hbeta_one hm
    simpa using hmono
  have hshift_pow : 1 <= (beta - 1) ^ n := one_le_pow₀ hshift_one
  have hmul := mul_le_mul hbeta_pow hshift_pow zero_le_one (pow_nonneg hbeta_nonneg m)
  simpa using hmul

theorem beta_le_two_mul_belyi_aux_of_beta_ge_two
    (hm : 1 <= m)
    (hn : 1 <= n)
    (hbeta : 2 <= beta) :
    beta <= 2 * belyiAux m n beta := by
  have hmain := beta_le_belyi_aux_of_beta_ge_two (m := m) (n := n) hm hn hbeta
  have hnonneg : 0 <= belyiAux m n beta := by nlinarith [hmain, hbeta]
  nlinarith

theorem belyi_aux_pos_of_gt_one
    (hx : 1 < x) :
    0 < belyiAux m n x := by
  unfold belyiAux
  exact mul_pos (pow_pos (by nlinarith) m) (pow_pos (by nlinarith) n)

theorem belyi_aux_beta_ge_four_mul_of_scale
    (hm : 1 <= m)
    (hn : 1 <= n)
    (hC : 2 <= C)
    (halpha : 1 < alpha)
    (hscale : beta / alpha >= C) :
    4 * belyiAux m n alpha <= belyiAux m n beta := by
  have halpha_pos : 0 < alpha := by nlinarith
  have hbeta_ge_alpha : alpha <= beta := by
    have hβa : 1 <= beta / alpha := by nlinarith
    rw [le_div_iff₀ halpha_pos] at hβa
    simpa using hβa
  have hratio2 : 2 <= beta / alpha := by nlinarith
  have hquad4 : 4 <= (beta / alpha) ^ 2 := by
    nlinarith [sq_nonneg (beta / alpha - 2)]
  have hprod := belyi_aux_ratio_ge_quadratic (m := m) (n := n)
    hm hn halpha hbeta_ge_alpha
  have hprod4 :
      4 <= (beta / alpha) ^ m * ((beta - 1) / (alpha - 1)) ^ n :=
    le_trans hquad4 hprod
  have hpos : 0 < belyiAux m n alpha :=
    belyi_aux_pos_of_gt_one (m := m) (n := n) halpha
  have hmul := mul_le_mul_of_nonneg_left hprod4 hpos.le
  have heq : belyiAux m n beta =
      belyiAux m n alpha *
        ((beta / alpha) ^ m * ((beta - 1) / (alpha - 1)) ^ n) := by
    unfold belyiAux
    have ha0 : alpha ≠ 0 := by nlinarith
    have ha1 : alpha - 1 ≠ 0 := by nlinarith
    field_simp [ha0, ha1]
  nlinarith

theorem belyi_aux_beta_gt_of_scale
    (hm : 1 <= m)
    (hn : 1 <= n)
    (hC : 2 <= C)
    (halpha : 1 < alpha)
    (hscale : beta / alpha >= C) :
    belyiAux m n alpha < belyiAux m n beta := by
  have hscaled := belyi_aux_beta_ge_four_mul_of_scale (m := m) (n := n)
    hm hn hC halpha hscale
  have hpos : 0 < belyiAux m n alpha :=
    belyi_aux_pos_of_gt_one (m := m) (n := n) halpha
  nlinarith

theorem half_square_ge_self_of_ge_two
    {y : Real} (hy : 2 <= y) :
    y <= (1 / 2) * y ^ 2 := by
  nlinarith [sq_nonneg y, mul_nonneg (by nlinarith : 0 <= y) (by nlinarith : 0 <= y - 2)]

theorem offset_ratio_ge_half_denominator_ratio
    {A B t : Real}
    (hA_nonneg : 0 <= A)
    (hB_pos : 0 < B)
    (ht_nonneg : 0 <= t)
    (ht_le_B : t <= B) :
    A / (2 * B) <= (A + t) / (B + t) := by
  have hleft_pos : 0 < 2 * B := by positivity
  have hright_pos : 0 < B + t := by nlinarith
  rw [div_le_div_iff₀ hleft_pos hright_pos]
  have hA_gap : 0 <= A * (B - t) := by
    exact mul_nonneg hA_nonneg (sub_nonneg.mpr ht_le_B)
  have hBt : 0 <= B * t := by
    exact mul_nonneg hB_pos.le ht_nonneg
  nlinarith

theorem offset_ratio_ge_div_two_offset
    {A B t : Real}
    (hA_nonneg : 0 <= A)
    (hB_nonneg : 0 <= B)
    (ht_pos : 0 < t)
    (hB_le_t : B <= t) :
    A / (2 * t) <= (A + t) / (B + t) := by
  have hleft_pos : 0 < 2 * t := by positivity
  have hright_pos : 0 < B + t := by nlinarith
  rw [div_le_div_iff₀ hleft_pos hright_pos]
  have hAB_le_At : A * B <= A * t := by
    exact mul_le_mul_of_nonneg_left hB_le_t hA_nonneg
  have ht_sq_nonneg : 0 <= t * t := mul_nonneg ht_pos.le ht_pos.le
  nlinarith

theorem two_mul_le_div_two_offset_of_offset_le_quarter
    {A t : Real}
    (hA_nonneg : 0 <= A)
    (ht_pos : 0 < t)
    (ht_le_quarter : t <= 1 / 4) :
    2 * A <= A / (2 * t) := by
  have hden_pos : 0 < 2 * t := by positivity
  rw [le_div_iff₀ hden_pos]
  have hfour_t : 4 * t <= 1 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hfour_t hA_nonneg
  nlinarith

theorem abs_belyi_aux_le_one_on_unit_interval
    (_hm : 1 <= m)
    (_hn : 1 <= n)
    (hx0 : 0 <= x)
    (hx1 : x <= 1) :
    |belyiAux m n x| <= 1 := by
  unfold belyiAux
  have hx_nonneg : 0 <= x := hx0
  have hx_le_one : x <= 1 := hx1
  have hx_pow_le : x ^ m <= 1 := by
    exact pow_le_one₀ hx_nonneg hx_le_one
  have hshift_abs_le : |x - 1| <= 1 := by
    rw [abs_of_nonpos (by nlinarith)]
    nlinarith
  have hshift_pow_abs_le : |(x - 1) ^ n| <= 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg (x - 1)) hshift_abs_le
  have hx_pow_abs_le : |x ^ m| <= 1 := by
    rw [abs_pow, abs_of_nonneg hx_nonneg]
    exact hx_pow_le
  rw [abs_mul]
  nlinarith [mul_le_mul hx_pow_abs_le hshift_pow_abs_le (abs_nonneg ((x - 1) ^ n))
    (by nlinarith [abs_nonneg (x ^ m)])]

theorem belyi_aux_beta_gt_unit_interval_value
    (hm : 1 <= m)
    (hn : 1 <= n)
    (hbeta : 2 <= beta)
    (hx0 : 0 <= x)
    (hx1 : x <= 1) :
    belyiAux m n x < belyiAux m n beta := by
  have hb : 1 < belyiAux m n beta :=
    belyi_aux_beta_gt_one (m := m) (n := n) hm hn hbeta
  have hxabs : |belyiAux m n x| <= 1 :=
    abs_belyi_aux_le_one_on_unit_interval (m := m) (n := n) hm hn hx0 hx1
  have hxle : belyiAux m n x <= 1 := by
    exact le_trans (le_abs_self _) hxabs
  exact lt_of_le_of_lt hxle hb

theorem belyi_aux_beta_ne_unit_interval_value
    (hm : 1 <= m)
    (hn : 1 <= n)
    (hbeta : 2 <= beta)
    (hx0 : 0 <= x)
    (hx1 : x <= 1) :
    belyiAux m n beta ≠ belyiAux m n x := by
  have hlt := belyi_aux_beta_gt_unit_interval_value (m := m) (n := n)
    hm hn hbeta hx0 hx1
  exact ne_of_gt hlt

end Lemma21Arithmetic

end NoncriticalBelyi
