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

theorem belyi_aux_strict_mono_on_gt_one
    (hm : 1 <= m)
    (hn : 1 <= n)
    (halpha : 1 < alpha)
    (hbeta : alpha < beta) :
    belyiAux m n alpha < belyiAux m n beta := by
  have hratio_lower := belyi_aux_ratio_lower_bound (m := m) (n := n)
    hm hn halpha hbeta.le
  have halpha_pos : 0 < alpha := by nlinarith
  have hratio_gt_one : 1 < beta / alpha := by
    rw [lt_div_iff₀ halpha_pos]
    nlinarith
  have hratio_product_gt_one :
      1 < (beta / alpha) ^ m * ((beta - 1) / (alpha - 1)) ^ n :=
    lt_of_lt_of_le hratio_gt_one hratio_lower
  have hpos : 0 < belyiAux m n alpha :=
    belyi_aux_pos_of_gt_one (m := m) (n := n) halpha
  have hmul :
      belyiAux m n alpha * 1 <
        belyiAux m n alpha *
          ((beta / alpha) ^ m * ((beta - 1) / (alpha - 1)) ^ n) :=
    mul_lt_mul_of_pos_left hratio_product_gt_one hpos
  have heq : belyiAux m n beta =
      belyiAux m n alpha *
        ((beta / alpha) ^ m * ((beta - 1) / (alpha - 1)) ^ n) := by
    unfold belyiAux
    have ha0 : alpha ≠ 0 := by nlinarith
    have ha1 : alpha - 1 ≠ 0 := by nlinarith
    field_simp [ha0, ha1]
  nlinarith

theorem belyi_aux_half_ratio_ge_scale
    (hm : 1 <= m)
    (hn : 1 <= n)
    (hC : 2 <= C)
    (halpha : 1 < alpha)
    (hscale : beta / alpha >= C) :
    beta / alpha <= belyiAux m n beta / (2 * belyiAux m n alpha) := by
  have halpha_pos : 0 < alpha := by nlinarith
  have hbeta_gt_alpha : alpha < beta :=
    beta_gt_alpha_of_scale (alpha := alpha) (beta := beta) (C := C)
      hC halpha_pos hscale
  have hbeta_ge_alpha : alpha <= beta := hbeta_gt_alpha.le
  have hquad := belyi_aux_ratio_ge_quadratic (m := m) (n := n)
    hm hn halpha hbeta_ge_alpha
  have hscale_two : 2 <= beta / alpha := by nlinarith
  have hhalf : beta / alpha <= (1 / 2) * (beta / alpha) ^ 2 := by
    nlinarith [sq_nonneg (beta / alpha),
      mul_nonneg (by nlinarith : 0 <= beta / alpha)
        (by nlinarith : 0 <= beta / alpha - 2)]
  have hhalf_prod :
      beta / alpha <=
        (1 / 2) *
          ((beta / alpha) ^ m * ((beta - 1) / (alpha - 1)) ^ n) := by
    nlinarith
  have hpos : 0 < belyiAux m n alpha :=
    belyi_aux_pos_of_gt_one (m := m) (n := n) halpha
  have heq : belyiAux m n beta =
      belyiAux m n alpha *
        ((beta / alpha) ^ m * ((beta - 1) / (alpha - 1)) ^ n) := by
    unfold belyiAux
    have ha0 : alpha ≠ 0 := by nlinarith
    have ha1 : alpha - 1 ≠ 0 := by nlinarith
    field_simp [ha0, ha1]
  have hden_pos : 0 < 2 * belyiAux m n alpha := by positivity
  rw [le_div_iff₀ hden_pos]
  rw [heq]
  have hmul := mul_le_mul_of_nonneg_right hhalf_prod hden_pos.le
  nlinarith

theorem belyi_aux_ratio_ge_scale_of_gt_one
    (hm : 1 <= m)
    (hn : 1 <= n)
    (hC : 2 <= C)
    (halpha : 1 < alpha)
    (hscale : beta / alpha >= C) :
    C <= belyiAux m n beta / belyiAux m n alpha := by
  have hbeta_ge_alpha : alpha <= beta := by
    have halpha_pos : 0 < alpha := by nlinarith
    have hratio_one : 1 <= beta / alpha := by nlinarith
    rw [le_div_iff₀ halpha_pos] at hratio_one
    simpa using hratio_one
  have hratio_lower := belyi_aux_ratio_lower_bound (m := m) (n := n)
    hm hn halpha hbeta_ge_alpha
  have hC_le_prod :
      C <= (beta / alpha) ^ m * ((beta - 1) / (alpha - 1)) ^ n :=
    le_trans (by simpa [ge_iff_le] using hscale) hratio_lower
  have hpos : 0 < belyiAux m n alpha :=
    belyi_aux_pos_of_gt_one (m := m) (n := n) halpha
  have heq : belyiAux m n beta =
      belyiAux m n alpha *
        ((beta / alpha) ^ m * ((beta - 1) / (alpha - 1)) ^ n) := by
    unfold belyiAux
    have ha0 : alpha ≠ 0 := by nlinarith
    have ha1 : alpha - 1 ≠ 0 := by nlinarith
    field_simp [ha0, ha1]
  rw [le_div_iff₀ hpos]
  rw [heq]
  have hmul := mul_le_mul_of_nonneg_right hC_le_prod hpos.le
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

theorem belyi_aux_shifted_ratio_ge_scale_of_offset_le_value
    (hm : 1 <= m)
    (hn : 1 <= n)
    (hC : 2 <= C)
    (halpha : 1 < alpha)
    (hscale : beta / alpha >= C)
    {f0 : Real}
    (hf0_nonneg : 0 <= f0)
    (hf0_le_value : f0 <= belyiAux m n alpha) :
    C <= (belyiAux m n beta + f0) / (belyiAux m n alpha + f0) := by
  have halpha_pos : 0 < alpha := by nlinarith
  have hbeta_gt_alpha : alpha < beta :=
    beta_gt_alpha_of_scale (alpha := alpha) (beta := beta) (C := C)
      hC halpha_pos hscale
  have hbeta_gt_one : 1 < beta := by nlinarith
  have hA_nonneg : 0 <= belyiAux m n beta :=
    (belyi_aux_pos_of_gt_one (m := m) (n := n) hbeta_gt_one).le
  have hB_pos : 0 < belyiAux m n alpha :=
    belyi_aux_pos_of_gt_one (m := m) (n := n) halpha
  have hshift :=
    offset_ratio_ge_half_denominator_ratio
      (A := belyiAux m n beta) (B := belyiAux m n alpha) (t := f0)
      hA_nonneg hB_pos hf0_nonneg hf0_le_value
  have hratio :=
    belyi_aux_half_ratio_ge_scale (m := m) (n := n)
      hm hn hC halpha hscale
  have hC_le_half : C <= belyiAux m n beta / (2 * belyiAux m n alpha) := by
    exact le_trans (by simpa [ge_iff_le] using hscale) hratio
  exact le_trans hC_le_half hshift

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

theorem value_le_shifted_div_offset_of_offset_le_one
    {A t : Real}
    (hA_nonneg : 0 <= A)
    (ht_pos : 0 < t)
    (ht_le_one : t <= 1) :
    A <= (A + t) / t := by
  rw [le_div_iff₀ ht_pos]
  have hAt_le_A : A * t <= A := by
    simpa using mul_le_mul_of_nonneg_left ht_le_one hA_nonneg
  nlinarith

theorem value_le_div_of_pos_le_one
    {A B : Real}
    (hA_nonneg : 0 <= A)
    (hB_pos : 0 < B)
    (hB_le_one : B <= 1) :
    A <= A / B := by
  rw [le_div_iff₀ hB_pos]
  have hAB_le_A : A * B <= A := by
    simpa using mul_le_mul_of_nonneg_left hB_le_one hA_nonneg
  exact hAB_le_A

theorem belyi_aux_ratio_ge_scale_of_value_le_one
    (hm : 1 <= m)
    (hn : 1 <= n)
    (hC : 2 <= C)
    (hC_le_beta : C <= beta)
    {alpha : Real}
    (hvalue_pos : 0 < belyiAux m n alpha)
    (hvalue_le_one : belyiAux m n alpha <= 1) :
    C <= belyiAux m n beta / belyiAux m n alpha := by
  have hbeta_ge_two : 2 <= beta := le_trans hC hC_le_beta
  have hbeta_le_value :=
    beta_le_belyi_aux_of_beta_ge_two (m := m) (n := n)
      hm hn hbeta_ge_two
  have hvalue_nonneg : 0 <= belyiAux m n beta := by nlinarith
  have hvalue_div :=
    value_le_div_of_pos_le_one
      (A := belyiAux m n beta) (B := belyiAux m n alpha)
      hvalue_nonneg hvalue_pos hvalue_le_one
  exact le_trans hC_le_beta (le_trans hbeta_le_value hvalue_div)

theorem belyi_aux_shifted_zero_ratio_ge_scale
    (hm : 1 <= m)
    (hn : 1 <= n)
    (hC : 2 <= C)
    (hC_le_beta : C <= beta)
    {f0 : Real}
    (hf0_pos : 0 < f0)
    (hf0_le_quarter : f0 <= 1 / 4) :
    C <= (belyiAux m n beta + f0) / (0 + f0) := by
  have hbeta_ge_two : 2 <= beta := le_trans hC hC_le_beta
  have hA_nonneg : 0 <= belyiAux m n beta :=
    (belyi_aux_pos_of_gt_one (m := m) (n := n) (by nlinarith)).le
  have hshift :=
    value_le_shifted_div_offset_of_offset_le_one
      (A := belyiAux m n beta) (t := f0)
      hA_nonneg hf0_pos (by nlinarith)
  have hbeta_le_value :=
    beta_le_belyi_aux_of_beta_ge_two (m := m) (n := n)
      hm hn hbeta_ge_two
  exact le_trans hC_le_beta (le_trans hbeta_le_value (by simpa using hshift))

theorem belyi_aux_shifted_ratio_ge_scale_of_value_le_offset
    (hm : 1 <= m)
    (hn : 1 <= n)
    (hC : 2 <= C)
    (halpha : 1 < alpha)
    (hscale : beta / alpha >= C)
    {f0 : Real}
    (hf0_pos : 0 < f0)
    (hf0_le_quarter : f0 <= 1 / 4)
    (hvalue_le_f0 : belyiAux m n alpha <= f0) :
    C <= (belyiAux m n beta + f0) / (belyiAux m n alpha + f0) := by
  have halpha_pos : 0 < alpha := by nlinarith
  have hscale_le : C <= beta / alpha := by simpa [ge_iff_le] using hscale
  have hbeta_ge_mul : C * alpha <= beta := by
    have h := mul_le_mul_of_nonneg_right hscale_le halpha_pos.le
    rwa [div_mul_cancel₀ beta (ne_of_gt halpha_pos)] at h
  have hC_le_beta : C <= beta := by nlinarith
  have hbeta_ge_two : 2 <= beta := le_trans hC hC_le_beta
  have hbeta_gt_alpha : alpha < beta :=
    beta_gt_alpha_of_scale (alpha := alpha) (beta := beta) (C := C)
      hC halpha_pos hscale
  have hbeta_gt_one : 1 < beta := by nlinarith
  have hA_nonneg : 0 <= belyiAux m n beta :=
    (belyi_aux_pos_of_gt_one (m := m) (n := n) hbeta_gt_one).le
  have hB_nonneg : 0 <= belyiAux m n alpha :=
    (belyi_aux_pos_of_gt_one (m := m) (n := n) halpha).le
  have hshift :=
    offset_ratio_ge_div_two_offset
      (A := belyiAux m n beta) (B := belyiAux m n alpha) (t := f0)
      hA_nonneg hB_nonneg hf0_pos hvalue_le_f0
  have htwo_le :=
    two_mul_le_div_two_offset_of_offset_le_quarter
      (A := belyiAux m n beta) (t := f0)
      hA_nonneg hf0_pos hf0_le_quarter
  have hbeta_le_two :=
    beta_le_two_mul_belyi_aux_of_beta_ge_two (m := m) (n := n)
      hm hn hbeta_ge_two
  exact le_trans hC_le_beta (le_trans hbeta_le_two (le_trans htwo_le hshift))

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

theorem belyi_aux_beta_not_mem_image_of_finite_real_set
    (hm : 1 <= m)
    (hn : 1 <= n)
    (hC : 2 <= C)
    {S : Finset Real}
    (h_one_mem : 1 ∈ S)
    (hS_shape : ∀ x ∈ S, (0 <= x ∧ x <= 1) ∨ 1 < x)
    (hscale : ∀ x ∈ S, x ≠ 0 → beta / x >= C) :
    belyiAux m n beta ∉ S.image (fun x => belyiAux m n x) := by
  classical
  have hbeta_ge_two : 2 <= beta :=
    beta_ge_two_of_condition (beta := beta) (C := C) hC
      (hscale 1 h_one_mem (by norm_num))
  intro hmem
  rcases (Finset.mem_image.mp hmem) with ⟨alpha, halpha_mem, halpha_eq⟩
  rcases hS_shape alpha halpha_mem with hunit | hgt_one
  · have hlt := belyi_aux_beta_gt_unit_interval_value (m := m) (n := n)
      hm hn hbeta_ge_two hunit.1 hunit.2
    nlinarith
  · have halpha_ne_zero : alpha ≠ 0 := by nlinarith
    have hbeta_gt_alpha : alpha < beta :=
      beta_gt_alpha_of_scale (alpha := alpha) (beta := beta) (C := C)
        hC (by nlinarith) (hscale alpha halpha_mem halpha_ne_zero)
    have hlt := belyi_aux_strict_mono_on_gt_one (m := m) (n := n)
      hm hn hgt_one hbeta_gt_alpha
    nlinarith

theorem belyi_aux_finite_shifted_ratio_ge_scale
    (hm : 1 <= m)
    (hn : 1 <= n)
    (hC : 2 <= C)
    {S : Finset Real}
    (h_one_mem : 1 ∈ S)
    (hscale : ∀ x ∈ S, x ≠ 0 → beta / x >= C)
    {f0 : Real}
    (hf0_pos : 0 < f0)
    (hf0_le_quarter : f0 <= 1 / 4)
    (hcases : ∀ x ∈ S, belyiAux m n x + f0 ≠ 0 →
      belyiAux m n x = 0 ∨
        (1 < x ∧ f0 <= belyiAux m n x) ∨
        (1 < x ∧ belyiAux m n x <= f0)) :
    ∀ x ∈ S, belyiAux m n x + f0 ≠ 0 →
      C <= (belyiAux m n beta + f0) / (belyiAux m n x + f0) := by
  have hC_le_beta : C <= beta := by
    have h := hscale 1 h_one_mem (by norm_num)
    simpa [ge_iff_le] using h
  intro x hxS hden
  rcases hcases x hxS hden with hzero | hpositive
  · have hratio := belyi_aux_shifted_zero_ratio_ge_scale (m := m) (n := n)
      hm hn hC hC_le_beta hf0_pos hf0_le_quarter
    simpa [hzero] using hratio
  · rcases hpositive with hle_value | hvalue_le
    · exact belyi_aux_shifted_ratio_ge_scale_of_offset_le_value
        (m := m) (n := n) (alpha := x) (beta := beta) (C := C)
        hm hn hC hle_value.1
        (hscale x hxS (by nlinarith [hle_value.1]))
        hf0_pos.le hle_value.2
    · exact belyi_aux_shifted_ratio_ge_scale_of_value_le_offset
        (m := m) (n := n) (alpha := x) (beta := beta) (C := C)
        hm hn hC hvalue_le.1
        (hscale x hxS (by nlinarith [hvalue_le.1]))
        hf0_pos hf0_le_quarter hvalue_le.2

theorem belyi_aux_finite_ratio_ge_scale
    (hm : 1 <= m)
    (hn : 1 <= n)
    (hC : 2 <= C)
    {S : Finset Real}
    (h_one_mem : 1 ∈ S)
    (hscale : ∀ x ∈ S, x ≠ 0 → beta / x >= C)
    (hcases : ∀ x ∈ S, belyiAux m n x ≠ 0 →
      1 < x ∨ (0 < belyiAux m n x ∧ belyiAux m n x <= 1)) :
    ∀ x ∈ S, belyiAux m n x ≠ 0 →
      C <= belyiAux m n beta / belyiAux m n x := by
  have hC_le_beta : C <= beta := by
    have h := hscale 1 h_one_mem (by norm_num)
    simpa [ge_iff_le] using h
  intro x hxS hx_ne_zero_value
  rcases hcases x hxS hx_ne_zero_value with hgt_one | hunit_value
  · exact belyi_aux_ratio_ge_scale_of_gt_one (m := m) (n := n)
      (alpha := x) (beta := beta) (C := C)
      hm hn hC hgt_one (hscale x hxS (by nlinarith [hgt_one]))
  · exact belyi_aux_ratio_ge_scale_of_value_le_one (m := m) (n := n)
      (beta := beta) (C := C) (alpha := x)
      hm hn hC hC_le_beta hunit_value.1 hunit_value.2

end Lemma21Arithmetic

end NoncriticalBelyi
