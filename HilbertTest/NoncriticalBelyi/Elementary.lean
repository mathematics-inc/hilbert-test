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

end Lemma21Arithmetic

end NoncriticalBelyi
