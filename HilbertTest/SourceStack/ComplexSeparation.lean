import HilbertTest.SourceStack.ProjectiveLine
import Mathlib

/-!
Finite-set separation on the complex affine line.

This is the analytic source step used in Mochizuki's Lemma 2.3: for a finite
set of points not containing `β`, choose a pole `λ` very close to `β` so that
the reciprocal translate `z ↦ (z - λ)⁻¹` is arbitrarily larger at `β` than at
the prescribed finite set.
-/

namespace HilbertTest
namespace SourceStack

noncomputable section

/-- The nearest-point distance from a point outside a finite complex set is
strictly positive. -/
theorem finset_complex_inf_norm_sub_pos
    (S : Finset ℂ) (β : ℂ) (hS : S.Nonempty) (hβ : β ∉ S) :
    0 < S.inf' hS (fun α : ℂ => ‖α - β‖) := by
  rcases Finset.exists_mem_eq_inf' hS (fun α : ℂ => ‖α - β‖) with
    ⟨α, hα, hmin⟩
  rw [hmin]
  refine norm_pos_iff.mpr ?_
  intro hzero
  apply hβ
  have hαβ : α = β := sub_eq_zero.mp hzero
  simpa [hαβ] using hα

/-- Given a finite set `S` not containing `β`, one can choose `λ` so close to
`β` that every point of `S` is at least `C` times farther from `λ` than `β` is.
-/
theorem exists_complex_point_nearby_separating_finset
    (S : Finset ℂ) (β : ℂ) (C : ℝ) (hC : 0 < C) (hβ : β ∉ S) :
    ∃ lam : ℂ,
      lam ≠ β ∧
      (∀ α ∈ S, lam ≠ α) ∧
      ∀ α ∈ S, C * ‖β - lam‖ ≤ ‖α - lam‖ := by
  by_cases hS : S.Nonempty
  · let d : ℝ := S.inf' hS (fun α : ℂ => ‖α - β‖)
    let ε : ℝ := d / (2 * (C + 1))
    let lam : ℂ := β + (ε : ℂ)
    have hd_pos : 0 < d := finset_complex_inf_norm_sub_pos S β hS hβ
    have hden_pos : 0 < 2 * (C + 1) := by nlinarith
    have hε_pos : 0 < ε := by
      exact div_pos hd_pos hden_pos
    have hε_nonneg : 0 ≤ ε := le_of_lt hε_pos
    have hε_ne_complex : (ε : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt hε_pos
    have hβlam_norm : ‖β - lam‖ = ε := by
      simp [lam, norm_neg, Real.norm_eq_abs, abs_of_nonneg hε_nonneg]
    have hlamβ_norm : ‖lam - β‖ = ε := by
      simp [lam, Real.norm_eq_abs, abs_of_nonneg hε_nonneg]
    have hε_mul : ε * (2 * (C + 1)) = d := by
      field_simp [ε, ne_of_gt hden_pos]
    have hCε_le_d_sub : C * ε ≤ d - ε := by
      nlinarith
    have hsep : ∀ α ∈ S, C * ‖β - lam‖ ≤ ‖α - lam‖ := by
      intro α hα
      have hd_le : d ≤ ‖α - β‖ := by
        simpa [d] using
          (Finset.inf'_le (s := S) (f := fun α : ℂ => ‖α - β‖) hα)
      have htri : ‖α - β‖ ≤ ‖α - lam‖ + ‖lam - β‖ := by
        simpa [dist_eq_norm] using dist_triangle α lam β
      have hd_sub_le : d - ε ≤ ‖α - lam‖ := by
        nlinarith
      rw [hβlam_norm]
      exact le_trans hCε_le_d_sub hd_sub_le
    refine ⟨lam, ?_, ?_, hsep⟩
    · intro hlamβ
      have : (ε : ℂ) = 0 := by
        have h := congrArg (fun z : ℂ => z - β) hlamβ
        simpa [lam] using h
      exact hε_ne_complex this
    · intro α hα hlamα
      have hβlam_pos : 0 < ‖β - lam‖ := by
        rw [hβlam_norm]
        exact hε_pos
      have hα_pos : 0 < ‖α - lam‖ := lt_of_lt_of_le (mul_pos hC hβlam_pos) (hsep α hα)
      have hα_zero : α - lam = 0 := by rw [hlamα, sub_self]
      have : ‖α - lam‖ = 0 := by simp [hα_zero]
      nlinarith
  · let lam : ℂ := β + 1
    refine ⟨lam, ?_, ?_, ?_⟩
    · intro hlamβ
      have : (1 : ℂ) = 0 := by
        have h := congrArg (fun z : ℂ => z - β) hlamβ
        simp [lam] at h
      exact one_ne_zero this
    · intro α hα
      exact (hS ⟨α, hα⟩).elim
    · intro α hα
      exact (hS ⟨α, hα⟩).elim

/-- The reciprocal translate used to separate a finite set from a distinguished
point. -/
def reciprocalTranslate (lam z : ℂ) : ℂ :=
  (z - lam)⁻¹

/-- Mochizuki's finite-set analytic separation step on `ℂ`: after choosing a
pole `λ`, the reciprocal translate is at least `C` times larger at `β` than at
all points of `S`. -/
theorem exists_reciprocal_translate_separating_finset
    (S : Finset ℂ) (β : ℂ) (C : ℝ) (hC : 0 < C) (hβ : β ∉ S) :
    ∃ lam : ℂ,
      lam ≠ β ∧
      (∀ α ∈ S, lam ≠ α) ∧
      ∀ α ∈ S,
        C * ‖reciprocalTranslate lam α‖ ≤ ‖reciprocalTranslate lam β‖ := by
  rcases exists_complex_point_nearby_separating_finset S β C hC hβ with
    ⟨lam, hlamβ, hlamS, hdist⟩
  refine ⟨lam, hlamβ, hlamS, ?_⟩
  intro α hα
  have hβ_norm_pos : 0 < ‖β - lam‖ := by
    exact norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hlamβ))
  have hα_norm_pos : 0 < ‖α - lam‖ := by
    exact norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm (hlamS α hα)))
  have hdiv : C / ‖α - lam‖ ≤ 1 / ‖β - lam‖ := by
    rw [div_le_div_iff₀ hα_norm_pos hβ_norm_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hdist α hα
  simpa [reciprocalTranslate, norm_inv, div_eq_mul_inv] using hdiv

/-- Projective-line form of Mochizuki Lemma 2.3 over `ℂ`: the chosen
reciprocal translate sends `β` to an affine point different from `0` and
`∞`, sends every point of `S` away from `∞`, and satisfies the same norm
separation estimate. -/
theorem exists_projective_reciprocalTranslate_separating_finset
    (S : Finset ℂ) (β : ℂ) (C : ℝ) (hC : 0 < C) (hβ : β ∉ S) :
    ∃ lam : ℂ,
      ProjectiveLine.reciprocalTranslate ℂ lam (ProjectiveLine.affinePoint ℂ β) ≠
        ProjectiveLine.zero ℂ ∧
      ProjectiveLine.reciprocalTranslate ℂ lam (ProjectiveLine.affinePoint ℂ β) ≠
        ProjectiveLine.infinity ℂ ∧
      (∀ α ∈ S,
        ProjectiveLine.reciprocalTranslate ℂ lam (ProjectiveLine.affinePoint ℂ α) ≠
          ProjectiveLine.infinity ℂ) ∧
      ∀ α ∈ S,
        C * ‖reciprocalTranslate lam α‖ ≤ ‖reciprocalTranslate lam β‖ := by
  rcases exists_reciprocal_translate_separating_finset S β C hC hβ with
    ⟨lam, hlamβ, hlamS, hsep⟩
  refine ⟨lam, ?_, ?_, ?_, hsep⟩
  · rw [ProjectiveLine.reciprocalTranslate_affinePoint_of_ne ℂ lam β
      (Ne.symm hlamβ)]
    exact ProjectiveLine.affinePoint_ne_zero ℂ
      (inv_ne_zero (sub_ne_zero.mpr (Ne.symm hlamβ)))
  · exact ProjectiveLine.reciprocalTranslate_affinePoint_ne_infinity ℂ
      lam β (Ne.symm hlamβ)
  · intro α hα
    exact ProjectiveLine.reciprocalTranslate_affinePoint_ne_infinity ℂ
      lam α (Ne.symm (hlamS α hα))

/-- Rational refinement of the reciprocal separation step: if the distinguished
point is rational, the pole may be chosen rational. -/
theorem exists_rational_reciprocal_translate_separating_finset
    (S : Finset ℂ) (β : ℚ) (C : ℝ) (hC : 0 < C) (hβ : (β : ℂ) ∉ S) :
    ∃ lam : ℚ,
      (lam : ℂ) ≠ (β : ℂ) ∧
      (∀ α ∈ S, (lam : ℂ) ≠ α) ∧
      ∀ α ∈ S,
        C * ‖reciprocalTranslate (lam : ℂ) α‖ ≤
          ‖reciprocalTranslate (lam : ℂ) (β : ℂ)‖ := by
  by_cases hS : S.Nonempty
  · let d : ℝ := S.inf' hS (fun α : ℂ => ‖α - (β : ℂ)‖)
    have hd_pos : 0 < d := finset_complex_inf_norm_sub_pos S (β : ℂ) hS hβ
    have hden_pos : 0 < 2 * (C + 1) := by nlinarith
    have hbound_pos : 0 < d / (2 * (C + 1)) := div_pos hd_pos hden_pos
    rcases exists_rat_btwn hbound_pos with ⟨ε, hε_pos, hε_bound⟩
    let lam : ℚ := β + ε
    let pole : ℂ := (lam : ℂ)
    have hε_nonneg : 0 ≤ (ε : ℝ) := le_of_lt hε_pos
    have hε_ne_complex : ((ε : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt hε_pos
    have hpole_eq : pole = (β : ℂ) + ((ε : ℝ) : ℂ) := by
      simp [pole, lam]
    have hβpole_norm : ‖(β : ℂ) - pole‖ = (ε : ℝ) := by
      simp [hpole_eq, norm_neg, Real.norm_eq_abs, abs_of_nonneg hε_nonneg]
    have hpoleβ_norm : ‖pole - (β : ℂ)‖ = (ε : ℝ) := by
      simp [hpole_eq, Real.norm_eq_abs, abs_of_nonneg hε_nonneg]
    have hε_mul_lt : (ε : ℝ) * (2 * (C + 1)) < d := by
      rwa [lt_div_iff₀ hden_pos] at hε_bound
    have hCε_le_d_sub : C * (ε : ℝ) ≤ d - (ε : ℝ) := by
      nlinarith
    have hsep_dist :
        ∀ α ∈ S, C * ‖(β : ℂ) - pole‖ ≤ ‖α - pole‖ := by
      intro α hα
      have hd_le : d ≤ ‖α - (β : ℂ)‖ := by
        simpa [d] using
          (Finset.inf'_le (s := S) (f := fun α : ℂ => ‖α - (β : ℂ)‖) hα)
      have htri : ‖α - (β : ℂ)‖ ≤ ‖α - pole‖ + ‖pole - (β : ℂ)‖ := by
        simpa [dist_eq_norm] using dist_triangle α pole (β : ℂ)
      have hd_sub_le : d - (ε : ℝ) ≤ ‖α - pole‖ := by
        nlinarith
      rw [hβpole_norm]
      exact le_trans hCε_le_d_sub hd_sub_le
    have hpole_ne_β : pole ≠ (β : ℂ) := by
      intro hpoleβ
      have : ((ε : ℝ) : ℂ) = 0 := by
        have h := congrArg (fun z : ℂ => z - (β : ℂ)) hpoleβ
        simpa [hpole_eq] using h
      exact hε_ne_complex this
    have hpole_ne_S : ∀ α ∈ S, pole ≠ α := by
      intro α hα hpoleα
      have hβpole_pos : 0 < ‖(β : ℂ) - pole‖ := by
        rw [hβpole_norm]
        exact hε_pos
      have hα_pos : 0 < ‖α - pole‖ :=
        lt_of_lt_of_le (mul_pos hC hβpole_pos) (hsep_dist α hα)
      have hα_zero : α - pole = 0 := by rw [← hpoleα, sub_self]
      have : ‖α - pole‖ = 0 := by simp [hα_zero]
      nlinarith
    refine ⟨lam, ?_, ?_, ?_⟩
    · simpa [pole] using hpole_ne_β
    · intro α hα
      simpa [pole] using hpole_ne_S α hα
    · intro α hα
      have hβ_norm_pos : 0 < ‖(β : ℂ) - pole‖ := by
        exact norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hpole_ne_β))
      have hα_norm_pos : 0 < ‖α - pole‖ := by
        exact norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm (hpole_ne_S α hα)))
      have hdiv : C / ‖α - pole‖ ≤ 1 / ‖(β : ℂ) - pole‖ := by
        rw [div_le_div_iff₀ hα_norm_pos hβ_norm_pos]
        simpa [mul_comm, mul_left_comm, mul_assoc] using hsep_dist α hα
      simpa [pole, reciprocalTranslate, norm_inv, div_eq_mul_inv] using hdiv
  · let lam : ℚ := β + 1
    refine ⟨lam, ?_, ?_, ?_⟩
    · intro hlamβ
      have : (1 : ℂ) = 0 := by
        have h := congrArg (fun z : ℂ => z - (β : ℂ)) hlamβ
        simp [lam] at h
      exact one_ne_zero this
    · intro α hα
      exact (hS ⟨α, hα⟩).elim
    · intro α hα
      exact (hS ⟨α, hα⟩).elim

/-- Projective-line rational refinement of Mochizuki Lemma 2.3: if the
distinguished point is rational, the reciprocal-translate pole may be chosen
rational, while the induced projective map sends the distinguished point away
from `0` and `∞` and sends the finite set away from `∞`. -/
theorem exists_projective_rational_reciprocalTranslate_separating_finset
    (S : Finset ℂ) (β : ℚ) (C : ℝ) (hC : 0 < C) (hβ : (β : ℂ) ∉ S) :
    ∃ lam : ℚ,
      ProjectiveLine.reciprocalTranslate ℂ (lam : ℂ)
          (ProjectiveLine.affinePoint ℂ (β : ℂ)) ≠
        ProjectiveLine.zero ℂ ∧
      ProjectiveLine.reciprocalTranslate ℂ (lam : ℂ)
          (ProjectiveLine.affinePoint ℂ (β : ℂ)) ≠
        ProjectiveLine.infinity ℂ ∧
      (∀ α ∈ S,
        ProjectiveLine.reciprocalTranslate ℂ (lam : ℂ)
            (ProjectiveLine.affinePoint ℂ α) ≠
          ProjectiveLine.infinity ℂ) ∧
      ∀ α ∈ S,
        C * ‖reciprocalTranslate (lam : ℂ) α‖ ≤
          ‖reciprocalTranslate (lam : ℂ) (β : ℂ)‖ := by
  rcases exists_rational_reciprocal_translate_separating_finset S β C hC hβ with
    ⟨lam, hlamβ, hlamS, hsep⟩
  refine ⟨lam, ?_, ?_, ?_, hsep⟩
  · exact ProjectiveLine.reciprocalTranslate_affinePoint_ne_zero ℂ
      (lam : ℂ) (β : ℂ) (Ne.symm hlamβ)
  · exact ProjectiveLine.reciprocalTranslate_affinePoint_ne_infinity ℂ
      (lam : ℂ) (β : ℂ) (Ne.symm hlamβ)
  · intro α hα
    exact ProjectiveLine.reciprocalTranslate_affinePoint_ne_infinity ℂ
      (lam : ℂ) α (Ne.symm (hlamS α hα))

/-- Projective finite-set form of Mochizuki Lemma 2.3 over `ℂ`: a finite set
of projective points may contain `∞`; the reciprocal translate sends `∞` to
`0`, sends every point of the finite set away from `∞`, and satisfies the
affine norm separation estimate on all affine members of the set. -/
theorem exists_projective_reciprocalTranslate_separating_projective_finset
    (S : Finset (ProjectiveLine.P1 ℂ)) (β : ℂ) (C : ℝ) (hC : 0 < C)
    (hβ : ProjectiveLine.affinePoint ℂ β ∉ S) :
    ∃ lam : ℂ,
      ProjectiveLine.reciprocalTranslate ℂ lam (ProjectiveLine.affinePoint ℂ β) ≠
        ProjectiveLine.zero ℂ ∧
      ProjectiveLine.reciprocalTranslate ℂ lam (ProjectiveLine.affinePoint ℂ β) ≠
        ProjectiveLine.infinity ℂ ∧
      (∀ p ∈ S,
        ProjectiveLine.reciprocalTranslate ℂ lam p ≠
          ProjectiveLine.infinity ℂ) ∧
      ∀ α : ℂ, ProjectiveLine.affinePoint ℂ α ∈ S →
        C * ‖reciprocalTranslate lam α‖ ≤ ‖reciprocalTranslate lam β‖ := by
  classical
  let Saff : Finset ℂ :=
    (S.filter fun p => p ≠ ProjectiveLine.infinity ℂ).image
      (ProjectiveLine.affineCoordOrZero ℂ)
  have hβaff : β ∉ Saff := by
    intro hβmem
    rcases Finset.mem_image.mp hβmem with ⟨p, hpfilter, hpcoord⟩
    rcases Finset.mem_filter.mp hpfilter with ⟨hpS, hpne⟩
    have hp_aff :
        ProjectiveLine.affinePoint ℂ (ProjectiveLine.affineCoordOrZero ℂ p) = p :=
      ProjectiveLine.affinePoint_affineCoordOrZero_of_ne_infinity ℂ hpne
    have hβp : ProjectiveLine.affinePoint ℂ β = p := by
      simpa [hpcoord] using hp_aff
    exact hβ (by simpa [hβp] using hpS)
  rcases exists_projective_reciprocalTranslate_separating_finset Saff β C hC hβaff with
    ⟨lam, hβzero, hβinf, hSaff_inf, hsep⟩
  refine ⟨lam, hβzero, hβinf, ?_, ?_⟩
  · intro p hpS
    by_cases hpinf : p = ProjectiveLine.infinity ℂ
    · rw [hpinf, ProjectiveLine.reciprocalTranslate_infinity]
      exact ProjectiveLine.zero_ne_infinity ℂ
    · have hpfilter :
          p ∈ S.filter (fun q => q ≠ ProjectiveLine.infinity ℂ) := by
        exact Finset.mem_filter.mpr ⟨hpS, hpinf⟩
      have hpcoord_mem : ProjectiveLine.affineCoordOrZero ℂ p ∈ Saff := by
        exact Finset.mem_image.mpr ⟨p, hpfilter, rfl⟩
      have hp_aff :
          ProjectiveLine.affinePoint ℂ (ProjectiveLine.affineCoordOrZero ℂ p) = p :=
        ProjectiveLine.affinePoint_affineCoordOrZero_of_ne_infinity ℂ hpinf
      have hnot := hSaff_inf (ProjectiveLine.affineCoordOrZero ℂ p) hpcoord_mem
      rwa [hp_aff] at hnot
  · intro α hαS
    have hneinf : ProjectiveLine.affinePoint ℂ α ≠ ProjectiveLine.infinity ℂ :=
      ProjectiveLine.affinePoint_ne_infinity ℂ α
    have hfilter :
        ProjectiveLine.affinePoint ℂ α ∈
          S.filter (fun p => p ≠ ProjectiveLine.infinity ℂ) := by
      exact Finset.mem_filter.mpr ⟨hαS, hneinf⟩
    have hαmem : α ∈ Saff := by
      refine Finset.mem_image.mpr ⟨ProjectiveLine.affinePoint ℂ α, hfilter, ?_⟩
      exact ProjectiveLine.affineCoordOrZero_affinePoint ℂ α
    exact hsep α hαmem

end

end SourceStack
end HilbertTest
