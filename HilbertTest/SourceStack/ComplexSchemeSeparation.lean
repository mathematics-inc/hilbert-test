import HilbertTest.SourceStack.ComplexSeparation
import HilbertTest.SourceStack.SchemeProjectiveLineTransform

/-!
Scheme-carrier form of the complex reciprocal separation step.

`ComplexSeparation` proves the analytic/projective finite-set separation used
in Mochizuki's Lemma 2.3.  This file transports the strengthened projective
statement to the concrete scheme carrier of `P^1 = Proj K[X0,X1]`, using the
checked point bridge from the linear projective-line model.
-/

namespace HilbertTest
namespace SourceStack
namespace ComplexSchemeSeparation

open SchemeProjectiveLineTransform

noncomputable section

/-- Scheme-point form of the strengthened projective finite-set separation over
`ℂ`: choose a reciprocal translate whose distinguished affine point avoids the
scheme marked set `{0,1,∞}`, whose finite projective set maps away from scheme
infinity, and which retains the affine norm estimate. -/
theorem exists_schemeReciprocalTranslatePoint_separating_projective_finset_avoid_marked
    (S : Finset (ProjectiveLine.P1 ℂ)) (β : ℂ) (C : ℝ) (hC : 0 < C)
    (hβ : ProjectiveLine.affinePoint ℂ β ∉ S) :
    ∃ lam : ℂ,
      schemeReciprocalTranslatePoint ℂ lam
          (ProjectiveLine.affinePoint ℂ β) ∉
        SchemeProjectiveLine.markedSchemePointSet ℂ ∧
      (∀ p ∈ S,
        schemeReciprocalTranslatePoint ℂ lam p ≠
          SchemeProjectiveLine.infinityPoint ℂ) ∧
      ∀ α : ℂ, ProjectiveLine.affinePoint ℂ α ∈ S →
        C * ‖reciprocalTranslate lam α‖ ≤ ‖reciprocalTranslate lam β‖ := by
  rcases exists_projective_reciprocalTranslate_separating_projective_finset_avoid_marked
      S β C hC hβ with
    ⟨lam, hlamβ, hlamβone, _hβzero, _hβone, _hβinf, hSinf, hsep⟩
  refine ⟨lam, ?_, ?_, hsep⟩
  · exact
      schemeReciprocalTranslatePoint_affinePoint_not_mem_markedSchemePointSet
        ℂ lam β (Ne.symm hlamβ)
        (sub_ne_one_of_ne_sub_one ℂ lam β hlamβone)
  · intro p hp
    exact
      schemeReciprocalTranslatePoint_ne_infinity_of_linear_ne_infinity
        ℂ lam p (hSinf p hp)

/-- Image-finset package form of the scheme-point reciprocal separation over
`ℂ`: the finite transformed image avoids scheme infinity and has the same
cardinality as the source finite set. -/
theorem exists_schemeReciprocalTranslatePoint_separating_projective_finset_image_package
    [DecidableEq (SchemeProjectiveLine.P1 ℂ)]
    (S : Finset (ProjectiveLine.P1 ℂ)) (β : ℂ) (C : ℝ) (hC : 0 < C)
    (hβ : ProjectiveLine.affinePoint ℂ β ∉ S) :
    ∃ lam : ℂ,
      schemeReciprocalTranslatePoint ℂ lam
          (ProjectiveLine.affinePoint ℂ β) ∉
        SchemeProjectiveLine.markedSchemePointSet ℂ ∧
      (∀ q ∈ S.image (schemeReciprocalTranslatePoint ℂ lam),
        q ≠ SchemeProjectiveLine.infinityPoint ℂ) ∧
      (S.image (schemeReciprocalTranslatePoint ℂ lam)).card = S.card ∧
      ∀ α : ℂ, ProjectiveLine.affinePoint ℂ α ∈ S →
        C * ‖reciprocalTranslate lam α‖ ≤ ‖reciprocalTranslate lam β‖ := by
  rcases exists_schemeReciprocalTranslatePoint_separating_projective_finset_avoid_marked
      S β C hC hβ with
    ⟨lam, hβmarked, hSinf, hsep⟩
  refine ⟨lam, hβmarked, ?_, ?_, hsep⟩
  · intro q hq
    rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
    exact hSinf p hp
  · exact schemeReciprocalTranslatePoint_image_card ℂ lam S

/-- Image-finset package form of the scheme-point reciprocal separation over
`ℂ`, strengthened with the induction handoff that the distinguished point's
image is not in the transformed finite image. -/
theorem exists_schemeReciprocalTranslatePoint_separating_projective_finset_image_package_with_beta_not_mem
    [DecidableEq (SchemeProjectiveLine.P1 ℂ)]
    (S : Finset (ProjectiveLine.P1 ℂ)) (β : ℂ) (C : ℝ) (hC : 0 < C)
    (hβ : ProjectiveLine.affinePoint ℂ β ∉ S) :
    ∃ lam : ℂ,
      schemeReciprocalTranslatePoint ℂ lam
          (ProjectiveLine.affinePoint ℂ β) ∉
        SchemeProjectiveLine.markedSchemePointSet ℂ ∧
      schemeReciprocalTranslatePoint ℂ lam
          (ProjectiveLine.affinePoint ℂ β) ∉
        S.image (schemeReciprocalTranslatePoint ℂ lam) ∧
      (∀ q ∈ S.image (schemeReciprocalTranslatePoint ℂ lam),
        q ≠ SchemeProjectiveLine.infinityPoint ℂ) ∧
      (S.image (schemeReciprocalTranslatePoint ℂ lam)).card = S.card ∧
      ∀ α : ℂ, ProjectiveLine.affinePoint ℂ α ∈ S →
        C * ‖reciprocalTranslate lam α‖ ≤ ‖reciprocalTranslate lam β‖ := by
  rcases exists_schemeReciprocalTranslatePoint_separating_projective_finset_image_package
      S β C hC hβ with
    ⟨lam, hβmarked, hSinf, hcard, hsep⟩
  refine ⟨lam, hβmarked, ?_, hSinf, hcard, hsep⟩
  exact
    (schemeReciprocalTranslatePoint_not_mem_image_iff ℂ lam S
      (ProjectiveLine.affinePoint ℂ β)).2 hβ

/-- Rational scheme-point form of the strengthened projective finite-set
separation: if the distinguished point is rational, the reciprocal-translate
pole can be chosen rational while retaining the scheme marked-set avoidance. -/
theorem exists_schemeRationalReciprocalTranslatePoint_separating_projective_finset_avoid_marked
    (S : Finset (ProjectiveLine.P1 ℂ)) (β : ℚ) (C : ℝ) (hC : 0 < C)
    (hβ : ProjectiveLine.affinePoint ℂ (β : ℂ) ∉ S) :
    ∃ lam : ℚ,
      schemeReciprocalTranslatePoint ℂ (lam : ℂ)
          (ProjectiveLine.affinePoint ℂ (β : ℂ)) ∉
        SchemeProjectiveLine.markedSchemePointSet ℂ ∧
      (∀ p ∈ S,
        schemeReciprocalTranslatePoint ℂ (lam : ℂ) p ≠
          SchemeProjectiveLine.infinityPoint ℂ) ∧
      ∀ α : ℂ, ProjectiveLine.affinePoint ℂ α ∈ S →
        C * ‖reciprocalTranslate (lam : ℂ) α‖ ≤
          ‖reciprocalTranslate (lam : ℂ) (β : ℂ)‖ := by
  rcases
      exists_projective_rational_reciprocalTranslate_separating_projective_finset_avoid_marked
        S β C hC hβ with
    ⟨lam, hlamβ, hlamβone, _hβzero, _hβone, _hβinf, hSinf, hsep⟩
  refine ⟨lam, ?_, ?_, hsep⟩
  · exact
      schemeReciprocalTranslatePoint_affinePoint_not_mem_markedSchemePointSet
        ℂ (lam : ℂ) (β : ℂ) (Ne.symm hlamβ)
        (sub_ne_one_of_ne_sub_one ℂ (lam : ℂ) (β : ℂ) hlamβone)
  · intro p hp
    exact
      schemeReciprocalTranslatePoint_ne_infinity_of_linear_ne_infinity
        ℂ (lam : ℂ) p (hSinf p hp)

/-- Image-finset package form of the rational scheme-point reciprocal
separation: the finite transformed image avoids scheme infinity and has the
same cardinality as the source finite set. -/
theorem exists_schemeRationalReciprocalTranslatePoint_separating_projective_finset_image_package
    [DecidableEq (SchemeProjectiveLine.P1 ℂ)]
    (S : Finset (ProjectiveLine.P1 ℂ)) (β : ℚ) (C : ℝ) (hC : 0 < C)
    (hβ : ProjectiveLine.affinePoint ℂ (β : ℂ) ∉ S) :
    ∃ lam : ℚ,
      schemeReciprocalTranslatePoint ℂ (lam : ℂ)
          (ProjectiveLine.affinePoint ℂ (β : ℂ)) ∉
        SchemeProjectiveLine.markedSchemePointSet ℂ ∧
      (∀ q ∈ S.image (schemeReciprocalTranslatePoint ℂ (lam : ℂ)),
        q ≠ SchemeProjectiveLine.infinityPoint ℂ) ∧
      (S.image (schemeReciprocalTranslatePoint ℂ (lam : ℂ))).card = S.card ∧
      ∀ α : ℂ, ProjectiveLine.affinePoint ℂ α ∈ S →
        C * ‖reciprocalTranslate (lam : ℂ) α‖ ≤
          ‖reciprocalTranslate (lam : ℂ) (β : ℂ)‖ := by
  rcases
      exists_schemeRationalReciprocalTranslatePoint_separating_projective_finset_avoid_marked
        S β C hC hβ with
    ⟨lam, hβmarked, hSinf, hsep⟩
  refine ⟨lam, hβmarked, ?_, ?_, hsep⟩
  · intro q hq
    rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
    exact hSinf p hp
  · exact schemeReciprocalTranslatePoint_image_card ℂ (lam : ℂ) S

/-- Image-finset package form of the rational scheme-point reciprocal
separation, strengthened with the induction handoff that the distinguished
rational point's image is not in the transformed finite image. -/
theorem exists_schemeRationalReciprocalTranslatePoint_separating_projective_finset_image_package_with_beta_not_mem
    [DecidableEq (SchemeProjectiveLine.P1 ℂ)]
    (S : Finset (ProjectiveLine.P1 ℂ)) (β : ℚ) (C : ℝ) (hC : 0 < C)
    (hβ : ProjectiveLine.affinePoint ℂ (β : ℂ) ∉ S) :
    ∃ lam : ℚ,
      schemeReciprocalTranslatePoint ℂ (lam : ℂ)
          (ProjectiveLine.affinePoint ℂ (β : ℂ)) ∉
        SchemeProjectiveLine.markedSchemePointSet ℂ ∧
      schemeReciprocalTranslatePoint ℂ (lam : ℂ)
          (ProjectiveLine.affinePoint ℂ (β : ℂ)) ∉
        S.image (schemeReciprocalTranslatePoint ℂ (lam : ℂ)) ∧
      (∀ q ∈ S.image (schemeReciprocalTranslatePoint ℂ (lam : ℂ)),
        q ≠ SchemeProjectiveLine.infinityPoint ℂ) ∧
      (S.image (schemeReciprocalTranslatePoint ℂ (lam : ℂ))).card = S.card ∧
      ∀ α : ℂ, ProjectiveLine.affinePoint ℂ α ∈ S →
        C * ‖reciprocalTranslate (lam : ℂ) α‖ ≤
          ‖reciprocalTranslate (lam : ℂ) (β : ℂ)‖ := by
  rcases
      exists_schemeRationalReciprocalTranslatePoint_separating_projective_finset_image_package
        S β C hC hβ with
    ⟨lam, hβmarked, hSinf, hcard, hsep⟩
  refine ⟨lam, hβmarked, ?_, hSinf, hcard, hsep⟩
  exact
    (schemeReciprocalTranslatePoint_not_mem_image_iff ℂ (lam : ℂ) S
      (ProjectiveLine.affinePoint ℂ (β : ℂ))).2 hβ

end

end ComplexSchemeSeparation
end SourceStack
end HilbertTest
