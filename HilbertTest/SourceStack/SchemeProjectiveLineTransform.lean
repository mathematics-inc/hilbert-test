import HilbertTest.SourceStack.ProjectiveLine
import HilbertTest.SourceStack.SchemeAffineLinePoints

/-!
Point-level scheme transport of the checked linear `P^1` transformations.

The full scheme-morphism construction for fractional-linear maps on
`P^1 = Proj K[X0,X1]` is still a later morphism-packaging step.  This file
records the point-level bridge already available from the concrete
linear-to-scheme point map: reciprocal translates and affine-linear maps on the
linear projective line transport to the expected scheme-carrier points.
-/

noncomputable section

namespace HilbertTest
namespace SourceStack
namespace SchemeProjectiveLineTransform

open SchemeAffineLinePoints

universe u

variable (K : Type u) [Field K]

/-- Scheme-carrier point map induced by the checked linear reciprocal translate
`x |-> 1 / (x - lambda)`. -/
def schemeReciprocalTranslatePoint
    (lambda : K) (p : ProjectiveLine.P1 K) : SchemeProjectiveLine.P1 K :=
  linearToSchemePoint K (ProjectiveLine.reciprocalTranslate K lambda p)

theorem schemeReciprocalTranslatePoint_injective
    (lambda : K) :
    Function.Injective (schemeReciprocalTranslatePoint K lambda) := by
  intro p q hpq
  have hlinear :
      ProjectiveLine.reciprocalTranslate K lambda p =
        ProjectiveLine.reciprocalTranslate K lambda q := by
    exact linearToSchemePoint_injective K
      (by simpa [schemeReciprocalTranslatePoint] using hpq)
  exact ProjectiveLine.reciprocalTranslate_injective K lambda hlinear

theorem schemeReciprocalTranslatePoint_eq_iff
    (lambda : K) (p q : ProjectiveLine.P1 K) :
    schemeReciprocalTranslatePoint K lambda p =
        schemeReciprocalTranslatePoint K lambda q ↔
      p = q := by
  exact ⟨fun h => schemeReciprocalTranslatePoint_injective K lambda h,
    fun h => by rw [h]⟩

/-- The reciprocal-translate scheme-point map preserves finset cardinality. -/
theorem schemeReciprocalTranslatePoint_image_card
    [DecidableEq (SchemeProjectiveLine.P1 K)]
    (lambda : K) (S : Finset (ProjectiveLine.P1 K)) :
    (S.image (schemeReciprocalTranslatePoint K lambda)).card = S.card :=
  Finset.card_image_of_injective S
    (schemeReciprocalTranslatePoint_injective K lambda)

/-- Membership in a finite image under a reciprocal translate is exactly
membership in the source finite set, using injectivity. -/
theorem schemeReciprocalTranslatePoint_mem_image_iff
    [DecidableEq (SchemeProjectiveLine.P1 K)]
    (lambda : K) (S : Finset (ProjectiveLine.P1 K))
    (p : ProjectiveLine.P1 K) :
    schemeReciprocalTranslatePoint K lambda p ∈
        S.image (schemeReciprocalTranslatePoint K lambda) ↔
      p ∈ S := by
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨q, hq, hpq⟩
    have hqp : q = p :=
      schemeReciprocalTranslatePoint_injective K lambda hpq
    simpa [hqp] using hq
  · intro hp
    exact Finset.mem_image_of_mem (schemeReciprocalTranslatePoint K lambda) hp

/-- A point outside the source finite set remains outside the reciprocal
translated finite image. -/
theorem schemeReciprocalTranslatePoint_not_mem_image_iff
    [DecidableEq (SchemeProjectiveLine.P1 K)]
    (lambda : K) (S : Finset (ProjectiveLine.P1 K))
    (p : ProjectiveLine.P1 K) :
    schemeReciprocalTranslatePoint K lambda p ∉
        S.image (schemeReciprocalTranslatePoint K lambda) ↔
      p ∉ S := by
  exact not_congr
    (schemeReciprocalTranslatePoint_mem_image_iff K lambda S p)

/-- The reciprocal-translated finite image lies in the marked scheme triple
exactly when every source point maps to the marked scheme triple. -/
theorem schemeReciprocalTranslatePoint_image_subset_markedSchemePointSet_iff
    [DecidableEq (SchemeProjectiveLine.P1 K)]
    (lambda : K) (S : Finset (ProjectiveLine.P1 K)) :
    (S.image (schemeReciprocalTranslatePoint K lambda) :
        Set (SchemeProjectiveLine.P1 K)) ⊆
      SchemeProjectiveLine.markedSchemePointSet K ↔
      ∀ p ∈ S,
        schemeReciprocalTranslatePoint K lambda p ∈
          SchemeProjectiveLine.markedSchemePointSet K := by
  constructor
  · intro hS p hp
    exact hS (Finset.mem_image_of_mem
      (schemeReciprocalTranslatePoint K lambda) hp)
  · intro hS q hq
    rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
    exact hS p hp

/-- If a finite set maps pointwise away from the marked scheme triple under a
reciprocal translate, then its image finset is contained in the marked
complement. -/
theorem schemeReciprocalTranslatePoint_image_subset_markedSchemePointSet_compl
    [DecidableEq (SchemeProjectiveLine.P1 K)]
    (lambda : K) (S : Finset (ProjectiveLine.P1 K))
    (hS : ∀ p ∈ S,
      schemeReciprocalTranslatePoint K lambda p ∉
        SchemeProjectiveLine.markedSchemePointSet K) :
    (S.image (schemeReciprocalTranslatePoint K lambda) :
        Set (SchemeProjectiveLine.P1 K)) ⊆
      (SchemeProjectiveLine.markedSchemePointSet K)ᶜ := by
  intro q hq
  rw [Set.mem_compl_iff]
  rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
  exact hS p hp

/-- The reciprocal-translated finite image lies in the marked complement
exactly when every source point maps away from the marked scheme triple. -/
theorem schemeReciprocalTranslatePoint_image_subset_markedSchemePointSet_compl_iff
    [DecidableEq (SchemeProjectiveLine.P1 K)]
    (lambda : K) (S : Finset (ProjectiveLine.P1 K)) :
    (S.image (schemeReciprocalTranslatePoint K lambda) :
        Set (SchemeProjectiveLine.P1 K)) ⊆
      (SchemeProjectiveLine.markedSchemePointSet K)ᶜ ↔
      ∀ p ∈ S,
        schemeReciprocalTranslatePoint K lambda p ∉
          SchemeProjectiveLine.markedSchemePointSet K := by
  constructor
  · intro hS p hp hmarked
    exact (hS (Finset.mem_image_of_mem
      (schemeReciprocalTranslatePoint K lambda) hp)) hmarked
  · intro hS
    exact schemeReciprocalTranslatePoint_image_subset_markedSchemePointSet_compl
      K lambda S hS

/-- Avoiding scheme infinity on the reciprocal-translated finite image is
equivalent to pointwise avoidance on the source finite set. -/
theorem schemeReciprocalTranslatePoint_image_avoids_infinity_iff
    [DecidableEq (SchemeProjectiveLine.P1 K)]
    (lambda : K) (S : Finset (ProjectiveLine.P1 K)) :
    (∀ q ∈ S.image (schemeReciprocalTranslatePoint K lambda),
      q ≠ SchemeProjectiveLine.infinityPoint K) ↔
      ∀ p ∈ S,
        schemeReciprocalTranslatePoint K lambda p ≠
          SchemeProjectiveLine.infinityPoint K := by
  constructor
  · intro hS p hp
    exact hS (schemeReciprocalTranslatePoint K lambda p)
      (Finset.mem_image_of_mem (schemeReciprocalTranslatePoint K lambda) hp)
  · intro hS q hq
    rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
    exact hS p hp

theorem schemeReciprocalTranslatePoint_affinePoint_of_ne
    (lambda r : K) (hr : r ≠ lambda) :
    schemeReciprocalTranslatePoint K lambda (ProjectiveLine.affinePoint K r) =
      SchemeAffineLinePoints.affinePoint K ((r - lambda)⁻¹) := by
  rw [schemeReciprocalTranslatePoint,
    ProjectiveLine.reciprocalTranslate_affinePoint_of_ne K lambda r hr,
    linearToSchemePoint_affinePoint]

theorem sub_ne_one_of_ne_sub_one
    (lambda r : K) (h : lambda ≠ r - 1) :
    r - lambda ≠ 1 := by
  intro hdiff
  apply h
  calc
    lambda = r - 1 := by
      rw [eq_sub_iff_add_eq]
      rw [add_comm]
      exact (sub_eq_iff_eq_add.mp hdiff).symm

theorem inv_sub_eq_one_iff_of_ne
    (lambda r : K) (hr : r ≠ lambda) :
    (r - lambda)⁻¹ = (1 : K) ↔ r - lambda = 1 := by
  constructor
  · intro hinv
    have h0 : r - lambda ≠ 0 := sub_ne_zero.mpr hr
    have hmul := congrArg (fun x : K => (r - lambda) * x) hinv
    have hrl : (1 : K) = r - lambda := by
      simpa [h0] using hmul
    exact hrl.symm
  · intro h
    rw [h]
    simp

theorem inv_sub_ne_one_of_ne_of_sub_ne_one
    (lambda r : K) (hr : r ≠ lambda) (hr1 : r - lambda ≠ 1) :
    (r - lambda)⁻¹ ≠ (1 : K) := by
  intro hinv
  exact hr1 ((inv_sub_eq_one_iff_of_ne K lambda r hr).1 hinv)

theorem schemeReciprocalTranslatePoint_affinePoint_ne_zero
    (lambda r : K) (hr : r ≠ lambda) :
    schemeReciprocalTranslatePoint K lambda
        (ProjectiveLine.affinePoint K r) ≠
      SchemeProjectiveLine.zeroPoint K := by
  rw [schemeReciprocalTranslatePoint_affinePoint_of_ne K lambda r hr]
  exact SchemeAffineLinePoints.affinePoint_ne_zero K
    (inv_ne_zero (sub_ne_zero.mpr hr))

theorem schemeReciprocalTranslatePoint_affinePoint_ne_one
    (lambda r : K) (hr : r ≠ lambda) (hr1 : r - lambda ≠ 1) :
    schemeReciprocalTranslatePoint K lambda
        (ProjectiveLine.affinePoint K r) ≠
      SchemeProjectiveLine.onePoint K := by
  rw [schemeReciprocalTranslatePoint_affinePoint_of_ne K lambda r hr]
  exact SchemeAffineLinePoints.affinePoint_ne_one K
    (inv_sub_ne_one_of_ne_of_sub_ne_one K lambda r hr hr1)

theorem schemeReciprocalTranslatePoint_affinePoint_ne_infinity
    (lambda r : K) (hr : r ≠ lambda) :
    schemeReciprocalTranslatePoint K lambda
        (ProjectiveLine.affinePoint K r) ≠
      SchemeProjectiveLine.infinityPoint K := by
  rw [schemeReciprocalTranslatePoint_affinePoint_of_ne K lambda r hr]
  exact SchemeAffineLinePoints.affinePoint_ne_infinity K _

theorem schemeReciprocalTranslatePoint_affinePoint_mem_markedSchemePointSet_iff_of_ne
    (lambda r : K) (hr : r ≠ lambda) :
    schemeReciprocalTranslatePoint K lambda
        (ProjectiveLine.affinePoint K r) ∈
      SchemeProjectiveLine.markedSchemePointSet K ↔
        r - lambda = 1 := by
  rw [schemeReciprocalTranslatePoint_affinePoint_of_ne K lambda r hr]
  rw [SchemeAffineLinePoints.affinePoint_mem_markedSchemePointSet_iff K]
  constructor
  · rintro (hzero | hone)
    · exact False.elim ((inv_ne_zero (sub_ne_zero.mpr hr)) hzero)
    · exact (inv_sub_eq_one_iff_of_ne K lambda r hr).1 hone
  · intro hone
    exact Or.inr ((inv_sub_eq_one_iff_of_ne K lambda r hr).2 hone)

theorem schemeReciprocalTranslatePoint_affinePoint_not_mem_markedSchemePointSet_iff_of_ne
    (lambda r : K) (hr : r ≠ lambda) :
    schemeReciprocalTranslatePoint K lambda
        (ProjectiveLine.affinePoint K r) ∉
      SchemeProjectiveLine.markedSchemePointSet K ↔
        r - lambda ≠ 1 := by
  exact not_congr
    (schemeReciprocalTranslatePoint_affinePoint_mem_markedSchemePointSet_iff_of_ne
      K lambda r hr)

theorem schemeReciprocalTranslatePoint_affinePoint_not_mem_markedSchemePointSet
    (lambda r : K) (hr : r ≠ lambda) (hr1 : r - lambda ≠ 1) :
    schemeReciprocalTranslatePoint K lambda
        (ProjectiveLine.affinePoint K r) ∉
      SchemeProjectiveLine.markedSchemePointSet K := by
  exact
    (schemeReciprocalTranslatePoint_affinePoint_not_mem_markedSchemePointSet_iff_of_ne
      K lambda r hr).2 hr1

theorem schemeReciprocalTranslatePoint_affinePoint_pole
    (lambda : K) :
    schemeReciprocalTranslatePoint K lambda
        (ProjectiveLine.affinePoint K lambda) =
      SchemeProjectiveLine.infinityPoint K := by
  rw [schemeReciprocalTranslatePoint,
    ProjectiveLine.reciprocalTranslate_affinePoint_pole,
    linearToSchemePoint_infinity]

theorem schemeReciprocalTranslatePoint_infinity
    (lambda : K) :
    schemeReciprocalTranslatePoint K lambda (ProjectiveLine.infinity K) =
      SchemeProjectiveLine.zeroPoint K := by
  rw [schemeReciprocalTranslatePoint, ProjectiveLine.reciprocalTranslate_infinity,
    linearToSchemePoint_zero]

theorem schemeReciprocalTranslatePoint_ne_infinity_of_linear_ne_infinity
    (lambda : K) (p : ProjectiveLine.P1 K)
    (h : ProjectiveLine.reciprocalTranslate K lambda p ≠
      ProjectiveLine.infinity K) :
    schemeReciprocalTranslatePoint K lambda p ≠
      SchemeProjectiveLine.infinityPoint K := by
  intro hp
  have hscheme :
      linearToSchemePoint K (ProjectiveLine.reciprocalTranslate K lambda p) =
        linearToSchemePoint K (ProjectiveLine.infinity K) := by
    simpa [schemeReciprocalTranslatePoint, linearToSchemePoint_infinity] using hp
  exact h (linearToSchemePoint_injective K hscheme)

/-- Scheme-carrier point map induced by the checked affine-linear map
`x |-> a * x + b` on the linear projective line. -/
def schemeAffineLinearPoint
    (a b : K) (ha : a ≠ 0) (p : ProjectiveLine.P1 K) :
    SchemeProjectiveLine.P1 K :=
  linearToSchemePoint K (ProjectiveLine.affineLinearMap K a b ha p)

theorem schemeAffineLinearPoint_injective
    (a b : K) (ha : a ≠ 0) :
    Function.Injective (schemeAffineLinearPoint K a b ha) := by
  intro p q hpq
  have hlinear :
      ProjectiveLine.affineLinearMap K a b ha p =
        ProjectiveLine.affineLinearMap K a b ha q := by
    exact linearToSchemePoint_injective K
      (by simpa [schemeAffineLinearPoint] using hpq)
  exact ProjectiveLine.affineLinearMap_injective K ha hlinear

theorem schemeAffineLinearPoint_eq_iff
    (a b : K) (ha : a ≠ 0) (p q : ProjectiveLine.P1 K) :
    schemeAffineLinearPoint K a b ha p =
        schemeAffineLinearPoint K a b ha q ↔
      p = q := by
  exact ⟨fun h => schemeAffineLinearPoint_injective K a b ha h,
    fun h => by rw [h]⟩

/-- The affine-linear scheme-point map preserves finset cardinality. -/
theorem schemeAffineLinearPoint_image_card
    [DecidableEq (SchemeProjectiveLine.P1 K)]
    (a b : K) (ha : a ≠ 0) (S : Finset (ProjectiveLine.P1 K)) :
    (S.image (schemeAffineLinearPoint K a b ha)).card = S.card :=
  Finset.card_image_of_injective S
    (schemeAffineLinearPoint_injective K a b ha)

/-- Membership in a finite image under an affine-linear transform is exactly
membership in the source finite set, using injectivity. -/
theorem schemeAffineLinearPoint_mem_image_iff
    [DecidableEq (SchemeProjectiveLine.P1 K)]
    (a b : K) (ha : a ≠ 0) (S : Finset (ProjectiveLine.P1 K))
    (p : ProjectiveLine.P1 K) :
    schemeAffineLinearPoint K a b ha p ∈
        S.image (schemeAffineLinearPoint K a b ha) ↔
      p ∈ S := by
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨q, hq, hpq⟩
    have hqp : q = p :=
      schemeAffineLinearPoint_injective K a b ha hpq
    simpa [hqp] using hq
  · intro hp
    exact Finset.mem_image_of_mem (schemeAffineLinearPoint K a b ha) hp

/-- A point outside the source finite set remains outside the affine-linear
transformed finite image. -/
theorem schemeAffineLinearPoint_not_mem_image_iff
    [DecidableEq (SchemeProjectiveLine.P1 K)]
    (a b : K) (ha : a ≠ 0) (S : Finset (ProjectiveLine.P1 K))
    (p : ProjectiveLine.P1 K) :
    schemeAffineLinearPoint K a b ha p ∉
        S.image (schemeAffineLinearPoint K a b ha) ↔
      p ∉ S := by
  exact not_congr
    (schemeAffineLinearPoint_mem_image_iff K a b ha S p)

/-- The affine-linear finite image lies in the marked scheme triple exactly
when every source point maps to the marked scheme triple. -/
theorem schemeAffineLinearPoint_image_subset_markedSchemePointSet_iff
    [DecidableEq (SchemeProjectiveLine.P1 K)]
    (a b : K) (ha : a ≠ 0) (S : Finset (ProjectiveLine.P1 K)) :
    (S.image (schemeAffineLinearPoint K a b ha) :
        Set (SchemeProjectiveLine.P1 K)) ⊆
      SchemeProjectiveLine.markedSchemePointSet K ↔
      ∀ p ∈ S,
        schemeAffineLinearPoint K a b ha p ∈
          SchemeProjectiveLine.markedSchemePointSet K := by
  constructor
  · intro hS p hp
    exact hS (Finset.mem_image_of_mem
      (schemeAffineLinearPoint K a b ha) hp)
  · intro hS q hq
    rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
    exact hS p hp

/-- If a finite set maps pointwise away from the marked scheme triple under an
affine-linear map, then its image finset is contained in the marked
complement. -/
theorem schemeAffineLinearPoint_image_subset_markedSchemePointSet_compl
    [DecidableEq (SchemeProjectiveLine.P1 K)]
    (a b : K) (ha : a ≠ 0) (S : Finset (ProjectiveLine.P1 K))
    (hS : ∀ p ∈ S,
      schemeAffineLinearPoint K a b ha p ∉
        SchemeProjectiveLine.markedSchemePointSet K) :
    (S.image (schemeAffineLinearPoint K a b ha) :
        Set (SchemeProjectiveLine.P1 K)) ⊆
      (SchemeProjectiveLine.markedSchemePointSet K)ᶜ := by
  intro q hq
  rw [Set.mem_compl_iff]
  rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
  exact hS p hp

/-- The affine-linear finite image lies in the marked complement exactly when
every source point maps away from the marked scheme triple. -/
theorem schemeAffineLinearPoint_image_subset_markedSchemePointSet_compl_iff
    [DecidableEq (SchemeProjectiveLine.P1 K)]
    (a b : K) (ha : a ≠ 0) (S : Finset (ProjectiveLine.P1 K)) :
    (S.image (schemeAffineLinearPoint K a b ha) :
        Set (SchemeProjectiveLine.P1 K)) ⊆
      (SchemeProjectiveLine.markedSchemePointSet K)ᶜ ↔
      ∀ p ∈ S,
        schemeAffineLinearPoint K a b ha p ∉
          SchemeProjectiveLine.markedSchemePointSet K := by
  constructor
  · intro hS p hp hmarked
    exact (hS (Finset.mem_image_of_mem
      (schemeAffineLinearPoint K a b ha) hp)) hmarked
  · intro hS
    exact schemeAffineLinearPoint_image_subset_markedSchemePointSet_compl
      K a b ha S hS

/-- Avoiding scheme infinity on the affine-linear finite image is equivalent
to pointwise avoidance on the source finite set. -/
theorem schemeAffineLinearPoint_image_avoids_infinity_iff
    [DecidableEq (SchemeProjectiveLine.P1 K)]
    (a b : K) (ha : a ≠ 0) (S : Finset (ProjectiveLine.P1 K)) :
    (∀ q ∈ S.image (schemeAffineLinearPoint K a b ha),
      q ≠ SchemeProjectiveLine.infinityPoint K) ↔
      ∀ p ∈ S,
        schemeAffineLinearPoint K a b ha p ≠
          SchemeProjectiveLine.infinityPoint K := by
  constructor
  · intro hS p hp
    exact hS (schemeAffineLinearPoint K a b ha p)
      (Finset.mem_image_of_mem (schemeAffineLinearPoint K a b ha) hp)
  · intro hS q hq
    rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
    exact hS p hp

theorem schemeAffineLinearPoint_affinePoint
    (a b : K) (ha : a ≠ 0) (r : K) :
    schemeAffineLinearPoint K a b ha (ProjectiveLine.affinePoint K r) =
      SchemeAffineLinePoints.affinePoint K (a * r + b) := by
  rw [schemeAffineLinearPoint, ProjectiveLine.affineLinearMap_affinePoint,
    linearToSchemePoint_affinePoint]

theorem schemeAffineLinearPoint_affinePoint_ne_zero
    (a b : K) (ha : a ≠ 0) (r : K) (h0 : a * r + b ≠ 0) :
    schemeAffineLinearPoint K a b ha
        (ProjectiveLine.affinePoint K r) ≠
      SchemeProjectiveLine.zeroPoint K := by
  rw [schemeAffineLinearPoint_affinePoint K a b ha r]
  exact SchemeAffineLinePoints.affinePoint_ne_zero K h0

theorem schemeAffineLinearPoint_affinePoint_ne_one
    (a b : K) (ha : a ≠ 0) (r : K) (h1 : a * r + b ≠ 1) :
    schemeAffineLinearPoint K a b ha
        (ProjectiveLine.affinePoint K r) ≠
      SchemeProjectiveLine.onePoint K := by
  rw [schemeAffineLinearPoint_affinePoint K a b ha r]
  exact SchemeAffineLinePoints.affinePoint_ne_one K h1

theorem schemeAffineLinearPoint_affinePoint_ne_infinity
    (a b : K) (ha : a ≠ 0) (r : K) :
    schemeAffineLinearPoint K a b ha
        (ProjectiveLine.affinePoint K r) ≠
      SchemeProjectiveLine.infinityPoint K := by
  rw [schemeAffineLinearPoint_affinePoint K a b ha r]
  exact SchemeAffineLinePoints.affinePoint_ne_infinity K _

theorem schemeAffineLinearPoint_affinePoint_mem_markedSchemePointSet_iff
    (a b : K) (ha : a ≠ 0) (r : K) :
    schemeAffineLinearPoint K a b ha
        (ProjectiveLine.affinePoint K r) ∈
      SchemeProjectiveLine.markedSchemePointSet K ↔
        a * r + b = 0 ∨ a * r + b = 1 := by
  rw [schemeAffineLinearPoint_affinePoint K a b ha r]
  exact SchemeAffineLinePoints.affinePoint_mem_markedSchemePointSet_iff K _

theorem schemeAffineLinearPoint_affinePoint_not_mem_markedSchemePointSet_iff
    (a b : K) (ha : a ≠ 0) (r : K) :
    schemeAffineLinearPoint K a b ha
        (ProjectiveLine.affinePoint K r) ∉
      SchemeProjectiveLine.markedSchemePointSet K ↔
        a * r + b ≠ 0 ∧ a * r + b ≠ 1 := by
  rw [schemeAffineLinearPoint_affinePoint_mem_markedSchemePointSet_iff K a b ha r]
  constructor
  · intro hmarked
    exact ⟨fun h0 => hmarked (Or.inl h0), fun h1 => hmarked (Or.inr h1)⟩
  · rintro ⟨h0, h1⟩ (hmarked | hmarked)
    · exact h0 hmarked
    · exact h1 hmarked

theorem schemeAffineLinearPoint_affinePoint_not_mem_markedSchemePointSet
    (a b : K) (ha : a ≠ 0) (r : K)
    (h0 : a * r + b ≠ 0) (h1 : a * r + b ≠ 1) :
    schemeAffineLinearPoint K a b ha
        (ProjectiveLine.affinePoint K r) ∉
      SchemeProjectiveLine.markedSchemePointSet K := by
  exact
    (schemeAffineLinearPoint_affinePoint_not_mem_markedSchemePointSet_iff
      K a b ha r).2 ⟨h0, h1⟩

theorem schemeAffineLinearPoint_infinity
    (a b : K) (ha : a ≠ 0) :
    schemeAffineLinearPoint K a b ha (ProjectiveLine.infinity K) =
      SchemeProjectiveLine.infinityPoint K := by
  rw [schemeAffineLinearPoint, ProjectiveLine.affineLinearMap_infinity,
    linearToSchemePoint_infinity]

end SchemeProjectiveLineTransform
end SourceStack
end HilbertTest
