import HilbertTest.SourceStack.ProjectiveLine
import HilbertTest.SourceStack.SchemeProjectiveLine

/-!
Shared labels for the linear and scheme-theoretic marked points on `P^1`.

The linear projective line and scheme-theoretic `Proj K[X₀,X₁]` have different
point types.  This file provides a common three-label indexing layer for the
marked points `0`, `1`, and `∞`, together with image and injectivity facts on
both sides.
-/

namespace HilbertTest
namespace SourceStack
namespace MarkedProjectiveLine

/-- The three labels for the marked points `0`, `1`, and `∞`. -/
inductive MarkedPointLabel where
  | zero
  | one
  | infinity
  deriving DecidableEq

instance : Fintype MarkedPointLabel where
  elems := {MarkedPointLabel.zero, MarkedPointLabel.one, MarkedPointLabel.infinity}
  complete := by
    intro x
    cases x <;> simp

universe u

/-- The linear projective point associated to a marked-point label. -/
noncomputable def linearPoint (K : Type u) [Field K] :
    MarkedPointLabel → ProjectiveLine.P1 K
  | .zero => ProjectiveLine.zero K
  | .one => ProjectiveLine.one K
  | .infinity => ProjectiveLine.infinity K

/-- The scheme-theoretic `Proj K[X₀,X₁]` point associated to a marked-point label. -/
noncomputable def schemePoint (K : Type u) [Field K] :
    MarkedPointLabel → _root_.ProjectiveSpectrum (SchemeProjectiveLine.grading K)
  | .zero => SchemeProjectiveLine.zeroPoint K
  | .one => SchemeProjectiveLine.onePoint K
  | .infinity => SchemeProjectiveLine.infinityPoint K

/-- The scheme-theoretic marked point associated to a label, with codomain
written as the scheme carrier `P1 K`. -/
noncomputable def schemeCarrierPoint (K : Type u) [Field K] :
    MarkedPointLabel → SchemeProjectiveLine.P1 K :=
  schemePoint K

/-- The finite image of the three labels on the linear projective line. -/
noncomputable def linearPointFinset (K : Type u) [Field K] :
    Finset (ProjectiveLine.P1 K) := by
  classical
  exact Finset.univ.image (linearPoint K)

/-- The finite image of the three labels on scheme-theoretic `P^1`. -/
noncomputable def schemePointFinset (K : Type u) [Field K] :
    Finset (_root_.ProjectiveSpectrum (SchemeProjectiveLine.grading K)) := by
  classical
  exact Finset.univ.image (schemePoint K)

/-- The finite image of the three labels on the scheme carrier `P1 K`. -/
noncomputable def schemeCarrierPointFinset (K : Type u) [Field K] :
    Finset (SchemeProjectiveLine.P1 K) := by
  classical
  exact Finset.univ.image (schemeCarrierPoint K)

/-- The finite image of the three labels on the scheme carrier `P1 K`, as a set. -/
noncomputable def schemeCarrierPointSet (K : Type u) [Field K] :
    Set (SchemeProjectiveLine.P1 K) :=
  schemeCarrierPointFinset K

theorem linearPointFinset_eq_branchFinset
    (K : Type u) [Field K] :
    linearPointFinset K = ProjectiveLine.branchFinset K := by
  classical
  ext p
  constructor
  · intro hp
    simp [linearPointFinset] at hp
    rcases hp with ⟨a, ha⟩
    cases a
    · simp [linearPoint, ProjectiveLine.branchFinset] at ha
      subst p
      simp [ProjectiveLine.branchFinset]
    · simp [linearPoint, ProjectiveLine.branchFinset] at ha
      subst p
      simp [ProjectiveLine.branchFinset]
    · simp [linearPoint, ProjectiveLine.branchFinset] at ha
      subst p
      simp [ProjectiveLine.branchFinset]
  · intro hp
    simp [ProjectiveLine.branchFinset] at hp
    rcases hp with hp | hp | hp
    · refine Finset.mem_image.mpr ⟨MarkedPointLabel.zero, by simp, ?_⟩
      simp [linearPoint, hp]
    · refine Finset.mem_image.mpr ⟨MarkedPointLabel.one, by simp, ?_⟩
      simp [linearPoint, hp]
    · refine Finset.mem_image.mpr ⟨MarkedPointLabel.infinity, by simp, ?_⟩
      simp [linearPoint, hp]

theorem schemePointFinset_eq_markedPointFinset
    (K : Type u) [Field K] :
    schemePointFinset K = SchemeProjectiveLine.markedPointFinset K := by
  classical
  ext p
  constructor
  · intro hp
    simp [schemePointFinset] at hp
    rcases hp with ⟨a, ha⟩
    cases a
    · simp [schemePoint, SchemeProjectiveLine.markedPointFinset] at ha
      subst p
      simp [SchemeProjectiveLine.markedPointFinset]
    · simp [schemePoint, SchemeProjectiveLine.markedPointFinset] at ha
      subst p
      simp [SchemeProjectiveLine.markedPointFinset]
    · simp [schemePoint, SchemeProjectiveLine.markedPointFinset] at ha
      subst p
      simp [SchemeProjectiveLine.markedPointFinset]
  · intro hp
    simp [SchemeProjectiveLine.markedPointFinset] at hp
    rcases hp with hp | hp | hp
    · refine Finset.mem_image.mpr ⟨MarkedPointLabel.zero, by simp, ?_⟩
      simp [schemePoint, hp]
    · refine Finset.mem_image.mpr ⟨MarkedPointLabel.one, by simp, ?_⟩
      simp [schemePoint, hp]
    · refine Finset.mem_image.mpr ⟨MarkedPointLabel.infinity, by simp, ?_⟩
      simp [schemePoint, hp]

theorem schemeCarrierPointFinset_eq_markedSchemePointFinset
    (K : Type u) [Field K] :
    schemeCarrierPointFinset K = SchemeProjectiveLine.markedSchemePointFinset K := by
  classical
  ext p
  constructor
  · intro hp
    simp [schemeCarrierPointFinset, schemeCarrierPoint] at hp
    rcases hp with ⟨a, ha⟩
    cases a
    · simp [schemePoint, SchemeProjectiveLine.markedSchemePointFinset,
        SchemeProjectiveLine.markedPointFinset] at ha
      subst p
      simp [SchemeProjectiveLine.markedSchemePointFinset,
        SchemeProjectiveLine.markedPointFinset]
    · simp [schemePoint, SchemeProjectiveLine.markedSchemePointFinset,
        SchemeProjectiveLine.markedPointFinset] at ha
      subst p
      simp [SchemeProjectiveLine.markedSchemePointFinset,
        SchemeProjectiveLine.markedPointFinset]
    · simp [schemePoint, SchemeProjectiveLine.markedSchemePointFinset,
        SchemeProjectiveLine.markedPointFinset] at ha
      subst p
      simp [SchemeProjectiveLine.markedSchemePointFinset,
        SchemeProjectiveLine.markedPointFinset]
  · intro hp
    simp [SchemeProjectiveLine.markedSchemePointFinset,
      SchemeProjectiveLine.markedPointFinset] at hp
    rcases hp with hp | hp | hp
    · refine Finset.mem_image.mpr ⟨MarkedPointLabel.zero, by simp, ?_⟩
      simp [schemeCarrierPoint, schemePoint, hp]
    · refine Finset.mem_image.mpr ⟨MarkedPointLabel.one, by simp, ?_⟩
      simp [schemeCarrierPoint, schemePoint, hp]
    · refine Finset.mem_image.mpr ⟨MarkedPointLabel.infinity, by simp, ?_⟩
      simp [schemeCarrierPoint, schemePoint, hp]

theorem schemeCarrierPointSet_eq_markedSchemePointSet
    (K : Type u) [Field K] :
    schemeCarrierPointSet K = SchemeProjectiveLine.markedSchemePointSet K := by
  ext p
  change p ∈ schemeCarrierPointFinset K ↔
    p ∈ SchemeProjectiveLine.markedSchemePointFinset K
  rw [schemeCarrierPointFinset_eq_markedSchemePointFinset K]

theorem linearPoint_injective
    (K : Type u) [Field K] :
    Function.Injective (linearPoint K) := by
  intro a b h
  cases a <;> cases b <;>
    simp [linearPoint, ProjectiveLine.zero_ne_one K, (ProjectiveLine.zero_ne_one K).symm,
      ProjectiveLine.zero_ne_infinity K, (ProjectiveLine.zero_ne_infinity K).symm,
      ProjectiveLine.one_ne_infinity K, (ProjectiveLine.one_ne_infinity K).symm] at h ⊢

theorem schemePoint_injective
    (K : Type u) [Field K] :
    Function.Injective (schemePoint K) := by
  intro a b h
  cases a <;> cases b <;>
    simp [schemePoint, SchemeProjectiveLine.zeroPoint_ne_onePoint K,
      (SchemeProjectiveLine.zeroPoint_ne_onePoint K).symm,
      SchemeProjectiveLine.zeroPoint_ne_infinityPoint K,
      (SchemeProjectiveLine.zeroPoint_ne_infinityPoint K).symm,
      SchemeProjectiveLine.onePoint_ne_infinityPoint K,
      (SchemeProjectiveLine.onePoint_ne_infinityPoint K).symm] at h ⊢

theorem schemeCarrierPoint_injective
    (K : Type u) [Field K] :
    Function.Injective (schemeCarrierPoint K) := by
  exact schemePoint_injective K

theorem linearPoint_mem_branchFinset
    (K : Type u) [Field K] (label : MarkedPointLabel) :
    linearPoint K label ∈ ProjectiveLine.branchFinset K := by
  classical
  rw [← linearPointFinset_eq_branchFinset]
  exact Finset.mem_image_of_mem (linearPoint K) (Finset.mem_univ label)

theorem schemePoint_mem_markedPointFinset
    (K : Type u) [Field K] (label : MarkedPointLabel) :
    schemePoint K label ∈ SchemeProjectiveLine.markedPointFinset K := by
  classical
  rw [← schemePointFinset_eq_markedPointFinset]
  exact Finset.mem_image_of_mem (schemePoint K) (Finset.mem_univ label)

theorem schemeCarrierPoint_mem_markedSchemePointFinset
    (K : Type u) [Field K] (label : MarkedPointLabel) :
    schemeCarrierPoint K label ∈ SchemeProjectiveLine.markedSchemePointFinset K := by
  classical
  rw [← schemeCarrierPointFinset_eq_markedSchemePointFinset]
  exact Finset.mem_image_of_mem (schemeCarrierPoint K) (Finset.mem_univ label)

theorem schemeCarrierPoint_mem_markedSchemePointSet
    (K : Type u) [Field K] (label : MarkedPointLabel) :
    schemeCarrierPoint K label ∈ SchemeProjectiveLine.markedSchemePointSet K := by
  change schemeCarrierPoint K label ∈ SchemeProjectiveLine.markedSchemePointFinset K
  exact schemeCarrierPoint_mem_markedSchemePointFinset K label

theorem linearPointFinset_card
    (K : Type u) [Field K] :
    (linearPointFinset K).card = 3 := by
  rw [linearPointFinset_eq_branchFinset]
  exact ProjectiveLine.branchFinset_card K

theorem schemePointFinset_card
    (K : Type u) [Field K] :
    (schemePointFinset K).card = 3 := by
  rw [schemePointFinset_eq_markedPointFinset]
  exact SchemeProjectiveLine.markedPointFinset_card K

theorem schemeCarrierPointFinset_card
    (K : Type u) [Field K] :
    (schemeCarrierPointFinset K).card = 3 := by
  rw [schemeCarrierPointFinset_eq_markedSchemePointFinset]
  exact SchemeProjectiveLine.markedSchemePointFinset_card K

theorem schemeCarrierPointSet_finite
    (K : Type u) [Field K] :
    (schemeCarrierPointSet K).Finite := by
  rw [schemeCarrierPointSet_eq_markedSchemePointSet]
  exact SchemeProjectiveLine.markedSchemePointSet_finite K

theorem linearPointFinset_card_eq_schemePointFinset_card
    (K : Type u) [Field K] :
    (linearPointFinset K).card = (schemePointFinset K).card := by
  rw [linearPointFinset_card K, schemePointFinset_card K]

theorem linearPointFinset_card_eq_schemeCarrierPointFinset_card
    (K : Type u) [Field K] :
    (linearPointFinset K).card = (schemeCarrierPointFinset K).card := by
  rw [linearPointFinset_card K, schemeCarrierPointFinset_card K]

end MarkedProjectiveLine
end SourceStack
end HilbertTest
