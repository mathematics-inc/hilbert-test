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

end MarkedProjectiveLine
end SourceStack
end HilbertTest
