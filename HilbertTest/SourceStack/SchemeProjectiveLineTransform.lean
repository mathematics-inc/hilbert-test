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

theorem schemeReciprocalTranslatePoint_affinePoint_of_ne
    (lambda r : K) (hr : r ≠ lambda) :
    schemeReciprocalTranslatePoint K lambda (ProjectiveLine.affinePoint K r) =
      SchemeAffineLinePoints.affinePoint K ((r - lambda)⁻¹) := by
  rw [schemeReciprocalTranslatePoint,
    ProjectiveLine.reciprocalTranslate_affinePoint_of_ne K lambda r hr,
    linearToSchemePoint_affinePoint]

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

/-- Scheme-carrier point map induced by the checked affine-linear map
`x |-> a * x + b` on the linear projective line. -/
def schemeAffineLinearPoint
    (a b : K) (ha : a ≠ 0) (p : ProjectiveLine.P1 K) :
    SchemeProjectiveLine.P1 K :=
  linearToSchemePoint K (ProjectiveLine.affineLinearMap K a b ha p)

theorem schemeAffineLinearPoint_affinePoint
    (a b : K) (ha : a ≠ 0) (r : K) :
    schemeAffineLinearPoint K a b ha (ProjectiveLine.affinePoint K r) =
      SchemeAffineLinePoints.affinePoint K (a * r + b) := by
  rw [schemeAffineLinearPoint, ProjectiveLine.affineLinearMap_affinePoint,
    linearToSchemePoint_affinePoint]

theorem schemeAffineLinearPoint_infinity
    (a b : K) (ha : a ≠ 0) :
    schemeAffineLinearPoint K a b ha (ProjectiveLine.infinity K) =
      SchemeProjectiveLine.infinityPoint K := by
  rw [schemeAffineLinearPoint, ProjectiveLine.affineLinearMap_infinity,
    linearToSchemePoint_infinity]

end SchemeProjectiveLineTransform
end SourceStack
end HilbertTest
