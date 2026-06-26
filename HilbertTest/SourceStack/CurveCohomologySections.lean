import HilbertTest.SourceStack.CurveDivisorSections

/-!
Cohomology-to-evaluation source layer for Mochizuki Theorem 2.5.

The paper uses Serre duality and the long exact cohomology sequence to show
that global sections of `L` surject onto the fiber at each point.  Pinned
Mathlib does not contain that curve-specific theorem.  This file isolates the
checked consequence needed by the divisor-section layer: surjectivity of the
evaluation map to the nontrivial fiber `K` makes the evaluation functional
nonzero.
-/

namespace HilbertTest
namespace SourceStack
namespace CurveCohomologySections

open CurveDivisorSections
open CurveRiemannRoch
open ProjectiveSectionMaps
open SchemeProjectiveLine

universe u v w

variable {K : Type u} [Field K]
variable {X : Type v}
variable {V : Type w} [AddCommGroup V] [Module K V]

/-- A surjective linear map to a nontrivial target is nonzero. -/
theorem linearMap_ne_zero_of_surjective
    {W : Type*} [AddCommGroup W] [Module K W] [Nontrivial W]
    (f : V →ₗ[K] W) (hf : Function.Surjective f) :
    f ≠ 0 := by
  intro hzero
  rcases exists_ne (0 : W) with ⟨w, hw⟩
  rcases hf w with ⟨v, hv⟩
  apply hw
  rw [← hv, hzero]
  simp

/-- Surjective point evaluations on a support set, abstracting the output of
the long exact cohomology sequence for `0 -> L(-x) -> L -> L ⊗ k(x) -> 0`. -/
structure EvaluationSurjectivityData
    (K : Type u) [Field K] (X : Type v)
    (V : Type w) [AddCommGroup V] [Module K V] where
  evalData : RRSectionEvaluationData K X V
  support : Set X
  eval_surjective_on_support : ∀ x ∈ support, Function.Surjective (evalData.eval x)

namespace EvaluationSurjectivityData

variable (E : EvaluationSurjectivityData K X V)

/-- Surjective evaluations to `K` are nonzero linear forms. -/
theorem eval_nonzero_on_support :
    ∀ x ∈ E.support, E.evalData.eval x ≠ 0 := by
  intro x hx
  exact linearMap_ne_zero_of_surjective
    (E.evalData.eval x) (E.eval_surjective_on_support x hx)

end EvaluationSurjectivityData

/-- Cohomological divisor-section data: evaluation surjectivity plus the
zero-section of the divisor line bundle. -/
structure CohomologicalDivisorSectionData
    (K : Type u) [Field K] (X : Type v)
    (V : Type w) [AddCommGroup V] [Module K V] where
  evalSurjectivity : EvaluationSurjectivityData K X V
  zeroSection : V
  zeroSection_hasZeroSet :
    HasZeroSet evalSurjectivity.evalData zeroSection evalSurjectivity.support

namespace CohomologicalDivisorSectionData

variable (D : CohomologicalDivisorSectionData K X V)

/-- Forget cohomological evaluation-surjectivity data to the divisor
zero-section package. -/
def toDivisorZeroSectionData : DivisorZeroSectionData K X V where
  evalData := D.evalSurjectivity.evalData
  support := D.evalSurjectivity.support
  zeroSection := D.zeroSection
  zeroSection_hasZeroSet := D.zeroSection_hasZeroSet
  eval_nonzero_on_support := D.evalSurjectivity.eval_nonzero_on_support

theorem toDivisorZeroSectionData_support :
    D.toDivisorZeroSectionData.support = D.evalSurjectivity.support := rfl

/-- The cohomological source package supplies a second section nonzero on the
divisor support. -/
theorem exists_section_nonzero_on_support
    [Infinite K] (hsupport : D.evalSurjectivity.support.Finite) :
    ∃ s1 : V, D.evalSurjectivity.evalData.nonzeroOnSet
      D.evalSurjectivity.support s1 := by
  exact D.toDivisorZeroSectionData.exists_section_nonzero_on_support hsupport

/-- The cohomological source package supplies a basepoint-free pair
`(s0, s1)`. -/
theorem exists_second_section_no_common_zero
    [Infinite K] (hsupport : D.evalSurjectivity.support.Finite) :
    ∃ s1 : V, HasNoCommonZero
      D.evalSurjectivity.evalData D.zeroSection s1 := by
  exact D.toDivisorZeroSectionData.exists_second_section_no_common_zero hsupport

section SchemeSupport

open AlgebraicGeometry

variable {C : Scheme.{u}}

/-- After the cohomological divisor package is upgraded to a projective-line
section pair, the divisor support maps to the marked branch point `0`. -/
theorem projectivePair_maps_support_to_marked
    (D : CohomologicalDivisorSectionData K C V)
    (P : ProjectiveLineSectionPair K C V)
    (heval : P.evalData = D.evalSurjectivity.evalData)
    (hsection0 : P.section0 = D.zeroSection) :
    ∀ x ∈ D.evalSurjectivity.support, P.hom.base x ∈ markedSchemePointSet K := by
  intro x hx
  have hzero : P.evalData.eval x P.section0 = 0 := by
    rw [heval, hsection0]
    exact (D.zeroSection_hasZeroSet x).2 hx
  exact P.maps_section0_zero_to_marked hzero

end SchemeSupport

end CohomologicalDivisorSectionData

end CurveCohomologySections
end SourceStack
end HilbertTest
