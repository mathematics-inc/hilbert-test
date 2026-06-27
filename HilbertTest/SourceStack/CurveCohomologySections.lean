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
open MarkedProjectiveLine
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

/-- Finite-family evaluation surjectivity after imposing vanishing on another
finite family.  This abstracts the cohomological consequence usually proved
from the exact sequence
`0 -> L(-S-x) -> L(-S) -> L(-S)|_x -> 0`. -/
structure RestrictedEvaluationSurjectivityData
    (K : Type u) [Field K] (X : Type v)
    (V : Type w) [AddCommGroup V] [Module K V] where
  evalData : RRSectionEvaluationData K X V
  restricted_eval_surjective :
    ∀ {S T : Finset X}, Disjoint S T →
      ∀ x ∈ T,
        Function.Surjective
          ((evalData.eval x).comp
            (commonKernel (K := K) (V := V) S evalData.eval).subtype)

namespace RestrictedEvaluationSurjectivityData

variable (E : RestrictedEvaluationSurjectivityData K X V)

/-- Surjectivity of restricted evaluations implies the nonzero restricted
evaluation hypothesis used by the Riemann-Roch finite-evaluation package. -/
theorem restricted_eval_nonzero :
    ∀ {S T : Finset X}, Disjoint S T →
      ∀ x ∈ T,
        (E.evalData.eval x).comp
            (commonKernel (K := K) (V := V) S E.evalData.eval).subtype ≠ 0 := by
  intro S T hdis x hx
  exact linearMap_ne_zero_of_surjective
    ((E.evalData.eval x).comp
      (commonKernel (K := K) (V := V) S E.evalData.eval).subtype)
    (E.restricted_eval_surjective hdis x hx)

/-- Forget cohomological restricted surjectivity to the Riemann-Roch
finite-evaluation package used by the downstream linear-algebra layer. -/
def toRiemannRochFiniteEvaluationPackage :
    RiemannRochFiniteEvaluationPackage K X V where
  eval := E.evalData.eval
  restricted_eval_nonzero := by
    intro S T hdis x hx
    exact E.restricted_eval_nonzero hdis x hx

theorem toRiemannRochFiniteEvaluationPackage_eval
    (x : X) :
    E.toRiemannRochFiniteEvaluationPackage.eval x = E.evalData.eval x := rfl

/-- The cohomological restricted-surjectivity package gives a section vanishing
on one finite set and nonzero on a disjoint finite set. -/
theorem exists_section_for_disjoint_finsets
    [Infinite K] {S T : Finset X} (hdis : Disjoint S T) :
    ∃ s : V, E.evalData.vanishesOn S s ∧ E.evalData.nonzeroOn T s := by
  exact E.toRiemannRochFiniteEvaluationPackage.exists_section_for_disjoint_finsets hdis

/-- Set-level version of the cohomological restricted-surjectivity handoff. -/
theorem exists_section_for_disjoint_finite_sets
    [Infinite K] {S T : Set X} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V, E.evalData.vanishesOnSet S s ∧ E.evalData.nonzeroOnSet T s := by
  exact E.toRiemannRochFiniteEvaluationPackage.exists_section_for_disjoint_finite_sets
    hS hT hdis

/-- Set-level finite subtype version of the cohomological restricted-
surjectivity handoff. -/
theorem exists_section_for_disjoint_finite_subtype_sets
    [Infinite K] (U : Set X) {S T : Set U} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V, (E.evalData.restrictSubtype U).vanishesOnSet S s ∧
      (E.evalData.restrictSubtype U).nonzeroOnSet T s := by
  exact
    E.toRiemannRochFiniteEvaluationPackage.exists_section_for_disjoint_finite_subtype_sets
      U hS hT hdis

/-- Singleton-target form after restricting the point set to a subtype: vanish
on a finite subtype set and remain nonzero at an outside subtype point. -/
theorem exists_section_vanishing_on_finite_subtype_nonzero_at
    [Infinite K] (U : Set X) {S : Set U} (hS : S.Finite) {x : U} (hx : x ∉ S) :
    ∃ s : V, (E.evalData.restrictSubtype U).vanishesOnSet S s ∧
      (E.evalData.restrictSubtype U).eval x s ≠ 0 := by
  exact
    E.toRiemannRochFiniteEvaluationPackage.exists_section_vanishing_on_finite_subtype_nonzero_at
      U hS hx

/-- Singleton-target form of restricted evaluation surjectivity: vanish on a
finite set and remain nonzero at a point outside it. -/
theorem exists_section_vanishing_on_finite_nonzero_at
    [Infinite K] {S : Set X} (hS : S.Finite) {x : X} (hx : x ∉ S) :
    ∃ s : V, E.evalData.vanishesOnSet S s ∧ E.evalData.eval x s ≠ 0 := by
  exact
    E.toRiemannRochFiniteEvaluationPackage.exists_section_vanishing_on_finite_nonzero_at
      hS hx

end RestrictedEvaluationSurjectivityData

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

/-- The cohomological divisor zero-section vanishes at exactly the support
points. -/
theorem zeroSection_eval_eq_zero_iff_mem_support (x : X) :
    D.evalSurjectivity.evalData.eval x D.zeroSection = 0 ↔
      x ∈ D.evalSurjectivity.support := by
  exact D.toDivisorZeroSectionData.zeroSection_eval_eq_zero_iff_mem_support x

/-- Away from the cohomological divisor support, the distinguished zero-section
is nonzero. -/
theorem zeroSection_eval_ne_zero_iff_not_mem_support (x : X) :
    D.evalSurjectivity.evalData.eval x D.zeroSection ≠ 0 ↔
      x ∉ D.evalSurjectivity.support := by
  exact D.toDivisorZeroSectionData.zeroSection_eval_ne_zero_iff_not_mem_support x

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
theorem projectivePair_maps_support_to_zeroPoint
    (D : CohomologicalDivisorSectionData K C V)
    (P : ProjectiveLineSectionPair K C V)
    (heval : P.evalData = D.evalSurjectivity.evalData)
    (hsection0 : P.section0 = D.zeroSection) :
    ∀ x ∈ D.evalSurjectivity.support,
      P.hom.base x = schemeCarrierPoint K MarkedPointLabel.zero := by
  exact
    D.toDivisorZeroSectionData.projectivePair_maps_support_to_zeroPoint
      P heval hsection0

/-- Away from the cohomological divisor support, the associated projective-line
morphism avoids the checked zero point. -/
theorem projectivePair_avoids_zeroPoint_off_support
    (D : CohomologicalDivisorSectionData K C V)
    (P : ProjectiveLineSectionPair K C V)
    (heval : P.evalData = D.evalSurjectivity.evalData)
    (hsection0 : P.section0 = D.zeroSection) :
    ∀ x ∉ D.evalSurjectivity.support,
      P.hom.base x ≠ schemeCarrierPoint K MarkedPointLabel.zero := by
  exact
    D.toDivisorZeroSectionData.projectivePair_avoids_zeroPoint_off_support
      P heval hsection0

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

/-- Factory form of the cohomological bridge: after the line-bundle
construction upgrades basepoint-free section pairs to projective-line section
pairs, the cohomological divisor package supplies one whose support maps to the
marked branch point. -/
theorem exists_projectivePair_maps_support_to_marked
    (D : CohomologicalDivisorSectionData K C V)
    [Infinite K] (hsupport : D.evalSurjectivity.support.Finite)
    (mkPair : ∀ s1 : V,
      HasNoCommonZero D.evalSurjectivity.evalData D.zeroSection s1 →
        ProjectiveLineSectionPair K C V)
    (hmk_eval : ∀ s1 hnc, (mkPair s1 hnc).evalData = D.evalSurjectivity.evalData)
    (hmk_section0 : ∀ s1 hnc, (mkPair s1 hnc).section0 = D.zeroSection) :
    ∃ s1 : V,
      ∃ hnc : HasNoCommonZero D.evalSurjectivity.evalData D.zeroSection s1,
        ∀ x ∈ D.evalSurjectivity.support,
          (mkPair s1 hnc).hom.base x ∈ markedSchemePointSet K := by
  rcases D.exists_second_section_no_common_zero hsupport with ⟨s1, hnc⟩
  exact ⟨s1, hnc,
    D.projectivePair_maps_support_to_marked
      (mkPair s1 hnc) (hmk_eval s1 hnc) (hmk_section0 s1 hnc)⟩

/-- Factory form of the cohomological divisor bridge, with the sharper
pointwise statement used in the reduction step: the support maps to `0`, while
any prescribed set disjoint from the support avoids `0`. -/
theorem exists_projectivePair_maps_support_to_zeroPoint_avoids_set
    (D : CohomologicalDivisorSectionData K C V)
    [Infinite K] (hsupport : D.evalSurjectivity.support.Finite) {S : Set C}
    (hdis : Disjoint S D.evalSurjectivity.support)
    (mkPair : ∀ s1 : V,
      HasNoCommonZero D.evalSurjectivity.evalData D.zeroSection s1 →
        ProjectiveLineSectionPair K C V)
    (hmk_eval : ∀ s1 hnc, (mkPair s1 hnc).evalData = D.evalSurjectivity.evalData)
    (hmk_section0 : ∀ s1 hnc, (mkPair s1 hnc).section0 = D.zeroSection) :
    ∃ s1 : V,
      ∃ hnc : HasNoCommonZero D.evalSurjectivity.evalData D.zeroSection s1,
        (∀ x ∈ D.evalSurjectivity.support,
          (mkPair s1 hnc).hom.base x = schemeCarrierPoint K MarkedPointLabel.zero) ∧
          ∀ x ∈ S,
            (mkPair s1 hnc).hom.base x ≠ schemeCarrierPoint K MarkedPointLabel.zero := by
  exact
    D.toDivisorZeroSectionData.exists_projectivePair_maps_support_to_zeroPoint_avoids_set
      hsupport hdis mkPair hmk_eval hmk_section0

end SchemeSupport

end CohomologicalDivisorSectionData

end CurveCohomologySections
end SourceStack
end HilbertTest
