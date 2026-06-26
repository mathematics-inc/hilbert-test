import HilbertTest.SourceStack.CurveRiemannRoch
import HilbertTest.SourceStack.BelyiCovers

/-!
Curve-to-Belyi construction interface.

This module connects the checked Riemann-Roch finite-evaluation handoff to the
abstract noncritical Belyi-cover interface.  The remaining geometric work is to
instantiate `SectionControlledBelyiData` from actual line-bundle sections and
finite morphisms to `P^1`.
-/

namespace HilbertTest
namespace SourceStack
namespace CurveBelyiConstruction

open CurveRiemannRoch

universe u v w z

/-- A curve-facing construction package: sections in `V` evaluate on points of
`X`, define continuous maps to a target `P`, and vanishing/nonvanishing controls
membership in the finite branch set. -/
structure SectionControlledBelyiData
    (K : Type u) [Field K]
    (X : Type v) [TopologicalSpace X]
    (P : Type w) [TopologicalSpace P]
    (V : Type z) [AddCommGroup V] [Module K V] where
  evalPackage : RiemannRochFiniteEvaluationPackage K X V
  branch : Set P
  branch_finite : branch.Finite
  map : V → X → P
  continuous_map : ∀ s, Continuous (map s)
  sends_vanishing_to_branch :
    ∀ {S : Set X} {s : V},
      evalPackage.toEvaluationData.vanishesOnSet S s →
        ∀ x ∈ S, map s x ∈ branch
  nonzero_avoids_branch :
    ∀ {T : Set X} {s : V},
      evalPackage.toEvaluationData.nonzeroOnSet T s →
        ∀ x ∈ T, map s x ∉ branch

namespace SectionControlledBelyiData

variable {K : Type u} [Field K]
variable {X : Type v} [TopologicalSpace X]
variable {P : Type w} [TopologicalSpace P]
variable {V : Type z} [AddCommGroup V] [Module K V]
variable (D : SectionControlledBelyiData K X P V)

/-- Forget a section-controlled construction package to abstract Belyi-cover
data. -/
def toBelyiCoverData : BelyiCoverData X P V where
  branch := D.branch
  branch_finite := D.branch_finite
  map := D.map
  continuous_map := D.continuous_map

theorem toBelyiCoverData_branch :
    D.toBelyiCoverData.branch = D.branch := rfl

theorem toBelyiCoverData_map_apply
    (s : V) (x : X) :
    D.toBelyiCoverData.map s x = D.map s x := rfl

/-- If a section vanishes on a finite set, the associated map sends that set to
the branch locus. -/
theorem sendsSetToBranch_of_vanishesOnSet
    {S : Set X} {s : V}
    (hs : D.evalPackage.toEvaluationData.vanishesOnSet S s) :
    D.toBelyiCoverData.sendsSetToBranch S s := by
  exact D.sends_vanishing_to_branch hs

/-- If a section is nonzero on a finite set, the associated map avoids the
branch locus on that set. -/
theorem avoidsBranch_of_nonzeroOnSet
    {T : Set X} {s : V}
    (hs : D.evalPackage.toEvaluationData.nonzeroOnSet T s) :
    ∀ x ∈ T, D.map s x ∉ D.branch := by
  exact D.nonzero_avoids_branch hs

/-- Main bridge: a section-controlled construction package over an infinite
field instantiates the abstract Theorem 2.5-style noncritical Belyi existence
interface. -/
def toNoncriticalBelyiExistence [Infinite K] :
    NoncriticalBelyiExistence X P V where
  branch := D.branch
  branch_finite := D.branch_finite
  map := D.map
  continuous_map := D.continuous_map
  exists_for_finite_disjoint := by
    intro S T hS hT hdis
    rcases D.evalPackage.exists_section_for_disjoint_finite_sets hS hT hdis with
      ⟨s, hsS, hsT⟩
    exact
      ⟨s,
        D.sends_vanishing_to_branch hsS,
        D.nonzero_avoids_branch hsT⟩

theorem toNoncriticalBelyiExistence_branch
    [Infinite K] :
    D.toNoncriticalBelyiExistence.branch = D.branch := rfl

theorem toNoncriticalBelyiExistence_toCoverData_branch
    [Infinite K] :
    D.toNoncriticalBelyiExistence.toBelyiCoverData.branch = D.branch := rfl

/-- The section-controlled construction gives the finite disjoint-set
conclusion directly. -/
theorem exists_for_finite_disjoint
    [Infinite K] {S T : Set X} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V, D.toBelyiCoverData.sendsSetToBranch S s ∧
      ∀ x ∈ T, D.map s x ∉ D.branch := by
  rcases D.evalPackage.exists_section_for_disjoint_finite_sets hS hT hdis with
    ⟨s, hsS, hsT⟩
  exact
    ⟨s,
      D.sendsSetToBranch_of_vanishesOnSet hsS,
      D.avoidsBranch_of_nonzeroOnSet hsT⟩

end SectionControlledBelyiData

end CurveBelyiConstruction
end SourceStack
end HilbertTest
