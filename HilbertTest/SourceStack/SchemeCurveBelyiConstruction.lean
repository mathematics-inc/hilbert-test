import HilbertTest.SourceStack.CurveBelyiConstruction
import HilbertTest.SourceStack.SchemeMarkedBelyi

/-!
Scheme-level bridge from section-controlled curve data to finite marked Belyi
families.

This module is still an interface layer: it does not construct the projective
line morphisms from line-bundle sections.  It proves that once such a
construction supplies finite marked Belyi maps whose marked-branch behavior is
controlled by section vanishing/nonvanishing, the paper-facing
`FiniteMarkedBelyiExistence` structure follows.
-/

noncomputable section

open AlgebraicGeometry

namespace HilbertTest
namespace SourceStack
namespace SchemeCurveBelyiConstruction

open CurveRiemannRoch
open CurveBelyiConstruction
open SchemeProjectiveLine
open SchemeMarkedBelyi

universe u w z

/-- Scheme-level section-controlled finite marked Belyi data.  The missing
curve/line-bundle construction should instantiate this structure for smooth
proper connected curves. -/
structure SectionControlledFiniteMarkedBelyiData
    (K : Type u) [Field K] (C : Scheme.{u})
    (V : Type w) [AddCommGroup V] [Module K V] where
  evalPackage : RiemannRochFiniteEvaluationPackage K C V
  hmarkedOpen : IsOpen (markedSchemePointSet K)ᶜ
  map : V → SchemeBelyi.FiniteBelyiMap
    (SchemeBelyi.markedBelyiTarget K hmarkedOpen) C
  sends_vanishing_to_marked :
    ∀ {S : Set C} {s : V},
      evalPackage.toEvaluationData.vanishesOnSet S s →
        ∀ x ∈ S, (map s).hom.base x ∈ markedSchemePointSet K
  nonzero_avoids_marked :
    ∀ {T : Set C} {s : V},
      evalPackage.toEvaluationData.nonzeroOnSet T s →
        ∀ x ∈ T, (map s).hom.base x ∉ markedSchemePointSet K

namespace SectionControlledFiniteMarkedBelyiData

variable {K : Type u} [Field K]
variable {C : Scheme.{u}}
variable {V : Type w} [AddCommGroup V] [Module K V]
variable (D : SectionControlledFiniteMarkedBelyiData K C V)

/-- Forget scheme-level finite marked Belyi data to the topological
section-controlled interface. -/
def toSectionControlledBelyiData :
    SectionControlledBelyiData K C (P1 K) V where
  evalPackage := D.evalPackage
  branch := markedSchemePointSet K
  branch_finite := markedSchemePointSet_finite K
  map s x := (D.map s).hom.base x
  continuous_map s := (D.map s).hom.continuous
  sends_vanishing_to_branch := by
    intro S s hs
    exact D.sends_vanishing_to_marked hs
  nonzero_avoids_branch := by
    intro T s hs
    exact D.nonzero_avoids_marked hs

theorem toSectionControlledBelyiData_branch :
    D.toSectionControlledBelyiData.branch = markedSchemePointSet K := rfl

theorem toSectionControlledBelyiData_map_apply
    (s : V) (x : C) :
    D.toSectionControlledBelyiData.map s x = (D.map s).hom.base x := rfl

/-- The scheme-level section-controlled package instantiates the paper-facing
finite marked Belyi existence interface over an infinite field. -/
def toFiniteMarkedBelyiExistence [Infinite K] :
    FiniteMarkedBelyiExistence K V C where
  hmarkedOpen := D.hmarkedOpen
  map := D.map
  exists_for_finite_disjoint := by
    intro S T hS hT hdis
    rcases D.evalPackage.exists_section_for_disjoint_finite_sets hS hT hdis with
      ⟨s, hsS, hsT⟩
    exact
      ⟨s,
        D.sends_vanishing_to_marked hsS,
        D.nonzero_avoids_marked hsT⟩

theorem toFiniteMarkedBelyiExistence_hmarkedOpen
    [Infinite K] :
    D.toFiniteMarkedBelyiExistence.hmarkedOpen = D.hmarkedOpen := rfl

theorem toFiniteMarkedBelyiExistence_map_apply
    [Infinite K] (s : V) :
    D.toFiniteMarkedBelyiExistence.map s = D.map s := rfl

/-- Direct finite disjoint-set conclusion for scheme-level section-controlled
finite marked Belyi data. -/
theorem exists_for_finite_disjoint
    [Infinite K] {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V, (∀ x ∈ S, (D.map s).hom.base x ∈ markedSchemePointSet K) ∧
      ∀ x ∈ T, (D.map s).hom.base x ∉ markedSchemePointSet K := by
  rcases D.evalPackage.exists_section_for_disjoint_finite_sets hS hT hdis with
    ⟨s, hsS, hsT⟩
  exact
    ⟨s,
      D.sends_vanishing_to_marked hsS,
      D.nonzero_avoids_marked hsT⟩

theorem toFiniteMarkedBelyiExistence_toMarkedCoverData_branch
    [Infinite K] :
    (FiniteMarkedBelyiExistence.toMarkedCoverData K V
      D.toFiniteMarkedBelyiExistence).branch = markedSchemePointSet K := by
  exact FiniteMarkedBelyiExistence.toMarkedCoverData_branch K V
    D.toFiniteMarkedBelyiExistence

/-- Direct pointwise tuple-cover consequence for section-controlled finite
marked Belyi data. -/
theorem pointwise_cover_complement
    [Infinite K] (κ : Type z) [Finite κ] {S : Set C} (hS : S.Finite)
    (x : κ → {x : C // x ∉ S}) :
    ∃ s : V,
      (FiniteMarkedBelyiExistence.toMarkedCoverData K V
        D.toFiniteMarkedBelyiExistence).sendsSetToBranch S s ∧
        ∀ i, (D.map s).hom.base (x i).1 ∉ markedSchemePointSet K := by
  rcases FiniteMarkedBelyiExistence.pointwise_cover_complement
      K V D.toFiniteMarkedBelyiExistence κ hS x with
    ⟨s, hsS, hsx⟩
  exact ⟨s, hsS, by simpa [toFiniteMarkedBelyiExistence] using hsx⟩

/-- Direct Corollary 3.1-style finite-subcover consequence for
section-controlled finite marked Belyi data. -/
theorem finite_subcover_on_complement
    [Infinite K] (κ : Type z) [Finite κ] [T1Space (P1 K)]
    {S : Set C} (hS : S.Finite) [CompactSpace (κ → {x : C // x ∉ S})] :
    ∃ t : Finset {s : V //
        (FiniteMarkedBelyiExistence.toMarkedCoverData K V
          D.toFiniteMarkedBelyiExistence).sendsSetToBranch S s},
      (⋃ s ∈ t,
          ((FiniteMarkedBelyiExistence.toMarkedCoverData K V
            D.toFiniteMarkedBelyiExistence).complementCoverData S).tupleAvoidSet
              (κ := κ) s) =
        (Set.univ : Set (κ → {x : C // x ∉ S})) := by
  exact FiniteMarkedBelyiExistence.finite_subcover_on_complement
    K V D.toFiniteMarkedBelyiExistence κ hS

end SectionControlledFiniteMarkedBelyiData

end SchemeCurveBelyiConstruction
end SourceStack
end HilbertTest
