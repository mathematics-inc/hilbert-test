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

/-- Finite disjoint-set conclusion after restricting the source of
section-controlled Belyi data to a subtype. -/
theorem exists_for_finite_disjoint_subtype_sets
    [Infinite K] (U : Set X) {S T : Set U} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V, (∀ x ∈ S, D.map s x.1 ∈ D.branch) ∧
      ∀ x ∈ T, D.map s x.1 ∉ D.branch := by
  let S' : Set X := (Subtype.val : U → X) '' S
  let T' : Set X := (Subtype.val : U → X) '' T
  have hS' : S'.Finite := hS.image (Subtype.val : U → X)
  have hT' : T'.Finite := hT.image (Subtype.val : U → X)
  have hdis' : Disjoint S' T' := by
    rw [Set.disjoint_left]
    intro y hyS hyT
    rcases hyS with ⟨s, hsS, rfl⟩
    rcases hyT with ⟨t, htT, ht⟩
    have hst : s = t := Subtype.ext ht.symm
    have hs_not_mem_T : s ∉ T := (Set.disjoint_left.mp hdis) hsS
    exact hs_not_mem_T (by simpa [hst] using htT)
  rcases D.exists_for_finite_disjoint hS' hT' hdis' with
    ⟨s, hsS, hsT⟩
  exact
    ⟨s,
      (by
        intro x hx
        exact hsS x.1 ⟨x, hx, rfl⟩),
      (by
        intro x hx
        exact hsT x.1 ⟨x, hx, rfl⟩)⟩

/-- Pointwise tuple-cover consequence for section-controlled Belyi data. -/
theorem pointwise_cover_complement
    [Infinite K] (κ : Type*) [Finite κ] {S : Set X} (hS : S.Finite)
    (x : κ → {x : X // x ∉ S}) :
    ∃ s : V, D.toBelyiCoverData.sendsSetToBranch S s ∧
      ∀ i, D.map s (x i).1 ∉ D.branch := by
  exact D.toNoncriticalBelyiExistence.pointwise_cover_complement hS x

/-- Finite tuple-subcover consequence for section-controlled Belyi data. -/
theorem finite_subcover_on_complement
    [Infinite K] (κ : Type*) [Finite κ] [T1Space P]
    {S : Set X} (hS : S.Finite) [CompactSpace (κ → {x : X // x ∉ S})] :
    ∃ t : Finset {s : V // D.toBelyiCoverData.sendsSetToBranch S s},
      (⋃ s ∈ t, (D.toBelyiCoverData.complementCoverData S).tupleAvoidSet
          (κ := κ) s) =
        (Set.univ : Set (κ → {x : X // x ∉ S})) := by
  exact D.toNoncriticalBelyiExistence.finite_subcover_on_complement
    (κ := κ) hS

/-- Membership form of the finite tuple-subcover consequence for
section-controlled Belyi data. -/
theorem finite_subcover_on_complement_forall
    [Infinite K] (κ : Type*) [Finite κ] [T1Space P]
    {S : Set X} (hS : S.Finite) [CompactSpace (κ → {x : X // x ∉ S})] :
    ∃ t : Finset {s : V // D.toBelyiCoverData.sendsSetToBranch S s},
      ∀ x : κ → {x : X // x ∉ S},
        ∃ s ∈ t,
          x ∈ (D.toBelyiCoverData.complementCoverData S).tupleAvoidSet
            (κ := κ) s := by
  exact D.toNoncriticalBelyiExistence.finite_subcover_on_complement_forall
    (κ := κ) hS

end SectionControlledBelyiData

end CurveBelyiConstruction
end SourceStack
end HilbertTest
