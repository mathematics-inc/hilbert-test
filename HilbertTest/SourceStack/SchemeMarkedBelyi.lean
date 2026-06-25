import HilbertTest.SourceStack.BelyiCovers
import HilbertTest.SourceStack.SchemeProjectiveLine
import HilbertTest.SourceStack.RationalMaps

/-!
Scheme-theoretic marked-branch instantiation for the abstract Belyi cover API.

The topological cover layer is phrased for an arbitrary finite branch set.  This
file specializes that interface to the checked marked triple on
`Proj K[X₀,X₁]`.
-/

namespace HilbertTest
namespace SourceStack
namespace SchemeMarkedBelyi

open SchemeProjectiveLine
open AlgebraicGeometry

noncomputable section

universe u v w
universe z

variable (K : Type u) [CommRing K] [IsDomain K]
variable (X : Type v) [TopologicalSpace X]
variable (Φ : Type w)
variable (map : Φ → X → _root_.ProjectiveSpectrum (grading K))
variable (continuous_map : ∀ φ, Continuous (map φ))

/-- The abstract topological Belyi-cover data with branch set equal to the
scheme-theoretic marked triple on `Proj K[X₀,X₁]`. -/
def markedCoverData :
    BelyiCoverData X (_root_.ProjectiveSpectrum (grading K)) Φ where
  branch := markedPointSet K
  branch_finite := markedPointSet_finite K
  map := map
  continuous_map := continuous_map

theorem markedCoverData_branch :
    (markedCoverData K X Φ map continuous_map).branch = markedPointSet K := rfl

theorem markedCoverData_sendsSetToBranch_iff
    (S : Set X) (φ : Φ) :
    (markedCoverData K X Φ map continuous_map).sendsSetToBranch S φ ↔
      ∀ x ∈ S, map φ x ∈ markedPointSet K := by
  rfl

theorem markedCoverData_mem_belyiOpen_iff
    (φ : Φ) (x : X) :
    x ∈ (markedCoverData K X Φ map continuous_map).belyiOpen φ ↔
      map φ x ∉ markedPointSet K := by
  rfl

theorem markedCoverData_branch_finite :
    (markedCoverData K X Φ map continuous_map).branch.Finite := by
  exact markedPointSet_finite K

variable (exists_for_finite_disjoint :
  ∀ {S T : Set X}, S.Finite → T.Finite → Disjoint S T →
    ∃ φ : Φ, (∀ x ∈ S, map φ x ∈ markedPointSet K) ∧
      ∀ x ∈ T, map φ x ∉ markedPointSet K)

/-- The noncritical Belyi finite-set existence interface specialized to the
scheme-theoretic marked triple on `Proj K[X₀,X₁]`. -/
def markedNoncriticalExistence :
    NoncriticalBelyiExistence X (_root_.ProjectiveSpectrum (grading K)) Φ where
  branch := markedPointSet K
  branch_finite := markedPointSet_finite K
  map := map
  continuous_map := continuous_map
  exists_for_finite_disjoint := by
    intro S T hS hT hdis
    rcases exists_for_finite_disjoint hS hT hdis with ⟨φ, hφS, hφT⟩
    exact ⟨φ, hφS, hφT⟩

theorem markedNoncriticalExistence_branch :
    (markedNoncriticalExistence K X Φ map continuous_map exists_for_finite_disjoint).branch =
      markedPointSet K := rfl

theorem markedNoncriticalExistence_toCoverData_branch :
    (markedNoncriticalExistence K X Φ map continuous_map
      exists_for_finite_disjoint).toBelyiCoverData.branch = markedPointSet K := rfl

theorem markedNoncritical_exists_belyiOpen_inside_complement
    [T1Space (_root_.ProjectiveSpectrum (grading K))]
    {A : Set X} (hA : A.Finite) {x : X} (hxA : x ∉ A) :
    ∃ φ : Φ,
      IsOpen ((markedNoncriticalExistence K X Φ map continuous_map
        exists_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
        x ∈ ((markedNoncriticalExistence K X Φ map continuous_map
          exists_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
          ((markedNoncriticalExistence K X Φ map continuous_map
            exists_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ⊆ Aᶜ := by
  exact (markedNoncriticalExistence K X Φ map continuous_map
    exists_for_finite_disjoint).exists_belyiOpen_inside_complement hA hxA

theorem markedNoncritical_exists_belyiOpen_containing_finite_inside_complement
    [T1Space (_root_.ProjectiveSpectrum (grading K))]
    {S T : Set X} (hS : S.Finite) (hT : T.Finite) (hdis : Disjoint S T) :
    ∃ φ : Φ,
      IsOpen ((markedNoncriticalExistence K X Φ map continuous_map
        exists_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
        T ⊆ ((markedNoncriticalExistence K X Φ map continuous_map
          exists_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
          ((markedNoncriticalExistence K X Φ map continuous_map
            exists_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ⊆ Sᶜ := by
  exact (markedNoncriticalExistence K X Φ map continuous_map
    exists_for_finite_disjoint).exists_belyiOpen_containing_finite_inside_complement hS hT hdis

theorem markedNoncritical_exists_belyiOpen_inside_open_of_finite_complement
    [T1Space (_root_.ProjectiveSpectrum (grading K))]
    {V : Set X} (hV : IsOpen V) (hVcompl : Vᶜ.Finite) {x : X} (hxV : x ∈ V) :
    ∃ φ : Φ,
      IsOpen ((markedNoncriticalExistence K X Φ map continuous_map
        exists_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
        x ∈ ((markedNoncriticalExistence K X Φ map continuous_map
          exists_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
          ((markedNoncriticalExistence K X Φ map continuous_map
            exists_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ⊆ V := by
  exact (markedNoncriticalExistence K X Φ map continuous_map
    exists_for_finite_disjoint).exists_belyiOpen_inside_open_of_finite_complement hV hVcompl hxV

theorem markedNoncritical_exists_belyiOpen_containing_finite_inside_open_of_finite_complement
    [T1Space (_root_.ProjectiveSpectrum (grading K))]
    {V T : Set X} (hV : IsOpen V) (hVcompl : Vᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ V) :
    ∃ φ : Φ,
      IsOpen ((markedNoncriticalExistence K X Φ map continuous_map
        exists_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
        T ⊆ ((markedNoncriticalExistence K X Φ map continuous_map
          exists_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
          ((markedNoncriticalExistence K X Φ map continuous_map
            exists_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ⊆ V := by
  exact (markedNoncriticalExistence K X Φ map continuous_map
    exists_for_finite_disjoint).exists_belyiOpen_containing_finite_inside_open_of_finite_complement
      hV hVcompl hT hTsub

theorem markedNoncritical_pointwise_cover_complement
    (κ : Type z) [Finite κ] {S : Set X} (hS : S.Finite)
    (x : κ → {x : X // x ∉ S}) :
    ∃ φ : Φ,
      (markedNoncriticalExistence K X Φ map continuous_map
        exists_for_finite_disjoint).toBelyiCoverData.sendsSetToBranch S φ ∧
        ∀ i, map φ (x i).1 ∉ markedPointSet K := by
  rcases (markedNoncriticalExistence K X Φ map continuous_map
    exists_for_finite_disjoint).pointwise_cover_complement hS x with ⟨φ, hφS, hφx⟩
  exact ⟨φ, hφS, hφx⟩

theorem markedNoncritical_finite_subcover_on_complement
    (κ : Type z) [Finite κ] [T1Space (_root_.ProjectiveSpectrum (grading K))]
    {S : Set X} (hS : S.Finite) [CompactSpace (κ → {x : X // x ∉ S})] :
    ∃ t : Finset {φ : Φ //
        (markedNoncriticalExistence K X Φ map continuous_map
          exists_for_finite_disjoint).toBelyiCoverData.sendsSetToBranch S φ},
      (⋃ φ ∈ t,
          ((markedNoncriticalExistence K X Φ map continuous_map
            exists_for_finite_disjoint).toBelyiCoverData.complementCoverData S).tupleAvoidSet
              (κ := κ) φ) =
        (Set.univ : Set (κ → {x : X // x ∉ S})) := by
  exact (markedNoncriticalExistence K X Φ map continuous_map
    exists_for_finite_disjoint).finite_subcover_on_complement (κ := κ) hS

section SchemeCarrierTarget

variable (schemeMap : Φ → X → P1 K)
variable (continuous_schemeMap : ∀ φ, Continuous (schemeMap φ))

/-- The same marked-branch cover data, now phrased with target carrier `P1 K`
instead of the raw `ProjectiveSpectrum` spelling. -/
def markedSchemeCoverData :
    BelyiCoverData X (P1 K) Φ where
  branch := markedSchemePointSet K
  branch_finite := markedSchemePointSet_finite K
  map := schemeMap
  continuous_map := continuous_schemeMap

theorem markedSchemeCoverData_branch :
    (markedSchemeCoverData K X Φ schemeMap continuous_schemeMap).branch =
      markedSchemePointSet K := rfl

theorem markedSchemeCoverData_sendsSetToBranch_iff
    (S : Set X) (φ : Φ) :
    (markedSchemeCoverData K X Φ schemeMap continuous_schemeMap).sendsSetToBranch S φ ↔
      ∀ x ∈ S, schemeMap φ x ∈ markedSchemePointSet K := by
  rfl

theorem markedSchemeCoverData_mem_belyiOpen_iff
    (φ : Φ) (x : X) :
    x ∈ (markedSchemeCoverData K X Φ schemeMap continuous_schemeMap).belyiOpen φ ↔
      schemeMap φ x ∉ markedSchemePointSet K := by
  rfl

theorem markedSchemeCoverData_branch_finite :
    (markedSchemeCoverData K X Φ schemeMap continuous_schemeMap).branch.Finite := by
  exact markedSchemePointSet_finite K

variable (exists_scheme_for_finite_disjoint :
  ∀ {S T : Set X}, S.Finite → T.Finite → Disjoint S T →
    ∃ φ : Φ, (∀ x ∈ S, schemeMap φ x ∈ markedSchemePointSet K) ∧
      ∀ x ∈ T, schemeMap φ x ∉ markedSchemePointSet K)

/-- The noncritical finite-set existence interface specialized to maps whose
target type is the scheme carrier `P1 K`. -/
def markedSchemeNoncriticalExistence :
    NoncriticalBelyiExistence X (P1 K) Φ where
  branch := markedSchemePointSet K
  branch_finite := markedSchemePointSet_finite K
  map := schemeMap
  continuous_map := continuous_schemeMap
  exists_for_finite_disjoint := by
    intro S T hS hT hdis
    rcases exists_scheme_for_finite_disjoint hS hT hdis with ⟨φ, hφS, hφT⟩
    exact ⟨φ, hφS, hφT⟩

theorem markedSchemeNoncriticalExistence_branch :
    (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
      exists_scheme_for_finite_disjoint).branch = markedSchemePointSet K := rfl

theorem markedSchemeNoncriticalExistence_toCoverData_branch :
    (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
      exists_scheme_for_finite_disjoint).toBelyiCoverData.branch = markedSchemePointSet K := rfl

theorem markedSchemeNoncritical_exists_belyiOpen_inside_complement
    [T1Space (P1 K)]
    {A : Set X} (hA : A.Finite) {x : X} (hxA : x ∉ A) :
    ∃ φ : Φ,
      IsOpen ((markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
        exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
        x ∈ ((markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
          exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
          ((markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
            exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ⊆ Aᶜ := by
  exact (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
    exists_scheme_for_finite_disjoint).exists_belyiOpen_inside_complement hA hxA

theorem markedSchemeNoncritical_exists_belyiOpen_containing_finite_inside_complement
    [T1Space (P1 K)]
    {S T : Set X} (hS : S.Finite) (hT : T.Finite) (hdis : Disjoint S T) :
    ∃ φ : Φ,
      IsOpen ((markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
        exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
        T ⊆ ((markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
          exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
          ((markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
            exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ⊆ Sᶜ := by
  exact (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
    exists_scheme_for_finite_disjoint).exists_belyiOpen_containing_finite_inside_complement hS hT hdis

theorem markedSchemeNoncritical_exists_belyiOpen_inside_open_of_finite_complement
    [T1Space (P1 K)]
    {V : Set X} (hV : IsOpen V) (hVcompl : Vᶜ.Finite) {x : X} (hxV : x ∈ V) :
    ∃ φ : Φ,
      IsOpen ((markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
        exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
        x ∈ ((markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
          exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
          ((markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
            exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ⊆ V := by
  exact (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
    exists_scheme_for_finite_disjoint).exists_belyiOpen_inside_open_of_finite_complement
      hV hVcompl hxV

theorem markedSchemeNoncritical_exists_belyiOpen_containing_finite_inside_open_of_finite_complement
    [T1Space (P1 K)]
    {V T : Set X} (hV : IsOpen V) (hVcompl : Vᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ V) :
    ∃ φ : Φ,
      IsOpen ((markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
        exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
        T ⊆ ((markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
          exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
          ((markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
            exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ⊆ V := by
  exact (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
    exists_scheme_for_finite_disjoint).exists_belyiOpen_containing_finite_inside_open_of_finite_complement
      hV hVcompl hT hTsub

theorem markedSchemeNoncritical_pointwise_cover_complement
    (κ : Type z) [Finite κ] {S : Set X} (hS : S.Finite)
    (x : κ → {x : X // x ∉ S}) :
    ∃ φ : Φ,
      (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
        exists_scheme_for_finite_disjoint).toBelyiCoverData.sendsSetToBranch S φ ∧
        ∀ i, schemeMap φ (x i).1 ∉ markedSchemePointSet K := by
  rcases (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
    exists_scheme_for_finite_disjoint).pointwise_cover_complement hS x with ⟨φ, hφS, hφx⟩
  exact ⟨φ, hφS, hφx⟩

theorem markedSchemeNoncritical_finite_subcover_on_complement
    (κ : Type z) [Finite κ] [T1Space (P1 K)]
    {S : Set X} (hS : S.Finite) [CompactSpace (κ → {x : X // x ∉ S})] :
    ∃ t : Finset {φ : Φ //
        (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
          exists_scheme_for_finite_disjoint).toBelyiCoverData.sendsSetToBranch S φ},
      (⋃ φ ∈ t,
          ((markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
            exists_scheme_for_finite_disjoint).toBelyiCoverData.complementCoverData S).tupleAvoidSet
              (κ := κ) φ) =
        (Set.univ : Set (κ → {x : X // x ∉ S})) := by
  exact (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
    exists_scheme_for_finite_disjoint).finite_subcover_on_complement (κ := κ) hS

end SchemeCarrierTarget

section PartialMapDomain

variable {C : Scheme.{u}}

/-- A partial map to `P1 K` gives a one-map Belyi-cover datum on its dense
domain, with branch set the checked scheme marked triple. -/
def partialMapMarkedCoverData
    (f : C.PartialMap (P1 K)) :
    BelyiCoverData f.domain (P1 K) Unit where
  branch := markedSchemePointSet K
  branch_finite := markedSchemePointSet_finite K
  map _ := RationalMaps.p1PartialMapDomainMap K f
  continuous_map _ := RationalMaps.continuous_p1PartialMapDomainMap K f

theorem partialMapMarkedCoverData_branch
    (f : C.PartialMap (P1 K)) :
    (partialMapMarkedCoverData K f).branch = markedSchemePointSet K := rfl

theorem partialMapMarkedCoverData_branch_finite
    (f : C.PartialMap (P1 K)) :
    (partialMapMarkedCoverData K f).branch.Finite := by
  exact markedSchemePointSet_finite K

theorem partialMapMarkedCoverData_sendsSetToBranch_iff
    (f : C.PartialMap (P1 K)) (S : Set f.domain) :
    (partialMapMarkedCoverData K f).sendsSetToBranch S () ↔
      ∀ x ∈ S, f.hom.base x ∈ markedSchemePointSet K := by
  rfl

theorem partialMapMarkedCoverData_mem_belyiOpen_iff
    (f : C.PartialMap (P1 K)) (x : f.domain) :
    x ∈ (partialMapMarkedCoverData K f).belyiOpen () ↔
      f.hom.base x ∉ markedSchemePointSet K := by
  rfl

end PartialMapDomain

end
end SchemeMarkedBelyi
end SourceStack
end HilbertTest
