import HilbertTest.SourceStack.BelyiCovers
import HilbertTest.SourceStack.SchemeBelyi
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

theorem markedNoncritical_exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
    [T1Space (_root_.ProjectiveSpectrum (grading K))] [NonemptyOpenFiniteComplement X]
    {V : Set X} (hV : IsOpen V) {x : X} (hxV : x ∈ V) :
    ∃ φ : Φ,
      IsOpen ((markedNoncriticalExistence K X Φ map continuous_map
        exists_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
        x ∈ ((markedNoncriticalExistence K X Φ map continuous_map
          exists_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
          ((markedNoncriticalExistence K X Φ map continuous_map
            exists_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ⊆ V := by
  exact (markedNoncriticalExistence K X Φ map continuous_map
    exists_for_finite_disjoint).exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement hV hxV

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

theorem markedSchemeNoncritical_exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
    [T1Space (P1 K)] [NonemptyOpenFiniteComplement X]
    {V : Set X} (hV : IsOpen V) {x : X} (hxV : x ∈ V) :
    ∃ φ : Φ,
      IsOpen ((markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
        exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
        x ∈ ((markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
          exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
          ((markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
            exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ⊆ V := by
  exact (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
    exists_scheme_for_finite_disjoint).exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
      hV hxV

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

theorem partialMapMarkedCoverData_map_apply
    (f : C.PartialMap (P1 K)) (x : f.domain) :
    (partialMapMarkedCoverData K f).map () x = f.hom.base x := by
  rfl

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

theorem partialMapMarkedCoverData_belyiOpen_eq
    (f : C.PartialMap (P1 K)) :
    (partialMapMarkedCoverData K f).belyiOpen () =
      {x : f.domain | f.hom.base x ∉ markedSchemePointSet K} := by
  rfl

theorem partialMapMarkedCoverData_belyiOpen_isOpen
    [T1Space (P1 K)] (f : C.PartialMap (P1 K)) :
    IsOpen ((partialMapMarkedCoverData K f).belyiOpen ()) := by
  exact (partialMapMarkedCoverData K f).belyiOpen_isOpen ()

theorem partialMapMarkedCoverData_belyiOpen_subset_compl_of_sendsSetToBranch
    (f : C.PartialMap (P1 K)) {S : Set f.domain}
    (hS : (partialMapMarkedCoverData K f).sendsSetToBranch S ()) :
    (partialMapMarkedCoverData K f).belyiOpen () ⊆ Sᶜ := by
  exact (partialMapMarkedCoverData K f).belyiOpen_subset_compl_of_sendsSetToBranch hS

/-- A rational map to `P1 K` from a reduced source gives one-map Belyi-cover
data on its canonical dense domain. -/
def rationalMapMarkedCoverData
    [IsReduced C] (f : C ⤏ P1 K) :
    BelyiCoverData f.domain (P1 K) Unit where
  branch := markedSchemePointSet K
  branch_finite := markedSchemePointSet_finite K
  map _ := RationalMaps.p1PartialMapDomainMap K f.toPartialMap
  continuous_map _ := RationalMaps.continuous_p1PartialMapDomainMap K f.toPartialMap

theorem rationalMapMarkedCoverData_branch
    [IsReduced C] (f : C ⤏ P1 K) :
    (rationalMapMarkedCoverData K f).branch = markedSchemePointSet K := rfl

theorem rationalMapMarkedCoverData_branch_finite
    [IsReduced C] (f : C ⤏ P1 K) :
    (rationalMapMarkedCoverData K f).branch.Finite := by
  exact markedSchemePointSet_finite K

theorem rationalMapMarkedCoverData_map_apply
    [IsReduced C] (f : C ⤏ P1 K) (x : f.domain) :
    (rationalMapMarkedCoverData K f).map () x = f.toPartialMap.hom.base x := by
  rfl

theorem rationalMapMarkedCoverData_sendsSetToBranch_iff
    [IsReduced C] (f : C ⤏ P1 K) (S : Set f.domain) :
    (rationalMapMarkedCoverData K f).sendsSetToBranch S () ↔
      ∀ x ∈ S, f.toPartialMap.hom.base x ∈ markedSchemePointSet K := by
  rfl

theorem rationalMapMarkedCoverData_mem_belyiOpen_iff
    [IsReduced C] (f : C ⤏ P1 K) (x : f.domain) :
    x ∈ (rationalMapMarkedCoverData K f).belyiOpen () ↔
      f.toPartialMap.hom.base x ∉ markedSchemePointSet K := by
  rfl

theorem rationalMapMarkedCoverData_belyiOpen_eq
    [IsReduced C] (f : C ⤏ P1 K) :
    (rationalMapMarkedCoverData K f).belyiOpen () =
      {x : f.domain | f.toPartialMap.hom.base x ∉ markedSchemePointSet K} := by
  rfl

theorem rationalMapMarkedCoverData_belyiOpen_isOpen
    [IsReduced C] [T1Space (P1 K)] (f : C ⤏ P1 K) :
    IsOpen ((rationalMapMarkedCoverData K f).belyiOpen ()) := by
  exact (rationalMapMarkedCoverData K f).belyiOpen_isOpen ()

theorem rationalMapMarkedCoverData_belyiOpen_subset_compl_of_sendsSetToBranch
    [IsReduced C] (f : C ⤏ P1 K) {S : Set f.domain}
    (hS : (rationalMapMarkedCoverData K f).sendsSetToBranch S ()) :
    (rationalMapMarkedCoverData K f).belyiOpen () ⊆ Sᶜ := by
  exact (rationalMapMarkedCoverData K f).belyiOpen_subset_compl_of_sendsSetToBranch hS

end PartialMapDomain

section MorphismFamily

variable (C : Scheme.{u})
variable (morphism : Φ → (C ⟶ P1 K))

/-- A family of honest scheme morphisms to `P1 K` gives marked-branch Belyi
cover data on the source carrier. -/
def morphismMarkedCoverData :
    BelyiCoverData C (P1 K) Φ where
  branch := markedSchemePointSet K
  branch_finite := markedSchemePointSet_finite K
  map φ x := (morphism φ).base x
  continuous_map φ := (morphism φ).continuous

theorem morphismMarkedCoverData_branch :
    (morphismMarkedCoverData K Φ C morphism).branch = markedSchemePointSet K := rfl

theorem morphismMarkedCoverData_branch_finite :
    (morphismMarkedCoverData K Φ C morphism).branch.Finite := by
  exact markedSchemePointSet_finite K

theorem morphismMarkedCoverData_map_apply
    (φ : Φ) (x : C) :
    (morphismMarkedCoverData K Φ C morphism).map φ x = (morphism φ).base x := by
  rfl

theorem morphismMarkedCoverData_sendsSetToBranch_iff
    (S : Set C) (φ : Φ) :
    (morphismMarkedCoverData K Φ C morphism).sendsSetToBranch S φ ↔
      ∀ x ∈ S, (morphism φ).base x ∈ markedSchemePointSet K := by
  rfl

theorem morphismMarkedCoverData_mem_belyiOpen_iff
    (φ : Φ) (x : C) :
    x ∈ (morphismMarkedCoverData K Φ C morphism).belyiOpen φ ↔
      (morphism φ).base x ∉ markedSchemePointSet K := by
  rfl

theorem morphismMarkedCoverData_belyiOpen_eq
    (φ : Φ) :
    (morphismMarkedCoverData K Φ C morphism).belyiOpen φ =
      {x : C | (morphism φ).base x ∉ markedSchemePointSet K} := by
  rfl

theorem morphismMarkedCoverData_belyiOpen_isOpen
    [T1Space (P1 K)] (φ : Φ) :
    IsOpen ((morphismMarkedCoverData K Φ C morphism).belyiOpen φ) := by
  exact (morphismMarkedCoverData K Φ C morphism).belyiOpen_isOpen φ

theorem morphismMarkedCoverData_belyiOpen_subset_compl_of_sendsSetToBranch
    {S : Set C} {φ : Φ}
    (hS : (morphismMarkedCoverData K Φ C morphism).sendsSetToBranch S φ) :
    (morphismMarkedCoverData K Φ C morphism).belyiOpen φ ⊆ Sᶜ := by
  exact (morphismMarkedCoverData K Φ C morphism).belyiOpen_subset_compl_of_sendsSetToBranch hS

variable (exists_morphism_for_finite_disjoint :
  ∀ {S T : Set C}, S.Finite → T.Finite → Disjoint S T →
    ∃ φ : Φ, (∀ x ∈ S, (morphism φ).base x ∈ markedSchemePointSet K) ∧
      ∀ x ∈ T, (morphism φ).base x ∉ markedSchemePointSet K)

/-- The noncritical finite-set existence interface specialized to honest
scheme-morphism families `C ⟶ P1 K`. -/
def morphismMarkedNoncriticalExistence :
    NoncriticalBelyiExistence C (P1 K) Φ where
  branch := markedSchemePointSet K
  branch_finite := markedSchemePointSet_finite K
  map φ x := (morphism φ).base x
  continuous_map φ := (morphism φ).continuous
  exists_for_finite_disjoint := by
    intro S T hS hT hdis
    rcases exists_morphism_for_finite_disjoint hS hT hdis with ⟨φ, hφS, hφT⟩
    exact ⟨φ, hφS, hφT⟩

theorem morphismMarkedNoncriticalExistence_branch :
    (morphismMarkedNoncriticalExistence K Φ C morphism
      exists_morphism_for_finite_disjoint).branch = markedSchemePointSet K := rfl

theorem morphismMarkedNoncriticalExistence_toCoverData_branch :
    (morphismMarkedNoncriticalExistence K Φ C morphism
      exists_morphism_for_finite_disjoint).toBelyiCoverData.branch =
      markedSchemePointSet K := rfl

theorem morphismMarkedNoncritical_exists_belyiOpen_inside_complement
    [T1Space (P1 K)]
    {A : Set C} (hA : A.Finite) {x : C} (hxA : x ∉ A) :
    ∃ φ : Φ,
      IsOpen ((morphismMarkedNoncriticalExistence K Φ C morphism
        exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
        x ∈ ((morphismMarkedNoncriticalExistence K Φ C morphism
          exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
          ((morphismMarkedNoncriticalExistence K Φ C morphism
            exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ⊆ Aᶜ := by
  exact (morphismMarkedNoncriticalExistence K Φ C morphism
    exists_morphism_for_finite_disjoint).exists_belyiOpen_inside_complement hA hxA

theorem morphismMarkedNoncritical_exists_belyiOpen_containing_finite_inside_complement
    [T1Space (P1 K)]
    {S T : Set C} (hS : S.Finite) (hT : T.Finite) (hdis : Disjoint S T) :
    ∃ φ : Φ,
      IsOpen ((morphismMarkedNoncriticalExistence K Φ C morphism
        exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
        T ⊆ ((morphismMarkedNoncriticalExistence K Φ C morphism
          exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
          ((morphismMarkedNoncriticalExistence K Φ C morphism
            exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ⊆ Sᶜ := by
  exact (morphismMarkedNoncriticalExistence K Φ C morphism
    exists_morphism_for_finite_disjoint).exists_belyiOpen_containing_finite_inside_complement
      hS hT hdis

theorem morphismMarkedNoncritical_exists_belyiOpen_inside_open_of_finite_complement
    [T1Space (P1 K)]
    {V : Set C} (hV : IsOpen V) (hVcompl : Vᶜ.Finite) {x : C} (hxV : x ∈ V) :
    ∃ φ : Φ,
      IsOpen ((morphismMarkedNoncriticalExistence K Φ C morphism
        exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
        x ∈ ((morphismMarkedNoncriticalExistence K Φ C morphism
          exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
          ((morphismMarkedNoncriticalExistence K Φ C morphism
            exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ⊆ V := by
  exact (morphismMarkedNoncriticalExistence K Φ C morphism
    exists_morphism_for_finite_disjoint).exists_belyiOpen_inside_open_of_finite_complement
      hV hVcompl hxV

theorem morphismMarkedNoncritical_exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
    [T1Space (P1 K)] [NonemptyOpenFiniteComplement C]
    {V : Set C} (hV : IsOpen V) {x : C} (hxV : x ∈ V) :
    ∃ φ : Φ,
      IsOpen ((morphismMarkedNoncriticalExistence K Φ C morphism
        exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
        x ∈ ((morphismMarkedNoncriticalExistence K Φ C morphism
          exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
          ((morphismMarkedNoncriticalExistence K Φ C morphism
            exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ⊆ V := by
  exact (morphismMarkedNoncriticalExistence K Φ C morphism
    exists_morphism_for_finite_disjoint).exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
      hV hxV

theorem morphismMarkedNoncritical_exists_belyiOpen_containing_finite_inside_open_of_finite_complement
    [T1Space (P1 K)]
    {V T : Set C} (hV : IsOpen V) (hVcompl : Vᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ V) :
    ∃ φ : Φ,
      IsOpen ((morphismMarkedNoncriticalExistence K Φ C morphism
        exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
        T ⊆ ((morphismMarkedNoncriticalExistence K Φ C morphism
          exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
          ((morphismMarkedNoncriticalExistence K Φ C morphism
            exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ⊆ V := by
  exact (morphismMarkedNoncriticalExistence K Φ C morphism
    exists_morphism_for_finite_disjoint).exists_belyiOpen_containing_finite_inside_open_of_finite_complement
      hV hVcompl hT hTsub

theorem morphismMarkedNoncritical_pointwise_cover_complement
    (κ : Type z) [Finite κ] {S : Set C} (hS : S.Finite)
    (x : κ → {x : C // x ∉ S}) :
    ∃ φ : Φ,
      (morphismMarkedNoncriticalExistence K Φ C morphism
        exists_morphism_for_finite_disjoint).toBelyiCoverData.sendsSetToBranch S φ ∧
        ∀ i, (morphism φ).base (x i).1 ∉ markedSchemePointSet K := by
  rcases (morphismMarkedNoncriticalExistence K Φ C morphism
    exists_morphism_for_finite_disjoint).pointwise_cover_complement hS x with ⟨φ, hφS, hφx⟩
  exact ⟨φ, hφS, hφx⟩

theorem morphismMarkedNoncritical_finite_subcover_on_complement
    (κ : Type z) [Finite κ] [T1Space (P1 K)]
    {S : Set C} (hS : S.Finite) [CompactSpace (κ → {x : C // x ∉ S})] :
    ∃ t : Finset {φ : Φ //
        (morphismMarkedNoncriticalExistence K Φ C morphism
          exists_morphism_for_finite_disjoint).toBelyiCoverData.sendsSetToBranch S φ},
      (⋃ φ ∈ t,
          ((morphismMarkedNoncriticalExistence K Φ C morphism
            exists_morphism_for_finite_disjoint).toBelyiCoverData.complementCoverData S).tupleAvoidSet
              (κ := κ) φ) =
        (Set.univ : Set (κ → {x : C // x ∉ S})) := by
  exact (morphismMarkedNoncriticalExistence K Φ C morphism
    exists_morphism_for_finite_disjoint).finite_subcover_on_complement (κ := κ) hS

end MorphismFamily

section SchemeBelyiMapBridge

variable {C : Scheme.{u}}
variable (hmarkedOpen : IsOpen (markedSchemePointSet K)ᶜ)
variable (φ : SchemeBelyi.BelyiMap (SchemeBelyi.markedBelyiTarget K hmarkedOpen) C)

/-- A scheme-level Belyi map to the marked `P1 K` target gives the corresponding
one-map marked cover datum on the source carrier. -/
def schemeBelyiMapMarkedCoverData :
    BelyiCoverData C (P1 K) Unit :=
  morphismMarkedCoverData K Unit C (fun _ => φ.hom)

theorem schemeBelyiMapMarkedCoverData_branch :
    (schemeBelyiMapMarkedCoverData K hmarkedOpen φ).branch =
      markedSchemePointSet K := rfl

theorem schemeBelyiMapMarkedCoverData_branch_finite :
    (schemeBelyiMapMarkedCoverData K hmarkedOpen φ).branch.Finite := by
  exact markedSchemePointSet_finite K

theorem schemeBelyiMapMarkedCoverData_map_apply
    (x : C) :
    (schemeBelyiMapMarkedCoverData K hmarkedOpen φ).map () x = φ.hom.base x := by
  rfl

theorem schemeBelyiMapMarkedCoverData_mem_belyiOpen_iff
    (x : C) :
    x ∈ (schemeBelyiMapMarkedCoverData K hmarkedOpen φ).belyiOpen () ↔
      φ.hom.base x ∉ markedSchemePointSet K := by
  rfl

theorem schemeBelyiMapMarkedCoverData_belyiOpen_eq_schemeBelyi :
    (schemeBelyiMapMarkedCoverData K hmarkedOpen φ).belyiOpen () =
      (φ.belyiOpen : Set C) := by
  rfl

theorem schemeBelyiMapMarkedCoverData_belyiOpen_isOpen :
    IsOpen ((schemeBelyiMapMarkedCoverData K hmarkedOpen φ).belyiOpen ()) := by
  rw [schemeBelyiMapMarkedCoverData_belyiOpen_eq_schemeBelyi K hmarkedOpen φ]
  exact φ.belyiOpen.2

variable (φfin :
  SchemeBelyi.FiniteBelyiMap (SchemeBelyi.markedBelyiTarget K hmarkedOpen) C)

/-- A finite scheme-level Belyi map to the marked `P1 K` target gives the same
one-map marked cover datum after forgetting finiteness. -/
def finiteSchemeBelyiMapMarkedCoverData :
    BelyiCoverData C (P1 K) Unit :=
  schemeBelyiMapMarkedCoverData K hmarkedOpen φfin.toBelyiMap

theorem finiteSchemeBelyiMapMarkedCoverData_branch :
    (finiteSchemeBelyiMapMarkedCoverData K hmarkedOpen φfin).branch =
      markedSchemePointSet K := rfl

theorem finiteSchemeBelyiMapMarkedCoverData_isFinite_hom :
    IsFinite φfin.hom :=
  φfin.finite_hom

theorem finiteSchemeBelyiMapMarkedCoverData_map_apply
    (x : C) :
    (finiteSchemeBelyiMapMarkedCoverData K hmarkedOpen φfin).map () x =
      φfin.hom.base x := by
  rfl

theorem finiteSchemeBelyiMapMarkedCoverData_belyiOpen_eq_schemeBelyi :
    (finiteSchemeBelyiMapMarkedCoverData K hmarkedOpen φfin).belyiOpen () =
      (φfin.toBelyiMap.belyiOpen : Set C) := by
  rfl

theorem finiteSchemeBelyiMapMarkedCoverData_belyiOpen_isOpen :
    IsOpen ((finiteSchemeBelyiMapMarkedCoverData K hmarkedOpen φfin).belyiOpen ()) := by
  rw [finiteSchemeBelyiMapMarkedCoverData_belyiOpen_eq_schemeBelyi K hmarkedOpen φfin]
  exact φfin.toBelyiMap.belyiOpen.2

end SchemeBelyiMapBridge

section FiniteMarkedBelyiExistence

/-- Paper-facing source interface: a family of finite scheme-level Belyi maps to
the marked `P1 K` target that satisfies the Theorem 2.5 finite disjoint-set
condition.  The missing curve/Riemann-Roch theorem is precisely an
instantiation of this structure for smooth proper connected curves. -/
structure FiniteMarkedBelyiExistence
    (K : Type u) [CommRing K] [IsDomain K] (Φ : Type w) (C : Scheme.{u}) where
  hmarkedOpen : IsOpen (markedSchemePointSet K)ᶜ
  map : Φ → SchemeBelyi.FiniteBelyiMap (SchemeBelyi.markedBelyiTarget K hmarkedOpen) C
  exists_for_finite_disjoint :
    ∀ {S T : Set C}, S.Finite → T.Finite → Disjoint S T →
      ∃ φ : Φ, (∀ x ∈ S, (map φ).hom.base x ∈ markedSchemePointSet K) ∧
        ∀ x ∈ T, (map φ).hom.base x ∉ markedSchemePointSet K

namespace FiniteMarkedBelyiExistence

variable {C : Scheme.{u}} (F : FiniteMarkedBelyiExistence K Φ C)

/-- Forget a finite marked Belyi family to its underlying morphism family. -/
def morphism : Φ → (C ⟶ P1 K) :=
  fun φ => (F.map φ).hom

/-- The topological marked cover data attached to a finite marked Belyi family. -/
def toMarkedCoverData :
    BelyiCoverData C (P1 K) Φ :=
  morphismMarkedCoverData K Φ C (morphism K Φ F)

/-- The noncritical finite-set existence interface attached to a finite marked
Belyi family. -/
def toMarkedNoncriticalExistence :
    NoncriticalBelyiExistence C (P1 K) Φ :=
  morphismMarkedNoncriticalExistence K Φ C (morphism K Φ F) F.exists_for_finite_disjoint

theorem toMarkedCoverData_branch :
    (toMarkedCoverData K Φ F).branch = markedSchemePointSet K := rfl

theorem toMarkedNoncriticalExistence_branch :
    (toMarkedNoncriticalExistence K Φ F).branch = markedSchemePointSet K := rfl

theorem map_apply
    (φ : Φ) (x : C) :
    (toMarkedCoverData K Φ F).map φ x = (F.map φ).hom.base x := by
  rfl

theorem finite_hom
    (φ : Φ) :
    IsFinite (F.map φ).hom :=
  (F.map φ).finite_hom

theorem mem_belyiOpen_iff
    (φ : Φ) (x : C) :
    x ∈ (toMarkedCoverData K Φ F).belyiOpen φ ↔
      (F.map φ).hom.base x ∉ markedSchemePointSet K := by
  rfl

theorem belyiOpen_eq_schemeBelyi
    (φ : Φ) :
    (toMarkedCoverData K Φ F).belyiOpen φ =
      ((F.map φ).toBelyiMap.belyiOpen : Set C) := by
  rfl

theorem belyiOpen_isOpen
    (φ : Φ) :
    IsOpen ((toMarkedCoverData K Φ F).belyiOpen φ) := by
  rw [belyiOpen_eq_schemeBelyi K Φ F φ]
  exact (F.map φ).toBelyiMap.belyiOpen.2

theorem exists_belyiOpen_inside_complement
    [T1Space (P1 K)]
    {A : Set C} (hA : A.Finite) {x : C} (hxA : x ∉ A) :
    ∃ φ : Φ,
      IsOpen ((toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ) ∧
        x ∈ ((toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ) ∧
          ((toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ) ⊆ Aᶜ := by
  exact (toMarkedNoncriticalExistence K Φ F).exists_belyiOpen_inside_complement hA hxA

theorem exists_belyiOpen_containing_finite_inside_complement
    [T1Space (P1 K)]
    {S T : Set C} (hS : S.Finite) (hT : T.Finite) (hdis : Disjoint S T) :
    ∃ φ : Φ,
      IsOpen ((toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ) ∧
        T ⊆ ((toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ) ∧
          ((toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ) ⊆ Sᶜ := by
  exact (toMarkedNoncriticalExistence K Φ F).exists_belyiOpen_containing_finite_inside_complement
    hS hT hdis

theorem exists_belyiOpen_inside_open_of_finite_complement
    [T1Space (P1 K)]
    {V : Set C} (hV : IsOpen V) (hVcompl : Vᶜ.Finite) {x : C} (hxV : x ∈ V) :
    ∃ φ : Φ,
      IsOpen ((toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ) ∧
        x ∈ ((toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ) ∧
          ((toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ) ⊆ V := by
  exact (toMarkedNoncriticalExistence K Φ F).exists_belyiOpen_inside_open_of_finite_complement
    hV hVcompl hxV

theorem exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
    [T1Space (P1 K)] [NonemptyOpenFiniteComplement C]
    {V : Set C} (hV : IsOpen V) {x : C} (hxV : x ∈ V) :
    ∃ φ : Φ,
      IsOpen ((toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ) ∧
        x ∈ ((toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ) ∧
          ((toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ) ⊆ V := by
  exact
    (toMarkedNoncriticalExistence K Φ F).exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
      hV hxV

theorem exists_belyiOpen_containing_finite_inside_open_of_finite_complement
    [T1Space (P1 K)]
    {V T : Set C} (hV : IsOpen V) (hVcompl : Vᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ V) :
    ∃ φ : Φ,
      IsOpen ((toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ) ∧
        T ⊆ ((toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ) ∧
          ((toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ) ⊆ V := by
  exact
    (toMarkedNoncriticalExistence K Φ F).exists_belyiOpen_containing_finite_inside_open_of_finite_complement
      hV hVcompl hT hTsub

theorem pointwise_cover_complement
    (κ : Type z) [Finite κ] {S : Set C} (hS : S.Finite)
    (x : κ → {x : C // x ∉ S}) :
    ∃ φ : Φ,
      (toMarkedCoverData K Φ F).sendsSetToBranch S φ ∧
        ∀ i, (F.map φ).hom.base (x i).1 ∉ markedSchemePointSet K := by
  rcases (toMarkedNoncriticalExistence K Φ F).pointwise_cover_complement hS x with
    ⟨φ, hφS, hφx⟩
  exact ⟨φ, hφS, hφx⟩

theorem finite_subcover_on_complement
    (κ : Type z) [Finite κ] [T1Space (P1 K)]
    {S : Set C} (hS : S.Finite) [CompactSpace (κ → {x : C // x ∉ S})] :
    ∃ t : Finset {φ : Φ // (toMarkedCoverData K Φ F).sendsSetToBranch S φ},
      (⋃ φ ∈ t, ((toMarkedCoverData K Φ F).complementCoverData S).tupleAvoidSet
          (κ := κ) φ) =
        (Set.univ : Set (κ → {x : C // x ∉ S})) := by
  exact (toMarkedNoncriticalExistence K Φ F).finite_subcover_on_complement (κ := κ) hS

end FiniteMarkedBelyiExistence

end FiniteMarkedBelyiExistence

end
end SchemeMarkedBelyi
end SourceStack
end HilbertTest
