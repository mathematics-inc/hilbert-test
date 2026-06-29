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

theorem markedCoverData_belyiOpen_carrier
    (φ : Φ) :
    (markedCoverData K X Φ map continuous_map).belyiOpen φ =
      {x : X | map φ x ∉ markedPointSet K} := by
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

theorem markedNoncriticalExistence_map_apply
    (φ : Φ) (x : X) :
    (markedNoncriticalExistence K X Φ map continuous_map
      exists_for_finite_disjoint).map φ x = map φ x := by
  rfl

theorem markedNoncriticalExistence_toCoverData_map_apply
    (φ : Φ) (x : X) :
    (markedNoncriticalExistence K X Φ map continuous_map
      exists_for_finite_disjoint).toBelyiCoverData.map φ x = map φ x := by
  rfl

theorem markedNoncriticalExistence_mem_belyiOpen_iff
    (φ : Φ) (x : X) :
    x ∈ (markedNoncriticalExistence K X Φ map continuous_map
      exists_for_finite_disjoint).toBelyiCoverData.belyiOpen φ ↔
      map φ x ∉ markedPointSet K := by
  exact
    NoncriticalBelyiExistence.mem_belyiOpen_iff
      (markedNoncriticalExistence K X Φ map continuous_map exists_for_finite_disjoint) φ x

theorem markedNoncriticalExistence_belyiOpen_carrier
    (φ : Φ) :
    (markedNoncriticalExistence K X Φ map continuous_map
      exists_for_finite_disjoint).toBelyiCoverData.belyiOpen φ =
      {x : X | map φ x ∉ markedPointSet K} := by
  exact
    NoncriticalBelyiExistence.belyiOpen_carrier
      (markedNoncriticalExistence K X Φ map continuous_map exists_for_finite_disjoint) φ

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

theorem markedNoncritical_exists_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
    [T1Space (_root_.ProjectiveSpectrum (grading K))] [NonemptyOpenFiniteComplement X]
    {V T : Set X} (hV : IsOpen V) (hVne : V.Nonempty)
    (hT : T.Finite) (hTsub : T ⊆ V) :
    ∃ φ : Φ,
      IsOpen ((markedNoncriticalExistence K X Φ map continuous_map
        exists_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
        T ⊆ ((markedNoncriticalExistence K X Φ map continuous_map
          exists_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
          ((markedNoncriticalExistence K X Φ map continuous_map
            exists_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ⊆ V := by
  exact (markedNoncriticalExistence K X Φ map continuous_map
    exists_for_finite_disjoint).exists_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
      hV hVne hT hTsub

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

/-- Membership form of the marked-triple finite subcover over a fixed
complement. -/
theorem markedNoncritical_finite_subcover_on_complement_forall
    (κ : Type z) [Finite κ] [T1Space (_root_.ProjectiveSpectrum (grading K))]
    {S : Set X} (hS : S.Finite) [CompactSpace (κ → {x : X // x ∉ S})] :
    ∃ t : Finset {φ : Φ //
        (markedNoncriticalExistence K X Φ map continuous_map
          exists_for_finite_disjoint).toBelyiCoverData.sendsSetToBranch S φ},
      ∀ x : κ → {x : X // x ∉ S},
        ∃ φ ∈ t,
          x ∈ ((markedNoncriticalExistence K X Φ map continuous_map
            exists_for_finite_disjoint).toBelyiCoverData.complementCoverData S).tupleAvoidSet
              (κ := κ) φ := by
  exact (markedNoncriticalExistence K X Φ map continuous_map
    exists_for_finite_disjoint).finite_subcover_on_complement_forall (κ := κ) hS

/-- Concrete branch-avoidance form of the raw marked-`Proj` finite subcover
over a fixed complement. -/
theorem markedNoncritical_finite_subcover_on_complement_forall_avoidance
    (κ : Type z) [Finite κ] [T1Space (_root_.ProjectiveSpectrum (grading K))]
    {S : Set X} (hS : S.Finite) [CompactSpace (κ → {x : X // x ∉ S})] :
    ∃ t : Finset {φ : Φ //
        (markedNoncriticalExistence K X Φ map continuous_map
          exists_for_finite_disjoint).toBelyiCoverData.sendsSetToBranch S φ},
      ∀ x : κ → {x : X // x ∉ S},
        ∃ φ ∈ t, ∀ i, map φ.1 (x i).1 ∉ markedPointSet K := by
  rcases markedNoncritical_finite_subcover_on_complement_forall
      K X Φ map continuous_map exists_for_finite_disjoint κ hS with
    ⟨t, ht⟩
  refine ⟨t, ?_⟩
  intro x
  rcases ht x with ⟨φ, hφt, hxφ⟩
  exact ⟨φ, hφt, hxφ⟩

/-- Raw marked-`Proj` noncritical compact-exhaustion cover bridge. -/
theorem markedNoncritical_finite_compact_cover_by_belyiOpen_exhaustions
    [T1Space (_root_.ProjectiveSpectrum (grading K))]
    [NonemptyOpenFiniteComplement X] [CompactSpace X]
    (Kex : ∀ φ : Φ,
      CompactExhaustion ((markedNoncriticalExistence K X Φ map continuous_map
        exists_for_finite_disjoint).toBelyiCoverData.belyiOpen φ)) :
    ∃ t : Finset (Φ × ℕ),
      (∀ p ∈ t,
        IsCompact ((Subtype.val :
          (markedNoncriticalExistence K X Φ map continuous_map
            exists_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 → X) ''
            (Kex p.1 p.2))) ∧
        (∀ p ∈ t,
          ((Subtype.val :
            (markedNoncriticalExistence K X Φ map continuous_map
              exists_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 → X) ''
              (Kex p.1 p.2)) ⊆
                (markedNoncriticalExistence K X Φ map continuous_map
                  exists_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1) ∧
          (Set.univ : Set X) ⊆
            ⋃ p ∈ t,
              (Subtype.val :
                (markedNoncriticalExistence K X Φ map continuous_map
                  exists_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 → X) ''
                (Kex p.1 p.2) := by
  exact
    (markedNoncriticalExistence K X Φ map continuous_map
      exists_for_finite_disjoint).finite_compact_cover_by_belyiOpen_exhaustions
      Kex

/-- Equality form of the raw marked-`Proj` compact-exhaustion cover bridge. -/
theorem markedNoncritical_finite_compact_cover_by_belyiOpen_exhaustions_eq_univ
    [T1Space (_root_.ProjectiveSpectrum (grading K))]
    [NonemptyOpenFiniteComplement X] [CompactSpace X]
    (Kex : ∀ φ : Φ,
      CompactExhaustion ((markedNoncriticalExistence K X Φ map continuous_map
        exists_for_finite_disjoint).toBelyiCoverData.belyiOpen φ)) :
    ∃ t : Finset (Φ × ℕ),
      (∀ p ∈ t,
        IsCompact ((Subtype.val :
          (markedNoncriticalExistence K X Φ map continuous_map
            exists_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 → X) ''
            (Kex p.1 p.2))) ∧
        (∀ p ∈ t,
          ((Subtype.val :
            (markedNoncriticalExistence K X Φ map continuous_map
              exists_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 → X) ''
              (Kex p.1 p.2)) ⊆
                (markedNoncriticalExistence K X Φ map continuous_map
                  exists_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1) ∧
          (⋃ p ∈ t,
            (Subtype.val :
              (markedNoncriticalExistence K X Φ map continuous_map
                exists_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 → X) ''
              (Kex p.1 p.2)) = (Set.univ : Set X) := by
  exact
    (markedNoncriticalExistence K X Φ map continuous_map
      exists_for_finite_disjoint).finite_compact_cover_by_belyiOpen_exhaustions_eq_univ
      Kex

/-- Raw marked-`Proj` noncritical compact-cover bridge with compact exhaustions
supplied by local compactness and second countability. -/
theorem markedNoncritical_finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact
    [T1Space (_root_.ProjectiveSpectrum (grading K))]
    [NonemptyOpenFiniteComplement X] [CompactSpace X]
    [LocallyCompactSpace X] [SecondCountableTopology X] :
    ∃ Kex : ∀ φ : Φ,
      CompactExhaustion ((markedNoncriticalExistence K X Φ map continuous_map
        exists_for_finite_disjoint).toBelyiCoverData.belyiOpen φ),
      ∃ t : Finset (Φ × ℕ),
        (∀ p ∈ t,
          IsCompact ((Subtype.val :
            (markedNoncriticalExistence K X Φ map continuous_map
              exists_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 → X) ''
              (Kex p.1 p.2))) ∧
          (∀ p ∈ t,
            ((Subtype.val :
              (markedNoncriticalExistence K X Φ map continuous_map
                exists_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 → X) ''
                (Kex p.1 p.2)) ⊆
                  (markedNoncriticalExistence K X Φ map continuous_map
                    exists_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1) ∧
            (Set.univ : Set X) ⊆
              ⋃ p ∈ t,
                (Subtype.val :
                  (markedNoncriticalExistence K X Φ map continuous_map
                    exists_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 → X) ''
                  (Kex p.1 p.2) := by
  exact
    (markedNoncriticalExistence K X Φ map continuous_map
      exists_for_finite_disjoint).finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact

/-- Equality form of the raw marked-`Proj` compact-cover bridge with compact
exhaustions supplied by local compactness and second countability. -/
theorem markedNoncritical_finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact_eq_univ
    [T1Space (_root_.ProjectiveSpectrum (grading K))]
    [NonemptyOpenFiniteComplement X] [CompactSpace X]
    [LocallyCompactSpace X] [SecondCountableTopology X] :
    ∃ Kex : ∀ φ : Φ,
      CompactExhaustion ((markedNoncriticalExistence K X Φ map continuous_map
        exists_for_finite_disjoint).toBelyiCoverData.belyiOpen φ),
      ∃ t : Finset (Φ × ℕ),
        (∀ p ∈ t,
          IsCompact ((Subtype.val :
            (markedNoncriticalExistence K X Φ map continuous_map
              exists_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 → X) ''
              (Kex p.1 p.2))) ∧
          (∀ p ∈ t,
            ((Subtype.val :
              (markedNoncriticalExistence K X Φ map continuous_map
                exists_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 → X) ''
                (Kex p.1 p.2)) ⊆
                  (markedNoncriticalExistence K X Φ map continuous_map
                    exists_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1) ∧
            (⋃ p ∈ t,
              (Subtype.val :
                (markedNoncriticalExistence K X Φ map continuous_map
                  exists_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 → X) ''
                (Kex p.1 p.2)) = (Set.univ : Set X) := by
  exact
    (markedNoncriticalExistence K X Φ map continuous_map
      exists_for_finite_disjoint).finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact_eq_univ

/-- Raw marked-`Proj` noncritical compact-coordinate Corollary 3.2 bridge. -/
theorem markedNoncritical_finite_compact_coordinate_sets_of_belyiOpen_exhaustions
    [T1Space (_root_.ProjectiveSpectrum (grading K))]
    [NonemptyOpenFiniteComplement X] [CompactSpace X]
    [LocallyCompactSpace X] [SecondCountableTopology X]
    {κ : Type z} {Z : κ → Type*} [∀ j, TopologicalSpace (Z j)]
    (G : Φ → X → ((j : κ) → Z j))
    (hG : ∀ φ, Continuous (G φ))
    (A : (j : κ) → Set (Z j))
    (hGA : ∀ φ x,
      x ∈ (markedNoncriticalExistence K X Φ map continuous_map
        exists_for_finite_disjoint).toBelyiCoverData.belyiOpen φ →
        ∀ j, G φ x j ∈ A j) :
    ∃ Kex : ∀ φ : Φ,
      CompactExhaustion ((markedNoncriticalExistence K X Φ map continuous_map
        exists_for_finite_disjoint).toBelyiCoverData.belyiOpen φ),
      ∃ t : Finset (Φ × ℕ),
        ∃ H : (j : κ) → Set (Z j),
          (∀ j, IsCompact (H j)) ∧
            (∀ j, H j ⊆ A j) ∧
              (Set.univ : Set X) ⊆
                ⋃ p ∈ t,
                  (Subtype.val :
                    (markedNoncriticalExistence K X Φ map continuous_map
                      exists_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 →
                      X) ''
                    (Kex p.1 p.2) ∧
                ∀ p ∈ t, ∀ x,
                  x ∈ (Subtype.val :
                    (markedNoncriticalExistence K X Φ map continuous_map
                      exists_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 →
                      X) ''
                      (Kex p.1 p.2) →
                    ∀ j, G p.1 x j ∈ H j := by
  exact
    (markedNoncriticalExistence K X Φ map continuous_map
      exists_for_finite_disjoint).finite_compact_coordinate_sets_of_belyiOpen_exhaustions
      G hG A hGA

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

theorem markedSchemeCoverData_belyiOpen_carrier
    (φ : Φ) :
    (markedSchemeCoverData K X Φ schemeMap continuous_schemeMap).belyiOpen φ =
      {x : X | schemeMap φ x ∉ markedSchemePointSet K} := by
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

theorem markedSchemeNoncriticalExistence_map_apply
    (φ : Φ) (x : X) :
    (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
      exists_scheme_for_finite_disjoint).map φ x = schemeMap φ x := by
  rfl

theorem markedSchemeNoncriticalExistence_toCoverData_map_apply
    (φ : Φ) (x : X) :
    (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
      exists_scheme_for_finite_disjoint).toBelyiCoverData.map φ x = schemeMap φ x := by
  rfl

theorem markedSchemeNoncriticalExistence_mem_belyiOpen_iff
    (φ : Φ) (x : X) :
    x ∈ (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
      exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen φ ↔
      schemeMap φ x ∉ markedSchemePointSet K := by
  exact
    NoncriticalBelyiExistence.mem_belyiOpen_iff
      (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
        exists_scheme_for_finite_disjoint) φ x

theorem markedSchemeNoncriticalExistence_belyiOpen_carrier
    (φ : Φ) :
    (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
      exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen φ =
      {x : X | schemeMap φ x ∉ markedSchemePointSet K} := by
  exact
    NoncriticalBelyiExistence.belyiOpen_carrier
      (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
        exists_scheme_for_finite_disjoint) φ

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

theorem markedSchemeNoncritical_exists_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
    [T1Space (P1 K)] [NonemptyOpenFiniteComplement X]
    {V T : Set X} (hV : IsOpen V) (hVne : V.Nonempty)
    (hT : T.Finite) (hTsub : T ⊆ V) :
    ∃ φ : Φ,
      IsOpen ((markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
        exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
        T ⊆ ((markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
          exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
          ((markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
            exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ⊆ V := by
  exact (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
    exists_scheme_for_finite_disjoint).exists_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
      hV hVne hT hTsub

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

/-- Membership form of the scheme-carrier marked finite subcover over a fixed
complement. -/
theorem markedSchemeNoncritical_finite_subcover_on_complement_forall
    (κ : Type z) [Finite κ] [T1Space (P1 K)]
    {S : Set X} (hS : S.Finite) [CompactSpace (κ → {x : X // x ∉ S})] :
    ∃ t : Finset {φ : Φ //
        (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
          exists_scheme_for_finite_disjoint).toBelyiCoverData.sendsSetToBranch S φ},
      ∀ x : κ → {x : X // x ∉ S},
        ∃ φ ∈ t,
          x ∈ ((markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
            exists_scheme_for_finite_disjoint).toBelyiCoverData.complementCoverData S).tupleAvoidSet
              (κ := κ) φ := by
  exact (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
    exists_scheme_for_finite_disjoint).finite_subcover_on_complement_forall (κ := κ) hS

/-- Concrete coordinate-avoidance form of the scheme-carrier marked finite
subcover over a fixed complement. -/
theorem markedSchemeNoncritical_finite_subcover_on_complement_forall_avoidance
    (κ : Type z) [Finite κ] [T1Space (P1 K)]
    {S : Set X} (hS : S.Finite) [CompactSpace (κ → {x : X // x ∉ S})] :
    ∃ t : Finset {φ : Φ //
        (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
          exists_scheme_for_finite_disjoint).toBelyiCoverData.sendsSetToBranch S φ},
      ∀ x : κ → {x : X // x ∉ S},
        ∃ φ ∈ t, ∀ i, schemeMap φ.1 (x i).1 ∉ markedSchemePointSet K := by
  rcases markedSchemeNoncritical_finite_subcover_on_complement_forall
      K X Φ schemeMap continuous_schemeMap exists_scheme_for_finite_disjoint
      κ hS with
    ⟨t, ht⟩
  refine ⟨t, ?_⟩
  intro x
  rcases ht x with ⟨φ, hφt, hxφ⟩
  refine ⟨φ, hφt, ?_⟩
  exact hxφ

/-- Scheme-carrier marked noncritical compact-exhaustion cover bridge. -/
theorem markedSchemeNoncritical_finite_compact_cover_by_belyiOpen_exhaustions
    [T1Space (P1 K)] [NonemptyOpenFiniteComplement X] [CompactSpace X]
    (Kex : ∀ φ : Φ,
      CompactExhaustion ((markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
        exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen φ)) :
    ∃ t : Finset (Φ × ℕ),
      (∀ p ∈ t,
        IsCompact ((Subtype.val :
          (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
            exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 → X) ''
            (Kex p.1 p.2))) ∧
        (∀ p ∈ t,
          ((Subtype.val :
            (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
              exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 → X) ''
              (Kex p.1 p.2)) ⊆
                (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
                  exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1) ∧
          (Set.univ : Set X) ⊆
            ⋃ p ∈ t,
              (Subtype.val :
                (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
                  exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 → X) ''
                (Kex p.1 p.2) := by
  exact
    (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
      exists_scheme_for_finite_disjoint).finite_compact_cover_by_belyiOpen_exhaustions
      Kex

/-- Equality form of the scheme-carrier marked compact-exhaustion cover
bridge. -/
theorem markedSchemeNoncritical_finite_compact_cover_by_belyiOpen_exhaustions_eq_univ
    [T1Space (P1 K)] [NonemptyOpenFiniteComplement X] [CompactSpace X]
    (Kex : ∀ φ : Φ,
      CompactExhaustion ((markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
        exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen φ)) :
    ∃ t : Finset (Φ × ℕ),
      (∀ p ∈ t,
        IsCompact ((Subtype.val :
          (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
            exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 → X) ''
            (Kex p.1 p.2))) ∧
        (∀ p ∈ t,
          ((Subtype.val :
            (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
              exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 → X) ''
              (Kex p.1 p.2)) ⊆
                (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
                  exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1) ∧
          (⋃ p ∈ t,
            (Subtype.val :
              (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
                exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 → X) ''
              (Kex p.1 p.2)) = (Set.univ : Set X) := by
  exact
    (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
      exists_scheme_for_finite_disjoint).finite_compact_cover_by_belyiOpen_exhaustions_eq_univ
      Kex

/-- Scheme-carrier marked noncritical compact-cover bridge with compact
exhaustions supplied by local compactness and second countability. -/
theorem markedSchemeNoncritical_finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact
    [T1Space (P1 K)] [NonemptyOpenFiniteComplement X] [CompactSpace X]
    [LocallyCompactSpace X] [SecondCountableTopology X] :
    ∃ Kex : ∀ φ : Φ,
      CompactExhaustion ((markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
        exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen φ),
      ∃ t : Finset (Φ × ℕ),
        (∀ p ∈ t,
          IsCompact ((Subtype.val :
            (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
              exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 → X) ''
              (Kex p.1 p.2))) ∧
          (∀ p ∈ t,
            ((Subtype.val :
              (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
                exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 → X) ''
                (Kex p.1 p.2)) ⊆
                  (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
                    exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1) ∧
            (Set.univ : Set X) ⊆
              ⋃ p ∈ t,
                (Subtype.val :
                  (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
                    exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 → X) ''
                  (Kex p.1 p.2) := by
  exact
    (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
      exists_scheme_for_finite_disjoint).finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact

/-- Equality form of the scheme-carrier marked compact-cover bridge with compact
exhaustions supplied by local compactness and second countability. -/
theorem markedSchemeNoncritical_finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact_eq_univ
    [T1Space (P1 K)] [NonemptyOpenFiniteComplement X] [CompactSpace X]
    [LocallyCompactSpace X] [SecondCountableTopology X] :
    ∃ Kex : ∀ φ : Φ,
      CompactExhaustion ((markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
        exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen φ),
      ∃ t : Finset (Φ × ℕ),
        (∀ p ∈ t,
          IsCompact ((Subtype.val :
            (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
              exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 → X) ''
              (Kex p.1 p.2))) ∧
          (∀ p ∈ t,
            ((Subtype.val :
              (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
                exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 → X) ''
                (Kex p.1 p.2)) ⊆
                  (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
                    exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1) ∧
            (⋃ p ∈ t,
              (Subtype.val :
                (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
                  exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 → X) ''
                (Kex p.1 p.2)) = (Set.univ : Set X) := by
  exact
    (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
      exists_scheme_for_finite_disjoint).finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact_eq_univ

/-- Scheme-carrier marked noncritical compact-coordinate Corollary 3.2 bridge. -/
theorem markedSchemeNoncritical_finite_compact_coordinate_sets_of_belyiOpen_exhaustions
    [T1Space (P1 K)] [NonemptyOpenFiniteComplement X] [CompactSpace X]
    [LocallyCompactSpace X] [SecondCountableTopology X]
    {κ : Type z} {Z : κ → Type*} [∀ j, TopologicalSpace (Z j)]
    (G : Φ → X → ((j : κ) → Z j))
    (hG : ∀ φ, Continuous (G φ))
    (A : (j : κ) → Set (Z j))
    (hGA : ∀ φ x,
      x ∈ (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
        exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen φ →
        ∀ j, G φ x j ∈ A j) :
    ∃ Kex : ∀ φ : Φ,
      CompactExhaustion ((markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
        exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen φ),
      ∃ t : Finset (Φ × ℕ),
        ∃ H : (j : κ) → Set (Z j),
          (∀ j, IsCompact (H j)) ∧
            (∀ j, H j ⊆ A j) ∧
              (Set.univ : Set X) ⊆
                ⋃ p ∈ t,
                  (Subtype.val :
                    (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
                      exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 →
                      X) ''
                    (Kex p.1 p.2) ∧
                ∀ p ∈ t, ∀ x,
                  x ∈ (Subtype.val :
                    (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
                      exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 →
                      X) ''
                      (Kex p.1 p.2) →
                    ∀ j, G p.1 x j ∈ H j := by
  exact
    (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
      exists_scheme_for_finite_disjoint).finite_compact_coordinate_sets_of_belyiOpen_exhaustions
      G hG A hGA

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

/-- Rational-map marked cover data is the partial-map marked cover data of the
canonical partial-map representative. -/
theorem rationalMapMarkedCoverData_eq_partialMapMarkedCoverData
    [IsReduced C] (f : C ⤏ P1 K) :
    rationalMapMarkedCoverData K f = partialMapMarkedCoverData K f.toPartialMap :=
  rfl

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

theorem morphismMarkedNoncriticalExistence_map_apply
    (φ : Φ) (x : C) :
    (morphismMarkedNoncriticalExistence K Φ C morphism
      exists_morphism_for_finite_disjoint).map φ x = (morphism φ).base x := by
  rfl

theorem morphismMarkedNoncriticalExistence_toCoverData_map_apply
    (φ : Φ) (x : C) :
    (morphismMarkedNoncriticalExistence K Φ C morphism
      exists_morphism_for_finite_disjoint).toBelyiCoverData.map φ x =
      (morphism φ).base x := by
  rfl

theorem morphismMarkedNoncriticalExistence_mem_belyiOpen_iff
    (φ : Φ) (x : C) :
    x ∈ (morphismMarkedNoncriticalExistence K Φ C morphism
      exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen φ ↔
      (morphism φ).base x ∉ markedSchemePointSet K := by
  exact
    NoncriticalBelyiExistence.mem_belyiOpen_iff
      (morphismMarkedNoncriticalExistence K Φ C morphism
        exists_morphism_for_finite_disjoint) φ x

theorem morphismMarkedNoncriticalExistence_belyiOpen_carrier
    (φ : Φ) :
    (morphismMarkedNoncriticalExistence K Φ C morphism
      exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen φ =
      {x : C | (morphism φ).base x ∉ markedSchemePointSet K} := by
  exact
    NoncriticalBelyiExistence.belyiOpen_carrier
      (morphismMarkedNoncriticalExistence K Φ C morphism
        exists_morphism_for_finite_disjoint) φ

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

theorem morphismMarkedNoncritical_exists_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
    [T1Space (P1 K)] [NonemptyOpenFiniteComplement C]
    {V T : Set C} (hV : IsOpen V) (hVne : V.Nonempty)
    (hT : T.Finite) (hTsub : T ⊆ V) :
    ∃ φ : Φ,
      IsOpen ((morphismMarkedNoncriticalExistence K Φ C morphism
        exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
        T ⊆ ((morphismMarkedNoncriticalExistence K Φ C morphism
          exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
          ((morphismMarkedNoncriticalExistence K Φ C morphism
            exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ⊆ V := by
  exact (morphismMarkedNoncriticalExistence K Φ C morphism
    exists_morphism_for_finite_disjoint).exists_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
      hV hVne hT hTsub

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

/-- Membership form of the scheme-morphism marked finite subcover over a fixed
complement. -/
theorem morphismMarkedNoncritical_finite_subcover_on_complement_forall
    (κ : Type z) [Finite κ] [T1Space (P1 K)]
    {S : Set C} (hS : S.Finite) [CompactSpace (κ → {x : C // x ∉ S})] :
    ∃ t : Finset {φ : Φ //
        (morphismMarkedNoncriticalExistence K Φ C morphism
          exists_morphism_for_finite_disjoint).toBelyiCoverData.sendsSetToBranch S φ},
      ∀ x : κ → {x : C // x ∉ S},
        ∃ φ ∈ t,
          x ∈ ((morphismMarkedNoncriticalExistence K Φ C morphism
            exists_morphism_for_finite_disjoint).toBelyiCoverData.complementCoverData S).tupleAvoidSet
              (κ := κ) φ := by
  exact (morphismMarkedNoncriticalExistence K Φ C morphism
    exists_morphism_for_finite_disjoint).finite_subcover_on_complement_forall (κ := κ) hS

/-- Concrete coordinate-avoidance form of the scheme-morphism marked finite
subcover over a fixed complement. -/
theorem morphismMarkedNoncritical_finite_subcover_on_complement_forall_avoidance
    (κ : Type z) [Finite κ] [T1Space (P1 K)]
    {S : Set C} (hS : S.Finite) [CompactSpace (κ → {x : C // x ∉ S})] :
    ∃ t : Finset {φ : Φ //
        (morphismMarkedNoncriticalExistence K Φ C morphism
          exists_morphism_for_finite_disjoint).toBelyiCoverData.sendsSetToBranch S φ},
      ∀ x : κ → {x : C // x ∉ S},
        ∃ φ ∈ t, ∀ i, (morphism φ.1).base (x i).1 ∉ markedSchemePointSet K := by
  rcases morphismMarkedNoncritical_finite_subcover_on_complement_forall
      K Φ C morphism exists_morphism_for_finite_disjoint κ hS with
    ⟨t, ht⟩
  refine ⟨t, ?_⟩
  intro x
  rcases ht x with ⟨φ, hφt, hxφ⟩
  refine ⟨φ, hφt, ?_⟩
  exact hxφ

/-- Scheme-morphism marked noncritical compact-exhaustion cover bridge. -/
theorem morphismMarkedNoncritical_finite_compact_cover_by_belyiOpen_exhaustions
    [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    (Kex : ∀ φ : Φ,
      CompactExhaustion ((morphismMarkedNoncriticalExistence K Φ C morphism
        exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen φ)) :
    ∃ t : Finset (Φ × ℕ),
      (∀ p ∈ t,
        IsCompact ((Subtype.val :
          (morphismMarkedNoncriticalExistence K Φ C morphism
            exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 → C) ''
            (Kex p.1 p.2))) ∧
        (∀ p ∈ t,
          ((Subtype.val :
            (morphismMarkedNoncriticalExistence K Φ C morphism
              exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 → C) ''
              (Kex p.1 p.2)) ⊆
                (morphismMarkedNoncriticalExistence K Φ C morphism
                  exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1) ∧
          (Set.univ : Set C) ⊆
            ⋃ p ∈ t,
              (Subtype.val :
                (morphismMarkedNoncriticalExistence K Φ C morphism
                  exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 → C) ''
                (Kex p.1 p.2) := by
  exact
    (morphismMarkedNoncriticalExistence K Φ C morphism
      exists_morphism_for_finite_disjoint).finite_compact_cover_by_belyiOpen_exhaustions
      Kex

/-- Equality form of the scheme-morphism marked compact-exhaustion cover
bridge. -/
theorem morphismMarkedNoncritical_finite_compact_cover_by_belyiOpen_exhaustions_eq_univ
    [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    (Kex : ∀ φ : Φ,
      CompactExhaustion ((morphismMarkedNoncriticalExistence K Φ C morphism
        exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen φ)) :
    ∃ t : Finset (Φ × ℕ),
      (∀ p ∈ t,
        IsCompact ((Subtype.val :
          (morphismMarkedNoncriticalExistence K Φ C morphism
            exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 → C) ''
            (Kex p.1 p.2))) ∧
        (∀ p ∈ t,
          ((Subtype.val :
            (morphismMarkedNoncriticalExistence K Φ C morphism
              exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 → C) ''
              (Kex p.1 p.2)) ⊆
                (morphismMarkedNoncriticalExistence K Φ C morphism
                  exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1) ∧
          (⋃ p ∈ t,
            (Subtype.val :
              (morphismMarkedNoncriticalExistence K Φ C morphism
                exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 → C) ''
              (Kex p.1 p.2)) = (Set.univ : Set C) := by
  exact
    (morphismMarkedNoncriticalExistence K Φ C morphism
      exists_morphism_for_finite_disjoint).finite_compact_cover_by_belyiOpen_exhaustions_eq_univ
      Kex

/-- Scheme-morphism marked noncritical compact-cover bridge with compact
exhaustions supplied by local compactness and second countability. -/
theorem morphismMarkedNoncritical_finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact
    [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    [LocallyCompactSpace C] [SecondCountableTopology C] :
    ∃ Kex : ∀ φ : Φ,
      CompactExhaustion ((morphismMarkedNoncriticalExistence K Φ C morphism
        exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen φ),
      ∃ t : Finset (Φ × ℕ),
        (∀ p ∈ t,
          IsCompact ((Subtype.val :
            (morphismMarkedNoncriticalExistence K Φ C morphism
              exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 → C) ''
              (Kex p.1 p.2))) ∧
          (∀ p ∈ t,
            ((Subtype.val :
              (morphismMarkedNoncriticalExistence K Φ C morphism
                exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 → C) ''
                (Kex p.1 p.2)) ⊆
                  (morphismMarkedNoncriticalExistence K Φ C morphism
                    exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1) ∧
            (Set.univ : Set C) ⊆
              ⋃ p ∈ t,
                (Subtype.val :
                  (morphismMarkedNoncriticalExistence K Φ C morphism
                    exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 → C) ''
                  (Kex p.1 p.2) := by
  exact
    (morphismMarkedNoncriticalExistence K Φ C morphism
      exists_morphism_for_finite_disjoint).finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact

/-- Equality form of the scheme-morphism marked compact-cover bridge with
compact exhaustions supplied by local compactness and second countability. -/
theorem morphismMarkedNoncritical_finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact_eq_univ
    [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    [LocallyCompactSpace C] [SecondCountableTopology C] :
    ∃ Kex : ∀ φ : Φ,
      CompactExhaustion ((morphismMarkedNoncriticalExistence K Φ C morphism
        exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen φ),
      ∃ t : Finset (Φ × ℕ),
        (∀ p ∈ t,
          IsCompact ((Subtype.val :
            (morphismMarkedNoncriticalExistence K Φ C morphism
              exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 → C) ''
              (Kex p.1 p.2))) ∧
          (∀ p ∈ t,
            ((Subtype.val :
              (morphismMarkedNoncriticalExistence K Φ C morphism
                exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 → C) ''
                (Kex p.1 p.2)) ⊆
                  (morphismMarkedNoncriticalExistence K Φ C morphism
                    exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1) ∧
            (⋃ p ∈ t,
              (Subtype.val :
                (morphismMarkedNoncriticalExistence K Φ C morphism
                  exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 → C) ''
                (Kex p.1 p.2)) = (Set.univ : Set C) := by
  exact
    (morphismMarkedNoncriticalExistence K Φ C morphism
      exists_morphism_for_finite_disjoint).finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact_eq_univ

/-- Scheme-morphism marked noncritical compact-coordinate Corollary 3.2 bridge. -/
theorem morphismMarkedNoncritical_finite_compact_coordinate_sets_of_belyiOpen_exhaustions
    [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    [LocallyCompactSpace C] [SecondCountableTopology C]
    {κ : Type z} {Z : κ → Type*} [∀ j, TopologicalSpace (Z j)]
    (G : Φ → C → ((j : κ) → Z j))
    (hG : ∀ φ, Continuous (G φ))
    (A : (j : κ) → Set (Z j))
    (hGA : ∀ φ x,
      x ∈ (morphismMarkedNoncriticalExistence K Φ C morphism
        exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen φ →
        ∀ j, G φ x j ∈ A j) :
    ∃ Kex : ∀ φ : Φ,
      CompactExhaustion ((morphismMarkedNoncriticalExistence K Φ C morphism
        exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen φ),
      ∃ t : Finset (Φ × ℕ),
        ∃ H : (j : κ) → Set (Z j),
          (∀ j, IsCompact (H j)) ∧
            (∀ j, H j ⊆ A j) ∧
              (Set.univ : Set C) ⊆
                ⋃ p ∈ t,
                  (Subtype.val :
                    (morphismMarkedNoncriticalExistence K Φ C morphism
                      exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 →
                      C) ''
                    (Kex p.1 p.2) ∧
                ∀ p ∈ t, ∀ x,
                  x ∈ (Subtype.val :
                    (morphismMarkedNoncriticalExistence K Φ C morphism
                      exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen p.1 →
                      C) ''
                      (Kex p.1 p.2) →
                    ∀ j, G p.1 x j ∈ H j := by
  exact
    (morphismMarkedNoncriticalExistence K Φ C morphism
      exists_morphism_for_finite_disjoint).finite_compact_coordinate_sets_of_belyiOpen_exhaustions
      G hG A hGA

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

theorem schemeBelyiMapMarkedCoverData_belyiOpen_carrier :
    (schemeBelyiMapMarkedCoverData K hmarkedOpen φ).belyiOpen () =
      {x : C | φ.hom.base x ∉ markedSchemePointSet K} := by
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

theorem finiteSchemeBelyiMapMarkedCoverData_branch_finite :
    (finiteSchemeBelyiMapMarkedCoverData K hmarkedOpen φfin).branch.Finite := by
  exact markedSchemePointSet_finite K

theorem finiteSchemeBelyiMapMarkedCoverData_isFinite_hom :
    IsFinite φfin.hom :=
  φfin.finite_hom

theorem finiteSchemeBelyiMapMarkedCoverData_map_apply
    (x : C) :
    (finiteSchemeBelyiMapMarkedCoverData K hmarkedOpen φfin).map () x =
      φfin.hom.base x := by
  rfl

theorem finiteSchemeBelyiMapMarkedCoverData_mem_belyiOpen_iff
    (x : C) :
    x ∈ (finiteSchemeBelyiMapMarkedCoverData K hmarkedOpen φfin).belyiOpen () ↔
      φfin.hom.base x ∉ markedSchemePointSet K := by
  rfl

theorem finiteSchemeBelyiMapMarkedCoverData_belyiOpen_carrier :
    (finiteSchemeBelyiMapMarkedCoverData K hmarkedOpen φfin).belyiOpen () =
      {x : C | φfin.hom.base x ∉ markedSchemePointSet K} := by
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

theorem toMarkedNoncriticalExistence_toBelyiCoverData_eq_toMarkedCoverData :
    (toMarkedNoncriticalExistence K Φ F).toBelyiCoverData =
      toMarkedCoverData K Φ F := rfl

theorem map_apply
    (φ : Φ) (x : C) :
    (toMarkedCoverData K Φ F).map φ x = (F.map φ).hom.base x := by
  rfl

theorem finite_hom
    (φ : Φ) :
    IsFinite (F.map φ).hom :=
  (F.map φ).finite_hom

/-- Every member of a finite marked Belyi family is dominant. -/
theorem isDominant_hom
    (φ : Φ) :
    IsDominant (F.map φ).hom :=
  SchemeBelyi.FiniteBelyiMap.isDominant_hom (F.map φ)

/-- The underlying continuous map of every member of a finite marked Belyi
family has dense range. -/
theorem denseRange_hom
    (φ : Φ) :
    DenseRange (F.map φ).hom.base :=
  SchemeBelyi.FiniteBelyiMap.denseRange_hom (F.map φ)

/-- The branch-open restriction of every member of a finite marked Belyi family
is etale. -/
theorem isEtale_restrict_branchOpen
    (φ : Φ) :
    IsEtale ((F.map φ).hom ∣_ (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.isEtale_restrict_branchOpen (F.map φ)

/-- The branch-open restriction of every member of a finite marked Belyi family
is finite. -/
theorem isFinite_restrict_branchOpen
    (φ : Φ) :
    IsFinite ((F.map φ).hom ∣_ (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.isFinite_restrict_branchOpen (F.map φ)

/-- The branch-open restriction of every member of a finite marked Belyi family
is affine. -/
theorem isAffineHom_restrict_branchOpen
    (φ : Φ) :
    IsAffineHom ((F.map φ).hom ∣_
      (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.isAffineHom_restrict_branchOpen (F.map φ)

/-- The branch-open restriction of every member of a finite marked Belyi family
is integral. -/
theorem isIntegralHom_restrict_branchOpen
    (φ : Φ) :
    IsIntegralHom ((F.map φ).hom ∣_
      (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.isIntegralHom_restrict_branchOpen (F.map φ)

/-- The branch-open restriction of every member of a finite marked Belyi family
is locally of finite type. -/
theorem locallyOfFiniteType_restrict_branchOpen
    (φ : Φ) :
    LocallyOfFiniteType ((F.map φ).hom ∣_
      (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.locallyOfFiniteType_restrict_branchOpen (F.map φ)

/-- The branch-open restriction of every member of a finite marked Belyi family
is separated. -/
theorem isSeparated_restrict_branchOpen
    (φ : Φ) :
    IsSeparated ((F.map φ).hom ∣_
      (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.isSeparated_restrict_branchOpen (F.map φ)

/-- The branch-open restriction of every member of a finite marked Belyi family
is quasi-compact. -/
theorem quasiCompact_restrict_branchOpen
    (φ : Φ) :
    QuasiCompact ((F.map φ).hom ∣_
      (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.quasiCompact_restrict_branchOpen (F.map φ)

/-- Every member of a finite marked Belyi family is affine as a morphism. -/
theorem isAffineHom_hom
    (φ : Φ) :
    IsAffineHom (F.map φ).hom :=
  SchemeBelyi.FiniteBelyiMap.isAffineHom_hom (F.map φ)

/-- Every member of a finite marked Belyi family is integral as a morphism. -/
theorem isIntegralHom_hom
    (φ : Φ) :
    IsIntegralHom (F.map φ).hom :=
  SchemeBelyi.FiniteBelyiMap.isIntegralHom_hom (F.map φ)

/-- Every member of a finite marked Belyi family is locally of finite type. -/
theorem locallyOfFiniteType_hom
    (φ : Φ) :
    LocallyOfFiniteType (F.map φ).hom :=
  SchemeBelyi.FiniteBelyiMap.locallyOfFiniteType_hom (F.map φ)

/-- Every member of a finite marked Belyi family is separated as a morphism. -/
theorem isSeparated_hom
    (φ : Φ) :
    IsSeparated (F.map φ).hom :=
  SchemeBelyi.FiniteBelyiMap.isSeparated_hom (F.map φ)

/-- Every member of a finite marked Belyi family is quasi-compact as a morphism. -/
theorem quasiCompact_hom
    (φ : Φ) :
    QuasiCompact (F.map φ).hom :=
  SchemeBelyi.FiniteBelyiMap.quasiCompact_hom (F.map φ)

theorem mem_belyiOpen_iff
    (φ : Φ) (x : C) :
    x ∈ (toMarkedCoverData K Φ F).belyiOpen φ ↔
      (F.map φ).hom.base x ∉ markedSchemePointSet K := by
  rfl

theorem toMarkedNoncriticalExistence_mem_belyiOpen_iff
    (φ : Φ) (x : C) :
    x ∈ (toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ ↔
      (F.map φ).hom.base x ∉ markedSchemePointSet K := by
  rfl

theorem belyiOpen_carrier
    (φ : Φ) :
    (toMarkedCoverData K Φ F).belyiOpen φ =
      {x : C | (F.map φ).hom.base x ∉ markedSchemePointSet K} := by
  rfl

theorem toMarkedNoncriticalExistence_belyiOpen_carrier
    (φ : Φ) :
    (toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ =
      {x : C | (F.map φ).hom.base x ∉ markedSchemePointSet K} := by
  rfl

theorem belyiOpen_eq_schemeBelyi
    (φ : Φ) :
    (toMarkedCoverData K Φ F).belyiOpen φ =
      ((F.map φ).toBelyiMap.belyiOpen : Set C) := by
  rfl

theorem toMarkedNoncriticalExistence_belyiOpen_eq_schemeBelyi
    (φ : Φ) :
    (toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ =
      ((F.map φ).toBelyiMap.belyiOpen : Set C) := by
  rfl

theorem belyiOpen_isOpen
    (φ : Φ) :
    IsOpen ((toMarkedCoverData K Φ F).belyiOpen φ) := by
  rw [belyiOpen_eq_schemeBelyi K Φ F φ]
  exact (F.map φ).toBelyiMap.belyiOpen.2

theorem toMarkedNoncriticalExistence_belyiOpen_isOpen
    (φ : Φ) :
    IsOpen ((toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ) := by
  rw [toMarkedNoncriticalExistence_belyiOpen_eq_schemeBelyi K Φ F φ]
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

/-- Direct scheme-Belyi-open form of the finite disjoint-set conclusion: the
selected finite marked Belyi map has source Belyi open containing `T` and
contained in the complement of `S`. -/
theorem exists_map_belyiOpen_controls
    {S T : Set C} (hS : S.Finite) (hT : T.Finite) (hdis : Disjoint S T) :
    ∃ φ : Φ, T ⊆ ((F.map φ).toBelyiMap.belyiOpen : Set C) ∧
      ((F.map φ).toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  rcases F.exists_for_finite_disjoint hS hT hdis with ⟨φ, hSmark, hTavoid⟩
  refine ⟨φ, ?_, ?_⟩
  · intro x hxT
    exact
      (SchemeBelyi.FiniteBelyiMap.mem_marked_belyiOpen_iff
        (K := K) (hmarkedOpen := F.hmarkedOpen) (F.map φ) x).2
        (hTavoid x hxT)
  · intro x hxOpen hxS
    have hxNotMarked :
        (F.map φ).hom.base x ∉ markedSchemePointSet K :=
      (SchemeBelyi.FiniteBelyiMap.mem_marked_belyiOpen_iff
        (K := K) (hmarkedOpen := F.hmarkedOpen) (F.map φ) x).1 hxOpen
    exact hxNotMarked (hSmark x hxS)

/-- Direct same-map form of the finite disjoint-set conclusion: the selected
finite marked Belyi map satisfies the marked point controls and its source
Belyi open contains `T` and is contained in `Sᶜ`. -/
theorem exists_map_controls_and_belyiOpen_controls
    {S T : Set C} (hS : S.Finite) (hT : T.Finite) (hdis : Disjoint S T) :
    ∃ φ : Φ,
      ((∀ x ∈ S, (F.map φ).hom.base x ∈ markedSchemePointSet K) ∧
        ∀ x ∈ T, (F.map φ).hom.base x ∉ markedSchemePointSet K) ∧
        T ⊆ ((F.map φ).toBelyiMap.belyiOpen : Set C) ∧
          ((F.map φ).toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  rcases F.exists_for_finite_disjoint hS hT hdis with ⟨φ, hSmark, hTavoid⟩
  refine ⟨φ, ⟨hSmark, hTavoid⟩, ?_, ?_⟩
  · intro x hxT
    exact
      (SchemeBelyi.FiniteBelyiMap.mem_marked_belyiOpen_iff
        (K := K) (hmarkedOpen := F.hmarkedOpen) (F.map φ) x).2
        (hTavoid x hxT)
  · intro x hxOpen hxS
    have hxNotMarked :
        (F.map φ).hom.base x ∉ markedSchemePointSet K :=
      (SchemeBelyi.FiniteBelyiMap.mem_marked_belyiOpen_iff
        (K := K) (hmarkedOpen := F.hmarkedOpen) (F.map φ) x).1 hxOpen
    exact hxNotMarked (hSmark x hxS)

/-- Direct same-map finite disjoint-set conclusion with explicit openness:
the selected finite marked Belyi map satisfies the marked point controls, its
source Belyi open is open, contains `T`, and is contained in `Sᶜ`. -/
theorem exists_map_controls_and_isOpen_belyiOpen_controls
    {S T : Set C} (hS : S.Finite) (hT : T.Finite) (hdis : Disjoint S T) :
    ∃ φ : Φ,
      ((∀ x ∈ S, (F.map φ).hom.base x ∈ markedSchemePointSet K) ∧
        ∀ x ∈ T, (F.map φ).hom.base x ∉ markedSchemePointSet K) ∧
        IsOpen ((F.map φ).toBelyiMap.belyiOpen : Set C) ∧
          T ⊆ ((F.map φ).toBelyiMap.belyiOpen : Set C) ∧
            ((F.map φ).toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  rcases exists_map_controls_and_belyiOpen_controls K Φ F hS hT hdis with
    ⟨φ, hcontrols, hTopen, hopenS⟩
  exact ⟨φ, hcontrols, (F.map φ).toBelyiMap.belyiOpen.2, hTopen, hopenS⟩

/-- Actual finite-map version of the one-point Corollary 1.2 consequence:
outside a finite set, some selected finite Belyi map has a source Belyi open
through the point and contained in the finite complement. -/
theorem exists_map_belyiOpen_inside_complement
    {A : Set C} (hA : A.Finite) {x : C} (hxA : x ∉ A) :
    ∃ φ : Φ,
      IsOpen ((F.map φ).toBelyiMap.belyiOpen : Set C) ∧
        x ∈ ((F.map φ).toBelyiMap.belyiOpen : Set C) ∧
          ((F.map φ).toBelyiMap.belyiOpen : Set C) ⊆ Aᶜ := by
  have hsingleton : ({x} : Set C).Finite := Set.finite_singleton x
  have hdis : Disjoint A ({x} : Set C) := by
    rw [Set.disjoint_left]
    intro y hyA hyx
    rw [Set.mem_singleton_iff] at hyx
    exact hxA (by simpa [hyx] using hyA)
  rcases exists_map_belyiOpen_controls K Φ F hA hsingleton hdis with
    ⟨φ, hmem, hsub⟩
  exact ⟨φ, (F.map φ).toBelyiMap.belyiOpen.2, hmem (by simp), hsub⟩

/-- Actual finite-map version of the finite-set Corollary 1.2 consequence:
for finite disjoint sets `S,T`, some selected finite Belyi map has a source
Belyi open containing `T` and contained in `Sᶜ`. -/
theorem exists_map_belyiOpen_containing_finite_inside_complement
    {S T : Set C} (hS : S.Finite) (hT : T.Finite) (hdis : Disjoint S T) :
    ∃ φ : Φ,
      IsOpen ((F.map φ).toBelyiMap.belyiOpen : Set C) ∧
        T ⊆ ((F.map φ).toBelyiMap.belyiOpen : Set C) ∧
          ((F.map φ).toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  rcases exists_map_belyiOpen_controls K Φ F hS hT hdis with
    ⟨φ, hTopen, hopenS⟩
  exact ⟨φ, (F.map φ).toBelyiMap.belyiOpen.2, hTopen, hopenS⟩

/-- Actual finite-map version of the one-point finite-complement-open
consequence. -/
theorem exists_map_belyiOpen_inside_open_of_finite_complement
    {V : Set C} (_hV : IsOpen V) (hVcompl : Vᶜ.Finite) {x : C} (hxV : x ∈ V) :
    ∃ φ : Φ,
      IsOpen ((F.map φ).toBelyiMap.belyiOpen : Set C) ∧
        x ∈ ((F.map φ).toBelyiMap.belyiOpen : Set C) ∧
          ((F.map φ).toBelyiMap.belyiOpen : Set C) ⊆ V := by
  rcases exists_map_belyiOpen_inside_complement K Φ F hVcompl
      (A := Vᶜ) (x := x) (by simpa using hxV) with
    ⟨φ, hopen, hxopen, hsub⟩
  exact ⟨φ, hopen, hxopen, by simpa using hsub⟩

/-- Actual finite-map version of the one-point nonempty-open finite-complement
consequence. -/
theorem exists_map_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
    [NonemptyOpenFiniteComplement C]
    {V : Set C} (hV : IsOpen V) {x : C} (hxV : x ∈ V) :
    ∃ φ : Φ,
      IsOpen ((F.map φ).toBelyiMap.belyiOpen : Set C) ∧
        x ∈ ((F.map φ).toBelyiMap.belyiOpen : Set C) ∧
          ((F.map φ).toBelyiMap.belyiOpen : Set C) ⊆ V := by
  exact exists_map_belyiOpen_inside_open_of_finite_complement K Φ F
    hV (finite_compl_of_isOpen_of_mem hV hxV) hxV

/-- Actual finite-map version of the finite-set finite-complement-open
consequence. -/
theorem exists_map_belyiOpen_containing_finite_inside_open_of_finite_complement
    {V T : Set C} (_hV : IsOpen V) (hVcompl : Vᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ V) :
    ∃ φ : Φ,
      IsOpen ((F.map φ).toBelyiMap.belyiOpen : Set C) ∧
        T ⊆ ((F.map φ).toBelyiMap.belyiOpen : Set C) ∧
          ((F.map φ).toBelyiMap.belyiOpen : Set C) ⊆ V := by
  have hdis : Disjoint Vᶜ T := by
    rw [Set.disjoint_left]
    intro x hxVcomp hxT
    exact hxVcomp (hTsub hxT)
  rcases exists_map_belyiOpen_containing_finite_inside_complement K Φ F
      hVcompl hT hdis with
    ⟨φ, hopen, hTopen, hsub⟩
  exact ⟨φ, hopen, hTopen, by simpa using hsub⟩

/-- Actual finite-map version of the finite-set nonempty-open
finite-complement consequence. -/
theorem exists_map_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
    [NonemptyOpenFiniteComplement C]
    {V T : Set C} (hV : IsOpen V) (hVne : V.Nonempty)
    (hT : T.Finite) (hTsub : T ⊆ V) :
    ∃ φ : Φ,
      IsOpen ((F.map φ).toBelyiMap.belyiOpen : Set C) ∧
        T ⊆ ((F.map φ).toBelyiMap.belyiOpen : Set C) ∧
          ((F.map φ).toBelyiMap.belyiOpen : Set C) ⊆ V := by
  exact exists_map_belyiOpen_containing_finite_inside_open_of_finite_complement
    K Φ F hV (finite_compl_of_isOpen_nonempty hV hVne) hT hTsub

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

/-- The Belyi opens attached to a finite marked Belyi family. -/
def belyiOpenSetFamily : Set (Set C) :=
  (toMarkedNoncriticalExistence K Φ F).belyiOpenSetFamily

/-- Corollary 1.2 in basis form for finite marked Belyi families. -/
theorem belyiOpenSetFamily_isTopologicalBasis
    [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] :
    TopologicalSpace.IsTopologicalBasis (belyiOpenSetFamily K Φ F) :=
  (toMarkedNoncriticalExistence K Φ F).belyiOpenSetFamily_isTopologicalBasis

/-- The Belyi opens attached to a finite marked Belyi family cover the source. -/
theorem belyiOpen_cover_univ
    [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] :
    (Set.univ : Set C) ⊆
      ⋃ φ : Φ, (toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ :=
  (toMarkedNoncriticalExistence K Φ F).belyiOpen_cover_univ

/-- Finite marked Belyi form of the compact-exhaustion cover bridge. -/
theorem finite_compact_cover_by_belyiOpen_exhaustions
    [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    (Kex : ∀ φ : Φ,
      CompactExhaustion ((toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ)) :
    ∃ t : Finset (Φ × ℕ),
      (∀ p ∈ t,
        IsCompact ((Subtype.val :
          (toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen p.1 → C) ''
            (Kex p.1 p.2))) ∧
        (∀ p ∈ t,
          ((Subtype.val :
            (toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen p.1 → C) ''
              (Kex p.1 p.2)) ⊆
                (toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen p.1) ∧
          (Set.univ : Set C) ⊆
            ⋃ p ∈ t,
              (Subtype.val :
                (toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen p.1 → C) ''
                  (Kex p.1 p.2) := by
  exact
    (toMarkedNoncriticalExistence K Φ F).finite_compact_cover_by_belyiOpen_exhaustions
      Kex

/-- Equality form of the finite marked Belyi compact-exhaustion cover bridge. -/
theorem finite_compact_cover_by_belyiOpen_exhaustions_eq_univ
    [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    (Kex : ∀ φ : Φ,
      CompactExhaustion ((toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ)) :
    ∃ t : Finset (Φ × ℕ),
      (∀ p ∈ t,
        IsCompact ((Subtype.val :
          (toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen p.1 → C) ''
            (Kex p.1 p.2))) ∧
        (∀ p ∈ t,
          ((Subtype.val :
            (toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen p.1 → C) ''
              (Kex p.1 p.2)) ⊆
                (toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen p.1) ∧
          (⋃ p ∈ t,
            (Subtype.val :
              (toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen p.1 → C) ''
                (Kex p.1 p.2)) = (Set.univ : Set C) := by
  exact
    (toMarkedNoncriticalExistence K Φ F).finite_compact_cover_by_belyiOpen_exhaustions_eq_univ
      Kex

/-- Finite marked Belyi compact-cover bridge with compact exhaustions supplied
from local compactness and second countability of the source. -/
theorem finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact
    [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    [LocallyCompactSpace C] [SecondCountableTopology C] :
    ∃ Kex : ∀ φ : Φ,
      CompactExhaustion ((toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ),
      ∃ t : Finset (Φ × ℕ),
        (∀ p ∈ t,
          IsCompact ((Subtype.val :
            (toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen p.1 → C) ''
              (Kex p.1 p.2))) ∧
          (∀ p ∈ t,
            ((Subtype.val :
              (toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen p.1 → C) ''
                (Kex p.1 p.2)) ⊆
                  (toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen p.1) ∧
            (Set.univ : Set C) ⊆
              ⋃ p ∈ t,
                (Subtype.val :
                  (toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen p.1 → C) ''
                    (Kex p.1 p.2) := by
  exact
    NoncriticalBelyiExistence.finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact
      (toMarkedNoncriticalExistence K Φ F)

/-- Equality form of the finite marked Belyi compact-cover bridge with compact
exhaustions supplied from local compactness and second countability. -/
theorem finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact_eq_univ
    [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    [LocallyCompactSpace C] [SecondCountableTopology C] :
    ∃ Kex : ∀ φ : Φ,
      CompactExhaustion ((toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ),
      ∃ t : Finset (Φ × ℕ),
        (∀ p ∈ t,
          IsCompact ((Subtype.val :
            (toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen p.1 → C) ''
              (Kex p.1 p.2))) ∧
          (∀ p ∈ t,
            ((Subtype.val :
              (toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen p.1 → C) ''
                (Kex p.1 p.2)) ⊆
                  (toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen p.1) ∧
            (⋃ p ∈ t,
              (Subtype.val :
                (toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen p.1 → C) ''
                  (Kex p.1 p.2)) = (Set.univ : Set C) := by
  exact
    NoncriticalBelyiExistence.finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact_eq_univ
      (toMarkedNoncriticalExistence K Φ F)

/-- Finite marked Belyi form of the compact-coordinate Corollary 3.2 bridge:
continuous product-valued maps on the selected Belyi opens give compact
coordinate target sets after choosing finitely many compact exhaustion members. -/
theorem finite_compact_coordinate_sets_of_belyiOpen_exhaustions
    [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    [LocallyCompactSpace C] [SecondCountableTopology C]
    {κ : Type z} {Z : κ → Type*} [∀ j, TopologicalSpace (Z j)]
    (G : Φ → C → ((j : κ) → Z j))
    (hG : ∀ φ, Continuous (G φ))
    (A : (j : κ) → Set (Z j))
    (hGA : ∀ φ x,
      x ∈ (toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ →
        ∀ j, G φ x j ∈ A j) :
    ∃ Kex : ∀ φ : Φ,
      CompactExhaustion ((toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ),
      ∃ t : Finset (Φ × ℕ),
        ∃ H : (j : κ) → Set (Z j),
          (∀ j, IsCompact (H j)) ∧
            (∀ j, H j ⊆ A j) ∧
              (Set.univ : Set C) ⊆
                ⋃ p ∈ t,
                  (Subtype.val :
                    (toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen p.1 →
                      C) ''
                    (Kex p.1 p.2) ∧
                ∀ p ∈ t, ∀ x,
                  x ∈ (Subtype.val :
                    (toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen p.1 →
                      C) ''
                      (Kex p.1 p.2) →
                    ∀ j, G p.1 x j ∈ H j := by
  exact
    NoncriticalBelyiExistence.finite_compact_coordinate_sets_of_belyiOpen_exhaustions
      (toMarkedNoncriticalExistence K Φ F) G hG A hGA

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

theorem exists_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
    [T1Space (P1 K)] [NonemptyOpenFiniteComplement C]
    {V T : Set C} (hV : IsOpen V) (hVne : V.Nonempty)
    (hT : T.Finite) (hTsub : T ⊆ V) :
    ∃ φ : Φ,
      IsOpen ((toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ) ∧
        T ⊆ ((toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ) ∧
          ((toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ) ⊆ V := by
  exact
    (toMarkedNoncriticalExistence K Φ F).exists_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
      hV hVne hT hTsub

/-- Actual finite-map finite-complement-open version retaining marked controls:
if `T` lies in an open with finite complement, a selected finite marked Belyi
map sends the complement to the marked set, avoids the marked set on `T`, and
has source Belyi open containing `T` inside the original open. -/
theorem exists_map_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_finite_complement
    {V T : Set C} (_hV : IsOpen V) (hVcompl : Vᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ V) :
    ∃ φ : Φ,
      ((∀ x ∈ Vᶜ, (F.map φ).hom.base x ∈ markedSchemePointSet K) ∧
        ∀ x ∈ T, (F.map φ).hom.base x ∉ markedSchemePointSet K) ∧
        IsOpen ((F.map φ).toBelyiMap.belyiOpen : Set C) ∧
          T ⊆ ((F.map φ).toBelyiMap.belyiOpen : Set C) ∧
            ((F.map φ).toBelyiMap.belyiOpen : Set C) ⊆ V := by
  have hdis : Disjoint Vᶜ T := by
    rw [Set.disjoint_left]
    intro x hxV hxT
    exact hxV (hTsub hxT)
  rcases exists_map_controls_and_isOpen_belyiOpen_controls
      K Φ F hVcompl hT hdis with ⟨φ, hcontrols, hopen, hTopen, hopenS⟩
  exact ⟨φ, hcontrols, hopen, hTopen, by simpa using hopenS⟩

/-- Actual finite-map nonempty-open finite-complement version retaining marked
controls. -/
theorem exists_map_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
    [NonemptyOpenFiniteComplement C]
    {V T : Set C} (hV : IsOpen V) (hVne : V.Nonempty)
    (hT : T.Finite) (hTsub : T ⊆ V) :
    ∃ φ : Φ,
      ((∀ x ∈ Vᶜ, (F.map φ).hom.base x ∈ markedSchemePointSet K) ∧
        ∀ x ∈ T, (F.map φ).hom.base x ∉ markedSchemePointSet K) ∧
        IsOpen ((F.map φ).toBelyiMap.belyiOpen : Set C) ∧
          T ⊆ ((F.map φ).toBelyiMap.belyiOpen : Set C) ∧
            ((F.map φ).toBelyiMap.belyiOpen : Set C) ⊆ V := by
  exact
    exists_map_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_finite_complement
      K Φ F hV (finite_compl_of_isOpen_nonempty hV hVne) hT hTsub

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

/-- Membership form of the finite marked Belyi-family subcover over a fixed
complement. -/
theorem finite_subcover_on_complement_forall
    (κ : Type z) [Finite κ] [T1Space (P1 K)]
    {S : Set C} (hS : S.Finite) [CompactSpace (κ → {x : C // x ∉ S})] :
    ∃ t : Finset {φ : Φ // (toMarkedCoverData K Φ F).sendsSetToBranch S φ},
      ∀ x : κ → {x : C // x ∉ S},
        ∃ φ ∈ t,
          x ∈ ((toMarkedCoverData K Φ F).complementCoverData S).tupleAvoidSet
            (κ := κ) φ := by
  exact (toMarkedNoncriticalExistence K Φ F).finite_subcover_on_complement_forall
    (κ := κ) hS

/-- Concrete coordinate-avoidance form of the finite marked Belyi-family
subcover over a fixed complement. -/
theorem finite_subcover_on_complement_forall_avoidance
    (κ : Type z) [Finite κ] [T1Space (P1 K)]
    {S : Set C} (hS : S.Finite) [CompactSpace (κ → {x : C // x ∉ S})] :
    ∃ t : Finset {φ : Φ // (toMarkedCoverData K Φ F).sendsSetToBranch S φ},
      ∀ x : κ → {x : C // x ∉ S},
        ∃ φ ∈ t, ∀ i, (F.map φ.1).hom.base (x i).1 ∉ markedSchemePointSet K := by
  rcases finite_subcover_on_complement_forall K Φ F κ hS with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  intro x
  rcases ht x with ⟨φ, hφt, hxφ⟩
  refine ⟨φ, hφt, ?_⟩
  exact hxφ

end FiniteMarkedBelyiExistence

end FiniteMarkedBelyiExistence

end
end SchemeMarkedBelyi
end SourceStack
end HilbertTest
