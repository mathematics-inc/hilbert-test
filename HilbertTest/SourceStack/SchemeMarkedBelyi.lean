import HilbertTest.SourceStack.BelyiCovers
import HilbertTest.SourceStack.SchemeProjectiveLine

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

noncomputable section

universe u v w

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

end
end SchemeMarkedBelyi
end SourceStack
end HilbertTest
