import HilbertTest.SourceStack.Topology

/-!
Topological cover layer for Mochizuki Corollary 3.1.

This module isolates the compactness argument from the curve-specific theorem
that constructs Belyi maps.  Once a source theorem supplies, for every finite
tuple of points, a map whose coordinate values avoid the finite branch set,
compactness extracts a finite list of maps.
-/

namespace HilbertTest
namespace SourceStack

open Set

universe u v w

/-- Abstract data for the open-cover step of Corollary 3.1: a finite branch set
in a target space and a family of continuous maps from the source. -/
structure BelyiCoverData (X P Φ : Type*) [TopologicalSpace X] [TopologicalSpace P] where
  branch : Set P
  branch_finite : branch.Finite
  map : Φ → X → P
  continuous_map : ∀ φ, Continuous (map φ)

namespace BelyiCoverData

variable {X P Φ κ : Type*} [TopologicalSpace X] [TopologicalSpace P]
variable (D : BelyiCoverData X P Φ)

/-- For a map in the family, this is the open locus of tuples whose coordinates
all avoid the branch set. -/
def tupleAvoidSet [Finite κ] (φ : Φ) : Set (κ → X) :=
  {x : κ → X | ∀ i, D.map φ (x i) ∉ D.branch}

/-- The tuple-avoidance locus is open. -/
theorem tupleAvoidSet_isOpen [Finite κ] [T1Space P] (φ : Φ) :
    IsOpen (D.tupleAvoidSet (κ := κ) φ) := by
  exact isOpen_pi_avoid_finite (D.map φ) (D.continuous_map φ)
    D.branch_finite

/-- A pointwise choice of an avoiding map gives an indexed open cover. -/
theorem tupleAvoidSet_cover_of_pointwise
    [Finite κ]
    (hcover : ∀ x : κ → X, ∃ φ : Φ, x ∈ D.tupleAvoidSet (κ := κ) φ) :
    (Set.univ : Set (κ → X)) ⊆ ⋃ φ : Φ, D.tupleAvoidSet (κ := κ) φ := by
  intro x _
  rcases hcover x with ⟨φ, hφ⟩
  exact mem_iUnion.2 ⟨φ, hφ⟩

/-- Compactness extracts a finite family of maps from the pointwise cover.
This is the formal topological content of Mochizuki Corollary 3.1. -/
theorem finite_subcover_of_pointwise
    [Finite κ] [T1Space P] [CompactSpace (κ → X)]
    (hcover : ∀ x : κ → X, ∃ φ : Φ, x ∈ D.tupleAvoidSet (κ := κ) φ) :
    ∃ t : Finset Φ,
      (⋃ φ ∈ t, D.tupleAvoidSet (κ := κ) φ) = (Set.univ : Set (κ → X)) := by
  exact compactSpace_finite_subcover_eq_univ
    (X := κ → X) (ι := Φ)
    (fun φ => D.tupleAvoidSet (κ := κ) φ)
    (fun φ => D.tupleAvoidSet_isOpen (κ := κ) φ)
    (D.tupleAvoidSet_cover_of_pointwise (κ := κ) hcover)

/-- A map sends a fixed subset of the source to the finite branch set.  In
Corollary 3.1 this is the condition `phi(S) subset {0,1,infinity}`. -/
def sendsSetToBranch (S : Set X) (φ : Φ) : Prop :=
  ∀ x ∈ S, D.map φ x ∈ D.branch

/-- Restrict the source to the complement of a fixed set and restrict the map
family to maps that send that fixed set to the branch set. -/
def complementCoverData (S : Set X) :
    BelyiCoverData {x : X // x ∉ S} P {φ : Φ // D.sendsSetToBranch S φ} where
  branch := D.branch
  branch_finite := D.branch_finite
  map φ x := D.map φ.1 x.1
  continuous_map φ := (D.continuous_map φ.1).comp continuous_subtype_val

/-- The complement-restricted tuple-avoidance set is just coordinate avoidance
for the underlying maps. -/
theorem complement_tupleAvoidSet_eq
    [Finite κ] (S : Set X) (φ : {φ : Φ // D.sendsSetToBranch S φ}) :
    (D.complementCoverData S).tupleAvoidSet (κ := κ) φ =
      {x : κ → {x : X // x ∉ S} | ∀ i, D.map φ.1 (x i).1 ∉ D.branch} := by
  rfl

/-- If the noncritical Belyi existence theorem supplies, for every tuple in
`X \\ S`, a map sending `S` to the branch set and avoiding the branch set on the
tuple, then compactness extracts finitely many such maps. -/
theorem finite_subcover_on_complement_of_pointwise
    [Finite κ] [T1Space P] {S : Set X} [CompactSpace (κ → {x : X // x ∉ S})]
    (hcover : ∀ x : κ → {x : X // x ∉ S},
      ∃ φ : Φ, D.sendsSetToBranch S φ ∧ ∀ i, D.map φ (x i).1 ∉ D.branch) :
    ∃ t : Finset {φ : Φ // D.sendsSetToBranch S φ},
      (⋃ φ ∈ t, (D.complementCoverData S).tupleAvoidSet (κ := κ) φ) =
        (Set.univ : Set (κ → {x : X // x ∉ S})) := by
  apply BelyiCoverData.finite_subcover_of_pointwise (D.complementCoverData S)
  intro x
  rcases hcover x with ⟨φ, hφS, hφx⟩
  exact ⟨⟨φ, hφS⟩, hφx⟩

end BelyiCoverData

end SourceStack
end HilbertTest
