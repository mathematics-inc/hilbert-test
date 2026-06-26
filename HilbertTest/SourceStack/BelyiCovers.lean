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

/-- Membership form of `finite_subcover_of_pointwise`: every tuple is covered
by one of finitely many selected maps. -/
theorem finite_subcover_of_pointwise_forall
    [Finite κ] [T1Space P] [CompactSpace (κ → X)]
    (hcover : ∀ x : κ → X, ∃ φ : Φ, x ∈ D.tupleAvoidSet (κ := κ) φ) :
    ∃ t : Finset Φ,
      ∀ x : κ → X, ∃ φ ∈ t, x ∈ D.tupleAvoidSet (κ := κ) φ := by
  rcases D.finite_subcover_of_pointwise (κ := κ) hcover with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  intro x
  have hx : x ∈ ⋃ φ ∈ t, D.tupleAvoidSet (κ := κ) φ := by
    rw [ht]
    trivial
  simpa [Set.mem_iUnion] using hx

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

/-- Restrict the source of a Belyi cover datum to an arbitrary subtype. -/
def restrictSubtype (U : Set X) : BelyiCoverData U P Φ where
  branch := D.branch
  branch_finite := D.branch_finite
  map φ x := D.map φ x.1
  continuous_map φ := (D.continuous_map φ).comp continuous_subtype_val

theorem restrictSubtype_branch (U : Set X) :
    (D.restrictSubtype U).branch = D.branch := rfl

theorem restrictSubtype_map_apply
    (U : Set X) (φ : Φ) (x : U) :
    (D.restrictSubtype U).map φ x = D.map φ x.1 := rfl

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

/-- Membership form of the complement finite-subcover theorem. -/
theorem finite_subcover_on_complement_of_pointwise_forall
    [Finite κ] [T1Space P] {S : Set X} [CompactSpace (κ → {x : X // x ∉ S})]
    (hcover : ∀ x : κ → {x : X // x ∉ S},
      ∃ φ : Φ, D.sendsSetToBranch S φ ∧ ∀ i, D.map φ (x i).1 ∉ D.branch) :
    ∃ t : Finset {φ : Φ // D.sendsSetToBranch S φ},
      ∀ x : κ → {x : X // x ∉ S},
        ∃ φ ∈ t, x ∈ (D.complementCoverData S).tupleAvoidSet (κ := κ) φ := by
  rcases D.finite_subcover_on_complement_of_pointwise (κ := κ) hcover with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  intro x
  have hx : x ∈ ⋃ φ ∈ t, (D.complementCoverData S).tupleAvoidSet (κ := κ) φ := by
    rw [ht]
    trivial
  simpa [Set.mem_iUnion] using hx

/-- The Belyi open attached to a map: the preimage of the complement of the
finite branch set. -/
def belyiOpen (φ : Φ) : Set X :=
  {x : X | D.map φ x ∉ D.branch}

/-- Belyi opens are open in the abstract topological setting. -/
theorem belyiOpen_isOpen [T1Space P] (φ : Φ) : IsOpen (D.belyiOpen φ) := by
  exact isOpen_avoid_finite_preimage (D.continuous_map φ) D.branch_finite

/-- If a map sends a subset to the branch set, then its Belyi open is contained
in the complement of that subset. -/
theorem belyiOpen_subset_compl_of_sendsSetToBranch
    {A : Set X} {φ : Φ} (hφA : D.sendsSetToBranch A φ) :
    D.belyiOpen φ ⊆ Aᶜ := by
  intro x hx hxA
  exact hx (hφA x hxA)

/-- Membership in the abstract Belyi open is branch-set avoidance. -/
theorem mem_belyiOpen_iff (φ : Φ) (x : X) :
    x ∈ D.belyiOpen φ ↔ D.map φ x ∉ D.branch :=
  Iff.rfl

theorem restrictSubtype_belyiOpen_eq_preimage
    (U : Set X) (φ : Φ) :
    (D.restrictSubtype U).belyiOpen φ =
      (Subtype.val : U → X) ⁻¹' D.belyiOpen φ := rfl

/-- Abstract form of the formal step behind Corollary 1.2: if the existence
theorem supplies a map sending `A` to the branch set while a point avoids the
branch set, then there is a Belyi open containing the point and contained in
`Aᶜ`. -/
theorem exists_belyiOpen_inside_of_point_avoidance
    [T1Space P] {A : Set X} {x : X}
    (h : ∃ φ : Φ, D.sendsSetToBranch A φ ∧ D.map φ x ∉ D.branch) :
    ∃ φ : Φ, IsOpen (D.belyiOpen φ) ∧ x ∈ D.belyiOpen φ ∧ D.belyiOpen φ ⊆ Aᶜ := by
  rcases h with ⟨φ, hφA, hφx⟩
  exact
    ⟨φ, D.belyiOpen_isOpen φ, hφx,
      D.belyiOpen_subset_compl_of_sendsSetToBranch hφA⟩

end BelyiCoverData

/-- Abstract source interface for Mochizuki Theorem 2.5: for finite disjoint
sets `S` and `T`, there is a map sending `S` into the branch set and avoiding
the branch set on `T`.  The curve/divisor/Riemann-Roch work is precisely what
is needed to instantiate this interface for smooth proper connected curves. -/
structure NoncriticalBelyiExistence
    (X P Φ : Type*) [TopologicalSpace X] [TopologicalSpace P]
    extends BelyiCoverData X P Φ where
  exists_for_finite_disjoint :
    ∀ {S T : Set X}, S.Finite → T.Finite → Disjoint S T →
      ∃ φ : Φ, toBelyiCoverData.sendsSetToBranch S φ ∧
        ∀ x ∈ T, map φ x ∉ branch

namespace NoncriticalBelyiExistence

variable {X P Φ κ : Type*} [TopologicalSpace X] [TopologicalSpace P]
variable (D : NoncriticalBelyiExistence X P Φ)

/-- Restrict a noncritical Belyi existence package to an arbitrary subtype of
the source.  Finite disjoint sets are pushed forward along the subtype
embedding, the original existence theorem is applied, and the same map is
restricted back. -/
def restrictSubtype (U : Set X) : NoncriticalBelyiExistence U P Φ where
  branch := D.branch
  branch_finite := D.branch_finite
  map φ x := D.map φ x.1
  continuous_map φ := (D.continuous_map φ).comp continuous_subtype_val
  exists_for_finite_disjoint := by
    intro S T hS hT hdis
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
      ⟨φ, hφS, hφT⟩
    exact
      ⟨φ,
        (by
          intro x hx
          exact hφS x.1 ⟨x, hx, rfl⟩),
        (by
          intro x hx
          exact hφT x.1 ⟨x, hx, rfl⟩)⟩

theorem restrictSubtype_toBelyiCoverData (U : Set X) :
    (D.restrictSubtype U).toBelyiCoverData =
      D.toBelyiCoverData.restrictSubtype U := rfl

theorem restrictSubtype_map_apply
    (U : Set X) (φ : Φ) (x : U) :
    (D.restrictSubtype U).map φ x = D.map φ x.1 := rfl

/-- Theorem 2.5-style finite-set existence gives the pointwise tuple-cover
hypothesis over the complement of a fixed finite set. -/
theorem pointwise_cover_complement
    [Finite κ] {S : Set X} (hS : S.Finite)
    (x : κ → {x : X // x ∉ S}) :
    ∃ φ : Φ, D.toBelyiCoverData.sendsSetToBranch S φ ∧
      ∀ i, D.map φ (x i).1 ∉ D.branch := by
  let T : Set X := Set.range fun i : κ => (x i).1
  have hT : T.Finite := Set.finite_range _
  have hdis : Disjoint S T := by
    rw [Set.disjoint_left]
    intro y hyS hyT
    rcases hyT with ⟨i, rfl⟩
    exact (x i).2 hyS
  rcases D.exists_for_finite_disjoint hS hT hdis with ⟨φ, hφS, hφT⟩
  exact ⟨φ, hφS, fun i => hφT (x i).1 ⟨i, rfl⟩⟩

/-- Abstract Corollary 3.1 from a Theorem 2.5-style existence interface:
compactness extracts finitely many maps satisfying the fixed-set condition and
covering all tuples in the complement. -/
theorem finite_subcover_on_complement
    [Finite κ] [T1Space P] {S : Set X} (hS : S.Finite)
    [CompactSpace (κ → {x : X // x ∉ S})] :
    ∃ t : Finset {φ : Φ // D.toBelyiCoverData.sendsSetToBranch S φ},
      (⋃ φ ∈ t, (D.toBelyiCoverData.complementCoverData S).tupleAvoidSet (κ := κ) φ) =
        (Set.univ : Set (κ → {x : X // x ∉ S})) := by
  exact D.toBelyiCoverData.finite_subcover_on_complement_of_pointwise
    (fun x => D.pointwise_cover_complement hS x)

/-- Membership form of the abstract Corollary 3.1 finite subcover. -/
theorem finite_subcover_on_complement_forall
    [Finite κ] [T1Space P] {S : Set X} (hS : S.Finite)
    [CompactSpace (κ → {x : X // x ∉ S})] :
    ∃ t : Finset {φ : Φ // D.toBelyiCoverData.sendsSetToBranch S φ},
      ∀ x : κ → {x : X // x ∉ S},
        ∃ φ ∈ t,
          x ∈ (D.toBelyiCoverData.complementCoverData S).tupleAvoidSet (κ := κ) φ := by
  exact D.toBelyiCoverData.finite_subcover_on_complement_of_pointwise_forall
    (fun x => D.pointwise_cover_complement hS x)

/-- Abstract Corollary 1.2 from the Theorem 2.5-style existence interface: for
a finite complement `A` and a point outside `A`, there is a Belyi open
containing the point and contained in `Aᶜ`. -/
theorem exists_belyiOpen_inside_complement
    [T1Space P] {A : Set X} (hA : A.Finite) {x : X} (hxA : x ∉ A) :
    ∃ φ : Φ,
      IsOpen (D.toBelyiCoverData.belyiOpen φ) ∧
        x ∈ D.toBelyiCoverData.belyiOpen φ ∧
          D.toBelyiCoverData.belyiOpen φ ⊆ Aᶜ := by
  apply D.toBelyiCoverData.exists_belyiOpen_inside_of_point_avoidance
  have hsingleton : ({x} : Set X).Finite := Set.finite_singleton x
  have hdis : Disjoint A ({x} : Set X) := by
    rw [Set.disjoint_left]
    intro y hyA hyx
    rw [Set.mem_singleton_iff] at hyx
    exact hxA (hyx ▸ hyA)
  rcases D.exists_for_finite_disjoint hA hsingleton hdis with ⟨φ, hφA, hφx⟩
  exact ⟨φ, hφA, hφx x (by simp)⟩

/-- Theorem 2.5-style finite-set existence, restated as a Belyi-open
containment statement: for finite disjoint sets `S` and `T`, there is a Belyi
open containing `T` and contained in the complement of `S`. -/
theorem exists_belyiOpen_containing_finite_inside_complement
    [T1Space P] {S T : Set X} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ φ : Φ,
      IsOpen (D.toBelyiCoverData.belyiOpen φ) ∧
        T ⊆ D.toBelyiCoverData.belyiOpen φ ∧
          D.toBelyiCoverData.belyiOpen φ ⊆ Sᶜ := by
  rcases D.exists_for_finite_disjoint hS hT hdis with ⟨φ, hφS, hφT⟩
  exact
    ⟨φ, D.toBelyiCoverData.belyiOpen_isOpen φ, hφT,
      D.toBelyiCoverData.belyiOpen_subset_compl_of_sendsSetToBranch hφS⟩

/-- Abstract finite-complement form of Mochizuki Corollary 1.2: if a target
open set has finite complement and contains `x`, then the Theorem 2.5-style
existence interface supplies a Belyi open containing `x` and contained in that
open set.  The missing curve-specific input is that opens in a proper smooth
curve have finite complement. -/
theorem exists_belyiOpen_inside_open_of_finite_complement
    [T1Space P] {V : Set X} (_hV : IsOpen V) (hVcompl : Vᶜ.Finite)
    {x : X} (hxV : x ∈ V) :
    ∃ φ : Φ,
      IsOpen (D.toBelyiCoverData.belyiOpen φ) ∧
        x ∈ D.toBelyiCoverData.belyiOpen φ ∧
          D.toBelyiCoverData.belyiOpen φ ⊆ V := by
  rcases D.exists_belyiOpen_inside_complement hVcompl
      (show x ∉ Vᶜ by simpa using hxV) with
    ⟨φ, hopen, hx, hsubset⟩
  exact ⟨φ, hopen, hx, by simpa only [compl_compl] using hsubset⟩

/-- Abstract finite-complement-space form of Mochizuki Corollary 1.2: if
nonempty opens in the source have finite complement, then any open neighborhood
of a point contains a Belyi open through that point.  The curve-specific source
material instantiates `NonemptyOpenFiniteComplement`. -/
theorem exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
    [T1Space P] [NonemptyOpenFiniteComplement X]
    {V : Set X} (hV : IsOpen V) {x : X} (hxV : x ∈ V) :
    ∃ φ : Φ,
      IsOpen (D.toBelyiCoverData.belyiOpen φ) ∧
        x ∈ D.toBelyiCoverData.belyiOpen φ ∧
          D.toBelyiCoverData.belyiOpen φ ⊆ V := by
  exact D.exists_belyiOpen_inside_open_of_finite_complement hV
    (finite_compl_of_isOpen_of_mem hV hxV) hxV

/-- Finite-set version of the Corollary 1.2 wrapper: if `V` has finite
complement and contains a finite set `T`, then a Belyi open contains `T` and is
contained in `V`. -/
theorem exists_belyiOpen_containing_finite_inside_open_of_finite_complement
    [T1Space P] {V T : Set X} (_hV : IsOpen V) (hVcompl : Vᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ V) :
    ∃ φ : Φ,
      IsOpen (D.toBelyiCoverData.belyiOpen φ) ∧
        T ⊆ D.toBelyiCoverData.belyiOpen φ ∧
          D.toBelyiCoverData.belyiOpen φ ⊆ V := by
  have hdis : Disjoint Vᶜ T := by
    rw [Set.disjoint_left]
    intro x hxV hxT
    exact hxV (hTsub hxT)
  rcases D.exists_belyiOpen_containing_finite_inside_complement hVcompl hT hdis with
    ⟨φ, hopen, hTopen, hsubset⟩
  exact ⟨φ, hopen, hTopen, by simpa only [compl_compl] using hsubset⟩

end NoncriticalBelyiExistence

end SourceStack
end HilbertTest
