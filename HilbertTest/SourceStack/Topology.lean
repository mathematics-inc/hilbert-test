import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Separation.Basic

/-!
Source-stack topology lemmas used by the local compactness layer of
Mochizuki's Corollary 3.2 and by the proper-variety/local-field references
such as Lorscheid.
-/

namespace HilbertTest
namespace SourceStack

section Compactness

variable {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {s : Set X} {f : X → Y}

/-- Continuous images of compact sets are compact.  This is the exact topological
step needed after local-field properness supplies compactness of point spaces. -/
theorem lorscheid_compact_image
    (hs : IsCompact s)
    (hf : Continuous f) :
    IsCompact (f '' s) :=
  hs.image hf

/-- Compactness gives a finite subcover for an indexed open cover over a
specified index set. -/
theorem compact_elim_finite_subcover_indexed
    {b : Set ι} {c : ι → Set X}
    (hs : IsCompact s)
    (hcopen : ∀ i ∈ b, IsOpen (c i))
    (hcover : s ⊆ ⋃ i ∈ b, c i) :
    ∃ b' : Set ι, b' ⊆ b ∧ Set.Finite b' ∧ s ⊆ ⋃ i ∈ b', c i :=
  hs.elim_finite_subcover_image hcopen hcover

/-- A compact space has a finite subcover for any open cover indexed by an
arbitrary type.  This is the finite-choice step in Mochizuki Corollary 3.1. -/
theorem compactSpace_elim_finite_subcover
    [CompactSpace X] (U : ι → Set X)
    (hUopen : ∀ i, IsOpen (U i))
    (hcover : (Set.univ : Set X) ⊆ ⋃ i, U i) :
    ∃ t : Finset ι, (Set.univ : Set X) ⊆ ⋃ i ∈ t, U i :=
  isCompact_univ.elim_finite_subcover U hUopen hcover

/-- A compact-space open cover admits a finite subcover written as equality
with the whole space. -/
theorem compactSpace_finite_subcover_eq_univ
    [CompactSpace X] (U : ι → Set X)
    (hUopen : ∀ i, IsOpen (U i))
    (hcover : (Set.univ : Set X) ⊆ ⋃ i, U i) :
    ∃ t : Finset ι, (⋃ i ∈ t, U i) = (Set.univ : Set X) := by
  rcases isCompact_univ.elim_finite_subcover U hUopen hcover with ⟨t, ht⟩
  exact ⟨t, Set.eq_univ_of_univ_subset ht⟩

/-- Continuous preimages of opens are open. -/
theorem isOpen_preimage_continuous
    (hf : Continuous f) {U : Set Y} (hU : IsOpen U) :
    IsOpen (f ⁻¹' U) :=
  hU.preimage hf

/-- Finite intersections of open sets are open. -/
theorem isOpen_iInter_of_finite_index
    {κ : Type*} [Finite κ] (U : κ → Set X)
    (hU : ∀ i, IsOpen (U i)) :
    IsOpen (⋂ i, U i) :=
  isOpen_iInter_of_finite hU

/-- Complements of finite subsets in a T1 space are open. -/
theorem finite_compl_isOpen
    [T1Space X] {T : Set X} (hT : T.Finite) :
    IsOpen Tᶜ :=
  hT.isClosed.isOpen_compl

/-- The locus where a continuous map avoids a finite subset of a T1 target is
open. -/
theorem isOpen_avoid_finite_preimage
    [T1Space Y] (hf : Continuous f) {T : Set Y} (hT : T.Finite) :
    IsOpen {x : X | f x ∉ T} := by
  change IsOpen (f ⁻¹' Tᶜ)
  exact hT.isClosed.isOpen_compl.preimage hf

/-- The locus where every coordinate of a tuple maps outside a finite subset of
a T1 target is open.  This is the topological shape of the sets `U_phi` in
Mochizuki Corollary 3.1. -/
theorem isOpen_pi_avoid_finite
    {κ : Type*} [Finite κ] [T1Space Y]
    (φ : X → Y) (hφ : Continuous φ) {T : Set Y} (hT : T.Finite) :
    IsOpen {x : κ → X | ∀ i, φ (x i) ∉ T} := by
  have hset : {x : κ → X | ∀ i, φ (x i) ∉ T} =
      ⋂ i, {x : κ → X | φ (x i) ∉ T} := by
    ext x
    simp [Set.mem_iInter]
  rw [hset]
  refine isOpen_iInter_of_finite fun i => ?_
  change IsOpen ((fun x : κ → X => φ (x i)) ⁻¹' Tᶜ)
  exact hT.isClosed.isOpen_compl.preimage (hφ.comp (continuous_apply i))

/-- A finite union of compact subsets is compact. -/
theorem compact_iUnion_of_finite
    {κ : Type*} [Finite κ] (K : κ → Set X)
    (hK : ∀ i, IsCompact (K i)) :
    IsCompact (⋃ i, K i) :=
  isCompact_iUnion hK

/-- A finite union of continuous images of compact subsets is compact. -/
theorem compact_iUnion_image_of_finite
    {κ : Type*} [Finite κ] (K : κ → Set X)
    (hK : ∀ i, IsCompact (K i)) (hf : Continuous f) :
    IsCompact (⋃ i, f '' K i) :=
  isCompact_iUnion fun i => (hK i).image hf

/-- Coordinate projections send compact subsets of a product to compact
subsets.  This is the topological projection step in Mochizuki Corollary 3.2. -/
theorem compact_pi_projection_image
    {κ : Type*} {Z : κ → Type*} [∀ i, TopologicalSpace (Z i)]
    {s : Set ((i : κ) → Z i)} (hs : IsCompact s) (i : κ) :
    IsCompact ((fun x : (j : κ) → Z j => x i) '' s) :=
  hs.image (continuous_apply i)

/-- A finite union of coordinate projections of compact subsets of a product is
compact.  This is the shape of the compact sets `H_v` in Mochizuki
Corollary 3.2. -/
theorem compact_iUnion_pi_projection_image
    {ι κ : Type*} [Finite ι] {Z : κ → Type*}
    [∀ i, TopologicalSpace (Z i)]
    (K : ι → Set ((i : κ) → Z i))
    (hK : ∀ i, IsCompact (K i)) (j : κ) :
    IsCompact (⋃ i, (fun x : (l : κ) → Z l => x j) '' K i) :=
  isCompact_iUnion fun i => (hK i).image (continuous_apply j)

/-- Products of compact spaces are compact in Mathlib's product topology. -/
theorem compactSpace_pi
    {κ : Type*} (Z : κ → Type*) [∀ i, TopologicalSpace (Z i)]
    [∀ i, CompactSpace (Z i)] :
    CompactSpace ((i : κ) → Z i) :=
  inferInstance

/-- A proper topological map pulls compact subsets back to compact subsets. -/
theorem properMap_preimage_compact
    {K : Set Y} (hf : IsProperMap f) (hK : IsCompact K) :
    IsCompact (f ⁻¹' K) :=
  hf.isCompact_preimage hK

/-- A proper topological map is closed. -/
theorem properMap_isClosedMap
    (hf : IsProperMap f) :
    IsClosedMap f :=
  hf.isClosedMap

/-- Proper topological maps are stable under composition. -/
theorem properMap_comp
    {Z : Type*} [TopologicalSpace Z] {g : Y → Z}
    (hf : IsProperMap f) (hg : IsProperMap g) :
    IsProperMap (g ∘ f) :=
  hf.comp hg

/-- A closed embedding is a proper topological map. -/
theorem closedEmbedding_isProperMap
    (hf : Topology.IsClosedEmbedding f) :
    IsProperMap f :=
  hf.isProperMap

/-- A continuous map from a compact space to a Hausdorff space is proper. -/
theorem continuous_isProperMap_of_compactSpace
    [CompactSpace X] [T2Space Y]
    (hf : Continuous f) :
    IsProperMap f :=
  hf.isProperMap

end Compactness

end SourceStack
end HilbertTest
