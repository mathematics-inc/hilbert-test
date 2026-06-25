import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Maps.Proper.Basic

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
