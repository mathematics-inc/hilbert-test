import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Constructions
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

/-- Curve-style cofinite-open property: every nonempty open subset has finite
complement.  For algebraic curves this is supplied by the theorem that a
nonempty open of a proper irreducible curve has finite complement; this class
keeps that source theorem as a precise topological input. -/
class NonemptyOpenFiniteComplement (X : Type*) [TopologicalSpace X] : Prop where
  finite_compl_of_isOpen_nonempty :
    ∀ {U : Set X}, IsOpen U → U.Nonempty → Uᶜ.Finite

theorem finite_compl_of_isOpen_nonempty
    [NonemptyOpenFiniteComplement X] {U : Set X}
    (hU : IsOpen U) (hne : U.Nonempty) :
    Uᶜ.Finite :=
  NonemptyOpenFiniteComplement.finite_compl_of_isOpen_nonempty hU hne

theorem finite_compl_of_isOpen_of_mem
    [NonemptyOpenFiniteComplement X] {U : Set X}
    (hU : IsOpen U) {x : X} (hx : x ∈ U) :
    Uᶜ.Finite :=
  finite_compl_of_isOpen_nonempty hU ⟨x, hx⟩

/-- The finite-complement-open property is inherited by open subspaces.  This
is the topological bridge used when the Belyi construction repeatedly restricts
from a curve to a nonempty open. -/
theorem nonemptyOpenFiniteComplement_subtype_of_isOpen
    [NonemptyOpenFiniteComplement X] {U : Set X} (hU : IsOpen U) :
    NonemptyOpenFiniteComplement U where
  finite_compl_of_isOpen_nonempty := by
    intro V hV hne
    have hVimageOpen : IsOpen ((Subtype.val : U → X) '' V) :=
      hU.isOpenMap_subtype_val V hV
    have hVimageNonempty : (((Subtype.val : U → X) '' V) : Set X).Nonempty := by
      rcases hne with ⟨x, hx⟩
      exact ⟨x.1, ⟨x, hx, rfl⟩⟩
    have hfiniteCompl : (((Subtype.val : U → X) '' V)ᶜ : Set X).Finite :=
      finite_compl_of_isOpen_nonempty hVimageOpen hVimageNonempty
    have himageComplSubset :
        ((Subtype.val : U → X) '' Vᶜ : Set X) ⊆
          (((Subtype.val : U → X) '' V)ᶜ : Set X) := by
      intro y hy hyV
      rcases hy with ⟨x, hxcompl, rfl⟩
      rcases hyV with ⟨z, hzV, hz⟩
      have hxz : x = z := Subtype.ext hz.symm
      exact hxcompl (by simpa [hxz] using hzV)
    have himageComplFinite : ((Subtype.val : U → X) '' Vᶜ : Set X).Finite :=
      hfiniteCompl.subset himageComplSubset
    exact himageComplFinite.of_finite_image
      (fun _ hx _ _ hxy => Subtype.ext hxy)

instance cofiniteTopology_nonemptyOpenFiniteComplement (X : Type*) :
    NonemptyOpenFiniteComplement (CofiniteTopology X) where
  finite_compl_of_isOpen_nonempty := by
    intro U hU hne
    exact (CofiniteTopology.isOpen_iff.mp hU) hne

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

/-- If compact subsets of a product lie coordinatewise in target subsets, then
the union of their coordinate projections still lies in the corresponding target
subset.  This is the set-theoretic containment behind the compact sets `H_v` in
Mochizuki Corollary 3.2. -/
theorem iUnion_pi_projection_image_subset_of_forall
    {ι κ : Type*} {Z : κ → Type*}
    (K : ι → Set ((i : κ) → Z i)) (A : (i : κ) → Set (Z i))
    (hK : ∀ i x, x ∈ K i → ∀ j, x j ∈ A j) (j : κ) :
    (⋃ i, (fun x : (l : κ) → Z l => x j) '' K i) ⊆ A j := by
  intro y hy
  rcases Set.mem_iUnion.mp hy with ⟨i, hyi⟩
  rcases hyi with ⟨x, hx, rfl⟩
  exact hK i x hx j

/-- Products of compact spaces are compact in Mathlib's product topology. -/
theorem compactSpace_pi
    {κ : Type*} (Z : κ → Type*) [∀ i, TopologicalSpace (Z i)]
    [∀ i, CompactSpace (Z i)] :
    CompactSpace ((i : κ) → Z i) :=
  inferInstance

/-- Locally compact second-countable spaces are sigma-compact.  This is the
countability input behind compact exhaustions in Mochizuki Corollary 3.2. -/
theorem sigmaCompact_of_locallyCompact_secondCountable
    [LocallyCompactSpace X] [SecondCountableTopology X] :
    SigmaCompactSpace X :=
  inferInstance

/-- A locally compact second-countable space admits a compact exhaustion. -/
theorem compactExhaustion_of_locallyCompact_secondCountable
    [LocallyCompactSpace X] [SecondCountableTopology X] :
    Nonempty (CompactExhaustion X) :=
  ⟨CompactExhaustion.choice X⟩

/-- An open subspace of a locally compact second-countable space admits a
compact exhaustion.  This packages the topological input used for the open sets
`U_phi` in Mochizuki Corollary 3.2. -/
theorem compactExhaustion_of_isOpen_subtype
    [LocallyCompactSpace X] [SecondCountableTopology X]
    {U : Set X} (hU : IsOpen U) :
    Nonempty (CompactExhaustion U) := by
  haveI : LocallyCompactSpace U := hU.locallyCompactSpace
  exact compactExhaustion_of_locallyCompact_secondCountable (X := U)

/-- The compact sets in a compact exhaustion are compact. -/
theorem compactExhaustion_isCompact
    (K : CompactExhaustion X) (n : ℕ) :
    IsCompact (K n) :=
  K.isCompact n

/-- A compact exhaustion covers the whole space. -/
theorem compactExhaustion_iUnion_eq
    (K : CompactExhaustion X) :
    (⋃ n, K n) = Set.univ :=
  K.iUnion_eq

/-- Each compact set in a compact exhaustion is contained in the interior of
the next one. -/
theorem compactExhaustion_subset_interior_succ
    (K : CompactExhaustion X) (n : ℕ) :
    K n ⊆ interior (K (n + 1)) :=
  K.subset_interior_succ n

/-- Compact exhaustions are monotone. -/
theorem compactExhaustion_subset
    (K : CompactExhaustion X) {m n : ℕ} (h : m ≤ n) :
    K m ⊆ K n :=
  K.subset h

/-- Every compact subset is eventually contained in a compact exhaustion. -/
theorem compactExhaustion_exists_superset_of_isCompact
    (K : CompactExhaustion X) {s : Set X} (hs : IsCompact s) :
    ∃ n, s ⊆ K n :=
  K.exists_superset_of_isCompact hs

/-- The interiors of a compact exhaustion form an open exhaustion. -/
theorem compactExhaustion_iUnion_interior_eq
    (K : CompactExhaustion X) :
    (⋃ n, interior (K n)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : x ∈ ⋃ n, K n := by
    rw [K.iUnion_eq]
    trivial
  rcases Set.mem_iUnion.mp hx with ⟨n, hxn⟩
  exact Set.mem_iUnion.mpr ⟨n + 1, K.subset_interior_succ n hxn⟩

/-- Every point of a space lies in the interior of some member of any compact
exhaustion. -/
theorem compactExhaustion_exists_mem_interior
    (K : CompactExhaustion X) (x : X) :
    ∃ n, x ∈ interior (K n) := by
  have hx : x ∈ ⋃ n, interior (K n) := by
    rw [compactExhaustion_iUnion_interior_eq K]
    trivial
  exact Set.mem_iUnion.mp hx

/-- Every compact subset is eventually contained in the interior of a member of
any compact exhaustion. -/
theorem compactExhaustion_exists_subset_interior_of_isCompact
    (K : CompactExhaustion X) {s : Set X} (hs : IsCompact s) :
    ∃ n, s ⊆ interior (K n) := by
  rcases K.exists_superset_of_isCompact hs with ⟨n, hn⟩
  exact ⟨n + 1, fun x hx => K.subset_interior_succ n (hn hx)⟩

/-- Each interior in a compact exhaustion is open. -/
theorem compactExhaustion_interior_isOpen
    (K : CompactExhaustion X) (n : ℕ) :
    IsOpen (interior (K n)) :=
  isOpen_interior

/-- In a Hausdorff space, the closure of each interior in a compact exhaustion
is compact.  This is the compact-closure step used in Mochizuki Corollary 3.2. -/
theorem compactExhaustion_closure_interior_isCompact
    [T2Space X] (K : CompactExhaustion X) (n : ℕ) :
    IsCompact (closure (interior (K n))) := by
  exact (K.isCompact n).of_isClosed_subset isClosed_closure
    (closure_minimal interior_subset (K.isCompact n).isClosed)

/-- In a locally compact space, every open neighborhood of a point contains a
compact set whose interior still contains the point. -/
theorem locallyCompact_exists_compact_subset
    [LocallyCompactSpace X] {x : X} {U : Set X}
    (hU : IsOpen U) (hx : x ∈ U) :
    ∃ K : Set X, IsCompact K ∧ x ∈ interior K ∧ K ⊆ U :=
  exists_compact_subset hU hx

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
