import Mathlib.GroupTheory.CosetCover

/-!
Source-stack lemmas for the linear algebra used in Scherr-Zieve's
`Separated Belyi Maps`, especially the vector-space avoidance argument in
Lemma 2.2.

The point of this file is not to reprove Mathlib internals, but to expose
source-labeled theorem names that a Hilbert dataset can target directly.
-/

namespace HilbertTest
namespace SourceStack

open Set

section InfiniteField

variable {K V : Type*} [DivisionRing K] [Infinite K] [AddCommGroup V] [Module K V]

/-- Scherr-Zieve linear-algebra layer: over an infinite field, finitely many
proper subspaces do not cover a vector space. -/
theorem scherr_zieve_no_finite_cover_by_proper_subspaces
    (s : Finset (Subspace K V))
    (hproper : ∀ W ∈ s, W ≠ ⊤) :
    (⋃ W ∈ s, (W : Set V)) ≠ Set.univ := by
  intro hcover
  have htop : ⊤ ∈ s := Subspace.top_mem_of_biUnion_eq_univ hcover
  exact hproper ⊤ htop rfl

/-- Avoidance form of the same finite-union lemma: there is a vector outside
every member of a finite family of proper subspaces. -/
theorem scherr_zieve_exists_vector_avoiding_finite_proper_subspaces
    (s : Finset (Subspace K V))
    (hproper : ∀ W ∈ s, W ≠ ⊤) :
    ∃ v : V, ∀ W ∈ s, v ∉ W := by
  by_contra hnone
  push_neg at hnone
  have hcover : (⋃ W ∈ s, (W : Set V)) = Set.univ := by
    ext v
    constructor
    · intro _
      trivial
    · intro _
      obtain ⟨W, hWs, hvW⟩ := hnone v
      exact mem_iUnion.2 ⟨W, mem_iUnion.2 ⟨hWs, hvW⟩⟩
  exact scherr_zieve_no_finite_cover_by_proper_subspaces s hproper hcover

end InfiniteField

end SourceStack
end HilbertTest
