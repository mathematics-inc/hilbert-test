import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Finite.Basic

/-!
Finite-set cardinality bookkeeping for the induction in Mochizuki Lemma 2.2 and
the corresponding `P^1` constructions in Belyi/Scherr-Zieve.
-/

namespace HilbertTest
namespace SourceStack

section ImageCardinality

variable {α β : Type*}

/-- If a map identifies two distinct elements of a finite set, then its image
has strictly smaller cardinality than the original finite set. -/
theorem card_image_lt_of_exists_distinct_same_image
    [DecidableEq β]
    (s : Finset α) (f : α → β) {a b : α}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) (hfab : f a = f b) :
    (s.image f).card < s.card := by
  have hnot_inj : ¬ Set.InjOn f (s : Set α) := by
    intro hinj
    exact hab (hinj ha hb hfab)
  have hne : (s.image f).card ≠ s.card := by
    intro hcard
    exact hnot_inj ((Finset.card_image_iff (s := s) (f := f)).1 hcard)
  exact lt_of_le_of_ne Finset.card_image_le hne

/-- Pigeonhole form: a map from a finite set into a strictly smaller finite set
identifies two distinct source elements. -/
theorem exists_distinct_same_image_of_maps_to_smaller
    (s : Finset α) (t : Finset β) (f : α → β)
    (hcard : t.card < s.card)
    (hmap : ∀ a ∈ s, f a ∈ t) :
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ f a = f b :=
  Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmap

/-- If a subset has strictly smaller image cardinality, then the image of the
ambient finite set has strictly smaller cardinality. -/
theorem card_image_lt_of_subset_with_smaller_subimage
    [DecidableEq β]
    (s u : Finset α) (f : α → β)
    (hu : u ⊆ s)
    (hcard : (u.image f).card < u.card) :
    (s.image f).card < s.card := by
  obtain ⟨a, ha, b, hb, hab, hfab⟩ :=
    exists_distinct_same_image_of_maps_to_smaller
      u (u.image f) f hcard (by intro x hx; exact Finset.mem_image_of_mem f hx)
  exact card_image_lt_of_exists_distinct_same_image s f (hu ha) (hu hb) hab hfab

/-- Lemma 2.2 cardinality package: four distinguished elements in a finite set
whose images occupy at most three values force a strict image-cardinality drop
for the whole finite set. -/
theorem card_image_lt_of_subset_card_four_image_le_three
    [DecidableEq β]
    (s u : Finset α) (f : α → β)
    (hu : u ⊆ s)
    (hucard : u.card = 4)
    (himage : (u.image f).card ≤ 3) :
    (s.image f).card < s.card := by
  have hcard : (u.image f).card < u.card := by omega
  exact card_image_lt_of_subset_with_smaller_subimage s u f hu hcard

/-- Lemma 2.2 induction handoff: under the four-to-three image hypothesis,
the actual image finset is a strictly smaller finite target containing every
image of the original finite set. -/
theorem exists_smaller_image_finset_of_subset_card_four_image_le_three
    [DecidableEq β]
    (s u : Finset α) (f : α → β)
    (hu : u ⊆ s)
    (hucard : u.card = 4)
    (himage : (u.image f).card ≤ 3) :
    ∃ t : Finset β,
      t = s.image f ∧
        (∀ x ∈ s, f x ∈ t) ∧
          t.card < s.card := by
  refine ⟨s.image f, rfl, ?_, ?_⟩
  · intro x hx
    exact Finset.mem_image_of_mem f hx
  · exact card_image_lt_of_subset_card_four_image_le_three
      s u f hu hucard himage

end ImageCardinality

section InfiniteEnlargement

variable {α : Type*} [Infinite α] [DecidableEq α]

/-- Theorem 2.5 finite-set enlargement step: in an infinite set of points, a
finite set `T` disjoint from `S` can be enlarged past any prescribed cardinality
while remaining disjoint from `S`. -/
theorem exists_finset_superset_card_ge_disjoint
    (S T : Finset α) (hdis : ∀ x, x ∈ S → x ∉ T) (N : ℕ) :
    ∃ T' : Finset α,
      T ⊆ T' ∧ (∀ x, x ∈ S → x ∉ T') ∧ N ≤ T'.card := by
  classical
  have hcomp : ((↑(S ∪ T) : Set α)ᶜ).Infinite :=
    (S ∪ T).finite_toSet.infinite_compl
  obtain ⟨R, hRsub, hRcard⟩ := hcomp.exists_subset_card_eq N
  refine ⟨T ∪ R, ?_, ?_, ?_⟩
  · intro x hx
    exact Finset.mem_union.mpr (Or.inl hx)
  · intro x hxS hxTR
    rcases Finset.mem_union.mp hxTR with hxT | hxR
    · exact hdis x hxS hxT
    · exact hRsub hxR (by
        exact Finset.mem_coe.mpr (Finset.mem_union.mpr (Or.inl hxS)))
  · rw [← hRcard]
    exact Finset.card_le_card (by intro x hx; exact Finset.mem_union.mpr (Or.inr hx))

end InfiniteEnlargement

end SourceStack
end HilbertTest
