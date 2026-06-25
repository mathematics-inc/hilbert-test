import Mathlib.Data.Finset.Card

/-!
Finite-set cardinality bookkeeping for the induction in Mochizuki Lemma 2.2 and
the corresponding `P^1` constructions in Belyi/Scherr-Zieve.
-/

namespace HilbertTest
namespace SourceStack

section ImageCardinality

variable {α β : Type*} [DecidableEq β]

/-- If a map identifies two distinct elements of a finite set, then its image
has strictly smaller cardinality than the original finite set. -/
theorem card_image_lt_of_exists_distinct_same_image
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

end ImageCardinality

end SourceStack
end HilbertTest
