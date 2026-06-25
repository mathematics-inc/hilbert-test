import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.NumberField.Completion

/-!
Local-field compactness source wrappers available in pinned Mathlib.

These do not yet cover the full theorem used by Mochizuki's Corollary 3.2
for arbitrary proper varieties over arbitrary local fields, but they expose the
checked local compactness/properness results that currently exist for p-adics
and infinite-place completions of number fields.
-/

noncomputable section

namespace HilbertTest
namespace SourceStack
namespace LocalFields

/-- The p-adic integers are compact. -/
theorem padicInt_compactSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    CompactSpace ℤ_[p] :=
  inferInstance

/-- The p-adic numbers form a proper metric space. -/
theorem padic_properSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    ProperSpace ℚ_[p] :=
  inferInstance

/-- The p-adic numbers are locally compact. -/
theorem padic_locallyCompactSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    LocallyCompactSpace ℚ_[p] :=
  inferInstance

/-- The p-adic numbers are complete. -/
theorem padic_completeSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    CompleteSpace ℚ_[p] :=
  inferInstance

/-- The completion of a number field at an infinite place is locally compact. -/
theorem infinitePlace_completion_locallyCompactSpace
    {K : Type*} [Field K] (v : NumberField.InfinitePlace K) :
    LocallyCompactSpace v.Completion :=
  inferInstance

end LocalFields
end SourceStack
end HilbertTest
