import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.NumberField.Completion
import Mathlib.Topology.Compactness.SigmaCompact

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

/-- The p-adic numbers are second countable. -/
theorem padic_secondCountableTopology
    (p : ℕ) [Fact (Nat.Prime p)] :
    SecondCountableTopology ℚ_[p] :=
  inferInstance

/-- The p-adic numbers are sigma-compact. -/
theorem padic_sigmaCompactSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    SigmaCompactSpace ℚ_[p] :=
  inferInstance

/-- The p-adic numbers admit a compact exhaustion. -/
theorem padic_compactExhaustion_exists
    (p : ℕ) [Fact (Nat.Prime p)] :
    Nonempty (CompactExhaustion ℚ_[p]) :=
  ⟨CompactExhaustion.choice ℚ_[p]⟩

/-- The completion of a number field at an infinite place is locally compact. -/
theorem infinitePlace_completion_locallyCompactSpace
    {K : Type*} [Field K] (v : NumberField.InfinitePlace K) :
    LocallyCompactSpace v.Completion :=
  inferInstance

/-- The embedding of an infinite-place completion into `ℂ` is an isometry. -/
theorem infinitePlace_completion_isometry_extensionEmbedding
    {K : Type*} [Field K] (v : NumberField.InfinitePlace K) :
    Isometry (NumberField.InfinitePlace.Completion.extensionEmbedding v) :=
  NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v

/-- The image of an infinite-place completion inside `ℂ` is closed. -/
theorem infinitePlace_completion_isClosed_image_extensionEmbedding
    {K : Type*} [Field K] (v : NumberField.InfinitePlace K) :
    IsClosed (Set.range (NumberField.InfinitePlace.Completion.extensionEmbedding v)) :=
  NumberField.InfinitePlace.Completion.isClosed_image_extensionEmbedding v

/-- The completion of a number field at an infinite place is second countable. -/
theorem infinitePlace_completion_secondCountableTopology
    {K : Type*} [Field K] (v : NumberField.InfinitePlace K) :
    SecondCountableTopology v.Completion := by
  have hf : Topology.IsEmbedding
      (NumberField.InfinitePlace.Completion.extensionEmbedding v) :=
    (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding
  exact hf.secondCountableTopology

/-- The completion of a number field at an infinite place is sigma-compact. -/
theorem infinitePlace_completion_sigmaCompactSpace
    {K : Type*} [Field K] (v : NumberField.InfinitePlace K) :
    SigmaCompactSpace v.Completion := by
  haveI : SecondCountableTopology v.Completion :=
    infinitePlace_completion_secondCountableTopology v
  infer_instance

/-- The completion of a number field at an infinite place admits a compact
exhaustion. -/
theorem infinitePlace_completion_compactExhaustion_exists
    {K : Type*} [Field K] (v : NumberField.InfinitePlace K) :
    Nonempty (CompactExhaustion v.Completion) := by
  haveI : SecondCountableTopology v.Completion :=
    infinitePlace_completion_secondCountableTopology v
  exact ⟨CompactExhaustion.choice v.Completion⟩

/-- A complex infinite-place completion is isometric to `ℂ`. -/
theorem infinitePlace_completion_isometryEquivComplex_exists
    {K : Type*} [Field K] {v : NumberField.InfinitePlace K}
    (hv : NumberField.InfinitePlace.IsComplex v) :
    Nonempty (v.Completion ≃ᵢ ℂ) :=
  ⟨NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv⟩

/-- A real infinite-place completion is isometric to `ℝ`. -/
theorem infinitePlace_completion_isometryEquivReal_exists
    {K : Type*} [Field K] {v : NumberField.InfinitePlace K}
    (hv : NumberField.InfinitePlace.IsReal v) :
    Nonempty (v.Completion ≃ᵢ ℝ) :=
  ⟨NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv⟩

end LocalFields
end SourceStack
end HilbertTest
