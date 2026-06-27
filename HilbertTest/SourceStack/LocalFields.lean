import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.NumberField.Completion
import Mathlib.NumberTheory.NumberField.FinitePlaces
import Mathlib.Data.Rat.Encodable
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Compactness.SigmaCompact

/-!
Local-field compactness source wrappers available in pinned Mathlib.

These do not yet cover the full theorem used by Mochizuki's Corollary 3.2
for arbitrary proper varieties over arbitrary local fields, but they expose the
checked local compactness/properness results that currently exist for p-adics
and infinite-place completions of number fields, together with the checked
finite-place completion, valuation, and norm facts currently available in
Mathlib.
-/

noncomputable section

open IsDedekindDomain
open scoped NumberField

namespace HilbertTest
namespace SourceStack
namespace LocalFields

/-- Number fields are countable, using a finite-dimensional `ℚ`-basis. -/
theorem numberField_countable
    (K : Type*) [Field K] [NumberField K] :
    Countable K := by
  classical
  let b := Module.finBasis ℚ K
  exact Countable.of_equiv (Fin (Module.finrank ℚ K) → ℚ)
    b.equivFun.toEquiv.symm

/-- Any topology on a number field is separable, since the underlying type is
countable. -/
theorem numberField_separableSpace
    (K : Type*) [Field K] [NumberField K] [TopologicalSpace K] :
    TopologicalSpace.SeparableSpace K := by
  classical
  haveI : Countable K := numberField_countable K
  exact TopologicalSpace.SeparableSpace.of_denseRange (fun x : K => x)
    (by simpa using (denseRange_id : DenseRange (id : K → K)))

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

/-- The p-adic numbers have a compact exhaustion. -/
theorem padic_compactExhaustion_exists
    (p : ℕ) [Fact (Nat.Prime p)] :
    Nonempty (CompactExhaustion ℚ_[p]) :=
  ⟨CompactExhaustion.choice ℚ_[p]⟩

/-- The completion of a number field at a finite place carries a normed-field
structure. -/
theorem finitePlace_adicCompletion_normedField_exists
    {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    Nonempty (NormedField (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) :=
  ⟨inferInstance⟩

/-- The completion of a number field at a finite place is complete. -/
theorem finitePlace_adicCompletion_completeSpace
    {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    CompleteSpace (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) :=
  inferInstance

/-- The finite-place completion of a number field is separable.  This is the
completion of the countable field `K` for the `v`-adic uniformity. -/
theorem finitePlace_adicCompletion_separableSpace
    {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    TopologicalSpace.SeparableSpace
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) := by
  letI : UniformSpace K := v.adicValued.toUniformSpace
  haveI : TopologicalSpace.SeparableSpace K := numberField_separableSpace K
  unfold IsDedekindDomain.HeightOneSpectrum.adicCompletion
  infer_instance

/-- The finite-place completion of a number field is second countable. -/
theorem finitePlace_adicCompletion_secondCountableTopology
    {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    SecondCountableTopology
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) := by
  haveI : TopologicalSpace.SeparableSpace
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) :=
    finitePlace_adicCompletion_separableSpace v
  exact UniformSpace.secondCountable_of_separable _

/-- Once local compactness is available, the finite-place completion of a
number field admits a compact exhaustion; second countability is supplied by the
preceding finite-place bridge. -/
theorem finitePlace_adicCompletion_compactExhaustion_exists_of_locallyCompact
    {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    [LocallyCompactSpace (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)] :
    Nonempty (CompactExhaustion
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) := by
  haveI : SecondCountableTopology
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) :=
    finitePlace_adicCompletion_secondCountableTopology v
  exact ⟨CompactExhaustion.choice
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)⟩

/-- The canonical embedding of a number field into its finite-place completion
has norm equal to the associated finite-place absolute value. -/
theorem finitePlace_embedding_norm_def
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    ‖NumberField.embedding v x‖ = NumberField.vadicAbv v x :=
  NumberField.FinitePlace.norm_def v x

/-- Integral elements have finite-place norm at most one. -/
theorem finitePlace_integral_norm_le_one
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    ‖NumberField.embedding v x‖ ≤ 1 :=
  NumberField.norm_le_one v x

/-- An integral element has finite-place norm one exactly when it is not in the
corresponding maximal ideal. -/
theorem finitePlace_integral_norm_eq_one_iff_not_mem
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    ‖NumberField.embedding v x‖ = 1 ↔ x ∉ v.asIdeal :=
  NumberField.norm_eq_one_iff_not_mem v x

/-- An integral element has finite-place norm less than one exactly when it lies
in the corresponding maximal ideal. -/
theorem finitePlace_integral_norm_lt_one_iff_mem
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    ‖NumberField.embedding v x‖ < 1 ↔ x ∈ v.asIdeal :=
  NumberField.norm_lt_one_iff_mem v x

/-- The finite-place absolute value agrees with the norm of the embedding into
the completion attached to its maximal ideal. -/
theorem finitePlace_norm_embedding_eq
    {K : Type*} [Field K] [NumberField K]
    (w : NumberField.FinitePlace K) (x : K) :
    ‖NumberField.embedding w.maximalIdeal x‖ = w x :=
  NumberField.FinitePlace.norm_embedding_eq w x

/-- The finite place associated to a height-one prime evaluates as the
corresponding embedding norm. -/
theorem finitePlace_mk_apply
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    NumberField.FinitePlace.mk v x = ‖NumberField.embedding v x‖ :=
  NumberField.FinitePlace.apply v x

/-- A finite-place absolute value is positive exactly on nonzero elements. -/
theorem finitePlace_pos_iff
    {K : Type*} [Field K] [NumberField K]
    {w : NumberField.FinitePlace K} {x : K} :
    0 < w x ↔ x ≠ 0 :=
  NumberField.FinitePlace.pos_iff

/-- Reconstructing a finite place from its maximal ideal gives the same place. -/
theorem finitePlace_mk_maximalIdeal
    {K : Type*} [Field K] [NumberField K]
    (w : NumberField.FinitePlace K) :
    NumberField.FinitePlace.mk w.maximalIdeal = w :=
  NumberField.FinitePlace.mk_maximalIdeal w

/-- Equality of finite places made from height-one primes is equality of the
primes. -/
theorem finitePlace_mk_eq_iff
    {K : Type*} [Field K] [NumberField K]
    {v₁ v₂ : HeightOneSpectrum (𝓞 K)} :
    NumberField.FinitePlace.mk v₁ = NumberField.FinitePlace.mk v₂ ↔ v₁ = v₂ :=
  NumberField.FinitePlace.mk_eq_iff

/-- The maximal ideal of the finite place associated to a height-one prime is
that prime. -/
theorem finitePlace_maximalIdeal_mk
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    (NumberField.FinitePlace.mk v).maximalIdeal = v :=
  NumberField.FinitePlace.maximalIdeal_mk v

/-- The maximal-ideal map on finite places is injective. -/
theorem finitePlace_maximalIdeal_injective
    {K : Type*} [Field K] [NumberField K] :
    Function.Injective (fun w : NumberField.FinitePlace K => w.maximalIdeal) :=
  NumberField.FinitePlace.maximalIdeal_injective

/-- Two finite places have the same maximal ideal exactly when they are equal. -/
theorem finitePlace_maximalIdeal_inj
    {K : Type*} [Field K] [NumberField K]
    (w₁ w₂ : NumberField.FinitePlace K) :
    w₁.maximalIdeal = w₂.maximalIdeal ↔ w₁ = w₂ :=
  NumberField.FinitePlace.maximalIdeal_inj w₁ w₂

/-- Finite places are equivalent to height-one primes of the ring of integers. -/
theorem finitePlace_equivHeightOneSpectrum
    {K : Type*} [Field K] [NumberField K] :
    Nonempty (NumberField.FinitePlace K ≃ HeightOneSpectrum (𝓞 K)) :=
  ⟨NumberField.FinitePlace.equivHeightOneSpectrum⟩

/-- A nonzero number-field element has nontrivial finite-place norm at only
finitely many finite places. -/
theorem finitePlace_mulSupport_finite
    {K : Type*} [Field K] [NumberField K] {x : K} (hx : x ≠ 0) :
    (Function.mulSupport fun w : NumberField.FinitePlace K => w x).Finite :=
  NumberField.FinitePlace.mulSupport_finite hx

/-- A nonzero algebraic integer has nontrivial finite-place norm at only
finitely many finite places. -/
theorem finitePlace_mulSupport_finite_int
    {K : Type*} [Field K] [NumberField K] {x : 𝓞 K} (hx : x ≠ 0) :
    (Function.mulSupport fun w : NumberField.FinitePlace K => w (x : K)).Finite :=
  NumberField.FinitePlace.mulSupport_finite_int hx

/-- The inverse of the finite-place/height-one-prime equivalence evaluates as
the corresponding embedding norm. -/
theorem heightOneSpectrum_equivHeightOneSpectrum_symm_apply
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    (NumberField.FinitePlace.equivHeightOneSpectrum.symm v) x =
      ‖NumberField.embedding v x‖ :=
  IsDedekindDomain.HeightOneSpectrum.equivHeightOneSpectrum_symm_apply v x

/-- The finite-place embedding norm times the local ideal norm is normalized to
one. -/
theorem heightOneSpectrum_embedding_mul_absNorm
    {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) {x : 𝓞 K} (hx : x ≠ 0) :
    ‖NumberField.embedding v (x : K)‖ *
        (Ideal.absNorm (v.maxPowDividing (Ideal.span {x})) : ℝ) = 1 :=
  IsDedekindDomain.HeightOneSpectrum.embedding_mul_absNorm v hx

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
