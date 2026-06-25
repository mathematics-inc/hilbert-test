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

omit [Infinite K] in
/-- A nonzero linear map has a proper kernel.  This is the hyperplane
avoidance bridge used when evaluations of Riemann-Roch spaces are known to be
nonzero. -/
theorem linearMap_ker_ne_top_of_ne_zero
    {W : Type*} [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) (hf : f ≠ 0) :
    LinearMap.ker f ≠ ⊤ := by
  intro htop
  exact hf (LinearMap.ker_eq_top.mp htop)

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

/-- Finite nonzero linear evaluations can be made simultaneously nonzero over
an infinite field.  This is the pure linear-algebra core of the finite
basepoint/evaluation avoidance step in the Scherr-Zieve curve reduction. -/
theorem exists_vector_avoiding_kernels_of_nonzero_linear_maps
    {ι W : Type*} [AddCommGroup W] [Module K W]
    (s : Finset ι) (f : ι → V →ₗ[K] W)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    ∃ v : V, ∀ i ∈ s, f i v ≠ 0 := by
  classical
  let kernels : Finset (Subspace K V) := s.image fun i => LinearMap.ker (f i)
  have hproper : ∀ W' ∈ kernels, W' ≠ ⊤ := by
    intro W' hW'
    rcases Finset.mem_image.mp hW' with ⟨i, hi, rfl⟩
    exact linearMap_ker_ne_top_of_ne_zero (f i) (hf i hi)
  obtain ⟨v, hv⟩ :=
    scherr_zieve_exists_vector_avoiding_finite_proper_subspaces kernels hproper
  refine ⟨v, ?_⟩
  intro i hi hzero
  exact hv (LinearMap.ker (f i)) (Finset.mem_image.mpr ⟨i, hi, rfl⟩) hzero

/-- Linear-form specialization of
`exists_vector_avoiding_kernels_of_nonzero_linear_maps`. -/
theorem exists_vector_nonzero_on_finite_linear_forms
    (s : Finset (V →ₗ[K] K))
    (hf : ∀ f ∈ s, f ≠ 0) :
    ∃ v : V, ∀ f ∈ s, f v ≠ 0 := by
  exact exists_vector_avoiding_kernels_of_nonzero_linear_maps
    (K := K) (V := V) s (fun f => f) hf

/-- The common kernel of a finite family of linear forms.  This is the
linear-algebra abstraction of imposing vanishing at a finite set of points. -/
noncomputable def commonKernel
    {σ : Type*} (s : Finset σ) (f : σ → V →ₗ[K] K) : Subspace K V :=
  ⨅ i : {i // i ∈ s}, LinearMap.ker (f i.1)

omit [Infinite K] in
/-- Membership in the common kernel is exactly simultaneous vanishing of all
linear forms in the finite family. -/
theorem mem_commonKernel_iff
    {σ : Type*} (s : Finset σ) (f : σ → V →ₗ[K] K) (v : V) :
    v ∈ commonKernel (K := K) (V := V) s f ↔ ∀ i ∈ s, f i v = 0 := by
  simp [commonKernel]

/-- Scherr-Zieve constrained-section linear algebra: inside a given subspace,
finitely many nonzero linear forms can be made simultaneously nonzero. -/
theorem exists_vector_in_subspace_nonzero_on_finite_linear_forms
    {ι : Type*} (W : Subspace K V) (s : Finset ι) (f : ι → V →ₗ[K] K)
    (hf : ∀ i ∈ s, (f i).comp W.subtype ≠ 0) :
    ∃ v : V, v ∈ W ∧ ∀ i ∈ s, f i v ≠ 0 := by
  obtain ⟨w, hw⟩ :=
    exists_vector_avoiding_kernels_of_nonzero_linear_maps
      (K := K) (V := W) s (fun i => (f i).comp W.subtype) hf
  exact ⟨w, w.property, by intro i hi; exact hw i hi⟩

/-- Scherr-Zieve/Riemann-Roch handoff: if the "avoid" evaluations remain
nonzero after restricting to the common kernel of the "vanish" evaluations,
then there is a vector vanishing on the first finite set and nonvanishing on
the second. -/
theorem exists_vector_vanishing_and_nonzero_on_finite_linear_forms
    {σ τ : Type*} (S : Finset σ) (T : Finset τ)
    (vanish : σ → V →ₗ[K] K) (avoid : τ → V →ₗ[K] K)
    (havoid : ∀ j ∈ T,
      (avoid j).comp (commonKernel (K := K) (V := V) S vanish).subtype ≠ 0) :
    ∃ v : V, (∀ i ∈ S, vanish i v = 0) ∧ ∀ j ∈ T, avoid j v ≠ 0 := by
  obtain ⟨v, hvW, hvavoid⟩ :=
    exists_vector_in_subspace_nonzero_on_finite_linear_forms
      (K := K) (V := V) (commonKernel (K := K) (V := V) S vanish)
      T avoid havoid
  exact ⟨v, (mem_commonKernel_iff (K := K) (V := V) S vanish v).mp hvW, hvavoid⟩

end InfiniteField

end SourceStack
end HilbertTest
