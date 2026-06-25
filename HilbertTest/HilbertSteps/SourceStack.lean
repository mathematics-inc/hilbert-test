import HilbertTest.SourceStack.FiniteSet
import HilbertTest.SourceStack.LinearAlgebra
import HilbertTest.SourceStack.ComplexSeparation
import HilbertTest.SourceStack.AffineSpace
import HilbertTest.SourceStack.ProjectiveLine
import HilbertTest.SourceStack.ProjectiveSpectrum
import HilbertTest.SourceStack.RationalMaps
import HilbertTest.SourceStack.FunctionFields
import HilbertTest.SourceStack.ResidueFields
import HilbertTest.SourceStack.FieldTheory
import HilbertTest.SourceStack.UnramifiedEtale
import HilbertTest.SourceStack.Ramification
import HilbertTest.SourceStack.DedekindDvr
import HilbertTest.SourceStack.FractionalIdeals
import HilbertTest.SourceStack.ArithmeticFunctionFields
import HilbertTest.SourceStack.Topology
import HilbertTest.SourceStack.LocalFields
import HilbertTest.SourceStack.Schemes

/-!
Hilbert-facing proof targets for the first recursive source-stack layer.

Each theorem in this file is intentionally phrased as a small benchmark target:
the source material has already been normalized into a stable theorem in
`HilbertTest.SourceStack.*`, and this file records the corresponding checked
formal step that Hilbert can solve and verify.
-/

namespace HilbertTest
namespace HilbertSteps

open Set
open CategoryTheory
open Opposite IsLocalRing
open AlgebraicGeometry
open HomogeneousLocalization
open scoped TensorProduct
open scoped Pointwise
open scoped nonZeroDivisors
open scoped IntermediateField Polynomial
open scoped AlgebraicGeometry

section FiniteSet

variable {α β : Type*}

theorem hilbert_card_image_lt_of_exists_distinct_same_image
    [DecidableEq β]
    (s : Finset α) (f : α → β) {a b : α}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) (hfab : f a = f b) :
    (s.image f).card < s.card := by
  exact SourceStack.card_image_lt_of_exists_distinct_same_image s f ha hb hab hfab

theorem hilbert_exists_distinct_same_image_of_maps_to_smaller
    (s : Finset α) (t : Finset β) (f : α → β)
    (hcard : t.card < s.card)
    (hmap : ∀ a ∈ s, f a ∈ t) :
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ f a = f b := by
  exact SourceStack.exists_distinct_same_image_of_maps_to_smaller s t f hcard hmap

theorem hilbert_card_image_lt_of_subset_with_smaller_subimage
    [DecidableEq β]
    (s u : Finset α) (f : α → β)
    (hu : u ⊆ s)
    (hcard : (u.image f).card < u.card) :
    (s.image f).card < s.card := by
  exact SourceStack.card_image_lt_of_subset_with_smaller_subimage s u f hu hcard

theorem hilbert_card_image_lt_of_subset_card_four_image_le_three
    [DecidableEq β]
    (s u : Finset α) (f : α → β)
    (hu : u ⊆ s)
    (hucard : u.card = 4)
    (himage : (u.image f).card ≤ 3) :
    (s.image f).card < s.card := by
  exact SourceStack.card_image_lt_of_subset_card_four_image_le_three
    s u f hu hucard himage

end FiniteSet

section LinearAlgebra

variable {K V : Type*} [DivisionRing K] [Infinite K] [AddCommGroup V] [Module K V]

theorem hilbert_scherr_zieve_no_finite_cover_by_proper_subspaces
    (s : Finset (Subspace K V))
    (hproper : ∀ W ∈ s, W ≠ ⊤) :
    (⋃ W ∈ s, (W : Set V)) ≠ Set.univ := by
  exact SourceStack.scherr_zieve_no_finite_cover_by_proper_subspaces s hproper

theorem hilbert_scherr_zieve_exists_vector_avoiding_finite_proper_subspaces
    (s : Finset (Subspace K V))
    (hproper : ∀ W ∈ s, W ≠ ⊤) :
    ∃ v : V, ∀ W ∈ s, v ∉ W := by
  exact SourceStack.scherr_zieve_exists_vector_avoiding_finite_proper_subspaces s hproper

end LinearAlgebra

section ComplexSeparation

theorem hilbert_finset_complex_inf_norm_sub_pos
    (S : Finset ℂ) (β : ℂ) (hS : S.Nonempty) (hβ : β ∉ S) :
    0 < S.inf' hS (fun α : ℂ => ‖α - β‖) := by
  exact SourceStack.finset_complex_inf_norm_sub_pos S β hS hβ

theorem hilbert_exists_complex_point_nearby_separating_finset
    (S : Finset ℂ) (β : ℂ) (C : ℝ) (hC : 0 < C) (hβ : β ∉ S) :
    ∃ lam : ℂ,
      lam ≠ β ∧
      (∀ α ∈ S, lam ≠ α) ∧
      ∀ α ∈ S, C * ‖β - lam‖ ≤ ‖α - lam‖ := by
  exact SourceStack.exists_complex_point_nearby_separating_finset S β C hC hβ

theorem hilbert_exists_reciprocal_translate_separating_finset
    (S : Finset ℂ) (β : ℂ) (C : ℝ) (hC : 0 < C) (hβ : β ∉ S) :
    ∃ lam : ℂ,
      lam ≠ β ∧
      (∀ α ∈ S, lam ≠ α) ∧
      ∀ α ∈ S,
        C * ‖SourceStack.reciprocalTranslate lam α‖ ≤
          ‖SourceStack.reciprocalTranslate lam β‖ := by
  exact SourceStack.exists_reciprocal_translate_separating_finset S β C hC hβ

theorem hilbert_exists_rational_reciprocal_translate_separating_finset
    (S : Finset ℂ) (β : ℚ) (C : ℝ) (hC : 0 < C) (hβ : (β : ℂ) ∉ S) :
    ∃ lam : ℚ,
      (lam : ℂ) ≠ (β : ℂ) ∧
      (∀ α ∈ S, (lam : ℂ) ≠ α) ∧
      ∀ α ∈ S,
        C * ‖SourceStack.reciprocalTranslate (lam : ℂ) α‖ ≤
          ‖SourceStack.reciprocalTranslate (lam : ℂ) (β : ℂ)‖ := by
  exact SourceStack.exists_rational_reciprocal_translate_separating_finset S β C hC hβ

end ComplexSeparation

namespace AffineSpace

universe u v

variable (n : Type v)
variable {S T U X : Scheme.{max u v}}

theorem hilbert_homOfVector_over
    (f : X ⟶ S) (w : n → Γ(X, ⊤)) :
    AlgebraicGeometry.AffineSpace.homOfVector f w ≫ 𝔸(n; S) ↘ S = f := by
  exact SourceStack.AffineSpace.homOfVector_over n f w

theorem hilbert_homOfVector_appTop_coord
    (f : X ⟶ S) (w : n → Γ(X, ⊤)) (i : n) :
    (AlgebraicGeometry.AffineSpace.homOfVector f w).appTop
      (AlgebraicGeometry.AffineSpace.coord S i) = w i := by
  exact SourceStack.AffineSpace.homOfVector_appTop_coord n f w i

theorem hilbert_hom_ext
    {f g : X ⟶ 𝔸(n; S)}
    (h₁ : f ≫ 𝔸(n; S) ↘ S = g ≫ 𝔸(n; S) ↘ S)
    (h₂ : ∀ i,
      f.appTop (AlgebraicGeometry.AffineSpace.coord S i) =
        g.appTop (AlgebraicGeometry.AffineSpace.coord S i)) :
    f = g := by
  exact SourceStack.AffineSpace.hom_ext n h₁ h₂

theorem hilbert_homOverEquiv_exists
    [X.Over S] :
    Nonempty ({ f : X ⟶ 𝔸(n; S) // f.IsOver S } ≃ (n → Γ(X, ⊤))) := by
  exact SourceStack.AffineSpace.homOverEquiv_exists n

theorem hilbert_isoOfIsAffine_exists
    [IsAffine S] :
    Nonempty (𝔸(n; S) ≅ Spec (.of (MvPolynomial n Γ(S, ⊤)))) := by
  exact SourceStack.AffineSpace.isoOfIsAffine_exists n

theorem hilbert_affineSpace_isAffine_of_base
    [IsAffine S] :
    IsAffine 𝔸(n; S) := by
  exact SourceStack.AffineSpace.affineSpace_isAffine_of_base n

theorem hilbert_SpecIso_exists
    (R : CommRingCat.{max u v}) :
    Nonempty (𝔸(n; Spec R) ≅ Spec (.of (MvPolynomial n R))) := by
  exact SourceStack.AffineSpace.SpecIso_exists n R

theorem hilbert_map_over
    (f : S ⟶ T) :
    AlgebraicGeometry.AffineSpace.map n f ≫ 𝔸(n; T) ↘ T =
      𝔸(n; S) ↘ S ≫ f := by
  exact SourceStack.AffineSpace.map_over n f

theorem hilbert_map_appTop_coord
    (f : S ⟶ T) (i : n) :
    (AlgebraicGeometry.AffineSpace.map n f).appTop
      (AlgebraicGeometry.AffineSpace.coord T i) =
        AlgebraicGeometry.AffineSpace.coord S i := by
  exact SourceStack.AffineSpace.map_appTop_coord n f i

theorem hilbert_map_id :
    AlgebraicGeometry.AffineSpace.map n (𝟙 S) = 𝟙 𝔸(n; S) := by
  exact SourceStack.AffineSpace.map_id n

theorem hilbert_map_comp
    (f : S ⟶ T) (g : T ⟶ U) :
    AlgebraicGeometry.AffineSpace.map n (f ≫ g) =
      AlgebraicGeometry.AffineSpace.map n f ≫
        AlgebraicGeometry.AffineSpace.map n g := by
  exact SourceStack.AffineSpace.map_comp n f g

theorem hilbert_reindex_over
    {m : Type v} (i : m → n) :
    AlgebraicGeometry.AffineSpace.reindex i S ≫ 𝔸(m; S) ↘ S =
      𝔸(n; S) ↘ S := by
  exact SourceStack.AffineSpace.reindex_over n i

theorem hilbert_reindex_appTop_coord
    {m : Type v} (i : m → n) (j : m) :
    (AlgebraicGeometry.AffineSpace.reindex i S).appTop
      (AlgebraicGeometry.AffineSpace.coord S j) =
        AlgebraicGeometry.AffineSpace.coord S (i j) := by
  exact SourceStack.AffineSpace.reindex_appTop_coord n i j

theorem hilbert_reindex_id :
    AlgebraicGeometry.AffineSpace.reindex (@id n) S = 𝟙 𝔸(n; S) := by
  exact SourceStack.AffineSpace.reindex_id n

theorem hilbert_reindex_comp
    {n₁ n₂ n₃ : Type v} (i : n₁ → n₂) (j : n₂ → n₃)
    (S : Scheme.{max u v}) :
    AlgebraicGeometry.AffineSpace.reindex (j ∘ i) S =
      AlgebraicGeometry.AffineSpace.reindex j S ≫
        AlgebraicGeometry.AffineSpace.reindex i S := by
  exact SourceStack.AffineSpace.reindex_comp i j S

theorem hilbert_map_reindex
    {n₁ n₂ : Type v} (i : n₁ → n₂) (f : S ⟶ T) :
    AlgebraicGeometry.AffineSpace.map n₂ f ≫
        AlgebraicGeometry.AffineSpace.reindex i T =
      AlgebraicGeometry.AffineSpace.reindex i S ≫
        AlgebraicGeometry.AffineSpace.map n₁ f := by
  exact SourceStack.AffineSpace.map_reindex i f

end AffineSpace

section Topology

variable {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {s : Set X} {f : X → Y}

theorem hilbert_lorscheid_compact_image
    (hs : IsCompact s)
    (hf : Continuous f) :
    IsCompact (f '' s) := by
  exact SourceStack.lorscheid_compact_image hs hf

theorem hilbert_compact_elim_finite_subcover_indexed
    {b : Set ι} {c : ι → Set X}
    (hs : IsCompact s)
    (hcopen : ∀ i ∈ b, IsOpen (c i))
    (hcover : s ⊆ ⋃ i ∈ b, c i) :
    ∃ b' : Set ι, b' ⊆ b ∧ Set.Finite b' ∧ s ⊆ ⋃ i ∈ b', c i := by
  exact SourceStack.compact_elim_finite_subcover_indexed hs hcopen hcover

theorem hilbert_properMap_preimage_compact
    {K : Set Y} (hf : IsProperMap f) (hK : IsCompact K) :
    IsCompact (f ⁻¹' K) := by
  exact SourceStack.properMap_preimage_compact hf hK

theorem hilbert_properMap_isClosedMap
    (hf : IsProperMap f) :
    IsClosedMap f := by
  exact SourceStack.properMap_isClosedMap hf

theorem hilbert_properMap_comp
    {Z : Type*} [TopologicalSpace Z] {g : Y → Z}
    (hf : IsProperMap f) (hg : IsProperMap g) :
    IsProperMap (g ∘ f) := by
  exact SourceStack.properMap_comp hf hg

theorem hilbert_closedEmbedding_isProperMap
    (hf : Topology.IsClosedEmbedding f) :
    IsProperMap f := by
  exact SourceStack.closedEmbedding_isProperMap hf

theorem hilbert_continuous_isProperMap_of_compactSpace
    [CompactSpace X] [T2Space Y]
    (hf : Continuous f) :
    IsProperMap f := by
  exact SourceStack.continuous_isProperMap_of_compactSpace hf

end Topology

namespace LocalFields

theorem hilbert_padicInt_compactSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    CompactSpace ℤ_[p] := by
  exact SourceStack.LocalFields.padicInt_compactSpace p

theorem hilbert_padic_properSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    ProperSpace ℚ_[p] := by
  exact SourceStack.LocalFields.padic_properSpace p

theorem hilbert_padic_locallyCompactSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    LocallyCompactSpace ℚ_[p] := by
  exact SourceStack.LocalFields.padic_locallyCompactSpace p

theorem hilbert_padic_completeSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    CompleteSpace ℚ_[p] := by
  exact SourceStack.LocalFields.padic_completeSpace p

theorem hilbert_infinitePlace_completion_locallyCompactSpace
    {K : Type*} [Field K] (v : NumberField.InfinitePlace K) :
    LocallyCompactSpace v.Completion := by
  exact SourceStack.LocalFields.infinitePlace_completion_locallyCompactSpace v

end LocalFields

namespace ProjectiveLine

variable (K : Type*) [DivisionRing K]

theorem hilbert_zero_ne_infinity :
    SourceStack.ProjectiveLine.zero K ≠ SourceStack.ProjectiveLine.infinity K := by
  exact SourceStack.ProjectiveLine.zero_ne_infinity K

theorem hilbert_zero_ne_one :
    SourceStack.ProjectiveLine.zero K ≠ SourceStack.ProjectiveLine.one K := by
  exact SourceStack.ProjectiveLine.zero_ne_one K

theorem hilbert_one_ne_infinity :
    SourceStack.ProjectiveLine.one K ≠ SourceStack.ProjectiveLine.infinity K := by
  exact SourceStack.ProjectiveLine.one_ne_infinity K

theorem hilbert_affinePoint_zero :
    SourceStack.ProjectiveLine.affinePoint K 0 = SourceStack.ProjectiveLine.zero K := by
  exact SourceStack.ProjectiveLine.affinePoint_zero K

theorem hilbert_affinePoint_one :
    SourceStack.ProjectiveLine.affinePoint K 1 = SourceStack.ProjectiveLine.one K := by
  exact SourceStack.ProjectiveLine.affinePoint_one K

theorem hilbert_affinePoint_ne_infinity (r : K) :
    SourceStack.ProjectiveLine.affinePoint K r ≠
      SourceStack.ProjectiveLine.infinity K := by
  exact SourceStack.ProjectiveLine.affinePoint_ne_infinity K r

theorem hilbert_affinePoint_ne_zero {r : K} (hr : r ≠ 0) :
    SourceStack.ProjectiveLine.affinePoint K r ≠
      SourceStack.ProjectiveLine.zero K := by
  exact SourceStack.ProjectiveLine.affinePoint_ne_zero K hr

theorem hilbert_affinePoint_ne_one {r : K} (hr : r ≠ 1) :
    SourceStack.ProjectiveLine.affinePoint K r ≠
      SourceStack.ProjectiveLine.one K := by
  exact SourceStack.ProjectiveLine.affinePoint_ne_one K hr

theorem hilbert_zero_mem_branchFinset :
    SourceStack.ProjectiveLine.zero K ∈ SourceStack.ProjectiveLine.branchFinset K := by
  exact SourceStack.ProjectiveLine.zero_mem_branchFinset K

theorem hilbert_one_mem_branchFinset :
    SourceStack.ProjectiveLine.one K ∈ SourceStack.ProjectiveLine.branchFinset K := by
  exact SourceStack.ProjectiveLine.one_mem_branchFinset K

theorem hilbert_infinity_mem_branchFinset :
    SourceStack.ProjectiveLine.infinity K ∈ SourceStack.ProjectiveLine.branchFinset K := by
  exact SourceStack.ProjectiveLine.infinity_mem_branchFinset K

theorem hilbert_branchFinset_card :
    (SourceStack.ProjectiveLine.branchFinset K).card = 3 := by
  exact SourceStack.ProjectiveLine.branchFinset_card K

theorem hilbert_zero_mem_fourPointFinset (r : K) :
    SourceStack.ProjectiveLine.zero K ∈
      SourceStack.ProjectiveLine.fourPointFinset K r := by
  exact SourceStack.ProjectiveLine.zero_mem_fourPointFinset K r

theorem hilbert_affinePoint_mem_fourPointFinset (r : K) :
    SourceStack.ProjectiveLine.affinePoint K r ∈
      SourceStack.ProjectiveLine.fourPointFinset K r := by
  exact SourceStack.ProjectiveLine.affinePoint_mem_fourPointFinset K r

theorem hilbert_one_mem_fourPointFinset (r : K) :
    SourceStack.ProjectiveLine.one K ∈
      SourceStack.ProjectiveLine.fourPointFinset K r := by
  exact SourceStack.ProjectiveLine.one_mem_fourPointFinset K r

theorem hilbert_infinity_mem_fourPointFinset (r : K) :
    SourceStack.ProjectiveLine.infinity K ∈
      SourceStack.ProjectiveLine.fourPointFinset K r := by
  exact SourceStack.ProjectiveLine.infinity_mem_fourPointFinset K r

theorem hilbert_fourPointFinset_card {r : K} (hr0 : r ≠ 0) (hr1 : r ≠ 1) :
    (SourceStack.ProjectiveLine.fourPointFinset K r).card = 4 := by
  exact SourceStack.ProjectiveLine.fourPointFinset_card K hr0 hr1

theorem hilbert_image_fourPointFinset_card_lt_of_maps_to_branch
    [DecidableEq (SourceStack.ProjectiveLine.P1 K)]
    {r : K} (hr0 : r ≠ 0) (hr1 : r ≠ 1)
    (f : SourceStack.ProjectiveLine.P1 K → SourceStack.ProjectiveLine.P1 K)
    (hmap : ∀ x ∈ SourceStack.ProjectiveLine.fourPointFinset K r,
      f x ∈ SourceStack.ProjectiveLine.branchFinset K) :
    ((SourceStack.ProjectiveLine.fourPointFinset K r).image f).card <
      (SourceStack.ProjectiveLine.fourPointFinset K r).card := by
  exact SourceStack.ProjectiveLine.image_fourPointFinset_card_lt_of_maps_to_branch
    K hr0 hr1 f hmap

end ProjectiveLine

namespace ProjectiveSpectrum

universe u v

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

theorem hilbert_basicOpen_mem_iff
    (f : A) (x : Proj 𝒜) :
    x ∈ Proj.basicOpen 𝒜 f ↔ f ∉ x.asHomogeneousIdeal := by
  exact SourceStack.ProjectiveSpectrum.basicOpen_mem_iff 𝒜 f x

theorem hilbert_basicOpen_one_eq_top :
    Proj.basicOpen 𝒜 (1 : A) = ⊤ := by
  exact SourceStack.ProjectiveSpectrum.basicOpen_one_eq_top 𝒜

theorem hilbert_basicOpen_zero_eq_bot :
    Proj.basicOpen 𝒜 (0 : A) = ⊥ := by
  exact SourceStack.ProjectiveSpectrum.basicOpen_zero_eq_bot 𝒜

theorem hilbert_basicOpen_pow_eq
    (f : A) (n : ℕ) (hn : 0 < n) :
    Proj.basicOpen 𝒜 (f ^ n) = Proj.basicOpen 𝒜 f := by
  exact SourceStack.ProjectiveSpectrum.basicOpen_pow_eq 𝒜 f n hn

theorem hilbert_basicOpen_mul_eq_inf
    (f g : A) :
    Proj.basicOpen 𝒜 (f * g) =
      Proj.basicOpen 𝒜 f ⊓ Proj.basicOpen 𝒜 g := by
  exact SourceStack.ProjectiveSpectrum.basicOpen_mul_eq_inf 𝒜 f g

theorem hilbert_basicOpen_mono_of_dvd
    {f g : A} (hfg : f ∣ g) :
    Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f := by
  exact SourceStack.ProjectiveSpectrum.basicOpen_mono_of_dvd 𝒜 hfg

theorem hilbert_basicOpen_eq_iSup_proj
    (f : A) :
    Proj.basicOpen 𝒜 f =
      ⨆ i : ℕ, Proj.basicOpen 𝒜 (GradedAlgebra.proj 𝒜 i f) := by
  exact SourceStack.ProjectiveSpectrum.basicOpen_eq_iSup_proj 𝒜 f

theorem hilbert_isBasis_basicOpen :
    TopologicalSpace.Opens.IsBasis (Set.range (Proj.basicOpen 𝒜)) := by
  exact SourceStack.ProjectiveSpectrum.isBasis_basicOpen 𝒜

theorem hilbert_iSup_basicOpen_eq_top
    {ι : Type*} (f : ι → A)
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ Ideal.span (Set.range f)) :
    ⨆ i, Proj.basicOpen 𝒜 (f i) = ⊤ := by
  exact SourceStack.ProjectiveSpectrum.iSup_basicOpen_eq_top 𝒜 f hf

theorem hilbert_toSpecZero_isSeparated :
    IsSeparated (Proj.toSpecZero 𝒜) := by
  exact SourceStack.ProjectiveSpectrum.toSpecZero_isSeparated 𝒜

theorem hilbert_proj_scheme_isSeparated :
    (Proj 𝒜).IsSeparated := by
  exact SourceStack.ProjectiveSpectrum.proj_scheme_isSeparated 𝒜

theorem hilbert_awayι_isOpenImmersion
    (f : A) {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    IsOpenImmersion (Proj.awayι 𝒜 f f_deg hm) := by
  exact SourceStack.ProjectiveSpectrum.awayι_isOpenImmersion 𝒜 f f_deg hm

theorem hilbert_opensRange_awayι
    (f : A) {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    (Proj.awayι 𝒜 f f_deg hm).opensRange = Proj.basicOpen 𝒜 f := by
  exact SourceStack.ProjectiveSpectrum.opensRange_awayι 𝒜 f f_deg hm

theorem hilbert_isAffineOpen_basicOpen
    (f : A) {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    IsAffineOpen (Proj.basicOpen 𝒜 f) := by
  exact SourceStack.ProjectiveSpectrum.isAffineOpen_basicOpen 𝒜 f f_deg hm

theorem hilbert_stalkIso_exists
    (x : Proj 𝒜) :
    Nonempty ((Proj 𝒜).presheaf.stalk x ≅
      CommRingCat.of (AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal)) := by
  exact SourceStack.ProjectiveSpectrum.stalkIso_exists 𝒜 x

theorem hilbert_basicOpenIsoSpec_exists
    (f : A) {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    Nonempty ((Proj.basicOpen 𝒜 f).toScheme ≅ Spec (.of (Away 𝒜 f))) := by
  exact SourceStack.ProjectiveSpectrum.basicOpenIsoSpec_exists 𝒜 f f_deg hm

theorem hilbert_basicOpenIsoAway_exists
    (f : A) {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    Nonempty (CommRingCat.of (Away 𝒜 f) ≅ Γ(Proj 𝒜, Proj.basicOpen 𝒜 f)) := by
  exact SourceStack.ProjectiveSpectrum.basicOpenIsoAway_exists 𝒜 f f_deg hm

end ProjectiveSpectrum

namespace RationalMaps

universe u

variable {X Y : Scheme.{u}}

theorem hilbert_partialMap_toRationalMap_surjective :
    Function.Surjective (@Scheme.PartialMap.toRationalMap X Y) := by
  exact SourceStack.RationalMaps.partialMap_toRationalMap_surjective

theorem hilbert_rationalMap_exists_rep
    (f : X ⤏ Y) :
    ∃ g : X.PartialMap Y, g.toRationalMap = f := by
  exact SourceStack.RationalMaps.rationalMap_exists_rep f

theorem hilbert_partialMap_toRationalMap_eq_iff
    {f g : X.PartialMap Y} :
    f.toRationalMap = g.toRationalMap ↔ f.equiv g := by
  exact SourceStack.RationalMaps.partialMap_toRationalMap_eq_iff

theorem hilbert_partialMap_dense_domain
    (f : X.PartialMap Y) :
    Dense (f.domain : Set X) := by
  exact SourceStack.RationalMaps.partialMap_dense_domain f

theorem hilbert_rationalMap_dense_domain
    (f : X ⤏ Y) :
    Dense (f.domain : Set X) := by
  exact SourceStack.RationalMaps.rationalMap_dense_domain f

theorem hilbert_rationalMap_toRationalMap_toPartialMap
    [IsReduced X] [Y.IsSeparated] (f : X ⤏ Y) :
    f.toPartialMap.toRationalMap = f := by
  exact SourceStack.RationalMaps.rationalMap_toRationalMap_toPartialMap f

theorem hilbert_partialMap_fromFunctionField_restrict
    [IrreducibleSpace X] (f : X.PartialMap Y)
    {U : X.Opens} (hU : Dense (U : Set X)) (hU' : U ≤ f.domain) :
    (f.restrict U hU hU').fromFunctionField = f.fromFunctionField := by
  exact SourceStack.RationalMaps.partialMap_fromFunctionField_restrict f hU hU'

theorem hilbert_rationalMap_fromFunctionField_toRationalMap
    [IrreducibleSpace X] (f : X.PartialMap Y) :
    f.toRationalMap.fromFunctionField = f.fromFunctionField := by
  exact SourceStack.RationalMaps.rationalMap_fromFunctionField_toRationalMap f

theorem hilbert_rationalMap_eq_of_fromFunctionField_eq
    [IsIntegral X] (f g : X ⤏ Y)
    (H : f.fromFunctionField = g.fromFunctionField) :
    f = g := by
  exact SourceStack.RationalMaps.rationalMap_eq_of_fromFunctionField_eq f g H

theorem hilbert_rationalMap_fromFunctionField_ofFunctionField
    {S : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
    [IsIntegral X] [LocallyOfFiniteType sY]
    (f : Spec X.functionField ⟶ Y)
    (h : f ≫ sY = X.fromSpecStalk _ ≫ sX) :
    (Scheme.RationalMap.ofFunctionField sX sY f h).fromFunctionField = f := by
  exact SourceStack.RationalMaps.rationalMap_fromFunctionField_ofFunctionField sX sY f h

end RationalMaps

namespace FunctionFields

universe u

variable {X Y : Scheme.{u}}

theorem hilbert_germToFunctionField_injective
    [IsIntegral X] (U : X.Opens) [Nonempty U] :
    Function.Injective (X.germToFunctionField U) := by
  exact SourceStack.FunctionFields.germToFunctionField_injective U

theorem hilbert_functionField_isFractionRing_of_isAffineOpen
    [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    IsFractionRing Γ(X, U) X.functionField := by
  exact SourceStack.FunctionFields.functionField_isFractionRing_of_isAffineOpen U hU

theorem hilbert_genericPoint_eq_of_isOpenImmersion
    (f : X ⟶ Y) [IsOpenImmersion f]
    [IrreducibleSpace X] [IrreducibleSpace Y] :
    f.base (genericPoint X) = genericPoint Y := by
  exact SourceStack.FunctionFields.genericPoint_eq_of_isOpenImmersion f

end FunctionFields

namespace ResidueFields

universe u

variable {X Y Z : Scheme.{u}}

theorem hilbert_residueField_field_exists
    (x : X) :
    Nonempty (Field (X.residueField x)) := by
  exact SourceStack.ResidueFields.residueField_field_exists x

theorem hilbert_residue_surjective
    (X : Scheme.{u}) (x : X) :
    Function.Surjective (X.residue x) := by
  exact SourceStack.ResidueFields.residue_surjective X x

theorem hilbert_evaluation_eq_zero_iff_not_mem_basicOpen
    (U : X.Opens) (x : X) (hx : x ∈ U) (f : Γ(X, U)) :
    X.evaluation U x hx f = 0 ↔ x ∉ X.basicOpen f := by
  exact SourceStack.ResidueFields.evaluation_eq_zero_iff_not_mem_basicOpen U x hx f

theorem hilbert_evaluation_ne_zero_iff_mem_basicOpen
    (U : X.Opens) (x : X) (hx : x ∈ U) (f : Γ(X, U)) :
    X.evaluation U x hx f ≠ 0 ↔ x ∈ X.basicOpen f := by
  exact SourceStack.ResidueFields.evaluation_ne_zero_iff_mem_basicOpen U x hx f

theorem hilbert_residue_residueFieldMap
    (f : X ⟶ Y) (x : X) :
    Y.residue (f.base x) ≫ f.residueFieldMap x =
      f.stalkMap x ≫ X.residue x := by
  exact SourceStack.ResidueFields.residue_residueFieldMap f x

theorem hilbert_residueFieldMap_id
    (x : X) :
    Scheme.Hom.residueFieldMap (𝟙 X) x = 𝟙 (X.residueField x) := by
  exact SourceStack.ResidueFields.residueFieldMap_id x

theorem hilbert_residueFieldMap_comp
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g).residueFieldMap x =
      g.residueFieldMap (f.base x) ≫ f.residueFieldMap x := by
  exact SourceStack.ResidueFields.residueFieldMap_comp f g x

theorem hilbert_Γevaluation_naturality
    (f : X ⟶ Y) (x : X) :
    Y.Γevaluation (f.base x) ≫ f.residueFieldMap x =
      f.c.app (op ⊤) ≫ X.Γevaluation x := by
  exact SourceStack.ResidueFields.Γevaluation_naturality f x

theorem hilbert_Γevaluation_naturality_apply
    (f : X ⟶ Y) (x : X) (a : Y.presheaf.obj (op ⊤)) :
    f.residueFieldMap x (Y.Γevaluation (f.base x) a) =
      X.Γevaluation x (f.c.app (op ⊤) a) := by
  exact SourceStack.ResidueFields.Γevaluation_naturality_apply f x a

theorem hilbert_residueFieldMap_isIso_of_openImmersion
    (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    IsIso (f.residueFieldMap x) := by
  exact SourceStack.ResidueFields.residueFieldMap_isIso_of_openImmersion f x

theorem hilbert_fromSpecStalk_closedPoint
    (x : X) :
    (X.fromSpecStalk x).base (closedPoint (X.presheaf.stalk x)) = x := by
  exact SourceStack.ResidueFields.fromSpecStalk_closedPoint x

theorem hilbert_range_fromSpecStalk
    (x : X) :
    Set.range (X.fromSpecStalk x).base = { y | y ⤳ x } := by
  exact SourceStack.ResidueFields.range_fromSpecStalk x

theorem hilbert_Spec_map_stalkMap_fromSpecStalk
    (f : X ⟶ Y) (x : X) :
    Spec.map (f.stalkMap x) ≫ Y.fromSpecStalk _ =
      X.fromSpecStalk x ≫ f := by
  exact SourceStack.ResidueFields.Spec_map_stalkMap_fromSpecStalk f x

theorem hilbert_fromSpecResidueField_apply
    (x : X) (s : Spec (X.residueField x)) :
    (X.fromSpecResidueField x).base s = x := by
  exact SourceStack.ResidueFields.fromSpecResidueField_apply x s

theorem hilbert_range_fromSpecResidueField
    (x : X) :
    Set.range (X.fromSpecResidueField x).base = {x} := by
  exact SourceStack.ResidueFields.range_fromSpecResidueField x

theorem hilbert_Spec_map_residueFieldMap_fromSpecResidueField
    (f : X ⟶ Y) (x : X) :
    Spec.map (f.residueFieldMap x) ≫ Y.fromSpecResidueField _ =
      X.fromSpecResidueField x ≫ f := by
  exact SourceStack.ResidueFields.Spec_map_residueFieldMap_fromSpecResidueField f x

theorem hilbert_SpecToEquivOfField_exists
    (K : Type u) [Field K] (X : Scheme.{u}) :
    Nonempty ((Spec (.of K) ⟶ X) ≃ Σ x, X.residueField x ⟶ .of K) := by
  exact SourceStack.ResidueFields.SpecToEquivOfField_exists K X

theorem hilbert_SpecToEquivOfLocalRing_exists
    (R : CommRingCat.{u}) [IsLocalRing R] (X : Scheme.{u}) :
    Nonempty ((Spec R ⟶ X) ≃
      Σ x, { f : X.presheaf.stalk x ⟶ R // IsLocalHom f.hom }) := by
  exact SourceStack.ResidueFields.SpecToEquivOfLocalRing_exists R X

end ResidueFields

namespace FieldTheory

universe u v w

variable (F E : Type*) [Field F] [Field E] [Algebra F E]

theorem hilbert_primitive_element_exists
    [FiniteDimensional F E] [Algebra.IsSeparable F E] :
    ∃ α : E, F⟮α⟯ = ⊤ := by
  exact SourceStack.FieldTheory.primitive_element_exists F E

theorem hilbert_primitive_element_exists_of_finite_intermediateField
    [Finite (IntermediateField F E)] (K : IntermediateField F E) :
    ∃ α : E, F⟮α⟯ = K := by
  exact SourceStack.FieldTheory.primitive_element_exists_of_finite_intermediateField F E K

theorem hilbert_finiteDimensional_of_exists_primitive_element
    [Algebra.IsAlgebraic F E]
    (h : ∃ α : E, F⟮α⟯ = ⊤) :
    FiniteDimensional F E := by
  exact SourceStack.FieldTheory.finiteDimensional_of_exists_primitive_element F E h

theorem hilbert_finite_intermediateField_of_exists_primitive_element
    [Algebra.IsAlgebraic F E]
    (h : ∃ α : E, F⟮α⟯ = ⊤) :
    Finite (IntermediateField F E) := by
  exact SourceStack.FieldTheory.finite_intermediateField_of_exists_primitive_element F E h

theorem hilbert_exists_primitive_element_iff_finite_intermediateField :
    (Algebra.IsAlgebraic F E ∧ ∃ α : E, F⟮α⟯ = ⊤) ↔
      Finite (IntermediateField F E) := by
  exact SourceStack.FieldTheory.exists_primitive_element_iff_finite_intermediateField F E

theorem hilbert_adjoin_finiteDimensional {x : E} (hx : IsIntegral F x) :
    FiniteDimensional F F⟮x⟯ := by
  exact SourceStack.FieldTheory.adjoin_finiteDimensional F E hx

theorem hilbert_finiteDimensional_adjoin {S : Set E} [Finite S]
    (hS : ∀ x ∈ S, IsIntegral F x) :
    FiniteDimensional F (IntermediateField.adjoin F S) := by
  exact SourceStack.FieldTheory.finiteDimensional_adjoin F E hS

theorem hilbert_adjoin_finrank_eq_minpoly_natDegree {x : E} (hx : IsIntegral F x) :
    Module.finrank F F⟮x⟯ = (minpoly F x).natDegree := by
  exact SourceStack.FieldTheory.adjoin_finrank_eq_minpoly_natDegree F E hx

theorem hilbert_isSeparable_adjoin_simple_iff_isSeparable {x : E} :
    Algebra.IsSeparable F F⟮x⟯ ↔ IsSeparable F x := by
  exact SourceStack.FieldTheory.isSeparable_adjoin_simple_iff_isSeparable F E

theorem hilbert_isSeparable_adjoin_pair_of_isSeparable {x y : E}
    (hx : IsSeparable F x) (hy : IsSeparable F y) :
    Algebra.IsSeparable F F⟮x, y⟯ := by
  exact SourceStack.FieldTheory.isSeparable_adjoin_pair_of_isSeparable F E hx hy

theorem hilbert_isSeparable_adjoin_iff_isSeparable {S : Set E} :
    Algebra.IsSeparable F (IntermediateField.adjoin F S) ↔
      ∀ x ∈ S, IsSeparable F x := by
  exact SourceStack.FieldTheory.isSeparable_adjoin_iff_isSeparable F E

theorem hilbert_minpoly_natDegree_le
    (x : E) [FiniteDimensional F E] :
    (minpoly F x).natDegree ≤ Module.finrank F E := by
  exact SourceStack.FieldTheory.minpoly_natDegree_le F E x

theorem hilbert_minpoly_degree_dvd {x : E} (hx : IsIntegral F x) :
    (minpoly F x).natDegree ∣ Module.finrank F E := by
  exact SourceStack.FieldTheory.minpoly_degree_dvd F E hx

theorem hilbert_galois_iff :
    IsGalois F E ↔ Algebra.IsSeparable F E ∧ Normal F E := by
  exact SourceStack.FieldTheory.galois_iff F E

theorem hilbert_isGalois_integral [IsGalois F E] (x : E) :
    IsIntegral F x := by
  exact SourceStack.FieldTheory.isGalois_integral F E x

theorem hilbert_isGalois_separable [IsGalois F E] (x : E) :
    IsSeparable F x := by
  exact SourceStack.FieldTheory.isGalois_separable F E x

theorem hilbert_isGalois_splits [IsGalois F E] (x : E) :
    Polynomial.Splits (algebraMap F E) (minpoly F x) := by
  exact SourceStack.FieldTheory.isGalois_splits F E x

theorem hilbert_isGalois_card_aut_eq_finrank
    [FiniteDimensional F E] [IsGalois F E] :
    Fintype.card (E ≃ₐ[F] E) = Module.finrank F E := by
  exact SourceStack.FieldTheory.isGalois_card_aut_eq_finrank F E

theorem hilbert_normal_criterion :
    Normal F E ↔
      ∀ x : E, IsIntegral F x ∧ Polynomial.Splits (algebraMap F E) (minpoly F x) := by
  exact SourceStack.FieldTheory.normal_criterion F E

theorem hilbert_normal_isIntegral [Normal F E] (x : E) :
    IsIntegral F x := by
  exact SourceStack.FieldTheory.normal_isIntegral F E x

theorem hilbert_normal_splits [Normal F E] (x : E) :
    Polynomial.Splits (algebraMap F E) (minpoly F x) := by
  exact SourceStack.FieldTheory.normal_splits F E x

theorem hilbert_normal_exists_isSplittingField
    [Normal F E] [FiniteDimensional F E] :
    ∃ p : F[X], Polynomial.IsSplittingField F E p := by
  exact SourceStack.FieldTheory.normal_exists_isSplittingField F E

theorem hilbert_minpoly_exists_algEquiv_of_root
    [Normal F E] {x y : E} (hy : IsAlgebraic F y)
    (h_ev : (Polynomial.aeval x) (minpoly F y) = 0) :
    ∃ σ : E ≃ₐ[F] E, σ x = y := by
  exact SourceStack.FieldTheory.minpoly_exists_algEquiv_of_root F E hy h_ev

theorem hilbert_minpoly_exists_algEquiv_of_root'
    [Normal F E] {x y : E} (hy : IsAlgebraic F y)
    (h_ev : (Polynomial.aeval x) (minpoly F y) = 0) :
    ∃ σ : E ≃ₐ[F] E, σ y = x := by
  exact SourceStack.FieldTheory.minpoly_exists_algEquiv_of_root' F E hy h_ev

variable (K : Type*) [Field K] [Algebra F K] [Algebra K E]
variable [IsScalarTower F K E]

theorem hilbert_restrictNormalHom_surjective
    [Normal F K] [Normal F E] :
    Function.Surjective (AlgEquiv.restrictNormalHom K :
      (E ≃ₐ[F] E) → K ≃ₐ[F] K) := by
  exact SourceStack.FieldTheory.restrictNormalHom_surjective F E K

end FieldTheory

namespace UnramifiedEtale

universe u v w

theorem hilbert_formallyUnramified_iff_subsingleton_kaehlerDifferential
    (R : Type v) [CommRing R]
    (A : Type u) [CommRing A] [Algebra R A] :
    Algebra.FormallyUnramified R A ↔ Subsingleton (Ω[A⁄R]) := by
  exact SourceStack.UnramifiedEtale.formallyUnramified_iff_subsingleton_kaehlerDifferential R A

theorem hilbert_formallyUnramified_iff_comp_injective
    (R : Type v) [CommRing R]
    (A : Type u) [CommRing A] [Algebra R A] :
    Algebra.FormallyUnramified R A ↔
      ∀ ⦃B : Type u⦄ [CommRing B] [Algebra R B] (I : Ideal B),
        I ^ 2 = ⊥ →
          Function.Injective ((Ideal.Quotient.mkₐ R I).comp :
            (A →ₐ[R] B) → A →ₐ[R] B ⧸ I) := by
  exact SourceStack.UnramifiedEtale.formallyUnramified_iff_comp_injective R A

theorem hilbert_formallyUnramified_comp
    (R : Type u) [CommRing R]
    (A : Type v) [CommRing A] [Algebra R A]
    (B : Type w) [CommRing B] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B]
    [Algebra.FormallyUnramified R A] [Algebra.FormallyUnramified A B] :
    Algebra.FormallyUnramified R B := by
  exact SourceStack.UnramifiedEtale.formallyUnramified_comp R A B

theorem hilbert_formallyUnramified_of_comp
    (R : Type u) [CommRing R]
    (A : Type v) [CommRing A] [Algebra R A]
    (B : Type w) [CommRing B] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B]
    [Algebra.FormallyUnramified R B] :
    Algebra.FormallyUnramified A B := by
  exact SourceStack.UnramifiedEtale.formallyUnramified_of_comp R A B

theorem hilbert_formallyUnramified_base_change
    {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] [Algebra R A]
    (B : Type w) [CommRing B] [Algebra R B]
    [Algebra.FormallyUnramified R A] :
    Algebra.FormallyUnramified B (B ⊗[R] A) := by
  exact SourceStack.UnramifiedEtale.formallyUnramified_base_change B

theorem hilbert_formallyUnramified_iff_isSeparable
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [Algebra.EssFiniteType K L] :
    Algebra.FormallyUnramified K L ↔ Algebra.IsSeparable K L := by
  exact SourceStack.UnramifiedEtale.formallyUnramified_iff_isSeparable K L

theorem hilbert_formallyEtale_iff_unramified_and_smooth
    (R : Type u) [CommRing R]
    (A : Type u) [CommRing A] [Algebra R A] :
    Algebra.FormallyEtale R A ↔
      Algebra.FormallyUnramified R A ∧ Algebra.FormallySmooth R A := by
  exact SourceStack.UnramifiedEtale.formallyEtale_iff_unramified_and_smooth R A

theorem hilbert_formallyEtale_to_formallyUnramified
    (R : Type u) [CommRing R]
    (A : Type u) [CommRing A] [Algebra R A]
    [Algebra.FormallyEtale R A] :
    Algebra.FormallyUnramified R A := by
  exact SourceStack.UnramifiedEtale.formallyEtale_to_formallyUnramified R A

theorem hilbert_formallyEtale_comp
    (R : Type u) [CommRing R]
    (A B : Type u) [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra.FormallyEtale R A] [Algebra.FormallyEtale A B] :
    Algebra.FormallyEtale R B := by
  exact SourceStack.UnramifiedEtale.formallyEtale_comp R A B

theorem hilbert_formallyEtale_base_change
    {R : Type u} [CommRing R]
    {A : Type u} [CommRing A] [Algebra R A]
    (B : Type u) [CommRing B] [Algebra R B]
    [Algebra.FormallyEtale R A] :
    Algebra.FormallyEtale B (B ⊗[R] A) := by
  exact SourceStack.UnramifiedEtale.formallyEtale_base_change B

theorem hilbert_formallyEtale_iff_isSeparable
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [Algebra.EssFiniteType K L] :
    Algebra.FormallyEtale K L ↔ Algebra.IsSeparable K L := by
  exact SourceStack.UnramifiedEtale.formallyEtale_iff_isSeparable K L

theorem hilbert_etale_comp
    (R : Type u) [CommRing R]
    (A B : Type u) [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra.Etale R A] [Algebra.Etale A B] :
    Algebra.Etale R B := by
  exact SourceStack.UnramifiedEtale.etale_comp R A B

theorem hilbert_etale_base_change
    (R : Type u) [CommRing R]
    (A B : Type u) [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B]
    [Algebra.Etale R A] :
    Algebra.Etale B (B ⊗[R] A) := by
  exact SourceStack.UnramifiedEtale.etale_base_change R A B

end UnramifiedEtale

namespace Ramification

universe u v w x

theorem hilbert_algebraUnramified_formallyUnramified
    (R : Type u) [CommRing R]
    (A : Type v) [CommRing A] [Algebra R A]
    [Algebra.Unramified R A] :
    Algebra.FormallyUnramified R A := by
  exact SourceStack.Ramification.algebraUnramified_formallyUnramified R A

theorem hilbert_algebraUnramified_finiteType
    (R : Type u) [CommRing R]
    (A : Type v) [CommRing A] [Algebra R A]
    [Algebra.Unramified R A] :
    Algebra.FiniteType R A := by
  exact SourceStack.Ramification.algebraUnramified_finiteType R A

theorem hilbert_algebraUnramified_of_equiv
    {R : Type u} [CommRing R]
    {A : Type v} {B : Type w}
    [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B]
    [Algebra.Unramified R A]
    (e : A ≃ₐ[R] B) :
    Algebra.Unramified R B := by
  exact SourceStack.Ramification.algebraUnramified_of_equiv e

theorem hilbert_algebraUnramified_of_isLocalization_Away
    {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] [Algebra R A]
    (r : R) [IsLocalization.Away r A] :
    Algebra.Unramified R A := by
  exact SourceStack.Ramification.algebraUnramified_of_isLocalization_Away r

theorem hilbert_algebraUnramified_comp
    (R : Type u) [CommRing R]
    (A : Type v) [CommRing A] [Algebra R A]
    (B : Type w) [CommRing B] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B]
    [Algebra.Unramified R A] [Algebra.Unramified A B] :
    Algebra.Unramified R B := by
  exact SourceStack.Ramification.algebraUnramified_comp R A B

theorem hilbert_algebraUnramified_baseChange
    (R : Type u) [CommRing R]
    (A : Type v) [CommRing A] [Algebra R A]
    (B : Type w) [CommRing B] [Algebra R B]
    [Algebra.Unramified R A] :
    Algebra.Unramified B (B ⊗[R] A) := by
  exact SourceStack.Ramification.algebraUnramified_baseChange R A B

theorem hilbert_formallyUnramified_of_field_isSeparable
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [Algebra.IsSeparable K L] :
    Algebra.FormallyUnramified K L := by
  exact SourceStack.Ramification.formallyUnramified_of_field_isSeparable K L

theorem hilbert_formallyUnramified_isSeparable_of_field
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [Algebra.FormallyUnramified K L] [Algebra.EssFiniteType K L] :
    Algebra.IsSeparable K L := by
  exact SourceStack.Ramification.formallyUnramified_isSeparable_of_field K L

theorem hilbert_formallyUnramified_iff_field_isSeparable
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [Algebra.EssFiniteType K L] :
    Algebra.FormallyUnramified K L ↔ Algebra.IsSeparable K L := by
  exact SourceStack.Ramification.formallyUnramified_iff_field_isSeparable K L

theorem hilbert_formallyUnramified_localization_base
    {R : Type u} {Rₘ : Type v} {Sₘ : Type w}
    [CommRing R] [CommRing Rₘ] [CommRing Sₘ]
    (M : Submonoid R)
    [Algebra R Sₘ] [Algebra R Rₘ] [Algebra Rₘ Sₘ]
    [IsScalarTower R Rₘ Sₘ]
    [Algebra.FormallyUnramified R Sₘ] :
    Algebra.FormallyUnramified Rₘ Sₘ := by
  exact SourceStack.Ramification.formallyUnramified_localization_base M

theorem hilbert_formallyUnramified_localization_map
    {R : Type u} {S : Type v} {Rₘ : Type w} {Sₘ : Type x}
    [CommRing R] [CommRing S] [CommRing Rₘ] [CommRing Sₘ]
    (M : Submonoid R)
    [Algebra R S] [Algebra R Sₘ] [Algebra S Sₘ]
    [Algebra R Rₘ] [Algebra Rₘ Sₘ]
    [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]
    [IsLocalization (Submonoid.map (algebraMap R S) M) Sₘ]
    [Algebra.FormallyUnramified R S] :
    Algebra.FormallyUnramified Rₘ Sₘ := by
  exact SourceStack.Ramification.formallyUnramified_localization_map
    (R := R) (S := S) (Rₘ := Rₘ) (Sₘ := Sₘ) M

theorem hilbert_formallyUnramified_iff_exists_tensorProduct
    (R : Type u) [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] :
    Algebra.FormallyUnramified R S ↔
      ∃ t : S ⊗[R] S,
        (∀ s, ((1 : S) ⊗ₜ[R] s - s ⊗ₜ[R] (1 : S)) * t = 0) ∧
          Algebra.TensorProduct.lmul' R t = 1 := by
  exact SourceStack.Ramification.formallyUnramified_iff_exists_tensorProduct R S

theorem hilbert_formallyUnramified_pi_iff
    {R : Type (max u v)} {I : Type v} [Finite I]
    (A : I → Type (max u v))
    [CommRing R] [(i : I) → CommRing (A i)]
    [(i : I) → Algebra R (A i)] :
    Algebra.FormallyUnramified R ((i : I) → A i) ↔
      ∀ i, Algebra.FormallyUnramified R (A i) := by
  exact SourceStack.Ramification.formallyUnramified_pi_iff A

theorem hilbert_ramificationIdx_spec
    {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    {f : R →+* S} {p : Ideal R} {P : Ideal S} {n : ℕ}
    (hle : Ideal.map f p ≤ P ^ n)
    (hgt : ¬ Ideal.map f p ≤ P ^ (n + 1)) :
    Ideal.ramificationIdx f p P = n := by
  exact SourceStack.Ramification.ramificationIdx_spec hle hgt

theorem hilbert_ramificationIdx_bot
    {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    {f : R →+* S} {P : Ideal S} :
    Ideal.ramificationIdx f (⊥ : Ideal R) P = 0 := by
  exact SourceStack.Ramification.ramificationIdx_bot

theorem hilbert_ramificationIdx_of_not_le
    {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    {f : R →+* S} {p : Ideal R} {P : Ideal S}
    (h : ¬ Ideal.map f p ≤ P) :
    Ideal.ramificationIdx f p P = 0 := by
  exact SourceStack.Ramification.ramificationIdx_of_not_le h

theorem hilbert_le_pow_ramificationIdx
    {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    {f : R →+* S} {p : Ideal R} {P : Ideal S} :
    Ideal.map f p ≤ P ^ Ideal.ramificationIdx f p P := by
  exact SourceStack.Ramification.le_pow_ramificationIdx

theorem hilbert_le_comap_pow_ramificationIdx
    {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    {f : R →+* S} {p : Ideal R} {P : Ideal S} :
    p ≤ Ideal.comap f (P ^ Ideal.ramificationIdx f p P) := by
  exact SourceStack.Ramification.le_comap_pow_ramificationIdx

theorem hilbert_le_comap_of_ramificationIdx_ne_zero
    {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    {f : R →+* S} {p : Ideal R} {P : Ideal S}
    (h : Ideal.ramificationIdx f p P ≠ 0) :
    p ≤ Ideal.comap f P := by
  exact SourceStack.Ramification.le_comap_of_ramificationIdx_ne_zero h

theorem hilbert_ramificationIdx_eq_normalizedFactors_count
    {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    {f : R →+* S} {p : Ideal R} {P : Ideal S}
    [IsDedekindDomain S] [DecidableEq (Ideal S)]
    (hp0 : Ideal.map f p ≠ ⊥)
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    Ideal.ramificationIdx f p P =
      Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (Ideal.map f p)) := by
  exact SourceStack.Ramification.ramificationIdx_eq_normalizedFactors_count hp0 hP hP0

theorem hilbert_ramificationIdx_ne_zero_of_dedekind
    {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    {f : R →+* S} {p : Ideal R} {P : Ideal S}
    [IsDedekindDomain S]
    (hp0 : Ideal.map f p ≠ ⊥)
    (hP : P.IsPrime)
    (hle : Ideal.map f p ≤ P) :
    Ideal.ramificationIdx f p P ≠ 0 := by
  exact SourceStack.Ramification.ramificationIdx_ne_zero_of_dedekind hp0 hP hle

theorem hilbert_inertiaDeg_algebraMap
    {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    (p : Ideal R) (P : Ideal S)
    [Algebra R S] [P.LiesOver p] [p.IsMaximal] :
    Ideal.inertiaDeg p P = Module.finrank (R ⧸ p) (S ⧸ P) := by
  exact SourceStack.Ramification.inertiaDeg_algebraMap p P

theorem hilbert_inertiaDeg_pos
    {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    (p : Ideal R) (P : Ideal S)
    [Algebra R S] [p.IsMaximal] [Module.Finite R S] [P.LiesOver p] :
    0 < Ideal.inertiaDeg p P := by
  exact SourceStack.Ramification.inertiaDeg_pos p P

theorem hilbert_ramificationIdx_tower
    {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    {T : Type w} [CommRing T]
    [IsDedekindDomain S] [IsDedekindDomain T]
    {f : R →+* S} {g : S →+* T}
    {p : Ideal R} {P : Ideal S} {Q : Ideal T}
    [P.IsPrime] [Q.IsPrime]
    (hg0 : Ideal.map g P ≠ ⊥)
    (hfg : Ideal.map (g.comp f) p ≠ ⊥)
    (hg : Ideal.map g P ≤ Q) :
    Ideal.ramificationIdx (g.comp f) p Q =
      Ideal.ramificationIdx f p P * Ideal.ramificationIdx g P Q := by
  exact SourceStack.Ramification.ramificationIdx_tower hg0 hfg hg

theorem hilbert_ramificationIdx_algebra_tower
    {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    {T : Type w} [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsDedekindDomain S] [IsDedekindDomain T]
    {p : Ideal R} {P : Ideal S} {Q : Ideal T}
    [P.IsPrime] [Q.IsPrime]
    (hg0 : Ideal.map (algebraMap S T) P ≠ ⊥)
    (hfg : Ideal.map (algebraMap R T) p ≠ ⊥)
    (hg : Ideal.map (algebraMap S T) P ≤ Q) :
    Ideal.ramificationIdx (algebraMap R T) p Q =
      Ideal.ramificationIdx (algebraMap R S) p P *
        Ideal.ramificationIdx (algebraMap S T) P Q := by
  exact SourceStack.Ramification.ramificationIdx_algebra_tower hg0 hfg hg

theorem hilbert_inertiaDeg_algebra_tower
    {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    {T : Type w} [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (p : Ideal R) (P : Ideal S) (I : Ideal T)
    [p.IsMaximal] [P.IsMaximal] [P.LiesOver p] [I.LiesOver P] :
    Ideal.inertiaDeg p I = Ideal.inertiaDeg p P * Ideal.inertiaDeg P I := by
  exact SourceStack.Ramification.inertiaDeg_algebra_tower p P I

theorem hilbert_sum_ramification_inertia
    (R : Type u) [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S]
    (p : Ideal R)
    (K : Type w) [Field K]
    (L : Type x) [Field L]
    [IsDedekindDomain R] [IsDedekindDomain S]
    [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L]
    [Algebra K L] [Algebra R L]
    [IsScalarTower R S L] [IsScalarTower R K L]
    [Module.Finite R S] [p.IsMaximal]
    (hp0 : p ≠ ⊥) :
    (∑ P ∈ @Multiset.toFinset (Ideal S) (Classical.decEq (Ideal S))
        (UniqueFactorizationMonoid.factors (Ideal.map (algebraMap R S) p)),
        Ideal.ramificationIdx (algebraMap R S) p P * Ideal.inertiaDeg p P) =
      Module.finrank K L := by
  exact SourceStack.Ramification.sum_ramification_inertia R S p K L hp0

theorem hilbert_decompositionSubgroup_eq_stabilizer
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) :
    ValuationSubring.decompositionSubgroup K A =
      MulAction.stabilizer (L ≃ₐ[K] L) A := by
  exact SourceStack.Ramification.decompositionSubgroup_eq_stabilizer K A

theorem hilbert_inertiaSubgroup_eq_ker
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) :
    ValuationSubring.inertiaSubgroup K A =
      MonoidHom.ker
        (MulSemiringAction.toRingAut
          (ValuationSubring.decompositionSubgroup K A)
          (IsLocalRing.ResidueField A)) := by
  exact SourceStack.Ramification.inertiaSubgroup_eq_ker K A

end Ramification

namespace DedekindDvr

universe u v

theorem hilbert_prime_isMaximal_of_dimensionLEOne
    {R : Type u} [CommRing R] [Ring.DimensionLEOne R]
    {p : Ideal R} (hp : p.IsPrime) (hne : p ≠ ⊥) :
    p.IsMaximal := by
  exact SourceStack.DedekindDvr.prime_isMaximal_of_dimensionLEOne hp hne

theorem hilbert_eq_bot_of_prime_lt_prime
    {R : Type u} [CommRing R] [Ring.DimensionLEOne R]
    (p P : Ideal R) [p.IsPrime] [P.IsPrime]
    (hlt : p < P) :
    p = ⊥ := by
  exact SourceStack.DedekindDvr.eq_bot_of_prime_lt_prime p P hlt

theorem hilbert_not_prime_chain_length_two
    {R : Type u} [CommRing R] [Ring.DimensionLEOne R]
    (p₀ p₁ p₂ : Ideal R) [p₁.IsPrime] [p₂.IsPrime] :
    ¬ (p₀ < p₁ ∧ p₁ < p₂) := by
  exact SourceStack.DedekindDvr.not_prime_chain_length_two p₀ p₁ p₂

theorem hilbert_principalIdealRing_dimensionLEOne
    (A : Type u) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] :
    Ring.DimensionLEOne A := by
  exact SourceStack.DedekindDvr.principalIdealRing_dimensionLEOne A

theorem hilbert_isDedekindDomain_iff_fractionField
    (A : Type u) [CommRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K] :
    IsDedekindDomain A ↔
      IsDomain A ∧ IsNoetherianRing A ∧ Ring.DimensionLEOne A ∧
        ∀ {x : K}, IsIntegral A x → ∃ y, (algebraMap A K) y = x := by
  exact SourceStack.DedekindDvr.isDedekindDomain_iff_fractionField A K

theorem hilbert_localization_isDedekindDomain
    (A : Type u) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    {M : Submonoid A} (hM : M ≤ nonZeroDivisors A)
    (Aₘ : Type v) [CommRing Aₘ] [IsDomain Aₘ] [Algebra A Aₘ]
    [IsLocalization M Aₘ] :
    IsDedekindDomain Aₘ := by
  exact SourceStack.DedekindDvr.localization_isDedekindDomain A hM Aₘ

theorem hilbert_localization_atPrime_isDedekindDomain
    (A : Type u) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (P : Ideal A) [P.IsPrime]
    (Aₘ : Type v) [CommRing Aₘ] [IsDomain Aₘ] [Algebra A Aₘ]
    [IsLocalization.AtPrime Aₘ P] :
    IsDedekindDomain Aₘ := by
  exact SourceStack.DedekindDvr.localization_atPrime_isDedekindDomain A P Aₘ

theorem hilbert_localization_atPrime_not_isField
    (A : Type u) [CommRing A] [IsDomain A]
    {P : Ideal A} (hP : P ≠ ⊥) [P.IsPrime]
    (Aₘ : Type v) [CommRing Aₘ] [Algebra A Aₘ]
    [IsLocalization.AtPrime Aₘ P] :
    ¬ IsField Aₘ := by
  exact SourceStack.DedekindDvr.localization_atPrime_not_isField A hP Aₘ

theorem hilbert_localization_atPrime_isDVR_of_dedekind
    (A : Type u) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    {P : Ideal A} (hP : P ≠ ⊥) [P.IsPrime]
    (Aₘ : Type v) [CommRing Aₘ] [IsDomain Aₘ] [Algebra A Aₘ]
    [IsLocalization.AtPrime Aₘ P] :
    IsDiscreteValuationRing Aₘ := by
  exact SourceStack.DedekindDvr.localization_atPrime_isDVR_of_dedekind A hP Aₘ

theorem hilbert_dedekindDomain_to_dedekindDomainDvr
    (A : Type u) [CommRing A] [IsDomain A] [IsDedekindDomain A] :
    IsDedekindDomainDvr A := by
  exact SourceStack.DedekindDvr.dedekindDomain_to_dedekindDomainDvr A

theorem hilbert_dedekindDomainDvr_isIntegrallyClosed
    (A : Type u) [CommRing A] [IsDomain A] [IsDedekindDomainDvr A] :
    IsIntegrallyClosed A := by
  exact SourceStack.DedekindDvr.dedekindDomainDvr_isIntegrallyClosed A

theorem hilbert_dedekindDomainDvr_to_dedekindDomain
    (A : Type u) [CommRing A] [IsDomain A] [IsDedekindDomainDvr A] :
    IsDedekindDomain A := by
  exact SourceStack.DedekindDvr.dedekindDomainDvr_to_dedekindDomain A

theorem hilbert_dvr_not_isField
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    ¬ IsField R := by
  exact SourceStack.DedekindDvr.dvr_not_isField R

theorem hilbert_irreducible_iff_uniformizer
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) :
    Irreducible ϖ ↔ IsLocalRing.maximalIdeal R = Ideal.span {ϖ} := by
  exact SourceStack.DedekindDvr.irreducible_iff_uniformizer ϖ

theorem hilbert_irreducible_maximalIdeal_eq
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ) :
    IsLocalRing.maximalIdeal R = Ideal.span {ϖ} := by
  exact SourceStack.DedekindDvr.irreducible_maximalIdeal_eq hϖ

theorem hilbert_exists_irreducible
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    ∃ ϖ : R, Irreducible ϖ := by
  exact SourceStack.DedekindDvr.exists_irreducible R

theorem hilbert_exists_prime
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    ∃ ϖ : R, Prime ϖ := by
  exact SourceStack.DedekindDvr.exists_prime R

theorem hilbert_dvr_iff_pid_with_one_nonzero_prime
    (R : Type u) [CommRing R] [IsDomain R] :
    IsDiscreteValuationRing R ↔
      IsPrincipalIdealRing R ∧ ∃! P : Ideal R, P ≠ ⊥ ∧ P.IsPrime := by
  exact SourceStack.DedekindDvr.dvr_iff_pid_with_one_nonzero_prime R

theorem hilbert_associated_of_irreducible
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {a b : R} (ha : Irreducible a) (hb : Irreducible b) :
    Associated a b := by
  exact SourceStack.DedekindDvr.associated_of_irreducible R ha hb

theorem hilbert_associated_pow_irreducible
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {x : R} (hx : x ≠ 0) {ϖ : R} (hϖ : Irreducible ϖ) :
    ∃ n : ℕ, Associated x (ϖ ^ n) := by
  exact SourceStack.DedekindDvr.associated_pow_irreducible hx hϖ

theorem hilbert_eq_unit_mul_pow_irreducible
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {x : R} (hx : x ≠ 0) {ϖ : R} (hϖ : Irreducible ϖ) :
    ∃ n : ℕ, ∃ u : Rˣ, x = (u : R) * ϖ ^ n := by
  exact SourceStack.DedekindDvr.eq_unit_mul_pow_irreducible hx hϖ

theorem hilbert_ideal_eq_span_pow_irreducible
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {I : Ideal R} (hI : I ≠ ⊥) {ϖ : R} (hϖ : Irreducible ϖ) :
    ∃ n : ℕ, I = Ideal.span {ϖ ^ n} := by
  exact SourceStack.DedekindDvr.ideal_eq_span_pow_irreducible hI hϖ

theorem hilbert_addVal_zero
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    IsDiscreteValuationRing.addVal R 0 = ⊤ := by
  exact SourceStack.DedekindDvr.addVal_zero

theorem hilbert_addVal_one
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    IsDiscreteValuationRing.addVal R 1 = 0 := by
  exact SourceStack.DedekindDvr.addVal_one

theorem hilbert_addVal_uniformizer
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ) :
    IsDiscreteValuationRing.addVal R ϖ = 1 := by
  exact SourceStack.DedekindDvr.addVal_uniformizer hϖ

theorem hilbert_addVal_mul
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {a b : R} :
    IsDiscreteValuationRing.addVal R (a * b) =
      IsDiscreteValuationRing.addVal R a + IsDiscreteValuationRing.addVal R b := by
  exact SourceStack.DedekindDvr.addVal_mul

theorem hilbert_addVal_pow
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (a : R) (n : ℕ) :
    IsDiscreteValuationRing.addVal R (a ^ n) =
      n • IsDiscreteValuationRing.addVal R a := by
  exact SourceStack.DedekindDvr.addVal_pow a n

theorem hilbert_addVal_eq_top_iff
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {a : R} :
    IsDiscreteValuationRing.addVal R a = ⊤ ↔ a = 0 := by
  exact SourceStack.DedekindDvr.addVal_eq_top_iff

theorem hilbert_addVal_le_iff_dvd
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {a b : R} :
    IsDiscreteValuationRing.addVal R a ≤ IsDiscreteValuationRing.addVal R b ↔ a ∣ b := by
  exact SourceStack.DedekindDvr.addVal_le_iff_dvd

theorem hilbert_addVal_add
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {a b : R} :
    IsDiscreteValuationRing.addVal R a ⊓ IsDiscreteValuationRing.addVal R b ≤
      IsDiscreteValuationRing.addVal R (a + b) := by
  exact SourceStack.DedekindDvr.addVal_add

end DedekindDvr

namespace FractionalIdeals

universe u v w x

theorem hilbert_coeIdeal_le_coeIdeal
    {R : Type u} [CommRing R]
    (K : Type v) [CommRing K] [Algebra R K] [IsFractionRing R K]
    {I J : Ideal R} :
    (I : FractionalIdeal R⁰ K) ≤ (J : FractionalIdeal R⁰ K) ↔ I ≤ J := by
  exact SourceStack.FractionalIdeals.coeIdeal_le_coeIdeal K

theorem hilbert_coeIdeal_injective
    {R : Type u} [CommRing R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K] :
    Function.Injective (fun I : Ideal R => (I : FractionalIdeal R⁰ K)) := by
  exact SourceStack.FractionalIdeals.coeIdeal_injective

theorem hilbert_coeIdeal_eq_zero
    {R : Type u} [CommRing R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    {I : Ideal R} :
    (I : FractionalIdeal R⁰ K) = 0 ↔ I = ⊥ := by
  exact SourceStack.FractionalIdeals.coeIdeal_eq_zero

theorem hilbert_coeIdeal_eq_one
    {R : Type u} [CommRing R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    {I : Ideal R} :
    (I : FractionalIdeal R⁰ K) = 1 ↔ I = 1 := by
  exact SourceStack.FractionalIdeals.coeIdeal_eq_one

theorem hilbert_coeIdeal_mul
    {R : Type u} [CommRing R]
    {S : Submonoid R} {P : Type v} [CommRing P] [Algebra R P]
    (I J : Ideal R) :
    ((I * J : Ideal R) : FractionalIdeal S P) =
      (I : FractionalIdeal S P) * (J : FractionalIdeal S P) := by
  exact SourceStack.FractionalIdeals.coeIdeal_mul I J

theorem hilbert_coeIdeal_pow
    {R : Type u} [CommRing R]
    (S : Submonoid R) (P : Type v) [CommRing P] [Algebra R P]
    (I : Ideal R) (n : ℕ) :
    ((I ^ n : Ideal R) : FractionalIdeal S P) =
      (I : FractionalIdeal S P) ^ n := by
  exact SourceStack.FractionalIdeals.coeIdeal_pow S P I n

theorem hilbert_map_comp
    {R : Type u} [CommRing R]
    {S : Submonoid R}
    {P : Type v} [CommRing P] [Algebra R P]
    {P' : Type w} [CommRing P'] [Algebra R P']
    {P'' : Type x} [CommRing P''] [Algebra R P'']
    (I : FractionalIdeal S P) (g : P →ₐ[R] P') (g' : P' →ₐ[R] P'') :
    FractionalIdeal.map (g'.comp g) I =
      FractionalIdeal.map g' (FractionalIdeal.map g I) := by
  exact SourceStack.FractionalIdeals.map_comp I g g'

theorem hilbert_map_add
    {R : Type u} [CommRing R]
    {S : Submonoid R}
    {P : Type v} [CommRing P] [Algebra R P]
    {P' : Type w} [CommRing P'] [Algebra R P']
    (I J : FractionalIdeal S P) (g : P →ₐ[R] P') :
    FractionalIdeal.map g (I + J) =
      FractionalIdeal.map g I + FractionalIdeal.map g J := by
  exact SourceStack.FractionalIdeals.map_add I J g

theorem hilbert_map_mul
    {R : Type u} [CommRing R]
    {S : Submonoid R}
    {P : Type v} [CommRing P] [Algebra R P]
    {P' : Type w} [CommRing P'] [Algebra R P']
    (I J : FractionalIdeal S P) (g : P →ₐ[R] P') :
    FractionalIdeal.map g (I * J) =
      FractionalIdeal.map g I * FractionalIdeal.map g J := by
  exact SourceStack.FractionalIdeals.map_mul I J g

theorem hilbert_map_injective
    {R : Type u} [CommRing R]
    {S : Submonoid R}
    {P : Type v} [CommRing P] [Algebra R P]
    {P' : Type w} [CommRing P'] [Algebra R P']
    (g : P →ₐ[R] P') (hg : Function.Injective g) :
    Function.Injective (FractionalIdeal.map (S := S) g) := by
  exact SourceStack.FractionalIdeals.map_injective g hg

theorem hilbert_mem_spanSingleton
    {R : Type u} [CommRing R]
    {S : Submonoid R}
    {P : Type v} [CommRing P] [Algebra R P] [IsLocalization S P]
    {x y : P} :
    x ∈ FractionalIdeal.spanSingleton S y ↔ ∃ z : R, z • y = x := by
  exact SourceStack.FractionalIdeals.mem_spanSingleton

theorem hilbert_spanSingleton_mul_spanSingleton
    {R : Type u} [CommRing R]
    {S : Submonoid R}
    {P : Type v} [CommRing P] [Algebra R P] [IsLocalization S P]
    (x y : P) :
    FractionalIdeal.spanSingleton S x * FractionalIdeal.spanSingleton S y =
      FractionalIdeal.spanSingleton S (x * y) := by
  exact SourceStack.FractionalIdeals.spanSingleton_mul_spanSingleton x y

theorem hilbert_spanSingleton_pow
    {R : Type u} [CommRing R]
    {S : Submonoid R}
    {P : Type v} [CommRing P] [Algebra R P] [IsLocalization S P]
    (x : P) (n : ℕ) :
    FractionalIdeal.spanSingleton S x ^ n =
      FractionalIdeal.spanSingleton S (x ^ n) := by
  exact SourceStack.FractionalIdeals.spanSingleton_pow x n

theorem hilbert_coeIdeal_span_singleton
    {R : Type u} [CommRing R]
    {S : Submonoid R}
    {P : Type v} [CommRing P] [Algebra R P] [IsLocalization S P]
    (x : R) :
    ((Ideal.span {x} : Ideal R) : FractionalIdeal S P) =
      FractionalIdeal.spanSingleton S ((algebraMap R P) x) := by
  exact SourceStack.FractionalIdeals.coeIdeal_span_singleton x

theorem hilbert_isPrincipal_iff
    {R : Type u} [CommRing R]
    {S : Submonoid R}
    {P : Type v} [CommRing P] [Algebra R P] [IsLocalization S P]
    (I : FractionalIdeal S P) :
    (I : Submodule R P).IsPrincipal ↔
      ∃ x : P, I = FractionalIdeal.spanSingleton S x := by
  exact SourceStack.FractionalIdeals.isPrincipal_iff I

theorem hilbert_exists_eq_spanSingleton_mul
    {R : Type u} [CommRing R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K] [IsDomain R]
    (I : FractionalIdeal R⁰ K) :
    ∃ a : R, ∃ aI : Ideal R, a ≠ 0 ∧
      I = FractionalIdeal.spanSingleton R⁰ ((algebraMap R K) a)⁻¹ *
        (aI : FractionalIdeal R⁰ K) := by
  exact SourceStack.FractionalIdeals.exists_eq_spanSingleton_mul I

theorem hilbert_div_spanSingleton
    {R : Type u} [CommRing R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K] [IsDomain R]
    (J : FractionalIdeal R⁰ K) (d : K) :
    J / FractionalIdeal.spanSingleton R⁰ d =
      FractionalIdeal.spanSingleton R⁰ d⁻¹ * J := by
  exact SourceStack.FractionalIdeals.div_spanSingleton J d

theorem hilbert_extended_add
    {A : Type u} [CommRing A]
    {B : Type v} [CommRing B]
    {f : A →+* B}
    {K : Type w} {M : Submonoid A} [CommRing K] [Algebra A K] [IsLocalization M K]
    (L : Type x) {N : Submonoid B} [CommRing L] [Algebra B L] [IsLocalization N L]
    (hf : M ≤ Submonoid.comap f N)
    (I J : FractionalIdeal M K) :
    FractionalIdeal.extended L hf (I + J) =
      FractionalIdeal.extended L hf I + FractionalIdeal.extended L hf J := by
  exact SourceStack.FractionalIdeals.extended_add L hf I J

theorem hilbert_extended_mul
    {A : Type u} [CommRing A]
    {B : Type v} [CommRing B]
    {f : A →+* B}
    {K : Type w} {M : Submonoid A} [CommRing K] [Algebra A K] [IsLocalization M K]
    (L : Type x) {N : Submonoid B} [CommRing L] [Algebra B L] [IsLocalization N L]
    (hf : M ≤ Submonoid.comap f N)
    (I J : FractionalIdeal M K) :
    FractionalIdeal.extended L hf (I * J) =
      FractionalIdeal.extended L hf I * FractionalIdeal.extended L hf J := by
  exact SourceStack.FractionalIdeals.extended_mul L hf I J

theorem hilbert_absNorm_eq_zero_iff
    {R : Type u} [CommRing R] [IsDedekindDomain R] [Module.Free ℤ R]
    [Module.Finite ℤ R]
    {K : Type v} [CommRing K] [Algebra R K] [IsFractionRing R K]
    [NoZeroDivisors K] {I : FractionalIdeal R⁰ K} :
    FractionalIdeal.absNorm I = 0 ↔ I = 0 := by
  exact SourceStack.FractionalIdeals.absNorm_eq_zero_iff

theorem hilbert_coeIdeal_absNorm
    {R : Type u} [CommRing R] [IsDedekindDomain R] [Module.Free ℤ R]
    [Module.Finite ℤ R]
    {K : Type v} [CommRing K] [Algebra R K] [IsFractionRing R K]
    (I : Ideal R) :
    FractionalIdeal.absNorm (I : FractionalIdeal R⁰ K) =
      (Ideal.absNorm I : ℤ) := by
  exact SourceStack.FractionalIdeals.coeIdeal_absNorm I

end FractionalIdeals

namespace ArithmeticFunctionFields

universe u v w

theorem hilbert_functionField_iff_finiteDimensional
    (Fq : Type u) [Field Fq]
    (F : Type v) [Field F]
    (Fqt : Type w) [Field Fqt] [Algebra Fq[X] Fqt]
    [IsFractionRing Fq[X] Fqt]
    [Algebra (RatFunc Fq) F] [Algebra Fqt F] [Algebra Fq[X] F]
    [IsScalarTower Fq[X] Fqt F] [IsScalarTower Fq[X] (RatFunc Fq) F] :
    FunctionField Fq F ↔ FiniteDimensional Fqt F := by
  exact SourceStack.ArithmeticFunctionFields.functionField_iff_finiteDimensional Fq F Fqt

theorem hilbert_polynomial_algebraMap_injective
    (Fq : Type u) [Field Fq]
    (F : Type v) [Field F]
    [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
    [IsScalarTower Fq[X] (RatFunc Fq) F] :
    Function.Injective (algebraMap Fq[X] F) := by
  exact SourceStack.ArithmeticFunctionFields.polynomial_algebraMap_injective Fq F

namespace RingOfIntegers

theorem hilbert_isDomain
    (Fq : Type u) [Field Fq]
    (F : Type v) [Field F] [Algebra Fq[X] F] :
    IsDomain (FunctionField.ringOfIntegers Fq F) := by
  exact SourceStack.ArithmeticFunctionFields.RingOfIntegers.isDomain Fq F

theorem hilbert_not_isField
    (Fq : Type u) [Field Fq]
    (F : Type v) [Field F]
    [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
    [IsScalarTower Fq[X] (RatFunc Fq) F] :
    ¬ IsField (FunctionField.ringOfIntegers Fq F) := by
  exact SourceStack.ArithmeticFunctionFields.RingOfIntegers.not_isField Fq F

theorem hilbert_isFractionRing
    (Fq : Type u) [Field Fq]
    (F : Type v) [Field F]
    [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
    [IsScalarTower Fq[X] (RatFunc Fq) F]
    [FunctionField Fq F] :
    IsFractionRing (FunctionField.ringOfIntegers Fq F) F := by
  exact SourceStack.ArithmeticFunctionFields.RingOfIntegers.isFractionRing Fq F

theorem hilbert_isDedekindDomain
    (Fq : Type u) [Field Fq]
    (F : Type v) [Field F]
    [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
    [IsScalarTower Fq[X] (RatFunc Fq) F]
    [FunctionField Fq F] [Algebra.IsSeparable (RatFunc Fq) F] :
    IsDedekindDomain (FunctionField.ringOfIntegers Fq F) := by
  exact SourceStack.ArithmeticFunctionFields.RingOfIntegers.isDedekindDomain Fq F

end RingOfIntegers

namespace InftyValuation

theorem hilbert_map_mul
    (Fq : Type u) [Field Fq] [DecidableEq (RatFunc Fq)]
    (x y : RatFunc Fq) :
    FunctionField.inftyValuationDef Fq (x * y) =
      FunctionField.inftyValuationDef Fq x * FunctionField.inftyValuationDef Fq y := by
  exact SourceStack.ArithmeticFunctionFields.InftyValuation.map_mul Fq x y

theorem hilbert_map_add_le_max
    (Fq : Type u) [Field Fq] [DecidableEq (RatFunc Fq)]
    (x y : RatFunc Fq) :
    FunctionField.inftyValuationDef Fq (x + y) ≤
      max (FunctionField.inftyValuationDef Fq x) (FunctionField.inftyValuationDef Fq y) := by
  exact SourceStack.ArithmeticFunctionFields.InftyValuation.map_add_le_max Fq x y

theorem hilbert_C
    (Fq : Type u) [Field Fq] [DecidableEq (RatFunc Fq)]
    {k : Fq} (hk : k ≠ 0) :
    FunctionField.inftyValuationDef Fq (RatFunc.C k) =
      Multiplicative.ofAdd (0 : ℤ) := by
  exact SourceStack.ArithmeticFunctionFields.InftyValuation.C Fq hk

theorem hilbert_X
    (Fq : Type u) [Field Fq] [DecidableEq (RatFunc Fq)] :
    FunctionField.inftyValuationDef Fq RatFunc.X =
      Multiplicative.ofAdd (1 : ℤ) := by
  exact SourceStack.ArithmeticFunctionFields.InftyValuation.X Fq

theorem hilbert_polynomial
    (Fq : Type u) [Field Fq] [DecidableEq (RatFunc Fq)]
    {p : Fq[X]} (hp : p ≠ 0) :
    FunctionField.inftyValuationDef Fq (algebraMap Fq[X] (RatFunc Fq) p) =
      Multiplicative.ofAdd (p.natDegree : ℤ) := by
  exact SourceStack.ArithmeticFunctionFields.InftyValuation.polynomial Fq hp

theorem hilbert_FqtInfty_field
    (Fq : Type u) [Field Fq] [DecidableEq (RatFunc Fq)] :
    Nonempty (Field (FunctionField.FqtInfty Fq)) := by
  exact SourceStack.ArithmeticFunctionFields.InftyValuation.FqtInfty_field Fq

end InftyValuation

end ArithmeticFunctionFields

namespace Schemes

universe u

variable {X Y Z : Scheme.{u}}

theorem hilbert_closedImmersion_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsClosedImmersion f] [IsClosedImmersion g] :
    IsClosedImmersion (f ≫ g) := by
  exact SourceStack.Schemes.closedImmersion_comp f g

theorem hilbert_closedImmersion_isFinite
    (f : X ⟶ Y) [IsClosedImmersion f] :
    IsFinite f := by
  exact SourceStack.Schemes.closedImmersion_isFinite f

theorem hilbert_closedImmersion_universallyClosed
    (f : X ⟶ Y) [IsClosedImmersion f] :
    UniversallyClosed f := by
  exact SourceStack.Schemes.closedImmersion_universallyClosed f

theorem hilbert_closedImmersion_isProper
    (f : X ⟶ Y) [IsClosedImmersion f] :
    IsProper f := by
  exact SourceStack.Schemes.closedImmersion_isProper f

theorem hilbert_closedImmersion_stable_under_base_change :
    MorphismProperty.IsStableUnderBaseChange (@IsClosedImmersion) := by
  exact SourceStack.Schemes.closedImmersion_stable_under_base_change

theorem hilbert_closedImmersion_iff_isFinite_and_mono
    (f : X ⟶ Y) :
    IsClosedImmersion f ↔ IsFinite f ∧ Mono f := by
  exact SourceStack.Schemes.closedImmersion_iff_isFinite_and_mono f

theorem hilbert_finite_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFinite f] [IsFinite g] :
    IsFinite (f ≫ g) := by
  exact SourceStack.Schemes.finite_comp f g

theorem hilbert_finite_iff_integralHom_and_locallyOfFiniteType
    (f : X ⟶ Y) :
    IsFinite f ↔ IsIntegralHom f ∧ LocallyOfFiniteType f := by
  exact SourceStack.Schemes.finite_iff_integralHom_and_locallyOfFiniteType f

theorem hilbert_finite_is_integral
    (f : X ⟶ Y) [IsFinite f] :
    IsIntegralHom f := by
  exact SourceStack.Schemes.finite_is_integral f

theorem hilbert_finite_locally_of_finite_type
    (f : X ⟶ Y) [IsFinite f] :
    LocallyOfFiniteType f := by
  exact SourceStack.Schemes.finite_locally_of_finite_type f

theorem hilbert_finite_stable_under_base_change :
    MorphismProperty.IsStableUnderBaseChange (@IsFinite) := by
  exact SourceStack.Schemes.finite_stable_under_base_change

theorem hilbert_smooth_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSmooth f] [IsSmooth g] :
    IsSmooth (f ≫ g) := by
  exact SourceStack.Schemes.smooth_comp f g

theorem hilbert_smooth_stable_under_base_change :
    MorphismProperty.IsStableUnderBaseChange (@IsSmooth) := by
  exact SourceStack.Schemes.smooth_stable_under_base_change

theorem hilbert_separated_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [IsSeparated g] :
    IsSeparated (f ≫ g) := by
  exact SourceStack.Schemes.separated_comp f g

theorem hilbert_separated_stable_under_base_change :
    MorphismProperty.IsStableUnderBaseChange (@IsSeparated) := by
  exact SourceStack.Schemes.separated_stable_under_base_change

theorem hilbert_universallyClosed_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [UniversallyClosed f] [UniversallyClosed g] :
    UniversallyClosed (f ≫ g) := by
  exact SourceStack.Schemes.universallyClosed_comp f g

theorem hilbert_universallyClosed_stable_under_base_change :
    MorphismProperty.IsStableUnderBaseChange (@UniversallyClosed) := by
  exact SourceStack.Schemes.universallyClosed_stable_under_base_change

theorem hilbert_universallyClosed_isClosedMap
    (f : X ⟶ Y) [UniversallyClosed f] :
    IsClosedMap f.base := by
  exact SourceStack.Schemes.universallyClosed_isClosedMap f

theorem hilbert_proper_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsProper f] [IsProper g] :
    IsProper (f ≫ g) := by
  exact SourceStack.Schemes.proper_comp f g

theorem hilbert_proper_stable_under_base_change :
    MorphismProperty.IsStableUnderBaseChange (@IsProper) := by
  exact SourceStack.Schemes.proper_stable_under_base_change

theorem hilbert_universally_closed_isProperMap
    (f : X ⟶ Y) [UniversallyClosed f] :
    IsProperMap f.base := by
  exact SourceStack.Schemes.universally_closed_isProperMap f

theorem hilbert_proper_isProperMap
    (f : X ⟶ Y) [IsProper f] :
    IsProperMap f.base := by
  exact SourceStack.Schemes.proper_isProperMap f

theorem hilbert_etale_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsEtale f] [IsEtale g] :
    IsEtale (f ≫ g) := by
  exact SourceStack.Schemes.etale_comp f g

theorem hilbert_etale_stable_under_base_change :
    MorphismProperty.IsStableUnderBaseChange (@IsEtale) := by
  exact SourceStack.Schemes.etale_stable_under_base_change

end Schemes

end HilbertSteps
end HilbertTest
