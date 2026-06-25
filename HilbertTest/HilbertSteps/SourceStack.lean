import HilbertTest.SourceStack.FiniteSet
import HilbertTest.SourceStack.LinearAlgebra
import HilbertTest.SourceStack.ComplexSeparation
import HilbertTest.SourceStack.ProjectiveLine
import HilbertTest.SourceStack.RationalMaps
import HilbertTest.SourceStack.FunctionFields
import HilbertTest.SourceStack.FieldTheory
import HilbertTest.SourceStack.UnramifiedEtale
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
open AlgebraicGeometry
open scoped TensorProduct
open scoped IntermediateField Polynomial

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
