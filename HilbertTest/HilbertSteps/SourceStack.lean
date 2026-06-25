import HilbertTest.SourceStack.FiniteSet
import HilbertTest.SourceStack.LinearAlgebra
import HilbertTest.SourceStack.ComplexSeparation
import HilbertTest.SourceStack.ProjectiveLine
import HilbertTest.SourceStack.RationalMaps
import HilbertTest.SourceStack.FunctionFields
import HilbertTest.SourceStack.UnramifiedEtale
import HilbertTest.SourceStack.Topology
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

end Topology

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
