import Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks

/-!
Surjective-on-stalks source wrappers.

This module exposes Mathlib's scheme-morphism property saying all stalk maps are
surjective, together with its affine criterion, locality, composition/base-change
stability, and the pullback embedding theorem.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology
open AlgebraicGeometry

namespace HilbertTest
namespace SourceStack
namespace SurjectiveOnStalks

universe u

variable {X Y Z S : Scheme.{u}}

/-- A morphism that is surjective on stalks has surjective stalk maps at every
point. -/
theorem stalkMap_surjective
    (f : X ⟶ Y) [AlgebraicGeometry.SurjectiveOnStalks f] (x : X) :
    Function.Surjective (f.stalkMap x) :=
  f.stalkMap_surjective x

/-- Open immersions are surjective on stalks. -/
theorem openImmersion_surjectiveOnStalks
    (f : X ⟶ Y) [IsOpenImmersion f] :
    AlgebraicGeometry.SurjectiveOnStalks f :=
  inferInstance

/-- Surjectivity on stalks is multiplicative. -/
theorem surjectiveOnStalks_multiplicative :
    MorphismProperty.IsMultiplicative (@AlgebraicGeometry.SurjectiveOnStalks) :=
  inferInstance

/-- Surjectivity on stalks is stable under composition. -/
theorem surjectiveOnStalks_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicGeometry.SurjectiveOnStalks f]
    [AlgebraicGeometry.SurjectiveOnStalks g] :
    AlgebraicGeometry.SurjectiveOnStalks (f ≫ g) :=
  inferInstance

/-- Surjectivity on stalks is exactly the stalkwise surjectivity property. -/
theorem surjectiveOnStalks_eq_stalkwise :
    @AlgebraicGeometry.SurjectiveOnStalks =
      AlgebraicGeometry.stalkwise (Function.Surjective ·) :=
  AlgebraicGeometry.SurjectiveOnStalks.eq_stalkwise

/-- Surjectivity on stalks is local at the target. -/
theorem surjectiveOnStalks_isLocalAtTarget :
    IsLocalAtTarget (@AlgebraicGeometry.SurjectiveOnStalks) :=
  inferInstance

/-- Surjectivity on stalks is local at the source. -/
theorem surjectiveOnStalks_isLocalAtSource :
    IsLocalAtSource (@AlgebraicGeometry.SurjectiveOnStalks) :=
  inferInstance

/-- For affine schemes, surjectivity on stalks is the corresponding ring-hom
property. -/
theorem surjectiveOnStalks_Spec_iff
    {R S : CommRingCat.{u}} {φ : R ⟶ S} :
    AlgebraicGeometry.SurjectiveOnStalks (Spec.map φ) ↔
      RingHom.SurjectiveOnStalks φ.hom :=
  AlgebraicGeometry.SurjectiveOnStalks.Spec_iff

/-- Affine criterion for surjectivity on stalks. -/
theorem surjectiveOnStalks_iff_of_isAffine
    {f : X ⟶ Y} [IsAffine X] [IsAffine Y] :
    AlgebraicGeometry.SurjectiveOnStalks f ↔
      RingHom.SurjectiveOnStalks (f.app ⊤).hom :=
  AlgebraicGeometry.SurjectiveOnStalks.iff_of_isAffine

/-- If a composite is surjective on stalks, then the first morphism is
surjective on stalks. -/
theorem surjectiveOnStalks_of_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicGeometry.SurjectiveOnStalks (f ≫ g)] :
    AlgebraicGeometry.SurjectiveOnStalks f :=
  AlgebraicGeometry.SurjectiveOnStalks.of_comp f g

/-- Surjectivity on stalks is stable under base change. -/
theorem surjectiveOnStalks_stableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange (@AlgebraicGeometry.SurjectiveOnStalks) :=
  inferInstance

/-- If the right leg is surjective on stalks, then the underlying map from a
scheme pullback to the product of carrier spaces is an embedding. -/
theorem surjectiveOnStalks_isEmbedding_pullback
    (f : X ⟶ S) (g : Y ⟶ S)
    [AlgebraicGeometry.SurjectiveOnStalks g] :
    IsEmbedding (fun x ↦ ((pullback.fst f g).base x, (pullback.snd f g).base x)) :=
  AlgebraicGeometry.SurjectiveOnStalks.isEmbedding_pullback f g

end SurjectiveOnStalks
end SourceStack
end HilbertTest

