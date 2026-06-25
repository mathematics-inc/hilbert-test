import Mathlib.AlgebraicGeometry.ResidueField

/-!
Residue-field and stalk source wrappers.

This module exposes Mathlib's point-level scheme API: stalk maps, residue
fields, evaluation at points, morphisms `Spec κ(x) -> X`, and the equivalence
between field-valued points and residue-field maps.
-/

noncomputable section

open CategoryTheory Opposite IsLocalRing
open AlgebraicGeometry

namespace HilbertTest
namespace SourceStack
namespace ResidueFields

universe u

variable {X Y Z : Scheme.{u}}

/-- The residue field at a scheme point carries a field structure. -/
theorem residueField_field_exists
    (x : X) :
    Nonempty (Field (X.residueField x)) :=
  ⟨inferInstance⟩

/-- The residue map from the stalk to the residue field is surjective. -/
theorem residue_surjective
    (X : Scheme.{u}) (x : X) :
    Function.Surjective (X.residue x) :=
  Scheme.residue_surjective X x

/-- Evaluation of a section at a point is zero iff the point is not in the
section's basic open. -/
theorem evaluation_eq_zero_iff_not_mem_basicOpen
    (U : X.Opens) (x : X) (hx : x ∈ U) (f : Γ(X, U)) :
    X.evaluation U x hx f = 0 ↔ x ∉ X.basicOpen f :=
  Scheme.evaluation_eq_zero_iff_not_mem_basicOpen X x hx f

/-- Evaluation of a section at a point is nonzero iff the point is in the
section's basic open. -/
theorem evaluation_ne_zero_iff_mem_basicOpen
    (U : X.Opens) (x : X) (hx : x ∈ U) (f : Γ(X, U)) :
    X.evaluation U x hx f ≠ 0 ↔ x ∈ X.basicOpen f :=
  Scheme.evaluation_ne_zero_iff_mem_basicOpen X x hx f

/-- Residue-field maps are compatible with stalk maps and residue maps. -/
theorem residue_residueFieldMap
    (f : X ⟶ Y) (x : X) :
    Y.residue (f.base x) ≫ f.residueFieldMap x =
      f.stalkMap x ≫ X.residue x :=
  Scheme.residue_residueFieldMap f x

/-- The identity morphism induces the identity residue-field map. -/
theorem residueFieldMap_id
    (x : X) :
    Scheme.Hom.residueFieldMap (𝟙 X) x = 𝟙 (X.residueField x) :=
  Scheme.residueFieldMap_id x

/-- Residue-field maps are functorial under composition. -/
theorem residueFieldMap_comp
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g).residueFieldMap x =
      g.residueFieldMap (f.base x) ≫ f.residueFieldMap x :=
  Scheme.residueFieldMap_comp f g x

/-- Global evaluation is natural for residue-field maps. -/
theorem Γevaluation_naturality
    (f : X ⟶ Y) (x : X) :
    Y.Γevaluation (f.base x) ≫ f.residueFieldMap x =
      f.c.app (op ⊤) ≫ X.Γevaluation x :=
  Scheme.Γevaluation_naturality f x

/-- Elementwise form of naturality of global evaluation. -/
theorem Γevaluation_naturality_apply
    (f : X ⟶ Y) (x : X) (a : Y.presheaf.obj (op ⊤)) :
    f.residueFieldMap x (Y.Γevaluation (f.base x) a) =
      X.Γevaluation x (f.c.app (op ⊤) a) :=
  Scheme.Γevaluation_naturality_apply f x a

/-- Open immersions induce residue-field isomorphisms. -/
theorem residueFieldMap_isIso_of_openImmersion
    (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    IsIso (f.residueFieldMap x) :=
  inferInstance

/-- The closed point of `Spec O_{X,x}` maps to `x`. -/
theorem fromSpecStalk_closedPoint
    (x : X) :
    (X.fromSpecStalk x).base (closedPoint (X.presheaf.stalk x)) = x :=
  Scheme.fromSpecStalk_closedPoint

/-- The range of `Spec O_{X,x} -> X` is the set of points specializing to `x`. -/
theorem range_fromSpecStalk
    (x : X) :
    Set.range (X.fromSpecStalk x).base = { y | y ⤳ x } :=
  Scheme.range_fromSpecStalk

/-- Stalk maps are compatible with the canonical maps from stalk spectra. -/
theorem Spec_map_stalkMap_fromSpecStalk
    (f : X ⟶ Y) (x : X) :
    Spec.map (f.stalkMap x) ≫ Y.fromSpecStalk _ =
      X.fromSpecStalk x ≫ f :=
  Scheme.Spec_map_stalkMap_fromSpecStalk f

/-- The canonical map from the residue-field spectrum maps every point to `x`. -/
theorem fromSpecResidueField_apply
    (x : X) (s : Spec (X.residueField x)) :
    (X.fromSpecResidueField x).base s = x :=
  Scheme.fromSpecResidueField_apply x s

/-- The range of `Spec κ(x) -> X` is the singleton `{x}`. -/
theorem range_fromSpecResidueField
    (x : X) :
    Set.range (X.fromSpecResidueField x).base = {x} :=
  Scheme.range_fromSpecResidueField x

/-- Residue-field maps are compatible with the canonical maps `Spec κ(x) -> X`. -/
theorem Spec_map_residueFieldMap_fromSpecResidueField
    (f : X ⟶ Y) (x : X) :
    Spec.map (f.residueFieldMap x) ≫ Y.fromSpecResidueField _ =
      X.fromSpecResidueField x ≫ f :=
  Scheme.Hom.Spec_map_residueFieldMap_fromSpecResidueField f x

/-- Field-valued points of a scheme are equivalent to a scheme point plus a map
from its residue field. -/
theorem SpecToEquivOfField_exists
    (K : Type u) [Field K] (X : Scheme.{u}) :
    Nonempty ((Spec (.of K) ⟶ X) ≃ Σ x, X.residueField x ⟶ .of K) :=
  ⟨Scheme.SpecToEquivOfField K X⟩

/-- Local-ring-valued points are equivalent to a scheme point plus a local map
from the stalk at that point. -/
theorem SpecToEquivOfLocalRing_exists
    (R : CommRingCat.{u}) [IsLocalRing R] (X : Scheme.{u}) :
    Nonempty ((Spec R ⟶ X) ≃
      Σ x, { f : X.presheaf.stalk x ⟶ R // IsLocalHom f.hom }) :=
  ⟨SpecToEquivOfLocalRing X R⟩

end ResidueFields
end SourceStack
end HilbertTest
