import Mathlib.AlgebraicGeometry.Scheme

/-!
Raw scheme stalk-map source wrappers.

This module exposes the basic stalk-map identities for scheme morphisms:
identity, composition, specialization naturality, congruence, inverse isomorphism
identities, and compatibility with germs.
-/

noncomputable section

open CategoryTheory TopologicalSpace IsLocalRing
open AlgebraicGeometry

namespace HilbertTest
namespace SourceStack
namespace StalkMaps

universe u

variable {X Y Z : Scheme.{u}}

/-- Stalk maps of scheme morphisms are local homomorphisms. -/
theorem stalkMap_isLocalHom
    (f : X ⟶ Y) (x : X) :
    IsLocalHom (f.stalkMap x).hom :=
  inferInstance

/-- The stalk map of the identity morphism is the identity. -/
theorem stalkMap_id
    (X : Scheme.{u}) (x : X) :
    (𝟙 X : X ⟶ X).stalkMap x = 𝟙 (X.presheaf.stalk x) :=
  Scheme.stalkMap_id X x

/-- Stalk maps are functorial under composition. -/
theorem stalkMap_comp
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g : X ⟶ Z).stalkMap x =
      g.stalkMap (f.base x) ≫ f.stalkMap x :=
  Scheme.stalkMap_comp f g x

/-- Stalk maps commute with specialization maps. -/
theorem stalkSpecializes_stalkMap
    (f : X ⟶ Y) (x x' : X) (h : x ⤳ x') :
    Y.presheaf.stalkSpecializes (f.base.map_specializes h) ≫ f.stalkMap x =
      f.stalkMap x' ≫ X.presheaf.stalkSpecializes h :=
  Scheme.stalkSpecializes_stalkMap f x x' h

/-- Elementwise form of compatibility between stalk maps and specialization
maps. -/
theorem stalkSpecializes_stalkMap_apply
    (f : X ⟶ Y) (x x' : X) (h : x ⤳ x')
    (y : Y.presheaf.stalk (f.base x')) :
    f.stalkMap x (Y.presheaf.stalkSpecializes (f.base.map_specializes h) y) =
      X.presheaf.stalkSpecializes h (f.stalkMap x' y) :=
  Scheme.stalkSpecializes_stalkMap_apply f x x' h y

/-- Stalk maps respect equal morphisms and equal source points. -/
theorem stalkMap_congr
    (f g : X ⟶ Y) (hfg : f = g) (x x' : X) (hxx' : x = x') :
    f.stalkMap x ≫ (X.presheaf.stalkCongr (Inseparable.of_eq hxx')).hom =
      (Y.presheaf.stalkCongr
        (Inseparable.of_eq <| hfg ▸ hxx' ▸ rfl)).hom ≫
        g.stalkMap x' :=
  Scheme.stalkMap_congr f g hfg x x' hxx'

/-- Hom form of stalk-map congruence for equal morphisms. -/
theorem stalkMap_congr_hom
    (f g : X ⟶ Y) (hfg : f = g) (x : X) :
    f.stalkMap x =
      (Y.presheaf.stalkCongr (Inseparable.of_eq <| hfg ▸ rfl)).hom ≫
        g.stalkMap x :=
  Scheme.stalkMap_congr_hom f g hfg x

/-- Stalk-map congruence for equal source points. -/
theorem stalkMap_congr_point
    (f : X ⟶ Y) (x x' : X) (hxx' : x = x') :
    f.stalkMap x ≫ (X.presheaf.stalkCongr (Inseparable.of_eq hxx')).hom =
      (Y.presheaf.stalkCongr (Inseparable.of_eq <| hxx' ▸ rfl)).hom ≫
        f.stalkMap x' :=
  Scheme.stalkMap_congr_point f x x' hxx'

/-- Stalk maps for an isomorphism followed by its inverse compose to the
point-congruence stalk map. -/
theorem stalkMap_hom_inv
    (e : X ≅ Y) (y : Y) :
    e.hom.stalkMap (e.inv.base y) ≫ e.inv.stalkMap y =
      (Y.presheaf.stalkCongr (Inseparable.of_eq (by simp))).hom :=
  Scheme.stalkMap_hom_inv e y

/-- Elementwise form of `stalkMap_hom_inv`. -/
theorem stalkMap_hom_inv_apply
    (e : X ≅ Y) (y : Y) (z : Y.presheaf.stalk (e.hom.base (e.inv.base y))) :
    e.inv.stalkMap y (e.hom.stalkMap (e.inv.base y) z) =
      (Y.presheaf.stalkCongr (Inseparable.of_eq (by simp))).hom z :=
  Scheme.stalkMap_hom_inv_apply e y z

/-- Stalk maps for an inverse followed by an isomorphism compose to the
point-congruence stalk map. -/
theorem stalkMap_inv_hom
    (e : X ≅ Y) (x : X) :
    e.inv.stalkMap (e.hom.base x) ≫ e.hom.stalkMap x =
      (X.presheaf.stalkCongr (Inseparable.of_eq (by simp))).hom :=
  Scheme.stalkMap_inv_hom e x

/-- Elementwise form of `stalkMap_inv_hom`. -/
theorem stalkMap_inv_hom_apply
    (e : X ≅ Y) (x : X) (y : X.presheaf.stalk (e.inv.base (e.hom.base x))) :
    e.hom.stalkMap x (e.inv.stalkMap (e.hom.base x) y) =
      (X.presheaf.stalkCongr (Inseparable.of_eq (by simp))).hom y :=
  Scheme.stalkMap_inv_hom_apply e x y

/-- Stalk maps are compatible with germs of sections over opens. -/
theorem stalkMap_germ
    (f : X ⟶ Y) (U : Y.Opens) (x : X) (hx : f.base x ∈ U) :
    Y.presheaf.germ U (f.base x) hx ≫ f.stalkMap x =
      f.app U ≫ X.presheaf.germ (f ⁻¹ᵁ U) x hx :=
  Scheme.stalkMap_germ f U x hx

/-- Elementwise form of compatibility between stalk maps and germs. -/
theorem stalkMap_germ_apply
    (f : X ⟶ Y) (U : Y.Opens) (x : X) (hx : f.base x ∈ U) (y : Γ(Y, U)) :
    f.stalkMap x (Y.presheaf.germ U (f.base x) hx y) =
      X.presheaf.germ (f ⁻¹ᵁ U) x hx (f.app U y) :=
  Scheme.stalkMap_germ_apply f U x hx y

end StalkMaps
end SourceStack
end HilbertTest
