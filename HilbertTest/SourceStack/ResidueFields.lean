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

/-- A section has empty basic open iff all point evaluations vanish. -/
theorem basicOpen_eq_bot_iff_forall_evaluation_eq_zero
    (U : X.Opens) (f : Γ(X, U)) :
    X.basicOpen f = ⊥ ↔
      ∀ x : U, X.evaluation U x x.2 f = 0 :=
  Scheme.basicOpen_eq_bot_iff_forall_evaluation_eq_zero X f

/-- Residue-field maps are compatible with stalk maps and residue maps. -/
theorem residue_residueFieldMap
    (f : X ⟶ Y) (x : X) :
    Y.residue (f.base x) ≫ f.residueFieldMap x =
      f.stalkMap x ≫ X.residue x :=
  Scheme.residue_residueFieldMap f x

/-- Evaluation over an open is natural for residue-field maps. -/
theorem evaluation_naturality
    (f : X ⟶ Y) {V : Y.Opens} (x : X) (hx : f.base x ∈ V) :
    Y.evaluation V (f.base x) hx ≫ f.residueFieldMap x =
      f.app V ≫ X.evaluation (f ⁻¹ᵁ V) x hx :=
  Scheme.evaluation_naturality f x hx

/-- Elementwise form of naturality for evaluation over an open. -/
theorem evaluation_naturality_apply
    (f : X ⟶ Y) {V : Y.Opens} (x : X) (hx : f.base x ∈ V)
    (s : Γ(Y, V)) :
    f.residueFieldMap x (Y.evaluation V (f.base x) hx s) =
      X.evaluation (f ⁻¹ᵁ V) x hx (f.app V s) :=
  Scheme.evaluation_naturality_apply f x hx s

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

/-- Equal points have isomorphic residue fields. -/
theorem residueFieldCongr_exists
    {x y : X} (h : x = y) :
    Nonempty (X.residueField x ≅ X.residueField y) :=
  ⟨Scheme.residueFieldCongr h⟩

/-- The residue-field congruence for reflexivity is the identity isomorphism. -/
theorem residueFieldCongr_refl
    {x : X} :
    Scheme.residueFieldCongr (show x = x from rfl) =
      Iso.refl (X.residueField x) :=
  Scheme.residueFieldCongr_refl

/-- Reversing an equality reverses the residue-field congruence. -/
theorem residueFieldCongr_symm
    {x y : X} (h : x = y) :
    (Scheme.residueFieldCongr h).symm = Scheme.residueFieldCongr h.symm :=
  Scheme.residueFieldCongr_symm h

/-- The inverse of a residue-field congruence is the congruence for the reverse
equality. -/
theorem residueFieldCongr_inv
    {x y : X} (h : x = y) :
    (Scheme.residueFieldCongr h).inv =
      (Scheme.residueFieldCongr h.symm).hom :=
  Scheme.residueFieldCongr_inv h

/-- Residue-field congruences compose along transitive point equalities. -/
theorem residueFieldCongr_trans
    {x y z : X} (hxy : x = y) (hyz : y = z) :
    Scheme.residueFieldCongr hxy ≪≫ Scheme.residueFieldCongr hyz =
      Scheme.residueFieldCongr (hxy.trans hyz) :=
  Scheme.residueFieldCongr_trans hxy hyz

/-- Hom form of transitivity for residue-field congruences. -/
theorem residueFieldCongr_trans_hom
    {x y z : X} (hxy : x = y) (hyz : y = z) :
    (Scheme.residueFieldCongr hxy).hom ≫
        (Scheme.residueFieldCongr hyz).hom =
      (Scheme.residueFieldCongr (hxy.trans hyz)).hom :=
  Scheme.residueFieldCongr_trans_hom X hxy hyz

/-- Residue maps are compatible with residue-field congruences. -/
theorem residue_residueFieldCongr
    {x y : X} (h : x = y) :
    X.residue x ≫ (Scheme.residueFieldCongr h).hom =
      (X.presheaf.stalkCongr (Inseparable.of_eq h)).hom ≫ X.residue y :=
  Scheme.residue_residueFieldCongr X h

/-- Residue-field maps respect equal scheme morphisms. -/
theorem residueFieldMap_congr
    {f g : X ⟶ Y} (e : f = g) (x : X) :
    f.residueFieldMap x =
      (Scheme.residueFieldCongr (by rw [e])).hom ≫ g.residueFieldMap x :=
  Scheme.Hom.residueFieldMap_congr e x

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

/-- A local map from the stalk to a field descends to the residue field. -/
theorem descResidueField_exists
    {K : Type u} [Field K] {x : X}
    (f : X.presheaf.stalk x ⟶ CommRingCat.of K) [IsLocalHom f.hom] :
    Nonempty (X.residueField x ⟶ CommRingCat.of K) :=
  ⟨Scheme.descResidueField f⟩

/-- The descended residue-field map composes with the residue map to recover the
original local stalk map. -/
theorem residue_descResidueField
    {K : Type u} [Field K] {x : X}
    (f : X.presheaf.stalk x ⟶ CommRingCat.of K) [IsLocalHom f.hom] :
    X.residue x ≫ Scheme.descResidueField f = f :=
  Scheme.residue_descResidueField f

/-- The canonical map from an affine open's stalk spectrum agrees with the
global canonical stalk-spectrum map. -/
theorem affineOpen_fromSpecStalk_eq_fromSpecStalk
    {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hxU : x ∈ U) :
    hU.fromSpecStalk hxU = X.fromSpecStalk x :=
  AlgebraicGeometry.IsAffineOpen.fromSpecStalk_eq_fromSpecStalk hU hxU

/-- The closed point of `Spec O_{X,x}` maps to `x`. -/
theorem fromSpecStalk_closedPoint
    (x : X) :
    (X.fromSpecStalk x).base (closedPoint (X.presheaf.stalk x)) = x :=
  Scheme.fromSpecStalk_closedPoint

/-- Formula for the sheaf map of the canonical stalk-spectrum morphism on an
open containing the point. -/
theorem fromSpecStalk_app
    {U : X.Opens} {x : X} (hxU : x ∈ U) :
    (X.fromSpecStalk x).app U =
      X.presheaf.germ U x hxU ≫
        (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv ≫
          (Spec (X.presheaf.stalk x)).presheaf.map (homOfLE le_top).op :=
  Scheme.fromSpecStalk_app hxU

/-- Formula for the global-section map of the canonical stalk-spectrum
morphism. -/
theorem fromSpecStalk_appTop
    {x : X} :
    (X.fromSpecStalk x).appTop =
      X.presheaf.germ ⊤ x trivial ≫
        (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv ≫
          (Spec (X.presheaf.stalk x)).presheaf.map (homOfLE le_top).op :=
  Scheme.fromSpecStalk_appTop

/-- The range of `Spec O_{X,x} -> X` is the set of points specializing to `x`. -/
theorem range_fromSpecStalk
    (x : X) :
    Set.range (X.fromSpecStalk x).base = { y | y ⤳ x } :=
  Scheme.range_fromSpecStalk

/-- Specialization maps on stalks are compatible with canonical
stalk-spectrum maps. -/
theorem Spec_map_stalkSpecializes_fromSpecStalk
    {x y : X} (h : x ⤳ y) :
    Spec.map (X.presheaf.stalkSpecializes h) ≫ X.fromSpecStalk y =
      X.fromSpecStalk x :=
  Scheme.Spec_map_stalkSpecializes_fromSpecStalk h

/-- Stalk maps are compatible with the canonical maps from stalk spectra. -/
theorem Spec_map_stalkMap_fromSpecStalk
    (f : X ⟶ Y) (x : X) :
    Spec.map (f.stalkMap x) ≫ Y.fromSpecStalk _ =
      X.fromSpecStalk x ≫ f :=
  Scheme.Spec_map_stalkMap_fromSpecStalk f

/-- The canonical stalk-spectrum map for an affine scheme is given by the
structure-sheaf stalk map. -/
theorem Spec_fromSpecStalk
    (R : CommRingCat.{u}) (x : Spec R) :
    (Spec R).fromSpecStalk x =
      Spec.map ((Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ x trivial) :=
  Scheme.Spec_fromSpecStalk R x

/-- The canonical `Spec O_{X,x} -> U` over an open subscheme composes with the
open immersion to the global canonical map. -/
theorem Opens_fromSpecStalkOfMem_ι
    (U : X.Opens) (x : X) (hxU : x ∈ U) :
    U.fromSpecStalkOfMem x hxU ≫ U.ι = X.fromSpecStalk x :=
  Scheme.Opens.fromSpecStalkOfMem_ι U x hxU

/-- The canonical stalk-spectrum map followed by `toSpecΓ` is the spectrum map
of the global germ. -/
theorem fromSpecStalk_toSpecΓ
    (X : Scheme.{u}) (x : X) :
    X.fromSpecStalk x ≫ X.toSpecΓ =
      Spec.map (X.presheaf.germ ⊤ x trivial) :=
  Scheme.fromSpecStalk_toSpecΓ X x

/-- The open-subscheme stalk-spectrum map followed by `toSpecΓ` is the spectrum
map of the germ on that open. -/
theorem Opens_fromSpecStalkOfMem_toSpecΓ
    (U : X.Opens) (x : X) (hxU : x ∈ U) :
    U.fromSpecStalkOfMem x hxU ≫ U.toSpecΓ =
      Spec.map (X.presheaf.germ U x hxU) :=
  Scheme.Opens.fromSpecStalkOfMem_toSpecΓ U x hxU

/-- The closed-point stalk of `Spec R` for a local ring is canonically
isomorphic to `R`. -/
theorem stalkClosedPointIso_exists
    (R : CommRingCat.{u}) [IsLocalRing R] :
    Nonempty ((Spec R).presheaf.stalk (closedPoint R) ≅ R) :=
  ⟨stalkClosedPointIso R⟩

/-- Inverse of the closed-point stalk isomorphism is the structure-sheaf stalk
map. -/
theorem stalkClosedPointIso_inv
    (R : CommRingCat.{u}) [IsLocalRing R] :
    (stalkClosedPointIso R).inv = StructureSheaf.toStalk R _ :=
  AlgebraicGeometry.stalkClosedPointIso_inv R

/-- The germ at the closed point followed by the closed-point stalk isomorphism
recovers the global-section isomorphism for affine schemes. -/
theorem germ_stalkClosedPointIso_hom
    (R : CommRingCat.{u}) [IsLocalRing R] :
    (Spec R).presheaf.germ ⊤ (closedPoint R) trivial ≫
        (stalkClosedPointIso R).hom =
      (Scheme.ΓSpecIso R).hom :=
  AlgebraicGeometry.germ_stalkClosedPointIso_hom R

/-- Spectrum form of the closed-point stalk isomorphism. -/
theorem Spec_stalkClosedPointIso
    (R : CommRingCat.{u}) [IsLocalRing R] :
    Spec.map (stalkClosedPointIso R).inv =
      (Spec R).fromSpecStalk (closedPoint R) :=
  AlgebraicGeometry.Spec_stalkClosedPointIso R

/-- A morphism from the spectrum of a local ring induces a local map from the
stalk at the image of the closed point. -/
theorem stalkClosedPointTo_isLocalHom
    {R : CommRingCat.{u}} [IsLocalRing R] (f : Spec R ⟶ X) :
    IsLocalHom (Scheme.stalkClosedPointTo f).hom := by
  infer_instance

/-- If the closed point maps into an open, the preimage of that open is all of
`Spec R`. -/
theorem preimage_eq_top_of_closedPoint_mem
    {R : CommRingCat.{u}} [IsLocalRing R] (f : Spec R ⟶ X)
    {U : X.Opens} (hU : f.base (closedPoint R) ∈ U) :
    f ⁻¹ᵁ U = ⊤ :=
  Scheme.preimage_eq_top_of_closedPoint_mem f hU

/-- Closed-point stalk maps are functorial under postcomposition. -/
theorem stalkClosedPointTo_comp
    {R : CommRingCat.{u}} [IsLocalRing R] (f : Spec R ⟶ X) (g : X ⟶ Y) :
    Scheme.stalkClosedPointTo (f ≫ g) =
      g.stalkMap _ ≫ Scheme.stalkClosedPointTo f :=
  Scheme.stalkClosedPointTo_comp f g

/-- The closed-point stalk map of the canonical stalk-spectrum morphism is the
point-congruence stalk map. -/
theorem stalkClosedPointTo_fromSpecStalk
    (x : X) :
    Scheme.stalkClosedPointTo (X.fromSpecStalk x) =
      (X.presheaf.stalkCongr
        (Inseparable.of_eq (by rw [Scheme.fromSpecStalk_closedPoint]))).hom :=
  Scheme.stalkClosedPointTo_fromSpecStalk x

/-- The local map induced at the closed point reconstructs the original
morphism from `Spec R`. -/
theorem Spec_stalkClosedPointTo_fromSpecStalk
    {R : CommRingCat.{u}} [IsLocalRing R] (f : Spec R ⟶ X) :
    Spec.map (Scheme.stalkClosedPointTo f) ≫ X.fromSpecStalk _ = f :=
  Scheme.Spec_stalkClosedPointTo_fromSpecStalk (f := f)

/-- The canonical map from the residue-field spectrum maps every point to `x`. -/
theorem fromSpecResidueField_apply
    (x : X) (s : Spec (X.residueField x)) :
    (X.fromSpecResidueField x).base s = x :=
  Scheme.fromSpecResidueField_apply x s

/-- Residue-field congruences are compatible with the canonical maps from
residue-field spectra. -/
theorem residueFieldCongr_fromSpecResidueField
    {x y : X} (h : x = y) :
    Spec.map (Scheme.residueFieldCongr h).hom ≫ X.fromSpecResidueField x =
      X.fromSpecResidueField y :=
  Scheme.residueFieldCongr_fromSpecResidueField h

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

/-- A local stalk map to a field gives the same point as the descended
residue-field map. -/
theorem descResidueField_fromSpecResidueField
    {K : Type u} [Field K] {x : X}
    (f : X.presheaf.stalk x ⟶ CommRingCat.of K) [IsLocalHom f.hom] :
    Spec.map (Scheme.descResidueField f) ≫ X.fromSpecResidueField x =
      Spec.map f ≫ X.fromSpecStalk x :=
  Scheme.descResidueField_fromSpecResidueField X f

/-- The field-valued point reconstructed from its closed-point residue-field
map is the original morphism. -/
theorem descResidueField_stalkClosedPointTo_fromSpecResidueField
    (K : Type u) [Field K] (X : Scheme.{u})
    (f : Spec (CommRingCat.of K) ⟶ X) :
    Spec.map (@Scheme.descResidueField (CommRingCat.of K) _ X _
        (Scheme.stalkClosedPointTo f) _) ≫
      X.fromSpecResidueField (f.base (closedPoint K)) = f :=
  Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X f

/-- Field-valued points of a scheme are equivalent to a scheme point plus a map
from its residue field. -/
theorem SpecToEquivOfField_exists
    (K : Type u) [Field K] (X : Scheme.{u}) :
    Nonempty ((Spec (.of K) ⟶ X) ≃ Σ x, X.residueField x ⟶ .of K) :=
  ⟨Scheme.SpecToEquivOfField K X⟩

/-- Equality criterion for the sigma data classifying field-valued points. -/
theorem SpecToEquivOfField_eq_iff
    {K : Type u} [Field K] {X : Scheme.{u}}
    {f₁ f₂ : Σ x, X.residueField x ⟶ CommRingCat.of K} :
    f₁ = f₂ ↔
      ∃ e : f₁.1 = f₂.1,
        f₁.2 = (Scheme.residueFieldCongr e).hom ≫ f₂.2 :=
  Scheme.SpecToEquivOfField_eq_iff

/-- Local-ring-valued points are equivalent to a scheme point plus a local map
from the stalk at that point. -/
theorem SpecToEquivOfLocalRing_exists
    (R : CommRingCat.{u}) [IsLocalRing R] (X : Scheme.{u}) :
    Nonempty ((Spec R ⟶ X) ≃
      Σ x, { f : X.presheaf.stalk x ⟶ R // IsLocalHom f.hom }) :=
  ⟨SpecToEquivOfLocalRing X R⟩

/-- Equality criterion for the sigma data classifying local-ring-valued points. -/
theorem SpecToEquivOfLocalRing_eq_iff
    {R : CommRingCat.{u}} [IsLocalRing R] {X : Scheme.{u}}
    {f₁ f₂ : Σ x, { f : X.presheaf.stalk x ⟶ R // IsLocalHom f.hom }} :
    f₁ = f₂ ↔
      ∃ h₁ : f₁.1 = f₂.1,
        f₁.2.1 = (X.presheaf.stalkCongr (Inseparable.of_eq h₁)).hom ≫ f₂.2.1 :=
  _root_.AlgebraicGeometry.SpecToEquivOfLocalRing_eq_iff

end ResidueFields
end SourceStack
end HilbertTest
