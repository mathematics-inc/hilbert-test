import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
Point-carrier source wrappers for scheme pullbacks.

This module exposes Mathlib's description of the underlying points of a scheme
fiber product in terms of points over the same base point and prime ideals of
the tensor product of residue fields.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing TensorProduct
open AlgebraicGeometry

namespace HilbertTest
namespace SourceStack
namespace PullbackCarrier

universe u

variable {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}

/-- A triplet can be built from two points with the same image in the base. -/
theorem triplet_mk'_exists
    (x : X) (y : Y) (h : f.base x = g.base y) :
    Nonempty (Scheme.Pullback.Triplet f g) :=
  ⟨Scheme.Pullback.Triplet.mk' x y h⟩

/-- The residue-field tensor attached to a pullback triplet is nontrivial. -/
theorem triplet_tensor_nontrivial
    (T : Scheme.Pullback.Triplet f g) :
    Nontrivial T.tensor :=
  inferInstance

/-- The first canonical map into the residue-field tensor exists. -/
theorem triplet_tensorInl_exists
    (T : Scheme.Pullback.Triplet f g) :
    Nonempty (X.residueField T.x ⟶ T.tensor) :=
  ⟨T.tensorInl⟩

/-- The second canonical map into the residue-field tensor exists. -/
theorem triplet_tensorInr_exists
    (T : Scheme.Pullback.Triplet f g) :
    Nonempty (Y.residueField T.y ⟶ T.tensor) :=
  ⟨T.tensorInr⟩

/-- The two spectrum maps from the tensor square form the residue-field
pullback square. -/
theorem triplet_Spec_map_tensor_isPullback
    (T : Scheme.Pullback.Triplet f g) :
    IsPullback
      (Spec.map T.tensorInl) (Spec.map T.tensorInr)
      (Spec.map ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x))
      (Spec.map ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y)) :=
  T.Spec_map_tensor_isPullback

/-- The tensor spectrum maps compatibly to the two legs over the base. -/
theorem triplet_Spec_map_tensorInl_fromSpecResidueField
    (T : Scheme.Pullback.Triplet f g) :
    (Spec.map T.tensorInl ≫ X.fromSpecResidueField T.x) ≫ f =
      (Spec.map T.tensorInr ≫ Y.fromSpecResidueField T.y) ≫ g :=
  T.Spec_map_tensorInl_fromSpecResidueField

/-- The map from the tensor spectrum to the scheme pullback exists. -/
theorem triplet_SpecTensorTo_exists
    (T : Scheme.Pullback.Triplet f g) :
    Nonempty (Spec T.tensor ⟶ pullback f g) :=
  ⟨T.SpecTensorTo⟩

/-- The tensor-spectrum point projects to the first triplet point. -/
theorem triplet_specTensorTo_base_fst
    (T : Scheme.Pullback.Triplet f g) (p : Spec T.tensor) :
    (pullback.fst f g).base (T.SpecTensorTo.base p) = T.x :=
  Scheme.Pullback.Triplet.specTensorTo_base_fst T p

/-- The tensor-spectrum point projects to the second triplet point. -/
theorem triplet_specTensorTo_base_snd
    (T : Scheme.Pullback.Triplet f g) (p : Spec T.tensor) :
    (pullback.snd f g).base (T.SpecTensorTo.base p) = T.y :=
  Scheme.Pullback.Triplet.specTensorTo_base_snd T p

/-- First projection identity for the tensor-spectrum map. -/
theorem triplet_specTensorTo_fst
    (T : Scheme.Pullback.Triplet f g) :
    T.SpecTensorTo ≫ pullback.fst f g =
      Spec.map T.tensorInl ≫ X.fromSpecResidueField T.x :=
  Scheme.Pullback.Triplet.specTensorTo_fst T

/-- Second projection identity for the tensor-spectrum map. -/
theorem triplet_specTensorTo_snd
    (T : Scheme.Pullback.Triplet f g) :
    T.SpecTensorTo ≫ pullback.snd f g =
      Spec.map T.tensorInr ≫ Y.fromSpecResidueField T.y :=
  Scheme.Pullback.Triplet.specTensorTo_snd T

/-- A point of the scheme pullback yields the corresponding residue-field
triplet. -/
theorem triplet_ofPoint_exists
    (t : ↑(pullback f g)) :
    Nonempty (Scheme.Pullback.Triplet f g) :=
  ⟨Scheme.Pullback.Triplet.ofPoint t⟩

/-- Constructing a pullback point from a triplet and then extracting the triplet
recovers the original triplet. -/
theorem triplet_ofPoint_SpecTensorTo
    (T : Scheme.Pullback.Triplet f g) (p : Spec T.tensor) :
    Scheme.Pullback.Triplet.ofPoint (T.SpecTensorTo.base p) = T :=
  Scheme.Pullback.Triplet.ofPoint_SpecTensorTo T p

/-- Residue-field maps from a pullback point satisfy the tensor equalizer
relation. -/
theorem residueFieldCongr_inv_residueFieldMap_ofPoint
    (t : ↑(pullback f g)) :
    ((S.residueFieldCongr (Scheme.Pullback.Triplet.ofPoint t).hx).inv ≫
        f.residueFieldMap (Scheme.Pullback.Triplet.ofPoint t).x) ≫
      (pullback.fst f g).residueFieldMap t =
    ((S.residueFieldCongr (Scheme.Pullback.Triplet.ofPoint t).hy).inv ≫
        g.residueFieldMap (Scheme.Pullback.Triplet.ofPoint t).y) ≫
      (pullback.snd f g).residueFieldMap t :=
  Scheme.Pullback.residueFieldCongr_inv_residueFieldMap_ofPoint t

/-- The canonical tensor map to the residue field at a pullback point exists. -/
theorem ofPointTensor_exists
    (t : ↑(pullback f g)) :
    Nonempty ((Scheme.Pullback.Triplet.ofPoint t).tensor ⟶
      (pullback f g).residueField t) :=
  ⟨Scheme.Pullback.ofPointTensor t⟩

/-- The tensor map to the residue field reconstructs the residue-field point of
the scheme pullback. -/
theorem ofPointTensor_SpecTensorTo
    (t : ↑(pullback f g)) :
    Spec.map (Scheme.Pullback.ofPointTensor t) ≫
        (Scheme.Pullback.Triplet.ofPoint t).SpecTensorTo =
      (pullback f g).fromSpecResidueField t :=
  Scheme.Pullback.ofPointTensor_SpecTensorTo t

/-- The chosen point of the tensor spectrum maps back to the original pullback
point. -/
theorem SpecTensorTo_SpecOfPoint
    (t : ↑(pullback f g)) :
    (Scheme.Pullback.Triplet.ofPoint t).SpecTensorTo.base
        (Scheme.Pullback.SpecOfPoint t) = t :=
  Scheme.Pullback.SpecTensorTo_SpecOfPoint t

/-- Tensor congruence is compatible with the tensor-spectrum map. -/
theorem tensorCongr_SpecTensorTo
    {T T' : Scheme.Pullback.Triplet f g} (h : T = T') :
    Spec.map (Scheme.Pullback.Triplet.tensorCongr h).hom ≫ T.SpecTensorTo =
      T'.SpecTensorTo :=
  Scheme.Pullback.tensorCongr_SpecTensorTo h

/-- Helper equality criterion for the carrier-equivalence sigma data. -/
theorem carrierEquiv_eq_iff
    {T₁ T₂ : Σ T : Scheme.Pullback.Triplet f g, Spec T.tensor} :
    T₁ = T₂ ↔
      ∃ e : T₁.1 = T₂.1,
        (Spec.map (Scheme.Pullback.Triplet.tensorCongr e).inv).base T₁.2 =
          T₂.2 :=
  Scheme.Pullback.carrierEquiv_eq_iff

/-- Pullback points are equivalent to triplets plus a point of the corresponding
residue-field tensor spectrum. -/
theorem carrierEquiv_exists :
    Nonempty (↑(pullback f g) ≃
      Σ T : Scheme.Pullback.Triplet f g, Spec T.tensor) :=
  ⟨Scheme.Pullback.carrierEquiv⟩

/-- The inverse carrier equivalence projects to the first triplet point. -/
theorem carrierEquiv_symm_fst
    (T : Scheme.Pullback.Triplet f g) (p : Spec T.tensor) :
    (pullback.fst f g).base (Scheme.Pullback.carrierEquiv.symm ⟨T, p⟩) = T.x :=
  Scheme.Pullback.carrierEquiv_symm_fst T p

/-- The inverse carrier equivalence projects to the second triplet point. -/
theorem carrierEquiv_symm_snd
    (T : Scheme.Pullback.Triplet f g) (p : Spec T.tensor) :
    (pullback.snd f g).base (Scheme.Pullback.carrierEquiv.symm ⟨T, p⟩) = T.y :=
  Scheme.Pullback.carrierEquiv_symm_snd T p

/-- Every triplet has a point of the scheme pullback above its two points. -/
theorem triplet_exists_preimage
    (T : Scheme.Pullback.Triplet f g) :
    ∃ t : ↑(pullback f g),
      (pullback.fst f g).base t = T.x ∧
        (pullback.snd f g).base t = T.y :=
  T.exists_preimage

/-- Two points over the same base point lift to a point of the scheme pullback. -/
theorem exists_preimage_pullback
    (x : X) (y : Y) (h : f.base x = g.base y) :
    ∃ z : ↑(pullback f g),
      (pullback.fst f g).base z = x ∧
        (pullback.snd f g).base z = y :=
  Scheme.Pullback.exists_preimage_pullback x y h

/-- Range of the first projection from a scheme pullback. -/
theorem range_fst
    (f : X ⟶ S) (g : Y ⟶ S) :
    Set.range (pullback.fst f g).base = f.base ⁻¹' Set.range g.base :=
  Scheme.Pullback.range_fst f g

/-- Range of the second projection from a scheme pullback. -/
theorem range_snd
    (f : X ⟶ S) (g : Y ⟶ S) :
    Set.range (pullback.snd f g).base = g.base ⁻¹' Set.range f.base :=
  Scheme.Pullback.range_snd f g

/-- Range of the composite through the first projection from a scheme pullback. -/
theorem range_fst_comp
    (f : X ⟶ S) (g : Y ⟶ S) :
    Set.range (pullback.fst f g ≫ f).base =
      Set.range f.base ∩ Set.range g.base :=
  Scheme.Pullback.range_fst_comp f g

/-- Range of the composite through the second projection from a scheme pullback. -/
theorem range_snd_comp
    (f : X ⟶ S) (g : Y ⟶ S) :
    Set.range (pullback.snd f g ≫ g).base =
      Set.range f.base ∩ Set.range g.base :=
  Scheme.Pullback.range_snd_comp f g

/-- Range formula for the map between two scheme pullbacks. -/
theorem range_map
    {X' Y' S' : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (f' : X' ⟶ S') (g' : Y' ⟶ S') (i₁ : X ⟶ X')
    (i₂ : Y ⟶ Y') (i₃ : S ⟶ S')
    (e₁ : f ≫ i₃ = i₁ ≫ f') (e₂ : g ≫ i₃ = i₂ ≫ g') [Mono i₃] :
    Set.range (pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂).base =
      (pullback.fst f' g').base ⁻¹' Set.range i₁.base ∩
        (pullback.snd f' g').base ⁻¹' Set.range i₂.base :=
  Scheme.Pullback.range_map f g f' g' i₁ i₂ i₃ e₁ e₂

/-- Surjectivity of scheme morphisms is stable under base change. -/
theorem surjective_stableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange (@Surjective) :=
  inferInstance

end PullbackCarrier
end SourceStack
end HilbertTest

