import Mathlib.AlgebraicGeometry.RationalMap
import HilbertTest.SourceStack.SchemeProjectiveLine

/-!
Rational-map source wrappers for the curve/function-field part of the Belyi
formalization.  These expose the Mathlib facts currently available before the
missing divisor/Riemann-Roch curve layer.
-/

noncomputable section

open CategoryTheory

namespace HilbertTest
namespace SourceStack
namespace RationalMaps

open AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

/-- The partial map associated to an honest morphism is defined on all of the
source. -/
theorem hom_toPartialMap_domain
    (f : X ⟶ Y) :
    f.toPartialMap.domain = ⊤ :=
  rfl

/-- The morphism underlying the partial map associated to an honest morphism is
the top-open identification followed by the original morphism. -/
theorem hom_toPartialMap_hom
    (f : X ⟶ Y) :
    f.toPartialMap.hom = X.topIso.hom ≫ f :=
  rfl

/-- On any stalk, the partial map associated to an honest morphism restricts to
the canonical stalk-spectrum map followed by the original morphism. -/
theorem hom_toPartialMap_fromSpecStalkOfMem
    (f : X ⟶ Y) (x : X) :
    f.toPartialMap.fromSpecStalkOfMem (x := x) trivial =
      X.fromSpecStalk x ≫ f :=
  Scheme.PartialMap.fromSpecStalkOfMem_toPartialMap f x

/-- An honest morphism over a base gives a partial map over the same base. -/
theorem hom_toPartialMap_isOver
    {S : Scheme.{u}} [X.Over S] [Y.Over S] (f : X ⟶ Y) [f.IsOver S] :
    f.toPartialMap.IsOver S := by
  infer_instance

/-- An honest morphism over a base gives a rational map over the same base. -/
theorem hom_toRationalMap_isOver
    {S : Scheme.{u}} [X.Over S] [Y.Over S] (f : X ⟶ Y) [f.IsOver S] :
    f.toRationalMap.IsOver S := by
  infer_instance

/-- On the function field, the partial map associated to an honest morphism is
the canonical generic stalk-spectrum map followed by the original morphism. -/
theorem hom_toPartialMap_fromFunctionField
    [IrreducibleSpace X] (f : X ⟶ Y) :
    f.toPartialMap.fromFunctionField = X.fromSpecStalk _ ≫ f := by
  unfold Scheme.PartialMap.fromFunctionField
  rw [Scheme.PartialMap.fromSpecStalkOfMem_toPartialMap]

/-- On the function field, the rational map associated to an honest morphism is
the canonical generic stalk-spectrum map followed by the original morphism. -/
theorem hom_toRationalMap_fromFunctionField
    [IrreducibleSpace X] (f : X ⟶ Y) :
    f.toRationalMap.fromFunctionField = X.fromSpecStalk _ ≫ f := by
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap]
  exact hom_toPartialMap_fromFunctionField f

/-- Every rational map has a partial-map representative. -/
theorem partialMap_toRationalMap_surjective :
    Function.Surjective (@Scheme.PartialMap.toRationalMap X Y) :=
  Scheme.PartialMap.toRationalMap_surjective

/-- A rational map has a representative as a partial map. -/
theorem rationalMap_exists_rep
    (f : X ⤏ Y) :
    ∃ g : X.PartialMap Y, g.toRationalMap = f :=
  f.exists_rep

/-- Equality of rational maps is equivalence of partial-map representatives. -/
theorem partialMap_toRationalMap_eq_iff
    {f g : X.PartialMap Y} :
    f.toRationalMap = g.toRationalMap ↔ f.equiv g :=
  Scheme.PartialMap.toRationalMap_eq_iff

/-- A partial map is defined on a dense open subscheme. -/
theorem partialMap_dense_domain
    (f : X.PartialMap Y) :
    Dense (f.domain : Set X) :=
  f.dense_domain

/-- A rational map has a dense domain of definition. -/
theorem rationalMap_dense_domain
    (f : X ⤏ Y) :
    Dense (f.domain : Set X) :=
  f.dense_domain

/-- For a reduced source and separated target, the canonical partial map
representing a rational map maps back to the same rational map. -/
theorem rationalMap_toRationalMap_toPartialMap
    [IsReduced X] [Y.IsSeparated] (f : X ⤏ Y) :
    f.toPartialMap.toRationalMap = f :=
  f.toRationalMap_toPartialMap

/-- The canonical partial-map representative of a rational map is defined on
the rational map's domain of definition. -/
theorem rationalMap_toPartialMap_domain
    [IsReduced X] [Y.IsSeparated] (f : X ⤏ Y) :
    f.toPartialMap.domain = f.domain :=
  rfl

/-- Restricting a partial map to a smaller dense open does not change its
induced map from the function field. -/
theorem partialMap_fromFunctionField_restrict
    [IrreducibleSpace X] (f : X.PartialMap Y)
    {U : X.Opens} (hU : Dense (U : Set X)) (hU' : U ≤ f.domain) :
    (f.restrict U hU hU').fromFunctionField = f.fromFunctionField :=
  f.fromFunctionField_restrict hU hU'

/-- The function-field map associated to a partial-map representative agrees
with the one associated to its rational-map class. -/
theorem rationalMap_fromFunctionField_toRationalMap
    [IrreducibleSpace X] (f : X.PartialMap Y) :
    f.toRationalMap.fromFunctionField = f.fromFunctionField :=
  Scheme.RationalMap.fromFunctionField_toRationalMap f

/-- A rational map out of an integral scheme is determined by its map from the
function field. -/
theorem rationalMap_eq_of_fromFunctionField_eq
    [IsIntegral X] (f g : X ⤏ Y)
    (H : f.fromFunctionField = g.fromFunctionField) :
    f = g :=
  Scheme.RationalMap.eq_of_fromFunctionField_eq f g H

/-- Spreading a function-field map to a rational map recovers the original map
on the function field. -/
theorem rationalMap_fromFunctionField_ofFunctionField
    {S : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
    [IsIntegral X] [LocallyOfFiniteType sY]
    (f : Spec X.functionField ⟶ Y)
    (h : f ≫ sY = X.fromSpecStalk _ ≫ sX) :
    (Scheme.RationalMap.ofFunctionField sX sY f h).fromFunctionField = f :=
  Scheme.RationalMap.fromFunctionField_ofFunctionField sX sY f h

/-- The function-field spreading construction lies over the chosen base. -/
theorem rationalMap_ofFunctionField_compHom
    {S : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
    [IsIntegral X] [LocallyOfFiniteType sY]
    (f : Spec X.functionField ⟶ Y)
    (h : f ≫ sY = X.fromSpecStalk _ ≫ sX) :
    (Scheme.RationalMap.ofFunctionField sX sY f h).compHom sY =
      sX.toRationalMap :=
  (Scheme.RationalMap.equivFunctionField sX sY ⟨f, h⟩).2

/-- The Mathlib equivalence between base-compatible maps from the function
field and base-compatible rational maps. -/
noncomputable def rationalMap_equivFunctionField
    {S : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
    [IsIntegral X] [LocallyOfFiniteType sY] :
    { f : Spec X.functionField ⟶ Y // f ≫ sY = X.fromSpecStalk _ ≫ sX } ≃
      { f : X ⤏ Y // f.compHom sY = sX.toRationalMap } :=
  Scheme.RationalMap.equivFunctionField sX sY

/-- Applying the function-field/rational-map equivalence is the usual
spreading construction. -/
theorem rationalMap_equivFunctionField_apply
    {S : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
    [IsIntegral X] [LocallyOfFiniteType sY]
    (f : Spec X.functionField ⟶ Y)
    (h : f ≫ sY = X.fromSpecStalk _ ≫ sX) :
    ((rationalMap_equivFunctionField sX sY) ⟨f, h⟩).1 =
      Scheme.RationalMap.ofFunctionField sX sY f h :=
  rfl

/-- Applying the inverse function-field/rational-map equivalence takes a
rational map to its map from the function field. -/
theorem rationalMap_equivFunctionField_symm_apply
    {S : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
    [IsIntegral X] [LocallyOfFiniteType sY]
    (f : X ⤏ Y)
    (h : f.compHom sY = sX.toRationalMap) :
    ((rationalMap_equivFunctionField sX sY).symm ⟨f, h⟩).1 =
      f.fromFunctionField :=
  rfl

/-- The function-field/rational-map equivalence is left-inverse to its
inverse on function-field morphisms. -/
theorem rationalMap_equivFunctionField_left_inv
    {S : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
    [IsIntegral X] [LocallyOfFiniteType sY]
    (f : { f : Spec X.functionField ⟶ Y // f ≫ sY = X.fromSpecStalk _ ≫ sX }) :
    (rationalMap_equivFunctionField sX sY).symm
        ((rationalMap_equivFunctionField sX sY) f) = f :=
  (rationalMap_equivFunctionField sX sY).left_inv f

/-- The function-field/rational-map equivalence is right-inverse to its
inverse on rational maps. -/
theorem rationalMap_equivFunctionField_right_inv
    {S : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
    [IsIntegral X] [LocallyOfFiniteType sY]
    (f : { f : X ⤏ Y // f.compHom sY = sX.toRationalMap }) :
    (rationalMap_equivFunctionField sX sY)
        ((rationalMap_equivFunctionField sX sY).symm f) = f :=
  (rationalMap_equivFunctionField sX sY).right_inv f

/-- Over-scheme form of the function-field/rational-map equivalence. -/
noncomputable def rationalMap_equivFunctionFieldOver
    {S : Scheme.{u}} [X.Over S] [Y.Over S]
    [IsIntegral X] [LocallyOfFiniteType (Y ↘ S)] :
    { f : Spec X.functionField ⟶ Y // f.IsOver S } ≃
      { f : X ⤏ Y // f.IsOver S } :=
  Scheme.RationalMap.equivFunctionFieldOver (X := X) (Y := Y) (S := S)

/-- The over-scheme function-field/rational-map equivalence is left-inverse to
its inverse on over-morphisms from the function field. -/
theorem rationalMap_equivFunctionFieldOver_left_inv
    {S : Scheme.{u}} [X.Over S] [Y.Over S]
    [IsIntegral X] [LocallyOfFiniteType (Y ↘ S)]
    (f : { f : Spec X.functionField ⟶ Y // f.IsOver S }) :
    (rationalMap_equivFunctionFieldOver (X := X) (Y := Y) (S := S)).symm
        ((rationalMap_equivFunctionFieldOver (X := X) (Y := Y) (S := S)) f) = f :=
  (rationalMap_equivFunctionFieldOver (X := X) (Y := Y) (S := S)).left_inv f

/-- The over-scheme function-field/rational-map equivalence is right-inverse to
its inverse on over-rational maps. -/
theorem rationalMap_equivFunctionFieldOver_right_inv
    {S : Scheme.{u}} [X.Over S] [Y.Over S]
    [IsIntegral X] [LocallyOfFiniteType (Y ↘ S)]
    (f : { f : X ⤏ Y // f.IsOver S }) :
    (rationalMap_equivFunctionFieldOver (X := X) (Y := Y) (S := S))
        ((rationalMap_equivFunctionFieldOver (X := X) (Y := Y) (S := S)).symm f) = f :=
  (rationalMap_equivFunctionFieldOver (X := X) (Y := Y) (S := S)).right_inv f

/-- A partial map is over the base exactly when its right-composition with
the target structure morphism agrees with the source structure morphism on
the dense domain. -/
theorem partialMap_isOver_iff
    {S : Scheme.{u}} [X.Over S] [Y.Over S] {f : X.PartialMap Y} :
    f.IsOver S ↔ (f.compHom (Y ↘ S)).hom = f.domain.ι ≫ X ↘ S :=
  Scheme.PartialMap.isOver_iff

/-- Equivalent partial-map-over-base criterion as equality with the restricted
source structure morphism. -/
theorem partialMap_isOver_iff_eq_restrict
    {S : Scheme.{u}} [X.Over S] [Y.Over S] {f : X.PartialMap Y} :
    f.IsOver S ↔
      f.compHom (Y ↘ S) = (X ↘ S).toPartialMap.restrict _ f.dense_domain (by simp) :=
  Scheme.PartialMap.isOver_iff_eq_restrict

/-- A rational map over the base has a partial-map representative over the
same base. -/
theorem rationalMap_exists_partialMap_over
    {S : Scheme.{u}} [X.Over S] [Y.Over S] (f : X ⤏ Y) [f.IsOver S] :
    ∃ g : X.PartialMap Y, g.IsOver S ∧ g.toRationalMap = f :=
  Scheme.RationalMap.exists_partialMap_over S f

/-- If a partial map represents an over rational map, then some restriction of
the partial map is itself over the base. -/
theorem partialMap_exists_restrict_isOver
    {S : Scheme.{u}} [X.Over S] [Y.Over S] (f : X.PartialMap Y)
    [f.toRationalMap.IsOver S] :
    ∃ U hU hU', (f.restrict U hU hU').IsOver S :=
  Scheme.PartialMap.exists_restrict_isOver S f

/-- Right-composition of an over partial map with an over morphism remains
over the base. -/
theorem partialMap_compHom_isOver
    {S Z : Scheme.{u}} [X.Over S] [Y.Over S] [Z.Over S]
    (f : X.PartialMap Y) (g : Y ⟶ Z) [f.IsOver S] [g.IsOver S] :
    (f.compHom g).IsOver S := by
  infer_instance

/-- Right-composition of an over rational map with an over morphism remains
over the base. -/
theorem rationalMap_compHom_isOver
    {S Z : Scheme.{u}} [X.Over S] [Y.Over S] [Z.Over S]
    (f : X ⤏ Y) (g : Y ⟶ Z) [f.IsOver S] [g.IsOver S] :
    (f.compHom g).IsOver S := by
  infer_instance

/-- Right-composition of a rational map composes its induced function-field
morphism with the target morphism. -/
theorem rationalMap_fromFunctionField_compHom
    [IrreducibleSpace X] {Z : Scheme.{u}} (f : X ⤏ Y) (g : Y ⟶ Z) :
    (f.compHom g).fromFunctionField = f.fromFunctionField ≫ g := by
  obtain ⟨f, rfl⟩ := f.exists_rep
  exact Scheme.PartialMap.fromSpecStalkOfMem_compHom f g _ _

/-- If a rational map is represented by a partial map, then composing the
rational-map class on the right composes the representative's function-field
morphism. -/
theorem rationalMap_fromFunctionField_toRationalMap_compHom
    [IrreducibleSpace X] {Z : Scheme.{u}} (f : X.PartialMap Y) (g : Y ⟶ Z) :
    (f.toRationalMap.compHom g).fromFunctionField = f.fromFunctionField ≫ g := by
  rw [← Scheme.RationalMap.compHom_toRationalMap]
  exact Scheme.PartialMap.fromSpecStalkOfMem_compHom f g _ _

/-- A rational map is over the base exactly when composing it with the target
structure morphism gives the source structure morphism as a rational map. -/
theorem rationalMap_isOver_iff
    {S : Scheme.{u}} [X.Over S] [Y.Over S] {f : X ⤏ Y} :
    f.IsOver S ↔ f.compHom (Y ↘ S) = (X ↘ S).toRationalMap :=
  Scheme.RationalMap.isOver_iff

/-- For a reduced source and separated base, a partial map is over the base
exactly when its rational-map class is over the base. -/
theorem partialMap_isOver_toRationalMap_iff_of_isSeparated
    {S : Scheme.{u}} [X.Over S] [Y.Over S] [IsReduced X] [S.IsSeparated]
    {f : X.PartialMap Y} :
    f.toRationalMap.IsOver S ↔ f.IsOver S :=
  Scheme.PartialMap.isOver_toRationalMap_iff_of_isSeparated

/-- The canonical partial-map representative of an over rational map is over
the base when the source is reduced and the target/base are separated. -/
theorem rationalMap_toPartialMap_isOver
    {S : Scheme.{u}} [IsReduced X] [Y.IsSeparated] [S.IsSeparated]
    [X.Over S] [Y.Over S] (f : X ⤏ Y) [f.IsOver S] :
    f.toPartialMap.IsOver S := by
  infer_instance

section SchemeProjectiveLineTarget

open SchemeProjectiveLine

variable (K : Type u) [CommRing K]
variable {X : Scheme.{u}}

/-- The partial map associated to an honest morphism to `P1 K` is defined on
all of the source. -/
theorem p1Hom_toPartialMap_domain
    (f : X ⟶ P1 K) :
    f.toPartialMap.domain = ⊤ :=
  hom_toPartialMap_domain f

/-- An honest morphism to `P1 K` over a base gives a partial map over that
base. -/
theorem p1Hom_toPartialMap_isOver
    {S : Scheme.{u}} [X.Over S] [(P1 K).Over S]
    (f : X ⟶ P1 K) [f.IsOver S] :
    f.toPartialMap.IsOver S :=
  hom_toPartialMap_isOver f

/-- An honest morphism to `P1 K` over a base gives a rational map over that
base. -/
theorem p1Hom_toRationalMap_isOver
    {S : Scheme.{u}} [X.Over S] [(P1 K).Over S]
    (f : X ⟶ P1 K) [f.IsOver S] :
    f.toRationalMap.IsOver S :=
  hom_toRationalMap_isOver f

/-- On the function field, the partial map associated to an honest morphism to
`P1 K` is the canonical generic stalk-spectrum map followed by the original
morphism. -/
theorem p1Hom_toPartialMap_fromFunctionField
    [IrreducibleSpace X] (f : X ⟶ P1 K) :
    f.toPartialMap.fromFunctionField = X.fromSpecStalk _ ≫ f :=
  hom_toPartialMap_fromFunctionField f

/-- On the function field, the rational map associated to an honest morphism to
`P1 K` is the canonical generic stalk-spectrum map followed by the original
morphism. -/
theorem p1Hom_toRationalMap_fromFunctionField
    [IrreducibleSpace X] (f : X ⟶ P1 K) :
    f.toRationalMap.fromFunctionField = X.fromSpecStalk _ ≫ f :=
  hom_toRationalMap_fromFunctionField f

/-- A rational map to the scheme-theoretic projective line has a partial-map
representative. -/
theorem p1RationalMap_exists_rep
    (f : X ⤏ P1 K) :
    ∃ g : X.PartialMap (P1 K), g.toRationalMap = f :=
  rationalMap_exists_rep f

/-- Equality of rational maps to `P1 K` is equivalence of partial-map
representatives. -/
theorem p1PartialMap_toRationalMap_eq_iff
    {f g : X.PartialMap (P1 K)} :
    f.toRationalMap = g.toRationalMap ↔ f.equiv g :=
  partialMap_toRationalMap_eq_iff

/-- A partial map to `P1 K` is defined on a dense open subscheme. -/
theorem p1PartialMap_dense_domain
    (f : X.PartialMap (P1 K)) :
    Dense (f.domain : Set X) :=
  partialMap_dense_domain f

/-- A rational map to `P1 K` has a dense domain of definition. -/
theorem p1RationalMap_dense_domain
    (f : X ⤏ P1 K) :
    Dense (f.domain : Set X) :=
  rationalMap_dense_domain f

/-- For a reduced source, the canonical partial-map representative of a
rational map to `P1 K` maps back to the same rational map. -/
theorem p1RationalMap_toRationalMap_toPartialMap
    [IsReduced X] (f : X ⤏ P1 K) :
    f.toPartialMap.toRationalMap = f :=
  rationalMap_toRationalMap_toPartialMap f

/-- The canonical partial-map representative of a rational map to `P1 K` is
defined on the rational map's domain of definition. -/
theorem p1RationalMap_toPartialMap_domain
    [IsReduced X] (f : X ⤏ P1 K) :
    f.toPartialMap.domain = f.domain :=
  rationalMap_toPartialMap_domain f

/-- A partial map to `P1 K` is over a base exactly when its composition with
the target structure morphism agrees with the source structure morphism on the
dense domain. -/
theorem p1PartialMap_isOver_iff
    {S : Scheme.{u}} [X.Over S] [(P1 K).Over S]
    {f : X.PartialMap (P1 K)} :
    f.IsOver S ↔ (f.compHom (P1 K ↘ S)).hom = f.domain.ι ≫ X ↘ S :=
  partialMap_isOver_iff

/-- A rational map to `P1 K` over a base has a partial-map representative over
the same base. -/
theorem p1RationalMap_exists_partialMap_over
    {S : Scheme.{u}} [X.Over S] [(P1 K).Over S]
    (f : X ⤏ P1 K) [f.IsOver S] :
    ∃ g : X.PartialMap (P1 K), g.IsOver S ∧ g.toRationalMap = f :=
  rationalMap_exists_partialMap_over f

/-- A rational map to `P1 K` is over the base exactly when composing with the
target structure morphism gives the source structure rational map. -/
theorem p1RationalMap_isOver_iff
    {S : Scheme.{u}} [X.Over S] [(P1 K).Over S] {f : X ⤏ P1 K} :
    f.IsOver S ↔ f.compHom (P1 K ↘ S) = (X ↘ S).toRationalMap :=
  rationalMap_isOver_iff

/-- For a reduced source and separated base, a partial map to `P1 K` is over
the base exactly when its rational-map class is over the base. -/
theorem p1PartialMap_isOver_toRationalMap_iff_of_isSeparated
    {S : Scheme.{u}} [X.Over S] [(P1 K).Over S] [IsReduced X] [S.IsSeparated]
    {f : X.PartialMap (P1 K)} :
    f.toRationalMap.IsOver S ↔ f.IsOver S :=
  partialMap_isOver_toRationalMap_iff_of_isSeparated

/-- The canonical partial-map representative of an over rational map to `P1 K`
is over the base under the separatedness hypotheses. -/
theorem p1RationalMap_toPartialMap_isOver
    {S : Scheme.{u}} [IsReduced X] [S.IsSeparated] [X.Over S] [(P1 K).Over S]
    (f : X ⤏ P1 K) [f.IsOver S] :
    f.toPartialMap.IsOver S :=
  rationalMap_toPartialMap_isOver f

/-- Restricting a partial map to `P1 K` to a smaller dense open does not change
its induced map from the function field. -/
theorem p1PartialMap_fromFunctionField_restrict
    [IrreducibleSpace X] (f : X.PartialMap (P1 K))
    {U : X.Opens} (hU : Dense (U : Set X)) (hU' : U ≤ f.domain) :
    (f.restrict U hU hU').fromFunctionField = f.fromFunctionField :=
  partialMap_fromFunctionField_restrict f hU hU'

/-- Restricting a partial map to `P1 K` changes its domain to the chosen dense
open. -/
theorem p1PartialMap_restrict_domain
    (f : X.PartialMap (P1 K))
    {U : X.Opens} (hU : Dense (U : Set X)) (hU' : U ≤ f.domain) :
    (f.restrict U hU hU').domain = U :=
  rfl

/-- The morphism underlying a restricted partial map to `P1 K` is obtained by
precomposing with the inclusion of dense opens. -/
theorem p1PartialMap_restrict_hom
    (f : X.PartialMap (P1 K))
    {U : X.Opens} (hU : Dense (U : Set X)) (hU' : U ≤ f.domain) :
    (f.restrict U hU hU').hom = X.homOfLE hU' ≫ f.hom :=
  rfl

/-- Restricting a partial map to `P1 K` to its own domain does not change it. -/
theorem p1PartialMap_restrict_id
    (f : X.PartialMap (P1 K)) :
    f.restrict f.domain f.dense_domain le_rfl = f :=
  Scheme.PartialMap.restrict_id f

/-- A partial map's domain is contained in the domain of its rational-map class,
specialized to target `P1 K`. -/
theorem p1PartialMap_le_domain_toRationalMap
    (f : X.PartialMap (P1 K)) :
    f.domain ≤ f.toRationalMap.domain :=
  Scheme.PartialMap.le_domain_toRationalMap f

/-- Membership in the domain of a rational map to `P1 K` is witnessed by a
partial-map representative defined at that point. -/
theorem p1RationalMap_mem_domain
    {f : X ⤏ P1 K} {x : X} :
    x ∈ f.domain ↔ ∃ g : X.PartialMap (P1 K), x ∈ g.domain ∧ g.toRationalMap = f :=
  Scheme.RationalMap.mem_domain

/-- The underlying continuous map from the dense domain of a partial map to
`P1 K`. -/
noncomputable def p1PartialMapDomainMap
    (f : X.PartialMap (P1 K)) :
    f.domain → P1 K :=
  f.hom.base

theorem p1PartialMapDomainMap_apply
    (f : X.PartialMap (P1 K)) (x : f.domain) :
    p1PartialMapDomainMap K f x = f.hom.base x :=
  rfl

theorem continuous_p1PartialMapDomainMap
    (f : X.PartialMap (P1 K)) :
    Continuous (p1PartialMapDomainMap K f) :=
  f.hom.continuous

/-- Composing a partial map to `P1 K` with an honest morphism on the right does
not change the partial-map domain. -/
theorem p1PartialMap_compHom_domain
    {Z : Scheme.{u}} (f : X.PartialMap (P1 K)) (g : P1 K ⟶ Z) :
    (f.compHom g).domain = f.domain :=
  rfl

/-- The morphism underlying a right-composition of a partial map to `P1 K` is
the composition of the underlying morphisms. -/
theorem p1PartialMap_compHom_hom
    {Z : Scheme.{u}} (f : X.PartialMap (P1 K)) (g : P1 K ⟶ Z) :
    (f.compHom g).hom = f.hom ≫ g :=
  rfl

/-- Right-composition of a partial map to `P1 K` represents the
right-composition of its rational-map class. -/
theorem p1PartialMap_compHom_toRationalMap
    {Z : Scheme.{u}} (f : X.PartialMap (P1 K)) (g : P1 K ⟶ Z) :
    (f.compHom g).toRationalMap = f.toRationalMap.compHom g :=
  Scheme.RationalMap.compHom_toRationalMap f g

/-- At a point in the domain of a partial map to `P1 K`, the induced map from
`Spec O_{X,x}` is the canonical local map followed by the underlying morphism. -/
theorem p1PartialMap_fromSpecStalkOfMem_eq
    (f : X.PartialMap (P1 K)) {x : X} (hx : x ∈ f.domain) :
    f.fromSpecStalkOfMem hx =
      f.domain.fromSpecStalkOfMem x hx ≫ f.hom :=
  rfl

/-- Restricting a partial map to `P1 K` to a smaller dense open does not change
the induced local map from `Spec O_{X,x}` at points of the smaller open. -/
theorem p1PartialMap_fromSpecStalkOfMem_restrict
    (f : X.PartialMap (P1 K))
    {U : X.Opens} (hU : Dense (U : Set X)) (hU' : U ≤ f.domain)
    {x : X} (hx : x ∈ U) :
    (f.restrict U hU hU').fromSpecStalkOfMem hx =
      f.fromSpecStalkOfMem (hU' hx) :=
  Scheme.PartialMap.fromSpecStalkOfMem_restrict f hU hU' hx

/-- Right-composition of a partial map to `P1 K` composes the induced local map
from `Spec O_{X,x}` with the target morphism. -/
theorem p1PartialMap_fromSpecStalkOfMem_compHom
    {Z : Scheme.{u}} (f : X.PartialMap (P1 K)) (g : P1 K ⟶ Z)
    {x : X} (hx : x ∈ f.domain) :
    (f.compHom g).fromSpecStalkOfMem hx =
      f.fromSpecStalkOfMem hx ≫ g :=
  Scheme.PartialMap.fromSpecStalkOfMem_compHom f g x hx

/-- Right-composition of a partial map to `P1 K` composes the induced
function-field map with the target morphism. -/
theorem p1PartialMap_fromFunctionField_compHom
    [IrreducibleSpace X]
    {Z : Scheme.{u}} (f : X.PartialMap (P1 K)) (g : P1 K ⟶ Z) :
    (f.compHom g).fromFunctionField = f.fromFunctionField ≫ g :=
  Scheme.PartialMap.fromSpecStalkOfMem_compHom f g _ _

/-- Right-composition of a rational map to `P1 K` composes its induced
function-field morphism with the target morphism. -/
theorem p1RationalMap_fromFunctionField_compHom
    [IrreducibleSpace X]
    {Z : Scheme.{u}} (f : X ⤏ P1 K) (g : P1 K ⟶ Z) :
    (f.compHom g).fromFunctionField = f.fromFunctionField ≫ g :=
  rationalMap_fromFunctionField_compHom f g

/-- If a rational map to `P1 K` is represented by a partial map, then composing
the rational-map class on the right composes the representative's
function-field morphism. -/
theorem p1RationalMap_fromFunctionField_toRationalMap_compHom
    [IrreducibleSpace X]
    {Z : Scheme.{u}} (f : X.PartialMap (P1 K)) (g : P1 K ⟶ Z) :
    (f.toRationalMap.compHom g).fromFunctionField = f.fromFunctionField ≫ g :=
  rationalMap_fromFunctionField_toRationalMap_compHom f g

/-- The function-field map associated to a partial map to `P1 K` agrees with
the one associated to its rational-map class. -/
theorem p1RationalMap_fromFunctionField_toRationalMap
    [IrreducibleSpace X] (f : X.PartialMap (P1 K)) :
    f.toRationalMap.fromFunctionField = f.fromFunctionField :=
  rationalMap_fromFunctionField_toRationalMap f

/-- A rational map from an integral scheme to `P1 K` is determined by its map
from the function field. -/
theorem p1RationalMap_eq_of_fromFunctionField_eq
    [IsIntegral X] (f g : X ⤏ P1 K)
    (H : f.fromFunctionField = g.fromFunctionField) :
    f = g :=
  rationalMap_eq_of_fromFunctionField_eq f g H

end SchemeProjectiveLineTarget

end RationalMaps
end SourceStack
end HilbertTest
