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

section SchemeProjectiveLineTarget

open SchemeProjectiveLine

variable (K : Type u) [CommRing K]
variable {X : Scheme.{u}}

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
