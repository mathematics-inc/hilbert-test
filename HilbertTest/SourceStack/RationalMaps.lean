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
