import Mathlib.AlgebraicGeometry.RationalMap

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

end RationalMaps
end SourceStack
end HilbertTest
