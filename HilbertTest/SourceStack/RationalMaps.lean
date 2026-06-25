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

end RationalMaps
end SourceStack
end HilbertTest
