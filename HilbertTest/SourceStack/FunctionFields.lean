import Mathlib.AlgebraicGeometry.FunctionField

/-!
Function-field source wrappers for the curve/rational-function layer.
-/

noncomputable section

open CategoryTheory

namespace HilbertTest
namespace SourceStack
namespace FunctionFields

open AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

/-- On an integral scheme, sections over a nonempty open inject into the
function field. -/
theorem germToFunctionField_injective
    [IsIntegral X] (U : X.Opens) [Nonempty U] :
    Function.Injective (X.germToFunctionField U) :=
  X.germToFunctionField_injective U

/-- On an integral scheme, an affine nonempty open has the scheme function field
as the fraction field of its coordinate ring. -/
theorem functionField_isFractionRing_of_isAffineOpen
    [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    IsFractionRing Γ(X, U) X.functionField :=
  AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen X U hU

/-- Open immersions of irreducible schemes identify generic points. -/
theorem genericPoint_eq_of_isOpenImmersion
    (f : X ⟶ Y) [IsOpenImmersion f]
    [IrreducibleSpace X] [IrreducibleSpace Y] :
    f.base (genericPoint X) = genericPoint Y :=
  AlgebraicGeometry.genericPoint_eq_of_isOpenImmersion f

end FunctionFields
end SourceStack
end HilbertTest
