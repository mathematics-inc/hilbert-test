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

/-- On an integral scheme, germ maps to arbitrary stalks are injective. -/
theorem germ_injective_of_isIntegral
    [IsIntegral X] {U : X.Opens} (x : X) (hx : x ∈ U) :
    Function.Injective (X.presheaf.germ U x hx) :=
  AlgebraicGeometry.germ_injective_of_isIntegral X x hx

/-- The generic point of an irreducible scheme lies in every nonempty open. -/
theorem genericPoint_mem_open
    [IrreducibleSpace X] (U : X.Opens) [Nonempty U] :
    genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
    (by simpa using (inferInstance : Nonempty U))

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

/-- The function field of an affine integral scheme is the fraction field of its
coordinate ring. -/
theorem functionField_isFractionRing_of_affine
    (R : CommRingCat.{u}) [IsDomain R] :
    IsFractionRing R (Spec R).functionField :=
  AlgebraicGeometry.functionField_isFractionRing_of_affine R

/-- The generic point of an affine integral scheme is the bottom prime. -/
theorem genericPoint_eq_bot_of_affine
    (R : CommRingCat.{u}) [IsDomain R] :
    genericPoint (Spec R) = (⊥ : PrimeSpectrum R) :=
  AlgebraicGeometry.genericPoint_eq_bot_of_affine R

/-- Integral schemes remain integral on nonempty open subschemes. -/
theorem isIntegral_open
    [IsIntegral X] (U : X.Opens) [Nonempty U] :
    IsIntegral U :=
  inferInstance

/-- Stalks of an integral scheme have the scheme function field as their
fraction field. -/
theorem stalk_isFractionRing_functionField
    [IsIntegral X] (x : X) :
    IsFractionRing (X.presheaf.stalk x) X.functionField :=
  inferInstance

/-- The affine-open point associated to the generic point is the generic point of
the affine chart. -/
theorem primeIdealOf_genericPoint
    [IsIntegral X] {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    hU.primeIdealOf
        ⟨genericPoint X, genericPoint_mem_open (X := X) U⟩ =
      genericPoint (Spec Γ(X, U)) :=
  hU.primeIdealOf_genericPoint

/-- The section ring, stalk, and function field form the expected scalar tower. -/
theorem functionField_isScalarTower
    [IrreducibleSpace X] (U : X.Opens) (x : U) [Nonempty U] :
    IsScalarTower Γ(X, U) (X.presheaf.stalk x) X.functionField :=
  AlgebraicGeometry.functionField_isScalarTower X U x

/-- Open immersions of irreducible schemes identify generic points. -/
theorem genericPoint_eq_of_isOpenImmersion
    (f : X ⟶ Y) [IsOpenImmersion f]
    [IrreducibleSpace X] [IrreducibleSpace Y] :
    f.base (genericPoint X) = genericPoint Y :=
  AlgebraicGeometry.genericPoint_eq_of_isOpenImmersion f

end FunctionFields
end SourceStack
end HilbertTest
