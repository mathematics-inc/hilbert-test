import Mathlib.NumberTheory.FunctionField

/-!
Arithmetic function-field source wrappers.

This is the number-theoretic function-field API currently present in pinned
Mathlib: finite extensions of `Fq(t)`, their rings of integers, and the place at
infinity on `Fq(t)`.  It is not yet the algebraic-geometry function field of a
smooth proper curve, but it is a checked source layer for the affine
Dedekind-domain side of curve/function-field arguments.
-/

noncomputable section

open scoped nonZeroDivisors Polynomial Multiplicative

namespace HilbertTest
namespace SourceStack
namespace ArithmeticFunctionFields

universe u v w

/-- A function field over `Fq` is equivalently finite-dimensional over any chosen
fraction field of `Fq[X]`. -/
theorem functionField_iff_finiteDimensional
    (Fq : Type u) [Field Fq]
    (F : Type v) [Field F]
    (Fqt : Type w) [Field Fqt] [Algebra Fq[X] Fqt]
    [IsFractionRing Fq[X] Fqt]
    [Algebra (RatFunc Fq) F] [Algebra Fqt F] [Algebra Fq[X] F]
    [IsScalarTower Fq[X] Fqt F] [IsScalarTower Fq[X] (RatFunc Fq) F] :
    FunctionField Fq F ↔ FiniteDimensional Fqt F :=
  functionField_iff Fq F Fqt

/-- The polynomial algebra injects into a function field through `Fq(t)`. -/
theorem polynomial_algebraMap_injective
    (Fq : Type u) [Field Fq]
    (F : Type v) [Field F]
    [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
    [IsScalarTower Fq[X] (RatFunc Fq) F] :
    Function.Injective (algebraMap Fq[X] F) :=
  algebraMap_injective Fq F

namespace RingOfIntegers

/-- The function-field ring of integers is a domain. -/
theorem isDomain
    (Fq : Type u) [Field Fq]
    (F : Type v) [Field F] [Algebra Fq[X] F] :
    IsDomain (FunctionField.ringOfIntegers Fq F) :=
  inferInstance

/-- The polynomial algebra injects into the function-field ring of integers. -/
theorem algebraMap_injective
    (Fq : Type u) [Field Fq]
    (F : Type v) [Field F]
    [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
    [IsScalarTower Fq[X] (RatFunc Fq) F] :
    Function.Injective (algebraMap Fq[X] (FunctionField.ringOfIntegers Fq F)) :=
  FunctionField.ringOfIntegers.algebraMap_injective Fq F

/-- The function-field ring of integers is not a field. -/
theorem not_isField
    (Fq : Type u) [Field Fq]
    (F : Type v) [Field F]
    [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
    [IsScalarTower Fq[X] (RatFunc Fq) F] :
    ¬ IsField (FunctionField.ringOfIntegers Fq F) :=
  FunctionField.ringOfIntegers.not_isField Fq F

/-- For a function field, the ring of integers has fraction field `F`. -/
theorem isFractionRing
    (Fq : Type u) [Field Fq]
    (F : Type v) [Field F]
    [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
    [IsScalarTower Fq[X] (RatFunc Fq) F]
    [FunctionField Fq F] :
    IsFractionRing (FunctionField.ringOfIntegers Fq F) F :=
  inferInstance

/-- For a function field, the ring of integers is integrally closed. -/
theorem isIntegrallyClosed
    (Fq : Type u) [Field Fq]
    (F : Type v) [Field F]
    [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
    [IsScalarTower Fq[X] (RatFunc Fq) F]
    [FunctionField Fq F] :
    IsIntegrallyClosed (FunctionField.ringOfIntegers Fq F) :=
  inferInstance

/-- For a separable function field, the ring of integers is a Dedekind domain. -/
theorem isDedekindDomain
    (Fq : Type u) [Field Fq]
    (F : Type v) [Field F]
    [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
    [IsScalarTower Fq[X] (RatFunc Fq) F]
    [FunctionField Fq F] [Algebra.IsSeparable (RatFunc Fq) F] :
    IsDedekindDomain (FunctionField.ringOfIntegers Fq F) :=
  inferInstance

end RingOfIntegers

namespace InftyValuation

variable (Fq : Type u) [Field Fq] [DecidableEq (RatFunc Fq)]

/-- The valuation at infinity sends zero to zero. -/
theorem map_zero :
    FunctionField.inftyValuationDef Fq 0 = 0 :=
  FunctionField.InftyValuation.map_zero' Fq

/-- The valuation at infinity sends one to one. -/
theorem map_one :
    FunctionField.inftyValuationDef Fq 1 = 1 :=
  FunctionField.InftyValuation.map_one' Fq

/-- The valuation at infinity is multiplicative. -/
theorem map_mul
    (x y : RatFunc Fq) :
    FunctionField.inftyValuationDef Fq (x * y) =
      FunctionField.inftyValuationDef Fq x * FunctionField.inftyValuationDef Fq y :=
  FunctionField.InftyValuation.map_mul' Fq x y

/-- The valuation at infinity satisfies the nonarchimedean inequality. -/
theorem map_add_le_max
    (x y : RatFunc Fq) :
    FunctionField.inftyValuationDef Fq (x + y) ≤
      max (FunctionField.inftyValuationDef Fq x) (FunctionField.inftyValuationDef Fq y) :=
  FunctionField.InftyValuation.map_add_le_max' Fq x y

/-- Nonzero constants have valuation `ofAdd 0` at infinity. -/
theorem C
    {k : Fq} (hk : k ≠ 0) :
    FunctionField.inftyValuationDef Fq (RatFunc.C k) =
      Multiplicative.ofAdd (0 : ℤ) :=
  FunctionField.inftyValuation.C Fq hk

/-- The coordinate `X` has valuation `ofAdd 1` at infinity. -/
theorem X :
    FunctionField.inftyValuationDef Fq RatFunc.X =
      Multiplicative.ofAdd (1 : ℤ) :=
  FunctionField.inftyValuation.X Fq

/-- A nonzero polynomial has valuation equal to its degree at infinity. -/
theorem polynomial
    {p : Fq[X]} (hp : p ≠ 0) :
    FunctionField.inftyValuationDef Fq (algebraMap Fq[X] (RatFunc Fq) p) =
      Multiplicative.ofAdd (p.natDegree : ℤ) :=
  FunctionField.inftyValuation.polynomial Fq hp

/-- The completion at infinity carries a field structure. -/
theorem FqtInfty_field :
    Nonempty (Field (FunctionField.FqtInfty Fq)) :=
  ⟨inferInstance⟩

end InftyValuation

end ArithmeticFunctionFields
end SourceStack
end HilbertTest
