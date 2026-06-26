import HilbertTest.SourceStack.P1PolynomialSeparation

/-!
Finite forbidden target values for the polynomial step in Lemma 2.4.

The polynomial separation layers above assume a selected value `p(beta)` outside
the replacement set and outside the affine branch values `0` and `1`.  This file
checks the finite-set part of that choice: the forbidden values form a finite
set, hence an infinite field has values outside it.  It also provides the
constructor that converts a proof that `p(beta)` avoids this forbidden set into
the `P1PolynomialSeparationStep` package.
-/

noncomputable section

open scoped Polynomial

namespace HilbertTest
namespace SourceStack
namespace PolynomialTargetAvoidance

open P1PolynomialSeparation
open PolynomialMaps

universe u v

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]

/-- The affine branch values `0` and `1`, i.e. the finite affine part of
`{0,1,infinity}`. -/
def affineBranchValueSet : Set E :=
  ({0, 1} : Set E)

theorem mem_affineBranchValueSet_iff (y : E) :
    y ∈ affineBranchValueSet E ↔ y = 0 ∨ y = 1 := by
  simp [affineBranchValueSet]

theorem affineBranchValueSet_finite :
    (affineBranchValueSet E).Finite := by
  simp [affineBranchValueSet]

/-- The finite forbidden target set for the polynomial step:
replacement values together with the affine branch values `0` and `1`. -/
def forbiddenTargetSet (S : Set E) (p : F[X]) : Set E :=
  replacementSet F E S p ∪ affineBranchValueSet E

theorem forbiddenTargetSet_finite
    {S : Set E} (hS : S.Finite) (p : F[X]) :
    (forbiddenTargetSet F E S p).Finite :=
  (replacementSet_finite F E hS p).union (affineBranchValueSet_finite E)

theorem mem_forbiddenTargetSet_iff
    {S : Set E} (p : F[X]) (y : E) :
    y ∈ forbiddenTargetSet F E S p ↔
      y ∈ replacementSet F E S p ∨ y = 0 ∨ y = 1 := by
  simp [forbiddenTargetSet, affineBranchValueSet, or_left_comm, or_assoc, or_comm]

theorem not_mem_forbiddenTargetSet_iff
    {S : Set E} (p : F[X]) (y : E) :
    y ∉ forbiddenTargetSet F E S p ↔
      y ∉ replacementSet F E S p ∧ y ≠ 0 ∧ y ≠ 1 := by
  simp [forbiddenTargetSet, affineBranchValueSet, and_left_comm, and_assoc, and_comm]

theorem exists_target_not_mem_forbiddenTargetSet
    [Infinite E] {S : Set E} (hS : S.Finite) (p : F[X]) :
    ∃ y : E, y ∉ forbiddenTargetSet F E S p :=
  (forbiddenTargetSet_finite F E hS p).exists_not_mem

theorem target_not_mem_replacement_of_not_mem_forbiddenTargetSet
    {S : Set E} {p : F[X]} {y : E}
    (hy : y ∉ forbiddenTargetSet F E S p) :
    y ∉ replacementSet F E S p :=
  ((not_mem_forbiddenTargetSet_iff F E p y).1 hy).1

theorem target_ne_zero_of_not_mem_forbiddenTargetSet
    {S : Set E} {p : F[X]} {y : E}
    (hy : y ∉ forbiddenTargetSet F E S p) :
    y ≠ 0 :=
  ((not_mem_forbiddenTargetSet_iff F E p y).1 hy).2.1

theorem target_ne_one_of_not_mem_forbiddenTargetSet
    {S : Set E} {p : F[X]} {y : E}
    (hy : y ∉ forbiddenTargetSet F E S p) :
    y ≠ 1 :=
  ((not_mem_forbiddenTargetSet_iff F E p y).1 hy).2.2

/-- Convert a selected polynomial value outside the finite forbidden set into
the affine-chart `P1` polynomial-separation package. -/
def toP1PolynomialSeparationStep
    {S : Set E} {β : E}
    (p : F[X]) (hpder : p.derivative ≠ 0)
    (hβ : Polynomial.aeval β p ∉ forbiddenTargetSet F E S p) :
    P1PolynomialSeparationStep F E S β := by
  have havoid :=
    (not_mem_forbiddenTargetSet_iff F E p (Polynomial.aeval β p)).1 hβ
  exact
    { polynomial := p
      derivative_ne_zero := hpder
      target_not_mem_replacement := havoid.1
      target_ne_zero := havoid.2.1
      target_ne_one := havoid.2.2 }

theorem toP1PolynomialSeparationStep_polynomial
    {S : Set E} {β : E}
    (p : F[X]) (hpder : p.derivative ≠ 0)
    (hβ : Polynomial.aeval β p ∉ forbiddenTargetSet F E S p) :
    (toP1PolynomialSeparationStep F E p hpder hβ).polynomial = p :=
  rfl

theorem toP1PolynomialSeparationStep_target_not_mem_replacement
    {S : Set E} {β : E}
    (p : F[X]) (hpder : p.derivative ≠ 0)
    (hβ : Polynomial.aeval β p ∉ forbiddenTargetSet F E S p) :
    Polynomial.aeval β p ∉ replacementSet F E S p :=
  (toP1PolynomialSeparationStep F E p hpder hβ).target_not_mem_replacement

theorem toP1PolynomialSeparationStep_target_ne_zero
    {S : Set E} {β : E}
    (p : F[X]) (hpder : p.derivative ≠ 0)
    (hβ : Polynomial.aeval β p ∉ forbiddenTargetSet F E S p) :
    Polynomial.aeval β p ≠ 0 :=
  (toP1PolynomialSeparationStep F E p hpder hβ).target_ne_zero

theorem toP1PolynomialSeparationStep_target_ne_one
    {S : Set E} {β : E}
    (p : F[X]) (hpder : p.derivative ≠ 0)
    (hβ : Polynomial.aeval β p ∉ forbiddenTargetSet F E S p) :
    Polynomial.aeval β p ≠ 1 :=
  (toP1PolynomialSeparationStep F E p hpder hβ).target_ne_one

end PolynomialTargetAvoidance
end SourceStack
end HilbertTest
