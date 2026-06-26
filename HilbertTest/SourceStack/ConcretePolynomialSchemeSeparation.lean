import HilbertTest.SourceStack.PolynomialSchemeSeparation
import HilbertTest.SourceStack.SchemeAffineLinePoints

/-!
Concrete scheme-carrier polynomial separation.

`PolynomialSchemeSeparation` proves the separation package assuming an abstract
linear-to-scheme point bridge for `P^1`.  `SchemeAffineLinePoints` constructs
that bridge concretely from the affine scheme points `[r:1]` on
`Proj K[X0,X1]`.  This file composes the two, exposing the actual scheme point
map `x |-> [p(x):1]` and selected target `[p(beta):1]` with no abstract bridge
parameter.
-/

noncomputable section

open scoped Polynomial

namespace HilbertTest
namespace SourceStack
namespace ConcretePolynomialSchemeSeparation

open P1PolynomialSeparation
open P1SchemePointBridge
open PolynomialSchemeSeparation
open SchemeAffineLinePoints

universe u v

variable (F : Type u) (K : Type v)
variable [Field F] [Field K] [Algebra F K]

/-- The concrete scheme-carrier polynomial point map `x |-> [p(x):1]`. -/
def concreteSchemePolynomialPointMap (p : F[X]) (x : K) :
    SchemeProjectiveLine.P1 K :=
  SchemeAffineLinePoints.affinePoint K (Polynomial.aeval x p)

/-- The concrete selected scheme-carrier target `[p(beta):1]`. -/
def concreteSchemePolynomialTargetPoint (p : F[X]) (β : K) :
    SchemeProjectiveLine.P1 K :=
  SchemeAffineLinePoints.affinePoint K (Polynomial.aeval β p)

variable {S : Set K} {β : K}
variable (P : P1PolynomialSeparationStep F K S β)

theorem concreteSchemePolynomialPointMap_eq_bridge
    (x : K) :
    (SchemeAffineLinePoints.concreteLinearSchemePointBridge K).schemePointMap F P x =
      concreteSchemePolynomialPointMap F K P.polynomial x := by
  change SchemeAffineLinePoints.linearToSchemePoint K (P.pointMap x) =
    SchemeAffineLinePoints.affinePoint K (Polynomial.aeval x P.polynomial)
  rw [P1PolynomialSeparationStep.pointMap, affinePolynomialPointMap,
    SchemeAffineLinePoints.linearToSchemePoint_affinePoint]

theorem concreteSchemePolynomialTargetPoint_eq_bridge :
    (SchemeAffineLinePoints.concreteLinearSchemePointBridge K).schemeTargetPoint F P =
      concreteSchemePolynomialTargetPoint F K P.polynomial β := by
  change SchemeAffineLinePoints.linearToSchemePoint K P.targetPoint =
    SchemeAffineLinePoints.affinePoint K (Polynomial.aeval β P.polynomial)
  rw [P1PolynomialSeparationStep.targetPoint,
    SchemeAffineLinePoints.linearToSchemePoint_affinePoint]

theorem concreteSchemePolynomialPointMap_mem_markedSchemePointSet_iff
    (p : F[X]) (x : K) :
    concreteSchemePolynomialPointMap F K p x ∈
        SchemeProjectiveLine.markedSchemePointSet K ↔
      Polynomial.aeval x p = 0 ∨ Polynomial.aeval x p = 1 := by
  simpa [concreteSchemePolynomialPointMap] using
    SchemeAffineLinePoints.affinePoint_mem_markedSchemePointSet_iff K
      (Polynomial.aeval x p)

theorem concreteSchemePolynomialTargetPoint_mem_markedSchemePointSet_iff
    (p : F[X]) (β : K) :
    concreteSchemePolynomialTargetPoint F K p β ∈
        SchemeProjectiveLine.markedSchemePointSet K ↔
      Polynomial.aeval β p = 0 ∨ Polynomial.aeval β p = 1 := by
  simpa [concreteSchemePolynomialTargetPoint] using
    SchemeAffineLinePoints.affinePoint_mem_markedSchemePointSet_iff K
      (Polynomial.aeval β p)

/-- Concrete point-map branch avoidance in scalar-value form. -/
theorem concreteSchemePolynomialPointMap_not_mem_markedSchemePointSet_iff
    (p : F[X]) (x : K) :
    concreteSchemePolynomialPointMap F K p x ∉
        SchemeProjectiveLine.markedSchemePointSet K ↔
      Polynomial.aeval x p ≠ 0 ∧ Polynomial.aeval x p ≠ 1 := by
  constructor
  · intro h
    exact not_or.mp
      ((not_congr (concreteSchemePolynomialPointMap_mem_markedSchemePointSet_iff
        F K p x)).1 h)
  · intro h
    exact (not_congr (concreteSchemePolynomialPointMap_mem_markedSchemePointSet_iff
      F K p x)).2 (not_or.mpr h)

/-- Concrete selected-target branch avoidance in scalar-value form. -/
theorem concreteSchemePolynomialTargetPoint_not_mem_markedSchemePointSet_iff
    (p : F[X]) (β : K) :
    concreteSchemePolynomialTargetPoint F K p β ∉
        SchemeProjectiveLine.markedSchemePointSet K ↔
      Polynomial.aeval β p ≠ 0 ∧ Polynomial.aeval β p ≠ 1 := by
  constructor
  · intro h
    exact not_or.mp
      ((not_congr (concreteSchemePolynomialTargetPoint_mem_markedSchemePointSet_iff
        F K p β)).1 h)
  · intro h
    exact (not_congr (concreteSchemePolynomialTargetPoint_mem_markedSchemePointSet_iff
      F K p β)).2 (not_or.mpr h)

theorem concreteSchemePolynomialTargetPoint_not_mem_markedSchemePointSet
    {p : F[X]} {β : K}
    (h0 : Polynomial.aeval β p ≠ 0)
    (h1 : Polynomial.aeval β p ≠ 1) :
    concreteSchemePolynomialTargetPoint F K p β ∉
      SchemeProjectiveLine.markedSchemePointSet K := by
  simpa [concreteSchemePolynomialTargetPoint] using
    SchemeAffineLinePoints.affinePoint_not_mem_markedSchemePointSet_of_ne_zero_one
      K h0 h1

/-- Concrete scheme-carrier separation package: for a finite input set and a
polynomial with nonzero derivative over an algebraically closed target field,
choose `beta` so `[p(beta):1]` avoids the marked scheme triple, is separated
from all `[p(x):1]` with `x ∈ S`, and has only noncritical polynomial preimages.
-/
theorem exists_concrete_scheme_separation_package
    [IsAlgClosed K]
    {S : Set K} (hS : S.Finite)
    (p : F[X]) (hpder : p.derivative ≠ 0) :
    ∃ β : K, ∃ P : P1PolynomialSeparationStep F K S β,
      P.polynomial = p ∧
        concreteSchemePolynomialTargetPoint F K P.polynomial β ∉
          SchemeProjectiveLine.markedSchemePointSet K ∧
          (∀ x ∈ S, concreteSchemePolynomialPointMap F K P.polynomial x ≠
            concreteSchemePolynomialTargetPoint F K P.polynomial β) ∧
            ∀ x : K, concreteSchemePolynomialPointMap F K P.polynomial x =
              concreteSchemePolynomialTargetPoint F K P.polynomial β →
              Polynomial.aeval x P.polynomial.derivative ≠ 0 := by
  obtain ⟨β, P, hP, htarget, hsep, hcrit⟩ :=
    PolynomialSchemeSeparation.exists_scheme_separation_package F K
      (SchemeAffineLinePoints.concreteLinearSchemePointBridge K) hS p hpder
  refine ⟨β, P, hP, ?_, ?_, ?_⟩
  · simpa [concreteSchemePolynomialTargetPoint_eq_bridge F K P]
      using htarget
  · intro x hx
    simpa [concreteSchemePolynomialPointMap_eq_bridge F K P x,
      concreteSchemePolynomialTargetPoint_eq_bridge F K P]
      using hsep x hx
  · intro x hx
    exact hcrit x (by
      simpa [concreteSchemePolynomialPointMap_eq_bridge F K P x,
        concreteSchemePolynomialTargetPoint_eq_bridge F K P]
        using hx)

end ConcretePolynomialSchemeSeparation
end SourceStack
end HilbertTest
