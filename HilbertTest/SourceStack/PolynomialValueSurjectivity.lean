import HilbertTest.SourceStack.PolynomialTargetAvoidance
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
Realizing avoided target values as polynomial values.

`PolynomialTargetAvoidance` proves that the forbidden target values form a
finite set.  Over an algebraically closed field, a positive-degree polynomial
hits every target value, so an outside target value can be written as `p(beta)`.
This file formalizes that step and packages the resulting selected `beta` into
the `P1PolynomialSeparationStep` interface when the derivative is nonzero.
-/

noncomputable section

open scoped Polynomial

namespace HilbertTest
namespace SourceStack
namespace PolynomialValueSurjectivity

open PolynomialTargetAvoidance

universe u v

variable (F : Type u) (E : Type v)
variable [Field F] [Field E] [Algebra F E]

/-- A polynomial with nonzero formal derivative has positive degree. -/
theorem natDegree_pos_of_derivative_ne_zero
    (p : F[X]) (hpder : p.derivative ≠ 0) :
    0 < p.natDegree := by
  by_contra hnot
  have hzero : p.natDegree = 0 := Nat.eq_zero_of_not_pos hnot
  exact hpder (Polynomial.derivative_of_natDegree_zero hzero)

/-- A polynomial with nonzero formal derivative remains positive-degree after
coefficient extension to a nontrivial field. -/
theorem map_natDegree_pos_of_derivative_ne_zero
    (p : F[X]) (hpder : p.derivative ≠ 0) :
    0 < (p.map (algebraMap F E)).natDegree := by
  rw [Polynomial.natDegree_map]
  exact natDegree_pos_of_derivative_ne_zero F p hpder

/-- A positive-degree polynomial over an algebraically closed target field
realizes every prescribed target value after applying coefficients to that
field. -/
theorem exists_aeval_eq_of_map_natDegree_pos
    [IsAlgClosed E]
    (p : F[X]) (hp : 0 < (p.map (algebraMap F E)).natDegree) (y : E) :
    ∃ β : E, Polynomial.aeval β p = y := by
  let pE : E[X] := p.map (algebraMap F E)
  have hpE : 0 < pE.natDegree := hp
  have hqnat : 0 < (pE - Polynomial.C y).natDegree := by
    simpa [pE] using hpE
  have hqdegree_pos : 0 < (pE - Polynomial.C y).degree :=
    (Polynomial.natDegree_pos_iff_degree_pos).1 hqnat
  have hqdegree_ne : (pE - Polynomial.C y).degree ≠ 0 := ne_of_gt hqdegree_pos
  obtain ⟨β, hβroot⟩ := IsAlgClosed.exists_root (pE - Polynomial.C y) hqdegree_ne
  refine ⟨β, ?_⟩
  have h_eval_sub : pE.eval β - y = 0 := by
    simpa [Polynomial.IsRoot.def] using hβroot
  have h_eval : pE.eval β = y := sub_eq_zero.mp h_eval_sub
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  exact h_eval

/-- Over an algebraically closed target field, a positive-degree polynomial has
some value outside the finite forbidden target set. -/
theorem exists_beta_not_mem_forbiddenTargetSet
    [IsAlgClosed E]
    {S : Set E} (hS : S.Finite)
    (p : F[X]) (hp : 0 < (p.map (algebraMap F E)).natDegree) :
    ∃ β : E, Polynomial.aeval β p ∉ forbiddenTargetSet F E S p := by
  obtain ⟨y, hy⟩ := exists_target_not_mem_forbiddenTargetSet F E hS p
  obtain ⟨β, hβ⟩ := exists_aeval_eq_of_map_natDegree_pos F E p hp y
  exact ⟨β, by simpa [hβ] using hy⟩

/-- Over an algebraically closed target field, a polynomial with nonzero formal
derivative has a value outside the finite forbidden target set. -/
theorem exists_beta_not_mem_forbiddenTargetSet_of_derivative_ne_zero
    [IsAlgClosed E]
    {S : Set E} (hS : S.Finite)
    (p : F[X]) (hpder : p.derivative ≠ 0) :
    ∃ β : E, Polynomial.aeval β p ∉ forbiddenTargetSet F E S p :=
  exists_beta_not_mem_forbiddenTargetSet F E hS p
    (map_natDegree_pos_of_derivative_ne_zero F E p hpder)

/-- A positive-degree polynomial over an algebraically closed target field,
with nonzero formal derivative, yields a selected `P1` polynomial-separation
step for any finite input set. -/
theorem exists_p1PolynomialSeparationStep
    [IsAlgClosed E]
    {S : Set E} (hS : S.Finite)
    (p : F[X]) (hp : 0 < (p.map (algebraMap F E)).natDegree)
    (hpder : p.derivative ≠ 0) :
    ∃ β : E, ∃ P : P1PolynomialSeparation.P1PolynomialSeparationStep F E S β,
      P.polynomial = p := by
  obtain ⟨β, hβ⟩ := exists_beta_not_mem_forbiddenTargetSet F E hS p hp
  refine ⟨β, toP1PolynomialSeparationStep F E p hpder hβ, ?_⟩
  exact toP1PolynomialSeparationStep_polynomial F E p hpder hβ

/-- Over an algebraically closed target field, a polynomial with nonzero formal
derivative yields a selected `P1` polynomial-separation step for any finite
input set. -/
theorem exists_p1PolynomialSeparationStep_of_derivative_ne_zero
    [IsAlgClosed E]
    {S : Set E} (hS : S.Finite)
    (p : F[X]) (hpder : p.derivative ≠ 0) :
    ∃ β : E, ∃ P : P1PolynomialSeparation.P1PolynomialSeparationStep F E S β,
      P.polynomial = p := by
  exact exists_p1PolynomialSeparationStep F E hS p
    (map_natDegree_pos_of_derivative_ne_zero F E p hpder) hpder

/-- Concrete Mochizuki polynomial instance of the value-surjectivity step:
for positive exponents in characteristic zero, `x^m * (x - 1)^n` yields a
selected `P1` polynomial-separation step for any finite input set. -/
theorem exists_p1PolynomialSeparationStep_mochizukiPolynomial
    [CharZero F] [IsAlgClosed E]
    {S : Set E} (hS : S.Finite)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ∃ β : E, ∃ P : P1PolynomialSeparation.P1PolynomialSeparationStep
      F E S β,
      P.polynomial = PolynomialMaps.mochizukiPolynomial F m n := by
  exact exists_p1PolynomialSeparationStep_of_derivative_ne_zero
    F E hS (PolynomialMaps.mochizukiPolynomial F m n)
    (PolynomialMaps.mochizukiPolynomial_derivative_ne_zero F m n hm hn)

end PolynomialValueSurjectivity
end SourceStack
end HilbertTest
