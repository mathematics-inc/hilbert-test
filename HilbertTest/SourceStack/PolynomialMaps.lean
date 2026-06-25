import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Derivative

/-!
Polynomial finite-set wrappers for the recursive Belyi source stack.

Mochizuki Lemma 2.4 replaces a finite algebraic set `S` by
`f₀(S) ∪ f₀(S₀)`, where `S₀` is the set of roots of `f₀'`.  This file exposes
the underlying finite-image and derivative-root finiteness facts in a stable
namespace for Hilbert benchmarks.
-/

noncomputable section

open scoped Polynomial

namespace HilbertTest
namespace SourceStack
namespace PolynomialMaps

universe u v

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]

/-- The root set of the derivative of a polynomial is finite. -/
theorem derivative_rootSet_finite (p : F[X]) :
    (p.derivative.rootSet E).Finite :=
  Polynomial.rootSet_finite p.derivative E

/-- Membership in the derivative root set is evaluation to zero when the
derivative is nonzero. -/
theorem mem_derivative_rootSet_iff {p : F[X]} (hpder : p.derivative ≠ 0)
    (x : E) :
    x ∈ p.derivative.rootSet E ↔ Polynomial.aeval x p.derivative = 0 := by
  exact Polynomial.mem_rootSet_of_ne hpder

/-- Polynomial evaluation sends finite sets to finite sets. -/
theorem polynomial_image_finite {S : Set E} (hS : S.Finite) (p : F[X]) :
    ((fun x : E => Polynomial.aeval x p) '' S).Finite :=
  hS.image _

/-- The Lemma 2.4 replacement set `p(S) ∪ p(rootSet p')` is finite whenever
`S` is finite. -/
theorem polynomial_image_union_derivative_root_image_finite
    {S : Set E} (hS : S.Finite) (p : F[X]) :
    (((fun x : E => Polynomial.aeval x p) '' S) ∪
      ((fun x : E => Polynomial.aeval x p) '' p.derivative.rootSet E)).Finite :=
  (hS.image _).union ((derivative_rootSet_finite F E p).image _)

end PolynomialMaps
end SourceStack
end HilbertTest
