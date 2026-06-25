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

/-- The image of a set under polynomial evaluation. -/
def imageSet (S : Set E) (p : F[X]) : Set E :=
  (fun x : E => Polynomial.aeval x p) '' S

/-- The critical-value set supplied by the roots of the formal derivative. -/
def criticalValueSet (p : F[X]) : Set E :=
  imageSet F E (p.derivative.rootSet E) p

/-- The finite replacement set `p(S) ∪ p(rootSet p')` used in Lemma 2.4. -/
def replacementSet (S : Set E) (p : F[X]) : Set E :=
  imageSet F E S p ∪ criticalValueSet F E p

/-- A point of the original set maps into the polynomial image set. -/
theorem mem_imageSet_of_mem {S : Set E} {x : E} (p : F[X]) (hx : x ∈ S) :
    Polynomial.aeval x p ∈ imageSet F E S p :=
  ⟨x, hx, rfl⟩

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

/-- The named polynomial image set is finite for finite input sets. -/
theorem imageSet_finite {S : Set E} (hS : S.Finite) (p : F[X]) :
    (imageSet F E S p).Finite :=
  polynomial_image_finite F E hS p

/-- The critical-value set of a polynomial is finite. -/
theorem criticalValueSet_finite (p : F[X]) :
    (criticalValueSet F E p).Finite :=
  imageSet_finite F E (derivative_rootSet_finite F E p) p

/-- A derivative root maps into the critical-value set. -/
theorem mem_criticalValueSet_of_mem_derivative_root {p : F[X]} {x : E}
    (hx : x ∈ p.derivative.rootSet E) :
    Polynomial.aeval x p ∈ criticalValueSet F E p :=
  mem_imageSet_of_mem F E p hx

/-- A point where a nonzero derivative evaluates to zero maps into the
critical-value set. -/
theorem mem_criticalValueSet_of_derivative_aeval_eq_zero {p : F[X]}
    (hpder : p.derivative ≠ 0) {x : E}
    (hx : Polynomial.aeval x p.derivative = 0) :
    Polynomial.aeval x p ∈ criticalValueSet F E p :=
  mem_criticalValueSet_of_mem_derivative_root F E
    ((mem_derivative_rootSet_iff F E hpder x).2 hx)

/-- The Lemma 2.4 replacement set `p(S) ∪ p(rootSet p')` is finite whenever
`S` is finite. -/
theorem polynomial_image_union_derivative_root_image_finite
    {S : Set E} (hS : S.Finite) (p : F[X]) :
    (((fun x : E => Polynomial.aeval x p) '' S) ∪
      ((fun x : E => Polynomial.aeval x p) '' p.derivative.rootSet E)).Finite :=
  (hS.image _).union ((derivative_rootSet_finite F E p).image _)

/-- The named Lemma 2.4 replacement set is finite whenever `S` is finite. -/
theorem replacementSet_finite {S : Set E} (hS : S.Finite) (p : F[X]) :
    (replacementSet F E S p).Finite :=
  (imageSet_finite F E hS p).union (criticalValueSet_finite F E p)

/-- The ordinary image is contained in the Lemma 2.4 replacement set. -/
theorem imageSet_subset_replacementSet (S : Set E) (p : F[X]) :
    imageSet F E S p ⊆ replacementSet F E S p :=
  Set.subset_union_left

/-- The critical-value set is contained in the Lemma 2.4 replacement set. -/
theorem criticalValueSet_subset_replacementSet (S : Set E) (p : F[X]) :
    criticalValueSet F E p ⊆ replacementSet F E S p :=
  Set.subset_union_right

/-- Nonmembership in the replacement set is simultaneous nonmembership in the
ordinary image and the critical-value set. -/
theorem not_mem_replacementSet_iff {S : Set E} (p : F[X]) (y : E) :
    y ∉ replacementSet F E S p ↔
      y ∉ imageSet F E S p ∧ y ∉ criticalValueSet F E p := by
  simp [replacementSet]

end PolynomialMaps
end SourceStack
end HilbertTest
