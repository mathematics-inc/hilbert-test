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

/-- Polynomial image sets are monotone in the input set. -/
theorem imageSet_mono {S T : Set E} (hST : S ⊆ T) (p : F[X]) :
    imageSet F E S p ⊆ imageSet F E T p := by
  rintro y ⟨x, hxS, rfl⟩
  exact ⟨x, hST hxS, rfl⟩

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

/-- Membership in the Lemma 2.4 replacement set is membership in the ordinary
image or in the critical-value set. -/
theorem mem_replacementSet_iff {S : Set E} (p : F[X]) (y : E) :
    y ∈ replacementSet F E S p ↔
      y ∈ imageSet F E S p ∨ y ∈ criticalValueSet F E p := by
  simp [replacementSet]

/-- Ordinary image points belong to the Lemma 2.4 replacement set. -/
theorem mem_replacementSet_of_mem_imageSet {S : Set E} {p : F[X]} {y : E}
    (hy : y ∈ imageSet F E S p) :
    y ∈ replacementSet F E S p :=
  (mem_replacementSet_iff F E p y).2 (Or.inl hy)

/-- Critical values belong to the Lemma 2.4 replacement set. -/
theorem mem_replacementSet_of_mem_criticalValueSet {S : Set E} {p : F[X]} {y : E}
    (hy : y ∈ criticalValueSet F E p) :
    y ∈ replacementSet F E S p :=
  (mem_replacementSet_iff F E p y).2 (Or.inr hy)

/-- Replacement sets are monotone in the finite input set. -/
theorem replacementSet_mono {S T : Set E} (hST : S ⊆ T) (p : F[X]) :
    replacementSet F E S p ⊆ replacementSet F E T p := by
  intro y hy
  rcases (mem_replacementSet_iff F E p y).1 hy with hy | hy
  · exact mem_replacementSet_of_mem_imageSet F E (imageSet_mono F E hST p hy)
  · exact mem_replacementSet_of_mem_criticalValueSet F E hy

/-- Nonmembership in the replacement set is simultaneous nonmembership in the
ordinary image and the critical-value set. -/
theorem not_mem_replacementSet_iff {S : Set E} (p : F[X]) (y : E) :
    y ∉ replacementSet F E S p ↔
      y ∉ imageSet F E S p ∧ y ∉ criticalValueSet F E p := by
  simp [replacementSet]

/-- If `y` is outside the image of `S`, no point of `S` evaluates to `y`. -/
theorem aeval_ne_of_not_mem_imageSet {S : Set E} {p : F[X]} {x y : E}
    (hy : y ∉ imageSet F E S p) (hx : x ∈ S) :
    Polynomial.aeval x p ≠ y := by
  intro hxy
  exact hy ⟨x, hx, hxy⟩

/-- If `y` is outside the replacement set, no point of the original set
evaluates to `y`. -/
theorem aeval_ne_of_not_mem_replacementSet {S : Set E} {p : F[X]} {x y : E}
    (hy : y ∉ replacementSet F E S p) (hx : x ∈ S) :
    Polynomial.aeval x p ≠ y :=
  aeval_ne_of_not_mem_imageSet F E ((not_mem_replacementSet_iff F E p y).1 hy).1 hx

/-- If `y` is not a critical value, then every preimage of `y` has nonzero
formal derivative. -/
theorem derivative_aeval_ne_zero_of_value_not_mem_criticalValueSet
    {p : F[X]} (hpder : p.derivative ≠ 0) {x y : E}
    (hy : y ∉ criticalValueSet F E p) (hxy : Polynomial.aeval x p = y) :
    Polynomial.aeval x p.derivative ≠ 0 := by
  intro hder
  exact hy (by
    simpa [hxy] using
      (mem_criticalValueSet_of_derivative_aeval_eq_zero F E hpder hder))

/-- If `y` is outside the replacement set, then every preimage of `y` has
nonzero formal derivative. -/
theorem derivative_aeval_ne_zero_of_value_not_mem_replacementSet
    {S : Set E} {p : F[X]} (hpder : p.derivative ≠ 0) {x y : E}
    (hy : y ∉ replacementSet F E S p) (hxy : Polynomial.aeval x p = y) :
    Polynomial.aeval x p.derivative ≠ 0 :=
  derivative_aeval_ne_zero_of_value_not_mem_criticalValueSet F E hpder
    ((not_mem_replacementSet_iff F E p y).1 hy).2 hxy

/-- Evaluation of a polynomial composition. -/
theorem aeval_comp (p q : F[X]) (x : E) :
    Polynomial.aeval x (p.comp q) = Polynomial.aeval (Polynomial.aeval x q) p := by
  exact Polynomial.aeval_comp x

/-- The formal derivative chain rule for polynomial composition. -/
theorem derivative_comp (p q : F[X]) :
    (p.comp q).derivative = q.derivative * p.derivative.comp q := by
  exact Polynomial.derivative_comp p q

/-- The chain rule after evaluating at a point. -/
theorem aeval_derivative_comp (p q : F[X]) (x : E) :
    Polynomial.aeval x (p.comp q).derivative =
      Polynomial.aeval x q.derivative *
        Polynomial.aeval (Polynomial.aeval x q) p.derivative := by
  rw [Polynomial.derivative_comp]
  rw [map_mul]
  rw [Polynomial.aeval_comp]

/-- If both factors in the chain rule are nonzero, the derivative of the
composition is nonzero. -/
theorem derivative_aeval_comp_ne_zero
    (p q : F[X]) {x : E}
    (hq : Polynomial.aeval x q.derivative ≠ 0)
    (hp : Polynomial.aeval (Polynomial.aeval x q) p.derivative ≠ 0) :
    Polynomial.aeval x (p.comp q).derivative ≠ 0 := by
  rw [aeval_derivative_comp F E p q x]
  exact mul_ne_zero hq hp

end PolynomialMaps
end SourceStack
end HilbertTest
