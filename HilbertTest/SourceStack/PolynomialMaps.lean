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

/-- If `q` maps `S` into `T` and `p` separates `T` from the selected outer
target value, then `p.comp q` separates `S` from the selected composed target. -/
theorem aeval_comp_ne_target_of_mapsTo_and_outer_separates
    {S T : Set E} {p q : F[X]} {β x : E}
    (hmap : ∀ z ∈ S, Polynomial.aeval z q ∈ T)
    (hsep : ∀ y ∈ T,
      Polynomial.aeval y p ≠ Polynomial.aeval (Polynomial.aeval β q) p)
    (hx : x ∈ S) :
    Polynomial.aeval x (p.comp q) ≠ Polynomial.aeval β (p.comp q) := by
  rw [aeval_comp F E p q x, aeval_comp F E p q β]
  exact hsep (Polynomial.aeval x q) (hmap x hx)

/-- Noncriticality over a composed target follows from noncriticality of the
inner map at composed-target preimages and of the outer map at the induced outer
preimages. -/
theorem derivative_aeval_comp_ne_zero_of_target_preimage
    (p q : F[X]) {β x : E}
    (hq : ∀ z : E,
      Polynomial.aeval z (p.comp q) = Polynomial.aeval β (p.comp q) →
        Polynomial.aeval z q.derivative ≠ 0)
    (hp : ∀ y : E,
      Polynomial.aeval y p = Polynomial.aeval (Polynomial.aeval β q) p →
        Polynomial.aeval y p.derivative ≠ 0)
    (hx : Polynomial.aeval x (p.comp q) = Polynomial.aeval β (p.comp q)) :
      Polynomial.aeval x (p.comp q).derivative ≠ 0 := by
  have hq_nonzero := hq x hx
  have houter_eq :
      Polynomial.aeval (Polynomial.aeval x q) p =
        Polynomial.aeval (Polynomial.aeval β q) p := by
    have h := hx
    rw [aeval_comp F E p q x, aeval_comp F E p q β] at h
    exact h
  exact derivative_aeval_comp_ne_zero F E p q hq_nonzero (hp _ houter_eq)

section MochizukiLemma21

universe w

/-- Mochizuki's Lemma 2.1 polynomial `x^m * (x - 1)^n`. -/
def mochizukiPolynomial (R : Type w) [CommRing R] (m n : ℕ) : R[X] :=
  (Polynomial.X : R[X]) ^ m * ((Polynomial.X : R[X]) - Polynomial.C (1 : R)) ^ n

/-- Product-rule expansion for the derivative of Mochizuki's Lemma 2.1
polynomial. -/
theorem mochizukiPolynomial_derivative_expansion
    (R : Type w) [CommRing R] (m n : ℕ) :
    (mochizukiPolynomial R m n).derivative =
      (Polynomial.C (m : R) * Polynomial.X ^ (m - 1)) *
          ((Polynomial.X : R[X]) - Polynomial.C (1 : R)) ^ n +
        Polynomial.X ^ m *
          (Polynomial.C (n : R) *
            ((Polynomial.X : R[X]) - Polynomial.C (1 : R)) ^ (n - 1)) := by
  rw [mochizukiPolynomial, Polynomial.derivative_mul, Polynomial.derivative_X_pow,
    Polynomial.derivative_X_sub_C_pow]

/-- The derivative computation from Mochizuki Lemma 2.1:
`(x^m (x - 1)^n)' = x^(m-1) (x-1)^(n-1) ((m+n)x - m)`. -/
theorem mochizukiPolynomial_derivative_factor
    (R : Type w) [CommRing R] (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (mochizukiPolynomial R m n).derivative =
      Polynomial.X ^ (m - 1) * ((Polynomial.X : R[X]) - Polynomial.C (1 : R)) ^ (n - 1) *
        (Polynomial.C ((m + n : ℕ) : R) * Polynomial.X - Polynomial.C (m : R)) := by
  let Y : R[X] := (Polynomial.X : R[X]) - Polynomial.C (1 : R)
  have hmX : (Polynomial.X : R[X]) ^ m = Polynomial.X ^ (m - 1) * Polynomial.X := by
    nth_rewrite 1 [show m = (m - 1) + 1 by omega]
    rw [pow_succ]
  have hnY : Y ^ n = Y ^ (n - 1) * Y := by
    nth_rewrite 1 [show n = (n - 1) + 1 by omega]
    rw [pow_succ]
  rw [mochizukiPolynomial_derivative_expansion]
  change Polynomial.C (m : R) * Polynomial.X ^ (m - 1) * Y ^ n +
      Polynomial.X ^ m * (Polynomial.C (n : R) * Y ^ (n - 1)) =
    Polynomial.X ^ (m - 1) * Y ^ (n - 1) *
      (Polynomial.C ((m + n : ℕ) : R) * Polynomial.X - Polynomial.C (m : R))
  rw [hmX, hnY]
  rw [Nat.cast_add, map_add]
  dsimp [Y]
  rw [Polynomial.C_1]
  ring_nf

/-- Evaluated derivative factorization for Mochizuki's Lemma 2.1 polynomial. -/
theorem mochizukiPolynomial_derivative_aeval
    (K : Type w) [Field K] (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (x : K) :
    Polynomial.aeval x (mochizukiPolynomial K m n).derivative =
      x ^ (m - 1) * (x - 1) ^ (n - 1) *
        (((m + n : ℕ) : K) * x - (m : K)) := by
  rw [mochizukiPolynomial_derivative_factor K m n hm hn]
  simp [map_mul, map_sub]

/-- Affine critical-point consequence from Mochizuki Lemma 2.1(b): over
characteristic zero, every affine critical point of `x^m * (x - 1)^n` is
`0`, `1`, or `m/(m+n)`. -/
theorem mochizukiPolynomial_derivative_aeval_eq_zero_imp
    (K : Type w) [Field K] [CharZero K]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) {x : K}
    (hx : Polynomial.aeval x (mochizukiPolynomial K m n).derivative = 0) :
    x = 0 ∨ x = 1 ∨ x = (m : K) / ((m + n : ℕ) : K) := by
  rw [mochizukiPolynomial_derivative_aeval K m n hm hn x] at hx
  rcases mul_eq_zero.mp hx with hprod | hlin
  · rcases mul_eq_zero.mp hprod with hx0 | hx1
    · exact Or.inl (pow_eq_zero hx0)
    · right
      left
      exact sub_eq_zero.mp (pow_eq_zero hx1)
  · right
    right
    have hmn_ne : ((m + n : ℕ) : K) ≠ 0 := by
      exact_mod_cast (show m + n ≠ 0 by omega)
    have hlin' : x * ((m + n : ℕ) : K) = (m : K) := by
      rw [mul_comm]
      exact sub_eq_zero.mp hlin
    exact (eq_div_iff hmn_ne).2 hlin'

end MochizukiLemma21

end PolynomialMaps
end SourceStack
end HilbertTest
