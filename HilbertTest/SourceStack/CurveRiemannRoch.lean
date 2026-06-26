import HilbertTest.SourceStack.LinearAlgebra

/-!
Source-stack interface for the Riemann-Roch-to-linear-algebra handoff in
Scherr-Zieve's reduction from curves to `P^1`.

This file does not assume curve Riemann-Roch.  It isolates the
checked consequence needed downstream: once a curve/divisor theorem supplies
nonzero restricted evaluation maps on a Riemann-Roch space of sections, the
existing Scherr-Zieve finite-linear-form avoidance lemma produces a section
vanishing on one finite set and nonvanishing on another.
-/

namespace HilbertTest
namespace SourceStack
namespace CurveRiemannRoch

universe u v w

/-- Abstract Riemann-Roch section-evaluation data: a vector space of sections
and a linear evaluation functional at each point of the curve-like source. -/
structure RRSectionEvaluationData
    (K : Type u) [Field K] (X : Type v)
    (V : Type w) [AddCommGroup V] [Module K V] where
  eval : X → V →ₗ[K] K

namespace RRSectionEvaluationData

variable {K : Type u} [Field K]
variable {X : Type v} {V : Type w} [AddCommGroup V] [Module K V]
variable (D : RRSectionEvaluationData K X V)

/-- A section vanishes on a finite set of points when every listed evaluation is
zero. -/
def vanishesOn (S : Finset X) (s : V) : Prop :=
  ∀ x ∈ S, D.eval x s = 0

/-- A section is nonzero on a finite set of points when every listed evaluation
is nonzero. -/
def nonzeroOn (T : Finset X) (s : V) : Prop :=
  ∀ x ∈ T, D.eval x s ≠ 0

/-- Set-level version of finite-set vanishing, matching the statement style of
the Belyi-map existence interfaces. -/
def vanishesOnSet (S : Set X) (s : V) : Prop :=
  ∀ x ∈ S, D.eval x s = 0

/-- Set-level version of finite-set nonvanishing, matching the statement style
of the Belyi-map existence interfaces. -/
def nonzeroOnSet (T : Set X) (s : V) : Prop :=
  ∀ x ∈ T, D.eval x s ≠ 0

/-- Vanishing on a finite set is membership in the common kernel of the
corresponding evaluation forms. -/
theorem vanishesOn_iff_mem_commonKernel
    (S : Finset X) (s : V) :
    D.vanishesOn S s ↔
      s ∈ commonKernel (K := K) (V := V) S D.eval := by
  rw [vanishesOn]
  exact (mem_commonKernel_iff (K := K) (V := V) S D.eval s).symm

/-- Nonvanishing on a finite set is the pointwise nonzero condition for the
corresponding evaluation forms. -/
theorem nonzeroOn_iff
    (T : Finset X) (s : V) :
    D.nonzeroOn T s ↔ ∀ x ∈ T, D.eval x s ≠ 0 := by
  rfl

/-- Converting a finite set to a finset preserves the section-vanishing
condition. -/
theorem vanishesOn_toFinset_iff
    {S : Set X} (hS : S.Finite) (s : V) :
    D.vanishesOn hS.toFinset s ↔ D.vanishesOnSet S s := by
  constructor
  · intro hs x hx
    exact hs x ((Set.Finite.mem_toFinset hS).2 hx)
  · intro hs x hx
    exact hs x ((Set.Finite.mem_toFinset hS).1 hx)

/-- Converting a finite set to a finset preserves the section-nonvanishing
condition. -/
theorem nonzeroOn_toFinset_iff
    {T : Set X} (hT : T.Finite) (s : V) :
    D.nonzeroOn hT.toFinset s ↔ D.nonzeroOnSet T s := by
  constructor
  · intro hs x hx
    exact hs x ((Set.Finite.mem_toFinset hT).2 hx)
  · intro hs x hx
    exact hs x ((Set.Finite.mem_toFinset hT).1 hx)

/-- If all evaluations in a finite family are nonzero linear forms, then some
section is nonzero at every point in the family. -/
theorem exists_section_nonzero_on_finite
    [Infinite K] (T : Finset X)
    (hT : ∀ x ∈ T, D.eval x ≠ 0) :
    ∃ s : V, D.nonzeroOn T s := by
  exact exists_vector_avoiding_kernels_of_nonzero_linear_maps
    (K := K) (V := V) T D.eval hT

/-- Riemann-Roch handoff: if, after imposing vanishing on `S`, every
evaluation at `T` remains a nonzero linear form on the common kernel, then
there is a section vanishing on `S` and nonzero on `T`. -/
theorem exists_section_vanishing_on_and_nonzero_on
    [Infinite K] (S T : Finset X)
    (havoid : ∀ x ∈ T,
      (D.eval x).comp (commonKernel (K := K) (V := V) S D.eval).subtype ≠ 0) :
    ∃ s : V, D.vanishesOn S s ∧ D.nonzeroOn T s := by
  exact exists_vector_vanishing_and_nonzero_on_finite_linear_forms
    (K := K) (V := V) S T D.eval D.eval havoid

end RRSectionEvaluationData

/-- Curve-facing package expected from a future divisor/Riemann-Roch
formalization: finite disjoint sets give nonzero restricted evaluations on the
Riemann-Roch section space after imposing vanishing on the first set. -/
structure RiemannRochFiniteEvaluationPackage
    (K : Type u) [Field K] (X : Type v)
    (V : Type w) [AddCommGroup V] [Module K V] where
  eval : X → V →ₗ[K] K
  restricted_eval_nonzero :
    ∀ {S T : Finset X}, Disjoint S T →
      ∀ x ∈ T,
        (eval x).comp (commonKernel (K := K) (V := V) S eval).subtype ≠ 0

namespace RiemannRochFiniteEvaluationPackage

variable {K : Type u} [Field K]
variable {X : Type v} {V : Type w} [AddCommGroup V] [Module K V]
variable (D : RiemannRochFiniteEvaluationPackage K X V)

/-- Forget the Riemann-Roch nonzero-restriction package to plain section
evaluation data. -/
def toEvaluationData : RRSectionEvaluationData K X V where
  eval := D.eval

theorem toEvaluationData_eval
    (x : X) :
    (D.toEvaluationData).eval x = D.eval x := rfl

/-- Scherr-Zieve Proposition 2.1 linear core, abstracted from curves: a
Riemann-Roch finite-evaluation package over an infinite field yields a section
vanishing on one finite set and nonzero on a disjoint finite set. -/
theorem exists_section_for_disjoint_finsets
    [Infinite K] {S T : Finset X} (hdis : Disjoint S T) :
    ∃ s : V, (D.toEvaluationData).vanishesOn S s ∧
      (D.toEvaluationData).nonzeroOn T s := by
  exact (D.toEvaluationData).exists_section_vanishing_on_and_nonzero_on S T
    (by
      intro x hx
      exact D.restricted_eval_nonzero hdis x hx)

/-- Set-level form of the finite Riemann-Roch evaluation handoff: finite
disjoint sets yield a section vanishing on the first and nonzero on the second. -/
theorem exists_section_for_disjoint_finite_sets
    [Infinite K] {S T : Set X} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V, (D.toEvaluationData).vanishesOnSet S s ∧
      (D.toEvaluationData).nonzeroOnSet T s := by
  have hdisFin : Disjoint hS.toFinset hT.toFinset := by
    rw [Finset.disjoint_left]
    intro x hxS hxT
    exact (Set.disjoint_left.mp hdis)
      ((Set.Finite.mem_toFinset hS).1 hxS)
      ((Set.Finite.mem_toFinset hT).1 hxT)
  rcases D.exists_section_for_disjoint_finsets hdisFin with ⟨s, hsS, hsT⟩
  exact
    ⟨s,
      ((D.toEvaluationData).vanishesOn_toFinset_iff hS s).1 hsS,
      ((D.toEvaluationData).nonzeroOn_toFinset_iff hT s).1 hsT⟩

/-- Singleton-target form: for a finite set `S` and a point outside it, there
is a section vanishing on `S` and nonzero at that point. -/
theorem exists_section_vanishing_on_finite_nonzero_at
    [Infinite K] {S : Set X} (hS : S.Finite) {x : X} (hx : x ∉ S) :
    ∃ s : V, (D.toEvaluationData).vanishesOnSet S s ∧ D.eval x s ≠ 0 := by
  have hdis : Disjoint S ({x} : Set X) := by
    rw [Set.disjoint_left]
    intro y hyS hyx
    rw [Set.mem_singleton_iff] at hyx
    subst y
    exact hx hyS
  rcases D.exists_section_for_disjoint_finite_sets
      hS (Set.finite_singleton x) hdis with ⟨s, hsS, hsx⟩
  exact ⟨s, hsS, hsx x (by simp)⟩

end RiemannRochFiniteEvaluationPackage

end CurveRiemannRoch
end SourceStack
end HilbertTest
