import HilbertTest.SourceStack.CurveDivisorSections

/-!
Cohomology-to-evaluation source layer for Mochizuki Theorem 2.5.

The paper uses Serre duality and the long exact cohomology sequence to show
that global sections of `L` surject onto the fiber at each point.  Pinned
Mathlib does not contain that curve-specific theorem.  This file isolates the
checked consequence needed by the divisor-section layer: surjectivity of the
evaluation map to the nontrivial fiber `K` makes the evaluation functional
nonzero.
-/

namespace HilbertTest
namespace SourceStack
namespace CurveCohomologySections

open CurveDivisorSections
open CurveRiemannRoch
open BelyiReduction
open MarkedProjectiveLine
open ProjectiveSectionMaps
open SchemeMarkedBelyi
open SchemeProjectiveLine

universe u v w z

variable {K : Type u} [Field K]
variable {X : Type v}
variable {V : Type w} [AddCommGroup V] [Module K V]

/-- A surjective linear map to a nontrivial target is nonzero. -/
theorem linearMap_ne_zero_of_surjective
    {W : Type*} [AddCommGroup W] [Module K W] [Nontrivial W]
    (f : V →ₗ[K] W) (hf : Function.Surjective f) :
    f ≠ 0 := by
  intro hzero
  rcases exists_ne (0 : W) with ⟨w, hw⟩
  rcases hf w with ⟨v, hv⟩
  apply hw
  rw [← hv, hzero]
  simp

/-- Surjective point evaluations on a support set, abstracting the output of
the long exact cohomology sequence for `0 -> L(-x) -> L -> L ⊗ k(x) -> 0`. -/
structure EvaluationSurjectivityData
    (K : Type u) [Field K] (X : Type v)
    (V : Type w) [AddCommGroup V] [Module K V] where
  evalData : RRSectionEvaluationData K X V
  support : Set X
  eval_surjective_on_support : ∀ x ∈ support, Function.Surjective (evalData.eval x)

namespace EvaluationSurjectivityData

variable (E : EvaluationSurjectivityData K X V)

/-- Surjective evaluations to `K` are nonzero linear forms. -/
theorem eval_nonzero_on_support :
    ∀ x ∈ E.support, E.evalData.eval x ≠ 0 := by
  intro x hx
  exact linearMap_ne_zero_of_surjective
    (E.evalData.eval x) (E.eval_surjective_on_support x hx)

end EvaluationSurjectivityData

/-- Finite-family evaluation surjectivity after imposing vanishing on another
finite family.  This abstracts the cohomological consequence usually proved
from the exact sequence
`0 -> L(-S-x) -> L(-S) -> L(-S)|_x -> 0`. -/
structure RestrictedEvaluationSurjectivityData
    (K : Type u) [Field K] (X : Type v)
    (V : Type w) [AddCommGroup V] [Module K V] where
  evalData : RRSectionEvaluationData K X V
  restricted_eval_surjective :
    ∀ {S T : Finset X}, Disjoint S T →
      ∀ x ∈ T,
        Function.Surjective
          ((evalData.eval x).comp
            (commonKernel (K := K) (V := V) S evalData.eval).subtype)

namespace RestrictedEvaluationSurjectivityData

variable (E : RestrictedEvaluationSurjectivityData K X V)

/-- Surjectivity of restricted evaluations implies the nonzero restricted
evaluation hypothesis used by the Riemann-Roch finite-evaluation package. -/
theorem restricted_eval_nonzero :
    ∀ {S T : Finset X}, Disjoint S T →
      ∀ x ∈ T,
        (E.evalData.eval x).comp
            (commonKernel (K := K) (V := V) S E.evalData.eval).subtype ≠ 0 := by
  intro S T hdis x hx
  exact linearMap_ne_zero_of_surjective
    ((E.evalData.eval x).comp
      (commonKernel (K := K) (V := V) S E.evalData.eval).subtype)
    (E.restricted_eval_surjective hdis x hx)

/-- Forget cohomological restricted surjectivity to the Riemann-Roch
finite-evaluation package used by the downstream linear-algebra layer. -/
def toRiemannRochFiniteEvaluationPackage :
    RiemannRochFiniteEvaluationPackage K X V where
  eval := E.evalData.eval
  restricted_eval_nonzero := by
    intro S T hdis x hx
    exact E.restricted_eval_nonzero hdis x hx

theorem toRiemannRochFiniteEvaluationPackage_eval
    (x : X) :
    E.toRiemannRochFiniteEvaluationPackage.eval x = E.evalData.eval x := rfl

/-- The cohomological restricted-surjectivity package gives a section vanishing
on one finite set and nonzero on a disjoint finite set. -/
theorem exists_section_for_disjoint_finsets
    [Infinite K] {S T : Finset X} (hdis : Disjoint S T) :
    ∃ s : V, E.evalData.vanishesOn S s ∧ E.evalData.nonzeroOn T s := by
  exact E.toRiemannRochFiniteEvaluationPackage.exists_section_for_disjoint_finsets hdis

/-- Set-level version of the cohomological restricted-surjectivity handoff. -/
theorem exists_section_for_disjoint_finite_sets
    [Infinite K] {S T : Set X} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V, E.evalData.vanishesOnSet S s ∧ E.evalData.nonzeroOnSet T s := by
  exact E.toRiemannRochFiniteEvaluationPackage.exists_section_for_disjoint_finite_sets
    hS hT hdis

/-- Set-level finite subtype version of the cohomological restricted-
surjectivity handoff. -/
theorem exists_section_for_disjoint_finite_subtype_sets
    [Infinite K] (U : Set X) {S T : Set U} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V, (E.evalData.restrictSubtype U).vanishesOnSet S s ∧
      (E.evalData.restrictSubtype U).nonzeroOnSet T s := by
  exact
    E.toRiemannRochFiniteEvaluationPackage.exists_section_for_disjoint_finite_subtype_sets
      U hS hT hdis

/-- Singleton-target form after restricting the point set to a subtype: vanish
on a finite subtype set and remain nonzero at an outside subtype point. -/
theorem exists_section_vanishing_on_finite_subtype_nonzero_at
    [Infinite K] (U : Set X) {S : Set U} (hS : S.Finite) {x : U} (hx : x ∉ S) :
    ∃ s : V, (E.evalData.restrictSubtype U).vanishesOnSet S s ∧
      (E.evalData.restrictSubtype U).eval x s ≠ 0 := by
  exact
    E.toRiemannRochFiniteEvaluationPackage.exists_section_vanishing_on_finite_subtype_nonzero_at
      U hS hx

/-- Singleton-target form of restricted evaluation surjectivity: vanish on a
finite set and remain nonzero at a point outside it. -/
theorem exists_section_vanishing_on_finite_nonzero_at
    [Infinite K] {S : Set X} (hS : S.Finite) {x : X} (hx : x ∉ S) :
    ∃ s : V, E.evalData.vanishesOnSet S s ∧ E.evalData.eval x s ≠ 0 := by
  exact
    E.toRiemannRochFiniteEvaluationPackage.exists_section_vanishing_on_finite_nonzero_at
      hS hx

/-- Finite-complement-open version of restricted evaluation surjectivity:
vanish on the complement of `U` and remain nonzero on a finite subset of `U`. -/
theorem exists_section_vanishing_on_complement_nonzero_on_finite
    [Infinite K] {U T : Set X} (hUcompl : Uᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ s : V, E.evalData.vanishesOnSet Uᶜ s ∧
      E.evalData.nonzeroOnSet T s := by
  exact
    E.toRiemannRochFiniteEvaluationPackage.exists_section_vanishing_on_complement_nonzero_on_finite
      hUcompl hT hTsub

/-- Pointwise finite-complement-open version of restricted evaluation
surjectivity. -/
theorem exists_section_vanishing_on_complement_nonzero_at
    [Infinite K] {U : Set X} (hUcompl : Uᶜ.Finite)
    {x : X} (hxU : x ∈ U) :
    ∃ s : V, E.evalData.vanishesOnSet Uᶜ s ∧ E.evalData.eval x s ≠ 0 := by
  exact
    E.toRiemannRochFiniteEvaluationPackage.exists_section_vanishing_on_complement_nonzero_at
      hUcompl hxU

/-- Nonempty-open finite-complement version of restricted evaluation
surjectivity. -/
theorem exists_section_vanishing_on_complement_nonzero_on_finite_of_nonemptyOpenFiniteComplement
    [Infinite K] [TopologicalSpace X] [NonemptyOpenFiniteComplement X]
    {U T : Set X} (hU : IsOpen U) (hUne : U.Nonempty)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ s : V, E.evalData.vanishesOnSet Uᶜ s ∧
      E.evalData.nonzeroOnSet T s := by
  exact
    E.toRiemannRochFiniteEvaluationPackage.exists_section_vanishing_on_complement_nonzero_on_finite_of_nonemptyOpenFiniteComplement
      hU hUne hT hTsub

/-- Pointwise nonempty-open finite-complement version of restricted evaluation
surjectivity. -/
theorem exists_section_vanishing_on_complement_nonzero_at_of_nonemptyOpenFiniteComplement
    [Infinite K] [TopologicalSpace X] [NonemptyOpenFiniteComplement X]
    {U : Set X} (hU : IsOpen U) {x : X} (hxU : x ∈ U) :
    ∃ s : V, E.evalData.vanishesOnSet Uᶜ s ∧ E.evalData.eval x s ≠ 0 := by
  exact
    E.toRiemannRochFiniteEvaluationPackage.exists_section_vanishing_on_complement_nonzero_at_of_nonemptyOpenFiniteComplement
      hU hxU

section SchemeSupport

open AlgebraicGeometry

variable {C : Scheme.{u}}

/-- Cohomological restricted evaluation surjectivity selects an actual
canonical two-section finite marked Belyi map once that family is known to use
the cohomological Riemann-Roch evaluation package. -/
theorem twoSectionBezoutFamily_exists_for_finite_disjoint
    (E : RestrictedEvaluationSurjectivityData K C V)
    [Infinite K]
    (F : TwoSectionBezoutProjectiveSectionFiniteMarkedFamily K C V)
    (heval : F.evalPackage = E.toRiemannRochFiniteEvaluationPackage)
    {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V, (∀ x ∈ S, (F.map s).hom.base x ∈ markedSchemePointSet K) ∧
      ∀ x ∈ T, (F.map s).hom.base x ∉ markedSchemePointSet K := by
  rcases E.exists_section_for_disjoint_finite_sets hS hT hdis with
    ⟨s, hsS, hsT⟩
  refine ⟨s, ?_, ?_⟩
  · intro x hxS
    exact F.eval_zero_to_marked s
      (by
        rw [heval]
        exact hsS x hxS)
  · intro x hxT
    exact F.eval_nonzero_avoids_marked s
      (by
        rw [heval]
        exact hsT x hxT)

/-- Belyi-open form of the cohomological restricted-surjectivity handoff to a
canonical two-section finite marked Belyi family. -/
theorem twoSectionBezoutFamily_exists_map_belyiOpen_controls
    (E : RestrictedEvaluationSurjectivityData K C V)
    [Infinite K]
    (F : TwoSectionBezoutProjectiveSectionFiniteMarkedFamily K C V)
    (heval : F.evalPackage = E.toRiemannRochFiniteEvaluationPackage)
    {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V, T ⊆ ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
      ((F.map s).toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  rcases E.twoSectionBezoutFamily_exists_for_finite_disjoint
      F heval hS hT hdis with
    ⟨s, hSmark, hTavoid⟩
  refine ⟨s, ?_, ?_⟩
  · intro x hxT
    exact
      (SchemeBelyi.FiniteBelyiMap.mem_marked_belyiOpen_iff
        (K := K) (hmarkedOpen := F.hmarkedOpen) (F.map s) x).2
        (hTavoid x hxT)
  · intro x hxOpen hxS
    have hxNotMarked :
        (F.map s).hom.base x ∉ markedSchemePointSet K :=
      (SchemeBelyi.FiniteBelyiMap.mem_marked_belyiOpen_iff
        (K := K) (hmarkedOpen := F.hmarkedOpen) (F.map s) x).1 hxOpen
    exact hxNotMarked (hSmark x hxS)

/-- Combined marked-control, openness, and Belyi-open form of the
cohomological restricted-surjectivity handoff to a canonical two-section
finite marked Belyi family. -/
theorem twoSectionBezoutFamily_exists_map_controls_and_isOpen_belyiOpen_controls
    (E : RestrictedEvaluationSurjectivityData K C V)
    [Infinite K]
    (F : TwoSectionBezoutProjectiveSectionFiniteMarkedFamily K C V)
    (heval : F.evalPackage = E.toRiemannRochFiniteEvaluationPackage)
    {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V,
      ((∀ x ∈ S, (F.map s).hom.base x ∈ markedSchemePointSet K) ∧
        ∀ x ∈ T, (F.map s).hom.base x ∉ markedSchemePointSet K) ∧
        IsOpen ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
          T ⊆ ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
            ((F.map s).toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  rcases E.twoSectionBezoutFamily_exists_for_finite_disjoint
      F heval hS hT hdis with
    ⟨s, hSmark, hTavoid⟩
  have hTopen :
      T ⊆ ((F.map s).toBelyiMap.belyiOpen : Set C) := by
    intro x hxT
    exact
      (SchemeBelyi.FiniteBelyiMap.mem_marked_belyiOpen_iff
        (K := K) (hmarkedOpen := F.hmarkedOpen) (F.map s) x).2
        (hTavoid x hxT)
  have hopenS :
      ((F.map s).toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
    intro x hxOpen hxS
    have hxNotMarked :
        (F.map s).hom.base x ∉ markedSchemePointSet K :=
      (SchemeBelyi.FiniteBelyiMap.mem_marked_belyiOpen_iff
        (K := K) (hmarkedOpen := F.hmarkedOpen) (F.map s) x).1 hxOpen
    exact hxNotMarked (hSmark x hxS)
  exact
    ⟨s, ⟨hSmark, hTavoid⟩, (F.map s).toBelyiMap.belyiOpen.2,
      hTopen, hopenS⟩

/-- Finite-complement-open form of the cohomological handoff to a canonical
two-section finite marked Belyi family. -/
theorem twoSectionBezoutFamily_exists_map_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_finite_complement
    (E : RestrictedEvaluationSurjectivityData K C V)
    [Infinite K]
    (F : TwoSectionBezoutProjectiveSectionFiniteMarkedFamily K C V)
    (heval : F.evalPackage = E.toRiemannRochFiniteEvaluationPackage)
    {U T : Set C} (_hU : IsOpen U) (hUcompl : Uᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ s : V,
      ((∀ x ∈ Uᶜ, (F.map s).hom.base x ∈ markedSchemePointSet K) ∧
        ∀ x ∈ T, (F.map s).hom.base x ∉ markedSchemePointSet K) ∧
        IsOpen ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
          T ⊆ ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
            ((F.map s).toBelyiMap.belyiOpen : Set C) ⊆ U := by
  have hdis : Disjoint Uᶜ T := by
    rw [Set.disjoint_left]
    intro x hxU hxT
    exact hxU (hTsub hxT)
  rcases E.twoSectionBezoutFamily_exists_map_controls_and_isOpen_belyiOpen_controls
      F heval hUcompl hT hdis with
    ⟨s, hcontrols, hopen, hTopen, hopenS⟩
  exact ⟨s, hcontrols, hopen, hTopen, by simpa using hopenS⟩

/-- Nonempty-open finite-complement topology form of the cohomological handoff
to a canonical two-section finite marked Belyi family. -/
theorem twoSectionBezoutFamily_exists_map_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
    (E : RestrictedEvaluationSurjectivityData K C V)
    [Infinite K] [NonemptyOpenFiniteComplement C]
    (F : TwoSectionBezoutProjectiveSectionFiniteMarkedFamily K C V)
    (heval : F.evalPackage = E.toRiemannRochFiniteEvaluationPackage)
    {U T : Set C} (hU : IsOpen U) (hUne : U.Nonempty)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ s : V,
      ((∀ x ∈ Uᶜ, (F.map s).hom.base x ∈ markedSchemePointSet K) ∧
        ∀ x ∈ T, (F.map s).hom.base x ∉ markedSchemePointSet K) ∧
        IsOpen ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
          T ⊆ ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
            ((F.map s).toBelyiMap.belyiOpen : Set C) ⊆ U := by
  exact
    E.twoSectionBezoutFamily_exists_map_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_finite_complement
      F heval hU (finite_compl_of_isOpen_nonempty hU hUne) hT hTsub

/-- Package the cohomological restricted-surjectivity handoff to a canonical
two-section finite marked Belyi family as the paper-facing finite marked Belyi
existence interface. -/
noncomputable def twoSectionBezoutFamily_toFiniteMarkedBelyiExistence
    (E : RestrictedEvaluationSurjectivityData K C V)
    [Infinite K]
    (F : TwoSectionBezoutProjectiveSectionFiniteMarkedFamily K C V)
    (heval : F.evalPackage = E.toRiemannRochFiniteEvaluationPackage) :
    FiniteMarkedBelyiExistence K V C where
  hmarkedOpen := F.hmarkedOpen
  map := F.map
  exists_for_finite_disjoint := by
    intro S T hS hT hdis
    exact E.twoSectionBezoutFamily_exists_for_finite_disjoint
      F heval hS hT hdis

theorem twoSectionBezoutFamily_toFiniteMarkedBelyiExistence_hmarkedOpen
    (E : RestrictedEvaluationSurjectivityData K C V)
    [Infinite K]
    (F : TwoSectionBezoutProjectiveSectionFiniteMarkedFamily K C V)
    (heval : F.evalPackage = E.toRiemannRochFiniteEvaluationPackage) :
    (E.twoSectionBezoutFamily_toFiniteMarkedBelyiExistence F heval).hmarkedOpen =
      F.hmarkedOpen := rfl

theorem twoSectionBezoutFamily_toFiniteMarkedBelyiExistence_map_apply
    (E : RestrictedEvaluationSurjectivityData K C V)
    [Infinite K]
    (F : TwoSectionBezoutProjectiveSectionFiniteMarkedFamily K C V)
    (heval : F.evalPackage = E.toRiemannRochFiniteEvaluationPackage)
    (s : V) :
    (E.twoSectionBezoutFamily_toFiniteMarkedBelyiExistence F heval).map s =
      F.map s := rfl

theorem twoSectionBezoutFamily_toFiniteMarkedBelyiExistence_mem_belyiOpen_iff
    (E : RestrictedEvaluationSurjectivityData K C V)
    [Infinite K]
    (F : TwoSectionBezoutProjectiveSectionFiniteMarkedFamily K C V)
    (heval : F.evalPackage = E.toRiemannRochFiniteEvaluationPackage)
    (s : V) (x : C) :
    x ∈ (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
      (E.twoSectionBezoutFamily_toFiniteMarkedBelyiExistence F heval)).toBelyiCoverData.belyiOpen s ↔
      (F.map s).hom.base x ∉ markedSchemePointSet K := by
  exact
    FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence_mem_belyiOpen_iff
      K V (E.twoSectionBezoutFamily_toFiniteMarkedBelyiExistence F heval) s x

theorem twoSectionBezoutFamily_toFiniteMarkedBelyiExistence_belyiOpen_eq_schemeBelyi
    (E : RestrictedEvaluationSurjectivityData K C V)
    [Infinite K]
    (F : TwoSectionBezoutProjectiveSectionFiniteMarkedFamily K C V)
    (heval : F.evalPackage = E.toRiemannRochFiniteEvaluationPackage)
    (s : V) :
    (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
      (E.twoSectionBezoutFamily_toFiniteMarkedBelyiExistence F heval)).toBelyiCoverData.belyiOpen s =
      ((F.map s).toBelyiMap.belyiOpen : Set C) := by
  exact
    FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence_belyiOpen_eq_schemeBelyi
      K V (E.twoSectionBezoutFamily_toFiniteMarkedBelyiExistence F heval) s

end SchemeSupport

end RestrictedEvaluationSurjectivityData

section SchemeTwoSectionSource

open AlgebraicGeometry

variable {C : Scheme.{u}}

/-- A direct cohomology-to-two-section finite marked source package.  This is
the streamlined version of the paper's construction after the canonical
two-section projective-line family has been built: restricted evaluation
surjectivity supplies the sections, and the two-section family supplies the
finite marked Belyi maps. -/
structure CohomologicalTwoSectionFiniteMarkedSourceData
    (K : Type u) [Field K] (C : Scheme.{u})
    (V : Type w) [AddCommGroup V] [Module K V] where
  restricted : RestrictedEvaluationSurjectivityData K C V
  family : TwoSectionBezoutProjectiveSectionFiniteMarkedFamily K C V
  evalPackage_eq :
    family.evalPackage = restricted.toRiemannRochFiniteEvaluationPackage

namespace CohomologicalTwoSectionFiniteMarkedSourceData

variable (D : CohomologicalTwoSectionFiniteMarkedSourceData K C V)

/-- The paper-facing finite marked Belyi family obtained directly from
cohomological restricted evaluation and the canonical two-section construction. -/
noncomputable def toFiniteMarkedBelyiExistence
    [Infinite K] : FiniteMarkedBelyiExistence K V C :=
  D.restricted.twoSectionBezoutFamily_toFiniteMarkedBelyiExistence
    D.family D.evalPackage_eq

theorem toFiniteMarkedBelyiExistence_hmarkedOpen
    [Infinite K] :
    D.toFiniteMarkedBelyiExistence.hmarkedOpen = D.family.hmarkedOpen := by
  exact
    D.restricted.twoSectionBezoutFamily_toFiniteMarkedBelyiExistence_hmarkedOpen
      D.family D.evalPackage_eq

theorem toFiniteMarkedBelyiExistence_map_apply
    [Infinite K] (s : V) :
    D.toFiniteMarkedBelyiExistence.map s = D.family.map s := by
  exact
    D.restricted.twoSectionBezoutFamily_toFiniteMarkedBelyiExistence_map_apply
      D.family D.evalPackage_eq s

/-- Each finite marked Belyi map selected by the direct cohomological
two-section source package is finite. -/
theorem toFiniteMarkedBelyiExistence_map_finite_hom
    [Infinite K] (s : V) :
    IsFinite (D.toFiniteMarkedBelyiExistence.map s).hom := by
  rw [D.toFiniteMarkedBelyiExistence_map_apply s]
  exact D.family.map_finite_hom s

/-- Each selected finite marked Belyi map is dominant. -/
theorem toFiniteMarkedBelyiExistence_map_isDominant_hom
    [Infinite K] (s : V) :
    IsDominant (D.toFiniteMarkedBelyiExistence.map s).hom := by
  rw [D.toFiniteMarkedBelyiExistence_map_apply s]
  exact D.family.map_isDominant_hom s

/-- Each selected finite marked Belyi map has dense range on the underlying
topological spaces. -/
theorem toFiniteMarkedBelyiExistence_map_denseRange_hom
    [Infinite K] (s : V) :
    DenseRange (D.toFiniteMarkedBelyiExistence.map s).hom.base := by
  rw [D.toFiniteMarkedBelyiExistence_map_apply s]
  exact D.family.map_denseRange_hom s

/-- Belyi-open membership for the direct cohomological two-section package is
exactly marked-branch avoidance for the concrete two-section finite map. -/
theorem toFiniteMarkedBelyiExistence_mem_belyiOpen_iff
    [Infinite K] (s : V) (x : C) :
    x ∈ (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
      D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s ↔
      (D.family.map s).hom.base x ∉ markedSchemePointSet K := by
  exact
    D.restricted.twoSectionBezoutFamily_toFiniteMarkedBelyiExistence_mem_belyiOpen_iff
      D.family D.evalPackage_eq s x

/-- The noncritical Belyi open from the paper-facing family is the scheme-level
Belyi open of the concrete two-section finite map. -/
theorem toFiniteMarkedBelyiExistence_belyiOpen_eq_schemeBelyi
    [Infinite K] (s : V) :
    (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
      D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s =
      ((D.family.map s).toBelyiMap.belyiOpen : Set C) := by
  exact
    D.restricted.twoSectionBezoutFamily_toFiniteMarkedBelyiExistence_belyiOpen_eq_schemeBelyi
      D.family D.evalPackage_eq s

/-- Direct finite disjoint-set conclusion from the cohomological two-section
source package. -/
theorem exists_for_finite_disjoint
    [Infinite K] {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V, (∀ x ∈ S, (D.family.map s).hom.base x ∈ markedSchemePointSet K) ∧
      ∀ x ∈ T, (D.family.map s).hom.base x ∉ markedSchemePointSet K := by
  exact
    D.restricted.twoSectionBezoutFamily_exists_for_finite_disjoint
      D.family D.evalPackage_eq hS hT hdis

/-- Direct Belyi-open controls for finite disjoint sets from the cohomological
two-section source package. -/
theorem exists_map_belyiOpen_controls
    [Infinite K] {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V, T ⊆ ((D.family.map s).toBelyiMap.belyiOpen : Set C) ∧
      ((D.family.map s).toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  exact
    D.restricted.twoSectionBezoutFamily_exists_map_belyiOpen_controls
      D.family D.evalPackage_eq hS hT hdis

/-- Direct same-map marked, open, and Belyi-open controls for finite disjoint
sets from the cohomological two-section source package. -/
theorem exists_map_controls_and_isOpen_belyiOpen_controls
    [Infinite K] {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V,
      ((∀ x ∈ S, (D.family.map s).hom.base x ∈ markedSchemePointSet K) ∧
        ∀ x ∈ T, (D.family.map s).hom.base x ∉ markedSchemePointSet K) ∧
        IsOpen ((D.family.map s).toBelyiMap.belyiOpen : Set C) ∧
          T ⊆ ((D.family.map s).toBelyiMap.belyiOpen : Set C) ∧
            ((D.family.map s).toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  exact
    D.restricted.twoSectionBezoutFamily_exists_map_controls_and_isOpen_belyiOpen_controls
      D.family D.evalPackage_eq hS hT hdis

/-- Finite-complement-open form of the direct cohomological two-section
source package, retaining marked controls. -/
theorem exists_map_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_finite_complement
    [Infinite K]
    {U T : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ s : V,
      ((∀ x ∈ Uᶜ, (D.family.map s).hom.base x ∈ markedSchemePointSet K) ∧
        ∀ x ∈ T, (D.family.map s).hom.base x ∉ markedSchemePointSet K) ∧
        IsOpen ((D.family.map s).toBelyiMap.belyiOpen : Set C) ∧
          T ⊆ ((D.family.map s).toBelyiMap.belyiOpen : Set C) ∧
            ((D.family.map s).toBelyiMap.belyiOpen : Set C) ⊆ U := by
  exact
    D.restricted.twoSectionBezoutFamily_exists_map_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_finite_complement
      D.family D.evalPackage_eq hU hUcompl hT hTsub

/-- Nonempty-open finite-complement form of the direct cohomological
two-section source package. -/
theorem exists_map_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
    [Infinite K] [NonemptyOpenFiniteComplement C]
    {U T : Set C} (hU : IsOpen U) (hUne : U.Nonempty)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ s : V,
      ((∀ x ∈ Uᶜ, (D.family.map s).hom.base x ∈ markedSchemePointSet K) ∧
        ∀ x ∈ T, (D.family.map s).hom.base x ∉ markedSchemePointSet K) ∧
        IsOpen ((D.family.map s).toBelyiMap.belyiOpen : Set C) ∧
          T ⊆ ((D.family.map s).toBelyiMap.belyiOpen : Set C) ∧
            ((D.family.map s).toBelyiMap.belyiOpen : Set C) ⊆ U := by
  exact
    D.restricted.twoSectionBezoutFamily_exists_map_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
      D.family D.evalPackage_eq hU hUne hT hTsub

/-- The Belyi open attached to the section `s` in the paper-facing family. -/
def belyiOpen
    [Infinite K] (s : V) : Set C :=
  ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
    D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s)

theorem mem_belyiOpen_iff
    [Infinite K] (s : V) (x : C) :
    x ∈ D.belyiOpen s ↔
      (D.family.map s).hom.base x ∉ markedSchemePointSet K := by
  exact D.toFiniteMarkedBelyiExistence_mem_belyiOpen_iff s x

theorem belyiOpen_eq_schemeBelyi
    [Infinite K] (s : V) :
    D.belyiOpen s = ((D.family.map s).toBelyiMap.belyiOpen : Set C) := by
  exact D.toFiniteMarkedBelyiExistence_belyiOpen_eq_schemeBelyi s

/-- The Belyi opens attached to the direct cohomological two-section finite
marked family. -/
def belyiOpenSetFamily
    [Infinite K] : Set (Set C) :=
  D.toFiniteMarkedBelyiExistence.belyiOpenSetFamily

/-- Corollary 1.2 in basis form, obtained directly from cohomological
restricted evaluation plus the canonical two-section finite marked family. -/
theorem belyiOpenSetFamily_isTopologicalBasis
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] :
    TopologicalSpace.IsTopologicalBasis D.belyiOpenSetFamily :=
  D.toFiniteMarkedBelyiExistence.belyiOpenSetFamily_isTopologicalBasis

/-- The direct cohomological two-section Belyi opens cover the source. -/
theorem belyiOpen_cover_univ
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] :
    (Set.univ : Set C) ⊆ ⋃ s : V, D.belyiOpen s := by
  exact FiniteMarkedBelyiExistence.belyiOpen_cover_univ
    K V D.toFiniteMarkedBelyiExistence

/-- One-point Belyi-open consequence from the direct cohomological two-section
source package. -/
theorem exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C]
    {U : Set C} (hU : IsOpen U) {x : C} (hxU : x ∈ U) :
    ∃ s : V,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        x ∈ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ U := by
  exact
    FiniteMarkedBelyiExistence.exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
      K V D.toFiniteMarkedBelyiExistence hU hxU

/-- Finite-set Belyi-open consequence from the direct cohomological
two-section source package. -/
theorem exists_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C]
    {U T : Set C} (hU : IsOpen U) (hUne : U.Nonempty)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ s : V,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        T ⊆ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ U := by
  exact
    FiniteMarkedBelyiExistence.exists_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
      K V D.toFiniteMarkedBelyiExistence hU hUne hT hTsub

/-- Compact-exhaustion cover bridge for the direct cohomological two-section
source package. -/
theorem finite_compact_cover_by_belyiOpen_exhaustions
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    (Kex : ∀ s : V, CompactExhaustion (D.belyiOpen s)) :
    ∃ t : Finset (V × ℕ),
      (∀ p ∈ t,
        IsCompact ((Subtype.val : D.belyiOpen p.1 → C) '' (Kex p.1 p.2))) ∧
        (∀ p ∈ t,
          ((Subtype.val : D.belyiOpen p.1 → C) '' (Kex p.1 p.2)) ⊆
            D.belyiOpen p.1) ∧
          (Set.univ : Set C) ⊆
            ⋃ p ∈ t, (Subtype.val : D.belyiOpen p.1 → C) '' (Kex p.1 p.2) := by
  exact
    FiniteMarkedBelyiExistence.finite_compact_cover_by_belyiOpen_exhaustions
      K V D.toFiniteMarkedBelyiExistence Kex

/-- Compact-cover bridge for the direct cohomological two-section package,
with compact exhaustions supplied by local compactness and second countability. -/
theorem finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    [LocallyCompactSpace C] [SecondCountableTopology C] :
    ∃ Kex : ∀ s : V, CompactExhaustion (D.belyiOpen s),
      ∃ t : Finset (V × ℕ),
        (∀ p ∈ t,
          IsCompact ((Subtype.val : D.belyiOpen p.1 → C) '' (Kex p.1 p.2))) ∧
          (∀ p ∈ t,
            ((Subtype.val : D.belyiOpen p.1 → C) '' (Kex p.1 p.2)) ⊆
              D.belyiOpen p.1) ∧
            (Set.univ : Set C) ⊆
              ⋃ p ∈ t, (Subtype.val : D.belyiOpen p.1 → C) '' (Kex p.1 p.2) := by
  exact
    FiniteMarkedBelyiExistence.finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact
      K V D.toFiniteMarkedBelyiExistence

end CohomologicalTwoSectionFiniteMarkedSourceData

/-- Cohomological source package with the finite marked two-section family
constructed directly from finite/dominant/étale proofs for the canonical
two-section morphisms.  The evaluation compatibility is reduced to structural
alignment of the two-section data with the restricted evaluation package. -/
structure CohomologicalFiniteDominantEtaleTwoSectionSourceData
    (K : Type u) [Field K] (C : Scheme.{u})
    (V : Type w) [AddCommGroup V] [Module K V] where
  restricted : RestrictedEvaluationSurjectivityData K C V
  hmarkedOpen : IsOpen (markedSchemePointSet K)ᶜ
  twoSection : V → TwoSectionBezoutTrivializedIsUnitData K C V
  hFinite : ∀ s : V, IsFinite (twoSection s).globalHom
  hDominant : ∀ s : V, IsDominant (twoSection s).globalHom
  hEtale :
    ∀ s : V, IsEtale
      (((twoSection s).globalHom) ∣_
        (SchemeBelyi.markedBelyiTarget K hmarkedOpen).branchOpen)
  evalData_eq :
    ∀ s : V,
      (twoSection s).evalData =
        restricted.toRiemannRochFiniteEvaluationPackage.toEvaluationData
  section0_eq : ∀ s : V, (twoSection s).section0 = s
  nonzero_avoids_marked :
    ∀ {T : Set C} {s : V},
      restricted.toRiemannRochFiniteEvaluationPackage.toEvaluationData.nonzeroOnSet T s →
        ∀ x ∈ T, (twoSection s).globalHom.base x ∉ markedSchemePointSet K

namespace CohomologicalFiniteDominantEtaleTwoSectionSourceData

variable (D : CohomologicalFiniteDominantEtaleTwoSectionSourceData K C V)

/-- The canonical finite marked two-section family constructed from the direct
finite/dominant/étale source data. -/
noncomputable def family : TwoSectionBezoutProjectiveSectionFiniteMarkedFamily K C V :=
  TwoSectionBezoutProjectiveSectionFiniteMarkedFamily.ofFiniteDominantEtaleTwoSectionAligned
    D.restricted.toRiemannRochFiniteEvaluationPackage D.hmarkedOpen D.twoSection
    D.hFinite D.hDominant D.hEtale D.evalData_eq D.section0_eq
    D.nonzero_avoids_marked

theorem family_evalPackage :
    D.family.evalPackage = D.restricted.toRiemannRochFiniteEvaluationPackage := rfl

theorem family_hmarkedOpen :
    D.family.hmarkedOpen = D.hmarkedOpen := rfl

theorem family_twoSection :
    D.family.twoSection = D.twoSection := by
  exact
    TwoSectionBezoutProjectiveSectionFiniteMarkedFamily.ofFiniteDominantEtaleTwoSectionAligned_twoSection
      D.restricted.toRiemannRochFiniteEvaluationPackage D.hmarkedOpen D.twoSection
      D.hFinite D.hDominant D.hEtale D.evalData_eq D.section0_eq
      D.nonzero_avoids_marked

theorem family_map_hom (s : V) :
    (D.family.map s).hom = (D.twoSection s).globalHom := by
  exact
    TwoSectionBezoutProjectiveSectionFiniteMarkedFamily.ofFiniteDominantEtaleTwoSectionAligned_map_hom
      D.restricted.toRiemannRochFiniteEvaluationPackage D.hmarkedOpen D.twoSection
      D.hFinite D.hDominant D.hEtale D.evalData_eq D.section0_eq
      D.nonzero_avoids_marked s

theorem family_trivialized_eq_lifted (s : V) :
    D.family.trivialized s =
      (D.twoSection s).toTrivializedIsUnitSectionRatioDataLifted := by
  exact
    TwoSectionBezoutProjectiveSectionFiniteMarkedFamily.ofFiniteDominantEtaleTwoSectionAligned_trivialized_eq_lifted
      D.restricted.toRiemannRochFiniteEvaluationPackage D.hmarkedOpen D.twoSection
      D.hFinite D.hDominant D.hEtale D.evalData_eq D.section0_eq
      D.nonzero_avoids_marked s

/-- Forget the direct finite/dominant/étale source package to the previously
checked cohomological two-section source package. -/
noncomputable def toCohomologicalTwoSectionFiniteMarkedSourceData :
    CohomologicalTwoSectionFiniteMarkedSourceData K C V where
  restricted := D.restricted
  family := D.family
  evalPackage_eq := D.family_evalPackage

/-- The paper-facing finite marked Belyi family obtained from the direct
finite/dominant/étale cohomological source package. -/
noncomputable def toFiniteMarkedBelyiExistence
    [Infinite K] : FiniteMarkedBelyiExistence K V C :=
  D.toCohomologicalTwoSectionFiniteMarkedSourceData.toFiniteMarkedBelyiExistence

theorem toFiniteMarkedBelyiExistence_hmarkedOpen
    [Infinite K] :
    D.toFiniteMarkedBelyiExistence.hmarkedOpen = D.hmarkedOpen := by
  calc
    D.toFiniteMarkedBelyiExistence.hmarkedOpen =
        D.toCohomologicalTwoSectionFiniteMarkedSourceData.family.hmarkedOpen := by
      exact
        CohomologicalTwoSectionFiniteMarkedSourceData.toFiniteMarkedBelyiExistence_hmarkedOpen
          D.toCohomologicalTwoSectionFiniteMarkedSourceData
    _ = D.hmarkedOpen := D.family_hmarkedOpen

theorem toFiniteMarkedBelyiExistence_map_apply
    [Infinite K] (s : V) :
    D.toFiniteMarkedBelyiExistence.map s = D.family.map s := by
  change
    D.toCohomologicalTwoSectionFiniteMarkedSourceData.toFiniteMarkedBelyiExistence.map s =
      D.toCohomologicalTwoSectionFiniteMarkedSourceData.family.map s
  exact
    CohomologicalTwoSectionFiniteMarkedSourceData.toFiniteMarkedBelyiExistence_map_apply
      D.toCohomologicalTwoSectionFiniteMarkedSourceData s

theorem toFiniteMarkedBelyiExistence_map_hom
    [Infinite K] (s : V) :
    (D.toFiniteMarkedBelyiExistence.map s).hom =
      (D.twoSection s).globalHom := by
  calc
    (D.toFiniteMarkedBelyiExistence.map s).hom =
        (D.toCohomologicalTwoSectionFiniteMarkedSourceData.family.map s).hom := by
      change
        (D.toCohomologicalTwoSectionFiniteMarkedSourceData.toFiniteMarkedBelyiExistence.map s).hom =
          (D.toCohomologicalTwoSectionFiniteMarkedSourceData.family.map s).hom
      rw [CohomologicalTwoSectionFiniteMarkedSourceData.toFiniteMarkedBelyiExistence_map_apply]
    _ = (D.twoSection s).globalHom := D.family_map_hom s

theorem toFiniteMarkedBelyiExistence_map_finite_hom
    [Infinite K] (s : V) :
    IsFinite (D.toFiniteMarkedBelyiExistence.map s).hom := by
  change
    IsFinite
      (D.toCohomologicalTwoSectionFiniteMarkedSourceData.toFiniteMarkedBelyiExistence.map s).hom
  exact
    CohomologicalTwoSectionFiniteMarkedSourceData.toFiniteMarkedBelyiExistence_map_finite_hom
      D.toCohomologicalTwoSectionFiniteMarkedSourceData s

/-- Each finite marked Belyi map selected by the direct finite/dominant/étale
two-section source package is dominant. -/
theorem toFiniteMarkedBelyiExistence_map_isDominant_hom
    [Infinite K] (s : V) :
    IsDominant (D.toFiniteMarkedBelyiExistence.map s).hom := by
  change
    IsDominant
      (D.toCohomologicalTwoSectionFiniteMarkedSourceData.toFiniteMarkedBelyiExistence.map s).hom
  exact
    CohomologicalTwoSectionFiniteMarkedSourceData.toFiniteMarkedBelyiExistence_map_isDominant_hom
      D.toCohomologicalTwoSectionFiniteMarkedSourceData s

/-- Each selected finite marked Belyi map has dense range on the underlying
topological spaces. -/
theorem toFiniteMarkedBelyiExistence_map_denseRange_hom
    [Infinite K] (s : V) :
    DenseRange (D.toFiniteMarkedBelyiExistence.map s).hom.base := by
  change
    DenseRange
      (D.toCohomologicalTwoSectionFiniteMarkedSourceData.toFiniteMarkedBelyiExistence.map s).hom.base
  exact
    CohomologicalTwoSectionFiniteMarkedSourceData.toFiniteMarkedBelyiExistence_map_denseRange_hom
      D.toCohomologicalTwoSectionFiniteMarkedSourceData s

theorem toFiniteMarkedBelyiExistence_mem_belyiOpen_iff
    [Infinite K] (s : V) (x : C) :
    x ∈ (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
      D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s ↔
      (D.twoSection s).globalHom.base x ∉ markedSchemePointSet K := by
  calc
    x ∈ (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s ↔
        (D.toCohomologicalTwoSectionFiniteMarkedSourceData.family.map s).hom.base x ∉
          markedSchemePointSet K := by
      exact
        CohomologicalTwoSectionFiniteMarkedSourceData.toFiniteMarkedBelyiExistence_mem_belyiOpen_iff
          D.toCohomologicalTwoSectionFiniteMarkedSourceData s x
    _ ↔ (D.twoSection s).globalHom.base x ∉ markedSchemePointSet K := by
      change (D.family.map s).hom.base x ∉ markedSchemePointSet K ↔
        (D.twoSection s).globalHom.base x ∉ markedSchemePointSet K
      rw [D.family_map_hom s]

/-- The packaged noncritical Belyi open agrees with the scheme-level Belyi open
of the selected finite marked Belyi map. -/
theorem toFiniteMarkedBelyiExistence_belyiOpen_eq_schemeBelyi
    [Infinite K] (s : V) :
    (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
      D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s =
      ((D.toFiniteMarkedBelyiExistence.map s).toBelyiMap.belyiOpen : Set C) := by
  exact
    FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence_belyiOpen_eq_schemeBelyi
      K V D.toFiniteMarkedBelyiExistence s

/-- Direct two-section form of the finite disjoint-set conclusion. -/
theorem exists_twoSection_controls_for_finite_disjoint
    [Infinite K]
    {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V,
      (∀ x ∈ S, (D.twoSection s).globalHom.base x ∈ markedSchemePointSet K) ∧
        ∀ x ∈ T, (D.twoSection s).globalHom.base x ∉ markedSchemePointSet K := by
  rcases D.toFiniteMarkedBelyiExistence.exists_for_finite_disjoint
      hS hT hdis with
    ⟨s, hSctrl, hTctrl⟩
  refine ⟨s, ?_, ?_⟩
  · intro x hx
    simpa [D.toFiniteMarkedBelyiExistence_map_hom s] using hSctrl x hx
  · intro x hx
    simpa [D.toFiniteMarkedBelyiExistence_map_hom s] using hTctrl x hx

/-- Direct two-section form of the open-containment conclusion in a
finite-complement source topology. -/
theorem exists_twoSection_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
    [Infinite K] [NonemptyOpenFiniteComplement C]
    {U T : Set C} (hU : IsOpen U) (hUne : U.Nonempty)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ s : V,
      ((∀ x ∈ Uᶜ, (D.twoSection s).globalHom.base x ∈ markedSchemePointSet K) ∧
        ∀ x ∈ T, (D.twoSection s).globalHom.base x ∉ markedSchemePointSet K) ∧
        IsOpen ((D.toFiniteMarkedBelyiExistence.map s).toBelyiMap.belyiOpen : Set C) ∧
          T ⊆ ((D.toFiniteMarkedBelyiExistence.map s).toBelyiMap.belyiOpen : Set C) ∧
            ((D.toFiniteMarkedBelyiExistence.map s).toBelyiMap.belyiOpen : Set C) ⊆ U := by
  rcases
      CohomologicalTwoSectionFiniteMarkedSourceData.exists_map_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
        D.toCohomologicalTwoSectionFiniteMarkedSourceData hU hUne hT hTsub with
    ⟨s, hcontrols, hopen, hTopen, hopenU⟩
  refine ⟨s, ?_, ?_, ?_, ?_⟩
  · exact ⟨fun x hx => by
        simpa [D.family_map_hom s] using hcontrols.1 x hx,
      fun x hx => by
        simpa [D.family_map_hom s] using hcontrols.2 x hx⟩
  · simpa [D.toFiniteMarkedBelyiExistence_map_apply s] using hopen
  · simpa [D.toFiniteMarkedBelyiExistence_map_apply s] using hTopen
  · simpa [D.toFiniteMarkedBelyiExistence_map_apply s] using hopenU

/-- The Belyi open attached to a direct finite/dominant/étale two-section source
parameter. -/
def belyiOpen
    [Infinite K] (s : V) : Set C :=
  ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
    D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s)

theorem mem_belyiOpen_iff
    [Infinite K] (s : V) (x : C) :
    x ∈ D.belyiOpen s ↔
      (D.twoSection s).globalHom.base x ∉ markedSchemePointSet K := by
  exact D.toFiniteMarkedBelyiExistence_mem_belyiOpen_iff s x

theorem belyiOpen_eq_schemeBelyi
    [Infinite K] (s : V) :
    D.belyiOpen s =
      ((D.toFiniteMarkedBelyiExistence.map s).toBelyiMap.belyiOpen : Set C) := by
  exact D.toFiniteMarkedBelyiExistence_belyiOpen_eq_schemeBelyi s

/-- The Belyi opens attached to the finite marked Belyi family selected from the
direct finite/dominant/étale two-section source package. -/
def belyiOpenSetFamily
    [Infinite K] : Set (Set C) :=
  D.toFiniteMarkedBelyiExistence.belyiOpenSetFamily

/-- Corollary 1.2 in basis form directly from the direct finite/dominant/étale
two-section source package. -/
theorem belyiOpenSetFamily_isTopologicalBasis
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] :
    TopologicalSpace.IsTopologicalBasis D.belyiOpenSetFamily :=
  D.toFiniteMarkedBelyiExistence.belyiOpenSetFamily_isTopologicalBasis

/-- The Belyi opens produced from the direct finite/dominant/étale two-section
source package cover the source. -/
theorem belyiOpen_cover_univ
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] :
    (Set.univ : Set C) ⊆ ⋃ s : V, D.belyiOpen s := by
  exact FiniteMarkedBelyiExistence.belyiOpen_cover_univ
    K V D.toFiniteMarkedBelyiExistence

/-- Finite-set Belyi-open consequence directly from the direct
finite/dominant/étale two-section source package in the curve-style
finite-complement topology form. -/
theorem exists_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C]
    {U T : Set C} (hU : IsOpen U) (hUne : U.Nonempty)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ s : V,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        T ⊆ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ U := by
  exact
    FiniteMarkedBelyiExistence.exists_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
      K V D.toFiniteMarkedBelyiExistence hU hUne hT hTsub

/-- Compact-cover bridge for direct finite/dominant/étale two-section source
Belyi opens, with compact exhaustions supplied by local compactness and second
countability. -/
theorem finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    [LocallyCompactSpace C] [SecondCountableTopology C] :
    ∃ Kex : ∀ s : V, CompactExhaustion (D.belyiOpen s),
      ∃ t : Finset (V × ℕ),
        (∀ p ∈ t,
          IsCompact ((Subtype.val : D.belyiOpen p.1 → C) '' (Kex p.1 p.2))) ∧
          (∀ p ∈ t,
            ((Subtype.val : D.belyiOpen p.1 → C) '' (Kex p.1 p.2)) ⊆
              D.belyiOpen p.1) ∧
            (Set.univ : Set C) ⊆
              ⋃ p ∈ t, (Subtype.val : D.belyiOpen p.1 → C) '' (Kex p.1 p.2) := by
  exact
    FiniteMarkedBelyiExistence.finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact
      K V D.toFiniteMarkedBelyiExistence

end CohomologicalFiniteDominantEtaleTwoSectionSourceData

/-- Cohomological source package whose two-section maps use the constructed
chart-ring maps coming from the canonical unit ratios on the two Bezout basic
opens.  This is the same finite/dominant/étale bridge as
`CohomologicalFiniteDominantEtaleTwoSectionSourceData`, but with the explicit
local chart-ring maps removed from the source data. -/
structure CohomologicalConstructedFiniteDominantEtaleTwoSectionSourceData
    (K : Type u) [Field K] (C : Scheme.{u})
    (V : Type w) [AddCommGroup V] [Module K V] where
  restricted : RestrictedEvaluationSurjectivityData K C V
  hmarkedOpen : IsOpen (markedSchemePointSet K)ᶜ
  twoSection : V → TwoSectionBezoutConstructedTrivializedIsUnitData K C V
  hFinite : ∀ s : V, IsFinite (twoSection s).globalHom
  hDominant : ∀ s : V, IsDominant (twoSection s).globalHom
  hEtale :
    ∀ s : V, IsEtale
      (((twoSection s).globalHom) ∣_
        (SchemeBelyi.markedBelyiTarget K hmarkedOpen).branchOpen)
  evalData_eq :
    ∀ s : V,
      (twoSection s).evalData =
        restricted.toRiemannRochFiniteEvaluationPackage.toEvaluationData
  section0_eq : ∀ s : V, (twoSection s).section0 = s
  nonzero_avoids_marked :
    ∀ {T : Set C} {s : V},
      restricted.toRiemannRochFiniteEvaluationPackage.toEvaluationData.nonzeroOnSet T s →
        ∀ x ∈ T, (twoSection s).globalHom.base x ∉ markedSchemePointSet K

namespace CohomologicalConstructedFiniteDominantEtaleTwoSectionSourceData

variable (D : CohomologicalConstructedFiniteDominantEtaleTwoSectionSourceData K C V)

/-- The explicit two-section package obtained by forgetting that the local
chart-ring maps were constructed from unit ratios. -/
noncomputable def explicitTwoSection (s : V) :
    TwoSectionBezoutTrivializedIsUnitData K C V :=
  (D.twoSection s).toTwoSectionBezoutTrivializedIsUnitData

theorem explicitTwoSection_globalHom (s : V) :
    (D.explicitTwoSection s).globalHom = (D.twoSection s).globalHom := rfl

theorem explicitTwoSection_evalData (s : V) :
    (D.explicitTwoSection s).evalData = (D.twoSection s).evalData := rfl

theorem explicitTwoSection_section0 (s : V) :
    (D.explicitTwoSection s).section0 = (D.twoSection s).section0 := rfl

/-- Forget constructed chart maps to the direct finite/dominant/étale
cohomological source package with explicit two-section data. -/
noncomputable def toCohomologicalFiniteDominantEtaleTwoSectionSourceData :
    CohomologicalFiniteDominantEtaleTwoSectionSourceData K C V where
  restricted := D.restricted
  hmarkedOpen := D.hmarkedOpen
  twoSection := D.explicitTwoSection
  hFinite := by
    intro s
    simpa [explicitTwoSection] using D.hFinite s
  hDominant := by
    intro s
    simpa [explicitTwoSection] using D.hDominant s
  hEtale := by
    intro s
    simpa [explicitTwoSection] using D.hEtale s
  evalData_eq := by
    intro s
    simpa [explicitTwoSection] using D.evalData_eq s
  section0_eq := by
    intro s
    simpa [explicitTwoSection] using D.section0_eq s
  nonzero_avoids_marked := by
    intro T s hT x hx
    simpa [explicitTwoSection] using D.nonzero_avoids_marked hT x hx

/-- The finite marked two-section family obtained from constructed local chart
maps. -/
noncomputable def family : TwoSectionBezoutProjectiveSectionFiniteMarkedFamily K C V :=
  D.toCohomologicalFiniteDominantEtaleTwoSectionSourceData.family

theorem family_map_hom (s : V) :
    (D.family.map s).hom = (D.twoSection s).globalHom := by
  exact
    D.toCohomologicalFiniteDominantEtaleTwoSectionSourceData.family_map_hom s

/-- The paper-facing finite marked Belyi family obtained from the constructed
finite/dominant/étale cohomological source package. -/
noncomputable def toFiniteMarkedBelyiExistence
    [Infinite K] : FiniteMarkedBelyiExistence K V C :=
  D.toCohomologicalFiniteDominantEtaleTwoSectionSourceData.toFiniteMarkedBelyiExistence

theorem toFiniteMarkedBelyiExistence_hmarkedOpen
    [Infinite K] :
    D.toFiniteMarkedBelyiExistence.hmarkedOpen = D.hmarkedOpen := by
  exact
    D.toCohomologicalFiniteDominantEtaleTwoSectionSourceData.toFiniteMarkedBelyiExistence_hmarkedOpen

theorem toFiniteMarkedBelyiExistence_map_hom
    [Infinite K] (s : V) :
    (D.toFiniteMarkedBelyiExistence.map s).hom =
      (D.twoSection s).globalHom := by
  exact
    D.toCohomologicalFiniteDominantEtaleTwoSectionSourceData.toFiniteMarkedBelyiExistence_map_hom s

theorem toFiniteMarkedBelyiExistence_mem_belyiOpen_iff
    [Infinite K] (s : V) (x : C) :
    x ∈ (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
      D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s ↔
      (D.twoSection s).globalHom.base x ∉ markedSchemePointSet K := by
  exact
    D.toCohomologicalFiniteDominantEtaleTwoSectionSourceData.toFiniteMarkedBelyiExistence_mem_belyiOpen_iff
      s x

/-- Direct constructed two-section form of the finite disjoint-set conclusion. -/
theorem exists_twoSection_controls_for_finite_disjoint
    [Infinite K]
    {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V,
      (∀ x ∈ S, (D.twoSection s).globalHom.base x ∈ markedSchemePointSet K) ∧
        ∀ x ∈ T, (D.twoSection s).globalHom.base x ∉ markedSchemePointSet K := by
  exact
    D.toCohomologicalFiniteDominantEtaleTwoSectionSourceData.exists_twoSection_controls_for_finite_disjoint
      hS hT hdis

/-- The Belyi open attached to a constructed finite/dominant/étale two-section
source parameter. -/
def belyiOpen
    [Infinite K] (s : V) : Set C :=
  ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
    D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s)

theorem mem_belyiOpen_iff
    [Infinite K] (s : V) (x : C) :
    x ∈ D.belyiOpen s ↔
      (D.twoSection s).globalHom.base x ∉ markedSchemePointSet K := by
  exact D.toFiniteMarkedBelyiExistence_mem_belyiOpen_iff s x

theorem belyiOpen_eq_schemeBelyi
    [Infinite K] (s : V) :
    D.belyiOpen s =
      ((D.toFiniteMarkedBelyiExistence.map s).toBelyiMap.belyiOpen : Set C) := by
  exact
    D.toCohomologicalFiniteDominantEtaleTwoSectionSourceData.belyiOpen_eq_schemeBelyi s

theorem exists_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C]
    {U T : Set C} (hU : IsOpen U) (hUne : U.Nonempty)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ s : V,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        T ⊆ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ U := by
  exact
    D.toCohomologicalFiniteDominantEtaleTwoSectionSourceData.exists_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
      hU hUne hT hTsub

end CohomologicalConstructedFiniteDominantEtaleTwoSectionSourceData

/-- Cohomological source package whose two-section maps use local chart-ring
maps constructed from canonical unit ratios, with the local `K`-algebra
structures induced by structure morphisms to `Spec K`.  Compared with
`CohomologicalConstructedFiniteDominantEtaleTwoSectionSourceData`, this
removes the local algebra structures from the source data. -/
structure CohomologicalStructuredFiniteDominantEtaleTwoSectionSourceData
    (K : Type u) [Field K] (C : Scheme.{u})
    (V : Type w) [AddCommGroup V] [Module K V] where
  restricted : RestrictedEvaluationSurjectivityData K C V
  hmarkedOpen : IsOpen (markedSchemePointSet K)ᶜ
  twoSection : V → TwoSectionBezoutStructuredTrivializedIsUnitData K C V
  hFinite : ∀ s : V, IsFinite (twoSection s).globalHom
  hDominant : ∀ s : V, IsDominant (twoSection s).globalHom
  hEtale :
    ∀ s : V, IsEtale
      (((twoSection s).globalHom) ∣_
        (SchemeBelyi.markedBelyiTarget K hmarkedOpen).branchOpen)
  evalData_eq :
    ∀ s : V,
      (twoSection s).evalData =
        restricted.toRiemannRochFiniteEvaluationPackage.toEvaluationData
  section0_eq : ∀ s : V, (twoSection s).section0 = s
  nonzero_avoids_marked :
    ∀ {T : Set C} {s : V},
      restricted.toRiemannRochFiniteEvaluationPackage.toEvaluationData.nonzeroOnSet T s →
        ∀ x ∈ T, (twoSection s).globalHom.base x ∉ markedSchemePointSet K

namespace CohomologicalStructuredFiniteDominantEtaleTwoSectionSourceData

variable (D : CohomologicalStructuredFiniteDominantEtaleTwoSectionSourceData K C V)

/-- The constructed two-section package obtained by forgetting that the local
`K`-algebra structures came from a structure morphism. -/
noncomputable def constructedTwoSection (s : V) :
    TwoSectionBezoutConstructedTrivializedIsUnitData K C V :=
  (D.twoSection s).toTwoSectionBezoutConstructedTrivializedIsUnitData

theorem constructedTwoSection_globalHom (s : V) :
    (D.constructedTwoSection s).globalHom = (D.twoSection s).globalHom := rfl

theorem constructedTwoSection_evalData (s : V) :
    (D.constructedTwoSection s).evalData = (D.twoSection s).evalData := rfl

theorem constructedTwoSection_section0 (s : V) :
    (D.constructedTwoSection s).section0 = (D.twoSection s).section0 := rfl

/-- Forget structure-morphism-induced local algebras to the constructed
finite/dominant/étale cohomological source package. -/
noncomputable def toCohomologicalConstructedFiniteDominantEtaleTwoSectionSourceData :
    CohomologicalConstructedFiniteDominantEtaleTwoSectionSourceData K C V where
  restricted := D.restricted
  hmarkedOpen := D.hmarkedOpen
  twoSection := D.constructedTwoSection
  hFinite := by
    intro s
    simpa [constructedTwoSection] using D.hFinite s
  hDominant := by
    intro s
    simpa [constructedTwoSection] using D.hDominant s
  hEtale := by
    intro s
    simpa [constructedTwoSection] using D.hEtale s
  evalData_eq := by
    intro s
    simpa [constructedTwoSection] using D.evalData_eq s
  section0_eq := by
    intro s
    simpa [constructedTwoSection] using D.section0_eq s
  nonzero_avoids_marked := by
    intro T s hT x hx
    simpa [constructedTwoSection] using D.nonzero_avoids_marked hT x hx

/-- The finite marked two-section family obtained from structured local chart
maps. -/
noncomputable def family : TwoSectionBezoutProjectiveSectionFiniteMarkedFamily K C V :=
  TwoSectionBezoutProjectiveSectionFiniteMarkedFamily.ofStructuredFiniteDominantEtaleTwoSectionAligned
    D.restricted.toRiemannRochFiniteEvaluationPackage D.hmarkedOpen D.twoSection
    D.hFinite D.hDominant D.hEtale D.evalData_eq D.section0_eq
    D.nonzero_avoids_marked

theorem family_evalPackage :
    D.family.evalPackage = D.restricted.toRiemannRochFiniteEvaluationPackage := rfl

theorem family_hmarkedOpen :
    D.family.hmarkedOpen = D.hmarkedOpen := rfl

theorem family_twoSection :
    D.family.twoSection =
      TwoSectionBezoutProjectiveSectionFiniteMarkedFamily.explicitTwoSectionOfStructured
        D.twoSection := by
  exact
    TwoSectionBezoutProjectiveSectionFiniteMarkedFamily.ofStructuredFiniteDominantEtaleTwoSectionAligned_twoSection
      D.restricted.toRiemannRochFiniteEvaluationPackage D.hmarkedOpen D.twoSection
      D.hFinite D.hDominant D.hEtale D.evalData_eq D.section0_eq
      D.nonzero_avoids_marked

theorem family_map_hom (s : V) :
    (D.family.map s).hom = (D.twoSection s).globalHom := by
  exact
    TwoSectionBezoutProjectiveSectionFiniteMarkedFamily.ofStructuredFiniteDominantEtaleTwoSectionAligned_map_hom
      D.restricted.toRiemannRochFiniteEvaluationPackage D.hmarkedOpen D.twoSection
      D.hFinite D.hDominant D.hEtale D.evalData_eq D.section0_eq
      D.nonzero_avoids_marked s

/-- Forget the structured finite/dominant/étale source package to the general
cohomological two-section source interface. -/
noncomputable def toCohomologicalTwoSectionFiniteMarkedSourceData :
    CohomologicalTwoSectionFiniteMarkedSourceData K C V where
  restricted := D.restricted
  family := D.family
  evalPackage_eq := D.family_evalPackage

/-- The paper-facing finite marked Belyi family obtained from the structured
finite/dominant/étale cohomological source package. -/
noncomputable def toFiniteMarkedBelyiExistence
    [Infinite K] : FiniteMarkedBelyiExistence K V C :=
  D.toCohomologicalTwoSectionFiniteMarkedSourceData.toFiniteMarkedBelyiExistence

theorem toFiniteMarkedBelyiExistence_hmarkedOpen
    [Infinite K] :
    D.toFiniteMarkedBelyiExistence.hmarkedOpen = D.hmarkedOpen := by
  calc
    D.toFiniteMarkedBelyiExistence.hmarkedOpen =
        D.toCohomologicalTwoSectionFiniteMarkedSourceData.family.hmarkedOpen := by
      exact
        CohomologicalTwoSectionFiniteMarkedSourceData.toFiniteMarkedBelyiExistence_hmarkedOpen
          D.toCohomologicalTwoSectionFiniteMarkedSourceData
    _ = D.hmarkedOpen := D.family_hmarkedOpen

theorem toFiniteMarkedBelyiExistence_map_apply
    [Infinite K] (s : V) :
    D.toFiniteMarkedBelyiExistence.map s = D.family.map s := by
  change
    D.toCohomologicalTwoSectionFiniteMarkedSourceData.toFiniteMarkedBelyiExistence.map s =
      D.toCohomologicalTwoSectionFiniteMarkedSourceData.family.map s
  exact
    CohomologicalTwoSectionFiniteMarkedSourceData.toFiniteMarkedBelyiExistence_map_apply
      D.toCohomologicalTwoSectionFiniteMarkedSourceData s

theorem toFiniteMarkedBelyiExistence_map_hom
    [Infinite K] (s : V) :
    (D.toFiniteMarkedBelyiExistence.map s).hom =
      (D.twoSection s).globalHom := by
  calc
    (D.toFiniteMarkedBelyiExistence.map s).hom =
        (D.toCohomologicalTwoSectionFiniteMarkedSourceData.family.map s).hom := by
      change
        (D.toCohomologicalTwoSectionFiniteMarkedSourceData.toFiniteMarkedBelyiExistence.map s).hom =
          (D.toCohomologicalTwoSectionFiniteMarkedSourceData.family.map s).hom
      rw [CohomologicalTwoSectionFiniteMarkedSourceData.toFiniteMarkedBelyiExistence_map_apply]
    _ = (D.twoSection s).globalHom := D.family_map_hom s

theorem toFiniteMarkedBelyiExistence_mem_belyiOpen_iff
    [Infinite K] (s : V) (x : C) :
    x ∈ (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
      D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s ↔
      (D.twoSection s).globalHom.base x ∉ markedSchemePointSet K := by
  calc
    x ∈ (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s ↔
        (D.toCohomologicalTwoSectionFiniteMarkedSourceData.family.map s).hom.base x ∉
          markedSchemePointSet K := by
      exact
        CohomologicalTwoSectionFiniteMarkedSourceData.toFiniteMarkedBelyiExistence_mem_belyiOpen_iff
          D.toCohomologicalTwoSectionFiniteMarkedSourceData s x
    _ ↔ (D.twoSection s).globalHom.base x ∉ markedSchemePointSet K := by
      change (D.family.map s).hom.base x ∉ markedSchemePointSet K ↔
        (D.twoSection s).globalHom.base x ∉ markedSchemePointSet K
      rw [D.family_map_hom s]

/-- Direct structured two-section form of the finite disjoint-set conclusion. -/
theorem exists_twoSection_controls_for_finite_disjoint
    [Infinite K]
    {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V,
      (∀ x ∈ S, (D.twoSection s).globalHom.base x ∈ markedSchemePointSet K) ∧
        ∀ x ∈ T, (D.twoSection s).globalHom.base x ∉ markedSchemePointSet K := by
  exact
    D.toCohomologicalConstructedFiniteDominantEtaleTwoSectionSourceData.exists_twoSection_controls_for_finite_disjoint
      hS hT hdis

/-- The Belyi open attached to a structured finite/dominant/étale two-section
source parameter. -/
def belyiOpen
    [Infinite K] (s : V) : Set C :=
  ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
    D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s)

theorem mem_belyiOpen_iff
    [Infinite K] (s : V) (x : C) :
    x ∈ D.belyiOpen s ↔
      (D.twoSection s).globalHom.base x ∉ markedSchemePointSet K := by
  exact D.toFiniteMarkedBelyiExistence_mem_belyiOpen_iff s x

theorem belyiOpen_eq_schemeBelyi
    [Infinite K] (s : V) :
    D.belyiOpen s =
      ((D.toFiniteMarkedBelyiExistence.map s).toBelyiMap.belyiOpen : Set C) := by
  exact
    FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence_belyiOpen_eq_schemeBelyi
      K V D.toFiniteMarkedBelyiExistence s

theorem exists_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C]
    {U T : Set C} (hU : IsOpen U) (hUne : U.Nonempty)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ s : V,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        T ⊆ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ U := by
  exact
    D.toCohomologicalConstructedFiniteDominantEtaleTwoSectionSourceData.exists_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
      hU hUne hT hTsub

end CohomologicalStructuredFiniteDominantEtaleTwoSectionSourceData

end SchemeTwoSectionSource

/-- Cohomological divisor-section data: evaluation surjectivity plus the
zero-section of the divisor line bundle. -/
structure CohomologicalDivisorSectionData
    (K : Type u) [Field K] (X : Type v)
    (V : Type w) [AddCommGroup V] [Module K V] where
  evalSurjectivity : EvaluationSurjectivityData K X V
  zeroSection : V
  zeroSection_hasZeroSet :
    HasZeroSet evalSurjectivity.evalData zeroSection evalSurjectivity.support

namespace CohomologicalDivisorSectionData

variable (D : CohomologicalDivisorSectionData K X V)

/-- Forget cohomological evaluation-surjectivity data to the divisor
zero-section package. -/
def toDivisorZeroSectionData : DivisorZeroSectionData K X V where
  evalData := D.evalSurjectivity.evalData
  support := D.evalSurjectivity.support
  zeroSection := D.zeroSection
  zeroSection_hasZeroSet := D.zeroSection_hasZeroSet
  eval_nonzero_on_support := D.evalSurjectivity.eval_nonzero_on_support

theorem toDivisorZeroSectionData_support :
    D.toDivisorZeroSectionData.support = D.evalSurjectivity.support := rfl

/-- The cohomological divisor zero-section vanishes at exactly the support
points. -/
theorem zeroSection_eval_eq_zero_iff_mem_support (x : X) :
    D.evalSurjectivity.evalData.eval x D.zeroSection = 0 ↔
      x ∈ D.evalSurjectivity.support := by
  exact D.toDivisorZeroSectionData.zeroSection_eval_eq_zero_iff_mem_support x

/-- Away from the cohomological divisor support, the distinguished zero-section
is nonzero. -/
theorem zeroSection_eval_ne_zero_iff_not_mem_support (x : X) :
    D.evalSurjectivity.evalData.eval x D.zeroSection ≠ 0 ↔
      x ∉ D.evalSurjectivity.support := by
  exact D.toDivisorZeroSectionData.zeroSection_eval_ne_zero_iff_not_mem_support x

/-- The cohomological source package supplies a second section nonzero on the
divisor support. -/
theorem exists_section_nonzero_on_support
    [Infinite K] (hsupport : D.evalSurjectivity.support.Finite) :
    ∃ s1 : V, D.evalSurjectivity.evalData.nonzeroOnSet
      D.evalSurjectivity.support s1 := by
  exact D.toDivisorZeroSectionData.exists_section_nonzero_on_support hsupport

/-- The cohomological source package supplies a basepoint-free pair
`(s0, s1)`. -/
theorem exists_second_section_no_common_zero
    [Infinite K] (hsupport : D.evalSurjectivity.support.Finite) :
    ∃ s1 : V, HasNoCommonZero
      D.evalSurjectivity.evalData D.zeroSection s1 := by
  exact D.toDivisorZeroSectionData.exists_second_section_no_common_zero hsupport

section SchemeSupport

open AlgebraicGeometry
open CategoryTheory

variable {C : Scheme.{u}}

/-- After the cohomological divisor package is upgraded to a projective-line
section pair, the divisor support maps to the marked branch point `0`. -/
theorem projectivePair_maps_support_to_zeroPoint
    (D : CohomologicalDivisorSectionData K C V)
    (P : ProjectiveLineSectionPair K C V)
    (heval : P.evalData = D.evalSurjectivity.evalData)
    (hsection0 : P.section0 = D.zeroSection) :
    ∀ x ∈ D.evalSurjectivity.support,
      P.hom.base x = schemeCarrierPoint K MarkedPointLabel.zero := by
  exact
    D.toDivisorZeroSectionData.projectivePair_maps_support_to_zeroPoint
      P heval hsection0

/-- Away from the cohomological divisor support, the associated projective-line
morphism avoids the checked zero point. -/
theorem projectivePair_avoids_zeroPoint_off_support
    (D : CohomologicalDivisorSectionData K C V)
    (P : ProjectiveLineSectionPair K C V)
    (heval : P.evalData = D.evalSurjectivity.evalData)
    (hsection0 : P.section0 = D.zeroSection) :
    ∀ x ∉ D.evalSurjectivity.support,
      P.hom.base x ≠ schemeCarrierPoint K MarkedPointLabel.zero := by
  exact
    D.toDivisorZeroSectionData.projectivePair_avoids_zeroPoint_off_support
      P heval hsection0

/-- After the cohomological divisor package is upgraded to a projective-line
section pair, the divisor support maps to the marked branch point `0`. -/
theorem projectivePair_maps_support_to_marked
    (D : CohomologicalDivisorSectionData K C V)
    (P : ProjectiveLineSectionPair K C V)
    (heval : P.evalData = D.evalSurjectivity.evalData)
    (hsection0 : P.section0 = D.zeroSection) :
    ∀ x ∈ D.evalSurjectivity.support, P.hom.base x ∈ markedSchemePointSet K := by
  intro x hx
  have hzero : P.evalData.eval x P.section0 = 0 := by
    rw [heval, hsection0]
    exact (D.zeroSection_hasZeroSet x).2 hx
  exact P.maps_section0_zero_to_marked hzero

/-- If the canonical two-section finite marked family uses the cohomological
divisor evaluation data, then the finite marked Belyi map attached to the
cohomological zero-section sends the divisor support to the marked branch set. -/
theorem twoSectionBezoutFamily_zeroSection_maps_support_to_marked
    (D : CohomologicalDivisorSectionData K C V)
    (F : TwoSectionBezoutProjectiveSectionFiniteMarkedFamily K C V)
    (heval : F.evalPackage.toEvaluationData = D.evalSurjectivity.evalData) :
    ∀ x ∈ D.evalSurjectivity.support,
      (F.map D.zeroSection).hom.base x ∈ markedSchemePointSet K := by
  exact
    D.toDivisorZeroSectionData.twoSectionBezoutFamily_zeroSection_maps_support_to_marked
      F heval

/-- If the canonical two-section finite marked family uses the cohomological
divisor evaluation data, then the finite marked Belyi map attached to the
cohomological zero-section avoids the marked branch set off the support. -/
theorem twoSectionBezoutFamily_zeroSection_avoids_marked_off_support
    (D : CohomologicalDivisorSectionData K C V)
    (F : TwoSectionBezoutProjectiveSectionFiniteMarkedFamily K C V)
    (heval : F.evalPackage.toEvaluationData = D.evalSurjectivity.evalData) :
    ∀ x ∉ D.evalSurjectivity.support,
      (F.map D.zeroSection).hom.base x ∉ markedSchemePointSet K := by
  exact
    D.toDivisorZeroSectionData.twoSectionBezoutFamily_zeroSection_avoids_marked_off_support
      F heval

/-- For the finite marked Belyi map attached to the cohomological zero-section,
the source Belyi open is exactly the complement of the divisor support. -/
theorem twoSectionBezoutFamily_zeroSection_mem_belyiOpen_iff
    (D : CohomologicalDivisorSectionData K C V)
    (F : TwoSectionBezoutProjectiveSectionFiniteMarkedFamily K C V)
    (heval : F.evalPackage.toEvaluationData = D.evalSurjectivity.evalData) (x : C) :
    x ∈ ((F.map D.zeroSection).toBelyiMap.belyiOpen : Set C) ↔
      x ∉ D.evalSurjectivity.support := by
  exact
    D.toDivisorZeroSectionData.twoSectionBezoutFamily_zeroSection_mem_belyiOpen_iff
      F heval x

/-- Set equality form of the cohomological zero-section Belyi-open
computation. -/
theorem twoSectionBezoutFamily_zeroSection_belyiOpen_eq_support_compl
    (D : CohomologicalDivisorSectionData K C V)
    (F : TwoSectionBezoutProjectiveSectionFiniteMarkedFamily K C V)
    (heval : F.evalPackage.toEvaluationData = D.evalSurjectivity.evalData) :
    ((F.map D.zeroSection).toBelyiMap.belyiOpen : Set C) =
      D.evalSurjectivity.supportᶜ := by
  exact
    D.toDivisorZeroSectionData.twoSectionBezoutFamily_zeroSection_belyiOpen_eq_support_compl
      F heval

/-- If the cohomological divisor support is the complement of a prescribed set
`U`, then the zero-section finite marked Belyi open is exactly `U`. -/
theorem twoSectionBezoutFamily_zeroSection_belyiOpen_eq_of_support_eq_compl
    (D : CohomologicalDivisorSectionData K C V)
    (F : TwoSectionBezoutProjectiveSectionFiniteMarkedFamily K C V)
    (heval : F.evalPackage.toEvaluationData = D.evalSurjectivity.evalData)
    {U : Set C} (hsupport : D.evalSurjectivity.support = Uᶜ) :
    ((F.map D.zeroSection).toBelyiMap.belyiOpen : Set C) = U := by
  exact
    D.toDivisorZeroSectionData.twoSectionBezoutFamily_zeroSection_belyiOpen_eq_of_support_eq_compl
      F heval hsupport

/-- Structured cohomological source form: the zero-section map sends the
cohomological divisor support to the marked branch set. -/
theorem structuredSource_zeroSection_maps_support_to_marked
    (D : CohomologicalDivisorSectionData K C V)
    (S : CohomologicalStructuredFiniteDominantEtaleTwoSectionSourceData K C V)
    (heval :
      S.restricted.toRiemannRochFiniteEvaluationPackage.toEvaluationData =
        D.evalSurjectivity.evalData) :
    ∀ x ∈ D.evalSurjectivity.support,
      (S.family.map D.zeroSection).hom.base x ∈ markedSchemePointSet K := by
  have hfamilyEval :
      S.family.evalPackage.toEvaluationData = D.evalSurjectivity.evalData := by
    rw [S.family_evalPackage]
    exact heval
  exact D.twoSectionBezoutFamily_zeroSection_maps_support_to_marked
    S.family hfamilyEval

/-- Structured cohomological source form: the zero-section map avoids the
marked branch set off the cohomological divisor support. -/
theorem structuredSource_zeroSection_avoids_marked_off_support
    (D : CohomologicalDivisorSectionData K C V)
    (S : CohomologicalStructuredFiniteDominantEtaleTwoSectionSourceData K C V)
    (heval :
      S.restricted.toRiemannRochFiniteEvaluationPackage.toEvaluationData =
        D.evalSurjectivity.evalData) :
    ∀ x ∉ D.evalSurjectivity.support,
      (S.family.map D.zeroSection).hom.base x ∉ markedSchemePointSet K := by
  have hfamilyEval :
      S.family.evalPackage.toEvaluationData = D.evalSurjectivity.evalData := by
    rw [S.family_evalPackage]
    exact heval
  exact D.twoSectionBezoutFamily_zeroSection_avoids_marked_off_support
    S.family hfamilyEval

/-- Structured cohomological source form: membership in the zero-section
Belyi open is exactly avoidance of the cohomological divisor support. -/
theorem structuredSource_zeroSection_mem_belyiOpen_iff
    (D : CohomologicalDivisorSectionData K C V)
    (S : CohomologicalStructuredFiniteDominantEtaleTwoSectionSourceData K C V)
    (heval :
      S.restricted.toRiemannRochFiniteEvaluationPackage.toEvaluationData =
        D.evalSurjectivity.evalData) (x : C) :
    x ∈ ((S.family.map D.zeroSection).toBelyiMap.belyiOpen : Set C) ↔
      x ∉ D.evalSurjectivity.support := by
  have hfamilyEval :
      S.family.evalPackage.toEvaluationData = D.evalSurjectivity.evalData := by
    rw [S.family_evalPackage]
    exact heval
  exact D.twoSectionBezoutFamily_zeroSection_mem_belyiOpen_iff
    S.family hfamilyEval x

/-- Structured cohomological source form: the zero-section Belyi open is the
complement of the cohomological divisor support. -/
theorem structuredSource_zeroSection_belyiOpen_eq_support_compl
    (D : CohomologicalDivisorSectionData K C V)
    (S : CohomologicalStructuredFiniteDominantEtaleTwoSectionSourceData K C V)
    (heval :
      S.restricted.toRiemannRochFiniteEvaluationPackage.toEvaluationData =
        D.evalSurjectivity.evalData) :
    ((S.family.map D.zeroSection).toBelyiMap.belyiOpen : Set C) =
      D.evalSurjectivity.supportᶜ := by
  ext x
  exact D.structuredSource_zeroSection_mem_belyiOpen_iff S heval x

/-- Packaged structured source form: the zero-section Belyi open from the
finite marked Belyi existence package is the complement of the cohomological
divisor support. -/
theorem structuredSource_toFiniteMarkedBelyiExistence_zeroSection_belyiOpen_eq_support_compl
    (D : CohomologicalDivisorSectionData K C V)
    [Infinite K]
    (S : CohomologicalStructuredFiniteDominantEtaleTwoSectionSourceData K C V)
    (heval :
      S.restricted.toRiemannRochFiniteEvaluationPackage.toEvaluationData =
        D.evalSurjectivity.evalData) :
    ((S.toFiniteMarkedBelyiExistence.map D.zeroSection).toBelyiMap.belyiOpen : Set C) =
      D.evalSurjectivity.supportᶜ := by
  rw [S.toFiniteMarkedBelyiExistence_map_apply D.zeroSection]
  exact D.structuredSource_zeroSection_belyiOpen_eq_support_compl S heval

/-- Named-open structured source form: the zero-section noncritical Belyi open
is the complement of the cohomological divisor support. -/
theorem structuredSource_zeroSection_named_belyiOpen_eq_support_compl
    (D : CohomologicalDivisorSectionData K C V)
    [Infinite K]
    (S : CohomologicalStructuredFiniteDominantEtaleTwoSectionSourceData K C V)
    (heval :
      S.restricted.toRiemannRochFiniteEvaluationPackage.toEvaluationData =
        D.evalSurjectivity.evalData) :
    S.belyiOpen D.zeroSection = D.evalSurjectivity.supportᶜ := by
  rw [S.belyiOpen_eq_schemeBelyi D.zeroSection]
  exact
    D.structuredSource_toFiniteMarkedBelyiExistence_zeroSection_belyiOpen_eq_support_compl
      S heval

/-- Named-open structured source form with a prescribed complement: if the
cohomological divisor support is `Uᶜ`, then the zero-section noncritical Belyi
open is exactly `U`. -/
theorem structuredSource_zeroSection_named_belyiOpen_eq_of_support_eq_compl
    (D : CohomologicalDivisorSectionData K C V)
    [Infinite K]
    (S : CohomologicalStructuredFiniteDominantEtaleTwoSectionSourceData K C V)
    (heval :
      S.restricted.toRiemannRochFiniteEvaluationPackage.toEvaluationData =
        D.evalSurjectivity.evalData)
    {U : Set C} (hsupport : D.evalSurjectivity.support = Uᶜ) :
    S.belyiOpen D.zeroSection = U := by
  simpa [hsupport] using
    D.structuredSource_zeroSection_named_belyiOpen_eq_support_compl S heval

/-- The structured zero-section named Belyi open is open. -/
theorem structuredSource_zeroSection_named_belyiOpen_isOpen
    (D : CohomologicalDivisorSectionData K C V)
    [Infinite K]
    (S : CohomologicalStructuredFiniteDominantEtaleTwoSectionSourceData K C V) :
    IsOpen (S.belyiOpen D.zeroSection) := by
  rw [S.belyiOpen_eq_schemeBelyi D.zeroSection]
  exact (S.toFiniteMarkedBelyiExistence.map D.zeroSection).toBelyiMap.belyiOpen.2

/-- If the cohomological divisor support is the complement of `U`, then `U`
is open because it is realized as the structured zero-section named Belyi
open. -/
theorem structuredSource_isOpen_of_support_eq_compl
    (D : CohomologicalDivisorSectionData K C V)
    [Infinite K]
    (S : CohomologicalStructuredFiniteDominantEtaleTwoSectionSourceData K C V)
    (heval :
      S.restricted.toRiemannRochFiniteEvaluationPackage.toEvaluationData =
        D.evalSurjectivity.evalData)
    {U : Set C} (hsupport : D.evalSurjectivity.support = Uᶜ) :
    IsOpen U := by
  rw [← D.structuredSource_zeroSection_named_belyiOpen_eq_of_support_eq_compl
    S heval hsupport]
  exact D.structuredSource_zeroSection_named_belyiOpen_isOpen S

/-- The cohomological zero-section finite marked Belyi open is open. -/
theorem twoSectionBezoutFamily_zeroSection_belyiOpen_isOpen
    (D : CohomologicalDivisorSectionData K C V)
    (F : TwoSectionBezoutProjectiveSectionFiniteMarkedFamily K C V) :
    IsOpen ((F.map D.zeroSection).toBelyiMap.belyiOpen : Set C) :=
  D.toDivisorZeroSectionData.twoSectionBezoutFamily_zeroSection_belyiOpen_isOpen F

/-- If the cohomological divisor support is the complement of `U`, then `U` is
open because it is the zero-section finite marked Belyi open. -/
theorem twoSectionBezoutFamily_isOpen_of_support_eq_compl
    (D : CohomologicalDivisorSectionData K C V)
    (F : TwoSectionBezoutProjectiveSectionFiniteMarkedFamily K C V)
    (heval : F.evalPackage.toEvaluationData = D.evalSurjectivity.evalData)
    {U : Set C} (hsupport : D.evalSurjectivity.support = Uᶜ) :
    IsOpen U := by
  exact
    D.toDivisorZeroSectionData.twoSectionBezoutFamily_isOpen_of_support_eq_compl
      F heval hsupport

/-- A projective-line section pair whose first section is the cohomological
divisor zero-section supplies the auxiliary reduction data for the pair
`S, D.evalSurjectivity.support`, once the remaining finite/dominant/étale
checks for the auxiliary morphism are supplied. -/
noncomputable def projectivePair_toP1ReductionAuxiliaryData
    (D : CohomologicalDivisorSectionData K C V)
    {Φ : Type z}
    (F : FiniteMarkedBelyiExistence K Φ (P1 K))
    {S : Set C} (hdis : Disjoint S D.evalSurjectivity.support)
    (P : ProjectiveLineSectionPair K C V)
    (heval : P.evalData = D.evalSurjectivity.evalData)
    (hsection0 : P.section0 = D.zeroSection)
    (badValues : Set (P1 K)) (hbad : badValues.Finite)
    (hfinite : IsFinite P.hom) (hdominant : IsDominant P.hom)
    (htargetBad : schemeCarrierPoint K MarkedPointLabel.zero ∉ badValues)
    (hAuxEtale :
      ∀ φ : Φ,
        ((F.map φ).toBelyiMap.belyiOpen : Set (P1 K)) ⊆
            (reductionBadSet P.hom S badValues)ᶜ →
          IsEtale (P.hom ∣_ (F.map φ).toBelyiMap.belyiOpen)) :
    P1ReductionAuxiliaryData K C F S D.evalSurjectivity.support :=
  D.toDivisorZeroSectionData.projectivePair_toP1ReductionAuxiliaryData
    F hdis P heval hsection0 badValues hbad hfinite hdominant
    htargetBad hAuxEtale

/-- Factory form of the cohomological bridge: after the line-bundle
construction upgrades basepoint-free section pairs to projective-line section
pairs, the cohomological divisor package supplies one whose support maps to the
marked branch point. -/
theorem exists_projectivePair_maps_support_to_marked
    (D : CohomologicalDivisorSectionData K C V)
    [Infinite K] (hsupport : D.evalSurjectivity.support.Finite)
    (mkPair : ∀ s1 : V,
      HasNoCommonZero D.evalSurjectivity.evalData D.zeroSection s1 →
        ProjectiveLineSectionPair K C V)
    (hmk_eval : ∀ s1 hnc, (mkPair s1 hnc).evalData = D.evalSurjectivity.evalData)
    (hmk_section0 : ∀ s1 hnc, (mkPair s1 hnc).section0 = D.zeroSection) :
    ∃ s1 : V,
      ∃ hnc : HasNoCommonZero D.evalSurjectivity.evalData D.zeroSection s1,
        ∀ x ∈ D.evalSurjectivity.support,
          (mkPair s1 hnc).hom.base x ∈ markedSchemePointSet K := by
  rcases D.exists_second_section_no_common_zero hsupport with ⟨s1, hnc⟩
  exact ⟨s1, hnc,
    D.projectivePair_maps_support_to_marked
      (mkPair s1 hnc) (hmk_eval s1 hnc) (hmk_section0 s1 hnc)⟩

/-- Factory form of the cohomological divisor bridge, with the sharper
pointwise statement used in the reduction step: the support maps to `0`, while
any prescribed set disjoint from the support avoids `0`. -/
theorem exists_projectivePair_maps_support_to_zeroPoint_avoids_set
    (D : CohomologicalDivisorSectionData K C V)
    [Infinite K] (hsupport : D.evalSurjectivity.support.Finite) {S : Set C}
    (hdis : Disjoint S D.evalSurjectivity.support)
    (mkPair : ∀ s1 : V,
      HasNoCommonZero D.evalSurjectivity.evalData D.zeroSection s1 →
        ProjectiveLineSectionPair K C V)
    (hmk_eval : ∀ s1 hnc, (mkPair s1 hnc).evalData = D.evalSurjectivity.evalData)
    (hmk_section0 : ∀ s1 hnc, (mkPair s1 hnc).section0 = D.zeroSection) :
    ∃ s1 : V,
      ∃ hnc : HasNoCommonZero D.evalSurjectivity.evalData D.zeroSection s1,
        (∀ x ∈ D.evalSurjectivity.support,
          (mkPair s1 hnc).hom.base x = schemeCarrierPoint K MarkedPointLabel.zero) ∧
          ∀ x ∈ S,
            (mkPair s1 hnc).hom.base x ≠ schemeCarrierPoint K MarkedPointLabel.zero := by
  exact
    D.toDivisorZeroSectionData.exists_projectivePair_maps_support_to_zeroPoint_avoids_set
      hsupport hdis mkPair hmk_eval hmk_section0

/-- Finite-complement-open cohomological section-pair control: if the divisor
support is a finite set inside `U`, the projective-line section-pair factory
yields a map sending the support to `0` and the complement of `U` away from
`0`. -/
theorem exists_projectivePair_maps_support_to_zeroPoint_avoids_complement_of_finite_complement
    (D : CohomologicalDivisorSectionData K C V)
    [Infinite K] {U T : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ U)
    (hsupport : D.evalSurjectivity.support = T)
    (mkPair : ∀ s1 : V,
      HasNoCommonZero D.evalSurjectivity.evalData D.zeroSection s1 →
        ProjectiveLineSectionPair K C V)
    (hmk_eval : ∀ s1 hnc, (mkPair s1 hnc).evalData = D.evalSurjectivity.evalData)
    (hmk_section0 : ∀ s1 hnc, (mkPair s1 hnc).section0 = D.zeroSection) :
    ∃ s1 : V,
      ∃ hnc : HasNoCommonZero D.evalSurjectivity.evalData D.zeroSection s1,
        (∀ x ∈ T,
          (mkPair s1 hnc).hom.base x = schemeCarrierPoint K MarkedPointLabel.zero) ∧
          ∀ x ∈ Uᶜ,
            (mkPair s1 hnc).hom.base x ≠ schemeCarrierPoint K MarkedPointLabel.zero := by
  exact
    D.toDivisorZeroSectionData.exists_projectivePair_maps_support_to_zeroPoint_avoids_complement_of_finite_complement
      hU hUcompl hT hTsub hsupport mkPair hmk_eval hmk_section0

/-- Nonempty-open finite-complement cohomological section-pair control in a
finite-complement topology. -/
theorem exists_projectivePair_maps_support_to_zeroPoint_avoids_complement_of_nonemptyOpenFiniteComplement
    (D : CohomologicalDivisorSectionData K C V)
    [Infinite K] [NonemptyOpenFiniteComplement C]
    {U T : Set C} (hU : IsOpen U) (hUne : U.Nonempty)
    (hT : T.Finite) (hTsub : T ⊆ U)
    (hsupport : D.evalSurjectivity.support = T)
    (mkPair : ∀ s1 : V,
      HasNoCommonZero D.evalSurjectivity.evalData D.zeroSection s1 →
        ProjectiveLineSectionPair K C V)
    (hmk_eval : ∀ s1 hnc, (mkPair s1 hnc).evalData = D.evalSurjectivity.evalData)
    (hmk_section0 : ∀ s1 hnc, (mkPair s1 hnc).section0 = D.zeroSection) :
    ∃ s1 : V,
      ∃ hnc : HasNoCommonZero D.evalSurjectivity.evalData D.zeroSection s1,
        (∀ x ∈ T,
          (mkPair s1 hnc).hom.base x = schemeCarrierPoint K MarkedPointLabel.zero) ∧
          ∀ x ∈ Uᶜ,
            (mkPair s1 hnc).hom.base x ≠ schemeCarrierPoint K MarkedPointLabel.zero := by
  exact
    D.toDivisorZeroSectionData.exists_projectivePair_maps_support_to_zeroPoint_avoids_complement_of_nonemptyOpenFiniteComplement
      hU hUne hT hTsub hsupport mkPair hmk_eval hmk_section0

/-- Factory form of the cohomological divisor-to-reduction bridge: after
basepoint-free section pairs are upgraded to projective-line section pairs and
the auxiliary morphism checks are supplied, the cohomological divisor package
gives reduction auxiliary data for `S` and the divisor support. -/
theorem exists_p1ReductionAuxiliaryData_of_projectivePair_factory
    (D : CohomologicalDivisorSectionData K C V)
    [Infinite K] {Φ : Type z}
    (F : FiniteMarkedBelyiExistence K Φ (P1 K))
    (hsupport : D.evalSurjectivity.support.Finite) {S : Set C}
    (hdis : Disjoint S D.evalSurjectivity.support)
    (badValues : Set (P1 K)) (hbad : badValues.Finite)
    (mkPair : ∀ s1 : V,
      HasNoCommonZero D.evalSurjectivity.evalData D.zeroSection s1 →
        ProjectiveLineSectionPair K C V)
    (hmk_eval : ∀ s1 hnc, (mkPair s1 hnc).evalData = D.evalSurjectivity.evalData)
    (hmk_section0 : ∀ s1 hnc, (mkPair s1 hnc).section0 = D.zeroSection)
    (hmk_finite : ∀ s1 hnc, IsFinite (mkPair s1 hnc).hom)
    (hmk_dominant : ∀ s1 hnc, IsDominant (mkPair s1 hnc).hom)
    (htargetBad : schemeCarrierPoint K MarkedPointLabel.zero ∉ badValues)
    (hAuxEtale :
      ∀ s1 hnc φ,
        ((F.map φ).toBelyiMap.belyiOpen : Set (P1 K)) ⊆
            (reductionBadSet (mkPair s1 hnc).hom S badValues)ᶜ →
          IsEtale ((mkPair s1 hnc).hom ∣_ (F.map φ).toBelyiMap.belyiOpen)) :
    ∃ s1 : V,
      ∃ _ : HasNoCommonZero D.evalSurjectivity.evalData D.zeroSection s1,
        Nonempty (P1ReductionAuxiliaryData K C F S D.evalSurjectivity.support) := by
  exact
    D.toDivisorZeroSectionData.exists_p1ReductionAuxiliaryData_of_projectivePair_factory
      F hsupport hdis badValues hbad mkPair hmk_eval hmk_section0
      hmk_finite hmk_dominant htargetBad hAuxEtale

/-- Set-indexed form of
`exists_p1ReductionAuxiliaryData_of_projectivePair_factory`: if the
cohomological divisor support is the prescribed finite set `T`, the produced
auxiliary data is typed for the reduction pair `S,T`. -/
theorem exists_p1ReductionAuxiliaryData_for_sets_of_projectivePair_factory
    (D : CohomologicalDivisorSectionData K C V)
    [Infinite K] {Φ : Type z}
    (F : FiniteMarkedBelyiExistence K Φ (P1 K))
    {S T : Set C} (hT : T.Finite)
    (hsupport : D.evalSurjectivity.support = T)
    (hdis : Disjoint S T)
    (badValues : Set (P1 K)) (hbad : badValues.Finite)
    (mkPair : ∀ s1 : V,
      HasNoCommonZero D.evalSurjectivity.evalData D.zeroSection s1 →
        ProjectiveLineSectionPair K C V)
    (hmk_eval : ∀ s1 hnc, (mkPair s1 hnc).evalData = D.evalSurjectivity.evalData)
    (hmk_section0 : ∀ s1 hnc, (mkPair s1 hnc).section0 = D.zeroSection)
    (hmk_finite : ∀ s1 hnc, IsFinite (mkPair s1 hnc).hom)
    (hmk_dominant : ∀ s1 hnc, IsDominant (mkPair s1 hnc).hom)
    (htargetBad : schemeCarrierPoint K MarkedPointLabel.zero ∉ badValues)
    (hAuxEtale :
      ∀ s1 hnc φ,
        ((F.map φ).toBelyiMap.belyiOpen : Set (P1 K)) ⊆
            (reductionBadSet (mkPair s1 hnc).hom S badValues)ᶜ →
          IsEtale ((mkPair s1 hnc).hom ∣_ (F.map φ).toBelyiMap.belyiOpen)) :
    ∃ s1 : V,
      ∃ _ : HasNoCommonZero D.evalSurjectivity.evalData D.zeroSection s1,
        Nonempty (P1ReductionAuxiliaryData K C F S T) := by
  exact
    D.toDivisorZeroSectionData.exists_p1ReductionAuxiliaryData_for_sets_of_projectivePair_factory
      F hT hsupport hdis badValues hbad mkPair hmk_eval hmk_section0
      hmk_finite hmk_dominant htargetBad hAuxEtale

/-- Finite-complement-open cohomological auxiliary-data bridge: if the
cohomological divisor support is a finite set inside `U`, the section-pair
factory gives auxiliary reduction data for the pair `Uᶜ, T`. -/
theorem exists_p1ReductionAuxiliaryData_containing_finite_inside_open_of_finite_complement_for_sets_of_projectivePair_factory
    (D : CohomologicalDivisorSectionData K C V)
    [Infinite K] {Φ : Type z}
    (F : FiniteMarkedBelyiExistence K Φ (P1 K))
    {U T : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ U)
    (hsupport : D.evalSurjectivity.support = T)
    (badValues : Set (P1 K)) (hbad : badValues.Finite)
    (mkPair : ∀ s1 : V,
      HasNoCommonZero D.evalSurjectivity.evalData D.zeroSection s1 →
        ProjectiveLineSectionPair K C V)
    (hmk_eval : ∀ s1 hnc, (mkPair s1 hnc).evalData = D.evalSurjectivity.evalData)
    (hmk_section0 : ∀ s1 hnc, (mkPair s1 hnc).section0 = D.zeroSection)
    (hmk_finite : ∀ s1 hnc, IsFinite (mkPair s1 hnc).hom)
    (hmk_dominant : ∀ s1 hnc, IsDominant (mkPair s1 hnc).hom)
    (htargetBad : schemeCarrierPoint K MarkedPointLabel.zero ∉ badValues)
    (hAuxEtale :
      ∀ s1 hnc φ,
        ((F.map φ).toBelyiMap.belyiOpen : Set (P1 K)) ⊆
            (reductionBadSet (mkPair s1 hnc).hom Uᶜ badValues)ᶜ →
          IsEtale ((mkPair s1 hnc).hom ∣_ (F.map φ).toBelyiMap.belyiOpen)) :
    ∃ s1 : V,
      ∃ _ : HasNoCommonZero D.evalSurjectivity.evalData D.zeroSection s1,
        Nonempty (P1ReductionAuxiliaryData K C F Uᶜ T) := by
  exact
    D.toDivisorZeroSectionData.exists_p1ReductionAuxiliaryData_containing_finite_inside_open_of_finite_complement_for_sets_of_projectivePair_factory
      F hU hUcompl hT hTsub hsupport badValues hbad mkPair hmk_eval
      hmk_section0 hmk_finite hmk_dominant htargetBad hAuxEtale

/-- Nonempty-open cohomological auxiliary-data bridge in a finite-complement
topology. -/
theorem exists_p1ReductionAuxiliaryData_containing_finite_inside_open_of_nonemptyOpenFiniteComplement_for_sets_of_projectivePair_factory
    (D : CohomologicalDivisorSectionData K C V)
    [Infinite K] [NonemptyOpenFiniteComplement C] {Φ : Type z}
    (F : FiniteMarkedBelyiExistence K Φ (P1 K))
    {U T : Set C} (hU : IsOpen U) (hUne : U.Nonempty)
    (hT : T.Finite) (hTsub : T ⊆ U)
    (hsupport : D.evalSurjectivity.support = T)
    (badValues : Set (P1 K)) (hbad : badValues.Finite)
    (mkPair : ∀ s1 : V,
      HasNoCommonZero D.evalSurjectivity.evalData D.zeroSection s1 →
        ProjectiveLineSectionPair K C V)
    (hmk_eval : ∀ s1 hnc, (mkPair s1 hnc).evalData = D.evalSurjectivity.evalData)
    (hmk_section0 : ∀ s1 hnc, (mkPair s1 hnc).section0 = D.zeroSection)
    (hmk_finite : ∀ s1 hnc, IsFinite (mkPair s1 hnc).hom)
    (hmk_dominant : ∀ s1 hnc, IsDominant (mkPair s1 hnc).hom)
    (htargetBad : schemeCarrierPoint K MarkedPointLabel.zero ∉ badValues)
    (hAuxEtale :
      ∀ s1 hnc φ,
        ((F.map φ).toBelyiMap.belyiOpen : Set (P1 K)) ⊆
            (reductionBadSet (mkPair s1 hnc).hom Uᶜ badValues)ᶜ →
          IsEtale ((mkPair s1 hnc).hom ∣_ (F.map φ).toBelyiMap.belyiOpen)) :
    ∃ s1 : V,
      ∃ _ : HasNoCommonZero D.evalSurjectivity.evalData D.zeroSection s1,
        Nonempty (P1ReductionAuxiliaryData K C F Uᶜ T) := by
  exact
    D.toDivisorZeroSectionData.exists_p1ReductionAuxiliaryData_containing_finite_inside_open_of_nonemptyOpenFiniteComplement_for_sets_of_projectivePair_factory
      F hU hUne hT hTsub hsupport badValues hbad mkPair hmk_eval
      hmk_section0 hmk_finite hmk_dominant htargetBad hAuxEtale

/-- Composed-map form of the cohomological divisor-to-reduction bridge: after
basepoint-free section pairs are upgraded to projective-line section pairs and
the auxiliary morphism checks are supplied, the cohomological divisor package
produces an actual composed finite Belyi map whose Belyi open contains `T` and
avoids `S`. -/
theorem exists_composedMap_belyiOpen_controls_for_sets_of_projectivePair_factory
    (D : CohomologicalDivisorSectionData K C V)
    [Infinite K] {Φ : Type z}
    (F : FiniteMarkedBelyiExistence K Φ (P1 K))
    {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hsupport : D.evalSurjectivity.support = T)
    (hdis : Disjoint S T)
    (badValues : Set (P1 K)) (hbad : badValues.Finite)
    (mkPair : ∀ s1 : V,
      HasNoCommonZero D.evalSurjectivity.evalData D.zeroSection s1 →
        ProjectiveLineSectionPair K C V)
    (hmk_eval : ∀ s1 hnc, (mkPair s1 hnc).evalData = D.evalSurjectivity.evalData)
    (hmk_section0 : ∀ s1 hnc, (mkPair s1 hnc).section0 = D.zeroSection)
    (hmk_finite : ∀ s1 hnc, IsFinite (mkPair s1 hnc).hom)
    (hmk_dominant : ∀ s1 hnc, IsDominant (mkPair s1 hnc).hom)
    (htargetBad : schemeCarrierPoint K MarkedPointLabel.zero ∉ badValues)
    (hAuxEtale :
      ∀ s1 hnc phi,
        ((F.map phi).toBelyiMap.belyiOpen : Set (P1 K)) ⊆
            (reductionBadSet (mkPair s1 hnc).hom S badValues)ᶜ →
          IsEtale ((mkPair s1 hnc).hom ∣_ (F.map phi).toBelyiMap.belyiOpen)) :
    ∃ s1 : V,
      ∃ hnc : HasNoCommonZero D.evalSurjectivity.evalData D.zeroSection s1,
        ∃ phi : Φ,
          ∃ composed : SchemeBelyi.FiniteBelyiMap
            (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen) C,
            composed.hom = (mkPair s1 hnc).hom ≫ (F.map phi).hom ∧
              T ⊆ (composed.toBelyiMap.belyiOpen : Set C) ∧
                (composed.toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  exact
    D.toDivisorZeroSectionData.exists_composedMap_belyiOpen_controls_for_sets_of_projectivePair_factory
      F hS hT hsupport hdis badValues hbad mkPair hmk_eval hmk_section0
      hmk_finite hmk_dominant htargetBad hAuxEtale

/-- Combined composed-map form of the cohomological divisor-to-reduction
bridge: the cohomological divisor package produces an actual composed finite
Belyi map with both marked controls and Belyi-open controls. -/
theorem exists_composedMap_controls_and_belyiOpen_controls_for_sets_of_projectivePair_factory
    (D : CohomologicalDivisorSectionData K C V)
    [Infinite K] {Φ : Type z}
    (F : FiniteMarkedBelyiExistence K Φ (P1 K))
    {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hsupport : D.evalSurjectivity.support = T)
    (hdis : Disjoint S T)
    (badValues : Set (P1 K)) (hbad : badValues.Finite)
    (mkPair : ∀ s1 : V,
      HasNoCommonZero D.evalSurjectivity.evalData D.zeroSection s1 →
        ProjectiveLineSectionPair K C V)
    (hmk_eval : ∀ s1 hnc, (mkPair s1 hnc).evalData = D.evalSurjectivity.evalData)
    (hmk_section0 : ∀ s1 hnc, (mkPair s1 hnc).section0 = D.zeroSection)
    (hmk_finite : ∀ s1 hnc, IsFinite (mkPair s1 hnc).hom)
    (hmk_dominant : ∀ s1 hnc, IsDominant (mkPair s1 hnc).hom)
    (htargetBad : schemeCarrierPoint K MarkedPointLabel.zero ∉ badValues)
    (hAuxEtale :
      ∀ s1 hnc phi,
        ((F.map phi).toBelyiMap.belyiOpen : Set (P1 K)) ⊆
            (reductionBadSet (mkPair s1 hnc).hom S badValues)ᶜ →
          IsEtale ((mkPair s1 hnc).hom ∣_ (F.map phi).toBelyiMap.belyiOpen)) :
    ∃ s1 : V,
      ∃ hnc : HasNoCommonZero D.evalSurjectivity.evalData D.zeroSection s1,
        ∃ phi : Φ,
          ∃ composed : SchemeBelyi.FiniteBelyiMap
            (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen) C,
            composed.hom = (mkPair s1 hnc).hom ≫ (F.map phi).hom ∧
              ((∀ x ∈ S, composed.hom.base x ∈ markedSchemePointSet K) ∧
                ∀ x ∈ T, composed.hom.base x ∉ markedSchemePointSet K) ∧
                T ⊆ (composed.toBelyiMap.belyiOpen : Set C) ∧
                  (composed.toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  exact
    D.toDivisorZeroSectionData.exists_composedMap_controls_and_belyiOpen_controls_for_sets_of_projectivePair_factory
      F hS hT hsupport hdis badValues hbad mkPair hmk_eval hmk_section0
      hmk_finite hmk_dominant htargetBad hAuxEtale

/-- Combined composed-map form of the cohomological divisor-to-reduction bridge
with explicit openness: the cohomological divisor package produces an actual
composed finite Belyi map with marked controls, an open source Belyi open, and
Belyi-open controls. -/
theorem exists_composedMap_controls_and_isOpen_belyiOpen_controls_for_sets_of_projectivePair_factory
    (D : CohomologicalDivisorSectionData K C V)
    [Infinite K] {Φ : Type z}
    (F : FiniteMarkedBelyiExistence K Φ (P1 K))
    {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hsupport : D.evalSurjectivity.support = T)
    (hdis : Disjoint S T)
    (badValues : Set (P1 K)) (hbad : badValues.Finite)
    (mkPair : ∀ s1 : V,
      HasNoCommonZero D.evalSurjectivity.evalData D.zeroSection s1 →
        ProjectiveLineSectionPair K C V)
    (hmk_eval : ∀ s1 hnc, (mkPair s1 hnc).evalData = D.evalSurjectivity.evalData)
    (hmk_section0 : ∀ s1 hnc, (mkPair s1 hnc).section0 = D.zeroSection)
    (hmk_finite : ∀ s1 hnc, IsFinite (mkPair s1 hnc).hom)
    (hmk_dominant : ∀ s1 hnc, IsDominant (mkPair s1 hnc).hom)
    (htargetBad : schemeCarrierPoint K MarkedPointLabel.zero ∉ badValues)
    (hAuxEtale :
      ∀ s1 hnc phi,
        ((F.map phi).toBelyiMap.belyiOpen : Set (P1 K)) ⊆
            (reductionBadSet (mkPair s1 hnc).hom S badValues)ᶜ →
          IsEtale ((mkPair s1 hnc).hom ∣_ (F.map phi).toBelyiMap.belyiOpen)) :
    ∃ s1 : V,
      ∃ hnc : HasNoCommonZero D.evalSurjectivity.evalData D.zeroSection s1,
        ∃ phi : Φ,
          ∃ composed : SchemeBelyi.FiniteBelyiMap
            (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen) C,
            composed.hom = (mkPair s1 hnc).hom ≫ (F.map phi).hom ∧
              ((∀ x ∈ S, composed.hom.base x ∈ markedSchemePointSet K) ∧
                ∀ x ∈ T, composed.hom.base x ∉ markedSchemePointSet K) ∧
                IsOpen (composed.toBelyiMap.belyiOpen : Set C) ∧
                  T ⊆ (composed.toBelyiMap.belyiOpen : Set C) ∧
                    (composed.toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  exact
    D.toDivisorZeroSectionData.exists_composedMap_controls_and_isOpen_belyiOpen_controls_for_sets_of_projectivePair_factory
      F hS hT hsupport hdis badValues hbad mkPair hmk_eval hmk_section0
      hmk_finite hmk_dominant htargetBad hAuxEtale

/-- Finite-complement-open composed-map form of the cohomological
divisor-to-reduction bridge: if `T` lies in an open with finite complement,
the cohomological divisor package produces an actual composed finite Belyi map
whose Belyi open contains `T` and is contained in that open. -/
theorem exists_composedMap_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_finite_complement_for_sets_of_projectivePair_factory
    (D : CohomologicalDivisorSectionData K C V)
    [Infinite K] {Φ : Type z}
    (F : FiniteMarkedBelyiExistence K Φ (P1 K))
    {U T : Set C} (_hU : IsOpen U) (hUcompl : Uᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ U)
    (hsupport : D.evalSurjectivity.support = T)
    (badValues : Set (P1 K)) (hbad : badValues.Finite)
    (mkPair : ∀ s1 : V,
      HasNoCommonZero D.evalSurjectivity.evalData D.zeroSection s1 →
        ProjectiveLineSectionPair K C V)
    (hmk_eval : ∀ s1 hnc, (mkPair s1 hnc).evalData = D.evalSurjectivity.evalData)
    (hmk_section0 : ∀ s1 hnc, (mkPair s1 hnc).section0 = D.zeroSection)
    (hmk_finite : ∀ s1 hnc, IsFinite (mkPair s1 hnc).hom)
    (hmk_dominant : ∀ s1 hnc, IsDominant (mkPair s1 hnc).hom)
    (htargetBad : schemeCarrierPoint K MarkedPointLabel.zero ∉ badValues)
    (hAuxEtale :
      ∀ s1 hnc phi,
        ((F.map phi).toBelyiMap.belyiOpen : Set (P1 K)) ⊆
            (reductionBadSet (mkPair s1 hnc).hom Uᶜ badValues)ᶜ →
          IsEtale ((mkPair s1 hnc).hom ∣_ (F.map phi).toBelyiMap.belyiOpen)) :
    ∃ s1 : V,
      ∃ hnc : HasNoCommonZero D.evalSurjectivity.evalData D.zeroSection s1,
        ∃ phi : Φ,
          ∃ composed : SchemeBelyi.FiniteBelyiMap
            (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen) C,
            composed.hom = (mkPair s1 hnc).hom ≫ (F.map phi).hom ∧
              ((∀ x ∈ Uᶜ, composed.hom.base x ∈ markedSchemePointSet K) ∧
                ∀ x ∈ T, composed.hom.base x ∉ markedSchemePointSet K) ∧
                IsOpen (composed.toBelyiMap.belyiOpen : Set C) ∧
                  T ⊆ (composed.toBelyiMap.belyiOpen : Set C) ∧
                    (composed.toBelyiMap.belyiOpen : Set C) ⊆ U := by
  exact
    D.toDivisorZeroSectionData.exists_composedMap_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_finite_complement_for_sets_of_projectivePair_factory
      F _hU hUcompl hT hTsub hsupport badValues hbad mkPair hmk_eval hmk_section0
      hmk_finite hmk_dominant htargetBad hAuxEtale

/-- Nonempty-open composed-map form of the cohomological
divisor-to-reduction bridge in a finite-complement topology. -/
theorem exists_composedMap_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement_for_sets_of_projectivePair_factory
    (D : CohomologicalDivisorSectionData K C V)
    [Infinite K] [NonemptyOpenFiniteComplement C] {Φ : Type z}
    (F : FiniteMarkedBelyiExistence K Φ (P1 K))
    {U T : Set C} (hU : IsOpen U) (hUne : U.Nonempty)
    (hT : T.Finite) (hTsub : T ⊆ U)
    (hsupport : D.evalSurjectivity.support = T)
    (badValues : Set (P1 K)) (hbad : badValues.Finite)
    (mkPair : ∀ s1 : V,
      HasNoCommonZero D.evalSurjectivity.evalData D.zeroSection s1 →
        ProjectiveLineSectionPair K C V)
    (hmk_eval : ∀ s1 hnc, (mkPair s1 hnc).evalData = D.evalSurjectivity.evalData)
    (hmk_section0 : ∀ s1 hnc, (mkPair s1 hnc).section0 = D.zeroSection)
    (hmk_finite : ∀ s1 hnc, IsFinite (mkPair s1 hnc).hom)
    (hmk_dominant : ∀ s1 hnc, IsDominant (mkPair s1 hnc).hom)
    (htargetBad : schemeCarrierPoint K MarkedPointLabel.zero ∉ badValues)
    (hAuxEtale :
      ∀ s1 hnc phi,
        ((F.map phi).toBelyiMap.belyiOpen : Set (P1 K)) ⊆
            (reductionBadSet (mkPair s1 hnc).hom Uᶜ badValues)ᶜ →
          IsEtale ((mkPair s1 hnc).hom ∣_ (F.map phi).toBelyiMap.belyiOpen)) :
    ∃ s1 : V,
      ∃ hnc : HasNoCommonZero D.evalSurjectivity.evalData D.zeroSection s1,
        ∃ phi : Φ,
          ∃ composed : SchemeBelyi.FiniteBelyiMap
            (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen) C,
            composed.hom = (mkPair s1 hnc).hom ≫ (F.map phi).hom ∧
              ((∀ x ∈ Uᶜ, composed.hom.base x ∈ markedSchemePointSet K) ∧
                ∀ x ∈ T, composed.hom.base x ∉ markedSchemePointSet K) ∧
                IsOpen (composed.toBelyiMap.belyiOpen : Set C) ∧
                  T ⊆ (composed.toBelyiMap.belyiOpen : Set C) ∧
                    (composed.toBelyiMap.belyiOpen : Set C) ⊆ U := by
  exact
    D.toDivisorZeroSectionData.exists_composedMap_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement_for_sets_of_projectivePair_factory
      F hU hUne hT hTsub hsupport badValues hbad mkPair hmk_eval hmk_section0
      hmk_finite hmk_dominant htargetBad hAuxEtale

end SchemeSupport

end CohomologicalDivisorSectionData

section SchemeReductionSource

open AlgebraicGeometry
open CategoryTheory

variable {C : Scheme.{u}}

/-- A cohomological source package indexed by all finite disjoint pairs of
source sets.  For each pair `S,T`, it supplies a divisor zero-section package
with support `T`, the projective-line section-pair construction, and the
remaining finite/dominant/étale checks needed to enter the reduction layer. -/
structure CohomologicalP1ReductionSourceData
    (K : Type u) [Field K] (C : Scheme.{u})
    (V : Type w) [AddCommGroup V] [Module K V]
    {Φ : Type z} (F : FiniteMarkedBelyiExistence K Φ (P1 K)) where
  divisor : ∀ _ : ReductionIndex C, CohomologicalDivisorSectionData K C V
  support_eq :
    ∀ i : ReductionIndex C, (divisor i).evalSurjectivity.support = i.1.2
  badValues : ∀ _ : ReductionIndex C, Set (P1 K)
  badValues_finite : ∀ i : ReductionIndex C, (badValues i).Finite
  mkPair :
    ∀ i : ReductionIndex C, ∀ s1 : V,
      HasNoCommonZero (divisor i).evalSurjectivity.evalData
        (divisor i).zeroSection s1 →
        ProjectiveLineSectionPair K C V
  mkPair_eval :
    ∀ i : ReductionIndex C, ∀ s1 hnc,
      (mkPair i s1 hnc).evalData = (divisor i).evalSurjectivity.evalData
  mkPair_section0 :
    ∀ i : ReductionIndex C, ∀ s1 hnc,
      (mkPair i s1 hnc).section0 = (divisor i).zeroSection
  mkPair_finite :
    ∀ i : ReductionIndex C, ∀ s1 hnc, IsFinite (mkPair i s1 hnc).hom
  mkPair_dominant :
    ∀ i : ReductionIndex C, ∀ s1 hnc, IsDominant (mkPair i s1 hnc).hom
  target_not_bad :
    ∀ i : ReductionIndex C,
      schemeCarrierPoint K MarkedPointLabel.zero ∉ badValues i
  aux_etale :
    ∀ i : ReductionIndex C, ∀ s1 hnc φ,
      ((F.map φ).toBelyiMap.belyiOpen : Set (P1 K)) ⊆
          (reductionBadSet (mkPair i s1 hnc).hom i.1.1 (badValues i))ᶜ →
        IsEtale ((mkPair i s1 hnc).hom ∣_ (F.map φ).toBelyiMap.belyiOpen)

namespace CohomologicalP1ReductionSourceData

variable {Φ : Type z}
variable {F : FiniteMarkedBelyiExistence K Φ (P1 K)}

/-- A cohomological reduction-source package supplies the global reduction
family needed by the finite marked Belyi interface. -/
theorem exists_p1ReductionExistence
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F) :
    ∃ E : P1ReductionExistence K C,
      E.hmarkedOpen = F.hmarkedOpen := by
  classical
  apply P1ReductionExistence.exists_of_auxiliaryData_nonempty F
  intro S T hS hT hdis
  let i : ReductionIndex C := ⟨(S, T), hS, hT, hdis⟩
  rcases
      CohomologicalDivisorSectionData.exists_p1ReductionAuxiliaryData_for_sets_of_projectivePair_factory
        (CohomologicalP1ReductionSourceData.divisor D i) F hT
        (CohomologicalP1ReductionSourceData.support_eq D i) hdis
        (CohomologicalP1ReductionSourceData.badValues D i)
        (CohomologicalP1ReductionSourceData.badValues_finite D i)
        (CohomologicalP1ReductionSourceData.mkPair D i)
        (CohomologicalP1ReductionSourceData.mkPair_eval D i)
        (CohomologicalP1ReductionSourceData.mkPair_section0 D i)
        (CohomologicalP1ReductionSourceData.mkPair_finite D i)
        (CohomologicalP1ReductionSourceData.mkPair_dominant D i)
        (CohomologicalP1ReductionSourceData.target_not_bad D i)
        (CohomologicalP1ReductionSourceData.aux_etale D i) with
    ⟨s1, hnc, haux⟩
  exact haux

/-- Direct composed-map consequence from the indexed cohomological source
package: for every finite disjoint pair `S,T`, the package produces an actual
composed finite Belyi map whose Belyi open contains `T` and avoids `S`. -/
theorem exists_composedMap_belyiOpen_controls_for_finite_disjoint
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ i : ReductionIndex C,
      ∃ s1 : V,
        ∃ hnc : HasNoCommonZero (D.divisor i).evalSurjectivity.evalData
          (D.divisor i).zeroSection s1,
          ∃ φ : Φ,
            ∃ composed : SchemeBelyi.FiniteBelyiMap
              (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen) C,
              i.1.1 = S ∧
                i.1.2 = T ∧
                  composed.hom = (D.mkPair i s1 hnc).hom ≫ (F.map φ).hom ∧
                    T ⊆ (composed.toBelyiMap.belyiOpen : Set C) ∧
                      (composed.toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  let i : ReductionIndex C := ⟨(S, T), hS, hT, hdis⟩
  rcases
      CohomologicalDivisorSectionData.exists_composedMap_belyiOpen_controls_for_sets_of_projectivePair_factory
        (CohomologicalP1ReductionSourceData.divisor D i) F hS hT
        (CohomologicalP1ReductionSourceData.support_eq D i) hdis
        (CohomologicalP1ReductionSourceData.badValues D i)
        (CohomologicalP1ReductionSourceData.badValues_finite D i)
        (CohomologicalP1ReductionSourceData.mkPair D i)
        (CohomologicalP1ReductionSourceData.mkPair_eval D i)
        (CohomologicalP1ReductionSourceData.mkPair_section0 D i)
        (CohomologicalP1ReductionSourceData.mkPair_finite D i)
        (CohomologicalP1ReductionSourceData.mkPair_dominant D i)
        (CohomologicalP1ReductionSourceData.target_not_bad D i)
        (CohomologicalP1ReductionSourceData.aux_etale D i) with
    ⟨s1, hnc, φ, composed, hhom, hTopen, hopenS⟩
  exact ⟨i, s1, hnc, φ, composed, rfl, rfl, hhom, hTopen, hopenS⟩

/-- Direct combined composed-map consequence from the indexed cohomological
source package: for every finite disjoint pair `S,T`, the package produces an
actual composed finite Belyi map with both marked controls and Belyi-open
controls. -/
theorem exists_composedMap_controls_and_belyiOpen_controls_for_finite_disjoint
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ i : ReductionIndex C,
      ∃ s1 : V,
        ∃ hnc : HasNoCommonZero (D.divisor i).evalSurjectivity.evalData
          (D.divisor i).zeroSection s1,
          ∃ φ : Φ,
            ∃ composed : SchemeBelyi.FiniteBelyiMap
              (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen) C,
              i.1.1 = S ∧
                i.1.2 = T ∧
                  composed.hom = (D.mkPair i s1 hnc).hom ≫ (F.map φ).hom ∧
                    ((∀ x ∈ S, composed.hom.base x ∈ markedSchemePointSet K) ∧
                      ∀ x ∈ T, composed.hom.base x ∉ markedSchemePointSet K) ∧
                      T ⊆ (composed.toBelyiMap.belyiOpen : Set C) ∧
                        (composed.toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  let i : ReductionIndex C := ⟨(S, T), hS, hT, hdis⟩
  rcases
      CohomologicalDivisorSectionData.exists_composedMap_controls_and_belyiOpen_controls_for_sets_of_projectivePair_factory
        (CohomologicalP1ReductionSourceData.divisor D i) F hS hT
        (CohomologicalP1ReductionSourceData.support_eq D i) hdis
        (CohomologicalP1ReductionSourceData.badValues D i)
        (CohomologicalP1ReductionSourceData.badValues_finite D i)
        (CohomologicalP1ReductionSourceData.mkPair D i)
        (CohomologicalP1ReductionSourceData.mkPair_eval D i)
        (CohomologicalP1ReductionSourceData.mkPair_section0 D i)
        (CohomologicalP1ReductionSourceData.mkPair_finite D i)
        (CohomologicalP1ReductionSourceData.mkPair_dominant D i)
        (CohomologicalP1ReductionSourceData.target_not_bad D i)
        (CohomologicalP1ReductionSourceData.aux_etale D i) with
    ⟨s1, hnc, φ, composed, hhom, hcontrols, hTopen, hopenS⟩
  exact ⟨i, s1, hnc, φ, composed, rfl, rfl, hhom, hcontrols, hTopen, hopenS⟩

/-- Direct combined composed-map consequence from the indexed cohomological
source package with explicit openness: for every finite disjoint pair `S,T`,
the package produces an actual composed finite Belyi map with marked controls,
an open source Belyi open, and Belyi-open controls. -/
theorem exists_composedMap_controls_and_isOpen_belyiOpen_controls_for_finite_disjoint
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ i : ReductionIndex C,
      ∃ s1 : V,
        ∃ hnc : HasNoCommonZero (D.divisor i).evalSurjectivity.evalData
          (D.divisor i).zeroSection s1,
          ∃ φ : Φ,
            ∃ composed : SchemeBelyi.FiniteBelyiMap
              (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen) C,
              i.1.1 = S ∧
                i.1.2 = T ∧
                  composed.hom = (D.mkPair i s1 hnc).hom ≫ (F.map φ).hom ∧
                    ((∀ x ∈ S, composed.hom.base x ∈ markedSchemePointSet K) ∧
                      ∀ x ∈ T, composed.hom.base x ∉ markedSchemePointSet K) ∧
                      IsOpen (composed.toBelyiMap.belyiOpen : Set C) ∧
                        T ⊆ (composed.toBelyiMap.belyiOpen : Set C) ∧
                          (composed.toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  rcases D.exists_composedMap_controls_and_belyiOpen_controls_for_finite_disjoint
      hS hT hdis with
    ⟨i, s1, hnc, φ, composed, hiS, hiT, hhom, hcontrols, hTopen, hopenS⟩
  exact
    ⟨i, s1, hnc, φ, composed, hiS, hiT, hhom, hcontrols,
      composed.toBelyiMap.belyiOpen.2, hTopen, hopenS⟩

/-- Finite-complement-open composed-map consequence from the indexed
cohomological source package: if a finite set `T` lies in an open whose
complement is finite, the package produces an actual composed finite Belyi map
whose Belyi open contains `T` and is contained in that open. -/
theorem exists_composedMap_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_finite_complement
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    {U T : Set C} (_hU : IsOpen U) (hUcompl : Uᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ i : ReductionIndex C,
      ∃ s1 : V,
        ∃ hnc : HasNoCommonZero (D.divisor i).evalSurjectivity.evalData
          (D.divisor i).zeroSection s1,
          ∃ φ : Φ,
            ∃ composed : SchemeBelyi.FiniteBelyiMap
              (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen) C,
              i.1.1 = Uᶜ ∧
                i.1.2 = T ∧
                  composed.hom = (D.mkPair i s1 hnc).hom ≫ (F.map φ).hom ∧
                    ((∀ x ∈ Uᶜ, composed.hom.base x ∈ markedSchemePointSet K) ∧
                      ∀ x ∈ T, composed.hom.base x ∉ markedSchemePointSet K) ∧
                      IsOpen (composed.toBelyiMap.belyiOpen : Set C) ∧
                        T ⊆ (composed.toBelyiMap.belyiOpen : Set C) ∧
                          (composed.toBelyiMap.belyiOpen : Set C) ⊆ U := by
  have hdis : Disjoint Uᶜ T := by
    rw [Set.disjoint_left]
    intro x hxU hxT
    exact hxU (hTsub hxT)
  rcases D.exists_composedMap_controls_and_isOpen_belyiOpen_controls_for_finite_disjoint
      hUcompl hT hdis with
    ⟨i, s1, hnc, φ, composed, hiS, hiT, hhom, hcontrols, hopen, hTopen, hopenS⟩
  exact
    ⟨i, s1, hnc, φ, composed, hiS, hiT, hhom, hcontrols, hopen, hTopen,
      by simpa using hopenS⟩

/-- Nonempty-open composed-map consequence from the indexed cohomological
source package in a finite-complement topology: if a finite set `T` lies in a
nonempty open, the package produces an actual composed finite Belyi map whose
Belyi open contains `T` and is contained in that open. -/
theorem exists_composedMap_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
    [Infinite K] [NonemptyOpenFiniteComplement C]
    (D : CohomologicalP1ReductionSourceData K C V F)
    {U T : Set C} (hU : IsOpen U) (hUne : U.Nonempty)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ i : ReductionIndex C,
      ∃ s1 : V,
        ∃ hnc : HasNoCommonZero (D.divisor i).evalSurjectivity.evalData
          (D.divisor i).zeroSection s1,
          ∃ φ : Φ,
            ∃ composed : SchemeBelyi.FiniteBelyiMap
              (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen) C,
              i.1.1 = Uᶜ ∧
                i.1.2 = T ∧
                  composed.hom = (D.mkPair i s1 hnc).hom ≫ (F.map φ).hom ∧
                    ((∀ x ∈ Uᶜ, composed.hom.base x ∈ markedSchemePointSet K) ∧
                      ∀ x ∈ T, composed.hom.base x ∉ markedSchemePointSet K) ∧
                      IsOpen (composed.toBelyiMap.belyiOpen : Set C) ∧
                        T ⊆ (composed.toBelyiMap.belyiOpen : Set C) ∧
                          (composed.toBelyiMap.belyiOpen : Set C) ⊆ U := by
  exact
    D.exists_composedMap_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_finite_complement
      hU (finite_compl_of_isOpen_nonempty hU hUne) hT hTsub

/-- One-point finite-complement-open composed-map consequence from the indexed
cohomological source package. -/
theorem exists_composedMap_controls_and_isOpen_belyiOpen_inside_open_of_finite_complement
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    {U : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite) {x : C} (hxU : x ∈ U) :
    ∃ i : ReductionIndex C,
      ∃ s1 : V,
        ∃ hnc : HasNoCommonZero (D.divisor i).evalSurjectivity.evalData
          (D.divisor i).zeroSection s1,
          ∃ φ : Φ,
            ∃ composed : SchemeBelyi.FiniteBelyiMap
              (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen) C,
              i.1.1 = Uᶜ ∧
                i.1.2 = ({x} : Set C) ∧
                  composed.hom = (D.mkPair i s1 hnc).hom ≫ (F.map φ).hom ∧
                    ((∀ y ∈ Uᶜ, composed.hom.base y ∈ markedSchemePointSet K) ∧
                      ∀ y ∈ ({x} : Set C),
                        composed.hom.base y ∉ markedSchemePointSet K) ∧
                      IsOpen (composed.toBelyiMap.belyiOpen : Set C) ∧
                        x ∈ (composed.toBelyiMap.belyiOpen : Set C) ∧
                          (composed.toBelyiMap.belyiOpen : Set C) ⊆ U := by
  have hT : ({x} : Set C).Finite := Set.finite_singleton x
  have hTsub : ({x} : Set C) ⊆ U := by
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    simpa [hy] using hxU
  rcases
      D.exists_composedMap_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_finite_complement
        hU hUcompl hT hTsub with
    ⟨i, s1, hnc, φ, composed, hiS, hiT, hhom, hcontrols, hopen, hTopen, hopenU⟩
  exact
    ⟨i, s1, hnc, φ, composed, hiS, hiT, hhom, hcontrols, hopen,
      hTopen (by simp), hopenU⟩

/-- One-point nonempty-open composed-map consequence from the indexed
cohomological source package in a finite-complement topology. -/
theorem exists_composedMap_controls_and_isOpen_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
    [Infinite K] [NonemptyOpenFiniteComplement C]
    (D : CohomologicalP1ReductionSourceData K C V F)
    {U : Set C} (hU : IsOpen U) {x : C} (hxU : x ∈ U) :
    ∃ i : ReductionIndex C,
      ∃ s1 : V,
        ∃ hnc : HasNoCommonZero (D.divisor i).evalSurjectivity.evalData
          (D.divisor i).zeroSection s1,
          ∃ φ : Φ,
            ∃ composed : SchemeBelyi.FiniteBelyiMap
              (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen) C,
              i.1.1 = Uᶜ ∧
                i.1.2 = ({x} : Set C) ∧
                  composed.hom = (D.mkPair i s1 hnc).hom ≫ (F.map φ).hom ∧
                    ((∀ y ∈ Uᶜ, composed.hom.base y ∈ markedSchemePointSet K) ∧
                      ∀ y ∈ ({x} : Set C),
                        composed.hom.base y ∉ markedSchemePointSet K) ∧
                      IsOpen (composed.toBelyiMap.belyiOpen : Set C) ∧
                        x ∈ (composed.toBelyiMap.belyiOpen : Set C) ∧
                          (composed.toBelyiMap.belyiOpen : Set C) ⊆ U := by
  exact
    D.exists_composedMap_controls_and_isOpen_belyiOpen_inside_open_of_finite_complement
      hU (finite_compl_of_isOpen_of_mem hU hxU) hxU

/-- The indexed cohomological reduction-source package gives the paper-facing
finite marked Belyi existence interface after forgetting the intermediate
reduction family. -/
theorem exists_finiteMarkedBelyiExistence
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F) :
    ∃ E : FiniteMarkedBelyiExistence K (ReductionIndex C) C,
      E.hmarkedOpen = F.hmarkedOpen := by
  rcases D.exists_p1ReductionExistence with ⟨E, hE⟩
  exact
    ⟨E.toFiniteMarkedBelyiExistence,
      hE⟩

/-- Choose the global reduction family supplied by the indexed cohomological
source data. -/
noncomputable def toP1ReductionExistence
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F) :
    P1ReductionExistence K C :=
  Classical.choose D.exists_p1ReductionExistence

theorem toP1ReductionExistence_hmarkedOpen
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F) :
    D.toP1ReductionExistence.hmarkedOpen = F.hmarkedOpen :=
  Classical.choose_spec D.exists_p1ReductionExistence

/-- Each chosen cohomological reduction-family map is finite. -/
theorem toP1ReductionExistence_map_finite_hom
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (i : ReductionIndex C) :
    IsFinite (D.toP1ReductionExistence.map i).hom :=
  SchemeBelyi.FiniteBelyiMap.isFinite_hom (D.toP1ReductionExistence.map i)

/-- Each chosen cohomological reduction-family map is dominant. -/
theorem toP1ReductionExistence_map_isDominant_hom
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (i : ReductionIndex C) :
    IsDominant (D.toP1ReductionExistence.map i).hom :=
  SchemeBelyi.FiniteBelyiMap.isDominant_hom (D.toP1ReductionExistence.map i)

/-- Each chosen cohomological reduction-family map has dense range on
underlying spaces. -/
theorem toP1ReductionExistence_map_denseRange_hom
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (i : ReductionIndex C) :
    DenseRange (D.toP1ReductionExistence.map i).hom.base :=
  SchemeBelyi.FiniteBelyiMap.denseRange_hom (D.toP1ReductionExistence.map i)

/-- Each chosen cohomological reduction-family map is etale over the marked
branch-complement open. -/
theorem toP1ReductionExistence_map_isEtale_restrict_branchOpen
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (i : ReductionIndex C) :
    IsEtale ((D.toP1ReductionExistence.map i).hom ∣_
      (SchemeBelyi.markedBelyiTarget K
        D.toP1ReductionExistence.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.isEtale_restrict_branchOpen
    (D.toP1ReductionExistence.map i)

/-- The branch-open restriction of each chosen cohomological reduction-family
map is finite. -/
theorem toP1ReductionExistence_map_isFinite_restrict_branchOpen
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (i : ReductionIndex C) :
    IsFinite ((D.toP1ReductionExistence.map i).hom ∣_
      (SchemeBelyi.markedBelyiTarget K
        D.toP1ReductionExistence.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.isFinite_restrict_branchOpen
    (D.toP1ReductionExistence.map i)

/-- The branch-open restriction of each chosen cohomological reduction-family
map is affine. -/
theorem toP1ReductionExistence_map_isAffineHom_restrict_branchOpen
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (i : ReductionIndex C) :
    IsAffineHom ((D.toP1ReductionExistence.map i).hom ∣_
      (SchemeBelyi.markedBelyiTarget K
        D.toP1ReductionExistence.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.isAffineHom_restrict_branchOpen
    (D.toP1ReductionExistence.map i)

/-- The branch-open restriction of each chosen cohomological reduction-family
map is integral. -/
theorem toP1ReductionExistence_map_isIntegralHom_restrict_branchOpen
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (i : ReductionIndex C) :
    IsIntegralHom ((D.toP1ReductionExistence.map i).hom ∣_
      (SchemeBelyi.markedBelyiTarget K
        D.toP1ReductionExistence.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.isIntegralHom_restrict_branchOpen
    (D.toP1ReductionExistence.map i)

/-- The branch-open restriction of each chosen cohomological reduction-family
map is locally of finite type. -/
theorem toP1ReductionExistence_map_locallyOfFiniteType_restrict_branchOpen
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (i : ReductionIndex C) :
    LocallyOfFiniteType ((D.toP1ReductionExistence.map i).hom ∣_
      (SchemeBelyi.markedBelyiTarget K
        D.toP1ReductionExistence.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.locallyOfFiniteType_restrict_branchOpen
    (D.toP1ReductionExistence.map i)

/-- The branch-open restriction of each chosen cohomological reduction-family
map is separated. -/
theorem toP1ReductionExistence_map_isSeparated_restrict_branchOpen
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (i : ReductionIndex C) :
    IsSeparated ((D.toP1ReductionExistence.map i).hom ∣_
      (SchemeBelyi.markedBelyiTarget K
        D.toP1ReductionExistence.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.isSeparated_restrict_branchOpen
    (D.toP1ReductionExistence.map i)

/-- The branch-open restriction of each chosen cohomological reduction-family
map is quasi-compact. -/
theorem toP1ReductionExistence_map_quasiCompact_restrict_branchOpen
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (i : ReductionIndex C) :
    QuasiCompact ((D.toP1ReductionExistence.map i).hom ∣_
      (SchemeBelyi.markedBelyiTarget K
        D.toP1ReductionExistence.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.quasiCompact_restrict_branchOpen
    (D.toP1ReductionExistence.map i)

/-- Each chosen cohomological reduction-family map is affine. -/
theorem toP1ReductionExistence_map_isAffineHom_hom
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (i : ReductionIndex C) :
    IsAffineHom (D.toP1ReductionExistence.map i).hom :=
  SchemeBelyi.FiniteBelyiMap.isAffineHom_hom (D.toP1ReductionExistence.map i)

/-- Each chosen cohomological reduction-family map is integral. -/
theorem toP1ReductionExistence_map_isIntegralHom_hom
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (i : ReductionIndex C) :
    IsIntegralHom (D.toP1ReductionExistence.map i).hom :=
  SchemeBelyi.FiniteBelyiMap.isIntegralHom_hom (D.toP1ReductionExistence.map i)

/-- Each chosen cohomological reduction-family map is locally of finite type. -/
theorem toP1ReductionExistence_map_locallyOfFiniteType_hom
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (i : ReductionIndex C) :
    LocallyOfFiniteType (D.toP1ReductionExistence.map i).hom :=
  SchemeBelyi.FiniteBelyiMap.locallyOfFiniteType_hom (D.toP1ReductionExistence.map i)

/-- Each chosen cohomological reduction-family map is separated. -/
theorem toP1ReductionExistence_map_isSeparated_hom
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (i : ReductionIndex C) :
    IsSeparated (D.toP1ReductionExistence.map i).hom :=
  SchemeBelyi.FiniteBelyiMap.isSeparated_hom (D.toP1ReductionExistence.map i)

/-- Each chosen cohomological reduction-family map is quasi-compact. -/
theorem toP1ReductionExistence_map_quasiCompact_hom
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (i : ReductionIndex C) :
    QuasiCompact (D.toP1ReductionExistence.map i).hom :=
  SchemeBelyi.FiniteBelyiMap.quasiCompact_hom (D.toP1ReductionExistence.map i)

/-- Forget the chosen cohomological reduction family to the paper-facing finite
marked Belyi existence interface. -/
noncomputable def toFiniteMarkedBelyiExistence
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F) :
    FiniteMarkedBelyiExistence K (ReductionIndex C) C :=
  D.toP1ReductionExistence.toFiniteMarkedBelyiExistence

theorem toFiniteMarkedBelyiExistence_hmarkedOpen
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F) :
    D.toFiniteMarkedBelyiExistence.hmarkedOpen = F.hmarkedOpen := by
  simp [toFiniteMarkedBelyiExistence, toP1ReductionExistence_hmarkedOpen]

theorem toFiniteMarkedBelyiExistence_map_apply
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (i : ReductionIndex C) :
    D.toFiniteMarkedBelyiExistence.map i = D.toP1ReductionExistence.map i := rfl

/-- Each chosen cohomological finite marked map is finite. -/
theorem toFiniteMarkedBelyiExistence_map_finite_hom
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (i : ReductionIndex C) :
    IsFinite (D.toFiniteMarkedBelyiExistence.map i).hom :=
  SchemeBelyi.FiniteBelyiMap.isFinite_hom (D.toFiniteMarkedBelyiExistence.map i)

/-- Each chosen cohomological finite marked map is dominant. -/
theorem toFiniteMarkedBelyiExistence_map_isDominant_hom
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (i : ReductionIndex C) :
    IsDominant (D.toFiniteMarkedBelyiExistence.map i).hom :=
  SchemeBelyi.FiniteBelyiMap.isDominant_hom (D.toFiniteMarkedBelyiExistence.map i)

/-- Each chosen cohomological finite marked map has dense range on underlying
spaces. -/
theorem toFiniteMarkedBelyiExistence_map_denseRange_hom
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (i : ReductionIndex C) :
    DenseRange (D.toFiniteMarkedBelyiExistence.map i).hom.base :=
  SchemeBelyi.FiniteBelyiMap.denseRange_hom (D.toFiniteMarkedBelyiExistence.map i)

/-- Each chosen cohomological finite marked map is etale over the marked
branch-complement open. -/
theorem toFiniteMarkedBelyiExistence_map_isEtale_restrict_branchOpen
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (i : ReductionIndex C) :
    IsEtale ((D.toFiniteMarkedBelyiExistence.map i).hom ∣_
      (SchemeBelyi.markedBelyiTarget K
        D.toFiniteMarkedBelyiExistence.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.isEtale_restrict_branchOpen
    (D.toFiniteMarkedBelyiExistence.map i)

/-- The branch-open restriction of each chosen cohomological map is finite. -/
theorem toFiniteMarkedBelyiExistence_map_isFinite_restrict_branchOpen
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (i : ReductionIndex C) :
    IsFinite ((D.toFiniteMarkedBelyiExistence.map i).hom ∣_
      (SchemeBelyi.markedBelyiTarget K
        D.toFiniteMarkedBelyiExistence.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.isFinite_restrict_branchOpen
    (D.toFiniteMarkedBelyiExistence.map i)

/-- The branch-open restriction of each chosen cohomological map is affine. -/
theorem toFiniteMarkedBelyiExistence_map_isAffineHom_restrict_branchOpen
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (i : ReductionIndex C) :
    IsAffineHom ((D.toFiniteMarkedBelyiExistence.map i).hom ∣_
      (SchemeBelyi.markedBelyiTarget K
        D.toFiniteMarkedBelyiExistence.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.isAffineHom_restrict_branchOpen
    (D.toFiniteMarkedBelyiExistence.map i)

/-- The branch-open restriction of each chosen cohomological map is integral. -/
theorem toFiniteMarkedBelyiExistence_map_isIntegralHom_restrict_branchOpen
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (i : ReductionIndex C) :
    IsIntegralHom ((D.toFiniteMarkedBelyiExistence.map i).hom ∣_
      (SchemeBelyi.markedBelyiTarget K
        D.toFiniteMarkedBelyiExistence.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.isIntegralHom_restrict_branchOpen
    (D.toFiniteMarkedBelyiExistence.map i)

/-- The branch-open restriction of each chosen cohomological map is locally of
finite type. -/
theorem toFiniteMarkedBelyiExistence_map_locallyOfFiniteType_restrict_branchOpen
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (i : ReductionIndex C) :
    LocallyOfFiniteType ((D.toFiniteMarkedBelyiExistence.map i).hom ∣_
      (SchemeBelyi.markedBelyiTarget K
        D.toFiniteMarkedBelyiExistence.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.locallyOfFiniteType_restrict_branchOpen
    (D.toFiniteMarkedBelyiExistence.map i)

/-- The branch-open restriction of each chosen cohomological map is separated. -/
theorem toFiniteMarkedBelyiExistence_map_isSeparated_restrict_branchOpen
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (i : ReductionIndex C) :
    IsSeparated ((D.toFiniteMarkedBelyiExistence.map i).hom ∣_
      (SchemeBelyi.markedBelyiTarget K
        D.toFiniteMarkedBelyiExistence.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.isSeparated_restrict_branchOpen
    (D.toFiniteMarkedBelyiExistence.map i)

/-- The branch-open restriction of each chosen cohomological map is
quasi-compact. -/
theorem toFiniteMarkedBelyiExistence_map_quasiCompact_restrict_branchOpen
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (i : ReductionIndex C) :
    QuasiCompact ((D.toFiniteMarkedBelyiExistence.map i).hom ∣_
      (SchemeBelyi.markedBelyiTarget K
        D.toFiniteMarkedBelyiExistence.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.quasiCompact_restrict_branchOpen
    (D.toFiniteMarkedBelyiExistence.map i)

/-- Each chosen cohomological finite marked map is affine. -/
theorem toFiniteMarkedBelyiExistence_map_isAffineHom_hom
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (i : ReductionIndex C) :
    IsAffineHom (D.toFiniteMarkedBelyiExistence.map i).hom :=
  SchemeBelyi.FiniteBelyiMap.isAffineHom_hom (D.toFiniteMarkedBelyiExistence.map i)

/-- Each chosen cohomological finite marked map is integral. -/
theorem toFiniteMarkedBelyiExistence_map_isIntegralHom_hom
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (i : ReductionIndex C) :
    IsIntegralHom (D.toFiniteMarkedBelyiExistence.map i).hom :=
  SchemeBelyi.FiniteBelyiMap.isIntegralHom_hom (D.toFiniteMarkedBelyiExistence.map i)

/-- Each chosen cohomological finite marked map is locally of finite type. -/
theorem toFiniteMarkedBelyiExistence_map_locallyOfFiniteType_hom
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (i : ReductionIndex C) :
    LocallyOfFiniteType (D.toFiniteMarkedBelyiExistence.map i).hom :=
  SchemeBelyi.FiniteBelyiMap.locallyOfFiniteType_hom
    (D.toFiniteMarkedBelyiExistence.map i)

/-- Each chosen cohomological finite marked map is separated. -/
theorem toFiniteMarkedBelyiExistence_map_isSeparated_hom
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (i : ReductionIndex C) :
    IsSeparated (D.toFiniteMarkedBelyiExistence.map i).hom :=
  SchemeBelyi.FiniteBelyiMap.isSeparated_hom (D.toFiniteMarkedBelyiExistence.map i)

/-- Each chosen cohomological finite marked map is quasi-compact. -/
theorem toFiniteMarkedBelyiExistence_map_quasiCompact_hom
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (i : ReductionIndex C) :
    QuasiCompact (D.toFiniteMarkedBelyiExistence.map i).hom :=
  SchemeBelyi.FiniteBelyiMap.quasiCompact_hom (D.toFiniteMarkedBelyiExistence.map i)

theorem toFiniteMarkedBelyiExistence_mem_belyiOpen_iff
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (i : ReductionIndex C) (x : C) :
    x ∈ (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
      (ReductionIndex C) D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i ↔
      (D.toFiniteMarkedBelyiExistence.map i).hom.base x ∉ markedSchemePointSet K := by
  exact
    FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence_mem_belyiOpen_iff
      K (ReductionIndex C) D.toFiniteMarkedBelyiExistence i x

theorem toFiniteMarkedBelyiExistence_belyiOpen_carrier
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (i : ReductionIndex C) :
    (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
      (ReductionIndex C) D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i =
      {x : C | (D.toFiniteMarkedBelyiExistence.map i).hom.base x ∉
        markedSchemePointSet K} := by
  exact
    FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence_belyiOpen_carrier
      K (ReductionIndex C) D.toFiniteMarkedBelyiExistence i

theorem toFiniteMarkedBelyiExistence_belyiOpen_eq_schemeBelyi
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (i : ReductionIndex C) :
    (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
      (ReductionIndex C) D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i =
      ((D.toFiniteMarkedBelyiExistence.map i).toBelyiMap.belyiOpen : Set C) := by
  exact
    FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence_belyiOpen_eq_schemeBelyi
      K (ReductionIndex C) D.toFiniteMarkedBelyiExistence i

/-- Direct finite disjoint-set consequence from the cohomological source
package after choosing the reduction family. -/
theorem exists_for_finite_disjoint
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ i : ReductionIndex C,
      (∀ x ∈ S, (D.toFiniteMarkedBelyiExistence.map i).hom.base x ∈
        markedSchemePointSet K) ∧
        ∀ x ∈ T, (D.toFiniteMarkedBelyiExistence.map i).hom.base x ∉
          markedSchemePointSet K :=
  D.toFiniteMarkedBelyiExistence.exists_for_finite_disjoint hS hT hdis

/-- Direct scheme-Belyi-open form of the finite disjoint-set conclusion after
choosing the cohomological reduction family. -/
theorem exists_map_belyiOpen_controls
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ i : ReductionIndex C,
      T ⊆ ((D.toFiniteMarkedBelyiExistence.map i).toBelyiMap.belyiOpen : Set C) ∧
        ((D.toFiniteMarkedBelyiExistence.map i).toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  exact
    FiniteMarkedBelyiExistence.exists_map_belyiOpen_controls
      (K := K) (Φ := ReductionIndex C) D.toFiniteMarkedBelyiExistence
      hS hT hdis

/-- Direct same-map finite disjoint-set consequence after choosing the
cohomological reduction family: the selected finite Belyi map satisfies the
marked controls and its Belyi open contains `T` and avoids `S`. -/
theorem exists_map_controls_and_belyiOpen_controls
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ i : ReductionIndex C,
      ((∀ x ∈ S, (D.toFiniteMarkedBelyiExistence.map i).hom.base x ∈
        markedSchemePointSet K) ∧
        ∀ x ∈ T, (D.toFiniteMarkedBelyiExistence.map i).hom.base x ∉
          markedSchemePointSet K) ∧
        T ⊆ ((D.toFiniteMarkedBelyiExistence.map i).toBelyiMap.belyiOpen : Set C) ∧
          ((D.toFiniteMarkedBelyiExistence.map i).toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  exact
    FiniteMarkedBelyiExistence.exists_map_controls_and_belyiOpen_controls
      (K := K) (Φ := ReductionIndex C) D.toFiniteMarkedBelyiExistence
      hS hT hdis

/-- Direct same-map finite disjoint-set consequence after choosing the
cohomological reduction family, with explicit openness of the selected source
Belyi open. -/
theorem exists_map_controls_and_isOpen_belyiOpen_controls
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ i : ReductionIndex C,
      ((∀ x ∈ S, (D.toFiniteMarkedBelyiExistence.map i).hom.base x ∈
        markedSchemePointSet K) ∧
        ∀ x ∈ T, (D.toFiniteMarkedBelyiExistence.map i).hom.base x ∉
          markedSchemePointSet K) ∧
        IsOpen ((D.toFiniteMarkedBelyiExistence.map i).toBelyiMap.belyiOpen : Set C) ∧
          T ⊆ ((D.toFiniteMarkedBelyiExistence.map i).toBelyiMap.belyiOpen : Set C) ∧
            ((D.toFiniteMarkedBelyiExistence.map i).toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  exact
    FiniteMarkedBelyiExistence.exists_map_controls_and_isOpen_belyiOpen_controls
      (K := K) (Φ := ReductionIndex C) D.toFiniteMarkedBelyiExistence
      hS hT hdis

/-- Actual finite-map one-point Belyi-open consequence after choosing the
cohomological reduction family. -/
theorem exists_map_belyiOpen_inside_complement
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    {A : Set C} (hA : A.Finite) {x : C} (hxA : x ∉ A) :
    ∃ i : ReductionIndex C,
      IsOpen ((D.toFiniteMarkedBelyiExistence.map i).toBelyiMap.belyiOpen : Set C) ∧
        x ∈ ((D.toFiniteMarkedBelyiExistence.map i).toBelyiMap.belyiOpen : Set C) ∧
          ((D.toFiniteMarkedBelyiExistence.map i).toBelyiMap.belyiOpen : Set C) ⊆ Aᶜ := by
  exact
    FiniteMarkedBelyiExistence.exists_map_belyiOpen_inside_complement
      K (ReductionIndex C) D.toFiniteMarkedBelyiExistence hA hxA

/-- Actual finite-map finite-set Belyi-open consequence after choosing the
cohomological reduction family. -/
theorem exists_map_belyiOpen_containing_finite_inside_complement
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ i : ReductionIndex C,
      IsOpen ((D.toFiniteMarkedBelyiExistence.map i).toBelyiMap.belyiOpen : Set C) ∧
        T ⊆ ((D.toFiniteMarkedBelyiExistence.map i).toBelyiMap.belyiOpen : Set C) ∧
          ((D.toFiniteMarkedBelyiExistence.map i).toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  exact
    FiniteMarkedBelyiExistence.exists_map_belyiOpen_containing_finite_inside_complement
      K (ReductionIndex C) D.toFiniteMarkedBelyiExistence hS hT hdis

/-- Actual finite-map one-point Belyi-open consequence after choosing the
cohomological reduction family, with the finite complement supplied
explicitly. -/
theorem exists_map_belyiOpen_inside_open_of_finite_complement
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    {U : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite) {x : C} (hxU : x ∈ U) :
    ∃ i : ReductionIndex C,
      IsOpen ((D.toFiniteMarkedBelyiExistence.map i).toBelyiMap.belyiOpen : Set C) ∧
        x ∈ ((D.toFiniteMarkedBelyiExistence.map i).toBelyiMap.belyiOpen : Set C) ∧
          ((D.toFiniteMarkedBelyiExistence.map i).toBelyiMap.belyiOpen : Set C) ⊆ U := by
  exact
    FiniteMarkedBelyiExistence.exists_map_belyiOpen_inside_open_of_finite_complement
      K (ReductionIndex C) D.toFiniteMarkedBelyiExistence hU hUcompl hxU

/-- Actual finite-map one-point Belyi-open consequence after choosing the
cohomological reduction family in the curve-style finite-complement topology
form. -/
theorem exists_map_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
    [Infinite K] [NonemptyOpenFiniteComplement C]
    (D : CohomologicalP1ReductionSourceData K C V F)
    {U : Set C} (hU : IsOpen U) {x : C} (hxU : x ∈ U) :
    ∃ i : ReductionIndex C,
      IsOpen ((D.toFiniteMarkedBelyiExistence.map i).toBelyiMap.belyiOpen : Set C) ∧
        x ∈ ((D.toFiniteMarkedBelyiExistence.map i).toBelyiMap.belyiOpen : Set C) ∧
          ((D.toFiniteMarkedBelyiExistence.map i).toBelyiMap.belyiOpen : Set C) ⊆ U := by
  exact
    FiniteMarkedBelyiExistence.exists_map_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
      K (ReductionIndex C) D.toFiniteMarkedBelyiExistence hU hxU

/-- Actual finite-map finite-set Belyi-open consequence after choosing the
cohomological reduction family, with the finite complement supplied
explicitly. -/
theorem exists_map_belyiOpen_containing_finite_inside_open_of_finite_complement
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    {U T : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ i : ReductionIndex C,
      IsOpen ((D.toFiniteMarkedBelyiExistence.map i).toBelyiMap.belyiOpen : Set C) ∧
        T ⊆ ((D.toFiniteMarkedBelyiExistence.map i).toBelyiMap.belyiOpen : Set C) ∧
          ((D.toFiniteMarkedBelyiExistence.map i).toBelyiMap.belyiOpen : Set C) ⊆ U := by
  exact
    FiniteMarkedBelyiExistence.exists_map_belyiOpen_containing_finite_inside_open_of_finite_complement
      K (ReductionIndex C) D.toFiniteMarkedBelyiExistence hU hUcompl hT hTsub

/-- Actual finite-map finite-set Belyi-open consequence after choosing the
cohomological reduction family in the curve-style finite-complement topology
form. -/
theorem exists_map_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
    [Infinite K] [NonemptyOpenFiniteComplement C]
    (D : CohomologicalP1ReductionSourceData K C V F)
    {U T : Set C} (hU : IsOpen U) (hUne : U.Nonempty)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ i : ReductionIndex C,
      IsOpen ((D.toFiniteMarkedBelyiExistence.map i).toBelyiMap.belyiOpen : Set C) ∧
        T ⊆ ((D.toFiniteMarkedBelyiExistence.map i).toBelyiMap.belyiOpen : Set C) ∧
          ((D.toFiniteMarkedBelyiExistence.map i).toBelyiMap.belyiOpen : Set C) ⊆ U := by
  exact
    FiniteMarkedBelyiExistence.exists_map_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
      K (ReductionIndex C) D.toFiniteMarkedBelyiExistence hU hUne hT hTsub

/-- Actual finite-map finite-set Belyi-open consequence retaining marked
controls after choosing the cohomological reduction family, with the finite
complement supplied explicitly. -/
theorem exists_map_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_finite_complement
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    {U T : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ i : ReductionIndex C,
      ((∀ x ∈ Uᶜ, (D.toFiniteMarkedBelyiExistence.map i).hom.base x ∈
        markedSchemePointSet K) ∧
        ∀ x ∈ T, (D.toFiniteMarkedBelyiExistence.map i).hom.base x ∉
          markedSchemePointSet K) ∧
        IsOpen ((D.toFiniteMarkedBelyiExistence.map i).toBelyiMap.belyiOpen : Set C) ∧
          T ⊆ ((D.toFiniteMarkedBelyiExistence.map i).toBelyiMap.belyiOpen : Set C) ∧
            ((D.toFiniteMarkedBelyiExistence.map i).toBelyiMap.belyiOpen : Set C) ⊆ U := by
  exact
    FiniteMarkedBelyiExistence.exists_map_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_finite_complement
      K (ReductionIndex C) D.toFiniteMarkedBelyiExistence hU hUcompl hT hTsub

/-- Actual finite-map finite-set Belyi-open consequence retaining marked
controls after choosing the cohomological reduction family in the curve-style
finite-complement topology form. -/
theorem exists_map_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
    [Infinite K] [NonemptyOpenFiniteComplement C]
    (D : CohomologicalP1ReductionSourceData K C V F)
    {U T : Set C} (hU : IsOpen U) (hUne : U.Nonempty)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ i : ReductionIndex C,
      ((∀ x ∈ Uᶜ, (D.toFiniteMarkedBelyiExistence.map i).hom.base x ∈
        markedSchemePointSet K) ∧
        ∀ x ∈ T, (D.toFiniteMarkedBelyiExistence.map i).hom.base x ∉
          markedSchemePointSet K) ∧
        IsOpen ((D.toFiniteMarkedBelyiExistence.map i).toBelyiMap.belyiOpen : Set C) ∧
          T ⊆ ((D.toFiniteMarkedBelyiExistence.map i).toBelyiMap.belyiOpen : Set C) ∧
            ((D.toFiniteMarkedBelyiExistence.map i).toBelyiMap.belyiOpen : Set C) ⊆ U := by
  exact
    FiniteMarkedBelyiExistence.exists_map_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
      K (ReductionIndex C) D.toFiniteMarkedBelyiExistence hU hUne hT hTsub

/-- Actual finite-map finite-set Belyi-open consequence retaining marked
controls on the chosen `P1ReductionExistence` maps, with the finite complement
supplied explicitly. -/
theorem exists_p1Reduction_map_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_finite_complement
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    {U T : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ i : ReductionIndex C,
      ((∀ x ∈ Uᶜ, (D.toP1ReductionExistence.map i).hom.base x ∈
        markedSchemePointSet K) ∧
        ∀ x ∈ T, (D.toP1ReductionExistence.map i).hom.base x ∉
          markedSchemePointSet K) ∧
        IsOpen ((D.toP1ReductionExistence.map i).toBelyiMap.belyiOpen : Set C) ∧
          T ⊆ ((D.toP1ReductionExistence.map i).toBelyiMap.belyiOpen : Set C) ∧
            ((D.toP1ReductionExistence.map i).toBelyiMap.belyiOpen : Set C) ⊆ U := by
  simpa [toFiniteMarkedBelyiExistence] using
    D.exists_map_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_finite_complement
      hU hUcompl hT hTsub

/-- Actual finite-map finite-set Belyi-open consequence retaining marked
controls on the chosen `P1ReductionExistence` maps in the curve-style
finite-complement topology form. -/
theorem exists_p1Reduction_map_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
    [Infinite K] [NonemptyOpenFiniteComplement C]
    (D : CohomologicalP1ReductionSourceData K C V F)
    {U T : Set C} (hU : IsOpen U) (hUne : U.Nonempty)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ i : ReductionIndex C,
      ((∀ x ∈ Uᶜ, (D.toP1ReductionExistence.map i).hom.base x ∈
        markedSchemePointSet K) ∧
        ∀ x ∈ T, (D.toP1ReductionExistence.map i).hom.base x ∉
          markedSchemePointSet K) ∧
        IsOpen ((D.toP1ReductionExistence.map i).toBelyiMap.belyiOpen : Set C) ∧
          T ⊆ ((D.toP1ReductionExistence.map i).toBelyiMap.belyiOpen : Set C) ∧
            ((D.toP1ReductionExistence.map i).toBelyiMap.belyiOpen : Set C) ⊆ U := by
  simpa [toFiniteMarkedBelyiExistence] using
    D.exists_map_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
      hU hUne hT hTsub

/-- Corollary 1.2-style one-point Belyi-open consequence directly from the
cohomological source package. -/
theorem exists_belyiOpen_inside_complement
    [Infinite K] [T1Space (P1 K)]
    (D : CohomologicalP1ReductionSourceData K C V F)
    {A : Set C} (hA : A.Finite) {x : C} (hxA : x ∉ A) :
    ∃ i : ReductionIndex C,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
        (ReductionIndex C) D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ∧
        x ∈ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
          (ReductionIndex C) D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
            (ReductionIndex C) D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ⊆ Aᶜ := by
  exact FiniteMarkedBelyiExistence.exists_belyiOpen_inside_complement
    K (ReductionIndex C) D.toFiniteMarkedBelyiExistence hA hxA

/-- Finite-set Belyi-open consequence directly from the cohomological source
package, inside the complement of a finite set. -/
theorem exists_belyiOpen_containing_finite_inside_complement
    [Infinite K] [T1Space (P1 K)]
    (D : CohomologicalP1ReductionSourceData K C V F)
    {S T : Set C} (hS : S.Finite) (hT : T.Finite) (hdis : Disjoint S T) :
    ∃ i : ReductionIndex C,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
        (ReductionIndex C) D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ∧
        T ⊆ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
          (ReductionIndex C) D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
            (ReductionIndex C) D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ⊆ Sᶜ := by
  exact
    FiniteMarkedBelyiExistence.exists_belyiOpen_containing_finite_inside_complement
      K (ReductionIndex C) D.toFiniteMarkedBelyiExistence hS hT hdis

/-- One-point Belyi-open consequence directly from the cohomological source
package, with the finite complement supplied explicitly. -/
theorem exists_belyiOpen_inside_open_of_finite_complement
    [Infinite K] [T1Space (P1 K)]
    (D : CohomologicalP1ReductionSourceData K C V F)
    {U : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite) {x : C} (hxU : x ∈ U) :
    ∃ i : ReductionIndex C,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
        (ReductionIndex C) D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ∧
        x ∈ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
          (ReductionIndex C) D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
            (ReductionIndex C) D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ⊆ U := by
  exact FiniteMarkedBelyiExistence.exists_belyiOpen_inside_open_of_finite_complement
    K (ReductionIndex C) D.toFiniteMarkedBelyiExistence hU hUcompl hxU

/-- Finite-set Belyi-open consequence directly from the cohomological source
package, with the finite complement supplied explicitly. -/
theorem exists_belyiOpen_containing_finite_inside_open_of_finite_complement
    [Infinite K] [T1Space (P1 K)]
    (D : CohomologicalP1ReductionSourceData K C V F)
    {U T : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ i : ReductionIndex C,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
        (ReductionIndex C) D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ∧
        T ⊆ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
          (ReductionIndex C) D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
            (ReductionIndex C) D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ⊆ U := by
  exact
    FiniteMarkedBelyiExistence.exists_belyiOpen_containing_finite_inside_open_of_finite_complement
      K (ReductionIndex C) D.toFiniteMarkedBelyiExistence hU hUcompl hT hTsub

/-- One-point Belyi-open consequence directly from the cohomological source
package in the curve-style finite-complement topology form. -/
theorem exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C]
    (D : CohomologicalP1ReductionSourceData K C V F)
    {U : Set C} (hU : IsOpen U) {x : C} (hxU : x ∈ U) :
    ∃ i : ReductionIndex C,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
        (ReductionIndex C) D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ∧
        x ∈ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
          (ReductionIndex C) D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
            (ReductionIndex C) D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ⊆ U := by
  exact FiniteMarkedBelyiExistence.exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
    K (ReductionIndex C) D.toFiniteMarkedBelyiExistence hU hxU

/-- The Belyi open attached to a chosen cohomological reduction index. -/
def belyiOpen
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (i : ReductionIndex C) : Set C :=
  ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
    (ReductionIndex C) D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i)

theorem mem_belyiOpen_iff
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (i : ReductionIndex C) (x : C) :
    x ∈ D.belyiOpen i ↔
      (D.toFiniteMarkedBelyiExistence.map i).hom.base x ∉ markedSchemePointSet K := by
  exact D.toFiniteMarkedBelyiExistence_mem_belyiOpen_iff i x

theorem belyiOpen_carrier
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (i : ReductionIndex C) :
    D.belyiOpen i =
      {x : C | (D.toFiniteMarkedBelyiExistence.map i).hom.base x ∉
        markedSchemePointSet K} := by
  exact D.toFiniteMarkedBelyiExistence_belyiOpen_carrier i

theorem belyiOpen_eq_schemeBelyi
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (i : ReductionIndex C) :
    D.belyiOpen i =
      ((D.toFiniteMarkedBelyiExistence.map i).toBelyiMap.belyiOpen : Set C) := by
  exact D.toFiniteMarkedBelyiExistence_belyiOpen_eq_schemeBelyi i

/-- The Belyi opens attached to the finite marked Belyi family chosen from the
cohomological source package. -/
def belyiOpenSetFamily
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F) :
    Set (Set C) :=
  D.toFiniteMarkedBelyiExistence.belyiOpenSetFamily

/-- Corollary 1.2 in basis form directly from the cohomological source package:
the Belyi opens produced by the chosen family form a basis for the source
topology. -/
theorem belyiOpenSetFamily_isTopologicalBasis
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C]
    (D : CohomologicalP1ReductionSourceData K C V F) :
    TopologicalSpace.IsTopologicalBasis D.belyiOpenSetFamily :=
  D.toFiniteMarkedBelyiExistence.belyiOpenSetFamily_isTopologicalBasis

/-- The Belyi opens produced from the cohomological source package cover the
source. -/
theorem belyiOpen_cover_univ
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C]
    (D : CohomologicalP1ReductionSourceData K C V F) :
    (Set.univ : Set C) ⊆ ⋃ i : ReductionIndex C, D.belyiOpen i := by
  exact FiniteMarkedBelyiExistence.belyiOpen_cover_univ
    K (ReductionIndex C) D.toFiniteMarkedBelyiExistence

/-- Cohomological source form of the compact-exhaustion cover bridge. -/
theorem finite_compact_cover_by_belyiOpen_exhaustions
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (Kex : ∀ i : ReductionIndex C, CompactExhaustion (D.belyiOpen i)) :
    ∃ t : Finset (ReductionIndex C × ℕ),
      (∀ p ∈ t,
        IsCompact ((Subtype.val : D.belyiOpen p.1 → C) '' (Kex p.1 p.2))) ∧
        (∀ p ∈ t,
          ((Subtype.val : D.belyiOpen p.1 → C) '' (Kex p.1 p.2)) ⊆
            D.belyiOpen p.1) ∧
          (Set.univ : Set C) ⊆
            ⋃ p ∈ t, (Subtype.val : D.belyiOpen p.1 → C) '' (Kex p.1 p.2) := by
  exact
    FiniteMarkedBelyiExistence.finite_compact_cover_by_belyiOpen_exhaustions
      K (ReductionIndex C) D.toFiniteMarkedBelyiExistence Kex

/-- Equality form of the cohomological source compact-exhaustion cover bridge. -/
theorem finite_compact_cover_by_belyiOpen_exhaustions_eq_univ
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (Kex : ∀ i : ReductionIndex C, CompactExhaustion (D.belyiOpen i)) :
    ∃ t : Finset (ReductionIndex C × ℕ),
      (∀ p ∈ t,
        IsCompact ((Subtype.val : D.belyiOpen p.1 → C) '' (Kex p.1 p.2))) ∧
        (∀ p ∈ t,
          ((Subtype.val : D.belyiOpen p.1 → C) '' (Kex p.1 p.2)) ⊆
            D.belyiOpen p.1) ∧
          (⋃ p ∈ t, (Subtype.val : D.belyiOpen p.1 → C) '' (Kex p.1 p.2)) =
            (Set.univ : Set C) := by
  exact
    FiniteMarkedBelyiExistence.finite_compact_cover_by_belyiOpen_exhaustions_eq_univ
      K (ReductionIndex C) D.toFiniteMarkedBelyiExistence Kex

/-- Cohomological source compact-cover bridge with compact exhaustions supplied
by local compactness and second countability. -/
theorem finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    [LocallyCompactSpace C] [SecondCountableTopology C]
    (D : CohomologicalP1ReductionSourceData K C V F) :
    ∃ Kex : ∀ i : ReductionIndex C, CompactExhaustion (D.belyiOpen i),
      ∃ t : Finset (ReductionIndex C × ℕ),
        (∀ p ∈ t,
          IsCompact ((Subtype.val : D.belyiOpen p.1 → C) '' (Kex p.1 p.2))) ∧
          (∀ p ∈ t,
            ((Subtype.val : D.belyiOpen p.1 → C) '' (Kex p.1 p.2)) ⊆
              D.belyiOpen p.1) ∧
            (Set.univ : Set C) ⊆
              ⋃ p ∈ t, (Subtype.val : D.belyiOpen p.1 → C) '' (Kex p.1 p.2) := by
  exact
    FiniteMarkedBelyiExistence.finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact
      K (ReductionIndex C) D.toFiniteMarkedBelyiExistence

/-- Equality form of the cohomological source compact-cover bridge with compact
exhaustions supplied by local compactness and second countability. -/
theorem finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact_eq_univ
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    [LocallyCompactSpace C] [SecondCountableTopology C]
    (D : CohomologicalP1ReductionSourceData K C V F) :
    ∃ Kex : ∀ i : ReductionIndex C, CompactExhaustion (D.belyiOpen i),
      ∃ t : Finset (ReductionIndex C × ℕ),
        (∀ p ∈ t,
          IsCompact ((Subtype.val : D.belyiOpen p.1 → C) '' (Kex p.1 p.2))) ∧
          (∀ p ∈ t,
            ((Subtype.val : D.belyiOpen p.1 → C) '' (Kex p.1 p.2)) ⊆
              D.belyiOpen p.1) ∧
            (⋃ p ∈ t, (Subtype.val : D.belyiOpen p.1 → C) '' (Kex p.1 p.2)) =
              (Set.univ : Set C) := by
  exact
    FiniteMarkedBelyiExistence.finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact_eq_univ
      K (ReductionIndex C) D.toFiniteMarkedBelyiExistence

/-- Cohomological source compact-coordinate bridge: after choosing the Belyi
family supplied by the source data, continuous product-valued coordinate maps
give the compact coordinate target sets appearing in Corollary 3.2. -/
theorem finite_compact_coordinate_sets_of_belyiOpen_exhaustions
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    [LocallyCompactSpace C] [SecondCountableTopology C]
    (D : CohomologicalP1ReductionSourceData K C V F)
    {κ : Type*} {Z : κ → Type*} [∀ j, TopologicalSpace (Z j)]
    (G : ReductionIndex C → C → ((j : κ) → Z j))
    (hG : ∀ i, Continuous (G i))
    (A : (j : κ) → Set (Z j))
    (hGA : ∀ i x, x ∈ D.belyiOpen i → ∀ j, G i x j ∈ A j) :
    ∃ Kex : ∀ i : ReductionIndex C, CompactExhaustion (D.belyiOpen i),
      ∃ t : Finset (ReductionIndex C × ℕ),
        ∃ H : (j : κ) → Set (Z j),
          (∀ j, IsCompact (H j)) ∧
            (∀ j, H j ⊆ A j) ∧
              (Set.univ : Set C) ⊆
                ⋃ p ∈ t, (Subtype.val : D.belyiOpen p.1 → C) '' (Kex p.1 p.2) ∧
                ∀ p ∈ t, ∀ x,
                  x ∈ (Subtype.val : D.belyiOpen p.1 → C) '' (Kex p.1 p.2) →
                    ∀ j, G p.1 x j ∈ H j := by
  exact
    FiniteMarkedBelyiExistence.finite_compact_coordinate_sets_of_belyiOpen_exhaustions
      K (ReductionIndex C) D.toFiniteMarkedBelyiExistence G hG A hGA

/-- Finite-set Belyi-open consequence directly from the cohomological source
package in the curve-style finite-complement topology form. -/
theorem exists_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C]
    (D : CohomologicalP1ReductionSourceData K C V F)
    {U T : Set C} (hU : IsOpen U) (hUne : U.Nonempty)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ i : ReductionIndex C,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
        (ReductionIndex C) D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ∧
        T ⊆ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
          (ReductionIndex C) D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
            (ReductionIndex C) D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ⊆ U := by
  exact
    FiniteMarkedBelyiExistence.exists_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
      K (ReductionIndex C) D.toFiniteMarkedBelyiExistence hU hUne hT hTsub

/-- Pointwise tuple-cover consequence directly from the cohomological source
package. -/
theorem pointwise_cover_complement
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (κ : Type z) [Finite κ] {S : Set C} (hS : S.Finite)
    (x : κ → {x : C // x ∉ S}) :
    ∃ i : ReductionIndex C,
      (FiniteMarkedBelyiExistence.toMarkedCoverData K
        (ReductionIndex C) D.toFiniteMarkedBelyiExistence).sendsSetToBranch S i ∧
        ∀ j, (D.toFiniteMarkedBelyiExistence.map i).hom.base (x j).1 ∉
          markedSchemePointSet K := by
  exact FiniteMarkedBelyiExistence.pointwise_cover_complement
    K (ReductionIndex C) D.toFiniteMarkedBelyiExistence κ hS x

/-- Finite tuple-subcover consequence directly from the cohomological source
package. -/
theorem finite_subcover_on_complement
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (κ : Type z) [Finite κ] [T1Space (P1 K)]
    {S : Set C} (hS : S.Finite) [CompactSpace (κ → {x : C // x ∉ S})] :
    ∃ t : Finset {i : ReductionIndex C //
        (FiniteMarkedBelyiExistence.toMarkedCoverData K
          (ReductionIndex C) D.toFiniteMarkedBelyiExistence).sendsSetToBranch S i},
      (⋃ i ∈ t,
          ((FiniteMarkedBelyiExistence.toMarkedCoverData K
            (ReductionIndex C) D.toFiniteMarkedBelyiExistence).complementCoverData S).tupleAvoidSet
              (κ := κ) i) =
        (Set.univ : Set (κ → {x : C // x ∉ S})) := by
  exact FiniteMarkedBelyiExistence.finite_subcover_on_complement
    K (ReductionIndex C) D.toFiniteMarkedBelyiExistence κ hS

/-- Membership form of the finite tuple-subcover consequence directly from the
cohomological source package. -/
theorem finite_subcover_on_complement_forall
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (κ : Type z) [Finite κ] [T1Space (P1 K)]
    {S : Set C} (hS : S.Finite) [CompactSpace (κ → {x : C // x ∉ S})] :
    ∃ t : Finset {i : ReductionIndex C //
        (FiniteMarkedBelyiExistence.toMarkedCoverData K
          (ReductionIndex C) D.toFiniteMarkedBelyiExistence).sendsSetToBranch S i},
      ∀ x : κ → {x : C // x ∉ S},
        ∃ i ∈ t,
          x ∈ ((FiniteMarkedBelyiExistence.toMarkedCoverData K
            (ReductionIndex C) D.toFiniteMarkedBelyiExistence).complementCoverData S).tupleAvoidSet
              (κ := κ) i := by
  exact FiniteMarkedBelyiExistence.finite_subcover_on_complement_forall
    K (ReductionIndex C) D.toFiniteMarkedBelyiExistence κ hS

/-- Concrete coordinate-avoidance form of the finite tuple-subcover consequence
directly from the cohomological source package. -/
theorem finite_subcover_on_complement_forall_avoidance
    [Infinite K]
    (D : CohomologicalP1ReductionSourceData K C V F)
    (κ : Type z) [Finite κ] [T1Space (P1 K)]
    {S : Set C} (hS : S.Finite) [CompactSpace (κ → {x : C // x ∉ S})] :
    ∃ t : Finset {i : ReductionIndex C //
        (FiniteMarkedBelyiExistence.toMarkedCoverData K
          (ReductionIndex C) D.toFiniteMarkedBelyiExistence).sendsSetToBranch S i},
      ∀ x : κ → {x : C // x ∉ S},
        ∃ i ∈ t, ∀ j, (D.toFiniteMarkedBelyiExistence.map i.1).hom.base (x j).1 ∉
          markedSchemePointSet K := by
  exact FiniteMarkedBelyiExistence.finite_subcover_on_complement_forall_avoidance
    K (ReductionIndex C) D.toFiniteMarkedBelyiExistence κ hS

end CohomologicalP1ReductionSourceData

end SchemeReductionSource

end CurveCohomologySections
end SourceStack
end HilbertTest
