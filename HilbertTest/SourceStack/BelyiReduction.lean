import HilbertTest.SourceStack.SchemeMarkedBelyi

/-!
Reduction through an auxiliary morphism to `P1`.

In Mochizuki's proof of Theorem 2.5, the line-bundle construction gives an
auxiliary finite morphism `ψ : X -> P1`.  One then enlarges the finite set on
`P1` by the image of the prescribed set and the ramification values of `ψ`, and
composes `ψ` with a Belyi map of `P1`.  This file checks the formal
set-theoretic part of that reduction and packages a family of such reductions
as the existing finite marked Belyi existence interface.
-/

noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace HilbertTest
namespace SourceStack
namespace BelyiReduction

open SchemeBelyi
open SchemeMarkedBelyi
open SchemeProjectiveLine

universe u z

variable {K : Type u} [Field K]
variable {C : Scheme.{u}}
variable {hmarkedOpen : IsOpen (markedSchemePointSet K)ᶜ}

/-- The finite bad set on `P1` used in the reduction: the image of the
prescribed source set under the auxiliary morphism, union a prescribed finite
set of bad target values such as ramification values. -/
def reductionBadSet (aux : C ⟶ P1 K) (S : Set C) (badValues : Set (P1 K)) :
    Set (P1 K) :=
  aux.base '' S ∪ badValues

theorem reductionBadSet_finite
    (aux : C ⟶ P1 K) {S : Set C} {badValues : Set (P1 K)}
    (hS : S.Finite) (hbad : badValues.Finite) :
    (reductionBadSet aux S badValues).Finite := by
  exact (hS.image aux.base).union hbad

theorem aux_image_mem_reductionBadSet_of_mem
    (aux : C ⟶ P1 K) {S : Set C} {badValues : Set (P1 K)}
    {x : C} (hx : x ∈ S) :
    aux.base x ∈ reductionBadSet aux S badValues := by
  exact Or.inl ⟨x, hx, rfl⟩

theorem badValue_mem_reductionBadSet_of_mem
    (aux : C ⟶ P1 K) {S : Set C} {badValues : Set (P1 K)}
    {y : P1 K} (hy : y ∈ badValues) :
    y ∈ reductionBadSet aux S badValues := by
  exact Or.inr hy

theorem image_subset_reductionBadSet
    (aux : C ⟶ P1 K) (S : Set C) (badValues : Set (P1 K)) :
    aux.base '' S ⊆ reductionBadSet aux S badValues := by
  exact Set.subset_union_left

theorem badValues_subset_reductionBadSet
    (aux : C ⟶ P1 K) (S : Set C) (badValues : Set (P1 K)) :
    badValues ⊆ reductionBadSet aux S badValues := by
  exact Set.subset_union_right

/-- A target point is outside the enlarged reduction bad set exactly when it is
not hit by the prescribed source set and is not one of the prescribed bad
target values. -/
theorem not_mem_reductionBadSet_iff
    (aux : C ⟶ P1 K) (S : Set C) (badValues : Set (P1 K))
    (y : P1 K) :
    y ∉ reductionBadSet aux S badValues ↔
      (∀ x ∈ S, aux.base x ≠ y) ∧ y ∉ badValues := by
  constructor
  · intro hy
    constructor
    · intro x hx hxy
      exact hy (Or.inl ⟨x, hx, hxy⟩)
    · intro hybad
      exact hy (Or.inr hybad)
  · intro h hy
    rcases hy with hyImage | hybad
    · rcases hyImage with ⟨x, hx, hxy⟩
      exact h.1 x hx hxy
    · exact h.2 hybad

/-- Forward form of `not_mem_reductionBadSet_iff`. -/
theorem not_mem_reductionBadSet_of_image_avoids_of_not_mem_badValues
    (aux : C ⟶ P1 K) {S : Set C} {badValues : Set (P1 K)}
    {y : P1 K}
    (himage : ∀ x ∈ S, aux.base x ≠ y)
    (hybad : y ∉ badValues) :
    y ∉ reductionBadSet aux S badValues := by
  exact (not_mem_reductionBadSet_iff aux S badValues y).2 ⟨himage, hybad⟩

/-- The enlarged reduction bad set is disjoint from a target singleton exactly
when the source image and the prescribed bad-value set avoid that target. -/
theorem disjoint_reductionBadSet_singleton_iff
    (aux : C ⟶ P1 K) (S : Set C) (badValues : Set (P1 K))
    (y : P1 K) :
    Disjoint (reductionBadSet aux S badValues) ({y} : Set (P1 K)) ↔
      (∀ x ∈ S, aux.base x ≠ y) ∧ y ∉ badValues := by
  constructor
  · intro hdis
    have hy : y ∉ reductionBadSet aux S badValues := by
      intro hy
      exact (Set.disjoint_left.mp hdis) hy (by simp)
    exact (not_mem_reductionBadSet_iff aux S badValues y).1 hy
  · intro h
    rw [Set.disjoint_left]
    intro z hz hzy
    rw [Set.mem_singleton_iff] at hzy
    subst z
    exact (not_mem_reductionBadSet_iff aux S badValues y).2 h hz

/-- Applying finite marked Belyi existence on `P1` to the enlarged reduction
bad set and a target singleton gives the `p1Map` branch-control data required
by the reduction step.  The hypotheses spell out the paper's target-avoidance
checks: the target is not in `aux(S)` and is not among the prescribed bad
values such as ramification values. -/
theorem exists_p1Map_for_reductionBadSet_target
    {Φ : Type z}
    (F : FiniteMarkedBelyiExistence K Φ (P1 K))
    (aux : C ⟶ P1 K) {S : Set C} {badValues : Set (P1 K)}
    (hS : S.Finite) (hbad : badValues.Finite)
    {targetPoint : P1 K}
    (himage : ∀ x ∈ S, aux.base x ≠ targetPoint)
    (htargetBad : targetPoint ∉ badValues) :
    ∃ φ : Φ,
      (∀ y ∈ reductionBadSet aux S badValues,
        (F.map φ).hom.base y ∈ markedSchemePointSet K) ∧
        (F.map φ).hom.base targetPoint ∉ markedSchemePointSet K := by
  have hbadSet : (reductionBadSet aux S badValues).Finite :=
    reductionBadSet_finite aux hS hbad
  have hdis :
      Disjoint (reductionBadSet aux S badValues) ({targetPoint} : Set (P1 K)) :=
    (disjoint_reductionBadSet_singleton_iff aux S badValues targetPoint).2
      ⟨himage, htargetBad⟩
  rcases F.exists_for_finite_disjoint hbadSet
      (Set.finite_singleton targetPoint) hdis with ⟨φ, hφbad, hφtarget⟩
  exact ⟨φ, hφbad, hφtarget targetPoint (by simp)⟩

/-- One reduction step for fixed finite sets `S,T` on the source curve.  The
`bad` set is the finite set on `P1` that the later Belyi map must send to the
marked branch triple; in the paper it contains `ψ(S)` and the ramification
values of `ψ`. -/
structure P1ReductionStep
    (K : Type u) [Field K] (C : Scheme.{u})
    (hmarkedOpen : IsOpen (markedSchemePointSet K)ᶜ)
    (S T : Set C) where
  bad : Set (P1 K)
  bad_finite : bad.Finite
  aux : C ⟶ P1 K
  p1Map : FiniteBelyiMap (markedBelyiTarget K hmarkedOpen) (P1 K)
  composed : FiniteBelyiMap (markedBelyiTarget K hmarkedOpen) C
  composed_base_eq :
    ∀ x : C, composed.hom.base x = p1Map.hom.base (aux.base x)
  maps_S_to_bad : ∀ x ∈ S, aux.base x ∈ bad
  p1Map_maps_bad_to_marked :
    ∀ y ∈ bad, p1Map.hom.base y ∈ markedSchemePointSet K
  targetPoint : P1 K
  maps_T_to_target : ∀ x ∈ T, aux.base x = targetPoint
  p1Map_target_avoids_marked :
    p1Map.hom.base targetPoint ∉ markedSchemePointSet K

namespace P1ReductionStep

variable {S T : Set C}

/-- Construct a reduction step from the standard bad set
`aux(S) ∪ badValues`.  This packages the routine finiteness and containment
fields so that later curve-specific work only has to supply the auxiliary map,
the marked Belyi map on `P1`, the composed finite map, and control of the
chosen bad target values. -/
def ofBadValues
    (hS : S.Finite)
    (badValues : Set (P1 K)) (hbad : badValues.Finite)
    (aux : C ⟶ P1 K)
    (p1Map : FiniteBelyiMap (markedBelyiTarget K hmarkedOpen) (P1 K))
    (composed : FiniteBelyiMap (markedBelyiTarget K hmarkedOpen) C)
    (composed_base_eq :
      ∀ x : C, composed.hom.base x = p1Map.hom.base (aux.base x))
    (p1Map_maps_bad_to_marked :
      ∀ y ∈ reductionBadSet aux S badValues,
        p1Map.hom.base y ∈ markedSchemePointSet K)
    (targetPoint : P1 K)
    (maps_T_to_target : ∀ x ∈ T, aux.base x = targetPoint)
    (p1Map_target_avoids_marked :
      p1Map.hom.base targetPoint ∉ markedSchemePointSet K) :
    P1ReductionStep K C hmarkedOpen S T where
  bad := reductionBadSet aux S badValues
  bad_finite := reductionBadSet_finite aux hS hbad
  aux := aux
  p1Map := p1Map
  composed := composed
  composed_base_eq := composed_base_eq
  maps_S_to_bad := by
    intro x hx
    exact aux_image_mem_reductionBadSet_of_mem aux hx
  p1Map_maps_bad_to_marked := p1Map_maps_bad_to_marked
  targetPoint := targetPoint
  maps_T_to_target := maps_T_to_target
  p1Map_target_avoids_marked := p1Map_target_avoids_marked

theorem ofBadValues_bad
    (hS : S.Finite)
    (badValues : Set (P1 K)) (hbad : badValues.Finite)
    (aux : C ⟶ P1 K)
    (p1Map : FiniteBelyiMap (markedBelyiTarget K hmarkedOpen) (P1 K))
    (composed : FiniteBelyiMap (markedBelyiTarget K hmarkedOpen) C)
    (composed_base_eq :
      ∀ x : C, composed.hom.base x = p1Map.hom.base (aux.base x))
    (p1Map_maps_bad_to_marked :
      ∀ y ∈ reductionBadSet aux S badValues,
        p1Map.hom.base y ∈ markedSchemePointSet K)
    (targetPoint : P1 K)
    (maps_T_to_target : ∀ x ∈ T, aux.base x = targetPoint)
    (p1Map_target_avoids_marked :
      p1Map.hom.base targetPoint ∉ markedSchemePointSet K) :
    (ofBadValues (K := K) (C := C) (hmarkedOpen := hmarkedOpen) (S := S) (T := T)
      hS badValues hbad aux p1Map composed composed_base_eq
      p1Map_maps_bad_to_marked targetPoint maps_T_to_target
      p1Map_target_avoids_marked).bad =
        reductionBadSet aux S badValues := rfl

theorem ofBadValues_bad_finite
    (hS : S.Finite)
    (badValues : Set (P1 K)) (hbad : badValues.Finite)
    (aux : C ⟶ P1 K)
    (p1Map : FiniteBelyiMap (markedBelyiTarget K hmarkedOpen) (P1 K))
    (composed : FiniteBelyiMap (markedBelyiTarget K hmarkedOpen) C)
    (composed_base_eq :
      ∀ x : C, composed.hom.base x = p1Map.hom.base (aux.base x))
    (p1Map_maps_bad_to_marked :
      ∀ y ∈ reductionBadSet aux S badValues,
        p1Map.hom.base y ∈ markedSchemePointSet K)
    (targetPoint : P1 K)
    (maps_T_to_target : ∀ x ∈ T, aux.base x = targetPoint)
    (p1Map_target_avoids_marked :
      p1Map.hom.base targetPoint ∉ markedSchemePointSet K) :
    (ofBadValues (K := K) (C := C) (hmarkedOpen := hmarkedOpen) (S := S) (T := T)
      hS badValues hbad aux p1Map composed composed_base_eq
      p1Map_maps_bad_to_marked targetPoint maps_T_to_target
      p1Map_target_avoids_marked).bad.Finite :=
  reductionBadSet_finite aux hS hbad

/-- Construct a reduction step while building the composed finite Belyi map
from the auxiliary morphism and the chosen finite Belyi map on `P1`.  The
remaining geometric input is that the composite is étale over the marked
branch-complement open. -/
def ofBadValuesComposed
    (hS : S.Finite)
    (badValues : Set (P1 K)) (hbad : badValues.Finite)
    (aux : C ⟶ P1 K) [IsFinite aux] [IsDominant aux]
    (p1Map : FiniteBelyiMap (markedBelyiTarget K hmarkedOpen) (P1 K))
    (hcomposedEtale :
      IsEtale ((aux ≫ p1Map.hom) ∣_ (markedBranchOpen K hmarkedOpen)))
    (p1Map_maps_bad_to_marked :
      ∀ y ∈ reductionBadSet aux S badValues,
        p1Map.hom.base y ∈ markedSchemePointSet K)
    (targetPoint : P1 K)
    (maps_T_to_target : ∀ x ∈ T, aux.base x = targetPoint)
    (p1Map_target_avoids_marked :
      p1Map.hom.base targetPoint ∉ markedSchemePointSet K) :
    P1ReductionStep K C hmarkedOpen S T :=
  ofBadValues (K := K) (C := C) (hmarkedOpen := hmarkedOpen) (S := S) (T := T)
    hS badValues hbad aux p1Map (p1Map.compAux aux hcomposedEtale)
    (by
      intro x
      exact SchemeBelyi.FiniteBelyiMap.compAux_base p1Map aux hcomposedEtale x)
    p1Map_maps_bad_to_marked targetPoint maps_T_to_target p1Map_target_avoids_marked

theorem ofBadValuesComposed_composed_hom
    (hS : S.Finite)
    (badValues : Set (P1 K)) (hbad : badValues.Finite)
    (aux : C ⟶ P1 K) [IsFinite aux] [IsDominant aux]
    (p1Map : FiniteBelyiMap (markedBelyiTarget K hmarkedOpen) (P1 K))
    (hcomposedEtale :
      IsEtale ((aux ≫ p1Map.hom) ∣_ (markedBranchOpen K hmarkedOpen)))
    (p1Map_maps_bad_to_marked :
      ∀ y ∈ reductionBadSet aux S badValues,
        p1Map.hom.base y ∈ markedSchemePointSet K)
    (targetPoint : P1 K)
    (maps_T_to_target : ∀ x ∈ T, aux.base x = targetPoint)
    (p1Map_target_avoids_marked :
      p1Map.hom.base targetPoint ∉ markedSchemePointSet K) :
    (ofBadValuesComposed (K := K) (C := C) (hmarkedOpen := hmarkedOpen)
      (S := S) (T := T) hS badValues hbad aux p1Map hcomposedEtale
      p1Map_maps_bad_to_marked targetPoint maps_T_to_target
      p1Map_target_avoids_marked).composed.hom =
        aux ≫ p1Map.hom := rfl

theorem ofBadValuesComposed_composed_base_eq
    (hS : S.Finite)
    (badValues : Set (P1 K)) (hbad : badValues.Finite)
    (aux : C ⟶ P1 K) [IsFinite aux] [IsDominant aux]
    (p1Map : FiniteBelyiMap (markedBelyiTarget K hmarkedOpen) (P1 K))
    (hcomposedEtale :
      IsEtale ((aux ≫ p1Map.hom) ∣_ (markedBranchOpen K hmarkedOpen)))
    (p1Map_maps_bad_to_marked :
      ∀ y ∈ reductionBadSet aux S badValues,
        p1Map.hom.base y ∈ markedSchemePointSet K)
    (targetPoint : P1 K)
    (maps_T_to_target : ∀ x ∈ T, aux.base x = targetPoint)
    (p1Map_target_avoids_marked :
      p1Map.hom.base targetPoint ∉ markedSchemePointSet K)
    (x : C) :
    (ofBadValuesComposed (K := K) (C := C) (hmarkedOpen := hmarkedOpen)
      (S := S) (T := T) hS badValues hbad aux p1Map hcomposedEtale
      p1Map_maps_bad_to_marked targetPoint maps_T_to_target
      p1Map_target_avoids_marked).composed.hom.base x =
        p1Map.hom.base (aux.base x) := by
  exact SchemeBelyi.FiniteBelyiMap.compAux_base p1Map aux hcomposedEtale x

/-- Variant of `ofBadValuesComposed` where composite étaleness is proved from
étaleness of the auxiliary morphism over the preimage of the marked
branch-complement open. -/
def ofBadValuesComposedAuxEtale
    (hS : S.Finite)
    (badValues : Set (P1 K)) (hbad : badValues.Finite)
    (aux : C ⟶ P1 K) [IsFinite aux] [IsDominant aux]
    (p1Map : FiniteBelyiMap (markedBelyiTarget K hmarkedOpen) (P1 K))
    (hAuxEtale : IsEtale (aux ∣_ p1Map.toBelyiMap.belyiOpen))
    (p1Map_maps_bad_to_marked :
      ∀ y ∈ reductionBadSet aux S badValues,
        p1Map.hom.base y ∈ markedSchemePointSet K)
    (targetPoint : P1 K)
    (maps_T_to_target : ∀ x ∈ T, aux.base x = targetPoint)
    (p1Map_target_avoids_marked :
      p1Map.hom.base targetPoint ∉ markedSchemePointSet K) :
    P1ReductionStep K C hmarkedOpen S T :=
  ofBadValuesComposed (K := K) (C := C) (hmarkedOpen := hmarkedOpen)
    (S := S) (T := T) hS badValues hbad aux p1Map
    (p1Map.compAux_etale_of_aux_restrict aux hAuxEtale)
    p1Map_maps_bad_to_marked targetPoint maps_T_to_target p1Map_target_avoids_marked

theorem ofBadValuesComposedAuxEtale_composed_hom
    (hS : S.Finite)
    (badValues : Set (P1 K)) (hbad : badValues.Finite)
    (aux : C ⟶ P1 K) [IsFinite aux] [IsDominant aux]
    (p1Map : FiniteBelyiMap (markedBelyiTarget K hmarkedOpen) (P1 K))
    (hAuxEtale : IsEtale (aux ∣_ p1Map.toBelyiMap.belyiOpen))
    (p1Map_maps_bad_to_marked :
      ∀ y ∈ reductionBadSet aux S badValues,
        p1Map.hom.base y ∈ markedSchemePointSet K)
    (targetPoint : P1 K)
    (maps_T_to_target : ∀ x ∈ T, aux.base x = targetPoint)
    (p1Map_target_avoids_marked :
      p1Map.hom.base targetPoint ∉ markedSchemePointSet K) :
    (ofBadValuesComposedAuxEtale (K := K) (C := C) (hmarkedOpen := hmarkedOpen)
      (S := S) (T := T) hS badValues hbad aux p1Map hAuxEtale
      p1Map_maps_bad_to_marked targetPoint maps_T_to_target
      p1Map_target_avoids_marked).composed.hom =
        aux ≫ p1Map.hom := rfl

theorem ofBadValuesComposedAuxEtale_composed_base_eq
    (hS : S.Finite)
    (badValues : Set (P1 K)) (hbad : badValues.Finite)
    (aux : C ⟶ P1 K) [IsFinite aux] [IsDominant aux]
    (p1Map : FiniteBelyiMap (markedBelyiTarget K hmarkedOpen) (P1 K))
    (hAuxEtale : IsEtale (aux ∣_ p1Map.toBelyiMap.belyiOpen))
    (p1Map_maps_bad_to_marked :
      ∀ y ∈ reductionBadSet aux S badValues,
        p1Map.hom.base y ∈ markedSchemePointSet K)
    (targetPoint : P1 K)
    (maps_T_to_target : ∀ x ∈ T, aux.base x = targetPoint)
    (p1Map_target_avoids_marked :
      p1Map.hom.base targetPoint ∉ markedSchemePointSet K)
    (x : C) :
    (ofBadValuesComposedAuxEtale (K := K) (C := C) (hmarkedOpen := hmarkedOpen)
      (S := S) (T := T) hS badValues hbad aux p1Map hAuxEtale
      p1Map_maps_bad_to_marked targetPoint maps_T_to_target
      p1Map_target_avoids_marked).composed.hom.base x =
        p1Map.hom.base (aux.base x) := by
  exact SchemeBelyi.FiniteBelyiMap.compAuxOfAuxEtale_base p1Map aux hAuxEtale x

variable {S T : Set C}
variable (R : P1ReductionStep K C hmarkedOpen S T)

/-- The composed map sends the prescribed source set to the marked branch
triple. -/
theorem composed_maps_S_to_marked :
    ∀ x ∈ S, R.composed.hom.base x ∈ markedSchemePointSet K := by
  intro x hx
  rw [R.composed_base_eq x]
  exact R.p1Map_maps_bad_to_marked (R.aux.base x) (R.maps_S_to_bad x hx)

/-- The composed map avoids the marked branch triple on the prescribed
noncritical set. -/
theorem composed_avoids_T_marked :
    ∀ x ∈ T, R.composed.hom.base x ∉ markedSchemePointSet K := by
  intro x hx
  rw [R.composed_base_eq x, R.maps_T_to_target x hx]
  exact R.p1Map_target_avoids_marked

/-- The one-step reduction gives the finite disjoint-set conclusion for the
fixed pair `S,T`. -/
theorem composed_controls :
    (∀ x ∈ S, R.composed.hom.base x ∈ markedSchemePointSet K) ∧
      ∀ x ∈ T, R.composed.hom.base x ∉ markedSchemePointSet K :=
  ⟨R.composed_maps_S_to_marked, R.composed_avoids_T_marked⟩

end P1ReductionStep

/-- Index type for the finite marked Belyi family obtained from reductions for
all finite disjoint pairs of source sets. -/
def ReductionIndex (C : Scheme.{u}) : Type u :=
  {p : Set C × Set C // p.1.Finite ∧ p.2.Finite ∧ Disjoint p.1 p.2}

/-- A family of reduction steps for every finite disjoint pair of source sets. -/
structure P1ReductionExistence
    (K : Type u) [Field K] (C : Scheme.{u}) where
  hmarkedOpen : IsOpen (markedSchemePointSet K)ᶜ
  step :
    ∀ {S T : Set C}, S.Finite → T.Finite → Disjoint S T →
      P1ReductionStep K C hmarkedOpen S T

namespace P1ReductionExistence

variable (E : P1ReductionExistence K C)

/-- The finite marked Belyi map attached to an indexed reduction. -/
def map (i : ReductionIndex C) :
    FiniteBelyiMap (markedBelyiTarget K E.hmarkedOpen) C :=
  E.step i.2.1 i.2.2.1 i.2.2.2 |>.composed

/-- A reduction family instantiates the paper-facing finite marked Belyi
existence interface. -/
def toFiniteMarkedBelyiExistence :
    FiniteMarkedBelyiExistence K (ReductionIndex C) C where
  hmarkedOpen := E.hmarkedOpen
  map := E.map
  exists_for_finite_disjoint := by
    intro S T hS hT hdis
    let i : ReductionIndex C := ⟨(S, T), hS, hT, hdis⟩
    exact
      ⟨i,
        (E.step hS hT hdis).composed_maps_S_to_marked,
        (E.step hS hT hdis).composed_avoids_T_marked⟩

theorem toFiniteMarkedBelyiExistence_hmarkedOpen :
    E.toFiniteMarkedBelyiExistence.hmarkedOpen = E.hmarkedOpen := rfl

theorem toFiniteMarkedBelyiExistence_map_apply
    (i : ReductionIndex C) :
    E.toFiniteMarkedBelyiExistence.map i = E.map i := rfl

/-- Direct finite disjoint-set conclusion from a reduction family. -/
theorem exists_for_finite_disjoint
    {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ i : ReductionIndex C,
      (∀ x ∈ S, (E.map i).hom.base x ∈ markedSchemePointSet K) ∧
        ∀ x ∈ T, (E.map i).hom.base x ∉ markedSchemePointSet K := by
  exact E.toFiniteMarkedBelyiExistence.exists_for_finite_disjoint hS hT hdis

/-- Corollary 1.2-style one-point open consequence directly from a reduction
family. -/
theorem exists_belyiOpen_inside_complement
    [T1Space (P1 K)]
    {A : Set C} (hA : A.Finite) {x : C} (hxA : x ∉ A) :
    ∃ i : ReductionIndex C,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
        (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ∧
        x ∈ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
          (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
            (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ⊆ Aᶜ := by
  exact FiniteMarkedBelyiExistence.exists_belyiOpen_inside_complement
    K (ReductionIndex C) E.toFiniteMarkedBelyiExistence hA hxA

/-- Corollary 1.2-style finite-set open consequence directly from a reduction
family, inside the complement of a finite source set. -/
theorem exists_belyiOpen_containing_finite_inside_complement
    [T1Space (P1 K)]
    {S T : Set C} (hS : S.Finite) (hT : T.Finite) (hdis : Disjoint S T) :
    ∃ i : ReductionIndex C,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
        (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ∧
        T ⊆ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
          (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
            (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ⊆ Sᶜ := by
  exact
    FiniteMarkedBelyiExistence.exists_belyiOpen_containing_finite_inside_complement
      K (ReductionIndex C) E.toFiniteMarkedBelyiExistence hS hT hdis

/-- Corollary 1.2-style one-point open consequence directly from a reduction
family, with the finite complement supplied explicitly. -/
theorem exists_belyiOpen_inside_open_of_finite_complement
    [T1Space (P1 K)]
    {U : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite) {x : C} (hxU : x ∈ U) :
    ∃ i : ReductionIndex C,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
        (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ∧
        x ∈ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
          (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
            (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ⊆ U := by
  exact FiniteMarkedBelyiExistence.exists_belyiOpen_inside_open_of_finite_complement
    K (ReductionIndex C) E.toFiniteMarkedBelyiExistence hU hUcompl hxU

/-- Corollary 1.2-style finite-set open consequence directly from a reduction
family, with the finite complement supplied explicitly. -/
theorem exists_belyiOpen_containing_finite_inside_open_of_finite_complement
    [T1Space (P1 K)]
    {U T : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ i : ReductionIndex C,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
        (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ∧
        T ⊆ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
          (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
            (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ⊆ U := by
  exact
    FiniteMarkedBelyiExistence.exists_belyiOpen_containing_finite_inside_open_of_finite_complement
      K (ReductionIndex C) E.toFiniteMarkedBelyiExistence hU hUcompl hT hTsub

/-- Corollary 1.2-style one-point open consequence directly from a reduction
family in the curve-style finite-complement topology form. -/
theorem exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
    [T1Space (P1 K)] [NonemptyOpenFiniteComplement C]
    {U : Set C} (hU : IsOpen U) {x : C} (hxU : x ∈ U) :
    ∃ i : ReductionIndex C,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
        (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ∧
        x ∈ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
          (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
            (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ⊆ U := by
  exact FiniteMarkedBelyiExistence.exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
    K (ReductionIndex C) E.toFiniteMarkedBelyiExistence hU hxU

/-- Corollary 1.2-style finite-set open consequence directly from a reduction
family in the curve-style finite-complement topology form. -/
theorem exists_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
    [T1Space (P1 K)] [NonemptyOpenFiniteComplement C]
    {U T : Set C} (hU : IsOpen U) (hUne : U.Nonempty)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ i : ReductionIndex C,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
        (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ∧
        T ⊆ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
          (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
            (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ⊆ U := by
  exact
    FiniteMarkedBelyiExistence.exists_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
      K (ReductionIndex C) E.toFiniteMarkedBelyiExistence hU hUne hT hTsub

/-- Pointwise tuple-cover consequence directly from a reduction family. -/
theorem pointwise_cover_complement
    (κ : Type z) [Finite κ] {S : Set C} (hS : S.Finite)
    (x : κ → {x : C // x ∉ S}) :
    ∃ i : ReductionIndex C,
      (FiniteMarkedBelyiExistence.toMarkedCoverData K
        (ReductionIndex C) E.toFiniteMarkedBelyiExistence).sendsSetToBranch S i ∧
        ∀ j, (E.map i).hom.base (x j).1 ∉ markedSchemePointSet K := by
  exact FiniteMarkedBelyiExistence.pointwise_cover_complement
    K (ReductionIndex C) E.toFiniteMarkedBelyiExistence κ hS x

/-- Finite tuple-subcover consequence directly from a reduction family. -/
theorem finite_subcover_on_complement
    (κ : Type z) [Finite κ] [T1Space (P1 K)]
    {S : Set C} (hS : S.Finite) [CompactSpace (κ → {x : C // x ∉ S})] :
    ∃ t : Finset {i : ReductionIndex C //
        (FiniteMarkedBelyiExistence.toMarkedCoverData K
          (ReductionIndex C) E.toFiniteMarkedBelyiExistence).sendsSetToBranch S i},
      (⋃ i ∈ t,
          ((FiniteMarkedBelyiExistence.toMarkedCoverData K
            (ReductionIndex C) E.toFiniteMarkedBelyiExistence).complementCoverData S).tupleAvoidSet
              (κ := κ) i) =
        (Set.univ : Set (κ → {x : C // x ∉ S})) := by
  exact FiniteMarkedBelyiExistence.finite_subcover_on_complement
    K (ReductionIndex C) E.toFiniteMarkedBelyiExistence κ hS

/-- Membership form of the finite tuple-subcover consequence directly from a
reduction family. -/
theorem finite_subcover_on_complement_forall
    (κ : Type z) [Finite κ] [T1Space (P1 K)]
    {S : Set C} (hS : S.Finite) [CompactSpace (κ → {x : C // x ∉ S})] :
    ∃ t : Finset {i : ReductionIndex C //
        (FiniteMarkedBelyiExistence.toMarkedCoverData K
          (ReductionIndex C) E.toFiniteMarkedBelyiExistence).sendsSetToBranch S i},
      ∀ x : κ → {x : C // x ∉ S},
        ∃ i ∈ t,
          x ∈ ((FiniteMarkedBelyiExistence.toMarkedCoverData K
            (ReductionIndex C) E.toFiniteMarkedBelyiExistence).complementCoverData S).tupleAvoidSet
              (κ := κ) i := by
  exact FiniteMarkedBelyiExistence.finite_subcover_on_complement_forall
    K (ReductionIndex C) E.toFiniteMarkedBelyiExistence κ hS

end P1ReductionExistence

end BelyiReduction
end SourceStack
end HilbertTest
