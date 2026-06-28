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

variable {hmarkedOpen : IsOpen (markedSchemePointSet K)ᶜ}

/-- If a finite marked Belyi map on `P1` sends a bad set to the marked branch
triple, then its Belyi open is contained in the complement of that bad set. -/
theorem p1Map_belyiOpen_subset_compl_of_maps_bad_to_marked
    (p1Map : FiniteBelyiMap (markedBelyiTarget K hmarkedOpen) (P1 K))
    {bad : Set (P1 K)}
    (hbad : ∀ y ∈ bad, p1Map.hom.base y ∈ markedSchemePointSet K) :
    (p1Map.toBelyiMap.belyiOpen : Set (P1 K)) ⊆ badᶜ := by
  intro y hyOpen hyBad
  have hyNotMarked :
      p1Map.hom.base y ∉ markedSchemePointSet K :=
    (FiniteBelyiMap.mem_marked_belyiOpen_iff
      (K := K) (hmarkedOpen := hmarkedOpen) p1Map y).1 hyOpen
  exact hyNotMarked (hbad y hyBad)

/-- Specialization to the reduction bad set `aux(S) ∪ badValues`. -/
theorem p1Map_belyiOpen_subset_compl_reductionBadSet_of_maps_bad_to_marked
    (p1Map : FiniteBelyiMap (markedBelyiTarget K hmarkedOpen) (P1 K))
    (aux : C ⟶ P1 K) (S : Set C) (badValues : Set (P1 K))
    (hbad : ∀ y ∈ reductionBadSet aux S badValues,
      p1Map.hom.base y ∈ markedSchemePointSet K) :
    (p1Map.toBelyiMap.belyiOpen : Set (P1 K)) ⊆
      (reductionBadSet aux S badValues)ᶜ := by
  exact p1Map_belyiOpen_subset_compl_of_maps_bad_to_marked p1Map hbad

/-- Bundled form of the `P1` selection step: finite marked Belyi existence gives
a map controlling the enlarged bad set and target point, and the selected map's
Belyi open avoids the enlarged bad set. -/
theorem exists_p1Map_for_reductionBadSet_target_with_belyiOpen_subset_compl
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
        (F.map φ).hom.base targetPoint ∉ markedSchemePointSet K ∧
          ((F.map φ).toBelyiMap.belyiOpen : Set (P1 K)) ⊆
            (reductionBadSet aux S badValues)ᶜ := by
  rcases exists_p1Map_for_reductionBadSet_target F aux hS hbad
      himage htargetBad with ⟨φ, hφbad, hφtarget⟩
  exact
    ⟨φ, hφbad, hφtarget,
      p1Map_belyiOpen_subset_compl_reductionBadSet_of_maps_bad_to_marked
        (F.map φ) aux S badValues hφbad⟩

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

/-- Fixed-pair source material for the auxiliary-map reduction.  This packages
the geometric inputs needed to turn finite marked Belyi existence on `P1` into
a reduction step on `C`: an auxiliary finite dominant morphism, a finite set of
bad values, a target point for the noncritical set, and the étaleness check used
after selecting a Belyi map on `P1`. -/
structure P1ReductionAuxiliaryData
    (K : Type u) [Field K] (C : Scheme.{u})
    {Φ : Type z} (F : FiniteMarkedBelyiExistence K Φ (P1 K))
    (S T : Set C) where
  badValues : Set (P1 K)
  badValues_finite : badValues.Finite
  aux : C ⟶ P1 K
  aux_finite : IsFinite aux
  aux_dominant : IsDominant aux
  targetPoint : P1 K
  image_avoids_target : ∀ x ∈ S, aux.base x ≠ targetPoint
  target_not_bad : targetPoint ∉ badValues
  maps_T_to_target : ∀ x ∈ T, aux.base x = targetPoint
  aux_etale_on_selected_belyiOpen :
    ∀ φ : Φ,
      ((F.map φ).toBelyiMap.belyiOpen : Set (P1 K)) ⊆
          (reductionBadSet aux S badValues)ᶜ →
        IsEtale (aux ∣_ (F.map φ).toBelyiMap.belyiOpen)

namespace P1ReductionAuxiliaryData

variable {Φ : Type z}
variable {F : FiniteMarkedBelyiExistence K Φ (P1 K)}
variable {S T : Set C}
variable (D : P1ReductionAuxiliaryData K C F S T)

/-- The auxiliary-data bad set has finite enlarged reduction bad set. -/
theorem reductionBadSet_finite (hS : S.Finite) :
    (reductionBadSet D.aux S D.badValues).Finite := by
  exact BelyiReduction.reductionBadSet_finite D.aux hS D.badValues_finite

end P1ReductionAuxiliaryData

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

/-- Construct a one-step reduction directly from finite marked Belyi existence
on `P1`, target avoidance for the enlarged bad set, and an auxiliary-étaleness
criterion over any selected Belyi open avoiding that bad set.  This packages
the reduction paragraph of Theorem 2.5 into a single formal handoff. -/
theorem exists_of_p1MapExistence_auxEtale
    {Φ : Type z}
    (F : FiniteMarkedBelyiExistence K Φ (P1 K))
    (hS : S.Finite)
    (badValues : Set (P1 K)) (hbad : badValues.Finite)
    (aux : C ⟶ P1 K) [IsFinite aux] [IsDominant aux]
    {targetPoint : P1 K}
    (himage : ∀ x ∈ S, aux.base x ≠ targetPoint)
    (htargetBad : targetPoint ∉ badValues)
    (maps_T_to_target : ∀ x ∈ T, aux.base x = targetPoint)
    (hAuxEtale :
      ∀ φ : Φ,
        ((F.map φ).toBelyiMap.belyiOpen : Set (P1 K)) ⊆
            (reductionBadSet aux S badValues)ᶜ →
          IsEtale (aux ∣_ (F.map φ).toBelyiMap.belyiOpen)) :
    ∃ φ : Φ, ∃ R : P1ReductionStep K C F.hmarkedOpen S T,
      R.p1Map = F.map φ ∧
        R.composed.hom = aux ≫ (F.map φ).hom ∧
          ((∀ x ∈ S, R.composed.hom.base x ∈ markedSchemePointSet K) ∧
            ∀ x ∈ T, R.composed.hom.base x ∉ markedSchemePointSet K) := by
  rcases exists_p1Map_for_reductionBadSet_target_with_belyiOpen_subset_compl
      F aux hS hbad himage htargetBad with
    ⟨φ, hφbad, hφtarget, hφOpen⟩
  let R : P1ReductionStep K C F.hmarkedOpen S T :=
    ofBadValuesComposedAuxEtale (K := K) (C := C) (hmarkedOpen := F.hmarkedOpen)
      (S := S) (T := T) hS badValues hbad aux (F.map φ)
      (hAuxEtale φ hφOpen) hφbad targetPoint maps_T_to_target hφtarget
  refine ⟨φ, R, rfl, ?_, ?_⟩
  · exact ofBadValuesComposedAuxEtale_composed_hom
      (K := K) (C := C) (hmarkedOpen := F.hmarkedOpen) (S := S) (T := T)
      hS badValues hbad aux (F.map φ) (hAuxEtale φ hφOpen)
      hφbad targetPoint maps_T_to_target hφtarget
  · constructor
    · intro x hx
      rw [R.composed_base_eq x]
      exact R.p1Map_maps_bad_to_marked (R.aux.base x) (R.maps_S_to_bad x hx)
    · intro x hx
      rw [R.composed_base_eq x, R.maps_T_to_target x hx]
      exact R.p1Map_target_avoids_marked

/-- Map-level corollary of `exists_of_p1MapExistence_auxEtale`: the reduction
data produces an actual composed finite Belyi map on `C` with the prescribed
branch and noncritical controls. -/
theorem exists_composedMap_of_p1MapExistence_auxEtale
    {Φ : Type z}
    (F : FiniteMarkedBelyiExistence K Φ (P1 K))
    (hS : S.Finite)
    (badValues : Set (P1 K)) (hbad : badValues.Finite)
    (aux : C ⟶ P1 K) [IsFinite aux] [IsDominant aux]
    {targetPoint : P1 K}
    (himage : ∀ x ∈ S, aux.base x ≠ targetPoint)
    (htargetBad : targetPoint ∉ badValues)
    (maps_T_to_target : ∀ x ∈ T, aux.base x = targetPoint)
    (hAuxEtale :
      ∀ φ : Φ,
        ((F.map φ).toBelyiMap.belyiOpen : Set (P1 K)) ⊆
            (reductionBadSet aux S badValues)ᶜ →
          IsEtale (aux ∣_ (F.map φ).toBelyiMap.belyiOpen)) :
    ∃ φ : Φ,
      ∃ composed : FiniteBelyiMap (markedBelyiTarget K F.hmarkedOpen) C,
        composed.hom = aux ≫ (F.map φ).hom ∧
          ((∀ x ∈ S, composed.hom.base x ∈ markedSchemePointSet K) ∧
            ∀ x ∈ T, composed.hom.base x ∉ markedSchemePointSet K) := by
  rcases exists_of_p1MapExistence_auxEtale F hS badValues hbad aux
      himage htargetBad maps_T_to_target hAuxEtale with
    ⟨φ, R, _hR, hhom, hcontrols⟩
  exact ⟨φ, R.composed, hhom, hcontrols⟩

/-- Fixed-pair auxiliary source material produces a reduction step after
selecting a suitable finite marked Belyi map on `P1`. -/
theorem exists_of_auxiliaryData
    {Φ : Type z}
    (F : FiniteMarkedBelyiExistence K Φ (P1 K))
    (hS : S.Finite)
    (D : P1ReductionAuxiliaryData K C F S T) :
    ∃ φ : Φ, ∃ R : P1ReductionStep K C F.hmarkedOpen S T,
      R.p1Map = F.map φ ∧
        R.composed.hom = D.aux ≫ (F.map φ).hom ∧
          ((∀ x ∈ S, R.composed.hom.base x ∈ markedSchemePointSet K) ∧
            ∀ x ∈ T, R.composed.hom.base x ∉ markedSchemePointSet K) := by
  letI : IsFinite D.aux := D.aux_finite
  letI : IsDominant D.aux := D.aux_dominant
  exact exists_of_p1MapExistence_auxEtale
    (K := K) (C := C) (S := S) (T := T) F hS
    D.badValues D.badValues_finite D.aux
    (targetPoint := D.targetPoint)
    D.image_avoids_target D.target_not_bad D.maps_T_to_target
    D.aux_etale_on_selected_belyiOpen

/-- Map-level version of `exists_of_auxiliaryData`: fixed-pair auxiliary source
material produces the composed finite Belyi map and the prescribed controls. -/
theorem exists_composedMap_of_auxiliaryData
    {Φ : Type z}
    (F : FiniteMarkedBelyiExistence K Φ (P1 K))
    (hS : S.Finite)
    (D : P1ReductionAuxiliaryData K C F S T) :
    ∃ φ : Φ,
      ∃ composed : FiniteBelyiMap (markedBelyiTarget K F.hmarkedOpen) C,
        composed.hom = D.aux ≫ (F.map φ).hom ∧
          ((∀ x ∈ S, composed.hom.base x ∈ markedSchemePointSet K) ∧
            ∀ x ∈ T, composed.hom.base x ∉ markedSchemePointSet K) := by
  letI : IsFinite D.aux := D.aux_finite
  letI : IsDominant D.aux := D.aux_dominant
  exact exists_composedMap_of_p1MapExistence_auxEtale
    (K := K) (C := C) (S := S) (T := T) F hS
    D.badValues D.badValues_finite D.aux
    (targetPoint := D.targetPoint)
    D.image_avoids_target D.target_not_bad D.maps_T_to_target
    D.aux_etale_on_selected_belyiOpen

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

/-- The composed Belyi open contains the prescribed noncritical set `T`. -/
theorem T_subset_composed_belyiOpen :
    T ⊆ (R.composed.toBelyiMap.belyiOpen : Set C) := by
  intro x hx
  exact
    (SchemeBelyi.FiniteBelyiMap.mem_marked_belyiOpen_iff
      (K := K) (hmarkedOpen := hmarkedOpen) R.composed x).2
      (R.composed_avoids_T_marked x hx)

/-- The composed Belyi open avoids the prescribed branch-forcing set `S`. -/
theorem composed_belyiOpen_subset_compl_S :
    (R.composed.toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  intro x hxOpen hxS
  have hxNotMarked :
      R.composed.hom.base x ∉ markedSchemePointSet K :=
    (SchemeBelyi.FiniteBelyiMap.mem_marked_belyiOpen_iff
      (K := K) (hmarkedOpen := hmarkedOpen) R.composed x).1 hxOpen
  exact hxNotMarked (R.composed_maps_S_to_marked x hxS)

/-- Open-set form of the one-step reduction controls: the composed Belyi open
contains `T` and is contained in the complement of `S`. -/
theorem composed_belyiOpen_controls :
    T ⊆ (R.composed.toBelyiMap.belyiOpen : Set C) ∧
      (R.composed.toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ :=
  ⟨R.T_subset_composed_belyiOpen, R.composed_belyiOpen_subset_compl_S⟩

/-- Open-control version of `exists_of_p1MapExistence_auxEtale`: finite marked
Belyi existence on `P1` and an auxiliary-étaleness criterion produce a
composed finite Belyi map whose Belyi open contains `T` and avoids `S`. -/
theorem exists_composedMap_belyiOpen_controls_of_p1MapExistence_auxEtale
    {Φ : Type z}
    (F : FiniteMarkedBelyiExistence K Φ (P1 K))
    (hS : S.Finite)
    (badValues : Set (P1 K)) (hbad : badValues.Finite)
    (aux : C ⟶ P1 K) [IsFinite aux] [IsDominant aux]
    {targetPoint : P1 K}
    (himage : ∀ x ∈ S, aux.base x ≠ targetPoint)
    (htargetBad : targetPoint ∉ badValues)
    (maps_T_to_target : ∀ x ∈ T, aux.base x = targetPoint)
    (hAuxEtale :
      ∀ φ : Φ,
        ((F.map φ).toBelyiMap.belyiOpen : Set (P1 K)) ⊆
            (reductionBadSet aux S badValues)ᶜ →
          IsEtale (aux ∣_ (F.map φ).toBelyiMap.belyiOpen)) :
    ∃ φ : Φ,
      ∃ composed : FiniteBelyiMap (markedBelyiTarget K F.hmarkedOpen) C,
        composed.hom = aux ≫ (F.map φ).hom ∧
          T ⊆ (composed.toBelyiMap.belyiOpen : Set C) ∧
            (composed.toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  rcases exists_of_p1MapExistence_auxEtale F hS badValues hbad aux
      himage htargetBad maps_T_to_target hAuxEtale with
    ⟨φ, R, _hR, hhom, _hcontrols⟩
  exact
    ⟨φ, R.composed, hhom,
      R.T_subset_composed_belyiOpen,
      R.composed_belyiOpen_subset_compl_S⟩

/-- Combined map-level and open-control version of the one-step reduction:
the selected composed finite Belyi map has the prescribed marked controls and
its Belyi open contains `T` while avoiding `S`. -/
theorem exists_composedMap_controls_and_belyiOpen_controls_of_p1MapExistence_auxEtale
    {Φ : Type z}
    (F : FiniteMarkedBelyiExistence K Φ (P1 K))
    (hS : S.Finite)
    (badValues : Set (P1 K)) (hbad : badValues.Finite)
    (aux : C ⟶ P1 K) [IsFinite aux] [IsDominant aux]
    {targetPoint : P1 K}
    (himage : ∀ x ∈ S, aux.base x ≠ targetPoint)
    (htargetBad : targetPoint ∉ badValues)
    (maps_T_to_target : ∀ x ∈ T, aux.base x = targetPoint)
    (hAuxEtale :
      ∀ φ : Φ,
        ((F.map φ).toBelyiMap.belyiOpen : Set (P1 K)) ⊆
            (reductionBadSet aux S badValues)ᶜ →
          IsEtale (aux ∣_ (F.map φ).toBelyiMap.belyiOpen)) :
    ∃ φ : Φ,
      ∃ composed : FiniteBelyiMap (markedBelyiTarget K F.hmarkedOpen) C,
        composed.hom = aux ≫ (F.map φ).hom ∧
          ((∀ x ∈ S, composed.hom.base x ∈ markedSchemePointSet K) ∧
            ∀ x ∈ T, composed.hom.base x ∉ markedSchemePointSet K) ∧
            T ⊆ (composed.toBelyiMap.belyiOpen : Set C) ∧
              (composed.toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  rcases exists_of_p1MapExistence_auxEtale F hS badValues hbad aux
      himage htargetBad maps_T_to_target hAuxEtale with
    ⟨φ, R, _hR, hhom, hcontrols⟩
  exact
    ⟨φ, R.composed, hhom, hcontrols,
      R.T_subset_composed_belyiOpen,
      R.composed_belyiOpen_subset_compl_S⟩

/-- Open-control version of `exists_composedMap_of_auxiliaryData`: fixed-pair
auxiliary source material directly produces a composed finite Belyi map whose
Belyi open contains `T` and avoids `S`. -/
theorem exists_composedMap_belyiOpen_controls_of_auxiliaryData
    {Φ : Type z}
    (F : FiniteMarkedBelyiExistence K Φ (P1 K))
    (hS : S.Finite)
    (D : P1ReductionAuxiliaryData K C F S T) :
    ∃ φ : Φ,
      ∃ composed : FiniteBelyiMap (markedBelyiTarget K F.hmarkedOpen) C,
        composed.hom = D.aux ≫ (F.map φ).hom ∧
          T ⊆ (composed.toBelyiMap.belyiOpen : Set C) ∧
            (composed.toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  letI : IsFinite D.aux := D.aux_finite
  letI : IsDominant D.aux := D.aux_dominant
  exact exists_composedMap_belyiOpen_controls_of_p1MapExistence_auxEtale
    (K := K) (C := C) (S := S) (T := T) F hS
    D.badValues D.badValues_finite D.aux
    (targetPoint := D.targetPoint)
    D.image_avoids_target D.target_not_bad D.maps_T_to_target
    D.aux_etale_on_selected_belyiOpen

/-- Combined map-level and open-control version of `exists_of_auxiliaryData`:
fixed-pair auxiliary source material directly produces a composed finite Belyi
map with both marked controls and Belyi-open controls. -/
theorem exists_composedMap_controls_and_belyiOpen_controls_of_auxiliaryData
    {Φ : Type z}
    (F : FiniteMarkedBelyiExistence K Φ (P1 K))
    (hS : S.Finite)
    (D : P1ReductionAuxiliaryData K C F S T) :
    ∃ φ : Φ,
      ∃ composed : FiniteBelyiMap (markedBelyiTarget K F.hmarkedOpen) C,
        composed.hom = D.aux ≫ (F.map φ).hom ∧
          ((∀ x ∈ S, composed.hom.base x ∈ markedSchemePointSet K) ∧
            ∀ x ∈ T, composed.hom.base x ∉ markedSchemePointSet K) ∧
            T ⊆ (composed.toBelyiMap.belyiOpen : Set C) ∧
              (composed.toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  letI : IsFinite D.aux := D.aux_finite
  letI : IsDominant D.aux := D.aux_dominant
  exact exists_composedMap_controls_and_belyiOpen_controls_of_p1MapExistence_auxEtale
    (K := K) (C := C) (S := S) (T := T) F hS
    D.badValues D.badValues_finite D.aux
    (targetPoint := D.targetPoint)
    D.image_avoids_target D.target_not_bad D.maps_T_to_target
    D.aux_etale_on_selected_belyiOpen

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

/-- Per-pair auxiliary source material assembles into a global reduction family,
which is the reduction-level input needed by the finite marked Belyi interface. -/
theorem exists_of_auxiliaryData
    {Φ : Type z}
    (F : FiniteMarkedBelyiExistence K Φ (P1 K))
    (data :
      ∀ {S T : Set C}, S.Finite → T.Finite → Disjoint S T →
        P1ReductionAuxiliaryData K C F S T) :
    ∃ E : P1ReductionExistence K C,
      E.hmarkedOpen = F.hmarkedOpen := by
  classical
  refine
    ⟨{ hmarkedOpen := F.hmarkedOpen
       step := ?_ },
      rfl⟩
  intro S T hS hT hdis
  let D := data (S := S) (T := T) hS hT hdis
  let hex := P1ReductionStep.exists_of_auxiliaryData
    (K := K) (C := C) (S := S) (T := T) F hS D
  exact Classical.choose (Classical.choose_spec hex)

/-- Version of `exists_of_auxiliaryData` where the per-pair source material is
available as nonempty data packages.  This is the form produced by the
divisor/cohomology source layer before making choices. -/
theorem exists_of_auxiliaryData_nonempty
    {Φ : Type z}
    (F : FiniteMarkedBelyiExistence K Φ (P1 K))
    (data :
      ∀ {S T : Set C}, S.Finite → T.Finite → Disjoint S T →
        Nonempty (P1ReductionAuxiliaryData K C F S T)) :
    ∃ E : P1ReductionExistence K C,
      E.hmarkedOpen = F.hmarkedOpen := by
  classical
  exact exists_of_auxiliaryData F
    (fun {S T} hS hT hdis =>
      Classical.choice (data (S := S) (T := T) hS hT hdis))

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

theorem toFiniteMarkedBelyiExistence_finite_hom
    (i : ReductionIndex C) :
    IsFinite (E.toFiniteMarkedBelyiExistence.map i).hom :=
  SchemeMarkedBelyi.FiniteMarkedBelyiExistence.finite_hom
    K (ReductionIndex C) E.toFiniteMarkedBelyiExistence i

theorem map_finite_hom
    (i : ReductionIndex C) :
    IsFinite (E.map i).hom := by
  rw [← E.toFiniteMarkedBelyiExistence_map_apply i]
  exact E.toFiniteMarkedBelyiExistence_finite_hom i

theorem toFiniteMarkedBelyiExistence_mem_belyiOpen_iff
    (i : ReductionIndex C) (x : C) :
    x ∈ (FiniteMarkedBelyiExistence.toMarkedCoverData K
      (ReductionIndex C) E.toFiniteMarkedBelyiExistence).belyiOpen i ↔
        (E.map i).hom.base x ∉ markedSchemePointSet K := by
  exact
    SchemeMarkedBelyi.FiniteMarkedBelyiExistence.mem_belyiOpen_iff
      K (ReductionIndex C) E.toFiniteMarkedBelyiExistence i x

theorem toFiniteMarkedBelyiExistence_belyiOpen_carrier
    (i : ReductionIndex C) :
    (FiniteMarkedBelyiExistence.toMarkedCoverData K
      (ReductionIndex C) E.toFiniteMarkedBelyiExistence).belyiOpen i =
        {x : C | (E.map i).hom.base x ∉ markedSchemePointSet K} := by
  exact
    SchemeMarkedBelyi.FiniteMarkedBelyiExistence.belyiOpen_carrier
      K (ReductionIndex C) E.toFiniteMarkedBelyiExistence i

theorem toFiniteMarkedBelyiExistence_belyiOpen_eq_schemeBelyi
    (i : ReductionIndex C) :
    (FiniteMarkedBelyiExistence.toMarkedCoverData K
      (ReductionIndex C) E.toFiniteMarkedBelyiExistence).belyiOpen i =
        ((E.map i).toBelyiMap.belyiOpen : Set C) := by
  exact
    SchemeMarkedBelyi.FiniteMarkedBelyiExistence.belyiOpen_eq_schemeBelyi
      K (ReductionIndex C) E.toFiniteMarkedBelyiExistence i

theorem toFiniteMarkedBelyiExistence_toNoncritical_belyiOpen_eq_schemeBelyi
    (i : ReductionIndex C) :
    (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
      (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i =
        ((E.map i).toBelyiMap.belyiOpen : Set C) := by
  exact
    SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence_belyiOpen_eq_schemeBelyi
      K (ReductionIndex C) E.toFiniteMarkedBelyiExistence i

/-- Direct finite disjoint-set conclusion from a reduction family. -/
theorem exists_for_finite_disjoint
    {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ i : ReductionIndex C,
      (∀ x ∈ S, (E.map i).hom.base x ∈ markedSchemePointSet K) ∧
        ∀ x ∈ T, (E.map i).hom.base x ∉ markedSchemePointSet K := by
  exact E.toFiniteMarkedBelyiExistence.exists_for_finite_disjoint hS hT hdis

/-- Direct scheme-Belyi-open form of the finite disjoint-set conclusion for a
global `P1`-reduction family. -/
theorem exists_map_belyiOpen_controls
    {S T : Set C} (hS : S.Finite) (hT : T.Finite) (hdis : Disjoint S T) :
    ∃ i : ReductionIndex C, T ⊆ ((E.map i).toBelyiMap.belyiOpen : Set C) ∧
      ((E.map i).toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  rcases
      FiniteMarkedBelyiExistence.exists_map_belyiOpen_controls
        (K := K) (Φ := ReductionIndex C) E.toFiniteMarkedBelyiExistence
        hS hT hdis with
    ⟨i, hTopen, hopenS⟩
  exact
    ⟨i,
      (by simpa [toFiniteMarkedBelyiExistence_map_apply] using hTopen),
      (by simpa [toFiniteMarkedBelyiExistence_map_apply] using hopenS)⟩

/-- Actual finite-map one-point Belyi-open consequence from a reduction
family. -/
theorem exists_map_belyiOpen_inside_complement
    {A : Set C} (hA : A.Finite) {x : C} (hxA : x ∉ A) :
    ∃ i : ReductionIndex C,
      IsOpen ((E.map i).toBelyiMap.belyiOpen : Set C) ∧
        x ∈ ((E.map i).toBelyiMap.belyiOpen : Set C) ∧
          ((E.map i).toBelyiMap.belyiOpen : Set C) ⊆ Aᶜ := by
  rcases
      FiniteMarkedBelyiExistence.exists_map_belyiOpen_inside_complement
        K (ReductionIndex C) E.toFiniteMarkedBelyiExistence hA hxA with
    ⟨i, hopen, hxopen, hsub⟩
  exact
    ⟨i,
      (by simpa [toFiniteMarkedBelyiExistence_map_apply] using hopen),
      (by simpa [toFiniteMarkedBelyiExistence_map_apply] using hxopen),
      (by simpa [toFiniteMarkedBelyiExistence_map_apply] using hsub)⟩

/-- Actual finite-map finite-set Belyi-open consequence from a reduction
family. -/
theorem exists_map_belyiOpen_containing_finite_inside_complement
    {S T : Set C} (hS : S.Finite) (hT : T.Finite) (hdis : Disjoint S T) :
    ∃ i : ReductionIndex C,
      IsOpen ((E.map i).toBelyiMap.belyiOpen : Set C) ∧
        T ⊆ ((E.map i).toBelyiMap.belyiOpen : Set C) ∧
          ((E.map i).toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  rcases
      FiniteMarkedBelyiExistence.exists_map_belyiOpen_containing_finite_inside_complement
        K (ReductionIndex C) E.toFiniteMarkedBelyiExistence hS hT hdis with
    ⟨i, hopen, hTopen, hsub⟩
  exact
    ⟨i,
      (by simpa [toFiniteMarkedBelyiExistence_map_apply] using hopen),
      (by simpa [toFiniteMarkedBelyiExistence_map_apply] using hTopen),
      (by simpa [toFiniteMarkedBelyiExistence_map_apply] using hsub)⟩

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

/-- Concrete coordinate-avoidance form of the finite tuple-subcover consequence
directly from a reduction family. -/
theorem finite_subcover_on_complement_forall_avoidance
    (κ : Type z) [Finite κ] [T1Space (P1 K)]
    {S : Set C} (hS : S.Finite) [CompactSpace (κ → {x : C // x ∉ S})] :
    ∃ t : Finset {i : ReductionIndex C //
        (FiniteMarkedBelyiExistence.toMarkedCoverData K
          (ReductionIndex C) E.toFiniteMarkedBelyiExistence).sendsSetToBranch S i},
      ∀ x : κ → {x : C // x ∉ S},
        ∃ i ∈ t, ∀ j, (E.map i.1).hom.base (x j).1 ∉ markedSchemePointSet K := by
  exact FiniteMarkedBelyiExistence.finite_subcover_on_complement_forall_avoidance
    K (ReductionIndex C) E.toFiniteMarkedBelyiExistence κ hS

/-- Compact-exhaustion cover bridge directly from a reduction family. -/
theorem finite_compact_cover_by_belyiOpen_exhaustions
    [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    (Kex : ∀ i : ReductionIndex C,
      CompactExhaustion ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
        (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i)) :
    ∃ t : Finset (ReductionIndex C × ℕ),
      (∀ p ∈ t,
        IsCompact ((Subtype.val :
          (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
            (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 →
            C) ''
            (Kex p.1 p.2))) ∧
        (∀ p ∈ t,
          ((Subtype.val :
            (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
              (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 →
              C) ''
              (Kex p.1 p.2)) ⊆
                (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
                  (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1) ∧
          (Set.univ : Set C) ⊆
            ⋃ p ∈ t,
              (Subtype.val :
                (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
                  (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 →
                  C) ''
                (Kex p.1 p.2) := by
  exact
    FiniteMarkedBelyiExistence.finite_compact_cover_by_belyiOpen_exhaustions
      K (ReductionIndex C) E.toFiniteMarkedBelyiExistence Kex

/-- Equality form of the compact-exhaustion cover bridge directly from a
reduction family. -/
theorem finite_compact_cover_by_belyiOpen_exhaustions_eq_univ
    [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    (Kex : ∀ i : ReductionIndex C,
      CompactExhaustion ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
        (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i)) :
    ∃ t : Finset (ReductionIndex C × ℕ),
      (∀ p ∈ t,
        IsCompact ((Subtype.val :
          (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
            (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 →
            C) ''
            (Kex p.1 p.2))) ∧
        (∀ p ∈ t,
          ((Subtype.val :
            (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
              (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 →
              C) ''
              (Kex p.1 p.2)) ⊆
                (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
                  (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1) ∧
          (⋃ p ∈ t,
            (Subtype.val :
              (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
                (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 →
                C) ''
              (Kex p.1 p.2)) = (Set.univ : Set C) := by
  exact
    FiniteMarkedBelyiExistence.finite_compact_cover_by_belyiOpen_exhaustions_eq_univ
      K (ReductionIndex C) E.toFiniteMarkedBelyiExistence Kex

/-- Compact-cover bridge directly from a reduction family, with compact
exhaustions supplied by local compactness and second countability. -/
theorem finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact
    [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    [LocallyCompactSpace C] [SecondCountableTopology C] :
    ∃ Kex : ∀ i : ReductionIndex C,
      CompactExhaustion ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
        (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i),
      ∃ t : Finset (ReductionIndex C × ℕ),
        (∀ p ∈ t,
          IsCompact ((Subtype.val :
            (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
              (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 →
              C) ''
              (Kex p.1 p.2))) ∧
          (∀ p ∈ t,
            ((Subtype.val :
              (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
                (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 →
                C) ''
                (Kex p.1 p.2)) ⊆
                  (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
                    (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1) ∧
            (Set.univ : Set C) ⊆
              ⋃ p ∈ t,
                (Subtype.val :
                  (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
                    (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 →
                    C) ''
                  (Kex p.1 p.2) := by
  exact
    FiniteMarkedBelyiExistence.finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact
      K (ReductionIndex C) E.toFiniteMarkedBelyiExistence

/-- Equality form of the compact-cover bridge directly from a reduction family,
with compact exhaustions supplied by local compactness and second countability. -/
theorem finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact_eq_univ
    [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    [LocallyCompactSpace C] [SecondCountableTopology C] :
    ∃ Kex : ∀ i : ReductionIndex C,
      CompactExhaustion ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
        (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i),
      ∃ t : Finset (ReductionIndex C × ℕ),
        (∀ p ∈ t,
          IsCompact ((Subtype.val :
            (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
              (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 →
              C) ''
              (Kex p.1 p.2))) ∧
          (∀ p ∈ t,
            ((Subtype.val :
              (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
                (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 →
                C) ''
                (Kex p.1 p.2)) ⊆
                  (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
                    (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1) ∧
            (⋃ p ∈ t,
              (Subtype.val :
                (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
                  (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 →
                  C) ''
                (Kex p.1 p.2)) = (Set.univ : Set C) := by
  exact
    FiniteMarkedBelyiExistence.finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact_eq_univ
      K (ReductionIndex C) E.toFiniteMarkedBelyiExistence

/-- Compact-coordinate Corollary 3.2 bridge directly from a reduction family. -/
theorem finite_compact_coordinate_sets_of_belyiOpen_exhaustions
    [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    [LocallyCompactSpace C] [SecondCountableTopology C]
    {κ : Type z} {Z : κ → Type*} [∀ j, TopologicalSpace (Z j)]
    (G : ReductionIndex C → C → ((j : κ) → Z j))
    (hG : ∀ i, Continuous (G i))
    (A : (j : κ) → Set (Z j))
    (hGA : ∀ i x,
      x ∈ (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
        (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i →
        ∀ j, G i x j ∈ A j) :
    ∃ Kex : ∀ i : ReductionIndex C,
      CompactExhaustion ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
        (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i),
      ∃ t : Finset (ReductionIndex C × ℕ),
        ∃ H : (j : κ) → Set (Z j),
          (∀ j, IsCompact (H j)) ∧
            (∀ j, H j ⊆ A j) ∧
              (Set.univ : Set C) ⊆
                ⋃ p ∈ t,
                  (Subtype.val :
                    (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
                      (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 →
                      C) ''
                    (Kex p.1 p.2) ∧
                ∀ p ∈ t, ∀ x,
                  x ∈ (Subtype.val :
                    (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
                      (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 →
                      C) ''
                      (Kex p.1 p.2) →
                    ∀ j, G p.1 x j ∈ H j := by
  exact
    FiniteMarkedBelyiExistence.finite_compact_coordinate_sets_of_belyiOpen_exhaustions
      K (ReductionIndex C) E.toFiniteMarkedBelyiExistence G hG A hGA

end P1ReductionExistence

end BelyiReduction
end SourceStack
end HilbertTest
