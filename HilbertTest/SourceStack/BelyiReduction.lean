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

open AlgebraicGeometry

namespace HilbertTest
namespace SourceStack
namespace BelyiReduction

open SchemeBelyi
open SchemeMarkedBelyi
open SchemeProjectiveLine

universe u

variable {K : Type u} [Field K]
variable {C : Scheme.{u}}
variable {hmarkedOpen : IsOpen (markedSchemePointSet K)ᶜ}

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

end P1ReductionExistence

end BelyiReduction
end SourceStack
end HilbertTest
