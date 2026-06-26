import HilbertTest.SourceStack.MarkedProjectiveLine
import HilbertTest.SourceStack.SchemeCurveBelyiConstruction
import Mathlib.AlgebraicGeometry.Gluing

/-!
Projective-section source layer for the curve step in Theorem 2.5.

Mochizuki's proof chooses a divisor `D` supported on `T`, the section `s0`
with zero divisor `D`, and a section `s1` nonzero on `T`.  The first checked
fact here is the elementary basepoint-free consequence: if `s0` vanishes
exactly on `T` and `s1` is nonzero on `T`, then `s0` and `s1` have no common
zero.  The rest of the file packages the still-missing Stacks/Vakil
line-bundle construction of the associated map to `P1` as a narrow interface
that feeds into the existing finite marked Belyi machinery.
-/

noncomputable section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

namespace HilbertTest
namespace SourceStack
namespace ProjectiveSectionMaps

open CurveRiemannRoch
open MarkedProjectiveLine
open SchemeCurveBelyiConstruction
open SchemeProjectiveLine

universe u v w

variable {K : Type u} [Field K]
variable {X : Type v}
variable {V : Type w} [AddCommGroup V] [Module K V]

/-- Two sections have no common basepoint if at every point at least one
evaluation is nonzero. -/
def HasNoCommonZero
    (D : RRSectionEvaluationData K X V) (s0 s1 : V) : Prop :=
  ∀ x : X, D.eval x s0 ≠ 0 ∨ D.eval x s1 ≠ 0

/-- A section has a prescribed zero set. -/
def HasZeroSet
    (D : RRSectionEvaluationData K X V) (s : V) (T : Set X) : Prop :=
  ∀ x : X, D.eval x s = 0 ↔ x ∈ T

/-- If `s0` vanishes exactly on `T` and `s1` is nonzero on `T`, then the pair
`(s0, s1)` has no common zero. -/
theorem hasNoCommonZero_of_hasZeroSet_nonzeroOnSet
    (D : RRSectionEvaluationData K X V) (s0 s1 : V) (T : Set X)
    (hzero : HasZeroSet D s0 T)
    (hnonzero : D.nonzeroOnSet T s1) :
    HasNoCommonZero D s0 s1 := by
  intro x
  by_cases hx : x ∈ T
  · exact Or.inr (hnonzero x hx)
  · exact Or.inl (by
      intro hs0
      exact hx ((hzero x).1 hs0))

/-- A projective line morphism determined by two sections, as supplied by the
future line-bundle/global-section construction.  The fields record only the
pointwise properties used by the Belyi reduction. -/
structure ProjectiveLineSectionPair
    (K : Type u) [Field K] (C : Scheme.{u})
    (V : Type w) [AddCommGroup V] [Module K V] where
  evalData : RRSectionEvaluationData K C V
  section0 : V
  section1 : V
  no_common_zero : HasNoCommonZero evalData section0 section1
  hom : C ⟶ P1 K
  zero_of_section0_vanishes :
    ∀ x : C, evalData.eval x section0 = 0 →
      hom.base x = schemeCarrierPoint K MarkedPointLabel.zero
  section0_vanishes_of_zero :
    ∀ x : C, hom.base x = schemeCarrierPoint K MarkedPointLabel.zero →
      evalData.eval x section0 = 0

namespace ProjectiveLineSectionPair

variable {C : Scheme.{u}}
variable (P : ProjectiveLineSectionPair K C V)

/-- Points where the first section vanishes map to the checked marked branch
triple. -/
theorem maps_section0_zero_to_marked
    {x : C} (hx : P.evalData.eval x P.section0 = 0) :
    P.hom.base x ∈ markedSchemePointSet K := by
  rw [P.zero_of_section0_vanishes x hx]
  exact schemeCarrierPoint_mem_markedSchemePointSet K MarkedPointLabel.zero

/-- A prescribed zero set for the first section maps into the marked branch
triple. -/
theorem maps_zeroSet_to_marked
    {T : Set C} (hzero : HasZeroSet P.evalData P.section0 T) :
    ∀ x ∈ T, P.hom.base x ∈ markedSchemePointSet K := by
  intro x hx
  exact P.maps_section0_zero_to_marked ((hzero x).2 hx)

/-- Away from the zero locus of the first section, the associated point is not
the marked zero point. -/
theorem avoids_zeroPoint_of_section0_nonzero
    {x : C} (hx : P.evalData.eval x P.section0 ≠ 0) :
    P.hom.base x ≠ schemeCarrierPoint K MarkedPointLabel.zero := by
  intro hzero
  exact hx (P.section0_vanishes_of_zero x hzero)

end ProjectiveLineSectionPair

/-- Local chart data for constructing the projective-line morphism attached to
two sections.  This is the checked scheme-gluing bridge: the global morphism
`C ⟶ P1 K` is no longer a primitive field, but is obtained from compatible
local morphisms on an open cover.  The remaining source-material obligation is
to construct the local chart maps themselves from trivializations of the line
bundle. -/
structure GluedProjectiveLineSectionData
    (K : Type u) [Field K] (C : Scheme.{u})
    (V : Type w) [AddCommGroup V] [Module K V] where
  evalData : RRSectionEvaluationData K C V
  section0 : V
  section1 : V
  no_common_zero : HasNoCommonZero evalData section0 section1
  cover : C.OpenCover
  localHom : ∀ i : cover.J, cover.obj i ⟶ P1 K
  local_compat :
    ∀ i j : cover.J,
      pullback.fst (cover.map i) (cover.map j) ≫ localHom i =
        pullback.snd (cover.map i) (cover.map j) ≫ localHom j
  local_zero_of_section0_vanishes :
    ∀ i (x : cover.obj i),
      evalData.eval ((cover.map i).base x) section0 = 0 →
        (localHom i).base x = schemeCarrierPoint K MarkedPointLabel.zero
  local_section0_vanishes_of_zero :
    ∀ i (x : cover.obj i),
      (localHom i).base x = schemeCarrierPoint K MarkedPointLabel.zero →
        evalData.eval ((cover.map i).base x) section0 = 0

namespace GluedProjectiveLineSectionData

variable {C : Scheme.{u}}
variable (D : GluedProjectiveLineSectionData K C V)

/-- The projective-line morphism obtained by gluing compatible local chart
morphisms. -/
def globalHom : C ⟶ P1 K :=
  D.cover.glueMorphisms D.localHom D.local_compat

@[reassoc]
theorem cover_map_globalHom (i : D.cover.J) :
    D.cover.map i ≫ D.globalHom = D.localHom i := by
  exact D.cover.ι_glueMorphisms D.localHom D.local_compat i

/-- On each member of the cover, the glued morphism has the prescribed local
description. -/
theorem globalHom_base_of_cover (i : D.cover.J) (x : D.cover.obj i) :
    D.globalHom.base ((D.cover.map i).base x) = (D.localHom i).base x := by
  change ((D.cover.map i ≫ D.globalHom).base x) = (D.localHom i).base x
  rw [D.cover_map_globalHom i]

/-- If the first section vanishes at a point, the glued map sends that point to
the checked scheme point `0 ∈ P1`. -/
theorem global_zero_of_section0_vanishes
    (x : C) (hx : D.evalData.eval x D.section0 = 0) :
    D.globalHom.base x = schemeCarrierPoint K MarkedPointLabel.zero := by
  classical
  rcases D.cover.covers x with ⟨y, hy⟩
  calc
    D.globalHom.base x =
        D.globalHom.base ((D.cover.map (D.cover.f x)).base y) := by
          rw [hy]
    _ = (D.localHom (D.cover.f x)).base y := D.globalHom_base_of_cover (D.cover.f x) y
    _ = schemeCarrierPoint K MarkedPointLabel.zero :=
        D.local_zero_of_section0_vanishes (D.cover.f x) y (by simpa [hy] using hx)

/-- Conversely, if the glued map sends a point to `0 ∈ P1`, the first section
vanishes there. -/
theorem section0_vanishes_of_global_zero
    (x : C)
    (hx : D.globalHom.base x = schemeCarrierPoint K MarkedPointLabel.zero) :
    D.evalData.eval x D.section0 = 0 := by
  classical
  rcases D.cover.covers x with ⟨y, hy⟩
  have hlocal :
      (D.localHom (D.cover.f x)).base y =
        schemeCarrierPoint K MarkedPointLabel.zero := by
    rw [← D.globalHom_base_of_cover (D.cover.f x) y]
    simpa [hy] using hx
  have hv :=
    D.local_section0_vanishes_of_zero (D.cover.f x) y hlocal
  simpa [hy] using hv

/-- The glued local chart data supplies the narrower projective-section pair
interface used by the existing finite marked Belyi bridge. -/
def toProjectiveLineSectionPair : ProjectiveLineSectionPair K C V where
  evalData := D.evalData
  section0 := D.section0
  section1 := D.section1
  no_common_zero := D.no_common_zero
  hom := D.globalHom
  zero_of_section0_vanishes := D.global_zero_of_section0_vanishes
  section0_vanishes_of_zero := D.section0_vanishes_of_global_zero

theorem toProjectiveLineSectionPair_hom :
    D.toProjectiveLineSectionPair.hom = D.globalHom := rfl

theorem toProjectiveLineSectionPair_maps_section0_zero_to_marked
    {x : C} (hx : D.evalData.eval x D.section0 = 0) :
    D.toProjectiveLineSectionPair.hom.base x ∈ markedSchemePointSet K := by
  exact D.toProjectiveLineSectionPair.maps_section0_zero_to_marked hx

end GluedProjectiveLineSectionData

/-- Finite marked Belyi maps obtained from projective-section pairs.  The
fields split the proof passage into: section evaluations, the projective
section map, the finite marked Belyi refinement, and the remaining branch
avoidance supplied by the Belyi polynomial reduction. -/
structure ProjectiveSectionFiniteMarkedFamily
    (K : Type u) [Field K] (C : Scheme.{u})
    (V : Type w) [AddCommGroup V] [Module K V] where
  evalPackage : RiemannRochFiniteEvaluationPackage K C V
  hmarkedOpen : IsOpen (markedSchemePointSet K)ᶜ
  pair : V → ProjectiveLineSectionPair K C V
  map : V → SchemeBelyi.FiniteBelyiMap
    (SchemeBelyi.markedBelyiTarget K hmarkedOpen) C
  map_base_eq_pair : ∀ s x, (map s).hom.base x = (pair s).hom.base x
  pair_section0_eval_eq_index :
    ∀ s x, (pair s).evalData.eval x (pair s).section0 = evalPackage.eval x s
  nonzero_avoids_marked :
    ∀ {T : Set C} {s : V},
      evalPackage.toEvaluationData.nonzeroOnSet T s →
        ∀ x ∈ T, (map s).hom.base x ∉ markedSchemePointSet K

namespace ProjectiveSectionFiniteMarkedFamily

variable {C : Scheme.{u}}
variable (F : ProjectiveSectionFiniteMarkedFamily K C V)

/-- The projective-section finite marked family is a section-controlled finite
marked Belyi family. -/
def toSectionControlledFiniteMarkedBelyiData :
    SectionControlledFiniteMarkedBelyiData K C V where
  evalPackage := F.evalPackage
  hmarkedOpen := F.hmarkedOpen
  map := F.map
  sends_vanishing_to_marked := by
    intro S s hs x hx
    rw [F.map_base_eq_pair s x]
    exact (F.pair s).maps_section0_zero_to_marked
      (by
        rw [F.pair_section0_eval_eq_index s x]
        exact hs x hx)
  nonzero_avoids_marked := by
    intro T s hs
    exact F.nonzero_avoids_marked hs

theorem toSectionControlledFiniteMarkedBelyiData_map_apply
    (s : V) :
    F.toSectionControlledFiniteMarkedBelyiData.map s = F.map s := rfl

/-- Finite disjoint-set conclusion after the projective-section construction
has supplied finite marked Belyi maps and branch avoidance. -/
theorem exists_for_finite_disjoint
    [Infinite K] {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V, (∀ x ∈ S, (F.map s).hom.base x ∈ markedSchemePointSet K) ∧
      ∀ x ∈ T, (F.map s).hom.base x ∉ markedSchemePointSet K := by
  exact F.toSectionControlledFiniteMarkedBelyiData.exists_for_finite_disjoint
    hS hT hdis

/-- Corollary 1.2-style one-point open consequence of the projective-section
finite marked family. -/
theorem exists_belyiOpen_inside_complement
    [Infinite K] [T1Space (P1 K)]
    {A : Set C} (hA : A.Finite) {x : C} (hxA : x ∉ A) :
    ∃ s : V,
      IsOpen ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        x ∈ ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ Aᶜ := by
  exact
    F.toSectionControlledFiniteMarkedBelyiData.exists_belyiOpen_inside_complement
      hA hxA

end ProjectiveSectionFiniteMarkedFamily

end ProjectiveSectionMaps
end SourceStack
end HilbertTest
