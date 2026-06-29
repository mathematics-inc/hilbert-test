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

/-- A structure morphism `X ⟶ Spec K` induces the usual `K`-algebra structure
on the global sections of `X`. -/
noncomputable def schemeStructureAlgebra
    (K : Type u) [Field K] (X : Scheme.{u})
    (structureMap : X ⟶ Spec (CommRingCat.of K)) :
    Algebra K Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ structureMap.appTop).hom.toAlgebra

theorem schemeStructureAlgebra_algebraMap
    (K : Type u) [Field K] (X : Scheme.{u})
    (structureMap : X ⟶ Spec (CommRingCat.of K)) :
    @algebraMap K Γ(X, ⊤) _ _
      (schemeStructureAlgebra K X structureMap) =
        ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ structureMap.appTop).hom := rfl

/-- A structure morphism on a scheme supplies `K`-algebra structures on all
members of an open cover by composing their cover maps with the structure
morphism. -/
noncomputable def openCoverLocalSectionAlgebra
    (K : Type u) [Field K] {C : Scheme.{u}}
    (cover : C.OpenCover) (structureMap : C ⟶ Spec (CommRingCat.of K)) :
    ∀ i : cover.J, Algebra K Γ(cover.obj i, ⊤) :=
  fun i => schemeStructureAlgebra K (cover.obj i) (cover.map i ≫ structureMap)

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

/-- The first section vanishes at a point exactly when the associated
projective-line morphism hits the checked zero point there. -/
theorem section0_vanishes_iff_hom_eq_zero (x : C) :
    P.evalData.eval x P.section0 = 0 ↔
      P.hom.base x = schemeCarrierPoint K MarkedPointLabel.zero := by
  constructor
  · exact P.zero_of_section0_vanishes x
  · exact P.section0_vanishes_of_zero x

/-- The first section is nonzero at a point exactly when the associated
projective-line morphism avoids the checked zero point there. -/
theorem section0_nonzero_iff_hom_ne_zero (x : C) :
    P.evalData.eval x P.section0 ≠ 0 ↔
      P.hom.base x ≠ schemeCarrierPoint K MarkedPointLabel.zero := by
  constructor
  · exact P.avoids_zeroPoint_of_section0_nonzero
  · intro hzero hvanish
    exact hzero (P.zero_of_section0_vanishes x hvanish)

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

/-- The first section vanishes exactly on the zero fiber of the glued
projective-line morphism. -/
theorem section0_vanishes_iff_globalHom_eq_zero (x : C) :
    D.evalData.eval x D.section0 = 0 ↔
      D.globalHom.base x = schemeCarrierPoint K MarkedPointLabel.zero := by
  constructor
  · exact D.global_zero_of_section0_vanishes x
  · exact D.section0_vanishes_of_global_zero x

/-- The first section is nonzero exactly away from the zero fiber of the glued
projective-line morphism. -/
theorem section0_nonzero_iff_globalHom_ne_zero (x : C) :
    D.evalData.eval x D.section0 ≠ 0 ↔
      D.globalHom.base x ≠ schemeCarrierPoint K MarkedPointLabel.zero := by
  constructor
  · intro hsection hzero
    exact hsection (D.section0_vanishes_of_global_zero x hzero)
  · intro hzero hsection
    exact hzero (D.global_zero_of_section0_vanishes x hsection)

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

/-- A more concrete local chart package for the two-section construction:
local maps land in one of the two standard affine charts of `P1` before being
composed with the corresponding open immersion into `P1` and glued.  This
matches the usual proof from line-bundle trivializations: on each trivializing
open, the section ratio is an affine coordinate in either the `X₀ ≠ 0` or
`X₁ ≠ 0` chart. -/
structure StandardChartProjectiveLineSectionData
    (K : Type u) [Field K] (C : Scheme.{u})
    (V : Type w) [AddCommGroup V] [Module K V] where
  evalData : RRSectionEvaluationData K C V
  section0 : V
  section1 : V
  no_common_zero : HasNoCommonZero evalData section0 section1
  cover : C.OpenCover
  chart : cover.J → StandardAffineChart
  localChartHom :
    ∀ i : cover.J, cover.obj i ⟶ standardChartScheme K (chart i)
  local_compat :
    ∀ i j : cover.J,
      (pullback.fst (cover.map i) (cover.map j) ≫ localChartHom i) ≫
          standardChartMap K (chart i) =
        (pullback.snd (cover.map i) (cover.map j) ≫ localChartHom j) ≫
          standardChartMap K (chart j)
  local_zero_of_section0_vanishes :
    ∀ i (x : cover.obj i),
      evalData.eval ((cover.map i).base x) section0 = 0 →
        (localChartHom i ≫ standardChartMap K (chart i)).base x =
          schemeCarrierPoint K MarkedPointLabel.zero
  local_section0_vanishes_of_zero :
    ∀ i (x : cover.obj i),
      (localChartHom i ≫ standardChartMap K (chart i)).base x =
          schemeCarrierPoint K MarkedPointLabel.zero →
        evalData.eval ((cover.map i).base x) section0 = 0

namespace StandardChartProjectiveLineSectionData

variable {C : Scheme.{u}}
variable (D : StandardChartProjectiveLineSectionData K C V)

/-- The local map to `P1` obtained from a local affine-chart map. -/
def localHom (i : D.cover.J) : D.cover.obj i ⟶ P1 K :=
  D.localChartHom i ≫ standardChartMap K (D.chart i)

@[reassoc]
theorem localHom_eq (i : D.cover.J) :
    D.localHom i = D.localChartHom i ≫ standardChartMap K (D.chart i) := rfl

/-- Forget concrete standard-chart targets to the general glued local-map
package. -/
def toGluedProjectiveLineSectionData :
    GluedProjectiveLineSectionData K C V where
  evalData := D.evalData
  section0 := D.section0
  section1 := D.section1
  no_common_zero := D.no_common_zero
  cover := D.cover
  localHom := D.localHom
  local_compat := by
    intro i j
    simpa [localHom, Category.assoc] using D.local_compat i j
  local_zero_of_section0_vanishes := by
    intro i x hx
    simpa [localHom] using D.local_zero_of_section0_vanishes i x hx
  local_section0_vanishes_of_zero := by
    intro i x hx
    exact D.local_section0_vanishes_of_zero i x (by simpa [localHom] using hx)

/-- The global morphism obtained by composing local standard-chart maps with
their chart open immersions and gluing. -/
def globalHom : C ⟶ P1 K :=
  D.toGluedProjectiveLineSectionData.globalHom

theorem toGluedProjectiveLineSectionData_globalHom :
    D.toGluedProjectiveLineSectionData.globalHom = D.globalHom := rfl

@[reassoc]
theorem cover_map_globalHom (i : D.cover.J) :
    D.cover.map i ≫ D.globalHom = D.localHom i := by
  exact D.toGluedProjectiveLineSectionData.cover_map_globalHom i

theorem globalHom_base_of_cover (i : D.cover.J) (x : D.cover.obj i) :
    D.globalHom.base ((D.cover.map i).base x) = (D.localHom i).base x := by
  exact D.toGluedProjectiveLineSectionData.globalHom_base_of_cover i x

theorem global_zero_of_section0_vanishes
    (x : C) (hx : D.evalData.eval x D.section0 = 0) :
    D.globalHom.base x = schemeCarrierPoint K MarkedPointLabel.zero := by
  exact D.toGluedProjectiveLineSectionData.global_zero_of_section0_vanishes x hx

theorem section0_vanishes_of_global_zero
    (x : C)
    (hx : D.globalHom.base x = schemeCarrierPoint K MarkedPointLabel.zero) :
    D.evalData.eval x D.section0 = 0 := by
  exact D.toGluedProjectiveLineSectionData.section0_vanishes_of_global_zero x hx

/-- The first section vanishes exactly on the zero fiber of the glued
standard-chart projective-line morphism. -/
theorem section0_vanishes_iff_globalHom_eq_zero (x : C) :
    D.evalData.eval x D.section0 = 0 ↔
      D.globalHom.base x = schemeCarrierPoint K MarkedPointLabel.zero := by
  constructor
  · exact D.global_zero_of_section0_vanishes x
  · exact D.section0_vanishes_of_global_zero x

/-- The first section is nonzero exactly away from the zero fiber of the glued
standard-chart projective-line morphism. -/
theorem section0_nonzero_iff_globalHom_ne_zero (x : C) :
    D.evalData.eval x D.section0 ≠ 0 ↔
      D.globalHom.base x ≠ schemeCarrierPoint K MarkedPointLabel.zero := by
  constructor
  · intro hsection hzero
    exact hsection (D.section0_vanishes_of_global_zero x hzero)
  · intro hzero hsection
    exact hzero (D.global_zero_of_section0_vanishes x hsection)

def toProjectiveLineSectionPair : ProjectiveLineSectionPair K C V :=
  D.toGluedProjectiveLineSectionData.toProjectiveLineSectionPair

theorem toGluedProjectiveLineSectionData_toProjectiveLineSectionPair :
    D.toGluedProjectiveLineSectionData.toProjectiveLineSectionPair =
      D.toProjectiveLineSectionPair := rfl

theorem toProjectiveLineSectionPair_hom :
    D.toProjectiveLineSectionPair.hom = D.globalHom := rfl

theorem toProjectiveLineSectionPair_maps_section0_zero_to_marked
    {x : C} (hx : D.evalData.eval x D.section0 = 0) :
    D.toProjectiveLineSectionPair.hom.base x ∈ markedSchemePointSet K := by
  exact D.toProjectiveLineSectionPair.maps_section0_zero_to_marked hx

end StandardChartProjectiveLineSectionData

/-- Ring-hom form of the concrete standard-chart local package.  This is one
step closer to the line-bundle construction: local section ratios should supply
ring maps from the standard chart coordinate rings to global functions on the
trivializing opens; the `Γ-Spec` adjunction then constructs the local chart
morphisms used by `StandardChartProjectiveLineSectionData`. -/
structure StandardChartProjectiveLineSectionRingData
    (K : Type u) [Field K] (C : Scheme.{u})
    (V : Type w) [AddCommGroup V] [Module K V] where
  evalData : RRSectionEvaluationData K C V
  section0 : V
  section1 : V
  no_common_zero : HasNoCommonZero evalData section0 section1
  cover : C.OpenCover
  chart : cover.J → StandardAffineChart
  localChartRingHom :
    ∀ i : cover.J,
      CommRingCat.of (standardChartRing K (chart i)) ⟶ Γ(cover.obj i, ⊤)
  local_compat :
    ∀ i j : cover.J,
      (pullback.fst (cover.map i) (cover.map j) ≫
          standardChartHomOfRingHom K (localChartRingHom i)) ≫
            standardChartMap K (chart i) =
        (pullback.snd (cover.map i) (cover.map j) ≫
          standardChartHomOfRingHom K (localChartRingHom j)) ≫
            standardChartMap K (chart j)
  local_zero_of_section0_vanishes :
    ∀ i (x : cover.obj i),
      evalData.eval ((cover.map i).base x) section0 = 0 →
        (standardChartToP1HomOfRingHom K (localChartRingHom i)).base x =
          schemeCarrierPoint K MarkedPointLabel.zero
  local_section0_vanishes_of_zero :
    ∀ i (x : cover.obj i),
      (standardChartToP1HomOfRingHom K (localChartRingHom i)).base x =
          schemeCarrierPoint K MarkedPointLabel.zero →
        evalData.eval ((cover.map i).base x) section0 = 0

namespace StandardChartProjectiveLineSectionRingData

variable {C : Scheme.{u}}
variable (D : StandardChartProjectiveLineSectionRingData K C V)

/-- The local standard-chart morphism obtained from the local chart coordinate
ring map. -/
def localChartHom (i : D.cover.J) :
    D.cover.obj i ⟶ standardChartScheme K (D.chart i) :=
  standardChartHomOfRingHom K (D.localChartRingHom i)

/-- The local map to `P1` obtained from the ring-hom chart morphism. -/
def localHom (i : D.cover.J) : D.cover.obj i ⟶ P1 K :=
  standardChartToP1HomOfRingHom K (D.localChartRingHom i)

theorem localHom_eq (i : D.cover.J) :
    D.localHom i = D.localChartHom i ≫ standardChartMap K (D.chart i) := rfl

/-- Convert local chart coordinate-ring maps to local standard-chart morphism
data. -/
def toStandardChartProjectiveLineSectionData :
    StandardChartProjectiveLineSectionData K C V where
  evalData := D.evalData
  section0 := D.section0
  section1 := D.section1
  no_common_zero := D.no_common_zero
  cover := D.cover
  chart := D.chart
  localChartHom := D.localChartHom
  local_compat := by
    intro i j
    simpa [localChartHom] using D.local_compat i j
  local_zero_of_section0_vanishes := by
    intro i x hx
    simpa [localHom, localChartHom, standardChartToP1HomOfRingHom_def] using
      D.local_zero_of_section0_vanishes i x hx
  local_section0_vanishes_of_zero := by
    intro i x hx
    exact D.local_section0_vanishes_of_zero i x
      (by simpa [localHom, localChartHom, standardChartToP1HomOfRingHom_def] using hx)

def globalHom : C ⟶ P1 K :=
  D.toStandardChartProjectiveLineSectionData.globalHom

theorem toStandardChartProjectiveLineSectionData_globalHom :
    D.toStandardChartProjectiveLineSectionData.globalHom = D.globalHom := rfl

@[reassoc]
theorem cover_map_globalHom (i : D.cover.J) :
    D.cover.map i ≫ D.globalHom = D.localHom i := by
  exact D.toStandardChartProjectiveLineSectionData.cover_map_globalHom i

theorem globalHom_base_of_cover (i : D.cover.J) (x : D.cover.obj i) :
    D.globalHom.base ((D.cover.map i).base x) = (D.localHom i).base x := by
  exact D.toStandardChartProjectiveLineSectionData.globalHom_base_of_cover i x

theorem global_zero_of_section0_vanishes
    (x : C) (hx : D.evalData.eval x D.section0 = 0) :
    D.globalHom.base x = schemeCarrierPoint K MarkedPointLabel.zero := by
  exact D.toStandardChartProjectiveLineSectionData.global_zero_of_section0_vanishes x hx

theorem section0_vanishes_of_global_zero
    (x : C)
    (hx : D.globalHom.base x = schemeCarrierPoint K MarkedPointLabel.zero) :
    D.evalData.eval x D.section0 = 0 := by
  exact D.toStandardChartProjectiveLineSectionData.section0_vanishes_of_global_zero x hx

/-- The first section vanishes exactly on the zero fiber of the glued
ring-hom chart projective-line morphism. -/
theorem section0_vanishes_iff_globalHom_eq_zero (x : C) :
    D.evalData.eval x D.section0 = 0 ↔
      D.globalHom.base x = schemeCarrierPoint K MarkedPointLabel.zero := by
  constructor
  · exact D.global_zero_of_section0_vanishes x
  · exact D.section0_vanishes_of_global_zero x

/-- The first section is nonzero exactly away from the zero fiber of the glued
ring-hom chart projective-line morphism. -/
theorem section0_nonzero_iff_globalHom_ne_zero (x : C) :
    D.evalData.eval x D.section0 ≠ 0 ↔
      D.globalHom.base x ≠ schemeCarrierPoint K MarkedPointLabel.zero := by
  constructor
  · intro hsection hzero
    exact hsection (D.section0_vanishes_of_global_zero x hzero)
  · intro hzero hsection
    exact hzero (D.global_zero_of_section0_vanishes x hsection)

def toProjectiveLineSectionPair : ProjectiveLineSectionPair K C V :=
  D.toStandardChartProjectiveLineSectionData.toProjectiveLineSectionPair

theorem toStandardChartProjectiveLineSectionData_toProjectiveLineSectionPair :
    D.toStandardChartProjectiveLineSectionData.toProjectiveLineSectionPair =
      D.toProjectiveLineSectionPair := rfl

theorem toProjectiveLineSectionPair_hom :
    D.toProjectiveLineSectionPair.hom = D.globalHom := rfl

theorem toProjectiveLineSectionPair_maps_section0_zero_to_marked
    {x : C} (hx : D.evalData.eval x D.section0 = 0) :
    D.toProjectiveLineSectionPair.hom.base x ∈ markedSchemePointSet K := by
  exact D.toProjectiveLineSectionPair.maps_section0_zero_to_marked hx

end StandardChartProjectiveLineSectionRingData

/-- Section-ratio form of the local chart construction.  This refines
`StandardChartProjectiveLineSectionRingData` by naming the regular function
which is the pullback of the standard affine coordinate on each chart.  In the
eventual line-bundle proof those functions are the local quotients `s1/s0` and
`s0/s1` on trivializing opens. -/
structure SectionRatioProjectiveLineSectionData
    (K : Type u) [Field K] (C : Scheme.{u})
    (V : Type w) [AddCommGroup V] [Module K V] where
  evalData : RRSectionEvaluationData K C V
  section0 : V
  section1 : V
  no_common_zero : HasNoCommonZero evalData section0 section1
  cover : C.OpenCover
  chart : cover.J → StandardAffineChart
  localSectionRatio : ∀ i : cover.J, Γ(cover.obj i, ⊤)
  localChartRingHom :
    ∀ i : cover.J,
      CommRingCat.of (standardChartRing K (chart i)) ⟶ Γ(cover.obj i, ⊤)
  localChartCoordinate_eq_ratio :
    ∀ i : cover.J,
      standardChartCoordinateSection K (localChartRingHom i) = localSectionRatio i
  local_compat :
    ∀ i j : cover.J,
      (pullback.fst (cover.map i) (cover.map j) ≫
          standardChartHomOfRingHom K (localChartRingHom i)) ≫
            standardChartMap K (chart i) =
        (pullback.snd (cover.map i) (cover.map j) ≫
          standardChartHomOfRingHom K (localChartRingHom j)) ≫
            standardChartMap K (chart j)
  local_zero_of_section0_vanishes :
    ∀ i (x : cover.obj i),
      evalData.eval ((cover.map i).base x) section0 = 0 →
        (standardChartToP1HomOfRingHom K (localChartRingHom i)).base x =
          schemeCarrierPoint K MarkedPointLabel.zero
  local_section0_vanishes_of_zero :
    ∀ i (x : cover.obj i),
      (standardChartToP1HomOfRingHom K (localChartRingHom i)).base x =
          schemeCarrierPoint K MarkedPointLabel.zero →
        evalData.eval ((cover.map i).base x) section0 = 0

namespace SectionRatioProjectiveLineSectionData

variable {C : Scheme.{u}}
variable (D : SectionRatioProjectiveLineSectionData K C V)

/-- The pulled-back affine coordinate on a local chart, before identifying it
with the section ratio. -/
def localCoordinate (i : D.cover.J) : Γ(D.cover.obj i, ⊤) :=
  standardChartCoordinateSection K (D.localChartRingHom i)

/-- The local coordinate pulled back from `P1` is the named local section
ratio. -/
theorem localCoordinate_eq_ratio (i : D.cover.J) :
    D.localCoordinate i = D.localSectionRatio i := by
  simpa [localCoordinate] using D.localChartCoordinate_eq_ratio i

/-- The same coordinate-ratio statement expanded as an equality after applying
the chart coordinate-ring homomorphism. -/
theorem localChartRingHom_coordinate_eq_ratio (i : D.cover.J) :
    D.localChartRingHom i (standardChartCoordinate K (D.chart i)) =
      D.localSectionRatio i := by
  simpa [localCoordinate, standardChartCoordinateSection] using
    D.localCoordinate_eq_ratio i

/-- Forget the explicit section-ratio names to the chart coordinate-ring
package. -/
def toStandardChartProjectiveLineSectionRingData :
    StandardChartProjectiveLineSectionRingData K C V where
  evalData := D.evalData
  section0 := D.section0
  section1 := D.section1
  no_common_zero := D.no_common_zero
  cover := D.cover
  chart := D.chart
  localChartRingHom := D.localChartRingHom
  local_compat := D.local_compat
  local_zero_of_section0_vanishes := D.local_zero_of_section0_vanishes
  local_section0_vanishes_of_zero := D.local_section0_vanishes_of_zero

/-- The local standard-chart morphism obtained from the local section-ratio
chart ring map. -/
def localChartHom (i : D.cover.J) :
    D.cover.obj i ⟶ standardChartScheme K (D.chart i) :=
  D.toStandardChartProjectiveLineSectionRingData.localChartHom i

/-- The local map to `P1` obtained from a section-ratio chart ring map. -/
def localHom (i : D.cover.J) : D.cover.obj i ⟶ P1 K :=
  D.toStandardChartProjectiveLineSectionRingData.localHom i

theorem localHom_eq (i : D.cover.J) :
    D.localHom i = D.localChartHom i ≫ standardChartMap K (D.chart i) := by
  exact D.toStandardChartProjectiveLineSectionRingData.localHom_eq i

def globalHom : C ⟶ P1 K :=
  D.toStandardChartProjectiveLineSectionRingData.globalHom

theorem toStandardChartProjectiveLineSectionRingData_globalHom :
    D.toStandardChartProjectiveLineSectionRingData.globalHom = D.globalHom := rfl

@[reassoc]
theorem cover_map_globalHom (i : D.cover.J) :
    D.cover.map i ≫ D.globalHom = D.localHom i := by
  exact D.toStandardChartProjectiveLineSectionRingData.cover_map_globalHom i

theorem globalHom_base_of_cover (i : D.cover.J) (x : D.cover.obj i) :
    D.globalHom.base ((D.cover.map i).base x) = (D.localHom i).base x := by
  exact D.toStandardChartProjectiveLineSectionRingData.globalHom_base_of_cover i x

theorem global_zero_of_section0_vanishes
    (x : C) (hx : D.evalData.eval x D.section0 = 0) :
    D.globalHom.base x = schemeCarrierPoint K MarkedPointLabel.zero := by
  exact D.toStandardChartProjectiveLineSectionRingData.global_zero_of_section0_vanishes x hx

theorem section0_vanishes_of_global_zero
    (x : C)
    (hx : D.globalHom.base x = schemeCarrierPoint K MarkedPointLabel.zero) :
    D.evalData.eval x D.section0 = 0 := by
  exact D.toStandardChartProjectiveLineSectionRingData.section0_vanishes_of_global_zero x hx

/-- The first section vanishes exactly on the zero fiber of the
section-ratio projective-line morphism. -/
theorem section0_vanishes_iff_globalHom_eq_zero (x : C) :
    D.evalData.eval x D.section0 = 0 ↔
      D.globalHom.base x = schemeCarrierPoint K MarkedPointLabel.zero := by
  constructor
  · exact D.global_zero_of_section0_vanishes x
  · exact D.section0_vanishes_of_global_zero x

/-- The first section is nonzero exactly away from the zero fiber of the
section-ratio projective-line morphism. -/
theorem section0_nonzero_iff_globalHom_ne_zero (x : C) :
    D.evalData.eval x D.section0 ≠ 0 ↔
      D.globalHom.base x ≠ schemeCarrierPoint K MarkedPointLabel.zero := by
  constructor
  · intro hsection hzero
    exact hsection (D.section0_vanishes_of_global_zero x hzero)
  · intro hzero hsection
    exact hzero (D.global_zero_of_section0_vanishes x hsection)

def toProjectiveLineSectionPair : ProjectiveLineSectionPair K C V :=
  D.toStandardChartProjectiveLineSectionRingData.toProjectiveLineSectionPair

theorem toStandardChartProjectiveLineSectionRingData_toProjectiveLineSectionPair :
    D.toStandardChartProjectiveLineSectionRingData.toProjectiveLineSectionPair =
      D.toProjectiveLineSectionPair := rfl

theorem toProjectiveLineSectionPair_hom :
    D.toProjectiveLineSectionPair.hom = D.globalHom := rfl

theorem toProjectiveLineSectionPair_maps_section0_zero_to_marked
    {x : C} (hx : D.evalData.eval x D.section0 = 0) :
    D.toProjectiveLineSectionPair.hom.base x ∈ markedSchemePointSet K := by
  exact D.toProjectiveLineSectionPair.maps_section0_zero_to_marked hx

end SectionRatioProjectiveLineSectionData

/-- Section-ratio data in which the standard-chart coordinate-ring maps are
constructed from the named regular ratios.  Compared with
`SectionRatioProjectiveLineSectionData`, this removes `localChartRingHom` and
`localChartCoordinate_eq_ratio` as primitive fields: once each local section
ring is a `K`-algebra, the standard affine chart ring maps are built by
localizing the homogeneous-coordinate evaluation `(X₀, X₁) = (1, r)` or
`(r, 1)`. -/
structure CoordinateSectionRatioProjectiveLineSectionData
    (K : Type u) [Field K] (C : Scheme.{u})
    (V : Type w) [AddCommGroup V] [Module K V] where
  evalData : RRSectionEvaluationData K C V
  section0 : V
  section1 : V
  no_common_zero : HasNoCommonZero evalData section0 section1
  cover : C.OpenCover
  chart : cover.J → StandardAffineChart
  localSectionAlgebra : ∀ i : cover.J, Algebra K Γ(cover.obj i, ⊤)
  localSectionRatio : ∀ i : cover.J, Γ(cover.obj i, ⊤)
  local_compat :
    ∀ i j : cover.J,
      (pullback.fst (cover.map i) (cover.map j) ≫
          standardChartHomOfRingHom K
            (standardChartRingCatHomOfCoordinateOfAlgebra K (chart i)
              (localSectionAlgebra i) (localSectionRatio i))) ≫
            standardChartMap K (chart i) =
        (pullback.snd (cover.map i) (cover.map j) ≫
          standardChartHomOfRingHom K
            (standardChartRingCatHomOfCoordinateOfAlgebra K (chart j)
              (localSectionAlgebra j) (localSectionRatio j))) ≫
            standardChartMap K (chart j)
  local_zero_of_section0_vanishes :
    ∀ i (x : cover.obj i),
      evalData.eval ((cover.map i).base x) section0 = 0 →
        (standardChartToP1HomOfRingHom K
          (standardChartRingCatHomOfCoordinateOfAlgebra K (chart i)
            (localSectionAlgebra i) (localSectionRatio i))).base x =
          schemeCarrierPoint K MarkedPointLabel.zero
  local_section0_vanishes_of_zero :
    ∀ i (x : cover.obj i),
      (standardChartToP1HomOfRingHom K
          (standardChartRingCatHomOfCoordinateOfAlgebra K (chart i)
            (localSectionAlgebra i) (localSectionRatio i))).base x =
          schemeCarrierPoint K MarkedPointLabel.zero →
        evalData.eval ((cover.map i).base x) section0 = 0

namespace CoordinateSectionRatioProjectiveLineSectionData

variable {C : Scheme.{u}}
variable (D : CoordinateSectionRatioProjectiveLineSectionData K C V)

/-- The chart coordinate-ring map built from the named local section ratio. -/
noncomputable def localChartRingHom (i : D.cover.J) :
    CommRingCat.of (standardChartRing K (D.chart i)) ⟶ Γ(D.cover.obj i, ⊤) :=
  standardChartRingCatHomOfCoordinateOfAlgebra K (D.chart i)
    (D.localSectionAlgebra i) (D.localSectionRatio i)

/-- The pulled-back affine coordinate on a local chart, built from the named
local section ratio. -/
noncomputable def localCoordinate (i : D.cover.J) : Γ(D.cover.obj i, ⊤) :=
  standardChartCoordinateSection K (D.localChartRingHom i)

/-- The constructed chart-ring map pulls the distinguished coordinate back to
the supplied local section ratio. -/
theorem localCoordinate_eq_ratio (i : D.cover.J) :
    D.localCoordinate i = D.localSectionRatio i := by
  change D.localChartRingHom i (standardChartCoordinate K (D.chart i)) =
    D.localSectionRatio i
  exact standardChartRingCatHomOfCoordinateOfAlgebra_apply_coordinate K (D.chart i)
    (D.localSectionAlgebra i) (D.localSectionRatio i)

/-- Expanded coordinate-ratio identity for the constructed local chart-ring
map. -/
theorem localChartRingHom_coordinate_eq_ratio (i : D.cover.J) :
    D.localChartRingHom i (standardChartCoordinate K (D.chart i)) =
      D.localSectionRatio i := by
  simpa [localCoordinate, standardChartCoordinateSection] using
    D.localCoordinate_eq_ratio i

/-- Forget that the local chart-ring maps were constructed from ratios. -/
noncomputable def toSectionRatioProjectiveLineSectionData :
    SectionRatioProjectiveLineSectionData K C V where
  evalData := D.evalData
  section0 := D.section0
  section1 := D.section1
  no_common_zero := D.no_common_zero
  cover := D.cover
  chart := D.chart
  localSectionRatio := D.localSectionRatio
  localChartRingHom := D.localChartRingHom
  localChartCoordinate_eq_ratio := D.localCoordinate_eq_ratio
  local_compat := D.local_compat
  local_zero_of_section0_vanishes := D.local_zero_of_section0_vanishes
  local_section0_vanishes_of_zero := D.local_section0_vanishes_of_zero

/-- The local map to `P1` obtained from a constructed section-ratio chart ring
map. -/
noncomputable def localHom (i : D.cover.J) : D.cover.obj i ⟶ P1 K :=
  D.toSectionRatioProjectiveLineSectionData.localHom i

/-- The global projective-line morphism obtained by gluing the constructed
section-ratio chart maps. -/
noncomputable def globalHom : C ⟶ P1 K :=
  D.toSectionRatioProjectiveLineSectionData.globalHom

theorem toSectionRatioProjectiveLineSectionData_globalHom :
    D.toSectionRatioProjectiveLineSectionData.globalHom = D.globalHom := rfl

@[reassoc]
theorem cover_map_globalHom (i : D.cover.J) :
    D.cover.map i ≫ D.globalHom = D.localHom i := by
  exact D.toSectionRatioProjectiveLineSectionData.cover_map_globalHom i

theorem globalHom_base_of_cover (i : D.cover.J) (x : D.cover.obj i) :
    D.globalHom.base ((D.cover.map i).base x) = (D.localHom i).base x := by
  exact D.toSectionRatioProjectiveLineSectionData.globalHom_base_of_cover i x

theorem global_zero_of_section0_vanishes
    (x : C) (hx : D.evalData.eval x D.section0 = 0) :
    D.globalHom.base x = schemeCarrierPoint K MarkedPointLabel.zero := by
  exact D.toSectionRatioProjectiveLineSectionData.global_zero_of_section0_vanishes x hx

theorem section0_vanishes_of_global_zero
    (x : C)
    (hx : D.globalHom.base x = schemeCarrierPoint K MarkedPointLabel.zero) :
    D.evalData.eval x D.section0 = 0 := by
  exact D.toSectionRatioProjectiveLineSectionData.section0_vanishes_of_global_zero x hx

/-- The first section vanishes exactly on the zero fiber of the constructed
section-ratio projective-line morphism. -/
theorem section0_vanishes_iff_globalHom_eq_zero (x : C) :
    D.evalData.eval x D.section0 = 0 ↔
      D.globalHom.base x = schemeCarrierPoint K MarkedPointLabel.zero := by
  exact D.toSectionRatioProjectiveLineSectionData.section0_vanishes_iff_globalHom_eq_zero x

/-- The first section is nonzero exactly away from the zero fiber of the
constructed section-ratio projective-line morphism. -/
theorem section0_nonzero_iff_globalHom_ne_zero (x : C) :
    D.evalData.eval x D.section0 ≠ 0 ↔
      D.globalHom.base x ≠ schemeCarrierPoint K MarkedPointLabel.zero := by
  exact D.toSectionRatioProjectiveLineSectionData.section0_nonzero_iff_globalHom_ne_zero x

noncomputable def toProjectiveLineSectionPair : ProjectiveLineSectionPair K C V :=
  D.toSectionRatioProjectiveLineSectionData.toProjectiveLineSectionPair

theorem toSectionRatioProjectiveLineSectionData_toProjectiveLineSectionPair :
    D.toSectionRatioProjectiveLineSectionData.toProjectiveLineSectionPair =
      D.toProjectiveLineSectionPair := rfl

theorem toProjectiveLineSectionPair_hom :
    D.toProjectiveLineSectionPair.hom = D.globalHom := rfl

theorem toProjectiveLineSectionPair_maps_section0_zero_to_marked
    {x : C} (hx : D.evalData.eval x D.section0 = 0) :
    D.toProjectiveLineSectionPair.hom.base x ∈ markedSchemePointSet K := by
  exact D.toProjectiveLineSectionPair.maps_section0_zero_to_marked hx

end CoordinateSectionRatioProjectiveLineSectionData

/-- Choice of denominator in a local trivialization of the two selected
sections.  If `section0` is the nonvanishing denominator, the point lands in
the `X0 ≠ 0` chart with affine coordinate `s1/s0`; if `section1` is the
nonvanishing denominator, it lands in the `X1 ≠ 0` chart with coordinate
`s0/s1`. -/
inductive LocalSectionRatioChart where
  | section0
  | section1
  deriving DecidableEq, Inhabited

namespace LocalSectionRatioChart

/-- The standard affine chart selected by a nonvanishing local denominator. -/
def toStandardAffineChart : LocalSectionRatioChart → StandardAffineChart
  | section0 => StandardAffineChart.x0
  | section1 => StandardAffineChart.x1

/-- The numerator of the local affine coordinate for a pair of local section
representatives. -/
def numerator {R : Type*} : LocalSectionRatioChart → R → R → R
  | section0, _s0, s1 => s1
  | section1, s0, _s1 => s0

/-- The denominator of the local affine coordinate for a pair of local section
representatives. -/
def denominator {R : Type*} : LocalSectionRatioChart → R → R → R
  | section0, s0, _s1 => s0
  | section1, _s0, s1 => s1

/-- The local algebraic equation saying that `ratio` is the regular quotient of
the two local section representatives on a trivializing open. -/
def ratioEquation {R : Type*} [Mul R]
    (c : LocalSectionRatioChart) (s0 s1 ratio : R) : Prop :=
  ratio * denominator c s0 s1 = numerator c s0 s1

@[simp]
theorem toStandardAffineChart_section0 :
    toStandardAffineChart section0 = StandardAffineChart.x0 := rfl

@[simp]
theorem toStandardAffineChart_section1 :
    toStandardAffineChart section1 = StandardAffineChart.x1 := rfl

@[simp]
theorem numerator_section0 {R : Type*} (s0 s1 : R) :
    numerator section0 s0 s1 = s1 := rfl

@[simp]
theorem numerator_section1 {R : Type*} (s0 s1 : R) :
    numerator section1 s0 s1 = s0 := rfl

@[simp]
theorem denominator_section0 {R : Type*} (s0 s1 : R) :
    denominator section0 s0 s1 = s0 := rfl

@[simp]
theorem denominator_section1 {R : Type*} (s0 s1 : R) :
    denominator section1 s0 s1 = s1 := rfl

theorem ratioEquation_section0 {R : Type*} [Mul R] (s0 s1 ratio : R) :
    ratioEquation section0 s0 s1 ratio ↔ ratio * s0 = s1 := Iff.rfl

theorem ratioEquation_section1 {R : Type*} [Mul R] (s0 s1 ratio : R) :
    ratioEquation section1 s0 s1 ratio ↔ ratio * s1 = s0 := Iff.rfl

/-- If the chosen denominator is a unit, the local quotient is represented by
`numerator * denominator⁻¹`. -/
def unitRatio {R : Type*} [Monoid R]
    (c : LocalSectionRatioChart) (s0 s1 : R) (u : Rˣ) : R :=
  numerator c s0 s1 * ↑(u⁻¹)

/-- The unit-denominator quotient satisfies the ratio equation. -/
theorem unitRatio_mul_denominator_eq_numerator
    {R : Type*} [CommMonoid R]
    (c : LocalSectionRatioChart) (s0 s1 : R) (u : Rˣ)
    (hden : denominator c s0 s1 = (u : R)) :
    unitRatio c s0 s1 u * denominator c s0 s1 =
      numerator c s0 s1 := by
  unfold unitRatio
  rw [hden]
  simp [mul_assoc, mul_comm, mul_left_comm]

end LocalSectionRatioChart

/-- Local-trivialization algebra for the section-ratio construction.  A genuine
invertible sheaf trivialization should supply local representatives of the two
global sections and regular ratios satisfying the displayed quotient equations.
This package proves that such local algebra feeds the already checked
section-ratio chart construction. -/
structure TrivializedSectionRatioData
    (K : Type u) [Field K] (C : Scheme.{u})
    (V : Type w) [AddCommGroup V] [Module K V] where
  evalData : RRSectionEvaluationData K C V
  section0 : V
  section1 : V
  no_common_zero : HasNoCommonZero evalData section0 section1
  cover : C.OpenCover
  ratioChart : cover.J → LocalSectionRatioChart
  localSection0 : ∀ i : cover.J, Γ(cover.obj i, ⊤)
  localSection1 : ∀ i : cover.J, Γ(cover.obj i, ⊤)
  localSectionRatio : ∀ i : cover.J, Γ(cover.obj i, ⊤)
  local_ratio_spec :
    ∀ i : cover.J,
      LocalSectionRatioChart.ratioEquation (ratioChart i)
        (localSection0 i) (localSection1 i) (localSectionRatio i)
  localChartRingHom :
    ∀ i : cover.J,
      CommRingCat.of
        (standardChartRing K (LocalSectionRatioChart.toStandardAffineChart (ratioChart i))) ⟶
          Γ(cover.obj i, ⊤)
  localChartCoordinate_eq_ratio :
    ∀ i : cover.J,
      standardChartCoordinateSection K (localChartRingHom i) = localSectionRatio i
  local_compat :
    ∀ i j : cover.J,
      (pullback.fst (cover.map i) (cover.map j) ≫
          standardChartHomOfRingHom K (localChartRingHom i)) ≫
            standardChartMap K
              (LocalSectionRatioChart.toStandardAffineChart (ratioChart i)) =
        (pullback.snd (cover.map i) (cover.map j) ≫
          standardChartHomOfRingHom K (localChartRingHom j)) ≫
            standardChartMap K
              (LocalSectionRatioChart.toStandardAffineChart (ratioChart j))
  local_zero_of_section0_vanishes :
    ∀ i (x : cover.obj i),
      evalData.eval ((cover.map i).base x) section0 = 0 →
        (standardChartToP1HomOfRingHom K (localChartRingHom i)).base x =
          schemeCarrierPoint K MarkedPointLabel.zero
  local_section0_vanishes_of_zero :
    ∀ i (x : cover.obj i),
      (standardChartToP1HomOfRingHom K (localChartRingHom i)).base x =
          schemeCarrierPoint K MarkedPointLabel.zero →
        evalData.eval ((cover.map i).base x) section0 = 0

namespace TrivializedSectionRatioData

variable {C : Scheme.{u}}
variable (D : TrivializedSectionRatioData K C V)

/-- The standard `P1` chart selected on a local trivializing open. -/
def chart (i : D.cover.J) : StandardAffineChart :=
  LocalSectionRatioChart.toStandardAffineChart (D.ratioChart i)

theorem chart_eq (i : D.cover.J) :
    D.chart i = LocalSectionRatioChart.toStandardAffineChart (D.ratioChart i) := rfl

/-- The local regular quotient equation supplied by the trivialization. -/
theorem local_ratio_mul_denominator_eq_numerator (i : D.cover.J) :
    D.localSectionRatio i *
        LocalSectionRatioChart.denominator (D.ratioChart i)
          (D.localSection0 i) (D.localSection1 i) =
      LocalSectionRatioChart.numerator (D.ratioChart i)
        (D.localSection0 i) (D.localSection1 i) :=
  D.local_ratio_spec i

/-- Expanded coordinate pullback statement for the local chart ring map. -/
theorem localChartRingHom_coordinate_eq_ratio (i : D.cover.J) :
    D.localChartRingHom i (standardChartCoordinate K (D.chart i)) =
      D.localSectionRatio i := by
  simpa [chart, standardChartCoordinateSection] using
    D.localChartCoordinate_eq_ratio i

/-- Forget local trivialized-section algebra to the section-ratio chart
package. -/
def toSectionRatioProjectiveLineSectionData :
    SectionRatioProjectiveLineSectionData K C V where
  evalData := D.evalData
  section0 := D.section0
  section1 := D.section1
  no_common_zero := D.no_common_zero
  cover := D.cover
  chart := D.chart
  localSectionRatio := D.localSectionRatio
  localChartRingHom := D.localChartRingHom
  localChartCoordinate_eq_ratio := by
    intro i
    simpa [chart] using D.localChartCoordinate_eq_ratio i
  local_compat := by
    intro i j
    simpa [chart] using D.local_compat i j
  local_zero_of_section0_vanishes := by
    intro i x hx
    simpa [chart] using D.local_zero_of_section0_vanishes i x hx
  local_section0_vanishes_of_zero := by
    intro i x hx
    exact D.local_section0_vanishes_of_zero i x (by simpa [chart] using hx)

/-- The local map to `P1` obtained from the trivialized section-ratio data. -/
def localHom (i : D.cover.J) : D.cover.obj i ⟶ P1 K :=
  D.toSectionRatioProjectiveLineSectionData.localHom i

def globalHom : C ⟶ P1 K :=
  D.toSectionRatioProjectiveLineSectionData.globalHom

theorem toSectionRatioProjectiveLineSectionData_globalHom :
    D.toSectionRatioProjectiveLineSectionData.globalHom = D.globalHom := rfl

@[reassoc]
theorem cover_map_globalHom (i : D.cover.J) :
    D.cover.map i ≫ D.globalHom = D.localHom i := by
  exact D.toSectionRatioProjectiveLineSectionData.cover_map_globalHom i

theorem globalHom_base_of_cover (i : D.cover.J) (x : D.cover.obj i) :
    D.globalHom.base ((D.cover.map i).base x) = (D.localHom i).base x := by
  exact D.toSectionRatioProjectiveLineSectionData.globalHom_base_of_cover i x

theorem global_zero_of_section0_vanishes
    (x : C) (hx : D.evalData.eval x D.section0 = 0) :
    D.globalHom.base x = schemeCarrierPoint K MarkedPointLabel.zero := by
  exact D.toSectionRatioProjectiveLineSectionData.global_zero_of_section0_vanishes x hx

theorem section0_vanishes_of_global_zero
    (x : C)
    (hx : D.globalHom.base x = schemeCarrierPoint K MarkedPointLabel.zero) :
    D.evalData.eval x D.section0 = 0 := by
  exact D.toSectionRatioProjectiveLineSectionData.section0_vanishes_of_global_zero x hx

/-- The first section vanishes exactly on the zero fiber of the trivialized
section-ratio projective-line morphism. -/
theorem section0_vanishes_iff_globalHom_eq_zero (x : C) :
    D.evalData.eval x D.section0 = 0 ↔
      D.globalHom.base x = schemeCarrierPoint K MarkedPointLabel.zero := by
  constructor
  · exact D.global_zero_of_section0_vanishes x
  · exact D.section0_vanishes_of_global_zero x

/-- The first section is nonzero exactly away from the zero fiber of the
trivialized section-ratio projective-line morphism. -/
theorem section0_nonzero_iff_globalHom_ne_zero (x : C) :
    D.evalData.eval x D.section0 ≠ 0 ↔
      D.globalHom.base x ≠ schemeCarrierPoint K MarkedPointLabel.zero := by
  constructor
  · intro hsection hzero
    exact hsection (D.section0_vanishes_of_global_zero x hzero)
  · intro hzero hsection
    exact hzero (D.global_zero_of_section0_vanishes x hsection)

def toProjectiveLineSectionPair : ProjectiveLineSectionPair K C V :=
  D.toSectionRatioProjectiveLineSectionData.toProjectiveLineSectionPair

theorem toSectionRatioProjectiveLineSectionData_toProjectiveLineSectionPair :
    D.toSectionRatioProjectiveLineSectionData.toProjectiveLineSectionPair =
      D.toProjectiveLineSectionPair := rfl

theorem toProjectiveLineSectionPair_hom :
    D.toProjectiveLineSectionPair.hom = D.globalHom := rfl

theorem toProjectiveLineSectionPair_maps_section0_zero_to_marked
    {x : C} (hx : D.evalData.eval x D.section0 = 0) :
    D.toProjectiveLineSectionPair.hom.base x ∈ markedSchemePointSet K := by
  exact D.toProjectiveLineSectionPair.maps_section0_zero_to_marked hx

end TrivializedSectionRatioData

/-- A unit-denominator version of the local trivialized-section package.  This
is the algebraic shape supplied on opens where one of the two local section
representatives is invertible: the local ratio is constructed as
`numerator * denominator⁻¹`, rather than assumed as a primitive field. -/
structure TrivializedUnitSectionRatioData
    (K : Type u) [Field K] (C : Scheme.{u})
    (V : Type w) [AddCommGroup V] [Module K V] where
  evalData : RRSectionEvaluationData K C V
  section0 : V
  section1 : V
  no_common_zero : HasNoCommonZero evalData section0 section1
  cover : C.OpenCover
  ratioChart : cover.J → LocalSectionRatioChart
  localSection0 : ∀ i : cover.J, Γ(cover.obj i, ⊤)
  localSection1 : ∀ i : cover.J, Γ(cover.obj i, ⊤)
  denominatorUnit : ∀ i : cover.J, (Γ(cover.obj i, ⊤))ˣ
  denominatorUnit_spec :
    ∀ i : cover.J,
      LocalSectionRatioChart.denominator (ratioChart i)
        (localSection0 i) (localSection1 i) = (denominatorUnit i : Γ(cover.obj i, ⊤))
  localChartRingHom :
    ∀ i : cover.J,
      CommRingCat.of
        (standardChartRing K (LocalSectionRatioChart.toStandardAffineChart (ratioChart i))) ⟶
          Γ(cover.obj i, ⊤)
  localChartCoordinate_eq_unitRatio :
    ∀ i : cover.J,
      standardChartCoordinateSection K (localChartRingHom i) =
        LocalSectionRatioChart.unitRatio (ratioChart i)
          (localSection0 i) (localSection1 i) (denominatorUnit i)
  local_compat :
    ∀ i j : cover.J,
      (pullback.fst (cover.map i) (cover.map j) ≫
          standardChartHomOfRingHom K (localChartRingHom i)) ≫
            standardChartMap K
              (LocalSectionRatioChart.toStandardAffineChart (ratioChart i)) =
        (pullback.snd (cover.map i) (cover.map j) ≫
          standardChartHomOfRingHom K (localChartRingHom j)) ≫
            standardChartMap K
              (LocalSectionRatioChart.toStandardAffineChart (ratioChart j))
  local_zero_of_section0_vanishes :
    ∀ i (x : cover.obj i),
      evalData.eval ((cover.map i).base x) section0 = 0 →
        (standardChartToP1HomOfRingHom K (localChartRingHom i)).base x =
          schemeCarrierPoint K MarkedPointLabel.zero
  local_section0_vanishes_of_zero :
    ∀ i (x : cover.obj i),
      (standardChartToP1HomOfRingHom K (localChartRingHom i)).base x =
          schemeCarrierPoint K MarkedPointLabel.zero →
        evalData.eval ((cover.map i).base x) section0 = 0

namespace TrivializedUnitSectionRatioData

variable {C : Scheme.{u}}
variable (D : TrivializedUnitSectionRatioData K C V)

/-- The standard `P1` chart selected on a local trivializing open. -/
def chart (i : D.cover.J) : StandardAffineChart :=
  LocalSectionRatioChart.toStandardAffineChart (D.ratioChart i)

/-- The regular ratio constructed from the unit denominator. -/
def localSectionRatio (i : D.cover.J) : Γ(D.cover.obj i, ⊤) :=
  LocalSectionRatioChart.unitRatio (D.ratioChart i)
    (D.localSection0 i) (D.localSection1 i) (D.denominatorUnit i)

theorem denominator_eq_unit (i : D.cover.J) :
    LocalSectionRatioChart.denominator (D.ratioChart i)
        (D.localSection0 i) (D.localSection1 i) =
      (D.denominatorUnit i : Γ(D.cover.obj i, ⊤)) :=
  D.denominatorUnit_spec i

/-- The unit-constructed local ratio satisfies the quotient equation. -/
theorem local_ratio_mul_denominator_eq_numerator (i : D.cover.J) :
    D.localSectionRatio i *
        LocalSectionRatioChart.denominator (D.ratioChart i)
          (D.localSection0 i) (D.localSection1 i) =
      LocalSectionRatioChart.numerator (D.ratioChart i)
        (D.localSection0 i) (D.localSection1 i) := by
  exact LocalSectionRatioChart.unitRatio_mul_denominator_eq_numerator
    (D.ratioChart i) (D.localSection0 i) (D.localSection1 i)
    (D.denominatorUnit i) (D.denominator_eq_unit i)

theorem localChartCoordinate_eq_ratio (i : D.cover.J) :
    standardChartCoordinateSection K (D.localChartRingHom i) =
      D.localSectionRatio i := by
  simpa [localSectionRatio] using D.localChartCoordinate_eq_unitRatio i

/-- Forget unit-denominator data to the ratio-equation trivialized package. -/
def toTrivializedSectionRatioData :
    TrivializedSectionRatioData K C V where
  evalData := D.evalData
  section0 := D.section0
  section1 := D.section1
  no_common_zero := D.no_common_zero
  cover := D.cover
  ratioChart := D.ratioChart
  localSection0 := D.localSection0
  localSection1 := D.localSection1
  localSectionRatio := D.localSectionRatio
  local_ratio_spec := D.local_ratio_mul_denominator_eq_numerator
  localChartRingHom := D.localChartRingHom
  localChartCoordinate_eq_ratio := D.localChartCoordinate_eq_ratio
  local_compat := D.local_compat
  local_zero_of_section0_vanishes := D.local_zero_of_section0_vanishes
  local_section0_vanishes_of_zero := D.local_section0_vanishes_of_zero

def globalHom : C ⟶ P1 K :=
  D.toTrivializedSectionRatioData.globalHom

theorem toTrivializedSectionRatioData_globalHom :
    D.toTrivializedSectionRatioData.globalHom = D.globalHom := rfl

def toProjectiveLineSectionPair : ProjectiveLineSectionPair K C V :=
  D.toTrivializedSectionRatioData.toProjectiveLineSectionPair

theorem toTrivializedSectionRatioData_toProjectiveLineSectionPair :
    D.toTrivializedSectionRatioData.toProjectiveLineSectionPair =
      D.toProjectiveLineSectionPair := rfl

theorem toProjectiveLineSectionPair_hom :
    D.toProjectiveLineSectionPair.hom = D.globalHom := rfl

/-- The first section vanishes exactly on the zero fiber of the
unit-denominator trivialized projective-line morphism. -/
theorem section0_vanishes_iff_globalHom_eq_zero (x : C) :
    D.evalData.eval x D.section0 = 0 ↔
      D.globalHom.base x = schemeCarrierPoint K MarkedPointLabel.zero := by
  exact D.toProjectiveLineSectionPair.section0_vanishes_iff_hom_eq_zero x

/-- The first section is nonzero exactly away from the zero fiber of the
unit-denominator trivialized projective-line morphism. -/
theorem section0_nonzero_iff_globalHom_ne_zero (x : C) :
    D.evalData.eval x D.section0 ≠ 0 ↔
      D.globalHom.base x ≠ schemeCarrierPoint K MarkedPointLabel.zero := by
  exact D.toProjectiveLineSectionPair.section0_nonzero_iff_hom_ne_zero x

theorem toProjectiveLineSectionPair_maps_section0_zero_to_marked
    {x : C} (hx : D.evalData.eval x D.section0 = 0) :
    D.toProjectiveLineSectionPair.hom.base x ∈ markedSchemePointSet K := by
  exact D.toProjectiveLineSectionPair.maps_section0_zero_to_marked hx

end TrivializedUnitSectionRatioData

/-- A denominator-is-unit version of the local trivialized-section package.
This is closer to the output of basic-open and trivialization arguments: they
usually prove that the selected local denominator is invertible, rather than
constructing the `Units` value by hand. -/
structure TrivializedIsUnitSectionRatioData
    (K : Type u) [Field K] (C : Scheme.{u})
    (V : Type w) [AddCommGroup V] [Module K V] where
  evalData : RRSectionEvaluationData K C V
  section0 : V
  section1 : V
  no_common_zero : HasNoCommonZero evalData section0 section1
  cover : C.OpenCover
  ratioChart : cover.J → LocalSectionRatioChart
  localSection0 : ∀ i : cover.J, Γ(cover.obj i, ⊤)
  localSection1 : ∀ i : cover.J, Γ(cover.obj i, ⊤)
  denominator_isUnit :
    ∀ i : cover.J,
      IsUnit (LocalSectionRatioChart.denominator (ratioChart i)
        (localSection0 i) (localSection1 i))
  localChartRingHom :
    ∀ i : cover.J,
      CommRingCat.of
        (standardChartRing K (LocalSectionRatioChart.toStandardAffineChart (ratioChart i))) ⟶
          Γ(cover.obj i, ⊤)
  localChartCoordinate_eq_unitRatio :
    ∀ i : cover.J,
      standardChartCoordinateSection K (localChartRingHom i) =
        LocalSectionRatioChart.unitRatio (ratioChart i)
          (localSection0 i) (localSection1 i) ((denominator_isUnit i).unit)
  local_compat :
    ∀ i j : cover.J,
      (pullback.fst (cover.map i) (cover.map j) ≫
          standardChartHomOfRingHom K (localChartRingHom i)) ≫
            standardChartMap K
              (LocalSectionRatioChart.toStandardAffineChart (ratioChart i)) =
        (pullback.snd (cover.map i) (cover.map j) ≫
          standardChartHomOfRingHom K (localChartRingHom j)) ≫
            standardChartMap K
              (LocalSectionRatioChart.toStandardAffineChart (ratioChart j))
  local_zero_of_section0_vanishes :
    ∀ i (x : cover.obj i),
      evalData.eval ((cover.map i).base x) section0 = 0 →
        (standardChartToP1HomOfRingHom K (localChartRingHom i)).base x =
          schemeCarrierPoint K MarkedPointLabel.zero
  local_section0_vanishes_of_zero :
    ∀ i (x : cover.obj i),
      (standardChartToP1HomOfRingHom K (localChartRingHom i)).base x =
          schemeCarrierPoint K MarkedPointLabel.zero →
        evalData.eval ((cover.map i).base x) section0 = 0

namespace TrivializedIsUnitSectionRatioData

variable {C : Scheme.{u}}
variable (D : TrivializedIsUnitSectionRatioData K C V)

/-- The explicit unit extracted from the denominator-is-unit proof. -/
def denominatorUnit (i : D.cover.J) : (Γ(D.cover.obj i, ⊤))ˣ :=
  (D.denominator_isUnit i).unit

theorem denominator_eq_unit (i : D.cover.J) :
    LocalSectionRatioChart.denominator (D.ratioChart i)
        (D.localSection0 i) (D.localSection1 i) =
      (D.denominatorUnit i : Γ(D.cover.obj i, ⊤)) := by
  exact (D.denominator_isUnit i).unit_spec.symm

/-- Forget denominator-is-unit data to the explicit unit-denominator package. -/
def toTrivializedUnitSectionRatioData :
    TrivializedUnitSectionRatioData K C V where
  evalData := D.evalData
  section0 := D.section0
  section1 := D.section1
  no_common_zero := D.no_common_zero
  cover := D.cover
  ratioChart := D.ratioChart
  localSection0 := D.localSection0
  localSection1 := D.localSection1
  denominatorUnit := D.denominatorUnit
  denominatorUnit_spec := D.denominator_eq_unit
  localChartRingHom := D.localChartRingHom
  localChartCoordinate_eq_unitRatio := by
    intro i
    simpa [denominatorUnit] using D.localChartCoordinate_eq_unitRatio i
  local_compat := D.local_compat
  local_zero_of_section0_vanishes := D.local_zero_of_section0_vanishes
  local_section0_vanishes_of_zero := D.local_section0_vanishes_of_zero

def localSectionRatio (i : D.cover.J) : Γ(D.cover.obj i, ⊤) :=
  D.toTrivializedUnitSectionRatioData.localSectionRatio i

theorem local_ratio_mul_denominator_eq_numerator (i : D.cover.J) :
    D.localSectionRatio i *
        LocalSectionRatioChart.denominator (D.ratioChart i)
          (D.localSection0 i) (D.localSection1 i) =
      LocalSectionRatioChart.numerator (D.ratioChart i)
        (D.localSection0 i) (D.localSection1 i) := by
  exact D.toTrivializedUnitSectionRatioData.local_ratio_mul_denominator_eq_numerator i

theorem localChartCoordinate_eq_ratio (i : D.cover.J) :
    standardChartCoordinateSection K (D.localChartRingHom i) =
      D.localSectionRatio i := by
  exact D.toTrivializedUnitSectionRatioData.localChartCoordinate_eq_ratio i

def globalHom : C ⟶ P1 K :=
  D.toTrivializedUnitSectionRatioData.globalHom

theorem toTrivializedUnitSectionRatioData_globalHom :
    D.toTrivializedUnitSectionRatioData.globalHom = D.globalHom := rfl

def toProjectiveLineSectionPair : ProjectiveLineSectionPair K C V :=
  D.toTrivializedUnitSectionRatioData.toProjectiveLineSectionPair

theorem toTrivializedUnitSectionRatioData_toProjectiveLineSectionPair :
    D.toTrivializedUnitSectionRatioData.toProjectiveLineSectionPair =
      D.toProjectiveLineSectionPair := rfl

theorem toProjectiveLineSectionPair_hom :
    D.toProjectiveLineSectionPair.hom = D.globalHom := rfl

/-- The first section vanishes exactly on the zero fiber of the
denominator-is-unit trivialized projective-line morphism. -/
theorem section0_vanishes_iff_globalHom_eq_zero (x : C) :
    D.evalData.eval x D.section0 = 0 ↔
      D.globalHom.base x = schemeCarrierPoint K MarkedPointLabel.zero := by
  exact D.toProjectiveLineSectionPair.section0_vanishes_iff_hom_eq_zero x

/-- The first section is nonzero exactly away from the zero fiber of the
denominator-is-unit trivialized projective-line morphism. -/
theorem section0_nonzero_iff_globalHom_ne_zero (x : C) :
    D.evalData.eval x D.section0 ≠ 0 ↔
      D.globalHom.base x ≠ schemeCarrierPoint K MarkedPointLabel.zero := by
  exact D.toProjectiveLineSectionPair.section0_nonzero_iff_hom_ne_zero x

theorem toProjectiveLineSectionPair_maps_section0_zero_to_marked
    {x : C} (hx : D.evalData.eval x D.section0 = 0) :
    D.toProjectiveLineSectionPair.hom.base x ∈ markedSchemePointSet K := by
  exact D.toProjectiveLineSectionPair.maps_section0_zero_to_marked hx

end TrivializedIsUnitSectionRatioData

/-- The two-open cover attached to a pair of global functions satisfying a
Bezout equation.  The first open uses `section0` as denominator, the second
uses `section1`. -/
def twoSectionBezoutCover
    (C : Scheme.{u}) (s0 s1 a b : Γ(C, ⊤))
    (h : a * s0 + b * s1 = 1) :
    C.OpenCover :=
  Schemes.twoSectionBasicOpenCoverOfLinearCombination C s0 s1 a b h

/-- Universe-lifted version of the two-element family.  Mathlib's scheme
gluing API currently accepts covers whose index universe matches the scheme
universe, while the canonical two-element cover is indexed by `Fin 2` in
universe `0`. -/
def twoElementFamilyLifted {R : Type*} (x y : R) : ULift.{u} (Fin 2) → R :=
  fun i => Schemes.twoElementFamily x y i.down

@[simp]
theorem twoElementFamilyLifted_down {R : Type*}
    (x y : R) (i : ULift.{u} (Fin 2)) :
    twoElementFamilyLifted x y i = Schemes.twoElementFamily x y i.down := rfl

/-- A lifted two-section family satisfying a Bezout identity still spans the
unit ideal. -/
theorem ideal_span_range_twoElementFamilyLifted_eq_top_of_linear_combination
    {R : Type*} [CommSemiring R] (x y a b : R)
    (h : a * x + b * y = 1) :
    Ideal.span (Set.range (twoElementFamilyLifted x y :
      ULift.{u} (Fin 2) → R)) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  rw [← h]
  have hx :
      x ∈ Ideal.span (Set.range (twoElementFamilyLifted x y :
        ULift.{u} (Fin 2) → R)) :=
    Ideal.subset_span ⟨ULift.up (0 : Fin 2), by
      rfl⟩
  have hy :
      y ∈ Ideal.span (Set.range (twoElementFamilyLifted x y :
        ULift.{u} (Fin 2) → R)) :=
    Ideal.subset_span ⟨ULift.up (1 : Fin 2), by
      rfl⟩
  exact Ideal.add_mem _
    (Ideal.mul_mem_left _ a hx)
    (Ideal.mul_mem_left _ b hy)

/-- The universe-lifted two-basic-open cover attached to a pair of global
sections satisfying a Bezout equation. -/
def twoSectionBasicOpenCoverOfLinearCombinationLifted
    (X : Scheme.{u}) (s0 s1 a b : Γ(X, ⊤))
    (h : a * s0 + b * s1 = 1) :
    Scheme.OpenCover.{u, u} X :=
  Schemes.basicOpenCoverOfSpanEqTop X (twoElementFamilyLifted s0 s1 :
    ULift.{u} (Fin 2) → Γ(X, ⊤))
    (ideal_span_range_twoElementFamilyLifted_eq_top_of_linear_combination
      s0 s1 a b h)

/-- Universe-lifted two-open Bezout cover.  This is definitionally the same
basic-open family as `twoSectionBezoutCover`, but indexed by `ULift (Fin 2)`
so that it can be passed to `Scheme.Cover.glueMorphisms`. -/
def twoSectionBezoutCoverLifted
    (C : Scheme.{u}) (s0 s1 a b : Γ(C, ⊤))
    (h : a * s0 + b * s1 = 1) :
    Scheme.OpenCover.{u, u} C :=
  twoSectionBasicOpenCoverOfLinearCombinationLifted C s0 s1 a b h

/-- Chart choices for the two basic opens of a two-section Bezout cover. -/
def twoSectionRatioChart : Fin 2 → LocalSectionRatioChart
  | 0 => LocalSectionRatioChart.section0
  | 1 => LocalSectionRatioChart.section1

@[simp]
theorem twoSectionRatioChart_zero :
    twoSectionRatioChart 0 = LocalSectionRatioChart.section0 := rfl

@[simp]
theorem twoSectionRatioChart_one :
    twoSectionRatioChart 1 = LocalSectionRatioChart.section1 := rfl

/-- The first global function restricted to one member of the two-section
Bezout cover. -/
def twoSectionLocalSection0
    (C : Scheme.{u}) (s0 s1 a b : Γ(C, ⊤))
    (h : a * s0 + b * s1 = 1) (i : Fin 2) :
    Γ((twoSectionBezoutCover C s0 s1 a b h).obj i, ⊤) :=
  Schemes.basicOpenTopRestrict C (Schemes.twoElementFamily s0 s1 i) s0

/-- The second global function restricted to one member of the two-section
Bezout cover. -/
def twoSectionLocalSection1
    (C : Scheme.{u}) (s0 s1 a b : Γ(C, ⊤))
    (h : a * s0 + b * s1 = 1) (i : Fin 2) :
    Γ((twoSectionBezoutCover C s0 s1 a b h).obj i, ⊤) :=
  Schemes.basicOpenTopRestrict C (Schemes.twoElementFamily s0 s1 i) s1

/-- The first global function restricted to a member of the universe-lifted
two-section Bezout cover. -/
def twoSectionLocalSection0Lifted
    (C : Scheme.{u}) (s0 s1 a b : Γ(C, ⊤))
    (h : a * s0 + b * s1 = 1) (i : ULift.{u} (Fin 2)) :
    Γ((twoSectionBezoutCoverLifted C s0 s1 a b h).obj i, ⊤) := by
  simpa [twoSectionBezoutCoverLifted,
    twoSectionBasicOpenCoverOfLinearCombinationLifted,
    Schemes.basicOpenCoverOfSpanEqTop, twoElementFamilyLifted] using
    (Schemes.basicOpenTopRestrict C (Schemes.twoElementFamily s0 s1 i.down) s0)

/-- The second global function restricted to a member of the universe-lifted
two-section Bezout cover. -/
def twoSectionLocalSection1Lifted
    (C : Scheme.{u}) (s0 s1 a b : Γ(C, ⊤))
    (h : a * s0 + b * s1 = 1) (i : ULift.{u} (Fin 2)) :
    Γ((twoSectionBezoutCoverLifted C s0 s1 a b h).obj i, ⊤) := by
  simpa [twoSectionBezoutCoverLifted,
    twoSectionBasicOpenCoverOfLinearCombinationLifted,
    Schemes.basicOpenCoverOfSpanEqTop, twoElementFamilyLifted] using
    (Schemes.basicOpenTopRestrict C (Schemes.twoElementFamily s0 s1 i.down) s1)

/-- On each member of the two-section Bezout cover, the selected denominator is
a unit. -/
theorem twoSectionLocal_denominator_isUnit
    (C : Scheme.{u}) (s0 s1 a b : Γ(C, ⊤))
    (h : a * s0 + b * s1 = 1) (i : Fin 2) :
    IsUnit (LocalSectionRatioChart.denominator (twoSectionRatioChart i)
      (twoSectionLocalSection0 C s0 s1 a b h i)
      (twoSectionLocalSection1 C s0 s1 a b h i)) := by
  fin_cases i
  · dsimp [twoSectionRatioChart, twoSectionLocalSection0, twoSectionLocalSection1,
      Schemes.basicOpenTopRestrict]
    apply RingHom.isUnit_map
    simpa [Schemes.basicOpenTopRestrict] using
      Schemes.isUnit_basicOpenTopRestrict_self C s0
  · dsimp [twoSectionRatioChart, twoSectionLocalSection0, twoSectionLocalSection1,
      Schemes.basicOpenTopRestrict]
    apply RingHom.isUnit_map
    simpa [Schemes.basicOpenTopRestrict] using
      Schemes.isUnit_basicOpenTopRestrict_self C s1

/-- On each member of the universe-lifted two-section Bezout cover, the
selected denominator is a unit. -/
theorem twoSectionLocal_denominator_isUnit_lifted
    (C : Scheme.{u}) (s0 s1 a b : Γ(C, ⊤))
    (h : a * s0 + b * s1 = 1) (i : ULift.{u} (Fin 2)) :
    IsUnit (LocalSectionRatioChart.denominator (twoSectionRatioChart i.down)
      (twoSectionLocalSection0Lifted C s0 s1 a b h i)
      (twoSectionLocalSection1Lifted C s0 s1 a b h i)) := by
  rcases i with ⟨i⟩
  simpa [twoSectionLocalSection0Lifted, twoSectionLocalSection1Lifted,
    twoSectionBezoutCoverLifted, twoSectionBasicOpenCoverOfLinearCombinationLifted,
    twoElementFamilyLifted] using
      twoSectionLocal_denominator_isUnit C s0 s1 a b h i

/-- The local `K`-algebra structures on the canonical two-section Bezout cover
induced by a structure morphism `C ⟶ Spec K`. -/
noncomputable def twoSectionBezoutLocalSectionAlgebraOfStructure
    (K : Type u) [Field K] (C : Scheme.{u})
    (structureMap : C ⟶ Spec (CommRingCat.of K))
    (s0 s1 a b : Γ(C, ⊤)) (h : a * s0 + b * s1 = 1) :
    ∀ i : Fin 2,
      Algebra K Γ((twoSectionBezoutCover C s0 s1 a b h).obj i, ⊤) :=
  openCoverLocalSectionAlgebra K (twoSectionBezoutCover C s0 s1 a b h) structureMap

/-- The canonical regular affine coordinate on a member of the two-section
Bezout cover, obtained by dividing the selected numerator by the selected
unit denominator. -/
noncomputable def twoSectionLocalUnitRatio
    (C : Scheme.{u}) (s0 s1 a b : Γ(C, ⊤))
    (h : a * s0 + b * s1 = 1) (i : Fin 2) :
    Γ((twoSectionBezoutCover C s0 s1 a b h).obj i, ⊤) :=
  LocalSectionRatioChart.unitRatio (twoSectionRatioChart i)
    (twoSectionLocalSection0 C s0 s1 a b h i)
    (twoSectionLocalSection1 C s0 s1 a b h i)
    ((twoSectionLocal_denominator_isUnit C s0 s1 a b h i).unit)

/-- Given a `K`-algebra structure on the local section ring of a two-section
Bezout basic open, the canonical local ratio determines the corresponding
standard-chart coordinate-ring map. -/
noncomputable def twoSectionLocalChartRingHomOfAlgebra
    (K : Type u) [Field K] (C : Scheme.{u})
    (s0 s1 a b : Γ(C, ⊤)) (h : a * s0 + b * s1 = 1)
    (localSectionAlgebra :
      ∀ i : Fin 2, Algebra K Γ((twoSectionBezoutCover C s0 s1 a b h).obj i, ⊤))
    (i : Fin 2) :
    CommRingCat.of
      (standardChartRing K
        (LocalSectionRatioChart.toStandardAffineChart (twoSectionRatioChart i))) ⟶
      Γ((twoSectionBezoutCover C s0 s1 a b h).obj i, ⊤) :=
  standardChartRingCatHomOfCoordinateOfAlgebra K
    (LocalSectionRatioChart.toStandardAffineChart (twoSectionRatioChart i))
    (localSectionAlgebra i)
    (twoSectionLocalUnitRatio C s0 s1 a b h i)

/-- The chart-ring map constructed from the canonical two-section local ratio
pulls back the standard affine coordinate to that ratio. -/
theorem twoSectionLocalChartRingHomOfAlgebra_coordinate_eq_unitRatio
    (K : Type u) [Field K] (C : Scheme.{u})
    (s0 s1 a b : Γ(C, ⊤)) (h : a * s0 + b * s1 = 1)
    (localSectionAlgebra :
      ∀ i : Fin 2, Algebra K Γ((twoSectionBezoutCover C s0 s1 a b h).obj i, ⊤))
    (i : Fin 2) :
    standardChartCoordinateSection K
        (twoSectionLocalChartRingHomOfAlgebra K C s0 s1 a b h localSectionAlgebra i) =
      twoSectionLocalUnitRatio C s0 s1 a b h i := by
  change
    twoSectionLocalChartRingHomOfAlgebra K C s0 s1 a b h localSectionAlgebra i
      (standardChartCoordinate K
        (LocalSectionRatioChart.toStandardAffineChart (twoSectionRatioChart i))) =
      twoSectionLocalUnitRatio C s0 s1 a b h i
  exact standardChartRingCatHomOfCoordinateOfAlgebra_apply_coordinate K
    (LocalSectionRatioChart.toStandardAffineChart (twoSectionRatioChart i))
    (localSectionAlgebra i) (twoSectionLocalUnitRatio C s0 s1 a b h i)

/-- Specialization of the constructed local chart-ring map to the local
`K`-algebras induced by a structure morphism `C ⟶ Spec K`. -/
theorem twoSectionLocalChartRingHomOfStructure_coordinate_eq_unitRatio
    (K : Type u) [Field K] (C : Scheme.{u})
    (structureMap : C ⟶ Spec (CommRingCat.of K))
    (s0 s1 a b : Γ(C, ⊤)) (h : a * s0 + b * s1 = 1)
    (i : Fin 2) :
    standardChartCoordinateSection K
        (twoSectionLocalChartRingHomOfAlgebra K C s0 s1 a b h
          (twoSectionBezoutLocalSectionAlgebraOfStructure K C structureMap s0 s1 a b h) i) =
      twoSectionLocalUnitRatio C s0 s1 a b h i := by
  exact
    twoSectionLocalChartRingHomOfAlgebra_coordinate_eq_unitRatio K C s0 s1 a b h
      (twoSectionBezoutLocalSectionAlgebraOfStructure K C structureMap s0 s1 a b h) i

/-- Canonical two-basic-open version of the denominator-is-unit
projective-section package.  It fixes the cover, chart choices, and local
section representatives from a Bezout pair of global functions; the remaining
fields are the chart coordinate ring maps, their overlap compatibility, and
the pointwise zero criteria needed for the final `P1` morphism. -/
structure TwoSectionBezoutTrivializedIsUnitData
    (K : Type u) [Field K] (C : Scheme.{u})
    (V : Type w) [AddCommGroup V] [Module K V] where
  evalData : RRSectionEvaluationData K C V
  section0 : V
  section1 : V
  no_common_zero : HasNoCommonZero evalData section0 section1
  globalSection0 : Γ(C, ⊤)
  globalSection1 : Γ(C, ⊤)
  bezoutCoeff0 : Γ(C, ⊤)
  bezoutCoeff1 : Γ(C, ⊤)
  bezout :
    bezoutCoeff0 * globalSection0 + bezoutCoeff1 * globalSection1 = 1
  localChartRingHom :
    ∀ i : Fin 2,
      CommRingCat.of
        (standardChartRing K
          (LocalSectionRatioChart.toStandardAffineChart (twoSectionRatioChart i))) ⟶
          Γ((twoSectionBezoutCover C globalSection0 globalSection1
            bezoutCoeff0 bezoutCoeff1 bezout).obj i, ⊤)
  localChartCoordinate_eq_unitRatio :
    ∀ i : Fin 2,
      standardChartCoordinateSection K (localChartRingHom i) =
        LocalSectionRatioChart.unitRatio (twoSectionRatioChart i)
          (twoSectionLocalSection0 C globalSection0 globalSection1
            bezoutCoeff0 bezoutCoeff1 bezout i)
          (twoSectionLocalSection1 C globalSection0 globalSection1
            bezoutCoeff0 bezoutCoeff1 bezout i)
          ((twoSectionLocal_denominator_isUnit C globalSection0 globalSection1
            bezoutCoeff0 bezoutCoeff1 bezout i).unit)
  local_compat :
    ∀ i j : Fin 2,
      (pullback.fst
          ((twoSectionBezoutCover C globalSection0 globalSection1
            bezoutCoeff0 bezoutCoeff1 bezout).map i)
          ((twoSectionBezoutCover C globalSection0 globalSection1
            bezoutCoeff0 bezoutCoeff1 bezout).map j) ≫
          standardChartHomOfRingHom K (localChartRingHom i)) ≫
            standardChartMap K
              (LocalSectionRatioChart.toStandardAffineChart (twoSectionRatioChart i)) =
        (pullback.snd
          ((twoSectionBezoutCover C globalSection0 globalSection1
            bezoutCoeff0 bezoutCoeff1 bezout).map i)
          ((twoSectionBezoutCover C globalSection0 globalSection1
            bezoutCoeff0 bezoutCoeff1 bezout).map j) ≫
          standardChartHomOfRingHom K (localChartRingHom j)) ≫
            standardChartMap K
              (LocalSectionRatioChart.toStandardAffineChart (twoSectionRatioChart j))
  local_zero_of_section0_vanishes :
    ∀ i (x : (twoSectionBezoutCover C globalSection0 globalSection1
        bezoutCoeff0 bezoutCoeff1 bezout).obj i),
      evalData.eval (((twoSectionBezoutCover C globalSection0 globalSection1
        bezoutCoeff0 bezoutCoeff1 bezout).map i).base x) section0 = 0 →
        (standardChartToP1HomOfRingHom K (localChartRingHom i)).base x =
          schemeCarrierPoint K MarkedPointLabel.zero
  local_section0_vanishes_of_zero :
    ∀ i (x : (twoSectionBezoutCover C globalSection0 globalSection1
        bezoutCoeff0 bezoutCoeff1 bezout).obj i),
      (standardChartToP1HomOfRingHom K (localChartRingHom i)).base x =
          schemeCarrierPoint K MarkedPointLabel.zero →
        evalData.eval (((twoSectionBezoutCover C globalSection0 globalSection1
          bezoutCoeff0 bezoutCoeff1 bezout).map i).base x) section0 = 0

namespace TwoSectionBezoutTrivializedIsUnitData

variable {C : Scheme.{u}}
variable (D : TwoSectionBezoutTrivializedIsUnitData K C V)

/-- The canonical two-basic-open cover of the two chosen global functions. -/
def cover : C.OpenCover :=
  twoSectionBezoutCover C D.globalSection0 D.globalSection1
    D.bezoutCoeff0 D.bezoutCoeff1 D.bezout

/-- The chart selected on each member of the two-basic-open cover. -/
def ratioChart : D.cover.J → LocalSectionRatioChart :=
  twoSectionRatioChart

/-- The first local section representative on each canonical basic open. -/
def localSection0 (i : D.cover.J) : Γ(D.cover.obj i, ⊤) :=
  twoSectionLocalSection0 C D.globalSection0 D.globalSection1
    D.bezoutCoeff0 D.bezoutCoeff1 D.bezout i

/-- The second local section representative on each canonical basic open. -/
def localSection1 (i : D.cover.J) : Γ(D.cover.obj i, ⊤) :=
  twoSectionLocalSection1 C D.globalSection0 D.globalSection1
    D.bezoutCoeff0 D.bezoutCoeff1 D.bezout i

/-- The selected denominator is a unit on each canonical basic open. -/
theorem denominator_isUnit (i : D.cover.J) :
    IsUnit (LocalSectionRatioChart.denominator (D.ratioChart i)
      (D.localSection0 i) (D.localSection1 i)) := by
  exact twoSectionLocal_denominator_isUnit C D.globalSection0 D.globalSection1
    D.bezoutCoeff0 D.bezoutCoeff1 D.bezout i

/-- Assemble the canonical two-open data into the denominator-is-unit
trivialized section-ratio package. -/
def toTrivializedIsUnitSectionRatioData :
    TrivializedIsUnitSectionRatioData K C V where
  evalData := D.evalData
  section0 := D.section0
  section1 := D.section1
  no_common_zero := D.no_common_zero
  cover := D.cover
  ratioChart := D.ratioChart
  localSection0 := D.localSection0
  localSection1 := D.localSection1
  denominator_isUnit := D.denominator_isUnit
  localChartRingHom := D.localChartRingHom
  localChartCoordinate_eq_unitRatio := by
    intro i
    simpa [cover, ratioChart, localSection0, localSection1,
      denominator_isUnit] using D.localChartCoordinate_eq_unitRatio i
  local_compat := by
    intro i j
    simpa [cover, ratioChart] using D.local_compat i j
  local_zero_of_section0_vanishes := by
    intro i x hx
    simpa [cover] using D.local_zero_of_section0_vanishes i x hx
  local_section0_vanishes_of_zero := by
    intro i x hx
    exact D.local_section0_vanishes_of_zero i x (by simpa [cover] using hx)

theorem toTrivialized_localSection0 (i : D.cover.J) :
    (D.toTrivializedIsUnitSectionRatioData).localSection0 i =
      D.localSection0 i := rfl

theorem toTrivialized_localSection1 (i : D.cover.J) :
    (D.toTrivializedIsUnitSectionRatioData).localSection1 i =
      D.localSection1 i := rfl

theorem toTrivialized_localChartRingHom (i : D.cover.J) :
    (D.toTrivializedIsUnitSectionRatioData).localChartRingHom i =
      D.localChartRingHom i := rfl

theorem toTrivialized_localSectionRatio_eq_unitRatio (i : D.cover.J) :
    (D.toTrivializedIsUnitSectionRatioData).localSectionRatio i =
      LocalSectionRatioChart.unitRatio (D.ratioChart i)
        (D.localSection0 i) (D.localSection1 i) ((D.denominator_isUnit i).unit) := rfl

theorem toTrivialized_localChartCoordinate_eq_ratio (i : D.cover.J) :
    standardChartCoordinateSection K
        ((D.toTrivializedIsUnitSectionRatioData).localChartRingHom i) =
      (D.toTrivializedIsUnitSectionRatioData).localSectionRatio i := by
  exact (D.toTrivializedIsUnitSectionRatioData).localChartCoordinate_eq_ratio i

theorem toTrivialized_local_ratio_mul_denominator_eq_numerator (i : D.cover.J) :
    (D.toTrivializedIsUnitSectionRatioData).localSectionRatio i *
        LocalSectionRatioChart.denominator
          ((D.toTrivializedIsUnitSectionRatioData).ratioChart i)
          ((D.toTrivializedIsUnitSectionRatioData).localSection0 i)
          ((D.toTrivializedIsUnitSectionRatioData).localSection1 i) =
      LocalSectionRatioChart.numerator
        ((D.toTrivializedIsUnitSectionRatioData).ratioChart i)
        ((D.toTrivializedIsUnitSectionRatioData).localSection0 i)
        ((D.toTrivializedIsUnitSectionRatioData).localSection1 i) := by
  exact (D.toTrivializedIsUnitSectionRatioData).local_ratio_mul_denominator_eq_numerator i

/-- Universe-lifted version of the canonical two-basic-open cover.  This is the
same pair of basic opens as `D.cover`, with the index type lifted from `Fin 2`
to `ULift (Fin 2)` so that Mathlib's gluing API can construct the global
projective-line morphism. -/
def coverLifted : Scheme.OpenCover.{u, u} C :=
  twoSectionBezoutCoverLifted C D.globalSection0 D.globalSection1
    D.bezoutCoeff0 D.bezoutCoeff1 D.bezout

/-- The chart selected on each member of the universe-lifted two-basic-open
cover. -/
def ratioChartLifted (i : D.coverLifted.J) : LocalSectionRatioChart :=
  twoSectionRatioChart i.down

/-- The first local section representative on each member of the
universe-lifted canonical basic-open cover. -/
def localSection0Lifted (i : D.coverLifted.J) : Γ(D.coverLifted.obj i, ⊤) :=
  twoSectionLocalSection0Lifted C D.globalSection0 D.globalSection1
    D.bezoutCoeff0 D.bezoutCoeff1 D.bezout i

/-- The second local section representative on each member of the
universe-lifted canonical basic-open cover. -/
def localSection1Lifted (i : D.coverLifted.J) : Γ(D.coverLifted.obj i, ⊤) :=
  twoSectionLocalSection1Lifted C D.globalSection0 D.globalSection1
    D.bezoutCoeff0 D.bezoutCoeff1 D.bezout i

/-- The selected denominator is a unit on each member of the universe-lifted
canonical basic-open cover. -/
theorem denominator_isUnit_lifted (i : D.coverLifted.J) :
    IsUnit (LocalSectionRatioChart.denominator (D.ratioChartLifted i)
      (D.localSection0Lifted i) (D.localSection1Lifted i)) := by
  exact twoSectionLocal_denominator_isUnit_lifted C D.globalSection0 D.globalSection1
    D.bezoutCoeff0 D.bezoutCoeff1 D.bezout i

/-- Assemble the canonical two-open data into the denominator-is-unit
trivialized section-ratio package over the universe-lifted cover. -/
def toTrivializedIsUnitSectionRatioDataLifted :
    TrivializedIsUnitSectionRatioData K C V where
  evalData := D.evalData
  section0 := D.section0
  section1 := D.section1
  no_common_zero := D.no_common_zero
  cover := D.coverLifted
  ratioChart := D.ratioChartLifted
  localSection0 := D.localSection0Lifted
  localSection1 := D.localSection1Lifted
  denominator_isUnit := D.denominator_isUnit_lifted
  localChartRingHom := fun i => by
    simpa [coverLifted, twoSectionBezoutCoverLifted,
      twoSectionBasicOpenCoverOfLinearCombinationLifted,
      Schemes.basicOpenCoverOfSpanEqTop, twoElementFamilyLifted] using
      D.localChartRingHom i.down
  localChartCoordinate_eq_unitRatio := by
    intro i
    rcases i with ⟨i⟩
    simpa [coverLifted, ratioChartLifted, localSection0Lifted,
      localSection1Lifted, denominator_isUnit_lifted, twoSectionLocalSection0Lifted,
      twoSectionLocalSection1Lifted, twoSectionBezoutCoverLifted,
      twoSectionBasicOpenCoverOfLinearCombinationLifted,
      Schemes.basicOpenCoverOfSpanEqTop, twoElementFamilyLifted] using
      D.localChartCoordinate_eq_unitRatio i
  local_compat := by
    intro i j
    rcases i with ⟨i⟩
    rcases j with ⟨j⟩
    simpa [coverLifted, ratioChartLifted, twoSectionBezoutCoverLifted,
      twoSectionBasicOpenCoverOfLinearCombinationLifted,
      Schemes.basicOpenCoverOfSpanEqTop, twoElementFamilyLifted] using
      D.local_compat i j
  local_zero_of_section0_vanishes := by
    intro i x hx
    rcases i with ⟨i⟩
    simpa [coverLifted, twoSectionBezoutCoverLifted,
      twoSectionBasicOpenCoverOfLinearCombinationLifted,
      Schemes.basicOpenCoverOfSpanEqTop, twoElementFamilyLifted] using
      D.local_zero_of_section0_vanishes i x hx
  local_section0_vanishes_of_zero := by
    intro i x hx
    rcases i with ⟨i⟩
    exact D.local_section0_vanishes_of_zero i x (by
      simpa [coverLifted, twoSectionBezoutCoverLifted,
        twoSectionBasicOpenCoverOfLinearCombinationLifted,
        Schemes.basicOpenCoverOfSpanEqTop, twoElementFamilyLifted] using hx)

/-- The global projective-line morphism assembled from the canonical
two-section Bezout data. -/
def globalHom : C ⟶ P1 K :=
  D.toTrivializedIsUnitSectionRatioDataLifted.globalHom

theorem toTrivializedIsUnitSectionRatioDataLifted_globalHom :
    D.toTrivializedIsUnitSectionRatioDataLifted.globalHom = D.globalHom := rfl

/-- The projective-section pair extracted from the canonical two-section Bezout
data. -/
def toProjectiveLineSectionPair : ProjectiveLineSectionPair K C V :=
  D.toTrivializedIsUnitSectionRatioDataLifted.toProjectiveLineSectionPair

theorem toTrivializedIsUnitSectionRatioDataLifted_toProjectiveLineSectionPair :
    D.toTrivializedIsUnitSectionRatioDataLifted.toProjectiveLineSectionPair =
      D.toProjectiveLineSectionPair := rfl

theorem toProjectiveLineSectionPair_hom :
    D.toProjectiveLineSectionPair.hom = D.globalHom := rfl

theorem toProjectiveLineSectionPair_evalData :
    D.toProjectiveLineSectionPair.evalData = D.evalData := rfl

theorem toProjectiveLineSectionPair_section0 :
    D.toProjectiveLineSectionPair.section0 = D.section0 := rfl

theorem toProjectiveLineSectionPair_section1 :
    D.toProjectiveLineSectionPair.section1 = D.section1 := rfl

/-- The first section vanishes exactly on the zero fiber of the two-section
Bezout projective-line morphism. -/
theorem section0_vanishes_iff_globalHom_eq_zero (x : C) :
    D.evalData.eval x D.section0 = 0 ↔
      D.globalHom.base x = schemeCarrierPoint K MarkedPointLabel.zero := by
  exact D.toProjectiveLineSectionPair.section0_vanishes_iff_hom_eq_zero x

/-- The first section is nonzero exactly away from the zero fiber of the
two-section Bezout projective-line morphism. -/
theorem section0_nonzero_iff_globalHom_ne_zero (x : C) :
    D.evalData.eval x D.section0 ≠ 0 ↔
      D.globalHom.base x ≠ schemeCarrierPoint K MarkedPointLabel.zero := by
  exact D.toProjectiveLineSectionPair.section0_nonzero_iff_hom_ne_zero x

theorem toProjectiveLineSectionPair_maps_section0_zero_to_marked
    {x : C} (hx : D.evalData.eval x D.section0 = 0) :
    D.toProjectiveLineSectionPair.hom.base x ∈ markedSchemePointSet K := by
  exact D.toProjectiveLineSectionPair.maps_section0_zero_to_marked hx

end TwoSectionBezoutTrivializedIsUnitData

/-- Canonical two-basic-open section data where the local chart-ring maps are
constructed from the canonical unit ratios.  Compared with
`TwoSectionBezoutTrivializedIsUnitData`, this removes `localChartRingHom` and
`localChartCoordinate_eq_unitRatio` as fields; the remaining assumptions are
the local `K`-algebra structures, overlap compatibility of the resulting
maps, and the zero-fiber criterion. -/
structure TwoSectionBezoutConstructedTrivializedIsUnitData
    (K : Type u) [Field K] (C : Scheme.{u})
    (V : Type w) [AddCommGroup V] [Module K V] where
  evalData : RRSectionEvaluationData K C V
  section0 : V
  section1 : V
  no_common_zero : HasNoCommonZero evalData section0 section1
  globalSection0 : Γ(C, ⊤)
  globalSection1 : Γ(C, ⊤)
  bezoutCoeff0 : Γ(C, ⊤)
  bezoutCoeff1 : Γ(C, ⊤)
  bezout :
    bezoutCoeff0 * globalSection0 + bezoutCoeff1 * globalSection1 = 1
  localSectionAlgebra :
    ∀ i : Fin 2,
      Algebra K Γ((twoSectionBezoutCover C globalSection0 globalSection1
        bezoutCoeff0 bezoutCoeff1 bezout).obj i, ⊤)
  local_compat :
    ∀ i j : Fin 2,
      (pullback.fst
          ((twoSectionBezoutCover C globalSection0 globalSection1
            bezoutCoeff0 bezoutCoeff1 bezout).map i)
          ((twoSectionBezoutCover C globalSection0 globalSection1
            bezoutCoeff0 bezoutCoeff1 bezout).map j) ≫
          standardChartHomOfRingHom K
            (twoSectionLocalChartRingHomOfAlgebra K C globalSection0 globalSection1
              bezoutCoeff0 bezoutCoeff1 bezout localSectionAlgebra i)) ≫
            standardChartMap K
              (LocalSectionRatioChart.toStandardAffineChart (twoSectionRatioChart i)) =
        (pullback.snd
          ((twoSectionBezoutCover C globalSection0 globalSection1
            bezoutCoeff0 bezoutCoeff1 bezout).map i)
          ((twoSectionBezoutCover C globalSection0 globalSection1
            bezoutCoeff0 bezoutCoeff1 bezout).map j) ≫
          standardChartHomOfRingHom K
            (twoSectionLocalChartRingHomOfAlgebra K C globalSection0 globalSection1
              bezoutCoeff0 bezoutCoeff1 bezout localSectionAlgebra j)) ≫
            standardChartMap K
              (LocalSectionRatioChart.toStandardAffineChart (twoSectionRatioChart j))
  local_zero_of_section0_vanishes :
    ∀ i (x : (twoSectionBezoutCover C globalSection0 globalSection1
        bezoutCoeff0 bezoutCoeff1 bezout).obj i),
      evalData.eval (((twoSectionBezoutCover C globalSection0 globalSection1
        bezoutCoeff0 bezoutCoeff1 bezout).map i).base x) section0 = 0 →
        (standardChartToP1HomOfRingHom K
          (twoSectionLocalChartRingHomOfAlgebra K C globalSection0 globalSection1
            bezoutCoeff0 bezoutCoeff1 bezout localSectionAlgebra i)).base x =
          schemeCarrierPoint K MarkedPointLabel.zero
  local_section0_vanishes_of_zero :
    ∀ i (x : (twoSectionBezoutCover C globalSection0 globalSection1
        bezoutCoeff0 bezoutCoeff1 bezout).obj i),
      (standardChartToP1HomOfRingHom K
          (twoSectionLocalChartRingHomOfAlgebra K C globalSection0 globalSection1
            bezoutCoeff0 bezoutCoeff1 bezout localSectionAlgebra i)).base x =
          schemeCarrierPoint K MarkedPointLabel.zero →
        evalData.eval (((twoSectionBezoutCover C globalSection0 globalSection1
          bezoutCoeff0 bezoutCoeff1 bezout).map i).base x) section0 = 0

namespace TwoSectionBezoutConstructedTrivializedIsUnitData

variable {C : Scheme.{u}}
variable (D : TwoSectionBezoutConstructedTrivializedIsUnitData K C V)

/-- The canonical two-basic-open cover of the two chosen global functions. -/
def cover : C.OpenCover :=
  twoSectionBezoutCover C D.globalSection0 D.globalSection1
    D.bezoutCoeff0 D.bezoutCoeff1 D.bezout

/-- The chart selected on each member of the two-basic-open cover. -/
def ratioChart : D.cover.J → LocalSectionRatioChart :=
  twoSectionRatioChart

/-- The first local section representative on each canonical basic open. -/
def localSection0 (i : D.cover.J) : Γ(D.cover.obj i, ⊤) :=
  twoSectionLocalSection0 C D.globalSection0 D.globalSection1
    D.bezoutCoeff0 D.bezoutCoeff1 D.bezout i

/-- The second local section representative on each canonical basic open. -/
def localSection1 (i : D.cover.J) : Γ(D.cover.obj i, ⊤) :=
  twoSectionLocalSection1 C D.globalSection0 D.globalSection1
    D.bezoutCoeff0 D.bezoutCoeff1 D.bezout i

/-- The selected denominator is a unit on each canonical basic open. -/
theorem denominator_isUnit (i : D.cover.J) :
    IsUnit (LocalSectionRatioChart.denominator (D.ratioChart i)
      (D.localSection0 i) (D.localSection1 i)) := by
  exact twoSectionLocal_denominator_isUnit C D.globalSection0 D.globalSection1
    D.bezoutCoeff0 D.bezoutCoeff1 D.bezout i

/-- The canonical unit ratio on a basic open. -/
noncomputable def localSectionRatio (i : D.cover.J) : Γ(D.cover.obj i, ⊤) :=
  twoSectionLocalUnitRatio C D.globalSection0 D.globalSection1
    D.bezoutCoeff0 D.bezoutCoeff1 D.bezout i

/-- The constructed chart coordinate-ring map on a canonical basic open. -/
noncomputable def localChartRingHom (i : D.cover.J) :
    CommRingCat.of
      (standardChartRing K
        (LocalSectionRatioChart.toStandardAffineChart (D.ratioChart i))) ⟶
      Γ(D.cover.obj i, ⊤) :=
  twoSectionLocalChartRingHomOfAlgebra K C D.globalSection0 D.globalSection1
    D.bezoutCoeff0 D.bezoutCoeff1 D.bezout D.localSectionAlgebra i

/-- The constructed chart-ring map pulls back the distinguished affine
coordinate to the canonical unit ratio. -/
theorem localChartCoordinate_eq_unitRatio (i : D.cover.J) :
    standardChartCoordinateSection K (D.localChartRingHom i) =
      LocalSectionRatioChart.unitRatio (D.ratioChart i)
        (D.localSection0 i) (D.localSection1 i) ((D.denominator_isUnit i).unit) := by
  simpa [localChartRingHom, localSectionRatio, twoSectionLocalUnitRatio,
    ratioChart, localSection0, localSection1, denominator_isUnit] using
    twoSectionLocalChartRingHomOfAlgebra_coordinate_eq_unitRatio K C
      D.globalSection0 D.globalSection1 D.bezoutCoeff0 D.bezoutCoeff1
      D.bezout D.localSectionAlgebra i

/-- Forget constructed chart maps to the canonical two-section Bezout package
with explicit chart-ring maps. -/
noncomputable def toTwoSectionBezoutTrivializedIsUnitData :
    TwoSectionBezoutTrivializedIsUnitData K C V where
  evalData := D.evalData
  section0 := D.section0
  section1 := D.section1
  no_common_zero := D.no_common_zero
  globalSection0 := D.globalSection0
  globalSection1 := D.globalSection1
  bezoutCoeff0 := D.bezoutCoeff0
  bezoutCoeff1 := D.bezoutCoeff1
  bezout := D.bezout
  localChartRingHom := D.localChartRingHom
  localChartCoordinate_eq_unitRatio := D.localChartCoordinate_eq_unitRatio
  local_compat := D.local_compat
  local_zero_of_section0_vanishes := D.local_zero_of_section0_vanishes
  local_section0_vanishes_of_zero := D.local_section0_vanishes_of_zero

/-- The global projective-line morphism assembled from the constructed
two-section Bezout data. -/
noncomputable def globalHom : C ⟶ P1 K :=
  D.toTwoSectionBezoutTrivializedIsUnitData.globalHom

theorem toTwoSectionBezoutTrivializedIsUnitData_globalHom :
    D.toTwoSectionBezoutTrivializedIsUnitData.globalHom = D.globalHom := rfl

/-- The projective-section pair extracted from the constructed two-section
Bezout data. -/
noncomputable def toProjectiveLineSectionPair : ProjectiveLineSectionPair K C V :=
  D.toTwoSectionBezoutTrivializedIsUnitData.toProjectiveLineSectionPair

theorem toTwoSectionBezoutTrivializedIsUnitData_toProjectiveLineSectionPair :
    D.toTwoSectionBezoutTrivializedIsUnitData.toProjectiveLineSectionPair =
      D.toProjectiveLineSectionPair := rfl

theorem toProjectiveLineSectionPair_hom :
    D.toProjectiveLineSectionPair.hom = D.globalHom := rfl

theorem toProjectiveLineSectionPair_evalData :
    D.toProjectiveLineSectionPair.evalData = D.evalData := rfl

theorem toProjectiveLineSectionPair_section0 :
    D.toProjectiveLineSectionPair.section0 = D.section0 := rfl

theorem toProjectiveLineSectionPair_section1 :
    D.toProjectiveLineSectionPair.section1 = D.section1 := rfl

/-- The first section vanishes exactly on the zero fiber of the constructed
two-section Bezout projective-line morphism. -/
theorem section0_vanishes_iff_globalHom_eq_zero (x : C) :
    D.evalData.eval x D.section0 = 0 ↔
      D.globalHom.base x = schemeCarrierPoint K MarkedPointLabel.zero := by
  exact
    D.toTwoSectionBezoutTrivializedIsUnitData.section0_vanishes_iff_globalHom_eq_zero x

/-- The first section is nonzero exactly away from the zero fiber of the
constructed two-section Bezout projective-line morphism. -/
theorem section0_nonzero_iff_globalHom_ne_zero (x : C) :
    D.evalData.eval x D.section0 ≠ 0 ↔
      D.globalHom.base x ≠ schemeCarrierPoint K MarkedPointLabel.zero := by
  exact
    D.toTwoSectionBezoutTrivializedIsUnitData.section0_nonzero_iff_globalHom_ne_zero x

theorem toProjectiveLineSectionPair_maps_section0_zero_to_marked
    {x : C} (hx : D.evalData.eval x D.section0 = 0) :
    D.toProjectiveLineSectionPair.hom.base x ∈ markedSchemePointSet K := by
  exact D.toProjectiveLineSectionPair.maps_section0_zero_to_marked hx

end TwoSectionBezoutConstructedTrivializedIsUnitData

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

/-- Build a projective-section finite marked family from scheme-level
section-controlled finite marked Belyi data, once projective-line section pairs
are supplied whose underlying maps and section evaluations match that data. -/
def ofSectionControlledFiniteMarkedBelyiData
    (D : SectionControlledFiniteMarkedBelyiData K C V)
    (pair : V → ProjectiveLineSectionPair K C V)
    (hmap : ∀ s x, (D.map s).hom.base x = (pair s).hom.base x)
    (heval :
      ∀ s x, (pair s).evalData.eval x (pair s).section0 =
        D.evalPackage.eval x s) :
    ProjectiveSectionFiniteMarkedFamily K C V where
  evalPackage := D.evalPackage
  hmarkedOpen := D.hmarkedOpen
  pair := pair
  map := D.map
  map_base_eq_pair := hmap
  pair_section0_eval_eq_index := heval
  nonzero_avoids_marked := by
    intro T s hs
    exact D.nonzero_avoids_marked hs

@[simp]
theorem ofSectionControlledFiniteMarkedBelyiData_evalPackage
    (D : SectionControlledFiniteMarkedBelyiData K C V)
    (pair : V → ProjectiveLineSectionPair K C V)
    (hmap : ∀ s x, (D.map s).hom.base x = (pair s).hom.base x)
    (heval :
      ∀ s x, (pair s).evalData.eval x (pair s).section0 =
        D.evalPackage.eval x s) :
    (ofSectionControlledFiniteMarkedBelyiData D pair hmap heval).evalPackage =
      D.evalPackage := rfl

@[simp]
theorem ofSectionControlledFiniteMarkedBelyiData_pair
    (D : SectionControlledFiniteMarkedBelyiData K C V)
    (pair : V → ProjectiveLineSectionPair K C V)
    (hmap : ∀ s x, (D.map s).hom.base x = (pair s).hom.base x)
    (heval :
      ∀ s x, (pair s).evalData.eval x (pair s).section0 =
        D.evalPackage.eval x s)
    (s : V) :
    (ofSectionControlledFiniteMarkedBelyiData D pair hmap heval).pair s =
      pair s := rfl

@[simp]
theorem ofSectionControlledFiniteMarkedBelyiData_map_apply
    (D : SectionControlledFiniteMarkedBelyiData K C V)
    (pair : V → ProjectiveLineSectionPair K C V)
    (hmap : ∀ s x, (D.map s).hom.base x = (pair s).hom.base x)
    (heval :
      ∀ s x, (pair s).evalData.eval x (pair s).section0 =
        D.evalPackage.eval x s)
    (s : V) :
    (ofSectionControlledFiniteMarkedBelyiData D pair hmap heval).map s =
      D.map s := rfl

/-- Each projective-section finite marked family map is finite. -/
theorem map_finite_hom
    (s : V) :
    IsFinite (F.map s).hom :=
  SchemeBelyi.FiniteBelyiMap.isFinite_hom (F.map s)

/-- Each projective-section finite marked family map is dominant. -/
theorem map_isDominant_hom
    (s : V) :
    IsDominant (F.map s).hom :=
  SchemeBelyi.FiniteBelyiMap.isDominant_hom (F.map s)

/-- Each projective-section finite marked family map has dense range on
underlying spaces. -/
theorem map_denseRange_hom
    (s : V) :
    DenseRange (F.map s).hom.base :=
  SchemeBelyi.FiniteBelyiMap.denseRange_hom (F.map s)

/-- Each projective-section finite marked family map is etale over the marked
branch-complement open. -/
theorem map_isEtale_restrict_branchOpen
    (s : V) :
    IsEtale ((F.map s).hom ∣_
      (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.isEtale_restrict_branchOpen (F.map s)

/-- The branch-open restriction of each projective-section map is finite. -/
theorem map_isFinite_restrict_branchOpen
    (s : V) :
    IsFinite ((F.map s).hom ∣_
      (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.isFinite_restrict_branchOpen (F.map s)

/-- The branch-open restriction of each projective-section map is affine. -/
theorem map_isAffineHom_restrict_branchOpen
    (s : V) :
    IsAffineHom ((F.map s).hom ∣_
      (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.isAffineHom_restrict_branchOpen (F.map s)

/-- The branch-open restriction of each projective-section map is integral. -/
theorem map_isIntegralHom_restrict_branchOpen
    (s : V) :
    IsIntegralHom ((F.map s).hom ∣_
      (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.isIntegralHom_restrict_branchOpen (F.map s)

/-- The branch-open restriction of each projective-section map is locally of
finite type. -/
theorem map_locallyOfFiniteType_restrict_branchOpen
    (s : V) :
    LocallyOfFiniteType ((F.map s).hom ∣_
      (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.locallyOfFiniteType_restrict_branchOpen (F.map s)

/-- The branch-open restriction of each projective-section map is separated. -/
theorem map_isSeparated_restrict_branchOpen
    (s : V) :
    IsSeparated ((F.map s).hom ∣_
      (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.isSeparated_restrict_branchOpen (F.map s)

/-- The branch-open restriction of each projective-section map is quasi-compact. -/
theorem map_quasiCompact_restrict_branchOpen
    (s : V) :
    QuasiCompact ((F.map s).hom ∣_
      (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.quasiCompact_restrict_branchOpen (F.map s)

/-- Each projective-section finite marked family map is affine. -/
theorem map_isAffineHom_hom
    (s : V) :
    IsAffineHom (F.map s).hom :=
  SchemeBelyi.FiniteBelyiMap.isAffineHom_hom (F.map s)

/-- Each projective-section finite marked family map is integral. -/
theorem map_isIntegralHom_hom
    (s : V) :
    IsIntegralHom (F.map s).hom :=
  SchemeBelyi.FiniteBelyiMap.isIntegralHom_hom (F.map s)

/-- Each projective-section finite marked family map is locally of finite type. -/
theorem map_locallyOfFiniteType_hom
    (s : V) :
    LocallyOfFiniteType (F.map s).hom :=
  SchemeBelyi.FiniteBelyiMap.locallyOfFiniteType_hom (F.map s)

/-- Each projective-section finite marked family map is separated. -/
theorem map_isSeparated_hom
    (s : V) :
    IsSeparated (F.map s).hom :=
  SchemeBelyi.FiniteBelyiMap.isSeparated_hom (F.map s)

/-- Each projective-section finite marked family map is quasi-compact. -/
theorem map_quasiCompact_hom
    (s : V) :
    QuasiCompact (F.map s).hom :=
  SchemeBelyi.FiniteBelyiMap.quasiCompact_hom (F.map s)

theorem toFiniteMarkedBelyiExistence_mem_belyiOpen_iff
    [Infinite K] (s : V) (x : C) :
    x ∈ (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
      F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s ↔
      (F.map s).hom.base x ∉ markedSchemePointSet K := by
  exact
    SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence_mem_belyiOpen_iff
      K V F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence s x

theorem toFiniteMarkedBelyiExistence_belyiOpen_carrier
    [Infinite K] (s : V) :
    (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
      F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s =
      {x : C | (F.map s).hom.base x ∉ markedSchemePointSet K} := by
  exact
    SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence_belyiOpen_carrier
      K V F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence s

theorem toFiniteMarkedBelyiExistence_belyiOpen_eq_schemeBelyi
    [Infinite K] (s : V) :
    (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
      F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s =
      ((F.map s).toBelyiMap.belyiOpen : Set C) := by
  exact
    SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence_belyiOpen_eq_schemeBelyi
      K V F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence s

/-- If a selected projective section evaluates to zero at a point, the
corresponding finite Belyi map sends that point into the marked branch set. -/
theorem eval_zero_to_marked
    (s : V) {x : C} (hx : F.evalPackage.eval x s = 0) :
    (F.map s).hom.base x ∈ markedSchemePointSet K := by
  rw [F.map_base_eq_pair s x]
  exact (F.pair s).maps_section0_zero_to_marked
    (by
      rw [F.pair_section0_eval_eq_index s x]
      exact hx)

/-- If a selected projective section evaluates nontrivially at a point, the
corresponding finite Belyi map avoids the marked branch set at that point. -/
theorem eval_nonzero_avoids_marked
    (s : V) {x : C} (hx : F.evalPackage.eval x s ≠ 0) :
    (F.map s).hom.base x ∉ markedSchemePointSet K := by
  exact F.nonzero_avoids_marked (T := {x}) (s := s)
    (by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact hx)
    x (by simp)

/-- Finite disjoint-set conclusion after the projective-section construction
has supplied finite marked Belyi maps and branch avoidance. -/
theorem exists_for_finite_disjoint
    [Infinite K] {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V, (∀ x ∈ S, (F.map s).hom.base x ∈ markedSchemePointSet K) ∧
      ∀ x ∈ T, (F.map s).hom.base x ∉ markedSchemePointSet K := by
  exact F.toSectionControlledFiniteMarkedBelyiData.exists_for_finite_disjoint
    hS hT hdis

/-- Direct Belyi-open form of the finite disjoint-set conclusion: the selected
finite Belyi map has Belyi open containing `T` and avoiding `S`. -/
theorem exists_map_belyiOpen_controls
    [Infinite K] {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V, T ⊆ ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
      ((F.map s).toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  rcases F.exists_for_finite_disjoint hS hT hdis with ⟨s, hSmark, hTavoid⟩
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

/-- Direct same-map finite disjoint-set conclusion for projective-section
finite marked families: the selected finite Belyi map satisfies the marked
controls and its Belyi open contains `T` and avoids `S`. -/
theorem exists_map_controls_and_belyiOpen_controls
    [Infinite K] {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V,
      ((∀ x ∈ S, (F.map s).hom.base x ∈ markedSchemePointSet K) ∧
        ∀ x ∈ T, (F.map s).hom.base x ∉ markedSchemePointSet K) ∧
        T ⊆ ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
          ((F.map s).toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  rcases F.exists_for_finite_disjoint hS hT hdis with ⟨s, hSmark, hTavoid⟩
  refine ⟨s, ⟨hSmark, hTavoid⟩, ?_, ?_⟩
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

/-- Direct same-map finite disjoint-set conclusion for projective-section
finite marked families, with explicit openness of the selected source Belyi
open. -/
theorem exists_map_controls_and_isOpen_belyiOpen_controls
    [Infinite K] {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V,
      ((∀ x ∈ S, (F.map s).hom.base x ∈ markedSchemePointSet K) ∧
        ∀ x ∈ T, (F.map s).hom.base x ∉ markedSchemePointSet K) ∧
        IsOpen ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
          T ⊆ ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
            ((F.map s).toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  rcases F.exists_map_controls_and_belyiOpen_controls hS hT hdis with
    ⟨s, hcontrols, hTopen, hopenS⟩
  exact ⟨s, hcontrols, (F.map s).toBelyiMap.belyiOpen.2, hTopen, hopenS⟩

/-- Actual finite-map one-point finite-complement-open consequence for
projective-section finite marked families. -/
theorem exists_map_belyiOpen_inside_open_of_finite_complement
    [Infinite K]
    {U : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite) {x : C} (hxU : x ∈ U) :
    ∃ s : V,
      IsOpen ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
        x ∈ ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
          ((F.map s).toBelyiMap.belyiOpen : Set C) ⊆ U := by
  exact
    F.toSectionControlledFiniteMarkedBelyiData.exists_map_belyiOpen_inside_open_of_finite_complement
      hU hUcompl hxU

/-- Actual finite-map finite-set finite-complement-open consequence for
projective-section finite marked families. -/
theorem exists_map_belyiOpen_containing_finite_inside_open_of_finite_complement
    [Infinite K]
    {U T : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ s : V,
      IsOpen ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
        T ⊆ ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
          ((F.map s).toBelyiMap.belyiOpen : Set C) ⊆ U := by
  exact
    F.toSectionControlledFiniteMarkedBelyiData.exists_map_belyiOpen_containing_finite_inside_open_of_finite_complement
      hU hUcompl hT hTsub

/-- Actual finite-map finite-complement-open consequence retaining marked
controls for projective-section finite marked families. -/
theorem exists_map_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_finite_complement
    [Infinite K]
    {U T : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ s : V,
      ((∀ x ∈ Uᶜ, (F.map s).hom.base x ∈ markedSchemePointSet K) ∧
        ∀ x ∈ T, (F.map s).hom.base x ∉ markedSchemePointSet K) ∧
        IsOpen ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
          T ⊆ ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
            ((F.map s).toBelyiMap.belyiOpen : Set C) ⊆ U := by
  exact
    F.toSectionControlledFiniteMarkedBelyiData.exists_map_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_finite_complement
      hU hUcompl hT hTsub

/-- Actual finite-map nonempty-open finite-complement consequence retaining
marked controls for projective-section finite marked families. -/
theorem exists_map_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
    [Infinite K] [NonemptyOpenFiniteComplement C]
    {U T : Set C} (hU : IsOpen U) (hUne : U.Nonempty)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ s : V,
      ((∀ x ∈ Uᶜ, (F.map s).hom.base x ∈ markedSchemePointSet K) ∧
        ∀ x ∈ T, (F.map s).hom.base x ∉ markedSchemePointSet K) ∧
        IsOpen ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
          T ⊆ ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
            ((F.map s).toBelyiMap.belyiOpen : Set C) ⊆ U := by
  exact
    F.toSectionControlledFiniteMarkedBelyiData.exists_map_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
      hU hUne hT hTsub

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

/-- Corollary 1.2-style finite-set open consequence of the projective-section
finite marked family, inside the complement of a finite source set. -/
theorem exists_belyiOpen_containing_finite_inside_complement
    [Infinite K] [T1Space (P1 K)]
    {S T : Set C} (hS : S.Finite) (hT : T.Finite) (hdis : Disjoint S T) :
    ∃ s : V,
      IsOpen ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        T ⊆ ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ Sᶜ := by
  exact
    F.toSectionControlledFiniteMarkedBelyiData.exists_belyiOpen_containing_finite_inside_complement
      hS hT hdis

/-- Corollary 1.2-style one-point open consequence of the projective-section
finite marked family, with the finite complement supplied explicitly. -/
theorem exists_belyiOpen_inside_open_of_finite_complement
    [Infinite K] [T1Space (P1 K)]
    {U : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite) {x : C} (hxU : x ∈ U) :
    ∃ s : V,
      IsOpen ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        x ∈ ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ U := by
  exact
    F.toSectionControlledFiniteMarkedBelyiData.exists_belyiOpen_inside_open_of_finite_complement
      hU hUcompl hxU

/-- Corollary 1.2-style finite-set open consequence of the projective-section
finite marked family, with the finite complement supplied explicitly. -/
theorem exists_belyiOpen_containing_finite_inside_open_of_finite_complement
    [Infinite K] [T1Space (P1 K)]
    {U T : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ s : V,
      IsOpen ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        T ⊆ ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ U := by
  exact
    F.toSectionControlledFiniteMarkedBelyiData.exists_belyiOpen_containing_finite_inside_open_of_finite_complement
      hU hUcompl hT hTsub

/-- Corollary 1.2-style one-point open consequence of the projective-section
finite marked family in the curve-style finite-complement topology form. -/
theorem exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C]
    {U : Set C} (hU : IsOpen U) {x : C} (hxU : x ∈ U) :
    ∃ s : V,
      IsOpen ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        x ∈ ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ U := by
  exact
    F.toSectionControlledFiniteMarkedBelyiData.exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
      hU hxU

/-- Corollary 1.2-style finite-set open consequence of the projective-section
finite marked family in the curve-style finite-complement topology form. -/
theorem exists_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C]
    {U T : Set C} (hU : IsOpen U) (hUne : U.Nonempty)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ s : V,
      IsOpen ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        T ⊆ ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ U := by
  exact
    F.toSectionControlledFiniteMarkedBelyiData.exists_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
      hU hUne hT hTsub

/-- Direct finite tuple-subcover consequence of the projective-section finite
marked family. -/
theorem finite_subcover_on_complement
    [Infinite K] (κ : Type*) [Finite κ] [T1Space (P1 K)]
    {S : Set C} (hS : S.Finite) [CompactSpace (κ → {x : C // x ∉ S})] :
    ∃ t : Finset {s : V //
        (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedCoverData K V
          F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).sendsSetToBranch S s},
      (⋃ s ∈ t, ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedCoverData K V
            F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).complementCoverData S).tupleAvoidSet
              (κ := κ) s) =
        (Set.univ : Set (κ → {x : C // x ∉ S})) := by
  exact F.toSectionControlledFiniteMarkedBelyiData.finite_subcover_on_complement
    κ hS

/-- Direct finite tuple-subcover consequence of the projective-section finite
marked family, in membership form. -/
theorem finite_subcover_on_complement_forall
    [Infinite K] (κ : Type*) [Finite κ] [T1Space (P1 K)]
    {S : Set C} (hS : S.Finite) [CompactSpace (κ → {x : C // x ∉ S})] :
    ∃ t : Finset {s : V //
        (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedCoverData K V
          F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).sendsSetToBranch S s},
      ∀ x : κ → {x : C // x ∉ S},
        ∃ s ∈ t,
          x ∈ ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedCoverData K V
            F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).complementCoverData S).tupleAvoidSet
              (κ := κ) s := by
  exact F.toSectionControlledFiniteMarkedBelyiData.finite_subcover_on_complement_forall
    κ hS

/-- Direct finite tuple-subcover consequence of the projective-section finite
marked family, in concrete marked-avoidance form. -/
theorem finite_subcover_on_complement_forall_avoidance
    [Infinite K] (κ : Type*) [Finite κ] [T1Space (P1 K)]
    {S : Set C} (hS : S.Finite) [CompactSpace (κ → {x : C // x ∉ S})] :
    ∃ t : Finset {s : V //
        (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedCoverData K V
          F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).sendsSetToBranch S s},
      ∀ x : κ → {x : C // x ∉ S},
        ∃ s ∈ t, ∀ i, (F.map s.1).hom.base (x i).1 ∉ markedSchemePointSet K := by
  exact F.toSectionControlledFiniteMarkedBelyiData.finite_subcover_on_complement_forall_avoidance
    κ hS

/-- Compact-exhaustion cover bridge for projective-section finite marked
families. -/
theorem finite_compact_cover_by_belyiOpen_exhaustions
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    (Kex : ∀ s : V,
      CompactExhaustion ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s)) :
    ∃ t : Finset (V × ℕ),
      (∀ p ∈ t,
        IsCompact ((Subtype.val :
          (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
            (Kex p.1 p.2))) ∧
        (∀ p ∈ t,
          ((Subtype.val :
            (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
              F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
              (Kex p.1 p.2)) ⊆
                (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                  F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1) ∧
          (Set.univ : Set C) ⊆
            ⋃ p ∈ t,
              (Subtype.val :
                (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                  F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
                (Kex p.1 p.2) := by
  exact
    F.toSectionControlledFiniteMarkedBelyiData.finite_compact_cover_by_belyiOpen_exhaustions
      Kex

/-- Equality form of the compact-exhaustion cover bridge for projective-section
finite marked families. -/
theorem finite_compact_cover_by_belyiOpen_exhaustions_eq_univ
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    (Kex : ∀ s : V,
      CompactExhaustion ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s)) :
    ∃ t : Finset (V × ℕ),
      (∀ p ∈ t,
        IsCompact ((Subtype.val :
          (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
            (Kex p.1 p.2))) ∧
        (∀ p ∈ t,
          ((Subtype.val :
            (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
              F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
              (Kex p.1 p.2)) ⊆
                (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                  F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1) ∧
          (⋃ p ∈ t,
            (Subtype.val :
              (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
              (Kex p.1 p.2)) = (Set.univ : Set C) := by
  exact
    F.toSectionControlledFiniteMarkedBelyiData.finite_compact_cover_by_belyiOpen_exhaustions_eq_univ
      Kex

/-- Compact-cover bridge for projective-section finite marked families, with
compact exhaustions supplied by local compactness and second countability. -/
theorem finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    [LocallyCompactSpace C] [SecondCountableTopology C] :
    ∃ Kex : ∀ s : V,
      CompactExhaustion ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s),
      ∃ t : Finset (V × ℕ),
        (∀ p ∈ t,
          IsCompact ((Subtype.val :
            (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
              F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
              (Kex p.1 p.2))) ∧
          (∀ p ∈ t,
            ((Subtype.val :
              (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
                (Kex p.1 p.2)) ⊆
                  (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                    F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1) ∧
            (Set.univ : Set C) ⊆
              ⋃ p ∈ t,
                (Subtype.val :
                  (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                    F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
                  (Kex p.1 p.2) := by
  exact
    F.toSectionControlledFiniteMarkedBelyiData.finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact

/-- Equality form of the compact-cover bridge for projective-section finite
marked families, with compact exhaustions supplied by local compactness and
second countability. -/
theorem finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact_eq_univ
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    [LocallyCompactSpace C] [SecondCountableTopology C] :
    ∃ Kex : ∀ s : V,
      CompactExhaustion ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s),
      ∃ t : Finset (V × ℕ),
        (∀ p ∈ t,
          IsCompact ((Subtype.val :
            (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
              F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
              (Kex p.1 p.2))) ∧
          (∀ p ∈ t,
            ((Subtype.val :
              (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
                (Kex p.1 p.2)) ⊆
                  (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                    F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1) ∧
            (⋃ p ∈ t,
              (Subtype.val :
                (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                  F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
                (Kex p.1 p.2)) = (Set.univ : Set C) := by
  exact
    F.toSectionControlledFiniteMarkedBelyiData.finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact_eq_univ

/-- Compact-coordinate Corollary 3.2 bridge for projective-section finite
marked families. -/
theorem finite_compact_coordinate_sets_of_belyiOpen_exhaustions
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    [LocallyCompactSpace C] [SecondCountableTopology C]
    {κ : Type*} {Z : κ → Type*} [∀ j, TopologicalSpace (Z j)]
    (G : V → C → ((j : κ) → Z j))
    (hG : ∀ s, Continuous (G s))
    (A : (j : κ) → Set (Z j))
    (hGA : ∀ s x,
      x ∈ (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s →
        ∀ j, G s x j ∈ A j) :
    ∃ Kex : ∀ s : V,
      CompactExhaustion ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s),
      ∃ t : Finset (V × ℕ),
        ∃ H : (j : κ) → Set (Z j),
          (∀ j, IsCompact (H j)) ∧
            (∀ j, H j ⊆ A j) ∧
              (Set.univ : Set C) ⊆
                ⋃ p ∈ t,
                  (Subtype.val :
                    (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                      F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 →
                      C) ''
                    (Kex p.1 p.2) ∧
                ∀ p ∈ t, ∀ x,
                  x ∈ (Subtype.val :
                    (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                      F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 →
                      C) ''
                      (Kex p.1 p.2) →
                    ∀ j, G p.1 x j ∈ H j := by
  exact
    F.toSectionControlledFiniteMarkedBelyiData.finite_compact_coordinate_sets_of_belyiOpen_exhaustions
      G hG A hGA

end ProjectiveSectionFiniteMarkedFamily

/-- A concrete version of the finite marked family whose projective-section
maps are supplied by trivialized local section-ratio data.  This assembles the
line-bundle chart construction layer with the finite marked Belyi-map layer. -/
structure TrivializedProjectiveSectionFiniteMarkedFamily
    (K : Type u) [Field K] (C : Scheme.{u})
    (V : Type w) [AddCommGroup V] [Module K V] where
  evalPackage : RiemannRochFiniteEvaluationPackage K C V
  hmarkedOpen : IsOpen (markedSchemePointSet K)ᶜ
  trivialized : V → TrivializedSectionRatioData K C V
  map : V → SchemeBelyi.FiniteBelyiMap
    (SchemeBelyi.markedBelyiTarget K hmarkedOpen) C
  map_base_eq_globalHom :
    ∀ s x, (map s).hom.base x = (trivialized s).globalHom.base x
  trivialized_section0_eval_eq_index :
    ∀ s x, (trivialized s).evalData.eval x (trivialized s).section0 = evalPackage.eval x s
  nonzero_avoids_marked :
    ∀ {T : Set C} {s : V},
      evalPackage.toEvaluationData.nonzeroOnSet T s →
        ∀ x ∈ T, (map s).hom.base x ∉ markedSchemePointSet K

namespace TrivializedProjectiveSectionFiniteMarkedFamily

variable {C : Scheme.{u}}
variable (F : TrivializedProjectiveSectionFiniteMarkedFamily K C V)

/-- The projective-section pair attached to a section through its trivialized
local ratio data. -/
def pair (s : V) : ProjectiveLineSectionPair K C V :=
  (F.trivialized s).toProjectiveLineSectionPair

theorem pair_hom (s : V) :
    (F.pair s).hom = (F.trivialized s).globalHom := rfl

theorem map_base_eq_pair (s : V) (x : C) :
    (F.map s).hom.base x = (F.pair s).hom.base x := by
  exact F.map_base_eq_globalHom s x

theorem pair_section0_eval_eq_index (s : V) (x : C) :
    (F.pair s).evalData.eval x (F.pair s).section0 =
      F.evalPackage.eval x s := by
  exact F.trivialized_section0_eval_eq_index s x

/-- Forget the trivialized-ratio construction to the existing projective-section
finite marked family interface. -/
def toProjectiveSectionFiniteMarkedFamily :
    ProjectiveSectionFiniteMarkedFamily K C V where
  evalPackage := F.evalPackage
  hmarkedOpen := F.hmarkedOpen
  pair := F.pair
  map := F.map
  map_base_eq_pair := F.map_base_eq_pair
  pair_section0_eval_eq_index := F.pair_section0_eval_eq_index
  nonzero_avoids_marked := by
    intro T s hs
    exact F.nonzero_avoids_marked hs

theorem toProjectiveSectionFiniteMarkedFamily_map_apply
    (s : V) :
    F.toProjectiveSectionFiniteMarkedFamily.map s = F.map s := rfl

/-- Each trivialized-ratio finite marked family map is finite. -/
theorem map_finite_hom
    (s : V) :
    IsFinite (F.map s).hom :=
  SchemeBelyi.FiniteBelyiMap.isFinite_hom (F.map s)

/-- Each trivialized-ratio finite marked family map is dominant. -/
theorem map_isDominant_hom
    (s : V) :
    IsDominant (F.map s).hom :=
  SchemeBelyi.FiniteBelyiMap.isDominant_hom (F.map s)

/-- Each trivialized-ratio finite marked family map has dense range on
underlying spaces. -/
theorem map_denseRange_hom
    (s : V) :
    DenseRange (F.map s).hom.base :=
  SchemeBelyi.FiniteBelyiMap.denseRange_hom (F.map s)

/-- Each trivialized-ratio finite marked family map is etale over the marked
branch-complement open. -/
theorem map_isEtale_restrict_branchOpen
    (s : V) :
    IsEtale ((F.map s).hom ∣_
      (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.isEtale_restrict_branchOpen (F.map s)

/-- The branch-open restriction of each trivialized-ratio map is finite. -/
theorem map_isFinite_restrict_branchOpen
    (s : V) :
    IsFinite ((F.map s).hom ∣_
      (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.isFinite_restrict_branchOpen (F.map s)

/-- The branch-open restriction of each trivialized-ratio map is affine. -/
theorem map_isAffineHom_restrict_branchOpen
    (s : V) :
    IsAffineHom ((F.map s).hom ∣_
      (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.isAffineHom_restrict_branchOpen (F.map s)

/-- The branch-open restriction of each trivialized-ratio map is integral. -/
theorem map_isIntegralHom_restrict_branchOpen
    (s : V) :
    IsIntegralHom ((F.map s).hom ∣_
      (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.isIntegralHom_restrict_branchOpen (F.map s)

/-- The branch-open restriction of each trivialized-ratio map is locally of
finite type. -/
theorem map_locallyOfFiniteType_restrict_branchOpen
    (s : V) :
    LocallyOfFiniteType ((F.map s).hom ∣_
      (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.locallyOfFiniteType_restrict_branchOpen (F.map s)

/-- The branch-open restriction of each trivialized-ratio map is separated. -/
theorem map_isSeparated_restrict_branchOpen
    (s : V) :
    IsSeparated ((F.map s).hom ∣_
      (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.isSeparated_restrict_branchOpen (F.map s)

/-- The branch-open restriction of each trivialized-ratio map is quasi-compact. -/
theorem map_quasiCompact_restrict_branchOpen
    (s : V) :
    QuasiCompact ((F.map s).hom ∣_
      (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.quasiCompact_restrict_branchOpen (F.map s)

/-- Each trivialized-ratio finite marked family map is affine. -/
theorem map_isAffineHom_hom
    (s : V) :
    IsAffineHom (F.map s).hom :=
  SchemeBelyi.FiniteBelyiMap.isAffineHom_hom (F.map s)

/-- Each trivialized-ratio finite marked family map is integral. -/
theorem map_isIntegralHom_hom
    (s : V) :
    IsIntegralHom (F.map s).hom :=
  SchemeBelyi.FiniteBelyiMap.isIntegralHom_hom (F.map s)

/-- Each trivialized-ratio finite marked family map is locally of finite type. -/
theorem map_locallyOfFiniteType_hom
    (s : V) :
    LocallyOfFiniteType (F.map s).hom :=
  SchemeBelyi.FiniteBelyiMap.locallyOfFiniteType_hom (F.map s)

/-- Each trivialized-ratio finite marked family map is separated. -/
theorem map_isSeparated_hom
    (s : V) :
    IsSeparated (F.map s).hom :=
  SchemeBelyi.FiniteBelyiMap.isSeparated_hom (F.map s)

/-- Each trivialized-ratio finite marked family map is quasi-compact. -/
theorem map_quasiCompact_hom
    (s : V) :
    QuasiCompact (F.map s).hom :=
  SchemeBelyi.FiniteBelyiMap.quasiCompact_hom (F.map s)

theorem toFiniteMarkedBelyiExistence_mem_belyiOpen_iff
    [Infinite K] (s : V) (x : C) :
    x ∈ (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
      F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s ↔
      (F.map s).hom.base x ∉ markedSchemePointSet K := by
  exact
    ProjectiveSectionFiniteMarkedFamily.toFiniteMarkedBelyiExistence_mem_belyiOpen_iff
      F.toProjectiveSectionFiniteMarkedFamily s x

theorem toFiniteMarkedBelyiExistence_belyiOpen_carrier
    [Infinite K] (s : V) :
    (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
      F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s =
      {x : C | (F.map s).hom.base x ∉ markedSchemePointSet K} := by
  exact
    ProjectiveSectionFiniteMarkedFamily.toFiniteMarkedBelyiExistence_belyiOpen_carrier
      F.toProjectiveSectionFiniteMarkedFamily s

theorem toFiniteMarkedBelyiExistence_belyiOpen_eq_schemeBelyi
    [Infinite K] (s : V) :
    (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
      F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s =
      ((F.map s).toBelyiMap.belyiOpen : Set C) := by
  exact
    ProjectiveSectionFiniteMarkedFamily.toFiniteMarkedBelyiExistence_belyiOpen_eq_schemeBelyi
      F.toProjectiveSectionFiniteMarkedFamily s

/-- Pointwise zero-evaluation branch consequence for concrete trivialized-ratio
finite marked families. -/
theorem eval_zero_to_marked
    (s : V) {x : C} (hx : F.evalPackage.eval x s = 0) :
    (F.map s).hom.base x ∈ markedSchemePointSet K := by
  exact F.toProjectiveSectionFiniteMarkedFamily.eval_zero_to_marked s hx

/-- Pointwise nonzero-evaluation branch-avoidance consequence for concrete
trivialized-ratio finite marked families. -/
theorem eval_nonzero_avoids_marked
    (s : V) {x : C} (hx : F.evalPackage.eval x s ≠ 0) :
    (F.map s).hom.base x ∉ markedSchemePointSet K := by
  exact F.toProjectiveSectionFiniteMarkedFamily.eval_nonzero_avoids_marked s hx

/-- Direct finite disjoint-set conclusion for the concrete trivialized-ratio
finite marked family. -/
theorem exists_for_finite_disjoint
    [Infinite K] {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V, (∀ x ∈ S, (F.map s).hom.base x ∈ markedSchemePointSet K) ∧
      ∀ x ∈ T, (F.map s).hom.base x ∉ markedSchemePointSet K := by
  exact F.toProjectiveSectionFiniteMarkedFamily.exists_for_finite_disjoint
    hS hT hdis

/-- Direct Belyi-open controls for concrete trivialized-ratio finite marked
families. -/
theorem exists_map_belyiOpen_controls
    [Infinite K] {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V, T ⊆ ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
      ((F.map s).toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  exact F.toProjectiveSectionFiniteMarkedFamily.exists_map_belyiOpen_controls
    hS hT hdis

/-- Direct same-map marked and Belyi-open controls for concrete
trivialized-ratio finite marked families. -/
theorem exists_map_controls_and_belyiOpen_controls
    [Infinite K] {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V,
      ((∀ x ∈ S, (F.map s).hom.base x ∈ markedSchemePointSet K) ∧
        ∀ x ∈ T, (F.map s).hom.base x ∉ markedSchemePointSet K) ∧
        T ⊆ ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
          ((F.map s).toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  exact F.toProjectiveSectionFiniteMarkedFamily.exists_map_controls_and_belyiOpen_controls
    hS hT hdis

/-- Direct same-map marked, open, and Belyi-open controls for concrete
trivialized-ratio finite marked families. -/
theorem exists_map_controls_and_isOpen_belyiOpen_controls
    [Infinite K] {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V,
      ((∀ x ∈ S, (F.map s).hom.base x ∈ markedSchemePointSet K) ∧
        ∀ x ∈ T, (F.map s).hom.base x ∉ markedSchemePointSet K) ∧
        IsOpen ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
          T ⊆ ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
            ((F.map s).toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  exact F.toProjectiveSectionFiniteMarkedFamily.exists_map_controls_and_isOpen_belyiOpen_controls
    hS hT hdis

/-- Actual finite-map one-point finite-complement-open consequence for
concrete trivialized-ratio finite marked families. -/
theorem exists_map_belyiOpen_inside_open_of_finite_complement
    [Infinite K]
    {U : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite) {x : C} (hxU : x ∈ U) :
    ∃ s : V,
      IsOpen ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
        x ∈ ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
          ((F.map s).toBelyiMap.belyiOpen : Set C) ⊆ U := by
  exact
    F.toProjectiveSectionFiniteMarkedFamily.exists_map_belyiOpen_inside_open_of_finite_complement
      hU hUcompl hxU

/-- Actual finite-map finite-set finite-complement-open consequence for
concrete trivialized-ratio finite marked families. -/
theorem exists_map_belyiOpen_containing_finite_inside_open_of_finite_complement
    [Infinite K]
    {U T : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ s : V,
      IsOpen ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
        T ⊆ ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
          ((F.map s).toBelyiMap.belyiOpen : Set C) ⊆ U := by
  exact
    F.toProjectiveSectionFiniteMarkedFamily.exists_map_belyiOpen_containing_finite_inside_open_of_finite_complement
      hU hUcompl hT hTsub

/-- Actual finite-map finite-complement-open consequence retaining marked
controls for concrete trivialized-ratio finite marked families. -/
theorem exists_map_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_finite_complement
    [Infinite K]
    {U T : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ s : V,
      ((∀ x ∈ Uᶜ, (F.map s).hom.base x ∈ markedSchemePointSet K) ∧
        ∀ x ∈ T, (F.map s).hom.base x ∉ markedSchemePointSet K) ∧
        IsOpen ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
          T ⊆ ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
            ((F.map s).toBelyiMap.belyiOpen : Set C) ⊆ U := by
  exact
    F.toProjectiveSectionFiniteMarkedFamily.exists_map_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_finite_complement
      hU hUcompl hT hTsub

/-- Actual finite-map nonempty-open finite-complement consequence retaining
marked controls for concrete trivialized-ratio finite marked families. -/
theorem exists_map_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
    [Infinite K] [NonemptyOpenFiniteComplement C]
    {U T : Set C} (hU : IsOpen U) (hUne : U.Nonempty)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ s : V,
      ((∀ x ∈ Uᶜ, (F.map s).hom.base x ∈ markedSchemePointSet K) ∧
        ∀ x ∈ T, (F.map s).hom.base x ∉ markedSchemePointSet K) ∧
        IsOpen ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
          T ⊆ ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
            ((F.map s).toBelyiMap.belyiOpen : Set C) ⊆ U := by
  exact
    F.toProjectiveSectionFiniteMarkedFamily.exists_map_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
      hU hUne hT hTsub

/-- Direct one-point Belyi-open consequence for concrete trivialized-ratio
finite marked families. -/
theorem exists_belyiOpen_inside_complement
    [Infinite K] [T1Space (P1 K)]
    {A : Set C} (hA : A.Finite) {x : C} (hxA : x ∉ A) :
    ∃ s : V,
      IsOpen ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        x ∈ ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ Aᶜ := by
  exact F.toProjectiveSectionFiniteMarkedFamily.exists_belyiOpen_inside_complement
    hA hxA

/-- Direct finite-set Belyi-open consequence for concrete trivialized-ratio
finite marked families, inside the complement of a finite source set. -/
theorem exists_belyiOpen_containing_finite_inside_complement
    [Infinite K] [T1Space (P1 K)]
    {S T : Set C} (hS : S.Finite) (hT : T.Finite) (hdis : Disjoint S T) :
    ∃ s : V,
      IsOpen ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        T ⊆ ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ Sᶜ := by
  exact F.toProjectiveSectionFiniteMarkedFamily.exists_belyiOpen_containing_finite_inside_complement
    hS hT hdis

/-- Direct one-point Belyi-open consequence for concrete trivialized-ratio
finite marked families, with the finite complement supplied explicitly. -/
theorem exists_belyiOpen_inside_open_of_finite_complement
    [Infinite K] [T1Space (P1 K)]
    {U : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite) {x : C} (hxU : x ∈ U) :
    ∃ s : V,
      IsOpen ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        x ∈ ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ U := by
  exact F.toProjectiveSectionFiniteMarkedFamily.exists_belyiOpen_inside_open_of_finite_complement
    hU hUcompl hxU

/-- Direct finite-set Belyi-open consequence for concrete trivialized-ratio
finite marked families, with the finite complement supplied explicitly. -/
theorem exists_belyiOpen_containing_finite_inside_open_of_finite_complement
    [Infinite K] [T1Space (P1 K)]
    {U T : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ s : V,
      IsOpen ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        T ⊆ ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ U := by
  exact F.toProjectiveSectionFiniteMarkedFamily.exists_belyiOpen_containing_finite_inside_open_of_finite_complement
    hU hUcompl hT hTsub

/-- Direct one-point Belyi-open consequence for concrete trivialized-ratio
finite marked families in the curve-style finite-complement topology form. -/
theorem exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C]
    {U : Set C} (hU : IsOpen U) {x : C} (hxU : x ∈ U) :
    ∃ s : V,
      IsOpen ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        x ∈ ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ U := by
  exact F.toProjectiveSectionFiniteMarkedFamily.exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
    hU hxU

/-- Direct finite-set Belyi-open consequence for concrete trivialized-ratio
finite marked families in the curve-style finite-complement topology form. -/
theorem exists_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C]
    {U T : Set C} (hU : IsOpen U) (hUne : U.Nonempty)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ s : V,
      IsOpen ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        T ⊆ ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ U := by
  exact F.toProjectiveSectionFiniteMarkedFamily.exists_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
    hU hUne hT hTsub

/-- Direct finite tuple-subcover consequence for concrete trivialized-ratio
finite marked families. -/
theorem finite_subcover_on_complement
    [Infinite K] (κ : Type*) [Finite κ] [T1Space (P1 K)]
    {S : Set C} (hS : S.Finite) [CompactSpace (κ → {x : C // x ∉ S})] :
    ∃ t : Finset {s : V //
        (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedCoverData K V
          F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).sendsSetToBranch S s},
      (⋃ s ∈ t, ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedCoverData K V
            F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).complementCoverData S).tupleAvoidSet
              (κ := κ) s) =
        (Set.univ : Set (κ → {x : C // x ∉ S})) := by
  exact F.toProjectiveSectionFiniteMarkedFamily.finite_subcover_on_complement
    κ hS

/-- Direct finite tuple-subcover consequence for concrete trivialized-ratio
finite marked families, in membership form. -/
theorem finite_subcover_on_complement_forall
    [Infinite K] (κ : Type*) [Finite κ] [T1Space (P1 K)]
    {S : Set C} (hS : S.Finite) [CompactSpace (κ → {x : C // x ∉ S})] :
    ∃ t : Finset {s : V //
        (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedCoverData K V
          F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).sendsSetToBranch S s},
      ∀ x : κ → {x : C // x ∉ S},
        ∃ s ∈ t,
          x ∈ ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedCoverData K V
            F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).complementCoverData S).tupleAvoidSet
              (κ := κ) s := by
  exact F.toProjectiveSectionFiniteMarkedFamily.finite_subcover_on_complement_forall
    κ hS

/-- Direct finite tuple-subcover consequence for concrete trivialized-ratio
finite marked families, in concrete marked-avoidance form. -/
theorem finite_subcover_on_complement_forall_avoidance
    [Infinite K] (κ : Type*) [Finite κ] [T1Space (P1 K)]
    {S : Set C} (hS : S.Finite) [CompactSpace (κ → {x : C // x ∉ S})] :
    ∃ t : Finset {s : V //
        (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedCoverData K V
          F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).sendsSetToBranch S s},
      ∀ x : κ → {x : C // x ∉ S},
        ∃ s ∈ t, ∀ i, (F.map s.1).hom.base (x i).1 ∉ markedSchemePointSet K := by
  rcases F.toProjectiveSectionFiniteMarkedFamily.finite_subcover_on_complement_forall_avoidance
      κ hS with
    ⟨t, ht⟩
  refine ⟨t, ?_⟩
  intro x
  rcases ht x with ⟨s, hst, hsx⟩
  exact ⟨s, hst, by simpa [toProjectiveSectionFiniteMarkedFamily] using hsx⟩

/-- Compact-exhaustion cover bridge for concrete trivialized-ratio finite
marked families. -/
theorem finite_compact_cover_by_belyiOpen_exhaustions
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    (Kex : ∀ s : V,
      CompactExhaustion ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s)) :
    ∃ t : Finset (V × ℕ),
      (∀ p ∈ t,
        IsCompact ((Subtype.val :
          (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
            (Kex p.1 p.2))) ∧
        (∀ p ∈ t,
          ((Subtype.val :
            (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
              F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
              (Kex p.1 p.2)) ⊆
                (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                  F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1) ∧
          (Set.univ : Set C) ⊆
            ⋃ p ∈ t,
              (Subtype.val :
                (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                  F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
                (Kex p.1 p.2) := by
  exact
    F.toProjectiveSectionFiniteMarkedFamily.finite_compact_cover_by_belyiOpen_exhaustions
      Kex

/-- Equality form of the compact-exhaustion cover bridge for concrete
trivialized-ratio finite marked families. -/
theorem finite_compact_cover_by_belyiOpen_exhaustions_eq_univ
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    (Kex : ∀ s : V,
      CompactExhaustion ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s)) :
    ∃ t : Finset (V × ℕ),
      (∀ p ∈ t,
        IsCompact ((Subtype.val :
          (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
            (Kex p.1 p.2))) ∧
        (∀ p ∈ t,
          ((Subtype.val :
            (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
              F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
              (Kex p.1 p.2)) ⊆
                (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                  F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1) ∧
          (⋃ p ∈ t,
            (Subtype.val :
              (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
              (Kex p.1 p.2)) = (Set.univ : Set C) := by
  exact
    F.toProjectiveSectionFiniteMarkedFamily.finite_compact_cover_by_belyiOpen_exhaustions_eq_univ
      Kex

/-- Compact-cover bridge for concrete trivialized-ratio finite marked
families, with compact exhaustions supplied by local compactness and second
countability. -/
theorem finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    [LocallyCompactSpace C] [SecondCountableTopology C] :
    ∃ Kex : ∀ s : V,
      CompactExhaustion ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s),
      ∃ t : Finset (V × ℕ),
        (∀ p ∈ t,
          IsCompact ((Subtype.val :
            (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
              F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
              (Kex p.1 p.2))) ∧
          (∀ p ∈ t,
            ((Subtype.val :
              (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
                (Kex p.1 p.2)) ⊆
                  (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                    F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1) ∧
            (Set.univ : Set C) ⊆
              ⋃ p ∈ t,
                (Subtype.val :
                  (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                    F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
                  (Kex p.1 p.2) := by
  exact
    F.toProjectiveSectionFiniteMarkedFamily.finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact

/-- Equality form of the compact-cover bridge for concrete trivialized-ratio
finite marked families, with compact exhaustions supplied by local compactness
and second countability. -/
theorem finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact_eq_univ
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    [LocallyCompactSpace C] [SecondCountableTopology C] :
    ∃ Kex : ∀ s : V,
      CompactExhaustion ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s),
      ∃ t : Finset (V × ℕ),
        (∀ p ∈ t,
          IsCompact ((Subtype.val :
            (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
              F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
              (Kex p.1 p.2))) ∧
          (∀ p ∈ t,
            ((Subtype.val :
              (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
                (Kex p.1 p.2)) ⊆
                  (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                    F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1) ∧
            (⋃ p ∈ t,
              (Subtype.val :
                (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                  F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
                (Kex p.1 p.2)) = (Set.univ : Set C) := by
  exact
    F.toProjectiveSectionFiniteMarkedFamily.finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact_eq_univ

/-- Compact-coordinate Corollary 3.2 bridge for concrete trivialized-ratio
finite marked families. -/
theorem finite_compact_coordinate_sets_of_belyiOpen_exhaustions
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    [LocallyCompactSpace C] [SecondCountableTopology C]
    {κ : Type*} {Z : κ → Type*} [∀ j, TopologicalSpace (Z j)]
    (G : V → C → ((j : κ) → Z j))
    (hG : ∀ s, Continuous (G s))
    (A : (j : κ) → Set (Z j))
    (hGA : ∀ s x,
      x ∈ (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s →
        ∀ j, G s x j ∈ A j) :
    ∃ Kex : ∀ s : V,
      CompactExhaustion ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s),
      ∃ t : Finset (V × ℕ),
        ∃ H : (j : κ) → Set (Z j),
          (∀ j, IsCompact (H j)) ∧
            (∀ j, H j ⊆ A j) ∧
              (Set.univ : Set C) ⊆
                ⋃ p ∈ t,
                  (Subtype.val :
                    (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                      F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 →
                      C) ''
                    (Kex p.1 p.2) ∧
                ∀ p ∈ t, ∀ x,
                  x ∈ (Subtype.val :
                    (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                      F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 →
                      C) ''
                      (Kex p.1 p.2) →
                    ∀ j, G p.1 x j ∈ H j := by
  exact
    F.toProjectiveSectionFiniteMarkedFamily.finite_compact_coordinate_sets_of_belyiOpen_exhaustions
      G hG A hGA

end TrivializedProjectiveSectionFiniteMarkedFamily

/-- A concrete finite marked family whose projective-section maps are supplied
by denominator-is-unit local section-ratio data.  This removes the need to
materialize explicit denominator units before entering the finite marked Belyi
family interface. -/
structure IsUnitTrivializedProjectiveSectionFiniteMarkedFamily
    (K : Type u) [Field K] (C : Scheme.{u})
    (V : Type w) [AddCommGroup V] [Module K V] where
  evalPackage : RiemannRochFiniteEvaluationPackage K C V
  hmarkedOpen : IsOpen (markedSchemePointSet K)ᶜ
  trivialized : V → TrivializedIsUnitSectionRatioData K C V
  map : V → SchemeBelyi.FiniteBelyiMap
    (SchemeBelyi.markedBelyiTarget K hmarkedOpen) C
  map_base_eq_globalHom :
    ∀ s x, (map s).hom.base x = (trivialized s).globalHom.base x
  trivialized_section0_eval_eq_index :
    ∀ s x, (trivialized s).evalData.eval x (trivialized s).section0 = evalPackage.eval x s
  nonzero_avoids_marked :
    ∀ {T : Set C} {s : V},
      evalPackage.toEvaluationData.nonzeroOnSet T s →
        ∀ x ∈ T, (map s).hom.base x ∉ markedSchemePointSet K

namespace IsUnitTrivializedProjectiveSectionFiniteMarkedFamily

variable {C : Scheme.{u}}
variable (F : IsUnitTrivializedProjectiveSectionFiniteMarkedFamily K C V)

/-- The projective-section pair attached to a section through denominator-is-unit
local ratio data. -/
def pair (s : V) : ProjectiveLineSectionPair K C V :=
  (F.trivialized s).toProjectiveLineSectionPair

theorem pair_hom (s : V) :
    (F.pair s).hom = (F.trivialized s).globalHom := rfl

theorem map_base_eq_pair (s : V) (x : C) :
    (F.map s).hom.base x = (F.pair s).hom.base x := by
  exact F.map_base_eq_globalHom s x

theorem pair_section0_eval_eq_index (s : V) (x : C) :
    (F.pair s).evalData.eval x (F.pair s).section0 =
      F.evalPackage.eval x s := by
  exact F.trivialized_section0_eval_eq_index s x

/-- Forget denominator-is-unit local data to the projective-section finite
marked family interface. -/
def toProjectiveSectionFiniteMarkedFamily :
    ProjectiveSectionFiniteMarkedFamily K C V where
  evalPackage := F.evalPackage
  hmarkedOpen := F.hmarkedOpen
  pair := F.pair
  map := F.map
  map_base_eq_pair := F.map_base_eq_pair
  pair_section0_eval_eq_index := F.pair_section0_eval_eq_index
  nonzero_avoids_marked := by
    intro T s hs
    exact F.nonzero_avoids_marked hs

theorem toProjectiveSectionFiniteMarkedFamily_map_apply
    (s : V) :
    F.toProjectiveSectionFiniteMarkedFamily.map s = F.map s := rfl

/-- Build the denominator-is-unit finite marked family from the more primitive
projective-section finite marked family, once the supplied trivialized local
data is known to induce the same projective-line section pair. -/
def ofProjectiveSectionFiniteMarkedFamily
    (projectiveFamily : ProjectiveSectionFiniteMarkedFamily K C V)
    (trivialized : V → TrivializedIsUnitSectionRatioData K C V)
    (hpair :
      ∀ s : V, projectiveFamily.pair s =
        (trivialized s).toProjectiveLineSectionPair) :
    IsUnitTrivializedProjectiveSectionFiniteMarkedFamily K C V where
  evalPackage := projectiveFamily.evalPackage
  hmarkedOpen := projectiveFamily.hmarkedOpen
  trivialized := trivialized
  map := projectiveFamily.map
  map_base_eq_globalHom := by
    intro s x
    calc
      (projectiveFamily.map s).hom.base x =
          (projectiveFamily.pair s).hom.base x :=
        projectiveFamily.map_base_eq_pair s x
      _ = ((trivialized s).toProjectiveLineSectionPair).hom.base x := by
        rw [hpair s]
      _ = (trivialized s).globalHom.base x := rfl
  trivialized_section0_eval_eq_index := by
    intro s x
    have h := projectiveFamily.pair_section0_eval_eq_index s x
    rw [hpair s] at h
    exact h
  nonzero_avoids_marked := by
    intro T s hs
    exact projectiveFamily.nonzero_avoids_marked hs

@[simp]
theorem ofProjectiveSectionFiniteMarkedFamily_evalPackage
    (projectiveFamily : ProjectiveSectionFiniteMarkedFamily K C V)
    (trivialized : V → TrivializedIsUnitSectionRatioData K C V)
    (hpair :
      ∀ s : V, projectiveFamily.pair s =
        (trivialized s).toProjectiveLineSectionPair) :
    (ofProjectiveSectionFiniteMarkedFamily projectiveFamily trivialized hpair).evalPackage =
      projectiveFamily.evalPackage := rfl

@[simp]
theorem ofProjectiveSectionFiniteMarkedFamily_trivialized
    (projectiveFamily : ProjectiveSectionFiniteMarkedFamily K C V)
    (trivialized : V → TrivializedIsUnitSectionRatioData K C V)
    (hpair :
      ∀ s : V, projectiveFamily.pair s =
        (trivialized s).toProjectiveLineSectionPair)
    (s : V) :
    (ofProjectiveSectionFiniteMarkedFamily projectiveFamily trivialized hpair).trivialized s =
      trivialized s := rfl

@[simp]
theorem ofProjectiveSectionFiniteMarkedFamily_map_apply
    (projectiveFamily : ProjectiveSectionFiniteMarkedFamily K C V)
    (trivialized : V → TrivializedIsUnitSectionRatioData K C V)
    (hpair :
      ∀ s : V, projectiveFamily.pair s =
        (trivialized s).toProjectiveLineSectionPair)
    (s : V) :
    (ofProjectiveSectionFiniteMarkedFamily projectiveFamily trivialized hpair).map s =
      projectiveFamily.map s := rfl

/-- Each denominator-is-unit finite marked family map is finite. -/
theorem map_finite_hom
    (s : V) :
    IsFinite (F.map s).hom :=
  SchemeBelyi.FiniteBelyiMap.isFinite_hom (F.map s)

/-- Each denominator-is-unit finite marked family map is dominant. -/
theorem map_isDominant_hom
    (s : V) :
    IsDominant (F.map s).hom :=
  SchemeBelyi.FiniteBelyiMap.isDominant_hom (F.map s)

/-- Each denominator-is-unit finite marked family map has dense range on
underlying spaces. -/
theorem map_denseRange_hom
    (s : V) :
    DenseRange (F.map s).hom.base :=
  SchemeBelyi.FiniteBelyiMap.denseRange_hom (F.map s)

/-- Each denominator-is-unit finite marked family map is etale over the marked
branch-complement open. -/
theorem map_isEtale_restrict_branchOpen
    (s : V) :
    IsEtale ((F.map s).hom ∣_
      (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.isEtale_restrict_branchOpen (F.map s)

/-- The branch-open restriction of each denominator-is-unit map is finite. -/
theorem map_isFinite_restrict_branchOpen
    (s : V) :
    IsFinite ((F.map s).hom ∣_
      (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.isFinite_restrict_branchOpen (F.map s)

/-- The branch-open restriction of each denominator-is-unit map is affine. -/
theorem map_isAffineHom_restrict_branchOpen
    (s : V) :
    IsAffineHom ((F.map s).hom ∣_
      (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.isAffineHom_restrict_branchOpen (F.map s)

/-- The branch-open restriction of each denominator-is-unit map is integral. -/
theorem map_isIntegralHom_restrict_branchOpen
    (s : V) :
    IsIntegralHom ((F.map s).hom ∣_
      (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.isIntegralHom_restrict_branchOpen (F.map s)

/-- The branch-open restriction of each denominator-is-unit map is locally of
finite type. -/
theorem map_locallyOfFiniteType_restrict_branchOpen
    (s : V) :
    LocallyOfFiniteType ((F.map s).hom ∣_
      (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.locallyOfFiniteType_restrict_branchOpen (F.map s)

/-- The branch-open restriction of each denominator-is-unit map is separated. -/
theorem map_isSeparated_restrict_branchOpen
    (s : V) :
    IsSeparated ((F.map s).hom ∣_
      (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.isSeparated_restrict_branchOpen (F.map s)

/-- The branch-open restriction of each denominator-is-unit map is quasi-compact. -/
theorem map_quasiCompact_restrict_branchOpen
    (s : V) :
    QuasiCompact ((F.map s).hom ∣_
      (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.quasiCompact_restrict_branchOpen (F.map s)

/-- Each denominator-is-unit finite marked family map is affine. -/
theorem map_isAffineHom_hom
    (s : V) :
    IsAffineHom (F.map s).hom :=
  SchemeBelyi.FiniteBelyiMap.isAffineHom_hom (F.map s)

/-- Each denominator-is-unit finite marked family map is integral. -/
theorem map_isIntegralHom_hom
    (s : V) :
    IsIntegralHom (F.map s).hom :=
  SchemeBelyi.FiniteBelyiMap.isIntegralHom_hom (F.map s)

/-- Each denominator-is-unit finite marked family map is locally of finite type. -/
theorem map_locallyOfFiniteType_hom
    (s : V) :
    LocallyOfFiniteType (F.map s).hom :=
  SchemeBelyi.FiniteBelyiMap.locallyOfFiniteType_hom (F.map s)

/-- Each denominator-is-unit finite marked family map is separated. -/
theorem map_isSeparated_hom
    (s : V) :
    IsSeparated (F.map s).hom :=
  SchemeBelyi.FiniteBelyiMap.isSeparated_hom (F.map s)

/-- Each denominator-is-unit finite marked family map is quasi-compact. -/
theorem map_quasiCompact_hom
    (s : V) :
    QuasiCompact (F.map s).hom :=
  SchemeBelyi.FiniteBelyiMap.quasiCompact_hom (F.map s)

theorem toFiniteMarkedBelyiExistence_mem_belyiOpen_iff
    [Infinite K] (s : V) (x : C) :
    x ∈ (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
      F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s ↔
      (F.map s).hom.base x ∉ markedSchemePointSet K := by
  exact
    ProjectiveSectionFiniteMarkedFamily.toFiniteMarkedBelyiExistence_mem_belyiOpen_iff
      F.toProjectiveSectionFiniteMarkedFamily s x

theorem toFiniteMarkedBelyiExistence_belyiOpen_carrier
    [Infinite K] (s : V) :
    (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
      F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s =
      {x : C | (F.map s).hom.base x ∉ markedSchemePointSet K} := by
  exact
    ProjectiveSectionFiniteMarkedFamily.toFiniteMarkedBelyiExistence_belyiOpen_carrier
      F.toProjectiveSectionFiniteMarkedFamily s

theorem toFiniteMarkedBelyiExistence_belyiOpen_eq_schemeBelyi
    [Infinite K] (s : V) :
    (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
      F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s =
      ((F.map s).toBelyiMap.belyiOpen : Set C) := by
  exact
    ProjectiveSectionFiniteMarkedFamily.toFiniteMarkedBelyiExistence_belyiOpen_eq_schemeBelyi
      F.toProjectiveSectionFiniteMarkedFamily s

/-- Pointwise zero-evaluation branch consequence for denominator-is-unit
trivialized finite marked families. -/
theorem eval_zero_to_marked
    (s : V) {x : C} (hx : F.evalPackage.eval x s = 0) :
    (F.map s).hom.base x ∈ markedSchemePointSet K := by
  exact F.toProjectiveSectionFiniteMarkedFamily.eval_zero_to_marked s hx

/-- Pointwise nonzero-evaluation branch-avoidance consequence for
denominator-is-unit trivialized finite marked families. -/
theorem eval_nonzero_avoids_marked
    (s : V) {x : C} (hx : F.evalPackage.eval x s ≠ 0) :
    (F.map s).hom.base x ∉ markedSchemePointSet K := by
  exact F.toProjectiveSectionFiniteMarkedFamily.eval_nonzero_avoids_marked s hx

/-- Direct finite disjoint-set conclusion for denominator-is-unit trivialized
finite marked families. -/
theorem exists_for_finite_disjoint
    [Infinite K] {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V, (∀ x ∈ S, (F.map s).hom.base x ∈ markedSchemePointSet K) ∧
      ∀ x ∈ T, (F.map s).hom.base x ∉ markedSchemePointSet K := by
  exact F.toProjectiveSectionFiniteMarkedFamily.exists_for_finite_disjoint
    hS hT hdis

/-- Direct Belyi-open controls for denominator-is-unit trivialized finite
marked families. -/
theorem exists_map_belyiOpen_controls
    [Infinite K] {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V, T ⊆ ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
      ((F.map s).toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  exact F.toProjectiveSectionFiniteMarkedFamily.exists_map_belyiOpen_controls
    hS hT hdis

/-- Direct same-map marked and Belyi-open controls for denominator-is-unit
trivialized finite marked families. -/
theorem exists_map_controls_and_belyiOpen_controls
    [Infinite K] {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V,
      ((∀ x ∈ S, (F.map s).hom.base x ∈ markedSchemePointSet K) ∧
        ∀ x ∈ T, (F.map s).hom.base x ∉ markedSchemePointSet K) ∧
        T ⊆ ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
          ((F.map s).toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  exact F.toProjectiveSectionFiniteMarkedFamily.exists_map_controls_and_belyiOpen_controls
    hS hT hdis

/-- Direct same-map marked, open, and Belyi-open controls for
denominator-is-unit trivialized finite marked families. -/
theorem exists_map_controls_and_isOpen_belyiOpen_controls
    [Infinite K] {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V,
      ((∀ x ∈ S, (F.map s).hom.base x ∈ markedSchemePointSet K) ∧
        ∀ x ∈ T, (F.map s).hom.base x ∉ markedSchemePointSet K) ∧
        IsOpen ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
          T ⊆ ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
            ((F.map s).toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  exact F.toProjectiveSectionFiniteMarkedFamily.exists_map_controls_and_isOpen_belyiOpen_controls
    hS hT hdis

/-- Actual finite-map one-point finite-complement-open consequence for
denominator-is-unit trivialized finite marked families. -/
theorem exists_map_belyiOpen_inside_open_of_finite_complement
    [Infinite K]
    {U : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite) {x : C} (hxU : x ∈ U) :
    ∃ s : V,
      IsOpen ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
        x ∈ ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
          ((F.map s).toBelyiMap.belyiOpen : Set C) ⊆ U := by
  exact
    F.toProjectiveSectionFiniteMarkedFamily.exists_map_belyiOpen_inside_open_of_finite_complement
      hU hUcompl hxU

/-- Actual finite-map finite-set finite-complement-open consequence for
denominator-is-unit trivialized finite marked families. -/
theorem exists_map_belyiOpen_containing_finite_inside_open_of_finite_complement
    [Infinite K]
    {U T : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ s : V,
      IsOpen ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
        T ⊆ ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
          ((F.map s).toBelyiMap.belyiOpen : Set C) ⊆ U := by
  exact
    F.toProjectiveSectionFiniteMarkedFamily.exists_map_belyiOpen_containing_finite_inside_open_of_finite_complement
      hU hUcompl hT hTsub

/-- Actual finite-map finite-complement-open consequence retaining marked
controls for denominator-is-unit trivialized finite marked families. -/
theorem exists_map_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_finite_complement
    [Infinite K]
    {U T : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ s : V,
      ((∀ x ∈ Uᶜ, (F.map s).hom.base x ∈ markedSchemePointSet K) ∧
        ∀ x ∈ T, (F.map s).hom.base x ∉ markedSchemePointSet K) ∧
        IsOpen ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
          T ⊆ ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
            ((F.map s).toBelyiMap.belyiOpen : Set C) ⊆ U := by
  exact
    F.toProjectiveSectionFiniteMarkedFamily.exists_map_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_finite_complement
      hU hUcompl hT hTsub

/-- Actual finite-map nonempty-open finite-complement consequence retaining
marked controls for denominator-is-unit trivialized finite marked families. -/
theorem exists_map_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
    [Infinite K] [NonemptyOpenFiniteComplement C]
    {U T : Set C} (hU : IsOpen U) (hUne : U.Nonempty)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ s : V,
      ((∀ x ∈ Uᶜ, (F.map s).hom.base x ∈ markedSchemePointSet K) ∧
        ∀ x ∈ T, (F.map s).hom.base x ∉ markedSchemePointSet K) ∧
        IsOpen ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
          T ⊆ ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
            ((F.map s).toBelyiMap.belyiOpen : Set C) ⊆ U := by
  exact
    F.toProjectiveSectionFiniteMarkedFamily.exists_map_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
      hU hUne hT hTsub

/-- Direct one-point Belyi-open consequence for denominator-is-unit
trivialized finite marked families. -/
theorem exists_belyiOpen_inside_complement
    [Infinite K] [T1Space (P1 K)]
    {A : Set C} (hA : A.Finite) {x : C} (hxA : x ∉ A) :
    ∃ s : V,
      IsOpen ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        x ∈ ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ Aᶜ := by
  exact F.toProjectiveSectionFiniteMarkedFamily.exists_belyiOpen_inside_complement
    hA hxA

/-- Direct finite-set Belyi-open consequence for denominator-is-unit
trivialized finite marked families, inside the complement of a finite source
set. -/
theorem exists_belyiOpen_containing_finite_inside_complement
    [Infinite K] [T1Space (P1 K)]
    {S T : Set C} (hS : S.Finite) (hT : T.Finite) (hdis : Disjoint S T) :
    ∃ s : V,
      IsOpen ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        T ⊆ ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ Sᶜ := by
  exact F.toProjectiveSectionFiniteMarkedFamily.exists_belyiOpen_containing_finite_inside_complement
    hS hT hdis

/-- Direct one-point Belyi-open consequence for denominator-is-unit
trivialized finite marked families, with the finite complement supplied
explicitly. -/
theorem exists_belyiOpen_inside_open_of_finite_complement
    [Infinite K] [T1Space (P1 K)]
    {U : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite) {x : C} (hxU : x ∈ U) :
    ∃ s : V,
      IsOpen ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        x ∈ ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ U := by
  exact F.toProjectiveSectionFiniteMarkedFamily.exists_belyiOpen_inside_open_of_finite_complement
    hU hUcompl hxU

/-- Direct finite-set Belyi-open consequence for denominator-is-unit
trivialized finite marked families, with the finite complement supplied
explicitly. -/
theorem exists_belyiOpen_containing_finite_inside_open_of_finite_complement
    [Infinite K] [T1Space (P1 K)]
    {U T : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ s : V,
      IsOpen ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        T ⊆ ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ U := by
  exact F.toProjectiveSectionFiniteMarkedFamily.exists_belyiOpen_containing_finite_inside_open_of_finite_complement
    hU hUcompl hT hTsub

/-- Direct one-point Belyi-open consequence for denominator-is-unit
trivialized finite marked families in the curve-style finite-complement
topology form. -/
theorem exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C]
    {U : Set C} (hU : IsOpen U) {x : C} (hxU : x ∈ U) :
    ∃ s : V,
      IsOpen ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        x ∈ ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ U := by
  exact F.toProjectiveSectionFiniteMarkedFamily.exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
    hU hxU

/-- Direct finite-set Belyi-open consequence for denominator-is-unit
trivialized finite marked families in the curve-style finite-complement
topology form. -/
theorem exists_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C]
    {U T : Set C} (hU : IsOpen U) (hUne : U.Nonempty)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ s : V,
      IsOpen ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        T ⊆ ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ U := by
  exact F.toProjectiveSectionFiniteMarkedFamily.exists_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
    hU hUne hT hTsub

/-- Direct finite tuple-subcover consequence for denominator-is-unit
trivialized finite marked families. -/
theorem finite_subcover_on_complement
    [Infinite K] (κ : Type*) [Finite κ] [T1Space (P1 K)]
    {S : Set C} (hS : S.Finite) [CompactSpace (κ → {x : C // x ∉ S})] :
    ∃ t : Finset {s : V //
        (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedCoverData K V
          F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).sendsSetToBranch S s},
      (⋃ s ∈ t, ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedCoverData K V
            F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).complementCoverData S).tupleAvoidSet
              (κ := κ) s) =
        (Set.univ : Set (κ → {x : C // x ∉ S})) := by
  exact F.toProjectiveSectionFiniteMarkedFamily.finite_subcover_on_complement
    κ hS

/-- Direct finite tuple-subcover consequence for denominator-is-unit
trivialized finite marked families, in membership form. -/
theorem finite_subcover_on_complement_forall
    [Infinite K] (κ : Type*) [Finite κ] [T1Space (P1 K)]
    {S : Set C} (hS : S.Finite) [CompactSpace (κ → {x : C // x ∉ S})] :
    ∃ t : Finset {s : V //
        (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedCoverData K V
          F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).sendsSetToBranch S s},
      ∀ x : κ → {x : C // x ∉ S},
        ∃ s ∈ t,
          x ∈ ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedCoverData K V
            F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).complementCoverData S).tupleAvoidSet
              (κ := κ) s := by
  exact F.toProjectiveSectionFiniteMarkedFamily.finite_subcover_on_complement_forall
    κ hS

/-- Direct finite tuple-subcover consequence for denominator-is-unit
trivialized finite marked families, in concrete marked-avoidance form. -/
theorem finite_subcover_on_complement_forall_avoidance
    [Infinite K] (κ : Type*) [Finite κ] [T1Space (P1 K)]
    {S : Set C} (hS : S.Finite) [CompactSpace (κ → {x : C // x ∉ S})] :
    ∃ t : Finset {s : V //
        (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedCoverData K V
          F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).sendsSetToBranch S s},
      ∀ x : κ → {x : C // x ∉ S},
        ∃ s ∈ t, ∀ i, (F.map s.1).hom.base (x i).1 ∉ markedSchemePointSet K := by
  rcases F.toProjectiveSectionFiniteMarkedFamily.finite_subcover_on_complement_forall_avoidance
      κ hS with
    ⟨t, ht⟩
  refine ⟨t, ?_⟩
  intro x
  rcases ht x with ⟨s, hst, hsx⟩
  exact ⟨s, hst, by simpa [toProjectiveSectionFiniteMarkedFamily] using hsx⟩

/-- Compact-exhaustion cover bridge for denominator-is-unit trivialized finite
marked families. -/
theorem finite_compact_cover_by_belyiOpen_exhaustions
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    (Kex : ∀ s : V,
      CompactExhaustion ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s)) :
    ∃ t : Finset (V × ℕ),
      (∀ p ∈ t,
        IsCompact ((Subtype.val :
          (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
            (Kex p.1 p.2))) ∧
        (∀ p ∈ t,
          ((Subtype.val :
            (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
              F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
              (Kex p.1 p.2)) ⊆
                (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                  F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1) ∧
          (Set.univ : Set C) ⊆
            ⋃ p ∈ t,
              (Subtype.val :
                (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                  F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
                (Kex p.1 p.2) := by
  exact
    F.toProjectiveSectionFiniteMarkedFamily.finite_compact_cover_by_belyiOpen_exhaustions
      Kex

/-- Equality form of the compact-exhaustion cover bridge for
denominator-is-unit trivialized finite marked families. -/
theorem finite_compact_cover_by_belyiOpen_exhaustions_eq_univ
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    (Kex : ∀ s : V,
      CompactExhaustion ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s)) :
    ∃ t : Finset (V × ℕ),
      (∀ p ∈ t,
        IsCompact ((Subtype.val :
          (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
            (Kex p.1 p.2))) ∧
        (∀ p ∈ t,
          ((Subtype.val :
            (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
              F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
              (Kex p.1 p.2)) ⊆
                (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                  F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1) ∧
          (⋃ p ∈ t,
            (Subtype.val :
              (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
              (Kex p.1 p.2)) = (Set.univ : Set C) := by
  exact
    F.toProjectiveSectionFiniteMarkedFamily.finite_compact_cover_by_belyiOpen_exhaustions_eq_univ
      Kex

/-- Compact-cover bridge for denominator-is-unit trivialized finite marked
families, with compact exhaustions supplied by local compactness and second
countability. -/
theorem finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    [LocallyCompactSpace C] [SecondCountableTopology C] :
    ∃ Kex : ∀ s : V,
      CompactExhaustion ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s),
      ∃ t : Finset (V × ℕ),
        (∀ p ∈ t,
          IsCompact ((Subtype.val :
            (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
              F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
              (Kex p.1 p.2))) ∧
          (∀ p ∈ t,
            ((Subtype.val :
              (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
                (Kex p.1 p.2)) ⊆
                  (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                    F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1) ∧
            (Set.univ : Set C) ⊆
              ⋃ p ∈ t,
                (Subtype.val :
                  (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                    F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
                  (Kex p.1 p.2) := by
  exact
    F.toProjectiveSectionFiniteMarkedFamily.finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact

/-- Equality form of the compact-cover bridge for denominator-is-unit
trivialized finite marked families, with compact exhaustions supplied by local
compactness and second countability. -/
theorem finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact_eq_univ
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    [LocallyCompactSpace C] [SecondCountableTopology C] :
    ∃ Kex : ∀ s : V,
      CompactExhaustion ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s),
      ∃ t : Finset (V × ℕ),
        (∀ p ∈ t,
          IsCompact ((Subtype.val :
            (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
              F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
              (Kex p.1 p.2))) ∧
          (∀ p ∈ t,
            ((Subtype.val :
              (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
                (Kex p.1 p.2)) ⊆
                  (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                    F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1) ∧
            (⋃ p ∈ t,
              (Subtype.val :
                (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                  F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
                (Kex p.1 p.2)) = (Set.univ : Set C) := by
  exact
    F.toProjectiveSectionFiniteMarkedFamily.finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact_eq_univ

/-- Compact-coordinate Corollary 3.2 bridge for denominator-is-unit trivialized
finite marked families. -/
theorem finite_compact_coordinate_sets_of_belyiOpen_exhaustions
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    [LocallyCompactSpace C] [SecondCountableTopology C]
    {κ : Type*} {Z : κ → Type*} [∀ j, TopologicalSpace (Z j)]
    (G : V → C → ((j : κ) → Z j))
    (hG : ∀ s, Continuous (G s))
    (A : (j : κ) → Set (Z j))
    (hGA : ∀ s x,
      x ∈ (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s →
        ∀ j, G s x j ∈ A j) :
    ∃ Kex : ∀ s : V,
      CompactExhaustion ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s),
      ∃ t : Finset (V × ℕ),
        ∃ H : (j : κ) → Set (Z j),
          (∀ j, IsCompact (H j)) ∧
            (∀ j, H j ⊆ A j) ∧
              (Set.univ : Set C) ⊆
                ⋃ p ∈ t,
                  (Subtype.val :
                    (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                      F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 →
                      C) ''
                    (Kex p.1 p.2) ∧
                ∀ p ∈ t, ∀ x,
                  x ∈ (Subtype.val :
                    (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                      F.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 →
                      C) ''
                      (Kex p.1 p.2) →
                    ∀ j, G p.1 x j ∈ H j := by
  exact
    F.toProjectiveSectionFiniteMarkedFamily.finite_compact_coordinate_sets_of_belyiOpen_exhaustions
      G hG A hGA

end IsUnitTrivializedProjectiveSectionFiniteMarkedFamily

/-- A finite marked family whose projective-section maps are supplied by the
canonical two-basic-open Bezout section-ratio package.  This connects the
explicit two-section construction directly to the finite marked Belyi family
interface. -/
structure TwoSectionBezoutProjectiveSectionFiniteMarkedFamily
    (K : Type u) [Field K] (C : Scheme.{u})
    (V : Type w) [AddCommGroup V] [Module K V] where
  isUnitFamily : IsUnitTrivializedProjectiveSectionFiniteMarkedFamily K C V
  twoSection : V → TwoSectionBezoutTrivializedIsUnitData K C V
  trivialized_evalData_eq :
    ∀ s : V, (isUnitFamily.trivialized s).evalData = (twoSection s).evalData
  trivialized_section0_eq :
    ∀ s : V, (isUnitFamily.trivialized s).section0 = (twoSection s).section0
  trivialized_section1_eq :
    ∀ s : V, (isUnitFamily.trivialized s).section1 = (twoSection s).section1
  trivialized_globalHom_eq :
    ∀ s : V, (isUnitFamily.trivialized s).globalHom = (twoSection s).globalHom

namespace TwoSectionBezoutProjectiveSectionFiniteMarkedFamily

variable {C : Scheme.{u}}
variable (F : TwoSectionBezoutProjectiveSectionFiniteMarkedFamily K C V)

/-- The evaluation package inherited from the denominator-is-unit finite
family. -/
def evalPackage : RiemannRochFiniteEvaluationPackage K C V :=
  F.isUnitFamily.evalPackage

/-- The marked-open proof inherited from the denominator-is-unit finite family. -/
def hmarkedOpen : IsOpen (markedSchemePointSet K)ᶜ :=
  F.isUnitFamily.hmarkedOpen

/-- The finite marked Belyi map family inherited from the denominator-is-unit
finite family. -/
def map (s : V) : SchemeBelyi.FiniteBelyiMap
    (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen) C :=
  F.isUnitFamily.map s

/-- The denominator-is-unit trivialized data obtained from the canonical
two-section package. -/
def trivialized (s : V) : TrivializedIsUnitSectionRatioData K C V :=
  F.isUnitFamily.trivialized s

/-- Build the canonical two-section finite marked family when the finite
marked is-unit family uses exactly the universe-lifted trivialization coming
from the Bezout two-section construction.  This collapses the compatibility
obligation to a single equality of local projective-line data. -/
def ofTrivializedLiftedEq
    (isUnitFamily : IsUnitTrivializedProjectiveSectionFiniteMarkedFamily K C V)
    (twoSection : V → TwoSectionBezoutTrivializedIsUnitData K C V)
    (htrivialized :
      ∀ s : V, isUnitFamily.trivialized s =
        (twoSection s).toTrivializedIsUnitSectionRatioDataLifted) :
    TwoSectionBezoutProjectiveSectionFiniteMarkedFamily K C V where
  isUnitFamily := isUnitFamily
  twoSection := twoSection
  trivialized_evalData_eq := by
    intro s
    rw [htrivialized s]
    rfl
  trivialized_section0_eq := by
    intro s
    rw [htrivialized s]
    rfl
  trivialized_section1_eq := by
    intro s
    rw [htrivialized s]
    rfl
  trivialized_globalHom_eq := by
    intro s
    rw [htrivialized s]
    exact
      TwoSectionBezoutTrivializedIsUnitData.toTrivializedIsUnitSectionRatioDataLifted_globalHom
        (D := twoSection s)

@[simp]
theorem ofTrivializedLiftedEq_isUnitFamily
    (isUnitFamily : IsUnitTrivializedProjectiveSectionFiniteMarkedFamily K C V)
    (twoSection : V → TwoSectionBezoutTrivializedIsUnitData K C V)
    (htrivialized :
      ∀ s : V, isUnitFamily.trivialized s =
        (twoSection s).toTrivializedIsUnitSectionRatioDataLifted) :
    (ofTrivializedLiftedEq isUnitFamily twoSection htrivialized).isUnitFamily =
      isUnitFamily := rfl

@[simp]
theorem ofTrivializedLiftedEq_twoSection
    (isUnitFamily : IsUnitTrivializedProjectiveSectionFiniteMarkedFamily K C V)
    (twoSection : V → TwoSectionBezoutTrivializedIsUnitData K C V)
    (htrivialized :
      ∀ s : V, isUnitFamily.trivialized s =
        (twoSection s).toTrivializedIsUnitSectionRatioDataLifted) :
    (ofTrivializedLiftedEq isUnitFamily twoSection htrivialized).twoSection =
      twoSection := rfl

theorem ofTrivializedLiftedEq_trivialized_eq
    (isUnitFamily : IsUnitTrivializedProjectiveSectionFiniteMarkedFamily K C V)
    (twoSection : V → TwoSectionBezoutTrivializedIsUnitData K C V)
    (htrivialized :
      ∀ s : V, isUnitFamily.trivialized s =
        (twoSection s).toTrivializedIsUnitSectionRatioDataLifted)
    (s : V) :
    (ofTrivializedLiftedEq isUnitFamily twoSection htrivialized).trivialized s =
      (twoSection s).toTrivializedIsUnitSectionRatioDataLifted := by
  exact htrivialized s

/-- Build the canonical two-section finite marked family directly from a
projective-section finite marked family whose projective pairs are the pairs
assembled by the canonical two-section Bezout data. -/
def ofProjectiveSectionFiniteMarkedFamily
    (projectiveFamily : ProjectiveSectionFiniteMarkedFamily K C V)
    (twoSection : V → TwoSectionBezoutTrivializedIsUnitData K C V)
    (hpair :
      ∀ s : V, projectiveFamily.pair s =
        (twoSection s).toProjectiveLineSectionPair) :
    TwoSectionBezoutProjectiveSectionFiniteMarkedFamily K C V :=
  ofTrivializedLiftedEq
    (IsUnitTrivializedProjectiveSectionFiniteMarkedFamily.ofProjectiveSectionFiniteMarkedFamily
      projectiveFamily
      (fun s => (twoSection s).toTrivializedIsUnitSectionRatioDataLifted)
      (by
        intro s
        calc
          projectiveFamily.pair s = (twoSection s).toProjectiveLineSectionPair :=
            hpair s
          _ = ((twoSection s).toTrivializedIsUnitSectionRatioDataLifted).toProjectiveLineSectionPair := by
            exact
              (TwoSectionBezoutTrivializedIsUnitData.toTrivializedIsUnitSectionRatioDataLifted_toProjectiveLineSectionPair
                (D := twoSection s)).symm))
    twoSection
    (by
      intro s
      rfl)

@[simp]
theorem ofProjectiveSectionFiniteMarkedFamily_twoSection
    (projectiveFamily : ProjectiveSectionFiniteMarkedFamily K C V)
    (twoSection : V → TwoSectionBezoutTrivializedIsUnitData K C V)
    (hpair :
      ∀ s : V, projectiveFamily.pair s =
        (twoSection s).toProjectiveLineSectionPair) :
    (ofProjectiveSectionFiniteMarkedFamily projectiveFamily twoSection hpair).twoSection =
      twoSection := rfl

@[simp]
theorem ofProjectiveSectionFiniteMarkedFamily_map_apply
    (projectiveFamily : ProjectiveSectionFiniteMarkedFamily K C V)
    (twoSection : V → TwoSectionBezoutTrivializedIsUnitData K C V)
    (hpair :
      ∀ s : V, projectiveFamily.pair s =
        (twoSection s).toProjectiveLineSectionPair)
    (s : V) :
    (ofProjectiveSectionFiniteMarkedFamily projectiveFamily twoSection hpair).map s =
      projectiveFamily.map s := rfl

theorem ofProjectiveSectionFiniteMarkedFamily_trivialized_eq_lifted
    (projectiveFamily : ProjectiveSectionFiniteMarkedFamily K C V)
    (twoSection : V → TwoSectionBezoutTrivializedIsUnitData K C V)
    (hpair :
      ∀ s : V, projectiveFamily.pair s =
        (twoSection s).toProjectiveLineSectionPair)
    (s : V) :
    (ofProjectiveSectionFiniteMarkedFamily projectiveFamily twoSection hpair).trivialized s =
      (twoSection s).toTrivializedIsUnitSectionRatioDataLifted := rfl

/-- Build the canonical two-section finite marked family directly from
section-controlled finite marked Belyi data, when each finite marked map agrees
with the projective-line morphism assembled by the two-section package and the
first-section evaluations match the section index. -/
def ofSectionControlledFiniteMarkedBelyiData
    (D : SectionControlledFiniteMarkedBelyiData K C V)
    (twoSection : V → TwoSectionBezoutTrivializedIsUnitData K C V)
    (hmap : ∀ s x, (D.map s).hom.base x = (twoSection s).globalHom.base x)
    (heval :
      ∀ s x, (twoSection s).evalData.eval x (twoSection s).section0 =
        D.evalPackage.eval x s) :
    TwoSectionBezoutProjectiveSectionFiniteMarkedFamily K C V :=
  ofProjectiveSectionFiniteMarkedFamily
    (ProjectiveSectionFiniteMarkedFamily.ofSectionControlledFiniteMarkedBelyiData
      D
      (fun s => (twoSection s).toProjectiveLineSectionPair)
      (by
        intro s x
        exact hmap s x)
      (by
        intro s x
        exact heval s x))
    twoSection
    (by
      intro s
      rfl)

@[simp]
theorem ofSectionControlledFiniteMarkedBelyiData_twoSection
    (D : SectionControlledFiniteMarkedBelyiData K C V)
    (twoSection : V → TwoSectionBezoutTrivializedIsUnitData K C V)
    (hmap : ∀ s x, (D.map s).hom.base x = (twoSection s).globalHom.base x)
    (heval :
      ∀ s x, (twoSection s).evalData.eval x (twoSection s).section0 =
        D.evalPackage.eval x s) :
    (ofSectionControlledFiniteMarkedBelyiData D twoSection hmap heval).twoSection =
      twoSection := rfl

@[simp]
theorem ofSectionControlledFiniteMarkedBelyiData_map_apply
    (D : SectionControlledFiniteMarkedBelyiData K C V)
    (twoSection : V → TwoSectionBezoutTrivializedIsUnitData K C V)
    (hmap : ∀ s x, (D.map s).hom.base x = (twoSection s).globalHom.base x)
    (heval :
      ∀ s x, (twoSection s).evalData.eval x (twoSection s).section0 =
        D.evalPackage.eval x s)
    (s : V) :
    (ofSectionControlledFiniteMarkedBelyiData D twoSection hmap heval).map s =
      D.map s := rfl

theorem ofSectionControlledFiniteMarkedBelyiData_trivialized_eq_lifted
    (D : SectionControlledFiniteMarkedBelyiData K C V)
    (twoSection : V → TwoSectionBezoutTrivializedIsUnitData K C V)
    (hmap : ∀ s x, (D.map s).hom.base x = (twoSection s).globalHom.base x)
    (heval :
      ∀ s x, (twoSection s).evalData.eval x (twoSection s).section0 =
        D.evalPackage.eval x s)
    (s : V) :
    (ofSectionControlledFiniteMarkedBelyiData D twoSection hmap heval).trivialized s =
      (twoSection s).toTrivializedIsUnitSectionRatioDataLifted := rfl

/-- Build the canonical two-section finite marked family directly from the
canonical two-section morphisms, once those morphisms are finite, dominant, and
étale over the marked branch-complement.  The vanishing-to-marked branch
control follows from the two-section zero-fiber theorem; the remaining
nonzero marked-avoidance is the separate Belyi-polynomial avoidance input. -/
def ofFiniteDominantEtaleTwoSection
    (evalPackage : RiemannRochFiniteEvaluationPackage K C V)
    (hmarkedOpen : IsOpen (markedSchemePointSet K)ᶜ)
    (twoSection : V → TwoSectionBezoutTrivializedIsUnitData K C V)
    (hFinite : ∀ s : V, IsFinite (twoSection s).globalHom)
    (hDominant : ∀ s : V, IsDominant (twoSection s).globalHom)
    (hEtale :
      ∀ s : V, IsEtale
        (((twoSection s).globalHom) ∣_
          (SchemeBelyi.markedBelyiTarget K hmarkedOpen).branchOpen))
    (heval :
      ∀ s x, (twoSection s).evalData.eval x (twoSection s).section0 =
        evalPackage.eval x s)
    (nonzero_avoids_marked :
      ∀ {T : Set C} {s : V},
        evalPackage.toEvaluationData.nonzeroOnSet T s →
          ∀ x ∈ T, (twoSection s).globalHom.base x ∉ markedSchemePointSet K) :
    TwoSectionBezoutProjectiveSectionFiniteMarkedFamily K C V :=
  ofSectionControlledFiniteMarkedBelyiData
    (SectionControlledFiniteMarkedBelyiData.ofFiniteDominantEtaleHomFamily
      evalPackage hmarkedOpen (fun s => (twoSection s).globalHom)
      hFinite hDominant hEtale
      (by
        intro S s hs x hx
        exact (twoSection s).toProjectiveLineSectionPair_maps_section0_zero_to_marked
          (by
            rw [heval s x]
            exact hs x hx))
      (by
        intro T s hs x hx
        exact nonzero_avoids_marked hs x hx))
    twoSection
    (by
      intro s x
      rfl)
    heval

@[simp]
theorem ofFiniteDominantEtaleTwoSection_twoSection
    (evalPackage : RiemannRochFiniteEvaluationPackage K C V)
    (hmarkedOpen : IsOpen (markedSchemePointSet K)ᶜ)
    (twoSection : V → TwoSectionBezoutTrivializedIsUnitData K C V)
    (hFinite : ∀ s : V, IsFinite (twoSection s).globalHom)
    (hDominant : ∀ s : V, IsDominant (twoSection s).globalHom)
    (hEtale :
      ∀ s : V, IsEtale
        (((twoSection s).globalHom) ∣_
          (SchemeBelyi.markedBelyiTarget K hmarkedOpen).branchOpen))
    (heval :
      ∀ s x, (twoSection s).evalData.eval x (twoSection s).section0 =
        evalPackage.eval x s)
    (nonzero_avoids_marked :
      ∀ {T : Set C} {s : V},
        evalPackage.toEvaluationData.nonzeroOnSet T s →
          ∀ x ∈ T, (twoSection s).globalHom.base x ∉ markedSchemePointSet K) :
    (ofFiniteDominantEtaleTwoSection evalPackage hmarkedOpen twoSection
      hFinite hDominant hEtale heval nonzero_avoids_marked).twoSection =
      twoSection := rfl

@[simp]
theorem ofFiniteDominantEtaleTwoSection_map_hom
    (evalPackage : RiemannRochFiniteEvaluationPackage K C V)
    (hmarkedOpen : IsOpen (markedSchemePointSet K)ᶜ)
    (twoSection : V → TwoSectionBezoutTrivializedIsUnitData K C V)
    (hFinite : ∀ s : V, IsFinite (twoSection s).globalHom)
    (hDominant : ∀ s : V, IsDominant (twoSection s).globalHom)
    (hEtale :
      ∀ s : V, IsEtale
        (((twoSection s).globalHom) ∣_
          (SchemeBelyi.markedBelyiTarget K hmarkedOpen).branchOpen))
    (heval :
      ∀ s x, (twoSection s).evalData.eval x (twoSection s).section0 =
        evalPackage.eval x s)
    (nonzero_avoids_marked :
      ∀ {T : Set C} {s : V},
        evalPackage.toEvaluationData.nonzeroOnSet T s →
          ∀ x ∈ T, (twoSection s).globalHom.base x ∉ markedSchemePointSet K)
    (s : V) :
    ((ofFiniteDominantEtaleTwoSection evalPackage hmarkedOpen twoSection
      hFinite hDominant hEtale heval nonzero_avoids_marked).map s).hom =
      (twoSection s).globalHom := rfl

theorem ofFiniteDominantEtaleTwoSection_trivialized_eq_lifted
    (evalPackage : RiemannRochFiniteEvaluationPackage K C V)
    (hmarkedOpen : IsOpen (markedSchemePointSet K)ᶜ)
    (twoSection : V → TwoSectionBezoutTrivializedIsUnitData K C V)
    (hFinite : ∀ s : V, IsFinite (twoSection s).globalHom)
    (hDominant : ∀ s : V, IsDominant (twoSection s).globalHom)
    (hEtale :
      ∀ s : V, IsEtale
        (((twoSection s).globalHom) ∣_
          (SchemeBelyi.markedBelyiTarget K hmarkedOpen).branchOpen))
    (heval :
      ∀ s x, (twoSection s).evalData.eval x (twoSection s).section0 =
        evalPackage.eval x s)
    (nonzero_avoids_marked :
      ∀ {T : Set C} {s : V},
        evalPackage.toEvaluationData.nonzeroOnSet T s →
          ∀ x ∈ T, (twoSection s).globalHom.base x ∉ markedSchemePointSet K)
    (s : V) :
    (ofFiniteDominantEtaleTwoSection evalPackage hmarkedOpen twoSection
      hFinite hDominant hEtale heval nonzero_avoids_marked).trivialized s =
      (twoSection s).toTrivializedIsUnitSectionRatioDataLifted := rfl

/-- Variant of `ofFiniteDominantEtaleTwoSection` where the pointwise
evaluation compatibility is derived from the fact that the two-section package
uses the evaluation package's evaluation data and takes its first section to be
the section index. -/
def ofFiniteDominantEtaleTwoSectionAligned
    (evalPackage : RiemannRochFiniteEvaluationPackage K C V)
    (hmarkedOpen : IsOpen (markedSchemePointSet K)ᶜ)
    (twoSection : V → TwoSectionBezoutTrivializedIsUnitData K C V)
    (hFinite : ∀ s : V, IsFinite (twoSection s).globalHom)
    (hDominant : ∀ s : V, IsDominant (twoSection s).globalHom)
    (hEtale :
      ∀ s : V, IsEtale
        (((twoSection s).globalHom) ∣_
          (SchemeBelyi.markedBelyiTarget K hmarkedOpen).branchOpen))
    (hevalData :
      ∀ s : V, (twoSection s).evalData = evalPackage.toEvaluationData)
    (hsection0 : ∀ s : V, (twoSection s).section0 = s)
    (nonzero_avoids_marked :
      ∀ {T : Set C} {s : V},
        evalPackage.toEvaluationData.nonzeroOnSet T s →
          ∀ x ∈ T, (twoSection s).globalHom.base x ∉ markedSchemePointSet K) :
    TwoSectionBezoutProjectiveSectionFiniteMarkedFamily K C V :=
  ofFiniteDominantEtaleTwoSection evalPackage hmarkedOpen twoSection
    hFinite hDominant hEtale
    (by
      intro s x
      rw [hevalData s, hsection0 s]
      rfl)
    nonzero_avoids_marked

@[simp]
theorem ofFiniteDominantEtaleTwoSectionAligned_twoSection
    (evalPackage : RiemannRochFiniteEvaluationPackage K C V)
    (hmarkedOpen : IsOpen (markedSchemePointSet K)ᶜ)
    (twoSection : V → TwoSectionBezoutTrivializedIsUnitData K C V)
    (hFinite : ∀ s : V, IsFinite (twoSection s).globalHom)
    (hDominant : ∀ s : V, IsDominant (twoSection s).globalHom)
    (hEtale :
      ∀ s : V, IsEtale
        (((twoSection s).globalHom) ∣_
          (SchemeBelyi.markedBelyiTarget K hmarkedOpen).branchOpen))
    (hevalData :
      ∀ s : V, (twoSection s).evalData = evalPackage.toEvaluationData)
    (hsection0 : ∀ s : V, (twoSection s).section0 = s)
    (nonzero_avoids_marked :
      ∀ {T : Set C} {s : V},
        evalPackage.toEvaluationData.nonzeroOnSet T s →
          ∀ x ∈ T, (twoSection s).globalHom.base x ∉ markedSchemePointSet K) :
    (ofFiniteDominantEtaleTwoSectionAligned evalPackage hmarkedOpen twoSection
      hFinite hDominant hEtale hevalData hsection0 nonzero_avoids_marked).twoSection =
      twoSection := rfl

@[simp]
theorem ofFiniteDominantEtaleTwoSectionAligned_map_hom
    (evalPackage : RiemannRochFiniteEvaluationPackage K C V)
    (hmarkedOpen : IsOpen (markedSchemePointSet K)ᶜ)
    (twoSection : V → TwoSectionBezoutTrivializedIsUnitData K C V)
    (hFinite : ∀ s : V, IsFinite (twoSection s).globalHom)
    (hDominant : ∀ s : V, IsDominant (twoSection s).globalHom)
    (hEtale :
      ∀ s : V, IsEtale
        (((twoSection s).globalHom) ∣_
          (SchemeBelyi.markedBelyiTarget K hmarkedOpen).branchOpen))
    (hevalData :
      ∀ s : V, (twoSection s).evalData = evalPackage.toEvaluationData)
    (hsection0 : ∀ s : V, (twoSection s).section0 = s)
    (nonzero_avoids_marked :
      ∀ {T : Set C} {s : V},
        evalPackage.toEvaluationData.nonzeroOnSet T s →
          ∀ x ∈ T, (twoSection s).globalHom.base x ∉ markedSchemePointSet K)
    (s : V) :
    ((ofFiniteDominantEtaleTwoSectionAligned evalPackage hmarkedOpen twoSection
      hFinite hDominant hEtale hevalData hsection0 nonzero_avoids_marked).map s).hom =
      (twoSection s).globalHom := rfl

theorem ofFiniteDominantEtaleTwoSectionAligned_trivialized_eq_lifted
    (evalPackage : RiemannRochFiniteEvaluationPackage K C V)
    (hmarkedOpen : IsOpen (markedSchemePointSet K)ᶜ)
    (twoSection : V → TwoSectionBezoutTrivializedIsUnitData K C V)
    (hFinite : ∀ s : V, IsFinite (twoSection s).globalHom)
    (hDominant : ∀ s : V, IsDominant (twoSection s).globalHom)
    (hEtale :
      ∀ s : V, IsEtale
        (((twoSection s).globalHom) ∣_
          (SchemeBelyi.markedBelyiTarget K hmarkedOpen).branchOpen))
    (hevalData :
      ∀ s : V, (twoSection s).evalData = evalPackage.toEvaluationData)
    (hsection0 : ∀ s : V, (twoSection s).section0 = s)
    (nonzero_avoids_marked :
      ∀ {T : Set C} {s : V},
        evalPackage.toEvaluationData.nonzeroOnSet T s →
          ∀ x ∈ T, (twoSection s).globalHom.base x ∉ markedSchemePointSet K)
    (s : V) :
    (ofFiniteDominantEtaleTwoSectionAligned evalPackage hmarkedOpen twoSection
      hFinite hDominant hEtale hevalData hsection0 nonzero_avoids_marked).trivialized s =
      (twoSection s).toTrivializedIsUnitSectionRatioDataLifted := rfl

theorem trivialized_evalData_eq_spec (s : V) :
    (F.trivialized s).evalData = (F.twoSection s).evalData :=
  F.trivialized_evalData_eq s

theorem trivialized_section0_eq_spec (s : V) :
    (F.trivialized s).section0 = (F.twoSection s).section0 :=
  F.trivialized_section0_eq s

theorem trivialized_section1_eq_spec (s : V) :
    (F.trivialized s).section1 = (F.twoSection s).section1 :=
  F.trivialized_section1_eq s

theorem trivialized_globalHom_eq_spec (s : V) :
    (F.trivialized s).globalHom = (F.twoSection s).globalHom :=
  F.trivialized_globalHom_eq s

/-- Forget the canonical two-section package to the denominator-is-unit finite
marked family interface. -/
def toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily :
    IsUnitTrivializedProjectiveSectionFiniteMarkedFamily K C V :=
  F.isUnitFamily

theorem toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily_map_apply
    (s : V) :
    F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.map s = F.map s := rfl

/-- The projective-section pair supplied by the canonical two-section Bezout
package. -/
def twoSectionPair (s : V) : ProjectiveLineSectionPair K C V :=
  (F.twoSection s).toProjectiveLineSectionPair

theorem twoSectionPair_hom (s : V) :
    (F.twoSectionPair s).hom = (F.twoSection s).globalHom := rfl

/-- The finite marked map has the same underlying point map as the canonical
two-section global morphism. -/
theorem map_base_eq_twoSection_globalHom (s : V) (x : C) :
    (F.map s).hom.base x = (F.twoSection s).globalHom.base x := by
  calc
    (F.map s).hom.base x = (F.trivialized s).globalHom.base x :=
      F.isUnitFamily.map_base_eq_globalHom s x
    _ = (F.twoSection s).globalHom.base x := by
      rw [F.trivialized_globalHom_eq_spec s]

/-- The finite marked map has the same underlying point map as the canonical
two-section projective-section pair. -/
theorem map_base_eq_twoSectionPair (s : V) (x : C) :
    (F.map s).hom.base x = (F.twoSectionPair s).hom.base x := by
  rw [F.twoSectionPair_hom s]
  exact F.map_base_eq_twoSection_globalHom s x

theorem twoSectionPair_section0_eval_eq_index (s : V) (x : C) :
    (F.twoSectionPair s).evalData.eval x (F.twoSectionPair s).section0 =
      F.evalPackage.eval x s := by
  change (F.twoSection s).evalData.eval x (F.twoSection s).section0 =
    F.evalPackage.eval x s
  rw [← F.trivialized_evalData_eq_spec s, ← F.trivialized_section0_eq_spec s]
  exact F.isUnitFamily.trivialized_section0_eval_eq_index s x

/-- Forget the finite marked family through the canonical two-section
projective-section pairs. -/
def toProjectiveSectionFiniteMarkedFamilyViaTwoSection :
    ProjectiveSectionFiniteMarkedFamily K C V where
  evalPackage := F.evalPackage
  hmarkedOpen := F.hmarkedOpen
  pair := F.twoSectionPair
  map := F.map
  map_base_eq_pair := F.map_base_eq_twoSectionPair
  pair_section0_eval_eq_index := F.twoSectionPair_section0_eval_eq_index
  nonzero_avoids_marked := by
    intro T s hs
    exact F.isUnitFamily.nonzero_avoids_marked hs

theorem toProjectiveSectionFiniteMarkedFamilyViaTwoSection_map_apply
    (s : V) :
    F.toProjectiveSectionFiniteMarkedFamilyViaTwoSection.map s = F.map s := rfl

/-- Each canonical two-section finite marked family map is finite. -/
theorem map_finite_hom
    (s : V) :
    IsFinite (F.map s).hom :=
  SchemeBelyi.FiniteBelyiMap.isFinite_hom (F.map s)

/-- Each canonical two-section finite marked family map is dominant. -/
theorem map_isDominant_hom
    (s : V) :
    IsDominant (F.map s).hom :=
  SchemeBelyi.FiniteBelyiMap.isDominant_hom (F.map s)

/-- Each canonical two-section finite marked family map has dense range on
underlying spaces. -/
theorem map_denseRange_hom
    (s : V) :
    DenseRange (F.map s).hom.base :=
  SchemeBelyi.FiniteBelyiMap.denseRange_hom (F.map s)

/-- Each canonical two-section finite marked family map is etale over the
marked branch-complement open. -/
theorem map_isEtale_restrict_branchOpen
    (s : V) :
    IsEtale ((F.map s).hom ∣_
      (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.isEtale_restrict_branchOpen (F.map s)

/-- The branch-open restriction of each canonical two-section map is finite. -/
theorem map_isFinite_restrict_branchOpen
    (s : V) :
    IsFinite ((F.map s).hom ∣_
      (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.isFinite_restrict_branchOpen (F.map s)

/-- The branch-open restriction of each canonical two-section map is affine. -/
theorem map_isAffineHom_restrict_branchOpen
    (s : V) :
    IsAffineHom ((F.map s).hom ∣_
      (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.isAffineHom_restrict_branchOpen (F.map s)

/-- The branch-open restriction of each canonical two-section map is integral. -/
theorem map_isIntegralHom_restrict_branchOpen
    (s : V) :
    IsIntegralHom ((F.map s).hom ∣_
      (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.isIntegralHom_restrict_branchOpen (F.map s)

/-- The branch-open restriction of each canonical two-section map is locally of
finite type. -/
theorem map_locallyOfFiniteType_restrict_branchOpen
    (s : V) :
    LocallyOfFiniteType ((F.map s).hom ∣_
      (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.locallyOfFiniteType_restrict_branchOpen (F.map s)

/-- The branch-open restriction of each canonical two-section map is separated. -/
theorem map_isSeparated_restrict_branchOpen
    (s : V) :
    IsSeparated ((F.map s).hom ∣_
      (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.isSeparated_restrict_branchOpen (F.map s)

/-- The branch-open restriction of each canonical two-section map is
quasi-compact. -/
theorem map_quasiCompact_restrict_branchOpen
    (s : V) :
    QuasiCompact ((F.map s).hom ∣_
      (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.quasiCompact_restrict_branchOpen (F.map s)

/-- Each canonical two-section finite marked family map is affine. -/
theorem map_isAffineHom_hom
    (s : V) :
    IsAffineHom (F.map s).hom :=
  SchemeBelyi.FiniteBelyiMap.isAffineHom_hom (F.map s)

/-- Each canonical two-section finite marked family map is integral. -/
theorem map_isIntegralHom_hom
    (s : V) :
    IsIntegralHom (F.map s).hom :=
  SchemeBelyi.FiniteBelyiMap.isIntegralHom_hom (F.map s)

/-- Each canonical two-section finite marked family map is locally of finite
type. -/
theorem map_locallyOfFiniteType_hom
    (s : V) :
    LocallyOfFiniteType (F.map s).hom :=
  SchemeBelyi.FiniteBelyiMap.locallyOfFiniteType_hom (F.map s)

/-- Each canonical two-section finite marked family map is separated. -/
theorem map_isSeparated_hom
    (s : V) :
    IsSeparated (F.map s).hom :=
  SchemeBelyi.FiniteBelyiMap.isSeparated_hom (F.map s)

/-- Each canonical two-section finite marked family map is quasi-compact. -/
theorem map_quasiCompact_hom
    (s : V) :
    QuasiCompact (F.map s).hom :=
  SchemeBelyi.FiniteBelyiMap.quasiCompact_hom (F.map s)

theorem toFiniteMarkedBelyiExistence_mem_belyiOpen_iff
    [Infinite K] (s : V) (x : C) :
    x ∈ (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
      F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s ↔
      (F.map s).hom.base x ∉ markedSchemePointSet K := by
  exact
    IsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toFiniteMarkedBelyiExistence_mem_belyiOpen_iff
      F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily s x

theorem toFiniteMarkedBelyiExistence_belyiOpen_carrier
    [Infinite K] (s : V) :
    (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
      F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s =
      {x : C | (F.map s).hom.base x ∉ markedSchemePointSet K} := by
  exact
    IsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toFiniteMarkedBelyiExistence_belyiOpen_carrier
      F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily s

theorem toFiniteMarkedBelyiExistence_belyiOpen_eq_schemeBelyi
    [Infinite K] (s : V) :
    (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
      F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s =
      ((F.map s).toBelyiMap.belyiOpen : Set C) := by
  exact
    IsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toFiniteMarkedBelyiExistence_belyiOpen_eq_schemeBelyi
      F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily s

/-- Pointwise zero-evaluation branch consequence for canonical two-section
Bezout finite marked families. -/
theorem eval_zero_to_marked
    (s : V) {x : C} (hx : F.evalPackage.eval x s = 0) :
    (F.map s).hom.base x ∈ markedSchemePointSet K := by
  exact IsUnitTrivializedProjectiveSectionFiniteMarkedFamily.eval_zero_to_marked
    F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily s hx

/-- Pointwise nonzero-evaluation branch-avoidance consequence for canonical
two-section Bezout finite marked families. -/
theorem eval_nonzero_avoids_marked
    (s : V) {x : C} (hx : F.evalPackage.eval x s ≠ 0) :
    (F.map s).hom.base x ∉ markedSchemePointSet K := by
  exact IsUnitTrivializedProjectiveSectionFiniteMarkedFamily.eval_nonzero_avoids_marked
    F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily s hx

/-- Direct finite disjoint-set conclusion for canonical two-section Bezout
finite marked families. -/
theorem exists_for_finite_disjoint
    [Infinite K] {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V, (∀ x ∈ S, (F.map s).hom.base x ∈ markedSchemePointSet K) ∧
      ∀ x ∈ T, (F.map s).hom.base x ∉ markedSchemePointSet K := by
  exact IsUnitTrivializedProjectiveSectionFiniteMarkedFamily.exists_for_finite_disjoint
    F.isUnitFamily hS hT hdis

/-- Direct Belyi-open controls for canonical two-section Bezout finite marked
families. -/
theorem exists_map_belyiOpen_controls
    [Infinite K] {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V, T ⊆ ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
      ((F.map s).toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  exact IsUnitTrivializedProjectiveSectionFiniteMarkedFamily.exists_map_belyiOpen_controls
    F.isUnitFamily hS hT hdis

/-- Direct same-map marked and Belyi-open controls for canonical two-section
Bezout finite marked families. -/
theorem exists_map_controls_and_belyiOpen_controls
    [Infinite K] {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V,
      ((∀ x ∈ S, (F.map s).hom.base x ∈ markedSchemePointSet K) ∧
        ∀ x ∈ T, (F.map s).hom.base x ∉ markedSchemePointSet K) ∧
        T ⊆ ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
          ((F.map s).toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  exact IsUnitTrivializedProjectiveSectionFiniteMarkedFamily.exists_map_controls_and_belyiOpen_controls
    F.isUnitFamily hS hT hdis

/-- Direct same-map marked, open, and Belyi-open controls for canonical
two-section Bezout finite marked families. -/
theorem exists_map_controls_and_isOpen_belyiOpen_controls
    [Infinite K] {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V,
      ((∀ x ∈ S, (F.map s).hom.base x ∈ markedSchemePointSet K) ∧
        ∀ x ∈ T, (F.map s).hom.base x ∉ markedSchemePointSet K) ∧
        IsOpen ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
          T ⊆ ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
            ((F.map s).toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  exact IsUnitTrivializedProjectiveSectionFiniteMarkedFamily.exists_map_controls_and_isOpen_belyiOpen_controls
    F.isUnitFamily hS hT hdis

/-- Actual finite-map one-point finite-complement-open consequence for
canonical two-section Bezout finite marked families. -/
theorem exists_map_belyiOpen_inside_open_of_finite_complement
    [Infinite K]
    {U : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite) {x : C} (hxU : x ∈ U) :
    ∃ s : V,
      IsOpen ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
        x ∈ ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
          ((F.map s).toBelyiMap.belyiOpen : Set C) ⊆ U := by
  exact
    IsUnitTrivializedProjectiveSectionFiniteMarkedFamily.exists_map_belyiOpen_inside_open_of_finite_complement
      F.isUnitFamily hU hUcompl hxU

/-- Actual finite-map finite-set finite-complement-open consequence for
canonical two-section Bezout finite marked families. -/
theorem exists_map_belyiOpen_containing_finite_inside_open_of_finite_complement
    [Infinite K]
    {U T : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ s : V,
      IsOpen ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
        T ⊆ ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
          ((F.map s).toBelyiMap.belyiOpen : Set C) ⊆ U := by
  exact
    IsUnitTrivializedProjectiveSectionFiniteMarkedFamily.exists_map_belyiOpen_containing_finite_inside_open_of_finite_complement
      F.isUnitFamily hU hUcompl hT hTsub

/-- Actual finite-map finite-complement-open consequence retaining marked
controls for canonical two-section Bezout finite marked families. -/
theorem exists_map_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_finite_complement
    [Infinite K]
    {U T : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ s : V,
      ((∀ x ∈ Uᶜ, (F.map s).hom.base x ∈ markedSchemePointSet K) ∧
        ∀ x ∈ T, (F.map s).hom.base x ∉ markedSchemePointSet K) ∧
        IsOpen ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
          T ⊆ ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
            ((F.map s).toBelyiMap.belyiOpen : Set C) ⊆ U := by
  exact
    IsUnitTrivializedProjectiveSectionFiniteMarkedFamily.exists_map_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_finite_complement
      F.isUnitFamily hU hUcompl hT hTsub

/-- Actual finite-map nonempty-open finite-complement consequence retaining
marked controls for canonical two-section Bezout finite marked families. -/
theorem exists_map_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
    [Infinite K] [NonemptyOpenFiniteComplement C]
    {U T : Set C} (hU : IsOpen U) (hUne : U.Nonempty)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ s : V,
      ((∀ x ∈ Uᶜ, (F.map s).hom.base x ∈ markedSchemePointSet K) ∧
        ∀ x ∈ T, (F.map s).hom.base x ∉ markedSchemePointSet K) ∧
        IsOpen ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
          T ⊆ ((F.map s).toBelyiMap.belyiOpen : Set C) ∧
            ((F.map s).toBelyiMap.belyiOpen : Set C) ⊆ U := by
  exact
    IsUnitTrivializedProjectiveSectionFiniteMarkedFamily.exists_map_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
      F.isUnitFamily hU hUne hT hTsub

/-- Direct one-point Belyi-open consequence for canonical two-section Bezout
finite marked families. -/
theorem exists_belyiOpen_inside_complement
    [Infinite K] [T1Space (P1 K)]
    {A : Set C} (hA : A.Finite) {x : C} (hxA : x ∉ A) :
    ∃ s : V,
      IsOpen ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        x ∈ ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ Aᶜ := by
  exact
    IsUnitTrivializedProjectiveSectionFiniteMarkedFamily.exists_belyiOpen_inside_complement
      F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily hA hxA

/-- Direct finite-set Belyi-open consequence for canonical two-section Bezout
finite marked families, inside the complement of a finite source set. -/
theorem exists_belyiOpen_containing_finite_inside_complement
    [Infinite K] [T1Space (P1 K)]
    {S T : Set C} (hS : S.Finite) (hT : T.Finite) (hdis : Disjoint S T) :
    ∃ s : V,
      IsOpen ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        T ⊆ ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ Sᶜ := by
  exact
    IsUnitTrivializedProjectiveSectionFiniteMarkedFamily.exists_belyiOpen_containing_finite_inside_complement
      F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily hS hT hdis

/-- Direct one-point Belyi-open consequence for canonical two-section Bezout
finite marked families, with the finite complement supplied explicitly. -/
theorem exists_belyiOpen_inside_open_of_finite_complement
    [Infinite K] [T1Space (P1 K)]
    {U : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite) {x : C} (hxU : x ∈ U) :
    ∃ s : V,
      IsOpen ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        x ∈ ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ U := by
  exact
    IsUnitTrivializedProjectiveSectionFiniteMarkedFamily.exists_belyiOpen_inside_open_of_finite_complement
      F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily hU hUcompl hxU

/-- Direct finite-set Belyi-open consequence for canonical two-section Bezout
finite marked families, with the finite complement supplied explicitly. -/
theorem exists_belyiOpen_containing_finite_inside_open_of_finite_complement
    [Infinite K] [T1Space (P1 K)]
    {U T : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ s : V,
      IsOpen ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        T ⊆ ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ U := by
  exact
    IsUnitTrivializedProjectiveSectionFiniteMarkedFamily.exists_belyiOpen_containing_finite_inside_open_of_finite_complement
      F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily hU hUcompl hT hTsub

/-- Direct one-point Belyi-open consequence for canonical two-section Bezout
finite marked families in the curve-style finite-complement topology form. -/
theorem exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C]
    {U : Set C} (hU : IsOpen U) {x : C} (hxU : x ∈ U) :
    ∃ s : V,
      IsOpen ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        x ∈ ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ U := by
  exact
    IsUnitTrivializedProjectiveSectionFiniteMarkedFamily.exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
      F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily hU hxU

/-- Direct finite-set Belyi-open consequence for canonical two-section Bezout
finite marked families in the curve-style finite-complement topology form. -/
theorem exists_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C]
    {U T : Set C} (hU : IsOpen U) (hUne : U.Nonempty)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ s : V,
      IsOpen ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        T ⊆ ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ U := by
  exact
    IsUnitTrivializedProjectiveSectionFiniteMarkedFamily.exists_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
      F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily hU hUne hT hTsub

/-- Direct finite tuple-subcover consequence for canonical two-section Bezout
finite marked families. -/
theorem finite_subcover_on_complement
    [Infinite K] (κ : Type*) [Finite κ] [T1Space (P1 K)]
    {S : Set C} (hS : S.Finite) [CompactSpace (κ → {x : C // x ∉ S})] :
    ∃ t : Finset {s : V //
        (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedCoverData K V
          F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).sendsSetToBranch S s},
      (⋃ s ∈ t, ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedCoverData K V
            F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).complementCoverData S).tupleAvoidSet
              (κ := κ) s) =
        (Set.univ : Set (κ → {x : C // x ∉ S})) := by
  exact
    IsUnitTrivializedProjectiveSectionFiniteMarkedFamily.finite_subcover_on_complement
      F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily κ hS

/-- Direct finite tuple-subcover consequence for canonical two-section Bezout
finite marked families, in membership form. -/
theorem finite_subcover_on_complement_forall
    [Infinite K] (κ : Type*) [Finite κ] [T1Space (P1 K)]
    {S : Set C} (hS : S.Finite) [CompactSpace (κ → {x : C // x ∉ S})] :
    ∃ t : Finset {s : V //
        (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedCoverData K V
          F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).sendsSetToBranch S s},
      ∀ x : κ → {x : C // x ∉ S},
        ∃ s ∈ t,
          x ∈ ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedCoverData K V
            F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).complementCoverData S).tupleAvoidSet
              (κ := κ) s := by
  exact
    IsUnitTrivializedProjectiveSectionFiniteMarkedFamily.finite_subcover_on_complement_forall
      F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily κ hS

/-- Direct finite tuple-subcover consequence for canonical two-section Bezout
finite marked families, in concrete marked-avoidance form. -/
theorem finite_subcover_on_complement_forall_avoidance
    [Infinite K] (κ : Type*) [Finite κ] [T1Space (P1 K)]
    {S : Set C} (hS : S.Finite) [CompactSpace (κ → {x : C // x ∉ S})] :
    ∃ t : Finset {s : V //
        (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedCoverData K V
          F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).sendsSetToBranch S s},
      ∀ x : κ → {x : C // x ∉ S},
        ∃ s ∈ t, ∀ i, (F.map s.1).hom.base (x i).1 ∉ markedSchemePointSet K := by
  rcases
      IsUnitTrivializedProjectiveSectionFiniteMarkedFamily.finite_subcover_on_complement_forall_avoidance
        F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily κ hS with
    ⟨t, ht⟩
  refine ⟨t, ?_⟩
  intro x
  rcases ht x with ⟨s, hst, hsx⟩
  exact ⟨s, hst, by
    simpa [toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily, map] using hsx⟩

/-- Compact-exhaustion cover bridge for canonical two-section Bezout finite
marked families. -/
theorem finite_compact_cover_by_belyiOpen_exhaustions
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    (Kex : ∀ s : V,
      CompactExhaustion ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s)) :
    ∃ t : Finset (V × ℕ),
      (∀ p ∈ t,
        IsCompact ((Subtype.val :
          (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
            (Kex p.1 p.2))) ∧
        (∀ p ∈ t,
          ((Subtype.val :
            (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
              F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
              (Kex p.1 p.2)) ⊆
                (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                  F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1) ∧
          (Set.univ : Set C) ⊆
            ⋃ p ∈ t,
              (Subtype.val :
                (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                  F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
                (Kex p.1 p.2) := by
  exact
    IsUnitTrivializedProjectiveSectionFiniteMarkedFamily.finite_compact_cover_by_belyiOpen_exhaustions
      F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily Kex

/-- Equality form of the compact-exhaustion cover bridge for canonical
two-section Bezout finite marked families. -/
theorem finite_compact_cover_by_belyiOpen_exhaustions_eq_univ
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    (Kex : ∀ s : V,
      CompactExhaustion ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s)) :
    ∃ t : Finset (V × ℕ),
      (∀ p ∈ t,
        IsCompact ((Subtype.val :
          (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
            (Kex p.1 p.2))) ∧
        (∀ p ∈ t,
          ((Subtype.val :
            (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
              F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
              (Kex p.1 p.2)) ⊆
                (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                  F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1) ∧
          (⋃ p ∈ t,
            (Subtype.val :
              (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
              (Kex p.1 p.2)) = (Set.univ : Set C) := by
  exact
    IsUnitTrivializedProjectiveSectionFiniteMarkedFamily.finite_compact_cover_by_belyiOpen_exhaustions_eq_univ
      F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily Kex

/-- Compact-cover bridge for canonical two-section Bezout finite marked
families, with compact exhaustions supplied by local compactness and second
countability. -/
theorem finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    [LocallyCompactSpace C] [SecondCountableTopology C] :
    ∃ Kex : ∀ s : V,
      CompactExhaustion ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s),
      ∃ t : Finset (V × ℕ),
        (∀ p ∈ t,
          IsCompact ((Subtype.val :
            (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
              F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
              (Kex p.1 p.2))) ∧
          (∀ p ∈ t,
            ((Subtype.val :
              (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
                (Kex p.1 p.2)) ⊆
                  (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                    F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1) ∧
            (Set.univ : Set C) ⊆
              ⋃ p ∈ t,
                (Subtype.val :
                  (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                    F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
                  (Kex p.1 p.2) := by
  exact
    IsUnitTrivializedProjectiveSectionFiniteMarkedFamily.finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact
      F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily

/-- Equality form of the compact-cover bridge for canonical two-section Bezout
finite marked families, with compact exhaustions supplied by local compactness
and second countability. -/
theorem finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact_eq_univ
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    [LocallyCompactSpace C] [SecondCountableTopology C] :
    ∃ Kex : ∀ s : V,
      CompactExhaustion ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s),
      ∃ t : Finset (V × ℕ),
        (∀ p ∈ t,
          IsCompact ((Subtype.val :
            (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
              F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
              (Kex p.1 p.2))) ∧
          (∀ p ∈ t,
            ((Subtype.val :
              (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
                (Kex p.1 p.2)) ⊆
                  (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                    F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1) ∧
            (⋃ p ∈ t,
              (Subtype.val :
                (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                  F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
                (Kex p.1 p.2)) = (Set.univ : Set C) := by
  exact
    IsUnitTrivializedProjectiveSectionFiniteMarkedFamily.finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact_eq_univ
      F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily

/-- Compact-coordinate Corollary 3.2 bridge for canonical two-section Bezout
finite marked families. -/
theorem finite_compact_coordinate_sets_of_belyiOpen_exhaustions
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    [LocallyCompactSpace C] [SecondCountableTopology C]
    {κ : Type*} {Z : κ → Type*} [∀ j, TopologicalSpace (Z j)]
    (G : V → C → ((j : κ) → Z j))
    (hG : ∀ s, Continuous (G s))
    (A : (j : κ) → Set (Z j))
    (hGA : ∀ s x,
      x ∈ (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s →
        ∀ j, G s x j ∈ A j) :
    ∃ Kex : ∀ s : V,
      CompactExhaustion ((SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s),
      ∃ t : Finset (V × ℕ),
        ∃ H : (j : κ) → Set (Z j),
          (∀ j, IsCompact (H j)) ∧
            (∀ j, H j ⊆ A j) ∧
              (Set.univ : Set C) ⊆
                ⋃ p ∈ t,
                  (Subtype.val :
                    (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                      F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 →
                      C) ''
                    (Kex p.1 p.2) ∧
                ∀ p ∈ t, ∀ x,
                  x ∈ (Subtype.val :
                    (SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                      F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 →
                      C) ''
                      (Kex p.1 p.2) →
                    ∀ j, G p.1 x j ∈ H j := by
  exact
    IsUnitTrivializedProjectiveSectionFiniteMarkedFamily.finite_compact_coordinate_sets_of_belyiOpen_exhaustions
      F.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily G hG A hGA

end TwoSectionBezoutProjectiveSectionFiniteMarkedFamily

end ProjectiveSectionMaps
end SourceStack
end HilbertTest
