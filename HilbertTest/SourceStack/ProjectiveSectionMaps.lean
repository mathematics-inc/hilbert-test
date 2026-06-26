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

def toProjectiveLineSectionPair : ProjectiveLineSectionPair K C V :=
  D.toGluedProjectiveLineSectionData.toProjectiveLineSectionPair

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

def toProjectiveLineSectionPair : ProjectiveLineSectionPair K C V :=
  D.toStandardChartProjectiveLineSectionData.toProjectiveLineSectionPair

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

def toProjectiveLineSectionPair : ProjectiveLineSectionPair K C V :=
  D.toStandardChartProjectiveLineSectionRingData.toProjectiveLineSectionPair

theorem toProjectiveLineSectionPair_hom :
    D.toProjectiveLineSectionPair.hom = D.globalHom := rfl

theorem toProjectiveLineSectionPair_maps_section0_zero_to_marked
    {x : C} (hx : D.evalData.eval x D.section0 = 0) :
    D.toProjectiveLineSectionPair.hom.base x ∈ markedSchemePointSet K := by
  exact D.toProjectiveLineSectionPair.maps_section0_zero_to_marked hx

end SectionRatioProjectiveLineSectionData

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

def toProjectiveLineSectionPair : ProjectiveLineSectionPair K C V :=
  D.toSectionRatioProjectiveLineSectionData.toProjectiveLineSectionPair

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

theorem toProjectiveLineSectionPair_hom :
    D.toProjectiveLineSectionPair.hom = D.globalHom := rfl

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

def globalHom : C ⟶ P1 K :=
  D.toTrivializedUnitSectionRatioData.globalHom

def toProjectiveLineSectionPair : ProjectiveLineSectionPair K C V :=
  D.toTrivializedUnitSectionRatioData.toProjectiveLineSectionPair

theorem toProjectiveLineSectionPair_hom :
    D.toProjectiveLineSectionPair.hom = D.globalHom := rfl

theorem toProjectiveLineSectionPair_maps_section0_zero_to_marked
    {x : C} (hx : D.evalData.eval x D.section0 = 0) :
    D.toProjectiveLineSectionPair.hom.base x ∈ markedSchemePointSet K := by
  exact D.toProjectiveLineSectionPair.maps_section0_zero_to_marked hx

end TrivializedIsUnitSectionRatioData

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

/-- Direct finite disjoint-set conclusion for the concrete trivialized-ratio
finite marked family. -/
theorem exists_for_finite_disjoint
    [Infinite K] {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V, (∀ x ∈ S, (F.map s).hom.base x ∈ markedSchemePointSet K) ∧
      ∀ x ∈ T, (F.map s).hom.base x ∉ markedSchemePointSet K := by
  exact F.toProjectiveSectionFiniteMarkedFamily.exists_for_finite_disjoint
    hS hT hdis

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

/-- Direct finite disjoint-set conclusion for denominator-is-unit trivialized
finite marked families. -/
theorem exists_for_finite_disjoint
    [Infinite K] {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V, (∀ x ∈ S, (F.map s).hom.base x ∈ markedSchemePointSet K) ∧
      ∀ x ∈ T, (F.map s).hom.base x ∉ markedSchemePointSet K := by
  exact F.toProjectiveSectionFiniteMarkedFamily.exists_for_finite_disjoint
    hS hT hdis

end IsUnitTrivializedProjectiveSectionFiniteMarkedFamily

end ProjectiveSectionMaps
end SourceStack
end HilbertTest
