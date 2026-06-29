import HilbertTest.SourceStack.CurveBelyiConstruction
import HilbertTest.SourceStack.SchemeMarkedBelyi

/-!
Scheme-level bridge from section-controlled curve data to finite marked Belyi
families.

This module is still an interface layer: it does not construct the projective
line morphisms from line-bundle sections.  It proves that once such a
construction supplies finite marked Belyi maps whose marked-branch behavior is
controlled by section vanishing/nonvanishing, the paper-facing
`FiniteMarkedBelyiExistence` structure follows.
-/

noncomputable section

open AlgebraicGeometry

namespace HilbertTest
namespace SourceStack
namespace SchemeCurveBelyiConstruction

open CurveRiemannRoch
open CurveBelyiConstruction
open SchemeProjectiveLine
open SchemeMarkedBelyi

universe u w z

/-- Scheme-level section-controlled finite marked Belyi data.  The missing
curve/line-bundle construction should instantiate this structure for smooth
proper connected curves. -/
structure SectionControlledFiniteMarkedBelyiData
    (K : Type u) [Field K] (C : Scheme.{u})
    (V : Type w) [AddCommGroup V] [Module K V] where
  evalPackage : RiemannRochFiniteEvaluationPackage K C V
  hmarkedOpen : IsOpen (markedSchemePointSet K)ᶜ
  map : V → SchemeBelyi.FiniteBelyiMap
    (SchemeBelyi.markedBelyiTarget K hmarkedOpen) C
  sends_vanishing_to_marked :
    ∀ {S : Set C} {s : V},
      evalPackage.toEvaluationData.vanishesOnSet S s →
        ∀ x ∈ S, (map s).hom.base x ∈ markedSchemePointSet K
  nonzero_avoids_marked :
    ∀ {T : Set C} {s : V},
      evalPackage.toEvaluationData.nonzeroOnSet T s →
        ∀ x ∈ T, (map s).hom.base x ∉ markedSchemePointSet K

namespace SectionControlledFiniteMarkedBelyiData

variable {K : Type u} [Field K]
variable {C : Scheme.{u}}
variable {V : Type w} [AddCommGroup V] [Module K V]
variable (D : SectionControlledFiniteMarkedBelyiData K C V)

/-- Forget scheme-level finite marked Belyi data to the topological
section-controlled interface. -/
def toSectionControlledBelyiData :
    SectionControlledBelyiData K C (P1 K) V where
  evalPackage := D.evalPackage
  branch := markedSchemePointSet K
  branch_finite := markedSchemePointSet_finite K
  map s x := (D.map s).hom.base x
  continuous_map s := (D.map s).hom.continuous
  sends_vanishing_to_branch := by
    intro S s hs
    exact D.sends_vanishing_to_marked hs
  nonzero_avoids_branch := by
    intro T s hs
    exact D.nonzero_avoids_marked hs

theorem toSectionControlledBelyiData_branch :
    D.toSectionControlledBelyiData.branch = markedSchemePointSet K := rfl

theorem toSectionControlledBelyiData_map_apply
    (s : V) (x : C) :
    D.toSectionControlledBelyiData.map s x = (D.map s).hom.base x := rfl

/-- A pointwise zero evaluation sends the associated finite marked Belyi map
into the marked branch set. -/
theorem eval_zero_to_marked
    (s : V) {x : C} (hx : D.evalPackage.eval x s = 0) :
    (D.map s).hom.base x ∈ markedSchemePointSet K := by
  exact D.sends_vanishing_to_marked (S := {x}) (s := s)
    (by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact hx)
    x (by simp)

/-- A pointwise nonzero evaluation makes the associated finite marked Belyi map
avoid the marked branch set. -/
theorem eval_nonzero_avoids_marked
    (s : V) {x : C} (hx : D.evalPackage.eval x s ≠ 0) :
    (D.map s).hom.base x ∉ markedSchemePointSet K := by
  exact D.nonzero_avoids_marked (T := {x}) (s := s)
    (by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact hx)
    x (by simp)

/-- The scheme-level section-controlled package instantiates the paper-facing
finite marked Belyi existence interface over an infinite field. -/
def toFiniteMarkedBelyiExistence [Infinite K] :
    FiniteMarkedBelyiExistence K V C where
  hmarkedOpen := D.hmarkedOpen
  map := D.map
  exists_for_finite_disjoint := by
    intro S T hS hT hdis
    rcases D.evalPackage.exists_section_for_disjoint_finite_sets hS hT hdis with
      ⟨s, hsS, hsT⟩
    exact
      ⟨s,
        D.sends_vanishing_to_marked hsS,
        D.nonzero_avoids_marked hsT⟩

theorem toFiniteMarkedBelyiExistence_hmarkedOpen
    [Infinite K] :
    D.toFiniteMarkedBelyiExistence.hmarkedOpen = D.hmarkedOpen := rfl

theorem toFiniteMarkedBelyiExistence_map_apply
    [Infinite K] (s : V) :
    D.toFiniteMarkedBelyiExistence.map s = D.map s := rfl

/-- Each section-controlled finite marked family map is finite. -/
theorem map_finite_hom
    (s : V) :
    IsFinite (D.map s).hom :=
  SchemeBelyi.FiniteBelyiMap.isFinite_hom (D.map s)

/-- Each section-controlled finite marked family map is dominant. -/
theorem map_isDominant_hom
    (s : V) :
    IsDominant (D.map s).hom :=
  SchemeBelyi.FiniteBelyiMap.isDominant_hom (D.map s)

/-- Each section-controlled finite marked family map has dense range on
underlying spaces. -/
theorem map_denseRange_hom
    (s : V) :
    DenseRange (D.map s).hom.base :=
  SchemeBelyi.FiniteBelyiMap.denseRange_hom (D.map s)

/-- Each section-controlled finite marked family map is etale over the marked
branch-complement open. -/
theorem map_isEtale_restrict_branchOpen
    (s : V) :
    IsEtale ((D.map s).hom ∣_
      (SchemeBelyi.markedBelyiTarget K D.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.isEtale_restrict_branchOpen (D.map s)

/-- The branch-open restriction of each section-controlled map is finite. -/
theorem map_isFinite_restrict_branchOpen
    (s : V) :
    IsFinite ((D.map s).hom ∣_
      (SchemeBelyi.markedBelyiTarget K D.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.isFinite_restrict_branchOpen (D.map s)

/-- The branch-open restriction of each section-controlled map is affine. -/
theorem map_isAffineHom_restrict_branchOpen
    (s : V) :
    IsAffineHom ((D.map s).hom ∣_
      (SchemeBelyi.markedBelyiTarget K D.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.isAffineHom_restrict_branchOpen (D.map s)

/-- The branch-open restriction of each section-controlled map is integral. -/
theorem map_isIntegralHom_restrict_branchOpen
    (s : V) :
    IsIntegralHom ((D.map s).hom ∣_
      (SchemeBelyi.markedBelyiTarget K D.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.isIntegralHom_restrict_branchOpen (D.map s)

/-- The branch-open restriction of each section-controlled map is locally of
finite type. -/
theorem map_locallyOfFiniteType_restrict_branchOpen
    (s : V) :
    LocallyOfFiniteType ((D.map s).hom ∣_
      (SchemeBelyi.markedBelyiTarget K D.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.locallyOfFiniteType_restrict_branchOpen (D.map s)

/-- The branch-open restriction of each section-controlled map is separated. -/
theorem map_isSeparated_restrict_branchOpen
    (s : V) :
    IsSeparated ((D.map s).hom ∣_
      (SchemeBelyi.markedBelyiTarget K D.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.isSeparated_restrict_branchOpen (D.map s)

/-- The branch-open restriction of each section-controlled map is quasi-compact. -/
theorem map_quasiCompact_restrict_branchOpen
    (s : V) :
    QuasiCompact ((D.map s).hom ∣_
      (SchemeBelyi.markedBelyiTarget K D.hmarkedOpen).branchOpen) :=
  SchemeBelyi.FiniteBelyiMap.quasiCompact_restrict_branchOpen (D.map s)

/-- Each section-controlled finite marked family map is affine. -/
theorem map_isAffineHom_hom
    (s : V) :
    IsAffineHom (D.map s).hom :=
  SchemeBelyi.FiniteBelyiMap.isAffineHom_hom (D.map s)

/-- Each section-controlled finite marked family map is integral. -/
theorem map_isIntegralHom_hom
    (s : V) :
    IsIntegralHom (D.map s).hom :=
  SchemeBelyi.FiniteBelyiMap.isIntegralHom_hom (D.map s)

/-- Each section-controlled finite marked family map is locally of finite type. -/
theorem map_locallyOfFiniteType_hom
    (s : V) :
    LocallyOfFiniteType (D.map s).hom :=
  SchemeBelyi.FiniteBelyiMap.locallyOfFiniteType_hom (D.map s)

/-- Each section-controlled finite marked family map is separated. -/
theorem map_isSeparated_hom
    (s : V) :
    IsSeparated (D.map s).hom :=
  SchemeBelyi.FiniteBelyiMap.isSeparated_hom (D.map s)

/-- Each section-controlled finite marked family map is quasi-compact. -/
theorem map_quasiCompact_hom
    (s : V) :
    QuasiCompact (D.map s).hom :=
  SchemeBelyi.FiniteBelyiMap.quasiCompact_hom (D.map s)

theorem toFiniteMarkedBelyiExistence_mem_belyiOpen_iff
    [Infinite K] (s : V) (x : C) :
    x ∈ (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
      D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s ↔
      (D.map s).hom.base x ∉ markedSchemePointSet K := by
  exact
    FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence_mem_belyiOpen_iff
      K V D.toFiniteMarkedBelyiExistence s x

theorem toFiniteMarkedBelyiExistence_belyiOpen_carrier
    [Infinite K] (s : V) :
    (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
      D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s =
      {x : C | (D.map s).hom.base x ∉ markedSchemePointSet K} := by
  exact
    FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence_belyiOpen_carrier
      K V D.toFiniteMarkedBelyiExistence s

theorem toFiniteMarkedBelyiExistence_belyiOpen_eq_schemeBelyi
    [Infinite K] (s : V) :
    (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
      D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s =
      ((D.map s).toBelyiMap.belyiOpen : Set C) := by
  exact
    FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence_belyiOpen_eq_schemeBelyi
      K V D.toFiniteMarkedBelyiExistence s

/-- Direct finite disjoint-set conclusion for scheme-level section-controlled
finite marked Belyi data. -/
theorem exists_for_finite_disjoint
    [Infinite K] {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V, (∀ x ∈ S, (D.map s).hom.base x ∈ markedSchemePointSet K) ∧
      ∀ x ∈ T, (D.map s).hom.base x ∉ markedSchemePointSet K := by
  rcases D.evalPackage.exists_section_for_disjoint_finite_sets hS hT hdis with
    ⟨s, hsS, hsT⟩
  exact
    ⟨s,
      D.sends_vanishing_to_marked hsS,
      D.nonzero_avoids_marked hsT⟩

/-- Direct scheme-Belyi-open form of the finite disjoint-set conclusion for
section-controlled finite marked Belyi data. -/
theorem exists_map_belyiOpen_controls
    [Infinite K] {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V, T ⊆ ((D.map s).toBelyiMap.belyiOpen : Set C) ∧
      ((D.map s).toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  rcases
      FiniteMarkedBelyiExistence.exists_map_belyiOpen_controls
        (K := K) (Φ := V) D.toFiniteMarkedBelyiExistence hS hT hdis with
    ⟨s, hTopen, hopenS⟩
  exact
    ⟨s,
      (by simpa [toFiniteMarkedBelyiExistence] using hTopen),
      (by simpa [toFiniteMarkedBelyiExistence] using hopenS)⟩

/-- Direct same-map finite disjoint-set conclusion for section-controlled
finite marked Belyi data: the selected finite Belyi map satisfies the marked
controls and its Belyi open contains `T` and avoids `S`. -/
theorem exists_map_controls_and_belyiOpen_controls
    [Infinite K] {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V,
      ((∀ x ∈ S, (D.map s).hom.base x ∈ markedSchemePointSet K) ∧
        ∀ x ∈ T, (D.map s).hom.base x ∉ markedSchemePointSet K) ∧
        T ⊆ ((D.map s).toBelyiMap.belyiOpen : Set C) ∧
          ((D.map s).toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  rcases
      FiniteMarkedBelyiExistence.exists_map_controls_and_belyiOpen_controls
        (K := K) (Φ := V) D.toFiniteMarkedBelyiExistence hS hT hdis with
    ⟨s, hcontrols, hTopen, hopenS⟩
  exact
    ⟨s,
      (by
        rcases hcontrols with ⟨hSmark, hTavoid⟩
        exact
          ⟨(by simpa [toFiniteMarkedBelyiExistence] using hSmark),
            (by simpa [toFiniteMarkedBelyiExistence] using hTavoid)⟩),
      (by simpa [toFiniteMarkedBelyiExistence] using hTopen),
      (by simpa [toFiniteMarkedBelyiExistence] using hopenS)⟩

/-- Direct same-map finite disjoint-set conclusion for section-controlled
finite marked Belyi data, with explicit openness of the selected source Belyi
open. -/
theorem exists_map_controls_and_isOpen_belyiOpen_controls
    [Infinite K] {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V,
      ((∀ x ∈ S, (D.map s).hom.base x ∈ markedSchemePointSet K) ∧
        ∀ x ∈ T, (D.map s).hom.base x ∉ markedSchemePointSet K) ∧
        IsOpen ((D.map s).toBelyiMap.belyiOpen : Set C) ∧
          T ⊆ ((D.map s).toBelyiMap.belyiOpen : Set C) ∧
            ((D.map s).toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  rcases
      FiniteMarkedBelyiExistence.exists_map_controls_and_isOpen_belyiOpen_controls
        (K := K) (Φ := V) D.toFiniteMarkedBelyiExistence hS hT hdis with
    ⟨s, hcontrols, hopen, hTopen, hopenS⟩
  exact
    ⟨s,
      (by
        rcases hcontrols with ⟨hSmark, hTavoid⟩
        exact
          ⟨(by simpa [toFiniteMarkedBelyiExistence] using hSmark),
            (by simpa [toFiniteMarkedBelyiExistence] using hTavoid)⟩),
      (by simpa [toFiniteMarkedBelyiExistence] using hopen),
      (by simpa [toFiniteMarkedBelyiExistence] using hTopen),
      (by simpa [toFiniteMarkedBelyiExistence] using hopenS)⟩

/-- Actual finite-map one-point Belyi-open consequence for
section-controlled finite marked Belyi data. -/
theorem exists_map_belyiOpen_inside_complement
    [Infinite K] {A : Set C} (hA : A.Finite) {x : C} (hxA : x ∉ A) :
    ∃ s : V,
      IsOpen ((D.map s).toBelyiMap.belyiOpen : Set C) ∧
        x ∈ ((D.map s).toBelyiMap.belyiOpen : Set C) ∧
          ((D.map s).toBelyiMap.belyiOpen : Set C) ⊆ Aᶜ := by
  rcases
      FiniteMarkedBelyiExistence.exists_map_belyiOpen_inside_complement
        K V D.toFiniteMarkedBelyiExistence hA hxA with
    ⟨s, hopen, hxopen, hsub⟩
  exact
    ⟨s,
      (by simpa [toFiniteMarkedBelyiExistence] using hopen),
      (by simpa [toFiniteMarkedBelyiExistence] using hxopen),
      (by simpa [toFiniteMarkedBelyiExistence] using hsub)⟩

/-- Actual finite-map finite-set Belyi-open consequence for
section-controlled finite marked Belyi data. -/
theorem exists_map_belyiOpen_containing_finite_inside_complement
    [Infinite K] {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V,
      IsOpen ((D.map s).toBelyiMap.belyiOpen : Set C) ∧
        T ⊆ ((D.map s).toBelyiMap.belyiOpen : Set C) ∧
          ((D.map s).toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  rcases
      FiniteMarkedBelyiExistence.exists_map_belyiOpen_containing_finite_inside_complement
        K V D.toFiniteMarkedBelyiExistence hS hT hdis with
    ⟨s, hopen, hTopen, hsub⟩
  exact
    ⟨s,
      (by simpa [toFiniteMarkedBelyiExistence] using hopen),
      (by simpa [toFiniteMarkedBelyiExistence] using hTopen),
      (by simpa [toFiniteMarkedBelyiExistence] using hsub)⟩

/-- Actual finite-map one-point finite-complement-open consequence for
section-controlled finite marked Belyi data. -/
theorem exists_map_belyiOpen_inside_open_of_finite_complement
    [Infinite K]
    {U : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite) {x : C} (hxU : x ∈ U) :
    ∃ s : V,
      IsOpen ((D.map s).toBelyiMap.belyiOpen : Set C) ∧
        x ∈ ((D.map s).toBelyiMap.belyiOpen : Set C) ∧
          ((D.map s).toBelyiMap.belyiOpen : Set C) ⊆ U := by
  rcases
      FiniteMarkedBelyiExistence.exists_map_belyiOpen_inside_open_of_finite_complement
        K V D.toFiniteMarkedBelyiExistence hU hUcompl hxU with
    ⟨s, hopen, hxopen, hsub⟩
  exact
    ⟨s,
      (by simpa [toFiniteMarkedBelyiExistence] using hopen),
      (by simpa [toFiniteMarkedBelyiExistence] using hxopen),
      (by simpa [toFiniteMarkedBelyiExistence] using hsub)⟩

/-- Actual finite-map finite-set finite-complement-open consequence for
section-controlled finite marked Belyi data. -/
theorem exists_map_belyiOpen_containing_finite_inside_open_of_finite_complement
    [Infinite K]
    {U T : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ s : V,
      IsOpen ((D.map s).toBelyiMap.belyiOpen : Set C) ∧
        T ⊆ ((D.map s).toBelyiMap.belyiOpen : Set C) ∧
          ((D.map s).toBelyiMap.belyiOpen : Set C) ⊆ U := by
  rcases
      FiniteMarkedBelyiExistence.exists_map_belyiOpen_containing_finite_inside_open_of_finite_complement
        K V D.toFiniteMarkedBelyiExistence hU hUcompl hT hTsub with
    ⟨s, hopen, hTopen, hsub⟩
  exact
    ⟨s,
      (by simpa [toFiniteMarkedBelyiExistence] using hopen),
      (by simpa [toFiniteMarkedBelyiExistence] using hTopen),
      (by simpa [toFiniteMarkedBelyiExistence] using hsub)⟩

/-- Actual finite-map finite-complement-open consequence retaining marked
controls for section-controlled finite marked Belyi data. -/
theorem exists_map_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_finite_complement
    [Infinite K]
    {U T : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ s : V,
      ((∀ x ∈ Uᶜ, (D.map s).hom.base x ∈ markedSchemePointSet K) ∧
        ∀ x ∈ T, (D.map s).hom.base x ∉ markedSchemePointSet K) ∧
        IsOpen ((D.map s).toBelyiMap.belyiOpen : Set C) ∧
          T ⊆ ((D.map s).toBelyiMap.belyiOpen : Set C) ∧
            ((D.map s).toBelyiMap.belyiOpen : Set C) ⊆ U := by
  rcases
      FiniteMarkedBelyiExistence.exists_map_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_finite_complement
        K V D.toFiniteMarkedBelyiExistence hU hUcompl hT hTsub with
    ⟨s, hcontrols, hopen, hTopen, hsub⟩
  exact
    ⟨s,
      (by simpa [toFiniteMarkedBelyiExistence] using hcontrols),
      (by simpa [toFiniteMarkedBelyiExistence] using hopen),
      (by simpa [toFiniteMarkedBelyiExistence] using hTopen),
      (by simpa [toFiniteMarkedBelyiExistence] using hsub)⟩

/-- Actual finite-map nonempty-open finite-complement consequence retaining
marked controls for section-controlled finite marked Belyi data. -/
theorem exists_map_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
    [Infinite K] [NonemptyOpenFiniteComplement C]
    {U T : Set C} (hU : IsOpen U) (hUne : U.Nonempty)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ s : V,
      ((∀ x ∈ Uᶜ, (D.map s).hom.base x ∈ markedSchemePointSet K) ∧
        ∀ x ∈ T, (D.map s).hom.base x ∉ markedSchemePointSet K) ∧
        IsOpen ((D.map s).toBelyiMap.belyiOpen : Set C) ∧
          T ⊆ ((D.map s).toBelyiMap.belyiOpen : Set C) ∧
            ((D.map s).toBelyiMap.belyiOpen : Set C) ⊆ U := by
  rcases
      FiniteMarkedBelyiExistence.exists_map_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement
        K V D.toFiniteMarkedBelyiExistence hU hUne hT hTsub with
    ⟨s, hcontrols, hopen, hTopen, hsub⟩
  exact
    ⟨s,
      (by simpa [toFiniteMarkedBelyiExistence] using hcontrols),
      (by simpa [toFiniteMarkedBelyiExistence] using hopen),
      (by simpa [toFiniteMarkedBelyiExistence] using hTopen),
      (by simpa [toFiniteMarkedBelyiExistence] using hsub)⟩

/-- Direct finite disjoint-set conclusion after restricting the source of
scheme-level section-controlled finite marked Belyi data to a subtype. -/
theorem exists_for_finite_disjoint_subtype_sets
    [Infinite K] (U : Set C) {S T : Set U} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V, (∀ x ∈ S, (D.map s).hom.base x.1 ∈ markedSchemePointSet K) ∧
      ∀ x ∈ T, (D.map s).hom.base x.1 ∉ markedSchemePointSet K := by
  let S' : Set C := (Subtype.val : U → C) '' S
  let T' : Set C := (Subtype.val : U → C) '' T
  have hS' : S'.Finite := hS.image (Subtype.val : U → C)
  have hT' : T'.Finite := hT.image (Subtype.val : U → C)
  have hdis' : Disjoint S' T' := by
    rw [Set.disjoint_left]
    intro y hyS hyT
    rcases hyS with ⟨s, hsS, rfl⟩
    rcases hyT with ⟨t, htT, ht⟩
    have hst : s = t := Subtype.ext ht.symm
    have hs_not_mem_T : s ∉ T := (Set.disjoint_left.mp hdis) hsS
    exact hs_not_mem_T (by simpa [hst] using htT)
  rcases D.exists_for_finite_disjoint hS' hT' hdis' with
    ⟨s, hsS, hsT⟩
  exact
    ⟨s,
      (by
        intro x hx
        exact hsS x.1 ⟨x, hx, rfl⟩),
      (by
        intro x hx
        exact hsT x.1 ⟨x, hx, rfl⟩)⟩

theorem toFiniteMarkedBelyiExistence_toMarkedCoverData_branch
    [Infinite K] :
    (FiniteMarkedBelyiExistence.toMarkedCoverData K V
      D.toFiniteMarkedBelyiExistence).branch = markedSchemePointSet K := by
  exact FiniteMarkedBelyiExistence.toMarkedCoverData_branch K V
    D.toFiniteMarkedBelyiExistence

/-- Direct Corollary 1.2-style one-point Belyi-open consequence for
section-controlled finite marked Belyi data. -/
theorem exists_belyiOpen_inside_complement
    [Infinite K] [T1Space (P1 K)]
    {A : Set C} (hA : A.Finite) {x : C} (hxA : x ∉ A) :
    ∃ s : V,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        x ∈ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ Aᶜ := by
  exact FiniteMarkedBelyiExistence.exists_belyiOpen_inside_complement
    K V D.toFiniteMarkedBelyiExistence hA hxA

/-- Direct finite-set Belyi-open consequence for section-controlled finite
marked Belyi data. -/
theorem exists_belyiOpen_containing_finite_inside_complement
    [Infinite K] [T1Space (P1 K)]
    {S T : Set C} (hS : S.Finite) (hT : T.Finite) (hdis : Disjoint S T) :
    ∃ s : V,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        T ⊆ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ Sᶜ := by
  exact FiniteMarkedBelyiExistence.exists_belyiOpen_containing_finite_inside_complement
    K V D.toFiniteMarkedBelyiExistence hS hT hdis

/-- Direct open-with-finite-complement one-point Belyi-open consequence for
section-controlled finite marked Belyi data. -/
theorem exists_belyiOpen_inside_open_of_finite_complement
    [Infinite K] [T1Space (P1 K)]
    {U : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite) {x : C} (hxU : x ∈ U) :
    ∃ s : V,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        x ∈ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ U := by
  exact FiniteMarkedBelyiExistence.exists_belyiOpen_inside_open_of_finite_complement
    K V D.toFiniteMarkedBelyiExistence hU hUcompl hxU

/-- Direct curve-style finite-complement-open one-point Belyi-open consequence
for section-controlled finite marked Belyi data. -/
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
  exact FiniteMarkedBelyiExistence.exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
    K V D.toFiniteMarkedBelyiExistence hU hxU

/-- Direct open-with-finite-complement finite-set Belyi-open consequence for
section-controlled finite marked Belyi data. -/
theorem exists_belyiOpen_containing_finite_inside_open_of_finite_complement
    [Infinite K] [T1Space (P1 K)]
    {U T : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ U) :
    ∃ s : V,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        T ⊆ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ U := by
  exact
    FiniteMarkedBelyiExistence.exists_belyiOpen_containing_finite_inside_open_of_finite_complement
      K V D.toFiniteMarkedBelyiExistence hU hUcompl hT hTsub

/-- Direct curve-style finite-complement-open finite-set Belyi-open consequence
for section-controlled finite marked Belyi data. -/
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

/-- Direct pointwise tuple-cover consequence for section-controlled finite
marked Belyi data. -/
theorem pointwise_cover_complement
    [Infinite K] (κ : Type z) [Finite κ] {S : Set C} (hS : S.Finite)
    (x : κ → {x : C // x ∉ S}) :
    ∃ s : V,
      (FiniteMarkedBelyiExistence.toMarkedCoverData K V
        D.toFiniteMarkedBelyiExistence).sendsSetToBranch S s ∧
        ∀ i, (D.map s).hom.base (x i).1 ∉ markedSchemePointSet K := by
  rcases FiniteMarkedBelyiExistence.pointwise_cover_complement
      K V D.toFiniteMarkedBelyiExistence κ hS x with
    ⟨s, hsS, hsx⟩
  exact ⟨s, hsS, by simpa [toFiniteMarkedBelyiExistence] using hsx⟩

/-- Direct Corollary 3.1-style finite-subcover consequence for
section-controlled finite marked Belyi data. -/
theorem finite_subcover_on_complement
    [Infinite K] (κ : Type z) [Finite κ] [T1Space (P1 K)]
    {S : Set C} (hS : S.Finite) [CompactSpace (κ → {x : C // x ∉ S})] :
    ∃ t : Finset {s : V //
        (FiniteMarkedBelyiExistence.toMarkedCoverData K V
          D.toFiniteMarkedBelyiExistence).sendsSetToBranch S s},
      (⋃ s ∈ t,
          ((FiniteMarkedBelyiExistence.toMarkedCoverData K V
            D.toFiniteMarkedBelyiExistence).complementCoverData S).tupleAvoidSet
              (κ := κ) s) =
        (Set.univ : Set (κ → {x : C // x ∉ S})) := by
  exact FiniteMarkedBelyiExistence.finite_subcover_on_complement
    K V D.toFiniteMarkedBelyiExistence κ hS

/-- Membership form of the direct Corollary 3.1-style finite-subcover
consequence for section-controlled finite marked Belyi data. -/
theorem finite_subcover_on_complement_forall
    [Infinite K] (κ : Type z) [Finite κ] [T1Space (P1 K)]
    {S : Set C} (hS : S.Finite) [CompactSpace (κ → {x : C // x ∉ S})] :
    ∃ t : Finset {s : V //
        (FiniteMarkedBelyiExistence.toMarkedCoverData K V
          D.toFiniteMarkedBelyiExistence).sendsSetToBranch S s},
      ∀ x : κ → {x : C // x ∉ S},
        ∃ s ∈ t,
          x ∈ ((FiniteMarkedBelyiExistence.toMarkedCoverData K V
            D.toFiniteMarkedBelyiExistence).complementCoverData S).tupleAvoidSet
              (κ := κ) s := by
  exact FiniteMarkedBelyiExistence.finite_subcover_on_complement_forall
    K V D.toFiniteMarkedBelyiExistence κ hS

/-- Concrete coordinate-avoidance form of the direct Corollary 3.1-style
finite-subcover consequence for section-controlled finite marked Belyi data. -/
theorem finite_subcover_on_complement_forall_avoidance
    [Infinite K] (κ : Type z) [Finite κ] [T1Space (P1 K)]
    {S : Set C} (hS : S.Finite) [CompactSpace (κ → {x : C // x ∉ S})] :
    ∃ t : Finset {s : V //
        (FiniteMarkedBelyiExistence.toMarkedCoverData K V
          D.toFiniteMarkedBelyiExistence).sendsSetToBranch S s},
      ∀ x : κ → {x : C // x ∉ S},
        ∃ s ∈ t, ∀ i, (D.map s.1).hom.base (x i).1 ∉ markedSchemePointSet K := by
  rcases FiniteMarkedBelyiExistence.finite_subcover_on_complement_forall_avoidance
      K V D.toFiniteMarkedBelyiExistence κ hS with
    ⟨t, ht⟩
  refine ⟨t, ?_⟩
  intro x
  rcases ht x with ⟨s, hst, hsx⟩
  exact ⟨s, hst, by simpa [toFiniteMarkedBelyiExistence] using hsx⟩

/-- Direct compact-exhaustion cover bridge for section-controlled finite marked
Belyi data. -/
theorem finite_compact_cover_by_belyiOpen_exhaustions
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    (Kex : ∀ s : V,
      CompactExhaustion ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s)) :
    ∃ t : Finset (V × ℕ),
      (∀ p ∈ t,
        IsCompact ((Subtype.val :
          (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
            (Kex p.1 p.2))) ∧
        (∀ p ∈ t,
          ((Subtype.val :
            (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
              D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
              (Kex p.1 p.2)) ⊆
                (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                  D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1) ∧
          (Set.univ : Set C) ⊆
            ⋃ p ∈ t,
              (Subtype.val :
                (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                  D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
                (Kex p.1 p.2) := by
  exact
    FiniteMarkedBelyiExistence.finite_compact_cover_by_belyiOpen_exhaustions
      K V D.toFiniteMarkedBelyiExistence Kex

/-- Equality form of the direct compact-exhaustion cover bridge for
section-controlled finite marked Belyi data. -/
theorem finite_compact_cover_by_belyiOpen_exhaustions_eq_univ
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    (Kex : ∀ s : V,
      CompactExhaustion ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s)) :
    ∃ t : Finset (V × ℕ),
      (∀ p ∈ t,
        IsCompact ((Subtype.val :
          (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
            (Kex p.1 p.2))) ∧
        (∀ p ∈ t,
          ((Subtype.val :
            (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
              D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
              (Kex p.1 p.2)) ⊆
                (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                  D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1) ∧
          (⋃ p ∈ t,
            (Subtype.val :
              (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
              (Kex p.1 p.2)) = (Set.univ : Set C) := by
  exact
    FiniteMarkedBelyiExistence.finite_compact_cover_by_belyiOpen_exhaustions_eq_univ
      K V D.toFiniteMarkedBelyiExistence Kex

/-- Direct compact-cover bridge for section-controlled finite marked Belyi data
with compact exhaustions supplied by local compactness and second countability. -/
theorem finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    [LocallyCompactSpace C] [SecondCountableTopology C] :
    ∃ Kex : ∀ s : V,
      CompactExhaustion ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s),
      ∃ t : Finset (V × ℕ),
        (∀ p ∈ t,
          IsCompact ((Subtype.val :
            (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
              D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
              (Kex p.1 p.2))) ∧
          (∀ p ∈ t,
            ((Subtype.val :
              (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
                (Kex p.1 p.2)) ⊆
                  (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                    D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1) ∧
            (Set.univ : Set C) ⊆
              ⋃ p ∈ t,
                (Subtype.val :
                  (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                    D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
                  (Kex p.1 p.2) := by
  exact
    FiniteMarkedBelyiExistence.finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact
      K V D.toFiniteMarkedBelyiExistence

/-- Equality form of the direct compact-cover bridge for section-controlled
finite marked Belyi data with compact exhaustions supplied by local compactness
and second countability. -/
theorem finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact_eq_univ
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    [LocallyCompactSpace C] [SecondCountableTopology C] :
    ∃ Kex : ∀ s : V,
      CompactExhaustion ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s),
      ∃ t : Finset (V × ℕ),
        (∀ p ∈ t,
          IsCompact ((Subtype.val :
            (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
              D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
              (Kex p.1 p.2))) ∧
          (∀ p ∈ t,
            ((Subtype.val :
              (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
                (Kex p.1 p.2)) ⊆
                  (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                    D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1) ∧
            (⋃ p ∈ t,
              (Subtype.val :
                (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                  D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 → C) ''
                (Kex p.1 p.2)) = (Set.univ : Set C) := by
  exact
    FiniteMarkedBelyiExistence.finite_compact_cover_by_belyiOpen_exhaustions_of_locallyCompact_eq_univ
      K V D.toFiniteMarkedBelyiExistence

/-- Direct compact-coordinate Corollary 3.2 bridge for section-controlled
finite marked Belyi data. -/
theorem finite_compact_coordinate_sets_of_belyiOpen_exhaustions
    [Infinite K] [T1Space (P1 K)] [NonemptyOpenFiniteComplement C] [CompactSpace C]
    [LocallyCompactSpace C] [SecondCountableTopology C]
    {κ : Type*} {Z : κ → Type*} [∀ j, TopologicalSpace (Z j)]
    (G : V → C → ((j : κ) → Z j))
    (hG : ∀ s, Continuous (G s))
    (A : (j : κ) → Set (Z j))
    (hGA : ∀ s x,
      x ∈ (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s →
        ∀ j, G s x j ∈ A j) :
    ∃ Kex : ∀ s : V,
      CompactExhaustion ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s),
      ∃ t : Finset (V × ℕ),
        ∃ H : (j : κ) → Set (Z j),
          (∀ j, IsCompact (H j)) ∧
            (∀ j, H j ⊆ A j) ∧
              (Set.univ : Set C) ⊆
                ⋃ p ∈ t,
                  (Subtype.val :
                    (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                      D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 →
                      C) ''
                    (Kex p.1 p.2) ∧
                ∀ p ∈ t, ∀ x,
                  x ∈ (Subtype.val :
                    (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
                      D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen p.1 →
                      C) ''
                      (Kex p.1 p.2) →
                    ∀ j, G p.1 x j ∈ H j := by
  exact
    FiniteMarkedBelyiExistence.finite_compact_coordinate_sets_of_belyiOpen_exhaustions
      K V D.toFiniteMarkedBelyiExistence G hG A hGA

end SectionControlledFiniteMarkedBelyiData

end SchemeCurveBelyiConstruction
end SourceStack
end HilbertTest
