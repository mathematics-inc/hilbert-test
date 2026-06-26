import HilbertTest.SourceStack.FiniteSet
import HilbertTest.SourceStack.LinearAlgebra
import HilbertTest.SourceStack.CurveRiemannRoch
import HilbertTest.SourceStack.CurveBelyiConstruction
import HilbertTest.SourceStack.SchemeCurveBelyiConstruction
import HilbertTest.SourceStack.BelyiReduction
import HilbertTest.SourceStack.ProjectiveSectionMaps
import HilbertTest.SourceStack.CurveDivisorSections
import HilbertTest.SourceStack.CurveCohomologySections
import HilbertTest.SourceStack.ComplexSeparation
import HilbertTest.SourceStack.AffineSpace
import HilbertTest.SourceStack.ProjectiveLine
import HilbertTest.SourceStack.ProjectiveSpectrum
import HilbertTest.SourceStack.SchemeProjectiveLine
import HilbertTest.SourceStack.MarkedProjectiveLine
import HilbertTest.SourceStack.SchemeMarkedBelyi
import HilbertTest.SourceStack.RationalMaps
import HilbertTest.SourceStack.FunctionFields
import HilbertTest.SourceStack.ResidueFields
import HilbertTest.SourceStack.StalkMaps
import HilbertTest.SourceStack.PullbackCarrier
import HilbertTest.SourceStack.SurjectiveOnStalks
import HilbertTest.SourceStack.FieldTheory
import HilbertTest.SourceStack.PolynomialMaps
import HilbertTest.SourceStack.PolynomialSeparation
import HilbertTest.SourceStack.P1PolynomialSeparation
import HilbertTest.SourceStack.PolynomialTargetAvoidance
import HilbertTest.SourceStack.PolynomialValueSurjectivity
import HilbertTest.SourceStack.P1SchemePointBridge
import HilbertTest.SourceStack.SchemeAffineLinePoints
import HilbertTest.SourceStack.SchemeProjectiveLineTransform
import HilbertTest.SourceStack.PolynomialSchemeSeparation
import HilbertTest.SourceStack.ConcretePolynomialSchemeSeparation
import HilbertTest.SourceStack.UnramifiedEtale
import HilbertTest.SourceStack.Ramification
import HilbertTest.SourceStack.DedekindDvr
import HilbertTest.SourceStack.FractionalIdeals
import HilbertTest.SourceStack.ArithmeticFunctionFields
import HilbertTest.SourceStack.Cohomology
import HilbertTest.SourceStack.SmoothKaehler
import HilbertTest.SourceStack.Topology
import HilbertTest.SourceStack.BelyiCovers
import HilbertTest.SourceStack.SchemeBelyi
import HilbertTest.SourceStack.LocalFields
import HilbertTest.SourceStack.Schemes

/-!
Hilbert-facing proof targets for the first recursive source-stack layer.

Each theorem in this file is intentionally phrased as a small benchmark target:
the source material has already been normalized into a stable theorem in
`HilbertTest.SourceStack.*`, and this file records the corresponding checked
formal step that Hilbert can solve and verify.
-/

namespace HilbertTest
namespace HilbertSteps

open Set
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Abelian
open Topology
open Opposite IsLocalRing
open AlgebraicGeometry
open HomogeneousLocalization
open scoped TensorProduct
open scoped Pointwise
open scoped nonZeroDivisors
open scoped IntermediateField Polynomial
open scoped AlgebraicGeometry

section FiniteSet

variable {α β : Type*}

theorem hilbert_card_image_lt_of_exists_distinct_same_image
    [DecidableEq β]
    (s : Finset α) (f : α → β) {a b : α}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) (hfab : f a = f b) :
    (s.image f).card < s.card := by
  exact SourceStack.card_image_lt_of_exists_distinct_same_image s f ha hb hab hfab

theorem hilbert_exists_distinct_same_image_of_maps_to_smaller
    (s : Finset α) (t : Finset β) (f : α → β)
    (hcard : t.card < s.card)
    (hmap : ∀ a ∈ s, f a ∈ t) :
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ f a = f b := by
  exact SourceStack.exists_distinct_same_image_of_maps_to_smaller s t f hcard hmap

theorem hilbert_card_image_lt_of_subset_with_smaller_subimage
    [DecidableEq β]
    (s u : Finset α) (f : α → β)
    (hu : u ⊆ s)
    (hcard : (u.image f).card < u.card) :
    (s.image f).card < s.card := by
  exact SourceStack.card_image_lt_of_subset_with_smaller_subimage s u f hu hcard

theorem hilbert_card_image_lt_of_subset_card_four_image_le_three
    [DecidableEq β]
    (s u : Finset α) (f : α → β)
    (hu : u ⊆ s)
    (hucard : u.card = 4)
    (himage : (u.image f).card ≤ 3) :
    (s.image f).card < s.card := by
  exact SourceStack.card_image_lt_of_subset_card_four_image_le_three
    s u f hu hucard himage

theorem hilbert_exists_finset_superset_card_ge_disjoint
    [Infinite α] [DecidableEq α]
    (S T : Finset α) (hdis : ∀ x, x ∈ S → x ∉ T) (N : ℕ) :
    ∃ T' : Finset α,
      T ⊆ T' ∧ (∀ x, x ∈ S → x ∉ T') ∧ N ≤ T'.card := by
  exact SourceStack.exists_finset_superset_card_ge_disjoint S T hdis N

end FiniteSet

section LinearAlgebra

variable {K V : Type*} [DivisionRing K] [Infinite K] [AddCommGroup V] [Module K V]

theorem hilbert_scherr_zieve_no_finite_cover_by_proper_subspaces
    (s : Finset (Subspace K V))
    (hproper : ∀ W ∈ s, W ≠ ⊤) :
    (⋃ W ∈ s, (W : Set V)) ≠ Set.univ := by
  exact SourceStack.scherr_zieve_no_finite_cover_by_proper_subspaces s hproper

theorem hilbert_scherr_zieve_exists_vector_avoiding_finite_proper_subspaces
    (s : Finset (Subspace K V))
    (hproper : ∀ W ∈ s, W ≠ ⊤) :
    ∃ v : V, ∀ W ∈ s, v ∉ W := by
  exact SourceStack.scherr_zieve_exists_vector_avoiding_finite_proper_subspaces s hproper

omit [Infinite K] in
theorem hilbert_subspace_ne_top_of_finrank_lt
    [FiniteDimensional K V] (W : Subspace K V)
    (h : Module.finrank K W < Module.finrank K V) :
    W ≠ ⊤ := by
  exact SourceStack.subspace_ne_top_of_finrank_lt W h

theorem hilbert_exists_vector_avoiding_subspaces_of_finrank_lt
    [FiniteDimensional K V] (s : Finset (Subspace K V))
    (hfinrank : ∀ W ∈ s, Module.finrank K W < Module.finrank K V) :
    ∃ v : V, ∀ W ∈ s, v ∉ W := by
  exact SourceStack.exists_vector_avoiding_subspaces_of_finrank_lt s hfinrank

omit [Infinite K] in
theorem hilbert_exists_vector_avoiding_subspaces_of_sum_card_lt
    [Fintype V] [DecidableEq V] [∀ W : Subspace K V, Fintype W]
    (s : Finset (Subspace K V))
    (hcard : (∑ W in s, Fintype.card W) < Fintype.card V) :
    ∃ v : V, ∀ W ∈ s, v ∉ W := by
  exact SourceStack.exists_vector_avoiding_subspaces_of_sum_card_lt s hcard

omit [Infinite K] in
theorem hilbert_linearMap_ker_ne_top_of_ne_zero
    {W : Type*} [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) (hf : f ≠ 0) :
    LinearMap.ker f ≠ ⊤ := by
  exact SourceStack.linearMap_ker_ne_top_of_ne_zero f hf

theorem hilbert_exists_vector_avoiding_kernels_of_nonzero_linear_maps
    {ι W : Type*} [AddCommGroup W] [Module K W]
    (s : Finset ι) (f : ι → V →ₗ[K] W)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    ∃ v : V, ∀ i ∈ s, f i v ≠ 0 := by
  exact SourceStack.exists_vector_avoiding_kernels_of_nonzero_linear_maps s f hf

theorem hilbert_exists_vector_nonzero_on_finite_linear_forms
    (s : Finset (V →ₗ[K] K))
    (hf : ∀ f ∈ s, f ≠ 0) :
    ∃ v : V, ∀ f ∈ s, f v ≠ 0 := by
  exact SourceStack.exists_vector_nonzero_on_finite_linear_forms s hf

omit [Infinite K] in
theorem hilbert_mem_commonKernel_iff
    {σ : Type*} (s : Finset σ) (f : σ → V →ₗ[K] K) (v : V) :
    v ∈ SourceStack.commonKernel (K := K) (V := V) s f ↔
      ∀ i ∈ s, f i v = 0 := by
  exact SourceStack.mem_commonKernel_iff s f v

theorem hilbert_exists_vector_in_subspace_nonzero_on_finite_linear_forms
    {ι : Type*} (W : Subspace K V) (s : Finset ι) (f : ι → V →ₗ[K] K)
    (hf : ∀ i ∈ s, (f i).comp W.subtype ≠ 0) :
    ∃ v : V, v ∈ W ∧ ∀ i ∈ s, f i v ≠ 0 := by
  exact SourceStack.exists_vector_in_subspace_nonzero_on_finite_linear_forms W s f hf

theorem hilbert_exists_vector_vanishing_and_nonzero_on_finite_linear_forms
    {σ τ : Type*} (S : Finset σ) (T : Finset τ)
    (vanish : σ → V →ₗ[K] K) (avoid : τ → V →ₗ[K] K)
    (havoid : ∀ j ∈ T,
      (avoid j).comp (SourceStack.commonKernel (K := K) (V := V) S vanish).subtype ≠ 0) :
    ∃ v : V, (∀ i ∈ S, vanish i v = 0) ∧ ∀ j ∈ T, avoid j v ≠ 0 := by
  exact SourceStack.exists_vector_vanishing_and_nonzero_on_finite_linear_forms
    S T vanish avoid havoid

end LinearAlgebra

namespace CurveRiemannRoch

open SourceStack.CurveRiemannRoch

variable {K X V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (D : RRSectionEvaluationData K X V)

theorem hilbert_rr_vanishesOn_iff_mem_commonKernel
    (S : Finset X) (s : V) :
    D.vanishesOn S s ↔
      s ∈ SourceStack.commonKernel (K := K) (V := V) S D.eval := by
  exact SourceStack.CurveRiemannRoch.RRSectionEvaluationData.vanishesOn_iff_mem_commonKernel
    D S s

theorem hilbert_rr_nonzeroOn_iff
    (T : Finset X) (s : V) :
    D.nonzeroOn T s ↔ ∀ x ∈ T, D.eval x s ≠ 0 := by
  exact SourceStack.CurveRiemannRoch.RRSectionEvaluationData.nonzeroOn_iff
    D T s

theorem hilbert_rr_vanishesOn_toFinset_iff
    {S : Set X} (hS : S.Finite) (s : V) :
    D.vanishesOn hS.toFinset s ↔ D.vanishesOnSet S s := by
  exact SourceStack.CurveRiemannRoch.RRSectionEvaluationData.vanishesOn_toFinset_iff
    D hS s

theorem hilbert_rr_nonzeroOn_toFinset_iff
    {T : Set X} (hT : T.Finite) (s : V) :
    D.nonzeroOn hT.toFinset s ↔ D.nonzeroOnSet T s := by
  exact SourceStack.CurveRiemannRoch.RRSectionEvaluationData.nonzeroOn_toFinset_iff
    D hT s

theorem hilbert_rr_exists_section_nonzero_on_finite
    [Infinite K] (T : Finset X)
    (hT : ∀ x ∈ T, D.eval x ≠ 0) :
    ∃ s : V, D.nonzeroOn T s := by
  exact SourceStack.CurveRiemannRoch.RRSectionEvaluationData.exists_section_nonzero_on_finite
    D T hT

theorem hilbert_rr_exists_section_vanishing_on_and_nonzero_on
    [Infinite K] (S T : Finset X)
    (havoid : ∀ x ∈ T,
      (D.eval x).comp (SourceStack.commonKernel (K := K) (V := V) S D.eval).subtype ≠ 0) :
    ∃ s : V, D.vanishesOn S s ∧ D.nonzeroOn T s := by
  exact SourceStack.CurveRiemannRoch.RRSectionEvaluationData.exists_section_vanishing_on_and_nonzero_on
    D S T havoid

variable (P : RiemannRochFiniteEvaluationPackage K X V)

theorem hilbert_rr_package_toEvaluationData_eval
    (x : X) :
    (P.toEvaluationData).eval x = P.eval x := by
  exact SourceStack.CurveRiemannRoch.RiemannRochFiniteEvaluationPackage.toEvaluationData_eval
    P x

theorem hilbert_rr_package_exists_section_for_disjoint_finsets
    [Infinite K] {S T : Finset X} (hdis : Disjoint S T) :
    ∃ s : V, (P.toEvaluationData).vanishesOn S s ∧
      (P.toEvaluationData).nonzeroOn T s := by
  exact SourceStack.CurveRiemannRoch.RiemannRochFiniteEvaluationPackage.exists_section_for_disjoint_finsets
    P hdis

theorem hilbert_rr_package_exists_section_for_disjoint_finite_sets
    [Infinite K] {S T : Set X} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V, (P.toEvaluationData).vanishesOnSet S s ∧
      (P.toEvaluationData).nonzeroOnSet T s := by
  exact SourceStack.CurveRiemannRoch.RiemannRochFiniteEvaluationPackage.exists_section_for_disjoint_finite_sets
    P hS hT hdis

end CurveRiemannRoch

namespace CurveBelyiConstruction

open SourceStack.CurveBelyiConstruction

variable {K X P V : Type*} [Field K]
variable [TopologicalSpace X] [TopologicalSpace P]
variable [AddCommGroup V] [Module K V]
variable (D : SectionControlledBelyiData K X P V)

theorem hilbert_sectionControlled_toBelyiCoverData_branch :
    D.toBelyiCoverData.branch = D.branch := by
  exact SourceStack.CurveBelyiConstruction.SectionControlledBelyiData.toBelyiCoverData_branch D

theorem hilbert_sectionControlled_toBelyiCoverData_map_apply
    (s : V) (x : X) :
    D.toBelyiCoverData.map s x = D.map s x := by
  exact SourceStack.CurveBelyiConstruction.SectionControlledBelyiData.toBelyiCoverData_map_apply
    D s x

theorem hilbert_sectionControlled_sendsSetToBranch_of_vanishesOnSet
    {S : Set X} {s : V}
    (hs : D.evalPackage.toEvaluationData.vanishesOnSet S s) :
    D.toBelyiCoverData.sendsSetToBranch S s := by
  exact SourceStack.CurveBelyiConstruction.SectionControlledBelyiData.sendsSetToBranch_of_vanishesOnSet
    D hs

theorem hilbert_sectionControlled_avoidsBranch_of_nonzeroOnSet
    {T : Set X} {s : V}
    (hs : D.evalPackage.toEvaluationData.nonzeroOnSet T s) :
    ∀ x ∈ T, D.map s x ∉ D.branch := by
  exact SourceStack.CurveBelyiConstruction.SectionControlledBelyiData.avoidsBranch_of_nonzeroOnSet
    D hs

theorem hilbert_sectionControlled_toNoncriticalBelyiExistence_branch
    [Infinite K] :
    D.toNoncriticalBelyiExistence.branch = D.branch := by
  exact SourceStack.CurveBelyiConstruction.SectionControlledBelyiData.toNoncriticalBelyiExistence_branch
    D

theorem hilbert_sectionControlled_toNoncriticalBelyiExistence_toCoverData_branch
    [Infinite K] :
    D.toNoncriticalBelyiExistence.toBelyiCoverData.branch = D.branch := by
  exact SourceStack.CurveBelyiConstruction.SectionControlledBelyiData.toNoncriticalBelyiExistence_toCoverData_branch
    D

theorem hilbert_sectionControlled_exists_for_finite_disjoint
    [Infinite K] {S T : Set X} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V, D.toBelyiCoverData.sendsSetToBranch S s ∧
      ∀ x ∈ T, D.map s x ∉ D.branch := by
  exact SourceStack.CurveBelyiConstruction.SectionControlledBelyiData.exists_for_finite_disjoint
    D hS hT hdis

end CurveBelyiConstruction

namespace SchemeCurveBelyiConstruction

open SourceStack.SchemeCurveBelyiConstruction
open SourceStack.SchemeProjectiveLine
open SourceStack.SchemeMarkedBelyi

universe u w

variable {K : Type u} [Field K]
variable {C : Scheme.{u}}
variable {V : Type w} [AddCommGroup V] [Module K V]
variable (D : SectionControlledFiniteMarkedBelyiData K C V)

theorem hilbert_schemeSectionControlled_toSectionControlledBelyiData_branch :
    D.toSectionControlledBelyiData.branch = markedSchemePointSet K := by
  exact SourceStack.SchemeCurveBelyiConstruction.SectionControlledFiniteMarkedBelyiData.toSectionControlledBelyiData_branch
    D

theorem hilbert_schemeSectionControlled_toSectionControlledBelyiData_map_apply
    (s : V) (x : C) :
    D.toSectionControlledBelyiData.map s x = (D.map s).hom.base x := by
  exact SourceStack.SchemeCurveBelyiConstruction.SectionControlledFiniteMarkedBelyiData.toSectionControlledBelyiData_map_apply
    D s x

theorem hilbert_schemeSectionControlled_toFiniteMarkedBelyiExistence_hmarkedOpen
    [Infinite K] :
    D.toFiniteMarkedBelyiExistence.hmarkedOpen = D.hmarkedOpen := by
  exact SourceStack.SchemeCurveBelyiConstruction.SectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence_hmarkedOpen
    D

theorem hilbert_schemeSectionControlled_toFiniteMarkedBelyiExistence_map_apply
    [Infinite K] (s : V) :
    D.toFiniteMarkedBelyiExistence.map s = D.map s := by
  exact SourceStack.SchemeCurveBelyiConstruction.SectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence_map_apply
    D s

theorem hilbert_schemeSectionControlled_exists_for_finite_disjoint
    [Infinite K] {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V, (∀ x ∈ S, (D.map s).hom.base x ∈ markedSchemePointSet K) ∧
      ∀ x ∈ T, (D.map s).hom.base x ∉ markedSchemePointSet K := by
  exact SourceStack.SchemeCurveBelyiConstruction.SectionControlledFiniteMarkedBelyiData.exists_for_finite_disjoint
    D hS hT hdis

theorem hilbert_schemeSectionControlled_toFiniteMarkedBelyiExistence_toMarkedCoverData_branch
    [Infinite K] :
    (FiniteMarkedBelyiExistence.toMarkedCoverData K V
      D.toFiniteMarkedBelyiExistence).branch = markedSchemePointSet K := by
  exact SourceStack.SchemeCurveBelyiConstruction.SectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence_toMarkedCoverData_branch
    D

theorem hilbert_schemeSectionControlled_exists_belyiOpen_inside_complement
    [Infinite K] [T1Space (P1 K)]
    {A : Set C} (hA : A.Finite) {x : C} (hxA : x ∉ A) :
    ∃ s : V,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        x ∈ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ Aᶜ := by
  exact SourceStack.SchemeCurveBelyiConstruction.SectionControlledFiniteMarkedBelyiData.exists_belyiOpen_inside_complement
    D hA hxA

theorem hilbert_schemeSectionControlled_exists_belyiOpen_containing_finite_inside_complement
    [Infinite K] [T1Space (P1 K)]
    {S T : Set C} (hS : S.Finite) (hT : T.Finite) (hdis : Disjoint S T) :
    ∃ s : V,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        T ⊆ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ Sᶜ := by
  exact SourceStack.SchemeCurveBelyiConstruction.SectionControlledFiniteMarkedBelyiData.exists_belyiOpen_containing_finite_inside_complement
    D hS hT hdis

theorem hilbert_schemeSectionControlled_exists_belyiOpen_inside_open_of_finite_complement
    [Infinite K] [T1Space (P1 K)]
    {U : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite) {x : C} (hxU : x ∈ U) :
    ∃ s : V,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        x ∈ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ U := by
  exact SourceStack.SchemeCurveBelyiConstruction.SectionControlledFiniteMarkedBelyiData.exists_belyiOpen_inside_open_of_finite_complement
    D hU hUcompl hxU

theorem hilbert_schemeSectionControlled_exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
    [Infinite K] [T1Space (P1 K)] [SourceStack.NonemptyOpenFiniteComplement C]
    {U : Set C} (hU : IsOpen U) {x : C} (hxU : x ∈ U) :
    ∃ s : V,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        x ∈ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            D.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ U := by
  exact SourceStack.SchemeCurveBelyiConstruction.SectionControlledFiniteMarkedBelyiData.exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
    D hU hxU

theorem hilbert_schemeSectionControlled_exists_belyiOpen_containing_finite_inside_open_of_finite_complement
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
  exact SourceStack.SchemeCurveBelyiConstruction.SectionControlledFiniteMarkedBelyiData.exists_belyiOpen_containing_finite_inside_open_of_finite_complement
    D hU hUcompl hT hTsub

theorem hilbert_schemeSectionControlled_pointwise_cover_complement
    [Infinite K] (κ : Type*) [Finite κ] {S : Set C} (hS : S.Finite)
    (x : κ → {x : C // x ∉ S}) :
    ∃ s : V,
      (FiniteMarkedBelyiExistence.toMarkedCoverData K V
        D.toFiniteMarkedBelyiExistence).sendsSetToBranch S s ∧
        ∀ i, (D.map s).hom.base (x i).1 ∉ markedSchemePointSet K := by
  exact SourceStack.SchemeCurveBelyiConstruction.SectionControlledFiniteMarkedBelyiData.pointwise_cover_complement
    D κ hS x

theorem hilbert_schemeSectionControlled_finite_subcover_on_complement
    [Infinite K] (κ : Type*) [Finite κ] [T1Space (P1 K)]
    {S : Set C} (hS : S.Finite) [CompactSpace (κ → {x : C // x ∉ S})] :
    ∃ t : Finset {s : V //
        (FiniteMarkedBelyiExistence.toMarkedCoverData K V
          D.toFiniteMarkedBelyiExistence).sendsSetToBranch S s},
      (⋃ s ∈ t,
          ((FiniteMarkedBelyiExistence.toMarkedCoverData K V
            D.toFiniteMarkedBelyiExistence).complementCoverData S).tupleAvoidSet
              (κ := κ) s) =
        (Set.univ : Set (κ → {x : C // x ∉ S})) := by
  exact SourceStack.SchemeCurveBelyiConstruction.SectionControlledFiniteMarkedBelyiData.finite_subcover_on_complement
    D κ hS

end SchemeCurveBelyiConstruction

namespace BelyiReduction

open SourceStack.BelyiReduction
open SourceStack.SchemeBelyi
open SourceStack.SchemeMarkedBelyi
open SourceStack.SchemeProjectiveLine

universe u z

variable {K : Type u} [Field K]
variable {C : Scheme.{u}}

theorem hilbert_reductionBadSet_finite
    (aux : C ⟶ SourceStack.SchemeProjectiveLine.P1 K)
    {S : Set C} {badValues : Set (SourceStack.SchemeProjectiveLine.P1 K)}
    (hS : S.Finite) (hbad : badValues.Finite) :
    (reductionBadSet aux S badValues).Finite := by
  exact SourceStack.BelyiReduction.reductionBadSet_finite aux hS hbad

theorem hilbert_aux_image_mem_reductionBadSet_of_mem
    (aux : C ⟶ SourceStack.SchemeProjectiveLine.P1 K)
    {S : Set C} {badValues : Set (SourceStack.SchemeProjectiveLine.P1 K)}
    {x : C} (hx : x ∈ S) :
    aux.base x ∈ reductionBadSet aux S badValues := by
  exact SourceStack.BelyiReduction.aux_image_mem_reductionBadSet_of_mem aux hx

theorem hilbert_badValue_mem_reductionBadSet_of_mem
    (aux : C ⟶ SourceStack.SchemeProjectiveLine.P1 K)
    {S : Set C} {badValues : Set (SourceStack.SchemeProjectiveLine.P1 K)}
    {y : SourceStack.SchemeProjectiveLine.P1 K} (hy : y ∈ badValues) :
    y ∈ reductionBadSet aux S badValues := by
  exact SourceStack.BelyiReduction.badValue_mem_reductionBadSet_of_mem aux hy

theorem hilbert_image_subset_reductionBadSet
    (aux : C ⟶ SourceStack.SchemeProjectiveLine.P1 K)
    (S : Set C) (badValues : Set (SourceStack.SchemeProjectiveLine.P1 K)) :
    aux.base '' S ⊆ reductionBadSet aux S badValues := by
  exact SourceStack.BelyiReduction.image_subset_reductionBadSet aux S badValues

theorem hilbert_badValues_subset_reductionBadSet
    (aux : C ⟶ SourceStack.SchemeProjectiveLine.P1 K)
    (S : Set C) (badValues : Set (SourceStack.SchemeProjectiveLine.P1 K)) :
    badValues ⊆ reductionBadSet aux S badValues := by
  exact SourceStack.BelyiReduction.badValues_subset_reductionBadSet aux S badValues

variable {hmarkedOpen : IsOpen (markedSchemePointSet K)ᶜ}
variable {S T : Set C}

theorem hilbert_p1ReductionStep_ofBadValues_bad
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
    (P1ReductionStep.ofBadValues
      (K := K) (C := C) (hmarkedOpen := hmarkedOpen) (S := S) (T := T)
      hS badValues hbad aux p1Map composed composed_base_eq
      p1Map_maps_bad_to_marked targetPoint maps_T_to_target
      p1Map_target_avoids_marked).bad =
        reductionBadSet aux S badValues := by
  exact SourceStack.BelyiReduction.P1ReductionStep.ofBadValues_bad
    hS badValues hbad aux p1Map composed composed_base_eq
    p1Map_maps_bad_to_marked targetPoint maps_T_to_target
    p1Map_target_avoids_marked

theorem hilbert_p1ReductionStep_ofBadValues_bad_finite
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
    (P1ReductionStep.ofBadValues
      (K := K) (C := C) (hmarkedOpen := hmarkedOpen) (S := S) (T := T)
      hS badValues hbad aux p1Map composed composed_base_eq
      p1Map_maps_bad_to_marked targetPoint maps_T_to_target
      p1Map_target_avoids_marked).bad.Finite := by
  exact SourceStack.BelyiReduction.P1ReductionStep.ofBadValues_bad_finite
    hS badValues hbad aux p1Map composed composed_base_eq
    p1Map_maps_bad_to_marked targetPoint maps_T_to_target
    p1Map_target_avoids_marked

theorem hilbert_p1ReductionStep_ofBadValuesComposed_composed_hom
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
    (P1ReductionStep.ofBadValuesComposed
      (K := K) (C := C) (hmarkedOpen := hmarkedOpen) (S := S) (T := T)
      hS badValues hbad aux p1Map hcomposedEtale
      p1Map_maps_bad_to_marked targetPoint maps_T_to_target
      p1Map_target_avoids_marked).composed.hom =
        aux ≫ p1Map.hom := by
  exact SourceStack.BelyiReduction.P1ReductionStep.ofBadValuesComposed_composed_hom
    hS badValues hbad aux p1Map hcomposedEtale p1Map_maps_bad_to_marked
    targetPoint maps_T_to_target p1Map_target_avoids_marked

theorem hilbert_p1ReductionStep_ofBadValuesComposed_composed_base_eq
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
    (P1ReductionStep.ofBadValuesComposed
      (K := K) (C := C) (hmarkedOpen := hmarkedOpen) (S := S) (T := T)
      hS badValues hbad aux p1Map hcomposedEtale
      p1Map_maps_bad_to_marked targetPoint maps_T_to_target
      p1Map_target_avoids_marked).composed.hom.base x =
        p1Map.hom.base (aux.base x) := by
  exact SourceStack.BelyiReduction.P1ReductionStep.ofBadValuesComposed_composed_base_eq
    hS badValues hbad aux p1Map hcomposedEtale p1Map_maps_bad_to_marked
    targetPoint maps_T_to_target p1Map_target_avoids_marked x

theorem hilbert_p1ReductionStep_ofBadValuesComposedAuxEtale_composed_hom
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
    (P1ReductionStep.ofBadValuesComposedAuxEtale
      (K := K) (C := C) (hmarkedOpen := hmarkedOpen) (S := S) (T := T)
      hS badValues hbad aux p1Map hAuxEtale
      p1Map_maps_bad_to_marked targetPoint maps_T_to_target
      p1Map_target_avoids_marked).composed.hom =
        aux ≫ p1Map.hom := by
  exact SourceStack.BelyiReduction.P1ReductionStep.ofBadValuesComposedAuxEtale_composed_hom
    hS badValues hbad aux p1Map hAuxEtale p1Map_maps_bad_to_marked
    targetPoint maps_T_to_target p1Map_target_avoids_marked

theorem hilbert_p1ReductionStep_ofBadValuesComposedAuxEtale_composed_base_eq
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
    (P1ReductionStep.ofBadValuesComposedAuxEtale
      (K := K) (C := C) (hmarkedOpen := hmarkedOpen) (S := S) (T := T)
      hS badValues hbad aux p1Map hAuxEtale
      p1Map_maps_bad_to_marked targetPoint maps_T_to_target
      p1Map_target_avoids_marked).composed.hom.base x =
        p1Map.hom.base (aux.base x) := by
  exact SourceStack.BelyiReduction.P1ReductionStep.ofBadValuesComposedAuxEtale_composed_base_eq
    hS badValues hbad aux p1Map hAuxEtale p1Map_maps_bad_to_marked
    targetPoint maps_T_to_target p1Map_target_avoids_marked x

variable (R : P1ReductionStep K C hmarkedOpen S T)

theorem hilbert_p1ReductionStep_composed_maps_S_to_marked :
    ∀ x ∈ S, R.composed.hom.base x ∈ markedSchemePointSet K := by
  exact SourceStack.BelyiReduction.P1ReductionStep.composed_maps_S_to_marked R

theorem hilbert_p1ReductionStep_composed_avoids_T_marked :
    ∀ x ∈ T, R.composed.hom.base x ∉ markedSchemePointSet K := by
  exact SourceStack.BelyiReduction.P1ReductionStep.composed_avoids_T_marked R

theorem hilbert_p1ReductionStep_composed_controls :
    (∀ x ∈ S, R.composed.hom.base x ∈ markedSchemePointSet K) ∧
      ∀ x ∈ T, R.composed.hom.base x ∉ markedSchemePointSet K := by
  exact SourceStack.BelyiReduction.P1ReductionStep.composed_controls R

variable (E : P1ReductionExistence K C)

theorem hilbert_p1ReductionExistence_toFiniteMarkedBelyiExistence_hmarkedOpen :
    E.toFiniteMarkedBelyiExistence.hmarkedOpen = E.hmarkedOpen := by
  exact SourceStack.BelyiReduction.P1ReductionExistence.toFiniteMarkedBelyiExistence_hmarkedOpen
    E

theorem hilbert_p1ReductionExistence_toFiniteMarkedBelyiExistence_map_apply
    (i : ReductionIndex C) :
    E.toFiniteMarkedBelyiExistence.map i = E.map i := by
  exact SourceStack.BelyiReduction.P1ReductionExistence.toFiniteMarkedBelyiExistence_map_apply
    E i

theorem hilbert_p1ReductionExistence_exists_for_finite_disjoint
    {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ i : ReductionIndex C,
      (∀ x ∈ S, (E.map i).hom.base x ∈ markedSchemePointSet K) ∧
        ∀ x ∈ T, (E.map i).hom.base x ∉ markedSchemePointSet K := by
  exact SourceStack.BelyiReduction.P1ReductionExistence.exists_for_finite_disjoint
    E hS hT hdis

theorem hilbert_p1ReductionExistence_exists_belyiOpen_inside_complement
    [T1Space (P1 K)]
    {A : Set C} (hA : A.Finite) {x : C} (hxA : x ∉ A) :
    ∃ i : ReductionIndex C,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
        (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ∧
        x ∈ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
          (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
            (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ⊆ Aᶜ := by
  exact SourceStack.BelyiReduction.P1ReductionExistence.exists_belyiOpen_inside_complement
    E hA hxA

theorem hilbert_p1ReductionExistence_exists_belyiOpen_inside_open_of_finite_complement
    [T1Space (P1 K)]
    {U : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite) {x : C} (hxU : x ∈ U) :
    ∃ i : ReductionIndex C,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
        (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ∧
        x ∈ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
          (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
            (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ⊆ U := by
  exact SourceStack.BelyiReduction.P1ReductionExistence.exists_belyiOpen_inside_open_of_finite_complement
    E hU hUcompl hxU

theorem hilbert_p1ReductionExistence_exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
    [T1Space (P1 K)] [SourceStack.NonemptyOpenFiniteComplement C]
    {U : Set C} (hU : IsOpen U) {x : C} (hxU : x ∈ U) :
    ∃ i : ReductionIndex C,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
        (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ∧
        x ∈ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
          (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K
            (ReductionIndex C) E.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen i) ⊆ U := by
  exact SourceStack.BelyiReduction.P1ReductionExistence.exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
    E hU hxU

theorem hilbert_p1ReductionExistence_pointwise_cover_complement
    (κ : Type z) [Finite κ] {S : Set C} (hS : S.Finite)
    (x : κ → {x : C // x ∉ S}) :
    ∃ i : ReductionIndex C,
      (FiniteMarkedBelyiExistence.toMarkedCoverData K
        (ReductionIndex C) E.toFiniteMarkedBelyiExistence).sendsSetToBranch S i ∧
        ∀ j, (E.map i).hom.base (x j).1 ∉ markedSchemePointSet K := by
  exact SourceStack.BelyiReduction.P1ReductionExistence.pointwise_cover_complement
    E κ hS x

theorem hilbert_p1ReductionExistence_finite_subcover_on_complement
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
  exact SourceStack.BelyiReduction.P1ReductionExistence.finite_subcover_on_complement
    E κ hS

end BelyiReduction

namespace ProjectiveSectionMaps

open SourceStack.ProjectiveSectionMaps
open SourceStack.CurveRiemannRoch
open SourceStack.SchemeProjectiveLine
open SourceStack.SchemeMarkedBelyi
open SourceStack.SchemeCurveBelyiConstruction
open SourceStack.MarkedProjectiveLine

universe u v w

variable {K : Type u} [Field K]
variable {X : Type v}
variable {V : Type w} [AddCommGroup V] [Module K V]

theorem hilbert_hasNoCommonZero_of_hasZeroSet_nonzeroOnSet
    (D : RRSectionEvaluationData K X V) (s0 s1 : V) (T : Set X)
    (hzero : HasZeroSet D s0 T)
    (hnonzero : D.nonzeroOnSet T s1) :
    HasNoCommonZero D s0 s1 := by
  exact SourceStack.ProjectiveSectionMaps.hasNoCommonZero_of_hasZeroSet_nonzeroOnSet
    D s0 s1 T hzero hnonzero

variable {C : Scheme.{u}}
variable (P : ProjectiveLineSectionPair K C V)

theorem hilbert_projectiveLineSectionPair_maps_section0_zero_to_marked
    {x : C} (hx : P.evalData.eval x P.section0 = 0) :
    P.hom.base x ∈ markedSchemePointSet K := by
  exact SourceStack.ProjectiveSectionMaps.ProjectiveLineSectionPair.maps_section0_zero_to_marked
    P hx

theorem hilbert_projectiveLineSectionPair_maps_zeroSet_to_marked
    {T : Set C} (hzero : HasZeroSet P.evalData P.section0 T) :
    ∀ x ∈ T, P.hom.base x ∈ markedSchemePointSet K := by
  exact SourceStack.ProjectiveSectionMaps.ProjectiveLineSectionPair.maps_zeroSet_to_marked
    P hzero

theorem hilbert_projectiveLineSectionPair_avoids_zeroPoint_of_section0_nonzero
    {x : C} (hx : P.evalData.eval x P.section0 ≠ 0) :
    P.hom.base x ≠ schemeCarrierPoint K MarkedPointLabel.zero := by
  exact SourceStack.ProjectiveSectionMaps.ProjectiveLineSectionPair.avoids_zeroPoint_of_section0_nonzero
    P hx

theorem hilbert_projectiveLineSectionPair_section0_vanishes_iff_hom_eq_zero
    (x : C) :
    P.evalData.eval x P.section0 = 0 ↔
      P.hom.base x = schemeCarrierPoint K MarkedPointLabel.zero := by
  exact SourceStack.ProjectiveSectionMaps.ProjectiveLineSectionPair.section0_vanishes_iff_hom_eq_zero
    P x

theorem hilbert_projectiveLineSectionPair_section0_nonzero_iff_hom_ne_zero
    (x : C) :
    P.evalData.eval x P.section0 ≠ 0 ↔
      P.hom.base x ≠ schemeCarrierPoint K MarkedPointLabel.zero := by
  exact SourceStack.ProjectiveSectionMaps.ProjectiveLineSectionPair.section0_nonzero_iff_hom_ne_zero
    P x

variable (G : GluedProjectiveLineSectionData K C V)

theorem hilbert_gluedProjectiveLineSectionData_cover_map_globalHom
    (i : G.cover.J) :
    G.cover.map i ≫ G.globalHom = G.localHom i := by
  exact SourceStack.ProjectiveSectionMaps.GluedProjectiveLineSectionData.cover_map_globalHom
    G i

theorem hilbert_gluedProjectiveLineSectionData_globalHom_base_of_cover
    (i : G.cover.J) (x : G.cover.obj i) :
    G.globalHom.base ((G.cover.map i).base x) = (G.localHom i).base x := by
  exact SourceStack.ProjectiveSectionMaps.GluedProjectiveLineSectionData.globalHom_base_of_cover
    G i x

theorem hilbert_gluedProjectiveLineSectionData_global_zero_of_section0_vanishes
    (x : C) (hx : G.evalData.eval x G.section0 = 0) :
    G.globalHom.base x = schemeCarrierPoint K MarkedPointLabel.zero := by
  exact SourceStack.ProjectiveSectionMaps.GluedProjectiveLineSectionData.global_zero_of_section0_vanishes
    G x hx

theorem hilbert_gluedProjectiveLineSectionData_section0_vanishes_of_global_zero
    (x : C)
    (hx : G.globalHom.base x = schemeCarrierPoint K MarkedPointLabel.zero) :
    G.evalData.eval x G.section0 = 0 := by
  exact SourceStack.ProjectiveSectionMaps.GluedProjectiveLineSectionData.section0_vanishes_of_global_zero
    G x hx

theorem hilbert_gluedProjectiveLineSectionData_section0_vanishes_iff_globalHom_eq_zero
    (x : C) :
    G.evalData.eval x G.section0 = 0 ↔
      G.globalHom.base x = schemeCarrierPoint K MarkedPointLabel.zero := by
  exact SourceStack.ProjectiveSectionMaps.GluedProjectiveLineSectionData.section0_vanishes_iff_globalHom_eq_zero
    G x

theorem hilbert_gluedProjectiveLineSectionData_section0_nonzero_iff_globalHom_ne_zero
    (x : C) :
    G.evalData.eval x G.section0 ≠ 0 ↔
      G.globalHom.base x ≠ schemeCarrierPoint K MarkedPointLabel.zero := by
  exact SourceStack.ProjectiveSectionMaps.GluedProjectiveLineSectionData.section0_nonzero_iff_globalHom_ne_zero
    G x

theorem hilbert_gluedProjectiveLineSectionData_toProjectiveLineSectionPair_hom :
    G.toProjectiveLineSectionPair.hom = G.globalHom := by
  exact SourceStack.ProjectiveSectionMaps.GluedProjectiveLineSectionData.toProjectiveLineSectionPair_hom
    G

theorem hilbert_gluedProjectiveLineSectionData_toProjectiveLineSectionPair_maps_section0_zero_to_marked
    {x : C} (hx : G.evalData.eval x G.section0 = 0) :
    G.toProjectiveLineSectionPair.hom.base x ∈ markedSchemePointSet K := by
  exact SourceStack.ProjectiveSectionMaps.GluedProjectiveLineSectionData.toProjectiveLineSectionPair_maps_section0_zero_to_marked
    G hx

variable (SC : StandardChartProjectiveLineSectionData K C V)

theorem hilbert_standardChartProjectiveLineSectionData_localHom_eq
    (i : SC.cover.J) :
    SC.localHom i = SC.localChartHom i ≫ standardChartMap K (SC.chart i) := by
  exact SourceStack.ProjectiveSectionMaps.StandardChartProjectiveLineSectionData.localHom_eq
    SC i

theorem hilbert_standardChartProjectiveLineSectionData_cover_map_globalHom
    (i : SC.cover.J) :
    SC.cover.map i ≫ SC.globalHom = SC.localHom i := by
  exact SourceStack.ProjectiveSectionMaps.StandardChartProjectiveLineSectionData.cover_map_globalHom
    SC i

theorem hilbert_standardChartProjectiveLineSectionData_globalHom_base_of_cover
    (i : SC.cover.J) (x : SC.cover.obj i) :
    SC.globalHom.base ((SC.cover.map i).base x) = (SC.localHom i).base x := by
  exact SourceStack.ProjectiveSectionMaps.StandardChartProjectiveLineSectionData.globalHom_base_of_cover
    SC i x

theorem hilbert_standardChartProjectiveLineSectionData_global_zero_of_section0_vanishes
    (x : C) (hx : SC.evalData.eval x SC.section0 = 0) :
    SC.globalHom.base x = schemeCarrierPoint K MarkedPointLabel.zero := by
  exact SourceStack.ProjectiveSectionMaps.StandardChartProjectiveLineSectionData.global_zero_of_section0_vanishes
    SC x hx

theorem hilbert_standardChartProjectiveLineSectionData_section0_vanishes_of_global_zero
    (x : C)
    (hx : SC.globalHom.base x = schemeCarrierPoint K MarkedPointLabel.zero) :
    SC.evalData.eval x SC.section0 = 0 := by
  exact SourceStack.ProjectiveSectionMaps.StandardChartProjectiveLineSectionData.section0_vanishes_of_global_zero
    SC x hx

theorem hilbert_standardChartProjectiveLineSectionData_section0_vanishes_iff_globalHom_eq_zero
    (x : C) :
    SC.evalData.eval x SC.section0 = 0 ↔
      SC.globalHom.base x = schemeCarrierPoint K MarkedPointLabel.zero := by
  exact SourceStack.ProjectiveSectionMaps.StandardChartProjectiveLineSectionData.section0_vanishes_iff_globalHom_eq_zero
    SC x

theorem hilbert_standardChartProjectiveLineSectionData_section0_nonzero_iff_globalHom_ne_zero
    (x : C) :
    SC.evalData.eval x SC.section0 ≠ 0 ↔
      SC.globalHom.base x ≠ schemeCarrierPoint K MarkedPointLabel.zero := by
  exact SourceStack.ProjectiveSectionMaps.StandardChartProjectiveLineSectionData.section0_nonzero_iff_globalHom_ne_zero
    SC x

theorem hilbert_standardChartProjectiveLineSectionData_toProjectiveLineSectionPair_hom :
    SC.toProjectiveLineSectionPair.hom = SC.globalHom := by
  exact SourceStack.ProjectiveSectionMaps.StandardChartProjectiveLineSectionData.toProjectiveLineSectionPair_hom
    SC

theorem hilbert_standardChartProjectiveLineSectionData_toProjectiveLineSectionPair_maps_section0_zero_to_marked
    {x : C} (hx : SC.evalData.eval x SC.section0 = 0) :
    SC.toProjectiveLineSectionPair.hom.base x ∈ markedSchemePointSet K := by
  exact SourceStack.ProjectiveSectionMaps.StandardChartProjectiveLineSectionData.toProjectiveLineSectionPair_maps_section0_zero_to_marked
    SC hx

variable (RD : StandardChartProjectiveLineSectionRingData K C V)

theorem hilbert_standardChartProjectiveLineSectionRingData_localHom_eq
    (i : RD.cover.J) :
    RD.localHom i = RD.localChartHom i ≫ standardChartMap K (RD.chart i) := by
  exact SourceStack.ProjectiveSectionMaps.StandardChartProjectiveLineSectionRingData.localHom_eq
    RD i

theorem hilbert_standardChartProjectiveLineSectionRingData_cover_map_globalHom
    (i : RD.cover.J) :
    RD.cover.map i ≫ RD.globalHom = RD.localHom i := by
  exact SourceStack.ProjectiveSectionMaps.StandardChartProjectiveLineSectionRingData.cover_map_globalHom
    RD i

theorem hilbert_standardChartProjectiveLineSectionRingData_globalHom_base_of_cover
    (i : RD.cover.J) (x : RD.cover.obj i) :
    RD.globalHom.base ((RD.cover.map i).base x) = (RD.localHom i).base x := by
  exact SourceStack.ProjectiveSectionMaps.StandardChartProjectiveLineSectionRingData.globalHom_base_of_cover
    RD i x

theorem hilbert_standardChartProjectiveLineSectionRingData_global_zero_of_section0_vanishes
    (x : C) (hx : RD.evalData.eval x RD.section0 = 0) :
    RD.globalHom.base x = schemeCarrierPoint K MarkedPointLabel.zero := by
  exact SourceStack.ProjectiveSectionMaps.StandardChartProjectiveLineSectionRingData.global_zero_of_section0_vanishes
    RD x hx

theorem hilbert_standardChartProjectiveLineSectionRingData_section0_vanishes_of_global_zero
    (x : C)
    (hx : RD.globalHom.base x = schemeCarrierPoint K MarkedPointLabel.zero) :
    RD.evalData.eval x RD.section0 = 0 := by
  exact SourceStack.ProjectiveSectionMaps.StandardChartProjectiveLineSectionRingData.section0_vanishes_of_global_zero
    RD x hx

theorem hilbert_standardChartProjectiveLineSectionRingData_section0_vanishes_iff_globalHom_eq_zero
    (x : C) :
    RD.evalData.eval x RD.section0 = 0 ↔
      RD.globalHom.base x = schemeCarrierPoint K MarkedPointLabel.zero := by
  exact SourceStack.ProjectiveSectionMaps.StandardChartProjectiveLineSectionRingData.section0_vanishes_iff_globalHom_eq_zero
    RD x

theorem hilbert_standardChartProjectiveLineSectionRingData_section0_nonzero_iff_globalHom_ne_zero
    (x : C) :
    RD.evalData.eval x RD.section0 ≠ 0 ↔
      RD.globalHom.base x ≠ schemeCarrierPoint K MarkedPointLabel.zero := by
  exact SourceStack.ProjectiveSectionMaps.StandardChartProjectiveLineSectionRingData.section0_nonzero_iff_globalHom_ne_zero
    RD x

theorem hilbert_standardChartProjectiveLineSectionRingData_toProjectiveLineSectionPair_hom :
    RD.toProjectiveLineSectionPair.hom = RD.globalHom := by
  exact SourceStack.ProjectiveSectionMaps.StandardChartProjectiveLineSectionRingData.toProjectiveLineSectionPair_hom
    RD

theorem hilbert_standardChartProjectiveLineSectionRingData_toProjectiveLineSectionPair_maps_section0_zero_to_marked
    {x : C} (hx : RD.evalData.eval x RD.section0 = 0) :
    RD.toProjectiveLineSectionPair.hom.base x ∈ markedSchemePointSet K := by
  exact SourceStack.ProjectiveSectionMaps.StandardChartProjectiveLineSectionRingData.toProjectiveLineSectionPair_maps_section0_zero_to_marked
    RD hx

variable (SRD : SectionRatioProjectiveLineSectionData K C V)

theorem hilbert_sectionRatioProjectiveLineSectionData_localCoordinate_eq_ratio
    (i : SRD.cover.J) :
    SRD.localCoordinate i = SRD.localSectionRatio i := by
  exact SourceStack.ProjectiveSectionMaps.SectionRatioProjectiveLineSectionData.localCoordinate_eq_ratio
    SRD i

theorem hilbert_sectionRatioProjectiveLineSectionData_localChartRingHom_coordinate_eq_ratio
    (i : SRD.cover.J) :
    SRD.localChartRingHom i (standardChartCoordinate K (SRD.chart i)) =
      SRD.localSectionRatio i := by
  exact SourceStack.ProjectiveSectionMaps.SectionRatioProjectiveLineSectionData.localChartRingHom_coordinate_eq_ratio
    SRD i

theorem hilbert_sectionRatioProjectiveLineSectionData_localHom_eq
    (i : SRD.cover.J) :
    SRD.localHom i = SRD.localChartHom i ≫ standardChartMap K (SRD.chart i) := by
  exact SourceStack.ProjectiveSectionMaps.SectionRatioProjectiveLineSectionData.localHom_eq
    SRD i

theorem hilbert_sectionRatioProjectiveLineSectionData_cover_map_globalHom
    (i : SRD.cover.J) :
    SRD.cover.map i ≫ SRD.globalHom = SRD.localHom i := by
  exact SourceStack.ProjectiveSectionMaps.SectionRatioProjectiveLineSectionData.cover_map_globalHom
    SRD i

theorem hilbert_sectionRatioProjectiveLineSectionData_globalHom_base_of_cover
    (i : SRD.cover.J) (x : SRD.cover.obj i) :
    SRD.globalHom.base ((SRD.cover.map i).base x) = (SRD.localHom i).base x := by
  exact SourceStack.ProjectiveSectionMaps.SectionRatioProjectiveLineSectionData.globalHom_base_of_cover
    SRD i x

theorem hilbert_sectionRatioProjectiveLineSectionData_global_zero_of_section0_vanishes
    (x : C) (hx : SRD.evalData.eval x SRD.section0 = 0) :
    SRD.globalHom.base x = schemeCarrierPoint K MarkedPointLabel.zero := by
  exact SourceStack.ProjectiveSectionMaps.SectionRatioProjectiveLineSectionData.global_zero_of_section0_vanishes
    SRD x hx

theorem hilbert_sectionRatioProjectiveLineSectionData_section0_vanishes_of_global_zero
    (x : C)
    (hx : SRD.globalHom.base x = schemeCarrierPoint K MarkedPointLabel.zero) :
    SRD.evalData.eval x SRD.section0 = 0 := by
  exact SourceStack.ProjectiveSectionMaps.SectionRatioProjectiveLineSectionData.section0_vanishes_of_global_zero
    SRD x hx

theorem hilbert_sectionRatioProjectiveLineSectionData_section0_vanishes_iff_globalHom_eq_zero
    (x : C) :
    SRD.evalData.eval x SRD.section0 = 0 ↔
      SRD.globalHom.base x = schemeCarrierPoint K MarkedPointLabel.zero := by
  exact SourceStack.ProjectiveSectionMaps.SectionRatioProjectiveLineSectionData.section0_vanishes_iff_globalHom_eq_zero
    SRD x

theorem hilbert_sectionRatioProjectiveLineSectionData_section0_nonzero_iff_globalHom_ne_zero
    (x : C) :
    SRD.evalData.eval x SRD.section0 ≠ 0 ↔
      SRD.globalHom.base x ≠ schemeCarrierPoint K MarkedPointLabel.zero := by
  exact SourceStack.ProjectiveSectionMaps.SectionRatioProjectiveLineSectionData.section0_nonzero_iff_globalHom_ne_zero
    SRD x

theorem hilbert_sectionRatioProjectiveLineSectionData_toProjectiveLineSectionPair_hom :
    SRD.toProjectiveLineSectionPair.hom = SRD.globalHom := by
  exact SourceStack.ProjectiveSectionMaps.SectionRatioProjectiveLineSectionData.toProjectiveLineSectionPair_hom
    SRD

theorem hilbert_sectionRatioProjectiveLineSectionData_toProjectiveLineSectionPair_maps_section0_zero_to_marked
    {x : C} (hx : SRD.evalData.eval x SRD.section0 = 0) :
    SRD.toProjectiveLineSectionPair.hom.base x ∈ markedSchemePointSet K := by
  exact SourceStack.ProjectiveSectionMaps.SectionRatioProjectiveLineSectionData.toProjectiveLineSectionPair_maps_section0_zero_to_marked
    SRD hx

theorem hilbert_localSectionRatioChart_toStandardAffineChart_section0 :
    LocalSectionRatioChart.toStandardAffineChart LocalSectionRatioChart.section0 =
      StandardAffineChart.x0 := by
  exact SourceStack.ProjectiveSectionMaps.LocalSectionRatioChart.toStandardAffineChart_section0

theorem hilbert_localSectionRatioChart_toStandardAffineChart_section1 :
    LocalSectionRatioChart.toStandardAffineChart LocalSectionRatioChart.section1 =
      StandardAffineChart.x1 := by
  exact SourceStack.ProjectiveSectionMaps.LocalSectionRatioChart.toStandardAffineChart_section1

theorem hilbert_localSectionRatioChart_ratioEquation_section0
    {R : Type*} [Mul R] (s0 s1 ratio : R) :
    LocalSectionRatioChart.ratioEquation
      LocalSectionRatioChart.section0 s0 s1 ratio ↔ ratio * s0 = s1 := by
  exact SourceStack.ProjectiveSectionMaps.LocalSectionRatioChart.ratioEquation_section0
    s0 s1 ratio

theorem hilbert_localSectionRatioChart_ratioEquation_section1
    {R : Type*} [Mul R] (s0 s1 ratio : R) :
    LocalSectionRatioChart.ratioEquation
      LocalSectionRatioChart.section1 s0 s1 ratio ↔ ratio * s1 = s0 := by
  exact SourceStack.ProjectiveSectionMaps.LocalSectionRatioChart.ratioEquation_section1
    s0 s1 ratio

theorem hilbert_localSectionRatioChart_unitRatio_mul_denominator_eq_numerator
    {R : Type*} [CommMonoid R]
    (c : LocalSectionRatioChart) (s0 s1 : R) (u : Rˣ)
    (hden : LocalSectionRatioChart.denominator c s0 s1 = (u : R)) :
    LocalSectionRatioChart.unitRatio c s0 s1 u *
        LocalSectionRatioChart.denominator c s0 s1 =
      LocalSectionRatioChart.numerator c s0 s1 := by
  exact SourceStack.ProjectiveSectionMaps.LocalSectionRatioChart.unitRatio_mul_denominator_eq_numerator
    c s0 s1 u hden

variable (TD : TrivializedSectionRatioData K C V)

theorem hilbert_trivializedSectionRatioData_chart_eq
    (i : TD.cover.J) :
    TD.chart i = LocalSectionRatioChart.toStandardAffineChart (TD.ratioChart i) := by
  exact SourceStack.ProjectiveSectionMaps.TrivializedSectionRatioData.chart_eq TD i

theorem hilbert_trivializedSectionRatioData_local_ratio_mul_denominator_eq_numerator
    (i : TD.cover.J) :
    TD.localSectionRatio i *
        LocalSectionRatioChart.denominator (TD.ratioChart i)
          (TD.localSection0 i) (TD.localSection1 i) =
      LocalSectionRatioChart.numerator (TD.ratioChart i)
        (TD.localSection0 i) (TD.localSection1 i) := by
  exact SourceStack.ProjectiveSectionMaps.TrivializedSectionRatioData.local_ratio_mul_denominator_eq_numerator
    TD i

theorem hilbert_trivializedSectionRatioData_localChartRingHom_coordinate_eq_ratio
    (i : TD.cover.J) :
    TD.localChartRingHom i (standardChartCoordinate K (TD.chart i)) =
      TD.localSectionRatio i := by
  exact SourceStack.ProjectiveSectionMaps.TrivializedSectionRatioData.localChartRingHom_coordinate_eq_ratio
    TD i

theorem hilbert_trivializedSectionRatioData_cover_map_globalHom
    (i : TD.cover.J) :
    TD.cover.map i ≫ TD.globalHom = TD.localHom i := by
  exact SourceStack.ProjectiveSectionMaps.TrivializedSectionRatioData.cover_map_globalHom
    TD i

theorem hilbert_trivializedSectionRatioData_globalHom_base_of_cover
    (i : TD.cover.J) (x : TD.cover.obj i) :
    TD.globalHom.base ((TD.cover.map i).base x) = (TD.localHom i).base x := by
  exact SourceStack.ProjectiveSectionMaps.TrivializedSectionRatioData.globalHom_base_of_cover
    TD i x

theorem hilbert_trivializedSectionRatioData_global_zero_of_section0_vanishes
    (x : C) (hx : TD.evalData.eval x TD.section0 = 0) :
    TD.globalHom.base x = schemeCarrierPoint K MarkedPointLabel.zero := by
  exact SourceStack.ProjectiveSectionMaps.TrivializedSectionRatioData.global_zero_of_section0_vanishes
    TD x hx

theorem hilbert_trivializedSectionRatioData_section0_vanishes_of_global_zero
    (x : C)
    (hx : TD.globalHom.base x = schemeCarrierPoint K MarkedPointLabel.zero) :
    TD.evalData.eval x TD.section0 = 0 := by
  exact SourceStack.ProjectiveSectionMaps.TrivializedSectionRatioData.section0_vanishes_of_global_zero
    TD x hx

theorem hilbert_trivializedSectionRatioData_section0_vanishes_iff_globalHom_eq_zero
    (x : C) :
    TD.evalData.eval x TD.section0 = 0 ↔
      TD.globalHom.base x = schemeCarrierPoint K MarkedPointLabel.zero := by
  exact SourceStack.ProjectiveSectionMaps.TrivializedSectionRatioData.section0_vanishes_iff_globalHom_eq_zero
    TD x

theorem hilbert_trivializedSectionRatioData_section0_nonzero_iff_globalHom_ne_zero
    (x : C) :
    TD.evalData.eval x TD.section0 ≠ 0 ↔
      TD.globalHom.base x ≠ schemeCarrierPoint K MarkedPointLabel.zero := by
  exact SourceStack.ProjectiveSectionMaps.TrivializedSectionRatioData.section0_nonzero_iff_globalHom_ne_zero
    TD x

theorem hilbert_trivializedSectionRatioData_toProjectiveLineSectionPair_hom :
    TD.toProjectiveLineSectionPair.hom = TD.globalHom := by
  exact SourceStack.ProjectiveSectionMaps.TrivializedSectionRatioData.toProjectiveLineSectionPair_hom
    TD

theorem hilbert_trivializedSectionRatioData_toProjectiveLineSectionPair_maps_section0_zero_to_marked
    {x : C} (hx : TD.evalData.eval x TD.section0 = 0) :
    TD.toProjectiveLineSectionPair.hom.base x ∈ markedSchemePointSet K := by
  exact SourceStack.ProjectiveSectionMaps.TrivializedSectionRatioData.toProjectiveLineSectionPair_maps_section0_zero_to_marked
    TD hx

variable (UD : TrivializedUnitSectionRatioData K C V)

theorem hilbert_trivializedUnitSectionRatioData_denominator_eq_unit
    (i : UD.cover.J) :
    LocalSectionRatioChart.denominator (UD.ratioChart i)
        (UD.localSection0 i) (UD.localSection1 i) =
      (UD.denominatorUnit i : Γ(UD.cover.obj i, ⊤)) := by
  exact SourceStack.ProjectiveSectionMaps.TrivializedUnitSectionRatioData.denominator_eq_unit
    UD i

theorem hilbert_trivializedUnitSectionRatioData_local_ratio_mul_denominator_eq_numerator
    (i : UD.cover.J) :
    UD.localSectionRatio i *
        LocalSectionRatioChart.denominator (UD.ratioChart i)
          (UD.localSection0 i) (UD.localSection1 i) =
      LocalSectionRatioChart.numerator (UD.ratioChart i)
        (UD.localSection0 i) (UD.localSection1 i) := by
  exact SourceStack.ProjectiveSectionMaps.TrivializedUnitSectionRatioData.local_ratio_mul_denominator_eq_numerator
    UD i

theorem hilbert_trivializedUnitSectionRatioData_localChartCoordinate_eq_ratio
    (i : UD.cover.J) :
    standardChartCoordinateSection K (UD.localChartRingHom i) =
      UD.localSectionRatio i := by
  exact SourceStack.ProjectiveSectionMaps.TrivializedUnitSectionRatioData.localChartCoordinate_eq_ratio
    UD i

theorem hilbert_trivializedUnitSectionRatioData_toProjectiveLineSectionPair_hom :
    UD.toProjectiveLineSectionPair.hom = UD.globalHom := by
  exact SourceStack.ProjectiveSectionMaps.TrivializedUnitSectionRatioData.toProjectiveLineSectionPair_hom
    UD

theorem hilbert_trivializedUnitSectionRatioData_section0_vanishes_iff_globalHom_eq_zero
    (x : C) :
    UD.evalData.eval x UD.section0 = 0 ↔
      UD.globalHom.base x = schemeCarrierPoint K MarkedPointLabel.zero := by
  exact SourceStack.ProjectiveSectionMaps.TrivializedUnitSectionRatioData.section0_vanishes_iff_globalHom_eq_zero
    UD x

theorem hilbert_trivializedUnitSectionRatioData_section0_nonzero_iff_globalHom_ne_zero
    (x : C) :
    UD.evalData.eval x UD.section0 ≠ 0 ↔
      UD.globalHom.base x ≠ schemeCarrierPoint K MarkedPointLabel.zero := by
  exact SourceStack.ProjectiveSectionMaps.TrivializedUnitSectionRatioData.section0_nonzero_iff_globalHom_ne_zero
    UD x

theorem hilbert_trivializedUnitSectionRatioData_toProjectiveLineSectionPair_maps_section0_zero_to_marked
    {x : C} (hx : UD.evalData.eval x UD.section0 = 0) :
    UD.toProjectiveLineSectionPair.hom.base x ∈ markedSchemePointSet K := by
  exact SourceStack.ProjectiveSectionMaps.TrivializedUnitSectionRatioData.toProjectiveLineSectionPair_maps_section0_zero_to_marked
    UD hx

variable (IUD : TrivializedIsUnitSectionRatioData K C V)

theorem hilbert_trivializedIsUnitSectionRatioData_denominator_eq_unit
    (i : IUD.cover.J) :
    LocalSectionRatioChart.denominator (IUD.ratioChart i)
        (IUD.localSection0 i) (IUD.localSection1 i) =
      (IUD.denominatorUnit i : Γ(IUD.cover.obj i, ⊤)) := by
  exact SourceStack.ProjectiveSectionMaps.TrivializedIsUnitSectionRatioData.denominator_eq_unit
    IUD i

theorem hilbert_trivializedIsUnitSectionRatioData_local_ratio_mul_denominator_eq_numerator
    (i : IUD.cover.J) :
    IUD.localSectionRatio i *
        LocalSectionRatioChart.denominator (IUD.ratioChart i)
          (IUD.localSection0 i) (IUD.localSection1 i) =
      LocalSectionRatioChart.numerator (IUD.ratioChart i)
        (IUD.localSection0 i) (IUD.localSection1 i) := by
  exact SourceStack.ProjectiveSectionMaps.TrivializedIsUnitSectionRatioData.local_ratio_mul_denominator_eq_numerator
    IUD i

theorem hilbert_trivializedIsUnitSectionRatioData_localChartCoordinate_eq_ratio
    (i : IUD.cover.J) :
    standardChartCoordinateSection K (IUD.localChartRingHom i) =
      IUD.localSectionRatio i := by
  exact SourceStack.ProjectiveSectionMaps.TrivializedIsUnitSectionRatioData.localChartCoordinate_eq_ratio
    IUD i

theorem hilbert_trivializedIsUnitSectionRatioData_toProjectiveLineSectionPair_hom :
    IUD.toProjectiveLineSectionPair.hom = IUD.globalHom := by
  exact SourceStack.ProjectiveSectionMaps.TrivializedIsUnitSectionRatioData.toProjectiveLineSectionPair_hom
    IUD

theorem hilbert_trivializedIsUnitSectionRatioData_section0_vanishes_iff_globalHom_eq_zero
    (x : C) :
    IUD.evalData.eval x IUD.section0 = 0 ↔
      IUD.globalHom.base x = schemeCarrierPoint K MarkedPointLabel.zero := by
  exact SourceStack.ProjectiveSectionMaps.TrivializedIsUnitSectionRatioData.section0_vanishes_iff_globalHom_eq_zero
    IUD x

theorem hilbert_trivializedIsUnitSectionRatioData_section0_nonzero_iff_globalHom_ne_zero
    (x : C) :
    IUD.evalData.eval x IUD.section0 ≠ 0 ↔
      IUD.globalHom.base x ≠ schemeCarrierPoint K MarkedPointLabel.zero := by
  exact SourceStack.ProjectiveSectionMaps.TrivializedIsUnitSectionRatioData.section0_nonzero_iff_globalHom_ne_zero
    IUD x

theorem hilbert_trivializedIsUnitSectionRatioData_toProjectiveLineSectionPair_maps_section0_zero_to_marked
    {x : C} (hx : IUD.evalData.eval x IUD.section0 = 0) :
    IUD.toProjectiveLineSectionPair.hom.base x ∈ markedSchemePointSet K := by
  exact SourceStack.ProjectiveSectionMaps.TrivializedIsUnitSectionRatioData.toProjectiveLineSectionPair_maps_section0_zero_to_marked
    IUD hx

theorem hilbert_twoSectionBezoutCover_eq
    (C : Scheme.{u}) (s0 s1 a b : Γ(C, ⊤))
    (h : a * s0 + b * s1 = 1) :
    twoSectionBezoutCover C s0 s1 a b h =
      SourceStack.Schemes.twoSectionBasicOpenCoverOfLinearCombination
        C s0 s1 a b h := by
  rfl

theorem hilbert_twoSectionRatioChart_zero :
    twoSectionRatioChart 0 = LocalSectionRatioChart.section0 := by
  exact SourceStack.ProjectiveSectionMaps.twoSectionRatioChart_zero

theorem hilbert_twoSectionRatioChart_one :
    twoSectionRatioChart 1 = LocalSectionRatioChart.section1 := by
  exact SourceStack.ProjectiveSectionMaps.twoSectionRatioChart_one

theorem hilbert_twoSectionLocalSection0_eq
    (C : Scheme.{u}) (s0 s1 a b : Γ(C, ⊤))
    (h : a * s0 + b * s1 = 1) (i : Fin 2) :
    twoSectionLocalSection0 C s0 s1 a b h i =
      SourceStack.Schemes.basicOpenTopRestrict C
        (SourceStack.Schemes.twoElementFamily s0 s1 i) s0 := by
  rfl

theorem hilbert_twoSectionLocalSection1_eq
    (C : Scheme.{u}) (s0 s1 a b : Γ(C, ⊤))
    (h : a * s0 + b * s1 = 1) (i : Fin 2) :
    twoSectionLocalSection1 C s0 s1 a b h i =
      SourceStack.Schemes.basicOpenTopRestrict C
        (SourceStack.Schemes.twoElementFamily s0 s1 i) s1 := by
  rfl

theorem hilbert_twoSectionLocal_denominator_isUnit
    (C : Scheme.{u}) (s0 s1 a b : Γ(C, ⊤))
    (h : a * s0 + b * s1 = 1) (i : Fin 2) :
    IsUnit (LocalSectionRatioChart.denominator (twoSectionRatioChart i)
      (twoSectionLocalSection0 C s0 s1 a b h i)
      (twoSectionLocalSection1 C s0 s1 a b h i)) := by
  exact SourceStack.ProjectiveSectionMaps.twoSectionLocal_denominator_isUnit
    C s0 s1 a b h i

variable (TSD : TwoSectionBezoutTrivializedIsUnitData K C V)

theorem hilbert_twoSectionBezoutTrivializedIsUnitData_cover :
    TwoSectionBezoutTrivializedIsUnitData.cover TSD =
      twoSectionBezoutCover C TSD.globalSection0 TSD.globalSection1
        TSD.bezoutCoeff0 TSD.bezoutCoeff1 TSD.bezout := by
  rfl

theorem hilbert_twoSectionBezoutTrivializedIsUnitData_ratioChart :
    TwoSectionBezoutTrivializedIsUnitData.ratioChart TSD =
      twoSectionRatioChart := by
  rfl

theorem hilbert_twoSectionBezoutTrivializedIsUnitData_localSection0
    (i : (TwoSectionBezoutTrivializedIsUnitData.cover TSD).J) :
    TwoSectionBezoutTrivializedIsUnitData.localSection0 TSD i =
      twoSectionLocalSection0 C TSD.globalSection0 TSD.globalSection1
        TSD.bezoutCoeff0 TSD.bezoutCoeff1 TSD.bezout i := by
  rfl

theorem hilbert_twoSectionBezoutTrivializedIsUnitData_localSection1
    (i : (TwoSectionBezoutTrivializedIsUnitData.cover TSD).J) :
    TwoSectionBezoutTrivializedIsUnitData.localSection1 TSD i =
      twoSectionLocalSection1 C TSD.globalSection0 TSD.globalSection1
        TSD.bezoutCoeff0 TSD.bezoutCoeff1 TSD.bezout i := by
  rfl

theorem hilbert_twoSectionBezoutTrivializedIsUnitData_denominator_isUnit
    (i : (TwoSectionBezoutTrivializedIsUnitData.cover TSD).J) :
    IsUnit (LocalSectionRatioChart.denominator
      (TwoSectionBezoutTrivializedIsUnitData.ratioChart TSD i)
      (TwoSectionBezoutTrivializedIsUnitData.localSection0 TSD i)
      (TwoSectionBezoutTrivializedIsUnitData.localSection1 TSD i)) := by
  exact SourceStack.ProjectiveSectionMaps.TwoSectionBezoutTrivializedIsUnitData.denominator_isUnit
    TSD i

theorem hilbert_twoSectionBezoutTrivializedIsUnitData_toTrivialized_cover :
    (TwoSectionBezoutTrivializedIsUnitData.toTrivializedIsUnitSectionRatioData TSD).cover =
      TwoSectionBezoutTrivializedIsUnitData.cover TSD := by
  rfl

theorem hilbert_twoSectionBezoutTrivializedIsUnitData_toTrivialized_ratioChart
    (i : (TwoSectionBezoutTrivializedIsUnitData.cover TSD).J) :
    (TwoSectionBezoutTrivializedIsUnitData.toTrivializedIsUnitSectionRatioData TSD).ratioChart i =
      TwoSectionBezoutTrivializedIsUnitData.ratioChart TSD i := by
  rfl

theorem hilbert_twoSectionBezoutTrivializedIsUnitData_toTrivialized_denominator_isUnit
    (i : (TwoSectionBezoutTrivializedIsUnitData.cover TSD).J) :
    (TwoSectionBezoutTrivializedIsUnitData.toTrivializedIsUnitSectionRatioData TSD).denominator_isUnit i =
      TwoSectionBezoutTrivializedIsUnitData.denominator_isUnit TSD i := by
  rfl

theorem hilbert_twoSectionBezoutTrivializedIsUnitData_toTrivialized_localSection0
    (i : (TwoSectionBezoutTrivializedIsUnitData.cover TSD).J) :
    (TwoSectionBezoutTrivializedIsUnitData.toTrivializedIsUnitSectionRatioData TSD).localSection0 i =
      TwoSectionBezoutTrivializedIsUnitData.localSection0 TSD i := by
  exact SourceStack.ProjectiveSectionMaps.TwoSectionBezoutTrivializedIsUnitData.toTrivialized_localSection0
    TSD i

theorem hilbert_twoSectionBezoutTrivializedIsUnitData_toTrivialized_localSection1
    (i : (TwoSectionBezoutTrivializedIsUnitData.cover TSD).J) :
    (TwoSectionBezoutTrivializedIsUnitData.toTrivializedIsUnitSectionRatioData TSD).localSection1 i =
      TwoSectionBezoutTrivializedIsUnitData.localSection1 TSD i := by
  exact SourceStack.ProjectiveSectionMaps.TwoSectionBezoutTrivializedIsUnitData.toTrivialized_localSection1
    TSD i

theorem hilbert_twoSectionBezoutTrivializedIsUnitData_toTrivialized_localChartRingHom
    (i : (TwoSectionBezoutTrivializedIsUnitData.cover TSD).J) :
    (TwoSectionBezoutTrivializedIsUnitData.toTrivializedIsUnitSectionRatioData TSD).localChartRingHom i =
      TwoSectionBezoutTrivializedIsUnitData.localChartRingHom TSD i := by
  exact SourceStack.ProjectiveSectionMaps.TwoSectionBezoutTrivializedIsUnitData.toTrivialized_localChartRingHom
    TSD i

theorem hilbert_twoSectionBezoutTrivializedIsUnitData_toTrivialized_localSectionRatio_eq_unitRatio
    (i : (TwoSectionBezoutTrivializedIsUnitData.cover TSD).J) :
    (TwoSectionBezoutTrivializedIsUnitData.toTrivializedIsUnitSectionRatioData TSD).localSectionRatio i =
      LocalSectionRatioChart.unitRatio
        (TwoSectionBezoutTrivializedIsUnitData.ratioChart TSD i)
        (TwoSectionBezoutTrivializedIsUnitData.localSection0 TSD i)
        (TwoSectionBezoutTrivializedIsUnitData.localSection1 TSD i)
        ((TwoSectionBezoutTrivializedIsUnitData.denominator_isUnit TSD i).unit) := by
  exact SourceStack.ProjectiveSectionMaps.TwoSectionBezoutTrivializedIsUnitData.toTrivialized_localSectionRatio_eq_unitRatio
    TSD i

theorem hilbert_twoSectionBezoutTrivializedIsUnitData_toTrivialized_localChartCoordinate_eq_ratio
    (i : (TwoSectionBezoutTrivializedIsUnitData.cover TSD).J) :
    standardChartCoordinateSection K
        ((TwoSectionBezoutTrivializedIsUnitData.toTrivializedIsUnitSectionRatioData TSD).localChartRingHom i) =
      (TwoSectionBezoutTrivializedIsUnitData.toTrivializedIsUnitSectionRatioData TSD).localSectionRatio i := by
  exact SourceStack.ProjectiveSectionMaps.TwoSectionBezoutTrivializedIsUnitData.toTrivialized_localChartCoordinate_eq_ratio
    TSD i

theorem hilbert_twoSectionBezoutTrivializedIsUnitData_toTrivialized_local_ratio_mul_denominator_eq_numerator
    (i : (TwoSectionBezoutTrivializedIsUnitData.cover TSD).J) :
    (TwoSectionBezoutTrivializedIsUnitData.toTrivializedIsUnitSectionRatioData TSD).localSectionRatio i *
        LocalSectionRatioChart.denominator
          ((TwoSectionBezoutTrivializedIsUnitData.toTrivializedIsUnitSectionRatioData TSD).ratioChart i)
          ((TwoSectionBezoutTrivializedIsUnitData.toTrivializedIsUnitSectionRatioData TSD).localSection0 i)
          ((TwoSectionBezoutTrivializedIsUnitData.toTrivializedIsUnitSectionRatioData TSD).localSection1 i) =
      LocalSectionRatioChart.numerator
        ((TwoSectionBezoutTrivializedIsUnitData.toTrivializedIsUnitSectionRatioData TSD).ratioChart i)
        ((TwoSectionBezoutTrivializedIsUnitData.toTrivializedIsUnitSectionRatioData TSD).localSection0 i)
        ((TwoSectionBezoutTrivializedIsUnitData.toTrivializedIsUnitSectionRatioData TSD).localSection1 i) := by
  exact SourceStack.ProjectiveSectionMaps.TwoSectionBezoutTrivializedIsUnitData.toTrivialized_local_ratio_mul_denominator_eq_numerator
    TSD i

variable (F : ProjectiveSectionFiniteMarkedFamily K C V)

theorem hilbert_projectiveSectionFiniteMarkedFamily_toSectionControlled_map_apply
    (s : V) :
    F.toSectionControlledFiniteMarkedBelyiData.map s = F.map s := by
  exact SourceStack.ProjectiveSectionMaps.ProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData_map_apply
    F s

theorem hilbert_projectiveSectionFiniteMarkedFamily_exists_for_finite_disjoint
    [Infinite K] {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V, (∀ x ∈ S, (F.map s).hom.base x ∈ markedSchemePointSet K) ∧
      ∀ x ∈ T, (F.map s).hom.base x ∉ markedSchemePointSet K := by
  exact SourceStack.ProjectiveSectionMaps.ProjectiveSectionFiniteMarkedFamily.exists_for_finite_disjoint
    F hS hT hdis

theorem hilbert_projectiveSectionFiniteMarkedFamily_exists_belyiOpen_inside_complement
    [Infinite K] [T1Space (P1 K)]
    {A : Set C} (hA : A.Finite) {x : C} (hxA : x ∉ A) :
    ∃ s : V,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        x ∈ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ Aᶜ := by
  exact SourceStack.ProjectiveSectionMaps.ProjectiveSectionFiniteMarkedFamily.exists_belyiOpen_inside_complement
    F hA hxA

theorem hilbert_projectiveSectionFiniteMarkedFamily_exists_belyiOpen_inside_open_of_finite_complement
    [Infinite K] [T1Space (P1 K)]
    {U : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite) {x : C} (hxU : x ∈ U) :
    ∃ s : V,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        x ∈ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ U := by
  exact SourceStack.ProjectiveSectionMaps.ProjectiveSectionFiniteMarkedFamily.exists_belyiOpen_inside_open_of_finite_complement
    F hU hUcompl hxU

theorem hilbert_projectiveSectionFiniteMarkedFamily_exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
    [Infinite K] [T1Space (P1 K)] [SourceStack.NonemptyOpenFiniteComplement C]
    {U : Set C} (hU : IsOpen U) {x : C} (hxU : x ∈ U) :
    ∃ s : V,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        x ∈ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            F.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ U := by
  exact SourceStack.ProjectiveSectionMaps.ProjectiveSectionFiniteMarkedFamily.exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
    F hU hxU

variable (TF : TrivializedProjectiveSectionFiniteMarkedFamily K C V)

theorem hilbert_trivializedProjectiveSectionFiniteMarkedFamily_pair_hom
    (s : V) :
    (TF.pair s).hom = (TF.trivialized s).globalHom := by
  exact SourceStack.ProjectiveSectionMaps.TrivializedProjectiveSectionFiniteMarkedFamily.pair_hom
    TF s

theorem hilbert_trivializedProjectiveSectionFiniteMarkedFamily_map_base_eq_pair
    (s : V) (x : C) :
    (TF.map s).hom.base x = (TF.pair s).hom.base x := by
  exact SourceStack.ProjectiveSectionMaps.TrivializedProjectiveSectionFiniteMarkedFamily.map_base_eq_pair
    TF s x

theorem hilbert_trivializedProjectiveSectionFiniteMarkedFamily_pair_section0_eval_eq_index
    (s : V) (x : C) :
    (TF.pair s).evalData.eval x (TF.pair s).section0 =
      TF.evalPackage.eval x s := by
  exact SourceStack.ProjectiveSectionMaps.TrivializedProjectiveSectionFiniteMarkedFamily.pair_section0_eval_eq_index
    TF s x

theorem hilbert_trivializedProjectiveSectionFiniteMarkedFamily_toProjectiveSectionFiniteMarkedFamily_map_apply
    (s : V) :
    TF.toProjectiveSectionFiniteMarkedFamily.map s = TF.map s := by
  exact SourceStack.ProjectiveSectionMaps.TrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily_map_apply
    TF s

theorem hilbert_trivializedProjectiveSectionFiniteMarkedFamily_exists_for_finite_disjoint
    [Infinite K] {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V, (∀ x ∈ S, (TF.map s).hom.base x ∈ markedSchemePointSet K) ∧
      ∀ x ∈ T, (TF.map s).hom.base x ∉ markedSchemePointSet K := by
  exact SourceStack.ProjectiveSectionMaps.TrivializedProjectiveSectionFiniteMarkedFamily.exists_for_finite_disjoint
    TF hS hT hdis

theorem hilbert_trivializedProjectiveSectionFiniteMarkedFamily_exists_belyiOpen_inside_complement
    [Infinite K] [T1Space (P1 K)]
    {A : Set C} (hA : A.Finite) {x : C} (hxA : x ∉ A) :
    ∃ s : V,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        TF.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        x ∈ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          TF.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            TF.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ Aᶜ := by
  exact SourceStack.ProjectiveSectionMaps.TrivializedProjectiveSectionFiniteMarkedFamily.exists_belyiOpen_inside_complement
    TF hA hxA

theorem hilbert_trivializedProjectiveSectionFiniteMarkedFamily_exists_belyiOpen_inside_open_of_finite_complement
    [Infinite K] [T1Space (P1 K)]
    {U : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite) {x : C} (hxU : x ∈ U) :
    ∃ s : V,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        TF.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        x ∈ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          TF.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            TF.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ U := by
  exact SourceStack.ProjectiveSectionMaps.TrivializedProjectiveSectionFiniteMarkedFamily.exists_belyiOpen_inside_open_of_finite_complement
    TF hU hUcompl hxU

theorem hilbert_trivializedProjectiveSectionFiniteMarkedFamily_exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
    [Infinite K] [T1Space (P1 K)] [SourceStack.NonemptyOpenFiniteComplement C]
    {U : Set C} (hU : IsOpen U) {x : C} (hxU : x ∈ U) :
    ∃ s : V,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        TF.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        x ∈ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          TF.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            TF.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ U := by
  exact SourceStack.ProjectiveSectionMaps.TrivializedProjectiveSectionFiniteMarkedFamily.exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
    TF hU hxU

variable (ITF : IsUnitTrivializedProjectiveSectionFiniteMarkedFamily K C V)

theorem hilbert_isUnitTrivializedProjectiveSectionFiniteMarkedFamily_pair_hom
    (s : V) :
    (ITF.pair s).hom = (ITF.trivialized s).globalHom := by
  exact SourceStack.ProjectiveSectionMaps.IsUnitTrivializedProjectiveSectionFiniteMarkedFamily.pair_hom
    ITF s

theorem hilbert_isUnitTrivializedProjectiveSectionFiniteMarkedFamily_map_base_eq_pair
    (s : V) (x : C) :
    (ITF.map s).hom.base x = (ITF.pair s).hom.base x := by
  exact SourceStack.ProjectiveSectionMaps.IsUnitTrivializedProjectiveSectionFiniteMarkedFamily.map_base_eq_pair
    ITF s x

theorem hilbert_isUnitTrivializedProjectiveSectionFiniteMarkedFamily_pair_section0_eval_eq_index
    (s : V) (x : C) :
    (ITF.pair s).evalData.eval x (ITF.pair s).section0 =
      ITF.evalPackage.eval x s := by
  exact SourceStack.ProjectiveSectionMaps.IsUnitTrivializedProjectiveSectionFiniteMarkedFamily.pair_section0_eval_eq_index
    ITF s x

theorem hilbert_isUnitTrivializedProjectiveSectionFiniteMarkedFamily_toProjectiveSectionFiniteMarkedFamily_map_apply
    (s : V) :
    ITF.toProjectiveSectionFiniteMarkedFamily.map s = ITF.map s := by
  exact SourceStack.ProjectiveSectionMaps.IsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily_map_apply
    ITF s

theorem hilbert_isUnitTrivializedProjectiveSectionFiniteMarkedFamily_exists_for_finite_disjoint
    [Infinite K] {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V, (∀ x ∈ S, (ITF.map s).hom.base x ∈ markedSchemePointSet K) ∧
      ∀ x ∈ T, (ITF.map s).hom.base x ∉ markedSchemePointSet K := by
  exact SourceStack.ProjectiveSectionMaps.IsUnitTrivializedProjectiveSectionFiniteMarkedFamily.exists_for_finite_disjoint
    ITF hS hT hdis

theorem hilbert_isUnitTrivializedProjectiveSectionFiniteMarkedFamily_exists_belyiOpen_inside_complement
    [Infinite K] [T1Space (P1 K)]
    {A : Set C} (hA : A.Finite) {x : C} (hxA : x ∉ A) :
    ∃ s : V,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        ITF.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        x ∈ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          ITF.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            ITF.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ Aᶜ := by
  exact SourceStack.ProjectiveSectionMaps.IsUnitTrivializedProjectiveSectionFiniteMarkedFamily.exists_belyiOpen_inside_complement
    ITF hA hxA

theorem hilbert_isUnitTrivializedProjectiveSectionFiniteMarkedFamily_exists_belyiOpen_inside_open_of_finite_complement
    [Infinite K] [T1Space (P1 K)]
    {U : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite) {x : C} (hxU : x ∈ U) :
    ∃ s : V,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        ITF.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        x ∈ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          ITF.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            ITF.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ U := by
  exact SourceStack.ProjectiveSectionMaps.IsUnitTrivializedProjectiveSectionFiniteMarkedFamily.exists_belyiOpen_inside_open_of_finite_complement
    ITF hU hUcompl hxU

theorem hilbert_isUnitTrivializedProjectiveSectionFiniteMarkedFamily_exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
    [Infinite K] [T1Space (P1 K)] [SourceStack.NonemptyOpenFiniteComplement C]
    {U : Set C} (hU : IsOpen U) {x : C} (hxU : x ∈ U) :
    ∃ s : V,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        ITF.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        x ∈ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          ITF.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            ITF.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ U := by
  exact SourceStack.ProjectiveSectionMaps.IsUnitTrivializedProjectiveSectionFiniteMarkedFamily.exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
    ITF hU hxU

variable (TSF : TwoSectionBezoutProjectiveSectionFiniteMarkedFamily K C V)

theorem hilbert_twoSectionBezoutProjectiveSectionFiniteMarkedFamily_evalPackage :
    TSF.evalPackage = TSF.isUnitFamily.evalPackage := by
  rfl

theorem hilbert_twoSectionBezoutProjectiveSectionFiniteMarkedFamily_trivialized
    (s : V) :
    TSF.trivialized s = TSF.isUnitFamily.trivialized s := by
  rfl

theorem hilbert_twoSectionBezoutProjectiveSectionFiniteMarkedFamily_trivialized_evalData_eq_spec
    (s : V) :
    (TSF.trivialized s).evalData = (TSF.twoSection s).evalData := by
  exact SourceStack.ProjectiveSectionMaps.TwoSectionBezoutProjectiveSectionFiniteMarkedFamily.trivialized_evalData_eq_spec
    TSF s

theorem hilbert_twoSectionBezoutProjectiveSectionFiniteMarkedFamily_trivialized_section0_eq_spec
    (s : V) :
    (TSF.trivialized s).section0 = (TSF.twoSection s).section0 := by
  exact SourceStack.ProjectiveSectionMaps.TwoSectionBezoutProjectiveSectionFiniteMarkedFamily.trivialized_section0_eq_spec
    TSF s

theorem hilbert_twoSectionBezoutProjectiveSectionFiniteMarkedFamily_trivialized_section1_eq_spec
    (s : V) :
    (TSF.trivialized s).section1 = (TSF.twoSection s).section1 := by
  exact SourceStack.ProjectiveSectionMaps.TwoSectionBezoutProjectiveSectionFiniteMarkedFamily.trivialized_section1_eq_spec
    TSF s

theorem hilbert_twoSectionBezoutProjectiveSectionFiniteMarkedFamily_toIsUnit_map_apply
    (s : V) :
    TSF.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.map s = TSF.map s := by
  exact SourceStack.ProjectiveSectionMaps.TwoSectionBezoutProjectiveSectionFiniteMarkedFamily.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily_map_apply
    TSF s

theorem hilbert_twoSectionBezoutProjectiveSectionFiniteMarkedFamily_exists_for_finite_disjoint
    [Infinite K] {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V, (∀ x ∈ S, (TSF.map s).hom.base x ∈ markedSchemePointSet K) ∧
      ∀ x ∈ T, (TSF.map s).hom.base x ∉ markedSchemePointSet K := by
  exact SourceStack.ProjectiveSectionMaps.TwoSectionBezoutProjectiveSectionFiniteMarkedFamily.exists_for_finite_disjoint
    TSF hS hT hdis

theorem hilbert_twoSectionBezoutProjectiveSectionFiniteMarkedFamily_exists_belyiOpen_inside_complement
    [Infinite K] [T1Space (P1 K)]
    {A : Set C} (hA : A.Finite) {x : C} (hxA : x ∉ A) :
    ∃ s : V,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        TSF.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        x ∈ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          TSF.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            TSF.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ Aᶜ := by
  exact SourceStack.ProjectiveSectionMaps.TwoSectionBezoutProjectiveSectionFiniteMarkedFamily.exists_belyiOpen_inside_complement
    TSF hA hxA

theorem hilbert_twoSectionBezoutProjectiveSectionFiniteMarkedFamily_exists_belyiOpen_inside_open_of_finite_complement
    [Infinite K] [T1Space (P1 K)]
    {U : Set C} (hU : IsOpen U) (hUcompl : Uᶜ.Finite) {x : C} (hxU : x ∈ U) :
    ∃ s : V,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        TSF.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        x ∈ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          TSF.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            TSF.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ U := by
  exact SourceStack.ProjectiveSectionMaps.TwoSectionBezoutProjectiveSectionFiniteMarkedFamily.exists_belyiOpen_inside_open_of_finite_complement
    TSF hU hUcompl hxU

theorem hilbert_twoSectionBezoutProjectiveSectionFiniteMarkedFamily_exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
    [Infinite K] [T1Space (P1 K)] [SourceStack.NonemptyOpenFiniteComplement C]
    {U : Set C} (hU : IsOpen U) {x : C} (hxU : x ∈ U) :
    ∃ s : V,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
        TSF.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
        x ∈ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
          TSF.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K V
            TSF.toIsUnitTrivializedProjectiveSectionFiniteMarkedFamily.toProjectiveSectionFiniteMarkedFamily.toSectionControlledFiniteMarkedBelyiData.toFiniteMarkedBelyiExistence).toBelyiCoverData.belyiOpen s) ⊆ U := by
  exact SourceStack.ProjectiveSectionMaps.TwoSectionBezoutProjectiveSectionFiniteMarkedFamily.exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
    TSF hU hxU

end ProjectiveSectionMaps

namespace CurveDivisorSections

open SourceStack.CurveDivisorSections
open SourceStack.ProjectiveSectionMaps

universe u v w

variable {K : Type u} [Field K]
variable {X : Type v}
variable {V : Type w} [AddCommGroup V] [Module K V]
variable (D : DivisorZeroSectionData K X V)

theorem hilbert_divisorZeroSection_zeroSection_hasZeroSet_apply :
    HasZeroSet D.evalData D.zeroSection D.support := by
  exact SourceStack.CurveDivisorSections.DivisorZeroSectionData.zeroSection_hasZeroSet_apply
    D

theorem hilbert_divisorZeroSection_exists_section_nonzero_on_support
    [Infinite K] (hsupport : D.support.Finite) :
    ∃ s1 : V, D.evalData.nonzeroOnSet D.support s1 := by
  exact SourceStack.CurveDivisorSections.DivisorZeroSectionData.exists_section_nonzero_on_support
    D hsupport

theorem hilbert_divisorZeroSection_hasNoCommonZero_zeroSection_of_nonzero_on_support
    {s1 : V} (hs1 : D.evalData.nonzeroOnSet D.support s1) :
    HasNoCommonZero D.evalData D.zeroSection s1 := by
  exact SourceStack.CurveDivisorSections.DivisorZeroSectionData.hasNoCommonZero_zeroSection_of_nonzero_on_support
    D hs1

theorem hilbert_divisorZeroSection_exists_second_section_no_common_zero
    [Infinite K] (hsupport : D.support.Finite) :
    ∃ s1 : V, HasNoCommonZero D.evalData D.zeroSection s1 := by
  exact SourceStack.CurveDivisorSections.DivisorZeroSectionData.exists_second_section_no_common_zero
    D hsupport

open SourceStack.SchemeProjectiveLine in
theorem hilbert_divisorZeroSection_projectivePair_maps_support_to_marked
    {C : Scheme.{u}} (D : DivisorZeroSectionData K C V)
    (P : SourceStack.ProjectiveSectionMaps.ProjectiveLineSectionPair K C V)
    (heval : P.evalData = D.evalData)
    (hsection0 : P.section0 = D.zeroSection) :
    ∀ x ∈ D.support, P.hom.base x ∈ markedSchemePointSet K := by
  exact SourceStack.CurveDivisorSections.DivisorZeroSectionData.projectivePair_maps_support_to_marked
    D P heval hsection0

open SourceStack.SchemeProjectiveLine in
theorem hilbert_divisorZeroSection_exists_projectivePair_maps_support_to_marked
    [Infinite K] {C : Scheme.{u}} (D : DivisorZeroSectionData K C V)
    (hsupport : D.support.Finite)
    (mkPair : ∀ s1 : V, HasNoCommonZero D.evalData D.zeroSection s1 →
      SourceStack.ProjectiveSectionMaps.ProjectiveLineSectionPair K C V)
    (hmk_eval : ∀ s1 hnc, (mkPair s1 hnc).evalData = D.evalData)
    (hmk_section0 : ∀ s1 hnc, (mkPair s1 hnc).section0 = D.zeroSection) :
    ∃ s1 : V, ∃ hnc : HasNoCommonZero D.evalData D.zeroSection s1,
      ∀ x ∈ D.support, (mkPair s1 hnc).hom.base x ∈ markedSchemePointSet K := by
  exact SourceStack.CurveDivisorSections.DivisorZeroSectionData.exists_projectivePair_maps_support_to_marked
    D hsupport mkPair hmk_eval hmk_section0

end CurveDivisorSections

namespace CurveCohomologySections

open SourceStack.CurveCohomologySections
open SourceStack.CurveDivisorSections
open SourceStack.ProjectiveSectionMaps

universe u v w

variable {K : Type u} [Field K]
variable {X : Type v}
variable {V : Type w} [AddCommGroup V] [Module K V]

theorem hilbert_linearMap_ne_zero_of_surjective
    {W : Type*} [AddCommGroup W] [Module K W] [Nontrivial W]
    (f : V →ₗ[K] W) (hf : Function.Surjective f) :
    f ≠ 0 := by
  exact SourceStack.CurveCohomologySections.linearMap_ne_zero_of_surjective
    f hf

variable (E : EvaluationSurjectivityData K X V)

theorem hilbert_evaluationSurjectivity_eval_nonzero_on_support :
    ∀ x ∈ E.support, E.evalData.eval x ≠ 0 := by
  exact SourceStack.CurveCohomologySections.EvaluationSurjectivityData.eval_nonzero_on_support
    E

variable (RE : RestrictedEvaluationSurjectivityData K X V)

theorem hilbert_restrictedEvaluationSurjectivity_restricted_eval_nonzero :
    ∀ {S T : Finset X}, Disjoint S T →
      ∀ x ∈ T,
        (RE.evalData.eval x).comp
            (SourceStack.commonKernel (K := K) (V := V) S RE.evalData.eval).subtype ≠ 0 := by
  exact
    SourceStack.CurveCohomologySections.RestrictedEvaluationSurjectivityData.restricted_eval_nonzero
      RE

theorem hilbert_restrictedEvaluationSurjectivity_toRiemannRochFiniteEvaluationPackage_eval
    (x : X) :
    RE.toRiemannRochFiniteEvaluationPackage.eval x = RE.evalData.eval x := by
  exact
    SourceStack.CurveCohomologySections.RestrictedEvaluationSurjectivityData.toRiemannRochFiniteEvaluationPackage_eval
      RE x

theorem hilbert_restrictedEvaluationSurjectivity_exists_section_for_disjoint_finsets
    [Infinite K] {S T : Finset X} (hdis : Disjoint S T) :
    ∃ s : V, RE.evalData.vanishesOn S s ∧ RE.evalData.nonzeroOn T s := by
  exact
    SourceStack.CurveCohomologySections.RestrictedEvaluationSurjectivityData.exists_section_for_disjoint_finsets
      RE hdis

theorem hilbert_restrictedEvaluationSurjectivity_exists_section_for_disjoint_finite_sets
    [Infinite K] {S T : Set X} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ s : V, RE.evalData.vanishesOnSet S s ∧ RE.evalData.nonzeroOnSet T s := by
  exact
    SourceStack.CurveCohomologySections.RestrictedEvaluationSurjectivityData.exists_section_for_disjoint_finite_sets
      RE hS hT hdis

variable (D : CohomologicalDivisorSectionData K X V)

theorem hilbert_cohomologicalDivisor_toDivisorZeroSectionData_support :
    D.toDivisorZeroSectionData.support = D.evalSurjectivity.support := by
  exact SourceStack.CurveCohomologySections.CohomologicalDivisorSectionData.toDivisorZeroSectionData_support
    D

theorem hilbert_cohomologicalDivisor_exists_section_nonzero_on_support
    [Infinite K] (hsupport : D.evalSurjectivity.support.Finite) :
    ∃ s1 : V, D.evalSurjectivity.evalData.nonzeroOnSet
      D.evalSurjectivity.support s1 := by
  exact SourceStack.CurveCohomologySections.CohomologicalDivisorSectionData.exists_section_nonzero_on_support
    D hsupport

theorem hilbert_cohomologicalDivisor_exists_second_section_no_common_zero
    [Infinite K] (hsupport : D.evalSurjectivity.support.Finite) :
    ∃ s1 : V, HasNoCommonZero
      D.evalSurjectivity.evalData D.zeroSection s1 := by
  exact SourceStack.CurveCohomologySections.CohomologicalDivisorSectionData.exists_second_section_no_common_zero
    D hsupport

open SourceStack.SchemeProjectiveLine in
theorem hilbert_cohomologicalDivisor_projectivePair_maps_support_to_marked
    {C : Scheme.{u}} (D : CohomologicalDivisorSectionData K C V)
    (P : SourceStack.ProjectiveSectionMaps.ProjectiveLineSectionPair K C V)
    (heval : P.evalData = D.evalSurjectivity.evalData)
    (hsection0 : P.section0 = D.zeroSection) :
    ∀ x ∈ D.evalSurjectivity.support, P.hom.base x ∈ markedSchemePointSet K := by
  exact SourceStack.CurveCohomologySections.CohomologicalDivisorSectionData.projectivePair_maps_support_to_marked
    D P heval hsection0

open SourceStack.SchemeProjectiveLine in
theorem hilbert_cohomologicalDivisor_exists_projectivePair_maps_support_to_marked
    [Infinite K] {C : Scheme.{u}} (D : CohomologicalDivisorSectionData K C V)
    (hsupport : D.evalSurjectivity.support.Finite)
    (mkPair : ∀ s1 : V,
      HasNoCommonZero D.evalSurjectivity.evalData D.zeroSection s1 →
        SourceStack.ProjectiveSectionMaps.ProjectiveLineSectionPair K C V)
    (hmk_eval : ∀ s1 hnc, (mkPair s1 hnc).evalData = D.evalSurjectivity.evalData)
    (hmk_section0 : ∀ s1 hnc, (mkPair s1 hnc).section0 = D.zeroSection) :
    ∃ s1 : V,
      ∃ hnc : HasNoCommonZero D.evalSurjectivity.evalData D.zeroSection s1,
        ∀ x ∈ D.evalSurjectivity.support,
          (mkPair s1 hnc).hom.base x ∈ markedSchemePointSet K := by
  exact SourceStack.CurveCohomologySections.CohomologicalDivisorSectionData.exists_projectivePair_maps_support_to_marked
    D hsupport mkPair hmk_eval hmk_section0

end CurveCohomologySections

section ComplexSeparation

theorem hilbert_finset_complex_inf_norm_sub_pos
    (S : Finset ℂ) (β : ℂ) (hS : S.Nonempty) (hβ : β ∉ S) :
    0 < S.inf' hS (fun α : ℂ => ‖α - β‖) := by
  exact SourceStack.finset_complex_inf_norm_sub_pos S β hS hβ

theorem hilbert_exists_complex_point_nearby_separating_finset
    (S : Finset ℂ) (β : ℂ) (C : ℝ) (hC : 0 < C) (hβ : β ∉ S) :
    ∃ lam : ℂ,
      lam ≠ β ∧
      (∀ α ∈ S, lam ≠ α) ∧
      ∀ α ∈ S, C * ‖β - lam‖ ≤ ‖α - lam‖ := by
  exact SourceStack.exists_complex_point_nearby_separating_finset S β C hC hβ

theorem hilbert_exists_reciprocal_translate_separating_finset
    (S : Finset ℂ) (β : ℂ) (C : ℝ) (hC : 0 < C) (hβ : β ∉ S) :
    ∃ lam : ℂ,
      lam ≠ β ∧
      (∀ α ∈ S, lam ≠ α) ∧
      ∀ α ∈ S,
        C * ‖SourceStack.reciprocalTranslate lam α‖ ≤
          ‖SourceStack.reciprocalTranslate lam β‖ := by
  exact SourceStack.exists_reciprocal_translate_separating_finset S β C hC hβ

theorem hilbert_exists_rational_reciprocal_translate_separating_finset
    (S : Finset ℂ) (β : ℚ) (C : ℝ) (hC : 0 < C) (hβ : (β : ℂ) ∉ S) :
    ∃ lam : ℚ,
      (lam : ℂ) ≠ (β : ℂ) ∧
      (∀ α ∈ S, (lam : ℂ) ≠ α) ∧
      ∀ α ∈ S,
        C * ‖SourceStack.reciprocalTranslate (lam : ℂ) α‖ ≤
          ‖SourceStack.reciprocalTranslate (lam : ℂ) (β : ℂ)‖ := by
  exact SourceStack.exists_rational_reciprocal_translate_separating_finset S β C hC hβ

end ComplexSeparation

namespace AffineSpace

universe u v

variable (n : Type v)
variable {S T U X : Scheme.{max u v}}

theorem hilbert_homOfVector_over
    (f : X ⟶ S) (w : n → Γ(X, ⊤)) :
    AlgebraicGeometry.AffineSpace.homOfVector f w ≫ 𝔸(n; S) ↘ S = f := by
  exact SourceStack.AffineSpace.homOfVector_over n f w

theorem hilbert_homOfVector_appTop_coord
    (f : X ⟶ S) (w : n → Γ(X, ⊤)) (i : n) :
    (AlgebraicGeometry.AffineSpace.homOfVector f w).appTop
      (AlgebraicGeometry.AffineSpace.coord S i) = w i := by
  exact SourceStack.AffineSpace.homOfVector_appTop_coord n f w i

theorem hilbert_hom_ext
    {f g : X ⟶ 𝔸(n; S)}
    (h₁ : f ≫ 𝔸(n; S) ↘ S = g ≫ 𝔸(n; S) ↘ S)
    (h₂ : ∀ i,
      f.appTop (AlgebraicGeometry.AffineSpace.coord S i) =
        g.appTop (AlgebraicGeometry.AffineSpace.coord S i)) :
    f = g := by
  exact SourceStack.AffineSpace.hom_ext n h₁ h₂

theorem hilbert_homOverEquiv_exists
    [X.Over S] :
    Nonempty ({ f : X ⟶ 𝔸(n; S) // f.IsOver S } ≃ (n → Γ(X, ⊤))) := by
  exact SourceStack.AffineSpace.homOverEquiv_exists n

theorem hilbert_isoOfIsAffine_exists
    [IsAffine S] :
    Nonempty (𝔸(n; S) ≅ Spec (.of (MvPolynomial n Γ(S, ⊤)))) := by
  exact SourceStack.AffineSpace.isoOfIsAffine_exists n

theorem hilbert_affineSpace_isAffine_of_base
    [IsAffine S] :
    IsAffine 𝔸(n; S) := by
  exact SourceStack.AffineSpace.affineSpace_isAffine_of_base n

theorem hilbert_SpecIso_exists
    (R : CommRingCat.{max u v}) :
    Nonempty (𝔸(n; Spec R) ≅ Spec (.of (MvPolynomial n R))) := by
  exact SourceStack.AffineSpace.SpecIso_exists n R

theorem hilbert_map_over
    (f : S ⟶ T) :
    AlgebraicGeometry.AffineSpace.map n f ≫ 𝔸(n; T) ↘ T =
      𝔸(n; S) ↘ S ≫ f := by
  exact SourceStack.AffineSpace.map_over n f

theorem hilbert_map_appTop_coord
    (f : S ⟶ T) (i : n) :
    (AlgebraicGeometry.AffineSpace.map n f).appTop
      (AlgebraicGeometry.AffineSpace.coord T i) =
        AlgebraicGeometry.AffineSpace.coord S i := by
  exact SourceStack.AffineSpace.map_appTop_coord n f i

theorem hilbert_map_id :
    AlgebraicGeometry.AffineSpace.map n (𝟙 S) = 𝟙 𝔸(n; S) := by
  exact SourceStack.AffineSpace.map_id n

theorem hilbert_map_comp
    (f : S ⟶ T) (g : T ⟶ U) :
    AlgebraicGeometry.AffineSpace.map n (f ≫ g) =
      AlgebraicGeometry.AffineSpace.map n f ≫
        AlgebraicGeometry.AffineSpace.map n g := by
  exact SourceStack.AffineSpace.map_comp n f g

theorem hilbert_reindex_over
    {m : Type v} (i : m → n) :
    AlgebraicGeometry.AffineSpace.reindex i S ≫ 𝔸(m; S) ↘ S =
      𝔸(n; S) ↘ S := by
  exact SourceStack.AffineSpace.reindex_over n i

theorem hilbert_reindex_appTop_coord
    {m : Type v} (i : m → n) (j : m) :
    (AlgebraicGeometry.AffineSpace.reindex i S).appTop
      (AlgebraicGeometry.AffineSpace.coord S j) =
        AlgebraicGeometry.AffineSpace.coord S (i j) := by
  exact SourceStack.AffineSpace.reindex_appTop_coord n i j

theorem hilbert_reindex_id :
    AlgebraicGeometry.AffineSpace.reindex (@id n) S = 𝟙 𝔸(n; S) := by
  exact SourceStack.AffineSpace.reindex_id n

theorem hilbert_reindex_comp
    {n₁ n₂ n₃ : Type v} (i : n₁ → n₂) (j : n₂ → n₃)
    (S : Scheme.{max u v}) :
    AlgebraicGeometry.AffineSpace.reindex (j ∘ i) S =
      AlgebraicGeometry.AffineSpace.reindex j S ≫
        AlgebraicGeometry.AffineSpace.reindex i S := by
  exact SourceStack.AffineSpace.reindex_comp i j S

theorem hilbert_map_reindex
    {n₁ n₂ : Type v} (i : n₁ → n₂) (f : S ⟶ T) :
    AlgebraicGeometry.AffineSpace.map n₂ f ≫
        AlgebraicGeometry.AffineSpace.reindex i T =
      AlgebraicGeometry.AffineSpace.reindex i S ≫
        AlgebraicGeometry.AffineSpace.map n₁ f := by
  exact SourceStack.AffineSpace.map_reindex i f

end AffineSpace

section Topology

variable {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {s : Set X} {f : X → Y}

theorem hilbert_lorscheid_compact_image
    (hs : IsCompact s)
    (hf : Continuous f) :
    IsCompact (f '' s) := by
  exact SourceStack.lorscheid_compact_image hs hf

theorem hilbert_compact_elim_finite_subcover_indexed
    {b : Set ι} {c : ι → Set X}
    (hs : IsCompact s)
    (hcopen : ∀ i ∈ b, IsOpen (c i))
    (hcover : s ⊆ ⋃ i ∈ b, c i) :
    ∃ b' : Set ι, b' ⊆ b ∧ Set.Finite b' ∧ s ⊆ ⋃ i ∈ b', c i := by
  exact SourceStack.compact_elim_finite_subcover_indexed hs hcopen hcover

theorem hilbert_compactSpace_elim_finite_subcover
    [CompactSpace X] (U : ι → Set X)
    (hUopen : ∀ i, IsOpen (U i))
    (hcover : (Set.univ : Set X) ⊆ ⋃ i, U i) :
    ∃ t : Finset ι, (Set.univ : Set X) ⊆ ⋃ i ∈ t, U i := by
  exact SourceStack.compactSpace_elim_finite_subcover U hUopen hcover

theorem hilbert_compactSpace_finite_subcover_eq_univ
    [CompactSpace X] (U : ι → Set X)
    (hUopen : ∀ i, IsOpen (U i))
    (hcover : (Set.univ : Set X) ⊆ ⋃ i, U i) :
    ∃ t : Finset ι, (⋃ i ∈ t, U i) = (Set.univ : Set X) := by
  exact SourceStack.compactSpace_finite_subcover_eq_univ U hUopen hcover

theorem hilbert_isOpen_preimage_continuous
    (hf : Continuous f) {U : Set Y} (hU : IsOpen U) :
    IsOpen (f ⁻¹' U) := by
  exact SourceStack.isOpen_preimage_continuous hf hU

theorem hilbert_isOpen_iInter_of_finite_index
    {κ : Type*} [Finite κ] (U : κ → Set X)
    (hU : ∀ i, IsOpen (U i)) :
    IsOpen (⋂ i, U i) := by
  exact SourceStack.isOpen_iInter_of_finite_index U hU

theorem hilbert_finite_compl_isOpen
    [T1Space X] {T : Set X} (hT : T.Finite) :
    IsOpen Tᶜ := by
  exact SourceStack.finite_compl_isOpen hT

theorem hilbert_finite_compl_of_isOpen_nonempty
    [SourceStack.NonemptyOpenFiniteComplement X] {U : Set X}
    (hU : IsOpen U) (hne : U.Nonempty) :
    Uᶜ.Finite := by
  exact SourceStack.finite_compl_of_isOpen_nonempty hU hne

theorem hilbert_finite_compl_of_isOpen_of_mem
    [SourceStack.NonemptyOpenFiniteComplement X] {U : Set X}
    (hU : IsOpen U) {x : X} (hx : x ∈ U) :
    Uᶜ.Finite := by
  exact SourceStack.finite_compl_of_isOpen_of_mem hU hx

theorem hilbert_cofiniteTopology_finite_compl_of_isOpen_nonempty
    (X : Type*) {U : Set (CofiniteTopology X)}
    (hU : IsOpen U) (hne : U.Nonempty) :
    Uᶜ.Finite := by
  exact SourceStack.finite_compl_of_isOpen_nonempty hU hne

theorem hilbert_isOpen_avoid_finite_preimage
    [T1Space Y] (hf : Continuous f) {T : Set Y} (hT : T.Finite) :
    IsOpen {x : X | f x ∉ T} := by
  exact SourceStack.isOpen_avoid_finite_preimage hf hT

theorem hilbert_isOpen_pi_avoid_finite
    {κ : Type*} [Finite κ] [T1Space Y]
    (φ : X → Y) (hφ : Continuous φ) {T : Set Y} (hT : T.Finite) :
    IsOpen {x : κ → X | ∀ i, φ (x i) ∉ T} := by
  exact SourceStack.isOpen_pi_avoid_finite φ hφ hT

theorem hilbert_compact_iUnion_of_finite
    {κ : Type*} [Finite κ] (K : κ → Set X)
    (hK : ∀ i, IsCompact (K i)) :
    IsCompact (⋃ i, K i) := by
  exact SourceStack.compact_iUnion_of_finite K hK

theorem hilbert_compact_iUnion_image_of_finite
    {κ : Type*} [Finite κ] (K : κ → Set X)
    (hK : ∀ i, IsCompact (K i)) (hf : Continuous f) :
    IsCompact (⋃ i, f '' K i) := by
  exact SourceStack.compact_iUnion_image_of_finite K hK hf

theorem hilbert_compact_pi_projection_image
    {κ : Type*} {Z : κ → Type*} [∀ i, TopologicalSpace (Z i)]
    {t : Set ((i : κ) → Z i)} (ht : IsCompact t) (i : κ) :
    IsCompact ((fun x : (j : κ) → Z j => x i) '' t) := by
  exact SourceStack.compact_pi_projection_image ht i

theorem hilbert_compact_iUnion_pi_projection_image
    {ι κ : Type*} [Finite ι] {Z : κ → Type*}
    [∀ i, TopologicalSpace (Z i)]
    (K : ι → Set ((i : κ) → Z i))
    (hK : ∀ i, IsCompact (K i)) (j : κ) :
    IsCompact (⋃ i, (fun x : (l : κ) → Z l => x j) '' K i) := by
  exact SourceStack.compact_iUnion_pi_projection_image K hK j

theorem hilbert_iUnion_pi_projection_image_subset_of_forall
    {ι κ : Type*} {Z : κ → Type*}
    (K : ι → Set ((i : κ) → Z i)) (A : (i : κ) → Set (Z i))
    (hK : ∀ i x, x ∈ K i → ∀ j, x j ∈ A j) (j : κ) :
    (⋃ i, (fun x : (l : κ) → Z l => x j) '' K i) ⊆ A j := by
  exact SourceStack.iUnion_pi_projection_image_subset_of_forall K A hK j

theorem hilbert_compactSpace_pi
    {κ : Type*} (Z : κ → Type*) [∀ i, TopologicalSpace (Z i)]
    [∀ i, CompactSpace (Z i)] :
    CompactSpace ((i : κ) → Z i) := by
  exact SourceStack.compactSpace_pi Z

theorem hilbert_sigmaCompact_of_locallyCompact_secondCountable
    [LocallyCompactSpace X] [SecondCountableTopology X] :
    SigmaCompactSpace X := by
  exact SourceStack.sigmaCompact_of_locallyCompact_secondCountable

theorem hilbert_compactExhaustion_of_locallyCompact_secondCountable
    [LocallyCompactSpace X] [SecondCountableTopology X] :
    Nonempty (CompactExhaustion X) := by
  exact SourceStack.compactExhaustion_of_locallyCompact_secondCountable

theorem hilbert_compactExhaustion_of_isOpen_subtype
    [LocallyCompactSpace X] [SecondCountableTopology X]
    {U : Set X} (hU : IsOpen U) :
    Nonempty (CompactExhaustion U) := by
  exact SourceStack.compactExhaustion_of_isOpen_subtype hU

theorem hilbert_compactExhaustion_isCompact
    (K : CompactExhaustion X) (n : ℕ) :
    IsCompact (K n) := by
  exact SourceStack.compactExhaustion_isCompact K n

theorem hilbert_compactExhaustion_iUnion_eq
    (K : CompactExhaustion X) :
    (⋃ n, K n) = Set.univ := by
  exact SourceStack.compactExhaustion_iUnion_eq K

theorem hilbert_compactExhaustion_subset_interior_succ
    (K : CompactExhaustion X) (n : ℕ) :
    K n ⊆ interior (K (n + 1)) := by
  exact SourceStack.compactExhaustion_subset_interior_succ K n

theorem hilbert_compactExhaustion_subset
    (K : CompactExhaustion X) {m n : ℕ} (h : m ≤ n) :
    K m ⊆ K n := by
  exact SourceStack.compactExhaustion_subset K h

theorem hilbert_compactExhaustion_exists_superset_of_isCompact
    (K : CompactExhaustion X) {t : Set X} (ht : IsCompact t) :
    ∃ n, t ⊆ K n := by
  exact SourceStack.compactExhaustion_exists_superset_of_isCompact K ht

theorem hilbert_compactExhaustion_iUnion_interior_eq
    (K : CompactExhaustion X) :
    (⋃ n, interior (K n)) = Set.univ := by
  exact SourceStack.compactExhaustion_iUnion_interior_eq K

theorem hilbert_compactExhaustion_exists_mem_interior
    (K : CompactExhaustion X) (x : X) :
    ∃ n, x ∈ interior (K n) := by
  exact SourceStack.compactExhaustion_exists_mem_interior K x

theorem hilbert_compactExhaustion_exists_subset_interior_of_isCompact
    (K : CompactExhaustion X) {t : Set X} (ht : IsCompact t) :
    ∃ n, t ⊆ interior (K n) := by
  exact SourceStack.compactExhaustion_exists_subset_interior_of_isCompact K ht

theorem hilbert_compactExhaustion_interior_isOpen
    (K : CompactExhaustion X) (n : ℕ) :
    IsOpen (interior (K n)) := by
  exact SourceStack.compactExhaustion_interior_isOpen K n

theorem hilbert_compactExhaustion_closure_interior_isCompact
    [T2Space X] (K : CompactExhaustion X) (n : ℕ) :
    IsCompact (closure (interior (K n))) := by
  exact SourceStack.compactExhaustion_closure_interior_isCompact K n

theorem hilbert_locallyCompact_exists_compact_subset
    [LocallyCompactSpace X] {x : X} {U : Set X}
    (hU : IsOpen U) (hx : x ∈ U) :
    ∃ K : Set X, IsCompact K ∧ x ∈ interior K ∧ K ⊆ U := by
  exact SourceStack.locallyCompact_exists_compact_subset hU hx

theorem hilbert_properMap_preimage_compact
    {K : Set Y} (hf : IsProperMap f) (hK : IsCompact K) :
    IsCompact (f ⁻¹' K) := by
  exact SourceStack.properMap_preimage_compact hf hK

theorem hilbert_properMap_isClosedMap
    (hf : IsProperMap f) :
    IsClosedMap f := by
  exact SourceStack.properMap_isClosedMap hf

theorem hilbert_properMap_comp
    {Z : Type*} [TopologicalSpace Z] {g : Y → Z}
    (hf : IsProperMap f) (hg : IsProperMap g) :
    IsProperMap (g ∘ f) := by
  exact SourceStack.properMap_comp hf hg

theorem hilbert_closedEmbedding_isProperMap
    (hf : Topology.IsClosedEmbedding f) :
    IsProperMap f := by
  exact SourceStack.closedEmbedding_isProperMap hf

theorem hilbert_continuous_isProperMap_of_compactSpace
    [CompactSpace X] [T2Space Y]
    (hf : Continuous f) :
    IsProperMap f := by
  exact SourceStack.continuous_isProperMap_of_compactSpace hf

end Topology

section BelyiCovers

open SourceStack

variable {X P Φ κ : Type*} [TopologicalSpace X] [TopologicalSpace P]
variable (D : BelyiCoverData X P Φ)

theorem hilbert_tupleAvoidSet_isOpen
    [Finite κ] [T1Space P] (φ : Φ) :
    IsOpen (D.tupleAvoidSet (κ := κ) φ) := by
  exact SourceStack.BelyiCoverData.tupleAvoidSet_isOpen D φ

theorem hilbert_tupleAvoidSet_cover_of_pointwise
    [Finite κ]
    (hcover : ∀ x : κ → X, ∃ φ : Φ, x ∈ D.tupleAvoidSet (κ := κ) φ) :
    (Set.univ : Set (κ → X)) ⊆ ⋃ φ : Φ, D.tupleAvoidSet (κ := κ) φ := by
  exact SourceStack.BelyiCoverData.tupleAvoidSet_cover_of_pointwise D hcover

theorem hilbert_finite_subcover_of_pointwise
    [Finite κ] [T1Space P] [CompactSpace (κ → X)]
    (hcover : ∀ x : κ → X, ∃ φ : Φ, x ∈ D.tupleAvoidSet (κ := κ) φ) :
    ∃ t : Finset Φ,
      (⋃ φ ∈ t, D.tupleAvoidSet (κ := κ) φ) = (Set.univ : Set (κ → X)) := by
  exact SourceStack.BelyiCoverData.finite_subcover_of_pointwise D hcover

theorem hilbert_finite_subcover_of_pointwise_forall
    [Finite κ] [T1Space P] [CompactSpace (κ → X)]
    (hcover : ∀ x : κ → X, ∃ φ : Φ, x ∈ D.tupleAvoidSet (κ := κ) φ) :
    ∃ t : Finset Φ,
      ∀ x : κ → X, ∃ φ ∈ t, x ∈ D.tupleAvoidSet (κ := κ) φ := by
  exact SourceStack.BelyiCoverData.finite_subcover_of_pointwise_forall D hcover

theorem hilbert_complement_tupleAvoidSet_eq
    [Finite κ] (S : Set X) (φ : {φ : Φ // D.sendsSetToBranch S φ}) :
    (D.complementCoverData S).tupleAvoidSet (κ := κ) φ =
      {x : κ → {x : X // x ∉ S} | ∀ i, D.map φ.1 (x i).1 ∉ D.branch} := by
  exact SourceStack.BelyiCoverData.complement_tupleAvoidSet_eq D S φ

theorem hilbert_finite_subcover_on_complement_of_pointwise
    [Finite κ] [T1Space P] {S : Set X} [CompactSpace (κ → {x : X // x ∉ S})]
    (hcover : ∀ x : κ → {x : X // x ∉ S},
      ∃ φ : Φ, D.sendsSetToBranch S φ ∧ ∀ i, D.map φ (x i).1 ∉ D.branch) :
    ∃ t : Finset {φ : Φ // D.sendsSetToBranch S φ},
      (⋃ φ ∈ t, (D.complementCoverData S).tupleAvoidSet (κ := κ) φ) =
        (Set.univ : Set (κ → {x : X // x ∉ S})) := by
  exact SourceStack.BelyiCoverData.finite_subcover_on_complement_of_pointwise D hcover

theorem hilbert_finite_subcover_on_complement_of_pointwise_forall
    [Finite κ] [T1Space P] {S : Set X} [CompactSpace (κ → {x : X // x ∉ S})]
    (hcover : ∀ x : κ → {x : X // x ∉ S},
      ∃ φ : Φ, D.sendsSetToBranch S φ ∧ ∀ i, D.map φ (x i).1 ∉ D.branch) :
    ∃ t : Finset {φ : Φ // D.sendsSetToBranch S φ},
      ∀ x : κ → {x : X // x ∉ S},
        ∃ φ ∈ t, x ∈ (D.complementCoverData S).tupleAvoidSet (κ := κ) φ := by
  exact SourceStack.BelyiCoverData.finite_subcover_on_complement_of_pointwise_forall
    D hcover

theorem hilbert_belyiOpen_isOpen
    [T1Space P] (φ : Φ) :
    IsOpen (D.belyiOpen φ) := by
  exact SourceStack.BelyiCoverData.belyiOpen_isOpen D φ

theorem hilbert_belyiOpen_subset_compl_of_sendsSetToBranch
    {A : Set X} {φ : Φ} (hφA : D.sendsSetToBranch A φ) :
    D.belyiOpen φ ⊆ Aᶜ := by
  exact SourceStack.BelyiCoverData.belyiOpen_subset_compl_of_sendsSetToBranch D hφA

theorem hilbert_mem_belyiOpen_iff
    (φ : Φ) (x : X) :
    x ∈ D.belyiOpen φ ↔ D.map φ x ∉ D.branch := by
  exact SourceStack.BelyiCoverData.mem_belyiOpen_iff D φ x

theorem hilbert_exists_belyiOpen_inside_of_point_avoidance
    [T1Space P] {A : Set X} {x : X}
    (h : ∃ φ : Φ, D.sendsSetToBranch A φ ∧ D.map φ x ∉ D.branch) :
    ∃ φ : Φ, IsOpen (D.belyiOpen φ) ∧ x ∈ D.belyiOpen φ ∧ D.belyiOpen φ ⊆ Aᶜ := by
  exact SourceStack.BelyiCoverData.exists_belyiOpen_inside_of_point_avoidance D h

variable (E : NoncriticalBelyiExistence X P Φ)

theorem hilbert_noncritical_pointwise_cover_complement
    [Finite κ] {S : Set X} (hS : S.Finite)
    (x : κ → {x : X // x ∉ S}) :
    ∃ φ : Φ, E.toBelyiCoverData.sendsSetToBranch S φ ∧
      ∀ i, E.map φ (x i).1 ∉ E.branch := by
  exact SourceStack.NoncriticalBelyiExistence.pointwise_cover_complement E hS x

theorem hilbert_noncritical_finite_subcover_on_complement
    [Finite κ] [T1Space P] {S : Set X} (hS : S.Finite)
    [CompactSpace (κ → {x : X // x ∉ S})] :
    ∃ t : Finset {φ : Φ // E.toBelyiCoverData.sendsSetToBranch S φ},
      (⋃ φ ∈ t, (E.toBelyiCoverData.complementCoverData S).tupleAvoidSet (κ := κ) φ) =
        (Set.univ : Set (κ → {x : X // x ∉ S})) := by
  exact SourceStack.NoncriticalBelyiExistence.finite_subcover_on_complement E hS

theorem hilbert_noncritical_finite_subcover_on_complement_forall
    [Finite κ] [T1Space P] {S : Set X} (hS : S.Finite)
    [CompactSpace (κ → {x : X // x ∉ S})] :
    ∃ t : Finset {φ : Φ // E.toBelyiCoverData.sendsSetToBranch S φ},
      ∀ x : κ → {x : X // x ∉ S},
        ∃ φ ∈ t,
          x ∈ (E.toBelyiCoverData.complementCoverData S).tupleAvoidSet (κ := κ) φ := by
  exact SourceStack.NoncriticalBelyiExistence.finite_subcover_on_complement_forall
    E hS

theorem hilbert_noncritical_exists_belyiOpen_inside_complement
    [T1Space P] {A : Set X} (hA : A.Finite) {x : X} (hxA : x ∉ A) :
    ∃ φ : Φ,
      IsOpen (E.toBelyiCoverData.belyiOpen φ) ∧
        x ∈ E.toBelyiCoverData.belyiOpen φ ∧
          E.toBelyiCoverData.belyiOpen φ ⊆ Aᶜ := by
  exact SourceStack.NoncriticalBelyiExistence.exists_belyiOpen_inside_complement E hA hxA

theorem hilbert_noncritical_exists_belyiOpen_containing_finite_inside_complement
    [T1Space P] {S T : Set X} (hS : S.Finite) (hT : T.Finite)
    (hdis : Disjoint S T) :
    ∃ φ : Φ,
      IsOpen (E.toBelyiCoverData.belyiOpen φ) ∧
        T ⊆ E.toBelyiCoverData.belyiOpen φ ∧
          E.toBelyiCoverData.belyiOpen φ ⊆ Sᶜ := by
  exact SourceStack.NoncriticalBelyiExistence.exists_belyiOpen_containing_finite_inside_complement
    E hS hT hdis

theorem hilbert_noncritical_exists_belyiOpen_inside_open_of_finite_complement
    [T1Space P] {V : Set X} (hV : IsOpen V) (hVcompl : Vᶜ.Finite)
    {x : X} (hxV : x ∈ V) :
    ∃ φ : Φ,
      IsOpen (E.toBelyiCoverData.belyiOpen φ) ∧
        x ∈ E.toBelyiCoverData.belyiOpen φ ∧
          E.toBelyiCoverData.belyiOpen φ ⊆ V := by
  exact SourceStack.NoncriticalBelyiExistence.exists_belyiOpen_inside_open_of_finite_complement
    E hV hVcompl hxV

theorem hilbert_noncritical_exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
    [T1Space P] [SourceStack.NonemptyOpenFiniteComplement X]
    {V : Set X} (hV : IsOpen V) {x : X} (hxV : x ∈ V) :
    ∃ φ : Φ,
      IsOpen (E.toBelyiCoverData.belyiOpen φ) ∧
        x ∈ E.toBelyiCoverData.belyiOpen φ ∧
          E.toBelyiCoverData.belyiOpen φ ⊆ V := by
  exact SourceStack.NoncriticalBelyiExistence.exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
    E hV hxV

theorem hilbert_noncritical_exists_belyiOpen_containing_finite_inside_open_of_finite_complement
    [T1Space P] {V T : Set X} (hV : IsOpen V) (hVcompl : Vᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ V) :
    ∃ φ : Φ,
      IsOpen (E.toBelyiCoverData.belyiOpen φ) ∧
        T ⊆ E.toBelyiCoverData.belyiOpen φ ∧
          E.toBelyiCoverData.belyiOpen φ ⊆ V := by
  exact SourceStack.NoncriticalBelyiExistence.exists_belyiOpen_containing_finite_inside_open_of_finite_complement
    E hV hVcompl hT hTsub

end BelyiCovers

section SchemeBelyi

universe u

variable {X P : Scheme.{u}} {T : SourceStack.SchemeBelyi.BelyiTarget P}
variable (φ : SourceStack.SchemeBelyi.BelyiMap T X)

theorem hilbert_schemeBelyi_isDominant_hom :
    IsDominant φ.hom := by
  exact SourceStack.SchemeBelyi.BelyiMap.isDominant_hom φ

theorem hilbert_schemeBelyi_denseRange_hom :
    DenseRange φ.hom.base := by
  exact SourceStack.SchemeBelyi.BelyiMap.denseRange_hom φ

theorem hilbert_schemeBelyi_isEtale_restrict_branchOpen :
    IsEtale (φ.hom ∣_ T.branchOpen) := by
  exact SourceStack.SchemeBelyi.BelyiMap.isEtale_restrict_branchOpen φ

theorem hilbert_schemeBelyi_belyiOpen_ι_isOpenImmersion :
    IsOpenImmersion φ.belyiOpen.ι := by
  exact SourceStack.SchemeBelyi.BelyiMap.belyiOpen_ι_isOpenImmersion φ

theorem hilbert_schemeBelyi_morphismRestrict_to_branchOpen_ι :
    (φ.hom ∣_ T.branchOpen) ≫ T.branchOpen.ι =
      φ.belyiOpen.ι ≫ φ.hom := by
  exact SourceStack.SchemeBelyi.BelyiMap.morphismRestrict_to_branchOpen_ι φ

variable (ψ : SourceStack.SchemeBelyi.FiniteBelyiMap T X)

theorem hilbert_schemeBelyi_finite_toBelyiMap_hom :
    ψ.toBelyiMap.hom = ψ.hom := by
  exact SourceStack.SchemeBelyi.FiniteBelyiMap.toBelyiMap_hom ψ

theorem hilbert_schemeBelyi_finite_isFinite_hom :
    IsFinite ψ.hom := by
  exact SourceStack.SchemeBelyi.FiniteBelyiMap.isFinite_hom ψ

theorem hilbert_schemeBelyi_finite_isDominant_hom :
    IsDominant ψ.hom := by
  exact SourceStack.SchemeBelyi.FiniteBelyiMap.isDominant_hom ψ

theorem hilbert_schemeBelyi_finite_denseRange_hom :
    DenseRange ψ.hom.base := by
  exact SourceStack.SchemeBelyi.FiniteBelyiMap.denseRange_hom ψ

theorem hilbert_schemeBelyi_finite_isEtale_restrict_branchOpen :
    IsEtale (ψ.hom ∣_ T.branchOpen) := by
  exact SourceStack.SchemeBelyi.FiniteBelyiMap.isEtale_restrict_branchOpen ψ

theorem hilbert_schemeBelyi_finite_isFinite_restrict_branchOpen :
    IsFinite (ψ.hom ∣_ T.branchOpen) := by
  exact SourceStack.SchemeBelyi.FiniteBelyiMap.isFinite_restrict_branchOpen ψ

theorem hilbert_schemeBelyi_finite_isAffineHom_hom :
    IsAffineHom ψ.hom := by
  exact SourceStack.SchemeBelyi.FiniteBelyiMap.isAffineHom_hom ψ

theorem hilbert_schemeBelyi_finite_isSeparated_hom :
    IsSeparated ψ.hom := by
  exact SourceStack.SchemeBelyi.FiniteBelyiMap.isSeparated_hom ψ

theorem hilbert_schemeBelyi_finite_quasiCompact_hom :
    QuasiCompact ψ.hom := by
  exact SourceStack.SchemeBelyi.FiniteBelyiMap.quasiCompact_hom ψ

theorem hilbert_schemeBelyi_finite_belyiOpen_ι_isOpenImmersion :
    IsOpenImmersion ψ.toBelyiMap.belyiOpen.ι := by
  exact SourceStack.SchemeBelyi.FiniteBelyiMap.belyiOpen_ι_isOpenImmersion ψ

theorem hilbert_schemeBelyi_finite_morphismRestrict_to_branchOpen_ι :
    (ψ.hom ∣_ T.branchOpen) ≫ T.branchOpen.ι =
      ψ.toBelyiMap.belyiOpen.ι ≫ ψ.hom := by
  exact SourceStack.SchemeBelyi.FiniteBelyiMap.morphismRestrict_to_branchOpen_ι ψ

theorem hilbert_schemeBelyi_finite_compAux_hom
    {Y : Scheme.{u}} (aux : Y ⟶ X) [IsFinite aux] [IsDominant aux]
    (hEtale : IsEtale ((aux ≫ ψ.hom) ∣_ T.branchOpen)) :
    (ψ.compAux aux hEtale).hom = aux ≫ ψ.hom := by
  exact SourceStack.SchemeBelyi.FiniteBelyiMap.compAux_hom ψ aux hEtale

theorem hilbert_schemeBelyi_finite_compAux_base
    {Y : Scheme.{u}} (aux : Y ⟶ X) [IsFinite aux] [IsDominant aux]
    (hEtale : IsEtale ((aux ≫ ψ.hom) ∣_ T.branchOpen)) (x : Y) :
    (ψ.compAux aux hEtale).hom.base x = ψ.hom.base (aux.base x) := by
  exact SourceStack.SchemeBelyi.FiniteBelyiMap.compAux_base ψ aux hEtale x

theorem hilbert_schemeBelyi_finite_compAux_isFinite_hom
    {Y : Scheme.{u}} (aux : Y ⟶ X) [IsFinite aux] [IsDominant aux]
    (hEtale : IsEtale ((aux ≫ ψ.hom) ∣_ T.branchOpen)) :
    IsFinite (ψ.compAux aux hEtale).hom := by
  exact SourceStack.SchemeBelyi.FiniteBelyiMap.compAux_isFinite_hom ψ aux hEtale

theorem hilbert_schemeBelyi_finite_compAux_isDominant_hom
    {Y : Scheme.{u}} (aux : Y ⟶ X) [IsFinite aux] [IsDominant aux]
    (hEtale : IsEtale ((aux ≫ ψ.hom) ∣_ T.branchOpen)) :
    IsDominant (ψ.compAux aux hEtale).hom := by
  exact SourceStack.SchemeBelyi.FiniteBelyiMap.compAux_isDominant_hom ψ aux hEtale

theorem hilbert_schemeBelyi_finite_compAux_etale_of_aux_restrict
    {Y : Scheme.{u}} (aux : Y ⟶ X) [IsFinite aux] [IsDominant aux]
    (hAuxEtale : IsEtale (aux ∣_ ψ.toBelyiMap.belyiOpen)) :
    IsEtale ((aux ≫ ψ.hom) ∣_ T.branchOpen) := by
  exact SourceStack.SchemeBelyi.FiniteBelyiMap.compAux_etale_of_aux_restrict
    ψ aux hAuxEtale

theorem hilbert_schemeBelyi_finite_compAuxOfAuxEtale_hom
    {Y : Scheme.{u}} (aux : Y ⟶ X) [IsFinite aux] [IsDominant aux]
    (hAuxEtale : IsEtale (aux ∣_ ψ.toBelyiMap.belyiOpen)) :
    (ψ.compAuxOfAuxEtale aux hAuxEtale).hom = aux ≫ ψ.hom := by
  exact SourceStack.SchemeBelyi.FiniteBelyiMap.compAuxOfAuxEtale_hom
    ψ aux hAuxEtale

theorem hilbert_schemeBelyi_finite_compAuxOfAuxEtale_base
    {Y : Scheme.{u}} (aux : Y ⟶ X) [IsFinite aux] [IsDominant aux]
    (hAuxEtale : IsEtale (aux ∣_ ψ.toBelyiMap.belyiOpen)) (x : Y) :
    (ψ.compAuxOfAuxEtale aux hAuxEtale).hom.base x = ψ.hom.base (aux.base x) := by
  exact SourceStack.SchemeBelyi.FiniteBelyiMap.compAuxOfAuxEtale_base
    ψ aux hAuxEtale x

section MarkedProjectiveLineTarget

open SourceStack.SchemeProjectiveLine

variable (K : Type u) [CommRing K] [IsDomain K]

theorem hilbert_schemeBelyi_markedSchemePointSet_compl_isOpen
    [T1Space (P1 K)] :
    IsOpen (markedSchemePointSet K)ᶜ := by
  exact SourceStack.SchemeBelyi.markedSchemePointSet_compl_isOpen K

theorem hilbert_schemeBelyi_markedBranchOpen_carrier
    (hmarkedOpen : IsOpen (markedSchemePointSet K)ᶜ) :
    (SourceStack.SchemeBelyi.markedBranchOpen K hmarkedOpen : Set (P1 K)) =
      (markedSchemePointSet K)ᶜ := by
  exact SourceStack.SchemeBelyi.markedBranchOpen_carrier K hmarkedOpen

theorem hilbert_schemeBelyi_mem_markedBranchOpen_iff
    (hmarkedOpen : IsOpen (markedSchemePointSet K)ᶜ) (p : P1 K) :
    p ∈ SourceStack.SchemeBelyi.markedBranchOpen K hmarkedOpen ↔
      p ∉ markedSchemePointSet K := by
  exact SourceStack.SchemeBelyi.mem_markedBranchOpen_iff K hmarkedOpen p

theorem hilbert_schemeBelyi_markedBelyiTarget_branchOpen
    (hmarkedOpen : IsOpen (markedSchemePointSet K)ᶜ) :
    (SourceStack.SchemeBelyi.markedBelyiTarget K hmarkedOpen).branchOpen =
      SourceStack.SchemeBelyi.markedBranchOpen K hmarkedOpen := by
  exact SourceStack.SchemeBelyi.markedBelyiTarget_branchOpen K hmarkedOpen

theorem hilbert_schemeBelyi_markedBelyiTargetOfT1_branchOpen
    [T1Space (P1 K)] :
    (SourceStack.SchemeBelyi.markedBelyiTargetOfT1 K).branchOpen =
      SourceStack.SchemeBelyi.markedBranchOpen K
        (SourceStack.SchemeBelyi.markedSchemePointSet_compl_isOpen K) := by
  exact SourceStack.SchemeBelyi.markedBelyiTargetOfT1_branchOpen K

variable {X : Scheme.{u}}
variable {hmarkedOpen : IsOpen (markedSchemePointSet K)ᶜ}
variable (φmarked :
  SourceStack.SchemeBelyi.BelyiMap
    (SourceStack.SchemeBelyi.markedBelyiTarget K hmarkedOpen) X)

theorem hilbert_schemeBelyi_mem_marked_belyiOpen_iff
    (x : X) :
    x ∈ φmarked.belyiOpen ↔
      φmarked.hom.base x ∉ markedSchemePointSet K := by
  exact SourceStack.SchemeBelyi.BelyiMap.mem_marked_belyiOpen_iff φmarked x

theorem hilbert_schemeBelyi_marked_belyiOpen_carrier :
    (φmarked.belyiOpen : Set X) =
      {x : X | φmarked.hom.base x ∉ markedSchemePointSet K} := by
  exact SourceStack.SchemeBelyi.BelyiMap.marked_belyiOpen_carrier φmarked

variable (ψmarked :
  SourceStack.SchemeBelyi.FiniteBelyiMap
    (SourceStack.SchemeBelyi.markedBelyiTarget K hmarkedOpen) X)

theorem hilbert_schemeBelyi_finite_mem_marked_belyiOpen_iff
    (x : X) :
    x ∈ ψmarked.toBelyiMap.belyiOpen ↔
      ψmarked.hom.base x ∉ markedSchemePointSet K := by
  exact SourceStack.SchemeBelyi.FiniteBelyiMap.mem_marked_belyiOpen_iff ψmarked x

theorem hilbert_schemeBelyi_finite_marked_belyiOpen_carrier :
    (ψmarked.toBelyiMap.belyiOpen : Set X) =
      {x : X | ψmarked.hom.base x ∉ markedSchemePointSet K} := by
  exact SourceStack.SchemeBelyi.FiniteBelyiMap.marked_belyiOpen_carrier ψmarked

end MarkedProjectiveLineTarget

end SchemeBelyi

namespace LocalFields

theorem hilbert_padicInt_compactSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    CompactSpace ℤ_[p] := by
  exact SourceStack.LocalFields.padicInt_compactSpace p

theorem hilbert_padic_properSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    ProperSpace ℚ_[p] := by
  exact SourceStack.LocalFields.padic_properSpace p

theorem hilbert_padic_locallyCompactSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    LocallyCompactSpace ℚ_[p] := by
  exact SourceStack.LocalFields.padic_locallyCompactSpace p

theorem hilbert_padic_completeSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    CompleteSpace ℚ_[p] := by
  exact SourceStack.LocalFields.padic_completeSpace p

theorem hilbert_padic_secondCountableTopology
    (p : ℕ) [Fact (Nat.Prime p)] :
    SecondCountableTopology ℚ_[p] := by
  exact SourceStack.LocalFields.padic_secondCountableTopology p

theorem hilbert_padic_sigmaCompactSpace
    (p : ℕ) [Fact (Nat.Prime p)] :
    SigmaCompactSpace ℚ_[p] := by
  exact SourceStack.LocalFields.padic_sigmaCompactSpace p

theorem hilbert_padic_compactExhaustion_exists
    (p : ℕ) [Fact (Nat.Prime p)] :
    Nonempty (CompactExhaustion ℚ_[p]) := by
  exact SourceStack.LocalFields.padic_compactExhaustion_exists p

theorem hilbert_infinitePlace_completion_locallyCompactSpace
    {K : Type*} [Field K] (v : NumberField.InfinitePlace K) :
    LocallyCompactSpace v.Completion := by
  exact SourceStack.LocalFields.infinitePlace_completion_locallyCompactSpace v

theorem hilbert_infinitePlace_completion_isometry_extensionEmbedding
    {K : Type*} [Field K] (v : NumberField.InfinitePlace K) :
    Isometry (NumberField.InfinitePlace.Completion.extensionEmbedding v) := by
  exact SourceStack.LocalFields.infinitePlace_completion_isometry_extensionEmbedding v

theorem hilbert_infinitePlace_completion_isClosed_image_extensionEmbedding
    {K : Type*} [Field K] (v : NumberField.InfinitePlace K) :
    IsClosed (Set.range (NumberField.InfinitePlace.Completion.extensionEmbedding v)) := by
  exact SourceStack.LocalFields.infinitePlace_completion_isClosed_image_extensionEmbedding v

theorem hilbert_infinitePlace_completion_secondCountableTopology
    {K : Type*} [Field K] (v : NumberField.InfinitePlace K) :
    SecondCountableTopology v.Completion := by
  exact SourceStack.LocalFields.infinitePlace_completion_secondCountableTopology v

theorem hilbert_infinitePlace_completion_sigmaCompactSpace
    {K : Type*} [Field K] (v : NumberField.InfinitePlace K) :
    SigmaCompactSpace v.Completion := by
  exact SourceStack.LocalFields.infinitePlace_completion_sigmaCompactSpace v

theorem hilbert_infinitePlace_completion_compactExhaustion_exists
    {K : Type*} [Field K] (v : NumberField.InfinitePlace K) :
    Nonempty (CompactExhaustion v.Completion) := by
  exact SourceStack.LocalFields.infinitePlace_completion_compactExhaustion_exists v

theorem hilbert_infinitePlace_completion_isometryEquivComplex_exists
    {K : Type*} [Field K] {v : NumberField.InfinitePlace K}
    (hv : NumberField.InfinitePlace.IsComplex v) :
    Nonempty (v.Completion ≃ᵢ ℂ) := by
  exact SourceStack.LocalFields.infinitePlace_completion_isometryEquivComplex_exists hv

theorem hilbert_infinitePlace_completion_isometryEquivReal_exists
    {K : Type*} [Field K] {v : NumberField.InfinitePlace K}
    (hv : NumberField.InfinitePlace.IsReal v) :
    Nonempty (v.Completion ≃ᵢ ℝ) := by
  exact SourceStack.LocalFields.infinitePlace_completion_isometryEquivReal_exists hv

end LocalFields

namespace ProjectiveLine

variable (K : Type*) [DivisionRing K]

theorem hilbert_zero_ne_infinity :
    SourceStack.ProjectiveLine.zero K ≠ SourceStack.ProjectiveLine.infinity K := by
  exact SourceStack.ProjectiveLine.zero_ne_infinity K

theorem hilbert_zero_ne_one :
    SourceStack.ProjectiveLine.zero K ≠ SourceStack.ProjectiveLine.one K := by
  exact SourceStack.ProjectiveLine.zero_ne_one K

theorem hilbert_one_ne_infinity :
    SourceStack.ProjectiveLine.one K ≠ SourceStack.ProjectiveLine.infinity K := by
  exact SourceStack.ProjectiveLine.one_ne_infinity K

theorem hilbert_affinePoint_zero :
    SourceStack.ProjectiveLine.affinePoint K 0 = SourceStack.ProjectiveLine.zero K := by
  exact SourceStack.ProjectiveLine.affinePoint_zero K

theorem hilbert_affinePoint_one :
    SourceStack.ProjectiveLine.affinePoint K 1 = SourceStack.ProjectiveLine.one K := by
  exact SourceStack.ProjectiveLine.affinePoint_one K

theorem hilbert_affinePoint_ne_infinity (r : K) :
    SourceStack.ProjectiveLine.affinePoint K r ≠
      SourceStack.ProjectiveLine.infinity K := by
  exact SourceStack.ProjectiveLine.affinePoint_ne_infinity K r

theorem hilbert_affinePoint_ne_zero {r : K} (hr : r ≠ 0) :
    SourceStack.ProjectiveLine.affinePoint K r ≠
      SourceStack.ProjectiveLine.zero K := by
  exact SourceStack.ProjectiveLine.affinePoint_ne_zero K hr

theorem hilbert_affinePoint_ne_one {r : K} (hr : r ≠ 1) :
    SourceStack.ProjectiveLine.affinePoint K r ≠
      SourceStack.ProjectiveLine.one K := by
  exact SourceStack.ProjectiveLine.affinePoint_ne_one K hr

theorem hilbert_affinePoint_injective :
    Function.Injective (SourceStack.ProjectiveLine.affinePoint K) := by
  exact SourceStack.ProjectiveLine.affinePoint_injective K

theorem hilbert_point_eq_affine_or_infinity
    (p : SourceStack.ProjectiveLine.P1 K) :
    (∃ r : K, p = SourceStack.ProjectiveLine.affinePoint K r) ∨
      p = SourceStack.ProjectiveLine.infinity K := by
  exact SourceStack.ProjectiveLine.point_eq_affine_or_infinity K p

section FractionalLinear

variable (F : Type*) [Field F]

theorem hilbert_reciprocalTranslate_affinePoint_of_ne
    (lambda r : F) (hr : r ≠ lambda) :
    SourceStack.ProjectiveLine.reciprocalTranslate F lambda
        (SourceStack.ProjectiveLine.affinePoint F r) =
      SourceStack.ProjectiveLine.affinePoint F ((r - lambda)⁻¹) := by
  exact SourceStack.ProjectiveLine.reciprocalTranslate_affinePoint_of_ne F lambda r hr

theorem hilbert_reciprocalTranslate_injective
    (lambda : F) :
    Function.Injective (SourceStack.ProjectiveLine.reciprocalTranslate F lambda) := by
  exact SourceStack.ProjectiveLine.reciprocalTranslate_injective F lambda

theorem hilbert_reciprocalTranslate_affinePoint_pole
    (lambda : F) :
    SourceStack.ProjectiveLine.reciprocalTranslate F lambda
        (SourceStack.ProjectiveLine.affinePoint F lambda) =
      SourceStack.ProjectiveLine.infinity F := by
  exact SourceStack.ProjectiveLine.reciprocalTranslate_affinePoint_pole F lambda

theorem hilbert_reciprocalTranslate_infinity
    (lambda : F) :
    SourceStack.ProjectiveLine.reciprocalTranslate F lambda
      (SourceStack.ProjectiveLine.infinity F) =
        SourceStack.ProjectiveLine.zero F := by
  exact SourceStack.ProjectiveLine.reciprocalTranslate_infinity F lambda

theorem hilbert_reciprocalTranslate_affinePoint_ne_infinity
    (lambda r : F) (hr : r ≠ lambda) :
    SourceStack.ProjectiveLine.reciprocalTranslate F lambda
        (SourceStack.ProjectiveLine.affinePoint F r) ≠
      SourceStack.ProjectiveLine.infinity F := by
  exact SourceStack.ProjectiveLine.reciprocalTranslate_affinePoint_ne_infinity F lambda r hr

theorem hilbert_reciprocalTranslate_affinePoint_ne_zero
    (lambda r : F) (hr : r ≠ lambda) :
    SourceStack.ProjectiveLine.reciprocalTranslate F lambda
        (SourceStack.ProjectiveLine.affinePoint F r) ≠
      SourceStack.ProjectiveLine.zero F := by
  exact SourceStack.ProjectiveLine.reciprocalTranslate_affinePoint_ne_zero F lambda r hr

theorem hilbert_affineLinearMap_affinePoint
    {a b : F} (ha : a ≠ 0) (r : F) :
    SourceStack.ProjectiveLine.affineLinearMap F a b ha
        (SourceStack.ProjectiveLine.affinePoint F r) =
      SourceStack.ProjectiveLine.affinePoint F (a * r + b) := by
  exact SourceStack.ProjectiveLine.affineLinearMap_affinePoint F ha r

theorem hilbert_affineLinearMap_injective
    {a b : F} (ha : a ≠ 0) :
    Function.Injective (SourceStack.ProjectiveLine.affineLinearMap F a b ha) := by
  exact SourceStack.ProjectiveLine.affineLinearMap_injective F ha

theorem hilbert_affineLinearMap_infinity
    {a b : F} (ha : a ≠ 0) :
    SourceStack.ProjectiveLine.affineLinearMap F a b ha
        (SourceStack.ProjectiveLine.infinity F) =
      SourceStack.ProjectiveLine.infinity F := by
  exact SourceStack.ProjectiveLine.affineLinearMap_infinity F ha

end FractionalLinear

theorem hilbert_zero_mem_branchFinset :
    SourceStack.ProjectiveLine.zero K ∈ SourceStack.ProjectiveLine.branchFinset K := by
  exact SourceStack.ProjectiveLine.zero_mem_branchFinset K

theorem hilbert_one_mem_branchFinset :
    SourceStack.ProjectiveLine.one K ∈ SourceStack.ProjectiveLine.branchFinset K := by
  exact SourceStack.ProjectiveLine.one_mem_branchFinset K

theorem hilbert_infinity_mem_branchFinset :
    SourceStack.ProjectiveLine.infinity K ∈ SourceStack.ProjectiveLine.branchFinset K := by
  exact SourceStack.ProjectiveLine.infinity_mem_branchFinset K

theorem hilbert_branchFinset_card :
    (SourceStack.ProjectiveLine.branchFinset K).card = 3 := by
  exact SourceStack.ProjectiveLine.branchFinset_card K

theorem hilbert_branchSet_finite :
    (SourceStack.ProjectiveLine.branchSet K).Finite := by
  exact SourceStack.ProjectiveLine.branchSet_finite K

theorem hilbert_mem_branchSet_iff (p : SourceStack.ProjectiveLine.P1 K) :
    p ∈ SourceStack.ProjectiveLine.branchSet K ↔
      p ∈ SourceStack.ProjectiveLine.branchFinset K := by
  exact SourceStack.ProjectiveLine.mem_branchSet_iff K p

theorem hilbert_affinePoint_mem_branchFinset_iff (r : K) :
    SourceStack.ProjectiveLine.affinePoint K r ∈
        SourceStack.ProjectiveLine.branchFinset K ↔
      r = 0 ∨ r = 1 := by
  exact SourceStack.ProjectiveLine.affinePoint_mem_branchFinset_iff K r

theorem hilbert_affinePoint_mem_branchSet_iff (r : K) :
    SourceStack.ProjectiveLine.affinePoint K r ∈
        SourceStack.ProjectiveLine.branchSet K ↔
      r = 0 ∨ r = 1 := by
  exact SourceStack.ProjectiveLine.affinePoint_mem_branchSet_iff K r

theorem hilbert_zero_mem_fourPointFinset (r : K) :
    SourceStack.ProjectiveLine.zero K ∈
      SourceStack.ProjectiveLine.fourPointFinset K r := by
  exact SourceStack.ProjectiveLine.zero_mem_fourPointFinset K r

theorem hilbert_affinePoint_mem_fourPointFinset (r : K) :
    SourceStack.ProjectiveLine.affinePoint K r ∈
      SourceStack.ProjectiveLine.fourPointFinset K r := by
  exact SourceStack.ProjectiveLine.affinePoint_mem_fourPointFinset K r

theorem hilbert_one_mem_fourPointFinset (r : K) :
    SourceStack.ProjectiveLine.one K ∈
      SourceStack.ProjectiveLine.fourPointFinset K r := by
  exact SourceStack.ProjectiveLine.one_mem_fourPointFinset K r

theorem hilbert_infinity_mem_fourPointFinset (r : K) :
    SourceStack.ProjectiveLine.infinity K ∈
      SourceStack.ProjectiveLine.fourPointFinset K r := by
  exact SourceStack.ProjectiveLine.infinity_mem_fourPointFinset K r

theorem hilbert_fourPointSet_finite (r : K) :
    (SourceStack.ProjectiveLine.fourPointSet K r).Finite := by
  exact SourceStack.ProjectiveLine.fourPointSet_finite K r

theorem hilbert_mem_fourPointSet_iff
    (r : K) (p : SourceStack.ProjectiveLine.P1 K) :
    p ∈ SourceStack.ProjectiveLine.fourPointSet K r ↔
      p ∈ SourceStack.ProjectiveLine.fourPointFinset K r := by
  exact SourceStack.ProjectiveLine.mem_fourPointSet_iff K r p

theorem hilbert_affinePoint_mem_fourPointFinset_iff (r x : K) :
    SourceStack.ProjectiveLine.affinePoint K x ∈
        SourceStack.ProjectiveLine.fourPointFinset K r ↔
      x = 0 ∨ x = r ∨ x = 1 := by
  exact SourceStack.ProjectiveLine.affinePoint_mem_fourPointFinset_iff K r x

theorem hilbert_affinePoint_mem_fourPointSet_iff (r x : K) :
    SourceStack.ProjectiveLine.affinePoint K x ∈
        SourceStack.ProjectiveLine.fourPointSet K r ↔
      x = 0 ∨ x = r ∨ x = 1 := by
  exact SourceStack.ProjectiveLine.affinePoint_mem_fourPointSet_iff K r x

theorem hilbert_fourPointFinset_card {r : K} (hr0 : r ≠ 0) (hr1 : r ≠ 1) :
    (SourceStack.ProjectiveLine.fourPointFinset K r).card = 4 := by
  exact SourceStack.ProjectiveLine.fourPointFinset_card K hr0 hr1

theorem hilbert_image_fourPointFinset_card_lt_of_maps_to_branch
    [DecidableEq (SourceStack.ProjectiveLine.P1 K)]
    {r : K} (hr0 : r ≠ 0) (hr1 : r ≠ 1)
    (f : SourceStack.ProjectiveLine.P1 K → SourceStack.ProjectiveLine.P1 K)
    (hmap : ∀ x ∈ SourceStack.ProjectiveLine.fourPointFinset K r,
      f x ∈ SourceStack.ProjectiveLine.branchFinset K) :
    ((SourceStack.ProjectiveLine.fourPointFinset K r).image f).card <
      (SourceStack.ProjectiveLine.fourPointFinset K r).card := by
  exact SourceStack.ProjectiveLine.image_fourPointFinset_card_lt_of_maps_to_branch
    K hr0 hr1 f hmap

theorem hilbert_exists_distinct_same_image_fourPoint_of_maps_to_branch
    {r : K} (hr0 : r ≠ 0) (hr1 : r ≠ 1)
    (f : SourceStack.ProjectiveLine.P1 K → SourceStack.ProjectiveLine.P1 K)
    (hmap : ∀ x ∈ SourceStack.ProjectiveLine.fourPointFinset K r,
      f x ∈ SourceStack.ProjectiveLine.branchFinset K) :
    ∃ x ∈ SourceStack.ProjectiveLine.fourPointFinset K r,
      ∃ y ∈ SourceStack.ProjectiveLine.fourPointFinset K r,
        x ≠ y ∧ f x = f y := by
  exact SourceStack.ProjectiveLine.exists_distinct_same_image_fourPoint_of_maps_to_branch
    K hr0 hr1 f hmap

theorem hilbert_image_card_lt_of_fourPoint_subset_maps_to_branch
    [DecidableEq (SourceStack.ProjectiveLine.P1 K)]
    {r : K} (hr0 : r ≠ 0) (hr1 : r ≠ 1)
    (S : Finset (SourceStack.ProjectiveLine.P1 K))
    (f : SourceStack.ProjectiveLine.P1 K → SourceStack.ProjectiveLine.P1 K)
    (hsubset : SourceStack.ProjectiveLine.fourPointFinset K r ⊆ S)
    (hmap : ∀ x ∈ S, f x ∈ SourceStack.ProjectiveLine.branchFinset K) :
    (S.image f).card < S.card := by
  exact SourceStack.ProjectiveLine.image_card_lt_of_fourPoint_subset_maps_to_branch
    K hr0 hr1 S f hsubset hmap

end ProjectiveLine

namespace ProjectiveSpectrum

universe u v

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

theorem hilbert_basicOpen_mem_iff
    (f : A) (x : Proj 𝒜) :
    x ∈ Proj.basicOpen 𝒜 f ↔ f ∉ x.asHomogeneousIdeal := by
  exact SourceStack.ProjectiveSpectrum.basicOpen_mem_iff 𝒜 f x

theorem hilbert_basicOpen_one_eq_top :
    Proj.basicOpen 𝒜 (1 : A) = ⊤ := by
  exact SourceStack.ProjectiveSpectrum.basicOpen_one_eq_top 𝒜

theorem hilbert_basicOpen_zero_eq_bot :
    Proj.basicOpen 𝒜 (0 : A) = ⊥ := by
  exact SourceStack.ProjectiveSpectrum.basicOpen_zero_eq_bot 𝒜

theorem hilbert_basicOpen_pow_eq
    (f : A) (n : ℕ) (hn : 0 < n) :
    Proj.basicOpen 𝒜 (f ^ n) = Proj.basicOpen 𝒜 f := by
  exact SourceStack.ProjectiveSpectrum.basicOpen_pow_eq 𝒜 f n hn

theorem hilbert_basicOpen_mul_eq_inf
    (f g : A) :
    Proj.basicOpen 𝒜 (f * g) =
      Proj.basicOpen 𝒜 f ⊓ Proj.basicOpen 𝒜 g := by
  exact SourceStack.ProjectiveSpectrum.basicOpen_mul_eq_inf 𝒜 f g

theorem hilbert_basicOpen_mono_of_dvd
    {f g : A} (hfg : f ∣ g) :
    Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f := by
  exact SourceStack.ProjectiveSpectrum.basicOpen_mono_of_dvd 𝒜 hfg

theorem hilbert_zeroLocus_mem_iff
    (s : Set A) (x : _root_.ProjectiveSpectrum 𝒜) :
    x ∈ _root_.ProjectiveSpectrum.zeroLocus 𝒜 s ↔
      s ⊆ x.asHomogeneousIdeal := by
  exact SourceStack.ProjectiveSpectrum.zeroLocus_mem_iff 𝒜 s x

theorem hilbert_isClosed_zeroLocus
    (s : Set A) :
    IsClosed (_root_.ProjectiveSpectrum.zeroLocus 𝒜 s) := by
  exact SourceStack.ProjectiveSpectrum.isClosed_zeroLocus 𝒜 s

theorem hilbert_zeroLocus_singleton_zero :
    _root_.ProjectiveSpectrum.zeroLocus 𝒜 ({0} : Set A) = Set.univ := by
  exact SourceStack.ProjectiveSpectrum.zeroLocus_singleton_zero 𝒜

theorem hilbert_zeroLocus_singleton_one :
    _root_.ProjectiveSpectrum.zeroLocus 𝒜 ({1} : Set A) = ∅ := by
  exact SourceStack.ProjectiveSpectrum.zeroLocus_singleton_one 𝒜

theorem hilbert_zeroLocus_union
    (s t : Set A) :
    _root_.ProjectiveSpectrum.zeroLocus 𝒜 (s ∪ t) =
      _root_.ProjectiveSpectrum.zeroLocus 𝒜 s ∩
        _root_.ProjectiveSpectrum.zeroLocus 𝒜 t := by
  exact SourceStack.ProjectiveSpectrum.zeroLocus_union 𝒜 s t

theorem hilbert_zeroLocus_singleton_mul
    (f g : A) :
    _root_.ProjectiveSpectrum.zeroLocus 𝒜 ({f * g} : Set A) =
      _root_.ProjectiveSpectrum.zeroLocus 𝒜 {f} ∪
        _root_.ProjectiveSpectrum.zeroLocus 𝒜 {g} := by
  exact SourceStack.ProjectiveSpectrum.zeroLocus_singleton_mul 𝒜 f g

theorem hilbert_zeroLocus_singleton_pow
    (f : A) (n : ℕ) (hn : 0 < n) :
    _root_.ProjectiveSpectrum.zeroLocus 𝒜 ({f ^ n} : Set A) =
      _root_.ProjectiveSpectrum.zeroLocus 𝒜 {f} := by
  exact SourceStack.ProjectiveSpectrum.zeroLocus_singleton_pow 𝒜 f n hn

theorem hilbert_mem_vanishingIdeal_iff
    (t : Set (_root_.ProjectiveSpectrum 𝒜)) (f : A) :
    f ∈ _root_.ProjectiveSpectrum.vanishingIdeal t ↔
      ∀ x ∈ t, f ∈ x.asHomogeneousIdeal := by
  exact SourceStack.ProjectiveSpectrum.mem_vanishingIdeal_iff 𝒜 t f

theorem hilbert_vanishingIdeal_singleton
    (x : _root_.ProjectiveSpectrum 𝒜) :
    _root_.ProjectiveSpectrum.vanishingIdeal {x} = x.asHomogeneousIdeal := by
  exact SourceStack.ProjectiveSpectrum.vanishingIdeal_singleton 𝒜 x

theorem hilbert_subset_zeroLocus_iff_subset_vanishingIdeal
    (t : Set (_root_.ProjectiveSpectrum 𝒜)) (s : Set A) :
    t ⊆ _root_.ProjectiveSpectrum.zeroLocus 𝒜 s ↔
      s ⊆ _root_.ProjectiveSpectrum.vanishingIdeal t := by
  exact SourceStack.ProjectiveSpectrum.subset_zeroLocus_iff_subset_vanishingIdeal 𝒜 t s

theorem hilbert_topological_basicOpen_eq_zeroLocus_compl
    (r : A) :
    (_root_.ProjectiveSpectrum.basicOpen 𝒜 r :
      Set (_root_.ProjectiveSpectrum 𝒜)) =
        (_root_.ProjectiveSpectrum.zeroLocus 𝒜 {r})ᶜ := by
  exact SourceStack.ProjectiveSpectrum.topological_basicOpen_eq_zeroLocus_compl 𝒜 r

theorem hilbert_isOpen_topological_basicOpen
    {a : A} :
    IsOpen (_root_.ProjectiveSpectrum.basicOpen 𝒜 a :
      Set (_root_.ProjectiveSpectrum 𝒜)) := by
  exact SourceStack.ProjectiveSpectrum.isOpen_topological_basicOpen 𝒜

theorem hilbert_mem_compl_zeroLocus_iff_not_mem
    {f : A} {I : _root_.ProjectiveSpectrum 𝒜} :
    I ∈ (_root_.ProjectiveSpectrum.zeroLocus 𝒜 {f})ᶜ ↔
      f ∉ I.asHomogeneousIdeal := by
  exact SourceStack.ProjectiveSpectrum.mem_compl_zeroLocus_iff_not_mem 𝒜

theorem hilbert_le_iff_mem_closure
    (x y : _root_.ProjectiveSpectrum 𝒜) :
    x ≤ y ↔ y ∈ closure {x} := by
  exact SourceStack.ProjectiveSpectrum.le_iff_mem_closure 𝒜 x y

theorem hilbert_basicOpen_eq_iSup_proj
    (f : A) :
    Proj.basicOpen 𝒜 f =
      ⨆ i : ℕ, Proj.basicOpen 𝒜 (GradedAlgebra.proj 𝒜 i f) := by
  exact SourceStack.ProjectiveSpectrum.basicOpen_eq_iSup_proj 𝒜 f

theorem hilbert_isBasis_basicOpen :
    TopologicalSpace.Opens.IsBasis (Set.range (Proj.basicOpen 𝒜)) := by
  exact SourceStack.ProjectiveSpectrum.isBasis_basicOpen 𝒜

theorem hilbert_iSup_basicOpen_eq_top
    {ι : Type*} (f : ι → A)
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ Ideal.span (Set.range f)) :
    ⨆ i, Proj.basicOpen 𝒜 (f i) = ⊤ := by
  exact SourceStack.ProjectiveSpectrum.iSup_basicOpen_eq_top 𝒜 f hf

theorem hilbert_toSpecZero_isSeparated :
    IsSeparated (Proj.toSpecZero 𝒜) := by
  exact SourceStack.ProjectiveSpectrum.toSpecZero_isSeparated 𝒜

theorem hilbert_proj_scheme_isSeparated :
    (Proj 𝒜).IsSeparated := by
  exact SourceStack.ProjectiveSpectrum.proj_scheme_isSeparated 𝒜

theorem hilbert_awayι_isOpenImmersion
    (f : A) {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    IsOpenImmersion (Proj.awayι 𝒜 f f_deg hm) := by
  exact SourceStack.ProjectiveSpectrum.awayι_isOpenImmersion 𝒜 f f_deg hm

theorem hilbert_opensRange_awayι
    (f : A) {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    (Proj.awayι 𝒜 f f_deg hm).opensRange = Proj.basicOpen 𝒜 f := by
  exact SourceStack.ProjectiveSpectrum.opensRange_awayι 𝒜 f f_deg hm

theorem hilbert_isAffineOpen_basicOpen
    (f : A) {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    IsAffineOpen (Proj.basicOpen 𝒜 f) := by
  exact SourceStack.ProjectiveSpectrum.isAffineOpen_basicOpen 𝒜 f f_deg hm

theorem hilbert_stalkIso_exists
    (x : Proj 𝒜) :
    Nonempty ((Proj 𝒜).presheaf.stalk x ≅
      CommRingCat.of (AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal)) := by
  exact SourceStack.ProjectiveSpectrum.stalkIso_exists 𝒜 x

theorem hilbert_basicOpenIsoSpec_exists
    (f : A) {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    Nonempty ((Proj.basicOpen 𝒜 f).toScheme ≅ Spec (.of (Away 𝒜 f))) := by
  exact SourceStack.ProjectiveSpectrum.basicOpenIsoSpec_exists 𝒜 f f_deg hm

theorem hilbert_basicOpenIsoAway_exists
    (f : A) {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    Nonempty (CommRingCat.of (Away 𝒜 f) ≅ Γ(Proj 𝒜, Proj.basicOpen 𝒜 f)) := by
  exact SourceStack.ProjectiveSpectrum.basicOpenIsoAway_exists 𝒜 f f_deg hm

theorem hilbert_awayToSection_exists
    (f : A) :
    Nonempty (CommRingCat.of (Away 𝒜 f) ⟶ Γ(Proj 𝒜, Proj.basicOpen 𝒜 f)) := by
  exact SourceStack.ProjectiveSpectrum.awayToSection_exists 𝒜 f

theorem hilbert_basicOpenToSpec_exists
    (f : A) :
    Nonempty ((Proj.basicOpen 𝒜 f).toScheme ⟶ Spec (.of (Away 𝒜 f))) := by
  exact SourceStack.ProjectiveSpectrum.basicOpenToSpec_exists 𝒜 f

theorem hilbert_basicOpenToSpec_app_top
    (f : A) :
    (Proj.basicOpenToSpec 𝒜 f).app ⊤ =
      (Scheme.ΓSpecIso _).hom ≫ Proj.awayToSection 𝒜 f ≫
        (Proj.basicOpen 𝒜 f).topIso.inv := by
  exact SourceStack.ProjectiveSpectrum.basicOpenToSpec_app_top 𝒜 f

theorem hilbert_awayι_toSpecZero
    (f : A) {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    Proj.awayι 𝒜 f f_deg hm ≫ Proj.toSpecZero 𝒜 =
      Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers f))) := by
  exact SourceStack.ProjectiveSpectrum.awayι_toSpecZero 𝒜 f f_deg hm

theorem hilbert_specMap_awayMap_awayι
    {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m)
    {m' : ℕ} {g : A} (g_deg : g ∈ 𝒜 m')
    {x : A} (hx : x = f * g) :
    Spec.map (CommRingCat.ofHom (awayMap 𝒜 g_deg hx)) ≫
      Proj.awayι 𝒜 f f_deg hm =
        Proj.awayι 𝒜 x (hx ▸ SetLike.mul_mem_graded f_deg g_deg)
          (hm.trans_le (m.le_add_right m')) := by
  exact SourceStack.ProjectiveSpectrum.specMap_awayMap_awayι 𝒜 f_deg hm g_deg hx

theorem hilbert_awayMap_awayToSection
    {f : A} {m' : ℕ} {g : A} (g_deg : g ∈ 𝒜 m')
    {x : A} (hx : x = f * g) :
    CommRingCat.ofHom (awayMap 𝒜 g_deg hx) ≫ Proj.awayToSection 𝒜 x =
      Proj.awayToSection 𝒜 f ≫
        (Proj 𝒜).presheaf.map
          (homOfLE (Proj.basicOpen_mono _ _ _ ⟨_, hx⟩)).op := by
  exact SourceStack.ProjectiveSpectrum.awayMap_awayToSection 𝒜 g_deg hx

theorem hilbert_basicOpenToSpec_SpecMap_awayMap
    {f : A} {m' : ℕ} {g : A} (g_deg : g ∈ 𝒜 m')
    {x : A} (hx : x = f * g) :
    Proj.basicOpenToSpec 𝒜 x ≫ Spec.map (CommRingCat.ofHom (awayMap 𝒜 g_deg hx)) =
      (Proj 𝒜).homOfLE (Proj.basicOpen_mono _ _ _ ⟨_, hx⟩) ≫
        Proj.basicOpenToSpec 𝒜 f := by
  exact SourceStack.ProjectiveSpectrum.basicOpenToSpec_SpecMap_awayMap 𝒜 g_deg hx

theorem hilbert_pullbackAwayιIso_exists
    {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m)
    {m' : ℕ} {g : A} (g_deg : g ∈ 𝒜 m') (hm' : 0 < m')
    {x : A} (hx : x = f * g) :
    Nonempty (Limits.pullback (Proj.awayι 𝒜 f f_deg hm) (Proj.awayι 𝒜 g g_deg hm') ≅
      Spec (CommRingCat.of (Away 𝒜 x))) := by
  exact SourceStack.ProjectiveSpectrum.pullbackAwayιIso_exists 𝒜 f_deg hm g_deg hm' hx

theorem hilbert_pullbackAwayιIso_hom_awayι
    {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m)
    {m' : ℕ} {g : A} (g_deg : g ∈ 𝒜 m') (hm' : 0 < m')
    {x : A} (hx : x = f * g) :
    (Proj.pullbackAwayιIso 𝒜 f_deg hm g_deg hm' hx).hom ≫
      Proj.awayι 𝒜 x (hx ▸ SetLike.mul_mem_graded f_deg g_deg)
        (hm.trans_le (m.le_add_right m')) =
      Limits.pullback.fst _ _ ≫ Proj.awayι 𝒜 f f_deg hm := by
  exact SourceStack.ProjectiveSpectrum.pullbackAwayιIso_hom_awayι
    𝒜 f_deg hm g_deg hm' hx

theorem hilbert_pullbackAwayιIso_hom_SpecMap_awayMap_left
    {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m)
    {m' : ℕ} {g : A} (g_deg : g ∈ 𝒜 m') (hm' : 0 < m')
    {x : A} (hx : x = f * g) :
    (Proj.pullbackAwayιIso 𝒜 f_deg hm g_deg hm' hx).hom ≫
      Spec.map (CommRingCat.ofHom (awayMap 𝒜 g_deg hx)) =
        Limits.pullback.fst _ _ := by
  exact SourceStack.ProjectiveSpectrum.pullbackAwayιIso_hom_SpecMap_awayMap_left
    𝒜 f_deg hm g_deg hm' hx

theorem hilbert_pullbackAwayιIso_hom_SpecMap_awayMap_right
    {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m)
    {m' : ℕ} {g : A} (g_deg : g ∈ 𝒜 m') (hm' : 0 < m')
    {x : A} (hx : x = f * g) :
    (Proj.pullbackAwayιIso 𝒜 f_deg hm g_deg hm' hx).hom ≫
      Spec.map (CommRingCat.ofHom (awayMap 𝒜 f_deg (hx.trans (mul_comm _ _)))) =
        Limits.pullback.snd _ _ := by
  exact SourceStack.ProjectiveSpectrum.pullbackAwayιIso_hom_SpecMap_awayMap_right
    𝒜 f_deg hm g_deg hm' hx

theorem hilbert_pullbackAwayιIso_inv_fst
    {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m)
    {m' : ℕ} {g : A} (g_deg : g ∈ 𝒜 m') (hm' : 0 < m')
    {x : A} (hx : x = f * g) :
    (Proj.pullbackAwayιIso 𝒜 f_deg hm g_deg hm' hx).inv ≫ Limits.pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (awayMap 𝒜 g_deg hx)) := by
  exact SourceStack.ProjectiveSpectrum.pullbackAwayιIso_inv_fst
    𝒜 f_deg hm g_deg hm' hx

theorem hilbert_pullbackAwayιIso_inv_snd
    {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m)
    {m' : ℕ} {g : A} (g_deg : g ∈ 𝒜 m') (hm' : 0 < m')
    {x : A} (hx : x = f * g) :
    (Proj.pullbackAwayιIso 𝒜 f_deg hm g_deg hm' hx).inv ≫ Limits.pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (awayMap 𝒜 f_deg (hx.trans (mul_comm _ _)))) := by
  exact SourceStack.ProjectiveSpectrum.pullbackAwayιIso_inv_snd
    𝒜 f_deg hm g_deg hm' hx

end ProjectiveSpectrum

namespace SchemeProjectiveLine

open SourceStack.SchemeProjectiveLine

universe u

variable (K : Type u) [CommRing K]

theorem hilbert_p1_eq_proj :
    P1 K = Proj (grading K) := by
  exact SourceStack.SchemeProjectiveLine.p1_eq_proj K

theorem hilbert_x0_mem_degree_one :
    X0 K ∈ grading K 1 := by
  exact SourceStack.SchemeProjectiveLine.x0_mem_degree_one K

theorem hilbert_x1_mem_degree_one :
    X1 K ∈ grading K 1 := by
  exact SourceStack.SchemeProjectiveLine.x1_mem_degree_one K

theorem hilbert_x0x1_mem_degree_two :
    X0 K * X1 K ∈ grading K 2 := by
  exact SourceStack.SchemeProjectiveLine.x0x1_mem_degree_two K

theorem hilbert_x0_chart_isOpenImmersion :
    IsOpenImmersion
      (Proj.awayι (grading K) (X0 K) (x0_mem_degree_one K) Nat.zero_lt_one) := by
  exact SourceStack.SchemeProjectiveLine.x0_chart_isOpenImmersion K

theorem hilbert_x1_chart_isOpenImmersion :
    IsOpenImmersion
      (Proj.awayι (grading K) (X1 K) (x1_mem_degree_one K) Nat.zero_lt_one) := by
  exact SourceStack.SchemeProjectiveLine.x1_chart_isOpenImmersion K

theorem hilbert_x0_chart_range :
    (Proj.awayι (grading K) (X0 K) (x0_mem_degree_one K) Nat.zero_lt_one).opensRange =
      Proj.basicOpen (grading K) (X0 K) := by
  exact SourceStack.SchemeProjectiveLine.x0_chart_range K

theorem hilbert_x1_chart_range :
    (Proj.awayι (grading K) (X1 K) (x1_mem_degree_one K) Nat.zero_lt_one).opensRange =
      Proj.basicOpen (grading K) (X1 K) := by
  exact SourceStack.SchemeProjectiveLine.x1_chart_range K

theorem hilbert_x0_basicOpen_isAffineOpen :
    IsAffineOpen (Proj.basicOpen (grading K) (X0 K)) := by
  exact SourceStack.SchemeProjectiveLine.x0_basicOpen_isAffineOpen K

theorem hilbert_x1_basicOpen_isAffineOpen :
    IsAffineOpen (Proj.basicOpen (grading K) (X1 K)) := by
  exact SourceStack.SchemeProjectiveLine.x1_basicOpen_isAffineOpen K

theorem hilbert_standardChartMap_isOpenImmersion
    (c : StandardAffineChart) :
    IsOpenImmersion (standardChartMap K c) := by
  exact SourceStack.SchemeProjectiveLine.standardChartMap_isOpenImmersion K c

theorem hilbert_standardChartMap_opensRange
    (c : StandardAffineChart) :
    (standardChartMap K c).opensRange = standardChartOpen K c := by
  exact SourceStack.SchemeProjectiveLine.standardChartMap_opensRange K c

theorem hilbert_standardChartOpen_isAffineOpen
    (c : StandardAffineChart) :
    IsAffineOpen (standardChartOpen K c) := by
  exact SourceStack.SchemeProjectiveLine.standardChartOpen_isAffineOpen K c

theorem hilbert_standardChartCoordinate_x0 :
    standardChartCoordinate K StandardAffineChart.x0 =
      Away.mk (grading K) (x0_mem_degree_one K) 1 (X1 K)
        (by simpa using x1_mem_degree_one K) := by
  exact SourceStack.SchemeProjectiveLine.standardChartCoordinate_x0 K

theorem hilbert_standardChartCoordinate_x1 :
    standardChartCoordinate K StandardAffineChart.x1 =
      Away.mk (grading K) (x1_mem_degree_one K) 1 (X0 K)
        (by simpa using x0_mem_degree_one K) := by
  exact SourceStack.SchemeProjectiveLine.standardChartCoordinate_x1 K

theorem hilbert_standardChartToP1HomOfRingHom_def
    {X : Scheme.{u}} {c : StandardAffineChart}
    (φ : CommRingCat.of (standardChartRing K c) ⟶ Γ(X, ⊤)) :
    standardChartToP1HomOfRingHom K φ =
      standardChartHomOfRingHom K φ ≫ standardChartMap K c := by
  exact SourceStack.SchemeProjectiveLine.standardChartToP1HomOfRingHom_def K φ

theorem hilbert_standardChartCoordinateSection_apply
    {X : Scheme.{u}} {c : StandardAffineChart}
    (φ : CommRingCat.of (standardChartRing K c) ⟶ Γ(X, ⊤)) :
    standardChartCoordinateSection K φ = φ (standardChartCoordinate K c) := by
  exact SourceStack.SchemeProjectiveLine.standardChartCoordinateSection_apply K φ

theorem hilbert_basicOpen_x0x1_eq_inf :
    Proj.basicOpen (grading K) (X0 K * X1 K) =
      Proj.basicOpen (grading K) (X0 K) ⊓ Proj.basicOpen (grading K) (X1 K) := by
  exact SourceStack.SchemeProjectiveLine.basicOpen_x0x1_eq_inf K

theorem hilbert_coordinate_chart_intersection_exists :
    Nonempty (Limits.pullback
      (Proj.awayι (grading K) (X0 K) (x0_mem_degree_one K) Nat.zero_lt_one)
      (Proj.awayι (grading K) (X1 K) (x1_mem_degree_one K) Nat.zero_lt_one) ≅
      Spec (CommRingCat.of (Away (grading K) (X0 K * X1 K)))) := by
  exact SourceStack.SchemeProjectiveLine.coordinate_chart_intersection_exists K

theorem hilbert_p1_isSeparated :
    (P1 K).IsSeparated := by
  exact SourceStack.SchemeProjectiveLine.p1_isSeparated K

theorem hilbert_irrelevant_homogeneousComponent_zero
    (p : CoordinateRing K)
    (hp : p ∈ HomogeneousIdeal.irrelevant (grading K)) :
    MvPolynomial.homogeneousComponent 0 p = 0 := by
  exact SourceStack.SchemeProjectiveLine.irrelevant_homogeneousComponent_zero K p hp

theorem hilbert_irrelevant_le_span_coordinates :
    (HomogeneousIdeal.irrelevant (grading K)).toIdeal ≤
      Ideal.span (Set.range fun i : Fin 2 => (MvPolynomial.X i : CoordinateRing K)) := by
  exact SourceStack.SchemeProjectiveLine.irrelevant_le_span_coordinates K

theorem hilbert_standard_affine_chart_cover :
    (⨆ i : Fin 2, Proj.basicOpen (grading K) (MvPolynomial.X i : CoordinateRing K)) = ⊤ := by
  exact SourceStack.SchemeProjectiveLine.standard_affine_chart_cover K

theorem hilbert_two_chart_cover :
    Proj.basicOpen (grading K) (X0 K) ⊔ Proj.basicOpen (grading K) (X1 K) = ⊤ := by
  exact SourceStack.SchemeProjectiveLine.two_chart_cover K

theorem hilbert_x0Ideal_isHomogeneous :
    (x0Ideal K).IsHomogeneous (grading K) := by
  exact SourceStack.SchemeProjectiveLine.x0Ideal_isHomogeneous K

theorem hilbert_x1Ideal_isHomogeneous :
    (x1Ideal K).IsHomogeneous (grading K) := by
  exact SourceStack.SchemeProjectiveLine.x1Ideal_isHomogeneous K

theorem hilbert_x0SubX1_mem_degree_one :
    X0SubX1 K ∈ grading K 1 := by
  exact SourceStack.SchemeProjectiveLine.x0SubX1_mem_degree_one K

theorem hilbert_x0SubX1Ideal_isHomogeneous :
    (x0SubX1Ideal K).IsHomogeneous (grading K) := by
  exact SourceStack.SchemeProjectiveLine.x0SubX1Ideal_isHomogeneous K

theorem hilbert_x0_mem_irrelevant :
    X0 K ∈ HomogeneousIdeal.irrelevant (grading K) := by
  exact SourceStack.SchemeProjectiveLine.x0_mem_irrelevant K

theorem hilbert_x1_mem_irrelevant :
    X1 K ∈ HomogeneousIdeal.irrelevant (grading K) := by
  exact SourceStack.SchemeProjectiveLine.x1_mem_irrelevant K

theorem hilbert_x1_not_mem_x0Ideal
    [Nontrivial K] :
    X1 K ∉ x0Ideal K := by
  exact SourceStack.SchemeProjectiveLine.x1_not_mem_x0Ideal K

theorem hilbert_x0_not_mem_x1Ideal
    [Nontrivial K] :
    X0 K ∉ x1Ideal K := by
  exact SourceStack.SchemeProjectiveLine.x0_not_mem_x1Ideal K

theorem hilbert_not_irrelevant_le_x0HomogeneousIdeal
    [Nontrivial K] :
    ¬ HomogeneousIdeal.irrelevant (grading K) ≤ x0HomogeneousIdeal K := by
  exact SourceStack.SchemeProjectiveLine.not_irrelevant_le_x0HomogeneousIdeal K

theorem hilbert_not_irrelevant_le_x1HomogeneousIdeal
    [Nontrivial K] :
    ¬ HomogeneousIdeal.irrelevant (grading K) ≤ x1HomogeneousIdeal K := by
  exact SourceStack.SchemeProjectiveLine.not_irrelevant_le_x1HomogeneousIdeal K

theorem hilbert_x0_not_mem_x0SubX1Ideal
    [Nontrivial K] :
    X0 K ∉ x0SubX1Ideal K := by
  exact SourceStack.SchemeProjectiveLine.x0_not_mem_x0SubX1Ideal K

theorem hilbert_not_irrelevant_le_x0SubX1HomogeneousIdeal
    [Nontrivial K] :
    ¬ HomogeneousIdeal.irrelevant (grading K) ≤ x0SubX1HomogeneousIdeal K := by
  exact SourceStack.SchemeProjectiveLine.not_irrelevant_le_x0SubX1HomogeneousIdeal K

theorem hilbert_x0PolynomialEquiv_X0 :
    x0PolynomialEquiv K (X0 K) = Polynomial.X := by
  exact SourceStack.SchemeProjectiveLine.x0PolynomialEquiv_X0 K

theorem hilbert_x0PolynomialEquiv_X1 :
    x0PolynomialEquiv K (X1 K) =
      Polynomial.C (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) K) := by
  exact SourceStack.SchemeProjectiveLine.x0PolynomialEquiv_X1 K

theorem hilbert_x1PolynomialEquiv_X1 :
    x1PolynomialEquiv K (X1 K) = Polynomial.X := by
  exact SourceStack.SchemeProjectiveLine.x1PolynomialEquiv_X1 K

theorem hilbert_x0PolynomialEquiv_X0SubX1 :
    x0PolynomialEquiv K (X0SubX1 K) = x0SubX1PolynomialTarget K := by
  exact SourceStack.SchemeProjectiveLine.x0PolynomialEquiv_X0SubX1 K

theorem hilbert_x0SubX1Ideal_eq_comap_span_X_sub_C_X :
    x0SubX1Ideal K =
      Ideal.comap
        (MvPolynomial.finSuccEquiv K 1 : CoordinateRing K →+*
          Polynomial (MvPolynomial (Fin 1) K))
        (Ideal.span ({x0SubX1PolynomialTarget K} :
          Set (Polynomial (MvPolynomial (Fin 1) K)))) := by
  exact SourceStack.SchemeProjectiveLine.x0SubX1Ideal_eq_comap_span_X_sub_C_X K

theorem hilbert_polynomial_span_X_isPrime
    [IsDomain K] :
    (Ideal.span ({Polynomial.X} : Set (Polynomial (MvPolynomial (Fin 1) K)))).IsPrime := by
  exact SourceStack.SchemeProjectiveLine.polynomial_span_X_isPrime K

theorem hilbert_polynomial_span_X_sub_C_X_isPrime
    [IsDomain K] :
    (Ideal.span ({x0SubX1PolynomialTarget K} :
      Set (Polynomial (MvPolynomial (Fin 1) K)))).IsPrime := by
  exact SourceStack.SchemeProjectiveLine.polynomial_span_X_sub_C_X_isPrime K

theorem hilbert_x0Ideal_eq_comap_span_X :
    x0Ideal K =
      Ideal.comap
        (MvPolynomial.finSuccEquiv K 1 : CoordinateRing K →+*
          Polynomial (MvPolynomial (Fin 1) K))
        (Ideal.span ({Polynomial.X} : Set (Polynomial (MvPolynomial (Fin 1) K)))) := by
  exact SourceStack.SchemeProjectiveLine.x0Ideal_eq_comap_span_X K

theorem hilbert_x1Ideal_eq_comap_span_X :
    x1Ideal K =
      Ideal.comap
        (x1PolynomialEquiv K : CoordinateRing K →+*
          Polynomial (MvPolynomial (Fin 1) K))
        (Ideal.span ({Polynomial.X} : Set (Polynomial (MvPolynomial (Fin 1) K)))) := by
  exact SourceStack.SchemeProjectiveLine.x1Ideal_eq_comap_span_X K

theorem hilbert_x0Ideal_isPrime
    [IsDomain K] :
    (x0Ideal K).IsPrime := by
  exact SourceStack.SchemeProjectiveLine.x0Ideal_isPrime K

theorem hilbert_x1Ideal_isPrime
    [IsDomain K] :
    (x1Ideal K).IsPrime := by
  exact SourceStack.SchemeProjectiveLine.x1Ideal_isPrime K

theorem hilbert_x0SubX1Ideal_isPrime
    [IsDomain K] :
    (x0SubX1Ideal K).IsPrime := by
  exact SourceStack.SchemeProjectiveLine.x0SubX1Ideal_isPrime K

theorem hilbert_zeroPoint_asHomogeneousIdeal
    [IsDomain K] :
    (zeroPoint K).asHomogeneousIdeal = x0HomogeneousIdeal K := by
  exact SourceStack.SchemeProjectiveLine.zeroPoint_asHomogeneousIdeal K

theorem hilbert_infinityPoint_asHomogeneousIdeal
    [IsDomain K] :
    (infinityPoint K).asHomogeneousIdeal = x1HomogeneousIdeal K := by
  exact SourceStack.SchemeProjectiveLine.infinityPoint_asHomogeneousIdeal K

theorem hilbert_onePoint_asHomogeneousIdeal
    [IsDomain K] :
    (onePoint K).asHomogeneousIdeal = x0SubX1HomogeneousIdeal K := by
  exact SourceStack.SchemeProjectiveLine.onePoint_asHomogeneousIdeal K

theorem hilbert_zeroPoint_ne_infinityPoint
    [IsDomain K] :
    zeroPoint K ≠ infinityPoint K := by
  exact SourceStack.SchemeProjectiveLine.zeroPoint_ne_infinityPoint K

theorem hilbert_zeroPoint_ne_onePoint
    [IsDomain K] :
    zeroPoint K ≠ onePoint K := by
  exact SourceStack.SchemeProjectiveLine.zeroPoint_ne_onePoint K

theorem hilbert_onePoint_ne_infinityPoint
    [IsDomain K] :
    onePoint K ≠ infinityPoint K := by
  exact SourceStack.SchemeProjectiveLine.onePoint_ne_infinityPoint K

theorem hilbert_zeroPoint_mem_markedPointFinset
    [IsDomain K] :
    zeroPoint K ∈ markedPointFinset K := by
  exact SourceStack.SchemeProjectiveLine.zeroPoint_mem_markedPointFinset K

theorem hilbert_onePoint_mem_markedPointFinset
    [IsDomain K] :
    onePoint K ∈ markedPointFinset K := by
  exact SourceStack.SchemeProjectiveLine.onePoint_mem_markedPointFinset K

theorem hilbert_infinityPoint_mem_markedPointFinset
    [IsDomain K] :
    infinityPoint K ∈ markedPointFinset K := by
  exact SourceStack.SchemeProjectiveLine.infinityPoint_mem_markedPointFinset K

theorem hilbert_markedPointFinset_card
    [IsDomain K] :
    (markedPointFinset K).card = 3 := by
  exact SourceStack.SchemeProjectiveLine.markedPointFinset_card K

theorem hilbert_markedPointSet_finite
    [IsDomain K] :
    (markedPointSet K).Finite := by
  exact SourceStack.SchemeProjectiveLine.markedPointSet_finite K

theorem hilbert_mem_markedPointSet_iff
    [IsDomain K] (p : _root_.ProjectiveSpectrum (grading K)) :
    p ∈ markedPointSet K ↔ p ∈ markedPointFinset K := by
  exact SourceStack.SchemeProjectiveLine.mem_markedPointSet_iff K p

theorem hilbert_markedSchemePointFinset_card
    [IsDomain K] :
    (markedSchemePointFinset K).card = 3 := by
  exact SourceStack.SchemeProjectiveLine.markedSchemePointFinset_card K

theorem hilbert_markedSchemePointSet_finite
    [IsDomain K] :
    (markedSchemePointSet K).Finite := by
  exact SourceStack.SchemeProjectiveLine.markedSchemePointSet_finite K

theorem hilbert_mem_markedSchemePointSet_iff
    [IsDomain K] (p : P1 K) :
    p ∈ markedSchemePointSet K ↔ p ∈ markedPointSet K := by
  exact SourceStack.SchemeProjectiveLine.mem_markedSchemePointSet_iff K p

theorem hilbert_zeroPoint_mem_markedSchemePointFinset
    [IsDomain K] :
    zeroPoint K ∈ markedSchemePointFinset K := by
  exact SourceStack.SchemeProjectiveLine.zeroPoint_mem_markedSchemePointFinset K

theorem hilbert_onePoint_mem_markedSchemePointFinset
    [IsDomain K] :
    onePoint K ∈ markedSchemePointFinset K := by
  exact SourceStack.SchemeProjectiveLine.onePoint_mem_markedSchemePointFinset K

theorem hilbert_infinityPoint_mem_markedSchemePointFinset
    [IsDomain K] :
    infinityPoint K ∈ markedSchemePointFinset K := by
  exact SourceStack.SchemeProjectiveLine.infinityPoint_mem_markedSchemePointFinset K

theorem hilbert_zeroPoint_mem_x1_basicOpen
    [IsDomain K] :
    zeroPoint K ∈ Proj.basicOpen (grading K) (X1 K) := by
  exact SourceStack.SchemeProjectiveLine.zeroPoint_mem_x1_basicOpen K

theorem hilbert_zeroPoint_not_mem_x0_basicOpen
    [IsDomain K] :
    zeroPoint K ∉ Proj.basicOpen (grading K) (X0 K) := by
  exact SourceStack.SchemeProjectiveLine.zeroPoint_not_mem_x0_basicOpen K

theorem hilbert_onePoint_mem_x0_basicOpen
    [IsDomain K] :
    onePoint K ∈ Proj.basicOpen (grading K) (X0 K) := by
  exact SourceStack.SchemeProjectiveLine.onePoint_mem_x0_basicOpen K

theorem hilbert_onePoint_mem_x1_basicOpen
    [IsDomain K] :
    onePoint K ∈ Proj.basicOpen (grading K) (X1 K) := by
  exact SourceStack.SchemeProjectiveLine.onePoint_mem_x1_basicOpen K

theorem hilbert_infinityPoint_mem_x0_basicOpen
    [IsDomain K] :
    infinityPoint K ∈ Proj.basicOpen (grading K) (X0 K) := by
  exact SourceStack.SchemeProjectiveLine.infinityPoint_mem_x0_basicOpen K

theorem hilbert_infinityPoint_not_mem_x1_basicOpen
    [IsDomain K] :
    infinityPoint K ∉ Proj.basicOpen (grading K) (X1 K) := by
  exact SourceStack.SchemeProjectiveLine.infinityPoint_not_mem_x1_basicOpen K

end SchemeProjectiveLine

namespace MarkedProjectiveLine

open SourceStack.MarkedProjectiveLine

universe u

theorem hilbert_linearPointFinset_eq_branchFinset
    (K : Type u) [Field K] :
    linearPointFinset K = SourceStack.ProjectiveLine.branchFinset K := by
  exact SourceStack.MarkedProjectiveLine.linearPointFinset_eq_branchFinset K

theorem hilbert_schemePointFinset_eq_markedPointFinset
    (K : Type u) [Field K] :
    schemePointFinset K = SourceStack.SchemeProjectiveLine.markedPointFinset K := by
  exact SourceStack.MarkedProjectiveLine.schemePointFinset_eq_markedPointFinset K

theorem hilbert_schemeCarrierPointFinset_eq_markedSchemePointFinset
    (K : Type u) [Field K] :
    schemeCarrierPointFinset K =
      SourceStack.SchemeProjectiveLine.markedSchemePointFinset K := by
  exact SourceStack.MarkedProjectiveLine.schemeCarrierPointFinset_eq_markedSchemePointFinset K

theorem hilbert_schemeCarrierPointSet_eq_markedSchemePointSet
    (K : Type u) [Field K] :
    schemeCarrierPointSet K = SourceStack.SchemeProjectiveLine.markedSchemePointSet K := by
  exact SourceStack.MarkedProjectiveLine.schemeCarrierPointSet_eq_markedSchemePointSet K

theorem hilbert_linearPoint_injective
    (K : Type u) [Field K] :
    Function.Injective (linearPoint K) := by
  exact SourceStack.MarkedProjectiveLine.linearPoint_injective K

theorem hilbert_schemePoint_injective
    (K : Type u) [Field K] :
    Function.Injective (schemePoint K) := by
  exact SourceStack.MarkedProjectiveLine.schemePoint_injective K

theorem hilbert_schemeCarrierPoint_injective
    (K : Type u) [Field K] :
    Function.Injective (schemeCarrierPoint K) := by
  exact SourceStack.MarkedProjectiveLine.schemeCarrierPoint_injective K

theorem hilbert_linearPoint_mem_branchFinset
    (K : Type u) [Field K] (label : MarkedPointLabel) :
    linearPoint K label ∈ SourceStack.ProjectiveLine.branchFinset K := by
  exact SourceStack.MarkedProjectiveLine.linearPoint_mem_branchFinset K label

theorem hilbert_schemePoint_mem_markedPointFinset
    (K : Type u) [Field K] (label : MarkedPointLabel) :
    schemePoint K label ∈ SourceStack.SchemeProjectiveLine.markedPointFinset K := by
  exact SourceStack.MarkedProjectiveLine.schemePoint_mem_markedPointFinset K label

theorem hilbert_schemeCarrierPoint_mem_markedSchemePointFinset
    (K : Type u) [Field K] (label : MarkedPointLabel) :
    schemeCarrierPoint K label ∈ SourceStack.SchemeProjectiveLine.markedSchemePointFinset K := by
  exact SourceStack.MarkedProjectiveLine.schemeCarrierPoint_mem_markedSchemePointFinset K label

theorem hilbert_schemeCarrierPoint_mem_markedSchemePointSet
    (K : Type u) [Field K] (label : MarkedPointLabel) :
    schemeCarrierPoint K label ∈ SourceStack.SchemeProjectiveLine.markedSchemePointSet K := by
  exact SourceStack.MarkedProjectiveLine.schemeCarrierPoint_mem_markedSchemePointSet K label

theorem hilbert_linearPointFinset_card
    (K : Type u) [Field K] :
    (linearPointFinset K).card = 3 := by
  exact SourceStack.MarkedProjectiveLine.linearPointFinset_card K

theorem hilbert_schemePointFinset_card
    (K : Type u) [Field K] :
    (schemePointFinset K).card = 3 := by
  exact SourceStack.MarkedProjectiveLine.schemePointFinset_card K

theorem hilbert_schemeCarrierPointFinset_card
    (K : Type u) [Field K] :
    (schemeCarrierPointFinset K).card = 3 := by
  exact SourceStack.MarkedProjectiveLine.schemeCarrierPointFinset_card K

theorem hilbert_schemeCarrierPointSet_finite
    (K : Type u) [Field K] :
    (schemeCarrierPointSet K).Finite := by
  exact SourceStack.MarkedProjectiveLine.schemeCarrierPointSet_finite K

theorem hilbert_linearPointFinset_card_eq_schemePointFinset_card
    (K : Type u) [Field K] :
    (linearPointFinset K).card = (schemePointFinset K).card := by
  exact SourceStack.MarkedProjectiveLine.linearPointFinset_card_eq_schemePointFinset_card K

theorem hilbert_linearPointFinset_card_eq_schemeCarrierPointFinset_card
    (K : Type u) [Field K] :
    (linearPointFinset K).card = (schemeCarrierPointFinset K).card := by
  exact SourceStack.MarkedProjectiveLine.linearPointFinset_card_eq_schemeCarrierPointFinset_card K

end MarkedProjectiveLine

namespace SchemeMarkedBelyi

open SourceStack.SchemeMarkedBelyi
open SourceStack.SchemeProjectiveLine

universe u v w

variable (K : Type u) [CommRing K] [IsDomain K]
variable (X : Type v) [TopologicalSpace X]
variable (Φ : Type w)
variable (map : Φ → X → _root_.ProjectiveSpectrum (grading K))
variable (continuous_map : ∀ φ, Continuous (map φ))

theorem hilbert_markedCoverData_branch :
    (markedCoverData K X Φ map continuous_map).branch = markedPointSet K := by
  exact SourceStack.SchemeMarkedBelyi.markedCoverData_branch K X Φ map continuous_map

theorem hilbert_markedCoverData_sendsSetToBranch_iff
    (S : Set X) (φ : Φ) :
    (markedCoverData K X Φ map continuous_map).sendsSetToBranch S φ ↔
      ∀ x ∈ S, map φ x ∈ markedPointSet K := by
  exact SourceStack.SchemeMarkedBelyi.markedCoverData_sendsSetToBranch_iff
    K X Φ map continuous_map S φ

theorem hilbert_markedCoverData_mem_belyiOpen_iff
    (φ : Φ) (x : X) :
    x ∈ (markedCoverData K X Φ map continuous_map).belyiOpen φ ↔
      map φ x ∉ markedPointSet K := by
  exact SourceStack.SchemeMarkedBelyi.markedCoverData_mem_belyiOpen_iff
    K X Φ map continuous_map φ x

theorem hilbert_markedCoverData_branch_finite :
    (markedCoverData K X Φ map continuous_map).branch.Finite := by
  exact SourceStack.SchemeMarkedBelyi.markedCoverData_branch_finite
    K X Φ map continuous_map

variable (exists_for_finite_disjoint :
  ∀ {S T : Set X}, S.Finite → T.Finite → Disjoint S T →
    ∃ φ : Φ, (∀ x ∈ S, map φ x ∈ markedPointSet K) ∧
      ∀ x ∈ T, map φ x ∉ markedPointSet K)

theorem hilbert_markedNoncriticalExistence_branch :
    (markedNoncriticalExistence K X Φ map continuous_map
      exists_for_finite_disjoint).branch = markedPointSet K := by
  exact SourceStack.SchemeMarkedBelyi.markedNoncriticalExistence_branch
    K X Φ map continuous_map exists_for_finite_disjoint

theorem hilbert_markedNoncriticalExistence_toCoverData_branch :
    (markedNoncriticalExistence K X Φ map continuous_map
      exists_for_finite_disjoint).toBelyiCoverData.branch = markedPointSet K := by
  exact SourceStack.SchemeMarkedBelyi.markedNoncriticalExistence_toCoverData_branch
    K X Φ map continuous_map exists_for_finite_disjoint

theorem hilbert_markedNoncritical_exists_belyiOpen_inside_complement
    [T1Space (_root_.ProjectiveSpectrum (grading K))]
    {A : Set X} (hA : A.Finite) {x : X} (hxA : x ∉ A) :
    ∃ φ : Φ,
      IsOpen ((markedNoncriticalExistence K X Φ map continuous_map
        exists_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
        x ∈ ((markedNoncriticalExistence K X Φ map continuous_map
          exists_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
          ((markedNoncriticalExistence K X Φ map continuous_map
            exists_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ⊆ Aᶜ := by
  exact SourceStack.SchemeMarkedBelyi.markedNoncritical_exists_belyiOpen_inside_complement
    K X Φ map continuous_map exists_for_finite_disjoint hA hxA

theorem hilbert_markedNoncritical_exists_belyiOpen_containing_finite_inside_complement
    [T1Space (_root_.ProjectiveSpectrum (grading K))]
    {S T : Set X} (hS : S.Finite) (hT : T.Finite) (hdis : Disjoint S T) :
    ∃ φ : Φ,
      IsOpen ((markedNoncriticalExistence K X Φ map continuous_map
        exists_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
        T ⊆ ((markedNoncriticalExistence K X Φ map continuous_map
          exists_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
          ((markedNoncriticalExistence K X Φ map continuous_map
            exists_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ⊆ Sᶜ := by
  exact SourceStack.SchemeMarkedBelyi.markedNoncritical_exists_belyiOpen_containing_finite_inside_complement
    K X Φ map continuous_map exists_for_finite_disjoint hS hT hdis

theorem hilbert_markedNoncritical_exists_belyiOpen_inside_open_of_finite_complement
    [T1Space (_root_.ProjectiveSpectrum (grading K))]
    {V : Set X} (hV : IsOpen V) (hVcompl : Vᶜ.Finite) {x : X} (hxV : x ∈ V) :
    ∃ φ : Φ,
      IsOpen ((markedNoncriticalExistence K X Φ map continuous_map
        exists_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
        x ∈ ((markedNoncriticalExistence K X Φ map continuous_map
          exists_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
          ((markedNoncriticalExistence K X Φ map continuous_map
            exists_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ⊆ V := by
  exact SourceStack.SchemeMarkedBelyi.markedNoncritical_exists_belyiOpen_inside_open_of_finite_complement
    K X Φ map continuous_map exists_for_finite_disjoint hV hVcompl hxV

theorem hilbert_markedNoncritical_exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
    [T1Space (_root_.ProjectiveSpectrum (grading K))]
    [SourceStack.NonemptyOpenFiniteComplement X]
    {V : Set X} (hV : IsOpen V) {x : X} (hxV : x ∈ V) :
    ∃ φ : Φ,
      IsOpen ((markedNoncriticalExistence K X Φ map continuous_map
        exists_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
        x ∈ ((markedNoncriticalExistence K X Φ map continuous_map
          exists_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
          ((markedNoncriticalExistence K X Φ map continuous_map
            exists_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ⊆ V := by
  exact
    SourceStack.SchemeMarkedBelyi.markedNoncritical_exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
      K X Φ map continuous_map exists_for_finite_disjoint hV hxV

theorem hilbert_markedNoncritical_exists_belyiOpen_containing_finite_inside_open_of_finite_complement
    [T1Space (_root_.ProjectiveSpectrum (grading K))]
    {V T : Set X} (hV : IsOpen V) (hVcompl : Vᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ V) :
    ∃ φ : Φ,
      IsOpen ((markedNoncriticalExistence K X Φ map continuous_map
        exists_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
        T ⊆ ((markedNoncriticalExistence K X Φ map continuous_map
          exists_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
          ((markedNoncriticalExistence K X Φ map continuous_map
            exists_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ⊆ V := by
  exact SourceStack.SchemeMarkedBelyi.markedNoncritical_exists_belyiOpen_containing_finite_inside_open_of_finite_complement
    K X Φ map continuous_map exists_for_finite_disjoint hV hVcompl hT hTsub

theorem hilbert_markedNoncritical_pointwise_cover_complement
    (κ : Type*) [Finite κ] {S : Set X} (hS : S.Finite)
    (x : κ → {x : X // x ∉ S}) :
    ∃ φ : Φ,
      (markedNoncriticalExistence K X Φ map continuous_map
        exists_for_finite_disjoint).toBelyiCoverData.sendsSetToBranch S φ ∧
        ∀ i, map φ (x i).1 ∉ markedPointSet K := by
  exact SourceStack.SchemeMarkedBelyi.markedNoncritical_pointwise_cover_complement
    K X Φ map continuous_map exists_for_finite_disjoint κ hS x

theorem hilbert_markedNoncritical_finite_subcover_on_complement
    (κ : Type*) [Finite κ] [T1Space (_root_.ProjectiveSpectrum (grading K))]
    {S : Set X} (hS : S.Finite) [CompactSpace (κ → {x : X // x ∉ S})] :
    ∃ t : Finset {φ : Φ //
        (markedNoncriticalExistence K X Φ map continuous_map
          exists_for_finite_disjoint).toBelyiCoverData.sendsSetToBranch S φ},
      (⋃ φ ∈ t,
          ((markedNoncriticalExistence K X Φ map continuous_map
            exists_for_finite_disjoint).toBelyiCoverData.complementCoverData S).tupleAvoidSet
              (κ := κ) φ) =
        (Set.univ : Set (κ → {x : X // x ∉ S})) := by
  exact SourceStack.SchemeMarkedBelyi.markedNoncritical_finite_subcover_on_complement
    K X Φ map continuous_map exists_for_finite_disjoint κ hS

section SchemeCarrierTarget

variable (schemeMap : Φ → X → P1 K)
variable (continuous_schemeMap : ∀ φ, Continuous (schemeMap φ))

theorem hilbert_markedSchemeCoverData_branch :
    (markedSchemeCoverData K X Φ schemeMap continuous_schemeMap).branch =
      markedSchemePointSet K := by
  exact SourceStack.SchemeMarkedBelyi.markedSchemeCoverData_branch
    K X Φ schemeMap continuous_schemeMap

theorem hilbert_markedSchemeCoverData_sendsSetToBranch_iff
    (S : Set X) (φ : Φ) :
    (markedSchemeCoverData K X Φ schemeMap continuous_schemeMap).sendsSetToBranch S φ ↔
      ∀ x ∈ S, schemeMap φ x ∈ markedSchemePointSet K := by
  exact SourceStack.SchemeMarkedBelyi.markedSchemeCoverData_sendsSetToBranch_iff
    K X Φ schemeMap continuous_schemeMap S φ

theorem hilbert_markedSchemeCoverData_mem_belyiOpen_iff
    (φ : Φ) (x : X) :
    x ∈ (markedSchemeCoverData K X Φ schemeMap continuous_schemeMap).belyiOpen φ ↔
      schemeMap φ x ∉ markedSchemePointSet K := by
  exact SourceStack.SchemeMarkedBelyi.markedSchemeCoverData_mem_belyiOpen_iff
    K X Φ schemeMap continuous_schemeMap φ x

theorem hilbert_markedSchemeCoverData_branch_finite :
    (markedSchemeCoverData K X Φ schemeMap continuous_schemeMap).branch.Finite := by
  exact SourceStack.SchemeMarkedBelyi.markedSchemeCoverData_branch_finite
    K X Φ schemeMap continuous_schemeMap

variable (exists_scheme_for_finite_disjoint :
  ∀ {S T : Set X}, S.Finite → T.Finite → Disjoint S T →
    ∃ φ : Φ, (∀ x ∈ S, schemeMap φ x ∈ markedSchemePointSet K) ∧
      ∀ x ∈ T, schemeMap φ x ∉ markedSchemePointSet K)

theorem hilbert_markedSchemeNoncriticalExistence_branch :
    (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
      exists_scheme_for_finite_disjoint).branch = markedSchemePointSet K := by
  exact SourceStack.SchemeMarkedBelyi.markedSchemeNoncriticalExistence_branch
    K X Φ schemeMap continuous_schemeMap exists_scheme_for_finite_disjoint

theorem hilbert_markedSchemeNoncriticalExistence_toCoverData_branch :
    (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
      exists_scheme_for_finite_disjoint).toBelyiCoverData.branch =
      markedSchemePointSet K := by
  exact SourceStack.SchemeMarkedBelyi.markedSchemeNoncriticalExistence_toCoverData_branch
    K X Φ schemeMap continuous_schemeMap exists_scheme_for_finite_disjoint

theorem hilbert_markedSchemeNoncritical_exists_belyiOpen_inside_complement
    [T1Space (P1 K)]
    {A : Set X} (hA : A.Finite) {x : X} (hxA : x ∉ A) :
    ∃ φ : Φ,
      IsOpen ((markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
        exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
        x ∈ ((markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
          exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
          ((markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
            exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ⊆ Aᶜ := by
  exact SourceStack.SchemeMarkedBelyi.markedSchemeNoncritical_exists_belyiOpen_inside_complement
    K X Φ schemeMap continuous_schemeMap exists_scheme_for_finite_disjoint hA hxA

theorem hilbert_markedSchemeNoncritical_exists_belyiOpen_containing_finite_inside_complement
    [T1Space (P1 K)]
    {S T : Set X} (hS : S.Finite) (hT : T.Finite) (hdis : Disjoint S T) :
    ∃ φ : Φ,
      IsOpen ((markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
        exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
        T ⊆ ((markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
          exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
          ((markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
            exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ⊆ Sᶜ := by
  exact SourceStack.SchemeMarkedBelyi.markedSchemeNoncritical_exists_belyiOpen_containing_finite_inside_complement
    K X Φ schemeMap continuous_schemeMap exists_scheme_for_finite_disjoint hS hT hdis

theorem hilbert_markedSchemeNoncritical_exists_belyiOpen_inside_open_of_finite_complement
    [T1Space (P1 K)]
    {V : Set X} (hV : IsOpen V) (hVcompl : Vᶜ.Finite) {x : X} (hxV : x ∈ V) :
    ∃ φ : Φ,
      IsOpen ((markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
        exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
        x ∈ ((markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
          exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
          ((markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
            exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ⊆ V := by
  exact SourceStack.SchemeMarkedBelyi.markedSchemeNoncritical_exists_belyiOpen_inside_open_of_finite_complement
    K X Φ schemeMap continuous_schemeMap exists_scheme_for_finite_disjoint hV hVcompl hxV

theorem hilbert_markedSchemeNoncritical_exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
    [T1Space (P1 K)] [SourceStack.NonemptyOpenFiniteComplement X]
    {V : Set X} (hV : IsOpen V) {x : X} (hxV : x ∈ V) :
    ∃ φ : Φ,
      IsOpen ((markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
        exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
        x ∈ ((markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
          exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
          ((markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
            exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ⊆ V := by
  exact
    SourceStack.SchemeMarkedBelyi.markedSchemeNoncritical_exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
      K X Φ schemeMap continuous_schemeMap exists_scheme_for_finite_disjoint hV hxV

theorem hilbert_markedSchemeNoncritical_exists_belyiOpen_containing_finite_inside_open_of_finite_complement
    [T1Space (P1 K)]
    {V T : Set X} (hV : IsOpen V) (hVcompl : Vᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ V) :
    ∃ φ : Φ,
      IsOpen ((markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
        exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
        T ⊆ ((markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
          exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
          ((markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
            exists_scheme_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ⊆ V := by
  exact SourceStack.SchemeMarkedBelyi.markedSchemeNoncritical_exists_belyiOpen_containing_finite_inside_open_of_finite_complement
    K X Φ schemeMap continuous_schemeMap exists_scheme_for_finite_disjoint hV hVcompl hT hTsub

theorem hilbert_markedSchemeNoncritical_pointwise_cover_complement
    (κ : Type*) [Finite κ] {S : Set X} (hS : S.Finite)
    (x : κ → {x : X // x ∉ S}) :
    ∃ φ : Φ,
      (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
        exists_scheme_for_finite_disjoint).toBelyiCoverData.sendsSetToBranch S φ ∧
        ∀ i, schemeMap φ (x i).1 ∉ markedSchemePointSet K := by
  exact SourceStack.SchemeMarkedBelyi.markedSchemeNoncritical_pointwise_cover_complement
    K X Φ schemeMap continuous_schemeMap exists_scheme_for_finite_disjoint κ hS x

theorem hilbert_markedSchemeNoncritical_finite_subcover_on_complement
    (κ : Type*) [Finite κ] [T1Space (P1 K)]
    {S : Set X} (hS : S.Finite) [CompactSpace (κ → {x : X // x ∉ S})] :
    ∃ t : Finset {φ : Φ //
        (markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
          exists_scheme_for_finite_disjoint).toBelyiCoverData.sendsSetToBranch S φ},
      (⋃ φ ∈ t,
          ((markedSchemeNoncriticalExistence K X Φ schemeMap continuous_schemeMap
            exists_scheme_for_finite_disjoint).toBelyiCoverData.complementCoverData S).tupleAvoidSet
              (κ := κ) φ) =
        (Set.univ : Set (κ → {x : X // x ∉ S})) := by
  exact SourceStack.SchemeMarkedBelyi.markedSchemeNoncritical_finite_subcover_on_complement
    K X Φ schemeMap continuous_schemeMap exists_scheme_for_finite_disjoint κ hS

end SchemeCarrierTarget

section PartialMapDomain

variable {C : Scheme.{u}}

theorem hilbert_partialMapMarkedCoverData_branch
    (f : C.PartialMap (P1 K)) :
    (partialMapMarkedCoverData K f).branch = markedSchemePointSet K := by
  exact SourceStack.SchemeMarkedBelyi.partialMapMarkedCoverData_branch K f

theorem hilbert_partialMapMarkedCoverData_branch_finite
    (f : C.PartialMap (P1 K)) :
    (partialMapMarkedCoverData K f).branch.Finite := by
  exact SourceStack.SchemeMarkedBelyi.partialMapMarkedCoverData_branch_finite K f

theorem hilbert_partialMapMarkedCoverData_map_apply
    (f : C.PartialMap (P1 K)) (x : f.domain) :
    (partialMapMarkedCoverData K f).map () x = f.hom.base x := by
  exact SourceStack.SchemeMarkedBelyi.partialMapMarkedCoverData_map_apply K f x

theorem hilbert_partialMapMarkedCoverData_sendsSetToBranch_iff
    (f : C.PartialMap (P1 K)) (S : Set f.domain) :
    (partialMapMarkedCoverData K f).sendsSetToBranch S () ↔
      ∀ x ∈ S, f.hom.base x ∈ markedSchemePointSet K := by
  exact SourceStack.SchemeMarkedBelyi.partialMapMarkedCoverData_sendsSetToBranch_iff K f S

theorem hilbert_partialMapMarkedCoverData_mem_belyiOpen_iff
    (f : C.PartialMap (P1 K)) (x : f.domain) :
    x ∈ (partialMapMarkedCoverData K f).belyiOpen () ↔
      f.hom.base x ∉ markedSchemePointSet K := by
  exact SourceStack.SchemeMarkedBelyi.partialMapMarkedCoverData_mem_belyiOpen_iff K f x

theorem hilbert_partialMapMarkedCoverData_belyiOpen_eq
    (f : C.PartialMap (P1 K)) :
    (partialMapMarkedCoverData K f).belyiOpen () =
      {x : f.domain | f.hom.base x ∉ markedSchemePointSet K} := by
  exact SourceStack.SchemeMarkedBelyi.partialMapMarkedCoverData_belyiOpen_eq K f

theorem hilbert_partialMapMarkedCoverData_belyiOpen_isOpen
    [T1Space (P1 K)] (f : C.PartialMap (P1 K)) :
    IsOpen ((partialMapMarkedCoverData K f).belyiOpen ()) := by
  exact SourceStack.SchemeMarkedBelyi.partialMapMarkedCoverData_belyiOpen_isOpen K f

theorem hilbert_partialMapMarkedCoverData_belyiOpen_subset_compl_of_sendsSetToBranch
    (f : C.PartialMap (P1 K)) {S : Set f.domain}
    (hS : (partialMapMarkedCoverData K f).sendsSetToBranch S ()) :
    (partialMapMarkedCoverData K f).belyiOpen () ⊆ Sᶜ := by
  exact SourceStack.SchemeMarkedBelyi.partialMapMarkedCoverData_belyiOpen_subset_compl_of_sendsSetToBranch
    K f hS

theorem hilbert_rationalMapMarkedCoverData_branch
    [IsReduced C] (f : C ⤏ P1 K) :
    (rationalMapMarkedCoverData K f).branch = markedSchemePointSet K := by
  exact SourceStack.SchemeMarkedBelyi.rationalMapMarkedCoverData_branch K f

theorem hilbert_rationalMapMarkedCoverData_branch_finite
    [IsReduced C] (f : C ⤏ P1 K) :
    (rationalMapMarkedCoverData K f).branch.Finite := by
  exact SourceStack.SchemeMarkedBelyi.rationalMapMarkedCoverData_branch_finite K f

theorem hilbert_rationalMapMarkedCoverData_map_apply
    [IsReduced C] (f : C ⤏ P1 K) (x : f.domain) :
    (rationalMapMarkedCoverData K f).map () x = f.toPartialMap.hom.base x := by
  exact SourceStack.SchemeMarkedBelyi.rationalMapMarkedCoverData_map_apply K f x

theorem hilbert_rationalMapMarkedCoverData_sendsSetToBranch_iff
    [IsReduced C] (f : C ⤏ P1 K) (S : Set f.domain) :
    (rationalMapMarkedCoverData K f).sendsSetToBranch S () ↔
      ∀ x ∈ S, f.toPartialMap.hom.base x ∈ markedSchemePointSet K := by
  exact SourceStack.SchemeMarkedBelyi.rationalMapMarkedCoverData_sendsSetToBranch_iff K f S

theorem hilbert_rationalMapMarkedCoverData_mem_belyiOpen_iff
    [IsReduced C] (f : C ⤏ P1 K) (x : f.domain) :
    x ∈ (rationalMapMarkedCoverData K f).belyiOpen () ↔
      f.toPartialMap.hom.base x ∉ markedSchemePointSet K := by
  exact SourceStack.SchemeMarkedBelyi.rationalMapMarkedCoverData_mem_belyiOpen_iff K f x

theorem hilbert_rationalMapMarkedCoverData_belyiOpen_eq
    [IsReduced C] (f : C ⤏ P1 K) :
    (rationalMapMarkedCoverData K f).belyiOpen () =
      {x : f.domain | f.toPartialMap.hom.base x ∉ markedSchemePointSet K} := by
  exact SourceStack.SchemeMarkedBelyi.rationalMapMarkedCoverData_belyiOpen_eq K f

theorem hilbert_rationalMapMarkedCoverData_belyiOpen_isOpen
    [IsReduced C] [T1Space (P1 K)] (f : C ⤏ P1 K) :
    IsOpen ((rationalMapMarkedCoverData K f).belyiOpen ()) := by
  exact SourceStack.SchemeMarkedBelyi.rationalMapMarkedCoverData_belyiOpen_isOpen K f

theorem hilbert_rationalMapMarkedCoverData_belyiOpen_subset_compl_of_sendsSetToBranch
    [IsReduced C] (f : C ⤏ P1 K) {S : Set f.domain}
    (hS : (rationalMapMarkedCoverData K f).sendsSetToBranch S ()) :
    (rationalMapMarkedCoverData K f).belyiOpen () ⊆ Sᶜ := by
  exact SourceStack.SchemeMarkedBelyi.rationalMapMarkedCoverData_belyiOpen_subset_compl_of_sendsSetToBranch
    K f hS

end PartialMapDomain

section MorphismFamily

variable (C : Scheme.{u})
variable (morphism : Φ → (C ⟶ P1 K))

theorem hilbert_morphismMarkedCoverData_branch :
    (morphismMarkedCoverData K Φ C morphism).branch = markedSchemePointSet K := by
  exact SourceStack.SchemeMarkedBelyi.morphismMarkedCoverData_branch K Φ C morphism

theorem hilbert_morphismMarkedCoverData_branch_finite :
    (morphismMarkedCoverData K Φ C morphism).branch.Finite := by
  exact SourceStack.SchemeMarkedBelyi.morphismMarkedCoverData_branch_finite K Φ C morphism

theorem hilbert_morphismMarkedCoverData_map_apply
    (φ : Φ) (x : C) :
    (morphismMarkedCoverData K Φ C morphism).map φ x = (morphism φ).base x := by
  exact SourceStack.SchemeMarkedBelyi.morphismMarkedCoverData_map_apply K Φ C morphism φ x

theorem hilbert_morphismMarkedCoverData_sendsSetToBranch_iff
    (S : Set C) (φ : Φ) :
    (morphismMarkedCoverData K Φ C morphism).sendsSetToBranch S φ ↔
      ∀ x ∈ S, (morphism φ).base x ∈ markedSchemePointSet K := by
  exact SourceStack.SchemeMarkedBelyi.morphismMarkedCoverData_sendsSetToBranch_iff
    K Φ C morphism S φ

theorem hilbert_morphismMarkedCoverData_mem_belyiOpen_iff
    (φ : Φ) (x : C) :
    x ∈ (morphismMarkedCoverData K Φ C morphism).belyiOpen φ ↔
      (morphism φ).base x ∉ markedSchemePointSet K := by
  exact SourceStack.SchemeMarkedBelyi.morphismMarkedCoverData_mem_belyiOpen_iff
    K Φ C morphism φ x

theorem hilbert_morphismMarkedCoverData_belyiOpen_eq
    (φ : Φ) :
    (morphismMarkedCoverData K Φ C morphism).belyiOpen φ =
      {x : C | (morphism φ).base x ∉ markedSchemePointSet K} := by
  exact SourceStack.SchemeMarkedBelyi.morphismMarkedCoverData_belyiOpen_eq
    K Φ C morphism φ

theorem hilbert_morphismMarkedCoverData_belyiOpen_isOpen
    [T1Space (P1 K)] (φ : Φ) :
    IsOpen ((morphismMarkedCoverData K Φ C morphism).belyiOpen φ) := by
  exact SourceStack.SchemeMarkedBelyi.morphismMarkedCoverData_belyiOpen_isOpen
    K Φ C morphism φ

theorem hilbert_morphismMarkedCoverData_belyiOpen_subset_compl_of_sendsSetToBranch
    {S : Set C} {φ : Φ}
    (hS : (morphismMarkedCoverData K Φ C morphism).sendsSetToBranch S φ) :
    (morphismMarkedCoverData K Φ C morphism).belyiOpen φ ⊆ Sᶜ := by
  exact SourceStack.SchemeMarkedBelyi.morphismMarkedCoverData_belyiOpen_subset_compl_of_sendsSetToBranch
    K Φ C morphism hS

variable (exists_morphism_for_finite_disjoint :
  ∀ {S T : Set C}, S.Finite → T.Finite → Disjoint S T →
    ∃ φ : Φ, (∀ x ∈ S, (morphism φ).base x ∈ markedSchemePointSet K) ∧
      ∀ x ∈ T, (morphism φ).base x ∉ markedSchemePointSet K)

theorem hilbert_morphismMarkedNoncriticalExistence_branch :
    (morphismMarkedNoncriticalExistence K Φ C morphism
      exists_morphism_for_finite_disjoint).branch = markedSchemePointSet K := by
  exact SourceStack.SchemeMarkedBelyi.morphismMarkedNoncriticalExistence_branch
    K Φ C morphism exists_morphism_for_finite_disjoint

theorem hilbert_morphismMarkedNoncriticalExistence_toCoverData_branch :
    (morphismMarkedNoncriticalExistence K Φ C morphism
      exists_morphism_for_finite_disjoint).toBelyiCoverData.branch =
      markedSchemePointSet K := by
  exact SourceStack.SchemeMarkedBelyi.morphismMarkedNoncriticalExistence_toCoverData_branch
    K Φ C morphism exists_morphism_for_finite_disjoint

theorem hilbert_morphismMarkedNoncritical_exists_belyiOpen_inside_complement
    [T1Space (P1 K)]
    {A : Set C} (hA : A.Finite) {x : C} (hxA : x ∉ A) :
    ∃ φ : Φ,
      IsOpen ((morphismMarkedNoncriticalExistence K Φ C morphism
        exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
        x ∈ ((morphismMarkedNoncriticalExistence K Φ C morphism
          exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
          ((morphismMarkedNoncriticalExistence K Φ C morphism
            exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ⊆ Aᶜ := by
  exact SourceStack.SchemeMarkedBelyi.morphismMarkedNoncritical_exists_belyiOpen_inside_complement
    K Φ C morphism exists_morphism_for_finite_disjoint hA hxA

theorem hilbert_morphismMarkedNoncritical_exists_belyiOpen_containing_finite_inside_complement
    [T1Space (P1 K)]
    {S T : Set C} (hS : S.Finite) (hT : T.Finite) (hdis : Disjoint S T) :
    ∃ φ : Φ,
      IsOpen ((morphismMarkedNoncriticalExistence K Φ C morphism
        exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
        T ⊆ ((morphismMarkedNoncriticalExistence K Φ C morphism
          exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
          ((morphismMarkedNoncriticalExistence K Φ C morphism
            exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ⊆ Sᶜ := by
  exact SourceStack.SchemeMarkedBelyi.morphismMarkedNoncritical_exists_belyiOpen_containing_finite_inside_complement
    K Φ C morphism exists_morphism_for_finite_disjoint hS hT hdis

theorem hilbert_morphismMarkedNoncritical_exists_belyiOpen_inside_open_of_finite_complement
    [T1Space (P1 K)]
    {V : Set C} (hV : IsOpen V) (hVcompl : Vᶜ.Finite) {x : C} (hxV : x ∈ V) :
    ∃ φ : Φ,
      IsOpen ((morphismMarkedNoncriticalExistence K Φ C morphism
        exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
        x ∈ ((morphismMarkedNoncriticalExistence K Φ C morphism
          exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
          ((morphismMarkedNoncriticalExistence K Φ C morphism
            exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ⊆ V := by
  exact SourceStack.SchemeMarkedBelyi.morphismMarkedNoncritical_exists_belyiOpen_inside_open_of_finite_complement
    K Φ C morphism exists_morphism_for_finite_disjoint hV hVcompl hxV

theorem hilbert_morphismMarkedNoncritical_exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
    [T1Space (P1 K)] [SourceStack.NonemptyOpenFiniteComplement C]
    {V : Set C} (hV : IsOpen V) {x : C} (hxV : x ∈ V) :
    ∃ φ : Φ,
      IsOpen ((morphismMarkedNoncriticalExistence K Φ C morphism
        exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
        x ∈ ((morphismMarkedNoncriticalExistence K Φ C morphism
          exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
          ((morphismMarkedNoncriticalExistence K Φ C morphism
            exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ⊆ V := by
  exact
    SourceStack.SchemeMarkedBelyi.morphismMarkedNoncritical_exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
      K Φ C morphism exists_morphism_for_finite_disjoint hV hxV

theorem hilbert_morphismMarkedNoncritical_exists_belyiOpen_containing_finite_inside_open_of_finite_complement
    [T1Space (P1 K)]
    {V T : Set C} (hV : IsOpen V) (hVcompl : Vᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ V) :
    ∃ φ : Φ,
      IsOpen ((morphismMarkedNoncriticalExistence K Φ C morphism
        exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
        T ⊆ ((morphismMarkedNoncriticalExistence K Φ C morphism
          exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ∧
          ((morphismMarkedNoncriticalExistence K Φ C morphism
            exists_morphism_for_finite_disjoint).toBelyiCoverData.belyiOpen φ) ⊆ V := by
  exact SourceStack.SchemeMarkedBelyi.morphismMarkedNoncritical_exists_belyiOpen_containing_finite_inside_open_of_finite_complement
    K Φ C morphism exists_morphism_for_finite_disjoint hV hVcompl hT hTsub

theorem hilbert_morphismMarkedNoncritical_pointwise_cover_complement
    (κ : Type*) [Finite κ] {S : Set C} (hS : S.Finite)
    (x : κ → {x : C // x ∉ S}) :
    ∃ φ : Φ,
      (morphismMarkedNoncriticalExistence K Φ C morphism
        exists_morphism_for_finite_disjoint).toBelyiCoverData.sendsSetToBranch S φ ∧
        ∀ i, (morphism φ).base (x i).1 ∉ markedSchemePointSet K := by
  exact SourceStack.SchemeMarkedBelyi.morphismMarkedNoncritical_pointwise_cover_complement
    K Φ C morphism exists_morphism_for_finite_disjoint κ hS x

theorem hilbert_morphismMarkedNoncritical_finite_subcover_on_complement
    (κ : Type*) [Finite κ] [T1Space (P1 K)]
    {S : Set C} (hS : S.Finite) [CompactSpace (κ → {x : C // x ∉ S})] :
    ∃ t : Finset {φ : Φ //
        (morphismMarkedNoncriticalExistence K Φ C morphism
          exists_morphism_for_finite_disjoint).toBelyiCoverData.sendsSetToBranch S φ},
      (⋃ φ ∈ t,
          ((morphismMarkedNoncriticalExistence K Φ C morphism
            exists_morphism_for_finite_disjoint).toBelyiCoverData.complementCoverData S).tupleAvoidSet
              (κ := κ) φ) =
        (Set.univ : Set (κ → {x : C // x ∉ S})) := by
  exact SourceStack.SchemeMarkedBelyi.morphismMarkedNoncritical_finite_subcover_on_complement
    K Φ C morphism exists_morphism_for_finite_disjoint κ hS

end MorphismFamily

section SchemeBelyiMapBridge

variable {C : Scheme.{u}}
variable (hmarkedOpen : IsOpen (markedSchemePointSet K)ᶜ)
variable (φ :
  SourceStack.SchemeBelyi.BelyiMap
    (SourceStack.SchemeBelyi.markedBelyiTarget K hmarkedOpen) C)

theorem hilbert_schemeBelyiMapMarkedCoverData_branch :
    (schemeBelyiMapMarkedCoverData K hmarkedOpen φ).branch =
      markedSchemePointSet K := by
  exact SourceStack.SchemeMarkedBelyi.schemeBelyiMapMarkedCoverData_branch
    K hmarkedOpen φ

theorem hilbert_schemeBelyiMapMarkedCoverData_branch_finite :
    (schemeBelyiMapMarkedCoverData K hmarkedOpen φ).branch.Finite := by
  exact SourceStack.SchemeMarkedBelyi.schemeBelyiMapMarkedCoverData_branch_finite
    K hmarkedOpen φ

theorem hilbert_schemeBelyiMapMarkedCoverData_map_apply
    (x : C) :
    (schemeBelyiMapMarkedCoverData K hmarkedOpen φ).map () x = φ.hom.base x := by
  exact SourceStack.SchemeMarkedBelyi.schemeBelyiMapMarkedCoverData_map_apply
    K hmarkedOpen φ x

theorem hilbert_schemeBelyiMapMarkedCoverData_mem_belyiOpen_iff
    (x : C) :
    x ∈ (schemeBelyiMapMarkedCoverData K hmarkedOpen φ).belyiOpen () ↔
      φ.hom.base x ∉ markedSchemePointSet K := by
  exact SourceStack.SchemeMarkedBelyi.schemeBelyiMapMarkedCoverData_mem_belyiOpen_iff
    K hmarkedOpen φ x

theorem hilbert_schemeBelyiMapMarkedCoverData_belyiOpen_eq_schemeBelyi :
    (schemeBelyiMapMarkedCoverData K hmarkedOpen φ).belyiOpen () =
      (φ.belyiOpen : Set C) := by
  exact SourceStack.SchemeMarkedBelyi.schemeBelyiMapMarkedCoverData_belyiOpen_eq_schemeBelyi
    K hmarkedOpen φ

theorem hilbert_schemeBelyiMapMarkedCoverData_belyiOpen_isOpen :
    IsOpen ((schemeBelyiMapMarkedCoverData K hmarkedOpen φ).belyiOpen ()) := by
  exact SourceStack.SchemeMarkedBelyi.schemeBelyiMapMarkedCoverData_belyiOpen_isOpen
    K hmarkedOpen φ

variable (φfin :
  SourceStack.SchemeBelyi.FiniteBelyiMap
    (SourceStack.SchemeBelyi.markedBelyiTarget K hmarkedOpen) C)

theorem hilbert_finiteSchemeBelyiMapMarkedCoverData_branch :
    (finiteSchemeBelyiMapMarkedCoverData K hmarkedOpen φfin).branch =
      markedSchemePointSet K := by
  exact SourceStack.SchemeMarkedBelyi.finiteSchemeBelyiMapMarkedCoverData_branch
    K hmarkedOpen φfin

theorem hilbert_finiteSchemeBelyiMapMarkedCoverData_isFinite_hom :
    IsFinite φfin.hom := by
  exact SourceStack.SchemeMarkedBelyi.finiteSchemeBelyiMapMarkedCoverData_isFinite_hom
    K hmarkedOpen φfin

theorem hilbert_finiteSchemeBelyiMapMarkedCoverData_map_apply
    (x : C) :
    (finiteSchemeBelyiMapMarkedCoverData K hmarkedOpen φfin).map () x =
      φfin.hom.base x := by
  exact SourceStack.SchemeMarkedBelyi.finiteSchemeBelyiMapMarkedCoverData_map_apply
    K hmarkedOpen φfin x

theorem hilbert_finiteSchemeBelyiMapMarkedCoverData_belyiOpen_eq_schemeBelyi :
    (finiteSchemeBelyiMapMarkedCoverData K hmarkedOpen φfin).belyiOpen () =
      (φfin.toBelyiMap.belyiOpen : Set C) := by
  exact SourceStack.SchemeMarkedBelyi.finiteSchemeBelyiMapMarkedCoverData_belyiOpen_eq_schemeBelyi
    K hmarkedOpen φfin

theorem hilbert_finiteSchemeBelyiMapMarkedCoverData_belyiOpen_isOpen :
    IsOpen ((finiteSchemeBelyiMapMarkedCoverData K hmarkedOpen φfin).belyiOpen ()) := by
  exact SourceStack.SchemeMarkedBelyi.finiteSchemeBelyiMapMarkedCoverData_belyiOpen_isOpen
    K hmarkedOpen φfin

end SchemeBelyiMapBridge

section FiniteMarkedBelyiFamily

variable {C : Scheme.{u}}
variable (F : FiniteMarkedBelyiExistence K Φ C)

theorem hilbert_finiteMarkedBelyiExistence_toMarkedCoverData_branch :
    (FiniteMarkedBelyiExistence.toMarkedCoverData K Φ F).branch =
      markedSchemePointSet K := by
  exact SourceStack.SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedCoverData_branch
    K Φ F

theorem hilbert_finiteMarkedBelyiExistence_toMarkedNoncriticalExistence_branch :
    (FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K Φ F).branch =
      markedSchemePointSet K := by
  exact SourceStack.SchemeMarkedBelyi.FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence_branch
    K Φ F

theorem hilbert_finiteMarkedBelyiExistence_map_apply
    (φ : Φ) (x : C) :
    (FiniteMarkedBelyiExistence.toMarkedCoverData K Φ F).map φ x =
      (F.map φ).hom.base x := by
  exact SourceStack.SchemeMarkedBelyi.FiniteMarkedBelyiExistence.map_apply
    K Φ F φ x

theorem hilbert_finiteMarkedBelyiExistence_finite_hom
    (φ : Φ) :
    IsFinite (F.map φ).hom := by
  exact SourceStack.SchemeMarkedBelyi.FiniteMarkedBelyiExistence.finite_hom
    K Φ F φ

theorem hilbert_finiteMarkedBelyiExistence_mem_belyiOpen_iff
    (φ : Φ) (x : C) :
    x ∈ (FiniteMarkedBelyiExistence.toMarkedCoverData K Φ F).belyiOpen φ ↔
      (F.map φ).hom.base x ∉ markedSchemePointSet K := by
  exact SourceStack.SchemeMarkedBelyi.FiniteMarkedBelyiExistence.mem_belyiOpen_iff
    K Φ F φ x

theorem hilbert_finiteMarkedBelyiExistence_belyiOpen_eq_schemeBelyi
    (φ : Φ) :
    (FiniteMarkedBelyiExistence.toMarkedCoverData K Φ F).belyiOpen φ =
      ((F.map φ).toBelyiMap.belyiOpen : Set C) := by
  exact SourceStack.SchemeMarkedBelyi.FiniteMarkedBelyiExistence.belyiOpen_eq_schemeBelyi
    K Φ F φ

theorem hilbert_finiteMarkedBelyiExistence_belyiOpen_isOpen
    (φ : Φ) :
    IsOpen ((FiniteMarkedBelyiExistence.toMarkedCoverData K Φ F).belyiOpen φ) := by
  exact SourceStack.SchemeMarkedBelyi.FiniteMarkedBelyiExistence.belyiOpen_isOpen
    K Φ F φ

theorem hilbert_finiteMarkedBelyiExistence_exists_belyiOpen_inside_complement
    [T1Space (P1 K)]
    {A : Set C} (hA : A.Finite) {x : C} (hxA : x ∉ A) :
    ∃ φ : Φ,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ) ∧
        x ∈ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ) ⊆ Aᶜ := by
  exact SourceStack.SchemeMarkedBelyi.FiniteMarkedBelyiExistence.exists_belyiOpen_inside_complement
    K Φ F hA hxA

theorem hilbert_finiteMarkedBelyiExistence_exists_belyiOpen_containing_finite_inside_complement
    [T1Space (P1 K)]
    {S T : Set C} (hS : S.Finite) (hT : T.Finite) (hdis : Disjoint S T) :
    ∃ φ : Φ,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ) ∧
        T ⊆ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ) ⊆ Sᶜ := by
  exact SourceStack.SchemeMarkedBelyi.FiniteMarkedBelyiExistence.exists_belyiOpen_containing_finite_inside_complement
    K Φ F hS hT hdis

theorem hilbert_finiteMarkedBelyiExistence_exists_belyiOpen_inside_open_of_finite_complement
    [T1Space (P1 K)]
    {V : Set C} (hV : IsOpen V) (hVcompl : Vᶜ.Finite) {x : C} (hxV : x ∈ V) :
    ∃ φ : Φ,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ) ∧
        x ∈ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ) ⊆ V := by
  exact SourceStack.SchemeMarkedBelyi.FiniteMarkedBelyiExistence.exists_belyiOpen_inside_open_of_finite_complement
    K Φ F hV hVcompl hxV

theorem hilbert_finiteMarkedBelyiExistence_exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
    [T1Space (P1 K)] [SourceStack.NonemptyOpenFiniteComplement C]
    {V : Set C} (hV : IsOpen V) {x : C} (hxV : x ∈ V) :
    ∃ φ : Φ,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ) ∧
        x ∈ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ) ⊆ V := by
  exact SourceStack.SchemeMarkedBelyi.FiniteMarkedBelyiExistence.exists_belyiOpen_inside_open_of_nonemptyOpenFiniteComplement
    K Φ F hV hxV

theorem hilbert_finiteMarkedBelyiExistence_exists_belyiOpen_containing_finite_inside_open_of_finite_complement
    [T1Space (P1 K)]
    {V T : Set C} (hV : IsOpen V) (hVcompl : Vᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ V) :
    ∃ φ : Φ,
      IsOpen ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ) ∧
        T ⊆ ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ) ∧
          ((FiniteMarkedBelyiExistence.toMarkedNoncriticalExistence K Φ F).toBelyiCoverData.belyiOpen φ) ⊆ V := by
  exact SourceStack.SchemeMarkedBelyi.FiniteMarkedBelyiExistence.exists_belyiOpen_containing_finite_inside_open_of_finite_complement
    K Φ F hV hVcompl hT hTsub

theorem hilbert_finiteMarkedBelyiExistence_pointwise_cover_complement
    (κ : Type*) [Finite κ] {S : Set C} (hS : S.Finite)
    (x : κ → {x : C // x ∉ S}) :
    ∃ φ : Φ,
      (FiniteMarkedBelyiExistence.toMarkedCoverData K Φ F).sendsSetToBranch S φ ∧
        ∀ i, (F.map φ).hom.base (x i).1 ∉ markedSchemePointSet K := by
  exact SourceStack.SchemeMarkedBelyi.FiniteMarkedBelyiExistence.pointwise_cover_complement
    K Φ F κ hS x

theorem hilbert_finiteMarkedBelyiExistence_finite_subcover_on_complement
    (κ : Type*) [Finite κ] [T1Space (P1 K)]
    {S : Set C} (hS : S.Finite) [CompactSpace (κ → {x : C // x ∉ S})] :
    ∃ t : Finset {φ : Φ //
        (FiniteMarkedBelyiExistence.toMarkedCoverData K Φ F).sendsSetToBranch S φ},
      (⋃ φ ∈ t,
          ((FiniteMarkedBelyiExistence.toMarkedCoverData K Φ F).complementCoverData S).tupleAvoidSet
              (κ := κ) φ) =
        (Set.univ : Set (κ → {x : C // x ∉ S})) := by
  exact SourceStack.SchemeMarkedBelyi.FiniteMarkedBelyiExistence.finite_subcover_on_complement
    K Φ F κ hS

end FiniteMarkedBelyiFamily

end SchemeMarkedBelyi

namespace RationalMaps

universe u

variable {X Y : Scheme.{u}}

theorem hilbert_partialMap_toRationalMap_surjective :
    Function.Surjective (@Scheme.PartialMap.toRationalMap X Y) := by
  exact SourceStack.RationalMaps.partialMap_toRationalMap_surjective

theorem hilbert_rationalMap_exists_rep
    (f : X ⤏ Y) :
    ∃ g : X.PartialMap Y, g.toRationalMap = f := by
  exact SourceStack.RationalMaps.rationalMap_exists_rep f

theorem hilbert_partialMap_toRationalMap_eq_iff
    {f g : X.PartialMap Y} :
    f.toRationalMap = g.toRationalMap ↔ f.equiv g := by
  exact SourceStack.RationalMaps.partialMap_toRationalMap_eq_iff

theorem hilbert_partialMap_dense_domain
    (f : X.PartialMap Y) :
    Dense (f.domain : Set X) := by
  exact SourceStack.RationalMaps.partialMap_dense_domain f

theorem hilbert_rationalMap_dense_domain
    (f : X ⤏ Y) :
    Dense (f.domain : Set X) := by
  exact SourceStack.RationalMaps.rationalMap_dense_domain f

theorem hilbert_rationalMap_toRationalMap_toPartialMap
    [IsReduced X] [Y.IsSeparated] (f : X ⤏ Y) :
    f.toPartialMap.toRationalMap = f := by
  exact SourceStack.RationalMaps.rationalMap_toRationalMap_toPartialMap f

theorem hilbert_partialMap_fromFunctionField_restrict
    [IrreducibleSpace X] (f : X.PartialMap Y)
    {U : X.Opens} (hU : Dense (U : Set X)) (hU' : U ≤ f.domain) :
    (f.restrict U hU hU').fromFunctionField = f.fromFunctionField := by
  exact SourceStack.RationalMaps.partialMap_fromFunctionField_restrict f hU hU'

theorem hilbert_rationalMap_fromFunctionField_toRationalMap
    [IrreducibleSpace X] (f : X.PartialMap Y) :
    f.toRationalMap.fromFunctionField = f.fromFunctionField := by
  exact SourceStack.RationalMaps.rationalMap_fromFunctionField_toRationalMap f

theorem hilbert_rationalMap_eq_of_fromFunctionField_eq
    [IsIntegral X] (f g : X ⤏ Y)
    (H : f.fromFunctionField = g.fromFunctionField) :
    f = g := by
  exact SourceStack.RationalMaps.rationalMap_eq_of_fromFunctionField_eq f g H

theorem hilbert_rationalMap_fromFunctionField_ofFunctionField
    {S : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
    [IsIntegral X] [LocallyOfFiniteType sY]
    (f : Spec X.functionField ⟶ Y)
    (h : f ≫ sY = X.fromSpecStalk _ ≫ sX) :
    (Scheme.RationalMap.ofFunctionField sX sY f h).fromFunctionField = f := by
  exact SourceStack.RationalMaps.rationalMap_fromFunctionField_ofFunctionField sX sY f h

theorem hilbert_p1RationalMap_exists_rep
    (K : Type u) [CommRing K] (f : X ⤏ SourceStack.SchemeProjectiveLine.P1 K) :
    ∃ g : X.PartialMap (SourceStack.SchemeProjectiveLine.P1 K), g.toRationalMap = f := by
  exact SourceStack.RationalMaps.p1RationalMap_exists_rep K f

theorem hilbert_p1PartialMap_toRationalMap_eq_iff
    (K : Type u) [CommRing K]
    {f g : X.PartialMap (SourceStack.SchemeProjectiveLine.P1 K)} :
    f.toRationalMap = g.toRationalMap ↔ f.equiv g := by
  exact SourceStack.RationalMaps.p1PartialMap_toRationalMap_eq_iff K

theorem hilbert_p1PartialMap_dense_domain
    (K : Type u) [CommRing K]
    (f : X.PartialMap (SourceStack.SchemeProjectiveLine.P1 K)) :
    Dense (f.domain : Set X) := by
  exact SourceStack.RationalMaps.p1PartialMap_dense_domain K f

theorem hilbert_p1RationalMap_dense_domain
    (K : Type u) [CommRing K] (f : X ⤏ SourceStack.SchemeProjectiveLine.P1 K) :
    Dense (f.domain : Set X) := by
  exact SourceStack.RationalMaps.p1RationalMap_dense_domain K f

theorem hilbert_p1RationalMap_toRationalMap_toPartialMap
    (K : Type u) [CommRing K] [IsReduced X]
    (f : X ⤏ SourceStack.SchemeProjectiveLine.P1 K) :
    f.toPartialMap.toRationalMap = f := by
  exact SourceStack.RationalMaps.p1RationalMap_toRationalMap_toPartialMap K f

theorem hilbert_p1PartialMap_fromFunctionField_restrict
    (K : Type u) [CommRing K] [IrreducibleSpace X]
    (f : X.PartialMap (SourceStack.SchemeProjectiveLine.P1 K))
    {U : X.Opens} (hU : Dense (U : Set X)) (hU' : U ≤ f.domain) :
    (f.restrict U hU hU').fromFunctionField = f.fromFunctionField := by
  exact SourceStack.RationalMaps.p1PartialMap_fromFunctionField_restrict K f hU hU'

theorem hilbert_p1PartialMap_restrict_domain
    (K : Type u) [CommRing K]
    (f : X.PartialMap (SourceStack.SchemeProjectiveLine.P1 K))
    {U : X.Opens} (hU : Dense (U : Set X)) (hU' : U ≤ f.domain) :
    (f.restrict U hU hU').domain = U := by
  exact SourceStack.RationalMaps.p1PartialMap_restrict_domain K f hU hU'

theorem hilbert_p1PartialMap_restrict_hom
    (K : Type u) [CommRing K]
    (f : X.PartialMap (SourceStack.SchemeProjectiveLine.P1 K))
    {U : X.Opens} (hU : Dense (U : Set X)) (hU' : U ≤ f.domain) :
    (f.restrict U hU hU').hom = X.homOfLE hU' ≫ f.hom := by
  exact SourceStack.RationalMaps.p1PartialMap_restrict_hom K f hU hU'

theorem hilbert_p1PartialMap_restrict_id
    (K : Type u) [CommRing K]
    (f : X.PartialMap (SourceStack.SchemeProjectiveLine.P1 K)) :
    f.restrict f.domain f.dense_domain le_rfl = f := by
  exact SourceStack.RationalMaps.p1PartialMap_restrict_id K f

theorem hilbert_p1PartialMap_le_domain_toRationalMap
    (K : Type u) [CommRing K]
    (f : X.PartialMap (SourceStack.SchemeProjectiveLine.P1 K)) :
    f.domain ≤ f.toRationalMap.domain := by
  exact SourceStack.RationalMaps.p1PartialMap_le_domain_toRationalMap K f

theorem hilbert_p1RationalMap_mem_domain
    (K : Type u) [CommRing K]
    {f : X ⤏ SourceStack.SchemeProjectiveLine.P1 K} {x : X} :
    x ∈ f.domain ↔
      ∃ g : X.PartialMap (SourceStack.SchemeProjectiveLine.P1 K),
        x ∈ g.domain ∧ g.toRationalMap = f := by
  exact SourceStack.RationalMaps.p1RationalMap_mem_domain K

theorem hilbert_p1PartialMapDomainMap_apply
    (K : Type u) [CommRing K]
    (f : X.PartialMap (SourceStack.SchemeProjectiveLine.P1 K))
    (x : f.domain) :
    SourceStack.RationalMaps.p1PartialMapDomainMap K f x = f.hom.base x := by
  exact SourceStack.RationalMaps.p1PartialMapDomainMap_apply K f x

theorem hilbert_continuous_p1PartialMapDomainMap
    (K : Type u) [CommRing K]
    (f : X.PartialMap (SourceStack.SchemeProjectiveLine.P1 K)) :
    Continuous (SourceStack.RationalMaps.p1PartialMapDomainMap K f) := by
  exact SourceStack.RationalMaps.continuous_p1PartialMapDomainMap K f

theorem hilbert_p1PartialMap_compHom_domain
    (K : Type u) [CommRing K] {Z : Scheme.{u}}
    (f : X.PartialMap (SourceStack.SchemeProjectiveLine.P1 K))
    (g : SourceStack.SchemeProjectiveLine.P1 K ⟶ Z) :
    (f.compHom g).domain = f.domain := by
  exact SourceStack.RationalMaps.p1PartialMap_compHom_domain K f g

theorem hilbert_p1PartialMap_compHom_hom
    (K : Type u) [CommRing K] {Z : Scheme.{u}}
    (f : X.PartialMap (SourceStack.SchemeProjectiveLine.P1 K))
    (g : SourceStack.SchemeProjectiveLine.P1 K ⟶ Z) :
    (f.compHom g).hom = f.hom ≫ g := by
  exact SourceStack.RationalMaps.p1PartialMap_compHom_hom K f g

theorem hilbert_p1PartialMap_fromSpecStalkOfMem_eq
    (K : Type u) [CommRing K]
    (f : X.PartialMap (SourceStack.SchemeProjectiveLine.P1 K))
    {x : X} (hx : x ∈ f.domain) :
    f.fromSpecStalkOfMem hx =
      f.domain.fromSpecStalkOfMem x hx ≫ f.hom := by
  exact SourceStack.RationalMaps.p1PartialMap_fromSpecStalkOfMem_eq K f hx

theorem hilbert_p1PartialMap_fromSpecStalkOfMem_restrict
    (K : Type u) [CommRing K]
    (f : X.PartialMap (SourceStack.SchemeProjectiveLine.P1 K))
    {U : X.Opens} (hU : Dense (U : Set X)) (hU' : U ≤ f.domain)
    {x : X} (hx : x ∈ U) :
    (f.restrict U hU hU').fromSpecStalkOfMem hx =
      f.fromSpecStalkOfMem (hU' hx) := by
  exact SourceStack.RationalMaps.p1PartialMap_fromSpecStalkOfMem_restrict K f hU hU' hx

theorem hilbert_p1RationalMap_fromFunctionField_toRationalMap
    (K : Type u) [CommRing K] [IrreducibleSpace X]
    (f : X.PartialMap (SourceStack.SchemeProjectiveLine.P1 K)) :
    f.toRationalMap.fromFunctionField = f.fromFunctionField := by
  exact SourceStack.RationalMaps.p1RationalMap_fromFunctionField_toRationalMap K f

theorem hilbert_p1RationalMap_eq_of_fromFunctionField_eq
    (K : Type u) [CommRing K] [IsIntegral X]
    (f g : X ⤏ SourceStack.SchemeProjectiveLine.P1 K)
    (H : f.fromFunctionField = g.fromFunctionField) :
    f = g := by
  exact SourceStack.RationalMaps.p1RationalMap_eq_of_fromFunctionField_eq K f g H

end RationalMaps

namespace FunctionFields

universe u

variable {X Y : Scheme.{u}}

theorem hilbert_germ_injective_of_isIntegral
    [IsIntegral X] {U : X.Opens} (x : X) (hx : x ∈ U) :
    Function.Injective (X.presheaf.germ U x hx) := by
  exact SourceStack.FunctionFields.germ_injective_of_isIntegral x hx

theorem hilbert_genericPoint_mem_open
    [IrreducibleSpace X] (U : X.Opens) [Nonempty U] :
    genericPoint X ∈ U := by
  exact SourceStack.FunctionFields.genericPoint_mem_open U

theorem hilbert_germToFunctionField_injective
    [IsIntegral X] (U : X.Opens) [Nonempty U] :
    Function.Injective (X.germToFunctionField U) := by
  exact SourceStack.FunctionFields.germToFunctionField_injective U

theorem hilbert_functionField_isFractionRing_of_isAffineOpen
    [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    IsFractionRing Γ(X, U) X.functionField := by
  exact SourceStack.FunctionFields.functionField_isFractionRing_of_isAffineOpen U hU

theorem hilbert_functionField_isFractionRing_of_affine
    (R : CommRingCat.{u}) [IsDomain R] :
    IsFractionRing R (Spec R).functionField := by
  exact SourceStack.FunctionFields.functionField_isFractionRing_of_affine R

theorem hilbert_genericPoint_eq_bot_of_affine
    (R : CommRingCat.{u}) [IsDomain R] :
    genericPoint (Spec R) = (⊥ : PrimeSpectrum R) := by
  exact SourceStack.FunctionFields.genericPoint_eq_bot_of_affine R

theorem hilbert_isIntegral_open
    [IsIntegral X] (U : X.Opens) [Nonempty U] :
    IsIntegral U := by
  exact SourceStack.FunctionFields.isIntegral_open U

theorem hilbert_stalk_isFractionRing_functionField
    [IsIntegral X] (x : X) :
    IsFractionRing (X.presheaf.stalk x) X.functionField := by
  exact SourceStack.FunctionFields.stalk_isFractionRing_functionField x

theorem hilbert_primeIdealOf_genericPoint
    [IsIntegral X] {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    hU.primeIdealOf
        ⟨genericPoint X, SourceStack.FunctionFields.genericPoint_mem_open (X := X) U⟩ =
      genericPoint (Spec Γ(X, U)) := by
  exact SourceStack.FunctionFields.primeIdealOf_genericPoint hU

theorem hilbert_functionField_isScalarTower
    [IrreducibleSpace X] (U : X.Opens) (x : U) [Nonempty U] :
    IsScalarTower Γ(X, U) (X.presheaf.stalk x) X.functionField := by
  exact SourceStack.FunctionFields.functionField_isScalarTower U x

theorem hilbert_genericPoint_eq_of_isOpenImmersion
    (f : X ⟶ Y) [IsOpenImmersion f]
    [IrreducibleSpace X] [IrreducibleSpace Y] :
    f.base (genericPoint X) = genericPoint Y := by
  exact SourceStack.FunctionFields.genericPoint_eq_of_isOpenImmersion f

end FunctionFields

namespace ResidueFields

universe u

variable {X Y Z : Scheme.{u}}

theorem hilbert_residueField_field_exists
    (x : X) :
    Nonempty (Field (X.residueField x)) := by
  exact SourceStack.ResidueFields.residueField_field_exists x

theorem hilbert_residue_surjective
    (X : Scheme.{u}) (x : X) :
    Function.Surjective (X.residue x) := by
  exact SourceStack.ResidueFields.residue_surjective X x

theorem hilbert_evaluation_eq_zero_iff_not_mem_basicOpen
    (U : X.Opens) (x : X) (hx : x ∈ U) (f : Γ(X, U)) :
    X.evaluation U x hx f = 0 ↔ x ∉ X.basicOpen f := by
  exact SourceStack.ResidueFields.evaluation_eq_zero_iff_not_mem_basicOpen U x hx f

theorem hilbert_evaluation_ne_zero_iff_mem_basicOpen
    (U : X.Opens) (x : X) (hx : x ∈ U) (f : Γ(X, U)) :
    X.evaluation U x hx f ≠ 0 ↔ x ∈ X.basicOpen f := by
  exact SourceStack.ResidueFields.evaluation_ne_zero_iff_mem_basicOpen U x hx f

theorem hilbert_basicOpen_eq_bot_iff_forall_evaluation_eq_zero
    (U : X.Opens) (f : Γ(X, U)) :
    X.basicOpen f = ⊥ ↔
      ∀ x : U, X.evaluation U x x.2 f = 0 := by
  exact SourceStack.ResidueFields.basicOpen_eq_bot_iff_forall_evaluation_eq_zero U f

theorem hilbert_residue_residueFieldMap
    (f : X ⟶ Y) (x : X) :
    Y.residue (f.base x) ≫ f.residueFieldMap x =
      f.stalkMap x ≫ X.residue x := by
  exact SourceStack.ResidueFields.residue_residueFieldMap f x

theorem hilbert_evaluation_naturality
    (f : X ⟶ Y) {V : Y.Opens} (x : X) (hx : f.base x ∈ V) :
    Y.evaluation V (f.base x) hx ≫ f.residueFieldMap x =
      f.app V ≫ X.evaluation (f ⁻¹ᵁ V) x hx := by
  exact SourceStack.ResidueFields.evaluation_naturality f x hx

theorem hilbert_evaluation_naturality_apply
    (f : X ⟶ Y) {V : Y.Opens} (x : X) (hx : f.base x ∈ V)
    (s : Γ(Y, V)) :
    f.residueFieldMap x (Y.evaluation V (f.base x) hx s) =
      X.evaluation (f ⁻¹ᵁ V) x hx (f.app V s) := by
  exact SourceStack.ResidueFields.evaluation_naturality_apply f x hx s

theorem hilbert_residueFieldMap_id
    (x : X) :
    Scheme.Hom.residueFieldMap (𝟙 X) x = 𝟙 (X.residueField x) := by
  exact SourceStack.ResidueFields.residueFieldMap_id x

theorem hilbert_residueFieldMap_comp
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g).residueFieldMap x =
      g.residueFieldMap (f.base x) ≫ f.residueFieldMap x := by
  exact SourceStack.ResidueFields.residueFieldMap_comp f g x

theorem hilbert_residueFieldCongr_exists
    {x y : X} (h : x = y) :
    Nonempty (X.residueField x ≅ X.residueField y) := by
  exact SourceStack.ResidueFields.residueFieldCongr_exists h

theorem hilbert_residueFieldCongr_refl
    {x : X} :
    Scheme.residueFieldCongr (show x = x from rfl) =
      Iso.refl (X.residueField x) := by
  exact SourceStack.ResidueFields.residueFieldCongr_refl

theorem hilbert_residueFieldCongr_symm
    {x y : X} (h : x = y) :
    (Scheme.residueFieldCongr h).symm = Scheme.residueFieldCongr h.symm := by
  exact SourceStack.ResidueFields.residueFieldCongr_symm h

theorem hilbert_residueFieldCongr_inv
    {x y : X} (h : x = y) :
    (Scheme.residueFieldCongr h).inv =
      (Scheme.residueFieldCongr h.symm).hom := by
  exact SourceStack.ResidueFields.residueFieldCongr_inv h

theorem hilbert_residueFieldCongr_trans
    {x y z : X} (hxy : x = y) (hyz : y = z) :
    Scheme.residueFieldCongr hxy ≪≫ Scheme.residueFieldCongr hyz =
      Scheme.residueFieldCongr (hxy.trans hyz) := by
  exact SourceStack.ResidueFields.residueFieldCongr_trans hxy hyz

theorem hilbert_residueFieldCongr_trans_hom
    {x y z : X} (hxy : x = y) (hyz : y = z) :
    (Scheme.residueFieldCongr hxy).hom ≫
        (Scheme.residueFieldCongr hyz).hom =
      (Scheme.residueFieldCongr (hxy.trans hyz)).hom := by
  exact SourceStack.ResidueFields.residueFieldCongr_trans_hom hxy hyz

theorem hilbert_residue_residueFieldCongr
    {x y : X} (h : x = y) :
    X.residue x ≫ (Scheme.residueFieldCongr h).hom =
      (X.presheaf.stalkCongr (Inseparable.of_eq h)).hom ≫ X.residue y := by
  exact SourceStack.ResidueFields.residue_residueFieldCongr h

theorem hilbert_residueFieldMap_congr
    {f g : X ⟶ Y} (e : f = g) (x : X) :
    f.residueFieldMap x =
      (Scheme.residueFieldCongr (by rw [e])).hom ≫ g.residueFieldMap x := by
  exact SourceStack.ResidueFields.residueFieldMap_congr e x

theorem hilbert_Γevaluation_naturality
    (f : X ⟶ Y) (x : X) :
    Y.Γevaluation (f.base x) ≫ f.residueFieldMap x =
      f.c.app (op ⊤) ≫ X.Γevaluation x := by
  exact SourceStack.ResidueFields.Γevaluation_naturality f x

theorem hilbert_Γevaluation_naturality_apply
    (f : X ⟶ Y) (x : X) (a : Y.presheaf.obj (op ⊤)) :
    f.residueFieldMap x (Y.Γevaluation (f.base x) a) =
      X.Γevaluation x (f.c.app (op ⊤) a) := by
  exact SourceStack.ResidueFields.Γevaluation_naturality_apply f x a

theorem hilbert_residueFieldMap_isIso_of_openImmersion
    (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    IsIso (f.residueFieldMap x) := by
  exact SourceStack.ResidueFields.residueFieldMap_isIso_of_openImmersion f x

theorem hilbert_descResidueField_exists
    {K : Type u} [Field K] {x : X}
    (f : X.presheaf.stalk x ⟶ CommRingCat.of K) [IsLocalHom f.hom] :
    Nonempty (X.residueField x ⟶ CommRingCat.of K) := by
  exact SourceStack.ResidueFields.descResidueField_exists f

theorem hilbert_residue_descResidueField
    {K : Type u} [Field K] {x : X}
    (f : X.presheaf.stalk x ⟶ CommRingCat.of K) [IsLocalHom f.hom] :
    X.residue x ≫ Scheme.descResidueField f = f := by
  exact SourceStack.ResidueFields.residue_descResidueField f

theorem hilbert_affineOpen_fromSpecStalk_eq_fromSpecStalk
    {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hxU : x ∈ U) :
    hU.fromSpecStalk hxU = X.fromSpecStalk x := by
  exact SourceStack.ResidueFields.affineOpen_fromSpecStalk_eq_fromSpecStalk hU hxU

theorem hilbert_fromSpecStalk_closedPoint
    (x : X) :
    (X.fromSpecStalk x).base (closedPoint (X.presheaf.stalk x)) = x := by
  exact SourceStack.ResidueFields.fromSpecStalk_closedPoint x

theorem hilbert_fromSpecStalk_app
    {U : X.Opens} {x : X} (hxU : x ∈ U) :
    (X.fromSpecStalk x).app U =
      X.presheaf.germ U x hxU ≫
        (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv ≫
          (Spec (X.presheaf.stalk x)).presheaf.map (homOfLE le_top).op := by
  exact SourceStack.ResidueFields.fromSpecStalk_app hxU

theorem hilbert_fromSpecStalk_appTop
    {x : X} :
    (X.fromSpecStalk x).appTop =
      X.presheaf.germ ⊤ x trivial ≫
        (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv ≫
          (Spec (X.presheaf.stalk x)).presheaf.map (homOfLE le_top).op := by
  exact SourceStack.ResidueFields.fromSpecStalk_appTop

theorem hilbert_range_fromSpecStalk
    (x : X) :
    Set.range (X.fromSpecStalk x).base = { y | y ⤳ x } := by
  exact SourceStack.ResidueFields.range_fromSpecStalk x

theorem hilbert_Spec_map_stalkSpecializes_fromSpecStalk
    {x y : X} (h : x ⤳ y) :
    Spec.map (X.presheaf.stalkSpecializes h) ≫ X.fromSpecStalk y =
      X.fromSpecStalk x := by
  exact SourceStack.ResidueFields.Spec_map_stalkSpecializes_fromSpecStalk h

theorem hilbert_Spec_map_stalkMap_fromSpecStalk
    (f : X ⟶ Y) (x : X) :
    Spec.map (f.stalkMap x) ≫ Y.fromSpecStalk _ =
      X.fromSpecStalk x ≫ f := by
  exact SourceStack.ResidueFields.Spec_map_stalkMap_fromSpecStalk f x

theorem hilbert_Spec_fromSpecStalk
    (R : CommRingCat.{u}) (x : Spec R) :
    (Spec R).fromSpecStalk x =
      Spec.map ((Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ x trivial) := by
  exact SourceStack.ResidueFields.Spec_fromSpecStalk R x

theorem hilbert_Opens_fromSpecStalkOfMem_ι
    (U : X.Opens) (x : X) (hxU : x ∈ U) :
    U.fromSpecStalkOfMem x hxU ≫ U.ι = X.fromSpecStalk x := by
  exact SourceStack.ResidueFields.Opens_fromSpecStalkOfMem_ι U x hxU

theorem hilbert_fromSpecStalk_toSpecΓ
    (X : Scheme.{u}) (x : X) :
    X.fromSpecStalk x ≫ X.toSpecΓ =
      Spec.map (X.presheaf.germ ⊤ x trivial) := by
  exact SourceStack.ResidueFields.fromSpecStalk_toSpecΓ X x

theorem hilbert_Opens_fromSpecStalkOfMem_toSpecΓ
    (U : X.Opens) (x : X) (hxU : x ∈ U) :
    U.fromSpecStalkOfMem x hxU ≫ U.toSpecΓ =
      Spec.map (X.presheaf.germ U x hxU) := by
  exact SourceStack.ResidueFields.Opens_fromSpecStalkOfMem_toSpecΓ U x hxU

theorem hilbert_stalkClosedPointIso_exists
    (R : CommRingCat.{u}) [IsLocalRing R] :
    Nonempty ((Spec R).presheaf.stalk (closedPoint R) ≅ R) := by
  exact SourceStack.ResidueFields.stalkClosedPointIso_exists R

theorem hilbert_stalkClosedPointIso_inv
    (R : CommRingCat.{u}) [IsLocalRing R] :
    (stalkClosedPointIso R).inv = StructureSheaf.toStalk R _ := by
  exact SourceStack.ResidueFields.stalkClosedPointIso_inv R

theorem hilbert_germ_stalkClosedPointIso_hom
    (R : CommRingCat.{u}) [IsLocalRing R] :
    (Spec R).presheaf.germ ⊤ (closedPoint R) trivial ≫
        (stalkClosedPointIso R).hom =
      (Scheme.ΓSpecIso R).hom := by
  exact SourceStack.ResidueFields.germ_stalkClosedPointIso_hom R

theorem hilbert_Spec_stalkClosedPointIso
    (R : CommRingCat.{u}) [IsLocalRing R] :
    Spec.map (stalkClosedPointIso R).inv =
      (Spec R).fromSpecStalk (closedPoint R) := by
  exact SourceStack.ResidueFields.Spec_stalkClosedPointIso R

theorem hilbert_stalkClosedPointTo_isLocalHom
    {R : CommRingCat.{u}} [IsLocalRing R] (f : Spec R ⟶ X) :
    IsLocalHom (Scheme.stalkClosedPointTo f).hom := by
  exact SourceStack.ResidueFields.stalkClosedPointTo_isLocalHom f

theorem hilbert_preimage_eq_top_of_closedPoint_mem
    {R : CommRingCat.{u}} [IsLocalRing R] (f : Spec R ⟶ X)
    {U : X.Opens} (hU : f.base (closedPoint R) ∈ U) :
    f ⁻¹ᵁ U = ⊤ := by
  exact SourceStack.ResidueFields.preimage_eq_top_of_closedPoint_mem f hU

theorem hilbert_stalkClosedPointTo_comp
    {R : CommRingCat.{u}} [IsLocalRing R] (f : Spec R ⟶ X) (g : X ⟶ Y) :
    Scheme.stalkClosedPointTo (f ≫ g) =
      g.stalkMap _ ≫ Scheme.stalkClosedPointTo f := by
  exact SourceStack.ResidueFields.stalkClosedPointTo_comp f g

theorem hilbert_stalkClosedPointTo_fromSpecStalk
    (x : X) :
    Scheme.stalkClosedPointTo (X.fromSpecStalk x) =
      (X.presheaf.stalkCongr
        (Inseparable.of_eq (by rw [Scheme.fromSpecStalk_closedPoint]))).hom := by
  exact SourceStack.ResidueFields.stalkClosedPointTo_fromSpecStalk x

theorem hilbert_Spec_stalkClosedPointTo_fromSpecStalk
    {R : CommRingCat.{u}} [IsLocalRing R] (f : Spec R ⟶ X) :
    Spec.map (Scheme.stalkClosedPointTo f) ≫ X.fromSpecStalk _ = f := by
  exact SourceStack.ResidueFields.Spec_stalkClosedPointTo_fromSpecStalk f

theorem hilbert_fromSpecResidueField_apply
    (x : X) (s : Spec (X.residueField x)) :
    (X.fromSpecResidueField x).base s = x := by
  exact SourceStack.ResidueFields.fromSpecResidueField_apply x s

theorem hilbert_residueFieldCongr_fromSpecResidueField
    {x y : X} (h : x = y) :
    Spec.map (Scheme.residueFieldCongr h).hom ≫ X.fromSpecResidueField x =
      X.fromSpecResidueField y := by
  exact SourceStack.ResidueFields.residueFieldCongr_fromSpecResidueField h

theorem hilbert_range_fromSpecResidueField
    (x : X) :
    Set.range (X.fromSpecResidueField x).base = {x} := by
  exact SourceStack.ResidueFields.range_fromSpecResidueField x

theorem hilbert_Spec_map_residueFieldMap_fromSpecResidueField
    (f : X ⟶ Y) (x : X) :
    Spec.map (f.residueFieldMap x) ≫ Y.fromSpecResidueField _ =
      X.fromSpecResidueField x ≫ f := by
  exact SourceStack.ResidueFields.Spec_map_residueFieldMap_fromSpecResidueField f x

theorem hilbert_descResidueField_fromSpecResidueField
    {K : Type u} [Field K] {x : X}
    (f : X.presheaf.stalk x ⟶ CommRingCat.of K) [IsLocalHom f.hom] :
    Spec.map (Scheme.descResidueField f) ≫ X.fromSpecResidueField x =
      Spec.map f ≫ X.fromSpecStalk x := by
  exact SourceStack.ResidueFields.descResidueField_fromSpecResidueField f

theorem hilbert_descResidueField_stalkClosedPointTo_fromSpecResidueField
    (K : Type u) [Field K] (X : Scheme.{u})
    (f : Spec (CommRingCat.of K) ⟶ X) :
    Spec.map (@Scheme.descResidueField (CommRingCat.of K) _ X _
        (Scheme.stalkClosedPointTo f) _) ≫
      X.fromSpecResidueField (f.base (closedPoint K)) = f := by
  exact SourceStack.ResidueFields.descResidueField_stalkClosedPointTo_fromSpecResidueField K X f

theorem hilbert_SpecToEquivOfField_exists
    (K : Type u) [Field K] (X : Scheme.{u}) :
    Nonempty ((Spec (.of K) ⟶ X) ≃ Σ x, X.residueField x ⟶ .of K) := by
  exact SourceStack.ResidueFields.SpecToEquivOfField_exists K X

theorem hilbert_SpecToEquivOfField_eq_iff
    {K : Type u} [Field K] {X : Scheme.{u}}
    {f₁ f₂ : Σ x, X.residueField x ⟶ CommRingCat.of K} :
    f₁ = f₂ ↔
      ∃ e : f₁.1 = f₂.1,
        f₁.2 = (Scheme.residueFieldCongr e).hom ≫ f₂.2 := by
  exact SourceStack.ResidueFields.SpecToEquivOfField_eq_iff

theorem hilbert_SpecToEquivOfLocalRing_exists
    (R : CommRingCat.{u}) [IsLocalRing R] (X : Scheme.{u}) :
    Nonempty ((Spec R ⟶ X) ≃
      Σ x, { f : X.presheaf.stalk x ⟶ R // IsLocalHom f.hom }) := by
  exact SourceStack.ResidueFields.SpecToEquivOfLocalRing_exists R X

theorem hilbert_SpecToEquivOfLocalRing_eq_iff
    {R : CommRingCat.{u}} [IsLocalRing R] {X : Scheme.{u}}
    {f₁ f₂ : Σ x, { f : X.presheaf.stalk x ⟶ R // IsLocalHom f.hom }} :
    f₁ = f₂ ↔
      ∃ h₁ : f₁.1 = f₂.1,
        f₁.2.1 = (X.presheaf.stalkCongr (Inseparable.of_eq h₁)).hom ≫ f₂.2.1 := by
  exact SourceStack.ResidueFields.SpecToEquivOfLocalRing_eq_iff

end ResidueFields

namespace StalkMaps

universe u

variable {X Y Z : Scheme.{u}}

theorem hilbert_stalkMap_isLocalHom
    (f : X ⟶ Y) (x : X) :
    IsLocalHom (f.stalkMap x).hom := by
  exact SourceStack.StalkMaps.stalkMap_isLocalHom f x

theorem hilbert_stalkMap_id
    (X : Scheme.{u}) (x : X) :
    (𝟙 X : X ⟶ X).stalkMap x = 𝟙 (X.presheaf.stalk x) := by
  exact SourceStack.StalkMaps.stalkMap_id X x

theorem hilbert_stalkMap_comp
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g : X ⟶ Z).stalkMap x =
      g.stalkMap (f.base x) ≫ f.stalkMap x := by
  exact SourceStack.StalkMaps.stalkMap_comp f g x

theorem hilbert_stalkSpecializes_stalkMap
    (f : X ⟶ Y) (x x' : X) (h : x ⤳ x') :
    Y.presheaf.stalkSpecializes (f.base.map_specializes h) ≫ f.stalkMap x =
      f.stalkMap x' ≫ X.presheaf.stalkSpecializes h := by
  exact SourceStack.StalkMaps.stalkSpecializes_stalkMap f x x' h

theorem hilbert_stalkSpecializes_stalkMap_apply
    (f : X ⟶ Y) (x x' : X) (h : x ⤳ x')
    (y : Y.presheaf.stalk (f.base x')) :
    f.stalkMap x (Y.presheaf.stalkSpecializes (f.base.map_specializes h) y) =
      X.presheaf.stalkSpecializes h (f.stalkMap x' y) := by
  exact SourceStack.StalkMaps.stalkSpecializes_stalkMap_apply f x x' h y

theorem hilbert_stalkMap_congr
    (f g : X ⟶ Y) (hfg : f = g) (x x' : X) (hxx' : x = x') :
    f.stalkMap x ≫ (X.presheaf.stalkCongr (Inseparable.of_eq hxx')).hom =
      (Y.presheaf.stalkCongr
        (Inseparable.of_eq <| hfg ▸ hxx' ▸ rfl)).hom ≫
        g.stalkMap x' := by
  exact SourceStack.StalkMaps.stalkMap_congr f g hfg x x' hxx'

theorem hilbert_stalkMap_congr_hom
    (f g : X ⟶ Y) (hfg : f = g) (x : X) :
    f.stalkMap x =
      (Y.presheaf.stalkCongr (Inseparable.of_eq <| hfg ▸ rfl)).hom ≫
        g.stalkMap x := by
  exact SourceStack.StalkMaps.stalkMap_congr_hom f g hfg x

theorem hilbert_stalkMap_congr_point
    (f : X ⟶ Y) (x x' : X) (hxx' : x = x') :
    f.stalkMap x ≫ (X.presheaf.stalkCongr (Inseparable.of_eq hxx')).hom =
      (Y.presheaf.stalkCongr (Inseparable.of_eq <| hxx' ▸ rfl)).hom ≫
        f.stalkMap x' := by
  exact SourceStack.StalkMaps.stalkMap_congr_point f x x' hxx'

theorem hilbert_stalkMap_hom_inv
    (e : X ≅ Y) (y : Y) :
    e.hom.stalkMap (e.inv.base y) ≫ e.inv.stalkMap y =
      (Y.presheaf.stalkCongr (Inseparable.of_eq (by simp))).hom := by
  exact SourceStack.StalkMaps.stalkMap_hom_inv e y

theorem hilbert_stalkMap_hom_inv_apply
    (e : X ≅ Y) (y : Y) (z : Y.presheaf.stalk (e.hom.base (e.inv.base y))) :
    e.inv.stalkMap y (e.hom.stalkMap (e.inv.base y) z) =
      (Y.presheaf.stalkCongr (Inseparable.of_eq (by simp))).hom z := by
  exact SourceStack.StalkMaps.stalkMap_hom_inv_apply e y z

theorem hilbert_stalkMap_inv_hom
    (e : X ≅ Y) (x : X) :
    e.inv.stalkMap (e.hom.base x) ≫ e.hom.stalkMap x =
      (X.presheaf.stalkCongr (Inseparable.of_eq (by simp))).hom := by
  exact SourceStack.StalkMaps.stalkMap_inv_hom e x

theorem hilbert_stalkMap_inv_hom_apply
    (e : X ≅ Y) (x : X) (y : X.presheaf.stalk (e.inv.base (e.hom.base x))) :
    e.hom.stalkMap x (e.inv.stalkMap (e.hom.base x) y) =
      (X.presheaf.stalkCongr (Inseparable.of_eq (by simp))).hom y := by
  exact SourceStack.StalkMaps.stalkMap_inv_hom_apply e x y

theorem hilbert_stalkMap_germ
    (f : X ⟶ Y) (U : Y.Opens) (x : X) (hx : f.base x ∈ U) :
    Y.presheaf.germ U (f.base x) hx ≫ f.stalkMap x =
      f.app U ≫ X.presheaf.germ (f ⁻¹ᵁ U) x hx := by
  exact SourceStack.StalkMaps.stalkMap_germ f U x hx

theorem hilbert_stalkMap_germ_apply
    (f : X ⟶ Y) (U : Y.Opens) (x : X) (hx : f.base x ∈ U) (y : Γ(Y, U)) :
    f.stalkMap x (Y.presheaf.germ U (f.base x) hx y) =
      X.presheaf.germ (f ⁻¹ᵁ U) x hx (f.app U y) := by
  exact SourceStack.StalkMaps.stalkMap_germ_apply f U x hx y

end StalkMaps

namespace PullbackCarrier

universe u

variable {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}

theorem hilbert_triplet_mk'_exists
    (x : X) (y : Y) (h : f.base x = g.base y) :
    Nonempty (Scheme.Pullback.Triplet f g) := by
  exact SourceStack.PullbackCarrier.triplet_mk'_exists x y h

theorem hilbert_triplet_tensor_nontrivial
    (T : Scheme.Pullback.Triplet f g) :
    Nontrivial T.tensor := by
  exact SourceStack.PullbackCarrier.triplet_tensor_nontrivial T

theorem hilbert_triplet_tensorInl_exists
    (T : Scheme.Pullback.Triplet f g) :
    Nonempty (X.residueField T.x ⟶ T.tensor) := by
  exact SourceStack.PullbackCarrier.triplet_tensorInl_exists T

theorem hilbert_triplet_tensorInr_exists
    (T : Scheme.Pullback.Triplet f g) :
    Nonempty (Y.residueField T.y ⟶ T.tensor) := by
  exact SourceStack.PullbackCarrier.triplet_tensorInr_exists T

theorem hilbert_triplet_Spec_map_tensor_isPullback
    (T : Scheme.Pullback.Triplet f g) :
    IsPullback
      (Spec.map T.tensorInl) (Spec.map T.tensorInr)
      (Spec.map ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x))
      (Spec.map ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y)) := by
  exact SourceStack.PullbackCarrier.triplet_Spec_map_tensor_isPullback T

theorem hilbert_triplet_Spec_map_tensorInl_fromSpecResidueField
    (T : Scheme.Pullback.Triplet f g) :
    (Spec.map T.tensorInl ≫ X.fromSpecResidueField T.x) ≫ f =
      (Spec.map T.tensorInr ≫ Y.fromSpecResidueField T.y) ≫ g := by
  exact SourceStack.PullbackCarrier.triplet_Spec_map_tensorInl_fromSpecResidueField T

theorem hilbert_triplet_SpecTensorTo_exists
    (T : Scheme.Pullback.Triplet f g) :
    Nonempty (Spec T.tensor ⟶ pullback f g) := by
  exact SourceStack.PullbackCarrier.triplet_SpecTensorTo_exists T

theorem hilbert_triplet_specTensorTo_base_fst
    (T : Scheme.Pullback.Triplet f g) (p : Spec T.tensor) :
    (pullback.fst f g).base (T.SpecTensorTo.base p) = T.x := by
  exact SourceStack.PullbackCarrier.triplet_specTensorTo_base_fst T p

theorem hilbert_triplet_specTensorTo_base_snd
    (T : Scheme.Pullback.Triplet f g) (p : Spec T.tensor) :
    (pullback.snd f g).base (T.SpecTensorTo.base p) = T.y := by
  exact SourceStack.PullbackCarrier.triplet_specTensorTo_base_snd T p

theorem hilbert_triplet_specTensorTo_fst
    (T : Scheme.Pullback.Triplet f g) :
    T.SpecTensorTo ≫ pullback.fst f g =
      Spec.map T.tensorInl ≫ X.fromSpecResidueField T.x := by
  exact SourceStack.PullbackCarrier.triplet_specTensorTo_fst T

theorem hilbert_triplet_specTensorTo_snd
    (T : Scheme.Pullback.Triplet f g) :
    T.SpecTensorTo ≫ pullback.snd f g =
      Spec.map T.tensorInr ≫ Y.fromSpecResidueField T.y := by
  exact SourceStack.PullbackCarrier.triplet_specTensorTo_snd T

theorem hilbert_triplet_ofPoint_exists
    (t : ↑(pullback f g)) :
    Nonempty (Scheme.Pullback.Triplet f g) := by
  exact SourceStack.PullbackCarrier.triplet_ofPoint_exists t

theorem hilbert_triplet_ofPoint_SpecTensorTo
    (T : Scheme.Pullback.Triplet f g) (p : Spec T.tensor) :
    Scheme.Pullback.Triplet.ofPoint (T.SpecTensorTo.base p) = T := by
  exact SourceStack.PullbackCarrier.triplet_ofPoint_SpecTensorTo T p

theorem hilbert_residueFieldCongr_inv_residueFieldMap_ofPoint
    (t : ↑(pullback f g)) :
    ((S.residueFieldCongr (Scheme.Pullback.Triplet.ofPoint t).hx).inv ≫
        f.residueFieldMap (Scheme.Pullback.Triplet.ofPoint t).x) ≫
      (pullback.fst f g).residueFieldMap t =
    ((S.residueFieldCongr (Scheme.Pullback.Triplet.ofPoint t).hy).inv ≫
        g.residueFieldMap (Scheme.Pullback.Triplet.ofPoint t).y) ≫
      (pullback.snd f g).residueFieldMap t := by
  exact SourceStack.PullbackCarrier.residueFieldCongr_inv_residueFieldMap_ofPoint t

theorem hilbert_ofPointTensor_exists
    (t : ↑(pullback f g)) :
    Nonempty ((Scheme.Pullback.Triplet.ofPoint t).tensor ⟶
      (pullback f g).residueField t) := by
  exact SourceStack.PullbackCarrier.ofPointTensor_exists t

theorem hilbert_ofPointTensor_SpecTensorTo
    (t : ↑(pullback f g)) :
    Spec.map (Scheme.Pullback.ofPointTensor t) ≫
        (Scheme.Pullback.Triplet.ofPoint t).SpecTensorTo =
      (pullback f g).fromSpecResidueField t := by
  exact SourceStack.PullbackCarrier.ofPointTensor_SpecTensorTo t

theorem hilbert_SpecTensorTo_SpecOfPoint
    (t : ↑(pullback f g)) :
    (Scheme.Pullback.Triplet.ofPoint t).SpecTensorTo.base
        (Scheme.Pullback.SpecOfPoint t) = t := by
  exact SourceStack.PullbackCarrier.SpecTensorTo_SpecOfPoint t

theorem hilbert_tensorCongr_SpecTensorTo
    {T T' : Scheme.Pullback.Triplet f g} (h : T = T') :
    Spec.map (Scheme.Pullback.Triplet.tensorCongr h).hom ≫ T.SpecTensorTo =
      T'.SpecTensorTo := by
  exact SourceStack.PullbackCarrier.tensorCongr_SpecTensorTo h

theorem hilbert_carrierEquiv_eq_iff
    {T₁ T₂ : Σ T : Scheme.Pullback.Triplet f g, Spec T.tensor} :
    T₁ = T₂ ↔
      ∃ e : T₁.1 = T₂.1,
        (Spec.map (Scheme.Pullback.Triplet.tensorCongr e).inv).base T₁.2 =
          T₂.2 := by
  exact SourceStack.PullbackCarrier.carrierEquiv_eq_iff

theorem hilbert_carrierEquiv_exists :
    Nonempty (↑(pullback f g) ≃
      Σ T : Scheme.Pullback.Triplet f g, Spec T.tensor) := by
  exact SourceStack.PullbackCarrier.carrierEquiv_exists

theorem hilbert_carrierEquiv_symm_fst
    (T : Scheme.Pullback.Triplet f g) (p : Spec T.tensor) :
    (pullback.fst f g).base (Scheme.Pullback.carrierEquiv.symm ⟨T, p⟩) = T.x := by
  exact SourceStack.PullbackCarrier.carrierEquiv_symm_fst T p

theorem hilbert_carrierEquiv_symm_snd
    (T : Scheme.Pullback.Triplet f g) (p : Spec T.tensor) :
    (pullback.snd f g).base (Scheme.Pullback.carrierEquiv.symm ⟨T, p⟩) = T.y := by
  exact SourceStack.PullbackCarrier.carrierEquiv_symm_snd T p

theorem hilbert_triplet_exists_preimage
    (T : Scheme.Pullback.Triplet f g) :
    ∃ t : ↑(pullback f g),
      (pullback.fst f g).base t = T.x ∧
        (pullback.snd f g).base t = T.y := by
  exact SourceStack.PullbackCarrier.triplet_exists_preimage T

theorem hilbert_exists_preimage_pullback
    (x : X) (y : Y) (h : f.base x = g.base y) :
    ∃ z : ↑(pullback f g),
      (pullback.fst f g).base z = x ∧
        (pullback.snd f g).base z = y := by
  exact SourceStack.PullbackCarrier.exists_preimage_pullback x y h

theorem hilbert_range_fst
    (f : X ⟶ S) (g : Y ⟶ S) :
    Set.range (pullback.fst f g).base = f.base ⁻¹' Set.range g.base := by
  exact SourceStack.PullbackCarrier.range_fst f g

theorem hilbert_range_snd
    (f : X ⟶ S) (g : Y ⟶ S) :
    Set.range (pullback.snd f g).base = g.base ⁻¹' Set.range f.base := by
  exact SourceStack.PullbackCarrier.range_snd f g

theorem hilbert_range_fst_comp
    (f : X ⟶ S) (g : Y ⟶ S) :
    Set.range (pullback.fst f g ≫ f).base =
      Set.range f.base ∩ Set.range g.base := by
  exact SourceStack.PullbackCarrier.range_fst_comp f g

theorem hilbert_range_snd_comp
    (f : X ⟶ S) (g : Y ⟶ S) :
    Set.range (pullback.snd f g ≫ g).base =
      Set.range f.base ∩ Set.range g.base := by
  exact SourceStack.PullbackCarrier.range_snd_comp f g

theorem hilbert_range_map
    {X' Y' S' : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (f' : X' ⟶ S') (g' : Y' ⟶ S') (i₁ : X ⟶ X')
    (i₂ : Y ⟶ Y') (i₃ : S ⟶ S')
    (e₁ : f ≫ i₃ = i₁ ≫ f') (e₂ : g ≫ i₃ = i₂ ≫ g') [Mono i₃] :
    Set.range (pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂).base =
      (pullback.fst f' g').base ⁻¹' Set.range i₁.base ∩
        (pullback.snd f' g').base ⁻¹' Set.range i₂.base := by
  exact SourceStack.PullbackCarrier.range_map f g f' g' i₁ i₂ i₃ e₁ e₂

theorem hilbert_surjective_stableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange (@Surjective) := by
  exact SourceStack.PullbackCarrier.surjective_stableUnderBaseChange

end PullbackCarrier

namespace SurjectiveOnStalks

universe u

variable {X Y Z S : Scheme.{u}}

theorem hilbert_stalkMap_surjective
    (f : X ⟶ Y) [AlgebraicGeometry.SurjectiveOnStalks f] (x : X) :
    Function.Surjective (f.stalkMap x) := by
  exact SourceStack.SurjectiveOnStalks.stalkMap_surjective f x

theorem hilbert_openImmersion_surjectiveOnStalks
    (f : X ⟶ Y) [IsOpenImmersion f] :
    AlgebraicGeometry.SurjectiveOnStalks f := by
  exact SourceStack.SurjectiveOnStalks.openImmersion_surjectiveOnStalks f

theorem hilbert_surjectiveOnStalks_multiplicative :
    MorphismProperty.IsMultiplicative (@AlgebraicGeometry.SurjectiveOnStalks) := by
  exact SourceStack.SurjectiveOnStalks.surjectiveOnStalks_multiplicative

theorem hilbert_surjectiveOnStalks_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicGeometry.SurjectiveOnStalks f]
    [AlgebraicGeometry.SurjectiveOnStalks g] :
    AlgebraicGeometry.SurjectiveOnStalks (f ≫ g) := by
  exact SourceStack.SurjectiveOnStalks.surjectiveOnStalks_comp f g

theorem hilbert_surjectiveOnStalks_eq_stalkwise :
    @AlgebraicGeometry.SurjectiveOnStalks =
      AlgebraicGeometry.stalkwise (Function.Surjective ·) := by
  exact SourceStack.SurjectiveOnStalks.surjectiveOnStalks_eq_stalkwise

theorem hilbert_surjectiveOnStalks_isLocalAtTarget :
    IsLocalAtTarget (@AlgebraicGeometry.SurjectiveOnStalks) := by
  exact SourceStack.SurjectiveOnStalks.surjectiveOnStalks_isLocalAtTarget

theorem hilbert_surjectiveOnStalks_isLocalAtSource :
    IsLocalAtSource (@AlgebraicGeometry.SurjectiveOnStalks) := by
  exact SourceStack.SurjectiveOnStalks.surjectiveOnStalks_isLocalAtSource

theorem hilbert_surjectiveOnStalks_Spec_iff
    {R S : CommRingCat.{u}} {φ : R ⟶ S} :
    AlgebraicGeometry.SurjectiveOnStalks (Spec.map φ) ↔
      RingHom.SurjectiveOnStalks φ.hom := by
  exact SourceStack.SurjectiveOnStalks.surjectiveOnStalks_Spec_iff

theorem hilbert_surjectiveOnStalks_iff_of_isAffine
    {f : X ⟶ Y} [IsAffine X] [IsAffine Y] :
    AlgebraicGeometry.SurjectiveOnStalks f ↔
      RingHom.SurjectiveOnStalks (f.app ⊤).hom := by
  exact SourceStack.SurjectiveOnStalks.surjectiveOnStalks_iff_of_isAffine

theorem hilbert_surjectiveOnStalks_of_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicGeometry.SurjectiveOnStalks (f ≫ g)] :
    AlgebraicGeometry.SurjectiveOnStalks f := by
  exact SourceStack.SurjectiveOnStalks.surjectiveOnStalks_of_comp f g

theorem hilbert_surjectiveOnStalks_stableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange (@AlgebraicGeometry.SurjectiveOnStalks) := by
  exact SourceStack.SurjectiveOnStalks.surjectiveOnStalks_stableUnderBaseChange

theorem hilbert_surjectiveOnStalks_isEmbedding_pullback
    (f : X ⟶ S) (g : Y ⟶ S)
    [AlgebraicGeometry.SurjectiveOnStalks g] :
    IsEmbedding (fun x ↦ ((pullback.fst f g).base x, (pullback.snd f g).base x)) := by
  exact SourceStack.SurjectiveOnStalks.surjectiveOnStalks_isEmbedding_pullback f g

end SurjectiveOnStalks

namespace FieldTheory

universe u v w

variable (F E : Type*) [Field F] [Field E] [Algebra F E]

theorem hilbert_primitive_element_exists
    [FiniteDimensional F E] [Algebra.IsSeparable F E] :
    ∃ α : E, F⟮α⟯ = ⊤ := by
  exact SourceStack.FieldTheory.primitive_element_exists F E

theorem hilbert_primitive_element_exists_of_finite_intermediateField
    [Finite (IntermediateField F E)] (K : IntermediateField F E) :
    ∃ α : E, F⟮α⟯ = K := by
  exact SourceStack.FieldTheory.primitive_element_exists_of_finite_intermediateField F E K

theorem hilbert_finiteDimensional_of_exists_primitive_element
    [Algebra.IsAlgebraic F E]
    (h : ∃ α : E, F⟮α⟯ = ⊤) :
    FiniteDimensional F E := by
  exact SourceStack.FieldTheory.finiteDimensional_of_exists_primitive_element F E h

theorem hilbert_finite_intermediateField_of_exists_primitive_element
    [Algebra.IsAlgebraic F E]
    (h : ∃ α : E, F⟮α⟯ = ⊤) :
    Finite (IntermediateField F E) := by
  exact SourceStack.FieldTheory.finite_intermediateField_of_exists_primitive_element F E h

theorem hilbert_exists_primitive_element_iff_finite_intermediateField :
    (Algebra.IsAlgebraic F E ∧ ∃ α : E, F⟮α⟯ = ⊤) ↔
      Finite (IntermediateField F E) := by
  exact SourceStack.FieldTheory.exists_primitive_element_iff_finite_intermediateField F E

theorem hilbert_adjoin_finiteDimensional {x : E} (hx : IsIntegral F x) :
    FiniteDimensional F F⟮x⟯ := by
  exact SourceStack.FieldTheory.adjoin_finiteDimensional F E hx

theorem hilbert_finiteDimensional_adjoin {S : Set E} [Finite S]
    (hS : ∀ x ∈ S, IsIntegral F x) :
    FiniteDimensional F (IntermediateField.adjoin F S) := by
  exact SourceStack.FieldTheory.finiteDimensional_adjoin F E hS

theorem hilbert_adjoin_finrank_eq_minpoly_natDegree {x : E} (hx : IsIntegral F x) :
    Module.finrank F F⟮x⟯ = (minpoly F x).natDegree := by
  exact SourceStack.FieldTheory.adjoin_finrank_eq_minpoly_natDegree F E hx

theorem hilbert_isSeparable_adjoin_simple_iff_isSeparable {x : E} :
    Algebra.IsSeparable F F⟮x⟯ ↔ IsSeparable F x := by
  exact SourceStack.FieldTheory.isSeparable_adjoin_simple_iff_isSeparable F E

theorem hilbert_isSeparable_adjoin_pair_of_isSeparable {x y : E}
    (hx : IsSeparable F x) (hy : IsSeparable F y) :
    Algebra.IsSeparable F F⟮x, y⟯ := by
  exact SourceStack.FieldTheory.isSeparable_adjoin_pair_of_isSeparable F E hx hy

theorem hilbert_isSeparable_adjoin_iff_isSeparable {S : Set E} :
    Algebra.IsSeparable F (IntermediateField.adjoin F S) ↔
      ∀ x ∈ S, IsSeparable F x := by
  exact SourceStack.FieldTheory.isSeparable_adjoin_iff_isSeparable F E

theorem hilbert_minpoly_natDegree_le
    (x : E) [FiniteDimensional F E] :
    (minpoly F x).natDegree ≤ Module.finrank F E := by
  exact SourceStack.FieldTheory.minpoly_natDegree_le F E x

theorem hilbert_minpoly_degree_dvd {x : E} (hx : IsIntegral F x) :
    (minpoly F x).natDegree ∣ Module.finrank F E := by
  exact SourceStack.FieldTheory.minpoly_degree_dvd F E hx

theorem hilbert_minpoly_natDegree_le_of_aeval_eq_zero
    (x : E) {p : F[X]} (hp0 : p ≠ 0)
    (hp : Polynomial.aeval x p = 0) :
    (minpoly F x).natDegree ≤ p.natDegree := by
  exact SourceStack.FieldTheory.minpoly_natDegree_le_of_aeval_eq_zero F E x hp0 hp

theorem hilbert_minpoly_natDegree_le_derivative_of_aeval_eq_zero
    (x : E) {p : F[X]} (hpder : p.derivative ≠ 0)
    (hp : Polynomial.aeval x p.derivative = 0) :
    (minpoly F x).natDegree ≤ p.derivative.natDegree := by
  exact SourceStack.FieldTheory.minpoly_natDegree_le_derivative_of_aeval_eq_zero F E x hpder hp

theorem hilbert_minpoly_natDegree_lt_of_derivative_root
    (x : E) {p : F[X]} (hpdeg : p.natDegree ≠ 0)
    (hpder : p.derivative ≠ 0)
    (hp : Polynomial.aeval x p.derivative = 0) :
    (minpoly F x).natDegree < p.natDegree := by
  exact SourceStack.FieldTheory.minpoly_natDegree_lt_of_derivative_root F E x hpdeg hpder hp

theorem hilbert_galois_iff :
    IsGalois F E ↔ Algebra.IsSeparable F E ∧ Normal F E := by
  exact SourceStack.FieldTheory.galois_iff F E

theorem hilbert_isGalois_integral [IsGalois F E] (x : E) :
    IsIntegral F x := by
  exact SourceStack.FieldTheory.isGalois_integral F E x

theorem hilbert_isGalois_separable [IsGalois F E] (x : E) :
    IsSeparable F x := by
  exact SourceStack.FieldTheory.isGalois_separable F E x

theorem hilbert_isGalois_splits [IsGalois F E] (x : E) :
    Polynomial.Splits (algebraMap F E) (minpoly F x) := by
  exact SourceStack.FieldTheory.isGalois_splits F E x

theorem hilbert_isGalois_card_aut_eq_finrank
    [FiniteDimensional F E] [IsGalois F E] :
    Fintype.card (E ≃ₐ[F] E) = Module.finrank F E := by
  exact SourceStack.FieldTheory.isGalois_card_aut_eq_finrank F E

theorem hilbert_normal_criterion :
    Normal F E ↔
      ∀ x : E, IsIntegral F x ∧ Polynomial.Splits (algebraMap F E) (minpoly F x) := by
  exact SourceStack.FieldTheory.normal_criterion F E

theorem hilbert_normal_isIntegral [Normal F E] (x : E) :
    IsIntegral F x := by
  exact SourceStack.FieldTheory.normal_isIntegral F E x

theorem hilbert_normal_splits [Normal F E] (x : E) :
    Polynomial.Splits (algebraMap F E) (minpoly F x) := by
  exact SourceStack.FieldTheory.normal_splits F E x

theorem hilbert_normal_exists_isSplittingField
    [Normal F E] [FiniteDimensional F E] :
    ∃ p : F[X], Polynomial.IsSplittingField F E p := by
  exact SourceStack.FieldTheory.normal_exists_isSplittingField F E

theorem hilbert_minpoly_exists_algEquiv_of_root
    [Normal F E] {x y : E} (hy : IsAlgebraic F y)
    (h_ev : (Polynomial.aeval x) (minpoly F y) = 0) :
    ∃ σ : E ≃ₐ[F] E, σ x = y := by
  exact SourceStack.FieldTheory.minpoly_exists_algEquiv_of_root F E hy h_ev

theorem hilbert_minpoly_exists_algEquiv_of_root'
    [Normal F E] {x y : E} (hy : IsAlgebraic F y)
    (h_ev : (Polynomial.aeval x) (minpoly F y) = 0) :
    ∃ σ : E ≃ₐ[F] E, σ y = x := by
  exact SourceStack.FieldTheory.minpoly_exists_algEquiv_of_root' F E hy h_ev

variable (K : Type*) [Field K] [Algebra F K] [Algebra K E]
variable [IsScalarTower F K E]

theorem hilbert_restrictNormalHom_surjective
    [Normal F K] [Normal F E] :
    Function.Surjective (AlgEquiv.restrictNormalHom K :
      (E ≃ₐ[F] E) → K ≃ₐ[F] K) := by
  exact SourceStack.FieldTheory.restrictNormalHom_surjective F E K

end FieldTheory

namespace PolynomialMaps

universe u v

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]

theorem hilbert_derivative_rootSet_finite (p : F[X]) :
    (p.derivative.rootSet E).Finite := by
  exact SourceStack.PolynomialMaps.derivative_rootSet_finite F E p

theorem hilbert_mem_derivative_rootSet_iff {p : F[X]} (hpder : p.derivative ≠ 0)
    (x : E) :
    x ∈ p.derivative.rootSet E ↔ Polynomial.aeval x p.derivative = 0 := by
  exact SourceStack.PolynomialMaps.mem_derivative_rootSet_iff F E hpder x

theorem hilbert_polynomial_image_finite {S : Set E} (hS : S.Finite) (p : F[X]) :
    ((fun x : E => Polynomial.aeval x p) '' S).Finite := by
  exact SourceStack.PolynomialMaps.polynomial_image_finite F E hS p

theorem hilbert_imageSet_finite {S : Set E} (hS : S.Finite) (p : F[X]) :
    (SourceStack.PolynomialMaps.imageSet F E S p).Finite := by
  exact SourceStack.PolynomialMaps.imageSet_finite F E hS p

theorem hilbert_mem_imageSet_of_mem {S : Set E} {x : E} (p : F[X]) (hx : x ∈ S) :
    Polynomial.aeval x p ∈ SourceStack.PolynomialMaps.imageSet F E S p := by
  exact SourceStack.PolynomialMaps.mem_imageSet_of_mem F E p hx

theorem hilbert_imageSet_mono {S T : Set E} (hST : S ⊆ T) (p : F[X]) :
    SourceStack.PolynomialMaps.imageSet F E S p ⊆
      SourceStack.PolynomialMaps.imageSet F E T p := by
  exact SourceStack.PolynomialMaps.imageSet_mono F E hST p

theorem hilbert_criticalValueSet_finite (p : F[X]) :
    (SourceStack.PolynomialMaps.criticalValueSet F E p).Finite := by
  exact SourceStack.PolynomialMaps.criticalValueSet_finite F E p

theorem hilbert_mem_criticalValueSet_of_mem_derivative_root
    {p : F[X]} {x : E} (hx : x ∈ p.derivative.rootSet E) :
    Polynomial.aeval x p ∈ SourceStack.PolynomialMaps.criticalValueSet F E p := by
  exact SourceStack.PolynomialMaps.mem_criticalValueSet_of_mem_derivative_root F E hx

theorem hilbert_mem_criticalValueSet_of_derivative_aeval_eq_zero
    {p : F[X]} (hpder : p.derivative ≠ 0) {x : E}
    (hx : Polynomial.aeval x p.derivative = 0) :
    Polynomial.aeval x p ∈ SourceStack.PolynomialMaps.criticalValueSet F E p := by
  exact SourceStack.PolynomialMaps.mem_criticalValueSet_of_derivative_aeval_eq_zero
    F E hpder hx

theorem hilbert_polynomial_image_union_derivative_root_image_finite
    {S : Set E} (hS : S.Finite) (p : F[X]) :
    (((fun x : E => Polynomial.aeval x p) '' S) ∪
      ((fun x : E => Polynomial.aeval x p) '' p.derivative.rootSet E)).Finite := by
  exact SourceStack.PolynomialMaps.polynomial_image_union_derivative_root_image_finite F E hS p

theorem hilbert_replacementSet_finite {S : Set E} (hS : S.Finite) (p : F[X]) :
    (SourceStack.PolynomialMaps.replacementSet F E S p).Finite := by
  exact SourceStack.PolynomialMaps.replacementSet_finite F E hS p

theorem hilbert_imageSet_subset_replacementSet (S : Set E) (p : F[X]) :
    SourceStack.PolynomialMaps.imageSet F E S p ⊆
      SourceStack.PolynomialMaps.replacementSet F E S p := by
  exact SourceStack.PolynomialMaps.imageSet_subset_replacementSet F E S p

theorem hilbert_criticalValueSet_subset_replacementSet (S : Set E) (p : F[X]) :
    SourceStack.PolynomialMaps.criticalValueSet F E p ⊆
      SourceStack.PolynomialMaps.replacementSet F E S p := by
  exact SourceStack.PolynomialMaps.criticalValueSet_subset_replacementSet F E S p

theorem hilbert_mem_replacementSet_iff {S : Set E} (p : F[X]) (y : E) :
    y ∈ SourceStack.PolynomialMaps.replacementSet F E S p ↔
      y ∈ SourceStack.PolynomialMaps.imageSet F E S p ∨
        y ∈ SourceStack.PolynomialMaps.criticalValueSet F E p := by
  exact SourceStack.PolynomialMaps.mem_replacementSet_iff F E p y

theorem hilbert_mem_replacementSet_of_mem_imageSet
    {S : Set E} {p : F[X]} {y : E}
    (hy : y ∈ SourceStack.PolynomialMaps.imageSet F E S p) :
    y ∈ SourceStack.PolynomialMaps.replacementSet F E S p := by
  exact SourceStack.PolynomialMaps.mem_replacementSet_of_mem_imageSet F E hy

theorem hilbert_mem_replacementSet_of_mem_criticalValueSet
    {S : Set E} {p : F[X]} {y : E}
    (hy : y ∈ SourceStack.PolynomialMaps.criticalValueSet F E p) :
    y ∈ SourceStack.PolynomialMaps.replacementSet F E S p := by
  exact SourceStack.PolynomialMaps.mem_replacementSet_of_mem_criticalValueSet F E hy

theorem hilbert_replacementSet_mono {S T : Set E} (hST : S ⊆ T) (p : F[X]) :
    SourceStack.PolynomialMaps.replacementSet F E S p ⊆
      SourceStack.PolynomialMaps.replacementSet F E T p := by
  exact SourceStack.PolynomialMaps.replacementSet_mono F E hST p

theorem hilbert_not_mem_replacementSet_iff {S : Set E} (p : F[X]) (y : E) :
    y ∉ SourceStack.PolynomialMaps.replacementSet F E S p ↔
      y ∉ SourceStack.PolynomialMaps.imageSet F E S p ∧
        y ∉ SourceStack.PolynomialMaps.criticalValueSet F E p := by
  exact SourceStack.PolynomialMaps.not_mem_replacementSet_iff F E p y

theorem hilbert_aeval_ne_of_not_mem_imageSet {S : Set E} {p : F[X]} {x y : E}
    (hy : y ∉ SourceStack.PolynomialMaps.imageSet F E S p) (hx : x ∈ S) :
    Polynomial.aeval x p ≠ y := by
  exact SourceStack.PolynomialMaps.aeval_ne_of_not_mem_imageSet F E hy hx

theorem hilbert_aeval_ne_of_not_mem_replacementSet
    {S : Set E} {p : F[X]} {x y : E}
    (hy : y ∉ SourceStack.PolynomialMaps.replacementSet F E S p) (hx : x ∈ S) :
    Polynomial.aeval x p ≠ y := by
  exact SourceStack.PolynomialMaps.aeval_ne_of_not_mem_replacementSet F E hy hx

theorem hilbert_derivative_aeval_ne_zero_of_value_not_mem_criticalValueSet
    {p : F[X]} (hpder : p.derivative ≠ 0) {x y : E}
    (hy : y ∉ SourceStack.PolynomialMaps.criticalValueSet F E p)
    (hxy : Polynomial.aeval x p = y) :
    Polynomial.aeval x p.derivative ≠ 0 := by
  exact SourceStack.PolynomialMaps.derivative_aeval_ne_zero_of_value_not_mem_criticalValueSet
    F E hpder hy hxy

theorem hilbert_derivative_aeval_ne_zero_of_value_not_mem_replacementSet
    {S : Set E} {p : F[X]} (hpder : p.derivative ≠ 0) {x y : E}
    (hy : y ∉ SourceStack.PolynomialMaps.replacementSet F E S p)
    (hxy : Polynomial.aeval x p = y) :
    Polynomial.aeval x p.derivative ≠ 0 := by
  exact SourceStack.PolynomialMaps.derivative_aeval_ne_zero_of_value_not_mem_replacementSet
    F E hpder hy hxy

theorem hilbert_aeval_comp (p q : F[X]) (x : E) :
    Polynomial.aeval x (p.comp q) =
      Polynomial.aeval (Polynomial.aeval x q) p := by
  exact SourceStack.PolynomialMaps.aeval_comp F E p q x

theorem hilbert_derivative_comp (p q : F[X]) :
    (p.comp q).derivative = q.derivative * p.derivative.comp q := by
  exact SourceStack.PolynomialMaps.derivative_comp F p q

theorem hilbert_aeval_derivative_comp (p q : F[X]) (x : E) :
    Polynomial.aeval x (p.comp q).derivative =
      Polynomial.aeval x q.derivative *
        Polynomial.aeval (Polynomial.aeval x q) p.derivative := by
  exact SourceStack.PolynomialMaps.aeval_derivative_comp F E p q x

theorem hilbert_derivative_aeval_comp_ne_zero
    (p q : F[X]) {x : E}
    (hq : Polynomial.aeval x q.derivative ≠ 0)
    (hp : Polynomial.aeval (Polynomial.aeval x q) p.derivative ≠ 0) :
    Polynomial.aeval x (p.comp q).derivative ≠ 0 := by
  exact SourceStack.PolynomialMaps.derivative_aeval_comp_ne_zero F E p q hq hp

theorem hilbert_aeval_comp_ne_target_of_mapsTo_and_outer_separates
    {S T : Set E} {p q : F[X]} {β x : E}
    (hmap : ∀ z ∈ S, Polynomial.aeval z q ∈ T)
    (hsep : ∀ y ∈ T,
      Polynomial.aeval y p ≠ Polynomial.aeval (Polynomial.aeval β q) p)
    (hx : x ∈ S) :
    Polynomial.aeval x (p.comp q) ≠ Polynomial.aeval β (p.comp q) := by
  exact SourceStack.PolynomialMaps.aeval_comp_ne_target_of_mapsTo_and_outer_separates
    F E hmap hsep hx

theorem hilbert_derivative_aeval_comp_ne_zero_of_target_preimage
    (p q : F[X]) {β x : E}
    (hq : ∀ z : E,
      Polynomial.aeval z (p.comp q) = Polynomial.aeval β (p.comp q) →
        Polynomial.aeval z q.derivative ≠ 0)
    (hp : ∀ y : E,
      Polynomial.aeval y p = Polynomial.aeval (Polynomial.aeval β q) p →
        Polynomial.aeval y p.derivative ≠ 0)
    (hx : Polynomial.aeval x (p.comp q) = Polynomial.aeval β (p.comp q)) :
    Polynomial.aeval x (p.comp q).derivative ≠ 0 := by
  exact SourceStack.PolynomialMaps.derivative_aeval_comp_ne_zero_of_target_preimage
    F E p q hq hp hx

end PolynomialMaps

namespace PolynomialSeparation

open SourceStack.PolynomialMaps
open SourceStack.PolynomialSeparation

universe u v

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
variable {S : Set E} {β : E}
variable (P : PolynomialSeparationStep F E S β)

theorem hilbert_polynomialSeparation_replacementSet_finite
    (hS : S.Finite) :
    (replacementSet F E S P.polynomial).Finite := by
  exact SourceStack.PolynomialSeparation.PolynomialSeparationStep.replacementSet_finite
    P hS

theorem hilbert_polynomialSeparation_aeval_ne_target_of_mem
    {x : E} (hx : x ∈ S) :
    Polynomial.aeval x P.polynomial ≠ Polynomial.aeval β P.polynomial := by
  exact SourceStack.PolynomialSeparation.PolynomialSeparationStep.aeval_ne_target_of_mem
    P hx

theorem hilbert_polynomialSeparation_target_not_mem_criticalValueSet :
    Polynomial.aeval β P.polynomial ∉
      criticalValueSet F E P.polynomial := by
  exact SourceStack.PolynomialSeparation.PolynomialSeparationStep.target_not_mem_criticalValueSet
    P

theorem hilbert_polynomialSeparation_derivative_ne_zero_at_preimage
    {x : E} (hx : Polynomial.aeval x P.polynomial =
      Polynomial.aeval β P.polynomial) :
    Polynomial.aeval x P.polynomial.derivative ≠ 0 := by
  exact SourceStack.PolynomialSeparation.PolynomialSeparationStep.derivative_ne_zero_at_preimage
    P hx

theorem hilbert_polynomialSeparation_separates_and_noncritical :
    (∀ x ∈ S, Polynomial.aeval x P.polynomial ≠
        Polynomial.aeval β P.polynomial) ∧
      ∀ x : E, Polynomial.aeval x P.polynomial =
        Polynomial.aeval β P.polynomial →
          Polynomial.aeval x P.polynomial.derivative ≠ 0 := by
  exact SourceStack.PolynomialSeparation.PolynomialSeparationStep.separates_and_noncritical
    P

end PolynomialSeparation

namespace P1PolynomialSeparation

open SourceStack.PolynomialMaps
open SourceStack.P1PolynomialSeparation

universe u v

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]

theorem hilbert_p1PolynomialSeparation_affinePolynomialPointMap_eq_iff
    (p : F[X]) (x y : E) :
    affinePolynomialPointMap F E p x = affinePolynomialPointMap F E p y ↔
      Polynomial.aeval x p = Polynomial.aeval y p := by
  exact SourceStack.P1PolynomialSeparation.affinePolynomialPointMap_eq_iff
    F E p x y

theorem hilbert_p1PolynomialSeparation_affinePolynomialPointMap_ne_target_of_aeval_ne
    {p : F[X]} {x β : E}
    (h : Polynomial.aeval x p ≠ Polynomial.aeval β p) :
    affinePolynomialPointMap F E p x ≠
      SourceStack.ProjectiveLine.affinePoint E (Polynomial.aeval β p) := by
  exact SourceStack.P1PolynomialSeparation.affinePolynomialPointMap_ne_target_of_aeval_ne
    F E h

theorem hilbert_p1PolynomialSeparation_derivative_ne_zero_of_affinePolynomialPointMap_eq_target
    {S : Set E} {p : F[X]} (hpder : p.derivative ≠ 0) {x β : E}
    (hβ : Polynomial.aeval β p ∉ replacementSet F E S p)
    (hmap : affinePolynomialPointMap F E p x =
      SourceStack.ProjectiveLine.affinePoint E (Polynomial.aeval β p)) :
    Polynomial.aeval x p.derivative ≠ 0 := by
  exact SourceStack.P1PolynomialSeparation.derivative_ne_zero_of_affinePolynomialPointMap_eq_target
    F E hpder hβ hmap

variable {S : Set E} {β : E}
variable (P : P1PolynomialSeparationStep F E S β)

theorem hilbert_p1PolynomialSeparation_targetPoint_ne_infinity :
    P.targetPoint ≠ SourceStack.ProjectiveLine.infinity E := by
  exact SourceStack.P1PolynomialSeparation.P1PolynomialSeparationStep.targetPoint_ne_infinity
    P

theorem hilbert_p1PolynomialSeparation_targetPoint_not_mem_branchFinset :
    P.targetPoint ∉ SourceStack.ProjectiveLine.branchFinset E := by
  exact SourceStack.P1PolynomialSeparation.P1PolynomialSeparationStep.targetPoint_not_mem_branchFinset
    P

theorem hilbert_p1PolynomialSeparation_targetPoint_not_mem_branchSet :
    P.targetPoint ∉ SourceStack.ProjectiveLine.branchSet E := by
  exact SourceStack.P1PolynomialSeparation.P1PolynomialSeparationStep.targetPoint_not_mem_branchSet
    P

theorem hilbert_p1PolynomialSeparation_pointMap_ne_target_of_mem
    {x : E} (hx : x ∈ S) :
    P.pointMap x ≠ P.targetPoint := by
  exact SourceStack.P1PolynomialSeparation.P1PolynomialSeparationStep.pointMap_ne_target_of_mem
    P hx

theorem hilbert_p1PolynomialSeparation_derivative_ne_zero_at_pointMap_preimage
    {x : E} (hx : P.pointMap x = P.targetPoint) :
    Polynomial.aeval x P.polynomial.derivative ≠ 0 := by
  exact SourceStack.P1PolynomialSeparation.P1PolynomialSeparationStep.derivative_ne_zero_at_pointMap_preimage
    P hx

theorem hilbert_p1PolynomialSeparation_separates_avoids_branch_and_noncritical :
    P.targetPoint ∉ SourceStack.ProjectiveLine.branchSet E ∧
      (∀ x ∈ S, P.pointMap x ≠ P.targetPoint) ∧
        ∀ x : E, P.pointMap x = P.targetPoint →
          Polynomial.aeval x P.polynomial.derivative ≠ 0 := by
  exact SourceStack.P1PolynomialSeparation.P1PolynomialSeparationStep.separates_avoids_branch_and_noncritical
    P

end P1PolynomialSeparation

namespace PolynomialTargetAvoidance

open SourceStack.PolynomialMaps
open SourceStack.PolynomialTargetAvoidance

universe u v

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]

theorem hilbert_polynomialTargetAvoidance_mem_affineBranchValueSet_iff
    (y : E) :
    y ∈ affineBranchValueSet E ↔ y = 0 ∨ y = 1 := by
  exact SourceStack.PolynomialTargetAvoidance.mem_affineBranchValueSet_iff E y

theorem hilbert_polynomialTargetAvoidance_affineBranchValueSet_finite :
    (affineBranchValueSet E).Finite := by
  exact SourceStack.PolynomialTargetAvoidance.affineBranchValueSet_finite E

theorem hilbert_polynomialTargetAvoidance_forbiddenTargetSet_finite
    {S : Set E} (hS : S.Finite) (p : F[X]) :
    (forbiddenTargetSet F E S p).Finite := by
  exact SourceStack.PolynomialTargetAvoidance.forbiddenTargetSet_finite F E hS p

theorem hilbert_polynomialTargetAvoidance_mem_forbiddenTargetSet_iff
    {S : Set E} (p : F[X]) (y : E) :
    y ∈ forbiddenTargetSet F E S p ↔
      y ∈ replacementSet F E S p ∨ y = 0 ∨ y = 1 := by
  exact SourceStack.PolynomialTargetAvoidance.mem_forbiddenTargetSet_iff
    F E p y

theorem hilbert_polynomialTargetAvoidance_not_mem_forbiddenTargetSet_iff
    {S : Set E} (p : F[X]) (y : E) :
    y ∉ forbiddenTargetSet F E S p ↔
      y ∉ replacementSet F E S p ∧ y ≠ 0 ∧ y ≠ 1 := by
  exact SourceStack.PolynomialTargetAvoidance.not_mem_forbiddenTargetSet_iff
    F E p y

theorem hilbert_polynomialTargetAvoidance_exists_target_not_mem_forbiddenTargetSet
    [Infinite E] {S : Set E} (hS : S.Finite) (p : F[X]) :
    ∃ y : E, y ∉ forbiddenTargetSet F E S p := by
  exact SourceStack.PolynomialTargetAvoidance.exists_target_not_mem_forbiddenTargetSet
    F E hS p

theorem hilbert_polynomialTargetAvoidance_target_not_mem_replacement_of_not_mem_forbiddenTargetSet
    {S : Set E} {p : F[X]} {y : E}
    (hy : y ∉ forbiddenTargetSet F E S p) :
    y ∉ replacementSet F E S p := by
  exact SourceStack.PolynomialTargetAvoidance.target_not_mem_replacement_of_not_mem_forbiddenTargetSet
    F E hy

theorem hilbert_polynomialTargetAvoidance_target_ne_zero_of_not_mem_forbiddenTargetSet
    {S : Set E} {p : F[X]} {y : E}
    (hy : y ∉ forbiddenTargetSet F E S p) :
    y ≠ 0 := by
  exact SourceStack.PolynomialTargetAvoidance.target_ne_zero_of_not_mem_forbiddenTargetSet
    F E hy

theorem hilbert_polynomialTargetAvoidance_target_ne_one_of_not_mem_forbiddenTargetSet
    {S : Set E} {p : F[X]} {y : E}
    (hy : y ∉ forbiddenTargetSet F E S p) :
    y ≠ 1 := by
  exact SourceStack.PolynomialTargetAvoidance.target_ne_one_of_not_mem_forbiddenTargetSet
    F E hy

theorem hilbert_polynomialTargetAvoidance_toP1PolynomialSeparationStep_polynomial
    {S : Set E} {β : E}
    (p : F[X]) (hpder : p.derivative ≠ 0)
    (hβ : Polynomial.aeval β p ∉ forbiddenTargetSet F E S p) :
    (toP1PolynomialSeparationStep F E p hpder hβ).polynomial = p := by
  exact SourceStack.PolynomialTargetAvoidance.toP1PolynomialSeparationStep_polynomial
    F E p hpder hβ

theorem hilbert_polynomialTargetAvoidance_toP1PolynomialSeparationStep_target_not_mem_replacement
    {S : Set E} {β : E}
    (p : F[X]) (hpder : p.derivative ≠ 0)
    (hβ : Polynomial.aeval β p ∉ forbiddenTargetSet F E S p) :
    Polynomial.aeval β p ∉ replacementSet F E S p := by
  exact SourceStack.PolynomialTargetAvoidance.toP1PolynomialSeparationStep_target_not_mem_replacement
    F E p hpder hβ

theorem hilbert_polynomialTargetAvoidance_toP1PolynomialSeparationStep_target_ne_zero
    {S : Set E} {β : E}
    (p : F[X]) (hpder : p.derivative ≠ 0)
    (hβ : Polynomial.aeval β p ∉ forbiddenTargetSet F E S p) :
    Polynomial.aeval β p ≠ 0 := by
  exact SourceStack.PolynomialTargetAvoidance.toP1PolynomialSeparationStep_target_ne_zero
    F E p hpder hβ

theorem hilbert_polynomialTargetAvoidance_toP1PolynomialSeparationStep_target_ne_one
    {S : Set E} {β : E}
    (p : F[X]) (hpder : p.derivative ≠ 0)
    (hβ : Polynomial.aeval β p ∉ forbiddenTargetSet F E S p) :
    Polynomial.aeval β p ≠ 1 := by
  exact SourceStack.PolynomialTargetAvoidance.toP1PolynomialSeparationStep_target_ne_one
    F E p hpder hβ

end PolynomialTargetAvoidance

namespace PolynomialValueSurjectivity

open SourceStack.PolynomialTargetAvoidance
open SourceStack.PolynomialValueSurjectivity

universe u v

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]

theorem hilbert_polynomialValueSurjectivity_natDegree_pos_of_derivative_ne_zero
    (p : F[X]) (hpder : p.derivative ≠ 0) :
    0 < p.natDegree := by
  exact SourceStack.PolynomialValueSurjectivity.natDegree_pos_of_derivative_ne_zero
    F p hpder

theorem hilbert_polynomialValueSurjectivity_map_natDegree_pos_of_derivative_ne_zero
    (p : F[X]) (hpder : p.derivative ≠ 0) :
    0 < (p.map (algebraMap F E)).natDegree := by
  exact SourceStack.PolynomialValueSurjectivity.map_natDegree_pos_of_derivative_ne_zero
    F E p hpder

theorem hilbert_polynomialValueSurjectivity_exists_aeval_eq_of_map_natDegree_pos
    [IsAlgClosed E]
    (p : F[X]) (hp : 0 < (p.map (algebraMap F E)).natDegree) (y : E) :
    ∃ β : E, Polynomial.aeval β p = y := by
  exact SourceStack.PolynomialValueSurjectivity.exists_aeval_eq_of_map_natDegree_pos
    F E p hp y

theorem hilbert_polynomialValueSurjectivity_exists_beta_not_mem_forbiddenTargetSet
    [IsAlgClosed E]
    {S : Set E} (hS : S.Finite)
    (p : F[X]) (hp : 0 < (p.map (algebraMap F E)).natDegree) :
    ∃ β : E, Polynomial.aeval β p ∉ forbiddenTargetSet F E S p := by
  exact SourceStack.PolynomialValueSurjectivity.exists_beta_not_mem_forbiddenTargetSet
    F E hS p hp

theorem hilbert_polynomialValueSurjectivity_exists_beta_not_mem_forbiddenTargetSet_of_derivative_ne_zero
    [IsAlgClosed E]
    {S : Set E} (hS : S.Finite)
    (p : F[X]) (hpder : p.derivative ≠ 0) :
    ∃ β : E, Polynomial.aeval β p ∉ forbiddenTargetSet F E S p := by
  exact SourceStack.PolynomialValueSurjectivity.exists_beta_not_mem_forbiddenTargetSet_of_derivative_ne_zero
    F E hS p hpder

theorem hilbert_polynomialValueSurjectivity_exists_p1PolynomialSeparationStep
    [IsAlgClosed E]
    {S : Set E} (hS : S.Finite)
    (p : F[X]) (hp : 0 < (p.map (algebraMap F E)).natDegree)
    (hpder : p.derivative ≠ 0) :
    ∃ β : E, ∃ P : SourceStack.P1PolynomialSeparation.P1PolynomialSeparationStep F E S β,
      P.polynomial = p := by
  exact SourceStack.PolynomialValueSurjectivity.exists_p1PolynomialSeparationStep
    F E hS p hp hpder

theorem hilbert_polynomialValueSurjectivity_exists_p1PolynomialSeparationStep_of_derivative_ne_zero
    [IsAlgClosed E]
    {S : Set E} (hS : S.Finite)
    (p : F[X]) (hpder : p.derivative ≠ 0) :
    ∃ β : E, ∃ P : SourceStack.P1PolynomialSeparation.P1PolynomialSeparationStep F E S β,
      P.polynomial = p := by
  exact SourceStack.PolynomialValueSurjectivity.exists_p1PolynomialSeparationStep_of_derivative_ne_zero
    F E hS p hpder

end PolynomialValueSurjectivity

namespace P1SchemePointBridge

open SourceStack.MarkedProjectiveLine
open SourceStack.P1PolynomialSeparation
open SourceStack.P1SchemePointBridge

universe u v

variable (K : Type u) [Field K]
variable (B : LinearSchemePointBridge K)

theorem hilbert_p1SchemePointBridge_toScheme_linearPoint
    (label : MarkedPointLabel) :
    B.toScheme (linearPoint K label) = schemeCarrierPoint K label := by
  exact SourceStack.P1SchemePointBridge.LinearSchemePointBridge.toScheme_linearPoint
    B label

theorem hilbert_p1SchemePointBridge_toScheme_mem_markedSchemePointSet_of_mem_branchSet
    {p : SourceStack.ProjectiveLine.P1 K}
    (hp : p ∈ SourceStack.ProjectiveLine.branchSet K) :
    B.toScheme p ∈ SourceStack.SchemeProjectiveLine.markedSchemePointSet K := by
  exact SourceStack.P1SchemePointBridge.LinearSchemePointBridge.toScheme_mem_markedSchemePointSet_of_mem_branchSet
    B hp

theorem hilbert_p1SchemePointBridge_mem_branchSet_of_toScheme_mem_markedSchemePointSet
    {p : SourceStack.ProjectiveLine.P1 K}
    (hp : B.toScheme p ∈ SourceStack.SchemeProjectiveLine.markedSchemePointSet K) :
    p ∈ SourceStack.ProjectiveLine.branchSet K := by
  exact SourceStack.P1SchemePointBridge.LinearSchemePointBridge.mem_branchSet_of_toScheme_mem_markedSchemePointSet
    B hp

theorem hilbert_p1SchemePointBridge_toScheme_mem_markedSchemePointSet_iff
    (p : SourceStack.ProjectiveLine.P1 K) :
    B.toScheme p ∈ SourceStack.SchemeProjectiveLine.markedSchemePointSet K ↔
      p ∈ SourceStack.ProjectiveLine.branchSet K := by
  exact SourceStack.P1SchemePointBridge.LinearSchemePointBridge.toScheme_mem_markedSchemePointSet_iff
    B p

theorem hilbert_p1SchemePointBridge_toScheme_not_mem_markedSchemePointSet_of_not_mem_branchSet
    {p : SourceStack.ProjectiveLine.P1 K}
    (hp : p ∉ SourceStack.ProjectiveLine.branchSet K) :
    B.toScheme p ∉ SourceStack.SchemeProjectiveLine.markedSchemePointSet K := by
  exact SourceStack.P1SchemePointBridge.LinearSchemePointBridge.toScheme_not_mem_markedSchemePointSet_of_not_mem_branchSet
    B hp

theorem hilbert_p1SchemePointBridge_toScheme_eq_iff
    {p q : SourceStack.ProjectiveLine.P1 K} :
    B.toScheme p = B.toScheme q ↔ p = q := by
  exact SourceStack.P1SchemePointBridge.LinearSchemePointBridge.toScheme_eq_iff
    B

variable (F : Type v) [Field F] [Algebra F K]
variable {S : Set K} {β : K}
variable (P : P1PolynomialSeparationStep F K S β)

theorem hilbert_p1SchemePointBridge_schemeTargetPoint_not_mem_markedSchemePointSet :
    B.schemeTargetPoint F P ∉
      SourceStack.SchemeProjectiveLine.markedSchemePointSet K := by
  exact SourceStack.P1SchemePointBridge.LinearSchemePointBridge.schemeTargetPoint_not_mem_markedSchemePointSet
    B F P

theorem hilbert_p1SchemePointBridge_schemePointMap_ne_target_of_mem
    {x : K} (hx : x ∈ S) :
    B.schemePointMap F P x ≠ B.schemeTargetPoint F P := by
  exact SourceStack.P1SchemePointBridge.LinearSchemePointBridge.schemePointMap_ne_target_of_mem
    B F P hx

theorem hilbert_p1SchemePointBridge_derivative_ne_zero_at_schemePointMap_preimage
    {x : K} (hx : B.schemePointMap F P x = B.schemeTargetPoint F P) :
    Polynomial.aeval x P.polynomial.derivative ≠ 0 := by
  exact SourceStack.P1SchemePointBridge.LinearSchemePointBridge.derivative_ne_zero_at_schemePointMap_preimage
    B F P hx

theorem hilbert_p1SchemePointBridge_scheme_separates_avoids_marked_and_noncritical :
    B.schemeTargetPoint F P ∉ SourceStack.SchemeProjectiveLine.markedSchemePointSet K ∧
      (∀ x ∈ S, B.schemePointMap F P x ≠ B.schemeTargetPoint F P) ∧
        ∀ x : K, B.schemePointMap F P x = B.schemeTargetPoint F P →
          Polynomial.aeval x P.polynomial.derivative ≠ 0 := by
  exact SourceStack.P1SchemePointBridge.LinearSchemePointBridge.scheme_separates_avoids_marked_and_noncritical
    B F P

end P1SchemePointBridge

namespace SchemeAffineLinePoints

open SourceStack.MarkedProjectiveLine
open SourceStack.P1SchemePointBridge
open SourceStack.SchemeAffineLinePoints

universe u

variable (K : Type u) [Field K]

theorem hilbert_schemeAffineLinePoints_affinePoint_zero :
    affinePoint K 0 = SourceStack.SchemeProjectiveLine.zeroPoint K := by
  exact SourceStack.SchemeAffineLinePoints.affinePoint_zero K

theorem hilbert_schemeAffineLinePoints_affinePoint_one :
    affinePoint K 1 = SourceStack.SchemeProjectiveLine.onePoint K := by
  exact SourceStack.SchemeAffineLinePoints.affinePoint_one K

theorem hilbert_schemeAffineLinePoints_affinePoint_ne_infinity
    (r : K) :
    affinePoint K r ≠ SourceStack.SchemeProjectiveLine.infinityPoint K := by
  exact SourceStack.SchemeAffineLinePoints.affinePoint_ne_infinity K r

theorem hilbert_schemeAffineLinePoints_affinePoint_injective :
    Function.Injective (affinePoint K) := by
  exact SourceStack.SchemeAffineLinePoints.affinePoint_injective K

theorem hilbert_schemeAffineLinePoints_affinePoint_eq_iff
    (r s : K) :
    affinePoint K r = affinePoint K s ↔ r = s := by
  exact SourceStack.SchemeAffineLinePoints.affinePoint_eq_iff K r s

theorem hilbert_schemeAffineLinePoints_affinePoint_mem_markedSchemePointSet_iff
    (r : K) :
    affinePoint K r ∈ SourceStack.SchemeProjectiveLine.markedSchemePointSet K ↔
      r = 0 ∨ r = 1 := by
  exact SourceStack.SchemeAffineLinePoints.affinePoint_mem_markedSchemePointSet_iff
    K r

theorem hilbert_schemeAffineLinePoints_affinePoint_ne_zero
    {r : K} (hr : r ≠ 0) :
    affinePoint K r ≠ SourceStack.SchemeProjectiveLine.zeroPoint K := by
  exact SourceStack.SchemeAffineLinePoints.affinePoint_ne_zero K hr

theorem hilbert_schemeAffineLinePoints_affinePoint_ne_one
    {r : K} (hr : r ≠ 1) :
    affinePoint K r ≠ SourceStack.SchemeProjectiveLine.onePoint K := by
  exact SourceStack.SchemeAffineLinePoints.affinePoint_ne_one K hr

theorem hilbert_schemeAffineLinePoints_affinePoint_not_mem_markedSchemePointSet_of_ne_zero_one
    {r : K} (h0 : r ≠ 0) (h1 : r ≠ 1) :
    affinePoint K r ∉ SourceStack.SchemeProjectiveLine.markedSchemePointSet K := by
  exact SourceStack.SchemeAffineLinePoints.affinePoint_not_mem_markedSchemePointSet_of_ne_zero_one
    K h0 h1

theorem hilbert_schemeAffineLinePoints_schemeFourPointSet_finite
    (r : K) :
    (schemeFourPointSet K r).Finite := by
  exact SourceStack.SchemeAffineLinePoints.schemeFourPointSet_finite K r

theorem hilbert_schemeAffineLinePoints_affinePoint_mem_schemeFourPointFinset_iff
    (r x : K) :
    affinePoint K x ∈ schemeFourPointFinset K r ↔
      x = 0 ∨ x = r ∨ x = 1 := by
  exact SourceStack.SchemeAffineLinePoints.affinePoint_mem_schemeFourPointFinset_iff
    K r x

theorem hilbert_schemeAffineLinePoints_affinePoint_mem_schemeFourPointSet_iff
    (r x : K) :
    affinePoint K x ∈ schemeFourPointSet K r ↔
      x = 0 ∨ x = r ∨ x = 1 := by
  exact SourceStack.SchemeAffineLinePoints.affinePoint_mem_schemeFourPointSet_iff
    K r x

theorem hilbert_schemeAffineLinePoints_schemeFourPointFinset_card
    {r : K} (hr0 : r ≠ 0) (hr1 : r ≠ 1) :
    (schemeFourPointFinset K r).card = 4 := by
  exact SourceStack.SchemeAffineLinePoints.schemeFourPointFinset_card K hr0 hr1

theorem hilbert_schemeAffineLinePoints_affinePoint_mem_x1_basicOpen
    (r : K) :
    affinePoint K r ∈ AlgebraicGeometry.Proj.basicOpen
      (SourceStack.SchemeProjectiveLine.grading K)
      (SourceStack.SchemeProjectiveLine.X1 K) := by
  exact SourceStack.SchemeAffineLinePoints.affinePoint_mem_x1_basicOpen K r

theorem hilbert_schemeAffineLinePoints_linearToSchemePoint_affinePoint
    (r : K) :
    linearToSchemePoint K (SourceStack.ProjectiveLine.affinePoint K r) =
      affinePoint K r := by
  exact SourceStack.SchemeAffineLinePoints.linearToSchemePoint_affinePoint K r

theorem hilbert_schemeAffineLinePoints_linearToSchemePoint_infinity :
    linearToSchemePoint K (SourceStack.ProjectiveLine.infinity K) =
      SourceStack.SchemeProjectiveLine.infinityPoint K := by
  exact SourceStack.SchemeAffineLinePoints.linearToSchemePoint_infinity K

theorem hilbert_schemeAffineLinePoints_linearToSchemePoint_injective :
    Function.Injective (linearToSchemePoint K) := by
  exact SourceStack.SchemeAffineLinePoints.linearToSchemePoint_injective K

theorem hilbert_schemeAffineLinePoints_linearToSchemePoint_zero :
    linearToSchemePoint K (SourceStack.ProjectiveLine.zero K) =
      SourceStack.SchemeProjectiveLine.zeroPoint K := by
  exact SourceStack.SchemeAffineLinePoints.linearToSchemePoint_zero K

theorem hilbert_schemeAffineLinePoints_linearToSchemePoint_one :
    linearToSchemePoint K (SourceStack.ProjectiveLine.one K) =
      SourceStack.SchemeProjectiveLine.onePoint K := by
  exact SourceStack.SchemeAffineLinePoints.linearToSchemePoint_one K

theorem hilbert_schemeAffineLinePoints_linearToSchemePoint_linearPoint
    (label : MarkedPointLabel) :
    linearToSchemePoint K (linearPoint K label) =
      schemeCarrierPoint K label := by
  exact SourceStack.SchemeAffineLinePoints.linearToSchemePoint_linearPoint K label

theorem hilbert_schemeAffineLinePoints_concreteBridge_toScheme :
    (concreteLinearSchemePointBridge K).toScheme = linearToSchemePoint K := by
  rfl

theorem hilbert_schemeAffineLinePoints_concreteBridge_injective :
    Function.Injective (concreteLinearSchemePointBridge K).toScheme := by
  exact (concreteLinearSchemePointBridge K).injective

theorem hilbert_schemeAffineLinePoints_concreteBridge_maps_label
    (label : MarkedPointLabel) :
    (concreteLinearSchemePointBridge K).toScheme (linearPoint K label) =
      schemeCarrierPoint K label := by
  exact (concreteLinearSchemePointBridge K).maps_label label

end SchemeAffineLinePoints

namespace SchemeProjectiveLineTransform

open SourceStack.SchemeProjectiveLineTransform

universe u

variable (K : Type u) [Field K]

theorem hilbert_schemeReciprocalTranslatePoint_affinePoint_of_ne
    (lambda r : K) (hr : r ≠ lambda) :
    schemeReciprocalTranslatePoint K lambda
        (SourceStack.ProjectiveLine.affinePoint K r) =
      SourceStack.SchemeAffineLinePoints.affinePoint K ((r - lambda)⁻¹) := by
  exact SourceStack.SchemeProjectiveLineTransform.schemeReciprocalTranslatePoint_affinePoint_of_ne
    K lambda r hr

theorem hilbert_schemeReciprocalTranslatePoint_affinePoint_pole
    (lambda : K) :
    schemeReciprocalTranslatePoint K lambda
        (SourceStack.ProjectiveLine.affinePoint K lambda) =
      SourceStack.SchemeProjectiveLine.infinityPoint K := by
  exact SourceStack.SchemeProjectiveLineTransform.schemeReciprocalTranslatePoint_affinePoint_pole
    K lambda

theorem hilbert_schemeReciprocalTranslatePoint_infinity
    (lambda : K) :
    schemeReciprocalTranslatePoint K lambda
        (SourceStack.ProjectiveLine.infinity K) =
      SourceStack.SchemeProjectiveLine.zeroPoint K := by
  exact SourceStack.SchemeProjectiveLineTransform.schemeReciprocalTranslatePoint_infinity
    K lambda

theorem hilbert_schemeAffineLinearPoint_affinePoint
    (a b : K) (ha : a ≠ 0) (r : K) :
    schemeAffineLinearPoint K a b ha
        (SourceStack.ProjectiveLine.affinePoint K r) =
      SourceStack.SchemeAffineLinePoints.affinePoint K (a * r + b) := by
  exact SourceStack.SchemeProjectiveLineTransform.schemeAffineLinearPoint_affinePoint
    K a b ha r

theorem hilbert_schemeAffineLinearPoint_infinity
    (a b : K) (ha : a ≠ 0) :
    schemeAffineLinearPoint K a b ha
        (SourceStack.ProjectiveLine.infinity K) =
      SourceStack.SchemeProjectiveLine.infinityPoint K := by
  exact SourceStack.SchemeProjectiveLineTransform.schemeAffineLinearPoint_infinity
    K a b ha

end SchemeProjectiveLineTransform

namespace PolynomialSchemeSeparation

open SourceStack.P1PolynomialSeparation
open SourceStack.P1SchemePointBridge
open SourceStack.PolynomialSchemeSeparation

universe u v

variable (F : Type u) (K : Type v)
variable [Field F] [Field K] [Algebra F K]
variable (B : LinearSchemePointBridge K)

theorem hilbert_polynomialSchemeSeparation_exists_scheme_separation_package
    [IsAlgClosed K]
    {S : Set K} (hS : S.Finite)
    (p : F[X]) (hpder : p.derivative ≠ 0) :
    ∃ β : K, ∃ P : P1PolynomialSeparationStep F K S β,
      P.polynomial = p ∧
        B.schemeTargetPoint F P ∉ SourceStack.SchemeProjectiveLine.markedSchemePointSet K ∧
          (∀ x ∈ S, B.schemePointMap F P x ≠ B.schemeTargetPoint F P) ∧
            ∀ x : K, B.schemePointMap F P x = B.schemeTargetPoint F P →
              Polynomial.aeval x P.polynomial.derivative ≠ 0 := by
  exact SourceStack.PolynomialSchemeSeparation.exists_scheme_separation_package
    F K B hS p hpder

end PolynomialSchemeSeparation

namespace ConcretePolynomialSchemeSeparation

open SourceStack.ConcretePolynomialSchemeSeparation
open SourceStack.P1PolynomialSeparation
open SourceStack.SchemeAffineLinePoints

universe u v

variable (F : Type u) (K : Type v)
variable [Field F] [Field K] [Algebra F K]
variable {S : Set K} {β : K}
variable (P : P1PolynomialSeparationStep F K S β)

theorem hilbert_concretePolynomialSchemeSeparation_pointMap_eq_bridge
    (x : K) :
    (concreteLinearSchemePointBridge K).schemePointMap F P x =
      concreteSchemePolynomialPointMap F K P.polynomial x := by
  exact SourceStack.ConcretePolynomialSchemeSeparation.concreteSchemePolynomialPointMap_eq_bridge
    F K P x

theorem hilbert_concretePolynomialSchemeSeparation_targetPoint_eq_bridge :
    (concreteLinearSchemePointBridge K).schemeTargetPoint F P =
      concreteSchemePolynomialTargetPoint F K P.polynomial β := by
  exact SourceStack.ConcretePolynomialSchemeSeparation.concreteSchemePolynomialTargetPoint_eq_bridge
    F K P

theorem hilbert_concretePolynomialSchemeSeparation_pointMap_mem_markedSchemePointSet_iff
    (p : F[X]) (x : K) :
    concreteSchemePolynomialPointMap F K p x ∈
        SourceStack.SchemeProjectiveLine.markedSchemePointSet K ↔
      Polynomial.aeval x p = 0 ∨ Polynomial.aeval x p = 1 := by
  exact SourceStack.ConcretePolynomialSchemeSeparation.concreteSchemePolynomialPointMap_mem_markedSchemePointSet_iff
    F K p x

theorem hilbert_concretePolynomialSchemeSeparation_targetPoint_mem_markedSchemePointSet_iff
    (p : F[X]) (β : K) :
    concreteSchemePolynomialTargetPoint F K p β ∈
        SourceStack.SchemeProjectiveLine.markedSchemePointSet K ↔
      Polynomial.aeval β p = 0 ∨ Polynomial.aeval β p = 1 := by
  exact SourceStack.ConcretePolynomialSchemeSeparation.concreteSchemePolynomialTargetPoint_mem_markedSchemePointSet_iff
    F K p β

theorem hilbert_concretePolynomialSchemeSeparation_targetPoint_not_mem_markedSchemePointSet
    {p : F[X]} {β : K}
    (h0 : Polynomial.aeval β p ≠ 0)
    (h1 : Polynomial.aeval β p ≠ 1) :
    concreteSchemePolynomialTargetPoint F K p β ∉
      SourceStack.SchemeProjectiveLine.markedSchemePointSet K := by
  exact SourceStack.ConcretePolynomialSchemeSeparation.concreteSchemePolynomialTargetPoint_not_mem_markedSchemePointSet
    F K h0 h1

theorem hilbert_concretePolynomialSchemeSeparation_exists_concrete_scheme_separation_package
    [IsAlgClosed K]
    {S : Set K} (hS : S.Finite)
    (p : F[X]) (hpder : p.derivative ≠ 0) :
    ∃ β : K, ∃ P : P1PolynomialSeparationStep F K S β,
      P.polynomial = p ∧
        concreteSchemePolynomialTargetPoint F K P.polynomial β ∉
          SourceStack.SchemeProjectiveLine.markedSchemePointSet K ∧
          (∀ x ∈ S, concreteSchemePolynomialPointMap F K P.polynomial x ≠
            concreteSchemePolynomialTargetPoint F K P.polynomial β) ∧
            ∀ x : K, concreteSchemePolynomialPointMap F K P.polynomial x =
              concreteSchemePolynomialTargetPoint F K P.polynomial β →
              Polynomial.aeval x P.polynomial.derivative ≠ 0 := by
  exact SourceStack.ConcretePolynomialSchemeSeparation.exists_concrete_scheme_separation_package
    F K hS p hpder

end ConcretePolynomialSchemeSeparation

namespace UnramifiedEtale

universe u v w

theorem hilbert_formallyUnramified_iff_subsingleton_kaehlerDifferential
    (R : Type v) [CommRing R]
    (A : Type u) [CommRing A] [Algebra R A] :
    Algebra.FormallyUnramified R A ↔ Subsingleton (Ω[A⁄R]) := by
  exact SourceStack.UnramifiedEtale.formallyUnramified_iff_subsingleton_kaehlerDifferential R A

theorem hilbert_formallyUnramified_iff_comp_injective
    (R : Type v) [CommRing R]
    (A : Type u) [CommRing A] [Algebra R A] :
    Algebra.FormallyUnramified R A ↔
      ∀ ⦃B : Type u⦄ [CommRing B] [Algebra R B] (I : Ideal B),
        I ^ 2 = ⊥ →
          Function.Injective ((Ideal.Quotient.mkₐ R I).comp :
            (A →ₐ[R] B) → A →ₐ[R] B ⧸ I) := by
  exact SourceStack.UnramifiedEtale.formallyUnramified_iff_comp_injective R A

theorem hilbert_formallyUnramified_comp
    (R : Type u) [CommRing R]
    (A : Type v) [CommRing A] [Algebra R A]
    (B : Type w) [CommRing B] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B]
    [Algebra.FormallyUnramified R A] [Algebra.FormallyUnramified A B] :
    Algebra.FormallyUnramified R B := by
  exact SourceStack.UnramifiedEtale.formallyUnramified_comp R A B

theorem hilbert_formallyUnramified_of_comp
    (R : Type u) [CommRing R]
    (A : Type v) [CommRing A] [Algebra R A]
    (B : Type w) [CommRing B] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B]
    [Algebra.FormallyUnramified R B] :
    Algebra.FormallyUnramified A B := by
  exact SourceStack.UnramifiedEtale.formallyUnramified_of_comp R A B

theorem hilbert_formallyUnramified_base_change
    {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] [Algebra R A]
    (B : Type w) [CommRing B] [Algebra R B]
    [Algebra.FormallyUnramified R A] :
    Algebra.FormallyUnramified B (B ⊗[R] A) := by
  exact SourceStack.UnramifiedEtale.formallyUnramified_base_change B

theorem hilbert_unramified_of_isLocalization_Away
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (r : R) [IsLocalization.Away r A] :
    Algebra.Unramified R A := by
  exact SourceStack.UnramifiedEtale.unramified_of_isLocalization_Away R A r

theorem hilbert_unramified_comp
    (R : Type u) [CommRing R]
    (A B : Type v) [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra.Unramified R A] [Algebra.Unramified A B] :
    Algebra.Unramified R B := by
  exact SourceStack.UnramifiedEtale.unramified_comp R A B

theorem hilbert_unramified_base_change
    (R : Type u) [CommRing R]
    (A B : Type v) [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B]
    [Algebra.Unramified R A] :
    Algebra.Unramified B (B ⊗[R] A) := by
  exact SourceStack.UnramifiedEtale.unramified_base_change R A B

theorem hilbert_formallyUnramified_iff_isSeparable
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [Algebra.EssFiniteType K L] :
    Algebra.FormallyUnramified K L ↔ Algebra.IsSeparable K L := by
  exact SourceStack.UnramifiedEtale.formallyUnramified_iff_isSeparable K L

theorem hilbert_formallyEtale_iff_unramified_and_smooth
    (R : Type u) [CommRing R]
    (A : Type u) [CommRing A] [Algebra R A] :
    Algebra.FormallyEtale R A ↔
      Algebra.FormallyUnramified R A ∧ Algebra.FormallySmooth R A := by
  exact SourceStack.UnramifiedEtale.formallyEtale_iff_unramified_and_smooth R A

theorem hilbert_formallyEtale_to_formallyUnramified
    (R : Type u) [CommRing R]
    (A : Type u) [CommRing A] [Algebra R A]
    [Algebra.FormallyEtale R A] :
    Algebra.FormallyUnramified R A := by
  exact SourceStack.UnramifiedEtale.formallyEtale_to_formallyUnramified R A

theorem hilbert_formallyEtale_of_equiv
    {R : Type u} [CommRing R]
    {A B : Type u} [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B]
    [Algebra.FormallyEtale R A]
    (e : A ≃ₐ[R] B) :
    Algebra.FormallyEtale R B := by
  exact SourceStack.UnramifiedEtale.formallyEtale_of_equiv e

theorem hilbert_formallyEtale_iff_of_equiv
    {R : Type u} [CommRing R]
    {A B : Type u} [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B]
    (e : A ≃ₐ[R] B) :
    Algebra.FormallyEtale R A ↔ Algebra.FormallyEtale R B := by
  exact SourceStack.UnramifiedEtale.formallyEtale_iff_of_equiv e

theorem hilbert_formallyEtale_of_isLocalization
    {R Rₘ : Type u} [CommRing R] [CommRing Rₘ]
    (M : Submonoid R) [Algebra R Rₘ] [IsLocalization M Rₘ] :
    Algebra.FormallyEtale R Rₘ := by
  exact SourceStack.UnramifiedEtale.formallyEtale_of_isLocalization M

theorem hilbert_formallyEtale_localization_base
    {R Rₘ Sₘ : Type u} [CommRing R] [CommRing Rₘ] [CommRing Sₘ]
    (M : Submonoid R)
    [Algebra R Sₘ] [Algebra R Rₘ] [Algebra Rₘ Sₘ]
    [IsScalarTower R Rₘ Sₘ] [IsLocalization M Rₘ]
    [Algebra.FormallyEtale R Sₘ] :
    Algebra.FormallyEtale Rₘ Sₘ := by
  exact SourceStack.UnramifiedEtale.formallyEtale_localization_base M

theorem hilbert_formallyEtale_localization_map
    {R S Rₘ Sₘ : Type u} [CommRing R] [CommRing S]
    [CommRing Rₘ] [CommRing Sₘ]
    (M : Submonoid R)
    [Algebra R S] [Algebra R Sₘ] [Algebra S Sₘ]
    [Algebra R Rₘ] [Algebra Rₘ Sₘ]
    [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]
    [IsLocalization M Rₘ]
    [IsLocalization (Submonoid.map (algebraMap R S) M) Sₘ]
    [Algebra.FormallyEtale R S] :
    Algebra.FormallyEtale Rₘ Sₘ := by
  exact SourceStack.UnramifiedEtale.formallyEtale_localization_map
    (R := R) (S := S) (Rₘ := Rₘ) (Sₘ := Sₘ) M

theorem hilbert_formallyEtale_comp
    (R : Type u) [CommRing R]
    (A B : Type u) [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra.FormallyEtale R A] [Algebra.FormallyEtale A B] :
    Algebra.FormallyEtale R B := by
  exact SourceStack.UnramifiedEtale.formallyEtale_comp R A B

theorem hilbert_formallyEtale_base_change
    {R : Type u} [CommRing R]
    {A : Type u} [CommRing A] [Algebra R A]
    (B : Type u) [CommRing B] [Algebra R B]
    [Algebra.FormallyEtale R A] :
    Algebra.FormallyEtale B (B ⊗[R] A) := by
  exact SourceStack.UnramifiedEtale.formallyEtale_base_change B

theorem hilbert_formallyEtale_iff_isSeparable
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [Algebra.EssFiniteType K L] :
    Algebra.FormallyEtale K L ↔ Algebra.IsSeparable K L := by
  exact SourceStack.UnramifiedEtale.formallyEtale_iff_isSeparable K L

theorem hilbert_formallyEtale_of_isSeparable
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [Algebra.IsSeparable K L] :
    Algebra.FormallyEtale K L := by
  exact SourceStack.UnramifiedEtale.formallyEtale_of_isSeparable K L

theorem hilbert_etale_of_equiv
    {R : Type u} [CommRing R]
    {A B : Type u} [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B]
    [Algebra.Etale R A]
    (e : A ≃ₐ[R] B) :
    Algebra.Etale R B := by
  exact SourceStack.UnramifiedEtale.etale_of_equiv e

theorem hilbert_etale_of_isLocalization_Away
    {R : Type u} [CommRing R]
    {A : Type u} [CommRing A] [Algebra R A]
    (r : R) [IsLocalization.Away r A] :
    Algebra.Etale R A := by
  exact SourceStack.UnramifiedEtale.etale_of_isLocalization_Away r

theorem hilbert_etale_comp
    (R : Type u) [CommRing R]
    (A B : Type u) [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra.Etale R A] [Algebra.Etale A B] :
    Algebra.Etale R B := by
  exact SourceStack.UnramifiedEtale.etale_comp R A B

theorem hilbert_etale_base_change
    (R : Type u) [CommRing R]
    (A B : Type u) [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B]
    [Algebra.Etale R A] :
    Algebra.Etale B (B ⊗[R] A) := by
  exact SourceStack.UnramifiedEtale.etale_base_change R A B

end UnramifiedEtale

namespace Ramification

universe u v w x

theorem hilbert_algebraUnramified_formallyUnramified
    (R : Type u) [CommRing R]
    (A : Type v) [CommRing A] [Algebra R A]
    [Algebra.Unramified R A] :
    Algebra.FormallyUnramified R A := by
  exact SourceStack.Ramification.algebraUnramified_formallyUnramified R A

theorem hilbert_algebraUnramified_finiteType
    (R : Type u) [CommRing R]
    (A : Type v) [CommRing A] [Algebra R A]
    [Algebra.Unramified R A] :
    Algebra.FiniteType R A := by
  exact SourceStack.Ramification.algebraUnramified_finiteType R A

theorem hilbert_algebraUnramified_of_equiv
    {R : Type u} [CommRing R]
    {A : Type v} {B : Type w}
    [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B]
    [Algebra.Unramified R A]
    (e : A ≃ₐ[R] B) :
    Algebra.Unramified R B := by
  exact SourceStack.Ramification.algebraUnramified_of_equiv e

theorem hilbert_algebraUnramified_of_isLocalization_Away
    {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] [Algebra R A]
    (r : R) [IsLocalization.Away r A] :
    Algebra.Unramified R A := by
  exact SourceStack.Ramification.algebraUnramified_of_isLocalization_Away r

theorem hilbert_algebraUnramified_comp
    (R : Type u) [CommRing R]
    (A : Type v) [CommRing A] [Algebra R A]
    (B : Type w) [CommRing B] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B]
    [Algebra.Unramified R A] [Algebra.Unramified A B] :
    Algebra.Unramified R B := by
  exact SourceStack.Ramification.algebraUnramified_comp R A B

theorem hilbert_algebraUnramified_baseChange
    (R : Type u) [CommRing R]
    (A : Type v) [CommRing A] [Algebra R A]
    (B : Type w) [CommRing B] [Algebra R B]
    [Algebra.Unramified R A] :
    Algebra.Unramified B (B ⊗[R] A) := by
  exact SourceStack.Ramification.algebraUnramified_baseChange R A B

theorem hilbert_formallyUnramified_of_field_isSeparable
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [Algebra.IsSeparable K L] :
    Algebra.FormallyUnramified K L := by
  exact SourceStack.Ramification.formallyUnramified_of_field_isSeparable K L

theorem hilbert_formallyUnramified_isSeparable_of_field
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [Algebra.FormallyUnramified K L] [Algebra.EssFiniteType K L] :
    Algebra.IsSeparable K L := by
  exact SourceStack.Ramification.formallyUnramified_isSeparable_of_field K L

theorem hilbert_formallyUnramified_iff_field_isSeparable
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [Algebra.EssFiniteType K L] :
    Algebra.FormallyUnramified K L ↔ Algebra.IsSeparable K L := by
  exact SourceStack.Ramification.formallyUnramified_iff_field_isSeparable K L

theorem hilbert_formallyUnramified_localization_base
    {R : Type u} {Rₘ : Type v} {Sₘ : Type w}
    [CommRing R] [CommRing Rₘ] [CommRing Sₘ]
    (M : Submonoid R)
    [Algebra R Sₘ] [Algebra R Rₘ] [Algebra Rₘ Sₘ]
    [IsScalarTower R Rₘ Sₘ]
    [Algebra.FormallyUnramified R Sₘ] :
    Algebra.FormallyUnramified Rₘ Sₘ := by
  exact SourceStack.Ramification.formallyUnramified_localization_base M

theorem hilbert_formallyUnramified_localization_map
    {R : Type u} {S : Type v} {Rₘ : Type w} {Sₘ : Type x}
    [CommRing R] [CommRing S] [CommRing Rₘ] [CommRing Sₘ]
    (M : Submonoid R)
    [Algebra R S] [Algebra R Sₘ] [Algebra S Sₘ]
    [Algebra R Rₘ] [Algebra Rₘ Sₘ]
    [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]
    [IsLocalization (Submonoid.map (algebraMap R S) M) Sₘ]
    [Algebra.FormallyUnramified R S] :
    Algebra.FormallyUnramified Rₘ Sₘ := by
  exact SourceStack.Ramification.formallyUnramified_localization_map
    (R := R) (S := S) (Rₘ := Rₘ) (Sₘ := Sₘ) M

theorem hilbert_formallyUnramified_iff_exists_tensorProduct
    (R : Type u) [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] :
    Algebra.FormallyUnramified R S ↔
      ∃ t : S ⊗[R] S,
        (∀ s, ((1 : S) ⊗ₜ[R] s - s ⊗ₜ[R] (1 : S)) * t = 0) ∧
          Algebra.TensorProduct.lmul' R t = 1 := by
  exact SourceStack.Ramification.formallyUnramified_iff_exists_tensorProduct R S

noncomputable def hilbert_formallyUnramified_tensorElem
    (R : Type u) [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S]
    [Algebra.FormallyUnramified R S] [Algebra.EssFiniteType R S] :
    S ⊗[R] S :=
  SourceStack.Ramification.formallyUnramified_tensorElem R S

theorem hilbert_formallyUnramified_one_tmul_sub_tmul_one_mul_tensorElem
    {R : Type u} [CommRing R]
    {S : Type v} [CommRing S] [Algebra R S]
    [Algebra.FormallyUnramified R S] [Algebra.EssFiniteType R S]
    (s : S) :
    ((1 : S) ⊗ₜ[R] s - s ⊗ₜ[R] (1 : S)) *
        SourceStack.Ramification.formallyUnramified_tensorElem R S = 0 := by
  exact SourceStack.Ramification.formallyUnramified_one_tmul_sub_tmul_one_mul_tensorElem s

theorem hilbert_formallyUnramified_one_tmul_mul_tensorElem
    {R : Type u} [CommRing R]
    {S : Type v} [CommRing S] [Algebra R S]
    [Algebra.FormallyUnramified R S] [Algebra.EssFiniteType R S]
    (s : S) :
    ((1 : S) ⊗ₜ[R] s) * SourceStack.Ramification.formallyUnramified_tensorElem R S =
      (s ⊗ₜ[R] (1 : S)) * SourceStack.Ramification.formallyUnramified_tensorElem R S := by
  exact SourceStack.Ramification.formallyUnramified_one_tmul_mul_tensorElem s

theorem hilbert_formallyUnramified_lmul_tensorElem
    (R : Type u) [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S]
    [Algebra.FormallyUnramified R S] [Algebra.EssFiniteType R S] :
    Algebra.TensorProduct.lmul' R
        (SourceStack.Ramification.formallyUnramified_tensorElem R S) = 1 := by
  exact SourceStack.Ramification.formallyUnramified_lmul_tensorElem R S

theorem hilbert_formallyUnramified_finite_of_free
    (R : Type u) [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S]
    [Algebra.FormallyUnramified R S] [Algebra.EssFiniteType R S]
    [Module.Free R S] :
    Module.Finite R S := by
  exact SourceStack.Ramification.formallyUnramified_finite_of_free R S

theorem hilbert_formallyUnramified_flat_of_restrictScalars
    (R : Type u) [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S]
    (M : Type w) [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M]
    [Algebra.FormallyUnramified R S] [Algebra.EssFiniteType R S]
    [Module.Flat R M] :
    Module.Flat S M := by
  exact SourceStack.Ramification.formallyUnramified_flat_of_restrictScalars R S M

theorem hilbert_formallyUnramified_projective_of_restrictScalars
    (R : Type u) [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S]
    (M : Type w) [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M]
    [Algebra.FormallyUnramified R S] [Algebra.EssFiniteType R S]
    [Module.Projective R M] :
    Module.Projective S M := by
  exact SourceStack.Ramification.formallyUnramified_projective_of_restrictScalars R S M

theorem hilbert_formallyUnramified_pi_iff
    {R : Type (max u v)} {I : Type v} [Finite I]
    (A : I → Type (max u v))
    [CommRing R] [(i : I) → CommRing (A i)]
    [(i : I) → Algebra R (A i)] :
    Algebra.FormallyUnramified R ((i : I) → A i) ↔
      ∀ i, Algebra.FormallyUnramified R (A i) := by
  exact SourceStack.Ramification.formallyUnramified_pi_iff A

theorem hilbert_ramificationIdx_spec
    {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    {f : R →+* S} {p : Ideal R} {P : Ideal S} {n : ℕ}
    (hle : Ideal.map f p ≤ P ^ n)
    (hgt : ¬ Ideal.map f p ≤ P ^ (n + 1)) :
    Ideal.ramificationIdx f p P = n := by
  exact SourceStack.Ramification.ramificationIdx_spec hle hgt

theorem hilbert_ramificationIdx_bot
    {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    {f : R →+* S} {P : Ideal S} :
    Ideal.ramificationIdx f (⊥ : Ideal R) P = 0 := by
  exact SourceStack.Ramification.ramificationIdx_bot

theorem hilbert_ramificationIdx_of_not_le
    {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    {f : R →+* S} {p : Ideal R} {P : Ideal S}
    (h : ¬ Ideal.map f p ≤ P) :
    Ideal.ramificationIdx f p P = 0 := by
  exact SourceStack.Ramification.ramificationIdx_of_not_le h

theorem hilbert_le_pow_ramificationIdx
    {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    {f : R →+* S} {p : Ideal R} {P : Ideal S} :
    Ideal.map f p ≤ P ^ Ideal.ramificationIdx f p P := by
  exact SourceStack.Ramification.le_pow_ramificationIdx

theorem hilbert_le_comap_pow_ramificationIdx
    {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    {f : R →+* S} {p : Ideal R} {P : Ideal S} :
    p ≤ Ideal.comap f (P ^ Ideal.ramificationIdx f p P) := by
  exact SourceStack.Ramification.le_comap_pow_ramificationIdx

theorem hilbert_le_comap_of_ramificationIdx_ne_zero
    {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    {f : R →+* S} {p : Ideal R} {P : Ideal S}
    (h : Ideal.ramificationIdx f p P ≠ 0) :
    p ≤ Ideal.comap f P := by
  exact SourceStack.Ramification.le_comap_of_ramificationIdx_ne_zero h

theorem hilbert_ramificationIdx_eq_normalizedFactors_count
    {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    {f : R →+* S} {p : Ideal R} {P : Ideal S}
    [IsDedekindDomain S] [DecidableEq (Ideal S)]
    (hp0 : Ideal.map f p ≠ ⊥)
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    Ideal.ramificationIdx f p P =
      Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (Ideal.map f p)) := by
  exact SourceStack.Ramification.ramificationIdx_eq_normalizedFactors_count hp0 hP hP0

theorem hilbert_ramificationIdx_ne_zero_of_dedekind
    {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    {f : R →+* S} {p : Ideal R} {P : Ideal S}
    [IsDedekindDomain S]
    (hp0 : Ideal.map f p ≠ ⊥)
    (hP : P.IsPrime)
    (hle : Ideal.map f p ≤ P) :
    Ideal.ramificationIdx f p P ≠ 0 := by
  exact SourceStack.Ramification.ramificationIdx_ne_zero_of_dedekind hp0 hP hle

theorem hilbert_inertiaDeg_algebraMap
    {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    (p : Ideal R) (P : Ideal S)
    [Algebra R S] [P.LiesOver p] [p.IsMaximal] :
    Ideal.inertiaDeg p P = Module.finrank (R ⧸ p) (S ⧸ P) := by
  exact SourceStack.Ramification.inertiaDeg_algebraMap p P

theorem hilbert_inertiaDeg_pos
    {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    (p : Ideal R) (P : Ideal S)
    [Algebra R S] [p.IsMaximal] [Module.Finite R S] [P.LiesOver p] :
    0 < Ideal.inertiaDeg p P := by
  exact SourceStack.Ramification.inertiaDeg_pos p P

theorem hilbert_ramificationIdx_tower
    {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    {T : Type w} [CommRing T]
    [IsDedekindDomain S] [IsDedekindDomain T]
    {f : R →+* S} {g : S →+* T}
    {p : Ideal R} {P : Ideal S} {Q : Ideal T}
    [P.IsPrime] [Q.IsPrime]
    (hg0 : Ideal.map g P ≠ ⊥)
    (hfg : Ideal.map (g.comp f) p ≠ ⊥)
    (hg : Ideal.map g P ≤ Q) :
    Ideal.ramificationIdx (g.comp f) p Q =
      Ideal.ramificationIdx f p P * Ideal.ramificationIdx g P Q := by
  exact SourceStack.Ramification.ramificationIdx_tower hg0 hfg hg

theorem hilbert_ramificationIdx_algebra_tower
    {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    {T : Type w} [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsDedekindDomain S] [IsDedekindDomain T]
    {p : Ideal R} {P : Ideal S} {Q : Ideal T}
    [P.IsPrime] [Q.IsPrime]
    (hg0 : Ideal.map (algebraMap S T) P ≠ ⊥)
    (hfg : Ideal.map (algebraMap R T) p ≠ ⊥)
    (hg : Ideal.map (algebraMap S T) P ≤ Q) :
    Ideal.ramificationIdx (algebraMap R T) p Q =
      Ideal.ramificationIdx (algebraMap R S) p P *
        Ideal.ramificationIdx (algebraMap S T) P Q := by
  exact SourceStack.Ramification.ramificationIdx_algebra_tower hg0 hfg hg

theorem hilbert_inertiaDeg_algebra_tower
    {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    {T : Type w} [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (p : Ideal R) (P : Ideal S) (I : Ideal T)
    [p.IsMaximal] [P.IsMaximal] [P.LiesOver p] [I.LiesOver P] :
    Ideal.inertiaDeg p I = Ideal.inertiaDeg p P * Ideal.inertiaDeg P I := by
  exact SourceStack.Ramification.inertiaDeg_algebra_tower p P I

theorem hilbert_sum_ramification_inertia
    (R : Type u) [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S]
    (p : Ideal R)
    (K : Type w) [Field K]
    (L : Type x) [Field L]
    [IsDedekindDomain R] [IsDedekindDomain S]
    [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L]
    [Algebra K L] [Algebra R L]
    [IsScalarTower R S L] [IsScalarTower R K L]
    [Module.Finite R S] [p.IsMaximal]
    (hp0 : p ≠ ⊥) :
    (∑ P ∈ @Multiset.toFinset (Ideal S) (Classical.decEq (Ideal S))
        (UniqueFactorizationMonoid.factors (Ideal.map (algebraMap R S) p)),
        Ideal.ramificationIdx (algebraMap R S) p P * Ideal.inertiaDeg p P) =
      Module.finrank K L := by
  exact SourceStack.Ramification.sum_ramification_inertia R S p K L hp0

theorem hilbert_decompositionSubgroup_eq_stabilizer
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) :
    ValuationSubring.decompositionSubgroup K A =
      MulAction.stabilizer (L ≃ₐ[K] L) A := by
  exact SourceStack.Ramification.decompositionSubgroup_eq_stabilizer K A

theorem hilbert_inertiaSubgroup_eq_ker
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) :
    ValuationSubring.inertiaSubgroup K A =
      MonoidHom.ker
        (MulSemiringAction.toRingAut
          (ValuationSubring.decompositionSubgroup K A)
          (IsLocalRing.ResidueField A)) := by
  exact SourceStack.Ramification.inertiaSubgroup_eq_ker K A

end Ramification

namespace DedekindDvr

universe u v

theorem hilbert_prime_isMaximal_of_dimensionLEOne
    {R : Type u} [CommRing R] [Ring.DimensionLEOne R]
    {p : Ideal R} (hp : p.IsPrime) (hne : p ≠ ⊥) :
    p.IsMaximal := by
  exact SourceStack.DedekindDvr.prime_isMaximal_of_dimensionLEOne hp hne

theorem hilbert_eq_bot_of_prime_lt_prime
    {R : Type u} [CommRing R] [Ring.DimensionLEOne R]
    (p P : Ideal R) [p.IsPrime] [P.IsPrime]
    (hlt : p < P) :
    p = ⊥ := by
  exact SourceStack.DedekindDvr.eq_bot_of_prime_lt_prime p P hlt

theorem hilbert_not_prime_chain_length_two
    {R : Type u} [CommRing R] [Ring.DimensionLEOne R]
    (p₀ p₁ p₂ : Ideal R) [p₁.IsPrime] [p₂.IsPrime] :
    ¬ (p₀ < p₁ ∧ p₁ < p₂) := by
  exact SourceStack.DedekindDvr.not_prime_chain_length_two p₀ p₁ p₂

theorem hilbert_principalIdealRing_dimensionLEOne
    (A : Type u) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] :
    Ring.DimensionLEOne A := by
  exact SourceStack.DedekindDvr.principalIdealRing_dimensionLEOne A

theorem hilbert_isDedekindDomain_iff_fractionField
    (A : Type u) [CommRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K] :
    IsDedekindDomain A ↔
      IsDomain A ∧ IsNoetherianRing A ∧ Ring.DimensionLEOne A ∧
        ∀ {x : K}, IsIntegral A x → ∃ y, (algebraMap A K) y = x := by
  exact SourceStack.DedekindDvr.isDedekindDomain_iff_fractionField A K

theorem hilbert_localization_isDedekindDomain
    (A : Type u) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    {M : Submonoid A} (hM : M ≤ nonZeroDivisors A)
    (Aₘ : Type v) [CommRing Aₘ] [IsDomain Aₘ] [Algebra A Aₘ]
    [IsLocalization M Aₘ] :
    IsDedekindDomain Aₘ := by
  exact SourceStack.DedekindDvr.localization_isDedekindDomain A hM Aₘ

theorem hilbert_localization_atPrime_isDedekindDomain
    (A : Type u) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (P : Ideal A) [P.IsPrime]
    (Aₘ : Type v) [CommRing Aₘ] [IsDomain Aₘ] [Algebra A Aₘ]
    [IsLocalization.AtPrime Aₘ P] :
    IsDedekindDomain Aₘ := by
  exact SourceStack.DedekindDvr.localization_atPrime_isDedekindDomain A P Aₘ

theorem hilbert_localization_atPrime_not_isField
    (A : Type u) [CommRing A] [IsDomain A]
    {P : Ideal A} (hP : P ≠ ⊥) [P.IsPrime]
    (Aₘ : Type v) [CommRing Aₘ] [Algebra A Aₘ]
    [IsLocalization.AtPrime Aₘ P] :
    ¬ IsField Aₘ := by
  exact SourceStack.DedekindDvr.localization_atPrime_not_isField A hP Aₘ

theorem hilbert_localization_atPrime_isDVR_of_dedekind
    (A : Type u) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    {P : Ideal A} (hP : P ≠ ⊥) [P.IsPrime]
    (Aₘ : Type v) [CommRing Aₘ] [IsDomain Aₘ] [Algebra A Aₘ]
    [IsLocalization.AtPrime Aₘ P] :
    IsDiscreteValuationRing Aₘ := by
  exact SourceStack.DedekindDvr.localization_atPrime_isDVR_of_dedekind A hP Aₘ

theorem hilbert_dedekindDomain_to_dedekindDomainDvr
    (A : Type u) [CommRing A] [IsDomain A] [IsDedekindDomain A] :
    IsDedekindDomainDvr A := by
  exact SourceStack.DedekindDvr.dedekindDomain_to_dedekindDomainDvr A

theorem hilbert_dedekindDomainDvr_isIntegrallyClosed
    (A : Type u) [CommRing A] [IsDomain A] [IsDedekindDomainDvr A] :
    IsIntegrallyClosed A := by
  exact SourceStack.DedekindDvr.dedekindDomainDvr_isIntegrallyClosed A

theorem hilbert_dedekindDomainDvr_to_dedekindDomain
    (A : Type u) [CommRing A] [IsDomain A] [IsDedekindDomainDvr A] :
    IsDedekindDomain A := by
  exact SourceStack.DedekindDvr.dedekindDomainDvr_to_dedekindDomain A

theorem hilbert_dvr_not_isField
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    ¬ IsField R := by
  exact SourceStack.DedekindDvr.dvr_not_isField R

theorem hilbert_irreducible_iff_uniformizer
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) :
    Irreducible ϖ ↔ IsLocalRing.maximalIdeal R = Ideal.span {ϖ} := by
  exact SourceStack.DedekindDvr.irreducible_iff_uniformizer ϖ

theorem hilbert_irreducible_maximalIdeal_eq
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ) :
    IsLocalRing.maximalIdeal R = Ideal.span {ϖ} := by
  exact SourceStack.DedekindDvr.irreducible_maximalIdeal_eq hϖ

theorem hilbert_exists_irreducible
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    ∃ ϖ : R, Irreducible ϖ := by
  exact SourceStack.DedekindDvr.exists_irreducible R

theorem hilbert_exists_prime
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    ∃ ϖ : R, Prime ϖ := by
  exact SourceStack.DedekindDvr.exists_prime R

theorem hilbert_dvr_iff_pid_with_one_nonzero_prime
    (R : Type u) [CommRing R] [IsDomain R] :
    IsDiscreteValuationRing R ↔
      IsPrincipalIdealRing R ∧ ∃! P : Ideal R, P ≠ ⊥ ∧ P.IsPrime := by
  exact SourceStack.DedekindDvr.dvr_iff_pid_with_one_nonzero_prime R

theorem hilbert_associated_of_irreducible
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {a b : R} (ha : Irreducible a) (hb : Irreducible b) :
    Associated a b := by
  exact SourceStack.DedekindDvr.associated_of_irreducible R ha hb

theorem hilbert_associated_pow_irreducible
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {x : R} (hx : x ≠ 0) {ϖ : R} (hϖ : Irreducible ϖ) :
    ∃ n : ℕ, Associated x (ϖ ^ n) := by
  exact SourceStack.DedekindDvr.associated_pow_irreducible hx hϖ

theorem hilbert_eq_unit_mul_pow_irreducible
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {x : R} (hx : x ≠ 0) {ϖ : R} (hϖ : Irreducible ϖ) :
    ∃ n : ℕ, ∃ u : Rˣ, x = (u : R) * ϖ ^ n := by
  exact SourceStack.DedekindDvr.eq_unit_mul_pow_irreducible hx hϖ

theorem hilbert_ideal_eq_span_pow_irreducible
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {I : Ideal R} (hI : I ≠ ⊥) {ϖ : R} (hϖ : Irreducible ϖ) :
    ∃ n : ℕ, I = Ideal.span {ϖ ^ n} := by
  exact SourceStack.DedekindDvr.ideal_eq_span_pow_irreducible hI hϖ

theorem hilbert_addVal_zero
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    IsDiscreteValuationRing.addVal R 0 = ⊤ := by
  exact SourceStack.DedekindDvr.addVal_zero

theorem hilbert_addVal_one
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    IsDiscreteValuationRing.addVal R 1 = 0 := by
  exact SourceStack.DedekindDvr.addVal_one

theorem hilbert_addVal_uniformizer
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ) :
    IsDiscreteValuationRing.addVal R ϖ = 1 := by
  exact SourceStack.DedekindDvr.addVal_uniformizer hϖ

theorem hilbert_addVal_mul
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {a b : R} :
    IsDiscreteValuationRing.addVal R (a * b) =
      IsDiscreteValuationRing.addVal R a + IsDiscreteValuationRing.addVal R b := by
  exact SourceStack.DedekindDvr.addVal_mul

theorem hilbert_addVal_pow
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (a : R) (n : ℕ) :
    IsDiscreteValuationRing.addVal R (a ^ n) =
      n • IsDiscreteValuationRing.addVal R a := by
  exact SourceStack.DedekindDvr.addVal_pow a n

theorem hilbert_addVal_eq_top_iff
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {a : R} :
    IsDiscreteValuationRing.addVal R a = ⊤ ↔ a = 0 := by
  exact SourceStack.DedekindDvr.addVal_eq_top_iff

theorem hilbert_addVal_le_iff_dvd
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {a b : R} :
    IsDiscreteValuationRing.addVal R a ≤ IsDiscreteValuationRing.addVal R b ↔ a ∣ b := by
  exact SourceStack.DedekindDvr.addVal_le_iff_dvd

theorem hilbert_addVal_add
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {a b : R} :
    IsDiscreteValuationRing.addVal R a ⊓ IsDiscreteValuationRing.addVal R b ≤
      IsDiscreteValuationRing.addVal R (a + b) := by
  exact SourceStack.DedekindDvr.addVal_add

end DedekindDvr

namespace FractionalIdeals

universe u v w x

theorem hilbert_coeIdeal_le_coeIdeal
    {R : Type u} [CommRing R]
    (K : Type v) [CommRing K] [Algebra R K] [IsFractionRing R K]
    {I J : Ideal R} :
    (I : FractionalIdeal R⁰ K) ≤ (J : FractionalIdeal R⁰ K) ↔ I ≤ J := by
  exact SourceStack.FractionalIdeals.coeIdeal_le_coeIdeal K

theorem hilbert_coeIdeal_injective
    {R : Type u} [CommRing R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K] :
    Function.Injective (fun I : Ideal R => (I : FractionalIdeal R⁰ K)) := by
  exact SourceStack.FractionalIdeals.coeIdeal_injective

theorem hilbert_coeIdeal_eq_zero
    {R : Type u} [CommRing R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    {I : Ideal R} :
    (I : FractionalIdeal R⁰ K) = 0 ↔ I = ⊥ := by
  exact SourceStack.FractionalIdeals.coeIdeal_eq_zero

theorem hilbert_coeIdeal_eq_one
    {R : Type u} [CommRing R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    {I : Ideal R} :
    (I : FractionalIdeal R⁰ K) = 1 ↔ I = 1 := by
  exact SourceStack.FractionalIdeals.coeIdeal_eq_one

theorem hilbert_coeIdeal_mul
    {R : Type u} [CommRing R]
    {S : Submonoid R} {P : Type v} [CommRing P] [Algebra R P]
    (I J : Ideal R) :
    ((I * J : Ideal R) : FractionalIdeal S P) =
      (I : FractionalIdeal S P) * (J : FractionalIdeal S P) := by
  exact SourceStack.FractionalIdeals.coeIdeal_mul I J

theorem hilbert_coeIdeal_pow
    {R : Type u} [CommRing R]
    (S : Submonoid R) (P : Type v) [CommRing P] [Algebra R P]
    (I : Ideal R) (n : ℕ) :
    ((I ^ n : Ideal R) : FractionalIdeal S P) =
      (I : FractionalIdeal S P) ^ n := by
  exact SourceStack.FractionalIdeals.coeIdeal_pow S P I n

theorem hilbert_map_comp
    {R : Type u} [CommRing R]
    {S : Submonoid R}
    {P : Type v} [CommRing P] [Algebra R P]
    {P' : Type w} [CommRing P'] [Algebra R P']
    {P'' : Type x} [CommRing P''] [Algebra R P'']
    (I : FractionalIdeal S P) (g : P →ₐ[R] P') (g' : P' →ₐ[R] P'') :
    FractionalIdeal.map (g'.comp g) I =
      FractionalIdeal.map g' (FractionalIdeal.map g I) := by
  exact SourceStack.FractionalIdeals.map_comp I g g'

theorem hilbert_map_add
    {R : Type u} [CommRing R]
    {S : Submonoid R}
    {P : Type v} [CommRing P] [Algebra R P]
    {P' : Type w} [CommRing P'] [Algebra R P']
    (I J : FractionalIdeal S P) (g : P →ₐ[R] P') :
    FractionalIdeal.map g (I + J) =
      FractionalIdeal.map g I + FractionalIdeal.map g J := by
  exact SourceStack.FractionalIdeals.map_add I J g

theorem hilbert_map_mul
    {R : Type u} [CommRing R]
    {S : Submonoid R}
    {P : Type v} [CommRing P] [Algebra R P]
    {P' : Type w} [CommRing P'] [Algebra R P']
    (I J : FractionalIdeal S P) (g : P →ₐ[R] P') :
    FractionalIdeal.map g (I * J) =
      FractionalIdeal.map g I * FractionalIdeal.map g J := by
  exact SourceStack.FractionalIdeals.map_mul I J g

theorem hilbert_map_injective
    {R : Type u} [CommRing R]
    {S : Submonoid R}
    {P : Type v} [CommRing P] [Algebra R P]
    {P' : Type w} [CommRing P'] [Algebra R P']
    (g : P →ₐ[R] P') (hg : Function.Injective g) :
    Function.Injective (FractionalIdeal.map (S := S) g) := by
  exact SourceStack.FractionalIdeals.map_injective g hg

theorem hilbert_mem_spanSingleton
    {R : Type u} [CommRing R]
    {S : Submonoid R}
    {P : Type v} [CommRing P] [Algebra R P] [IsLocalization S P]
    {x y : P} :
    x ∈ FractionalIdeal.spanSingleton S y ↔ ∃ z : R, z • y = x := by
  exact SourceStack.FractionalIdeals.mem_spanSingleton

theorem hilbert_spanSingleton_mul_spanSingleton
    {R : Type u} [CommRing R]
    {S : Submonoid R}
    {P : Type v} [CommRing P] [Algebra R P] [IsLocalization S P]
    (x y : P) :
    FractionalIdeal.spanSingleton S x * FractionalIdeal.spanSingleton S y =
      FractionalIdeal.spanSingleton S (x * y) := by
  exact SourceStack.FractionalIdeals.spanSingleton_mul_spanSingleton x y

theorem hilbert_spanSingleton_pow
    {R : Type u} [CommRing R]
    {S : Submonoid R}
    {P : Type v} [CommRing P] [Algebra R P] [IsLocalization S P]
    (x : P) (n : ℕ) :
    FractionalIdeal.spanSingleton S x ^ n =
      FractionalIdeal.spanSingleton S (x ^ n) := by
  exact SourceStack.FractionalIdeals.spanSingleton_pow x n

theorem hilbert_coeIdeal_span_singleton
    {R : Type u} [CommRing R]
    {S : Submonoid R}
    {P : Type v} [CommRing P] [Algebra R P] [IsLocalization S P]
    (x : R) :
    ((Ideal.span {x} : Ideal R) : FractionalIdeal S P) =
      FractionalIdeal.spanSingleton S ((algebraMap R P) x) := by
  exact SourceStack.FractionalIdeals.coeIdeal_span_singleton x

theorem hilbert_isPrincipal_iff
    {R : Type u} [CommRing R]
    {S : Submonoid R}
    {P : Type v} [CommRing P] [Algebra R P] [IsLocalization S P]
    (I : FractionalIdeal S P) :
    (I : Submodule R P).IsPrincipal ↔
      ∃ x : P, I = FractionalIdeal.spanSingleton S x := by
  exact SourceStack.FractionalIdeals.isPrincipal_iff I

theorem hilbert_exists_eq_spanSingleton_mul
    {R : Type u} [CommRing R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K] [IsDomain R]
    (I : FractionalIdeal R⁰ K) :
    ∃ a : R, ∃ aI : Ideal R, a ≠ 0 ∧
      I = FractionalIdeal.spanSingleton R⁰ ((algebraMap R K) a)⁻¹ *
        (aI : FractionalIdeal R⁰ K) := by
  exact SourceStack.FractionalIdeals.exists_eq_spanSingleton_mul I

theorem hilbert_div_spanSingleton
    {R : Type u} [CommRing R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K] [IsDomain R]
    (J : FractionalIdeal R⁰ K) (d : K) :
    J / FractionalIdeal.spanSingleton R⁰ d =
      FractionalIdeal.spanSingleton R⁰ d⁻¹ * J := by
  exact SourceStack.FractionalIdeals.div_spanSingleton J d

theorem hilbert_extended_add
    {A : Type u} [CommRing A]
    {B : Type v} [CommRing B]
    {f : A →+* B}
    {K : Type w} {M : Submonoid A} [CommRing K] [Algebra A K] [IsLocalization M K]
    (L : Type x) {N : Submonoid B} [CommRing L] [Algebra B L] [IsLocalization N L]
    (hf : M ≤ Submonoid.comap f N)
    (I J : FractionalIdeal M K) :
    FractionalIdeal.extended L hf (I + J) =
      FractionalIdeal.extended L hf I + FractionalIdeal.extended L hf J := by
  exact SourceStack.FractionalIdeals.extended_add L hf I J

theorem hilbert_extended_mul
    {A : Type u} [CommRing A]
    {B : Type v} [CommRing B]
    {f : A →+* B}
    {K : Type w} {M : Submonoid A} [CommRing K] [Algebra A K] [IsLocalization M K]
    (L : Type x) {N : Submonoid B} [CommRing L] [Algebra B L] [IsLocalization N L]
    (hf : M ≤ Submonoid.comap f N)
    (I J : FractionalIdeal M K) :
    FractionalIdeal.extended L hf (I * J) =
      FractionalIdeal.extended L hf I * FractionalIdeal.extended L hf J := by
  exact SourceStack.FractionalIdeals.extended_mul L hf I J

theorem hilbert_absNorm_eq_zero_iff
    {R : Type u} [CommRing R] [IsDedekindDomain R] [Module.Free ℤ R]
    [Module.Finite ℤ R]
    {K : Type v} [CommRing K] [Algebra R K] [IsFractionRing R K]
    [NoZeroDivisors K] {I : FractionalIdeal R⁰ K} :
    FractionalIdeal.absNorm I = 0 ↔ I = 0 := by
  exact SourceStack.FractionalIdeals.absNorm_eq_zero_iff

theorem hilbert_coeIdeal_absNorm
    {R : Type u} [CommRing R] [IsDedekindDomain R] [Module.Free ℤ R]
    [Module.Finite ℤ R]
    {K : Type v} [CommRing K] [Algebra R K] [IsFractionRing R K]
    (I : Ideal R) :
    FractionalIdeal.absNorm (I : FractionalIdeal R⁰ K) =
      (Ideal.absNorm I : ℤ) := by
  exact SourceStack.FractionalIdeals.coeIdeal_absNorm I

end FractionalIdeals

namespace ArithmeticFunctionFields

universe u v w

theorem hilbert_functionField_iff_finiteDimensional
    (Fq : Type u) [Field Fq]
    (F : Type v) [Field F]
    (Fqt : Type w) [Field Fqt] [Algebra Fq[X] Fqt]
    [IsFractionRing Fq[X] Fqt]
    [Algebra (RatFunc Fq) F] [Algebra Fqt F] [Algebra Fq[X] F]
    [IsScalarTower Fq[X] Fqt F] [IsScalarTower Fq[X] (RatFunc Fq) F] :
    FunctionField Fq F ↔ FiniteDimensional Fqt F := by
  exact SourceStack.ArithmeticFunctionFields.functionField_iff_finiteDimensional Fq F Fqt

theorem hilbert_polynomial_algebraMap_injective
    (Fq : Type u) [Field Fq]
    (F : Type v) [Field F]
    [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
    [IsScalarTower Fq[X] (RatFunc Fq) F] :
    Function.Injective (algebraMap Fq[X] F) := by
  exact SourceStack.ArithmeticFunctionFields.polynomial_algebraMap_injective Fq F

namespace RingOfIntegers

theorem hilbert_isDomain
    (Fq : Type u) [Field Fq]
    (F : Type v) [Field F] [Algebra Fq[X] F] :
    IsDomain (FunctionField.ringOfIntegers Fq F) := by
  exact SourceStack.ArithmeticFunctionFields.RingOfIntegers.isDomain Fq F

theorem hilbert_not_isField
    (Fq : Type u) [Field Fq]
    (F : Type v) [Field F]
    [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
    [IsScalarTower Fq[X] (RatFunc Fq) F] :
    ¬ IsField (FunctionField.ringOfIntegers Fq F) := by
  exact SourceStack.ArithmeticFunctionFields.RingOfIntegers.not_isField Fq F

theorem hilbert_isFractionRing
    (Fq : Type u) [Field Fq]
    (F : Type v) [Field F]
    [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
    [IsScalarTower Fq[X] (RatFunc Fq) F]
    [FunctionField Fq F] :
    IsFractionRing (FunctionField.ringOfIntegers Fq F) F := by
  exact SourceStack.ArithmeticFunctionFields.RingOfIntegers.isFractionRing Fq F

theorem hilbert_isDedekindDomain
    (Fq : Type u) [Field Fq]
    (F : Type v) [Field F]
    [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
    [IsScalarTower Fq[X] (RatFunc Fq) F]
    [FunctionField Fq F] [Algebra.IsSeparable (RatFunc Fq) F] :
    IsDedekindDomain (FunctionField.ringOfIntegers Fq F) := by
  exact SourceStack.ArithmeticFunctionFields.RingOfIntegers.isDedekindDomain Fq F

end RingOfIntegers

namespace InftyValuation

theorem hilbert_map_mul
    (Fq : Type u) [Field Fq] [DecidableEq (RatFunc Fq)]
    (x y : RatFunc Fq) :
    FunctionField.inftyValuationDef Fq (x * y) =
      FunctionField.inftyValuationDef Fq x * FunctionField.inftyValuationDef Fq y := by
  exact SourceStack.ArithmeticFunctionFields.InftyValuation.map_mul Fq x y

theorem hilbert_map_add_le_max
    (Fq : Type u) [Field Fq] [DecidableEq (RatFunc Fq)]
    (x y : RatFunc Fq) :
    FunctionField.inftyValuationDef Fq (x + y) ≤
      max (FunctionField.inftyValuationDef Fq x) (FunctionField.inftyValuationDef Fq y) := by
  exact SourceStack.ArithmeticFunctionFields.InftyValuation.map_add_le_max Fq x y

theorem hilbert_C
    (Fq : Type u) [Field Fq] [DecidableEq (RatFunc Fq)]
    {k : Fq} (hk : k ≠ 0) :
    FunctionField.inftyValuationDef Fq (RatFunc.C k) =
      Multiplicative.ofAdd (0 : ℤ) := by
  exact SourceStack.ArithmeticFunctionFields.InftyValuation.C Fq hk

theorem hilbert_X
    (Fq : Type u) [Field Fq] [DecidableEq (RatFunc Fq)] :
    FunctionField.inftyValuationDef Fq RatFunc.X =
      Multiplicative.ofAdd (1 : ℤ) := by
  exact SourceStack.ArithmeticFunctionFields.InftyValuation.X Fq

theorem hilbert_polynomial
    (Fq : Type u) [Field Fq] [DecidableEq (RatFunc Fq)]
    {p : Fq[X]} (hp : p ≠ 0) :
    FunctionField.inftyValuationDef Fq (algebraMap Fq[X] (RatFunc Fq) p) =
      Multiplicative.ofAdd (p.natDegree : ℤ) := by
  exact SourceStack.ArithmeticFunctionFields.InftyValuation.polynomial Fq hp

theorem hilbert_FqtInfty_field
    (Fq : Type u) [Field Fq] [DecidableEq (RatFunc Fq)] :
    Nonempty (Field (FunctionField.FqtInfty Fq)) := by
  exact SourceStack.ArithmeticFunctionFields.InftyValuation.FqtInfty_field Fq

end InftyValuation

end ArithmeticFunctionFields

namespace Cohomology

universe w' w v u

theorem hilbert_sheaf_H_eq_ext
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (F : Sheaf J AddCommGrp.{w})
    [HasSheafify J AddCommGrp.{w}] [HasExt.{w'} (Sheaf J AddCommGrp.{w})]
    (n : ℕ) :
    F.H n =
      Ext ((CategoryTheory.constantSheaf J AddCommGrp.{w}).obj
        (AddCommGrp.of (ULift ℤ))) F n := by
  exact SourceStack.Cohomology.sheaf_H_eq_ext F n

theorem hilbert_sheaf_H_addCommGroup
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (F : Sheaf J AddCommGrp.{w})
    [HasSheafify J AddCommGrp.{w}] [HasExt.{w'} (Sheaf J AddCommGrp.{w})]
    (n : ℕ) :
    Nonempty (AddCommGroup (F.H n)) := by
  exact SourceStack.Cohomology.sheaf_H_addCommGroup F n

theorem hilbert_cohomologyPresheafFunctor_exists
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrp.{v}] [HasExt.{w'} (Sheaf J AddCommGrp.{v})]
    (n : ℕ) :
    Nonempty (Sheaf J AddCommGrp.{v} ⥤ Cᵒᵖ ⥤ AddCommGrp.{w'}) := by
  exact SourceStack.Cohomology.cohomologyPresheafFunctor_exists J n

theorem hilbert_cohomologyPresheaf_exists
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrp.{v}] [HasExt.{w'} (Sheaf J AddCommGrp.{v})]
    (F : Sheaf J AddCommGrp.{v}) (n : ℕ) :
    Nonempty (Cᵒᵖ ⥤ AddCommGrp.{w'}) := by
  exact SourceStack.Cohomology.cohomologyPresheaf_exists J F n

theorem hilbert_scheme_modules_abelian
    (X : Scheme.{u}) :
    Nonempty (Abelian X.Modules) := by
  exact SourceStack.Cohomology.scheme_modules_abelian X

end Cohomology

namespace SmoothKaehler

universe u v w t t' q q'

theorem hilbert_formallySmooth_exists_lift
    {R : Type u} [CommSemiring R]
    {A : Type u} [Semiring A] [Algebra R A]
    {B : Type u} [CommRing B] [Algebra R B]
    [Algebra.FormallySmooth R A]
    (I : Ideal B) (hI : IsNilpotent I) (g : A →ₐ[R] B ⧸ I) :
    ∃ f : A →ₐ[R] B, (Ideal.Quotient.mkₐ R I).comp f = g := by
  exact SourceStack.SmoothKaehler.formallySmooth_exists_lift I hI g

theorem hilbert_formallySmooth_polynomial
    (R : Type u) [CommSemiring R] :
    Algebra.FormallySmooth R R[X] := by
  exact SourceStack.SmoothKaehler.formallySmooth_polynomial R

theorem hilbert_formallySmooth_mvPolynomial
    (R : Type u) [CommSemiring R] (σ : Type u) :
    Algebra.FormallySmooth R (MvPolynomial σ R) := by
  exact SourceStack.SmoothKaehler.formallySmooth_mvPolynomial R σ

theorem hilbert_formallySmooth_comp
    (R : Type u) [CommSemiring R]
    (A : Type u) [CommSemiring A] [Algebra R A]
    (B : Type u) [Semiring B] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B]
    [Algebra.FormallySmooth R A] [Algebra.FormallySmooth A B] :
    Algebra.FormallySmooth R B := by
  exact SourceStack.SmoothKaehler.formallySmooth_comp R A B

theorem hilbert_formallySmooth_base_change
    {R : Type u} [CommSemiring R]
    {A : Type u} [Semiring A] [Algebra R A]
    (B : Type u) [CommSemiring B] [Algebra R B]
    [Algebra.FormallySmooth R A] :
    Algebra.FormallySmooth B (B ⊗[R] A) := by
  exact SourceStack.SmoothKaehler.formallySmooth_base_change B

theorem hilbert_formallySmooth_localization_map
    {R S Rₘ Sₘ : Type u}
    [CommRing R] [CommRing S] [CommRing Rₘ] [CommRing Sₘ]
    (M : Submonoid R)
    [Algebra R S] [Algebra R Sₘ] [Algebra S Sₘ]
    [Algebra R Rₘ] [Algebra Rₘ Sₘ]
    [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]
    [IsLocalization M Rₘ] [IsLocalization (Submonoid.map (algebraMap R S) M) Sₘ]
    [Algebra.FormallySmooth R S] :
    Algebra.FormallySmooth Rₘ Sₘ := by
  exact SourceStack.SmoothKaehler.formallySmooth_localization_map
    (R := R) (S := S) (Rₘ := Rₘ) (Sₘ := Sₘ) M

theorem hilbert_formallySmooth_pi_iff
    {R : Type (max u v)} {I : Type u} (A : I → Type (max u v))
    [CommRing R] [(i : I) → CommRing (A i)]
    [(i : I) → Algebra R (A i)] [Finite I] :
    Algebra.FormallySmooth R ((i : I) → A i) ↔
      ∀ i, Algebra.FormallySmooth R (A i) := by
  exact SourceStack.SmoothKaehler.formallySmooth_pi_iff A

theorem hilbert_smooth_of_isLocalization_Away
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (r : R) [IsLocalization.Away r A] :
    Algebra.Smooth R A := by
  exact SourceStack.SmoothKaehler.smooth_of_isLocalization_Away r

theorem hilbert_smooth_comp
    (R : Type u) [CommRing R]
    (A B : Type u) [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra.Smooth R A] [Algebra.Smooth A B] :
    Algebra.Smooth R B := by
  exact SourceStack.SmoothKaehler.smooth_comp R A B

theorem hilbert_smooth_baseChange
    (R : Type u) [CommRing R]
    (A B : Type u) [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] [Algebra.Smooth R A] :
    Algebra.Smooth B (B ⊗[R] A) := by
  exact SourceStack.SmoothKaehler.smooth_baseChange R A B

theorem hilbert_standardSmooth_finitePresentation
    {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsStandardSmooth.{t, q} R S] :
    Algebra.FinitePresentation R S := by
  exact SourceStack.SmoothKaehler.standardSmooth_finitePresentation

theorem hilbert_standardSmooth_trans
    (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S]
    (T : Type w) [CommRing T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T]
    [Algebra.IsStandardSmooth.{t, q} R S]
    [Algebra.IsStandardSmooth.{t', q'} S T] :
    Algebra.IsStandardSmooth.{max t t', max q q'} R T := by
  exact SourceStack.SmoothKaehler.standardSmooth_trans R S T

theorem hilbert_standardSmooth_localization_away
    {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    (r : R) [IsLocalization.Away r S] :
    Algebra.IsStandardSmooth.{0, 0} R S := by
  exact SourceStack.SmoothKaehler.standardSmooth_localization_away r

theorem hilbert_standardSmooth_baseChange
    {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    (T : Type w) [CommRing T] [Algebra R T]
    [Algebra.IsStandardSmooth.{t, q} R S] :
    Algebra.IsStandardSmooth.{t, q} T (T ⊗[R] S) := by
  exact SourceStack.SmoothKaehler.standardSmooth_baseChange T

theorem hilbert_standardSmoothOfRelativeDimension_isStandardSmooth
    (n : ℕ) {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsStandardSmoothOfRelativeDimension.{t, q} n R S] :
    Algebra.IsStandardSmooth.{t, q} R S := by
  exact SourceStack.SmoothKaehler.standardSmoothOfRelativeDimension_isStandardSmooth n

theorem hilbert_standardSmoothOfRelativeDimension_id
    (R : Type u) [CommRing R] :
    Algebra.IsStandardSmoothOfRelativeDimension.{t, q} 0 R R := by
  exact SourceStack.SmoothKaehler.standardSmoothOfRelativeDimension_id R

theorem hilbert_standardSmoothOfRelativeDimension_trans
    (n m : ℕ)
    (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S]
    (T : Type w) [CommRing T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T]
    [Algebra.IsStandardSmoothOfRelativeDimension.{t, q} n R S]
    [Algebra.IsStandardSmoothOfRelativeDimension.{t', q'} m S T] :
    Algebra.IsStandardSmoothOfRelativeDimension.{max t t', max q q'} (m + n) R T := by
  exact SourceStack.SmoothKaehler.standardSmoothOfRelativeDimension_trans n m R S T

theorem hilbert_standardSmoothOfRelativeDimension_localization_away
    {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    (r : R) [IsLocalization.Away r S] :
    Algebra.IsStandardSmoothOfRelativeDimension.{0, 0} 0 R S := by
  exact SourceStack.SmoothKaehler.standardSmoothOfRelativeDimension_localization_away r

theorem hilbert_standardSmoothOfRelativeDimension_baseChange
    (n : ℕ)
    {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    (T : Type w) [CommRing T] [Algebra R T]
    [Algebra.IsStandardSmoothOfRelativeDimension.{t, q} n R S] :
    Algebra.IsStandardSmoothOfRelativeDimension.{t, q} n T (T ⊗[R] S) := by
  exact SourceStack.SmoothKaehler.standardSmoothOfRelativeDimension_baseChange n T

theorem hilbert_formallySmooth_iff_injective_and_projective
    {R P S : Type u} [CommRing R] [CommRing P] [CommRing S]
    [Algebra R P] [Algebra P S] [Algebra R S] [IsScalarTower R P S]
    (hf : Function.Surjective (algebraMap P S))
    [Algebra.FormallySmooth R P] :
    Algebra.FormallySmooth R S ↔
      Function.Injective (KaehlerDifferential.kerCotangentToTensor R P S) ∧
        Module.Projective S (Ω[S⁄R]) := by
  exact SourceStack.SmoothKaehler.formallySmooth_iff_injective_and_projective hf

theorem hilbert_formallySmooth_iff_subsingleton_and_projective
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] :
    Algebra.FormallySmooth R S ↔
      Subsingleton (Algebra.H1Cotangent R S) ∧ Module.Projective S (Ω[S⁄R]) := by
  exact SourceStack.SmoothKaehler.formallySmooth_iff_subsingleton_and_projective

theorem hilbert_kaehler_ideal_fg
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] :
    (KaehlerDifferential.ideal R S).FG := by
  exact SourceStack.SmoothKaehler.kaehler_ideal_fg R S

theorem hilbert_kaehler_finite
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] :
    Module.Finite S (Ω[S⁄R]) := by
  exact SourceStack.SmoothKaehler.kaehler_finite R S

theorem hilbert_kaehler_polynomialEquiv_D
    (R : Type u) [CommRing R] (P : R[X]) :
    (KaehlerDifferential.polynomialEquiv R)
      ((KaehlerDifferential.D R R[X]) P) =
        Polynomial.derivative P := by
  exact SourceStack.SmoothKaehler.kaehler_polynomialEquiv_D R P

theorem hilbert_kaehler_mvPolynomialBasis_repr_D_X
    (R : Type u) [CommRing R] (σ : Type v) (i : σ) :
    (KaehlerDifferential.mvPolynomialBasis R σ).repr
      ((KaehlerDifferential.D R (MvPolynomial σ R)) (MvPolynomial.X i)) =
        Finsupp.single i 1 := by
  exact SourceStack.SmoothKaehler.kaehler_mvPolynomialBasis_repr_D_X R σ i

end SmoothKaehler

namespace Schemes

universe u

variable {X Y Z : Scheme.{u}}

theorem hilbert_openImmersion_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    IsOpenImmersion (f ≫ g) := by
  exact SourceStack.Schemes.openImmersion_comp f g

theorem hilbert_openImmersion_mono
    (f : X ⟶ Y) [IsOpenImmersion f] :
    Mono f := by
  exact SourceStack.Schemes.openImmersion_mono f

theorem hilbert_openImmersion_locallyOfFiniteType
    (f : X ⟶ Y) [IsOpenImmersion f] :
    LocallyOfFiniteType f := by
  exact SourceStack.Schemes.openImmersion_locallyOfFiniteType f

theorem hilbert_openImmersion_isSmooth
    (f : X ⟶ Y) [IsOpenImmersion f] :
    IsSmooth f := by
  exact SourceStack.Schemes.openImmersion_isSmooth f

theorem hilbert_openImmersion_isEtale
    (f : X ⟶ Y) [IsOpenImmersion f] :
    IsEtale f := by
  exact SourceStack.Schemes.openImmersion_isEtale f

theorem hilbert_openImmersion_isSeparated
    (f : X ⟶ Y) [IsOpenImmersion f] :
    IsSeparated f := by
  exact SourceStack.Schemes.openImmersion_isSeparated f

theorem hilbert_affineHom_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsAffineHom f] [IsAffineHom g] :
    IsAffineHom (f ≫ g) := by
  exact SourceStack.Schemes.affineHom_comp f g

theorem hilbert_affineHom_stable_under_base_change :
    MorphismProperty.IsStableUnderBaseChange (@IsAffineHom) := by
  exact SourceStack.Schemes.affineHom_stable_under_base_change

theorem hilbert_affineHom_quasiCompact
    (f : X ⟶ Y) [IsAffineHom f] :
    QuasiCompact f := by
  exact SourceStack.Schemes.affineHom_quasiCompact f

theorem hilbert_affineHom_isSeparated
    (f : X ⟶ Y) [IsAffineHom f] :
    IsSeparated f := by
  exact SourceStack.Schemes.affineHom_isSeparated f

theorem hilbert_affineHom_isAffine_of_target
    (f : X ⟶ Y) [IsAffineHom f] [IsAffine Y] :
    IsAffine X := by
  exact SourceStack.Schemes.affineHom_isAffine_of_target f

theorem hilbert_finite_isAffineHom
    (f : X ⟶ Y) [IsFinite f] :
    IsAffineHom f := by
  exact SourceStack.Schemes.finite_isAffineHom f

theorem hilbert_finite_isSeparated
    (f : X ⟶ Y) [IsFinite f] :
    IsSeparated f := by
  exact SourceStack.Schemes.finite_isSeparated f

theorem hilbert_integralHom_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsIntegralHom f] [IsIntegralHom g] :
    IsIntegralHom (f ≫ g) := by
  exact SourceStack.Schemes.integralHom_comp f g

theorem hilbert_integralHom_stable_under_base_change :
    MorphismProperty.IsStableUnderBaseChange (@IsIntegralHom) := by
  exact SourceStack.Schemes.integralHom_stable_under_base_change

theorem hilbert_integralHom_restrict
    (f : X ⟶ Y) [IsIntegralHom f] (U : Y.Opens) :
    IsIntegralHom (f ∣_ U) := by
  exact SourceStack.Schemes.integralHom_restrict f U

theorem hilbert_finite_of_integralHom_and_locallyOfFiniteType
    (f : X ⟶ Y) [IsIntegralHom f] [LocallyOfFiniteType f] :
    IsFinite f := by
  exact SourceStack.Schemes.finite_of_integralHom_and_locallyOfFiniteType f

theorem hilbert_quasiCompact_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiCompact g] :
    QuasiCompact (f ≫ g) := by
  exact SourceStack.Schemes.quasiCompact_comp f g

theorem hilbert_quasiCompact_stable_under_base_change :
    MorphismProperty.IsStableUnderBaseChange (@QuasiCompact) := by
  exact SourceStack.Schemes.quasiCompact_stable_under_base_change

theorem hilbert_quasiCompact_isCompact_preimage
    (f : X ⟶ Y) [QuasiCompact f] {U : Set Y}
    (hUopen : IsOpen U) (hUcompact : IsCompact U) :
    IsCompact (f.base ⁻¹' U) := by
  exact SourceStack.Schemes.quasiCompact_isCompact_preimage f hUopen hUcompact

theorem hilbert_compactSpace_iff_quasiCompact (X : Scheme.{u}) :
    CompactSpace X ↔ QuasiCompact (CategoryTheory.Limits.terminal.from X) := by
  exact SourceStack.Schemes.compactSpace_iff_quasiCompact X

theorem hilbert_quasiCompact_over_affine_iff
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] :
    QuasiCompact f ↔ CompactSpace X := by
  exact SourceStack.Schemes.quasiCompact_over_affine_iff f

theorem hilbert_finite_quasiCompact
    (f : X ⟶ Y) [IsFinite f] :
    QuasiCompact f := by
  exact SourceStack.Schemes.finite_quasiCompact f

theorem hilbert_proper_quasiCompact
    (f : X ⟶ Y) [IsProper f] :
    QuasiCompact f := by
  exact SourceStack.Schemes.proper_quasiCompact f

theorem hilbert_quasiSeparated_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiSeparated f] [QuasiSeparated g] :
    QuasiSeparated (f ≫ g) := by
  exact SourceStack.Schemes.quasiSeparated_comp f g

theorem hilbert_quasiSeparated_stable_under_base_change :
    MorphismProperty.IsStableUnderBaseChange (@QuasiSeparated) := by
  exact SourceStack.Schemes.quasiSeparated_stable_under_base_change

theorem hilbert_quasiSeparated_over_affine_iff
    (f : X ⟶ Y) [IsAffine Y] :
    QuasiSeparated f ↔ QuasiSeparatedSpace X := by
  exact SourceStack.Schemes.quasiSeparated_over_affine_iff f

theorem hilbert_quasiSeparatedSpace_iff_quasiSeparated
    (X : Scheme.{u}) :
    QuasiSeparatedSpace X ↔ QuasiSeparated (CategoryTheory.Limits.terminal.from X) := by
  exact SourceStack.Schemes.quasiSeparatedSpace_iff_quasiSeparated X

theorem hilbert_affine_quasiSeparatedSpace
    (X : Scheme.{u}) [IsAffine X] :
    QuasiSeparatedSpace X := by
  exact SourceStack.Schemes.affine_quasiSeparatedSpace X

theorem hilbert_isCompact_basicOpen
    (X : Scheme.{u}) {U : X.Opens} (hU : IsCompact (U : Set X))
    (f : Γ(X, U)) :
    IsCompact (X.basicOpen f : Set X) := by
  exact SourceStack.Schemes.isCompact_basicOpen X hU f

theorem hilbert_isUnit_res_basicOpen
    (X : Scheme.{u}) {U : X.Opens} (f : Γ(X, U)) :
    IsUnit (f |_ᵣ X.basicOpen f) := by
  exact SourceStack.Schemes.isUnit_res_basicOpen X f

theorem hilbert_basicOpenUnit_coe
    (X : Scheme.{u}) {U : X.Opens} (f : Γ(X, U)) :
    (SourceStack.Schemes.basicOpenUnit X f : Γ(X, X.basicOpen f)) =
      f |_ᵣ X.basicOpen f := by
  exact SourceStack.Schemes.basicOpenUnit_coe X f

theorem hilbert_opensTopUnit_coe
    (U : X.Opens) (u : Γ(X, U)ˣ) :
    (SourceStack.Schemes.opensTopUnit U u : Γ(U, ⊤)) =
      U.topIso.inv u := by
  exact SourceStack.Schemes.opensTopUnit_coe U u

theorem hilbert_basicOpenTopUnit_coe
    (X : Scheme.{u}) {U : X.Opens} (f : Γ(X, U)) :
    (SourceStack.Schemes.basicOpenTopUnit X f : Γ(X.basicOpen f, ⊤)) =
      (X.basicOpen f).topIso.inv (f |_ᵣ X.basicOpen f) := by
  exact SourceStack.Schemes.basicOpenTopUnit_coe X f

theorem hilbert_basicOpenTopRestrict_self
    (X : Scheme.{u}) (f : Γ(X, ⊤)) :
    SourceStack.Schemes.basicOpenTopRestrict X f f =
      (SourceStack.Schemes.basicOpenTopUnit X f : Γ(X.basicOpen f, ⊤)) := by
  exact SourceStack.Schemes.basicOpenTopRestrict_self X f

theorem hilbert_isUnit_basicOpenTopRestrict_self
    (X : Scheme.{u}) (f : Γ(X, ⊤)) :
    IsUnit (SourceStack.Schemes.basicOpenTopRestrict X f f) := by
  exact SourceStack.Schemes.isUnit_basicOpenTopRestrict_self X f

theorem hilbert_iSup_basicOpen_of_span_eq_top
    (X : Scheme.{u}) (U : X.Opens) (s : Set Γ(X, U))
    (hs : Ideal.span s = ⊤) :
    (⨆ f ∈ s, X.basicOpen f) = U := by
  exact SourceStack.Schemes.iSup_basicOpen_of_span_eq_top X U s hs

theorem hilbert_iSup_basicOpen_range_eq_top_of_span_eq_top
    (X : Scheme.{u}) {ι : Type*} (f : ι → Γ(X, ⊤))
    (hs : Ideal.span (Set.range f) = ⊤) :
    (⨆ i, X.basicOpen (f i)) = ⊤ := by
  exact SourceStack.Schemes.iSup_basicOpen_range_eq_top_of_span_eq_top X f hs

theorem hilbert_basicOpenCoverOfSpanEqTop_iSup_opensRange
    (X : Scheme.{u}) {ι : Type*} (f : ι → Γ(X, ⊤))
    (hs : Ideal.span (Set.range f) = ⊤) :
    (⨆ i, ((SourceStack.Schemes.basicOpenCoverOfSpanEqTop X f hs).map i).opensRange) =
      ⊤ := by
  exact Scheme.OpenCover.iSup_opensRange
    (SourceStack.Schemes.basicOpenCoverOfSpanEqTop X f hs)

theorem hilbert_twoElementFamily_zero {R : Type*} (x y : R) :
    SourceStack.Schemes.twoElementFamily x y 0 = x := by
  exact SourceStack.Schemes.twoElementFamily_zero x y

theorem hilbert_twoElementFamily_one {R : Type*} (x y : R) :
    SourceStack.Schemes.twoElementFamily x y 1 = y := by
  exact SourceStack.Schemes.twoElementFamily_one x y

theorem hilbert_ideal_span_range_twoElementFamily_eq_top_of_linear_combination
    {R : Type*} [CommSemiring R] (x y a b : R)
    (h : a * x + b * y = 1) :
    Ideal.span (Set.range (SourceStack.Schemes.twoElementFamily x y)) = ⊤ := by
  exact SourceStack.Schemes.ideal_span_range_twoElementFamily_eq_top_of_linear_combination
    x y a b h

theorem hilbert_twoSectionBasicOpenCoverOfLinearCombination_iSup_opensRange
    (X : Scheme.{u}) (s0 s1 a b : Γ(X, ⊤))
    (h : a * s0 + b * s1 = 1) :
    (⨆ i, ((SourceStack.Schemes.twoSectionBasicOpenCoverOfLinearCombination
      X s0 s1 a b h).map i).opensRange) = ⊤ := by
  exact Scheme.OpenCover.iSup_opensRange
    (SourceStack.Schemes.twoSectionBasicOpenCoverOfLinearCombination
      X s0 s1 a b h)

theorem hilbert_exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact
    (X : Scheme.{u}) {U : X.Opens} (hU : IsCompact U.1)
    (x f : Γ(X, U)) (H : x |_ᵣ (X.basicOpen f) = 0) :
    ∃ n : ℕ, f ^ n * x = 0 := by
  exact SourceStack.Schemes.exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact
    X hU x f H

theorem hilbert_exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated
    (X : Scheme.{u}) (U : X.Opens)
    (hU : IsCompact U.1) (hU' : IsQuasiSeparated U.1)
    (f : Γ(X, U)) (x : Γ(X, X.basicOpen f)) :
    ∃ (n : ℕ) (y : Γ(X, U)),
      y |_ᵣ X.basicOpen f = (f |_ᵣ X.basicOpen f) ^ n * x := by
  exact SourceStack.Schemes.exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated
    X U hU hU' f x

theorem hilbert_isLocalization_basicOpen_of_qcqs
    {U : X.Opens} (hU : IsCompact U.1) (hU' : IsQuasiSeparated U.1)
    (f : Γ(X, U)) :
    IsLocalization.Away f (Γ(X, X.basicOpen f)) := by
  exact SourceStack.Schemes.isLocalization_basicOpen_of_qcqs hU hU' f

theorem hilbert_exists_of_res_eq_of_qcqs
    {U : X.Opens} (hU : IsCompact U.1) (hU' : IsQuasiSeparated U.1)
    {f g s : Γ(X, U)} (hfg : f |_ᵣ X.basicOpen s = g |_ᵣ X.basicOpen s) :
    ∃ n, s ^ n * f = s ^ n * g := by
  exact SourceStack.Schemes.exists_of_res_eq_of_qcqs hU hU' hfg

theorem hilbert_exists_of_res_zero_of_qcqs
    {U : X.Opens} (hU : IsCompact U.1) (hU' : IsQuasiSeparated U.1)
    {f s : Γ(X, U)} (hf : f |_ᵣ X.basicOpen s = 0) :
    ∃ n, s ^ n * f = 0 := by
  exact SourceStack.Schemes.exists_of_res_zero_of_qcqs hU hU' hf

theorem hilbert_isNilpotent_iff_basicOpen_eq_bot_of_isCompact
    {U : X.Opens} (hU : IsCompact (U : Set X)) (f : Γ(X, U)) :
    IsNilpotent f ↔ X.basicOpen f = ⊥ := by
  exact SourceStack.Schemes.isNilpotent_iff_basicOpen_eq_bot_of_isCompact hU f

theorem hilbert_zeroLocus_eq_top_iff_subset_nilradical_of_isCompact
    {U : X.Opens} (hU : IsCompact (U : Set X)) (s : Set Γ(X, U)) :
    X.zeroLocus s = ⊤ ↔ s ⊆ nilradical Γ(X, U) := by
  exact SourceStack.Schemes.zeroLocus_eq_top_iff_subset_nilradical_of_isCompact hU s

theorem hilbert_closedImmersion_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsClosedImmersion f] [IsClosedImmersion g] :
    IsClosedImmersion (f ≫ g) := by
  exact SourceStack.Schemes.closedImmersion_comp f g

theorem hilbert_closedImmersion_isFinite
    (f : X ⟶ Y) [IsClosedImmersion f] :
    IsFinite f := by
  exact SourceStack.Schemes.closedImmersion_isFinite f

theorem hilbert_closedImmersion_universallyClosed
    (f : X ⟶ Y) [IsClosedImmersion f] :
    UniversallyClosed f := by
  exact SourceStack.Schemes.closedImmersion_universallyClosed f

theorem hilbert_closedImmersion_isProper
    (f : X ⟶ Y) [IsClosedImmersion f] :
    IsProper f := by
  exact SourceStack.Schemes.closedImmersion_isProper f

theorem hilbert_closedImmersion_stable_under_base_change :
    MorphismProperty.IsStableUnderBaseChange (@IsClosedImmersion) := by
  exact SourceStack.Schemes.closedImmersion_stable_under_base_change

theorem hilbert_closedImmersion_iff_isFinite_and_mono
    (f : X ⟶ Y) :
    IsClosedImmersion f ↔ IsFinite f ∧ Mono f := by
  exact SourceStack.Schemes.closedImmersion_iff_isFinite_and_mono f

theorem hilbert_finite_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFinite f] [IsFinite g] :
    IsFinite (f ≫ g) := by
  exact SourceStack.Schemes.finite_comp f g

theorem hilbert_finite_iff_integralHom_and_locallyOfFiniteType
    (f : X ⟶ Y) :
    IsFinite f ↔ IsIntegralHom f ∧ LocallyOfFiniteType f := by
  exact SourceStack.Schemes.finite_iff_integralHom_and_locallyOfFiniteType f

theorem hilbert_finite_is_integral
    (f : X ⟶ Y) [IsFinite f] :
    IsIntegralHom f := by
  exact SourceStack.Schemes.finite_is_integral f

theorem hilbert_finite_locally_of_finite_type
    (f : X ⟶ Y) [IsFinite f] :
    LocallyOfFiniteType f := by
  exact SourceStack.Schemes.finite_locally_of_finite_type f

theorem hilbert_finite_stable_under_base_change :
    MorphismProperty.IsStableUnderBaseChange (@IsFinite) := by
  exact SourceStack.Schemes.finite_stable_under_base_change

theorem hilbert_finite_restrict
    (f : X ⟶ Y) [IsFinite f] (U : Y.Opens) :
    IsFinite (f ∣_ U) := by
  exact SourceStack.Schemes.finite_restrict f U

theorem hilbert_smooth_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSmooth f] [IsSmooth g] :
    IsSmooth (f ≫ g) := by
  exact SourceStack.Schemes.smooth_comp f g

theorem hilbert_smooth_stable_under_base_change :
    MorphismProperty.IsStableUnderBaseChange (@IsSmooth) := by
  exact SourceStack.Schemes.smooth_stable_under_base_change

theorem hilbert_smooth_restrict
    (f : X ⟶ Y) [IsSmooth f] (U : Y.Opens) :
    IsSmooth (f ∣_ U) := by
  exact SourceStack.Schemes.smooth_restrict f U

theorem hilbert_separated_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [IsSeparated g] :
    IsSeparated (f ≫ g) := by
  exact SourceStack.Schemes.separated_comp f g

theorem hilbert_separated_stable_under_base_change :
    MorphismProperty.IsStableUnderBaseChange (@IsSeparated) := by
  exact SourceStack.Schemes.separated_stable_under_base_change

theorem hilbert_separated_restrict
    (f : X ⟶ Y) [IsSeparated f] (U : Y.Opens) :
    IsSeparated (f ∣_ U) := by
  exact SourceStack.Schemes.separated_restrict f U

theorem hilbert_universallyClosed_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [UniversallyClosed f] [UniversallyClosed g] :
    UniversallyClosed (f ≫ g) := by
  exact SourceStack.Schemes.universallyClosed_comp f g

theorem hilbert_universallyClosed_stable_under_base_change :
    MorphismProperty.IsStableUnderBaseChange (@UniversallyClosed) := by
  exact SourceStack.Schemes.universallyClosed_stable_under_base_change

theorem hilbert_universallyClosed_isClosedMap
    (f : X ⟶ Y) [UniversallyClosed f] :
    IsClosedMap f.base := by
  exact SourceStack.Schemes.universallyClosed_isClosedMap f

theorem hilbert_universallyClosed_restrict
    (f : X ⟶ Y) [UniversallyClosed f] (U : Y.Opens) :
    UniversallyClosed (f ∣_ U) := by
  exact SourceStack.Schemes.universallyClosed_restrict f U

theorem hilbert_universallyClosed_quasiCompact
    (f : X ⟶ Y) [UniversallyClosed f] :
    QuasiCompact f := by
  exact SourceStack.Schemes.universallyClosed_quasiCompact f

theorem hilbert_compactSpace_of_universallyClosed_over_field
    (K : Type u) [Field K] (f : X ⟶ Spec (.of K)) [UniversallyClosed f] :
    CompactSpace X := by
  exact SourceStack.Schemes.compactSpace_of_universallyClosed_over_field K f

theorem hilbert_proper_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsProper f] [IsProper g] :
    IsProper (f ≫ g) := by
  exact SourceStack.Schemes.proper_comp f g

theorem hilbert_proper_stable_under_base_change :
    MorphismProperty.IsStableUnderBaseChange (@IsProper) := by
  exact SourceStack.Schemes.proper_stable_under_base_change

theorem hilbert_proper_restrict
    (f : X ⟶ Y) [IsProper f] (U : Y.Opens) :
    IsProper (f ∣_ U) := by
  exact SourceStack.Schemes.proper_restrict f U

theorem hilbert_proper_isClosedMap
    (f : X ⟶ Y) [IsProper f] :
    IsClosedMap f.base := by
  exact SourceStack.Schemes.proper_isClosedMap f

theorem hilbert_compactSpace_of_proper_over_field
    (K : Type u) [Field K] (f : X ⟶ Spec (.of K)) [IsProper f] :
    CompactSpace X := by
  exact SourceStack.Schemes.compactSpace_of_proper_over_field K f

theorem hilbert_universally_closed_isProperMap
    (f : X ⟶ Y) [UniversallyClosed f] :
    IsProperMap f.base := by
  exact SourceStack.Schemes.universally_closed_isProperMap f

theorem hilbert_proper_isProperMap
    (f : X ⟶ Y) [IsProper f] :
    IsProperMap f.base := by
  exact SourceStack.Schemes.proper_isProperMap f

theorem hilbert_etale_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsEtale f] [IsEtale g] :
    IsEtale (f ≫ g) := by
  exact SourceStack.Schemes.etale_comp f g

theorem hilbert_etale_stable_under_base_change :
    MorphismProperty.IsStableUnderBaseChange (@IsEtale) := by
  exact SourceStack.Schemes.etale_stable_under_base_change

theorem hilbert_etale_restrict
    (f : X ⟶ Y) [IsEtale f] (U : Y.Opens) :
    IsEtale (f ∣_ U) := by
  exact SourceStack.Schemes.etale_restrict f U

end Schemes

end HilbertSteps
end HilbertTest
