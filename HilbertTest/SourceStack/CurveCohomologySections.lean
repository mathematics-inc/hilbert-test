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

end RestrictedEvaluationSurjectivityData

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
