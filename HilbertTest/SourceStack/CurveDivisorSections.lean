import HilbertTest.SourceStack.BelyiReduction
import HilbertTest.SourceStack.ProjectiveSectionMaps

/-!
Divisor-section selection layer for Mochizuki Theorem 2.5.

In the paper, `D = sum_{t in T} [t]`, `L = O_X(D)`, and `s0` is the section
with zero divisor `D`.  Riemann-Roch/Serre duality gives enough evaluation
surjectivity to choose a second section `s1` nonzero at every point of `T`.
This file isolates the checked consequence of that source material: once the
zero-section and nonzero evaluation forms are supplied, the existing finite
linear-form avoidance lemma produces such an `s1`, and the pair `(s0, s1)` has
no common basepoint.
-/

namespace HilbertTest
namespace SourceStack
namespace CurveDivisorSections

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

/-- Divisor zero-section data abstracted from `L = O(D)`: a section whose zero
set is the prescribed support, together with nonzero evaluation functionals at
that support. -/
structure DivisorZeroSectionData
    (K : Type u) [Field K] (X : Type v)
    (V : Type w) [AddCommGroup V] [Module K V] where
  evalData : RRSectionEvaluationData K X V
  support : Set X
  zeroSection : V
  zeroSection_hasZeroSet : HasZeroSet evalData zeroSection support
  eval_nonzero_on_support : ∀ x ∈ support, evalData.eval x ≠ 0

namespace DivisorZeroSectionData

variable (D : DivisorZeroSectionData K X V)

/-- The first section vanishes exactly on the divisor support. -/
theorem zeroSection_hasZeroSet_apply :
    HasZeroSet D.evalData D.zeroSection D.support :=
  D.zeroSection_hasZeroSet

/-- The distinguished zero-section vanishes at exactly the support points. -/
theorem zeroSection_eval_eq_zero_iff_mem_support (x : X) :
    D.evalData.eval x D.zeroSection = 0 ↔ x ∈ D.support :=
  D.zeroSection_hasZeroSet x

/-- Away from the support, the distinguished zero-section is nonzero. -/
theorem zeroSection_eval_ne_zero_iff_not_mem_support (x : X) :
    D.evalData.eval x D.zeroSection ≠ 0 ↔ x ∉ D.support := by
  constructor
  · intro hzero hx
    exact hzero ((D.zeroSection_hasZeroSet x).2 hx)
  · intro hx hzero
    exact hx ((D.zeroSection_hasZeroSet x).1 hzero)

/-- Over an infinite field, finitely many nonzero evaluation forms can be
avoided simultaneously, so there is a section nonzero on the divisor support. -/
theorem exists_section_nonzero_on_support
    [Infinite K] (hsupport : D.support.Finite) :
    ∃ s1 : V, D.evalData.nonzeroOnSet D.support s1 := by
  have hforms :
      ∀ x ∈ hsupport.toFinset, D.evalData.eval x ≠ 0 := by
    intro x hx
    exact D.eval_nonzero_on_support x
      ((Set.Finite.mem_toFinset hsupport).1 hx)
  rcases D.evalData.exists_section_nonzero_on_finite
      hsupport.toFinset hforms with ⟨s1, hs1⟩
  exact ⟨s1, ((D.evalData).nonzeroOn_toFinset_iff hsupport s1).1 hs1⟩

/-- The divisor zero-section and a simultaneously nonzero second section form a
basepoint-free pair. -/
theorem hasNoCommonZero_zeroSection_of_nonzero_on_support
    {s1 : V} (hs1 : D.evalData.nonzeroOnSet D.support s1) :
    HasNoCommonZero D.evalData D.zeroSection s1 := by
  exact hasNoCommonZero_of_hasZeroSet_nonzeroOnSet
    D.evalData D.zeroSection s1 D.support D.zeroSection_hasZeroSet hs1

/-- The source-material package needed before the projective-line morphism:
there exists a second section such that `(s0, s1)` has no common basepoint. -/
theorem exists_second_section_no_common_zero
    [Infinite K] (hsupport : D.support.Finite) :
    ∃ s1 : V, HasNoCommonZero D.evalData D.zeroSection s1 := by
  rcases D.exists_section_nonzero_on_support hsupport with ⟨s1, hs1⟩
  exact ⟨s1, D.hasNoCommonZero_zeroSection_of_nonzero_on_support hs1⟩

end DivisorZeroSectionData

section SchemeSupport

open AlgebraicGeometry
open CategoryTheory

variable {C : Scheme.{u}}

namespace DivisorZeroSectionData

variable (D : DivisorZeroSectionData K C V)

/-- Once the basepoint-free pair has been upgraded to a projective-line
morphism, the zero-section support maps to the marked branch point `0`. -/
theorem projectivePair_maps_support_to_zeroPoint
    (P : ProjectiveLineSectionPair K C V)
    (heval : P.evalData = D.evalData)
    (hsection0 : P.section0 = D.zeroSection) :
    ∀ x ∈ D.support, P.hom.base x = schemeCarrierPoint K MarkedPointLabel.zero := by
  intro x hx
  exact P.zero_of_section0_vanishes x
    (by
      rw [heval, hsection0]
      exact (D.zeroSection_hasZeroSet x).2 hx)

/-- Away from the support of the zero-section divisor, the associated
projective-line morphism avoids the checked zero point. -/
theorem projectivePair_avoids_zeroPoint_off_support
    (P : ProjectiveLineSectionPair K C V)
    (heval : P.evalData = D.evalData)
    (hsection0 : P.section0 = D.zeroSection) :
    ∀ x ∉ D.support, P.hom.base x ≠ schemeCarrierPoint K MarkedPointLabel.zero := by
  intro x hx hzero
  have hvanish : D.evalData.eval x D.zeroSection = 0 := by
    rw [← heval, ← hsection0]
    exact P.section0_vanishes_of_zero x hzero
  exact hx ((D.zeroSection_hasZeroSet x).1 hvanish)

/-- Once the basepoint-free pair has been upgraded to a projective-line
morphism, the zero-section support maps to the marked branch point `0`. -/
theorem projectivePair_maps_support_to_marked
    (P : ProjectiveLineSectionPair K C V)
    (heval : P.evalData = D.evalData)
    (hsection0 : P.section0 = D.zeroSection) :
    ∀ x ∈ D.support, P.hom.base x ∈ markedSchemePointSet K := by
  intro x hx
  rw [D.projectivePair_maps_support_to_zeroPoint P heval hsection0 x hx]
  exact schemeCarrierPoint_mem_markedSchemePointSet K MarkedPointLabel.zero

/-- A projective-line section pair whose first section is the divisor
zero-section supplies the auxiliary reduction data for the pair
`S, D.support`, provided the remaining finite/dominant/étale source-material
checks for the auxiliary morphism are available. -/
noncomputable def projectivePair_toP1ReductionAuxiliaryData
    {Φ : Type z}
    (F : FiniteMarkedBelyiExistence K Φ (P1 K))
    {S : Set C} (hdis : Disjoint S D.support)
    (P : ProjectiveLineSectionPair K C V)
    (heval : P.evalData = D.evalData)
    (hsection0 : P.section0 = D.zeroSection)
    (badValues : Set (P1 K)) (hbad : badValues.Finite)
    (hfinite : IsFinite P.hom) (hdominant : IsDominant P.hom)
    (htargetBad : schemeCarrierPoint K MarkedPointLabel.zero ∉ badValues)
    (hAuxEtale :
      ∀ φ : Φ,
        ((F.map φ).toBelyiMap.belyiOpen : Set (P1 K)) ⊆
            (reductionBadSet P.hom S badValues)ᶜ →
          IsEtale (P.hom ∣_ (F.map φ).toBelyiMap.belyiOpen)) :
    P1ReductionAuxiliaryData K C F S D.support where
  badValues := badValues
  badValues_finite := hbad
  aux := P.hom
  aux_finite := hfinite
  aux_dominant := hdominant
  targetPoint := schemeCarrierPoint K MarkedPointLabel.zero
  image_avoids_target := by
    intro x hxS
    exact D.projectivePair_avoids_zeroPoint_off_support P heval hsection0 x
      ((Set.disjoint_left.mp hdis) hxS)
  target_not_bad := htargetBad
  maps_T_to_target := by
    intro x hx
    exact D.projectivePair_maps_support_to_zeroPoint P heval hsection0 x hx
  aux_etale_on_selected_belyiOpen := hAuxEtale

/-- Factory form of the divisor-section bridge: once the line-bundle
construction upgrades every basepoint-free pair `(s0, s1)` to a projective-line
section pair, the divisor source data supplies such a pair mapping the support
to the marked branch point. -/
theorem exists_projectivePair_maps_support_to_marked
    [Infinite K] (hsupport : D.support.Finite)
    (mkPair : ∀ s1 : V, HasNoCommonZero D.evalData D.zeroSection s1 →
      ProjectiveLineSectionPair K C V)
    (hmk_eval : ∀ s1 hnc, (mkPair s1 hnc).evalData = D.evalData)
    (hmk_section0 : ∀ s1 hnc, (mkPair s1 hnc).section0 = D.zeroSection) :
    ∃ s1 : V, ∃ hnc : HasNoCommonZero D.evalData D.zeroSection s1,
      ∀ x ∈ D.support, (mkPair s1 hnc).hom.base x ∈ markedSchemePointSet K := by
  rcases D.exists_second_section_no_common_zero hsupport with ⟨s1, hnc⟩
  exact ⟨s1, hnc,
    D.projectivePair_maps_support_to_marked
      (mkPair s1 hnc) (hmk_eval s1 hnc) (hmk_section0 s1 hnc)⟩

/-- Factory form of the divisor-section bridge, with the sharper pointwise
statement used in the reduction step: the support maps to `0`, while any
prescribed set disjoint from the support avoids `0`. -/
theorem exists_projectivePair_maps_support_to_zeroPoint_avoids_set
    [Infinite K] (hsupport : D.support.Finite) {S : Set C}
    (hdis : Disjoint S D.support)
    (mkPair : ∀ s1 : V, HasNoCommonZero D.evalData D.zeroSection s1 →
      ProjectiveLineSectionPair K C V)
    (hmk_eval : ∀ s1 hnc, (mkPair s1 hnc).evalData = D.evalData)
    (hmk_section0 : ∀ s1 hnc, (mkPair s1 hnc).section0 = D.zeroSection) :
    ∃ s1 : V, ∃ hnc : HasNoCommonZero D.evalData D.zeroSection s1,
      (∀ x ∈ D.support,
        (mkPair s1 hnc).hom.base x = schemeCarrierPoint K MarkedPointLabel.zero) ∧
        ∀ x ∈ S,
          (mkPair s1 hnc).hom.base x ≠ schemeCarrierPoint K MarkedPointLabel.zero := by
  rcases D.exists_second_section_no_common_zero hsupport with ⟨s1, hnc⟩
  refine ⟨s1, hnc, ?_, ?_⟩
  · exact D.projectivePair_maps_support_to_zeroPoint
      (mkPair s1 hnc) (hmk_eval s1 hnc) (hmk_section0 s1 hnc)
  · intro x hxS
    exact D.projectivePair_avoids_zeroPoint_off_support
      (mkPair s1 hnc) (hmk_eval s1 hnc) (hmk_section0 s1 hnc) x
      ((Set.disjoint_left.mp hdis) hxS)

/-- Factory form of the divisor-to-reduction bridge: once the line-bundle
construction upgrades every basepoint-free pair to a projective-line section
pair and the auxiliary morphism checks are supplied for those pairs, the
divisor source data gives reduction auxiliary data for `S` and the divisor
support. -/
theorem exists_p1ReductionAuxiliaryData_of_projectivePair_factory
    [Infinite K] {Φ : Type z}
    (F : FiniteMarkedBelyiExistence K Φ (P1 K))
    (hsupport : D.support.Finite) {S : Set C}
    (hdis : Disjoint S D.support)
    (badValues : Set (P1 K)) (hbad : badValues.Finite)
    (mkPair : ∀ s1 : V, HasNoCommonZero D.evalData D.zeroSection s1 →
      ProjectiveLineSectionPair K C V)
    (hmk_eval : ∀ s1 hnc, (mkPair s1 hnc).evalData = D.evalData)
    (hmk_section0 : ∀ s1 hnc, (mkPair s1 hnc).section0 = D.zeroSection)
    (hmk_finite : ∀ s1 hnc, IsFinite (mkPair s1 hnc).hom)
    (hmk_dominant : ∀ s1 hnc, IsDominant (mkPair s1 hnc).hom)
    (htargetBad : schemeCarrierPoint K MarkedPointLabel.zero ∉ badValues)
    (hAuxEtale :
      ∀ s1 hnc φ,
        ((F.map φ).toBelyiMap.belyiOpen : Set (P1 K)) ⊆
            (reductionBadSet (mkPair s1 hnc).hom S badValues)ᶜ →
          IsEtale ((mkPair s1 hnc).hom ∣_ (F.map φ).toBelyiMap.belyiOpen)) :
    ∃ s1 : V, ∃ _ : HasNoCommonZero D.evalData D.zeroSection s1,
      Nonempty (P1ReductionAuxiliaryData K C F S D.support) := by
  rcases D.exists_second_section_no_common_zero hsupport with ⟨s1, hnc⟩
  exact
    ⟨s1, hnc, ⟨
      D.projectivePair_toP1ReductionAuxiliaryData F hdis
        (mkPair s1 hnc) (hmk_eval s1 hnc) (hmk_section0 s1 hnc)
        badValues hbad (hmk_finite s1 hnc) (hmk_dominant s1 hnc)
        htargetBad (hAuxEtale s1 hnc)⟩⟩

/-- Set-indexed form of
`exists_p1ReductionAuxiliaryData_of_projectivePair_factory`: if the divisor
support is the prescribed finite set `T`, the produced auxiliary data is typed
for the reduction pair `S,T`. -/
theorem exists_p1ReductionAuxiliaryData_for_sets_of_projectivePair_factory
    [Infinite K] {Φ : Type z}
    (F : FiniteMarkedBelyiExistence K Φ (P1 K))
    {S T : Set C} (hT : T.Finite) (hsupport : D.support = T)
    (hdis : Disjoint S T)
    (badValues : Set (P1 K)) (hbad : badValues.Finite)
    (mkPair : ∀ s1 : V, HasNoCommonZero D.evalData D.zeroSection s1 →
      ProjectiveLineSectionPair K C V)
    (hmk_eval : ∀ s1 hnc, (mkPair s1 hnc).evalData = D.evalData)
    (hmk_section0 : ∀ s1 hnc, (mkPair s1 hnc).section0 = D.zeroSection)
    (hmk_finite : ∀ s1 hnc, IsFinite (mkPair s1 hnc).hom)
    (hmk_dominant : ∀ s1 hnc, IsDominant (mkPair s1 hnc).hom)
    (htargetBad : schemeCarrierPoint K MarkedPointLabel.zero ∉ badValues)
    (hAuxEtale :
      ∀ s1 hnc φ,
        ((F.map φ).toBelyiMap.belyiOpen : Set (P1 K)) ⊆
            (reductionBadSet (mkPair s1 hnc).hom S badValues)ᶜ →
          IsEtale ((mkPair s1 hnc).hom ∣_ (F.map φ).toBelyiMap.belyiOpen)) :
    ∃ s1 : V, ∃ _ : HasNoCommonZero D.evalData D.zeroSection s1,
      Nonempty (P1ReductionAuxiliaryData K C F S T) := by
  cases hsupport
  exact
    D.exists_p1ReductionAuxiliaryData_of_projectivePair_factory
      F hT hdis badValues hbad mkPair hmk_eval hmk_section0
      hmk_finite hmk_dominant htargetBad hAuxEtale

/-- Composed-map form of the divisor-to-reduction bridge: once the
line-bundle construction upgrades every basepoint-free pair to a projective-line
section pair and the auxiliary morphism checks are supplied for those pairs,
the divisor source data produces an actual composed finite Belyi map whose
Belyi open contains `T` and avoids `S`. -/
theorem exists_composedMap_belyiOpen_controls_for_sets_of_projectivePair_factory
    [Infinite K] {Φ : Type z}
    (F : FiniteMarkedBelyiExistence K Φ (P1 K))
    {S T : Set C} (hS : S.Finite) (hT : T.Finite)
    (hsupport : D.support = T)
    (hdis : Disjoint S T)
    (badValues : Set (P1 K)) (hbad : badValues.Finite)
    (mkPair : ∀ s1 : V, HasNoCommonZero D.evalData D.zeroSection s1 →
      ProjectiveLineSectionPair K C V)
    (hmk_eval : ∀ s1 hnc, (mkPair s1 hnc).evalData = D.evalData)
    (hmk_section0 : ∀ s1 hnc, (mkPair s1 hnc).section0 = D.zeroSection)
    (hmk_finite : ∀ s1 hnc, IsFinite (mkPair s1 hnc).hom)
    (hmk_dominant : ∀ s1 hnc, IsDominant (mkPair s1 hnc).hom)
    (htargetBad : schemeCarrierPoint K MarkedPointLabel.zero ∉ badValues)
    (hAuxEtale :
      ∀ s1 hnc phi,
        ((F.map phi).toBelyiMap.belyiOpen : Set (P1 K)) ⊆
            (reductionBadSet (mkPair s1 hnc).hom S badValues)ᶜ →
          IsEtale ((mkPair s1 hnc).hom ∣_ (F.map phi).toBelyiMap.belyiOpen)) :
    ∃ s1 : V, ∃ hnc : HasNoCommonZero D.evalData D.zeroSection s1,
      ∃ phi : Φ,
        ∃ composed : SchemeBelyi.FiniteBelyiMap
          (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen) C,
          composed.hom = (mkPair s1 hnc).hom ≫ (F.map phi).hom ∧
            T ⊆ (composed.toBelyiMap.belyiOpen : Set C) ∧
              (composed.toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  cases hsupport
  rcases D.exists_second_section_no_common_zero hT with ⟨s1, hnc⟩
  let P := mkPair s1 hnc
  have himage :
      ∀ x ∈ S, P.hom.base x ≠ schemeCarrierPoint K MarkedPointLabel.zero := by
    intro x hxS
    exact D.projectivePair_avoids_zeroPoint_off_support
      P (hmk_eval s1 hnc) (hmk_section0 s1 hnc) x
      ((Set.disjoint_left.mp hdis) hxS)
  have htarget :
      ∀ x ∈ D.support, P.hom.base x =
        schemeCarrierPoint K MarkedPointLabel.zero := by
    exact D.projectivePair_maps_support_to_zeroPoint
      P (hmk_eval s1 hnc) (hmk_section0 s1 hnc)
  letI : IsFinite P.hom := hmk_finite s1 hnc
  letI : IsDominant P.hom := hmk_dominant s1 hnc
  rcases
      P1ReductionStep.exists_composedMap_belyiOpen_controls_of_p1MapExistence_auxEtale
        (K := K) (C := C) (S := S) (T := D.support)
        F hS badValues hbad P.hom
        (targetPoint := schemeCarrierPoint K MarkedPointLabel.zero)
        himage htargetBad htarget (hAuxEtale s1 hnc) with
    ⟨phi, composed, hhom, hTopen, hopenS⟩
  exact ⟨s1, hnc, phi, composed, hhom, hTopen, hopenS⟩

end DivisorZeroSectionData

end SchemeSupport

end CurveDivisorSections
end SourceStack
end HilbertTest
