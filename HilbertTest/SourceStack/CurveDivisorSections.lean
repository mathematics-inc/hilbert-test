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

/-- If the canonical two-section finite marked family uses the divisor
evaluation data, then the finite marked Belyi map attached to the divisor
zero-section sends the divisor support to the marked branch set. -/
theorem twoSectionBezoutFamily_zeroSection_maps_support_to_marked
    (F : TwoSectionBezoutProjectiveSectionFiniteMarkedFamily K C V)
    (heval : F.evalPackage.toEvaluationData = D.evalData) :
    ∀ x ∈ D.support, (F.map D.zeroSection).hom.base x ∈ markedSchemePointSet K := by
  intro x hx
  have hxD : D.evalData.eval x D.zeroSection = 0 :=
    (D.zeroSection_hasZeroSet x).2 hx
  have hxF_evalData :
      F.evalPackage.toEvaluationData.eval x D.zeroSection = 0 := by
    simpa [heval] using hxD
  have hxF : F.evalPackage.eval x D.zeroSection = 0 := by
    simpa [CurveRiemannRoch.RiemannRochFiniteEvaluationPackage.toEvaluationData]
      using hxF_evalData
  exact F.eval_zero_to_marked D.zeroSection hxF

/-- If the canonical two-section finite marked family uses the divisor
evaluation data, then the finite marked Belyi map attached to the divisor
zero-section avoids the marked branch set away from the divisor support. -/
theorem twoSectionBezoutFamily_zeroSection_avoids_marked_off_support
    (F : TwoSectionBezoutProjectiveSectionFiniteMarkedFamily K C V)
    (heval : F.evalPackage.toEvaluationData = D.evalData) :
    ∀ x ∉ D.support, (F.map D.zeroSection).hom.base x ∉ markedSchemePointSet K := by
  intro x hx
  have hxD : D.evalData.eval x D.zeroSection ≠ 0 :=
    (D.zeroSection_eval_ne_zero_iff_not_mem_support x).2 hx
  have hxF_evalData :
      F.evalPackage.toEvaluationData.eval x D.zeroSection ≠ 0 := by
    simpa [heval] using hxD
  have hxF : F.evalPackage.eval x D.zeroSection ≠ 0 := by
    simpa [CurveRiemannRoch.RiemannRochFiniteEvaluationPackage.toEvaluationData]
      using hxF_evalData
  exact F.eval_nonzero_avoids_marked D.zeroSection hxF

/-- For the finite marked Belyi map attached to the divisor zero-section, the
source Belyi open is exactly the complement of the divisor support. -/
theorem twoSectionBezoutFamily_zeroSection_mem_belyiOpen_iff
    (F : TwoSectionBezoutProjectiveSectionFiniteMarkedFamily K C V)
    (heval : F.evalPackage.toEvaluationData = D.evalData) (x : C) :
    x ∈ ((F.map D.zeroSection).toBelyiMap.belyiOpen : Set C) ↔
      x ∉ D.support := by
  constructor
  · intro hxOpen hxSupport
    have hxNotMarked :
        (F.map D.zeroSection).hom.base x ∉ markedSchemePointSet K :=
      (SchemeBelyi.FiniteBelyiMap.mem_marked_belyiOpen_iff
        (K := K) (hmarkedOpen := F.hmarkedOpen) (F.map D.zeroSection) x).1 hxOpen
    exact hxNotMarked
      (D.twoSectionBezoutFamily_zeroSection_maps_support_to_marked
        F heval x hxSupport)
  · intro hxSupport
    exact
      (SchemeBelyi.FiniteBelyiMap.mem_marked_belyiOpen_iff
        (K := K) (hmarkedOpen := F.hmarkedOpen) (F.map D.zeroSection) x).2
        (D.twoSectionBezoutFamily_zeroSection_avoids_marked_off_support
          F heval x hxSupport)

/-- Set equality form of the zero-section Belyi-open computation. -/
theorem twoSectionBezoutFamily_zeroSection_belyiOpen_eq_support_compl
    (F : TwoSectionBezoutProjectiveSectionFiniteMarkedFamily K C V)
    (heval : F.evalPackage.toEvaluationData = D.evalData) :
    ((F.map D.zeroSection).toBelyiMap.belyiOpen : Set C) = D.supportᶜ := by
  ext x
  exact D.twoSectionBezoutFamily_zeroSection_mem_belyiOpen_iff F heval x

/-- If the divisor support is the complement of a prescribed set `U`, then the
zero-section finite marked Belyi open is exactly `U`. -/
theorem twoSectionBezoutFamily_zeroSection_belyiOpen_eq_of_support_eq_compl
    (F : TwoSectionBezoutProjectiveSectionFiniteMarkedFamily K C V)
    (heval : F.evalPackage.toEvaluationData = D.evalData)
    {U : Set C} (hsupport : D.support = Uᶜ) :
    ((F.map D.zeroSection).toBelyiMap.belyiOpen : Set C) = U := by
  simpa [hsupport] using
    D.twoSectionBezoutFamily_zeroSection_belyiOpen_eq_support_compl F heval

/-- The zero-section finite marked Belyi open is open. -/
theorem twoSectionBezoutFamily_zeroSection_belyiOpen_isOpen
    (F : TwoSectionBezoutProjectiveSectionFiniteMarkedFamily K C V) :
    IsOpen ((F.map D.zeroSection).toBelyiMap.belyiOpen : Set C) :=
  (F.map D.zeroSection).toBelyiMap.belyiOpen.2

/-- If the divisor support is the complement of `U`, then `U` is open because
it is realized as the source Belyi open of the zero-section finite marked map. -/
theorem twoSectionBezoutFamily_isOpen_of_support_eq_compl
    (F : TwoSectionBezoutProjectiveSectionFiniteMarkedFamily K C V)
    (heval : F.evalPackage.toEvaluationData = D.evalData)
    {U : Set C} (hsupport : D.support = Uᶜ) :
    IsOpen U := by
  rw [← D.twoSectionBezoutFamily_zeroSection_belyiOpen_eq_of_support_eq_compl
    F heval hsupport]
  exact D.twoSectionBezoutFamily_zeroSection_belyiOpen_isOpen F

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

/-- Bundled projective-line reduction source material for a divisor
zero-section.  This packages the line-bundle upgrade from a basepoint-free
section pair to a morphism `C -> P1`, together with the finite/dominant and
auxiliary etaleness checks used by the P1-reduction step. -/
structure ProjectivePairReductionFactory
    (D : DivisorZeroSectionData K C V)
    {Φ : Type z} (F : FiniteMarkedBelyiExistence K Φ (P1 K))
    (S : Set C) where
  badValues : Set (P1 K)
  badValues_finite : badValues.Finite
  mkPair : ∀ s1 : V, HasNoCommonZero D.evalData D.zeroSection s1 →
    ProjectiveLineSectionPair K C V
  mkPair_eval : ∀ s1 hnc, (mkPair s1 hnc).evalData = D.evalData
  mkPair_section0 : ∀ s1 hnc, (mkPair s1 hnc).section0 = D.zeroSection
  mkPair_finite : ∀ s1 hnc, IsFinite (mkPair s1 hnc).hom
  mkPair_dominant : ∀ s1 hnc, IsDominant (mkPair s1 hnc).hom
  target_not_bad :
    schemeCarrierPoint K MarkedPointLabel.zero ∉ badValues
  aux_etale :
    ∀ s1 hnc φ,
      ((F.map φ).toBelyiMap.belyiOpen : Set (P1 K)) ⊆
          (reductionBadSet (mkPair s1 hnc).hom S badValues)ᶜ →
        IsEtale ((mkPair s1 hnc).hom ∣_ (F.map φ).toBelyiMap.belyiOpen)

/-- Structured version of `ProjectivePairReductionFactory` in which the
projective-line section pair is not supplied directly: it is extracted from
the structured two-section Bezout chart data already formalized in
`ProjectiveSectionMaps`. -/
structure StructuredProjectivePairReductionFactory
    (D : DivisorZeroSectionData K C V)
    {Φ : Type z} (F : FiniteMarkedBelyiExistence K Φ (P1 K))
    (S : Set C) where
  badValues : Set (P1 K)
  badValues_finite : badValues.Finite
  twoSection :
    ∀ s1 : V, HasNoCommonZero D.evalData D.zeroSection s1 →
      TwoSectionBezoutStructuredTrivializedIsUnitData K C V
  twoSection_evalData : ∀ s1 hnc, (twoSection s1 hnc).evalData = D.evalData
  twoSection_section0 : ∀ s1 hnc, (twoSection s1 hnc).section0 = D.zeroSection
  twoSection_finite : ∀ s1 hnc, IsFinite (twoSection s1 hnc).globalHom
  twoSection_dominant : ∀ s1 hnc, IsDominant (twoSection s1 hnc).globalHom
  target_not_bad :
    schemeCarrierPoint K MarkedPointLabel.zero ∉ badValues
  aux_etale :
    ∀ s1 hnc φ,
      ((F.map φ).toBelyiMap.belyiOpen : Set (P1 K)) ⊆
          (reductionBadSet (twoSection s1 hnc).globalHom S badValues)ᶜ →
        IsEtale ((twoSection s1 hnc).globalHom ∣_
          (F.map φ).toBelyiMap.belyiOpen)

namespace StructuredProjectivePairReductionFactory

variable {Φ : Type z}
variable {F : FiniteMarkedBelyiExistence K Φ (P1 K)}
variable {S : Set C}
variable (A : StructuredProjectivePairReductionFactory D F S)

/-- Forget structured two-section Bezout chart data to the bundled
projective-pair reduction factory. -/
noncomputable def toProjectivePairReductionFactory :
    ProjectivePairReductionFactory D F S where
  badValues := A.badValues
  badValues_finite := A.badValues_finite
  mkPair := fun s1 hnc => (A.twoSection s1 hnc).toProjectiveLineSectionPair
  mkPair_eval := by
    intro s1 hnc
    calc
      (A.twoSection s1 hnc).toProjectiveLineSectionPair.evalData =
          (A.twoSection s1 hnc).evalData := by
        exact (A.twoSection s1 hnc).toProjectiveLineSectionPair_evalData
      _ = D.evalData := A.twoSection_evalData s1 hnc
  mkPair_section0 := by
    intro s1 hnc
    calc
      (A.twoSection s1 hnc).toProjectiveLineSectionPair.section0 =
          (A.twoSection s1 hnc).section0 := by
        exact (A.twoSection s1 hnc).toProjectiveLineSectionPair_section0
      _ = D.zeroSection := A.twoSection_section0 s1 hnc
  mkPair_finite := by
    intro s1 hnc
    rw [(A.twoSection s1 hnc).toProjectiveLineSectionPair_hom]
    exact A.twoSection_finite s1 hnc
  mkPair_dominant := by
    intro s1 hnc
    rw [(A.twoSection s1 hnc).toProjectiveLineSectionPair_hom]
    exact A.twoSection_dominant s1 hnc
  target_not_bad := A.target_not_bad
  aux_etale := by
    intro s1 hnc φ hsubset
    rw [(A.twoSection s1 hnc).toProjectiveLineSectionPair_hom]
    exact A.aux_etale s1 hnc φ
      (by
        simpa [(A.twoSection s1 hnc).toProjectiveLineSectionPair_hom] using
          hsubset)

end StructuredProjectivePairReductionFactory

/-- Bundled factory form of the divisor-to-reduction bridge: the divisor
source data plus a projective-pair reduction factory gives auxiliary reduction
data for `S` and the divisor support. -/
theorem exists_p1ReductionAuxiliaryData_of_projectivePairReductionFactory
    [Infinite K] {Φ : Type z}
    (F : FiniteMarkedBelyiExistence K Φ (P1 K))
    (hsupport : D.support.Finite) {S : Set C}
    (hdis : Disjoint S D.support)
    (A : ProjectivePairReductionFactory D F S) :
    ∃ s1 : V, ∃ _ : HasNoCommonZero D.evalData D.zeroSection s1,
      Nonempty (P1ReductionAuxiliaryData K C F S D.support) := by
  rcases D.exists_second_section_no_common_zero hsupport with ⟨s1, hnc⟩
  exact
    ⟨s1, hnc, ⟨
      D.projectivePair_toP1ReductionAuxiliaryData F hdis
        (A.mkPair s1 hnc) (A.mkPair_eval s1 hnc)
        (A.mkPair_section0 s1 hnc) A.badValues A.badValues_finite
        (A.mkPair_finite s1 hnc) (A.mkPair_dominant s1 hnc)
        A.target_not_bad (A.aux_etale s1 hnc)⟩⟩

/-- Set-indexed bundled factory form: if the divisor support is the prescribed
finite set `T`, the bundled projective-pair reduction factory gives auxiliary
data for the reduction pair `S,T`. -/
theorem exists_p1ReductionAuxiliaryData_for_sets_of_projectivePairReductionFactory
    [Infinite K] {Φ : Type z}
    (F : FiniteMarkedBelyiExistence K Φ (P1 K))
    {S T : Set C} (hT : T.Finite) (hsupport : D.support = T)
    (hdis : Disjoint S T)
    (A : ProjectivePairReductionFactory D F S) :
    ∃ s1 : V, ∃ _ : HasNoCommonZero D.evalData D.zeroSection s1,
      Nonempty (P1ReductionAuxiliaryData K C F S T) := by
  cases hsupport
  exact D.exists_p1ReductionAuxiliaryData_of_projectivePairReductionFactory
    F hT hdis A

/-- Set-indexed structured factory form: if the divisor support is the
prescribed finite set `T`, structured two-section Bezout chart data gives
auxiliary data for the reduction pair `S,T`. -/
theorem exists_p1ReductionAuxiliaryData_for_sets_of_structuredProjectivePairReductionFactory
    [Infinite K] {Φ : Type z}
    (F : FiniteMarkedBelyiExistence K Φ (P1 K))
    {S T : Set C} (hT : T.Finite) (hsupport : D.support = T)
    (hdis : Disjoint S T)
    (A : StructuredProjectivePairReductionFactory D F S) :
    ∃ s1 : V, ∃ _ : HasNoCommonZero D.evalData D.zeroSection s1,
      Nonempty (P1ReductionAuxiliaryData K C F S T) := by
  exact D.exists_p1ReductionAuxiliaryData_for_sets_of_projectivePairReductionFactory
    F hT hsupport hdis A.toProjectivePairReductionFactory

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

/-- Finite-complement-open section-pair control: if the divisor support is a
finite set inside `U`, the projective-line section-pair factory yields a map
sending the support to `0` and sending the complement of `U` away from `0`. -/
theorem exists_projectivePair_maps_support_to_zeroPoint_avoids_complement_of_finite_complement
    [Infinite K] {U T : Set C} (_hU : IsOpen U) (_hUcompl : Uᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ U) (hsupport : D.support = T)
    (mkPair : ∀ s1 : V, HasNoCommonZero D.evalData D.zeroSection s1 →
      ProjectiveLineSectionPair K C V)
    (hmk_eval : ∀ s1 hnc, (mkPair s1 hnc).evalData = D.evalData)
    (hmk_section0 : ∀ s1 hnc, (mkPair s1 hnc).section0 = D.zeroSection) :
    ∃ s1 : V, ∃ hnc : HasNoCommonZero D.evalData D.zeroSection s1,
      (∀ x ∈ T,
        (mkPair s1 hnc).hom.base x = schemeCarrierPoint K MarkedPointLabel.zero) ∧
        ∀ x ∈ Uᶜ,
          (mkPair s1 hnc).hom.base x ≠ schemeCarrierPoint K MarkedPointLabel.zero := by
  cases hsupport
  have hdis : Disjoint Uᶜ D.support := by
    rw [Set.disjoint_left]
    intro x hxU hxT
    exact hxU (hTsub hxT)
  exact
    D.exists_projectivePair_maps_support_to_zeroPoint_avoids_set
      hT hdis mkPair hmk_eval hmk_section0

/-- Nonempty-open finite-complement section-pair control in a finite-complement
topology. -/
theorem exists_projectivePair_maps_support_to_zeroPoint_avoids_complement_of_nonemptyOpenFiniteComplement
    [Infinite K] [NonemptyOpenFiniteComplement C]
    {U T : Set C} (hU : IsOpen U) (hUne : U.Nonempty)
    (hT : T.Finite) (hTsub : T ⊆ U) (hsupport : D.support = T)
    (mkPair : ∀ s1 : V, HasNoCommonZero D.evalData D.zeroSection s1 →
      ProjectiveLineSectionPair K C V)
    (hmk_eval : ∀ s1 hnc, (mkPair s1 hnc).evalData = D.evalData)
    (hmk_section0 : ∀ s1 hnc, (mkPair s1 hnc).section0 = D.zeroSection) :
    ∃ s1 : V, ∃ hnc : HasNoCommonZero D.evalData D.zeroSection s1,
      (∀ x ∈ T,
        (mkPair s1 hnc).hom.base x = schemeCarrierPoint K MarkedPointLabel.zero) ∧
        ∀ x ∈ Uᶜ,
          (mkPair s1 hnc).hom.base x ≠ schemeCarrierPoint K MarkedPointLabel.zero := by
  exact
    D.exists_projectivePair_maps_support_to_zeroPoint_avoids_complement_of_finite_complement
      hU (finite_compl_of_isOpen_nonempty hU hUne) hT hTsub hsupport
      mkPair hmk_eval hmk_section0

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

/-- Finite-complement-open auxiliary-data bridge: if the divisor support is a
finite set inside `U`, the section-pair factory gives auxiliary reduction data
for the pair `Uᶜ, T`. -/
theorem exists_p1ReductionAuxiliaryData_containing_finite_inside_open_of_finite_complement_for_sets_of_projectivePair_factory
    [Infinite K] {Φ : Type z}
    (F : FiniteMarkedBelyiExistence K Φ (P1 K))
    {U T : Set C} (_hU : IsOpen U) (_hUcompl : Uᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ U) (hsupport : D.support = T)
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
            (reductionBadSet (mkPair s1 hnc).hom Uᶜ badValues)ᶜ →
          IsEtale ((mkPair s1 hnc).hom ∣_ (F.map φ).toBelyiMap.belyiOpen)) :
    ∃ s1 : V, ∃ _ : HasNoCommonZero D.evalData D.zeroSection s1,
      Nonempty (P1ReductionAuxiliaryData K C F Uᶜ T) := by
  have hdis : Disjoint Uᶜ T := by
    rw [Set.disjoint_left]
    intro x hxU hxT
    exact hxU (hTsub hxT)
  exact
    D.exists_p1ReductionAuxiliaryData_for_sets_of_projectivePair_factory
      F hT hsupport hdis badValues hbad mkPair hmk_eval hmk_section0
      hmk_finite hmk_dominant htargetBad hAuxEtale

/-- Nonempty-open auxiliary-data bridge in a finite-complement topology. -/
theorem exists_p1ReductionAuxiliaryData_containing_finite_inside_open_of_nonemptyOpenFiniteComplement_for_sets_of_projectivePair_factory
    [Infinite K] [NonemptyOpenFiniteComplement C] {Φ : Type z}
    (F : FiniteMarkedBelyiExistence K Φ (P1 K))
    {U T : Set C} (hU : IsOpen U) (hUne : U.Nonempty)
    (hT : T.Finite) (hTsub : T ⊆ U) (hsupport : D.support = T)
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
            (reductionBadSet (mkPair s1 hnc).hom Uᶜ badValues)ᶜ →
          IsEtale ((mkPair s1 hnc).hom ∣_ (F.map φ).toBelyiMap.belyiOpen)) :
    ∃ s1 : V, ∃ _ : HasNoCommonZero D.evalData D.zeroSection s1,
      Nonempty (P1ReductionAuxiliaryData K C F Uᶜ T) := by
  exact
    D.exists_p1ReductionAuxiliaryData_containing_finite_inside_open_of_finite_complement_for_sets_of_projectivePair_factory
      F hU (finite_compl_of_isOpen_nonempty hU hUne) hT hTsub hsupport
      badValues hbad mkPair hmk_eval hmk_section0 hmk_finite hmk_dominant
      htargetBad hAuxEtale

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

/-- Combined composed-map form of the divisor-to-reduction bridge: the divisor
source data produces an actual composed finite Belyi map with both marked
controls and Belyi-open controls. -/
theorem exists_composedMap_controls_and_belyiOpen_controls_for_sets_of_projectivePair_factory
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
            ((∀ x ∈ S, composed.hom.base x ∈ markedSchemePointSet K) ∧
              ∀ x ∈ T, composed.hom.base x ∉ markedSchemePointSet K) ∧
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
      P1ReductionStep.exists_composedMap_controls_and_belyiOpen_controls_of_p1MapExistence_auxEtale
        (K := K) (C := C) (S := S) (T := D.support)
        F hS badValues hbad P.hom
        (targetPoint := schemeCarrierPoint K MarkedPointLabel.zero)
        himage htargetBad htarget (hAuxEtale s1 hnc) with
    ⟨phi, composed, hhom, hcontrols, hTopen, hopenS⟩
  exact ⟨s1, hnc, phi, composed, hhom, hcontrols, hTopen, hopenS⟩

/-- Combined composed-map form of the divisor-to-reduction bridge with
explicit openness: the divisor source data produces an actual composed finite
Belyi map with marked controls, an open source Belyi open, and Belyi-open
controls. -/
theorem exists_composedMap_controls_and_isOpen_belyiOpen_controls_for_sets_of_projectivePair_factory
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
            ((∀ x ∈ S, composed.hom.base x ∈ markedSchemePointSet K) ∧
              ∀ x ∈ T, composed.hom.base x ∉ markedSchemePointSet K) ∧
              IsOpen (composed.toBelyiMap.belyiOpen : Set C) ∧
                T ⊆ (composed.toBelyiMap.belyiOpen : Set C) ∧
                  (composed.toBelyiMap.belyiOpen : Set C) ⊆ Sᶜ := by
  rcases
      D.exists_composedMap_controls_and_belyiOpen_controls_for_sets_of_projectivePair_factory
        F hS hT hsupport hdis badValues hbad mkPair hmk_eval hmk_section0
        hmk_finite hmk_dominant htargetBad hAuxEtale with
    ⟨s1, hnc, phi, composed, hhom, hcontrols, hTopen, hopenS⟩
  exact
    ⟨s1, hnc, phi, composed, hhom, hcontrols,
      composed.toBelyiMap.belyiOpen.2, hTopen, hopenS⟩

/-- Finite-complement-open composed-map form of the divisor-to-reduction
bridge: when `T` lies in an open with finite complement, the divisor source
data produces an actual composed finite Belyi map whose Belyi open contains `T`
and is contained in that open. -/
theorem exists_composedMap_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_finite_complement_for_sets_of_projectivePair_factory
    [Infinite K] {Φ : Type z}
    (F : FiniteMarkedBelyiExistence K Φ (P1 K))
    {U T : Set C} (_hU : IsOpen U) (hUcompl : Uᶜ.Finite)
    (hT : T.Finite) (hTsub : T ⊆ U)
    (hsupport : D.support = T)
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
            (reductionBadSet (mkPair s1 hnc).hom Uᶜ badValues)ᶜ →
          IsEtale ((mkPair s1 hnc).hom ∣_ (F.map phi).toBelyiMap.belyiOpen)) :
    ∃ s1 : V, ∃ hnc : HasNoCommonZero D.evalData D.zeroSection s1,
      ∃ phi : Φ,
        ∃ composed : SchemeBelyi.FiniteBelyiMap
          (SchemeBelyi.markedBelyiTarget K F.hmarkedOpen) C,
          composed.hom = (mkPair s1 hnc).hom ≫ (F.map phi).hom ∧
            ((∀ x ∈ Uᶜ, composed.hom.base x ∈ markedSchemePointSet K) ∧
              ∀ x ∈ T, composed.hom.base x ∉ markedSchemePointSet K) ∧
              IsOpen (composed.toBelyiMap.belyiOpen : Set C) ∧
                T ⊆ (composed.toBelyiMap.belyiOpen : Set C) ∧
                  (composed.toBelyiMap.belyiOpen : Set C) ⊆ U := by
  have hdis : Disjoint Uᶜ T := by
    rw [Set.disjoint_left]
    intro x hxU hxT
    exact hxU (hTsub hxT)
  rcases
      D.exists_composedMap_controls_and_isOpen_belyiOpen_controls_for_sets_of_projectivePair_factory
        F hUcompl hT hsupport hdis badValues hbad mkPair hmk_eval hmk_section0
        hmk_finite hmk_dominant htargetBad hAuxEtale with
    ⟨s1, hnc, phi, composed, hhom, hcontrols, hopen, hTopen, hopenS⟩
  exact
    ⟨s1, hnc, phi, composed, hhom, hcontrols, hopen, hTopen,
      by simpa using hopenS⟩

/-- Nonempty-open composed-map form of the divisor-to-reduction bridge in a
finite-complement topology. -/
theorem exists_composedMap_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_nonemptyOpenFiniteComplement_for_sets_of_projectivePair_factory
    [Infinite K] [NonemptyOpenFiniteComplement C] {Φ : Type z}
    (F : FiniteMarkedBelyiExistence K Φ (P1 K))
    {U T : Set C} (hU : IsOpen U) (hUne : U.Nonempty)
    (hT : T.Finite) (hTsub : T ⊆ U)
    (hsupport : D.support = T)
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
            (reductionBadSet (mkPair s1 hnc).hom Uᶜ badValues)ᶜ →
          IsEtale ((mkPair s1 hnc).hom ∣_ (F.map phi).toBelyiMap.belyiOpen)) :
    ∃ s1 : V, ∃ hnc : HasNoCommonZero D.evalData D.zeroSection s1,
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
    D.exists_composedMap_controls_and_isOpen_belyiOpen_containing_finite_inside_open_of_finite_complement_for_sets_of_projectivePair_factory
      F hU (finite_compl_of_isOpen_nonempty hU hUne) hT hTsub hsupport
      badValues hbad mkPair hmk_eval hmk_section0 hmk_finite hmk_dominant
      htargetBad hAuxEtale

end DivisorZeroSectionData

end SchemeSupport

end CurveDivisorSections
end SourceStack
end HilbertTest
