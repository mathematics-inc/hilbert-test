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
open ProjectiveSectionMaps
open SchemeProjectiveLine

universe u v w

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

variable {C : Scheme.{u}}

namespace DivisorZeroSectionData

variable (D : DivisorZeroSectionData K C V)

/-- Once the basepoint-free pair has been upgraded to a projective-line
morphism, the zero-section support maps to the marked branch point `0`. -/
theorem projectivePair_maps_support_to_marked
    (P : ProjectiveLineSectionPair K C V)
    (heval : P.evalData = D.evalData)
    (hsection0 : P.section0 = D.zeroSection) :
    ∀ x ∈ D.support, P.hom.base x ∈ markedSchemePointSet K := by
  intro x hx
  have hzero : P.evalData.eval x P.section0 = 0 := by
    rw [heval, hsection0]
    exact (D.zeroSection_hasZeroSet x).2 hx
  exact P.maps_section0_zero_to_marked hzero

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

end DivisorZeroSectionData

end SchemeSupport

end CurveDivisorSections
end SourceStack
end HilbertTest
