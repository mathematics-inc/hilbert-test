import HilbertTest.SourceStack.MarkedProjectiveLine
import HilbertTest.SourceStack.P1PolynomialSeparation

/-!
Bridge from the linear projective-line point model to the scheme carrier `P1 K`.

The project has two checked point models for `P^1`: Mathlib's linear
projectivization and the scheme carrier of `Proj K[X0,X1]`.  This file isolates
the exact interface needed downstream: an injective map from the linear model to
the scheme carrier that agrees with the marked labels `0,1,infinity`.  The
concrete instance is constructed in `SchemeAffineLinePoints`; from this
interface, branch membership and the polynomial-separation handoff transport
formally.
-/

noncomputable section

open scoped Polynomial

set_option linter.unusedSectionVars false

namespace HilbertTest
namespace SourceStack
namespace P1SchemePointBridge

open MarkedProjectiveLine
open P1PolynomialSeparation

universe u v

variable (K : Type u) [Field K]

/-- Abstract interface for identifying the linear and scheme-carrier point
models of `P^1` on the marked triple. -/
structure LinearSchemePointBridge where
  toScheme : ProjectiveLine.P1 K → SchemeProjectiveLine.P1 K
  injective : Function.Injective toScheme
  maps_label :
    ∀ label : MarkedPointLabel,
      toScheme (linearPoint K label) = schemeCarrierPoint K label

namespace LinearSchemePointBridge

variable {K}
variable (B : LinearSchemePointBridge K)

theorem toScheme_linearPoint (label : MarkedPointLabel) :
    B.toScheme (linearPoint K label) = schemeCarrierPoint K label :=
  B.maps_label label

theorem toScheme_mem_markedSchemePointSet_of_mem_branchSet
    {p : ProjectiveLine.P1 K} (hp : p ∈ ProjectiveLine.branchSet K) :
    B.toScheme p ∈ SchemeProjectiveLine.markedSchemePointSet K := by
  classical
  change p ∈ ProjectiveLine.branchFinset K at hp
  rw [← linearPointFinset_eq_branchFinset K] at hp
  change p ∈ linearPointFinset K at hp
  rw [linearPointFinset] at hp
  rcases Finset.mem_image.mp hp with ⟨label, _hlabel, hp_eq⟩
  rw [← hp_eq, B.toScheme_linearPoint label]
  exact schemeCarrierPoint_mem_markedSchemePointSet K label

theorem mem_branchSet_of_toScheme_mem_markedSchemePointSet
    {p : ProjectiveLine.P1 K}
    (hp : B.toScheme p ∈ SchemeProjectiveLine.markedSchemePointSet K) :
    p ∈ ProjectiveLine.branchSet K := by
  classical
  change B.toScheme p ∈ SchemeProjectiveLine.markedSchemePointFinset K at hp
  rw [← schemeCarrierPointFinset_eq_markedSchemePointFinset K] at hp
  change B.toScheme p ∈ schemeCarrierPointFinset K at hp
  rw [schemeCarrierPointFinset] at hp
  rcases Finset.mem_image.mp hp with ⟨label, _hlabel, hp_eq⟩
  have hscheme :
      B.toScheme p = B.toScheme (linearPoint K label) := by
    rw [B.toScheme_linearPoint label]
    exact hp_eq.symm
  have hp_linear : p = linearPoint K label := B.injective hscheme
  rw [hp_linear]
  exact linearPoint_mem_branchFinset K label

theorem toScheme_mem_markedSchemePointSet_iff
    (p : ProjectiveLine.P1 K) :
    B.toScheme p ∈ SchemeProjectiveLine.markedSchemePointSet K ↔
      p ∈ ProjectiveLine.branchSet K := by
  exact
    ⟨fun hp => B.mem_branchSet_of_toScheme_mem_markedSchemePointSet hp,
      fun hp => B.toScheme_mem_markedSchemePointSet_of_mem_branchSet hp⟩

theorem toScheme_not_mem_markedSchemePointSet_of_not_mem_branchSet
    {p : ProjectiveLine.P1 K} (hp : p ∉ ProjectiveLine.branchSet K) :
    B.toScheme p ∉ SchemeProjectiveLine.markedSchemePointSet K := by
  intro hmarked
  exact hp (B.mem_branchSet_of_toScheme_mem_markedSchemePointSet hmarked)

/-- Avoiding the scheme marked triple after applying the bridge is equivalent
to avoiding the linear branch triple before applying it. -/
theorem toScheme_not_mem_markedSchemePointSet_iff
    (p : ProjectiveLine.P1 K) :
    B.toScheme p ∉ SchemeProjectiveLine.markedSchemePointSet K ↔
      p ∉ ProjectiveLine.branchSet K := by
  exact not_congr (B.toScheme_mem_markedSchemePointSet_iff p)

theorem toScheme_eq_iff
    {p q : ProjectiveLine.P1 K} :
    B.toScheme p = B.toScheme q ↔ p = q := by
  constructor
  · intro h
    exact B.injective h
  · intro h
    rw [h]

variable (F : Type v) [Field F] [Algebra F K]
variable {S : Set K} {β : K}
variable (P : P1PolynomialSeparationStep F K S β)

/-- The selected scheme-carrier target point obtained from the linear affine
target `[p(beta):1]`. -/
def schemeTargetPoint : SchemeProjectiveLine.P1 K :=
  B.toScheme P.targetPoint

/-- The scheme-carrier point map obtained from the linear affine polynomial
point map. -/
def schemePointMap (x : K) : SchemeProjectiveLine.P1 K :=
  B.toScheme (P.pointMap x)

/-- Equality of bridged affine polynomial points is equality of the underlying
linear projective-line points. -/
theorem schemePointMap_eq_target_iff
    (x : K) :
    B.schemePointMap F P x = B.schemeTargetPoint F P ↔
      P.pointMap x = P.targetPoint := by
  change B.toScheme (P.pointMap x) = B.toScheme P.targetPoint ↔
    P.pointMap x = P.targetPoint
  exact B.toScheme_eq_iff

/-- Separation from the bridged target is equivalent to separation from the
underlying linear target. -/
theorem schemePointMap_ne_target_iff
    (x : K) :
    B.schemePointMap F P x ≠ B.schemeTargetPoint F P ↔
      P.pointMap x ≠ P.targetPoint := by
  exact not_congr (B.schemePointMap_eq_target_iff F P x)

theorem schemeTargetPoint_not_mem_markedSchemePointSet :
    B.schemeTargetPoint F P ∉ SchemeProjectiveLine.markedSchemePointSet K := by
  exact B.toScheme_not_mem_markedSchemePointSet_of_not_mem_branchSet
    P.targetPoint_not_mem_branchSet

theorem schemePointMap_ne_target_of_mem
    {x : K} (hx : x ∈ S) :
    B.schemePointMap F P x ≠ B.schemeTargetPoint F P := by
  intro hscheme
  have hlinear : P.pointMap x = P.targetPoint := by
    exact B.injective hscheme
  exact P.pointMap_ne_target_of_mem hx hlinear

theorem derivative_ne_zero_at_schemePointMap_preimage
    {x : K} (hx : B.schemePointMap F P x = B.schemeTargetPoint F P) :
    Polynomial.aeval x P.polynomial.derivative ≠ 0 := by
  have hlinear : P.pointMap x = P.targetPoint := by
    exact B.injective hx
  exact P.derivative_ne_zero_at_pointMap_preimage hlinear

/-- Scheme-carrier transport of the affine-chart polynomial-separation package:
the selected target avoids the scheme marked triple, is separated from the input
set, and has only noncritical polynomial preimages. -/
theorem scheme_separates_avoids_marked_and_noncritical :
    B.schemeTargetPoint F P ∉ SchemeProjectiveLine.markedSchemePointSet K ∧
      (∀ x ∈ S, B.schemePointMap F P x ≠ B.schemeTargetPoint F P) ∧
        ∀ x : K, B.schemePointMap F P x = B.schemeTargetPoint F P →
          Polynomial.aeval x P.polynomial.derivative ≠ 0 := by
  exact
    ⟨B.schemeTargetPoint_not_mem_markedSchemePointSet F P,
      ⟨fun x hx => B.schemePointMap_ne_target_of_mem F P hx,
        fun x hx => B.derivative_ne_zero_at_schemePointMap_preimage F P hx⟩⟩

end LinearSchemePointBridge

end P1SchemePointBridge
end SourceStack
end HilbertTest
