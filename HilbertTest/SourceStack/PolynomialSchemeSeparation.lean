import HilbertTest.SourceStack.P1SchemePointBridge
import HilbertTest.SourceStack.PolynomialValueSurjectivity

/-!
Scheme-carrier polynomial separation existence.

This file composes the target-value realization theorem with the abstract
linear-to-scheme `P1` point bridge.  It gives the form needed by the later
scheme-valued Belyi reduction: from a finite input set and a polynomial with
nonzero derivative, choose `beta` so that the resulting scheme-carrier target
avoids the marked triple, the input set is separated from that target, and all
preimages over that target are noncritical for the polynomial.
-/

noncomputable section

open scoped Polynomial

namespace HilbertTest
namespace SourceStack
namespace PolynomialSchemeSeparation

open P1PolynomialSeparation
open P1SchemePointBridge
open PolynomialValueSurjectivity

universe u v

variable (F : Type u) (K : Type v)
variable [Field F] [Field K] [Algebra F K]
variable (B : LinearSchemePointBridge K)

/-- A nonzero-derivative polynomial over an algebraically closed target field
admits a selected `beta` whose associated scheme-carrier target avoids the
marked triple, separates the finite input set, and has only noncritical
polynomial preimages. -/
theorem exists_scheme_separation_package
    [IsAlgClosed K]
    {S : Set K} (hS : S.Finite)
    (p : F[X]) (hpder : p.derivative ≠ 0) :
    ∃ β : K, ∃ P : P1PolynomialSeparationStep F K S β,
      P.polynomial = p ∧
        B.schemeTargetPoint F P ∉ SchemeProjectiveLine.markedSchemePointSet K ∧
          (∀ x ∈ S, B.schemePointMap F P x ≠ B.schemeTargetPoint F P) ∧
            ∀ x : K, B.schemePointMap F P x = B.schemeTargetPoint F P →
              Polynomial.aeval x P.polynomial.derivative ≠ 0 := by
  obtain ⟨β, P, hP⟩ :=
    exists_p1PolynomialSeparationStep_of_derivative_ne_zero F K hS p hpder
  exact ⟨β, P, hP, B.scheme_separates_avoids_marked_and_noncritical F P⟩

end PolynomialSchemeSeparation
end SourceStack
end HilbertTest
