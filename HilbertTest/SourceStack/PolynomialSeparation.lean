import HilbertTest.SourceStack.PolynomialMaps

/-!
Polynomial separation package for Mochizuki Lemma 2.4.

The proof replaces a finite algebraic set `S` by
`p(S) ∪ p(rootSet p')`.  If the selected value `p(β)` lies outside that
replacement set, then no point of `S` maps to `p(β)` and no preimage of `p(β)`
is critical for `p`.  The component lemmas were already checked in
`PolynomialMaps`; this file packages them as the exact reduction step used
before applying the rational-point separation lemmas on `P1`.
-/

noncomputable section

open scoped Polynomial

set_option linter.unusedSectionVars false

namespace HilbertTest
namespace SourceStack
namespace PolynomialSeparation

open PolynomialMaps

universe u v

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]

/-- A polynomial step separating a finite set `S` from a target value
`p(β)`, with the target value outside the finite replacement set containing
ordinary images and critical values. -/
structure PolynomialSeparationStep (S : Set E) (β : E) where
  polynomial : F[X]
  derivative_ne_zero : polynomial.derivative ≠ 0
  target_not_mem_replacement :
    Polynomial.aeval β polynomial ∉ replacementSet F E S polynomial

namespace PolynomialSeparationStep

variable {F E}
variable [Field F] [Field E] [Algebra F E]
variable {S : Set E} {β : E}
variable (P : PolynomialSeparationStep F E S β)

/-- The replacement set attached to the separating polynomial is finite when
the original set is finite. -/
theorem replacementSet_finite
    (hS : S.Finite) :
    (replacementSet F E S P.polynomial).Finite :=
  PolynomialMaps.replacementSet_finite F E hS P.polynomial

/-- No point of the original set maps to the selected target value. -/
theorem aeval_ne_target_of_mem
    {x : E} (hx : x ∈ S) :
    Polynomial.aeval x P.polynomial ≠ Polynomial.aeval β P.polynomial :=
  PolynomialMaps.aeval_ne_of_not_mem_replacementSet F E
    P.target_not_mem_replacement hx

/-- The target value is not a critical value of the separating polynomial. -/
theorem target_not_mem_criticalValueSet :
    Polynomial.aeval β P.polynomial ∉
      criticalValueSet F E P.polynomial :=
  ((PolynomialMaps.not_mem_replacementSet_iff F E P.polynomial
    (Polynomial.aeval β P.polynomial)).1 P.target_not_mem_replacement).2

/-- Every preimage of the selected target value is noncritical for the
separating polynomial. -/
theorem derivative_ne_zero_at_preimage
    {x : E} (hx : Polynomial.aeval x P.polynomial =
      Polynomial.aeval β P.polynomial) :
    Polynomial.aeval x P.polynomial.derivative ≠ 0 :=
  PolynomialMaps.derivative_aeval_ne_zero_of_value_not_mem_replacementSet
    F E P.derivative_ne_zero P.target_not_mem_replacement hx

/-- Packaged Lemma 2.4 consequence: the target value is separated from `S`, and
all of its preimages are noncritical. -/
theorem separates_and_noncritical :
    (∀ x ∈ S, Polynomial.aeval x P.polynomial ≠
        Polynomial.aeval β P.polynomial) ∧
      ∀ x : E, Polynomial.aeval x P.polynomial =
        Polynomial.aeval β P.polynomial →
          Polynomial.aeval x P.polynomial.derivative ≠ 0 := by
  exact
    ⟨fun x hx => P.aeval_ne_target_of_mem hx,
      fun x hx => P.derivative_ne_zero_at_preimage hx⟩

end PolynomialSeparationStep

end PolynomialSeparation
end SourceStack
end HilbertTest
