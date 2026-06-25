import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
Source-stack scheme-morphism lemmas corresponding to Stacks Project facts used
in the Belyi-map definition: finite morphisms, smooth morphisms, and étale
morphisms are stable under the constructions needed for composition and
restriction/base change.
-/

noncomputable section

open CategoryTheory

namespace HilbertTest
namespace SourceStack
namespace Schemes

open AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

/-- Stacks finite-morphism layer: a composition of finite morphisms is finite. -/
theorem finite_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFinite f] [IsFinite g] :
    IsFinite (f ≫ g) :=
  inferInstance

/-- Stacks finite-morphism layer: a finite morphism is integral. -/
theorem finite_is_integral
    (f : X ⟶ Y) [IsFinite f] :
    IsIntegralHom f :=
  inferInstance

/-- Stacks finite-morphism layer: a finite morphism is locally of finite type. -/
theorem finite_locally_of_finite_type
    (f : X ⟶ Y) [IsFinite f] :
    LocallyOfFiniteType f :=
  inferInstance

/-- Stacks finite-morphism layer: finite morphisms are stable under base change. -/
theorem finite_stable_under_base_change :
    MorphismProperty.IsStableUnderBaseChange (@IsFinite) :=
  inferInstance

/-- Smooth morphisms are stable under composition. -/
theorem smooth_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSmooth f] [IsSmooth g] :
    IsSmooth (f ≫ g) :=
  inferInstance

/-- Smooth morphisms are stable under base change. -/
theorem smooth_stable_under_base_change :
    MorphismProperty.IsStableUnderBaseChange (@IsSmooth) :=
  AlgebraicGeometry.isSmooth_isStableUnderBaseChange

/-- Étale morphisms are stable under base change. -/
theorem etale_stable_under_base_change :
    MorphismProperty.IsStableUnderBaseChange (@IsEtale) :=
  inferInstance

end Schemes
end SourceStack
end HilbertTest
