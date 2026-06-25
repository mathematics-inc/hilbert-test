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

/-- Closed immersions are stable under composition. -/
theorem closedImmersion_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsClosedImmersion f] [IsClosedImmersion g] :
    IsClosedImmersion (f ≫ g) :=
  inferInstance

/-- Closed immersions are finite morphisms. -/
theorem closedImmersion_isFinite
    (f : X ⟶ Y) [IsClosedImmersion f] :
    IsFinite f :=
  inferInstance

/-- Closed immersions are universally closed. -/
theorem closedImmersion_universallyClosed
    (f : X ⟶ Y) [IsClosedImmersion f] :
    UniversallyClosed f :=
  inferInstance

/-- Closed immersions are proper morphisms. -/
theorem closedImmersion_isProper
    (f : X ⟶ Y) [IsClosedImmersion f] :
    IsProper f :=
  inferInstance

/-- Closed immersions are stable under base change. -/
theorem closedImmersion_stable_under_base_change :
    MorphismProperty.IsStableUnderBaseChange (@IsClosedImmersion) :=
  inferInstance

/-- Closed immersions are exactly finite monomorphisms in the Mathlib scheme
API. -/
theorem closedImmersion_iff_isFinite_and_mono
    (f : X ⟶ Y) :
    IsClosedImmersion f ↔ IsFinite f ∧ Mono f :=
  IsClosedImmersion.iff_isFinite_and_mono f

/-- Stacks finite-morphism layer: a composition of finite morphisms is finite. -/
theorem finite_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFinite f] [IsFinite g] :
    IsFinite (f ≫ g) :=
  inferInstance

/-- A morphism is finite iff it is integral and locally of finite type. -/
theorem finite_iff_integralHom_and_locallyOfFiniteType
    (f : X ⟶ Y) :
    IsFinite f ↔ IsIntegralHom f ∧ LocallyOfFiniteType f :=
  IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f

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

/-- Separated morphisms are stable under composition. -/
theorem separated_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [IsSeparated g] :
    IsSeparated (f ≫ g) :=
  inferInstance

/-- Separated morphisms are stable under base change. -/
theorem separated_stable_under_base_change :
    MorphismProperty.IsStableUnderBaseChange (@IsSeparated) :=
  inferInstance

/-- Universally closed morphisms are stable under composition. -/
theorem universallyClosed_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [UniversallyClosed f] [UniversallyClosed g] :
    UniversallyClosed (f ≫ g) :=
  inferInstance

/-- Universally closed morphisms are stable under base change. -/
theorem universallyClosed_stable_under_base_change :
    MorphismProperty.IsStableUnderBaseChange (@UniversallyClosed) :=
  inferInstance

/-- A universally closed morphism has a closed underlying topological map. -/
theorem universallyClosed_isClosedMap
    (f : X ⟶ Y) [UniversallyClosed f] :
    IsClosedMap f.base :=
  f.isClosedMap

/-- Proper morphisms are stable under composition. -/
theorem proper_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsProper f] [IsProper g] :
    IsProper (f ≫ g) :=
  MorphismProperty.comp_mem (@IsProper) f g inferInstance inferInstance

/-- Proper morphisms are stable under base change. -/
theorem proper_stable_under_base_change :
    MorphismProperty.IsStableUnderBaseChange (@IsProper) :=
  inferInstance

/-- A universally closed morphism has a topologically proper underlying map. -/
theorem universally_closed_isProperMap
    (f : X ⟶ Y) [UniversallyClosed f] :
    IsProperMap f.base :=
  f.isProperMap

/-- A proper morphism has a topologically proper underlying map. -/
theorem proper_isProperMap
    (f : X ⟶ Y) [IsProper f] :
    IsProperMap f.base :=
  f.isProperMap

/-- Étale morphisms are stable under composition. -/
theorem etale_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsEtale f] [IsEtale g] :
    IsEtale (f ≫ g) :=
  inferInstance

/-- Étale morphisms are stable under base change. -/
theorem etale_stable_under_base_change :
    MorphismProperty.IsStableUnderBaseChange (@IsEtale) :=
  inferInstance

end Schemes
end SourceStack
end HilbertTest
