import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
Source-stack scheme-morphism lemmas corresponding to Stacks Project facts used
in the Belyi-map definition: finite morphisms, smooth morphisms, and étale
morphisms are stable under the constructions needed for composition and
restriction/base change.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace HilbertTest
namespace SourceStack
namespace Schemes

open AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

/-- Open immersions are stable under composition. -/
theorem openImmersion_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    IsOpenImmersion (f ≫ g) :=
  inferInstance

/-- Open immersions are monomorphisms. -/
theorem openImmersion_mono
    (f : X ⟶ Y) [IsOpenImmersion f] :
    Mono f :=
  inferInstance

/-- Open immersions are locally of finite type. -/
theorem openImmersion_locallyOfFiniteType
    (f : X ⟶ Y) [IsOpenImmersion f] :
    LocallyOfFiniteType f :=
  inferInstance

/-- Open immersions are smooth morphisms. -/
theorem openImmersion_isSmooth
    (f : X ⟶ Y) [IsOpenImmersion f] :
    IsSmooth f :=
  inferInstance

/-- Open immersions are étale morphisms. -/
theorem openImmersion_isEtale
    (f : X ⟶ Y) [IsOpenImmersion f] :
    IsEtale f :=
  inferInstance

/-- Open immersions are separated morphisms. -/
theorem openImmersion_isSeparated
    (f : X ⟶ Y) [IsOpenImmersion f] :
    IsSeparated f :=
  inferInstance

/-- Affine morphisms are stable under composition. -/
theorem affineHom_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsAffineHom f] [IsAffineHom g] :
    IsAffineHom (f ≫ g) :=
  inferInstance

/-- Affine morphisms are stable under base change. -/
theorem affineHom_stable_under_base_change :
    MorphismProperty.IsStableUnderBaseChange (@IsAffineHom) :=
  AlgebraicGeometry.isAffineHom_isStableUnderBaseChange

/-- Affine morphisms are quasi-compact. -/
theorem affineHom_quasiCompact
    (f : X ⟶ Y) [IsAffineHom f] :
    QuasiCompact f :=
  inferInstance

/-- Affine morphisms are separated. -/
theorem affineHom_isSeparated
    (f : X ⟶ Y) [IsAffineHom f] :
    IsSeparated f :=
  inferInstance

/-- An affine morphism with affine target has affine source. -/
theorem affineHom_isAffine_of_target
    (f : X ⟶ Y) [IsAffineHom f] [IsAffine Y] :
    IsAffine X :=
  AlgebraicGeometry.isAffine_of_isAffineHom f

/-- Finite morphisms are affine. -/
theorem finite_isAffineHom
    (f : X ⟶ Y) [IsFinite f] :
    IsAffineHom f :=
  inferInstance

/-- Integral morphisms are stable under composition. -/
theorem integralHom_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsIntegralHom f] [IsIntegralHom g] :
    IsIntegralHom (f ≫ g) :=
  MorphismProperty.comp_mem (@IsIntegralHom) f g inferInstance inferInstance

/-- Integral morphisms are stable under base change. -/
theorem integralHom_stable_under_base_change :
    MorphismProperty.IsStableUnderBaseChange (@IsIntegralHom) :=
  inferInstance

/-- Integral morphisms stay integral after restricting the target to an open. -/
theorem integralHom_restrict
    (f : X ⟶ Y) [IsIntegralHom f] (U : Y.Opens) :
    IsIntegralHom (f ∣_ U) :=
  IsLocalAtTarget.restrict (P := @IsIntegralHom) (f := f) inferInstance U

/-- An integral morphism that is locally of finite type is finite. -/
theorem finite_of_integralHom_and_locallyOfFiniteType
    (f : X ⟶ Y) [IsIntegralHom f] [LocallyOfFiniteType f] :
    IsFinite f :=
  (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f).mpr
    ⟨inferInstance, inferInstance⟩

/-- Quasi-compact morphisms are stable under composition. -/
theorem quasiCompact_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiCompact g] :
    QuasiCompact (f ≫ g) :=
  inferInstance

/-- Quasi-compact morphisms are stable under base change. -/
theorem quasiCompact_stable_under_base_change :
    MorphismProperty.IsStableUnderBaseChange (@QuasiCompact) :=
  inferInstance

/-- A quasi-compact morphism pulls compact open subsets back to compact
subsets. -/
theorem quasiCompact_isCompact_preimage
    (f : X ⟶ Y) [QuasiCompact f] {U : Set Y}
    (hUopen : IsOpen U) (hUcompact : IsCompact U) :
    IsCompact (f.base ⁻¹' U) :=
  QuasiCompact.isCompact_preimage U hUopen hUcompact

/-- A scheme is compact exactly when its terminal morphism is quasi-compact. -/
theorem compactSpace_iff_quasiCompact (X : Scheme.{u}) :
    CompactSpace X ↔ QuasiCompact (terminal.from X) :=
  AlgebraicGeometry.compactSpace_iff_quasiCompact X

/-- Over an affine target, quasi-compactness of a morphism is compactness of
the source. -/
theorem quasiCompact_over_affine_iff
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] :
    QuasiCompact f ↔ CompactSpace X :=
  AlgebraicGeometry.quasiCompact_over_affine_iff f

/-- Finite morphisms are quasi-compact. -/
theorem finite_quasiCompact
    (f : X ⟶ Y) [IsFinite f] :
    QuasiCompact f :=
  inferInstance

/-- Proper morphisms are quasi-compact. -/
theorem proper_quasiCompact
    (f : X ⟶ Y) [IsProper f] :
    QuasiCompact f :=
  inferInstance

/-- Quasi-separated morphisms are stable under composition. -/
theorem quasiSeparated_comp
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiSeparated f] [QuasiSeparated g] :
    QuasiSeparated (f ≫ g) :=
  inferInstance

/-- Quasi-separated morphisms are stable under base change. -/
theorem quasiSeparated_stable_under_base_change :
    MorphismProperty.IsStableUnderBaseChange (@QuasiSeparated) :=
  inferInstance

/-- Over an affine target, quasi-separated morphisms are exactly
quasi-separated sources. -/
theorem quasiSeparated_over_affine_iff
    (f : X ⟶ Y) [IsAffine Y] :
    QuasiSeparated f ↔ QuasiSeparatedSpace X :=
  AlgebraicGeometry.quasiSeparated_over_affine_iff f

/-- A scheme is quasi-separated exactly when its terminal morphism is
quasi-separated. -/
theorem quasiSeparatedSpace_iff_quasiSeparated
    (X : Scheme.{u}) :
    QuasiSeparatedSpace X ↔ QuasiSeparated (terminal.from X) :=
  AlgebraicGeometry.quasiSeparatedSpace_iff_quasiSeparated X

/-- Affine schemes are quasi-separated. -/
theorem affine_quasiSeparatedSpace
    (X : Scheme.{u}) [IsAffine X] :
    QuasiSeparatedSpace X :=
  AlgebraicGeometry.quasiSeparatedSpace_of_isAffine X

/-- Basic opens in compact opens are compact. -/
theorem isCompact_basicOpen
    (X : Scheme.{u}) {U : X.Opens} (hU : IsCompact (U : Set X))
    (f : Γ(X, U)) :
    IsCompact (X.basicOpen f : Set X) :=
  AlgebraicGeometry.isCompact_basicOpen X hU f

/-- If a section vanishes on a basic open inside a compact open, some power of
the defining section kills it. -/
theorem exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact
    (X : Scheme.{u}) {U : X.Opens} (hU : IsCompact U.1)
    (x f : Γ(X, U)) (H : x |_ᵣ (X.basicOpen f) = 0) :
    ∃ n : ℕ, f ^ n * x = 0 :=
  AlgebraicGeometry.exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X hU x f H

/-- On a compact quasi-separated open, sections on a basic open can be cleared
by multiplying by a power of the defining section. -/
theorem exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated
    (X : Scheme.{u}) (U : X.Opens)
    (hU : IsCompact U.1) (hU' : IsQuasiSeparated U.1)
    (f : Γ(X, U)) (x : Γ(X, X.basicOpen f)) :
    ∃ (n : ℕ) (y : Γ(X, U)),
      y |_ᵣ X.basicOpen f = (f |_ᵣ X.basicOpen f) ^ n * x :=
  AlgebraicGeometry.exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated X U hU hU' f x

/-- Qcqs lemma: over a compact quasi-separated open, sections on a basic open
are the localization away from the defining section. -/
theorem isLocalization_basicOpen_of_qcqs
    {U : X.Opens} (hU : IsCompact U.1) (hU' : IsQuasiSeparated U.1)
    (f : Γ(X, U)) :
    IsLocalization.Away f (Γ(X, X.basicOpen f)) :=
  AlgebraicGeometry.is_localization_basicOpen_of_qcqs hU hU' f

/-- If two sections over a compact quasi-separated open agree on a basic open,
then a power of the defining section equalizes them globally. -/
theorem exists_of_res_eq_of_qcqs
    {U : X.Opens} (hU : IsCompact U.1) (hU' : IsQuasiSeparated U.1)
    {f g s : Γ(X, U)} (hfg : f |_ᵣ X.basicOpen s = g |_ᵣ X.basicOpen s) :
    ∃ n, s ^ n * f = s ^ n * g :=
  AlgebraicGeometry.exists_of_res_eq_of_qcqs hU hU' hfg

/-- If a section over a compact quasi-separated open vanishes on a basic open,
then a power of the defining section kills it globally. -/
theorem exists_of_res_zero_of_qcqs
    {U : X.Opens} (hU : IsCompact U.1) (hU' : IsQuasiSeparated U.1)
    {f s : Γ(X, U)} (hf : f |_ᵣ X.basicOpen s = 0) :
    ∃ n, s ^ n * f = 0 :=
  AlgebraicGeometry.exists_of_res_zero_of_qcqs hU hU' hf

/-- On a compact open, a section is nilpotent exactly when its basic open is
empty. -/
theorem isNilpotent_iff_basicOpen_eq_bot_of_isCompact
    {U : X.Opens} (hU : IsCompact (U : Set X)) (f : Γ(X, U)) :
    IsNilpotent f ↔ X.basicOpen f = ⊥ :=
  AlgebraicGeometry.Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact hU f

/-- On a compact open, the zero locus of a set of sections is all of `X`
exactly when every section lies in the nilradical. -/
theorem zeroLocus_eq_top_iff_subset_nilradical_of_isCompact
    {U : X.Opens} (hU : IsCompact (U : Set X)) (s : Set Γ(X, U)) :
    X.zeroLocus s = ⊤ ↔ s ⊆ nilradical Γ(X, U) :=
  AlgebraicGeometry.Scheme.zeroLocus_eq_top_iff_subset_nilradical_of_isCompact hU s

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

/-- Finite morphisms stay finite after restricting the target to an open. -/
theorem finite_restrict
    (f : X ⟶ Y) [IsFinite f] (U : Y.Opens) :
    IsFinite (f ∣_ U) :=
  IsLocalAtTarget.restrict (P := @IsFinite) (f := f) inferInstance U

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

/-- Smooth morphisms stay smooth after restricting the target to an open. -/
theorem smooth_restrict
    (f : X ⟶ Y) [IsSmooth f] (U : Y.Opens) :
    IsSmooth (f ∣_ U) :=
  IsLocalAtTarget.restrict (P := @IsSmooth) (f := f) inferInstance U

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

/-- Separated morphisms stay separated after restricting the target to an
open. -/
theorem separated_restrict
    (f : X ⟶ Y) [IsSeparated f] (U : Y.Opens) :
    IsSeparated (f ∣_ U) :=
  IsLocalAtTarget.restrict (P := @IsSeparated) (f := f) inferInstance U

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

/-- Proper morphisms stay proper after restricting the target to an open. -/
theorem proper_restrict
    (f : X ⟶ Y) [IsProper f] (U : Y.Opens) :
    IsProper (f ∣_ U) :=
  IsLocalAtTarget.restrict (P := @IsProper) (f := f) inferInstance U

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

/-- Étale morphisms stay étale after restricting the target to an open. -/
theorem etale_restrict
    (f : X ⟶ Y) [IsEtale f] (U : Y.Opens) :
    IsEtale (f ∣_ U) :=
  IsLocalAtTarget.restrict (P := @IsEtale) (f := f) inferInstance U

end Schemes
end SourceStack
end HilbertTest
