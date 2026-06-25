import Mathlib.RingTheory.Etale.Field

/-!
Algebraic unramified/etale source wrappers.

Pinned Mathlib does not yet expose a scheme-level unramified morphism or branch
locus API.  It does provide the bottom commutative-algebra layer used by the
Stacks definitions: Kähler differentials, formal unramifiedness, formal
étaleness, étale algebras, and separability over fields.
-/

noncomputable section

open scoped TensorProduct

namespace HilbertTest
namespace SourceStack
namespace UnramifiedEtale

universe u v w

/-- Formal unramifiedness is equivalent to trivial Kähler differentials. -/
theorem formallyUnramified_iff_subsingleton_kaehlerDifferential
    (R : Type v) [CommRing R]
    (A : Type u) [CommRing A] [Algebra R A] :
    Algebra.FormallyUnramified R A ↔ Subsingleton (Ω[A⁄R]) :=
  Algebra.formallyUnramified_iff R A

/-- Formal unramifiedness is equivalent to uniqueness of square-zero lifts. -/
theorem formallyUnramified_iff_comp_injective
    (R : Type v) [CommRing R]
    (A : Type u) [CommRing A] [Algebra R A] :
    Algebra.FormallyUnramified R A ↔
      ∀ ⦃B : Type u⦄ [CommRing B] [Algebra R B] (I : Ideal B),
        I ^ 2 = ⊥ →
          Function.Injective ((Ideal.Quotient.mkₐ R I).comp :
            (A →ₐ[R] B) → A →ₐ[R] B ⧸ I) :=
  Algebra.FormallyUnramified.iff_comp_injective

/-- Formal unramifiedness is stable under composition. -/
theorem formallyUnramified_comp
    (R : Type u) [CommRing R]
    (A : Type v) [CommRing A] [Algebra R A]
    (B : Type w) [CommRing B] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B]
    [Algebra.FormallyUnramified R A] [Algebra.FormallyUnramified A B] :
    Algebra.FormallyUnramified R B :=
  Algebra.FormallyUnramified.comp R A B

/-- If a composite algebra is formally unramified over the base, then the top
algebra is formally unramified over the middle algebra. -/
theorem formallyUnramified_of_comp
    (R : Type u) [CommRing R]
    (A : Type v) [CommRing A] [Algebra R A]
    (B : Type w) [CommRing B] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B]
    [Algebra.FormallyUnramified R B] :
    Algebra.FormallyUnramified A B :=
  Algebra.FormallyUnramified.of_comp R A B

/-- Formal unramifiedness is stable under base change. -/
theorem formallyUnramified_base_change
    {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] [Algebra R A]
    (B : Type w) [CommRing B] [Algebra R B]
    [Algebra.FormallyUnramified R A] :
    Algebra.FormallyUnramified B (B ⊗[R] A) :=
  Algebra.FormallyUnramified.base_change B

/-- Localization at one element is unramified. -/
theorem unramified_of_isLocalization_Away
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (r : R) [IsLocalization.Away r A] :
    Algebra.Unramified R A :=
  Algebra.Unramified.of_isLocalization_Away r

/-- Unramified algebras are stable under composition. -/
theorem unramified_comp
    (R : Type u) [CommRing R]
    (A B : Type v) [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra.Unramified R A] [Algebra.Unramified A B] :
    Algebra.Unramified R B :=
  Algebra.Unramified.comp R A B

/-- Unramified algebras are stable under base change. -/
theorem unramified_base_change
    (R : Type u) [CommRing R]
    (A B : Type v) [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B]
    [Algebra.Unramified R A] :
    Algebra.Unramified B (B ⊗[R] A) :=
  inferInstance

/-- For essentially finite type field extensions, formal unramifiedness is
separability. -/
theorem formallyUnramified_iff_isSeparable
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [Algebra.EssFiniteType K L] :
    Algebra.FormallyUnramified K L ↔ Algebra.IsSeparable K L :=
  Algebra.FormallyUnramified.iff_isSeparable K L

/-- Formal étaleness is formal unramifiedness plus formal smoothness. -/
theorem formallyEtale_iff_unramified_and_smooth
    (R : Type u) [CommRing R]
    (A : Type u) [CommRing A] [Algebra R A] :
    Algebra.FormallyEtale R A ↔
      Algebra.FormallyUnramified R A ∧ Algebra.FormallySmooth R A :=
  Algebra.FormallyEtale.iff_unramified_and_smooth

/-- Formal étaleness implies formal unramifiedness. -/
theorem formallyEtale_to_formallyUnramified
    (R : Type u) [CommRing R]
    (A : Type u) [CommRing A] [Algebra R A]
    [Algebra.FormallyEtale R A] :
    Algebra.FormallyUnramified R A :=
  inferInstance

/-- Formal étaleness is transported by algebra isomorphisms. -/
theorem formallyEtale_of_equiv
    {R : Type u} [CommRing R]
    {A B : Type u} [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B]
    [Algebra.FormallyEtale R A]
    (e : A ≃ₐ[R] B) :
    Algebra.FormallyEtale R B :=
  Algebra.FormallyEtale.of_equiv e

/-- Formal étaleness is invariant under algebra isomorphisms. -/
theorem formallyEtale_iff_of_equiv
    {R : Type u} [CommRing R]
    {A B : Type u} [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B]
    (e : A ≃ₐ[R] B) :
    Algebra.FormallyEtale R A ↔ Algebra.FormallyEtale R B :=
  Algebra.FormallyEtale.iff_of_equiv e

/-- Localizations are formally étale. -/
theorem formallyEtale_of_isLocalization
    {R Rₘ : Type u} [CommRing R] [CommRing Rₘ]
    (M : Submonoid R) [Algebra R Rₘ] [IsLocalization M Rₘ] :
    Algebra.FormallyEtale R Rₘ :=
  Algebra.FormallyEtale.of_isLocalization M

/-- Formal étaleness descends to the localized base. -/
theorem formallyEtale_localization_base
    {R Rₘ Sₘ : Type u} [CommRing R] [CommRing Rₘ] [CommRing Sₘ]
    (M : Submonoid R)
    [Algebra R Sₘ] [Algebra R Rₘ] [Algebra Rₘ Sₘ]
    [IsScalarTower R Rₘ Sₘ] [IsLocalization M Rₘ]
    [Algebra.FormallyEtale R Sₘ] :
    Algebra.FormallyEtale Rₘ Sₘ :=
  Algebra.FormallyEtale.localization_base M

/-- Formal étaleness localizes on source and target. -/
theorem formallyEtale_localization_map
    {R S Rₘ Sₘ : Type u} [CommRing R] [CommRing S]
    [CommRing Rₘ] [CommRing Sₘ]
    (M : Submonoid R)
    [Algebra R S] [Algebra R Sₘ] [Algebra S Sₘ]
    [Algebra R Rₘ] [Algebra Rₘ Sₘ]
    [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]
    [IsLocalization M Rₘ]
    [IsLocalization (Submonoid.map (algebraMap R S) M) Sₘ]
    [Algebra.FormallyEtale R S] :
    Algebra.FormallyEtale Rₘ Sₘ :=
  Algebra.FormallyEtale.localization_map (R := R) (S := S)
    (Rₘ := Rₘ) (Sₘ := Sₘ) M

/-- Formal étaleness is stable under composition. -/
theorem formallyEtale_comp
    (R : Type u) [CommRing R]
    (A B : Type u) [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra.FormallyEtale R A] [Algebra.FormallyEtale A B] :
    Algebra.FormallyEtale R B :=
  Algebra.FormallyEtale.comp R A B

/-- Formal étaleness is stable under base change. -/
theorem formallyEtale_base_change
    {R : Type u} [CommRing R]
    {A : Type u} [CommRing A] [Algebra R A]
    (B : Type u) [CommRing B] [Algebra R B]
    [Algebra.FormallyEtale R A] :
    Algebra.FormallyEtale B (B ⊗[R] A) :=
  Algebra.FormallyEtale.base_change B

/-- For essentially finite type field extensions, formal étaleness is
separability. -/
theorem formallyEtale_iff_isSeparable
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [Algebra.EssFiniteType K L] :
    Algebra.FormallyEtale K L ↔ Algebra.IsSeparable K L :=
  Algebra.FormallyEtale.iff_isSeparable K L

/-- Separable field extensions are formally étale. -/
theorem formallyEtale_of_isSeparable
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [Algebra.IsSeparable K L] :
    Algebra.FormallyEtale K L :=
  Algebra.FormallyEtale.of_isSeparable K L

/-- Étale algebras are transported by algebra isomorphisms. -/
theorem etale_of_equiv
    {R : Type u} [CommRing R]
    {A B : Type u} [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B]
    [Algebra.Etale R A]
    (e : A ≃ₐ[R] B) :
    Algebra.Etale R B :=
  Algebra.Etale.of_equiv e

/-- Localization at one element is étale. -/
theorem etale_of_isLocalization_Away
    {R : Type u} [CommRing R]
    {A : Type u} [CommRing A] [Algebra R A]
    (r : R) [IsLocalization.Away r A] :
    Algebra.Etale R A :=
  Algebra.Etale.of_isLocalization_Away r

/-- Étale algebras are stable under composition. -/
theorem etale_comp
    (R : Type u) [CommRing R]
    (A B : Type u) [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra.Etale R A] [Algebra.Etale A B] :
    Algebra.Etale R B :=
  Algebra.Etale.comp R A B

/-- Étale algebras are stable under base change. -/
theorem etale_base_change
    (R : Type u) [CommRing R]
    (A B : Type u) [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B]
    [Algebra.Etale R A] :
    Algebra.Etale B (B ⊗[R] A) :=
  Algebra.Etale.baseChange R A B

end UnramifiedEtale
end SourceStack
end HilbertTest
