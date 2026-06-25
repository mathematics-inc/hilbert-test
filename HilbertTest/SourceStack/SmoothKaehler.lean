import Mathlib.RingTheory.Smooth.Kaehler
import Mathlib.RingTheory.Smooth.Pi
import Mathlib.RingTheory.Smooth.StandardSmooth
import Mathlib.RingTheory.Kaehler.Polynomial

/-!
Formal smoothness and Kähler-differential source wrappers.

This is the commutative-algebra layer under smooth morphisms, ramification, and
curve differentials: nilpotent lifting for formally smooth algebras, stability
under composition/base change/localization, Kähler-characterizations of formal
smoothness, finite generation of differentials, and polynomial differential
computations.
-/

noncomputable section

open scoped TensorProduct Polynomial

namespace HilbertTest
namespace SourceStack
namespace SmoothKaehler

universe u v w t t' q q'

section FormalSmooth

variable {R : Type u} [CommSemiring R]
variable {A : Type u} [Semiring A] [Algebra R A]
variable {B : Type u} [CommRing B] [Algebra R B]

/-- Formal smoothness gives lifts across nilpotent quotients. -/
theorem formallySmooth_exists_lift
    [Algebra.FormallySmooth R A]
    (I : Ideal B) (hI : IsNilpotent I) (g : A →ₐ[R] B ⧸ I) :
    ∃ f : A →ₐ[R] B, (Ideal.Quotient.mkₐ R I).comp f = g :=
  Algebra.FormallySmooth.exists_lift I hI g

/-- The arbitrary formal-smooth lift composes back to the quotient map. -/
theorem formallySmooth_comp_lift
    [Algebra.FormallySmooth R A]
    (I : Ideal B) (hI : IsNilpotent I) (g : A →ₐ[R] B ⧸ I) :
    (Ideal.Quotient.mkₐ R I).comp (Algebra.FormallySmooth.lift I hI g) = g :=
  Algebra.FormallySmooth.comp_lift I hI g

/-- Formal smoothness is transported by algebra equivalences. -/
theorem formallySmooth_of_equiv
    {A' : Type u} [Semiring A'] [Algebra R A']
    [Algebra.FormallySmooth R A] (e : A ≃ₐ[R] A') :
    Algebra.FormallySmooth R A' :=
  Algebra.FormallySmooth.of_equiv e

/-- Polynomial algebras are formally smooth. -/
theorem formallySmooth_polynomial
    (R : Type u) [CommSemiring R] :
    Algebra.FormallySmooth R R[X] :=
  inferInstance

/-- Multivariable polynomial algebras are formally smooth. -/
theorem formallySmooth_mvPolynomial
    (R : Type u) [CommSemiring R] (σ : Type u) :
    Algebra.FormallySmooth R (MvPolynomial σ R) :=
  inferInstance

/-- Formal smoothness is stable under composition. -/
theorem formallySmooth_comp
    (R : Type u) [CommSemiring R]
    (A : Type u) [CommSemiring A] [Algebra R A]
    (B : Type u) [Semiring B] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B]
    [Algebra.FormallySmooth R A] [Algebra.FormallySmooth A B] :
    Algebra.FormallySmooth R B :=
  Algebra.FormallySmooth.comp R A B

/-- Formal smoothness is stable under base change. -/
theorem formallySmooth_base_change
    {R : Type u} [CommSemiring R]
    {A : Type u} [Semiring A] [Algebra R A]
    (B : Type u) [CommSemiring B] [Algebra R B]
    [Algebra.FormallySmooth R A] :
    Algebra.FormallySmooth B (B ⊗[R] A) :=
  Algebra.FormallySmooth.base_change B

/-- Formal smoothness descends to localized bases. -/
theorem formallySmooth_localization_base
    {R Rₘ Sₘ : Type u}
    [CommRing R] [CommRing Rₘ] [CommRing Sₘ]
    (M : Submonoid R)
    [Algebra R Sₘ] [Algebra R Rₘ] [Algebra Rₘ Sₘ]
    [IsScalarTower R Rₘ Sₘ] [IsLocalization M Rₘ]
    [Algebra.FormallySmooth R Sₘ] :
    Algebra.FormallySmooth Rₘ Sₘ :=
  Algebra.FormallySmooth.localization_base M

/-- Formal smoothness localizes source and target. -/
theorem formallySmooth_localization_map
    {R S Rₘ Sₘ : Type u}
    [CommRing R] [CommRing S] [CommRing Rₘ] [CommRing Sₘ]
    (M : Submonoid R)
    [Algebra R S] [Algebra R Sₘ] [Algebra S Sₘ]
    [Algebra R Rₘ] [Algebra Rₘ Sₘ]
    [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]
    [IsLocalization M Rₘ] [IsLocalization (Submonoid.map (algebraMap R S) M) Sₘ]
    [Algebra.FormallySmooth R S] :
    Algebra.FormallySmooth Rₘ Sₘ :=
  Algebra.FormallySmooth.localization_map
    (R := R) (S := S) (Rₘ := Rₘ) (Sₘ := Sₘ) M

/-- Formal smoothness of a finite product is componentwise. -/
theorem formallySmooth_pi_iff
    {R : Type (max u v)} {I : Type u} (A : I → Type (max u v))
    [CommRing R] [(i : I) → CommRing (A i)]
    [(i : I) → Algebra R (A i)] [Finite I] :
    Algebra.FormallySmooth R ((i : I) → A i) ↔
      ∀ i, Algebra.FormallySmooth R (A i) :=
  Algebra.FormallySmooth.pi_iff A

end FormalSmooth

section Smooth

/-- Smoothness is transported by algebra equivalences. -/
theorem smooth_of_equiv
    {R A B : Type u} [CommRing R]
    [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B]
    [Algebra.Smooth R A] (e : A ≃ₐ[R] B) :
    Algebra.Smooth R B :=
  Algebra.Smooth.of_equiv e

/-- Localization away from one element is smooth. -/
theorem smooth_of_isLocalization_Away
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (r : R) [IsLocalization.Away r A] :
    Algebra.Smooth R A :=
  Algebra.Smooth.of_isLocalization_Away r

/-- Smoothness is stable under composition. -/
theorem smooth_comp
    (R : Type u) [CommRing R]
    (A B : Type u) [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra.Smooth R A] [Algebra.Smooth A B] :
    Algebra.Smooth R B :=
  Algebra.Smooth.comp R A B

/-- Smoothness is stable under base change. -/
theorem smooth_baseChange
    (R : Type u) [CommRing R]
    (A B : Type u) [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] [Algebra.Smooth R A] :
    Algebra.Smooth B (B ⊗[R] A) :=
  Algebra.Smooth.baseChange R A B

end Smooth

section StandardSmooth

/-- Standard smooth algebras are finitely presented. -/
theorem standardSmooth_finitePresentation
    {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsStandardSmooth.{t, q} R S] :
    Algebra.FinitePresentation R S :=
  inferInstance

/-- Standard smoothness is stable under composition. -/
theorem standardSmooth_trans
    (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S]
    (T : Type w) [CommRing T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T]
    [Algebra.IsStandardSmooth.{t, q} R S]
    [Algebra.IsStandardSmooth.{t', q'} S T] :
    Algebra.IsStandardSmooth.{max t t', max q q'} R T :=
  Algebra.IsStandardSmooth.trans.{t, t', q, q'} R S T

/-- Localization away from an element is standard smooth. -/
theorem standardSmooth_localization_away
    {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    (r : R) [IsLocalization.Away r S] :
    Algebra.IsStandardSmooth.{0, 0} R S :=
  Algebra.IsStandardSmooth.localization_away r

/-- Standard smoothness is stable under base change. -/
theorem standardSmooth_baseChange
    {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    (T : Type w) [CommRing T] [Algebra R T]
    [Algebra.IsStandardSmooth.{t, q} R S] :
    Algebra.IsStandardSmooth.{t, q} T (T ⊗[R] S) :=
  Algebra.IsStandardSmooth.baseChange T

/-- Standard smoothness of specified relative dimension implies standard smoothness. -/
theorem standardSmoothOfRelativeDimension_isStandardSmooth
    (n : ℕ) {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsStandardSmoothOfRelativeDimension.{t, q} n R S] :
    Algebra.IsStandardSmooth.{t, q} R S :=
  Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth.{t, q} n

/-- The identity algebra is standard smooth of relative dimension zero. -/
theorem standardSmoothOfRelativeDimension_id
    (R : Type u) [CommRing R] :
    Algebra.IsStandardSmoothOfRelativeDimension.{t, q} 0 R R :=
  Algebra.IsStandardSmoothOfRelativeDimension.id R

/-- Standard smooth relative dimensions add in towers. -/
theorem standardSmoothOfRelativeDimension_trans
    (n m : ℕ)
    (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S]
    (T : Type w) [CommRing T] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T]
    [Algebra.IsStandardSmoothOfRelativeDimension.{t, q} n R S]
    [Algebra.IsStandardSmoothOfRelativeDimension.{t', q'} m S T] :
    Algebra.IsStandardSmoothOfRelativeDimension.{max t t', max q q'} (m + n) R T :=
  Algebra.IsStandardSmoothOfRelativeDimension.trans.{t, t', q, q'} n m R S T

/-- Localization away from an element is standard smooth of relative dimension zero. -/
theorem standardSmoothOfRelativeDimension_localization_away
    {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    (r : R) [IsLocalization.Away r S] :
    Algebra.IsStandardSmoothOfRelativeDimension.{0, 0} 0 R S :=
  Algebra.IsStandardSmoothOfRelativeDimension.localization_away r

/-- Standard smoothness of fixed relative dimension is stable under base change. -/
theorem standardSmoothOfRelativeDimension_baseChange
    (n : ℕ)
    {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    (T : Type w) [CommRing T] [Algebra R T]
    [Algebra.IsStandardSmoothOfRelativeDimension.{t, q} n R S] :
    Algebra.IsStandardSmoothOfRelativeDimension.{t, q} n T (T ⊗[R] S) :=
  Algebra.IsStandardSmoothOfRelativeDimension.baseChange n T

end StandardSmooth

section Kaehler

variable {R P S : Type u} [CommRing R] [CommRing P] [CommRing S]
variable [Algebra R P] [Algebra P S] [Algebra R S] [IsScalarTower R P S]

/-- For a presentation by a formally smooth algebra, formal smoothness is
equivalent to injectivity of the cotangent map plus projectivity of
Kähler differentials. -/
theorem formallySmooth_iff_injective_and_projective
    (hf : Function.Surjective (algebraMap P S))
    [Algebra.FormallySmooth R P] :
    Algebra.FormallySmooth R S ↔
      Function.Injective (KaehlerDifferential.kerCotangentToTensor R P S) ∧
        Module.Projective S (Ω[S⁄R]) :=
  Algebra.FormallySmooth.iff_injective_and_projective hf

/-- Formal smoothness is equivalent to vanishing of `H¹` of the cotangent
complex and projectivity of Kähler differentials. -/
theorem formallySmooth_iff_subsingleton_and_projective
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] :
    Algebra.FormallySmooth R S ↔
      Subsingleton (Algebra.H1Cotangent R S) ∧ Module.Projective S (Ω[S⁄R]) :=
  Algebra.FormallySmooth.iff_subsingleton_and_projective

/-- The Kähler ideal is finitely generated for essentially finite type algebras. -/
theorem kaehler_ideal_fg
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] :
    (KaehlerDifferential.ideal R S).FG :=
  KaehlerDifferential.ideal_fg R S

/-- Kähler differentials are finite for essentially finite type algebras. -/
theorem kaehler_finite
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] :
    Module.Finite S (Ω[S⁄R]) :=
  inferInstance

/-- Kähler differentials of a polynomial algebra are equivalent to the
polynomial algebra itself. -/
theorem kaehler_polynomialEquiv
    (R : Type u) [CommRing R] :
    Nonempty (Ω[R[X]⁄R] ≃ₗ[R[X]] R[X]) :=
  ⟨KaehlerDifferential.polynomialEquiv R⟩

/-- Under the polynomial Kähler equivalence, the universal derivation is the
formal derivative. -/
theorem kaehler_polynomialEquiv_D
    (R : Type u) [CommRing R] (P : R[X]) :
    (KaehlerDifferential.polynomialEquiv R)
      ((KaehlerDifferential.D R R[X]) P) =
        Polynomial.derivative P :=
  KaehlerDifferential.polynomialEquiv_D R P

/-- Kähler differentials of a multivariable polynomial algebra have the
standard basis indexed by variables. -/
theorem kaehler_mvPolynomialBasis
    (R : Type u) [CommRing R] (σ : Type v) :
    Nonempty (Basis σ (MvPolynomial σ R) (Ω[MvPolynomial σ R⁄R])) :=
  ⟨KaehlerDifferential.mvPolynomialBasis R σ⟩

/-- The universal derivation of a variable has basis representation `single i 1`. -/
theorem kaehler_mvPolynomialBasis_repr_D_X
    (R : Type u) [CommRing R] (σ : Type v) (i : σ) :
    (KaehlerDifferential.mvPolynomialBasis R σ).repr
      ((KaehlerDifferential.D R (MvPolynomial σ R)) (MvPolynomial.X i)) =
        Finsupp.single i 1 :=
  KaehlerDifferential.mvPolynomialBasis_repr_D_X R σ i

end Kaehler

end SmoothKaehler
end SourceStack
end HilbertTest
