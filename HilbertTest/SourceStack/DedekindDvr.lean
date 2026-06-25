import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
Dedekind-domain and DVR source wrappers.

Finite morphism ramification on smooth curves is local at codimension-one
points.  Pinned Mathlib does not yet supply the curve-local bridge, but it does
provide the commutative-algebra layer: dimension-one prime behavior, localization
of Dedekind domains, DVR localizations, uniformizers, prime-power ideals, and
the additive valuation on a DVR.
-/

noncomputable section

open scoped nonZeroDivisors Polynomial

namespace HilbertTest
namespace SourceStack
namespace DedekindDvr

universe u v

section DimensionOne

/-- In a one-dimensional ring, every nonzero prime ideal is maximal. -/
theorem prime_isMaximal_of_dimensionLEOne
    {R : Type u} [CommRing R] [Ring.DimensionLEOne R]
    {p : Ideal R} (hp : p.IsPrime) (hne : p ≠ ⊥) :
    p.IsMaximal :=
  hp.isMaximal hne

/-- A strict inclusion between prime ideals in dimension `≤ 1` starts at `⊥`. -/
theorem eq_bot_of_prime_lt_prime
    {R : Type u} [CommRing R] [Ring.DimensionLEOne R]
    (p P : Ideal R) [p.IsPrime] [P.IsPrime]
    (hlt : p < P) :
    p = ⊥ :=
  Ring.DimensionLEOne.eq_bot_of_lt p P hlt

/-- Dimension `≤ 1` forbids chains of two strict prime inclusions. -/
theorem not_prime_chain_length_two
    {R : Type u} [CommRing R] [Ring.DimensionLEOne R]
    (p₀ p₁ p₂ : Ideal R) [p₁.IsPrime] [p₂.IsPrime] :
    ¬ (p₀ < p₁ ∧ p₁ < p₂) :=
  Ring.DimensionLEOne.not_lt_lt p₀ p₁ p₂

/-- Principal ideal domains have Krull dimension `≤ 1`. -/
theorem principalIdealRing_dimensionLEOne
    (A : Type u) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] :
    Ring.DimensionLEOne A :=
  Ring.DimensionLEOne.principal_ideal_ring A

end DimensionOne

section Dedekind

/-- Dedekind-domain characterization via a fraction field. -/
theorem isDedekindDomain_iff_fractionField
    (A : Type u) [CommRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K] :
    IsDedekindDomain A ↔
      IsDomain A ∧ IsNoetherianRing A ∧ Ring.DimensionLEOne A ∧
        ∀ {x : K}, IsIntegral A x → ∃ y, (algebraMap A K) y = x :=
  isDedekindDomain_iff A K

/-- Localizing a Dedekind domain away from zero divisors remains Dedekind. -/
theorem localization_isDedekindDomain
    (A : Type u) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    {M : Submonoid A} (hM : M ≤ nonZeroDivisors A)
    (Aₘ : Type v) [CommRing Aₘ] [IsDomain Aₘ] [Algebra A Aₘ]
    [IsLocalization M Aₘ] :
    IsDedekindDomain Aₘ :=
  IsLocalization.isDedekindDomain A hM Aₘ

/-- Localizing a Dedekind domain at a prime remains Dedekind. -/
theorem localization_atPrime_isDedekindDomain
    (A : Type u) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (P : Ideal A) [P.IsPrime]
    (Aₘ : Type v) [CommRing Aₘ] [IsDomain Aₘ] [Algebra A Aₘ]
    [IsLocalization.AtPrime Aₘ P] :
    IsDedekindDomain Aₘ :=
  IsLocalization.AtPrime.isDedekindDomain A P Aₘ

/-- The localization at a nonzero prime of a domain is not a field. -/
theorem localization_atPrime_not_isField
    (A : Type u) [CommRing A] [IsDomain A]
    {P : Ideal A} (hP : P ≠ ⊥) [P.IsPrime]
    (Aₘ : Type v) [CommRing Aₘ] [Algebra A Aₘ]
    [IsLocalization.AtPrime Aₘ P] :
    ¬ IsField Aₘ :=
  IsLocalization.AtPrime.not_isField A hP Aₘ

/-- Localizing a Dedekind domain at a nonzero prime gives a DVR. -/
theorem localization_atPrime_isDVR_of_dedekind
    (A : Type u) [CommRing A] [IsDomain A] [IsDedekindDomain A]
    {P : Ideal A} (hP : P ≠ ⊥) [P.IsPrime]
    (Aₘ : Type v) [CommRing Aₘ] [IsDomain Aₘ] [Algebra A Aₘ]
    [IsLocalization.AtPrime Aₘ P] :
    IsDiscreteValuationRing Aₘ :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hP Aₘ

/-- A Dedekind domain satisfies the local-DVR definition of Dedekind domain. -/
theorem dedekindDomain_to_dedekindDomainDvr
    (A : Type u) [CommRing A] [IsDomain A] [IsDedekindDomain A] :
    IsDedekindDomainDvr A :=
  IsDedekindDomain.isDedekindDomainDvr A

/-- The local-DVR definition of Dedekind domain implies integral closedness. -/
theorem dedekindDomainDvr_isIntegrallyClosed
    (A : Type u) [CommRing A] [IsDomain A] [IsDedekindDomainDvr A] :
    IsIntegrallyClosed A :=
  IsDedekindDomainDvr.isIntegrallyClosed A

/-- The local-DVR definition of Dedekind domain implies the standard Dedekind-domain class. -/
theorem dedekindDomainDvr_to_dedekindDomain
    (A : Type u) [CommRing A] [IsDomain A] [IsDedekindDomainDvr A] :
    IsDedekindDomain A :=
  IsDedekindDomainDvr.isDedekindDomain A

end Dedekind

section DVR

/-- A DVR is not a field. -/
theorem dvr_not_isField
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    ¬ IsField R :=
  IsDiscreteValuationRing.not_isField R

/-- In a DVR, an element is a uniformizer iff it generates the maximal ideal. -/
theorem irreducible_iff_uniformizer
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) :
    Irreducible ϖ ↔ IsLocalRing.maximalIdeal R = Ideal.span {ϖ} :=
  IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ

/-- Irreducible elements generate the maximal ideal of a DVR. -/
theorem irreducible_maximalIdeal_eq
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ) :
    IsLocalRing.maximalIdeal R = Ideal.span {ϖ} :=
  hϖ.maximalIdeal_eq

/-- A DVR has an irreducible uniformizer. -/
theorem exists_irreducible
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    ∃ ϖ : R, Irreducible ϖ :=
  IsDiscreteValuationRing.exists_irreducible R

/-- A DVR has a prime element. -/
theorem exists_prime
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    ∃ ϖ : R, Prime ϖ :=
  IsDiscreteValuationRing.exists_prime R

/-- A domain is a DVR iff it is a PID with a unique nonzero prime ideal. -/
theorem dvr_iff_pid_with_one_nonzero_prime
    (R : Type u) [CommRing R] [IsDomain R] :
    IsDiscreteValuationRing R ↔
      IsPrincipalIdealRing R ∧ ∃! P : Ideal R, P ≠ ⊥ ∧ P.IsPrime :=
  IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime R

/-- Any two irreducible elements in a DVR are associated. -/
theorem associated_of_irreducible
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {a b : R} (ha : Irreducible a) (hb : Irreducible b) :
    Associated a b :=
  IsDiscreteValuationRing.associated_of_irreducible R ha hb

/-- Every nonzero element of a DVR is associated to a power of a uniformizer. -/
theorem associated_pow_irreducible
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {x : R} (hx : x ≠ 0) {ϖ : R} (hϖ : Irreducible ϖ) :
    ∃ n : ℕ, Associated x (ϖ ^ n) :=
  IsDiscreteValuationRing.associated_pow_irreducible hx hϖ

/-- Every nonzero element of a DVR is a unit times a power of a uniformizer. -/
theorem eq_unit_mul_pow_irreducible
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {x : R} (hx : x ≠ 0) {ϖ : R} (hϖ : Irreducible ϖ) :
    ∃ n : ℕ, ∃ u : Rˣ, x = (u : R) * ϖ ^ n :=
  IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ

/-- Every nonzero ideal of a DVR is generated by a power of a uniformizer. -/
theorem ideal_eq_span_pow_irreducible
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {I : Ideal R} (hI : I ≠ ⊥) {ϖ : R} (hϖ : Irreducible ϖ) :
    ∃ n : ℕ, I = Ideal.span {ϖ ^ n} :=
  IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hϖ

/-- The DVR additive valuation sends zero to top. -/
theorem addVal_zero
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    IsDiscreteValuationRing.addVal R 0 = ⊤ :=
  IsDiscreteValuationRing.addVal_zero

/-- The DVR additive valuation sends one to zero. -/
theorem addVal_one
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    IsDiscreteValuationRing.addVal R 1 = 0 :=
  IsDiscreteValuationRing.addVal_one

/-- A uniformizer has additive valuation one. -/
theorem addVal_uniformizer
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ) :
    IsDiscreteValuationRing.addVal R ϖ = 1 :=
  IsDiscreteValuationRing.addVal_uniformizer hϖ

/-- The DVR additive valuation is multiplicative as an additive valuation. -/
theorem addVal_mul
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {a b : R} :
    IsDiscreteValuationRing.addVal R (a * b) =
      IsDiscreteValuationRing.addVal R a + IsDiscreteValuationRing.addVal R b :=
  IsDiscreteValuationRing.addVal_mul

/-- The DVR additive valuation of a power is the scalar multiple of the valuation. -/
theorem addVal_pow
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (a : R) (n : ℕ) :
    IsDiscreteValuationRing.addVal R (a ^ n) =
      n • IsDiscreteValuationRing.addVal R a :=
  IsDiscreteValuationRing.addVal_pow a n

/-- The DVR additive valuation is top exactly at zero. -/
theorem addVal_eq_top_iff
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {a : R} :
    IsDiscreteValuationRing.addVal R a = ⊤ ↔ a = 0 :=
  IsDiscreteValuationRing.addVal_eq_top_iff

/-- In a DVR, valuation comparison is divisibility. -/
theorem addVal_le_iff_dvd
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {a b : R} :
    IsDiscreteValuationRing.addVal R a ≤ IsDiscreteValuationRing.addVal R b ↔ a ∣ b :=
  IsDiscreteValuationRing.addVal_le_iff_dvd

/-- The DVR additive valuation satisfies the nonarchimedean inequality. -/
theorem addVal_add
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {a b : R} :
    IsDiscreteValuationRing.addVal R a ⊓ IsDiscreteValuationRing.addVal R b ≤
      IsDiscreteValuationRing.addVal R (a + b) :=
  IsDiscreteValuationRing.addVal_add

end DVR

end DedekindDvr
end SourceStack
end HilbertTest
