import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE

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

/-- In dimension `≤ 1`, a nonzero prime contained in a prime is equal to it. -/
theorem dimensionLEOne_prime_le_prime_iff_eq
    {R : Type u} [CommRing R] [Ring.DimensionLEOne R]
    {P Q : Ideal R} [P.IsPrime] [Q.IsPrime] (hP0 : P ≠ ⊥) :
    P ≤ Q ↔ P = Q :=
  Ring.DimensionLeOne.prime_le_prime_iff_eq hP0

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

/-- The maximal ideal of a local Dedekind domain is principal. -/
theorem localDedekind_maximalIdeal_isPrincipal
    (R : Type u) [CommRing R] [IsLocalRing R] [IsDomain R]
    [IsDedekindDomain R] :
    (IsLocalRing.maximalIdeal R).IsPrincipal :=
  maximalIdeal_isPrincipal_of_isDedekindDomain R

/-- If the maximal ideal of a noetherian local domain is principal, every
nonzero ideal is a power of the maximal ideal. -/
theorem localRing_exists_maximalIdeal_pow_eq_of_principal
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    (h' : (IsLocalRing.maximalIdeal R).IsPrincipal)
    (I : Ideal R) (hI : I ≠ ⊥) :
    ∃ n : ℕ, I = IsLocalRing.maximalIdeal R ^ n :=
  exists_maximalIdeal_pow_eq_of_principal R h' I hI

/-- A height-one prime ideal in a Dedekind domain is prime in the ideal
monoid. -/
theorem heightOneSpectrum_prime
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    (v : IsDedekindDomain.HeightOneSpectrum R) :
    Prime v.asIdeal :=
  IsDedekindDomain.HeightOneSpectrum.prime v

/-- A height-one prime ideal in a Dedekind domain is irreducible in the ideal
monoid. -/
theorem heightOneSpectrum_irreducible
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    (v : IsDedekindDomain.HeightOneSpectrum R) :
    Irreducible v.asIdeal :=
  IsDedekindDomain.HeightOneSpectrum.irreducible v

/-- A height-one prime ideal gives an irreducible associate class. -/
theorem heightOneSpectrum_associates_irreducible
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    (v : IsDedekindDomain.HeightOneSpectrum R) :
    Irreducible (Associates.mk v.asIdeal) :=
  IsDedekindDomain.HeightOneSpectrum.associates_irreducible v

/-- Powers of a nonzero proper ideal in a Dedekind domain are strictly
decreasing. -/
theorem ideal_pow_right_strictAnti
    {A : Type u} [CommRing A] [IsDedekindDomain A]
    (I : Ideal A) (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) :
    StrictAnti fun n : ℕ => I ^ n :=
  Ideal.pow_right_strictAnti I hI0 hI1

/-- A sufficiently large power of a nonzero proper ideal is strictly contained
in the ideal. -/
theorem ideal_pow_lt_self
    {A : Type u} [CommRing A] [IsDedekindDomain A]
    (I : Ideal A) (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) (e : ℕ) (he : 2 ≤ e) :
    I ^ e < I :=
  Ideal.pow_lt_self I hI0 hI1 e he

/-- Each ideal-power layer of a nonzero proper ideal has an element not in the
next layer. -/
theorem ideal_exists_mem_pow_not_mem_pow_succ
    {A : Type u} [CommRing A] [IsDedekindDomain A]
    (I : Ideal A) (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) (e : ℕ) :
    ∃ x ∈ I ^ e, x ∉ I ^ (e + 1) :=
  Ideal.exists_mem_pow_not_mem_pow_succ I hI0 hI1 e

/-- If an ideal is squeezed between successive powers of a nonzero prime, it is
the upper power. -/
theorem ideal_eq_prime_pow_of_succ_lt_of_le
    {A : Type u} [CommRing A] [IsDedekindDomain A]
    {P I : Ideal A} [P.IsPrime] (hP : P ≠ ⊥)
    {i : ℕ} (hlt : P ^ (i + 1) < I) (hle : I ≤ P ^ i) :
    I = P ^ i :=
  Ideal.eq_prime_pow_of_succ_lt_of_le hP hlt hle

/-- For a prime ideal in a Dedekind domain, product membership in a prime power
forces one factor into the prime or the other into the same power. -/
theorem prime_mul_mem_pow
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    (I : Ideal R) [I.IsPrime] {a b : R} {n : ℕ}
    (h : a * b ∈ I ^ n) :
    a ∈ I ∨ b ∈ I ^ n :=
  Ideal.IsPrime.mul_mem_pow I h

/-- Symmetric product-membership form for a prime-power ideal in a Dedekind
domain. -/
theorem prime_mem_pow_mul
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    (I : Ideal R) [I.IsPrime] {a b : R} {n : ℕ}
    (h : a * b ∈ I ^ n) :
    a ∈ I ^ n ∨ b ∈ I :=
  Ideal.IsPrime.mem_pow_mul I h

/-- A normalized-factor count is determined by containment in one prime power
but not the next. -/
theorem ideal_count_normalizedFactors_eq
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {p x : Ideal R} [p.IsPrime] {n : ℕ}
    (hle : x ≤ p ^ n) [DecidableEq (Ideal R)] (hlt : ¬ x ≤ p ^ (n + 1)) :
    Multiset.count p (UniqueFactorizationMonoid.normalizedFactors x) = n :=
  Ideal.count_normalizedFactors_eq hle hlt

end Dedekind

section DVR

/-- The maximal ideal of a DVR is nonzero. -/
theorem dvr_maximalIdeal_ne_bot
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    IsLocalRing.maximalIdeal R ≠ ⊥ :=
  IsDiscreteValuationRing.not_a_field R

/-- A DVR is not a field. -/
theorem dvr_not_isField
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    ¬ IsField R :=
  IsDiscreteValuationRing.not_isField R

/-- In a local domain, a nonzero generator of the maximal ideal is
irreducible. -/
theorem irreducible_of_span_eq_maximalIdeal
    {R : Type u} [CommRing R] [IsLocalRing R] [IsDomain R]
    (ϖ : R) (hϖ : ϖ ≠ 0)
    (h : IsLocalRing.maximalIdeal R = Ideal.span {ϖ}) :
    Irreducible ϖ :=
  IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal ϖ hϖ h

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

/-- Unit-times-uniformizer-power decompositions have the same exponent. -/
theorem unit_mul_pow_congr_pow
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {p q : R} (hp : Irreducible p) (hq : Irreducible q)
    (u v : Rˣ) (m n : ℕ)
    (h : (u : R) * p ^ m = (v : R) * q ^ n) :
    m = n :=
  IsDiscreteValuationRing.unit_mul_pow_congr_pow hp hq u v m n h

/-- Unit-times-powers of the same uniformizer have the same unit coefficient. -/
theorem unit_mul_pow_congr_unit
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ) (u v : Rˣ) (m n : ℕ)
    (h : (u : R) * ϖ ^ m = (v : R) * ϖ ^ n) :
    u = v :=
  IsDiscreteValuationRing.unit_mul_pow_congr_unit hϖ u v m n h

/-- The DVR additive valuation reads off the exponent in a
unit-times-uniformizer-power expression. -/
theorem addVal_def_unit_mul_pow
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (r : R) (u : Rˣ) {ϖ : R} (hϖ : Irreducible ϖ) (n : ℕ)
    (hr : r = (u : R) * ϖ ^ n) :
    IsDiscreteValuationRing.addVal R r = n :=
  IsDiscreteValuationRing.addVal_def r u hϖ n hr

/-- The DVR additive valuation of a unit times a uniformizer power is the
power. -/
theorem addVal_unit_mul_pow
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (u : Rˣ) {ϖ : R} (hϖ : Irreducible ϖ) (n : ℕ) :
    IsDiscreteValuationRing.addVal R ((u : R) * ϖ ^ n) = n :=
  IsDiscreteValuationRing.addVal_def' u hϖ n

/-- The DVR additive valuation of a uniformizer power is the exponent. -/
theorem irreducible_addVal_pow
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ) (n : ℕ) :
    IsDiscreteValuationRing.addVal R (ϖ ^ n) = n :=
  hϖ.addVal_pow n

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

/-- The cotangent space of a noetherian local ring is subsingleton exactly when
the ring is a field. -/
theorem localRing_subsingleton_cotangentSpace_iff_field
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    Subsingleton (IsLocalRing.CotangentSpace R) ↔ IsField R :=
  IsLocalRing.subsingleton_cotangentSpace_iff

/-- The cotangent dimension of a noetherian local ring is zero exactly when the
ring is a field. -/
theorem localRing_finrank_cotangentSpace_eq_zero_iff_field
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) = 0 ↔
      IsField R :=
  IsLocalRing.finrank_cotangentSpace_eq_zero_iff

/-- The cotangent space of a noetherian local ring has dimension at most one
exactly when the maximal ideal is principal. -/
theorem localRing_finrank_cotangentSpace_le_one_iff_maximalIdeal_isPrincipal
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) ≤ 1 ↔
      (IsLocalRing.maximalIdeal R).IsPrincipal :=
  IsLocalRing.finrank_cotangentSpace_le_one_iff

/-- For a noetherian local nonfield, principal maximal ideal is equivalent to
cotangent dimension exactly one. -/
theorem localRing_finrank_cotangentSpace_eq_one_iff_maximalIdeal_isPrincipal_of_not_isField
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hR : ¬ IsField R) :
    Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) = 1 ↔
      (IsLocalRing.maximalIdeal R).IsPrincipal := by
  constructor
  · intro h
    exact
      (localRing_finrank_cotangentSpace_le_one_iff_maximalIdeal_isPrincipal R).mp
        (by rw [h])
  · intro hprincipal
    have hle :
        Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) ≤ 1 :=
      (localRing_finrank_cotangentSpace_le_one_iff_maximalIdeal_isPrincipal R).mpr
        hprincipal
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with hzero | hone
    · exact False.elim
        (hR ((localRing_finrank_cotangentSpace_eq_zero_iff_field R).mp hzero))
    · exact hone

/-- Cotangent-space characterization of a DVR: for a noetherian local domain,
cotangent dimension one is equivalent to being a DVR. -/
theorem localRing_finrank_cotangentSpace_eq_one_iff_dvr
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R] :
    Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) = 1 ↔
      IsDiscreteValuationRing R :=
  IsLocalRing.finrank_CotangentSpace_eq_one_iff

/-- The cotangent space of a DVR has dimension one over its residue field. -/
theorem dvr_finrank_cotangentSpace_eq_one
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) = 1 :=
  IsLocalRing.finrank_CotangentSpace_eq_one R

/-- The cotangent space of a DVR has positive dimension over its residue
field. -/
theorem dvr_finrank_cotangentSpace_pos
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    0 < Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) := by
  rw [dvr_finrank_cotangentSpace_eq_one R]
  norm_num

end DVR

end DedekindDvr
end SourceStack
end HilbertTest
