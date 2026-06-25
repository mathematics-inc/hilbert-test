import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.Finite
import Mathlib.RingTheory.Unramified.Pi
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Valuation.RamificationGroup

/-!
Ring-theoretic unramifiedness and ramification source wrappers.

The noncritical Belyi argument ultimately needs a scheme-level statement about
critical values.  Pinned Mathlib does not provide branch loci for maps of
curves, but it does provide the algebraic source layer for unramified algebras
and Dedekind-domain ramification/inertia.  These wrappers expose that checked
layer as small Hilbert targets.
-/

noncomputable section

open scoped TensorProduct Pointwise

namespace HilbertTest
namespace SourceStack
namespace Ramification

universe u v w x

section AlgebraUnramified

/-- Algebraic unramifiedness includes formal unramifiedness. -/
theorem algebraUnramified_formallyUnramified
    (R : Type u) [CommRing R]
    (A : Type v) [CommRing A] [Algebra R A]
    [Algebra.Unramified R A] :
    Algebra.FormallyUnramified R A :=
  inferInstance

/-- Algebraic unramifiedness includes finite type. -/
theorem algebraUnramified_finiteType
    (R : Type u) [CommRing R]
    (A : Type v) [CommRing A] [Algebra R A]
    [Algebra.Unramified R A] :
    Algebra.FiniteType R A :=
  inferInstance

/-- Algebraic unramifiedness is transported by algebra isomorphisms. -/
theorem algebraUnramified_of_equiv
    {R : Type u} [CommRing R]
    {A : Type v} {B : Type w}
    [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B]
    [Algebra.Unramified R A]
    (e : A ≃ₐ[R] B) :
    Algebra.Unramified R B :=
  Algebra.Unramified.of_equiv e

/-- Localizing at one element is unramified. -/
theorem algebraUnramified_of_isLocalization_Away
    {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] [Algebra R A]
    (r : R) [IsLocalization.Away r A] :
    Algebra.Unramified R A :=
  Algebra.Unramified.of_isLocalization_Away r

/-- Algebraic unramifiedness is stable under composition. -/
theorem algebraUnramified_comp
    (R : Type u) [CommRing R]
    (A : Type v) [CommRing A] [Algebra R A]
    (B : Type w) [CommRing B] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B]
    [Algebra.Unramified R A] [Algebra.Unramified A B] :
    Algebra.Unramified R B :=
  Algebra.Unramified.comp R A B

/-- Algebraic unramifiedness is stable under base change. -/
theorem algebraUnramified_baseChange
    (R : Type u) [CommRing R]
    (A : Type v) [CommRing A] [Algebra R A]
    (B : Type w) [CommRing B] [Algebra R B]
    [Algebra.Unramified R A] :
    Algebra.Unramified B (B ⊗[R] A) :=
  Algebra.Unramified.baseChange R A B

/-- Separable field extensions are formally unramified. -/
theorem formallyUnramified_of_field_isSeparable
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [Algebra.IsSeparable K L] :
    Algebra.FormallyUnramified K L :=
  Algebra.FormallyUnramified.of_isSeparable K L

/-- An essentially finite type formally unramified field extension is separable. -/
theorem formallyUnramified_isSeparable_of_field
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [Algebra.FormallyUnramified K L] [Algebra.EssFiniteType K L] :
    Algebra.IsSeparable K L :=
  Algebra.FormallyUnramified.isSeparable K L

/-- For essentially finite type field extensions, formal unramifiedness is separability. -/
theorem formallyUnramified_iff_field_isSeparable
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [Algebra.EssFiniteType K L] :
    Algebra.FormallyUnramified K L ↔ Algebra.IsSeparable K L :=
  Algebra.FormallyUnramified.iff_isSeparable K L

/-- Formal unramifiedness descends to the localized base. -/
theorem formallyUnramified_localization_base
    {R : Type u} {Rₘ : Type v} {Sₘ : Type w}
    [CommRing R] [CommRing Rₘ] [CommRing Sₘ]
    (M : Submonoid R)
    [Algebra R Sₘ] [Algebra R Rₘ] [Algebra Rₘ Sₘ]
    [IsScalarTower R Rₘ Sₘ]
    [Algebra.FormallyUnramified R Sₘ] :
    Algebra.FormallyUnramified Rₘ Sₘ :=
  Algebra.FormallyUnramified.localization_base M

/-- Formal unramifiedness localizes on source and target. -/
theorem formallyUnramified_localization_map
    {R : Type u} {S : Type v} {Rₘ : Type w} {Sₘ : Type x}
    [CommRing R] [CommRing S] [CommRing Rₘ] [CommRing Sₘ]
    (M : Submonoid R)
    [Algebra R S] [Algebra R Sₘ] [Algebra S Sₘ]
    [Algebra R Rₘ] [Algebra Rₘ Sₘ]
    [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]
    [IsLocalization (Submonoid.map (algebraMap R S) M) Sₘ]
    [Algebra.FormallyUnramified R S] :
    Algebra.FormallyUnramified Rₘ Sₘ :=
  Algebra.FormallyUnramified.localization_map (R := R) (S := S)
    (Rₘ := Rₘ) (Sₘ := Sₘ) M

/-- A finite-type algebra is formally unramified iff it admits the tensor-product
idempotent criterion. -/
theorem formallyUnramified_iff_exists_tensorProduct
    (R : Type u) [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] :
    Algebra.FormallyUnramified R S ↔
      ∃ t : S ⊗[R] S,
        (∀ s, ((1 : S) ⊗ₜ[R] s - s ⊗ₜ[R] (1 : S)) * t = 0) ∧
          Algebra.TensorProduct.lmul' R t = 1 :=
  Algebra.FormallyUnramified.iff_exists_tensorProduct

/-- The tensor element supplied by finite-type formal unramifiedness. -/
noncomputable def formallyUnramified_tensorElem
    (R : Type u) [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S]
    [Algebra.FormallyUnramified R S] [Algebra.EssFiniteType R S] :
    S ⊗[R] S :=
  Algebra.FormallyUnramified.elem R S

/-- The tensor element annihilates each generator `1 ⊗ s - s ⊗ 1`. -/
theorem formallyUnramified_one_tmul_sub_tmul_one_mul_tensorElem
    {R : Type u} [CommRing R]
    {S : Type v} [CommRing S] [Algebra R S]
    [Algebra.FormallyUnramified R S] [Algebra.EssFiniteType R S]
    (s : S) :
    ((1 : S) ⊗ₜ[R] s - s ⊗ₜ[R] (1 : S)) *
        formallyUnramified_tensorElem R S = 0 :=
  Algebra.FormallyUnramified.one_tmul_sub_tmul_one_mul_elem s

/-- Multiplication by the tensor element equalizes left and right tensors. -/
theorem formallyUnramified_one_tmul_mul_tensorElem
    {R : Type u} [CommRing R]
    {S : Type v} [CommRing S] [Algebra R S]
    [Algebra.FormallyUnramified R S] [Algebra.EssFiniteType R S]
    (s : S) :
    ((1 : S) ⊗ₜ[R] s) * formallyUnramified_tensorElem R S =
      (s ⊗ₜ[R] (1 : S)) * formallyUnramified_tensorElem R S :=
  Algebra.FormallyUnramified.one_tmul_mul_elem s

/-- The tensor element maps to one under multiplication. -/
theorem formallyUnramified_lmul_tensorElem
    (R : Type u) [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S]
    [Algebra.FormallyUnramified R S] [Algebra.EssFiniteType R S] :
    Algebra.TensorProduct.lmul' R (formallyUnramified_tensorElem R S) = 1 :=
  Algebra.FormallyUnramified.lmul_elem

/-- A free finite-type formally unramified algebra is module-finite. -/
theorem formallyUnramified_finite_of_free
    (R : Type u) [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S]
    [Algebra.FormallyUnramified R S] [Algebra.EssFiniteType R S]
    [Module.Free R S] :
    Module.Finite R S :=
  Algebra.FormallyUnramified.finite_of_free R S

/-- Over a finite-type formally unramified algebra, `R`-flat modules are `S`-flat. -/
theorem formallyUnramified_flat_of_restrictScalars
    (R : Type u) [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S]
    (M : Type w) [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M]
    [Algebra.FormallyUnramified R S] [Algebra.EssFiniteType R S]
    [Module.Flat R M] :
    Module.Flat S M :=
  Algebra.FormallyUnramified.flat_of_restrictScalars R S M

/-- Over a finite-type formally unramified algebra, `R`-projective modules are
`S`-projective. -/
theorem formallyUnramified_projective_of_restrictScalars
    (R : Type u) [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S]
    (M : Type w) [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M]
    [Algebra.FormallyUnramified R S] [Algebra.EssFiniteType R S]
    [Module.Projective R M] :
    Module.Projective S M :=
  Algebra.FormallyUnramified.projective_of_restrictScalars R S M

/-- Formal unramifiedness of a finite product is componentwise. -/
theorem formallyUnramified_pi_iff
    {R : Type (max u v)} {I : Type v} [Finite I]
    (A : I → Type (max u v))
    [CommRing R] [(i : I) → CommRing (A i)]
    [(i : I) → Algebra R (A i)] :
    Algebra.FormallyUnramified R ((i : I) → A i) ↔
      ∀ i, Algebra.FormallyUnramified R (A i) :=
  Algebra.FormallyUnramified.pi_iff A

end AlgebraUnramified

section IdealRamification

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S]

/-- The ramification index is the largest exponent satisfying the defining containment. -/
theorem ramificationIdx_spec
    {f : R →+* S} {p : Ideal R} {P : Ideal S} {n : ℕ}
    (hle : Ideal.map f p ≤ P ^ n)
    (hgt : ¬ Ideal.map f p ≤ P ^ (n + 1)) :
    Ideal.ramificationIdx f p P = n :=
  Ideal.ramificationIdx_spec hle hgt

/-- The bottom ideal has ramification index zero. -/
theorem ramificationIdx_bot
    {f : R →+* S} {P : Ideal S} :
    Ideal.ramificationIdx f (⊥ : Ideal R) P = 0 :=
  Ideal.ramificationIdx_bot

/-- If the mapped ideal is not contained in `P`, the ramification index is zero. -/
theorem ramificationIdx_of_not_le
    {f : R →+* S} {p : Ideal R} {P : Ideal S}
    (h : ¬ Ideal.map f p ≤ P) :
    Ideal.ramificationIdx f p P = 0 :=
  Ideal.ramificationIdx_of_not_le h

/-- The mapped ideal is contained in the prime power at the ramification index. -/
theorem le_pow_ramificationIdx
    {f : R →+* S} {p : Ideal R} {P : Ideal S} :
    Ideal.map f p ≤ P ^ Ideal.ramificationIdx f p P :=
  Ideal.le_pow_ramificationIdx

/-- Pulling back the ramification prime power contains the original ideal. -/
theorem le_comap_pow_ramificationIdx
    {f : R →+* S} {p : Ideal R} {P : Ideal S} :
    p ≤ Ideal.comap f (P ^ Ideal.ramificationIdx f p P) :=
  Ideal.le_comap_pow_ramificationIdx

/-- A nonzero ramification index forces containment in the comap of `P`. -/
theorem le_comap_of_ramificationIdx_ne_zero
    {f : R →+* S} {p : Ideal R} {P : Ideal S}
    (h : Ideal.ramificationIdx f p P ≠ 0) :
    p ≤ Ideal.comap f P :=
  Ideal.le_comap_of_ramificationIdx_ne_zero h

/-- In a Dedekind domain, ramification index is the multiplicity in the normalized factorization. -/
theorem ramificationIdx_eq_normalizedFactors_count
    {f : R →+* S} {p : Ideal R} {P : Ideal S}
    [IsDedekindDomain S] [DecidableEq (Ideal S)]
    (hp0 : Ideal.map f p ≠ ⊥)
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    Ideal.ramificationIdx f p P =
      Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (Ideal.map f p)) :=
  Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count hp0 hP hP0

/-- In a Dedekind domain, containment in a nonzero mapped ideal gives nonzero ramification. -/
theorem ramificationIdx_ne_zero_of_dedekind
    {f : R →+* S} {p : Ideal R} {P : Ideal S}
    [IsDedekindDomain S]
    (hp0 : Ideal.map f p ≠ ⊥)
    (hP : P.IsPrime)
    (hle : Ideal.map f p ≤ P) :
    Ideal.ramificationIdx f p P ≠ 0 :=
  Ideal.IsDedekindDomain.ramificationIdx_ne_zero hp0 hP hle

/-- If `P` lies over a maximal ideal `p`, inertia degree is the residue field finrank. -/
theorem inertiaDeg_algebraMap
    (p : Ideal R) (P : Ideal S)
    [Algebra R S] [P.LiesOver p] [p.IsMaximal] :
    Ideal.inertiaDeg p P = Module.finrank (R ⧸ p) (S ⧸ P) :=
  Ideal.inertiaDeg_algebraMap p P

/-- For a finite algebra over a maximal ideal, inertia degree is positive. -/
theorem inertiaDeg_pos
    (p : Ideal R) (P : Ideal S)
    [Algebra R S] [p.IsMaximal] [Module.Finite R S] [P.LiesOver p] :
    0 < Ideal.inertiaDeg p P :=
  Ideal.inertiaDeg_pos p P

/-- Ramification indices multiply in a tower of ring homomorphisms. -/
theorem ramificationIdx_tower
    {T : Type w} [CommRing T]
    [IsDedekindDomain S] [IsDedekindDomain T]
    {f : R →+* S} {g : S →+* T}
    {p : Ideal R} {P : Ideal S} {Q : Ideal T}
    [P.IsPrime] [Q.IsPrime]
    (hg0 : Ideal.map g P ≠ ⊥)
    (hfg : Ideal.map (g.comp f) p ≠ ⊥)
    (hg : Ideal.map g P ≤ Q) :
    Ideal.ramificationIdx (g.comp f) p Q =
      Ideal.ramificationIdx f p P * Ideal.ramificationIdx g P Q :=
  Ideal.ramificationIdx_tower hg0 hfg hg

/-- Ramification indices multiply in a tower of algebras. -/
theorem ramificationIdx_algebra_tower
    {T : Type w} [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsDedekindDomain S] [IsDedekindDomain T]
    {p : Ideal R} {P : Ideal S} {Q : Ideal T}
    [P.IsPrime] [Q.IsPrime]
    (hg0 : Ideal.map (algebraMap S T) P ≠ ⊥)
    (hfg : Ideal.map (algebraMap R T) p ≠ ⊥)
    (hg : Ideal.map (algebraMap S T) P ≤ Q) :
    Ideal.ramificationIdx (algebraMap R T) p Q =
      Ideal.ramificationIdx (algebraMap R S) p P *
        Ideal.ramificationIdx (algebraMap S T) P Q :=
  Ideal.ramificationIdx_algebra_tower hg0 hfg hg

/-- Inertia degrees multiply in a tower of algebras. -/
theorem inertiaDeg_algebra_tower
    {T : Type w} [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (p : Ideal R) (P : Ideal S) (I : Ideal T)
    [p.IsMaximal] [P.IsMaximal] [P.LiesOver p] [I.LiesOver P] :
    Ideal.inertiaDeg p I = Ideal.inertiaDeg p P * Ideal.inertiaDeg P I :=
  Ideal.inertiaDeg_algebra_tower p P I

/-- The fundamental identity: the sum of ramification-index times inertia-degree
over primes above `p` equals the field extension degree. -/
theorem sum_ramification_inertia
    (R : Type u) [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S]
    (p : Ideal R)
    (K : Type w) [Field K]
    (L : Type x) [Field L]
    [IsDedekindDomain R] [IsDedekindDomain S]
    [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L]
    [Algebra K L] [Algebra R L]
    [IsScalarTower R S L] [IsScalarTower R K L]
    [Module.Finite R S] [p.IsMaximal]
    (hp0 : p ≠ ⊥) :
    (∑ P ∈ @Multiset.toFinset (Ideal S) (Classical.decEq (Ideal S))
        (UniqueFactorizationMonoid.factors (Ideal.map (algebraMap R S) p)),
        Ideal.ramificationIdx (algebraMap R S) p P * Ideal.inertiaDeg p P) =
      Module.finrank K L :=
  Ideal.sum_ramification_inertia S p K L hp0

end IdealRamification

section ValuationRamificationGroups

/-- The decomposition subgroup is the stabilizer of the valuation subring. -/
theorem decompositionSubgroup_eq_stabilizer
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) :
    ValuationSubring.decompositionSubgroup K A =
      MulAction.stabilizer (L ≃ₐ[K] L) A :=
  rfl

/-- The inertia subgroup is the kernel of the action on the residue field. -/
theorem inertiaSubgroup_eq_ker
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) :
    ValuationSubring.inertiaSubgroup K A =
      MonoidHom.ker
        (MulSemiringAction.toRingAut
          (ValuationSubring.decompositionSubgroup K A)
          (IsLocalRing.ResidueField A)) :=
  rfl

end ValuationRamificationGroups

end Ramification
end SourceStack
end HilbertTest
