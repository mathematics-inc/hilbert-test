import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
Projective-spectrum source wrappers.

This is the scheme-theoretic layer currently available in Mathlib below a full
`P^1` API: `Proj` as a scheme, its basic opens, affine charts, affine open
cover, stalk computation, and separatedness.
-/

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open HomogeneousLocalization

namespace HilbertTest
namespace SourceStack
namespace ProjectiveSpectrum

universe u v

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

/-- Membership in a projective basic open is nonmembership in the corresponding
homogeneous prime ideal. -/
theorem basicOpen_mem_iff
    (f : A) (x : Proj 𝒜) :
    x ∈ Proj.basicOpen 𝒜 f ↔ f ∉ x.asHomogeneousIdeal :=
  Proj.mem_basicOpen 𝒜 f x

/-- The basic open of `1` is all of `Proj`. -/
theorem basicOpen_one_eq_top :
    Proj.basicOpen 𝒜 (1 : A) = ⊤ :=
  Proj.basicOpen_one 𝒜

/-- The basic open of `0` is empty. -/
theorem basicOpen_zero_eq_bot :
    Proj.basicOpen 𝒜 (0 : A) = ⊥ :=
  Proj.basicOpen_zero 𝒜

/-- Positive powers do not change a projective basic open. -/
theorem basicOpen_pow_eq
    (f : A) (n : ℕ) (hn : 0 < n) :
    Proj.basicOpen 𝒜 (f ^ n) = Proj.basicOpen 𝒜 f :=
  Proj.basicOpen_pow 𝒜 f n hn

/-- The basic open of a product is the intersection of the basic opens. -/
theorem basicOpen_mul_eq_inf
    (f g : A) :
    Proj.basicOpen 𝒜 (f * g) =
      Proj.basicOpen 𝒜 f ⊓ Proj.basicOpen 𝒜 g :=
  Proj.basicOpen_mul 𝒜 f g

/-- Divisibility gives containment of projective basic opens. -/
theorem basicOpen_mono_of_dvd
    {f g : A} (hfg : f ∣ g) :
    Proj.basicOpen 𝒜 g ≤ Proj.basicOpen 𝒜 f :=
  Proj.basicOpen_mono 𝒜 f g hfg

/-- A basic open is the supremum of the basic opens of its homogeneous
components. -/
theorem basicOpen_eq_iSup_proj
    (f : A) :
    Proj.basicOpen 𝒜 f =
      ⨆ i : ℕ, Proj.basicOpen 𝒜 (GradedAlgebra.proj 𝒜 i f) :=
  Proj.basicOpen_eq_iSup_proj 𝒜 f

/-- Projective basic opens form a basis. -/
theorem isBasis_basicOpen :
    TopologicalSpace.Opens.IsBasis (Set.range (Proj.basicOpen 𝒜)) :=
  Proj.isBasis_basicOpen 𝒜

/-- A family spanning the irrelevant ideal covers `Proj` by its basic opens. -/
theorem iSup_basicOpen_eq_top
    {ι : Type*} (f : ι → A)
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ Ideal.span (Set.range f)) :
    ⨆ i, Proj.basicOpen 𝒜 (f i) = ⊤ :=
  Proj.iSup_basicOpen_eq_top 𝒜 f hf

/-- The structure morphism `Proj A -> Spec A₀` is separated. -/
theorem toSpecZero_isSeparated :
    IsSeparated (Proj.toSpecZero 𝒜) :=
  inferInstance

/-- `Proj A` is a separated scheme. -/
theorem proj_scheme_isSeparated :
    (Proj 𝒜).IsSeparated :=
  inferInstance

/-- The standard affine chart map `(A_f)_0 -> Proj A` is an open immersion. -/
theorem awayι_isOpenImmersion
    (f : A) {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    IsOpenImmersion (Proj.awayι 𝒜 f f_deg hm) :=
  inferInstance

/-- The range of the standard affine chart map is the corresponding basic
open. -/
theorem opensRange_awayι
    (f : A) {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    (Proj.awayι 𝒜 f f_deg hm).opensRange = Proj.basicOpen 𝒜 f :=
  Proj.opensRange_awayι 𝒜 f f_deg hm

/-- A positive-degree homogeneous basic open is affine. -/
theorem isAffineOpen_basicOpen
    (f : A) {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    IsAffineOpen (Proj.basicOpen 𝒜 f) :=
  Proj.isAffineOpen_basicOpen 𝒜 (f := f) f_deg hm

/-- The canonical affine open cover of `Proj`. -/
noncomputable def affineOpenCover : (Proj 𝒜).AffineOpenCover :=
  Proj.affineOpenCover 𝒜

/-- The stalk of `Proj A` at a point is the degree-zero localization at the
corresponding homogeneous prime. -/
theorem stalkIso_exists
    (x : Proj 𝒜) :
    Nonempty ((Proj 𝒜).presheaf.stalk x ≅
      CommRingCat.of (AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal)) :=
  ⟨Proj.stalkIso 𝒜 x⟩

/-- On a positive-degree homogeneous basic open, `Proj` is isomorphic to the
degree-zero localization spectrum. -/
theorem basicOpenIsoSpec_exists
    (f : A) {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    Nonempty ((Proj.basicOpen 𝒜 f).toScheme ≅ Spec (.of (Away 𝒜 f))) :=
  ⟨Proj.basicOpenIsoSpec 𝒜 f f_deg hm⟩

/-- On a positive-degree homogeneous basic open, sections identify with the
degree-zero localization. -/
theorem basicOpenIsoAway_exists
    (f : A) {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    Nonempty (CommRingCat.of (Away 𝒜 f) ≅ Γ(Proj 𝒜, Proj.basicOpen 𝒜 f)) :=
  ⟨Proj.basicOpenIsoAway 𝒜 f f_deg hm⟩

/-- The canonical map from the degree-zero localization to sections on a
projective basic open. -/
theorem awayToSection_exists
    (f : A) :
    Nonempty (CommRingCat.of (Away 𝒜 f) ⟶ Γ(Proj 𝒜, Proj.basicOpen 𝒜 f)) :=
  ⟨Proj.awayToSection 𝒜 f⟩

/-- The canonical morphism from a projective basic open to the corresponding
degree-zero localization spectrum. -/
theorem basicOpenToSpec_exists
    (f : A) :
    Nonempty ((Proj.basicOpen 𝒜 f).toScheme ⟶ Spec (.of (Away 𝒜 f))) :=
  ⟨Proj.basicOpenToSpec 𝒜 f⟩

/-- The standard affine chart map is compatible with the structure morphism to
`Spec A₀`. -/
theorem awayι_toSpecZero
    (f : A) {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    Proj.awayι 𝒜 f f_deg hm ≫ Proj.toSpecZero 𝒜 =
      Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers f))) :=
  Proj.awayι_toSpecZero 𝒜 f f_deg hm

/-- Refining a standard affine chart by multiplying by another homogeneous
element agrees with the induced map on degree-zero localizations. -/
theorem specMap_awayMap_awayι
    {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m)
    {m' : ℕ} {g : A} (g_deg : g ∈ 𝒜 m')
    {x : A} (hx : x = f * g) :
    Spec.map (CommRingCat.ofHom (awayMap 𝒜 g_deg hx)) ≫
      Proj.awayι 𝒜 f f_deg hm =
        Proj.awayι 𝒜 x (hx ▸ SetLike.mul_mem_graded f_deg g_deg)
          (hm.trans_le (m.le_add_right m')) :=
  Proj.SpecMap_awayMap_awayι 𝒜 f_deg hm g_deg hx

/-- The intersection of two standard affine charts is the standard affine chart
of their product. -/
theorem pullbackAwayιIso_exists
    {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m)
    {m' : ℕ} {g : A} (g_deg : g ∈ 𝒜 m') (hm' : 0 < m')
    {x : A} (hx : x = f * g) :
    Nonempty (Limits.pullback (Proj.awayι 𝒜 f f_deg hm) (Proj.awayι 𝒜 g g_deg hm') ≅
      Spec (CommRingCat.of (Away 𝒜 x))) :=
  ⟨Proj.pullbackAwayιIso 𝒜 f_deg hm g_deg hm' hx⟩

end ProjectiveSpectrum
end SourceStack
end HilbertTest
