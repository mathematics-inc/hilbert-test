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

/-- Projective zero-locus membership is containment in the homogeneous ideal. -/
theorem zeroLocus_mem_iff
    (s : Set A) (x : _root_.ProjectiveSpectrum 𝒜) :
    x ∈ _root_.ProjectiveSpectrum.zeroLocus 𝒜 s ↔
      s ⊆ x.asHomogeneousIdeal :=
  _root_.ProjectiveSpectrum.mem_zeroLocus 𝒜 x s

/-- Projective zero loci are closed. -/
theorem isClosed_zeroLocus
    (s : Set A) :
    IsClosed (_root_.ProjectiveSpectrum.zeroLocus 𝒜 s) :=
  _root_.ProjectiveSpectrum.isClosed_zeroLocus 𝒜 s

/-- The zero locus of `{0}` is all of projective spectrum. -/
theorem zeroLocus_singleton_zero :
    _root_.ProjectiveSpectrum.zeroLocus 𝒜 ({0} : Set A) = Set.univ :=
  _root_.ProjectiveSpectrum.zeroLocus_singleton_zero 𝒜

/-- The zero locus of `{1}` is empty. -/
theorem zeroLocus_singleton_one :
    _root_.ProjectiveSpectrum.zeroLocus 𝒜 ({1} : Set A) = ∅ :=
  _root_.ProjectiveSpectrum.zeroLocus_singleton_one 𝒜

/-- Zero loci turn unions into intersections. -/
theorem zeroLocus_union
    (s t : Set A) :
    _root_.ProjectiveSpectrum.zeroLocus 𝒜 (s ∪ t) =
      _root_.ProjectiveSpectrum.zeroLocus 𝒜 s ∩
        _root_.ProjectiveSpectrum.zeroLocus 𝒜 t :=
  _root_.ProjectiveSpectrum.zeroLocus_union 𝒜 s t

/-- The zero locus of a product is the union of the two zero loci. -/
theorem zeroLocus_singleton_mul
    (f g : A) :
    _root_.ProjectiveSpectrum.zeroLocus 𝒜 ({f * g} : Set A) =
      _root_.ProjectiveSpectrum.zeroLocus 𝒜 {f} ∪
        _root_.ProjectiveSpectrum.zeroLocus 𝒜 {g} :=
  _root_.ProjectiveSpectrum.zeroLocus_singleton_mul 𝒜 f g

/-- Positive powers do not change singleton zero loci. -/
theorem zeroLocus_singleton_pow
    (f : A) (n : ℕ) (hn : 0 < n) :
    _root_.ProjectiveSpectrum.zeroLocus 𝒜 ({f ^ n} : Set A) =
      _root_.ProjectiveSpectrum.zeroLocus 𝒜 {f} :=
  _root_.ProjectiveSpectrum.zeroLocus_singleton_pow 𝒜 f n hn

/-- Membership in a vanishing ideal means vanishing at every point of the set. -/
theorem mem_vanishingIdeal_iff
    (t : Set (_root_.ProjectiveSpectrum 𝒜)) (f : A) :
    f ∈ _root_.ProjectiveSpectrum.vanishingIdeal t ↔
      ∀ x ∈ t, f ∈ x.asHomogeneousIdeal :=
  _root_.ProjectiveSpectrum.mem_vanishingIdeal t f

/-- The vanishing ideal of a singleton is the point's homogeneous ideal. -/
theorem vanishingIdeal_singleton
    (x : _root_.ProjectiveSpectrum 𝒜) :
    _root_.ProjectiveSpectrum.vanishingIdeal {x} = x.asHomogeneousIdeal :=
  _root_.ProjectiveSpectrum.vanishingIdeal_singleton x

/-- A set lies in a zero locus iff the defining set lies in its vanishing ideal. -/
theorem subset_zeroLocus_iff_subset_vanishingIdeal
    (t : Set (_root_.ProjectiveSpectrum 𝒜)) (s : Set A) :
    t ⊆ _root_.ProjectiveSpectrum.zeroLocus 𝒜 s ↔
      s ⊆ _root_.ProjectiveSpectrum.vanishingIdeal t :=
  _root_.ProjectiveSpectrum.subset_zeroLocus_iff_subset_vanishingIdeal 𝒜 t s

/-- A topological projective basic open is the complement of a singleton zero
locus. -/
theorem topological_basicOpen_eq_zeroLocus_compl
    (r : A) :
    (_root_.ProjectiveSpectrum.basicOpen 𝒜 r :
      Set (_root_.ProjectiveSpectrum 𝒜)) =
        (_root_.ProjectiveSpectrum.zeroLocus 𝒜 {r})ᶜ :=
  _root_.ProjectiveSpectrum.basicOpen_eq_zeroLocus_compl 𝒜 r

/-- Topological projective basic opens are open. -/
theorem isOpen_topological_basicOpen
    {a : A} :
    IsOpen (_root_.ProjectiveSpectrum.basicOpen 𝒜 a :
      Set (_root_.ProjectiveSpectrum 𝒜)) :=
  _root_.ProjectiveSpectrum.isOpen_basicOpen 𝒜

/-- A point lies outside a singleton zero locus iff the element is not in its
homogeneous ideal. -/
theorem mem_compl_zeroLocus_iff_not_mem
    {f : A} {I : _root_.ProjectiveSpectrum 𝒜} :
    I ∈ (_root_.ProjectiveSpectrum.zeroLocus 𝒜 {f})ᶜ ↔
      f ∉ I.asHomogeneousIdeal :=
  _root_.ProjectiveSpectrum.mem_compl_zeroLocus_iff_not_mem 𝒜

/-- The specialization order is membership in the closure of a singleton. -/
theorem le_iff_mem_closure
    (x y : _root_.ProjectiveSpectrum 𝒜) :
    x ≤ y ↔ y ∈ closure {x} :=
  _root_.ProjectiveSpectrum.le_iff_mem_closure 𝒜 x y

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
