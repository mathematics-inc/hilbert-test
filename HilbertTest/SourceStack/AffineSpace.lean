import Mathlib.AlgebraicGeometry.AffineSpace

/-!
Affine-space source wrappers.

This is the checked Mathlib layer for constructing morphisms to affine space
from global coordinate sections.  It is not the final projective-line map
construction, but it is the adjacent scheme API used by maps-from-sections
arguments.
-/

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

namespace HilbertTest
namespace SourceStack
namespace AffineSpace

universe u v

variable (n : Type v)
variable {S T U X : Scheme.{max u v}}

/-- The morphism to affine space built from coordinate sections lies over the
given base morphism. -/
theorem homOfVector_over
    (f : X ⟶ S) (w : n → Γ(X, ⊤)) :
    AlgebraicGeometry.AffineSpace.homOfVector f w ≫ 𝔸(n; S) ↘ S = f :=
  AlgebraicGeometry.AffineSpace.homOfVector_over f w

/-- Pulling back a standard coordinate along `homOfVector` recovers the chosen
global section. -/
theorem homOfVector_appTop_coord
    (f : X ⟶ S) (w : n → Γ(X, ⊤)) (i : n) :
    (AlgebraicGeometry.AffineSpace.homOfVector f w).appTop
      (AlgebraicGeometry.AffineSpace.coord S i) = w i :=
  AlgebraicGeometry.AffineSpace.homOfVector_appTop_coord f w i

/-- Morphisms to affine space are determined by the base morphism and coordinate
pullbacks. -/
theorem hom_ext
    {f g : X ⟶ 𝔸(n; S)}
    (h₁ : f ≫ 𝔸(n; S) ↘ S = g ≫ 𝔸(n; S) ↘ S)
    (h₂ : ∀ i,
      f.appTop (AlgebraicGeometry.AffineSpace.coord S i) =
        g.appTop (AlgebraicGeometry.AffineSpace.coord S i)) :
    f = g :=
  AlgebraicGeometry.AffineSpace.hom_ext h₁ h₂

/-- Over-morphisms to affine space are equivalent to coordinate global
sections. -/
theorem homOverEquiv_exists
    [X.Over S] :
    Nonempty ({ f : X ⟶ 𝔸(n; S) // f.IsOver S } ≃ (n → Γ(X, ⊤))) :=
  ⟨AlgebraicGeometry.AffineSpace.homOverEquiv S⟩

/-- Affine space over an affine scheme is the spectrum of a polynomial ring. -/
theorem isoOfIsAffine_exists
    [IsAffine S] :
    Nonempty (𝔸(n; S) ≅ Spec (.of (MvPolynomial n Γ(S, ⊤)))) :=
  ⟨AlgebraicGeometry.AffineSpace.isoOfIsAffine n S⟩

/-- Affine space over an affine scheme is affine. -/
theorem affineSpace_isAffine_of_base
    [IsAffine S] :
    IsAffine 𝔸(n; S) :=
  inferInstance

/-- Affine space over `Spec R` is `Spec R[n]`. -/
theorem SpecIso_exists
    (R : CommRingCat.{max u v}) :
    Nonempty (𝔸(n; Spec R) ≅ Spec (.of (MvPolynomial n R))) :=
  ⟨AlgebraicGeometry.AffineSpace.SpecIso n R⟩

/-- Affine-space base change maps lie over the base morphism. -/
theorem map_over
    (f : S ⟶ T) :
    AlgebraicGeometry.AffineSpace.map n f ≫ 𝔸(n; T) ↘ T =
      𝔸(n; S) ↘ S ≫ f :=
  AlgebraicGeometry.AffineSpace.map_over f

/-- Affine-space base change maps pull back standard coordinates to standard
coordinates. -/
theorem map_appTop_coord
    (f : S ⟶ T) (i : n) :
    (AlgebraicGeometry.AffineSpace.map n f).appTop
      (AlgebraicGeometry.AffineSpace.coord T i) =
        AlgebraicGeometry.AffineSpace.coord S i :=
  AlgebraicGeometry.AffineSpace.map_appTop_coord f i

/-- The affine-space map over the identity base morphism is the identity. -/
theorem map_id :
    AlgebraicGeometry.AffineSpace.map n (𝟙 S) = 𝟙 𝔸(n; S) :=
  AlgebraicGeometry.AffineSpace.map_id S

/-- Affine-space maps respect composition of base morphisms. -/
theorem map_comp
    (f : S ⟶ T) (g : T ⟶ U) :
    AlgebraicGeometry.AffineSpace.map n (f ≫ g) =
      AlgebraicGeometry.AffineSpace.map n f ≫
        AlgebraicGeometry.AffineSpace.map n g :=
  AlgebraicGeometry.AffineSpace.map_comp f g

/-- Reindexing affine coordinates lies over the identity on the base. -/
theorem reindex_over
    {m : Type v} (i : m → n) :
    AlgebraicGeometry.AffineSpace.reindex i S ≫ 𝔸(m; S) ↘ S =
      𝔸(n; S) ↘ S :=
  AlgebraicGeometry.AffineSpace.reindex_over i S

/-- Reindexing affine coordinates pulls back coordinates by the reindexing
function. -/
theorem reindex_appTop_coord
    {m : Type v} (i : m → n) (j : m) :
    (AlgebraicGeometry.AffineSpace.reindex i S).appTop
      (AlgebraicGeometry.AffineSpace.coord S j) =
        AlgebraicGeometry.AffineSpace.coord S (i j) :=
  AlgebraicGeometry.AffineSpace.reindex_appTop_coord i S j

/-- Reindexing by the identity is the identity. -/
theorem reindex_id :
    AlgebraicGeometry.AffineSpace.reindex (@id n) S = 𝟙 𝔸(n; S) :=
  AlgebraicGeometry.AffineSpace.reindex_id S

/-- Reindexing affine coordinates respects composition. -/
theorem reindex_comp
    {n₁ n₂ n₃ : Type v} (i : n₁ → n₂) (j : n₂ → n₃)
    (S : Scheme.{max u v}) :
    AlgebraicGeometry.AffineSpace.reindex (j ∘ i) S =
      AlgebraicGeometry.AffineSpace.reindex j S ≫
        AlgebraicGeometry.AffineSpace.reindex i S :=
  AlgebraicGeometry.AffineSpace.reindex_comp i j S

/-- Base-change maps and coordinate reindexing commute. -/
theorem map_reindex
    {n₁ n₂ : Type v} (i : n₁ → n₂) (f : S ⟶ T) :
    AlgebraicGeometry.AffineSpace.map n₂ f ≫
        AlgebraicGeometry.AffineSpace.reindex i T =
      AlgebraicGeometry.AffineSpace.reindex i S ≫
        AlgebraicGeometry.AffineSpace.map n₁ f :=
  AlgebraicGeometry.AffineSpace.map_reindex i f

end AffineSpace
end SourceStack
end HilbertTest
