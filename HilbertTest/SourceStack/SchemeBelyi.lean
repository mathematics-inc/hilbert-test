import HilbertTest.SourceStack.Schemes
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
Scheme-level abstraction of Mochizuki Definition 1.1.

Mathlib does not yet provide a specialized scheme-theoretic `P^1` with marked
points `0`, `1`, and `infinity`.  This module isolates the part of the
definition that is already available for an arbitrary target scheme equipped
with the open complement of the branch locus.
-/

noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace HilbertTest
namespace SourceStack
namespace SchemeBelyi

universe u

/-- A target scheme with the open over which a Belyi map is required to be
unramified/etale.  For Mochizuki this open is
`P^1 \\ {0,1,infinity}`. -/
structure BelyiTarget (P : Scheme.{u}) where
  branchOpen : P.Opens

/-- Abstract scheme-level Belyi map: a dominant morphism to the target that is
etale over the specified branch-complement open. -/
structure BelyiMap {P : Scheme.{u}} (T : BelyiTarget P) (X : Scheme.{u}) where
  hom : X ⟶ P
  dominant : IsDominant hom
  etale_on_branchOpen : IsEtale (hom ∣_ T.branchOpen)

namespace BelyiMap

variable {X P : Scheme.{u}} {T : BelyiTarget P} (φ : BelyiMap T X)

/-- The Belyi open of the source is the preimage of the target branch-complement
open. -/
def belyiOpen : X.Opens :=
  φ.hom ⁻¹ᵁ T.branchOpen

/-- The underlying morphism is dominant. -/
theorem isDominant_hom : IsDominant φ.hom :=
  φ.dominant

/-- The underlying continuous map has dense range. -/
theorem denseRange_hom : DenseRange φ.hom.base := by
  letI := φ.dominant
  exact φ.hom.denseRange

/-- The restriction over the branch-complement open is etale. -/
theorem isEtale_restrict_branchOpen :
    IsEtale (φ.hom ∣_ T.branchOpen) :=
  φ.etale_on_branchOpen

/-- The Belyi open includes into the source by an open immersion. -/
theorem belyiOpen_ι_isOpenImmersion :
    IsOpenImmersion φ.belyiOpen.ι :=
  inferInstance

/-- The restricted morphism composes with the target open immersion as the
source Belyi open immersion followed by the original map. -/
theorem morphismRestrict_to_branchOpen_ι :
    (φ.hom ∣_ T.branchOpen) ≫ T.branchOpen.ι = φ.belyiOpen.ι ≫ φ.hom := by
  exact morphismRestrict_ι φ.hom T.branchOpen

end BelyiMap

end SchemeBelyi
end SourceStack
end HilbertTest
