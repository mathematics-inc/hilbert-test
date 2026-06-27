import HilbertTest.SourceStack.Schemes
import HilbertTest.SourceStack.SchemeProjectiveLine
import HilbertTest.SourceStack.Topology
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

open SchemeProjectiveLine

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

/-- Finite scheme-level Belyi map: the abstract Definition 1.1 data together
with the finiteness condition on the morphism. -/
structure FiniteBelyiMap {P : Scheme.{u}} (T : BelyiTarget P) (X : Scheme.{u})
    extends BelyiMap T X where
  finite_hom : IsFinite hom

namespace BelyiMap

variable {X P : Scheme.{u}} {T : BelyiTarget P} (φ : BelyiMap T X)

/-- The Belyi open of the source is the preimage of the target branch-complement
open. -/
def belyiOpen : X.Opens :=
  φ.hom ⁻¹ᵁ T.branchOpen

/-- The Belyi open is the preimage of the target branch-complement open as a
set. -/
theorem belyiOpen_carrier :
    (φ.belyiOpen : Set X) = φ.hom.base ⁻¹' T.branchOpen := by
  rfl

/-- Membership in the Belyi open is membership of the image in the target
branch-complement open. -/
theorem mem_belyiOpen_iff (x : X) :
    x ∈ φ.belyiOpen ↔ φ.hom.base x ∈ T.branchOpen := by
  rfl

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

namespace FiniteBelyiMap

variable {X P : Scheme.{u}} {T : BelyiTarget P} (φ : FiniteBelyiMap T X)

theorem toBelyiMap_hom :
    φ.toBelyiMap.hom = φ.hom := rfl

/-- The Belyi open of a finite Belyi map is the preimage of the target
branch-complement open as a set. -/
theorem belyiOpen_carrier :
    (φ.toBelyiMap.belyiOpen : Set X) = φ.hom.base ⁻¹' T.branchOpen := by
  rfl

/-- Membership in the Belyi open of a finite Belyi map is membership of the
image in the target branch-complement open. -/
theorem mem_belyiOpen_iff (x : X) :
    x ∈ φ.toBelyiMap.belyiOpen ↔ φ.hom.base x ∈ T.branchOpen := by
  rfl

/-- The underlying morphism is finite. -/
theorem isFinite_hom :
    IsFinite φ.hom :=
  φ.finite_hom

/-- The underlying morphism is dominant. -/
theorem isDominant_hom :
    IsDominant φ.hom :=
  φ.dominant

/-- The underlying continuous map has dense range. -/
theorem denseRange_hom :
    DenseRange φ.hom.base := by
  exact φ.toBelyiMap.denseRange_hom

/-- The restriction over the branch-complement open is etale. -/
theorem isEtale_restrict_branchOpen :
    IsEtale (φ.hom ∣_ T.branchOpen) :=
  φ.etale_on_branchOpen

/-- Restricting a finite Belyi map over the branch-complement open is still
finite. -/
theorem isFinite_restrict_branchOpen :
    IsFinite (φ.hom ∣_ T.branchOpen) := by
  letI : IsFinite φ.hom := φ.finite_hom
  exact _root_.HilbertTest.SourceStack.Schemes.finite_restrict φ.hom T.branchOpen

/-- A finite Belyi map is affine as a morphism. -/
theorem isAffineHom_hom :
    IsAffineHom φ.hom := by
  letI : IsFinite φ.hom := φ.finite_hom
  exact _root_.HilbertTest.SourceStack.Schemes.finite_isAffineHom φ.hom

/-- A finite Belyi map is separated as a morphism. -/
theorem isSeparated_hom :
    IsSeparated φ.hom := by
  letI : IsFinite φ.hom := φ.finite_hom
  exact _root_.HilbertTest.SourceStack.Schemes.finite_isSeparated φ.hom

/-- A finite Belyi map is quasi-compact as a morphism. -/
theorem quasiCompact_hom :
    QuasiCompact φ.hom := by
  letI : IsFinite φ.hom := φ.finite_hom
  exact _root_.HilbertTest.SourceStack.Schemes.finite_quasiCompact φ.hom

/-- The Belyi open includes into the source by an open immersion. -/
theorem belyiOpen_ι_isOpenImmersion :
    IsOpenImmersion φ.toBelyiMap.belyiOpen.ι :=
  φ.toBelyiMap.belyiOpen_ι_isOpenImmersion

/-- The restricted morphism composes with the target open immersion as the
source Belyi open immersion followed by the original map. -/
theorem morphismRestrict_to_branchOpen_ι :
    (φ.hom ∣_ T.branchOpen) ≫ T.branchOpen.ι =
      φ.toBelyiMap.belyiOpen.ι ≫ φ.hom := by
  exact φ.toBelyiMap.morphismRestrict_to_branchOpen_ι

/-- Compose a finite Belyi map with a finite dominant auxiliary morphism.  The
remaining geometric input is exactly the branch-control statement that the
composite is étale over the target branch-complement open. -/
def compAux {Y : Scheme.{u}} {T : BelyiTarget P} (φ : FiniteBelyiMap T Y)
    (aux : X ⟶ Y) [IsFinite aux] [IsDominant aux]
    (hEtale : IsEtale ((aux ≫ φ.hom) ∣_ T.branchOpen)) :
    FiniteBelyiMap T X where
  hom := aux ≫ φ.hom
  dominant := by
    letI : IsDominant φ.hom := φ.dominant
    exact (IsDominant.comp_iff (f := aux) (g := φ.hom)).2 inferInstance
  etale_on_branchOpen := hEtale
  finite_hom := by
    letI : IsFinite φ.hom := φ.finite_hom
    exact _root_.HilbertTest.SourceStack.Schemes.finite_comp aux φ.hom

theorem compAux_hom {Y : Scheme.{u}} {T : BelyiTarget P}
    (φ : FiniteBelyiMap T Y) (aux : X ⟶ Y) [IsFinite aux] [IsDominant aux]
    (hEtale : IsEtale ((aux ≫ φ.hom) ∣_ T.branchOpen)) :
    (φ.compAux aux hEtale).hom = aux ≫ φ.hom := rfl

theorem compAux_base {Y : Scheme.{u}} {T : BelyiTarget P}
    (φ : FiniteBelyiMap T Y) (aux : X ⟶ Y) [IsFinite aux] [IsDominant aux]
    (hEtale : IsEtale ((aux ≫ φ.hom) ∣_ T.branchOpen)) (x : X) :
    (φ.compAux aux hEtale).hom.base x = φ.hom.base (aux.base x) := rfl

theorem compAux_isFinite_hom {Y : Scheme.{u}} {T : BelyiTarget P}
    (φ : FiniteBelyiMap T Y) (aux : X ⟶ Y) [IsFinite aux] [IsDominant aux]
    (hEtale : IsEtale ((aux ≫ φ.hom) ∣_ T.branchOpen)) :
    IsFinite (φ.compAux aux hEtale).hom :=
  (φ.compAux aux hEtale).finite_hom

theorem compAux_isDominant_hom {Y : Scheme.{u}} {T : BelyiTarget P}
    (φ : FiniteBelyiMap T Y) (aux : X ⟶ Y) [IsFinite aux] [IsDominant aux]
    (hEtale : IsEtale ((aux ≫ φ.hom) ∣_ T.branchOpen)) :
    IsDominant (φ.compAux aux hEtale).hom :=
  (φ.compAux aux hEtale).dominant

/-- If the auxiliary morphism is étale over the preimage of the branch-open,
then the composite is étale over the branch-open. -/
theorem compAux_etale_of_aux_restrict {Y : Scheme.{u}} {T : BelyiTarget P}
    (φ : FiniteBelyiMap T Y) (aux : X ⟶ Y) [IsFinite aux] [IsDominant aux]
    (hAuxEtale : IsEtale (aux ∣_ φ.toBelyiMap.belyiOpen)) :
    IsEtale ((aux ≫ φ.hom) ∣_ T.branchOpen) := by
  rw [morphismRestrict_comp]
  letI : IsEtale (aux ∣_ φ.hom ⁻¹ᵁ T.branchOpen) := by
    simpa [BelyiMap.belyiOpen] using hAuxEtale
  letI : IsEtale (φ.hom ∣_ T.branchOpen) := φ.etale_on_branchOpen
  exact _root_.HilbertTest.SourceStack.Schemes.etale_comp
    (aux ∣_ φ.hom ⁻¹ᵁ T.branchOpen) (φ.hom ∣_ T.branchOpen)

/-- Compose a finite Belyi map with an auxiliary finite dominant morphism that
is étale over the preimage of the branch-complement open. -/
def compAuxOfAuxEtale {Y : Scheme.{u}} {T : BelyiTarget P}
    (φ : FiniteBelyiMap T Y) (aux : X ⟶ Y) [IsFinite aux] [IsDominant aux]
    (hAuxEtale : IsEtale (aux ∣_ φ.toBelyiMap.belyiOpen)) :
    FiniteBelyiMap T X :=
  φ.compAux aux (φ.compAux_etale_of_aux_restrict aux hAuxEtale)

theorem compAuxOfAuxEtale_hom {Y : Scheme.{u}} {T : BelyiTarget P}
    (φ : FiniteBelyiMap T Y) (aux : X ⟶ Y) [IsFinite aux] [IsDominant aux]
    (hAuxEtale : IsEtale (aux ∣_ φ.toBelyiMap.belyiOpen)) :
    (φ.compAuxOfAuxEtale aux hAuxEtale).hom = aux ≫ φ.hom := rfl

theorem compAuxOfAuxEtale_base {Y : Scheme.{u}} {T : BelyiTarget P}
    (φ : FiniteBelyiMap T Y) (aux : X ⟶ Y) [IsFinite aux] [IsDominant aux]
    (hAuxEtale : IsEtale (aux ∣_ φ.toBelyiMap.belyiOpen)) (x : X) :
    (φ.compAuxOfAuxEtale aux hAuxEtale).hom.base x = φ.hom.base (aux.base x) := rfl

/-- The auxiliary-etale composition constructor yields a finite morphism. -/
theorem compAuxOfAuxEtale_isFinite_hom {Y : Scheme.{u}} {T : BelyiTarget P}
    (φ : FiniteBelyiMap T Y) (aux : X ⟶ Y) [IsFinite aux] [IsDominant aux]
    (hAuxEtale : IsEtale (aux ∣_ φ.toBelyiMap.belyiOpen)) :
    IsFinite (φ.compAuxOfAuxEtale aux hAuxEtale).hom :=
  (φ.compAuxOfAuxEtale aux hAuxEtale).finite_hom

/-- The auxiliary-etale composition constructor yields a dominant morphism. -/
theorem compAuxOfAuxEtale_isDominant_hom {Y : Scheme.{u}} {T : BelyiTarget P}
    (φ : FiniteBelyiMap T Y) (aux : X ⟶ Y) [IsFinite aux] [IsDominant aux]
    (hAuxEtale : IsEtale (aux ∣_ φ.toBelyiMap.belyiOpen)) :
    IsDominant (φ.compAuxOfAuxEtale aux hAuxEtale).hom :=
  (φ.compAuxOfAuxEtale aux hAuxEtale).dominant

/-- The auxiliary-etale composition constructor is étale over the target
branch-complement open. -/
theorem compAuxOfAuxEtale_isEtale_restrict_branchOpen {Y : Scheme.{u}}
    {T : BelyiTarget P}
    (φ : FiniteBelyiMap T Y) (aux : X ⟶ Y) [IsFinite aux] [IsDominant aux]
    (hAuxEtale : IsEtale (aux ∣_ φ.toBelyiMap.belyiOpen)) :
    IsEtale ((φ.compAuxOfAuxEtale aux hAuxEtale).hom ∣_ T.branchOpen) :=
  (φ.compAuxOfAuxEtale aux hAuxEtale).etale_on_branchOpen

/-- The Belyi open of the auxiliary-etale composition includes into the source
by an open immersion. -/
theorem compAuxOfAuxEtale_belyiOpen_ι_isOpenImmersion {Y : Scheme.{u}}
    {T : BelyiTarget P}
    (φ : FiniteBelyiMap T Y) (aux : X ⟶ Y) [IsFinite aux] [IsDominant aux]
    (hAuxEtale : IsEtale (aux ∣_ φ.toBelyiMap.belyiOpen)) :
    IsOpenImmersion (φ.compAuxOfAuxEtale aux hAuxEtale).toBelyiMap.belyiOpen.ι :=
  (φ.compAuxOfAuxEtale aux hAuxEtale).belyiOpen_ι_isOpenImmersion

end FiniteBelyiMap

section MarkedProjectiveLineTarget

variable (K : Type u) [CommRing K] [IsDomain K]

/-- In a T1 target topology, the complement of the checked marked triple on
`P1 K` is open.  The more general target below accepts this openness as an
explicit hypothesis, since scheme topologies are not T1 in full generality. -/
theorem markedSchemePointSet_compl_isOpen
    [T1Space (P1 K)] :
    IsOpen (markedSchemePointSet K)ᶜ :=
  finite_compl_isOpen (markedSchemePointSet_finite K)

/-- The branch-complement open `P1 K \\ {0,1,infinity}` as an open subscheme
carrier, assuming the complement of the checked marked triple is open. -/
def markedBranchOpen
    (hmarkedOpen : IsOpen (markedSchemePointSet K)ᶜ) :
    (P1 K).Opens where
  carrier := (markedSchemePointSet K)ᶜ
  is_open' := hmarkedOpen

theorem markedBranchOpen_carrier
    (hmarkedOpen : IsOpen (markedSchemePointSet K)ᶜ) :
    (markedBranchOpen K hmarkedOpen : Set (P1 K)) =
      (markedSchemePointSet K)ᶜ := rfl

theorem mem_markedBranchOpen_iff
    (hmarkedOpen : IsOpen (markedSchemePointSet K)ᶜ) (p : P1 K) :
    p ∈ markedBranchOpen K hmarkedOpen ↔ p ∉ markedSchemePointSet K := by
  rfl

/-- Mochizuki's marked `P1` target in the abstract scheme-level Belyi-map API. -/
def markedBelyiTarget
    (hmarkedOpen : IsOpen (markedSchemePointSet K)ᶜ) :
    BelyiTarget (P1 K) where
  branchOpen := markedBranchOpen K hmarkedOpen

theorem markedBelyiTarget_branchOpen
    (hmarkedOpen : IsOpen (markedSchemePointSet K)ᶜ) :
    (markedBelyiTarget K hmarkedOpen).branchOpen =
      markedBranchOpen K hmarkedOpen := rfl

/-- T1-specialized marked `P1` target, convenient for topological cover
arguments that already assume finite sets are closed. -/
def markedBelyiTargetOfT1
    [T1Space (P1 K)] :
    BelyiTarget (P1 K) :=
  markedBelyiTarget K (markedSchemePointSet_compl_isOpen K)

theorem markedBelyiTargetOfT1_branchOpen
    [T1Space (P1 K)] :
    (markedBelyiTargetOfT1 K).branchOpen =
      markedBranchOpen K (markedSchemePointSet_compl_isOpen K) := rfl

variable {K}
variable {X : Scheme.{u}}
variable {hmarkedOpen : IsOpen (markedSchemePointSet K)ᶜ}

theorem BelyiMap.mem_marked_belyiOpen_iff
    (φ : BelyiMap (markedBelyiTarget K hmarkedOpen) X) (x : X) :
    x ∈ φ.belyiOpen ↔ φ.hom.base x ∉ markedSchemePointSet K := by
  rfl

theorem BelyiMap.marked_belyiOpen_carrier
    (φ : BelyiMap (markedBelyiTarget K hmarkedOpen) X) :
    (φ.belyiOpen : Set X) =
      {x : X | φ.hom.base x ∉ markedSchemePointSet K} := by
  rfl

theorem FiniteBelyiMap.mem_marked_belyiOpen_iff
    (φ : FiniteBelyiMap (markedBelyiTarget K hmarkedOpen) X) (x : X) :
    x ∈ φ.toBelyiMap.belyiOpen ↔ φ.hom.base x ∉ markedSchemePointSet K := by
  rfl

theorem FiniteBelyiMap.marked_belyiOpen_carrier
    (φ : FiniteBelyiMap (markedBelyiTarget K hmarkedOpen) X) :
    (φ.toBelyiMap.belyiOpen : Set X) =
      {x : X | φ.hom.base x ∉ markedSchemePointSet K} := by
  rfl

end MarkedProjectiveLineTarget

end SchemeBelyi
end SourceStack
end HilbertTest
