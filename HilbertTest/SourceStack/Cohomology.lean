import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
Generic sheaf-cohomology and scheme-module source wrappers.

This is the bottom of the cohomological source stack available in pinned
Mathlib.  It defines abelian sheaf cohomology via Ext groups and exposes the
abelian category of sheaves of modules over a scheme.  It does not contain
Serre duality, coherent cohomology on curves, or Riemann-Roch.
-/

noncomputable section

namespace HilbertTest
namespace SourceStack
namespace Cohomology

universe w' w v u

open CategoryTheory
open CategoryTheory.Abelian
open AlgebraicGeometry

section SheafCohomology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (F : Sheaf J AddCommGrp.{w})
variable [HasSheafify J AddCommGrp.{w}] [HasExt.{w'} (Sheaf J AddCommGrp.{w})]

/-- Sheaf cohomology is defined as an Ext group. -/
theorem sheaf_H_eq_ext
    (n : ℕ) :
    F.H n =
      Ext ((CategoryTheory.constantSheaf J AddCommGrp.{w}).obj
        (AddCommGrp.of (ULift ℤ))) F n :=
  rfl

/-- Sheaf cohomology in each degree is an additive commutative group. -/
theorem sheaf_H_addCommGroup
    (n : ℕ) :
    Nonempty (AddCommGroup (F.H n)) :=
  ⟨inferInstance⟩

end SheafCohomology

section CohomologyPresheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasSheafify J AddCommGrp.{v}] [HasExt.{w'} (Sheaf J AddCommGrp.{v})]

/-- The cohomology presheaf functor exists for abelian sheaves on a site. -/
theorem cohomologyPresheafFunctor_exists
    (n : ℕ) :
    Nonempty (Sheaf J AddCommGrp.{v} ⥤ Cᵒᵖ ⥤ AddCommGrp.{w'}) :=
  ⟨Sheaf.cohomologyPresheafFunctor J n⟩

/-- The cohomology presheaf of a fixed abelian sheaf exists in each degree. -/
theorem cohomologyPresheaf_exists
    (F : Sheaf J AddCommGrp.{v}) (n : ℕ) :
    Nonempty (Cᵒᵖ ⥤ AddCommGrp.{w'}) :=
  ⟨F.cohomologyPresheaf n⟩

end CohomologyPresheaf

section SchemeModules

/-- Sheaves of modules over a scheme form an abelian category. -/
theorem scheme_modules_abelian
    (X : Scheme.{u}) :
    Nonempty (Abelian X.Modules) :=
  ⟨inferInstance⟩

end SchemeModules

end Cohomology
end SourceStack
end HilbertTest
