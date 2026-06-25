import HilbertTest.SourceStack.ProjectiveSpectrum
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
Scheme-theoretic projective-line source wrappers.

This file packages the concrete scheme candidate `P^1_K = Proj K[X₀,X₁]`
available from Mathlib's general `Proj` construction, together with the two
standard affine charts.  It is the bridge between the linear projectivization
bookkeeping in `SourceStack.ProjectiveLine` and the scheme-valued target needed
for Belyi morphisms.
-/

namespace HilbertTest
namespace SourceStack
namespace SchemeProjectiveLine

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open HomogeneousLocalization

noncomputable section

universe u

variable (K : Type u) [CommRing K]

/-- The homogeneous coordinate ring of the scheme-theoretic projective line. -/
abbrev CoordinateRing : Type u := MvPolynomial (Fin 2) K

/-- The standard grading on `K[X₀,X₁]` by total degree. -/
abbrev grading : ℕ → Submodule K (CoordinateRing K) :=
  MvPolynomial.homogeneousSubmodule (Fin 2) K

instance gradingGradedAlgebra : GradedAlgebra (grading K) :=
  MvPolynomial.gradedAlgebra

/-- The scheme-theoretic projective line built as `Proj K[X₀,X₁]`. -/
abbrev P1 : Scheme.{u} := Proj (grading K)

/-- The first homogeneous coordinate `X₀`. -/
abbrev X0 : CoordinateRing K := MvPolynomial.X (0 : Fin 2)

/-- The second homogeneous coordinate `X₁`. -/
abbrev X1 : CoordinateRing K := MvPolynomial.X (1 : Fin 2)

theorem p1_eq_proj :
    P1 K = Proj (grading K) := rfl

theorem x0_mem_degree_one :
    X0 K ∈ grading K 1 := by
  rw [MvPolynomial.mem_homogeneousSubmodule]
  exact MvPolynomial.isHomogeneous_X K (0 : Fin 2)

theorem x1_mem_degree_one :
    X1 K ∈ grading K 1 := by
  rw [MvPolynomial.mem_homogeneousSubmodule]
  exact MvPolynomial.isHomogeneous_X K (1 : Fin 2)

theorem x0x1_mem_degree_two :
    X0 K * X1 K ∈ grading K 2 := by
  simpa [X0, X1, grading] using
    (SetLike.mul_mem_graded (x0_mem_degree_one K) (x1_mem_degree_one K) :
      X0 K * X1 K ∈ grading K (1 + 1))

theorem x0_chart_isOpenImmersion :
    IsOpenImmersion
      (Proj.awayι (grading K) (X0 K) (x0_mem_degree_one K) Nat.zero_lt_one) := by
  exact ProjectiveSpectrum.awayι_isOpenImmersion
    (grading K) (X0 K) (x0_mem_degree_one K) Nat.zero_lt_one

theorem x1_chart_isOpenImmersion :
    IsOpenImmersion
      (Proj.awayι (grading K) (X1 K) (x1_mem_degree_one K) Nat.zero_lt_one) := by
  exact ProjectiveSpectrum.awayι_isOpenImmersion
    (grading K) (X1 K) (x1_mem_degree_one K) Nat.zero_lt_one

theorem x0_chart_range :
    (Proj.awayι (grading K) (X0 K) (x0_mem_degree_one K) Nat.zero_lt_one).opensRange =
      Proj.basicOpen (grading K) (X0 K) := by
  exact ProjectiveSpectrum.opensRange_awayι
    (grading K) (X0 K) (x0_mem_degree_one K) Nat.zero_lt_one

theorem x1_chart_range :
    (Proj.awayι (grading K) (X1 K) (x1_mem_degree_one K) Nat.zero_lt_one).opensRange =
      Proj.basicOpen (grading K) (X1 K) := by
  exact ProjectiveSpectrum.opensRange_awayι
    (grading K) (X1 K) (x1_mem_degree_one K) Nat.zero_lt_one

theorem x0_basicOpen_isAffineOpen :
    IsAffineOpen (Proj.basicOpen (grading K) (X0 K)) := by
  exact ProjectiveSpectrum.isAffineOpen_basicOpen
    (grading K) (X0 K) (x0_mem_degree_one K) Nat.zero_lt_one

theorem x1_basicOpen_isAffineOpen :
    IsAffineOpen (Proj.basicOpen (grading K) (X1 K)) := by
  exact ProjectiveSpectrum.isAffineOpen_basicOpen
    (grading K) (X1 K) (x1_mem_degree_one K) Nat.zero_lt_one

theorem basicOpen_x0x1_eq_inf :
    Proj.basicOpen (grading K) (X0 K * X1 K) =
      Proj.basicOpen (grading K) (X0 K) ⊓ Proj.basicOpen (grading K) (X1 K) := by
  exact ProjectiveSpectrum.basicOpen_mul_eq_inf (grading K) (X0 K) (X1 K)

theorem coordinate_chart_intersection_exists :
    Nonempty (Limits.pullback
      (Proj.awayι (grading K) (X0 K) (x0_mem_degree_one K) Nat.zero_lt_one)
      (Proj.awayι (grading K) (X1 K) (x1_mem_degree_one K) Nat.zero_lt_one) ≅
      Spec (CommRingCat.of (Away (grading K) (X0 K * X1 K)))) := by
  exact ProjectiveSpectrum.pullbackAwayιIso_exists
    (grading K) (x0_mem_degree_one K) Nat.zero_lt_one
    (x1_mem_degree_one K) Nat.zero_lt_one rfl

theorem p1_isSeparated :
    (P1 K).IsSeparated := by
  exact ProjectiveSpectrum.proj_scheme_isSeparated (grading K)

theorem irrelevant_homogeneousComponent_zero
    (p : CoordinateRing K)
    (hp : p ∈ HomogeneousIdeal.irrelevant (grading K)) :
    MvPolynomial.homogeneousComponent 0 p = 0 := by
  have hproj : GradedAlgebra.proj (grading K) 0 p = 0 := by
    simpa [HomogeneousIdeal.mem_irrelevant_iff] using hp
  rw [GradedAlgebra.proj_apply] at hproj
  have hproj_coe :
      ((((DirectSum.decompose (grading K)) p) 0 : grading K 0) :
        CoordinateRing K) = 0 := by
    exact hproj
  have hproj_decomp :
      ((((DirectSum.Decomposition.decompose' p) 0 :
        MvPolynomial.homogeneousSubmodule (Fin 2) K 0) :
        CoordinateRing K) = 0) := by
    change ((((DirectSum.decompose (grading K)) p) 0 : grading K 0) :
      CoordinateRing K) = 0
    exact hproj_coe
  exact (MvPolynomial.decomposition.decompose'_apply p 0).symm.trans hproj_decomp

theorem irrelevant_le_span_coordinates :
    (HomogeneousIdeal.irrelevant (grading K)).toIdeal ≤
      Ideal.span (Set.range fun i : Fin 2 => (MvPolynomial.X i : CoordinateRing K)) := by
  intro p hp
  rw [show (Set.range fun i : Fin 2 => (MvPolynomial.X i : CoordinateRing K)) =
      (MvPolynomial.X '' (Set.univ : Set (Fin 2)) : Set (CoordinateRing K)) by
    ext q
    simp]
  rw [MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  by_contra hnone
  push_neg at hnone
  have hmzero : m = 0 := by
    ext i
    exact hnone i trivial
  have hdeg : m.degree = 0 := by
    rw [Finsupp.degree_eq_zero_iff]
    exact hmzero
  have hcomp : MvPolynomial.homogeneousComponent 0 p = 0 :=
    irrelevant_homogeneousComponent_zero K p hp
  have hcoeff :
      MvPolynomial.coeff m (MvPolynomial.homogeneousComponent 0 p) =
        MvPolynomial.coeff m p := by
    rw [MvPolynomial.coeff_homogeneousComponent, hdeg, if_pos rfl]
  have hcoeff_zero : MvPolynomial.coeff m p = 0 := by
    rw [← hcoeff, hcomp]
    simp
  exact (MvPolynomial.mem_support_iff.mp hm) hcoeff_zero

theorem standard_affine_chart_cover :
    (⨆ i : Fin 2, Proj.basicOpen (grading K) (MvPolynomial.X i : CoordinateRing K)) = ⊤ := by
  exact ProjectiveSpectrum.iSup_basicOpen_eq_top (grading K)
    (fun i : Fin 2 => (MvPolynomial.X i : CoordinateRing K))
    (irrelevant_le_span_coordinates K)

theorem two_chart_cover :
    Proj.basicOpen (grading K) (X0 K) ⊔ Proj.basicOpen (grading K) (X1 K) = ⊤ := by
  rw [← standard_affine_chart_cover K]
  apply le_antisymm
  · exact sup_le
      (le_iSup (fun i : Fin 2 =>
        Proj.basicOpen (grading K) (MvPolynomial.X i : CoordinateRing K)) 0)
      (le_iSup (fun i : Fin 2 =>
        Proj.basicOpen (grading K) (MvPolynomial.X i : CoordinateRing K)) 1)
  · refine iSup_le ?_
    intro i
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right

/-- The ideal generated by the first homogeneous coordinate. -/
abbrev x0Ideal : Ideal (CoordinateRing K) :=
  Ideal.span ({X0 K} : Set (CoordinateRing K))

/-- The ideal generated by the second homogeneous coordinate. -/
abbrev x1Ideal : Ideal (CoordinateRing K) :=
  Ideal.span ({X1 K} : Set (CoordinateRing K))

theorem x0Ideal_isHomogeneous :
    (x0Ideal K).IsHomogeneous (grading K) := by
  apply Ideal.homogeneous_span
  intro x hx
  simp only [Set.mem_singleton_iff] at hx
  subst hx
  exact ⟨1, x0_mem_degree_one K⟩

theorem x1Ideal_isHomogeneous :
    (x1Ideal K).IsHomogeneous (grading K) := by
  apply Ideal.homogeneous_span
  intro x hx
  simp only [Set.mem_singleton_iff] at hx
  subst hx
  exact ⟨1, x1_mem_degree_one K⟩

/-- The homogeneous ideal `(X₀)` in the standard graded ring `K[X₀,X₁]`. -/
def x0HomogeneousIdeal : HomogeneousIdeal (grading K) :=
  ⟨x0Ideal K, x0Ideal_isHomogeneous K⟩

/-- The homogeneous ideal `(X₁)` in the standard graded ring `K[X₀,X₁]`. -/
def x1HomogeneousIdeal : HomogeneousIdeal (grading K) :=
  ⟨x1Ideal K, x1Ideal_isHomogeneous K⟩

theorem x0_mem_irrelevant :
    X0 K ∈ HomogeneousIdeal.irrelevant (grading K) := by
  rw [HomogeneousIdeal.mem_irrelevant_iff]
  rw [GradedRing.proj_apply]
  simpa using
    DirectSum.decompose_of_mem_ne (grading K) (x0_mem_degree_one K)
      (by decide : (1 : ℕ) ≠ 0)

theorem x1_mem_irrelevant :
    X1 K ∈ HomogeneousIdeal.irrelevant (grading K) := by
  rw [HomogeneousIdeal.mem_irrelevant_iff]
  rw [GradedRing.proj_apply]
  simpa using
    DirectSum.decompose_of_mem_ne (grading K) (x1_mem_degree_one K)
      (by decide : (1 : ℕ) ≠ 0)

section Nontrivial

variable [Nontrivial K]

theorem x1_not_mem_x0Ideal :
    X1 K ∉ x0Ideal K := by
  rw [x0Ideal]
  rw [show ({X0 K} : Set (CoordinateRing K)) =
      (MvPolynomial.X '' ({0} : Set (Fin 2)) : Set (CoordinateRing K)) by
    ext q
    simp [X0]]
  rw [MvPolynomial.mem_ideal_span_X_image]
  push_neg
  refine ⟨Finsupp.single (1 : Fin 2) 1, ?_, ?_⟩
  · simp [X1, MvPolynomial.support_X]
  · intro i hi
    simp only [Set.mem_singleton_iff] at hi
    subst hi
    simp

theorem x0_not_mem_x1Ideal :
    X0 K ∉ x1Ideal K := by
  rw [x1Ideal]
  rw [show ({X1 K} : Set (CoordinateRing K)) =
      (MvPolynomial.X '' ({1} : Set (Fin 2)) : Set (CoordinateRing K)) by
    ext q
    simp [X1]]
  rw [MvPolynomial.mem_ideal_span_X_image]
  push_neg
  refine ⟨Finsupp.single (0 : Fin 2) 1, ?_, ?_⟩
  · simp [X0, MvPolynomial.support_X]
  · intro i hi
    simp only [Set.mem_singleton_iff] at hi
    subst hi
    simp

theorem not_irrelevant_le_x0HomogeneousIdeal :
    ¬ HomogeneousIdeal.irrelevant (grading K) ≤ x0HomogeneousIdeal K := by
  intro hle
  exact x1_not_mem_x0Ideal K (hle (x1_mem_irrelevant K))

theorem not_irrelevant_le_x1HomogeneousIdeal :
    ¬ HomogeneousIdeal.irrelevant (grading K) ≤ x1HomogeneousIdeal K := by
  intro hle
  exact x0_not_mem_x1Ideal K (hle (x0_mem_irrelevant K))

end Nontrivial

end
end SchemeProjectiveLine
end SourceStack
end HilbertTest
