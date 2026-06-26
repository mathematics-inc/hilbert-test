import HilbertTest.SourceStack.P1SchemePointBridge

/-!
Concrete affine points on the scheme-theoretic projective line.

`SchemeProjectiveLine` constructs the marked points `0`, `1`, and `infinity`
on `Proj K[X0,X1]`.  This file adds the full affine family `[r:1]`, defined by
the homogeneous ideal `(X0 - r * X1)`, proves its basic chart and injectivity
properties over a field, and uses it to build the concrete bridge from the
linear projective-line model to the scheme carrier.
-/

noncomputable section

namespace HilbertTest
namespace SourceStack
namespace SchemeAffineLinePoints

open AlgebraicGeometry
open HomogeneousLocalization
open MarkedProjectiveLine
open P1SchemePointBridge
open SchemeProjectiveLine

universe u

variable (K : Type u) [CommRing K]

/-- The homogeneous linear form cutting out the affine point `[r:1]`. -/
def affinePointCoordinate (r : K) : CoordinateRing K :=
  X0 K - MvPolynomial.C r * X1 K

/-- The homogeneous ideal `(X0 - r * X1)` cutting out `[r:1]`. -/
def affinePointIdeal (r : K) : Ideal (CoordinateRing K) :=
  Ideal.span ({affinePointCoordinate K r} : Set (CoordinateRing K))

theorem C_mem_degree_zero (r : K) :
    (MvPolynomial.C r : CoordinateRing K) ∈ grading K 0 := by
  rw [MvPolynomial.mem_homogeneousSubmodule]
  exact MvPolynomial.isHomogeneous_C (Fin 2) r

theorem C_mul_x1_mem_degree_one (r : K) :
    (MvPolynomial.C r : CoordinateRing K) * X1 K ∈ grading K 1 := by
  simpa using
    (SetLike.mul_mem_graded (C_mem_degree_zero K r) (x1_mem_degree_one K) :
      (MvPolynomial.C r : CoordinateRing K) * X1 K ∈ grading K (0 + 1))

theorem affinePointCoordinate_mem_degree_one (r : K) :
    affinePointCoordinate K r ∈ grading K 1 :=
  sub_mem (x0_mem_degree_one K) (C_mul_x1_mem_degree_one K r)

theorem affinePointIdeal_isHomogeneous (r : K) :
    (affinePointIdeal K r).IsHomogeneous (grading K) := by
  apply Ideal.homogeneous_span
  intro x hx
  simp only [Set.mem_singleton_iff] at hx
  subst hx
  exact ⟨1, affinePointCoordinate_mem_degree_one K r⟩

/-- The homogeneous ideal of the affine point `[r:1]`. -/
def affinePointHomogeneousIdeal (r : K) : HomogeneousIdeal (grading K) :=
  ⟨affinePointIdeal K r, affinePointIdeal_isHomogeneous K r⟩

/-- The principal polynomial corresponding to `X0 - r * X1` on the `X1 != 0`
affine chart after the existing coordinate equivalence. -/
def affinePointPolynomialTarget (r : K) :
    Polynomial (MvPolynomial (Fin 1) K) :=
  Polynomial.X - Polynomial.C (MvPolynomial.C r * MvPolynomial.X (0 : Fin 1))

theorem x0PolynomialEquiv_C (r : K) :
    x0PolynomialEquiv K (MvPolynomial.C r : CoordinateRing K) =
      Polynomial.C (MvPolynomial.C r : MvPolynomial (Fin 1) K) := by
  change (x0PolynomialEquiv K) (algebraMap K (CoordinateRing K) r) =
    algebraMap K (Polynomial (MvPolynomial (Fin 1) K)) r
  exact AlgEquiv.commutes (x0PolynomialEquiv K) r

theorem x0PolynomialEquiv_affinePointCoordinate (r : K) :
    x0PolynomialEquiv K (affinePointCoordinate K r) =
      affinePointPolynomialTarget K r := by
  rw [affinePointCoordinate, affinePointPolynomialTarget]
  rw [map_sub, map_mul, x0PolynomialEquiv_X0, x0PolynomialEquiv_X1,
    x0PolynomialEquiv_C]
  simp

theorem affinePointIdeal_eq_comap_span (r : K) :
    affinePointIdeal K r =
      Ideal.comap
        (MvPolynomial.finSuccEquiv K 1 : CoordinateRing K →+*
          Polynomial (MvPolynomial (Fin 1) K))
        (Ideal.span ({affinePointPolynomialTarget K r} :
          Set (Polynomial (MvPolynomial (Fin 1) K)))) := by
  have himage :
      Set.image
          (MvPolynomial.finSuccEquiv K 1 : CoordinateRing K →+*
            Polynomial (MvPolynomial (Fin 1) K))
          ({affinePointCoordinate K r} : Set (CoordinateRing K)) =
        ({affinePointPolynomialTarget K r} :
          Set (Polynomial (MvPolynomial (Fin 1) K))) := by
    ext p
    simp [x0PolynomialEquiv_affinePointCoordinate]
  have hmap :
      Ideal.map
          (MvPolynomial.finSuccEquiv K 1 : CoordinateRing K →+*
            Polynomial (MvPolynomial (Fin 1) K))
          (affinePointIdeal K r) =
        Ideal.span ({affinePointPolynomialTarget K r} :
          Set (Polynomial (MvPolynomial (Fin 1) K))) := by
    rw [affinePointIdeal, Ideal.map_span, himage]
  rw [← hmap]
  exact (Ideal.comap_map_of_bijective
    (MvPolynomial.finSuccEquiv K 1 : CoordinateRing K →+*
      Polynomial (MvPolynomial (Fin 1) K))
    (MvPolynomial.finSuccEquiv K 1).bijective).symm

section Nontrivial

variable [Nontrivial K]

theorem x1_not_mem_affinePointIdeal (r : K) :
    X1 K ∉ affinePointIdeal K r := by
  intro hx
  have hxcomap :
      X1 K ∈ Ideal.comap
        (MvPolynomial.finSuccEquiv K 1 : CoordinateRing K →+*
          Polynomial (MvPolynomial (Fin 1) K))
        (Ideal.span ({affinePointPolynomialTarget K r} :
          Set (Polynomial (MvPolynomial (Fin 1) K)))) := by
    simpa [affinePointIdeal_eq_comap_span K r] using hx
  have hxspan :
      (MvPolynomial.finSuccEquiv K 1) (X1 K) ∈
        Ideal.span ({affinePointPolynomialTarget K r} :
          Set (Polynomial (MvPolynomial (Fin 1) K))) := hxcomap
  rcases (Ideal.mem_span_singleton'.mp hxspan) with ⟨q, hq⟩
  let a : MvPolynomial (Fin 1) K :=
    MvPolynomial.C r * MvPolynomial.X (0 : Fin 1)
  have heval_zero :
      Polynomial.aeval a ((MvPolynomial.finSuccEquiv K 1) (X1 K)) = 0 := by
    rw [← hq, map_mul]
    have htarget_eval :
        Polynomial.aeval a (affinePointPolynomialTarget K r) = 0 := by
      simp [affinePointPolynomialTarget, a]
    rw [htarget_eval]
    simp
  have heval_x1 :
      Polynomial.aeval a ((MvPolynomial.finSuccEquiv K 1) (X1 K)) =
        MvPolynomial.X (0 : Fin 1) := by
    rw [x0PolynomialEquiv_X1]
    simp
  exact MvPolynomial.X_ne_zero (0 : Fin 1) (heval_x1 ▸ heval_zero)

theorem not_irrelevant_le_affinePointHomogeneousIdeal (r : K) :
    ¬ HomogeneousIdeal.irrelevant (grading K) ≤ affinePointHomogeneousIdeal K r := by
  intro hle
  exact x1_not_mem_affinePointIdeal K r (hle (x1_mem_irrelevant K))

end Nontrivial

section Domain

variable [IsDomain K]

theorem polynomial_span_affinePointTarget_isPrime (r : K) :
    (Ideal.span ({affinePointPolynomialTarget K r} :
      Set (Polynomial (MvPolynomial (Fin 1) K)))).IsPrime := by
  have hprime :
      Prime (affinePointPolynomialTarget K r) :=
    Polynomial.prime_X_sub_C
      (MvPolynomial.C r * MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) K)
  exact (Ideal.span_singleton_prime hprime.ne_zero).2 hprime

theorem affinePointIdeal_isPrime (r : K) :
    (affinePointIdeal K r).IsPrime := by
  rw [affinePointIdeal_eq_comap_span K r]
  haveI :
      (Ideal.span ({affinePointPolynomialTarget K r} :
        Set (Polynomial (MvPolynomial (Fin 1) K)))).IsPrime :=
    polynomial_span_affinePointTarget_isPrime K r
  exact Ideal.comap_isPrime
    (MvPolynomial.finSuccEquiv K 1 : CoordinateRing K →+*
      Polynomial (MvPolynomial (Fin 1) K))
    (Ideal.span ({affinePointPolynomialTarget K r} :
      Set (Polynomial (MvPolynomial (Fin 1) K))))

/-- The scheme-theoretic affine point `[r:1]` of `Proj K[X0,X1]`. -/
def affinePoint (r : K) : _root_.ProjectiveSpectrum (grading K) where
  asHomogeneousIdeal := affinePointHomogeneousIdeal K r
  isPrime := affinePointIdeal_isPrime K r
  not_irrelevant_le := not_irrelevant_le_affinePointHomogeneousIdeal K r

theorem affinePoint_asHomogeneousIdeal (r : K) :
    (affinePoint K r).asHomogeneousIdeal = affinePointHomogeneousIdeal K r := rfl

omit [IsDomain K] in
theorem affinePointIdeal_zero :
    affinePointIdeal K 0 = x0Ideal K := by
  rw [affinePointIdeal, x0Ideal]
  congr
  ext q
  simp [affinePointCoordinate]

omit [IsDomain K] in
theorem affinePointHomogeneousIdeal_zero :
    affinePointHomogeneousIdeal K 0 = x0HomogeneousIdeal K :=
  HomogeneousIdeal.ext (affinePointIdeal_zero K)

theorem affinePoint_zero :
    affinePoint K 0 = zeroPoint K := by
  exact ProjectiveSpectrum.ext (affinePointHomogeneousIdeal_zero K)

omit [IsDomain K] in
theorem affinePointIdeal_one :
    affinePointIdeal K 1 = x0SubX1Ideal K := by
  rw [affinePointIdeal, x0SubX1Ideal]
  congr
  ext q
  simp [affinePointCoordinate, X0SubX1]

omit [IsDomain K] in
theorem affinePointHomogeneousIdeal_one :
    affinePointHomogeneousIdeal K 1 = x0SubX1HomogeneousIdeal K :=
  HomogeneousIdeal.ext (affinePointIdeal_one K)

theorem affinePoint_one :
    affinePoint K 1 = onePoint K := by
  exact ProjectiveSpectrum.ext (affinePointHomogeneousIdeal_one K)

theorem affinePoint_mem_x1_basicOpen (r : K) :
    affinePoint K r ∈ Proj.basicOpen (grading K) (X1 K) := by
  rw [ProjectiveSpectrum.basicOpen_mem_iff]
  exact x1_not_mem_affinePointIdeal K r

theorem affinePoint_ne_infinity (r : K) :
    affinePoint K r ≠ infinityPoint K := by
  intro h
  have hI : affinePointHomogeneousIdeal K r = x1HomogeneousIdeal K := by
    simpa [affinePoint_asHomogeneousIdeal, infinityPoint_asHomogeneousIdeal] using
      congrArg _root_.ProjectiveSpectrum.asHomogeneousIdeal h
  have hx1 : X1 K ∈ affinePointIdeal K r := by
    change X1 K ∈ (affinePointHomogeneousIdeal K r).toIdeal
    rw [hI]
    change X1 K ∈ x1Ideal K
    exact Ideal.mem_span_singleton_self (X1 K)
  exact x1_not_mem_affinePointIdeal K r hx1

omit [IsDomain K] in
theorem eval_affinePointPolynomialTarget (r s : K) :
    Polynomial.aeval (MvPolynomial.C r * MvPolynomial.X (0 : Fin 1))
        (affinePointPolynomialTarget K s) =
      MvPolynomial.C (r - s) * MvPolynomial.X (0 : Fin 1) := by
  simp [affinePointPolynomialTarget, sub_mul]

theorem C_sub_mul_X_ne_zero {r s : K} (h : r ≠ s) :
    MvPolynomial.C (r - s) * MvPolynomial.X (0 : Fin 1) ≠ 0 := by
  exact mul_ne_zero
    (MvPolynomial.C_ne_zero.mpr (sub_ne_zero.mpr h))
    (MvPolynomial.X_ne_zero (0 : Fin 1))

theorem affinePoint_injective :
    Function.Injective (affinePoint K) := by
  intro r s hrs
  by_contra hrs_ne
  have hI : affinePointHomogeneousIdeal K r = affinePointHomogeneousIdeal K s := by
    simpa [affinePoint_asHomogeneousIdeal] using
      congrArg _root_.ProjectiveSpectrum.asHomogeneousIdeal hrs
  have hs_mem : affinePointCoordinate K s ∈ affinePointIdeal K r := by
    change affinePointCoordinate K s ∈ (affinePointHomogeneousIdeal K r).toIdeal
    rw [hI]
    exact Ideal.mem_span_singleton_self (affinePointCoordinate K s)
  have hscomap :
      affinePointCoordinate K s ∈ Ideal.comap
        (MvPolynomial.finSuccEquiv K 1 : CoordinateRing K →+*
          Polynomial (MvPolynomial (Fin 1) K))
        (Ideal.span ({affinePointPolynomialTarget K r} :
          Set (Polynomial (MvPolynomial (Fin 1) K)))) := by
    simpa [affinePointIdeal_eq_comap_span K r] using hs_mem
  have hsspan :
      (MvPolynomial.finSuccEquiv K 1) (affinePointCoordinate K s) ∈
        Ideal.span ({affinePointPolynomialTarget K r} :
          Set (Polynomial (MvPolynomial (Fin 1) K))) := hscomap
  rcases (Ideal.mem_span_singleton'.mp hsspan) with ⟨q, hq⟩
  let a : MvPolynomial (Fin 1) K :=
    MvPolynomial.C r * MvPolynomial.X (0 : Fin 1)
  have heval_zero :
      Polynomial.aeval a
          ((MvPolynomial.finSuccEquiv K 1) (affinePointCoordinate K s)) = 0 := by
    rw [← hq, map_mul]
    have htarget_eval :
        Polynomial.aeval a (affinePointPolynomialTarget K r) = 0 := by
      simp [affinePointPolynomialTarget, a]
    rw [htarget_eval]
    simp
  have heval_target :
      Polynomial.aeval a
          ((MvPolynomial.finSuccEquiv K 1) (affinePointCoordinate K s)) =
        MvPolynomial.C (r - s) * MvPolynomial.X (0 : Fin 1) := by
    rw [x0PolynomialEquiv_affinePointCoordinate]
    exact eval_affinePointPolynomialTarget K r s
  exact C_sub_mul_X_ne_zero K hrs_ne (heval_target ▸ heval_zero)

theorem affinePoint_eq_iff (r s : K) :
    affinePoint K r = affinePoint K s ↔ r = s :=
  ⟨fun h => affinePoint_injective K h, fun h => by rw [h]⟩

theorem affinePoint_ne_zero {r : K} (hr : r ≠ 0) :
    affinePoint K r ≠ zeroPoint K := by
  intro h
  exact hr ((affinePoint_eq_iff K r 0).1 (by simpa [affinePoint_zero K] using h))

theorem affinePoint_ne_one {r : K} (hr : r ≠ 1) :
    affinePoint K r ≠ onePoint K := by
  intro h
  exact hr ((affinePoint_eq_iff K r 1).1 (by simpa [affinePoint_one K] using h))

theorem affinePoint_mem_markedSchemePointSet_iff (r : K) :
    affinePoint K r ∈ markedSchemePointSet K ↔ r = 0 ∨ r = 1 := by
  constructor
  · intro h
    change affinePoint K r ∈ markedPointFinset K at h
    simp [markedPointFinset, affinePoint_ne_infinity K r] at h
    rcases h with h0 | h1
    · left
      exact (affinePoint_eq_iff K r 0).1 (by simpa [affinePoint_zero K] using h0)
    · right
      exact (affinePoint_eq_iff K r 1).1 (by simpa [affinePoint_one K] using h1)
  · intro h
    change affinePoint K r ∈ markedPointFinset K
    rcases h with rfl | rfl
    · simpa [affinePoint_zero K] using zeroPoint_mem_markedPointFinset K
    · simpa [affinePoint_one K] using onePoint_mem_markedPointFinset K

theorem affinePoint_not_mem_markedSchemePointSet_of_ne_zero_one
    {r : K} (h0 : r ≠ 0) (h1 : r ≠ 1) :
    affinePoint K r ∉ markedSchemePointSet K := by
  intro h
  rcases (affinePoint_mem_markedSchemePointSet_iff K r).1 h with hr | hr
  · exact h0 hr
  · exact h1 hr

end Domain

section LinearBridge

variable (F : Type u) [Field F]

/-- Concrete map from the linear projective-line point model to the scheme
carrier of `Proj K[X0,X1]`. -/
def linearToSchemePoint (p : ProjectiveLine.P1 F) : SchemeProjectiveLine.P1 F := by
  classical
  exact
    if h : ∃ r : F, p = ProjectiveLine.affinePoint F r then
      affinePoint F (Classical.choose h)
    else
      infinityPoint F

theorem linearToSchemePoint_affinePoint (r : F) :
    linearToSchemePoint F (ProjectiveLine.affinePoint F r) = affinePoint F r := by
  unfold linearToSchemePoint
  rw [dif_pos ⟨r, rfl⟩]
  have hchoose :
      Classical.choose
          (⟨r, rfl⟩ :
            ∃ s : F, ProjectiveLine.affinePoint F r = ProjectiveLine.affinePoint F s) = r := by
    exact (ProjectiveLine.affinePoint_injective F
      (Classical.choose_spec
        (⟨r, rfl⟩ :
          ∃ s : F, ProjectiveLine.affinePoint F r =
            ProjectiveLine.affinePoint F s))).symm
  rw [hchoose]

theorem not_exists_affinePoint_eq_infinity :
    ¬ ∃ r : F, ProjectiveLine.infinity F = ProjectiveLine.affinePoint F r := by
  rintro ⟨r, hr⟩
  exact ProjectiveLine.affinePoint_ne_infinity F r hr.symm

theorem linearToSchemePoint_infinity :
    linearToSchemePoint F (ProjectiveLine.infinity F) = infinityPoint F := by
  unfold linearToSchemePoint
  rw [dif_neg (not_exists_affinePoint_eq_infinity F)]

theorem linearToSchemePoint_injective :
    Function.Injective (linearToSchemePoint F) := by
  intro p q hpq
  rcases ProjectiveLine.point_eq_affine_or_infinity F p with ⟨r, rfl⟩ | rfl
  · rcases ProjectiveLine.point_eq_affine_or_infinity F q with ⟨s, rfl⟩ | rfl
    · rw [linearToSchemePoint_affinePoint, linearToSchemePoint_affinePoint] at hpq
      exact congrArg (ProjectiveLine.affinePoint F)
        ((affinePoint_eq_iff F r s).1 hpq)
    · rw [linearToSchemePoint_affinePoint, linearToSchemePoint_infinity] at hpq
      exact False.elim ((affinePoint_ne_infinity F r) hpq)
  · rcases ProjectiveLine.point_eq_affine_or_infinity F q with ⟨s, rfl⟩ | rfl
    · rw [linearToSchemePoint_infinity, linearToSchemePoint_affinePoint] at hpq
      exact False.elim ((affinePoint_ne_infinity F s) hpq.symm)
    · rfl

theorem linearToSchemePoint_zero :
    linearToSchemePoint F (ProjectiveLine.zero F) = zeroPoint F := by
  rw [← ProjectiveLine.affinePoint_zero F, linearToSchemePoint_affinePoint,
    affinePoint_zero]

theorem linearToSchemePoint_one :
    linearToSchemePoint F (ProjectiveLine.one F) = onePoint F := by
  rw [← ProjectiveLine.affinePoint_one F, linearToSchemePoint_affinePoint,
    affinePoint_one]

theorem linearToSchemePoint_linearPoint (label : MarkedPointLabel) :
    linearToSchemePoint F (linearPoint F label) = schemeCarrierPoint F label := by
  cases label
  · exact linearToSchemePoint_zero F
  · exact linearToSchemePoint_one F
  · exact linearToSchemePoint_infinity F

/-- Concrete bridge from the linear `P1` point model to the scheme carrier. -/
def concreteLinearSchemePointBridge : LinearSchemePointBridge F where
  toScheme := linearToSchemePoint F
  injective := linearToSchemePoint_injective F
  maps_label := linearToSchemePoint_linearPoint F

end LinearBridge

end SchemeAffineLinePoints
end SourceStack
end HilbertTest
