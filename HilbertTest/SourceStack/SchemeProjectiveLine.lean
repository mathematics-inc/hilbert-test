import HilbertTest.SourceStack.ProjectiveSpectrum
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Logic.Equiv.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Polynomial.Basic

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

/-- The two standard affine charts of the scheme-theoretic projective line. -/
inductive StandardAffineChart where
  | x0
  | x1
  deriving DecidableEq, Inhabited

/-- The coordinate ring of a standard affine chart of `P1`. -/
abbrev standardChartRing (K : Type u) [CommRing K] :
    StandardAffineChart → Type u
  | StandardAffineChart.x0 => Away (grading K) (X0 K)
  | StandardAffineChart.x1 => Away (grading K) (X1 K)

instance standardChartRingCommRing (c : StandardAffineChart) :
    CommRing (standardChartRing K c) := by
  cases c <;> infer_instance

/-- The affine scheme underlying a standard chart of `P1`. -/
abbrev standardChartScheme (K : Type u) [CommRing K]
    (c : StandardAffineChart) : Scheme.{u} :=
  Spec (CommRingCat.of (standardChartRing K c))

/-- The standard chart open in `P1`. -/
def standardChartOpen : StandardAffineChart → (P1 K).Opens
  | StandardAffineChart.x0 => Proj.basicOpen (grading K) (X0 K)
  | StandardAffineChart.x1 => Proj.basicOpen (grading K) (X1 K)

/-- The open immersion from a standard affine chart into `P1`. -/
def standardChartMap (c : StandardAffineChart) :
    standardChartScheme K c ⟶ P1 K :=
  match c with
  | StandardAffineChart.x0 =>
      Proj.awayι (grading K) (X0 K) (x0_mem_degree_one K) Nat.zero_lt_one
  | StandardAffineChart.x1 =>
      Proj.awayι (grading K) (X1 K) (x1_mem_degree_one K) Nat.zero_lt_one

instance standardChartMap_isOpenImmersion (c : StandardAffineChart) :
    IsOpenImmersion (standardChartMap K c) := by
  cases c
  · exact x0_chart_isOpenImmersion K
  · exact x1_chart_isOpenImmersion K

theorem standardChartMap_opensRange (c : StandardAffineChart) :
    (standardChartMap K c).opensRange = standardChartOpen K c := by
  cases c
  · exact x0_chart_range K
  · exact x1_chart_range K

theorem standardChartOpen_isAffineOpen (c : StandardAffineChart) :
    IsAffineOpen (standardChartOpen K c) := by
  cases c
  · exact x0_basicOpen_isAffineOpen K
  · exact x1_basicOpen_isAffineOpen K

/-- The affine coordinate on a standard chart: `X₁/X₀` on the `X₀ ≠ 0`
chart, and `X₀/X₁` on the `X₁ ≠ 0` chart. -/
def standardChartCoordinate : (c : StandardAffineChart) → standardChartRing K c
  | StandardAffineChart.x0 =>
      Away.mk (grading K) (x0_mem_degree_one K) 1 (X1 K)
        (by simpa using x1_mem_degree_one K)
  | StandardAffineChart.x1 =>
      Away.mk (grading K) (x1_mem_degree_one K) 1 (X0 K)
        (by simpa using x0_mem_degree_one K)

@[simp]
theorem standardChartCoordinate_x0 :
    standardChartCoordinate K StandardAffineChart.x0 =
      Away.mk (grading K) (x0_mem_degree_one K) 1 (X1 K)
        (by simpa using x1_mem_degree_one K) := rfl

@[simp]
theorem standardChartCoordinate_x1 :
    standardChartCoordinate K StandardAffineChart.x1 =
      Away.mk (grading K) (x1_mem_degree_one K) 1 (X0 K)
        (by simpa using x0_mem_degree_one K) := rfl

/-- A ring map from the coordinate ring of a standard chart to global sections
of a scheme gives a morphism into that standard chart by the `Γ-Spec`
adjunction. -/
def standardChartHomOfRingHom {X : Scheme.{u}} {c : StandardAffineChart}
    (φ : CommRingCat.of (standardChartRing K c) ⟶ Γ(X, ⊤)) :
    X ⟶ standardChartScheme K c :=
  X.toSpecΓ ≫ Spec.map φ

/-- Composing a `Γ-Spec` chart morphism with the standard chart open immersion
gives a morphism to `P1`. -/
def standardChartToP1HomOfRingHom {X : Scheme.{u}} {c : StandardAffineChart}
    (φ : CommRingCat.of (standardChartRing K c) ⟶ Γ(X, ⊤)) :
    X ⟶ P1 K :=
  standardChartHomOfRingHom K φ ≫ standardChartMap K c

theorem standardChartToP1HomOfRingHom_def
    {X : Scheme.{u}} {c : StandardAffineChart}
    (φ : CommRingCat.of (standardChartRing K c) ⟶ Γ(X, ⊤)) :
    standardChartToP1HomOfRingHom K φ =
      standardChartHomOfRingHom K φ ≫ standardChartMap K c := rfl

/-- The regular function on `X` obtained by pulling back the distinguished
affine coordinate of a standard chart.  In the line-bundle construction this is
the local section ratio `s1/s0` on the `X0 ≠ 0` chart and `s0/s1` on the
`X1 ≠ 0` chart. -/
def standardChartCoordinateSection {X : Scheme.{u}} {c : StandardAffineChart}
    (φ : CommRingCat.of (standardChartRing K c) ⟶ Γ(X, ⊤)) :
    Γ(X, ⊤) :=
  φ (standardChartCoordinate K c)

@[simp]
theorem standardChartCoordinateSection_apply
    {X : Scheme.{u}} {c : StandardAffineChart}
    (φ : CommRingCat.of (standardChartRing K c) ⟶ Γ(X, ⊤)) :
    standardChartCoordinateSection K φ = φ (standardChartCoordinate K c) := rfl

section ChartCoordinateRingMap

variable {R : Type u} [CommRing R] [Algebra K R]

/-- The polynomial-coordinate evaluation attached to a standard affine chart.
On the `X₀ ≠ 0` chart this sends `(X₀, X₁)` to `(1, t)`, and on the
`X₁ ≠ 0` chart it sends `(X₀, X₁)` to `(t, 1)`. -/
def standardChartCoordinateValue (c : StandardAffineChart) (t : R) : Fin 2 → R :=
  match c with
  | StandardAffineChart.x0 => fun i => if i = 0 then 1 else t
  | StandardAffineChart.x1 => fun i => if i = 0 then t else 1

@[simp]
theorem standardChartCoordinateValue_x0_zero (t : R) :
    standardChartCoordinateValue StandardAffineChart.x0 t 0 = 1 := by
  simp [standardChartCoordinateValue]

@[simp]
theorem standardChartCoordinateValue_x0_one (t : R) :
    standardChartCoordinateValue StandardAffineChart.x0 t 1 = t := by
  simp [standardChartCoordinateValue]

@[simp]
theorem standardChartCoordinateValue_x1_zero (t : R) :
    standardChartCoordinateValue StandardAffineChart.x1 t 0 = t := by
  simp [standardChartCoordinateValue]

@[simp]
theorem standardChartCoordinateValue_x1_one (t : R) :
    standardChartCoordinateValue StandardAffineChart.x1 t 1 = 1 := by
  simp [standardChartCoordinateValue]

/-- The homogeneous-coordinate polynomial evaluation defining a standard affine
chart from an affine coordinate value. -/
def standardChartPolynomialEval (c : StandardAffineChart) (t : R) :
    CoordinateRing K →ₐ[K] R :=
  MvPolynomial.aeval (standardChartCoordinateValue c t)

@[simp]
theorem standardChartPolynomialEval_x0_X0 (t : R) :
    standardChartPolynomialEval K StandardAffineChart.x0 t (X0 K) = 1 := by
  simp [standardChartPolynomialEval, X0]

@[simp]
theorem standardChartPolynomialEval_x0_X1 (t : R) :
    standardChartPolynomialEval K StandardAffineChart.x0 t (X1 K) = t := by
  simp [standardChartPolynomialEval, X1]

@[simp]
theorem standardChartPolynomialEval_x1_X0 (t : R) :
    standardChartPolynomialEval K StandardAffineChart.x1 t (X0 K) = t := by
  simp [standardChartPolynomialEval, X0]

@[simp]
theorem standardChartPolynomialEval_x1_X1 (t : R) :
    standardChartPolynomialEval K StandardAffineChart.x1 t (X1 K) = 1 := by
  simp [standardChartPolynomialEval, X1]

/-- The homogeneous denominator inverted by a standard affine chart. -/
def standardChartDenominator : StandardAffineChart → CoordinateRing K
  | StandardAffineChart.x0 => X0 K
  | StandardAffineChart.x1 => X1 K

/-- The numerator of the affine coordinate on a standard affine chart. -/
def standardChartNumerator : StandardAffineChart → CoordinateRing K
  | StandardAffineChart.x0 => X1 K
  | StandardAffineChart.x1 => X0 K

@[simp]
theorem standardChartDenominator_x0 :
    standardChartDenominator K StandardAffineChart.x0 = X0 K := rfl

@[simp]
theorem standardChartDenominator_x1 :
    standardChartDenominator K StandardAffineChart.x1 = X1 K := rfl

@[simp]
theorem standardChartNumerator_x0 :
    standardChartNumerator K StandardAffineChart.x0 = X1 K := rfl

@[simp]
theorem standardChartNumerator_x1 :
    standardChartNumerator K StandardAffineChart.x1 = X0 K := rfl

/-- The polynomial evaluation sends the chart denominator to a unit. -/
theorem standardChartPolynomialEval_denominator_isUnit
    (c : StandardAffineChart) (t : R) :
    IsUnit (standardChartPolynomialEval K c t (standardChartDenominator K c)) := by
  cases c <;> simp [standardChartDenominator]

/-- The polynomial evaluation sends the chart numerator to the chosen affine
coordinate value. -/
theorem standardChartPolynomialEval_numerator
    (c : StandardAffineChart) (t : R) :
    standardChartPolynomialEval K c t (standardChartNumerator K c) = t := by
  cases c <;> simp [standardChartNumerator]

/-- The full localization map induced by the chart-coordinate polynomial
evaluation. -/
noncomputable def standardChartFullLocalizationRingHom
    (c : StandardAffineChart) (t : R) :
    Localization.Away (standardChartDenominator K c) →+* R :=
  IsLocalization.lift
    (M := Submonoid.powers (standardChartDenominator K c))
    (S := Localization.Away (standardChartDenominator K c))
    (g := (standardChartPolynomialEval K c t).toRingHom)
    (by
      intro y
      rcases y with ⟨y, n, rfl⟩
      simpa using (standardChartPolynomialEval_denominator_isUnit K c t).pow n)

/-- A standard affine coordinate value determines a map out of the
scheme-theoretic standard chart ring. -/
noncomputable def standardChartRingHomOfCoordinate
    (c : StandardAffineChart) (t : R) :
    standardChartRing K c →+* R :=
  match c with
  | StandardAffineChart.x0 =>
      (standardChartFullLocalizationRingHom K StandardAffineChart.x0 t).comp
        (algebraMap (standardChartRing K StandardAffineChart.x0) (Localization.Away (X0 K)))
  | StandardAffineChart.x1 =>
      (standardChartFullLocalizationRingHom K StandardAffineChart.x1 t).comp
        (algebraMap (standardChartRing K StandardAffineChart.x1) (Localization.Away (X1 K)))

/-- Categorical form of `standardChartRingHomOfCoordinate`. -/
noncomputable def standardChartRingCatHomOfCoordinate
    (c : StandardAffineChart) (t : R) :
    CommRingCat.of (standardChartRing K c) ⟶ CommRingCat.of R :=
  CommRingCat.ofHom (standardChartRingHomOfCoordinate K c t)

/-- Categorical chart-ring map from an affine coordinate value, taking the
target `K`-algebra structure as explicit data.  This is convenient for local
section rings whose algebra structures depend on an open-cover index. -/
noncomputable def standardChartRingCatHomOfCoordinateOfAlgebra
    {R : Type u} [CommRing R] (c : StandardAffineChart)
    (hAlg : Algebra K R) (t : R) :
    CommRingCat.of (standardChartRing K c) ⟶ CommRingCat.of R := by
  letI : Algebra K R := hAlg
  exact standardChartRingCatHomOfCoordinate K c t

/-- The chart ring map constructed from an affine coordinate value pulls back
the distinguished chart coordinate to that value. -/
theorem standardChartRingHomOfCoordinate_coordinate
    (c : StandardAffineChart) (t : R) :
    standardChartRingHomOfCoordinate K c t (standardChartCoordinate K c) = t := by
  cases c
  · change standardChartFullLocalizationRingHom K StandardAffineChart.x0 t
        (algebraMap (standardChartRing K StandardAffineChart.x0)
          (Localization.Away (X0 K))
          (Away.mk (grading K) (x0_mem_degree_one K) 1 (X1 K)
            (by simpa using x1_mem_degree_one K))) = t
    rw [HomogeneousLocalization.algebraMap_apply,
      HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
    dsimp [standardChartFullLocalizationRingHom]
    rw [IsLocalization.lift_mk'_spec]
    simp [standardChartFullLocalizationRingHom, standardChartDenominator,
      standardChartNumerator]
  · change standardChartFullLocalizationRingHom K StandardAffineChart.x1 t
        (algebraMap (standardChartRing K StandardAffineChart.x1)
          (Localization.Away (X1 K))
          (Away.mk (grading K) (x1_mem_degree_one K) 1 (X0 K)
            (by simpa using x0_mem_degree_one K))) = t
    rw [HomogeneousLocalization.algebraMap_apply,
      HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
    dsimp [standardChartFullLocalizationRingHom]
    rw [IsLocalization.lift_mk'_spec]
    simp [standardChartFullLocalizationRingHom, standardChartDenominator,
      standardChartNumerator]

/-- The explicit-algebra chart-ring map sends the distinguished coordinate to
the chosen affine coordinate value. -/
theorem standardChartRingCatHomOfCoordinateOfAlgebra_apply_coordinate
    {R : Type u} [CommRing R] (c : StandardAffineChart)
    (hAlg : Algebra K R) (t : R) :
    standardChartRingCatHomOfCoordinateOfAlgebra K c hAlg t
      (standardChartCoordinate K c) = t := by
  letI : Algebra K R := hAlg
  simpa [standardChartRingCatHomOfCoordinateOfAlgebra,
    standardChartRingCatHomOfCoordinate] using
    standardChartRingHomOfCoordinate_coordinate K c t

/-- Categorical version of the coordinate pullback identity. -/
theorem standardChartRingCatHomOfCoordinate_coordinate
    {X : Scheme.{u}} [Algebra K Γ(X, ⊤)] (c : StandardAffineChart) (t : Γ(X, ⊤)) :
    standardChartCoordinateSection K (standardChartRingCatHomOfCoordinate K c t) = t := by
  simpa [standardChartCoordinateSection, standardChartRingCatHomOfCoordinate] using
    standardChartRingHomOfCoordinate_coordinate K c t

end ChartCoordinateRingMap

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

/-- The homogeneous coordinate cutting out the point `[1:1]`. -/
abbrev X0SubX1 : CoordinateRing K :=
  X0 K - X1 K

/-- The ideal generated by `X₀ - X₁`. -/
abbrev x0SubX1Ideal : Ideal (CoordinateRing K) :=
  Ideal.span ({X0SubX1 K} : Set (CoordinateRing K))

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

theorem x0SubX1_mem_degree_one :
    X0SubX1 K ∈ grading K 1 := by
  exact sub_mem (x0_mem_degree_one K) (x1_mem_degree_one K)

theorem x0SubX1Ideal_isHomogeneous :
    (x0SubX1Ideal K).IsHomogeneous (grading K) := by
  apply Ideal.homogeneous_span
  intro x hx
  simp only [Set.mem_singleton_iff] at hx
  subst hx
  exact ⟨1, x0SubX1_mem_degree_one K⟩

/-- The homogeneous ideal `(X₀)` in the standard graded ring `K[X₀,X₁]`. -/
def x0HomogeneousIdeal : HomogeneousIdeal (grading K) :=
  ⟨x0Ideal K, x0Ideal_isHomogeneous K⟩

/-- The homogeneous ideal `(X₁)` in the standard graded ring `K[X₀,X₁]`. -/
def x1HomogeneousIdeal : HomogeneousIdeal (grading K) :=
  ⟨x1Ideal K, x1Ideal_isHomogeneous K⟩

/-- The homogeneous ideal `(X₀ - X₁)` in the standard graded ring `K[X₀,X₁]`. -/
def x0SubX1HomogeneousIdeal : HomogeneousIdeal (grading K) :=
  ⟨x0SubX1Ideal K, x0SubX1Ideal_isHomogeneous K⟩

/-- The coordinate order used by `MvPolynomial.finSuccEquiv`, sending `X₀` to the
polynomial variable. -/
abbrev x0PolynomialEquiv :
    CoordinateRing K ≃ₐ[K] Polynomial (MvPolynomial (Fin 1) K) :=
  MvPolynomial.finSuccEquiv K 1

/-- The principal target ideal generator corresponding to `X₀ - X₁` under
`finSuccEquiv`. -/
abbrev x0SubX1PolynomialTarget :
    Polynomial (MvPolynomial (Fin 1) K) :=
  Polynomial.X - Polynomial.C (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) K)

/-- The transposition of the two homogeneous coordinates. -/
abbrev coordinateSwap : Fin 2 ≃ Fin 2 :=
  Equiv.swap (0 : Fin 2) 1

/-- The coordinate order sending `X₁` to the polynomial variable. -/
abbrev x1PolynomialEquiv :
    CoordinateRing K ≃ₐ[K] Polynomial (MvPolynomial (Fin 1) K) :=
  (MvPolynomial.renameEquiv K coordinateSwap).trans (MvPolynomial.finSuccEquiv K 1)

theorem x0PolynomialEquiv_X0 :
    x0PolynomialEquiv K (X0 K) = Polynomial.X := by
  simp [x0PolynomialEquiv, X0, MvPolynomial.finSuccEquiv_X_zero]

theorem x0PolynomialEquiv_X1 :
    x0PolynomialEquiv K (X1 K) =
      Polynomial.C (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) K) := by
  change (MvPolynomial.finSuccEquiv K 1) (MvPolynomial.X (Fin.succ (0 : Fin 1))) =
    Polynomial.C (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) K)
  exact MvPolynomial.finSuccEquiv_X_succ

theorem x1PolynomialEquiv_X1 :
    x1PolynomialEquiv K (X1 K) = Polynomial.X := by
  simp [x1PolynomialEquiv, coordinateSwap, X1, MvPolynomial.finSuccEquiv_X_zero]

theorem x0PolynomialEquiv_X0SubX1 :
    x0PolynomialEquiv K (X0SubX1 K) = x0SubX1PolynomialTarget K := by
  rw [X0SubX1, map_sub, x0PolynomialEquiv_X0, x0PolynomialEquiv_X1]

theorem x0SubX1Ideal_eq_comap_span_X_sub_C_X :
    x0SubX1Ideal K =
      Ideal.comap
        (MvPolynomial.finSuccEquiv K 1 : CoordinateRing K →+*
          Polynomial (MvPolynomial (Fin 1) K))
        (Ideal.span ({x0SubX1PolynomialTarget K} :
          Set (Polynomial (MvPolynomial (Fin 1) K)))) := by
  have himage :
      Set.image
          (MvPolynomial.finSuccEquiv K 1 : CoordinateRing K →+*
            Polynomial (MvPolynomial (Fin 1) K))
          ({X0SubX1 K} : Set (CoordinateRing K)) =
        ({x0SubX1PolynomialTarget K} :
          Set (Polynomial (MvPolynomial (Fin 1) K))) := by
    ext p
    simp [x0PolynomialEquiv_X0SubX1]
  have hmap :
      Ideal.map
          (MvPolynomial.finSuccEquiv K 1 : CoordinateRing K →+*
            Polynomial (MvPolynomial (Fin 1) K))
          (x0SubX1Ideal K) =
        Ideal.span ({x0SubX1PolynomialTarget K} :
          Set (Polynomial (MvPolynomial (Fin 1) K))) := by
    rw [x0SubX1Ideal, Ideal.map_span, himage]
  rw [← hmap]
  exact (Ideal.comap_map_of_bijective
    (MvPolynomial.finSuccEquiv K 1 : CoordinateRing K →+*
      Polynomial (MvPolynomial (Fin 1) K))
    (MvPolynomial.finSuccEquiv K 1).bijective).symm

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

theorem x0_not_mem_x0SubX1Ideal :
    X0 K ∉ x0SubX1Ideal K := by
  intro hx
  have hxcomap :
      X0 K ∈ Ideal.comap
        (MvPolynomial.finSuccEquiv K 1 : CoordinateRing K →+*
          Polynomial (MvPolynomial (Fin 1) K))
        (Ideal.span ({x0SubX1PolynomialTarget K} :
          Set (Polynomial (MvPolynomial (Fin 1) K)))) := by
    simpa [x0SubX1Ideal_eq_comap_span_X_sub_C_X K] using hx
  have hxspan :
      (MvPolynomial.finSuccEquiv K 1) (X0 K) ∈
        Ideal.span ({x0SubX1PolynomialTarget K} :
          Set (Polynomial (MvPolynomial (Fin 1) K))) := hxcomap
  rcases (Ideal.mem_span_singleton'.mp hxspan) with ⟨q, hq⟩
  have heval_zero :
      Polynomial.aeval
          (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) K)
          ((MvPolynomial.finSuccEquiv K 1) (X0 K)) = 0 := by
    rw [← hq, map_mul]
    have htarget_eval :
        Polynomial.aeval
            (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) K)
            (x0SubX1PolynomialTarget K) = 0 := by
      simp [x0SubX1PolynomialTarget]
    rw [htarget_eval]
    simp
  have heval_x :
      Polynomial.aeval
          (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) K)
          ((MvPolynomial.finSuccEquiv K 1) (X0 K)) =
        (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) K) := by
    rw [x0PolynomialEquiv_X0]
    simp
  exact MvPolynomial.X_ne_zero (0 : Fin 1) (heval_x ▸ heval_zero)

theorem not_irrelevant_le_x0SubX1HomogeneousIdeal :
    ¬ HomogeneousIdeal.irrelevant (grading K) ≤ x0SubX1HomogeneousIdeal K := by
  intro hle
  exact x0_not_mem_x0SubX1Ideal K (hle (x0_mem_irrelevant K))

end Nontrivial

section Domain

variable [IsDomain K]

theorem polynomial_span_X_isPrime :
    (Ideal.span ({Polynomial.X} : Set (Polynomial (MvPolynomial (Fin 1) K)))).IsPrime := by
  let S := MvPolynomial (Fin 1) K
  have hXne : (Polynomial.X : Polynomial S) ≠ 0 := Polynomial.X_ne_zero
  have hXprime : Prime (Polynomial.X : Polynomial S) := Polynomial.prime_X
  exact (Ideal.span_singleton_prime hXne).2 hXprime

theorem polynomial_span_X_sub_C_X_isPrime :
    (Ideal.span ({x0SubX1PolynomialTarget K} :
      Set (Polynomial (MvPolynomial (Fin 1) K)))).IsPrime := by
  have hprime :
      Prime (x0SubX1PolynomialTarget K) :=
    Polynomial.prime_X_sub_C
      (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) K)
  exact (Ideal.span_singleton_prime hprime.ne_zero).2 hprime

omit [IsDomain K] in
theorem x0Ideal_eq_comap_span_X :
    x0Ideal K =
      Ideal.comap
        (MvPolynomial.finSuccEquiv K 1 : CoordinateRing K →+*
          Polynomial (MvPolynomial (Fin 1) K))
        (Ideal.span ({Polynomial.X} : Set (Polynomial (MvPolynomial (Fin 1) K)))) := by
  have hmap :
      Ideal.map
          (MvPolynomial.finSuccEquiv K 1 : CoordinateRing K →+*
            Polynomial (MvPolynomial (Fin 1) K))
          (x0Ideal K) =
        Ideal.span ({Polynomial.X} : Set (Polynomial (MvPolynomial (Fin 1) K))) := by
    rw [x0Ideal, Ideal.map_span]
    simp [X0, MvPolynomial.finSuccEquiv_X_zero]
  rw [← hmap]
  exact (Ideal.comap_map_of_bijective
    (MvPolynomial.finSuccEquiv K 1 : CoordinateRing K →+*
      Polynomial (MvPolynomial (Fin 1) K))
    (MvPolynomial.finSuccEquiv K 1).bijective).symm

omit [IsDomain K] in
theorem x1Ideal_eq_comap_span_X :
    x1Ideal K =
      Ideal.comap
        (x1PolynomialEquiv K : CoordinateRing K →+*
          Polynomial (MvPolynomial (Fin 1) K))
        (Ideal.span ({Polynomial.X} : Set (Polynomial (MvPolynomial (Fin 1) K)))) := by
  have hmap :
      Ideal.map
          (x1PolynomialEquiv K : CoordinateRing K →+*
            Polynomial (MvPolynomial (Fin 1) K))
          (x1Ideal K) =
        Ideal.span ({Polynomial.X} : Set (Polynomial (MvPolynomial (Fin 1) K))) := by
    rw [x1Ideal, Ideal.map_span]
    simp [x1PolynomialEquiv, coordinateSwap, X1, MvPolynomial.finSuccEquiv_X_zero]
  rw [← hmap]
  exact (Ideal.comap_map_of_bijective
    (x1PolynomialEquiv K : CoordinateRing K →+*
      Polynomial (MvPolynomial (Fin 1) K))
    (x1PolynomialEquiv K).bijective).symm

theorem x0Ideal_isPrime :
    (x0Ideal K).IsPrime := by
  rw [x0Ideal_eq_comap_span_X K]
  haveI :
      (Ideal.span ({Polynomial.X} : Set (Polynomial (MvPolynomial (Fin 1) K)))).IsPrime :=
    polynomial_span_X_isPrime K
  exact Ideal.comap_isPrime
    (MvPolynomial.finSuccEquiv K 1 : CoordinateRing K →+*
      Polynomial (MvPolynomial (Fin 1) K))
    (Ideal.span ({Polynomial.X} : Set (Polynomial (MvPolynomial (Fin 1) K))))

theorem x1Ideal_isPrime :
    (x1Ideal K).IsPrime := by
  rw [x1Ideal_eq_comap_span_X K]
  haveI :
      (Ideal.span ({Polynomial.X} : Set (Polynomial (MvPolynomial (Fin 1) K)))).IsPrime :=
    polynomial_span_X_isPrime K
  exact Ideal.comap_isPrime
    (x1PolynomialEquiv K : CoordinateRing K →+*
      Polynomial (MvPolynomial (Fin 1) K))
    (Ideal.span ({Polynomial.X} : Set (Polynomial (MvPolynomial (Fin 1) K))))

theorem x0SubX1Ideal_isPrime :
    (x0SubX1Ideal K).IsPrime := by
  rw [x0SubX1Ideal_eq_comap_span_X_sub_C_X K]
  haveI :
      (Ideal.span ({x0SubX1PolynomialTarget K} :
        Set (Polynomial (MvPolynomial (Fin 1) K)))).IsPrime :=
    polynomial_span_X_sub_C_X_isPrime K
  exact Ideal.comap_isPrime
    (MvPolynomial.finSuccEquiv K 1 : CoordinateRing K →+*
      Polynomial (MvPolynomial (Fin 1) K))
    (Ideal.span ({x0SubX1PolynomialTarget K} :
      Set (Polynomial (MvPolynomial (Fin 1) K))))

/-- The scheme-theoretic point `[0:1]` of `Proj K[X₀,X₁]`. -/
def zeroPoint : _root_.ProjectiveSpectrum (grading K) where
  asHomogeneousIdeal := x0HomogeneousIdeal K
  isPrime := x0Ideal_isPrime K
  not_irrelevant_le := not_irrelevant_le_x0HomogeneousIdeal K

/-- The scheme-theoretic point `[1:0]` of `Proj K[X₀,X₁]`. -/
def infinityPoint : _root_.ProjectiveSpectrum (grading K) where
  asHomogeneousIdeal := x1HomogeneousIdeal K
  isPrime := x1Ideal_isPrime K
  not_irrelevant_le := not_irrelevant_le_x1HomogeneousIdeal K

/-- The scheme-theoretic point `[1:1]` of `Proj K[X₀,X₁]`. -/
def onePoint : _root_.ProjectiveSpectrum (grading K) where
  asHomogeneousIdeal := x0SubX1HomogeneousIdeal K
  isPrime := x0SubX1Ideal_isPrime K
  not_irrelevant_le := not_irrelevant_le_x0SubX1HomogeneousIdeal K

theorem zeroPoint_asHomogeneousIdeal :
    (zeroPoint K).asHomogeneousIdeal = x0HomogeneousIdeal K := rfl

theorem infinityPoint_asHomogeneousIdeal :
    (infinityPoint K).asHomogeneousIdeal = x1HomogeneousIdeal K := rfl

theorem onePoint_asHomogeneousIdeal :
    (onePoint K).asHomogeneousIdeal = x0SubX1HomogeneousIdeal K := rfl

theorem zeroPoint_ne_infinityPoint :
    zeroPoint K ≠ infinityPoint K := by
  intro h
  have hI : x0HomogeneousIdeal K = x1HomogeneousIdeal K := by
    simpa [zeroPoint_asHomogeneousIdeal, infinityPoint_asHomogeneousIdeal] using
      congrArg _root_.ProjectiveSpectrum.asHomogeneousIdeal h
  have hx : X1 K ∈ x0Ideal K := by
    change X1 K ∈ (x0HomogeneousIdeal K).toIdeal
    rw [hI]
    change X1 K ∈ x1Ideal K
    exact Ideal.mem_span_singleton_self (X1 K)
  exact x1_not_mem_x0Ideal K hx

theorem zeroPoint_ne_onePoint :
    zeroPoint K ≠ onePoint K := by
  intro h
  have hI : x0HomogeneousIdeal K = x0SubX1HomogeneousIdeal K := by
    simpa [zeroPoint_asHomogeneousIdeal, onePoint_asHomogeneousIdeal] using
      congrArg _root_.ProjectiveSpectrum.asHomogeneousIdeal h
  have hx : X0 K ∈ x0SubX1Ideal K := by
    change X0 K ∈ (x0SubX1HomogeneousIdeal K).toIdeal
    rw [← hI]
    change X0 K ∈ x0Ideal K
    exact Ideal.mem_span_singleton_self (X0 K)
  exact x0_not_mem_x0SubX1Ideal K hx

theorem onePoint_ne_infinityPoint :
    onePoint K ≠ infinityPoint K := by
  intro h
  have hI : x0SubX1HomogeneousIdeal K = x1HomogeneousIdeal K := by
    simpa [onePoint_asHomogeneousIdeal, infinityPoint_asHomogeneousIdeal] using
      congrArg _root_.ProjectiveSpectrum.asHomogeneousIdeal h
  have hx1 : X1 K ∈ x0SubX1Ideal K := by
    change X1 K ∈ (x0SubX1HomogeneousIdeal K).toIdeal
    rw [hI]
    change X1 K ∈ x1Ideal K
    exact Ideal.mem_span_singleton_self (X1 K)
  have hx01 : X0SubX1 K ∈ x0SubX1Ideal K :=
    Ideal.mem_span_singleton_self (X0SubX1 K)
  have hx0 : X0 K ∈ x0SubX1Ideal K := by
    have hsum : X0SubX1 K + X1 K = X0 K := by
      simp [X0SubX1]
    simpa [hsum] using add_mem hx01 hx1
  exact x0_not_mem_x0SubX1Ideal K hx0

/-- The three marked scheme points `0`, `1`, and `∞` on `Proj K[X₀,X₁]`. -/
noncomputable def markedPointFinset : Finset (_root_.ProjectiveSpectrum (grading K)) := by
  classical
  exact {zeroPoint K, onePoint K, infinityPoint K}

theorem zeroPoint_mem_markedPointFinset :
    zeroPoint K ∈ markedPointFinset K := by
  classical
  simp [markedPointFinset]

theorem onePoint_mem_markedPointFinset :
    onePoint K ∈ markedPointFinset K := by
  classical
  simp [markedPointFinset]

theorem infinityPoint_mem_markedPointFinset :
    infinityPoint K ∈ markedPointFinset K := by
  classical
  simp [markedPointFinset]

theorem markedPointFinset_card :
    (markedPointFinset K).card = 3 := by
  classical
  simp [markedPointFinset, zeroPoint_ne_onePoint K, zeroPoint_ne_infinityPoint K,
    onePoint_ne_infinityPoint K]

/-- The three marked scheme points `0`, `1`, and `∞` as a set. -/
noncomputable def markedPointSet : Set (_root_.ProjectiveSpectrum (grading K)) :=
  markedPointFinset K

theorem markedPointSet_finite :
    (markedPointSet K).Finite :=
  (markedPointFinset K).finite_toSet

theorem mem_markedPointSet_iff (p : _root_.ProjectiveSpectrum (grading K)) :
    p ∈ markedPointSet K ↔ p ∈ markedPointFinset K :=
  Iff.rfl

/-- The three marked points viewed as a finset of points of the scheme `P^1_K`. -/
noncomputable def markedSchemePointFinset : Finset (P1 K) :=
  markedPointFinset K

/-- The three marked points viewed as a set of points of the scheme `P^1_K`. -/
noncomputable def markedSchemePointSet : Set (P1 K) :=
  markedPointSet K

theorem markedSchemePointFinset_card :
    (markedSchemePointFinset K).card = 3 := by
  exact markedPointFinset_card K

theorem markedSchemePointSet_finite :
    (markedSchemePointSet K).Finite :=
  markedPointSet_finite K

theorem mem_markedSchemePointSet_iff (p : P1 K) :
    p ∈ markedSchemePointSet K ↔ p ∈ markedPointSet K :=
  Iff.rfl

theorem zeroPoint_mem_markedSchemePointFinset :
    zeroPoint K ∈ markedSchemePointFinset K := by
  exact zeroPoint_mem_markedPointFinset K

theorem onePoint_mem_markedSchemePointFinset :
    onePoint K ∈ markedSchemePointFinset K := by
  exact onePoint_mem_markedPointFinset K

theorem infinityPoint_mem_markedSchemePointFinset :
    infinityPoint K ∈ markedSchemePointFinset K := by
  exact infinityPoint_mem_markedPointFinset K

theorem zeroPoint_mem_x1_basicOpen :
    zeroPoint K ∈ Proj.basicOpen (grading K) (X1 K) := by
  rw [ProjectiveSpectrum.basicOpen_mem_iff]
  change X1 K ∉ x0Ideal K
  exact x1_not_mem_x0Ideal K

theorem zeroPoint_not_mem_x0_basicOpen :
    zeroPoint K ∉ Proj.basicOpen (grading K) (X0 K) := by
  rw [ProjectiveSpectrum.basicOpen_mem_iff]
  push_neg
  change X0 K ∈ x0Ideal K
  exact Ideal.mem_span_singleton_self (X0 K)

theorem onePoint_mem_x0_basicOpen :
    onePoint K ∈ Proj.basicOpen (grading K) (X0 K) := by
  rw [ProjectiveSpectrum.basicOpen_mem_iff]
  exact x0_not_mem_x0SubX1Ideal K

theorem onePoint_mem_x1_basicOpen :
    onePoint K ∈ Proj.basicOpen (grading K) (X1 K) := by
  rw [ProjectiveSpectrum.basicOpen_mem_iff]
  intro hx1
  have hx01 : X0SubX1 K ∈ x0SubX1Ideal K :=
    Ideal.mem_span_singleton_self (X0SubX1 K)
  have hx0 : X0 K ∈ x0SubX1Ideal K := by
    have hsum : X0SubX1 K + X1 K = X0 K := by
      simp [X0SubX1]
    simpa [hsum] using add_mem hx01 hx1
  exact x0_not_mem_x0SubX1Ideal K hx0

theorem infinityPoint_mem_x0_basicOpen :
    infinityPoint K ∈ Proj.basicOpen (grading K) (X0 K) := by
  rw [ProjectiveSpectrum.basicOpen_mem_iff]
  change X0 K ∉ x1Ideal K
  exact x0_not_mem_x1Ideal K

theorem infinityPoint_not_mem_x1_basicOpen :
    infinityPoint K ∉ Proj.basicOpen (grading K) (X1 K) := by
  rw [ProjectiveSpectrum.basicOpen_mem_iff]
  push_neg
  change X1 K ∈ x1Ideal K
  exact Ideal.mem_span_singleton_self (X1 K)

end Domain

end
end SchemeProjectiveLine
end SourceStack
end HilbertTest
