import HilbertTest.SourceStack.PolynomialSeparation
import HilbertTest.SourceStack.ProjectiveLine

/-!
Polynomial separation on the affine chart of the linear projective line.

Mochizuki Lemma 2.4 uses a polynomial replacement step before returning to
maps into `P^1`.  `PolynomialSeparation` proves the field-level statement.  This
file transports that statement through the affine chart `x |-> [p(x):1]` of the
linear projective line, recording exactly where affine injectivity and avoidance
of `{0,1,infinity}` enter.
-/

noncomputable section

open scoped Polynomial

set_option linter.unusedSectionVars false

namespace HilbertTest
namespace SourceStack
namespace P1PolynomialSeparation

open PolynomialMaps
open PolynomialSeparation

universe u v

variable (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]

/-- The affine-chart `P^1` map associated to a polynomial: `x |-> [p(x):1]`. -/
def affinePolynomialPointMap (p : F[X]) (x : E) : ProjectiveLine.P1 E :=
  ProjectiveLine.affinePoint E (Polynomial.aeval x p)

theorem affinePolynomialPointMap_eq_iff
    (p : F[X]) (x y : E) :
    affinePolynomialPointMap F E p x = affinePolynomialPointMap F E p y ↔
      Polynomial.aeval x p = Polynomial.aeval y p := by
  constructor
  · intro h
    exact ProjectiveLine.affinePoint_injective E h
  · intro h
    simp [affinePolynomialPointMap, h]

theorem affinePolynomialPointMap_ne_target_of_aeval_ne
    {p : F[X]} {x β : E}
    (h : Polynomial.aeval x p ≠ Polynomial.aeval β p) :
    affinePolynomialPointMap F E p x ≠
      ProjectiveLine.affinePoint E (Polynomial.aeval β p) := by
  intro hmap
  exact h (ProjectiveLine.affinePoint_injective E hmap)

theorem derivative_ne_zero_of_affinePolynomialPointMap_eq_target
    {S : Set E} {p : F[X]} (hpder : p.derivative ≠ 0) {x β : E}
    (hβ : Polynomial.aeval β p ∉ replacementSet F E S p)
    (hmap : affinePolynomialPointMap F E p x =
      ProjectiveLine.affinePoint E (Polynomial.aeval β p)) :
    Polynomial.aeval x p.derivative ≠ 0 := by
  have hval : Polynomial.aeval x p = Polynomial.aeval β p :=
    ProjectiveLine.affinePoint_injective E hmap
  exact PolynomialMaps.derivative_aeval_ne_zero_of_value_not_mem_replacementSet
    F E hpder hβ hval

section MochizukiLemma21

variable (K : Type u) [Field K] [CharZero K]

/-- Projective-line form of Mochizuki Lemma 2.1(b): every affine critical point
of `x^m * (x - 1)^n` lies in the four-point set `{0, m/(m+n), 1, infinity}`. -/
theorem mochizukiPolynomial_derivative_zero_affinePoint_mem_fourPointSet
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) {x : K}
    (hx : Polynomial.aeval x (mochizukiPolynomial K m n).derivative = 0) :
    ProjectiveLine.affinePoint K x ∈
      ProjectiveLine.fourPointSet K ((m : K) / ((m + n : ℕ) : K)) := by
  have hcrit :=
    mochizukiPolynomial_derivative_aeval_eq_zero_imp K m n hm hn hx
  exact
    (ProjectiveLine.affinePoint_mem_fourPointSet_iff K
      ((m : K) / ((m + n : ℕ) : K)) x).2
      (by
        rcases hcrit with hzero | hone | hratio
        · exact Or.inl hzero
        · exact Or.inr (Or.inr hone)
        · exact Or.inr (Or.inl hratio))

/-- The four distinguished points `{0, m/(m+n), 1, infinity}` are distinct in
characteristic zero when both exponents are positive. -/
theorem mochizukiFourPointFinset_card
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (ProjectiveLine.fourPointFinset K
      ((m : K) / ((m + n : ℕ) : K))).card = 4 := by
  exact ProjectiveLine.fourPointFinset_card K
    (mochizukiRatio_ne_zero K m n hm hn)
    (mochizukiRatio_ne_one K m n hm hn)

/-- Mochizuki four-point cardinality drop: a map from
`{0, m/(m+n), 1, infinity}` into the branch triple has smaller image. -/
theorem image_mochizukiFourPointFinset_card_lt_of_maps_to_branch
    [DecidableEq (ProjectiveLine.P1 K)]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (f : ProjectiveLine.P1 K → ProjectiveLine.P1 K)
    (hmap : ∀ x ∈ ProjectiveLine.fourPointFinset K
      ((m : K) / ((m + n : ℕ) : K)),
        f x ∈ ProjectiveLine.branchFinset K) :
    ((ProjectiveLine.fourPointFinset K
      ((m : K) / ((m + n : ℕ) : K))).image f).card <
      (ProjectiveLine.fourPointFinset K
        ((m : K) / ((m + n : ℕ) : K))).card := by
  exact ProjectiveLine.image_fourPointFinset_card_lt_of_maps_to_branch K
    (mochizukiRatio_ne_zero K m n hm hn)
    (mochizukiRatio_ne_one K m n hm hn) f hmap

/-- Pigeonhole consequence for the Mochizuki four-point set: if the four
distinguished points all map into `{0,1,infinity}`, two have the same image. -/
theorem exists_distinct_same_image_mochizukiFourPoint_of_maps_to_branch
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (f : ProjectiveLine.P1 K → ProjectiveLine.P1 K)
    (hmap : ∀ x ∈ ProjectiveLine.fourPointFinset K
      ((m : K) / ((m + n : ℕ) : K)),
        f x ∈ ProjectiveLine.branchFinset K) :
    ∃ x ∈ ProjectiveLine.fourPointFinset K
        ((m : K) / ((m + n : ℕ) : K)),
      ∃ y ∈ ProjectiveLine.fourPointFinset K
          ((m : K) / ((m + n : ℕ) : K)),
        x ≠ y ∧ f x = f y := by
  exact ProjectiveLine.exists_distinct_same_image_fourPoint_of_maps_to_branch K
    (mochizukiRatio_ne_zero K m n hm hn)
    (mochizukiRatio_ne_one K m n hm hn) f hmap

/-- Lemma 2.2-style finite-set cardinality drop specialized to Mochizuki's
four distinguished points. -/
theorem image_card_lt_of_mochizukiFourPoint_subset_maps_to_branch
    [DecidableEq (ProjectiveLine.P1 K)]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (S : Finset (ProjectiveLine.P1 K))
    (f : ProjectiveLine.P1 K → ProjectiveLine.P1 K)
    (hsubset : ProjectiveLine.fourPointFinset K
      ((m : K) / ((m + n : ℕ) : K)) ⊆ S)
    (hmap : ∀ x ∈ S, f x ∈ ProjectiveLine.branchFinset K) :
    (S.image f).card < S.card := by
  exact ProjectiveLine.image_card_lt_of_fourPoint_subset_maps_to_branch K
    (mochizukiRatio_ne_zero K m n hm hn)
    (mochizukiRatio_ne_one K m n hm hn) S f hsubset hmap

/-- Lemma 2.2 induction handoff specialized to Mochizuki's four distinguished
points: the image finset is strictly smaller and contains all target images. -/
theorem exists_smaller_image_finset_of_mochizukiFourPoint_subset_maps_to_branch
    [DecidableEq (ProjectiveLine.P1 K)]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (S : Finset (ProjectiveLine.P1 K))
    (f : ProjectiveLine.P1 K → ProjectiveLine.P1 K)
    (hsubset : ProjectiveLine.fourPointFinset K
      ((m : K) / ((m + n : ℕ) : K)) ⊆ S)
    (hmap : ∀ x ∈ S, f x ∈ ProjectiveLine.branchFinset K) :
    ∃ T : Finset (ProjectiveLine.P1 K),
      T = S.image f ∧
        (∀ x ∈ S, f x ∈ T) ∧
          T.card < S.card := by
  exact ProjectiveLine.exists_smaller_image_finset_of_fourPoint_subset_maps_to_branch
    K (mochizukiRatio_ne_zero K m n hm hn)
    (mochizukiRatio_ne_one K m n hm hn) S f hsubset hmap

/-- Projective-line branch control for the normalized Belyi polynomial:
every affine critical point maps into the finite branch triple `{0,1,infinity}`. -/
theorem normalizedBelyiPolynomial_critical_affinePolynomialPointMap_mem_branchFinset
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) {x : K}
    (hx : Polynomial.aeval x (normalizedBelyiPolynomial K m n).derivative = 0) :
    affinePolynomialPointMap K K (normalizedBelyiPolynomial K m n) x ∈
      ProjectiveLine.branchFinset K := by
  have hvalue :
      Polynomial.aeval x (normalizedBelyiPolynomial K m n) = 0 ∨
        Polynomial.aeval x (normalizedBelyiPolynomial K m n) = 1 :=
    normalizedBelyiPolynomial_critical_value_eq_zero_or_one K m n hm hn hx
  simpa [affinePolynomialPointMap] using
    (ProjectiveLine.affinePoint_mem_branchFinset_iff K
      (Polynomial.aeval x (normalizedBelyiPolynomial K m n))).2 hvalue

/-- Set-valued branch-control form for the normalized Belyi polynomial. -/
theorem normalizedBelyiPolynomial_critical_affinePolynomialPointMap_mem_branchSet
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) {x : K}
    (hx : Polynomial.aeval x (normalizedBelyiPolynomial K m n).derivative = 0) :
    affinePolynomialPointMap K K (normalizedBelyiPolynomial K m n) x ∈
      ProjectiveLine.branchSet K := by
  have hvalue :
      Polynomial.aeval x (normalizedBelyiPolynomial K m n) = 0 ∨
        Polynomial.aeval x (normalizedBelyiPolynomial K m n) = 1 :=
    normalizedBelyiPolynomial_critical_value_eq_zero_or_one K m n hm hn hx
  simpa [affinePolynomialPointMap] using
    (ProjectiveLine.affinePoint_mem_branchSet_iff K
      (Polynomial.aeval x (normalizedBelyiPolynomial K m n))).2 hvalue

end MochizukiLemma21

/-- A polynomial separation step whose selected affine target avoids the branch
triple `{0,1,infinity}` on the linear projective line. -/
structure P1PolynomialSeparationStep (S : Set E) (β : E)
    extends PolynomialSeparationStep F E S β where
  target_ne_zero : Polynomial.aeval β polynomial ≠ 0
  target_ne_one : Polynomial.aeval β polynomial ≠ 1

namespace P1PolynomialSeparationStep

variable {F E}
variable [Field F] [Field E] [Algebra F E]
variable {S : Set E} {β : E}
variable (P : P1PolynomialSeparationStep F E S β)

/-- The selected affine target point `[p(β):1]`. -/
def targetPoint : ProjectiveLine.P1 E :=
  ProjectiveLine.affinePoint E (Polynomial.aeval β P.polynomial)

/-- The affine-chart `P^1` map attached to the separating polynomial. -/
def pointMap (x : E) : ProjectiveLine.P1 E :=
  affinePolynomialPointMap F E P.polynomial x

theorem targetPoint_ne_infinity :
    P.targetPoint ≠ ProjectiveLine.infinity E := by
  exact ProjectiveLine.affinePoint_ne_infinity E _

theorem targetPoint_not_mem_branchFinset :
    P.targetPoint ∉ ProjectiveLine.branchFinset E := by
  intro hbranch
  have hvalue :
      Polynomial.aeval β P.polynomial = 0 ∨
        Polynomial.aeval β P.polynomial = 1 := by
    simpa [targetPoint] using
      (ProjectiveLine.affinePoint_mem_branchFinset_iff E
        (Polynomial.aeval β P.polynomial)).1 hbranch
  rcases hvalue with hzero | hone
  · exact P.target_ne_zero hzero
  · exact P.target_ne_one hone

theorem targetPoint_not_mem_branchSet :
    P.targetPoint ∉ ProjectiveLine.branchSet E := by
  exact P.targetPoint_not_mem_branchFinset

theorem pointMap_ne_target_of_mem
    {x : E} (hx : x ∈ S) :
    P.pointMap x ≠ P.targetPoint := by
  exact affinePolynomialPointMap_ne_target_of_aeval_ne F E
    (PolynomialSeparationStep.aeval_ne_target_of_mem P.toPolynomialSeparationStep hx)

theorem derivative_ne_zero_at_pointMap_preimage
    {x : E} (hx : P.pointMap x = P.targetPoint) :
    Polynomial.aeval x P.polynomial.derivative ≠ 0 := by
  have hval : Polynomial.aeval x P.polynomial =
      Polynomial.aeval β P.polynomial := by
    exact ProjectiveLine.affinePoint_injective E hx
  exact PolynomialSeparationStep.derivative_ne_zero_at_preimage
    P.toPolynomialSeparationStep hval

/-- Packaged `P^1` affine-chart handoff: the selected target avoids the branch
triple, is separated from `S`, and all affine preimages are noncritical for the
separating polynomial. -/
theorem separates_avoids_branch_and_noncritical :
    P.targetPoint ∉ ProjectiveLine.branchSet E ∧
      (∀ x ∈ S, P.pointMap x ≠ P.targetPoint) ∧
        ∀ x : E, P.pointMap x = P.targetPoint →
          Polynomial.aeval x P.polynomial.derivative ≠ 0 := by
  exact
    ⟨P.targetPoint_not_mem_branchSet,
      ⟨fun x hx => P.pointMap_ne_target_of_mem hx,
        fun x hx => P.derivative_ne_zero_at_pointMap_preimage hx⟩⟩

end P1PolynomialSeparationStep

end P1PolynomialSeparation
end SourceStack
end HilbertTest
