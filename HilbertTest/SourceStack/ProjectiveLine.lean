import HilbertTest.SourceStack.FiniteSet
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Data.Matrix.Notation

/-!
Lightweight projective-line facts over Mathlib's linear projectivization.

This is not yet the scheme `\mathbb P^1_k`; it is the underlying linear
projective-space layer needed for later Belyi-map statements.  The scheme layer
will eventually have to connect these points to sections and morphisms.
-/

namespace HilbertTest
namespace SourceStack

open scoped LinearAlgebra.Projectivization

namespace ProjectiveLine

variable (K : Type*) [DivisionRing K]

/-- The linear projective line over `K`. -/
abbrev P1 : Type _ := ℙ K (Fin 2 → K)

/-- The point `0 = [0:1]` on the projective line. -/
def zero : P1 K :=
  Projectivization.mk K ![0, (1 : K)] (by
    intro h
    have h1 := congr_fun h 1
    simp at h1)

/-- The point `1 = [1:1]` on the projective line. -/
def one : P1 K :=
  Projectivization.mk K ![(1 : K), (1 : K)] (by
    intro h
    have h0 := congr_fun h 0
    simp at h0)

/-- The point `∞ = [1:0]` on the projective line. -/
def infinity : P1 K :=
  Projectivization.mk K ![(1 : K), 0] (by
    intro h
    have h0 := congr_fun h 0
    simp at h0)

/-- The affine point `[r:1]` on the projective line. -/
def affinePoint (r : K) : P1 K :=
  Projectivization.mk K ![r, (1 : K)] (by
    intro h
    have h1 := congr_fun h 1
    simp at h1)

theorem zero_ne_infinity : zero K ≠ infinity K := by
  intro h
  unfold zero infinity at h
  rw [Projectivization.mk_eq_mk_iff'] at h
  obtain ⟨a, ha⟩ := h
  have h0 := congr_fun ha 0
  have h1 := congr_fun ha 1
  simp at h0 h1

theorem zero_ne_one : zero K ≠ one K := by
  intro h
  unfold zero one at h
  rw [Projectivization.mk_eq_mk_iff'] at h
  obtain ⟨a, ha⟩ := h
  have h0 := congr_fun ha 0
  have h1 := congr_fun ha 1
  simp at h0 h1
  exact (_root_.zero_ne_one : (0 : K) ≠ 1) (h0.symm.trans h1)

theorem one_ne_infinity : one K ≠ infinity K := by
  intro h
  unfold one infinity at h
  rw [Projectivization.mk_eq_mk_iff'] at h
  obtain ⟨a, ha⟩ := h
  have h0 := congr_fun ha 0
  have h1 := congr_fun ha 1
  simp at h0 h1

theorem affinePoint_zero :
    affinePoint K 0 = zero K := rfl

theorem affinePoint_one :
    affinePoint K 1 = one K := rfl

theorem affinePoint_ne_infinity (r : K) :
    affinePoint K r ≠ infinity K := by
  intro h
  unfold affinePoint infinity at h
  rw [Projectivization.mk_eq_mk_iff'] at h
  obtain ⟨a, ha⟩ := h
  have h1 := congr_fun ha 1
  simp at h1

theorem affinePoint_ne_zero {r : K} (hr : r ≠ 0) :
    affinePoint K r ≠ zero K := by
  intro h
  unfold affinePoint zero at h
  rw [Projectivization.mk_eq_mk_iff'] at h
  obtain ⟨a, ha⟩ := h
  have h0 := congr_fun ha 0
  have h1 := congr_fun ha 1
  simp at h0 h1
  exact hr h0.symm

theorem affinePoint_ne_one {r : K} (hr : r ≠ 1) :
    affinePoint K r ≠ one K := by
  intro h
  unfold affinePoint one at h
  rw [Projectivization.mk_eq_mk_iff'] at h
  obtain ⟨a, ha⟩ := h
  have h0 := congr_fun ha 0
  have h1 := congr_fun ha 1
  simp at h0 h1
  exact hr (h0.symm.trans h1)

section FractionalLinear

variable (F : Type*) [Field F]

/-- The linear map on homogeneous coordinates inducing
`x ↦ 1 / (x - lambda)` on the affine chart. -/
def reciprocalTranslateLinear (lambda : F) : (Fin 2 → F) →ₗ[F] (Fin 2 → F) where
  toFun v := ![v 1, v 0 - lambda * v 1]
  map_add' v w := by
    ext i
    fin_cases i
    · simp
    · simp
      ring
  map_smul' c v := by
    ext i
    fin_cases i
    · simp
    · simp
      ring

/-- The homogeneous-coordinate map for `x ↦ 1 / (x - lambda)` is injective. -/
theorem reciprocalTranslateLinear_injective
    (lambda : F) :
    Function.Injective (reciprocalTranslateLinear F lambda) := by
  intro v w h
  have h0 := congr_fun h 0
  have h1 := congr_fun h 1
  simp [reciprocalTranslateLinear] at h0 h1
  funext i
  fin_cases i
  · have h1' : v 0 - lambda * w 1 = w 0 - lambda * w 1 := by
      simpa [h0] using h1
    exact sub_left_inj.mp h1'
  · exact h0

/-- The projective-line map induced by `x ↦ 1 / (x - lambda)`. -/
def reciprocalTranslate (lambda : F) : P1 F → P1 F :=
  Projectivization.map (reciprocalTranslateLinear F lambda)
    (reciprocalTranslateLinear_injective F lambda)

/-- Reciprocal translates are injective on the linear projective line. -/
theorem reciprocalTranslate_injective
    (lambda : F) :
    Function.Injective (reciprocalTranslate F lambda) := by
  unfold reciprocalTranslate
  exact Projectivization.map_injective (reciprocalTranslateLinear F lambda)
    (reciprocalTranslateLinear_injective F lambda)

/-- Away from its pole, the reciprocal translate sends `[r:1]` to
`[(r-lambda)^{-1}:1]`. -/
theorem reciprocalTranslate_affinePoint_of_ne
    (lambda r : F) (hr : r ≠ lambda) :
    reciprocalTranslate F lambda (affinePoint F r) =
      affinePoint F ((r - lambda)⁻¹) := by
  have hdiff : r - lambda ≠ 0 := sub_ne_zero.mpr hr
  unfold reciprocalTranslate affinePoint reciprocalTranslateLinear
  rw [Projectivization.map_mk]
  rw [Projectivization.mk_eq_mk_iff']
  refine ⟨r - lambda, ?_⟩
  ext i
  fin_cases i
  · simp [hdiff]
  · simp

/-- The pole maps to infinity under the reciprocal translate. -/
theorem reciprocalTranslate_affinePoint_pole
    (lambda : F) :
    reciprocalTranslate F lambda (affinePoint F lambda) =
      infinity F := by
  unfold reciprocalTranslate affinePoint infinity reciprocalTranslateLinear
  rw [Projectivization.map_mk]
  simp

/-- Infinity maps to zero under the reciprocal translate. -/
theorem reciprocalTranslate_infinity
    (lambda : F) :
    reciprocalTranslate F lambda (infinity F) = zero F := by
  unfold reciprocalTranslate infinity zero reciprocalTranslateLinear
  rw [Projectivization.map_mk]
  simp

/-- Away from the pole, affine points do not map to infinity. -/
theorem reciprocalTranslate_affinePoint_ne_infinity
    (lambda r : F) (hr : r ≠ lambda) :
    reciprocalTranslate F lambda (affinePoint F r) ≠ infinity F := by
  rw [reciprocalTranslate_affinePoint_of_ne F lambda r hr]
  exact affinePoint_ne_infinity F _

/-- Away from the pole, affine points do not map to zero. -/
theorem reciprocalTranslate_affinePoint_ne_zero
    (lambda r : F) (hr : r ≠ lambda) :
    reciprocalTranslate F lambda (affinePoint F r) ≠ zero F := by
  rw [reciprocalTranslate_affinePoint_of_ne F lambda r hr]
  exact affinePoint_ne_zero F (inv_ne_zero (sub_ne_zero.mpr hr))

/-- The linear map on homogeneous coordinates inducing `x ↦ a * x + b` on
the affine chart. -/
def affineLinearMapLinear (a b : F) : (Fin 2 → F) →ₗ[F] (Fin 2 → F) where
  toFun v := ![a * v 0 + b * v 1, v 1]
  map_add' v w := by
    ext i
    fin_cases i
    · simp
      ring
    · simp
  map_smul' c v := by
    ext i
    fin_cases i
    · simp
      ring
    · simp

/-- If `a ≠ 0`, the homogeneous-coordinate map for `x ↦ a*x+b` is injective. -/
theorem affineLinearMapLinear_injective
    {a b : F} (ha : a ≠ 0) :
    Function.Injective (affineLinearMapLinear F a b) := by
  intro v w h
  have h0 := congr_fun h 0
  have h1 := congr_fun h 1
  simp [affineLinearMapLinear] at h0 h1
  funext i
  fin_cases i
  · have h0' : a * v 0 = a * w 0 := by
      simpa [h1] using h0
    exact mul_left_cancel₀ ha h0'
  · exact h1

/-- The projective-line map induced by `x ↦ a*x+b`. -/
def affineLinearMap (a b : F) (ha : a ≠ 0) : P1 F → P1 F :=
  Projectivization.map (affineLinearMapLinear F a b)
    (affineLinearMapLinear_injective F ha)

/-- Affine linear maps with nonzero linear coefficient are injective on the
linear projective line. -/
theorem affineLinearMap_injective
    {a b : F} (ha : a ≠ 0) :
    Function.Injective (affineLinearMap F a b ha) := by
  unfold affineLinearMap
  exact Projectivization.map_injective (affineLinearMapLinear F a b)
    (affineLinearMapLinear_injective F ha)

/-- Affine linear maps send affine points to affine points by the expected
formula. -/
theorem affineLinearMap_affinePoint
    {a b : F} (ha : a ≠ 0) (r : F) :
    affineLinearMap F a b ha (affinePoint F r) =
      affinePoint F (a * r + b) := by
  unfold affineLinearMap affinePoint affineLinearMapLinear
  rw [Projectivization.map_mk]
  simp

/-- Affine linear maps with nonzero linear coefficient fix infinity. -/
theorem affineLinearMap_infinity
    {a b : F} (ha : a ≠ 0) :
    affineLinearMap F a b ha (infinity F) = infinity F := by
  unfold affineLinearMap infinity affineLinearMapLinear
  rw [Projectivization.map_mk]
  rw [Projectivization.mk_eq_mk_iff']
  refine ⟨a, ?_⟩
  ext i
  fin_cases i
  · simp
  · simp

end FractionalLinear

/-- The finite branch set `{0,1,∞}` as a finset of linear projective points. -/
noncomputable def branchFinset : Finset (P1 K) :=
  by
    classical
    exact {zero K, one K, infinity K}

theorem zero_mem_branchFinset : zero K ∈ branchFinset K := by
  classical
  simp [branchFinset]

theorem one_mem_branchFinset : one K ∈ branchFinset K := by
  classical
  simp [branchFinset]

theorem infinity_mem_branchFinset : infinity K ∈ branchFinset K := by
  classical
  simp [branchFinset]

theorem branchFinset_card : (branchFinset K).card = 3 := by
  classical
  simp [branchFinset, zero_ne_one K, zero_ne_infinity K, one_ne_infinity K]

/-- The finite set `{0,r,1,∞}` from Mochizuki Lemma 2.1. -/
noncomputable def fourPointFinset (r : K) : Finset (P1 K) :=
  by
    classical
    exact {zero K, affinePoint K r, one K, infinity K}

theorem zero_mem_fourPointFinset (r : K) :
    zero K ∈ fourPointFinset K r := by
  classical
  simp [fourPointFinset]

theorem affinePoint_mem_fourPointFinset (r : K) :
    affinePoint K r ∈ fourPointFinset K r := by
  classical
  simp [fourPointFinset]

theorem one_mem_fourPointFinset (r : K) :
    one K ∈ fourPointFinset K r := by
  classical
  simp [fourPointFinset]

theorem infinity_mem_fourPointFinset (r : K) :
    infinity K ∈ fourPointFinset K r := by
  classical
  simp [fourPointFinset]

theorem fourPointFinset_card {r : K} (hr0 : r ≠ 0) (hr1 : r ≠ 1) :
    (fourPointFinset K r).card = 4 := by
  classical
  have hzA : zero K ≠ affinePoint K r := (affinePoint_ne_zero K hr0).symm
  have hA1 : affinePoint K r ≠ one K := affinePoint_ne_one K hr1
  have hAinf : affinePoint K r ≠ infinity K := affinePoint_ne_infinity K r
  simp [fourPointFinset, zero_ne_one K, zero_ne_infinity K, one_ne_infinity K,
    hzA, hA1, hAinf]

/-- If a map sends the four-point set `{0,r,1,∞}` into the branch triple
`{0,1,∞}`, then the image of the four-point set has strictly smaller
cardinality. -/
theorem image_fourPointFinset_card_lt_of_maps_to_branch
    [DecidableEq (P1 K)]
    {r : K} (hr0 : r ≠ 0) (hr1 : r ≠ 1)
    (f : P1 K → P1 K)
    (hmap : ∀ x ∈ fourPointFinset K r, f x ∈ branchFinset K) :
    ((fourPointFinset K r).image f).card < (fourPointFinset K r).card := by
  have hsubset : (fourPointFinset K r).image f ⊆ branchFinset K := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    exact hmap x hx
  have hle : ((fourPointFinset K r).image f).card ≤ (branchFinset K).card :=
    Finset.card_le_card hsubset
  have hle3 : ((fourPointFinset K r).image f).card ≤ 3 := by
    simpa [branchFinset_card K] using hle
  rw [fourPointFinset_card K hr0 hr1]
  omega

/-- If a map sends the four distinguished points `{0,r,1,∞}` into the branch
triple `{0,1,∞}`, then two of the four distinguished points have the same
image. -/
theorem exists_distinct_same_image_fourPoint_of_maps_to_branch
    {r : K} (hr0 : r ≠ 0) (hr1 : r ≠ 1)
    (f : P1 K → P1 K)
    (hmap : ∀ x ∈ fourPointFinset K r, f x ∈ branchFinset K) :
    ∃ x ∈ fourPointFinset K r, ∃ y ∈ fourPointFinset K r, x ≠ y ∧ f x = f y := by
  have hcard : (branchFinset K).card < (fourPointFinset K r).card := by
    rw [branchFinset_card K, fourPointFinset_card K hr0 hr1]
    norm_num
  exact exists_distinct_same_image_of_maps_to_smaller
    (fourPointFinset K r) (branchFinset K) f hcard hmap

end ProjectiveLine

end SourceStack
end HilbertTest
