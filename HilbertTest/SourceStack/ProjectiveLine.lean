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

end ProjectiveLine

end SourceStack
end HilbertTest
