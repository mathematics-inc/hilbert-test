# Full-paper formalization status

Target source: `artifacts/attachments/noncritical-belyi-maps_backtranslated.tex`

The paper has the following formal targets:

- Definition 1.1: Belyi map and Belyi open.
- Corollary 1.2: Belyi opens form a Zariski base.
- Lemma 2.1: elementary separating properties of the polynomial
  `f x = x^m * (x - 1)^n`.
- Lemma 2.2: Belyi maps noncritical at prescribed rational points.
- Lemma 2.3: separation by `x ↦ 1 / (x - lambda)`.
- Lemma 2.4: reduction from algebraic points to rational points.
- Theorem 2.5: Belyi maps noncritical at prescribed points on a smooth proper
  connected curve over `Qbar`.
- Corollary 3.1: finite collection of Belyi maps for arbitrary sets of fixed
  cardinality.
- Corollary 3.2: local noncritical neighborhoods over completions of number
  fields.

## Checked in this fork

`HilbertTest/NoncriticalBelyi/Elementary.lean` contains a no-`sorry` Lean
formalization of elementary real-polynomial inequalities used in Lemma 2.1:

- scaling separation from `beta / alpha >= C`,
- the inequality `(beta - 1) / (alpha - 1) >= beta / alpha` for
  `1 < alpha <= beta`,
- the lower bounds in property (e),
- `f(beta) > 1` under the hypotheses used in the paper,
- `beta <= f(beta)` and `beta <= 2 * f(beta)` for `beta >= 2`,
- offset-ratio inequalities used in the odd-`n` case after adding `f₀`,
- `|f x| <= 1` for `x in [0, 1]`.

`HilbertTest/NoncriticalBelyi/Polynomial.lean` contains the corresponding
no-`sorry` algebraic polynomial layer over `ℚ[X]`:

- endpoint evaluations of `X^m * (X - 1)^n` at `0` and `1`,
- the formal derivative formula,
- the factored derivative
  `X^(m-1) * (X-1)^(n-1) * ((m+n)X - m)`,
- vanishing of the derivative at the middle point `m/(m+n)`.

`HilbertTest/SourceStack/ComplexSeparation.lean` contains a no-`sorry` Lean
formalization of the finite complex-set separation used in Lemma 2.3:

- positive nearest-point distance from `β` to a finite complex set not
  containing `β`,
- existence of a point `lambda` near `β` that separates the finite set by any
  prescribed factor `C > 0`,
- the reciprocal translate estimate for `z ↦ 1 / (z - lambda)`,
- the rational-pole refinement when `β` is rational.

`HilbertTest/SourceStack/ProjectiveLine.lean` now also checks the corresponding
linear-projectivization map induced by homogeneous coordinates
`[X:Y] ↦ [Y:X - λY]`, including its action on affine points away from the pole,
the pole, and infinity; it also checks affine-linear transformations
`[X:Y] ↦ [aX + bY:Y]` for `a != 0`.  Both classes of linear projective maps
are checked as injective on projective points.  The same source layer now checks
that affine coordinates are injective, every point is affine or infinity, and
membership in the branch/four-point sets reduces to coordinate membership on
the affine chart.  This is still below the scheme morphism layer.

`HilbertTest/Belyi1980/Polynomial.lean` also checks the middle-value
positivity and AM-GM bound
`(m/(m+n))^m * (n/(m+n))^n <= 1/4` used in Mochizuki's odd-`n` case of
Lemma 2.1.

`HilbertTest/SourceStack/FieldTheory.lean` checks the pure field-theory
building blocks behind the Lemma 2.4 reduction, including primitive elements,
finite adjoining, separability, normal/Galois splitting, conjugacy by
automorphisms in normal extensions, and the minimal-polynomial degree drop for
roots of a derivative.

`HilbertTest/SourceStack/PolynomialMaps.lean` checks the finite-set bookkeeping
for the same Lemma 2.4 reduction: derivative root sets are finite, nonzero
derivative root membership is evaluation to zero, polynomial images of finite
sets are finite, and the named replacement set `p(S) ∪ p(rootSet p')` has
checked finiteness, inclusion, and nonmembership lemmas.

`HilbertTest/SourceStack/Topology.lean` checks the compactness facts needed by
the local compactness layer of Corollary 3.2: compact images under continuous
maps, finite subcovers, finite unions of compact subsets and compact images,
coordinate projections of compact product subsets, compactness of products, and
basic topological proper-map compact-preimage/composition/closed-map wrappers.

The checked output is:

```text
Build completed successfully.
```

## Why the rest is not a direct Hilbert run

The released Hilbert repository is a prover-orchestration system for Lean
benchmark statements.  It expects a Lean verifier service plus prover and
reasoner LLM endpoints.  It does not contain an algebraic-geometry library for
this paper, and the attached TeX is not already expressed as Lean theorem
statements.

Mathlib v4.15.0 has useful scheme-morphism infrastructure, including:

- `AlgebraicGeometry.Morphisms.Finite`
- `AlgebraicGeometry.Morphisms.Proper`
- `AlgebraicGeometry.Morphisms.Smooth`
- `AlgebraicGeometry.Morphisms.Etale`
- `AlgebraicGeometry.ProjectiveSpectrum`

However, a genuine proof of the full paper also needs APIs that are not
available as ready-to-use Mathlib components:

- smooth proper connected algebraic curves as a working category,
- the projective line `P^1_Spec k` with distinguished points `0`, `1`, `∞`
  connected to rational functions,
- finite subsets of geometric points of schemes and their images under
  morphisms,
- ramification and "unramified over the complement of `{0,1,∞}`" in the exact
  form used by Belyi maps,
- divisors on smooth proper curves, associated line bundles, canonical bundles,
  and degree,
- Riemann-Roch/Serre duality consequences used in the proof of Theorem 2.5,
- construction of finite morphisms from two global sections of a line bundle,
- field-of-definition and Galois-conjugacy APIs for points over `Qbar`,
- completions of number fields and the locally compact topology used in
  Corollary 3.2.

## Realistic next milestones

0. Optionally formalize the page-9 polynomial construction in Belyi's
   *On Galois Extensions of a Maximal Cyclotomic Field*; see
   `BELYI_1980_ASSESSMENT.md`.
1. Finish the finite-set image/cardinality packaging for Lemma 2.1 over the
   scheme/projective-line model; the formal derivative and middle critical-point
   calculation over `ℚ[X]` are now checked.
2. Finish the scheme-`P^1` morphism packaging for Lemma 2.3; the analytic
   estimate and the linear-projectivization reciprocal/affine-linear maps are
   now checked.
3. Build a projective-line API sufficient for Lemma 2.2 and Lemma 2.4.
4. Add a Belyi-map definition over `P^1` using Mathlib's scheme morphism
   properties.
5. Develop or import the curve/divisor/line-bundle machinery needed for
   Theorem 2.5.
6. Prove Corollaries 1.2, 3.1, and 3.2 from Theorem 2.5 plus compactness and
   topology lemmas.

Until milestones 3-5 exist, a claimed no-`sorry` Lean proof of the entire paper
would either be incomplete or would hide the missing mathematics behind axioms.
