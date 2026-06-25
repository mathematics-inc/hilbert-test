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
the branch triple and four-point collections both as finsets and finite sets;
membership in these branch/four-point sets reduces to coordinate membership on
the affine chart.  It also checks the Lemma 2.2 induction bookkeeping that any
finite projective-line set containing `{0,r,1,∞}` has strictly smaller image
cardinality when the whole set maps into `{0,1,∞}`.  This is still below the
scheme morphism layer.

`HilbertTest/SourceStack/FiniteSet.lean` checks the finite combinatorics behind
the Lemma 2.2 induction and the first reduction in Theorem 2.5: image
cardinality drops after a collision, four points mapping into three values force
a collision, and in an infinite point set a finite set `T` can be enlarged past
any prescribed cardinality while remaining disjoint from a fixed finite set `S`.

`HilbertTest/SourceStack/LinearAlgebra.lean` checks the Scherr-Zieve linear
source layer over infinite fields: finite unions of proper subspaces do not
cover, Riemann-Roch dimension inequalities give proper subspaces via smaller
`finrank`, finitely many nonzero linear forms have a common nonvanishing vector,
and the constrained common-kernel form needed after Riemann-Roch supplies
evaluations chooses a vector vanishing on one finite family of linear forms and
nonvanishing on another when the avoid forms remain nonzero on the common
kernel.  It also checks the finite-field counting handoff: if the sum of the
cardinalities of finitely many subspaces is smaller than the ambient finite
vector space, one can choose a vector outside all of them.

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
checked finiteness, inclusion, nonmembership, separation, and
derivative-nonvanishing consequences.  It also checks polynomial-composition
evaluation, the derivative chain rule, and the corresponding derivative
nonvanishing condition for compositions.

`HilbertTest/SourceStack/RationalMaps.lean` and
`HilbertTest/SourceStack/FunctionFields.lean` check the scheme function-field
source layer available in Mathlib: dense-domain and partial-map representative
wrappers, function-field reconstruction and uniqueness for rational maps out of
integral schemes, injectivity of germs on integral schemes, generic-point
membership in nonempty opens, fraction-field identifications for affine schemes
and nonempty affine opens, affine-chart generic-point identification, stalks
with the scheme function field as fraction field, and the section/stalk/function
field scalar-tower bridge.  The remaining missing input is the curve-specific
divisor and Riemann-Roch machinery that produces the required rational
functions.

`HilbertTest/SourceStack/ResidueFields.lean` checks the scheme point and
residue-field source layer available in Mathlib: point evaluation of sections,
emptiness of basic opens by residue-field evaluation, naturality of evaluations
under scheme morphisms, residue-field maps and congruences, canonical morphisms
`Spec O_{X,x} -> X` and `Spec kappa(x) -> X`, their formulas on sheaves and
global sections, specialization compatibility, open-subscheme compatibility,
closed-point stalk isomorphisms for local rings, descent of local stalk maps to
residue fields, reconstruction of local-ring-valued and field-valued points from
their closed-point stalk/residue-field maps, compatibility of
`Spec kappa(x)` maps with `Spec O_{X,x}` maps, and equality criteria for
field-valued and local-ring-valued point data.  The remaining missing input is
the specialization of these general facts to algebraic points on curves and the
marked points of scheme-theoretic `P^1`.

`HilbertTest/SourceStack/PullbackCarrier.lean` checks Mathlib's point-carrier
description of scheme fiber products: triplets of points with common image in
the base, the residue-field tensor product attached to such triplets, canonical
maps from tensor spectra to pullbacks, reconstruction of pullback points from
residue-field tensor data, the carrier equivalence for pullback points, range
formulas for pullback projections and pullback maps, existence of points above
compatible pairs, and stability of surjectivity under base change.  The
remaining missing input is the curve-level specialization that turns this
general point-carrier API into statements about geometric points in the Belyi
maps used by the paper.

`HilbertTest/SourceStack/ProjectiveSpectrum.lean` checks the general `Proj`
source layer available in Mathlib: projective basic opens, affine charts,
affine-open chart ranges, affine basic opens, stalk localization, chart
compatibility with the structure morphism, intersections of standard affine
charts, separatedness of `Proj`, and the underlying projective-spectrum
zero-locus/vanishing-ideal topology.  The remaining missing input is the
specialized scheme `P^1 = Proj k[X,Y]` with marked `0`, `1`, and `infinity`
points connected to rational functions.

`HilbertTest/SourceStack/Topology.lean` checks the compactness facts needed by
the local compactness layer of Corollary 3.2: compact images under continuous
maps, finite subcovers, finite unions of compact subsets and compact images,
coordinate projections of compact product subsets, compactness of products, and
finite unions of coordinate projections of compact product subsets, including
the containment of those projection images in coordinatewise target subsets.
It also checks compact-exhaustion wrappers for locally compact
second-countable spaces, including inheritance by open subspaces, compactness
of the exhaustion sets, the interior containment step, coverage of the whole
space, eventual containment of compact subsets, the open exhaustion by
interiors, and compactness of the closure of each interior in a Hausdorff
space.  It also checks the basic locally compact compact-neighborhood lemma and
basic
topological proper-map compact-preimage/composition/closed-map wrappers.
It also checks the Corollary 3.1 open-cover infrastructure: compact-space
finite subcovers, continuous preimages of opens, finite intersections of opens,
finite-set complements in T1 spaces, and tuple-coordinate finite-avoidance
openness.

`HilbertTest/SourceStack/LocalFields.lean` checks local-field topology facts
available in Mathlib: compactness of the p-adic integers, properness/local
compactness/completeness/second countability/sigma compactness and compact
exhaustions for `ℚ_p`, locally compact/second-countable/sigma-compact
infinite-place completions of number fields, compact exhaustions for those
completions, the isometric closed embedding into `ℂ`, and real/complex
infinite-place isometry models.

`HilbertTest/SourceStack/BelyiCovers.lean` now formalizes the abstract
Corollary 3.1 compactness step: a family of continuous maps with finite branch
set gives open tuple-avoidance loci, pointwise avoidance gives an indexed open
cover, and compactness extracts a finite subcover.  It also formalizes the
fixed-set version over `X \ S`, restricting the map family to maps sending `S`
to the branch set.  The remaining missing input is the curve-level theorem
supplying those avoiding maps.

The same module also formalizes the abstract Corollary 1.2 consequence: if a
map sends a set `A` to the branch set and sends a chosen point outside the
branch set, its Belyi open is open, contains the point, and is contained in
`Aᶜ`.
It now includes a `NoncriticalBelyiExistence` interface matching the finite
disjoint-set conclusion of Theorem 2.5 and proves from it the pointwise
tuple-cover hypothesis and finite-subcover conclusion over `X \ S`, as well as
the finite-set Belyi-open containment statement and its explicit-complement and
open-with-finite-complement specializations behind Corollary 1.2.

`HilbertTest/SourceStack/SchemeBelyi.lean` now formalizes the scheme-level
abstract part of Definition 1.1: a target scheme with a branch-complement open,
a dominant morphism etale over that open, the source Belyi open as the preimage,
and the open-immersion/restriction identity for that preimage.  The missing
piece is the specialized `P^1` target with marked points `0`, `1`, and
`infinity`.

`HilbertTest/SourceStack/Schemes.lean` now also checks open-immersion wrappers
needed for Belyi open restrictions: composition, monomorphism, locally finite
type, smooth, etale, and separated.  It also checks that finite, smooth,
separated, proper, and etale morphisms keep those properties after restricting
the target to an open subscheme, and it checks quasi-compact composition,
base-change, compact-preimage, proper-to-compact-space bridges, and compact-space
bridge wrappers.  The same file now checks affine-morphism composition,
base-change, quasi-compactness, separatedness, affine-target source-affineness,
finite-implies-affine, finite-implies-separated,
integral-morphism composition/base-change/restriction, and the finite iff
integral plus locally finite type bridge.  It also checks
universally-closed restriction, quasi-compactness, closed-map and proper-map
bridges, and compactness of schemes universally closed or proper over a field.
It also now
checks quasi-separated composition/base-change and affine/terminal bridges, plus
the qcqs global-section localization layer: compact basic opens, power-clearing
for sections on basic opens, the localization statement for sections on
`D(f)`, nilpotent iff empty basic open on compact opens, and the compact-open
zero-locus/nilradical criterion.

`HilbertTest/SourceStack/UnramifiedEtale.lean` checks algebraic
formal-unramified and formal-etale source facts, including the
Kähler-differential characterization, square-zero lift uniqueness,
composition/base-change stability, separability equivalences over essentially
finite type field extensions, ring-level unramified algebra wrappers for
one-element localizations, composition, and base change, and formal-etale/etale
algebra wrappers for algebra equivalences, localizations, localized bases,
separable field extensions, and one-element localization.

`HilbertTest/SourceStack/Ramification.lean` checks the deeper
commutative-algebra source layer for ramification: algebraic unramifiedness,
formal-unramified localization, the finite-type tensor-product criterion and
distinguished tensor element identities, finite generation of free finite-type
formally unramified algebras, flat/projective transfer along finite-type
formally unramified algebras, Dedekind-domain ramification-index and
inertia-degree facts, tower laws, the fundamental `sum e*f = [L:K]` identity,
and valuation decomposition/inertia subgroup definitions.

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
