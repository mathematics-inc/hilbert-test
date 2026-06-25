# Recursive source map for formalizing noncritical/separated Belyi maps

This document records source material that can drive a Lean formalization of
the Belyi-map input used by Mochizuki's IUT-related work.  The goal is to recurse
from the target theorem down to sources whose statements are close enough to
Mathlib-style definitions and lemmas.

## Main conclusion

There is no single paper that supplies all missing formalization infrastructure.
There is, however, a workable source stack.

The best theorem-level replacement or companion for Mochizuki's
`Noncritical Belyi Maps` is:

- Zachary Scherr and Michael E. Zieve, **Separated Belyi Maps**,
  Mathematical Research Letters 21 (2014), 1389-1406; arXiv:1310.2555.

It directly refines Mochizuki's Theorem 2.5 and is closer to a formalization
plan because it:

- states prescribed behavior at finite sets of points;
- gives a reduction from a general curve to `P^1`;
- uses Riemann-Roch spaces explicitly;
- separates the proof into curve-level and `P^1`-level constructions;
- includes the finite-collection result corresponding to Mochizuki's
  Corollary 3.1.

For a Lean development, it is likely better to formalize Scherr-Zieve first,
then derive Mochizuki's stated noncritical result as a corollary or comparison.

## Dependency tree

### 0. Target layer

Sources:

- Shinichi Mochizuki, **Noncritical Belyi Maps** (2004).
- Scherr-Zieve, **Separated Belyi Maps** (2014).

Formalization target:

- Define Belyi maps as finite morphisms `C -> P^1` whose branch locus is
  contained in `{0, 1, infinity}`.
- Prove existence with prescribed finite-point behavior.
- Derive Zariski-base and finite-collection corollaries.

Why Scherr-Zieve is preferable:

- Mochizuki's proof uses line bundles, Serre duality, and a compactness argument.
- Scherr-Zieve packages the first curve reduction as a Riemann-Roch-space
  proposition and then handles the rest on `P^1`.

### 1. Ordinary Belyi theorem and explicit `P^1` constructions

Sources:

- G. V. Belyi, **On Galois Extensions of a Maximal Cyclotomic Field**,
  Math. USSR Izvestija 14 (1980), 247-256.
- Alexandr Borisov, **On a Question of Craven and a Theorem of Belyi**,
  arXiv:math/0205266.
- Jeroen Sijsling and John Voight, **On computing Belyi maps**,
  Publications Mathématiques de Besançon (2014).
- Anand Deopurkar, **Belyi's theorem** lecture notes, based on Köck's proof.

Formalization use:

- Finite sets of algebraic points on `P^1`.
- Finite image-cardinality bookkeeping.  This fork checks the generic theorems
  that identifying two points strictly lowers finite-set image cardinality and
  that mapping into a strictly smaller finite target identifies two points.
- Fractional linear transformations with rational coefficients.
- Complex finite-set separation for reciprocal translates.  The analytic
  estimate and rational-pole refinement are checked in
  `HilbertTest.SourceStack.ComplexSeparation`; the remaining work is to express
  it as a scheme `P^1` morphism statement.
- Polynomial/rational functions whose critical values are controlled.
- The explicit Belyi polynomial
  `(m+n)^(m+n)/(m^m*n^n) * t^m * (1 - t)^n`
  for a normalized triple `{0, m/(m+n), 1}`.

### 2. Curve reduction: Riemann-Roch spaces and finite morphisms to `P^1`

Sources:

- Scherr-Zieve, **Separated Belyi Maps**, Proposition 2.1 and Lemma 2.2.
- Stacks Project, **Algebraic Curves** chapter.
- Qing Liu, **Algebraic Geometry and Arithmetic Curves**.
- Robin Hartshorne, **Algebraic Geometry**, especially Chapters II-IV.
- Ravi Vakil, **The Rising Sea / Foundations of Algebraic Geometry** notes,
  especially the sections on line bundles and maps to projective space.

Formalization use:

- Proper smooth/geometrically integral curves over a field.
- Genus and Riemann-Roch spaces `L(D)`.
- Existence of rational functions with prescribed poles.
- A nonconstant rational function on a proper curve gives a finite morphism to
  `P^1`.
- Global sections of a generated line bundle give a morphism to projective
  space.

Minimal theorem package needed:

- Divisors and degree on a proper smooth curve.
- Riemann-Roch in the form `ell(D) = deg(D) + 1 - g` for
  `deg(D) >= 2g - 1`.
- The vector-space lemma that a finite union of proper subspaces does not cover
  a finite-dimensional vector space over an infinite field, plus the finite-field
  inclusion-exclusion variant used by Scherr-Zieve.

### 3. Scheme morphism layer

Sources:

- Stacks Project, **Morphisms of Schemes**:
  finite, proper, smooth, unramified, and étale morphisms.
- EGA IV for the classical source of the morphism-property package.
- Mathlib's existing `AlgebraicGeometry.Morphisms.*` files.

Formalization use:

- `IsFinite`, `IsProper`, `IsSmooth`, `IsEtale`, `Unramified`.
- Stability under composition and base change.
- Restricting a morphism over an open complement.
- Defining "unramified over `P^1 - {0,1,infinity}`" in terms of the restricted
  morphism.

Current Mathlib status:

- Several morphism properties already exist.
- This fork checks wrappers for finite, smooth, proper, and etale composition or
  base-change facts where Mathlib v4.15 exposes them directly.
- It also checks Mathlib's bridge from universally closed/proper morphisms to
  topologically proper underlying maps.
- The curve/divisor/ramification API needed to use them for Belyi maps does not
  yet exist as a coherent package.

### 4. Divisors, line bundles, and degree

Sources:

- Stacks Project, **Divisors** and **Properties** chapters.
- Stacks Project, **Effective Cartier divisors and invertible sheaves** tags.
- Hartshorne, **Algebraic Geometry**, Chapter II, Sections 5-7.
- Liu, **Algebraic Geometry and Arithmetic Curves**, Chapters 5 and 7.

Formalization use:

- Effective Cartier divisors from finite point sets on a smooth curve.
- Associated invertible sheaf `O(D)`.
- Tensor products, dual line bundles, and degree.
- Evaluation maps from global sections to fibers.

Mochizuki-specific use:

- If `D` is the sum of the prescribed set `T`, then `O_X(D)` has a section
  vanishing exactly on `D`.
- For `deg L >= 2g + 1`, section evaluation at points is surjective; equivalently
  `L(-x)` has vanishing `H^1`.

### 5. Cohomology, Serre duality, and Riemann-Roch

Sources:

- Stacks Project, **Cohomology of Schemes**, **Duality**, **Varieties**, and
  **Algebraic Curves**.
- Hartshorne, **Algebraic Geometry**, Chapter III and Chapter IV.
- Liu, **Algebraic Geometry and Arithmetic Curves**, Riemann-Roch for curves.
- Gabriel dos Santos, **The Riemann-Roch Theorem and Serre Duality** survey
  notes, useful as exposition but not as the primary formal source.

Formalization use:

- Coherent sheaf cohomology on proper schemes.
- `H^1(L(-x)) = 0` via Serre duality when the dual bundle has negative degree.
- Riemann-Roch for divisors/line bundles on curves.

Potential shortcut:

- For a first formalization, take the Riemann-Roch dimension formula for curves
  as the main imported theorem and avoid proving Serre duality until later.

### 6. Descent and fields of definition

Sources:

- André Weil, **The field of definition of a variety**.
- Pierre Dèbes and Michel Emsalem, **On fields of moduli of curves**.
- Pierre Dèbes and Jean-Claude Douai, **Algebraic covers: field of moduli versus
  field of definition**.
- Jeroen Sijsling and John Voight, **On explicit descent of marked curves and
  maps**, arXiv:1504.02814.

Formalization use:

- Galois-stable finite sets and divisors.
- Descent of marked maps or Belyi maps.
- Field-of-definition clauses for maps and automorphisms.

Recommended treatment:

- Avoid full descent initially by following Scherr-Zieve's field-aware
  construction over a perfect field or number field.
- Add Weil cocycles/descent only once the base theorem is checked.

### 7. Local fields and compactness for Corollary 3.2

Sources:

- Oliver Lorscheid, **Completeness and compactness for varieties over a local
  field**, arXiv:math/0410346.
- Cassels or Serre, **Local Fields** / **Corps locaux**.
- Stacks Project, proper morphisms and valuative criteria.

Formalization use:

- Completions of number fields at archimedean and nonarchimedean places.
- Finite extensions of local fields.
- Proper variety over a local field has compact local-point space.
- Compact images under continuous maps.

Recommended treatment:

- Do this after the algebraic Belyi theorem.  It is independent enough to be a
  later module.

### 8. Bottom layer: commutative algebra and topology

Sources:

- Stacks Project, **Algebra**, **More on Algebra**, **Modules**, **Divisors**.
- Atiyah-Macdonald, **Introduction to Commutative Algebra**.
- Eisenbud, **Commutative Algebra with a View Toward Algebraic Geometry**.

Formalization use:

- localization, integral extensions, finite modules;
- Kähler differentials;
- DVRs and local rings of smooth curves;
- tensor products and finite-dimensional vector spaces;
- finite unions of proper subspaces;
- compactness and finite-subcover arguments.

Much of this bottom layer already exists in Mathlib, but theorem names and API
shape must be audited before implementation.

## Gap-to-source matrix

The current formalization blockers in `FULL_PAPER_FORMALIZATION.md` split as
follows.

| Formalization gap | Best source to recurse to | Lean-facing target |
| --- | --- | --- |
| Smooth proper connected curves | Stacks Project, Algebraic Curves; Liu, Chapters 3-4 and 7 | A bundled curve structure over a field, eventually as a one-dimensional smooth proper connected scheme |
| `P^1` and rational functions | Stacks Project, Varieties/Morphisms; Hartshorne II.7; Vakil on maps to projective space | `P1 k`, points `0,1,infinity`, rational functions as morphisms where defined |
| Rational maps/function fields | Mathlib `AlgebraicGeometry.RationalMap`; Mathlib `AlgebraicGeometry.FunctionField`; Stacks Project rational maps and function fields | Checked dense-domain, representative, equivalence, and function-field reconstruction wrappers in `SourceStack.RationalMaps`; checked function-field injection/fraction-field/generic-point wrappers in `SourceStack.FunctionFields`; still needs curve-specific divisors/Riemann-Roch |
| Branch triple bookkeeping | Linear projectivization and finite-set arithmetic | Checked distinctness/membership/cardinality for `{0,1,infinity}` in `SourceStack.ProjectiveLine` |
| Complex finite-set separation | Mochizuki Lemma 2.3; elementary metric topology on `C`; density of `Q` in `R` | Checked in `SourceStack.ComplexSeparation`; still needs scheme `P^1` packaging |
| Finite image cardinality and pigeonhole | Elementary finite-set theory; Mochizuki Lemma 2.2 induction | Checked in `SourceStack.FiniteSet` |
| Lemma 2.1 auxiliary polynomial separation | Mochizuki Lemma 2.1; Belyi 1980 polynomial calculation | Checked real-polynomial ratio, positivity, scaled separation, and unit-interval separation consequences in `NoncriticalBelyi.Elementary`; still needs full `P^1` finite-set packaging |
| Finite morphisms to `P^1` | Stacks Project finite morphisms; Scherr-Zieve Proposition 2.1 | Checked general closed-immersion/finite/proper/separated/universally-closed stability and characterization wrappers in `SourceStack.Schemes`; still needs the curve-specific theorem that a nonconstant rational function on a proper curve induces a finite morphism |
| Branch locus and noncriticality | Stacks Project unramified/etale morphisms; SGA 1 for covers | Checked algebraic formal-unramified/formal-etale and separability source facts in `SourceStack.UnramifiedEtale`; still needs scheme-level unramified morphisms, branch locus, and finite-cover specialization |
| Divisors from finite point sets | Stacks Project Divisors; Liu Chapter 7; Hartshorne II.6 | Effective Cartier divisors on smooth curves and `O(D)` |
| Degree and canonical bundle | Stacks Project Algebraic Curves 53.4-53.5; Liu 7.3; Hartshorne IV | Degree of line bundles and `deg omega = 2g - 2` |
| Riemann-Roch spaces | Scherr-Zieve Lemma 2.2; Stacks Algebraic Curves 53.5; Liu 7.3 | `dim L(D)` and enough rational functions with prescribed poles |
| Basepoint-free/very ample line bundles | Vakil Class 44; Hartshorne IV.3; Stacks Algebraic Curves 53.7 | `deg L >= 2g` gives global generation; `deg L >= 2g+1` gives closed immersion |
| Finite union of proper subspaces | Linear algebra over finite/infinite fields; Scherr-Zieve Lemma 2.2 | Choose a section avoiding finitely many hyperplanes |
| Descent and field of definition | Weil; Dèbes-Emsalem; Dèbes-Douai; Sijsling-Voight | Galois-stable marked maps descend to the intended field |
| Local compactness in Corollary 3.2 | Lorscheid; Serre/Cassels local fields; Stacks properness | Checked compact image, finite subcover, and topological proper-map compact-preimage wrappers in `SourceStack.Topology`; checked p-adic and infinite-place completion compactness/local-compactness wrappers in `SourceStack.LocalFields`; still needs the algebraic theorem that proper varieties over arbitrary local fields have compact point spaces in the strong topology |
| Bottom algebra | Stacks Algebra/More on Algebra/Modules; Atiyah-Macdonald; Eisenbud | Localization, finite modules, integral extensions, Kahler differentials, DVRs |

This matrix is deliberately not only a reading list.  Each row identifies the
kind of theorem that must be present in Lean before the target paper can be
formalized without hiding content behind axioms.

## Recommended formalization path

1. Finish the elementary `P^1` rational-function layer:
   the remaining rational/scheme forms of Mochizuki Lemmas 2.1-2.4 plus
   Scherr-Zieve Lemmas 3.1-3.3.
2. Define a temporary `CurveLike` interface with divisors, Riemann-Roch spaces,
   genus, and finite morphisms to `P^1`; prove Scherr-Zieve Proposition 2.1
   against this interface.
3. Replace `CurveLike` assumptions with real scheme-theoretic definitions as
   Mathlib APIs are developed.
4. Define Belyi maps and Belyi opens using finite morphisms and unramified
   restrictions over `P^1 - {0,1,infinity}`.
5. Prove Scherr-Zieve Theorem 1.1 and Theorem 1.3.
6. Derive Mochizuki Theorem 2.5 and Corollaries 1.2 and 3.1.
7. Add the local-field compactness layer for Mochizuki Corollary 3.2.

This path recurses down to source material that is precise enough for Lean:
Stacks Project for scheme facts, Liu/Hartshorne/Vakil for curve-level proof
organization, and Scherr-Zieve for the theorem-level strategy closest to the
IUT-relevant Belyi input.
