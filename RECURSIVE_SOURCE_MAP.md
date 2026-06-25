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
- The general residue-field/stalk representation of scheme points and
  field-valued points is now checked in
  `HilbertTest.SourceStack.ResidueFields`; the remaining target-layer work is
  to specialize it to curve and `P^1(Qbar)` points.

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
  that mapping into a strictly smaller finite target identifies two points; it
  also checks the projective-line specialization that the four distinguished
  points `{0,r,1,∞}` collide under any map into `{0,1,∞}` when `r != 0,1`.
- Fractional linear transformations with rational coefficients.  The linear
  projectivization layer now checks affine-linear maps
  `[X:Y] -> [aX + bY:Y]` for `a != 0`.
- Complex finite-set separation for reciprocal translates.  The analytic
  estimate and rational-pole refinement are checked in
  `HilbertTest.SourceStack.ComplexSeparation`, and the corresponding linear
  projective-line map `[X:Y] -> [Y:X - lambda Y]` is checked in
  `HilbertTest.SourceStack.ProjectiveLine`; the remaining work is to express
  these maps as scheme `P^1` morphism statements.
- General `Proj` infrastructure for the scheme-theoretic projective line.  This
  fork now checks Mathlib's projective basic opens, affine charts, chart ranges,
  stalk localization, and separatedness wrappers in
  `HilbertTest.SourceStack.ProjectiveSpectrum`; still missing is the specialized
  `P^1 = Proj k[X,Y]` API and marked-point identification.
- Polynomial/rational functions whose critical values are controlled.
- The explicit Belyi polynomial
  `(m+n)^(m+n)/(m^m*n^n) * t^m * (1 - t)^n`
  for a normalized triple `{0, m/(m+n), 1}`.
- Galois/normal-field descent for algebraic points on `P^1`.  The pure
  field-theory facts are now checked in `HilbertTest.SourceStack.FieldTheory`;
  the remaining part is the geometric bridge from algebraic projective-line
  points and rational maps to those field extensions.

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
- Arithmetic function-field facts for finite extensions of `Fq(t)`, rings of
  integers, and the infinity valuation are checked in
  `HilbertTest.SourceStack.ArithmeticFunctionFields`; the missing bridge is the
  algebraic-geometry identification of smooth curve function fields with this
  arithmetic model when appropriate.
- Global sections of a generated line bundle give a morphism to projective
  space.
- The affine-space analogue of maps from global coordinate sections is checked
  in `HilbertTest.SourceStack.AffineSpace`; the remaining geometric jump is the
  projective version from basepoint-free line-bundle sections.

Minimal theorem package needed:

- Divisors and degree on a proper smooth curve.
- Riemann-Roch in the form `ell(D) = deg(D) + 1 - g` for
  `deg(D) >= 2g - 1`.
- The vector-space lemma that a finite union of proper subspaces does not cover
  a finite-dimensional vector space over an infinite field, plus the generic
  bridge from nonzero linear evaluations to proper kernels.  The finite-field
  inclusion-exclusion variant used by Scherr-Zieve remains separate.

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
- The commutative-algebra layer for formal smoothness and Kähler differentials
  is checked in `HilbertTest.SourceStack.SmoothKaehler`, including nilpotent
  lifting, stability under base change/localization, Kähler characterizations of
  formal smoothness, standard-smooth finite-presentation and relative-dimension
  stability, and polynomial differential computations.
- It also checks Mathlib's bridge from universally closed/proper morphisms to
  topologically proper underlying maps.
- The commutative-algebra layer for unramified algebras and ramification over
  Dedekind domains is checked in `HilbertTest.SourceStack.Ramification`,
  including the tensor-product criterion, ramification/inertia tower laws, the
  `sum e*f = [L:K]` identity, and decomposition/inertia subgroups of valuation
  subrings.
- The local algebra supporting codimension-one curve ramification is checked in
  `HilbertTest.SourceStack.DedekindDvr`: dimension-one prime behavior,
  Dedekind localization at nonzero primes, DVR uniformizers, prime-power ideals,
  and additive valuation laws.
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
- Fractional-ideal arithmetic for Dedekind-domain divisor calculations is
  checked in `HilbertTest.SourceStack.FractionalIdeals`; what remains is the
  scheme/curve bridge from point divisors and line bundles to that algebra.

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
- Generic abelian sheaf cohomology and scheme module-sheaf categories are
  checked in `HilbertTest.SourceStack.Cohomology`; the curve/coherent
  specialization is still absent.
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
- Primitive elements, finite adjoining, separability of generated extensions,
  normal/Galois splitting, minimal-polynomial conjugacy by automorphisms, and
  restriction of automorphisms in a normal tower are already checked as
  bottom-layer field-theory source wrappers.

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
- Kähler differentials and standard-smooth presentations;
- DVRs and local rings of smooth curves;
- tensor products and finite-dimensional vector spaces;
- finite unions of proper subspaces and finite nonzero linear-form avoidance;
- compactness and finite-subcover arguments.

Much of this bottom layer already exists in Mathlib, but theorem names and API
shape must be audited before implementation.

## Gap-to-source matrix

The current formalization blockers in `FULL_PAPER_FORMALIZATION.md` split as
follows.

| Formalization gap | Best source to recurse to | Lean-facing target |
| --- | --- | --- |
| Smooth proper connected curves | Stacks Project, Algebraic Curves; Liu, Chapters 3-4 and 7 | A bundled curve structure over a field, eventually as a one-dimensional smooth proper connected scheme |
| Maps from sections | Mathlib `AlgebraicGeometry.AffineSpace`; Stacks/Vakil maps to affine/projective space from sections | Checked affine-space `homOfVector`, coordinate pullback, over-morphism equivalence, affine-base spectrum identification, and functoriality in `SourceStack.AffineSpace`; still needs the projective line-bundle version |
| `P^1` and rational functions | Stacks Project, Varieties/Morphisms; Hartshorne II.7; Vakil on maps to projective space | `P1 k`, points `0,1,infinity`, rational functions as morphisms where defined |
| Rational maps/function fields | Mathlib `AlgebraicGeometry.RationalMap`; Mathlib `AlgebraicGeometry.FunctionField`; Stacks Project rational maps and function fields | Checked dense-domain, representative, equivalence, and function-field reconstruction wrappers in `SourceStack.RationalMaps`; checked function-field injection/fraction-field/generic-point wrappers in `SourceStack.FunctionFields`; still needs curve-specific divisors/Riemann-Roch |
| Scheme points and residue fields | Mathlib `AlgebraicGeometry.ResidueField` and `Stalk`; Stacks Project points/stalks/residue fields | Checked evaluation, residue-field functoriality, `Spec O_{X,x}` and `Spec kappa(x)` maps, ranges, and field/local-ring-valued point equivalences in `SourceStack.ResidueFields`; still needs algebraic-point specialization for curves and `P^1` |
| Branch triple and four-point bookkeeping | Linear projectivization and finite-set arithmetic | Checked distinctness/membership/cardinality for `{0,1,infinity}` and `{0,r,1,infinity}` in `SourceStack.ProjectiveLine`, including the image-cardinality drop when the four-point set maps into the branch triple; also checked reciprocal-translate and affine-linear projective maps used in Lemmas 2.3-2.4 |
| Scheme-theoretic projective line base | Mathlib `AlgebraicGeometry.ProjectiveSpectrum`; Stacks Project Proj/projective space | Checked general `Proj` basic opens, affine charts, chart ranges, stalk localization, and separatedness in `SourceStack.ProjectiveSpectrum`; still needs the specialized `P^1 = Proj k[X,Y]` marked-point API |
| Complex finite-set separation | Mochizuki Lemma 2.3; elementary metric topology on `C`; density of `Q` in `R` | Checked in `SourceStack.ComplexSeparation`, with matching linear projective reciprocal and affine-linear maps in `SourceStack.ProjectiveLine`; still needs scheme `P^1` packaging |
| Finite image cardinality and pigeonhole | Elementary finite-set theory; Mochizuki Lemma 2.2 induction | Checked collision, subset-image drop, and four-points-to-three-images cardinality-drop packages in `SourceStack.FiniteSet` |
| Algebraic point Galois conjugacy | Mathlib field theory; Stacks Project field extensions; standard primitive-element theorem | Checked primitive-element, finite adjoin, separability, normal/Galois, splitting, minimal-polynomial conjugacy, and normal-tower restriction wrappers in `SourceStack.FieldTheory`; still needs `P^1(Qbar)` point/model bridge |
| Lemma 2.1 auxiliary polynomial separation | Mochizuki Lemma 2.1; Belyi 1980 polynomial calculation | Checked real-polynomial ratio, positivity, scaled separation, and unit-interval separation consequences in `NoncriticalBelyi.Elementary`; checked the `ℚ[X]` endpoint, derivative, factored derivative, and middle critical-point calculation in `NoncriticalBelyi.Polynomial`; still needs full scheme `P^1` finite-set/ramification packaging |
| Finite morphisms to `P^1` | Stacks Project finite morphisms; Scherr-Zieve Proposition 2.1 | Checked general closed-immersion/finite/proper/separated/universally-closed stability and characterization wrappers in `SourceStack.Schemes`; still needs the curve-specific theorem that a nonconstant rational function on a proper curve induces a finite morphism |
| Branch locus and noncriticality | Stacks Project unramified/etale morphisms; SGA 1 for covers | Checked algebraic formal-unramified/formal-etale and separability source facts in `SourceStack.UnramifiedEtale`; still needs scheme-level unramified morphisms, branch locus, and finite-cover specialization |
| Divisors from finite point sets | Stacks Project Divisors; Liu Chapter 7; Hartshorne II.6 | Effective Cartier divisors on smooth curves and `O(D)` |
| Degree and canonical bundle | Stacks Project Algebraic Curves 53.4-53.5; Liu 7.3; Hartshorne IV | Degree of line bundles and `deg omega = 2g - 2` |
| Riemann-Roch spaces | Scherr-Zieve Lemma 2.2; Stacks Algebraic Curves 53.5; Liu 7.3 | `dim L(D)` and enough rational functions with prescribed poles |
| Basepoint-free/very ample line bundles | Vakil Class 44; Hartshorne IV.3; Stacks Algebraic Curves 53.7 | `deg L >= 2g` gives global generation; `deg L >= 2g+1` gives closed immersion |
| Finite union of proper subspaces | Linear algebra over finite/infinite fields; Scherr-Zieve Lemma 2.2 | Checked infinite-field finite-subspace avoidance and nonzero-linear-form avoidance in `SourceStack.LinearAlgebra`; still needs finite-field counting if positive-characteristic finite fields are targeted |
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
