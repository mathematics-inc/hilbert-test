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
  contained in `{0, 1, infinity}`.  The abstract scheme-level version with an
  arbitrary branch-complement open is now checked in
  `HilbertTest.SourceStack.SchemeBelyi`, including the marked `P1 K`
  branch-complement target, its source-open membership criterion, T1-specialized
  marked-target/source-open membership criteria, and a finite Belyi-map
  refinement with finite-restriction consequences.  The specialized
  ramification branch-locus API is still missing.
- Prove existence with prescribed finite-point behavior.
- Derive Zariski-base and finite-collection corollaries.  The abstract
  finite-branch-set topological consequences of these corollaries, including
  the explicit-complement and open-with-finite-complement Belyi-open steps for
  Corollary 1.2, finite-set Belyi-open containment, and the reduction from a
  Theorem 2.5-style finite disjoint-set source interface, are now checked in
  `HilbertTest.SourceStack.BelyiCovers`; the remaining target-layer work is to
  instantiate that interface with actual curve Belyi maps.
- The general residue-field/stalk representation of scheme points and
  field-valued points is now checked in
  `HilbertTest.SourceStack.ResidueFields`, including residue-field evaluation
  on basic opens, evaluation naturality, residue-field congruences, descent from
  local stalk maps, formulas for canonical stalk-spectrum maps on sheaves and
  global sections, open-subscheme and specialization compatibility, closed-point
  stalk isomorphisms for local rings, reconstruction of local-ring-valued and
  field-valued points, and equality criteria for field-valued and
  local-ring-valued point data; the remaining target-layer work is to specialize
  it to curve and `P^1(Qbar)` points.
- The raw stalk-map identities for scheme morphisms are now checked in
  `HilbertTest.SourceStack.StalkMaps`, including local-hom structure,
  identity/composition, specialization naturality, congruence for equal maps and
  equal source points, isomorphism inverse identities, and compatibility with
  germs; the remaining target-layer work is to use these identities in the
  branch/noncritical specialization for finite curve maps.
- The general scheme-pullback point carrier description is now checked in
  `HilbertTest.SourceStack.PullbackCarrier`, including compatible point
  triplets, residue-field tensor products, tensor-spectrum maps to pullbacks,
  reconstruction of pullback points, carrier-equivalence/equality criteria,
  projection and pullback-map range formulas, and surjective base change; the
  remaining target-layer work is to specialize these facts to curve products and
  geometric fibers of Belyi maps.
- The scheme-morphism source layer for maps surjective on stalks is now checked
  in `HilbertTest.SourceStack.SurjectiveOnStalks`, including pointwise stalk-map
  surjectivity, open-immersion examples, composition/base-change stability,
  source/target locality, affine criteria, and the pullback-to-product carrier
  embedding theorem; the remaining target-layer work is to relate these
  stalkwise morphism facts to finite curve maps, branch loci, and
  noncriticality.

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
  It also packages the induction handoff as an explicit smaller image finset
  containing every target image, with linear and concrete scheme-carrier
  Mochizuki four-point specializations.
  It also checks the infinite-point finite-enlargement step used at the start of
  Theorem 2.5 to enlarge `T` while keeping it disjoint from `S`.
- Fractional linear transformations with rational coefficients.  The linear
  projectivization layer now checks affine-linear maps
  `[X:Y] -> [aX + bY:Y]` for `a != 0`.
- Complex finite-set separation for reciprocal translates.  The analytic
  estimate and rational-pole refinement are checked in
  `HilbertTest.SourceStack.ComplexSeparation`, and the corresponding linear
  projective-line map `[X:Y] -> [Y:X - lambda Y]` is checked in
  `HilbertTest.SourceStack.ProjectiveLine`.  The strengthened variants choose
  the pole away from `beta - 1`, so the distinguished point maps away from all
  three marked projective points; `HilbertTest.SourceStack.ComplexSchemeSeparation`
  transports this to the concrete scheme carrier of `P^1`, including the
  rational-pole case.  The remaining work is to express these maps as honest
  scheme `P^1` morphism statements.
- General `Proj` infrastructure for the scheme-theoretic projective line.  This
  fork now checks Mathlib's projective basic opens, affine charts, chart ranges,
  stalk localization, chart compatibility with the structure morphism, the
  canonical basic-open-to-`Spec` map on global sections, chart refinement maps,
  intersections of standard affine charts with projection identities,
  separatedness, and zero-locus/vanishing-ideal topology wrappers in
  `HilbertTest.SourceStack.ProjectiveSpectrum`.  It now also checks the
  specialized scheme `P^1_K = Proj K[X0,X1]`, its two standard affine charts,
  their overlap, the two-chart cover, separatedness, homogeneous coordinate
  ideals `(X0)`, `(X1)`, and `(X0-X1)`, relevance witnesses, primeness of
  all three coordinate ideals over a domain, and the resulting `Proj` points
  `[0:1]`, `[1:0]`, and `[1:1]` in
  `HilbertTest.SourceStack.SchemeProjectiveLine`; it also packages these as a
  finite marked-point triple of cardinality three, re-exports that triple as a
  finset and finite set on the scheme carrier `P1 K`, and checks their
  standard-affine-chart membership.  The common-label bridge
  between this scheme triple and the linear projective-line branch triple is
  checked in `HilbertTest.SourceStack.MarkedProjectiveLine`, including the
  image set on the scheme carrier `P1 K`.  The full affine scheme-point family
  `[r:1]` and the concrete injective bridge from the linear point model to the
  scheme carrier are checked in
  `HilbertTest.SourceStack.SchemeAffineLinePoints`, and the abstract Belyi-cover
  finite-branch-set interface has been specialized to this scheme
  triple in `HilbertTest.SourceStack.SchemeMarkedBelyi`, including
  Corollary 1.2-style Belyi-open containment wrappers and Corollary 3.1-style
  pointwise-cover/finite-subcover wrappers, both for the raw projective-spectrum
  target and for maps whose target type is the scheme carrier `P1 K`, plus
  one-map partial/rational-map cover data and honest `C ⟶ P1 K`
  morphism-family cover/noncritical interfaces, and the bridge from scheme-level
  Belyi maps to the marked `P1 K` target back to the topological marked cover
  data, including the finite-map refinement.  It now also packages a
  paper-facing `FiniteMarkedBelyiExistence` family of finite scheme-level marked
  Belyi maps satisfying the finite disjoint-set condition, and proves the
  conversion from that family to marked cover/noncritical data, the resulting
  Corollary 1.2-style Belyi-open containment wrappers, and the finite-subcover
  wrapper.  Still missing is the curve theorem producing these
  finite marked Belyi-map families from rational functions with the marked
  points as branch targets.
- Polynomial/rational functions whose critical values are controlled.
- The explicit Belyi polynomial
  `(m+n)^(m+n)/(m^m*n^n) * t^m * (1 - t)^n`
  for a normalized triple `{0, m/(m+n), 1}`.  This algebraic polynomial layer
  is now checked in `HilbertTest.SourceStack.PolynomialMaps` over arbitrary
  characteristic-zero fields, including endpoint values, derivative
  factorization, middle criticality, middle value `1`, classification of
  affine critical points, and the fact that every affine critical value is `0`
  or `1`.  `HilbertTest.SourceStack.P1PolynomialSeparation` now lifts this to
  branch-triple membership for the affine-chart projective-line map
  `x |-> [B(x):1]`, and
  `HilbertTest.SourceStack.ConcretePolynomialSchemeSeparation` transports the
  same critical-point markedness statement to the concrete scheme carrier of
  `Proj K[X0,X1]`.
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
  a finite-dimensional vector space over an infinite field, the `finrank`
  inequality bridge from Riemann-Roch dimensions to proper subspaces, plus the
  generic bridge from nonzero linear evaluations to proper kernels and the
  common-kernel constrained vanishing/nonvanishing package.  The finite-field
  cardinality-sum avoidance handoff used by Scherr-Zieve is also checked.  The
  `CurveRiemannRoch` source layer now packages the infinite-field
  section-evaluation interface: if the curve/divisor theorem supplies nonzero
  restricted evaluations after imposing finite-set vanishing, the checked
  linear algebra gives a section vanishing on one finite set and nonzero on a
  disjoint finite set, with both `Finset` and finite-`Set` statement forms.  The
  `CurveBelyiConstruction` layer then shows that any section-controlled map
  family whose vanishing/nonvanishing behavior controls a finite branch set
  instantiates `NoncriticalBelyiExistence`.  The
  `SchemeCurveBelyiConstruction` layer specializes this to finite marked scheme
  Belyi maps, instantiates `FiniteMarkedBelyiExistence`, and exposes the
  Corollary 1.2-style Belyi-open containment wrappers, pointwise tuple-cover
  wrappers, and finite-subcover consequences directly.  The more specialized
  `ProjectiveSectionMaps` layer now checks the no-common-basepoint consequence
  from the two sections `s0,s1`, glues compatible local chart morphisms on an
  open cover into an honest global morphism `C -> P1 K`, descends the local
  zero-section criteria to that glued map, specializes the local maps to the
  actual two standard affine `P1` charts via `Proj.awayι`, constructs those
  local chart morphisms from local chart-coordinate ring maps by the `Γ-Spec`
  adjunction, tracks the pulled-back chart coordinate as the named local section
  ratio, records the local trivialization equation
  `ratio * denominator = numerator`, refines this to the unit-denominator
  construction `numerator * denominator⁻¹`, extracts the denominator unit from
  an `IsUnit` proof when that is the available local input, packages the result
  as a `ProjectiveLineSectionPair`, assembles finite marked families directly
  from trivialized ratio maps, including denominator-is-unit local ratio maps,
  whose finite Belyi maps agree with the glued maps, and proves that finite
  marked Belyi maps built from such pairs feed into the section-controlled
  finite marked bridge.  The
  `CurveDivisorSections` layer now checks the finite linear-avoidance step that
  chooses `s1` nonzero on the divisor support and derives the basepoint-free
  pair from the zero-section.  The `CurveCohomologySections` layer now checks
  that surjective point evaluations give nonzero evaluation functionals and
  therefore feed into the divisor-section package.  The `BelyiReduction` layer
  now constructs the bad target set `aux(S) ∪ badValues`, provides
  corresponding `P1ReductionStep` constructors, builds the composed finite
  Belyi map from a finite dominant auxiliary morphism and a finite Belyi map on
  `P1`, proves composite étaleness from auxiliary étaleness over the preimage
  of the marked branch-open, checks the composition-through-`P1` set control,
  and turns a family of reduction steps into `FiniteMarkedBelyiExistence`.  The inclusion-exclusion estimates remain
  separate.

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
  base-change facts where Mathlib v4.15 exposes them directly, plus
  finite-to-affine and finite-to-separated wrappers.
- The commutative-algebra layer for formal smoothness and Kähler differentials
  is checked in `HilbertTest.SourceStack.SmoothKaehler`, including nilpotent
  lifting, stability under base change/localization, Kähler characterizations of
  formal smoothness, standard-smooth finite-presentation and relative-dimension
  stability, and polynomial differential computations.
- It also checks Mathlib's bridge from universally closed/proper morphisms to
  closed and topologically proper underlying maps, plus compactness of schemes
  universally closed or proper over a field.
- The commutative-algebra layer for unramified algebras and ramification over
  Dedekind domains is checked in `HilbertTest.SourceStack.Ramification`,
  including the finite-type tensor-product criterion, the distinguished tensor
  element identities, finite generation of free finite-type formally
  unramified algebras, flat/projective transfer, ramification/inertia tower
  laws, the `sum e*f = [L:K]` identity, and decomposition/inertia subgroups of
  valuation subrings.
- The local algebra supporting codimension-one curve ramification is checked in
  `HilbertTest.SourceStack.DedekindDvr`: dimension-one prime behavior,
  Dedekind localization at nonzero primes, the concrete `Localization.AtPrime`
  DVR specialization, nonfield and nonzero/principal maximal-ideal consequences,
  DVR uniformizers, cotangent dimension one, prime-power ideals, and additive
  valuation laws.
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
- Compact images under continuous maps, finite compact unions, and compact
  product projections/products.
- Compact exhaustions of locally compact second-countable spaces, including the
  fact that compact subsets are eventually contained in the exhaustion.

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
| Maps from sections | Mathlib `AlgebraicGeometry.AffineSpace`; Stacks/Vakil maps to affine/projective space from sections | Checked affine-space `homOfVector`, coordinate pullback, over-morphism equivalence, affine-base spectrum identification, and functoriality in `SourceStack.AffineSpace`; checked the abstract `SectionControlledBelyiData` bridge in `SourceStack.CurveBelyiConstruction`, which turns section vanishing/nonvanishing control into `NoncriticalBelyiExistence`; checked the scheme-level `SectionControlledFiniteMarkedBelyiData` bridge in `SourceStack.SchemeCurveBelyiConstruction`, which instantiates `FiniteMarkedBelyiExistence` from finite marked Belyi maps controlled by section vanishing/nonvanishing and gives the Belyi-open, pointwise-cover, and finite-subcover outputs; checked `SourceStack.ProjectiveSectionMaps`, which proves the no-common-basepoint consequence for the two selected sections, glues compatible local chart morphisms on an open cover into an honest global morphism `C -> P1 K`, descends local zero-section criteria to the glued map, specializes the local maps to the actual two standard affine `P1` charts via `Proj.awayι`, constructs those local chart morphisms from local chart-coordinate ring maps by the `Γ-Spec` adjunction, tracks the pulled-back chart coordinate as the named local section ratio, records the local trivialization equation `ratio * denominator = numerator`, refines this to the unit-denominator construction `numerator * denominator⁻¹`, and now relies on the checked `SourceStack.Schemes` theorem that a denominator section restricts to an explicit unit on its own basic open and transports to the top sections of that open subscheme; checked `SourceStack.ProjectiveSectionMaps` also packages the result as a `ProjectiveLineSectionPair`, assembles finite marked families directly from trivialized ratio maps whose finite Belyi maps agree with the glued maps, and bridges finite marked Belyi maps built from such pairs into the section-controlled finite marked layer; checked `SourceStack.CurveDivisorSections`, which chooses the second section nonzero on a finite divisor support and derives the basepoint-free pair from the zero-section; checked `SourceStack.CurveCohomologySections`, which turns supportwise evaluation surjectivity into nonzero evaluation functionals and the divisor-section package; checked `SourceStack.BelyiReduction`, which constructs finite bad target sets, standard-set reduction-step constructors, and the composed finite Belyi map from a finite dominant auxiliary morphism plus a finite Belyi map on `P1`, proving composite étaleness from auxiliary étaleness over the marked branch-open preimage, then turns reduction-through-`P1` steps into `FiniteMarkedBelyiExistence`; still needs the actual line-bundle local chart construction and branch-control/finite-map theorem |
| `P^1` and rational functions | Stacks Project, Varieties/Morphisms; Hartshorne II.7; Vakil on maps to projective space | `P1 k`, points `0,1,infinity`, rational functions as morphisms where defined |
| Rational maps/function fields | Mathlib `AlgebraicGeometry.RationalMap`; Mathlib `AlgebraicGeometry.FunctionField`; Stacks Project rational maps and function fields | Checked dense-domain, representative, equivalence, and function-field reconstruction wrappers in `SourceStack.RationalMaps`, including direct variants for rational maps targeting scheme-theoretic `P1 K`, domain/restriction/local-stalk wrappers, and the named continuous dense-domain map for partial maps to `P1 K`; checked germ injectivity, generic-point membership, affine and affine-open fraction-field identifications, affine-chart generic-point identification, stalk/function-field fraction-field facts, and section/stalk/function-field scalar towers in `SourceStack.FunctionFields`; still needs curve-specific divisors/Riemann-Roch |
| Scheme points and residue fields | Mathlib `AlgebraicGeometry.ResidueField` and `Stalk`; Stacks Project points/stalks/residue fields | Checked evaluation, empty-basic-open criterion by residue-field evaluation, evaluation naturality, residue-field functoriality and congruence, `Spec O_{X,x}` and `Spec kappa(x)` maps, ranges, sheaf/global-section formulas for `Spec O_{X,x}`, specialization and open-subscheme compatibility, closed-point stalk isomorphisms for local rings, descent from local stalk maps, reconstruction of local-ring-valued and field-valued points from closed-point stalk/residue-field maps, `Spec kappa(x)`/`Spec O_{X,x}` compatibility, and field/local-ring-valued point equality criteria in `SourceStack.ResidueFields`; still needs algebraic-point specialization for curves and `P^1` |
| Scheme stalk maps | Mathlib `AlgebraicGeometry.Scheme`; Stacks Project stalk functoriality | Checked local-hom structure, identity/composition, specialization naturality, congruence for equal morphisms and equal source points, scheme-isomorphism inverse identities, and germ compatibility in `SourceStack.StalkMaps`; still needs branch/noncritical specialization for finite curve maps |
| Scheme pullback point carriers | Mathlib `AlgebraicGeometry.PullbackCarrier`; Stacks Project fiber products and residue fields | Checked compatible point triplets over a base, residue-field tensor products, tensor-spectrum maps to pullbacks, reconstruction of pullback points from residue-field tensor data, carrier-equivalence and equality criteria, projection and pullback-map range formulas, existence of pullback points over compatible point pairs, and surjectivity stability under base change in `SourceStack.PullbackCarrier`; still needs curve-product and Belyi-fiber specialization |
| Surjective-on-stalks morphisms | Mathlib `AlgebraicGeometry.Morphisms.SurjectiveOnStalks`; Stacks Project stalkwise morphism properties | Checked pointwise stalk-map surjectivity, open-immersion examples, composition/base-change stability, source and target locality, affine `Spec` criterion, descent from a surjective-on-stalks composite, and pullback-to-product carrier embedding in `SourceStack.SurjectiveOnStalks`; still needs branch-locus/noncritical specialization for finite curve maps |
| Branch triple and four-point bookkeeping | Linear projectivization and finite-set arithmetic | Checked distinctness/membership/cardinality for `{0,1,infinity}` and `{0,r,1,infinity}` in `SourceStack.ProjectiveLine`, including both finset and finite-set wrappers, injectivity of affine coordinates, the affine-or-infinity point classification, affine-chart membership tests for the branch and four-point sets, the image-cardinality drop when the four-point set maps into the branch triple, and the Lemma 2.2 package saying any finite set containing the four-point set has a strictly smaller image finset containing all target images when it maps into the branch triple; also checked injective reciprocal-translate and affine-linear projective maps used in Lemmas 2.3-2.4 |
| Scheme-theoretic projective line base | Mathlib `AlgebraicGeometry.ProjectiveSpectrum`; Stacks Project Proj/projective space | Checked general `Proj` basic opens, affine charts, chart ranges, stalk localization, chart compatibility with the structure morphism, the canonical basic-open-to-`Spec` map on global sections, chart refinement maps, standard-chart intersections with projection identities, separatedness, and projective zero-locus/vanishing-ideal topology in `SourceStack.ProjectiveSpectrum`; checked `P^1_K = Proj K[X0,X1]`, its two standard affine charts, chart ranges, chart overlap, two-chart cover, irrelevant-ideal containment, separatedness, homogeneous coordinate ideals `(X0)`, `(X1)`, and `(X0-X1)`, relevance witnesses, coordinate-ideal primeness, the `Proj` points `[0:1]`, `[1:0]`, and `[1:1]`, the finite marked-point triple of cardinality three, its finset/set aliases on the scheme carrier `P1 K`, and standard-chart membership facts in `SourceStack.SchemeProjectiveLine`; checked a shared injective three-label bridge between the linear and scheme marked triples in `SourceStack.MarkedProjectiveLine`, including the marked image set on the scheme carrier `P1 K`; checked the full affine scheme-point family `[r:1]`, its injectivity, marked-point compatibility, marked-triple membership criterion `r = 0 ∨ r = 1`, the scheme four-point set `{0,r,1,infinity}` with affine membership/cardinality facts, and the concrete linear-to-scheme point bridge in `SourceStack.SchemeAffineLinePoints`; checked point-level scheme transport of reciprocal and affine-linear transformations in `SourceStack.SchemeProjectiveLineTransform`, including transported injectivity/equality criteria; checked the abstract Belyi-cover finite-branch-set interface, Corollary 1.2-style open-containment wrappers, and Corollary 3.1-style finite-subcover wrappers specialized to this scheme triple in `SourceStack.SchemeMarkedBelyi`, including variants for maps targeting the scheme carrier `P1 K`, one-map cover data/open-locus facts on partial-map dense domains and rational-map canonical domains, cover/noncritical interfaces for honest `C ⟶ P1 K` morphism families, the marked `P1 K` branch-complement target, T1-specialized marked-target/source-open membership criteria, and finite Belyi-map refinement in `SourceStack.SchemeBelyi`, the bridge from scheme-level marked and finite marked Belyi maps to topological marked cover data, and a `FiniteMarkedBelyiExistence` interface converting finite marked Belyi-map families with Theorem 2.5-style finite disjoint-set behavior into Corollary 1.2 Belyi-open containment wrappers and the Corollary 3.1 finite-subcover output; still needs the full curve theorem producing the required morphisms/rational functions with branch control |
| Complex finite-set separation | Mochizuki Lemma 2.3; elementary metric topology on `C`; density of `Q` in `R` | Checked in `SourceStack.ComplexSeparation`, including strengthened pole avoidance so the distinguished point maps away from `0,1,infinity`; checked matching linear projective reciprocal and affine-linear maps in `SourceStack.ProjectiveLine`; checked point-level transport of those maps to scheme-carrier `P^1` in `SourceStack.SchemeProjectiveLineTransform`, including transported injectivity/equality criteria; checked concrete scheme-carrier finite-set separation, marked-set avoidance, scheme-infinity avoidance, and rational-pole variants in `SourceStack.ComplexSchemeSeparation`; still needs full scheme-morphism packaging |
| Finite image cardinality and pigeonhole | Elementary finite-set theory; Mochizuki Lemma 2.2 induction and Theorem 2.5 finite enlargement | Checked collision, subset-image drop, four-points-to-three-images cardinality-drop, explicit smaller-image induction handoff, and infinite-point finite-enlargement packages in `SourceStack.FiniteSet` |
| Algebraic point Galois conjugacy | Mathlib field theory; Stacks Project field extensions; standard primitive-element theorem | Checked primitive-element, finite adjoin, separability, normal/Galois, splitting, minimal-polynomial conjugacy, derivative-root degree-drop, and normal-tower restriction wrappers in `SourceStack.FieldTheory`; checked finite polynomial images and the named derivative-root replacement-set API, including membership, monotonicity, separation, derivative-nonvanishing away from the replacement set, and chain-rule nonvanishing under composition, in `SourceStack.PolynomialMaps`; checked the packaged selected-value separation and noncritical-preimage handoff in `SourceStack.PolynomialSeparation`; checked finite forbidden target set choice and conversion to a `P1` selected-value package in `SourceStack.PolynomialTargetAvoidance`; checked algebraically closed target-value realization and existence of a selected `beta` outside the forbidden set in `SourceStack.PolynomialValueSurjectivity`; checked the affine-chart linear projective-line transport in `SourceStack.P1PolynomialSeparation`; checked the abstract marked-label bridge to scheme-carrier `P1` and scheme-carrier transport in `SourceStack.P1SchemePointBridge`; checked the concrete scheme affine-point bridge in `SourceStack.SchemeAffineLinePoints`; checked the abstract and concrete composed scheme-carrier separation existence packages in `SourceStack.PolynomialSchemeSeparation` and `SourceStack.ConcretePolynomialSchemeSeparation`, including the concrete map `x |-> [p(x):1]` and branch-value membership criteria; still needs rational-map and morphism packaging to apply these field facts to Belyi maps |
| Lemma 2.1 auxiliary polynomial separation | Mochizuki Lemma 2.1; Belyi 1980 polynomial calculation | Checked real-polynomial ratio, positivity, scaled separation, and unit-interval separation consequences in `NoncriticalBelyi.Elementary`; checked the `ℚ[X]` endpoint, derivative, factored derivative, and middle critical-point calculation in `NoncriticalBelyi.Polynomial`; checked Belyi 1980's normalized auxiliary polynomial endpoints, middle criticality, unscaled middle-value product identity, positivity, and `<= 1/4` bound in `Belyi1980.Polynomial`; checked the arbitrary characteristic-zero normalized polynomial in `SourceStack.PolynomialMaps`, including critical-value containment in `{0,1}`, its affine-chart `P^1` branch-triple membership in `SourceStack.P1PolynomialSeparation`, and its concrete scheme-carrier markedness in `SourceStack.ConcretePolynomialSchemeSeparation`; still needs full scheme `P^1` finite-set/ramification packaging |
| Finite morphisms to `P^1` | Stacks Project finite morphisms; Scherr-Zieve Proposition 2.1 | Checked general closed-immersion/finite/proper/separated/universally-closed stability and characterization wrappers; checked affine and integral morphism composition/base-change/restriction, finite-to-affine, finite-to-separated, and finite iff integral plus locally finite type; checked quasi-compact, quasi-separated, compact-preimage, compact-space bridge, universally-closed/proper-over-field compactness, qcqs global-section localization wrappers, explicit basic-open unit restriction plus open-subscheme unit transport, the basic-open cover from a spanning family of sections, the two-section Bezout cover specialization, and the top-section restriction bridge for local representatives in `SourceStack.Schemes`; still needs the curve-specific theorem that a nonconstant rational function on a proper curve induces a finite morphism, and pinned Mathlib still lacks the integral/universally-closed bridge needed for finite-implies-proper |
| Branch locus and noncriticality | Stacks Project unramified/etale morphisms; SGA 1 for covers | Checked algebraic formal-unramified/formal-etale and separability source facts in `SourceStack.UnramifiedEtale`, plus ring-level unramified localization/composition/base-change wrappers and formal-etale/etale equivalence/localization/separable-field wrappers; checked open-immersion etale/smooth/separated/finite-type wrappers and target-open restriction stability in `SourceStack.Schemes`; still needs scheme-level unramified morphisms, branch locus, and finite-cover specialization |
| Divisors from finite point sets | Stacks Project Divisors; Liu Chapter 7; Hartshorne II.6 | Effective Cartier divisors on smooth curves and `O(D)` |
| Degree and canonical bundle | Stacks Project Algebraic Curves 53.4-53.5; Liu 7.3; Hartshorne IV | Degree of line bundles and `deg omega = 2g - 2` |
| Riemann-Roch spaces | Scherr-Zieve Lemma 2.2; Stacks Algebraic Curves 53.5; Liu 7.3 | Checked the abstract section-evaluation handoff in `SourceStack.CurveRiemannRoch`: finite-set vanishing as common-kernel membership, finite nonvanishing as pointwise nonzero evaluation, and a `RiemannRochFiniteEvaluationPackage` implying existence of a section vanishing on one finite set and nonzero on a disjoint finite set over an infinite field, both for `Finset`s and finite `Set`s; still needs the actual curve/divisor Riemann-Roch theorem instantiating that package |
| Basepoint-free/very ample line bundles | Vakil Class 44; Hartshorne IV.3; Stacks Algebraic Curves 53.7 | `deg L >= 2g` gives global generation; `deg L >= 2g+1` gives closed immersion |
| Finite union of proper subspaces | Linear algebra over finite/infinite fields; Scherr-Zieve Lemma 2.2 | Checked infinite-field finite-subspace avoidance, `finrank` inequality-to-proper-subspace bridge, nonzero-linear-form avoidance, common finite vanishing kernels, constrained vanish/nonvanish selection, and finite-field cardinality-sum avoidance in `SourceStack.LinearAlgebra`; still needs Scherr-Zieve's specialized finite-field inclusion-exclusion estimates if positive-characteristic finite fields are targeted |
| Descent and field of definition | Weil; Dèbes-Emsalem; Dèbes-Douai; Sijsling-Voight | Galois-stable marked maps descend to the intended field |
| Open-cover finite-subcover step in Corollary 3.1 | General topology compactness and finite branch-set complements | Checked compact-space finite-subcover wrappers and the topological openness of tuple-coordinate finite-avoidance loci in `SourceStack.Topology`; checked the abstract Belyi-cover finite extraction from pointwise avoidance, including the fixed-set complement version over `X \ S`, in `SourceStack.BelyiCovers`; still needs the curve-product quasi-compactness theorem and the Belyi-map cover/nonemptiness statement |
| Local compactness in Corollary 3.2 | Lorscheid; Serre/Cassels local fields; Stacks properness | Checked compact image, finite subcover, finite compact-union, product compactness/projection, finite unions of coordinate projection images plus coordinatewise target containment for the `H_v` construction, compact-exhaustion wrappers for spaces and open subspaces including open exhaustions by interiors and compact closure of interiors in Hausdorff spaces, locally compact compact-neighborhoods, and topological proper-map compact-preimage wrappers in `SourceStack.Topology`; checked scheme quasi-compact compact-preimage/compact-space bridge wrappers and universally-closed/proper-over-field topological compactness in `SourceStack.Schemes`; checked p-adic compact/proper/second-countable/sigma-compact/compact-exhaustion wrappers, finite-place completion norm/completeness/separability/second-countability wrappers plus conditional compact-exhaustion and sigma-compactness bridges under local compactness, and infinite-place completion local compactness, second countability, sigma compactness, compact exhaustions, and real/complex isometry models in `SourceStack.LocalFields`; still needs the algebraic theorem that proper varieties over arbitrary local fields have compact point spaces in the strong topology |
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
