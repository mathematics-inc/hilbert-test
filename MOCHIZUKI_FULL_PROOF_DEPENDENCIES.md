# Full Mochizuki proof dependency ledger

Target: formalize Mochizuki, **Noncritical Belyi Maps**, including Definition
1.1, Corollary 1.2, Lemmas 2.1-2.4, Theorem 2.5, Corollary 3.1, and Corollary
3.2, without `sorry`, `axiom`, or hidden theorem assumptions.

This file records the exact source material and Lean-facing theorem interfaces
still required.  It is intentionally stricter than a bibliography: each item must
eventually become a checked Lean declaration before the final paper can be
closed.

## Current checked state in this fork

The repository already contains Lean-checked sublayers that Hilbert can target:

- `HilbertTest.NoncriticalBelyi.Elementary`: elementary real inequalities from
  Mochizuki Lemma 2.1, including ratio bounds, unit-interval bounds, and
  domination of `beta` by the auxiliary polynomial at `beta >= 2`, plus the
  odd-case offset-ratio estimates and checked strict-separation consequences
  for positive points and unit-interval values.
- `HilbertTest.NoncriticalBelyi.Polynomial`: the algebraic `ℚ[X]` polynomial
  `X^m * (X - 1)^n` from Mochizuki Lemma 2.1, its endpoint values, formal
  derivative formula, factored derivative, and middle critical-point evaluation.
- `HilbertTest.Belyi1980.Polynomial`: the Belyi 1980 polynomial derivative,
  endpoint values at `0` and `1`, the middle critical point with derivative
  value `0`, normalized value `1`, and the middle-value positivity/`<= 1/4`
  bound used for Mochizuki Lemma 2.1, plus a packaged theorem combining the
  normalized endpoint values, middle criticality, and middle value.
- `HilbertTest.SourceStack.LinearAlgebra`: Scherr-Zieve finite-union avoidance
  for proper subspaces over an infinite field, the `finrank` inequality bridge
  from Riemann-Roch dimensions to proper subspaces, the finite nonzero
  linear-evaluation avoidance bridge used for Riemann-Roch spaces, and the
  common-kernel constrained vanishing/nonvanishing handoff; it also checks the
  finite-field cardinality-sum avoidance handoff used in Scherr-Zieve's
  positive-characteristic branch.
- `HilbertTest.SourceStack.FiniteSet`: finite image-cardinality drop and
  pigeonhole lemmas used in the Lemma 2.2 induction bookkeeping, including the
  four-distinguished-points-to-three-images cardinality-drop package; it also
  checks the Theorem 2.5 finite-enlargement step that an infinite point set lets
  one enlarge `T` past any prescribed cardinality while keeping it disjoint from
  a fixed finite set `S`.
- `HilbertTest.SourceStack.ComplexSeparation`: the finite complex-set
  separation step behind Mochizuki Lemma 2.3, including the reciprocal translate
  `z -> 1/(z - lambda)` and the rational-pole refinement when `beta` is
  rational.
- `HilbertTest.SourceStack.AffineSpace`: Mathlib affine-space wrappers showing
  that global coordinate sections define morphisms to affine space, pull back
  coordinates as expected, satisfy extensionality, identify over-morphisms with
  global sections, and are functorial in base and coordinates.
- `HilbertTest.SourceStack.ProjectiveLine`: linear projective-line points
  `0`, `1`, `infinity`, their distinctness, and the branch finset
  `{0,1,infinity}` with cardinality `3`, the corresponding finite branch set,
  plus affine points `[r:1]` and the four-point finset/set
  `{0,r,1,infinity}` with cardinality `4` when `r != 0,1`; affine coordinates
  are injective, every point is affine or infinity, and branch/four-point
  membership on the affine chart reduces to coordinate membership in `{0,1}`
  and `{0,r,1}`; if that four-point set maps into the
  branch triple, its image has strictly smaller cardinality and two of the four
  distinguished points have the same image; if a finite projective-line set
  contains the four-point set and maps into the branch triple, then the whole
  image has smaller cardinality, matching the Lemma 2.2 induction handoff; also
  the linear fractional
  reciprocal translate
  `[X:Y] -> [Y:X - lambda Y]` and its action on affine points, the pole, and
  infinity, plus affine-linear maps `[X:Y] -> [aX + bY:Y]` for `a != 0`; both
  classes of maps are checked as injective on projective points.
- `HilbertTest.SourceStack.ProjectiveSpectrum`: Mathlib `Proj` wrappers for
  projective basic opens, affine charts, affine-open chart ranges, affine
  basic opens, stalk localization, chart compatibility with the structure
  morphism, the canonical basic-open-to-`Spec` map on global sections, chart
  refinement maps, intersections of standard affine charts with projection
  identities, separatedness of `Proj`, and projective-spectrum
  zero-locus/vanishing-ideal topology.
- `HilbertTest.SourceStack.SchemeProjectiveLine`: the concrete scheme
  `P^1_K = Proj K[X0,X1]`, degree-one coordinate facts, the two standard
  affine chart open immersions, chart ranges and affine-open facts, the
  `D_+(X0 * X1)` overlap, the two-chart cover, separatedness of `P^1_K`,
  homogeneous coordinate ideals `(X0)`, `(X1)`, and `(X0-X1)`, and relevance
  witnesses showing the irrelevant ideal is not contained in any of these
  coordinate ideals.  It also checks polynomial-coordinate equivalences,
  primeness of these three ideals over a domain, and the resulting `Proj`
  points `[0:1]`, `[1:0]`, and `[1:1]`, packaged as a finite marked-point
  triple of cardinality three, with their expected membership/nonmembership in
  the two standard affine charts.
- `HilbertTest.SourceStack.MarkedProjectiveLine`: a common three-label index
  for the linear and scheme-theoretic marked triples, with image equalities to
  the existing finsets and injectivity of both label maps.
- `HilbertTest.SourceStack.SchemeMarkedBelyi`: specialization of the abstract
  finite-branch-set cover and noncritical-existence interfaces to the checked
  scheme-theoretic marked triple on `Proj K[X0,X1]`.
- `HilbertTest.SourceStack.RationalMaps`: Mathlib rational-map domain and
  partial-map representative wrappers, plus function-field reconstruction and
  uniqueness facts for rational maps out of integral schemes.
- `HilbertTest.SourceStack.FunctionFields`: Mathlib function-field wrappers for
  integral schemes, nonempty affine opens, affine schemes, stalk/function-field
  fraction-field identifications, generic-point membership and affine-chart
  identification, section/stalk/function-field scalar towers, and
  generic-point behavior under open immersions.
- `HilbertTest.SourceStack.ResidueFields`: Mathlib residue-field and stalk
  wrappers for point evaluations, empty basic opens by residue-field
  evaluation, evaluation naturality under scheme morphisms, residue-field maps
  and congruences, canonical morphisms `Spec O_{X,x} -> X` and
  `Spec kappa(x) -> X`, their ranges/functoriality and formulas on sheaves and
  global sections, specialization and open-subscheme compatibility,
  closed-point stalk isomorphisms for local rings, descent of local stalk maps
  to residue fields, reconstruction of local-ring-valued and field-valued
  points from closed-point stalk/residue-field maps, compatibility of
  `Spec kappa(x)` with `Spec O_{X,x}`, and equality criteria for field-valued
  and local-ring-valued points.
- `HilbertTest.SourceStack.StalkMaps`: Mathlib raw stalk-map wrappers for local
  homomorphism structure, identity/composition laws, specialization naturality,
  congruence under equal morphisms and equal source points, inverse identities
  for scheme isomorphisms, and germ compatibility.
- `HilbertTest.SourceStack.PullbackCarrier`: Mathlib scheme-pullback point
  wrappers for compatible point triplets over a base, residue-field tensor
  products, tensor-spectrum maps to pullbacks, reconstruction of pullback points
  from residue-field tensor data, carrier-equivalence and equality criteria,
  projection and pullback-map range formulas, existence of points above
  compatible pairs, and stability of surjectivity under base change.
- `HilbertTest.SourceStack.SurjectiveOnStalks`: Mathlib scheme-morphism
  wrappers for pointwise surjectivity of stalk maps, open-immersion examples,
  composition/base-change stability, source and target locality, the affine
  `Spec` criterion, descent from a surjective-on-stalks composite to the first
  morphism, and the pullback-to-product carrier embedding theorem.
- `HilbertTest.SourceStack.FieldTheory`: primitive-element, finite adjoin,
  separable-adjoin, minimal-polynomial degree, normality, Galois, splitting
  field, conjugacy-by-automorphism, normal-tower restriction wrappers, and the
  minimal-polynomial degree bound/derivative-root degree drop used in Lemma 2.4
  around Mathlib's field theory API.
- `HilbertTest.SourceStack.PolynomialMaps`: finiteness of derivative root sets,
  derivative-root membership by evaluation, finite polynomial images, and
  a named Lemma 2.4 replacement set `p(S) ∪ p(rootSet p')` with finiteness,
  inclusion, nonmembership, separation-from-`p(S)`, and noncritical-value
  derivative-nonvanishing wrappers; also composition evaluation and chain-rule
  derivative-nonvanishing wrappers.
- `HilbertTest.SourceStack.Schemes`: finite/smooth/proper/etale morphism
  stability wrappers around Mathlib, open-immersion composition/mono/etale/
  smooth/separated/finite-type wrappers, target-open restriction wrappers for
  finite/smooth/separated/proper/etale morphisms, closed-immersion and
  separated/universally closed bridges, finite-to-affine and
  finite-to-separated wrappers, plus the bridge from proper scheme morphisms to
  closed/topologically proper underlying maps, universally-closed
  restriction/quasi-compactness, and compactness of schemes universally closed
  or proper over a field.  It also checks
  quasi-separated composition/base-change and affine/terminal bridges, together
  with qcqs global-section localization and power-clearing lemmas on basic
  opens.
- `HilbertTest.SourceStack.UnramifiedEtale`: algebraic formal-unramified and
  formal-etale source facts, including the Kähler-differential characterization,
  square-zero lift uniqueness, composition/base-change stability, and
  separability equivalences over essentially finite type field extensions, plus
  ring-level unramified algebra wrappers for one-element localizations,
  composition, and base change, and formal-etale/etale algebra wrappers for
  algebra equivalences, localizations, localized bases, separable field
  extensions, and one-element localization.
- `HilbertTest.SourceStack.SmoothKaehler`: formal smooth lifting, polynomial
  formal smoothness, composition/base-change/localization stability, smooth
  algebra stability, Kähler-differential characterizations of formal smoothness,
  standard-smooth finite-presentation and relative-dimension stability, finite
  generation of differentials, and polynomial differential computations.
- `HilbertTest.SourceStack.Ramification`: ring-theoretic unramified algebra
  facts, the finite-type tensor-product criterion for formal unramifiedness,
  the distinguished tensor element identities, finite generation of free
  finite-type formally unramified algebras, flat/projective transfer along
  finite-type formally unramified algebras, Dedekind-domain ramification-index
  and inertia-degree facts, tower laws, the fundamental `sum e*f = [L:K]`
  identity, and valuation decomposition/inertia subgroup definitions.
- `HilbertTest.SourceStack.DedekindDvr`: dimension-one prime ideal facts,
  Dedekind-domain localization at primes, the theorem that nonzero prime
  localizations of a Dedekind domain are DVRs, the local-DVR definition of
  Dedekind domains, DVR uniformizers, prime-power ideal generation, and the DVR
  additive valuation laws.
- `HilbertTest.SourceStack.FractionalIdeals`: fractional-ideal arithmetic
  wrappers for coercing integral ideals, functorial maps, principal fractional
  ideals, denominator decomposition, ideal extension, and absolute norms.
- `HilbertTest.SourceStack.ArithmeticFunctionFields`: Mathlib's arithmetic
  function-field layer for finite extensions of `Fq(t)`, rings of integers as
  Dedekind domains under separability, and the valuation at infinity on `Fq(t)`.
- `HilbertTest.SourceStack.Cohomology`: generic abelian sheaf cohomology as Ext
  groups, cohomology presheaves, and the abelian category of sheaves of modules
  over a scheme.
- `HilbertTest.SourceStack.Topology`: compact image, finite-subcover facts,
  finite compact unions, compact product projections/products, and topological
  proper-map compact-preimage/composition/closed-map wrappers, including the
  finite union of coordinate projection images used to build the compact sets
  `H_v` in Corollary 3.2 and their containment in coordinatewise target
  subsets.  It now also checks the compact-exhaustion API for
  locally compact second-countable spaces and their open subspaces, including
  open exhaustions by interiors and compactness of the corresponding closures in
  Hausdorff spaces, together with the locally compact compact-neighborhood lemma.
- `HilbertTest.SourceStack.BelyiCovers`: abstract Belyi-open and Belyi-cover
  consequences from finite branch sets and continuous map families, including
  the Corollary 1.2 open-inside-complement step and the Corollary 3.1 finite
  extraction step over `X \ S`; it also exposes a `NoncriticalBelyiExistence`
  interface matching the finite disjoint-set conclusion of Theorem 2.5 and
  derives the pointwise tuple-cover hypothesis plus finite-set Belyi-open
  containment, explicit-complement, and open-with-finite-complement consequences
  of Corollary 1.2 from that interface.
- `HilbertTest.SourceStack.SchemeBelyi`: scheme-level abstract Definition 1.1
  wrappers for a target with a branch-complement open, dominant morphisms etale
  over that open, the preimage Belyi open, and the restriction/open-immersion
  identity for the Belyi open.
- `HilbertTest.SourceStack.LocalFields`: p-adic compactness, properness,
  second-countability, sigma-compactness, and compact-exhaustion wrappers, plus
  locally compact/second-countable/sigma-compact infinite-place completions,
  compact exhaustions, and real/complex infinite-place isometry models.
- `HilbertTest.HilbertSteps.*`: Hilbert-facing benchmark statements for those
  checked layers.
- `data/belyi_source_stack`, `data/belyi1980_polynomial`, and
  `data/mochizuki_elementary`: JSONL datasets in Hilbert's expected format.

## Theorem-level source stack

1. Mochizuki, **Noncritical Belyi Maps**.
2. Scherr-Zieve, **Separated Belyi Maps**.
3. Belyi, **On Galois Extensions of a Maximal Cyclotomic Field**.

Scherr-Zieve is the best theorem-level companion: it refines Mochizuki's
noncritical finite-set behavior and exposes a proof organization that separates
the curve reduction from the `P^1` construction.

## Required Lean modules and theorem interfaces

### A. Curves

Sources:

- Stacks Project, Algebraic Curves, especially curves/function fields and
  Riemann-Roch.
- Liu, **Algebraic Geometry and Arithmetic Curves**, Chapters 3, 5, and 7.
- Hartshorne, **Algebraic Geometry**, Chapters II-IV.
- Vakil, **Foundations of Algebraic Geometry**, line bundles and curves.

Lean-facing declarations needed:

- `SmoothProperConnectedCurve k`, implemented as a smooth proper connected
  one-dimensional scheme over a field.
- geometric/algebraic points `X(Qbar)` and finite subsets of such points.
  The general Mathlib equivalence between field-valued points `Spec K -> X`
  and a scheme point with a residue-field map is now checked in
  `SourceStack.ResidueFields`; the missing part is the specialized algebraic
  point API for curves over `Qbar`.
- base change of curves to field extensions.
- genus `genus X`.
- function field of a curve and rational functions.
  The scheme-theoretic function field of an integral scheme is checked in
  `SourceStack.FunctionFields`, and the arithmetic `Fq(t)`/ring-of-integers
  source layer is checked in `SourceStack.ArithmeticFunctionFields`; still
  missing is the specialization tying a smooth proper curve's function field to
  those arithmetic Dedekind-domain objects.
- nonconstant rational function `X -> P^1` induces a finite morphism.
  General quasi-compact scheme-morphism composition, base-change,
  compact-preimage, affine-target, terminal-morphism, finite, affine,
  integral, proper, quasi-separated, and qcqs section-localization wrappers are
  now checked in `SourceStack.Schemes`, including the bridge from integral plus
  locally finite type to finite and the direct finite-to-separated bridge.  The
  missing theorem is the curve-specific finite-morphism construction; pinned
  Mathlib also does not yet provide the integral/universally-closed bridge
  needed to derive finite-implies-proper.

### B. Divisors, line bundles, degree

Sources:

- Stacks Project, Divisors; Effective Cartier divisors and invertible sheaves.
- Stacks Project, Varieties, degrees on curves.
- Liu Chapter 7.
- Hartshorne II.5-II.7 and IV.

Lean-facing declarations needed:

- finite point set on a smooth curve gives a reduced effective Cartier divisor.
- associated invertible sheaf `O(D)`.
- canonical bundle `omega_X`.
- degree of divisors and line bundles on proper curves.
- `deg O(D) = card D` for reduced finite point divisors over `Qbar`.
- `deg omega_X = 2 * genus X - 2`.
- negative-degree line bundles on proper connected curves have no global
  sections.
The algebraic fractional-ideal arithmetic that will support Dedekind-domain
divisor calculations is now checked in `SourceStack.FractionalIdeals`; the
missing layer is the scheme/curve construction identifying point divisors and
line bundles with that algebraic arithmetic.

### C. Cohomology, Serre duality, Riemann-Roch

Sources:

- Stacks Project, Cohomology of Schemes, Duality, Algebraic Curves.
- Hartshorne III and IV.
- Liu 7.3.
- Gabriel dos Santos, **The Riemann-Roch Theorem and Serre Duality**, as
  exposition only.

Lean-facing declarations needed:

- coherent sheaf cohomology `H^i(X, F)` for proper schemes/curves.
  The generic sheaf-cohomology/Ext definition and abelian module-sheaf category
  are now checked in `SourceStack.Cohomology`; the missing part is the coherent
  sheaf cohomology specialization for algebraic curves.
- long exact cohomology sequence for short exact sequences of coherent sheaves.
- Serre duality for smooth proper curves:
  `H^1(X, L(-x))` dual to `Gamma(X, omega_X tensor L^{-1}(x))`.
- Riemann-Roch dimension formula:
  `ell(D) - ell(K-D) = deg D + 1 - genus X`.
- consequence: if `deg L >= 2g + 1`, evaluation
  `Gamma(X, L) -> L_x` is surjective for every point `x`.
- finite-family evaluation avoidance: choose a global section vanishing on one
  finite set and nonzero on another.  The infinite-field vector-space part, the
  `finrank` inequality-to-proper-subspace bridge, the generic
  nonzero-evaluation-to-proper-kernel bridge, and the common-kernel constrained
  vanishing/nonvanishing package are checked in `SourceStack.LinearAlgebra`; the
  missing part is connecting curve evaluation maps and actual Riemann-Roch
  dimension formulas to those linear forms.
The commutative-algebra smoothness/differential layer below smooth-curve
cohomology is now checked in `SourceStack.SmoothKaehler`, including
standard-smooth presentations and relative-dimension stability; the missing
layer is the geometric sheaf of differentials/canonical bundle and its curve
cohomology.

### D. Constructing the curve-to-`P^1` reduction

Sources:

- Mochizuki Theorem 2.5 proof.
- Scherr-Zieve Proposition 2.1 and Lemma 2.2.
- Vakil, maps to projective space from generated global sections.
- Stacks Project, linear series and morphisms to projective space.

Lean-facing declarations needed:

- two basepoint-free global sections of a line bundle define a morphism to
  `P^1`.  The affine analogue, where global coordinate sections define
  morphisms to affine space and determine them extensionally, is now checked in
  `SourceStack.AffineSpace`; the missing part is the projective/line-bundle
  version.
- if the induced rational function is nonconstant on a proper curve, the morphism
  is finite.
- pullback of `O(1)` is the chosen line bundle.
- if `s0` vanishes exactly on the reduced divisor `D = sum_{t in T} [t]`, then
  all points in `T` map to `0`.
- if `s1(t) != 0` for `t in T`, the morphism has no basepoints at `T`.
- reduced multiplicity-one vanishing implies unramified over `0`.
- if `S` is disjoint from `T`, then `0` is not in the image of `S`.

### E. Branch locus and Belyi maps

Sources:

- Stacks Project, Morphisms of Schemes: finite, unramified, etale, smooth.
- Stacks Project, Riemann-Hurwitz, for curve ramification bookkeeping.
- SGA 1, for covers if a cover-theoretic API is selected.

Lean-facing declarations needed:

- maximal open over which a finite morphism is unramified.
- branch locus of a finite morphism of curves.
- branch locus is finite for finite morphisms of smooth proper curves.
- `BelyiMap X` as a finite morphism `X -> P^1` unramified over the complement
  of `{0,1,infinity}`.
- behavior of branch loci under composition.
- composition with a `P^1 -> P^1` Belyi map preserves Belyi-ness.
The ring-theoretic ramification and inertia facts needed below this geometric
branch-locus layer are now checked in `SourceStack.Ramification`, and the
Dedekind/DVR local algebra underneath codimension-one ramification is checked in
`SourceStack.DedekindDvr`; open-immersion and target-open restriction wrappers
are checked in `SourceStack.Schemes`; the missing piece is still the
curve/scheme specialization that turns local ramification indices into
branch-locus statements for finite maps of smooth curves.

### F. `P^1` rational-function layer

Sources:

- Mochizuki Lemmas 2.1-2.4.
- Belyi 1980.
- Borisov, **On a Question of Craven and a Theorem of Belyi**.
- Deopurkar/Köck expositions of Belyi's theorem.

Lean-facing declarations needed:

- scheme-theoretic `P^1_k` connected to the linear projectivization layer.
  Mathlib's general `Proj` layer is now wrapped in
  `SourceStack.ProjectiveSpectrum`, including standard affine chart
  compatibility, canonical basic-open-to-`Spec` maps, chart refinement maps,
  and chart-intersection projection identities.  The specialized construction
  `P^1_k = Proj k[X,Y]` and its two standard affine charts are now checked in
  `SourceStack.SchemeProjectiveLine`, together with homogeneous coordinate
  ideals `(X0)`, `(X1)`, and `(X0-X1)`, relevance witnesses, primeness of all
  three coordinate ideals, and the `Proj` points `[0:1]`, `[1:0]`, and
  `[1:1]`, packaged as a finite marked-point triple with standard-chart
  membership facts; `MarkedProjectiveLine`
  now gives this scheme triple and the linear branch triple a shared injective
  three-label index.  `SchemeMarkedBelyi` now instantiates the abstract
  finite-branch-set cover interface with this scheme marked triple.  The
  missing item is the morphism/rational-function API using these marked points
  as the branch target.
- rational points `0`, `1`, `infinity` agree with the scheme points.
- polynomial/rational functions define morphisms `P^1 -> P^1`.
- critical points/critical values for `P^1 -> P^1` morphisms.
- derivative criterion for ramification of polynomial maps on affine charts.
- full scheme/`P^1` version of Mochizuki Lemma 2.1 over `Q`; the formal
  `ℚ[X]` derivative and critical-point calculation are checked, but the
  projective morphism and ramification packaging remains.
- Lemma 2.2 induction reducing finite rational sets.
- Lemma 2.3: the analytic complex finite-set separation, reciprocal translate
  estimate, rational-pole refinement, and linear-projectivization reciprocal
  translate/affine-linear maps are checked in `SourceStack.ComplexSeparation`
  and `SourceStack.ProjectiveLine`; still missing is the scheme-`P^1` morphism
  packaging.
- Lemma 2.4: Galois-stable induction on degree of algebraic points using minimal
  polynomials.  The underlying primitive-element, separability, normal/Galois,
  splitting, minimal-polynomial conjugacy, and derivative-root degree-drop facts
  are checked in `SourceStack.FieldTheory`; finite polynomial images and the
  named replacement-set API for `p(S) ∪ p(rootSet p')` are checked in
  `SourceStack.PolynomialMaps`, including the derivative-nonvanishing
  consequence away from the replacement set and the chain-rule nonvanishing
  wrapper for compositions; what remains is the `P^1(Qbar)` point/model layer
  and rational-map packaging needed to apply those field facts to Belyi maps.

### G. Field of definition and Galois conjugacy

Sources:

- Weil descent.
- Dèbes-Emsalem, **On fields of moduli of curves**.
- Dèbes-Douai, **Algebraic covers: field of moduli versus field of definition**.
- Sijsling-Voight, **On explicit descent of marked curves and maps**.

Lean-facing declarations needed:

- algebraic closure `Qbar`, number fields inside `Qbar`, and points defined over
  a number field.  Mathlib field-theory facts for finite/simple/Galois
  extensions are now wrapped in `SourceStack.FieldTheory`; this item is the
  geometric field-of-definition interface for curve and projective-line points.
- finite Galois-stable point sets and images under morphisms.
- minimal polynomial fields of definition for points of `P^1(Qbar)`.
- residue-field functoriality under scheme morphisms is now checked in
  `SourceStack.ResidueFields`; this still needs specialization to projective
  line coordinates and algebraic closures.
- if data are defined over a number field `F`, the constructed map can be chosen
  over `F`.

### H. Corollary 3.1: finite collection of maps

Sources:

- Mochizuki Corollary 3.1.
- Stacks Project, quasi-compactness of products/open covers.

Lean-facing declarations needed:

- finite products of curves and open complements `X \ S`.
- `Y = (X \ S)^n` is quasi-compact.
- for a Belyi map `phi`, the subset `U_phi` of points whose coordinate image
  avoids `{0,1,infinity}` is open and nonempty.
  The general topological part of openness is now checked in
  `SourceStack.Topology`: continuous preimages, finite intersections,
  complements of finite T1-subsets, and tuple-coordinate finite-avoidance
  loci.  The abstract cover extraction is now checked in
  `SourceStack.BelyiCovers`: pointwise existence of avoiding maps gives an
  indexed open cover, compactness extracts a finite subcover, and the
  complement version restricts to maps sending the fixed set `S` to the branch
  set.  The module also checks that a Theorem 2.5-style finite disjoint-set
  existence interface implies the needed pointwise tuple-cover hypothesis and
  finite-set Belyi-open containment, including the open-with-finite-complement
  Corollary 1.2 wrapper.  The
  missing part is the actual curve/Riemann-Roch construction instantiating that
  interface with genuine Belyi maps.
- Theorem 2.5 implies the family of all `U_phi` covers the relevant points.
- quasi-compactness gives a finite subcover.
  The scheme-level quasi-compact morphism composition/base-change/preimage
  facts, the compact-space/quasi-compact terminal morphism bridge, and
  universally-closed/proper-over-field compactness wrappers are now checked in
  `SourceStack.Schemes`; the remaining work is the curve-specific product/open
  complement construction and the Belyi-open family itself.

### I. Corollary 3.2: local compactness layer

Sources:

- Lorscheid, **Completeness and compactness for varieties over a local field**.
- Serre/Cassels, **Local Fields**.
- Stacks Project, proper morphisms.

Lean-facing declarations needed:

- completions of number fields at archimedean and nonarchimedean places.
- finite extensions of local fields.
- strong topology on `X(L)` for a variety over a local field.
- proper curve/product has compact local-point space.
- locally compact second-countable spaces admit compact exhaustions, with
  monotonicity, interior-containment, whole-space coverage, and eventual
  containment of compact subsets; open subspaces inherit such compact
  exhaustions, their interiors form an open exhaustion, and in Hausdorff spaces
  the closures of those interiors are compact.
- continuous image of a compact set is compact; finite unions of compact sets
  are compact; coordinate projections from product spaces preserve compactness.
  These topological steps, including finite unions of coordinate projection
  images, containment of those projection images in coordinatewise target
  subsets, and compact-exhaustion wrappers, are already checked in
  `SourceStack.Topology`; the proper-morphism-to-closed/proper-map bridge and
  field-valued universally-closed/proper compactness wrappers are checked in
  `SourceStack.Schemes`; topological proper-map compact-preimage facts are also
  checked in `SourceStack.Topology`; the missing step is the local-field point
  topology for arbitrary proper varieties and the full proper-variety compactness
  theorem.

## Dependency order for actual implementation

1. Finish the `P^1` rational-function layer:
   scheme `P^1`, polynomial maps, derivative/ramification criterion, the
   remaining rational/scheme forms of Lemmas 2.1-2.4.
2. Implement curve/divisor/line-bundle degree APIs.
3. Implement Riemann-Roch or import its curve-level consequences as checked
   Mathlib theorems.
4. Implement two-section morphisms to `P^1` and finite morphism/ramification
   behavior.
5. Prove Mochizuki Theorem 2.5.
6. Prove Corollary 3.1 from quasi-compactness.
7. Implement the local-field compactness bridge and prove Corollary 3.2.

Until items 2-4 exist in Lean, a no-axiom full proof of Theorem 2.5 cannot be
completed.  Hilbert can operate on each theorem once the statement is expressible
over available definitions, but it cannot replace absent definitions such as
divisors on smooth proper curves, Riemann-Roch spaces, or branch loci.
