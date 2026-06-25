# Assessment of `im1682_eng_backtranslated.pdf`

Source reviewed: Belyi, *On Galois Extensions of a Maximal Cyclotomic Field*.

## Relevant content

The paper contains the classical Belyi criterion on page 9:

> A complete nonsingular algebraic curve over a characteristic-zero field can be
> defined over the algebraic numbers iff it admits a cover of `P1` ramified over
> three points.

The proof also gives a polynomial reduction idea:

- start with a nonconstant rational function `t`;
- let `u` be the finite branch set;
- build iterated minimal-polynomial maps `f_u` that send the branch set to
  rational points;
- build maps `g_v` that send a finite rational set to `{0, 1, infinity}`;
- for a three-point set normalized to `{0, s, 1}`, use
  `(m + n)^(m+n) / (m^m n^n) * t^m * (1 - t)^n` with `s = m / (m + n)`.

This is mathematically relevant to the ordinary existence of Belyi maps and to
the elementary polynomial part already visible in Mochizuki's Lemma 2.1.

## What it does not provide

This paper does not provide the missing Lean/Mathlib infrastructure needed for
the full noncritical-Belyi formalization:

- no definitions or API for divisors, line bundles, canonical bundles, or degree
  on smooth proper curves;
- no Riemann-Roch or Serre-duality replacement for Mochizuki's construction of
  a finite morphism `X -> P1` unramified at a prescribed finite set;
- no formal theory of ramification/unramified-over-a-subset in scheme terms;
- no ready projective-line API tying rational functions to scheme morphisms;
- no control of prescribed noncritical points `T`;
- no locally compact completion machinery for Corollary 3.2.

The paper also relies on substantial external theorems, especially Riemann
existence and Weil descent.  Formalizing those from Mathlib would itself be a
major development.

## Impact on the plan

The paper is useful as a source for the ordinary Belyi theorem and for a
constructive polynomial reduction on `P1`.  It does not supply "everything else"
needed to formalize Mochizuki's full noncritical theorem.

The most realistic use is to add an optional milestone:

1. formalize Belyi's page-9 polynomial construction over `Polynomial Q`;
2. connect that to a function-field statement for curves once a curve and
   ramification API exists;
3. continue using Mochizuki's line-bundle/curve argument, or build an alternate
   Riemann-Roch-based construction, for prescribed noncritical points.
