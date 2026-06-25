# Hilbert formalization notes

The issue target is `artifacts/attachments/noncritical-belyi-maps_backtranslated.tex`,
which contains Mochizuki's *Noncritical Belyi Maps*.  I read the Hilbert paper
and used its workflow shape: decompose the informal text into smaller Lean
subgoals, check each subgoal with Lean, and assemble a verified file.

The released Hilbert repository expects:

- a prover LLM endpoint,
- an informal reasoner endpoint,
- Kimina Lean Server,
- Mathlib v4.15.0,
- an informal Mathlib retrieval cache.

This fork now contains a Lean 4.15.0 project with a checked Mathlib-backed
formalization of the elementary real-polynomial arithmetic used in Lemma 2.1 of
the TeX file.  The remaining results in the paper quantify over smooth proper
connected curves, morphisms to projective space, ramification loci, Belyi maps,
number fields, and local compactness.  They are recorded in the TeX source, but a
complete proof in Lean would require a dedicated algebraic-geometry development
rather than a direct Hilbert benchmark run.

Lean entry point:

```bash
lake build HilbertTest.NoncriticalBelyi.Elementary
```
