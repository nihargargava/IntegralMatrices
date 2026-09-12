# Repository Guidelines

## Project Goal and Source of Truth

This project formalizes the two main results of `papers/katznelson.tex`: the fixed-rank asymptotic count for integral matrices over a number field and the convergence theorem for moments of lifts of codes. The checked-in TeX file is authoritative and will later be updated by the author. The introduction of `main.lean` should mention the paper as `arXiv:2510.11673`; do not replace the checked-in source with an arXiv download.

The completion target is a fully checked formalization conditional only on the
explicitly attributed Schmidt height-counting input
`HasHeightCountBounds`.  Schmidt's external theorem is outside the scope of
the preprint and need not be reproved to complete this project.  It must remain
an explicit argument of every theorem that uses it, never an axiom or hidden
instance.  A later unconditional wrapper is a separate supporting project and
may be reported as such only after that input has been proved.

## TeX Sources Are Read-Only

Never create, edit, reformat, regenerate, or apply patches to any `.tex` file, including `papers/katznelson.tex`. Inspect TeX only to align Lean statements and proofs with the paper. Report every suspected paper issue to the author with exact line numbers and a suggested correction; only the author updates the manuscript.

## Project Structure and Roadmap

`main.lean` is the public entry point. As the development grows, use focused modules for lattice geometry, admissible functions and Riemann sums, number-field structure, echelon matrices and Schmidt’s theorem, successive minima and matrix counting, fixed-rank asymptotics, and lifts of codes. Keep the paper and its reference PDF under `papers/`.

Follow the proof order in the paper: establish Voronoi, covering-radius, Minkowski, Hadamard, Riemann-sum, and number-field lattice lemmas; formalize the echelon-matrix trijection and tail estimates; prove the rank-induction counting argument; then prove `th:main` and `th:higher_moments`. Preserve the paper’s notation and hypotheses, including the `T^(k*n*d)` main term, `T⁻¹ log T` error, `𝓛(𝓟,s)`, and the echelon-integral limit.

Formal statements and proof interfaces must preserve the manuscript's notation,
not merely its mathematical content. In particular, retain named objects such
as `𝓕_l(T)`, `η(x)`, the cutoff `X`, and the displayed Abel-summation terms
when formalizing that argument. A different Lean representation may be used
internally for elaboration or elementary bookkeeping only if the surrounding
declaration includes an explicit, proved bridge back to the manuscript's
notation. Do not present a notation-changing reformulation as the
formalization of the paper's step.

If a cited paper or reference needed for a proof is inaccessible, stop at that point and ask the author to supply the relevant PDF. Do not reconstruct the missing result from memory or use an unverified substitute.

Attribute all mathematical results, definitions, proof ideas, quotations, references, and reused code or formalization correctly. Preserve the distinction between results proved in the checked-in paper, results taken from cited sources, and new Lean infrastructure or proofs developed here; include the appropriate citation or provenance in comments and notes when it is not already clear.

## Fidelity and Provenance Gates

The objective is to formalize and audit the argument in the paper, not merely to
find some proof of the same final theorem. Before adding a declaration, classify
it in a nearby comment as exactly one of:

- `paper`: a statement or proof step appearing in the checked-in TeX, with its
  theorem, lemma, or equation label and line reference;
- `cited input`: a result imported from a cited paper, with the accessible source
  PDF, exact theorem reference, and a statement of why its hypotheses and
  normalization match here;
- `derived consequence`: a theorem proved from already classified declarations,
  with the paper statements on which it depends;
- `Lean infrastructure`: a representation, reindexing, or elementary helper
  introduced solely to encode a paper object; and
- `scaffold`: an explicitly temporary `axiom`, `opaque`, `sorry`, or interface.

Do not silently turn an alternative argument into a formalization of the paper.
In particular, dyadic decompositions, replacement summation arguments, stronger
general lemmas, or other proof shortcuts must be marked `Lean infrastructure` or
`derived consequence` and must not be cited as coverage of a paper proof step.
When the paper uses a specific construction (for example echelon matrices), a
different representation (for example Grassmannian points) requires an explicit,
proved bridge to that construction before it can replace it in the public proof
path.

Do not silently replace the paper's norms, measures, heights, denominators, or
normalizations. A norm-equivalence or an unspecified constant is enough only for
a correspondingly coarse bound; it is not enough to identify an exact main-term
constant or a normalized limit. Record any such mismatch as an issue and keep the
affected theorem provisional.

Every imported theorem interface must remain visibly attributed and must not be
treated as a local proof merely because a source paper states it. Do not add
`axiom` declarations, hidden assumptions, or `sorry`-based substitutes. For
results outside the scope of the preprint, a named `Prop` hypothesis in a
clearly conditional development is permitted. In particular, the final public
path may depend explicitly on `HasHeightCountBounds`, the attributed interface
for Schmidt's external height-counting theorem, under the project-goal decision
above. For any other out-of-scope cited result, the Lean proof need not
reproduce the cited author's proof; any mathematically valid formalization is
acceptable. The source, exact role, and proof status must be recorded. A theorem
depending on `sorry`, `axiom`, or `opaque` remains unverified and cannot be
reported as a formalization of the paper.

Before reporting progress on a paper section, audit the new declarations against
the TeX and label each one using the categories above. If a faithful formalization
would require a result that is not in the paper or in an accessible cited source,
stop and ask the author for the relevant PDF or for direction; do not fill the
gap with a self-invented substitute.

## Reusing Formalization Libraries

Importing a compatible external Lean library, or copying/adapting focused code
from one, is permitted when it advances the formalization. Record the original
author, repository, exact revision, source path and line range, license, and
the mathematical role of every such reuse in both a nearby Lean comment and
`notes/source-attribution.md`. Preserve the distinction between reused Lean
infrastructure and a cited mathematical input.

If an otherwise suitable library is pinned to an incompatible Lean or Mathlib
revision, port only the audited declarations needed here and validate them in
this repository; do not describe version incompatibility as a prohibition on
future direct imports. A copied theorem still needs a local proof and its
provenance. External results may be exposed as named hypotheses only where the
project goal explicitly permits that conditional interface; no reuse may hide an
axiom, `sorry`, or `opaque` dependency.

## Build, Test, and Development Commands

- The project uses Lake with Mathlib `master` and Lean `v4.34.0-rc2` as recorded in `lean-toolchain`; use `lake build` for the full development.
- Use `lake build Katznelson/MainTheorems.lean` for a focused theorem-module check.
- Build the manuscript with `pdflatex -interaction=nonstopmode -halt-on-error papers/katznelson.tex` when its TeX dependencies are installed.

## Coding and Proof Standards

Use standard Lean 4/mathlib naming, two-space indentation, explicit namespaces, and `ℝ` rather than temporary scalar stand-ins. Keep definitions and lemmas close to the corresponding paper sections. Opaque interfaces and `sorry` are permitted only as temporary scaffolding; the completed public theorem path must contain genuine definitions and proofs with no `sorry`.

## Contributions

Validate each module before building on it, and check formal statements against the authoritative TeX source. Final validation is a clean `lake build` with no unresolved declarations or `sorry`s. Use concise imperative commit subjects (for example, `Formalize rank factorization`); pull requests should describe the mathematical section covered, proof status, validation commands, and any new Lean or TeX dependencies.
