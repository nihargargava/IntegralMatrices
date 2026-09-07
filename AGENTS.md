# Repository Guidelines

## Project Goal and Source of Truth

This project formalizes the two main results of `papers/katznelson.tex`: the fixed-rank asymptotic count for integral matrices over a number field and the convergence theorem for moments of lifts of codes. The checked-in TeX file is authoritative and will later be updated by the author. The introduction of `main.lean` should mention the paper as `arXiv:2510.11673`; do not replace the checked-in source with an arXiv download.

## TeX Sources Are Read-Only

Never create, edit, reformat, regenerate, or apply patches to any `.tex` file, including `papers/katznelson.tex`. Inspect TeX only to align Lean statements and proofs with the paper. Report every suspected paper issue to the author with exact line numbers and a suggested correction; only the author updates the manuscript.

## Project Structure and Roadmap

`main.lean` is the public entry point. As the development grows, use focused modules for lattice geometry, admissible functions and Riemann sums, number-field structure, echelon matrices and Schmidt’s theorem, successive minima and matrix counting, fixed-rank asymptotics, and lifts of codes. Keep the paper and its reference PDF under `papers/`.

Follow the proof order in the paper: establish Voronoi, covering-radius, Minkowski, Hadamard, Riemann-sum, and number-field lattice lemmas; formalize the echelon-matrix trijection and tail estimates; prove the rank-induction counting argument; then prove `th:main` and `th:higher_moments`. Preserve the paper’s notation and hypotheses, including the `T^(k*n*d)` main term, `T⁻¹ log T` error, `𝓛(𝓟,s)`, and the echelon-integral limit.

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
`axiom` declarations, hidden assumptions, or `sorry`-based substitutes. This
also applies to results outside the scope of the preprint, such as Schmidt's
external height-counting theorem: either formalize the needed result in Lean
(possibly in a separate supporting module), use an already verified library
theorem, or expose the result as an explicit hypothesis in a clearly conditional
development. The unconditional public theorem path must not depend on that
hypothesis. For an out-of-scope cited result, the Lean proof need not reproduce
the cited author's proof; any mathematically valid formalization is acceptable.
The source, exact role, and proof status must be recorded. A theorem depending
on `sorry`, `axiom`, or `opaque` remains unverified and cannot be reported as a
formalization of the paper.

Before reporting progress on a paper section, audit the new declarations against
the TeX and label each one using the categories above. If a faithful formalization
would require a result that is not in the paper or in an accessible cited source,
stop and ask the author for the relevant PDF or for direction; do not fill the
gap with a self-invented substitute.

## Build, Test, and Development Commands

- The project uses Lake with Mathlib `master` and Lean `v4.34.0-rc2` as recorded in `lean-toolchain`; use `lake build` for the full development.
- Use `lake build Katznelson/MainTheorems.lean` for a focused theorem-module check.
- Build the manuscript with `pdflatex -interaction=nonstopmode -halt-on-error papers/katznelson.tex` when its TeX dependencies are installed.

## Coding and Proof Standards

Use standard Lean 4/mathlib naming, two-space indentation, explicit namespaces, and `ℝ` rather than temporary scalar stand-ins. Keep definitions and lemmas close to the corresponding paper sections. Opaque interfaces and `sorry` are permitted only as temporary scaffolding; the completed public theorem path must contain genuine definitions and proofs with no `sorry`.

## Contributions

Validate each module before building on it, and check formal statements against the authoritative TeX source. Final validation is a clean `lake build` with no unresolved declarations or `sorry`s. Use concise imperative commit subjects (for example, `Formalize rank factorization`); pull requests should describe the mathematical section covered, proof status, validation commands, and any new Lean or TeX dependencies.
