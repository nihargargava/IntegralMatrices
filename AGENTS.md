# Repository Guidelines

## Project Goal and Source of Truth

This project formalizes the two main results of `papers/katznelson.tex`: the fixed-rank asymptotic count for integral matrices over a number field and the convergence theorem for moments of lifts of codes. The checked-in TeX file is authoritative and will later be updated by the author. The introduction of `main.lean` should mention the paper as `arXiv:2510.11673`; do not replace the checked-in source with an arXiv download.

## TeX Sources Are Read-Only

Never create, edit, reformat, regenerate, or apply patches to any `.tex` file, including `papers/katznelson.tex`. Inspect TeX only to align Lean statements and proofs with the paper. Report every suspected paper issue to the author with exact line numbers and a suggested correction; only the author updates the manuscript.

## Project Structure and Roadmap

`main.lean` is the public entry point. As the development grows, use focused modules for lattice geometry, admissible functions and Riemann sums, number-field structure, echelon matrices and Schmidt’s theorem, successive minima and matrix counting, fixed-rank asymptotics, and lifts of codes. Keep the paper and its reference PDF under `papers/`.

Follow the proof order in the paper: establish Voronoi, covering-radius, Minkowski, Hadamard, Riemann-sum, and number-field lattice lemmas; formalize the echelon-matrix trijection and tail estimates; prove the rank-induction counting argument; then prove `th:main` and `th:higher_moments`. Preserve the paper’s notation and hypotheses, including the `T^(k*n*d)` main term, `T⁻¹ log T` error, `𝓛(𝓟,s)`, and the echelon-integral limit.

## Build, Test, and Development Commands

- The project uses Lake with Mathlib `master` and Lean `v4.34.0-rc2` as recorded in `lean-toolchain`; use `lake build` for the full development.
- Use `lake build Katznelson/MainTheorems.lean` for a focused theorem-module check.
- Build the manuscript with `pdflatex -interaction=nonstopmode -halt-on-error papers/katznelson.tex` when its TeX dependencies are installed.

## Coding and Proof Standards

Use standard Lean 4/mathlib naming, two-space indentation, explicit namespaces, and `ℝ` rather than temporary scalar stand-ins. Keep definitions and lemmas close to the corresponding paper sections. Opaque interfaces and `sorry` are permitted only as temporary scaffolding; the completed public theorem path must contain genuine definitions and proofs with no `sorry`.

## Contributions

Validate each module before building on it, and check formal statements against the authoritative TeX source. Final validation is a clean `lake build` with no unresolved declarations or `sorry`s. Use concise imperative commit subjects (for example, `Formalize rank factorization`); pull requests should describe the mathematical section covered, proof status, validation commands, and any new Lean or TeX dependencies.
