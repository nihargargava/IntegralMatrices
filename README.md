# Formalization of Integral Matrices of Fixed Rank

This repository is a Lean 4 formalization of the preprint
[*Integral matrices of fixed rank over number fields*](https://arxiv.org/abs/2510.11673)
by Nihar Gargava, Vlad Serban, Maryna Viazovska, and Ilaria Viglino.

The project follows the notation and proof strategy of the paper. Its two main
targets are:

1. the asymptotic count of fixed-rank matrices over the ring of integers of a
   number field, with the stated `T⁻¹ log T` error; and
2. the convergence theorem for moments over lattices obtained from lifts of
   algebraic codes.

> [!IMPORTANT]
> This formalization is under active development. The public theorem statements
> are present in `main.lean`, but their final proofs are not yet complete.

## Current status

The completed, machine-checked infrastructure includes:

- Euclidean Minkowski embeddings and integral matrices over number fields;
- admissible functions, compact-support finiteness, and lattice summability;
- finite-field Grassmannian counts and code-containment estimates;
- rank-drop estimates for reduction modulo prime ideals;
- decomposition of fixed-rank matrices by rational row space;
- primitive row lattices and denominator-clearing span results; and
- general, controlled, subspace, and row-matrix lattice Riemann-sum estimates.

The main remaining work consists of the successive-minima and lattice-product
geometry, echelon parametrization and Schmidt estimates, the fixed-rank
induction, and the final lifts-of-codes convergence argument. Temporary opaque
interfaces and the two final `sorry`s are tracked explicitly in the source.

## Formalization roadmap

- [x] State both main results in `main.lean` using the paper's notation and
  hypotheses.
- [x] Define the number-field, Euclidean, integral-matrix, prime-ideal, code,
  and lifted-lattice foundations.
- [x] Formalize admissible functions, support bounds, summability, and general
  lattice Riemann-sum estimates.
- [x] Prove the finite-field Grassmannian counts and uniform code-containment
  probability estimates.
- [x] Prove the rank-drop bounds for reduction modulo a prime ideal.
- [x] Decompose rank-`k` matrices by rational row space and construct the
  associated primitive integral row lattice.
- [x] Prove that the primitive row module spans its rational row space over
  both `K` and `ℚ`.
- [ ] Complete the row-lattice geometry.
  - [ ] Integrate the tested formula
    `finrank ℝ (rowRealSpan V) = k * degree K`.
  - [ ] Identify the `n`-row matrix space with the corresponding finite
    product of row spaces.
  - [ ] Prove the matrix-space dimension, covolume, and fundamental-radius
    formulas.
  - [ ] Match the normalized measure, height, denominator, and Jacobian with
    the manuscript definitions.
- [ ] Formalize the remaining geometry-of-numbers preliminaries.
  - [ ] Voronoi domains and covering-radius estimates.
  - [ ] Minkowski and Hadamard inequalities in the required normalization.
  - [ ] Successive minima for number-field lattices.
- [ ] Complete the matrix parametrization and subspace summation.
  - [ ] Define reduced-row-echelon representatives over `K`.
  - [ ] Prove the paper's echelon-matrix/row-space/lattice trijection.
  - [ ] Define and analyze the denominator `𝔇(D)`.
  - [ ] Formalize the required Schmidt counting estimate.
  - [ ] Prove convergence and tail bounds for the echelon sum.
- [ ] Prove the fixed-rank counting theorem.
  - [ ] Bound row spaces that interact with the support of `f`.
  - [ ] Establish the possible-successive-minima estimates.
  - [ ] Control the lower-rank terms.
  - [ ] Carry out the rank induction and sum over row spaces.
  - [ ] Identify the main constant and prove the `T⁻¹ log T` error.
  - [ ] Prove the no-logarithm refinement outside the exceptional case.
- [ ] Prove convergence for lifts of codes.
  - [ ] Expand the finite code average and group matrices by rank.
  - [ ] Control rank-drop and vanishing terms under the lift scaling.
  - [ ] Apply the fixed-rank asymptotic to each surviving rank.
  - [ ] Identify the limit with the convergent echelon-integral sum.
- [ ] Finish and audit the formalization.
  - [ ] Replace all temporary opaque interfaces with definitions and proofs.
  - [ ] Remove both public theorem `sorry`s.
  - [ ] Remove scratch files and resolve nonessential linter warnings.
  - [ ] Run a clean `lake build` and audit statements against the manuscript.

## Building the project

Install [elan](https://github.com/leanprover/elan) and Git, then clone the
repository. Elan will select the Lean version pinned in `lean-toolchain`
(`v4.34.0-rc2`). The Mathlib revision is recorded in `lake-manifest.json`.

```bash
lake exe cache get
lake build
```

Useful focused checks include:

```bash
lake build main
lake build Katznelson.Counting.RowLattice
lake build Katznelson.Counting.RowLatticeRiemann
```

Run `lake update` only when intentionally updating the Mathlib dependency.

## Repository layout

| Path | Contents |
| --- | --- |
| `main.lean` | Public statements of the two main theorems |
| `Katznelson/Foundations.lean` | Number-field, matrix, embedding, and norm conventions |
| `Katznelson/Counting/` | Finite-field, rank, row-space, lattice, and Riemann-sum arguments |
| `Katznelson/Lifts.lean` | Codes, lifted lattices, scaling, and moment definitions |
| `Katznelson/MainTheorems.lean` | Assembly layer and temporary theorem interfaces |
| `papers/katznelson.tex` | Authoritative manuscript used to align statements and proofs |
| `AGENTS.md` | Contributor workflow, roadmap, and coding conventions |

## Formalization policy

Proofs should follow the manuscript closely enough that the formal development
also checks the paper's argument. Preserve its notation where practical and
record the corresponding theorem, lemma, or equation label in comments.

All `.tex` files are strictly read-only in this repository. If a manuscript
issue is discovered, report its exact line numbers and a suggested correction;
do not edit the TeX source.

## Contributing

Contributions are welcome, especially self-contained Mathlib lemmas and work on
the next roadmap milestone. Before opening a pull request:

1. read `AGENTS.md`;
2. keep changes focused on one mathematical component;
3. run the relevant focused build and, when practical, `lake build`; and
4. state which part of the paper is covered and whether any scaffolding remains.

Please do not present the repository as a completed verification until both
public theorems build without `sorry` or opaque proof placeholders.
