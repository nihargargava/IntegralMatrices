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
> are present in `main.lean`, but the end-to-end proofs are not yet complete.

## Current status

The current, machine-checked infrastructure includes:

- Euclidean Minkowski embeddings and integral matrices over number fields;
- admissible functions, compact-support finiteness, and lattice summability;
- finite-field Grassmannian counts and code-containment estimates;
- rank-drop estimates for reduction modulo prime ideals;
- decomposition of fixed-rank matrices by rational row space;
- primitive row lattices and denominator-clearing span results; and
- general, controlled, subspace, and row-matrix lattice Riemann-sum estimates;
- a general lattice ball-volume estimate and a finite rank-filtered lattice
  sum bound, giving the corrected inequality used in the manuscript's
  low-rank inner-sum step;
- the product equivalence for the `n`-row lattice, its dimension
  `n * (k * degree K)`, and the corresponding reciprocal-power summability
  result; and
- ordinary height shells with finiteness, polynomial cardinality bounds, and
  the unit-shell Abel/summation-by-parts route to the sharp `p < q`
  reciprocal-height summability consequence, including the finite height-
  interval comparison and a quantitative ordinary-shell Abel estimate;
- the elementary positive-interval integral identities and the resulting
  three-case finite ordinary-shell bound needed for the low-rank estimate;
- the paper-side absolute-summability interface: a reciprocal-height
  domination hypothesis now yields summability of the corresponding matrix or
  subspace summands, together with the resulting qualitative vanishing of
  moving height tails;
- the manuscript's reduced-row-echelon type, the direct definition of
  `Λ_D`, the real row-set `M_n(Λ_D)`, and a proved equality between the direct
  and row-lattice definitions of `𝓕_l(T)`; and
- uniqueness and existence of the manuscript's reduced-row-echelon
  representative for every finite-dimensional row space, proved by induction
  on the number of columns; the proof includes the zero-rank base case, the
  zero-first-coordinate lift, and the normalized pivot-row construction; and
- the denominator module from the paper's index definition, including the
  common-denominator clearing lemma, the reduced-pivot coefficient lemma, and
  the exact `n`-fold product index for its coefficient module, together with
  the proved ambient-index identity corresponding to equation (21); and
- the manuscript-facing unrestricted `M_n(Λ_D)` Riemann estimate, obtained
  by the explicit direct-to-row-lattice reindexing and the proved matrix-space
  dimension formula; and
- the rank-zero row-matrix base case and the positive lower-rank induction
  split; and
- the exact finite-family lower-rank overcount identity, with each lower-rank
  matrix regrouped by its own row space and weighted by the number of chosen
  rank-k row spaces containing it.

The main remaining work is the quantitative geometry of the row lattices,
the exact normalization of measures and heights, the echelon-tail estimates,
the fixed-rank induction, and the final lifts-of-codes argument. The current
temporary interfaces are explicit in the source:

- `main.lean` has one public `sorry`, in `fixed_rank_count`;
- `Katznelson/Counting/Schmidt.lean` contains height-counting consequences
  parameterized by an explicit `HasHeightCountBounds` hypothesis.  Schmidt's
  theorem itself is not currently an axiom or a hidden assumption; its Lean
  proof remains supporting work outside the preprint's main scope.

Consequently, a successful Lean build means that the present statements and
infrastructure typecheck; it does not yet mean that the two main theorems
have been completely verified from definitions and proofs.

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
- [x] Define the manuscript's echelon matrices and direct `Λ_D`/`M_n(Λ_D)`
  support family, and prove its equality with the row-space implementation of
  `𝓕_l(T)`.
- [x] Prove that the primitive row module spans its rational row space over
  both `K` and `ℚ`.
- [x] Prove the real-span dimension formula
  `finrank ℝ (rowRealSpan V) = k * degree K`.
- [x] Identify the `n`-row matrix space with the corresponding finite product
  of row spaces and prove the matrix-space dimension formula.
- [x] Formalize finite ordinary height-shell bounds and the paper-aligned
   Abel/summation-by-parts `p < q` reciprocal-tail consequence of the
   polynomial count, including the positive/logarithmic/bounded exponent
   cases needed by the low-rank sum.
- [ ] Prove the product formulas for matrix-lattice covolumes and fundamental
   radii.
- [ ] Specialize the general ball-volume estimate to the row-matrix lattice
   after resolving the expensive matrix/subtype measure normalization in Lean.
- [ ] Match the normalized measure, height, denominator, and Jacobian with
  the manuscript definitions.
- [ ] Formalize the remaining geometry-of-numbers preliminaries.
  - [ ] Voronoi domains and covering-radius estimates.
  - [ ] Minkowski and Hadamard inequalities in the required normalization.
  - [ ] Successive minima for number-field lattices.
- [ ] Complete the matrix parametrization and subspace summation.
  - [x] Define reduced-row-echelon representatives over `K`, and prove the
    bijection with `Grassmannian K m l` by row space.
  - [x] Define the denominator module, prove its finiteness/positivity, and
    identify the image index with `M_n(Λ_D)` as in equation (21).
  - [ ] Discharge the explicit Schmidt height-counting hypothesis with a
    genuine supporting formalization.
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
  - [ ] Remove the remaining public theorem `sorry`.
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

Mathematical results and proof ideas are attributed to their sources. Schmidt's
1967 paper is the source of the original number-field height-counting argument;
Thunder's 1992 paper is recorded as an effective asymptotic refinement. The
corresponding local PDFs are kept in `papers/`, and source notes are kept in
`notes/`. If a cited paper cannot be accessed, stop and request that the author
provide a PDF rather than reconstructing the argument from memory.

## Contributing

Contributions are welcome, especially self-contained Mathlib lemmas and work on
the next roadmap milestone. Before opening a pull request:

1. read `AGENTS.md`;
2. keep changes focused on one mathematical component;
3. run the relevant focused build and, when practical, `lake build`; and
4. state which part of the paper is covered and whether any scaffolding remains.

Please do not present the repository as a completed verification until both
public theorems build without `sorry` or opaque proof placeholders.
