# Formalization of Integral Matrices of Fixed Rank

This repository formalizes the preprint [*Integral matrices of fixed rank over
number fields*](https://arxiv.org/abs/2510.11673) by Nihar Gargava, Vlad
Serban, Maryna Viazovska, and Ilaria Viglino. The checked-in source
[`papers/katznelson.tex`](papers/katznelson.tex) is the authoritative version
used by the formalization.

The project has two targets:

1. the fixed-rank asymptotic count for integral matrices over a number field,
   with main scale `T^(k*n*degree K)`, error `O(T⁻¹ log T)`, and the stated
   no-log refinement; and
2. convergence of moments for lifts of algebraic codes to the echelon-integral
   expression in Theorem `th:higher_moments`.

## Status

Both public theorem paths in [`main.lean`](main.lean) are machine checked.
There are no `sorry`, `axiom`, or `opaque` declarations in the development.
Where the audit found a mathematical error in the current TeX, the exact
location and proposed correction are recorded in
[`notes/paper-issues.md`](notes/paper-issues.md); the Lean development follows
the author's approved corrected reading while the corresponding manuscript
edits are pending.

The fixed-rank theorem is conditional on the explicit argument
`HasHeightCountBounds`, which is the polynomial upper-count interface used
from Schmidt's external height-counting theorem for the intermediate ranks
`1 ≤ l < m`. This is intentional: Schmidt's theorem is outside the scope of
the preprint and is exposed as a hypothesis rather than hidden as an axiom.
The full-rank Grassmannian is a singleton and is handled internally.

The checked development now includes:

- the number-field matrix spaces, integral embeddings, and the manuscript's
  discriminant/trace normalization;
- admissible functions, compact-support finiteness, and controlled lattice
  Riemann sums;
- Voronoi domains, covering radii, Hadamard and Minkowski estimates;
- number-field successive minima and the Fieker--Stehlé block-selection
  argument;
- reduced-row-echelon representatives and their equivalence with rational
  Grassmannian points;
- the paper's denominator module and its exact `n`-fold index;
- the exact bridge between `𝓕_l(T)` and the bounded row-space family;
- Schmidt/Abel ordinary-shell estimates with the manuscript's literal
  counting function `η(x)`, cutoff `X`, `alpha_l`, and `B_l(T)` bookkeeping;
- the literal termwise-absolute lower-rank and height-tail estimates;
- the rank-induction and final error assembly;
- the absolute convergence and exact identity
  `mainConstant = ∑_D 𝔇(D)⁻ⁿ ∫ f(xD) dx`; and
- a proved equivalence between codes and the literal family `𝓛(𝓟,s)`, a
  proved equivalence between integral representatives and each literal
  Cartesian power `Λ^m`, and the resulting manuscript-facing average;
- the finite-field rank grouping, scaling limit, and literal echelon-integral
  limit for the higher-moment theorem; and
- the finite-index and covolume calculation for the normalized lift family,
  including the manuscript-normalized unit-covolume statement in
  `Katznelson/Counting/LiftCovolume.lean`.

Three narrowly scoped adaptations are recorded explicitly. The exceptional
case `degree K = k = 1`, `m = n - 1` uses the author's approved
critical-radius argument. In the admissibility/Riemann subsystem, the Lean
implementation uses Mathlib's raw Euclidean mixed-space metric rather than
making the manuscript's discriminant/trace metric a global typeclass; exact
main-term measures and constants are nevertheless bridged to the manuscript
normalization. Finally, the large-radius branch of the uniform Riemann
estimate uses a compact-support lattice count instead of extending the
error-function proof. These deviations are author-approved only in their
stated local scopes. All other parts follow the checked-in manuscript's
notation and proof path. The final statement and provenance audit are
complete.
Non-fatal style linter warnings do not affect the checked theorem paths.

## Main declarations

- `Katznelson.fixed_rank_count` formalizes Theorem `th:main`.
- `Katznelson.lifts_of_codes_convergence` formalizes Theorem
  `th:higher_moments`.
- `Katznelson.manuscriptLiftsMoment_eq_liftsMoment` proves that the literal
  average over `𝓛(𝓟,s)` is the code-indexed form used in the calculation.
- `Katznelson.tsum_echelon_denominator_integral_eq_mainConstant` proves the
  manuscript formula for the fixed-rank main constant.
- `Katznelson.manuscriptEchelonIntegralLimit_eq_echelonIntegralLimit` bridges
  the literal higher-moment limit to the internal row-space representation.

## Building

Install [elan](https://github.com/leanprover/elan) and Git. Elan selects the
Lean version recorded in `lean-toolchain`; Lake uses the Mathlib revision in
`lake-manifest.json`.

```bash
lake exe cache get
lake build
```

Useful focused checks are:

```bash
lake build main
lake build Katznelson.FinalAssembly
lake env lean Katznelson/Counting/MainTermNormalization.lean
lake env lean Katznelson/Counting/LiftCovolume.lean
lake env lean Katznelson/Counting/UniformLowerRankLiteral.lean
```

## Repository layout

| Path | Contents |
| --- | --- |
| [`main.lean`](main.lean) | Public statements of the two main theorems |
| [`Katznelson/FinalAssembly.lean`](Katznelson/FinalAssembly.lean) | Final fixed-rank case split and error assembly |
| [`Katznelson/MainTheorems.lean`](Katznelson/MainTheorems.lean) | Shared counting and lifts infrastructure |
| [`Katznelson/Counting/`](Katznelson/Counting/) | Geometry, echelon, height, Riemann-sum, and counting modules |
| [`Katznelson/Lifts.lean`](Katznelson/Lifts.lean) | Codes, lifted lattices, scaling, and moments |
| [`papers/`](papers/) | Authoritative manuscript and accessible references |
| [`notes/`](notes/) | Paper issues, formalization issues, and source attribution |
| [`AGENTS.md`](AGENTS.md) | Fidelity, attribution, and contribution rules |

## Provenance and license

The development distinguishes manuscript steps, cited inputs, derived
consequences, and Lean-only infrastructure in nearby comments. Reused metric
and covolume code from Nihar Gargava's GPL-3.0 project
[*MeanValueIdealLattices*](https://github.com/nihargargava/MeanValueIdealLattices)
is attributed in the relevant source files and in
[`notes/source-attribution.md`](notes/source-attribution.md).

This repository is licensed under GPL-3.0-only; see [`LICENSE`](LICENSE).
