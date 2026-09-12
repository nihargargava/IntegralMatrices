# Source attribution and formalization provenance

The local source files are:

- `papers/Schmidt-HeightsAlgebraicSubspaces-1967.pdf`: Wolfgang M. Schmidt,
  “On Heights of Algebraic Subspaces and Diophantine Approximations,” *Annals
  of Mathematics* 85 (1967), 430–472.
- `papers/Thunder-AsymptoticEstimateHeights-1992.pdf`: Jeffrey Lin Thunder,
  “An Asymptotic Estimate for Heights of Algebraic Subspaces,” *Transactions
  of the American Mathematical Society* 331 (1992), 395–424.

The relationship used in this development is the following. Schmidt is the
source of the original height-counting argument over number fields; in the
notation needed here, his Theorem 3 gives upper and lower bounds of order
`T^m` for `k`-dimensional subspaces of `K^m`. Thunder gives an effective,
sharper asymptotic for the same counting problem (his Theorem 1), and is not
being cited as an independent replacement for Schmidt’s argument.

The checked-in manuscript `papers/katznelson.tex`, lines 817–828, attributes
the height-counting bound to Schmidt and mentions Thunder only for the more
precise asymptotic. Its lines 837–858 use the resulting height bound together
with the covolume/Jacobian identity and the lattice Riemann sum. The Lean
definitions of the row-space height and the matrix-space integral are new
formalization infrastructure corresponding to those manuscript definitions;
they are not claims that Schmidt or Thunder used Lean or Mathlib’s exact
interfaces.

The current Lean development consequently treats the row-space indexing as
new infrastructure and reserves the source attribution for the mathematical
height-counting input. The Lean consequences in `Schmidt.lean` take the upper
height-counting statement actually used by the proof as an explicit
hypothesis; they do not introduce an axiom. By the project goal, this is the
one permitted external hypothesis of the final conditional formalization; a
separate Lean proof of it is useful but not a completion requirement. Public
theorems request it only for intermediate ranks `1 ≤ l < m`; the singleton
full-rank Grassmannian is proved internally. From the explicit hypothesis, the
Lean file now proves the ordinary-shell reciprocal-height summability, the finite
height-interval-to-shell comparison, a quantitative ordinary-shell Abel
estimate (with Mathlib's `Ioc` endpoint convention), absolute summability under
the paper's reciprocal-height domination, and qualitative vanishing of moving
height tails. The endpoint/convention bridge, corresponding echelon summand
domination, and matrix-level quantitative `O(T^{-d})` tail are proved in the
literal lower-rank and height-tail modules. The exact covolume/Jacobian and
denominator normalization is proved separately in
`Katznelson/Counting/MainTermNormalization.lean`.

## Katznelson's fixed-rank argument

The manuscript identifies Yonatan R. Katznelson, “Integral matrices of fixed
rank,” *Proceedings of the American Mathematical Society* 120 (1994), no. 3,
667–675, as the source of the original integral-matrix argument (`K1994` in
`papers/authfile.bib`).  In particular, manuscript lines 126–151 and 363–366
attribute the overall combinatorial strategy to Katznelson, and line 640
attributes the corresponding Abel-summation setup to his equation (13).

The Lean development follows the generalized argument written in the
checked-in manuscript; it does not import Katznelson's theorem as a logical
input and does not claim that the locally proved Lean lemmas are results newly
originating here.  Consequently, the 1994 article is proof provenance rather
than an additional hypothesis of the public theorem path.

## Mathlib and the Gargava metric/covolume port

`Katznelson/Counting/PaperMetric.lean` records the manuscript's
discriminant-scaled trace metric at `papers/katznelson.tex:661-674` and proves
the ambient unit-covolume calculation for `𝓞_K`.  The direct library inputs
are from the pinned Mathlib revision
`8c20cb3e89be8ea111fd8fe1e34e93b9ff686f26`:

- `ZLattice.covolume_comap` in
  `Mathlib/Algebra/Module/ZLattice/Covolume.lean:102-105`;
- `NumberField.mixedEmbedding.euclidean.volumePreserving_toMixed` in
  `Mathlib/NumberTheory/NumberField/CanonicalEmbedding/Basic.lean:852-859`;
  and
- `NumberField.mixedEmbedding.covolume_integerLattice` in
  `Mathlib/NumberTheory/NumberField/Discriminant/Basic.lean:124-126`.

The focused trace-form and trace-covolume bookkeeping is adapted from Nihar
Gargava, [*MeanValueIdealLattices*](https://github.com/nihargargava/MeanValueIdealLattices),
`dependencies/Foundations.lean:227-239,3040-3059,3415-3442`, at commit
`339043190fd8b5468af851a680b7e8737f5467e7`.  That source is GPL-3.0 and was
written by the present project author; it is credited here and in the Lean
file header nonetheless.  It is a source of reused formalization code, not a
cited mathematical proof of the current manuscript.  Its associated research
paper is Gargava--Viazovska, arXiv:2411.14973.

The external Lake project is not currently imported as a dependency because
its Lean/Mathlib revision differs from this repository's pin; a direct import
is permitted if those versions later become compatible. The focused port is
small, compiled here, and excludes its deliberately scaffolded `Challenge.lean`.
`LICENSE` makes this repository GPL-3.0-only; Mathlib remains an external
Apache-2.0 dependency under its own license.

`Katznelson/Counting/LiftCovolume.lean` uses the pinned Mathlib finite-index,
Z-lattice, and linear-equivalence covolume results to prove the normalized
lift calculation required by the manuscript's higher-moment family.  The
raw-lift quotient argument, the integral column embedding, and the final
normalization bridge are new Lean formalization of the paper's objects; they
are marked in the source as paper steps, derived consequences, or Lean
infrastructure.  No external covolume identity is exposed as an axiom.

## Fieker--Stehlé and successive minima

`papers/Fieker-Stehle-ShortBases-2010.pdf` is Claus Fieker and Damien Stehlé,
“Short Bases of Lattices over Number Fields,” *ANTS-IX* (2010). Their Theorem
2 (p. 3) proves the number-field module-minima product estimate from classical
Minkowski's second theorem for the underlying `ℤ`-lattice. The source uses its
`T₂` norm and its module determinant. In the checked-in manuscript, this is
the cited input at `papers/katznelson.tex:930-933` for the second inequality
in `le:props_of_minima`.

`Katznelson/Counting/SuccessiveMinima.lean` records the literal source-style
module-minimum statement as the explicit proposition
`FiekerStehleProductBound`; it is not an axiom.  The public downstream path no
longer depends on that proposition.  Instead,
`Katznelson/Counting/MinkowskiSecond.lean` proves a non-sharp Euclidean
Minkowski-II product bound, and
`Katznelson/Counting/FiekerStehle.lean` formalizes the selection step on p. 3:
among the first `i * degree K + 1` real minima, a vector lies outside the
preceding `K`-span.  Their combination proves the all-rank product bound for
the recursively chosen manuscript vectors in the repository's raw Euclidean
realization.  This is a local Lean proof of the mathematical role of the
citation, not a claim that its numerical constant or its `T₂` normalization is
definitionally the manuscript metric.  The author has approved the raw
Euclidean realization for these coarse, unspecified-constant estimates; the
development does not claim a proved definitional identification of the two
norms. Exact main-term normalization is proved separately in
`Katznelson/Counting/MainTermNormalization.lean`.

## Gargava--Serban--Viazovska

`papers/Gargava-Serban-Viazovska-Moments-2024.pdf` is Nihar Gargava, Vlad
Serban, and Maryna Viazovska, “Moments of the number of points in a bounded
set for number field lattices,” arXiv:2308.15275v2 (2024). Lemma 11 (p. 7),
proved in Appendix A (pp. 36--39), identifies the Grassmannian height with the
product of the determinant of a row-reduced matrix and its denominator index.
This source supports the manuscript's denominator/height relationship; it is
not treated as a proof of the new Lean row-space or echelon infrastructure.
Corollary 17 (p. 12) is also the source cited at manuscript lines 830 and
203–204 for convergence of the echelon/Grassmannian main-term series.  The
Lean development proves the required convergence from the explicit Schmidt
upper-count hypothesis and the locally proved reciprocal-height Abel estimate;
thus Corollary 17 is recorded as proof provenance and corroboration, not as a
hidden imported assumption.
