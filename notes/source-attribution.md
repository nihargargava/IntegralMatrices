# Source attribution for height counting

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
height-counting input. The Lean consequences in `Schmidt.lean` take the
height-counting statement as an explicit hypothesis; they do not introduce an
axiom. A supporting Lean proof of that out-of-scope input remains separate from
the preprint's main formalization. From the explicit hypothesis, the Lean file
now proves the ordinary-shell reciprocal-height summability, the finite
height-interval-to-shell comparison, a quantitative ordinary-shell Abel
estimate (with Mathlib's `Ioc` endpoint convention), absolute summability under
the paper's reciprocal-height domination, and qualitative vanishing of moving
height tails. The paper's matrix-level quantitative `O(T^{-d})` tail still
requires the endpoint/convention bridge, the covolume/Jacobian normalization
bridge, and the corresponding echelon summand domination.
