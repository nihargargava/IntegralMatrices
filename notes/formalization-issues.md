# Formalization issues

## 2026-09-13 (resolved): normalized lift covolume

The higher-moment statement uses normalized lifts of finite-field codes and
the manuscript's unit-covolume lattice family.  The development now proves
the raw lift's finite index, identifies its ambient integral embedding, and
computes the determinant of the normalization map.  Consequently,
`Katznelson/Counting/LiftCovolume.lean` proves
`normalizedRawLift_covolume_paperMatrixMeasure` under the manuscript's
`s ≤ n` and `0 < n` hypotheses.  This is a proved bridge, not an assumed
normalization identity; the raw-lift and normalized-lift interfaces remain
explicit in the Lean declarations.

## 2026-09-12 (resolved): vacuous full-rank height-count interface

An earlier version of `HasHeightCountBounds` requested a two-sided estimate
of order `T^m`, and the public theorem requested it for every `1 ≤ l ≤ m`.
At `l = m`, however, `Grassmannian K m m` is a singleton, so its bounded-height
count cannot have a positive lower bound of order `T^m` when `m > 0`.  The
public theorem was therefore formally true but had an impossible hypothesis
in its full-rank case.

This was a defect in the Lean interface, not in the manuscript.  The
formalization uses only finiteness and the polynomial upper bound, so
`HasHeightCountBounds` now states exactly those properties.  Public theorems
request Schmidt's attributed input only for `1 ≤ l < m`; the full-rank bound
is proved internally from the singleton Grassmannian in
`Katznelson/Counting/Schmidt.lean` and combined with the intermediate-rank
input by `heightCountBounds_upTo_of_intermediate`.

## 2026-09-12 (resolved): literal lift-family and Cartesian-power indexing

The finite-field calculation was originally indexed directly by codes, while
the manuscript states equation `eq:nthmoment` as an average over the actual
normalized lattices `𝓛(𝓟,s)` and matrices in `Λ^m`.  The definitions were
mathematically intended to represent the same objects, but there was no
proved bridge excluding multiplicity or identifying the inner index types.

`Katznelson/Lifts.lean` now proves injectivity of the normalized-lift map,
constructs `codeEquivLifts`, and proves an equivalence between integral
matrices in the raw lift and matrices in the literal normalized Cartesian
power.  The public higher-moment theorem is stated using
`manuscriptLiftsMoment`, and
`manuscriptLiftsMoment_eq_liftsMoment` transports it to the code-indexed
finite-field calculation.

## 2026-09-12 (resolved by an author-approved local adaptation): arbitrary Riemann-error cutoff

The manuscript's remark `re:help` at
`papers/katznelson.tex:550-562` says that the admissibility range
`0 < ε ≤ 1` can be replaced by `0 < ε ≤ C` for any fixed positive `C`, after
updating the implicit constant.  The development now proves the immediate
restriction to every cutoff `εMax ≤ 1` in
`Katznelson/Counting/Admissible.lean` (`AdmissibleErrorControlUpTo.mono` and
`Admissible.errorControlUpTo_of_le_one`).

The extension to a cutoff greater than one remains represented explicitly by
`AdmissibleErrorControlUpTo f εMax`; it is not silently inferred from the
definition.  For merely bounded measurable compactly supported `f`, such an
inference would require measurability and integrability of the larger-radius
supremum `E_f(·, ε)`, uniformly over real subspaces.

The public proof no longer needs that inference.  In
`Katznelson/Counting/UniformRiemann.lean`, theorem
`Admissible.exists_uniform_rowMatrix_latticeVoronoiRiemann_estimate_rank_upTo`
uses the manuscript's error-function argument on the range where it is
available and, only in the complementary large-radius branch, uses compact
support plus a uniform lattice-point count.  The author explicitly permitted
this local deviation from the exposition; its statement, constants' order of
quantification, and every downstream normalization are unchanged.  This
permission does not relax fidelity elsewhere.

## 2026-09-07 (resolved): one-row norm versus matrix Frobenius norm

This was an active issue when `RowVector` was the ordinary function space
`Fin m → K_ℝ[K]`, which carries a supremum norm. It is now resolved:

- `Katznelson/Counting/RowLattice.lean:33-36` defines `RowVector` as the
  Euclidean `PiLp 2` row space;
- `Katznelson/Counting/RowLattice.lean:1850-1855` proves the corresponding
  row-product/matrix linear isometry; and
- `Katznelson/Counting/RowLatticeRiemann.lean:79-83` proves
  `rowMatrixLatticeCovolume V n = rowSpaceHeight V ^ n` from that isometry and
  the product-basis construction.

The former supremum-versus-Frobenius counterexample no longer applies, and the
exact raw-Mathlib product-covolume identity is available on the public proof
path. This resolution does not address the distinct discriminant/trace
normalization mismatch recorded below: that mismatch concerns the paper's
number-field metric versus Mathlib's mixed-space metric, not the row-product
Euclidean structure.

## 2026-09-12 (resolved for the normalized theorem path): number-field metric normalization

The current `K_ℝ[K]` realization is Mathlib's unscaled Euclidean mixed space
`ℝ^{r_1} × ℂ^{r_2}`.  The manuscript instead fixes, at
`papers/katznelson.tex:661-674`, the norm

\[
  \lVert x\rVert^2=|\Delta_K|^{-1/d}\operatorname{Tr}(x\bar x),
\]

chosen so that `𝓞_K` has unit covolume.  In particular, the complex-place
trace weights and discriminant factor are not definitionally the same as the
ambient Mathlib norm and measure used by `rowSpaceHeight`.

Update (2026-09-12): `Katznelson/Counting/PaperMetric.lean` now gives an
explicit manuscript-facing `paperTraceForm`, `paperNormSq`, `paperNorm`, and
`paperCovolume`.  From Mathlib's canonical-embedding covolume theorem and the
trace-volume conversion ported with attribution from
`MeanValueIdealLattices`, it proves
`paperCovolume_euclidean_integerLattice` and the paper-facing restatement
`paperCovolume_integralLattice`: the ambient lattice `𝓞_K` has covolume one
in the displayed normalization.  This resolves the bare ambient-covolume
claim, without changing the global Lean norm used by existing modules.

This is not a defect in the manuscript: its metric is designed so that the
ambient algebraic-integer lattice has covolume one.  Consequently, the
primitive-lattice projection formula gives exactly the reciprocal height used
at `papers/katznelson.tex:1477-1481`.  The prior contrary entry in
`notes/paper-issues.md` has been marked resolved.

Mathematically, for fixed `K`, `m`, and `k`, the two positive-definite metrics
give uniformly comparable norms and covolumes on row spaces of rank `k`.
Rather than treating that observation as an unproved Lean bridge, the current
coarse Fieker--Stehlé and counting estimates are proved directly in the raw
Euclidean realization under the scoped author permission recorded below.
Exact normalized quantities are handled separately in
`Katznelson/Counting/MainTermNormalization.lean`. That module normalizes the
coefficient-space Haar measure by the manuscript's unit-covolume condition,
proves that the denominator pullback lattice has covolume `𝔇(D)^n`, transports
the measure through `x ↦ xD`, and proves
`tsum_echelon_denominator_integral_eq_mainConstant`. Thus the exact
covolume, Jacobian, and main-term constant on the public theorem path no
longer rely on an unspecified norm-equivalence constant.

The coordinate expression for `paperTraceForm` remains the standard
Minkowski-coordinate realization used in the cited GPL formalization. Any
future separately encoded tensor-product trace interface should still be
connected by a proved bridge rather than silently identified.

The public `Admissible` predicate is still instantiated using Mathlib's raw
Euclidean mixed-space metric, not definitionally using `paperNorm`.  A full
transfer theorem would have to compare oscillation radii and all induced
subspace measures uniformly.  The author has explicitly permitted adapting
around this issue only in the present admissibility/Riemann part, so the public
proof uses the raw-Euclidean predicate and records that convention openly in
`Foundations.lean`, `Admissible.lean`, and `main.lean`.  This is not presented
as a proved identity of admissibility predicates.  It does not affect the
exact coefficient of the main term: that coefficient is transported through
`paperMatrixMeasure` by proved equalities.  No such permission is inferred for
any other manuscript step.

Formalization status: the literal source-style module-minimum proposition
remains available in `Katznelson/Counting/SuccessiveMinima.lean` for
provenance, but the public downstream path no longer assumes it.
`Katznelson/Counting/MinkowskiSecond.lean` and
`Katznelson/Counting/FiekerStehle.lean` now prove the raw-Euclidean
Minkowski-II and Fieker--Stehlé block-selection argument directly for the
recursive manuscript minima. The raw-realization comparison is used there
only for coarse bounds with unspecified constants. Exact normalized constants
and limits now use the separate proved coefficient-measure and pushforward
construction in `MainTermNormalization.lean`.
