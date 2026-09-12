# Paper issues

## 2026-09-12: wrong side of the integral-basis norm comparison in `le:crude_early`

Source: `papers/katznelson.tex`, lines 683--684 and 1108--1118.

The two-sided estimate at line 683 is

\[
C^{\mathrm{okl}}\|v_i\|\leq\|w_{ij}\|
 \leq C^{\mathrm{okr}}\|v_i\|.
\]

The second inequality at line 1110 instead asserts

\[
\sum_i\|v_i\|^2\geq
  \frac{(C^{\mathrm{okl}})^2}{d}\sum_{i,j}\|w_{ij}\|^2.
\]

That conclusion needs an *upper* bound on `\|w_{ij}\|` in terms of
`\|v_i\|`; it does not follow from the displayed lower bound involving
`C^{\mathrm{okl}}`. Consequently the coefficient in lines 1116 and 1118 is
also not justified as written.

Suggested correction: either use the upper constant explicitly, replacing
lines 1110, 1116, and 1118 respectively by

\[
\sum_i\|v_i\|^2\geq
 \frac{1}{d(C^{\mathrm{okr}})^2}\sum_{i,j}\|w_{ij}\|^2,
\]

\[
\frac{(C^{\mathrm{okr}})^2}{k}\|A\|^2
\geq \frac1{kd}\sum_{i,j}\|w_{ij}\|^2\geq H(D)^{2/(kd)},
\]

and

\[
C^{\mathrm{crude2}}=
 \left(\frac{C^{\mathrm{sup}}C^{\mathrm{okr}}}{\sqrt{k}}\right)^{kd}.
\]

Equivalently, before line 1110, decrease the previously chosen positive
`C^{\mathrm{okl}}` so that
`C^{\mathrm{okl}}C^{\mathrm{okr}}\leq1`; this preserves the lower inequality
at line 683 and makes the displayed estimate at line 1110 valid.  The latter
is the smallest notation-preserving repair.  The theorem itself remains true;
this is a local proof-constant mismatch.

Formalization status: `Katznelson/Counting/CrudeHeight.lean` now formalizes
the selected-row, sublattice, and Hadamard portions of the proof, together
with the lower `C^{\mathrm{okl}}` action estimate.  It exposes precisely why
line 1110 additionally needs the upper comparison or the stated constant
renormalization.

## 2026-09-11: zero rows in the relaxed reciprocal-minima sum

Source: `papers/katznelson.tex`, lines 1205--1208 and 1731--1748.

The displayed definition of `\mathcal B_k(T)` permits a zero row, but the
later reciprocal product contains factors `1 / \|l_i\|^{nd}`.  Thus, as
written, the relaxed sum at lines 1741--1748 includes undefined terms.  The
selected successive minima themselves are nonzero, so this is a local domain
clarification and does not affect the intended estimate.

Suggested correction: require `l_i \ne 0` for every `i` in the definition of
`\mathcal B_k(T)`, and retain that nonzero restriction when relaxing to the
ordered ambient-row sum.  Equivalently, state before line 1743 that terms with
a zero row are omitted.  The Lean development keeps the literal current
definition available, proves that the selected image is nonzero, and uses the
explicit nonzero ordered family for the reciprocal-tail argument.

## Low-rank estimate: negative summation exponent

Source: `papers/katznelson.tex`, lines 1492–1499 and 1602–1607.

The estimate

\[
\sum_{D' \in \mathcal F_l(T)} H(D')^{k-l-n}
  \leq C T^{ld(m+k-l-n)}\log T
\]

is not valid when `m + k - l - n < 0`. For example, with
`n = 4`, `m = k = 2`, and `l = 1`, a fixed positive-height `D'` belongs to
`\mathcal F_1(T)` for all sufficiently large `T`, so the left-hand side is
bounded below by a positive constant, whereas the displayed right-hand side
is `O(log T / T)`.

Suggested correction: put `α = m + k - l - n` and use a case distinction:

\[
\sum H(D')^{k-l-n} \leq C
\begin{cases}
T^{ld\alpha}, & \alpha > 0,\\
1 + \log T, & \alpha = 0,\\
1, & \alpha < 0.
\end{cases}
\]

The conclusion at lines 1495–1497 should then be weakened or reproved with
the corrected cases. A bound suggested by the existing exponent bookkeeping
is

\[
C\frac{1+\log T}{T^{d(n-m+k-1)}}.
\]

There is also a separate endpoint issue: the statement assumes `T ≥ 1` but
uses `log T`, whose value at `T = 1` is zero even when the low-rank sum is
positive. Either use `1 + log T` or assume `T ≥ 2`.

## 2026-09-08: false equality in the low-rank lattice-point bound

Source: `papers/katznelson.tex`, lines 1561--1564.

After reducing to the inner rank-`l` sum, the manuscript writes

\[
\sum_{\substack{A\in\M_n(\Lambda_{D'})\\\rank A=l}}
 f(T^{-1}A)
=
\sum_{\substack{A\in\M_n(\Lambda_{D'})\\\|A\|\leq \Cr{sup}T}}
 \|f\|_\infty.
\]

This equality is false for a general admissible function: the summands on the
left are values of `f` on the rank-`l` stratum, while the summands on the right
are all the constant `‖f‖∞`, and the two indexing sets are different. The
support bound and nonnegativity (after replacing `f` by `|f|`) justify the
inequality

\[
\sum_{\substack{A\in\M_n(\Lambda_{D'})\\\rank A=l}}
 f(T^{-1}A)
\leq
\sum_{\substack{A\in\M_n(\Lambda_{D'})\\\|A\|\leq \Cr{sup}T}}
 \|f\|_\infty,
\]

which is sufficient for the subsequent ball-volume estimate. Replace the
equality sign at line 1562 by `\leq` (and retain the support/nonnegativity
justification). The TeX source is read-only and has not been modified.

## 2026-09-08: the corrected height cases do not prove the claimed low-rank decay

Source: `papers/katznelson.tex`, lines 1495--1499 and 1612--1633 in the
current author-modified source.

The new three-case estimate at lines 1602--1610 repairs the negative-exponent
problem in the height sum, but the final conclusion at lines 1495--1499 is
still too strong. Write (q=n-m), and for (1\leq l<k) write

\[
\alpha_l
 =d\big((k-l)(m-l)+n(l-k)\big)
 =-d(k-l)(q+l).
\]

When (m+k-l-n<0), the corrected height factor is bounded by a constant,
so the corresponding term is \(T^{\alpha_l}\), not
\(T^{-dkq}\). Uniformly in (1\leq l<k), the available exponent is only

\[
\alpha_l\leq -d(q+k-1),
\]

with equality at (l=k-1). Thus the displayed conclusion

\[
 C(1+\log T)T^{-dk(n-m)}
\]

does not follow and is false in general. For example, take
\(K=\mathbb Q\), (n=5), and (m=k=2). Let (f\geq0) be admissible and
equal to (1) on a neighborhood of (0). The standard echelon matrix
\(D=I_2\) belongs to \(\mathcal F_2(T)\) for all sufficiently large (T\),
and the rank-one matrices with only the first column nonzero contribute
\(\gg T^5\) to the unnormalised low-rank sum. After division by
\(T^{kn}=T^{10}\), this is \(\gg T^{-5}\), whereas the claimed bound is
\(O((1+\log T)T^{-6})\).

Suggested correction: replace the conclusion of the low-rank lemma by a
bound of the form

\[
 C(1+\log T)T^{-d(n-m+k-1)},
\]

or weaken it to the decay actually needed later, namely
\(O(T^{-1}\log T)\), and update the subsequent use accordingly. In the
borderline case (m+k-l-n=0), note explicitly that
\(\alpha_l=-d k(k-l)<0\), so (T^{\alpha_l}(1+\log T)) is bounded; the
current text only says \(\alpha_l\leq0\), which is insufficient by itself.
The TeX source is read-only and has not been modified.

## 2026-09-09: sign mismatch in the revised low-rank exponent

Source: `papers/katznelson.tex`, lines 1495--1497, 1630--1633, and 1680 in
the current author-modified source.

The revised lemma statement at line 1496 uses the exponent
`d(n-m-k+1)`, while the proof at line 1631 and the downstream use at line
1680 use `d(n-m+k-1)`. The latter is the exponent supplied by the displayed
definition of `alpha_l`: at `l=k-1`,

\[
\frac{\alpha_{k-1}}{d}=m-k+1-n=-(n-m+k-1).
\]

Thus the statement should use `d(n-m+k-1)` if it is intended to record the
decay obtained from the proof. With the current minus sign, line 1680 invokes
a stronger estimate than the lemma actually states.

The inequality asserted at line 1631 is also incorrect as written: it says
`d^{-1} alpha_l < n-m+k-1` and simultaneously claims equality at
`l=k-1`. The useful statement in the negative case is

\[
\frac{\alpha_l}{d}=-(k-l)(n-m+l)\leq -(n-m+k-1),
\]

with equality at `l=k-1`. The conclusion at line 1633 must then explicitly
use this negative exponent; merely saying that the sum is bounded by a
constant does not prove the decay claimed in the lemma.

## 2026-09-09: remaining `k+1` typo and missing exponent comparisons

After the subsequent manuscript edit, line 1496 now uses
`d(n-m+k+1)`. This is still incorrect: at `l=k-1`, the exponent supplied by
`alpha_l` is exactly `-d(n-m+k-1)`, so the proof cannot yield the stronger
decay with `k+1`. Lines 1631 and 1680 use the intended `d(n-m+k-1)`; line
1496 should match them.

Even after correcting that typo, line 1633 needs two explicit comparisons:
in the positive and borderline cases, the exponent `-d k(n-m)` from lines
1621--1627 must be compared with `-d(n-m+k-1)` using
`k(n-m) \geq n-m+k-1`; and in the borderline case one must use
`alpha_l=-d k(n-m)<0`, not merely `alpha_l\leq0`. The final bound is not
established by the current phrase “at most a constant” alone.

## Resolution of the revised exponent entry

The author subsequently saved the manuscript correction: line 1496 now uses
`d(n-m+k-1)`, matching lines 1631 and 1680. The earlier `k+1`/sign mismatch
recorded above therefore refers to an intermediate unsaved version and is
resolved in the current source. No additional mathematical error was found
in the saved revision during the formalization pass. The terse final step at
line 1633 remains treated as an acceptable omitted comparison rather than a
separate paper error.

## 2026-09-12 (resolved): projected-lattice height normalization

Source: `papers/katznelson.tex`, lines 661--674 and 1477--1481.

The earlier entry incorrectly tested the assertion against Mathlib's raw
mixed-space Euclidean metric rather than the metric fixed in the manuscript.
The manuscript explicitly chooses

\[
  \lVert x\rVert^2=|\Delta_K|^{-1/d}\operatorname{Tr}(x\bar x)
\]

so that `𝓞_K^m` has unit covolume (line 674).  If `L` is this ambient
lattice and `L' = L ∩ W`, the usual primitive-lattice projection identity is

\[
  \operatorname{covol}(\operatorname{proj}_{W^\perp}L)
  = \frac{\operatorname{covol}(L)}{\operatorname{covol}(L')}.
\]

Here `L'` is primitive because `W` is a `K`-subspace.  Hence, in the
manuscript's stated normalization, the projected lattice indeed has covolume
`H(D')⁻¹`, as claimed.  This is not a manuscript error.

The current Lean realization still uses Mathlib's raw mixed-space metric,
whose `𝓞_K` covolume is `2^{-r₂} √|Δ_K|`. The exact normalized coefficient
measure, denominator-lattice covolume, and `x ↦ xD` pushforward bridge are now
proved in `Katznelson/Counting/MainTermNormalization.lean`; this was a
formalization normalization issue, not a defect of the paper.

## 2026-09-11: exceptional rank-one parametrization includes zero and double-counts

Source: `papers/katznelson.tex`, lines 1718--1722.

The displayed equality

\[
\sum_{\operatorname{rank} A=1} f(T^{-1}A)
= \sum_{v\in\mathbb Z^m_{\mathrm{prim}}}
  \sum_{w\in\mathbb Z^n} f(T^{-1}wv^T)
\]

is false.  The inner sum includes `w=0`, so its right-hand side contains one
copy of `f(0)` for every primitive `v`; it is therefore infinite whenever
`f(0) ≠ 0`, although the left-hand side only contains rank-one matrices.
Moreover, with the usual convention that `\mathbb Z^m_{\mathrm{prim}}`
contains both `v` and `-v`, every nonzero rank-one matrix occurs twice on the
right.

Suggested correction, consistent with the already correct calculation at
lines 331--336, is

\[
\sum_{\substack{A\in\mathbb Z^{n\times m}\\\operatorname{rank} A=1}}
 f(T^{-1}A)
= \frac12\sum_{v\in\mathbb Z^m_{\mathrm{prim}}}
  \sum_{w\in\mathbb Z^n\setminus\{0\}} f(T^{-1}wv^T).
\]

Alternatively, choose one representative from each pair `\{v,-v\}` and
omit the factor `1/2`; in either formulation `w=0` must be excluded.  The
correction is needed for the exceptional-case reference at line 1722, but it
does not change the stated `T^{-1}\log T` conclusion.

### Resolution

The author saved this correction in the checked-in manuscript: line 1720 now
uses `\tfrac12`, excludes `w=0`, and agrees with the earlier calculation at
lines 331--336.  This issue is resolved in the current TeX source.

## 2026-09-12: local indexing and endpoint errors in the final minima sum

Source: `papers/katznelson.tex`, lines 1743--1756 and 1800.

Three local corrections are needed in the displayed nested-sum argument.
They do not affect the asserted theorem or the bound proved in Lean.

1. At line 1745, `(l_1,\ldots,l_k)` must range over
   `\M_{1\times m}(\OK)^k`, and every `l_i` must remain nonzero.  The missing
   nonzero condition is the already recorded reciprocal-minima issue above.
2. At line 1747, the expression `l_{k-1}` is defined only for `k\geq2`, not
   `k\geq1`; the following paragraph separately treats the `k=1` base case.
3. At line 1800, a positive constant cannot be bounded by
   `C\log\lVert l_{k-1}\rVert` when `\lVert l_{k-1}\rVert=1`.  The preceding
   estimates actually bound both terms by a constant.  Replace the last
   sentence by “Both terms are bounded by a constant, so (1771) holds with
   `\delta=0`.”  Equivalently, `C(1+\log\lVert l_{k-1}\rVert)` can be used
   and then absorbed into `C_\delta\lVert l_{k-1}\rVert^\delta` for any
   fixed `0<\delta<1`.

The claim at lines 1753--1756 should be read uniformly in `T`: under the
standing hypothesis `(n-m)d>1`, the corresponding full nonzero lattice sum
converges.  Merely observing that each truncated sum is finite would not by
itself prove the required uniform bound; this is treated as a terse omitted
comparison rather than a separate obstruction.

## 2026-09-12: exceptional rank-one proof does not cover general admissible functions

Source: `papers/katznelson.tex`, lines 324--358 and 1716--1724.

Author disposition (2026-09-12): this is to be treated as a minor exposition
issue, not a blocker.  For this exceptional branch only, the formalization may
use the critical radius-sum argument below instead of following the prose
literally.  The ordinary fidelity requirements remain in force elsewhere.

The exceptional branch of the proof of `th:main` rewrites the rank-one sum
at lines 1718--1722 and then says that it “has been discussed” in
`ss:log_term`.  That subsection explicitly assumes at line 328 that `f` is
the indicator of a unit ball.  It explains the lattice-point error and why a
logarithm may occur, but it does not prove the asserted asymptotic, its
uniform error bound, or the stated main-term integral for an arbitrary
admissible `f`.  Thus the reference at line 1724 does not presently discharge
the exceptional case of the theorem as stated.

A short notation-preserving repair is to keep the same Riemann-sum argument
used immediately before this case and insert the critical radius estimate

\[
  \sum_{D\in\mathcal F_1(T)}\frac{\rho(\Lambda_D)}{H(D)^n}
  \ll 1+\log T.
\]

Indeed, in `d=1`, `k=1`, and `n=m+1`, the `k=1` specialization of
`eq:just_as_before` is bounded by

\[
  C\sum_{\substack{0\ne l\in\mathbb Z^m\\\lVert l\rVert\le C'T}}
    \lVert l\rVert^{-m}\ll 1+\log T
\]

by the ordinary-shell/Abel estimate.  Substitution into `eq:ineq212`, together
with `le:low_rank_terms` and `co:tail`, gives the required
`O(T^{-1}\log T)` error for every admissible `f`.  This is exactly the route
proved in Lean by
`ambientIntegralRowModule_norm_shell_sum_Icc_critical_rank_one`,
`exists_calF_coveringRadius_sum_bound_of_critical_rank_one_of_firstMinkowski`,
and
`exists_boundedRowSpaces_latticeVoronoi_radius_sum_bound_of_critical_rank_one`.
The Lean exceptional branch is therefore classified as the author-approved
derived argument for this isolated step.
