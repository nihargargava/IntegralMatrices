# Paper issues

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
