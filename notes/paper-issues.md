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
