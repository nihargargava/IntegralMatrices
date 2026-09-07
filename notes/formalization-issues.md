# Formalization issues

## 2026-09-07: one-row norm versus matrix Frobenius norm

The exact product-covolume bridge needed by the Schmidt/counting argument is
not valid with the current Lean representations.

- `Katznelson/Counting/RowLattice.lean:321-324` defines `rowSpaceHeight` from
  `rowZLattice V`, whose ambient one-row type is `Fin m → K_ℝ[K]`.
- `Katznelson/Counting/RowLattice.lean:654-656` identifies the matrix lattice
  algebraically with a finite product of those one-row lattices.
- `Katznelson/Counting/RowLatticeRiemann.lean:33-47` defines the matrix
  covolume in `M n m (K_ℝ[K])`, with the local Frobenius norm instance used by
  the Riemann estimates.

The ordinary finite-function-space norm on `Fin m → K_ℝ[K]` is not the
Frobenius/L2 norm used by the matrix space.  For example, over a real
one-dimensional coefficient space, the vector `(1,1)` has product-space
supremum norm `1`, whereas its 1-by-2 matrix has Frobenius norm `√2`.  Thus
the hoped-for identity

```
rowMatrixLatticeCovolume V n = rowSpaceHeight V ^ n
```

cannot be asserted or used with the present definitions; the induced Haar or
Hausdorff measures differ as well.  This also means that the current
`mainConstant` is not yet shown to be the manuscript's normalized integral
constant.

Suggested correction: represent one-row real spaces with the same explicit
Euclidean (`PiLp 2`, or an equivalent Frobenius `1 × m` matrix) norm used for
matrix rows, and then prove the resulting product linear isometry preserves
the covolume measure.  Alternatively, if the existing norms are retained,
compute and carry the norm-dependent measure conversion factor throughout;
the exact product identity must not be assumed.

This is a technical normalization issue rather than a serious obstruction to
the fixed-field asymptotic argument: all norms on the finite-dimensional
spaces involved are equivalent, with constants depending only on the fixed
number field and dimensions.  Those comparison constants are sufficient for
the height-counting, finiteness, and error estimates.  They are not by
themselves sufficient to identify two exact main-term normalizations, so the
final main-term bridge must still use the matching Euclidean measure or an
explicit conversion factor.

The manuscript itself specifies the restricted Euclidean norm in
`papers/katznelson.tex:412-420` and uses the corresponding Euclidean norm in
the successive-minima discussion at `:864-866`.  The TeX source is read-only.
