# Source attribution and formalization provenance

This committed note records the mathematical sources, library dependencies,
and reused formalization code used by the project. The public repository does
not include copies of the manuscript or cited papers.

## Mathematical sources

- Nihar Gargava, Vlad Serban, Maryna Viazovska, and Ilaria Viglino,
  [*Integral Matrices of Fixed Rank over Number Fields*](https://arxiv.org/abs/2510.11673).
  This is the primary source formalized here.
- Wolfgang M. Schmidt, [*On Heights of Algebraic Subspaces and Diophantine
  Approximations*](https://doi.org/10.2307/1970360), *Annals of Mathematics*
  85 (1967), 430--472. Its height-counting result is the explicit input
  `HasHeightCountBounds` for intermediate ranks.
- Yonatan R. Katznelson, [*Integral Matrices of Fixed
  Rank*](https://doi.org/10.2307/2160455), *Proceedings of the American
  Mathematical Society* 120 (1994), 667--675. This is the source of the
  original fixed-rank and Abel-summation strategy.
- Jeffrey Lin Thunder, [*An Asymptotic Estimate for Heights of Algebraic
  Subspaces*](https://doi.org/10.2307/2154015), *Transactions of the American
  Mathematical Society* 331 (1992), 395--424. This supplies the sharper
  effective height asymptotic cited for context.
- Claus Fieker and Damien Stehlé, [*Short Bases of Lattices over Number
  Fields*](https://doi.org/10.1007/978-3-642-14518-6_15), ANTS-IX, LNCS 6197
  (2010), 157--173. Theorem 2 is the source of the number-field
  successive-minima/product estimate; its selection argument is formalized
  in `Katznelson/Counting/FiekerStehle.lean`.
- Nihar Gargava, Vlad Serban, and Maryna Viazovska, [*Moments of the number
  of points in a bounded set for number field lattices*](https://arxiv.org/abs/2308.15275).
  Lemma 11 and Corollary 17 provide height/denominator and
  echelon/Grassmannian convergence provenance.

## Library and code provenance

The development uses Mathlib at the revision pinned in `lake-manifest.json`.
The trace-form and covolume code in the metric subsystem is adapted from
Nihar Gargava's GPL-3.0 [*Mean Value for Random Ideal
Lattices*](https://github.com/nihargargava/MeanValueIdealLattices), commit
`339043190fd8b5468af851a680b7e8737f5467e7`. It is reused formalization code,
not a hidden mathematical input.

The optional Palomar verification scripts are adapted from
[PalomarRegistry/PalomarTemplate](https://github.com/PalomarRegistry/PalomarTemplate),
commit `128a6c5ce5f48622e69927ccd639cbff401022e8`.

## Scope and adaptations

Schmidt's height-counting statement is exposed as an explicit hypothesis;
the public theorem path does not hide it as an axiom. The Lean development
uses the approved raw Euclidean mixed-space convention for coarse estimates,
while proving the manuscript normalization separately. The critical-radius
and large-radius Riemann branches are local adaptations recorded in the
metadata and committed Lean comments.
