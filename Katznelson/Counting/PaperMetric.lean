/-
Copyright (c) 2026 Nihar Gargava.
Released under GPL-3.0-only as described in the file LICENSE.
Authors: Nihar Gargava

Portions of the trace-covolume bookkeeping below are adapted from Nihar
Gargava's `MeanValueIdealLattices`,
`dependencies/Foundations.lean`, lines 227--239, 3040--3059, and 3415--3442,
at commit `339043190fd8b5468af851a680b7e8737f5467e7` (GPL-3.0).  That project
is not currently imported as a Lake dependency because its Lean/Mathlib
revision differs from this repository's pinned revision; direct imports remain
in scope when versions are compatible.  This file ports only the ambient
metric and covolume material needed for `papers/katznelson.tex`.
-/

import Katznelson.Foundations
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.NumberTheory.NumberField.Discriminant.Basic

/-!
# The manuscript's number-field metric

This module records the metric and ambient covolume normalization fixed in
`papers/katznelson.tex`, lines 661--674.  It deliberately does not replace
Lean's global norm on `K_ℝ[K]`: that would silently change existing lattice
interfaces.  Instead, `paperNorm` and `paperCovolume` are explicit named
bridges.  Coarse row-space estimates use fixed-field norm equivalence, while
the exact normalized public main-term path is proved with
`paperMatrixMeasure` in `Counting/MainTermNormalization.lean`.

## Provenance

The imported Mathlib inputs are:

* `ZLattice.covolume_comap` in
  `Mathlib/Algebra/Module/ZLattice/Covolume.lean`, lines 102--105;
* `NumberField.mixedEmbedding.euclidean.volumePreserving_toMixed` in
  `Mathlib/NumberTheory/NumberField/CanonicalEmbedding/Basic.lean`,
  lines 852--859; and
* `NumberField.mixedEmbedding.covolume_integerLattice` in
  `Mathlib/NumberTheory/NumberField/Discriminant/Basic.lean`, lines 124--126.

They are used as cited library inputs, not restated as locally proved source
results.  The derived results below are proved from those exact interfaces.
-/

namespace Katznelson

open MeasureTheory NumberField NumberField.InfinitePlace
open scoped BigOperators Classical NumberField

noncomputable section

/- paper: `papers/katznelson.tex`, equation `eq:norm`, lines 665--670.  This
is the real/complex-coordinate realization of `Tr(x * conjugate x)`, matching
the definition called `traceForm` in Gargava's GPL-3.0 formalization cited in
the file header. -/
def paperTraceForm (K : Type*) [Field K] [NumberField K] (x : K_ℝ[K]) : ℝ :=
  (∑ w : {w : InfinitePlace K // IsReal w},
      ((NumberField.mixedEmbedding.euclidean.toMixed K x).1 w) ^ 2) +
    2 * ∑ w : {w : InfinitePlace K // IsComplex w},
      Complex.normSq ((NumberField.mixedEmbedding.euclidean.toMixed K x).2 w)

/- derived consequence: nonnegativity of the coordinate trace form defined
above, using the elementary nonnegativity of squares and `Complex.normSq`. -/
theorem paperTraceForm_nonneg
    (K : Type*) [Field K] [NumberField K] (x : K_ℝ[K]) :
    0 ≤ paperTraceForm K x := by
  unfold paperTraceForm
  refine add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) ?_
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)

/- paper: `papers/katznelson.tex`, equation `eq:norm`, lines 665--670.  This
is its displayed squared norm with `d = degree K`; `Real.rpow` represents the
paper's real exponent `-1 / d`. -/
def paperNormSq (K : Type*) [Field K] [NumberField K] (x : K_ℝ[K]) : ℝ :=
  |(NumberField.discr K : ℝ)| ^ (-(1 / (degree K : ℝ))) * paperTraceForm K x

/- paper: `papers/katznelson.tex`, equation `eq:norm`, lines 665--670.  The
paper's norm is represented explicitly, rather than changing the inherited
Mathlib norm on `K_ℝ[K]`. -/
def paperNorm (K : Type*) [Field K] [NumberField K] (x : K_ℝ[K]) : ℝ :=
  Real.sqrt (paperNormSq K x)

/- derived consequence: the squared manuscript norm is nonnegative. -/
theorem paperNormSq_nonneg
    (K : Type*) [Field K] [NumberField K] (x : K_ℝ[K]) :
    0 ≤ paperNormSq K x := by
  unfold paperNormSq
  exact mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (paperTraceForm_nonneg K x)

/- derived consequence: `paperNorm` has exactly the squared value specified
by equation `eq:norm`. -/
theorem paperNorm_sq
    (K : Type*) [Field K] [NumberField K] (x : K_ℝ[K]) :
    paperNorm K x ^ 2 = paperNormSq K x := by
  unfold paperNorm
  exact Real.sq_sqrt (paperNormSq_nonneg K x)

/- Lean infrastructure: convert a standard mixed-coordinate covolume to the
volume attached to the coordinate trace form.  Every complex place contributes
a factor `2`.  This is the focused port of `toTraceCovolume` from the
Gargava formalization identified in the file header. -/
def toTraceCovolume (K : Type*) [Field K] [NumberField K]
    (standardCovolume : ℝ) : ℝ :=
  (2 : ℝ) ^ nrComplexPlaces K * standardCovolume

/- Lean infrastructure: the covolume of an integral lattice after the
trace-form volume conversion. -/
def traceCovolume (K : Type*) [Field K] [NumberField K]
    (L : Submodule ℤ K_ℝ[K]) : ℝ :=
  toTraceCovolume K (ZLattice.covolume L)

/- Lean infrastructure: transporting a full integral lattice by a real linear
equivalence scales its covolume by the absolute determinant.  This is copied
and adapted from `MeanValueIdealLattices`, `dependencies/Foundations.lean`,
lines 3415--3442, at the GPL-3.0 revision cited in the file header.  It is a
general measure-transport interface needed to connect the manuscript metric
to lattice covolumes; it is not a substitute for a manuscript proof step. -/
theorem covolume_comap_symm_det
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (μ : Measure V) [Measure.IsAddHaarMeasure μ] (e : V ≃L[ℝ] V) :
    ZLattice.covolume
        (ZLattice.comap ℝ L e.symm.toLinearMap) μ =
      |LinearMap.det (e : V →ₗ[ℝ] V)| *
        ZLattice.covolume L μ := by
  let b := Module.Free.chooseBasis ℤ L
  let b' := b.ofZLatticeComap ℝ L e.symm.toLinearEquiv
  rw [ZLattice.covolume_eq_measure_fundamentalDomain
    (ZLattice.comap ℝ L e.symm.toLinearMap) μ
    (ZLattice.isAddFundamentalDomain b' μ)]
  rw [Module.Basis.ofZLatticeBasis_comap]
  rw [← ZSpan.map_fundamentalDomain]
  simp only [ContinuousLinearEquiv.symm_symm]
  change (μ ((e : V → V) ''
      ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ))).toReal = _
  rw [Measure.addHaar_image_continuousLinearEquiv]
  rw [ENNReal.toReal_mul]
  · simp only [ENNReal.toReal_ofReal, abs_nonneg]
    rw [← Measure.real_def]
    rw [← ZLattice.covolume_eq_measure_fundamentalDomain L μ
      (ZLattice.isAddFundamentalDomain b μ)]

/- derived consequence: Mathlib's Euclidean realization of the integer
lattice has the same standard covolume as the ordinary mixed realization.
This uses the cited `covolume_comap`, volume-preservation, and discriminant
covolume interfaces recorded in the module documentation. -/
theorem euclidean_integerLattice_covolume
    (K : Type*) [Field K] [NumberField K] :
    ZLattice.covolume (NumberField.mixedEmbedding.euclidean.integerLattice K) =
      (2⁻¹ : ℝ) ^ nrComplexPlaces K * Real.sqrt |(NumberField.discr K : ℝ)| := by
  rw [NumberField.mixedEmbedding.euclidean.integerLattice]
  rw [ZLattice.covolume_comap _ volume volume
    (NumberField.mixedEmbedding.euclidean.volumePreserving_toMixed K)]
  exact NumberField.mixedEmbedding.covolume_integerLattice K

/- derived consequence: the trace-form covolume of `𝓞_K` is
`sqrt |Δ_K|`.  This is the focused port of
`traceCovolume_integerLattice` from the Gargava formalization cited above. -/
theorem traceCovolume_euclidean_integerLattice
    (K : Type*) [Field K] [NumberField K] :
    traceCovolume K (NumberField.mixedEmbedding.euclidean.integerLattice K) =
      Real.sqrt |(NumberField.discr K : ℝ)| := by
  rw [traceCovolume, toTraceCovolume, euclidean_integerLattice_covolume]
  rw [← mul_assoc, ← mul_pow]
  norm_num

/- Lean infrastructure: the numerical covolume conversion induced by the
manuscript factor `|Δ_K|^(-1 / d)` in dimension `d`.  It is intentionally a
named scalar conversion rather than a new global measure.  A theorem that
relates this scalar to every row-subspace measure remains a separate task. -/
def paperCovolume (K : Type*) [Field K] [NumberField K]
    (L : Submodule ℤ K_ℝ[K]) : ℝ :=
  traceCovolume K L / Real.sqrt |(NumberField.discr K : ℝ)|

/- Lean infrastructure: the discriminant normalization denominator is
nonzero. -/
theorem sqrt_abs_discr_ne_zero
    (K : Type*) [Field K] [NumberField K] :
    Real.sqrt |(NumberField.discr K : ℝ)| ≠ 0 := by
  exact Real.sqrt_ne_zero'.mpr
    (abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K)))

/- derived consequence: the manuscript-normalized ambient covolume of
`𝓞_K` is one, exactly as asserted at
`papers/katznelson.tex`, lines 671--674. -/
theorem paperCovolume_euclidean_integerLattice
    (K : Type*) [Field K] [NumberField K] :
    paperCovolume K (NumberField.mixedEmbedding.euclidean.integerLattice K) = 1 := by
  rw [paperCovolume, traceCovolume_euclidean_integerLattice]
  exact div_self (sqrt_abs_discr_ne_zero K)

end

end Katznelson
