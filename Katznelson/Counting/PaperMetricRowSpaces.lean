/-
Copyright (c) 2026 Nihar Gargava.
Released under GPL-3.0-only as described in the file LICENSE.
Authors: Nihar Gargava
-/

import Katznelson.Counting.PaperMetric
import Katznelson.Counting.RowLatticeRiemann
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Haar-normalization bridges for row spaces

The manuscript fixes the trace/discriminant Euclidean metric in
`papers/katznelson.tex`, lines 661--674, and uses the induced Lebesgue measure
on each row-matrix subspace at lines 844--858.  The current lattice and
Riemann-sum development uses Mathlib's Euclidean Hausdorff measure.  This
module proves the exact bridge relevant to the main term: reciprocal
covolume times an integral is independent of the choice of additive Haar
measure.  Thus no norm-equivalence constant enters the main term.

The proof uses Mathlib's uniqueness of additive Haar measure,
`isAddLeftInvariant_eq_smul`, from
`Mathlib/MeasureTheory/Measure/Haar/Unique.lean`, and its exact formulas for
integrals and real-valued measures under `NNReal` scaling.  These are library
inputs, not mathematical hypotheses or copied external code.
-/

namespace Katznelson

open MeasureTheory Set Module NumberField NumberField.InfinitePlace
open scoped Classical MeasureTheory NumberField

noncomputable section

/- Lean infrastructure: exact scaling of lattice covolume when the ambient
additive Haar measure is multiplied by a nonzero nonnegative real.  This is
proved directly from Mathlib's fundamental-domain definition of covolume. -/
theorem covolume_nnreal_smul_measure
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (mu : Measure E) [Measure.IsAddHaarMeasure mu]
    (c : NNReal) (hc : c ≠ 0) :
    ZLattice.covolume L (c • mu) =
      (c : ℝ) * ZLattice.covolume L mu := by
  let _ : Measure.IsAddHaarMeasure (c • mu) :=
    Measure.IsAddHaarMeasure.nnreal_smul mu hc
  let b := Module.Free.chooseBasis ℤ L
  rw [ZLattice.covolume_eq_measure_fundamentalDomain L (c • mu)
      (ZLattice.isAddFundamentalDomain b (c • mu)),
    ZLattice.covolume_eq_measure_fundamentalDomain L mu
      (ZLattice.isAddFundamentalDomain b mu)]
  exact measureReal_nnreal_smul_apply c

/- derived consequence: the normalized lattice integral is unchanged by a
nonzero scalar rescaling of Haar measure.  This combines the preceding
covolume formula with Mathlib's exact `integral_smul_nnreal_measure`; it is
the algebraic cancellation used implicitly in manuscript equation
`eq:d_D_defined`, lines 847--854. -/
theorem normalized_lattice_integral_nnreal_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (mu : Measure E) [Measure.IsAddHaarMeasure mu]
    (c : NNReal) (hc : c ≠ 0) (f : E → ℝ) :
    (ZLattice.covolume L (c • mu))⁻¹ * ∫ x, f x ∂(c • mu) =
      (ZLattice.covolume L mu)⁻¹ * ∫ x, f x ∂mu := by
  let _ : Measure.IsAddHaarMeasure (c • mu) :=
    Measure.IsAddHaarMeasure.nnreal_smul mu hc
  rw [covolume_nnreal_smul_measure L mu c hc,
    integral_smul_nnreal_measure]
  have hcR : (c : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hc
  field_simp
  simp [NNReal.smul_def]

/- derived consequence: on a finite-dimensional real space, the normalized
lattice integral is independent of the additive Haar measure, not merely of
an explicitly supplied scalar multiple.  Mathlib's uniqueness theorem
identifies the second measure with such a nonzero multiple.  Applied to the
Lebesgue measure induced by the paper metric and to Mathlib's Euclidean
Hausdorff measure, this is the exact normalization bridge required at
manuscript lines 844--858. -/
theorem normalized_lattice_integral_eq_of_isAddHaarMeasure
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (mu nu : Measure E) [Measure.IsAddHaarMeasure mu]
    [Measure.IsAddHaarMeasure nu] (f : E → ℝ) :
    (ZLattice.covolume L nu)⁻¹ * ∫ x, f x ∂nu =
      (ZLattice.covolume L mu)⁻¹ * ∫ x, f x ∂mu := by
  let c : NNReal := Measure.addHaarScalarFactor nu mu
  have hc : c ≠ 0 :=
    (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure nu mu).ne'
  have hnu : nu = c • mu :=
    Measure.isAddLeftInvariant_eq_smul nu mu
  rw [hnu]
  exact normalized_lattice_integral_nnreal_smul L mu c hc f

/- derived consequence: if the second Haar measure normalizes the lattice to
unit covolume, its integral is exactly the reciprocal-covolume normalized
integral for any other Haar measure.  This is the abstract form of the
measure `d_D x` introduced in manuscript lines 847--854. -/
theorem integral_unitCovolume_eq_normalized_lattice_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (mu nu : Measure E) [Measure.IsAddHaarMeasure mu]
    [Measure.IsAddHaarMeasure nu]
    (hnu : ZLattice.covolume L nu = 1) (f : E → ℝ) :
    ∫ x, f x ∂nu =
      (ZLattice.covolume L mu)⁻¹ * ∫ x, f x ∂mu := by
  have h := normalized_lattice_integral_eq_of_isAddHaarMeasure
    L mu nu f
  simpa [hnu] using h

/- derived consequence: an additive Haar measure for which a fixed full
lattice has covolume one is unique.  Consequently the manuscript's `d_D x`
at lines 851--854 is characterized by its stated unit-covolume property; no
unrecorded choice of Lebesgue normalization remains. -/
theorem isAddHaarMeasure_eq_of_lattice_covolume_eq_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (mu nu : Measure E) [Measure.IsAddHaarMeasure mu]
    [Measure.IsAddHaarMeasure nu]
    (hmu : ZLattice.covolume L mu = 1)
    (hnu : ZLattice.covolume L nu = 1) :
    mu = nu := by
  let c : NNReal := Measure.addHaarScalarFactor nu mu
  have hc : c ≠ 0 :=
    (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure nu mu).ne'
  have hmeasure : nu = c • mu :=
    Measure.isAddLeftInvariant_eq_smul nu mu
  have hcov := congrArg (fun rho : Measure E => ZLattice.covolume L rho)
    hmeasure
  let _ : Measure.IsAddHaarMeasure (c • mu) :=
    Measure.IsAddHaarMeasure.nnreal_smul mu hc
  rw [covolume_nnreal_smul_measure L mu c hc, hmu, hnu] at hcov
  have hc_one : c = 1 := by
    apply NNReal.coe_injective
    simpa using hcov.symm
  simpa [hc_one] using hmeasure.symm

/- Lean infrastructure: the positive scalar converting Mathlib's standard
mixed-coordinate volume on `K_ℝ` to the trace/discriminant-normalized volume
used by the manuscript.  The factor `2 ^ r₂` converts each complex coordinate
to the trace form and division by `sqrt |Δ_K|` accounts for the global
`|Δ_K|⁻¹/d` metric scaling in real dimension `d`; compare `eq:norm`, lines
661--674, and `toTraceCovolume` in `PaperMetric.lean`. -/
noncomputable def paperMeasureScale
    (K : Type*) [Field K] [NumberField K] : NNReal :=
  ⟨(2 : ℝ) ^ nrComplexPlaces K /
      Real.sqrt |(NumberField.discr K : ℝ)|,
    div_nonneg (pow_nonneg (by norm_num) _) (Real.sqrt_nonneg _)⟩

/- derived consequence: the manuscript volume-conversion scalar is strictly
positive; this uses the nonvanishing of the number-field discriminant already
recorded by `sqrt_abs_discr_ne_zero`. -/
theorem paperMeasureScale_pos
    (K : Type*) [Field K] [NumberField K] :
    0 < paperMeasureScale K := by
  change 0 < (2 : ℝ) ^ nrComplexPlaces K /
    Real.sqrt |(NumberField.discr K : ℝ)|
  exact div_pos (pow_pos (by norm_num) _)
    (Real.sqrt_pos.2
      (abs_pos.mpr
        (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))))

/- Lean infrastructure: an explicit additive Haar measure realizing the
numerical trace/discriminant volume conversion already encoded by
`paperCovolume` on one copy of `K_ℝ`.  The exact covolume comparison below,
rather than the name of this definition, is the bridge used downstream; this
definition does not by itself construct the inner product inducing
`paperNorm`. -/
noncomputable def paperMeasure
    (K : Type*) [Field K] [NumberField K] : Measure K_ℝ[K] :=
  paperMeasureScale K • (volume : Measure K_ℝ[K])

/- derived consequence: the explicit manuscript-normalized measure is an
additive Haar measure. -/
theorem paperMeasure_isAddHaarMeasure
    (K : Type*) [Field K] [NumberField K] :
    Measure.IsAddHaarMeasure (paperMeasure K) := by
  unfold paperMeasure
  exact Measure.IsAddHaarMeasure.nnreal_smul volume
    (paperMeasureScale_pos K).ne'

/- derived consequence: `paperCovolume` from `PaperMetric.lean` is exactly
the lattice covolume computed with `paperMeasure`, for every full lattice in
`K_ℝ`.  This turns the numerical conversion into an equality of actual Haar
measure covolumes; no norm-equivalence estimate or unspecified constant is
used. -/
theorem covolume_paperMeasure_eq_paperCovolume
    (K : Type*) [Field K] [NumberField K]
    (L : Submodule ℤ K_ℝ[K]) [DiscreteTopology L] [IsZLattice ℝ L] :
    ZLattice.covolume L (paperMeasure K) = paperCovolume K L := by
  let _ : Measure.IsAddHaarMeasure (paperMeasure K) :=
    paperMeasure_isAddHaarMeasure K
  rw [paperMeasure, covolume_nnreal_smul_measure L volume
    (paperMeasureScale K) (paperMeasureScale_pos K).ne']
  change
    (((2 : ℝ) ^ nrComplexPlaces K /
        Real.sqrt |(NumberField.discr K : ℝ)|) *
      ZLattice.covolume L) =
      ((2 : ℝ) ^ nrComplexPlaces K * ZLattice.covolume L) /
        Real.sqrt |(NumberField.discr K : ℝ)|
  ring

/- paper: the covolume-one normalization asserted at manuscript line 674,
now stated for the explicit Haar measure `paperMeasure`.  It is the actual
measure-level version of `paperCovolume_euclidean_integerLattice`. -/
theorem integerLattice_covolume_paperMeasure
    (K : Type*) [Field K] [NumberField K] :
    ZLattice.covolume
        (NumberField.mixedEmbedding.euclidean.integerLattice K)
        (paperMeasure K) = 1 := by
  rw [covolume_paperMeasure_eq_paperCovolume,
    paperCovolume_euclidean_integerLattice]

/- derived consequence: the manuscript-normalized measure and Mathlib's raw
Euclidean volume give exactly the same normalized lattice integral on
`K_ℝ`.  This is the one-copy specialization of the general Haar cancellation
that explicitly mentions the trace/discriminant measure. -/
theorem normalized_lattice_integral_paperMeasure_eq_volume
    (K : Type*) [Field K] [NumberField K]
    (L : Submodule ℤ K_ℝ[K]) [DiscreteTopology L] [IsZLattice ℝ L]
    (f : K_ℝ[K] → ℝ) :
    (ZLattice.covolume L (paperMeasure K))⁻¹ *
        ∫ x, f x ∂(paperMeasure K) =
      (ZLattice.covolume L volume)⁻¹ * ∫ x, f x ∂volume := by
  let _ : Measure.IsAddHaarMeasure (paperMeasure K) :=
    paperMeasure_isAddHaarMeasure K
  exact normalized_lattice_integral_eq_of_isAddHaarMeasure
    L volume (paperMeasure K) f

/- Lean infrastructure: fix on the matrix-row subspace the same induced
Borel structure used by `rowMatrixEuclideanMeasure`.  Naming these local
instances prevents elaboration from choosing a definitionally different
measurable-space argument through the dependent submodule. -/
noncomputable local instance paperMetricRowMatrixMeasurableSpace
    {K : Type*} [Field K] [NumberField K]
    {m k n : ℕ} (V : Grassmannian K m k) :
    MeasurableSpace (rowMatrixRealSpan V n) :=
  @Subtype.instMeasurableSpace (M n m (K_ℝ[K]))
    (fun A => A ∈ rowMatrixRealSpan V n)
    (kRealMatrixMeasurableSpace (K := K))

/- Lean infrastructure: the preceding induced measurable space is the Borel
space inherited from the Frobenius-normed ambient matrix space. -/
local instance paperMetricRowMatrixBorelSpace
    {K : Type*} [Field K] [NumberField K]
    {m k n : ℕ} (V : Grassmannian K m k) :
    BorelSpace (rowMatrixRealSpan V n) :=
  @Subtype.borelSpace (M n m (K_ℝ[K])) inferInstance
    (kRealMatrixMeasurableSpace (K := K))
    (kRealMatrixBorelSpace (K := K))
    (fun A => A ∈ rowMatrixRealSpan V n)

/- Lean infrastructure: expose Mathlib's standard fact that Euclidean
Hausdorff measure is additive Haar measure, at the exact dependent type used
by the row-matrix definitions. -/
local instance rowMatrixEuclideanMeasureIsAddHaar
    {K : Type*} [Field K] [NumberField K]
    {m k n : ℕ} (V : Grassmannian K m k) :
    Measure.IsAddHaarMeasure (rowMatrixEuclideanMeasure (n := n) V) := by
  unfold rowMatrixEuclideanMeasure
  exact @MeasureTheory.isAddHaarMeasure_euclideanHausdorffMeasure
    (rowMatrixRealSpan V n) inferInstance inferInstance inferInstance
    (paperMetricRowMatrixMeasurableSpace V)
    (paperMetricRowMatrixBorelSpace V)

/- Lean infrastructure: the main-term summand formed with an arbitrary
additive Haar measure on the row-matrix space.  Its lattice and integrand are
exactly those already used by `rowMatrixLatticeCovolume` and
`rowMatrixSubspaceIntegral`; only the measure is exposed. -/
noncomputable def rowMatrixNormalizedIntegralWithMeasure
    {K : Type*} [Field K] [NumberField K]
    {m k : ℕ} (V : Grassmannian K m k) (n : ℕ)
    (mu : Measure (rowMatrixRealSpan V n))
    (f : M n m (K_ℝ[K]) → ℝ) : ℝ :=
  (ZLattice.covolume (rowMatrixZLattice V n) mu)⁻¹ *
    ∫ A : rowMatrixRealSpan V n, f (A : M n m (K_ℝ[K])) ∂mu

/- derived consequence: the exposed row-matrix summand is independent of
the chosen additive Haar measure.  In particular, this gives a direct bridge
between the paper-metric induced measure from `eq:norm` (lines 661--674) and
the raw Euclidean measure used in the Lean Riemann-sum implementation. -/
theorem rowMatrixNormalizedIntegralWithMeasure_eq
    {K : Type*} [Field K] [NumberField K]
    {m k n : ℕ} (V : Grassmannian K m k)
    (mu nu : Measure (rowMatrixRealSpan V n))
    [Measure.IsAddHaarMeasure mu] [Measure.IsAddHaarMeasure nu]
    (f : M n m (K_ℝ[K]) → ℝ) :
    rowMatrixNormalizedIntegralWithMeasure V n nu f =
      rowMatrixNormalizedIntegralWithMeasure V n mu f := by
  unfold rowMatrixNormalizedIntegralWithMeasure
  exact @normalized_lattice_integral_eq_of_isAddHaarMeasure
    (rowMatrixRealSpan V n) inferInstance inferInstance inferInstance
    (paperMetricRowMatrixMeasurableSpace V)
    (paperMetricRowMatrixBorelSpace V)
    (rowMatrixZLattice V n) (rowMatrixZLattice.discreteTopology V)
    (rowMatrixZLattice.isZLattice V) mu nu
    (by assumption) (by assumption)
    (fun A : rowMatrixRealSpan V n => f (A : M n m (K_ℝ[K])))

/- derived consequence: exact measure-normalization form of the summand in
`eq:d_D_defined`, manuscript lines 847--854.  For every additive Haar measure
`mu`--hence in particular for the Lebesgue measure induced by the
trace/discriminant metric--normalizing by the covolume of `M_n(Λ_D)` gives
the existing Lean main-term summand.  This theorem makes no norm-equivalence
argument and introduces no unspecified constant. -/
theorem rowMatrixNormalizedIntegralWithMeasure_eq_mainSummand
    {K : Type*} [Field K] [NumberField K]
    {m k n : ℕ} (V : Grassmannian K m k)
    (mu : Measure (rowMatrixRealSpan V n))
    [Measure.IsAddHaarMeasure mu]
    (f : M n m (K_ℝ[K]) → ℝ) :
    rowMatrixNormalizedIntegralWithMeasure V n mu f =
      (rowMatrixLatticeCovolume V n)⁻¹ *
        rowMatrixSubspaceIntegral V n f := by
  rw [rowMatrixNormalizedIntegralWithMeasure_eq V
    (rowMatrixEuclideanMeasure (n := n) V) mu f]
  rfl

/- derived consequence: if `mu` is the manuscript's unit-covolume measure
`d_D x` from lines 847--854, its integral is exactly the existing Lean
main-term summand.  This isolates the defining unit-covolume property used in
the paper and does not require a choice of normalization for Haar measure. -/
theorem rowMatrix_unitCovolume_integral_eq_mainSummand
    {K : Type*} [Field K] [NumberField K]
    {m k n : ℕ} (V : Grassmannian K m k)
    (mu : Measure (rowMatrixRealSpan V n))
    [Measure.IsAddHaarMeasure mu]
    (hmu : ZLattice.covolume (rowMatrixZLattice V n) mu = 1)
    (f : M n m (K_ℝ[K]) → ℝ) :
    (∫ A : rowMatrixRealSpan V n,
        f (A : M n m (K_ℝ[K])) ∂mu) =
      (rowMatrixLatticeCovolume V n)⁻¹ *
        rowMatrixSubspaceIntegral V n f := by
  have h := rowMatrixNormalizedIntegralWithMeasure_eq_mainSummand
    V mu f
  unfold rowMatrixNormalizedIntegralWithMeasure at h
  simpa [hmu] using h

/- derived consequence: reciprocal-height form of the same
measure-independent summand,
combining the preceding normalization theorem with the exact product
covolume identity formalizing `M_n(Λ_D)` at manuscript lines 844--854.
This is the form used by `mainConstant_eq_height_normalized`.  Here
`rowSpaceHeight` remains the raw Euclidean realization; this equality is used
to compare the normalized summand, not to identify that raw height by itself
with the paper-metric height. -/
theorem rowMatrixNormalizedIntegralWithMeasure_eq_height_normalized
    {K : Type*} [Field K] [NumberField K]
    {m k n : ℕ} (V : Grassmannian K m k)
    (mu : Measure (rowMatrixRealSpan V n))
    [Measure.IsAddHaarMeasure mu]
    (f : M n m (K_ℝ[K]) → ℝ) :
    rowMatrixNormalizedIntegralWithMeasure V n mu f =
      (rowSpaceHeight V)⁻¹ ^ n * rowMatrixSubspaceIntegral V n f := by
  rw [rowMatrixNormalizedIntegralWithMeasure_eq_mainSummand V mu f,
    rowMatrixLatticeCovolume_eq_rowSpaceHeight_pow, inv_pow]

/- derived consequence: termwise Haar-normalization invariance passes to the
Grassmannian sum.  The right side is definitionally the summation expression
used by `mainConstant`; an importing assembly module can identify the full
manuscript constant by unfolding `mainConstant` and applying this theorem. -/
theorem tsum_rowMatrixNormalizedIntegralWithMeasure_eq_mainSummands
    {K : Type*} [Field K] [NumberField K]
    {m k n : ℕ}
    (mu : (V : Grassmannian K m k) →
      Measure (rowMatrixRealSpan V n))
    (hmu : ∀ V, Measure.IsAddHaarMeasure (mu V))
    (f : M n m (K_ℝ[K]) → ℝ) :
    (∑' V : Grassmannian K m k,
        rowMatrixNormalizedIntegralWithMeasure V n (mu V) f) =
      ∑' V : Grassmannian K m k,
        (rowMatrixLatticeCovolume V n)⁻¹ *
          rowMatrixSubspaceIntegral V n f := by
  apply tsum_congr
  intro V
  let _ : Measure.IsAddHaarMeasure (mu V) := hmu V
  exact rowMatrixNormalizedIntegralWithMeasure_eq_mainSummand V (mu V) f

/- derived consequence: summing the unit-covolume integrals `∫ f d_D` from
`eq:d_D_defined`, lines 847--854, gives the current row-space main-constant
expression.  The hypotheses state exactly the manuscript's characterization
of each `d_D`; uniqueness was proved above.  The existing echelon-to-row-space
bridge, rather than this theorem alone, justifies the change of index. -/
theorem tsum_rowMatrix_unitCovolume_integral_eq_mainSummands
    {K : Type*} [Field K] [NumberField K]
    {m k n : ℕ}
    (mu : (V : Grassmannian K m k) →
      Measure (rowMatrixRealSpan V n))
    (hmu : ∀ V, Measure.IsAddHaarMeasure (mu V))
    (hunit : ∀ V,
      ZLattice.covolume (rowMatrixZLattice V n) (mu V) = 1)
    (f : M n m (K_ℝ[K]) → ℝ) :
    (∑' V : Grassmannian K m k,
        ∫ A : rowMatrixRealSpan V n,
          f (A : M n m (K_ℝ[K])) ∂(mu V)) =
      ∑' V : Grassmannian K m k,
        (rowMatrixLatticeCovolume V n)⁻¹ *
          rowMatrixSubspaceIntegral V n f := by
  apply tsum_congr
  intro V
  let _ : Measure.IsAddHaarMeasure (mu V) := hmu V
  exact rowMatrix_unitCovolume_integral_eq_mainSummand
    V (mu V) (hunit V) f

end

end Katznelson
