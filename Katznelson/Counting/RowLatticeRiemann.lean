import Katznelson.Counting.RowLattice
import Katznelson.Counting.SubspaceRiemann

/-!
# Riemann sums for matrices with rows in a lattice

This file specializes Lemma `le:Riemann_estimate` to the lattice
`M_n(Λ_D)` from Definition `de:defi_of_M_t` and rewrites its lattice sum as
the sum over integral matrices used in Lemma `le:without_rank_cond`.
-/

namespace Katznelson

open MeasureTheory Set Module
open scoped Classical MeasureTheory NumberField

section

variable {K : Type*} [Field K] [NumberField K]

/- Package topology-sensitive quantities behind definitions.  Matrix norms
are scoped in Mathlib, so exposing their instances in theorem signatures
would create instance diamonds. -/
noncomputable def rowMatrixFundamentalRadius
    {m k : ℕ} (V : Grassmannian K m k) (n : ℕ) : ℝ :=
  let hdisc : DiscreteTopology (rowMatrixZLattice V n) := inferInstance
  let hZ := @IsZLattice.mk ℝ inferInstance (rowMatrixRealSpan V n)
    inferInstance inferInstance (rowMatrixZLattice V n) hdisc
    (rowMatrixZLattice_span_top V n)
  @latticeFundamentalRadius (rowMatrixRealSpan V n) inferInstance inferInstance
    inferInstance (rowMatrixZLattice V n) hdisc hZ

noncomputable def rowMatrixLatticeCovolume
    {m k : ℕ} (V : Grassmannian K m k) (n : ℕ) : ℝ :=
  let msX : MeasurableSpace (M n m (K_ℝ[K])) := borel _
  let bsX : @BorelSpace (M n m (K_ℝ[K])) inferInstance msX := ⟨rfl⟩
  let msW : MeasurableSpace (rowMatrixRealSpan V n) :=
    @Subtype.instMeasurableSpace (M n m (K_ℝ[K]))
      (fun x => x ∈ rowMatrixRealSpan V n) msX
  let bsW : @BorelSpace (rowMatrixRealSpan V n) inferInstance msW :=
    @Subtype.borelSpace (M n m (K_ℝ[K])) inferInstance msX bsX
      (fun x => x ∈ rowMatrixRealSpan V n)
  let mu : @Measure (rowMatrixRealSpan V n) msW :=
    @Measure.euclideanHausdorffMeasure (rowMatrixRealSpan V n)
      inferInstance msW bsW (Module.finrank ℝ (rowMatrixRealSpan V n))
  @ZLattice.covolume (rowMatrixRealSpan V n) inferInstance msW
    (rowMatrixZLattice V n) mu

noncomputable def rowMatrixSubspaceIntegral
    {m k : ℕ} (V : Grassmannian K m k) (n : ℕ)
    (f : M n m (K_ℝ[K]) → ℝ) : ℝ :=
  let msX : MeasurableSpace (M n m (K_ℝ[K])) := borel _
  let bsX : @BorelSpace (M n m (K_ℝ[K])) inferInstance msX := ⟨rfl⟩
  let msW : MeasurableSpace (rowMatrixRealSpan V n) :=
    @Subtype.instMeasurableSpace (M n m (K_ℝ[K]))
      (fun x => x ∈ rowMatrixRealSpan V n) msX
  let bsW : @BorelSpace (rowMatrixRealSpan V n) inferInstance msW :=
    @Subtype.borelSpace (M n m (K_ℝ[K])) inferInstance msX bsX
      (fun x => x ∈ rowMatrixRealSpan V n)
  let mu : @Measure (rowMatrixRealSpan V n) msW :=
    @Measure.euclideanHausdorffMeasure (rowMatrixRealSpan V n)
      inferInstance msW bsW (Module.finrank ℝ (rowMatrixRealSpan V n))
  @MeasureTheory.integral (rowMatrixRealSpan V n) ℝ inferInstance
    inferInstance msW mu (fun x => f x)

theorem rowMatrixFundamentalRadius_nonneg
    {m k n : ℕ} (V : Grassmannian K m k) :
    0 ≤ rowMatrixFundamentalRadius V n := by
  let hdisc : DiscreteTopology (rowMatrixZLattice V n) :=
    rowMatrixZLattice.discreteTopology V n
  let hZ : @IsZLattice ℝ inferInstance (rowMatrixRealSpan V n)
      inferInstance inferInstance (rowMatrixZLattice V n) hdisc :=
    @IsZLattice.mk ℝ inferInstance (rowMatrixRealSpan V n)
      inferInstance inferInstance (rowMatrixZLattice V n) hdisc
      (rowMatrixZLattice_span_top V n)
  change 0 ≤ @latticeFundamentalRadius (rowMatrixRealSpan V n)
    inferInstance inferInstance inferInstance (rowMatrixZLattice V n) hdisc hZ
  exact @latticeFundamentalRadius_nonneg (rowMatrixRealSpan V n)
    inferInstance inferInstance inferInstance (rowMatrixZLattice V n) hdisc hZ

theorem rowMatrixFundamentalRadius_pos
    {m k n : ℕ} (V : Grassmannian K m k)
    (hk : 0 < k) (hn : 0 < n) :
    0 < rowMatrixFundamentalRadius V n := by
  let hdisc : DiscreteTopology (rowMatrixZLattice V n) :=
    rowMatrixZLattice.discreteTopology V n
  let hZ : @IsZLattice ℝ inferInstance (rowMatrixRealSpan V n)
      inferInstance inferInstance (rowMatrixZLattice V n) hdisc :=
    @IsZLattice.mk ℝ inferInstance (rowMatrixRealSpan V n)
      inferInstance inferInstance (rowMatrixZLattice V n) hdisc
      (rowMatrixZLattice_span_top V n)
  letI : Nontrivial (rowMatrixRealSpan V n) :=
    Submodule.nontrivial_iff_ne_bot.mpr
      (rowMatrixRealSpan_ne_bot_of_pos V hk hn)
  change 0 < @latticeFundamentalRadius (rowMatrixRealSpan V n)
    inferInstance inferInstance inferInstance (rowMatrixZLattice V n) hdisc hZ
  exact @latticeFundamentalRadius_pos (rowMatrixRealSpan V n)
    inferInstance inferInstance inferInstance (rowMatrixZLattice V n) hdisc hZ
    inferInstance

theorem rowMatrixLatticeCovolume_pos
    {m k n : ℕ} (V : Grassmannian K m k) :
    0 < rowMatrixLatticeCovolume V n := by
  let msX : MeasurableSpace (M n m (K_ℝ[K])) := borel _
  let bsX : @BorelSpace (M n m (K_ℝ[K])) inferInstance msX := ⟨rfl⟩
  let msW : MeasurableSpace (rowMatrixRealSpan V n) :=
    @Subtype.instMeasurableSpace (M n m (K_ℝ[K]))
      (fun x => x ∈ rowMatrixRealSpan V n) msX
  let bsW : @BorelSpace (rowMatrixRealSpan V n) inferInstance msW :=
    @Subtype.borelSpace (M n m (K_ℝ[K])) inferInstance msX bsX
      (fun x => x ∈ rowMatrixRealSpan V n)
  let mu : @Measure (rowMatrixRealSpan V n) msW :=
    @Measure.euclideanHausdorffMeasure (rowMatrixRealSpan V n)
      inferInstance msW bsW (Module.finrank ℝ (rowMatrixRealSpan V n))
  change 0 < @ZLattice.covolume (rowMatrixRealSpan V n) inferInstance msW
    (rowMatrixZLattice V n) mu
  let hdisc : DiscreteTopology (rowMatrixZLattice V n) :=
    rowMatrixZLattice.discreteTopology V n
  let hZ : @IsZLattice ℝ inferInstance (rowMatrixRealSpan V n)
      inferInstance inferInstance (rowMatrixZLattice V n) hdisc :=
    @IsZLattice.mk ℝ inferInstance (rowMatrixRealSpan V n)
      inferInstance inferInstance (rowMatrixZLattice V n) hdisc
      (rowMatrixZLattice_span_top V n)
  exact @ZLattice.covolume_pos (rowMatrixRealSpan V n) inferInstance inferInstance
    inferInstance msW bsW (rowMatrixZLattice V n) hdisc hZ mu
    (@isAddHaarMeasure_euclideanHausdorffMeasure (rowMatrixRealSpan V n)
      inferInstance inferInstance inferInstance msW bsW)

/-- Reindex the abstract row-matrix lattice sum by the integral matrices
whose rows belong to `Λ_D`. -/
theorem tsum_rowMatrixZLattice_eq_integralRowMatrices
    {m k n : ℕ} (V : Grassmannian K m k)
    (f : M n m (K_ℝ[K]) → ℝ) (T : ℝ) :
    (∑' A : rowMatrixZLattice V n,
        f (T⁻¹ • (((A : rowMatrixRealSpan V n) : M n m (K_ℝ[K]))))) =
      ∑' A : {A : IntegralMatrix K n m // rowsInIntegralRowModule V A},
        f (T⁻¹ • embedMatrix A.1) := by
  let e := integralRowMatricesEquivRowMatrixZLattice V n
  simpa [e] using
    (e.tsum_eq (fun A : rowMatrixZLattice V n =>
      f (T⁻¹ • (((A : rowMatrixRealSpan V n) : M n m (K_ℝ[K])))))).symm

/- The same unrestricted sum can be written as a sum over independent rows,
   using the product equivalence from `RowLattice`. -/
theorem tsum_rowMatrixZLattice_eq_rowTuples
    {m k n : ℕ} (V : Grassmannian K m k)
    (f : M n m (K_ℝ[K]) → ℝ) (T : ℝ) :
    (∑' A : rowMatrixZLattice V n,
        f (T⁻¹ • (((A : rowMatrixRealSpan V n) : M n m (K_ℝ[K]))))) =
      ∑' A : Fin n → rowZLattice V,
        f (T⁻¹ • (fun i j =>
          (((A i : rowZLattice V) : Fin m → K_ℝ[K]) j))) := by
  let e := rowMatrixZLatticeEquiv (n := n) V
  let F : (Fin n → rowZLattice V) → ℝ := fun A =>
    f (T⁻¹ • (fun i j =>
      (((A i : rowZLattice V) : Fin m → K_ℝ[K]) j)))
  calc
    (∑' A : rowMatrixZLattice V n,
        f (T⁻¹ • (((A : rowMatrixRealSpan V n) : M n m (K_ℝ[K]))))) =
        ∑' A : rowMatrixZLattice V n, F (e A) := by
      apply tsum_congr
      intro A
      congr 1
    _ = ∑' A : Fin n → rowZLattice V, F A := e.tsum_eq F
    _ = ∑' A : Fin n → rowZLattice V,
        f (T⁻¹ • (fun i j =>
          (((A i : rowZLattice V) : Fin m → K_ℝ[K]) j))) := by
      rfl

/-- Reindex the rank-conditioned row-matrix lattice sum by the integral
matrices whose rows lie in `Λ_D` and whose rank is `k`. -/
theorem tsum_rowMatrixZLattice_rank_eq_integralRowMatrices
    {m k n : ℕ} (V : Grassmannian K m k)
    (f : M n m (K_ℝ[K]) → ℝ) (T : ℝ) :
    (∑' A : {A : rowMatrixZLattice V n // rowMatrixRank V A = k},
        f (T⁻¹ • (((A.1 : rowMatrixRealSpan V n) :
          M n m (K_ℝ[K]))))) =
      ∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V A ∧ integralMatrixRank A = k},
        f (T⁻¹ • embedMatrix A.1) := by
  let e := rankIntegralRowMatricesEquivRowMatrixZLattice (n := n) V
  simpa [e] using
    (e.tsum_eq
      (fun A : {A : rowMatrixZLattice V n // rowMatrixRank V A = k} =>
        f (T⁻¹ • (((A.1 : rowMatrixRealSpan V n) :
          M n m (K_ℝ[K])))))).symm

theorem summable_rowMatrixTerm
    {m k n : ℕ} (V : Grassmannian K m k)
    {f : M n m (K_ℝ[K]) → ℝ} (h_f : Admissible f)
    {T : ℝ} (hT : 0 < T) :
    Summable (fun A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V A} =>
      f (T⁻¹ • embedMatrix A.1)) := by
  exact (summable_scaled_integralMatrices f h_f hT).comp_injective
    Subtype.val_injective

/-- The exact general-lattice estimate for `M_n(Λ_D)`, before replacing
its dimension, covolume, and radius by the paper's product formulas. -/
theorem Admissible.rowMatrix_latticeRiemann_estimate
    {m k n : ℕ} (V : Grassmannian K m k)
    {f : M n m (K_ℝ[K]) → ℝ} (h_f : Admissible f)
    (hspan : rowMatrixRealSpan V n ≠ ⊥) :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧ ∀ T : ℝ, 0 < T →
      rowMatrixFundamentalRadius V n / T ≤ 1 →
      |(∑' A : {A : IntegralMatrix K n m // rowsInIntegralRowModule V A},
            f (T⁻¹ • embedMatrix A.1)) /
            T ^ Module.finrank ℝ (rowMatrixRealSpan V n) -
          (rowMatrixLatticeCovolume V n)⁻¹ *
            rowMatrixSubspaceIntegral V n f| ≤
        Cₐ * rowMatrixFundamentalRadius V n /
          (rowMatrixLatticeCovolume V n * T) := by
  let msX : MeasurableSpace (M n m (K_ℝ[K])) :=
    borel (M n m (K_ℝ[K]))
  let bsX : @BorelSpace (M n m (K_ℝ[K])) inferInstance msX := ⟨rfl⟩
  let hdisc : DiscreteTopology (rowMatrixZLattice V n) := inferInstance
  let hZ := @IsZLattice.mk ℝ inferInstance (rowMatrixRealSpan V n)
    inferInstance inferInstance (rowMatrixZLattice V n) hdisc
    (rowMatrixZLattice_span_top V n)
  obtain ⟨Cₐ, hCₐ, hestimate⟩ :=
    @Admissible.submodule_latticeRiemann_estimate
      (M n m (K_ℝ[K])) inferInstance inferInstance inferInstance
      msX bsX f h_f (rowMatrixRealSpan V n) hspan
      (rowMatrixZLattice V n) hdisc hZ
  refine ⟨Cₐ, hCₐ, fun T hT hRadius => ?_⟩
  simpa [rowMatrixFundamentalRadius, rowMatrixLatticeCovolume,
    rowMatrixSubspaceIntegral,
    tsum_rowMatrixZLattice_eq_integralRowMatrices V f T] using
    hestimate T hT hRadius

/-- Counting-facing form of the row-matrix estimate.  Under the positive-rank
hypotheses used for fixed-rank matrices, the exponent is the paper's
`n * k * degree K` and the real span is automatically nonzero. -/
theorem Admissible.rowMatrix_latticeRiemann_estimate_rank
    {m k n : ℕ} (V : Grassmannian K m k)
    {f : M n m (K_ℝ[K]) → ℝ} (h_f : Admissible f)
    (hk : 0 < k) (hn : 0 < n) :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧ ∀ T : ℝ, 0 < T →
      rowMatrixFundamentalRadius V n / T ≤ 1 →
      |(∑' A : {A : IntegralMatrix K n m // rowsInIntegralRowModule V A},
            f (T⁻¹ • embedMatrix A.1)) /
            T ^ (n * (k * degree K)) -
          (rowMatrixLatticeCovolume V n)⁻¹ *
            rowMatrixSubspaceIntegral V n f| ≤
        Cₐ * rowMatrixFundamentalRadius V n /
          (rowMatrixLatticeCovolume V n * T) := by
  obtain ⟨Cₐ, hCₐ, hestimate⟩ :=
    h_f.rowMatrix_latticeRiemann_estimate V
      (rowMatrixRealSpan_ne_bot_of_pos V hk hn)
  refine ⟨Cₐ, hCₐ, fun T hT hRadius => ?_⟩
  simpa [rowMatrixRealSpan_finrank V] using hestimate T hT hRadius

end

end Katznelson
