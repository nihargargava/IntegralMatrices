import Katznelson.MainTheorems
import Katznelson.Counting.UniformRiemann

/-!
# Uniform pointwise input for the finite-family assembly

This module supplies the pointwise rank-with-lower estimate used by
`finite_rowMatrix_rank_latticeVoronoi_error_with_mainConstant_bound`.  Its
constants are selected before the scale and before a member of the exact
row-space image of the manuscript's family `\mathcal F_k(T)`.
-/

namespace Katznelson

open Set
open scoped Classical NumberField

attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

/- [derived consequence of paper equations (19)--(21), lines 1667--1696,
   `co:covering_bound`, lines 1239--1248, and `eq:defi_of_calF`, lines
   784--803] Apply the uniform arbitrary-cutoff Riemann estimate to the exact
   row-space image of `\mathcal F_k(T)`.  The explicit cutoff is one larger
   than the fixed covering-radius bound, so both it and the Riemann constant
   are chosen before `T` and `V`.  The conclusion is exactly the pointwise
   rank-with-lower hypothesis of
   `finite_rowMatrix_rank_latticeVoronoi_error_with_mainConstant_bound`; no
   norm, covolume, family, or lower-rank term is replaced. -/
set_option maxHeartbeats 1800000 in
theorem Admissible.exists_uniform_boundedRowSpaces_rank_latticeVoronoi_estimate_with_lower
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    (hk : 0 < k) (hn : 0 < n) (Csup : ℝ) (hCsup : 0 < Csup) :
    ∃ εMax Cₐ : ℝ, 0 < εMax ∧ 0 < Cₐ ∧
      ∀ (T : ℝ), 0 < T →
        ∀ V : boundedRowSpaces
            (K := K) (n := n) (m := m) (k := k) Csup T,
          |(∑' A : {A : rowMatrixZLattice V.1 n //
                rowMatrixRank V.1 A = k},
              f (T⁻¹ • (((A.1 : rowMatrixRealSpan V.1 n) :
                M n m (K_ℝ[K]))))) /
                T ^ (n * (k * degree K)) -
              (rowMatrixLatticeCovolume V.1 n)⁻¹ *
                rowMatrixSubspaceIntegral V.1 n f| ≤
            Cₐ *
                (Real.sqrt (n : ℝ) *
                  latticeCoveringRadius (rowZLattice V.1)) /
              (rowMatrixLatticeCovolume V.1 n * T) +
            |(∑' A : {A : IntegralMatrix K n m //
                rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
              f (T⁻¹ • embedMatrix A.1))| /
                T ^ (n * (k * degree K)) := by
  let ε₀ : ℝ :=
    Real.sqrt (n : ℝ) *
      (Fintype.card (Σ _ : Fin k, IntegralBasisIndex K) : ℝ) *
        rowScalarActionBoundSum (K := K) (m := m) * Csup
  let εMax : ℝ := ε₀ + 1
  have hε₀ : 0 ≤ ε₀ := by
    dsimp [ε₀]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _))
        (rowScalarActionBoundSum_nonneg (K := K) (m := m)))
      hCsup.le
  have hεMax : 0 < εMax := by
    dsimp [εMax]
    linarith
  obtain ⟨Cₐ, hCₐ, hestimate⟩ :=
    h_f.exists_uniform_rowMatrix_rank_latticeVoronoi_estimate_with_lower_upTo
      f hk hn εMax hεMax
  refine ⟨εMax, Cₐ, hεMax, hCₐ, ?_⟩
  intro T hT V
  apply hestimate V.1 T hT
  have hVimage : V.1 ∈
      echelonRowSpace (K := K) ''
        calF (K := K) (l := k) (m := m) (n := n) Csup T := by
    rw [echelon_calF_image_eq_boundedRowSpaces
      (K := K) (l := k) (m := m) (n := n) (Csup := Csup) (T := T)]
    exact V.2
  have hnormalized :
      (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1)) / T ≤
        ε₀ := by
    simpa [ε₀] using
      (echelon_calF_image_matrixCoveringRadius_div_le
        (K := K) (n := n) (m := m) (k := k)
        (Csup := Csup) (T := T) hk hT hVimage)
  exact hnormalized.trans (by dsimp [εMax]; linarith)

end Katznelson
