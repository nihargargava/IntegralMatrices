import Katznelson.Counting.RowLattice
import Katznelson.Counting.SuccessiveMinima

/-!
# Matrix-level bound for the last selected successive minimum

This is the matrix-side part of the paper's proof of `le:injective_minima`.
The echelon-family wrapper is kept in `MinimumInjection` so that the
manuscript's `𝓕_k(T)` interface remains visible there.
-/

namespace Katznelson

open scoped Classical NumberField

attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

variable {K : Type*} [Field K] [NumberField K]

/- [paper, proof of `le:injective_minima`, lines 1221--1225] A rank-`k`
   lattice matrix with bounded Frobenius norm supplies `k` independent rows;
   the row norm estimate and the defining minimum property then bound the
   last selected minimum. -/
set_option maxHeartbeats 2000000 in
theorem rowMatrix_successiveMinimum_last_norm_le_of_rank_eq
    {m k n : ℕ} (V : Grassmannian K m k)
    (A : rowMatrixZLattice V n) (hk : 0 < k)
    {R : ℝ} (hArank : rowMatrixRank V A = k)
    (hAnorm : ‖((A : rowMatrixRealSpan V n) : M n m (K_ℝ[K]))‖ ≤ R) :
    ‖((rowSuccessiveMinimum V ⟨k - 1, by omega⟩ : rowZLattice V) :
        rowRealSpan V)‖ ≤ R := by
  obtain ⟨e, he⟩ :=
    exists_linearIndependent_rows_of_rowMatrixRank_eq V A hArank
  have hbound : ∀ i : Fin k,
      ‖((rowMatrixZLatticeEquiv V A (e i) : rowZLattice V) :
        rowRealSpan V)‖ ≤ R := by
    intro i
    rw [rowMatrixZLatticeEquiv_norm_coe]
    exact (norm_rowVectorOfFun_le_frobenius
      ((A : rowMatrixRealSpan V n) : M n m (K_ℝ[K])) (e i)).trans hAnorm
  have hV : ∃ v : Fin k → rowZLattice V,
      LinearIndependent K (fun i =>
        ((v i : rowZLattice V) : rowRealSpan V)) ∧
      ∀ i, ‖((v i : rowZLattice V) : rowRealSpan V)‖ ≤ R := by
    refine ⟨fun i => rowMatrixZLatticeEquiv V A (e i), he, hbound⟩
  exact rowSuccessiveMinimum_last_norm_le_of_independent_bounded V hk hV

end Katznelson
