import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Matrix.Normed
import Katznelson.Foundations
import Katznelson.Counting.Admissible
import Katznelson.Counting.FiniteField
import Katznelson.Counting.RowSpaces
import Katznelson.Lifts

namespace Katznelson

open scoped Classical
open Filter MeasureTheory
open scoped BigOperators NumberField Topology

/- Mathlib keeps matrix norms non-global because several choices are natural;
   the paper's Euclidean matrix norm is represented here by the Frobenius norm. -/
attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

/- `Matrix` is definitionally a finite iterated function space, but its
   product measure instance is not exposed through the matrix wrapper. -/
noncomputable instance matrixMeasureSpace {m n R : Type*} [Fintype m] [Fintype n]
    [MeasureSpace R] :
    MeasureSpace (Matrix m n R) := by
  change MeasureSpace (m → n → R)
  infer_instance

/- The Frobenius norm gives matrices their Euclidean topology.  Make its
   Borel measurable space explicit: typeclass search does not unfold the
   `Matrix` wrapper here. -/
noncomputable local instance matrixMeasurableSpace
    {m n R : Type*} [TopologicalSpace (Matrix m n R)] :
    MeasurableSpace (Matrix m n R) := borel (Matrix m n R)

local instance matrixBorelSpace
    {m n R : Type*} [TopologicalSpace (Matrix m n R)] :
    BorelSpace (Matrix m n R) := ⟨rfl⟩

/- The summand in Theorem `th:main`, with the rank condition made explicit. -/
noncomputable def fixedRankTerm
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (T : ℝ)
    (A : IntegralMatrix K n m) : ℝ :=
  if integralMatrixRank A = k then
    f (T⁻¹ • embedMatrix A)
  else 0

/- The paper's sum over all integral matrices of rank `k`. -/
noncomputable def fixedRankSum
    {K : Type*} [Field K] [NumberField K]
    (n m k : ℕ) (f : M n m (K_ℝ[K]) → ℝ) (T : ℝ) : ℝ :=
  ∑' A : IntegralMatrix K n m, fixedRankTerm (k := k) f T A

@[simp]
theorem fixedRankTerm_of_rank_eq
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (T : ℝ)
    (A : IntegralMatrix K n m)
    (hA : integralMatrixRank A = k) :
    fixedRankTerm (k := k) f T A = f (T⁻¹ • embedMatrix A) := by
  simp [fixedRankTerm, hA]

@[simp]
theorem fixedRankTerm_of_rank_ne
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (T : ℝ)
    (A : IntegralMatrix K n m)
    (hA : integralMatrixRank A ≠ k) :
    fixedRankTerm (k := k) f T A = 0 := by
  simp [fixedRankTerm, hA]

theorem fixedRankSum_eq_tsum_rank_subtype
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (T : ℝ) :
    fixedRankSum n m k f T =
      ∑' A : {A : IntegralMatrix K n m // integralMatrixRank A = k},
        f (T⁻¹ • embedMatrix A) := by
  let S : Set (IntegralMatrix K n m) :=
    {A | integralMatrixRank A = k}
  rw [fixedRankSum]
  change (∑' A : IntegralMatrix K n m, fixedRankTerm (k := k) f T A) =
    ∑' A : S, f (T⁻¹ • embedMatrix A)
  calc
    ∑' A : IntegralMatrix K n m, fixedRankTerm (k := k) f T A =
        ∑' A : IntegralMatrix K n m,
          S.indicator (fun A => f (T⁻¹ • embedMatrix A)) A := by
      apply tsum_congr
      intro A
      by_cases hA : integralMatrixRank A = k
      · simp [S, fixedRankTerm, hA]
      · simp [S, fixedRankTerm, hA]
    _ = ∑' A : S, f (T⁻¹ • embedMatrix A) := by
      exact (tsum_subtype S (fun A : IntegralMatrix K n m =>
        f (T⁻¹ • embedMatrix A))).symm

theorem summable_fixedRankTerm
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    {T : ℝ} (hT : 0 < T) :
    Summable (fun A : IntegralMatrix K n m =>
      fixedRankTerm (k := k) f T A) := by
  apply summable_of_hasFiniteSupport
  refine (finite_scaledSupport_integralMatrices f h_f hT).subset ?_
  intro A hterm
  by_contra hzero
  change ¬f (T⁻¹ • embedMatrix A) ≠ 0 at hzero
  have hfzero : f (T⁻¹ • embedMatrix A) = 0 := not_ne_iff.mp hzero
  apply hterm
  simp [fixedRankTerm, hfzero]

/- Equations `eq:bijection` and `le:new_bijection`: split the rank-`k`
   sum by its rational row space. -/
theorem fixedRankSum_eq_tsum_rowSpaces
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    {T : ℝ} (hT : 0 < T) :
    fixedRankSum n m k f T =
      ∑' V : Grassmannian K m k,
        ∑' A : {A : IntegralMatrix K n m //
            rowsInIntegralRowModule V A ∧ integralMatrixRank A = k},
          f (T⁻¹ • embedMatrix A.1) := by
  rw [fixedRankSum_eq_tsum_rank_subtype]
  let g : {A : IntegralMatrix K n m // integralMatrixRank A = k} → ℝ :=
    fun A => f (T⁻¹ • embedMatrix A.1)
  let e := rankMatrixEquivRowSpaces
    (K := K) (n := n) (m := m) (k := k)
  have hg : Summable g := by
    exact (summable_scaled_integralMatrices f h_f hT).comp_injective
      Subtype.val_injective
  have hge : Summable (g ∘ e.symm) := e.symm.summable_iff.mpr hg
  calc
    (∑' A : {A : IntegralMatrix K n m // integralMatrixRank A = k},
        f (T⁻¹ • embedMatrix A.1)) = ∑' A, g A := rfl
    _ = ∑' VA, g (e.symm VA) := (e.symm.tsum_eq g).symm
    _ = ∑' V : Grassmannian K m k,
        ∑' A : {A : IntegralMatrix K n m //
            rowsInIntegralRowModule V A ∧ integralMatrixRank A = k},
          f (T⁻¹ • embedMatrix A.1) := by
      simpa [g, e, Function.comp_def, rankMatrixEquivRowSpaces] using
        hge.tsum_sigma

/- The main-term constant from the paper's formula (19). -/
opaque mainConstant
    {K : Type*} [Field K] [NumberField K]
    (n m k : ℕ) (f : M n m (K_ℝ[K]) → ℝ) : ℝ

/- Error constant and relative error in the statement of `th:main`. -/
opaque errorConstant
    {K : Type*} [Field K] [NumberField K]
    (n m k : ℕ) (f : M n m (K_ℝ[K]) → ℝ) : ℝ

opaque relativeError
    {K : Type*} [Field K] [NumberField K]
    (n m k : ℕ) (f : M n m (K_ℝ[K]) → ℝ) (T : ℝ) : ℝ

/- The average and echelon-integral limit in Theorem `th:higher_moments` are
   introduced as temporary interfaces until the corresponding definitions are
   proved from the lattice and finite-field constructions. -/
opaque echelonIntegralLimit
    {K : Type*} [Field K] [NumberField K]
    (n m s : ℕ) (f : M n m (K_ℝ[K]) → ℝ) : ℝ

def tendsToAtNorm
    {K : Type*} [Field K] [NumberField K]
    (F : PrimeIdeal K → ℝ) (limit : ℝ) : Prop :=
  Tendsto F (comap (idealNorm : PrimeIdeal K → ℕ) atTop) (𝓝 limit)

end Katznelson
