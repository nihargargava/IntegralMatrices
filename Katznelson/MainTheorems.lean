import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Logic.Equiv.Basic
import Katznelson.Foundations
import Katznelson.Counting.Admissible
import Katznelson.Counting.FiniteField
import Katznelson.Counting.LiftAverage
import Katznelson.Counting.RowSpaces
import Katznelson.Counting.RowLatticeRiemann
import Katznelson.Counting.Schmidt
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

theorem fixedRankSum_zero
    {K : Type*} [Field K] [NumberField K]
    {n m : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (T : ℝ) :
    fixedRankSum n m 0 f T = f 0 := by
  rw [fixedRankSum]
  have hterm (A : IntegralMatrix K n m) :
      fixedRankTerm (k := 0) f T A =
        if A = 0 then f 0 else 0 := by
    by_cases hA : A = 0
    · subst A
      have hzeroRank :
          integralMatrixRank (0 : IntegralMatrix K n m) = 0 := by
        change Matrix.rank (algebraicMatrix (0 : IntegralMatrix K n m)) = 0
        rw [show algebraicMatrix (0 : IntegralMatrix K n m) = 0 by
          ext i j
          simp [algebraicMatrix]]
        exact Matrix.rank_zero
      rw [fixedRankTerm, hzeroRank]
      have hzeroEmbed : embedMatrix (0 : IntegralMatrix K n m) = 0 := by
        ext i j
        simp [embedMatrix]
      rw [hzeroEmbed]
      simp
    · have hrank : integralMatrixRank A ≠ 0 := by
        intro hrank
        exact hA (integralMatrix_eq_zero_of_integralMatrixRank_eq_zero A hrank)
      simp [fixedRankTerm, hrank, hA]
  rw [show (fun A : IntegralMatrix K n m => fixedRankTerm (k := 0) f T A) =
      (fun A => if A = 0 then f 0 else 0) by funext A; exact hterm A]
  have htsum :
      (∑' A : IntegralMatrix K n m, if A = 0 then f 0 else 0) =
        (if (0 : IntegralMatrix K n m) = 0 then f 0 else 0) :=
    tsum_eq_single (0 : IntegralMatrix K n m) (by
      intro A hA
      simp [hA])
  simpa using htsum

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

/- Partition an integral-matrix sum by algebraic rank.  The index is finite
   because a matrix has rank at most its number of columns. -/
theorem tsum_integralMatrix_eq_sum_rank
    {K : Type*} [Field K] [NumberField K]
    {n m : ℕ} (G : IntegralMatrix K n m → ℝ) (hG : Summable G) :
    ∑' A : IntegralMatrix K n m, G A =
      ∑ k : Fin (m + 1),
        ∑' A : {A : IntegralMatrix K n m // integralMatrixRank A = k.1},
          G A := by
  let rankIndex : IntegralMatrix K n m → Fin (m + 1) := fun A =>
    ⟨integralMatrixRank A, Nat.lt_succ_of_le (by
      change (algebraicMatrix A).rank ≤ m
      exact Matrix.rank_le_width (algebraicMatrix A))⟩
  let e := Equiv.sigmaFiberEquiv rankIndex
  have he : Summable (G ∘ e) := e.summable_iff.mpr hG
  calc
    (∑' A : IntegralMatrix K n m, G A) =
        ∑' A : Σ k : Fin (m + 1), {A : IntegralMatrix K n m //
          rankIndex A = k}, G (e A) := (e.tsum_eq G).symm
    _ = ∑' k : Fin (m + 1), ∑' A : {A : IntegralMatrix K n m //
          rankIndex A = k}, (G ∘ e) ⟨k, A⟩ := he.tsum_sigma
    _ = ∑ k : Fin (m + 1),
        ∑' A : {A : IntegralMatrix K n m // integralMatrixRank A = k.1},
          G A := by
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro k hk
      let fiberEquiv :
          {A : IntegralMatrix K n m // rankIndex A = k} ≃
            {A : IntegralMatrix K n m // integralMatrixRank A = k.1} := by
        let e' :
            {A : IntegralMatrix K n m // rankIndex A = k} ≃
              {A : IntegralMatrix K n m // integralMatrixRank A = k.1} :=
          { toFun := fun A => ⟨A.1, by
                exact congrArg Fin.val A.2⟩
            invFun := fun A => ⟨A.1, by
              apply Fin.ext
              exact A.2⟩
            left_inv := by
              intro A
              rfl
            right_inv := by
              intro A
              rfl }
        exact e'
      simpa [fiberEquiv, e, rankIndex, Function.comp_def] using
        (fiberEquiv.tsum_eq (fun A :
          {A : IntegralMatrix K n m // integralMatrixRank A = k.1} => G A))

/- The preceding partition is the fixed-rank form used in the paper's lift
   argument.  This theorem stops at the exact finite-field correction factor;
   the asymptotic replacement of that factor and the fixed-rank limit are
   handled separately. -/
theorem exists_liftsMoment_eq_sum_fixedRankWeighted
    {K : Type*} [Field K] [NumberField K]
    {n m s : ℕ} (hm : 0 < m) (hmn : m ≤ n) (hms : m ≤ s)
    (hsn : s ≤ n)
    (hcond : 1 - (s : ℝ) / (n : ℝ) < 1 / (m : ℝ))
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f) :
    ∃ Q : ℝ, 0 < Q ∧
      ∀ P : PrimeIdeal K, Q ≤ (idealNorm P : ℝ) →
        liftsMoment P n m s f =
          ∑ k : Fin (m + 1),
            (((idealNorm P : ℝ) ^ (k.1 * (n - s)))⁻¹ *
              codeContainmentCorrection P n s k.1) *
              fixedRankSum n m k.1 f (liftScale P n s) := by
  obtain ⟨Q, hQpos, hfull⟩ := exists_liftsMoment_eq_tsum_rankWeighted
    hm hmn hms hsn hcond f h_f
  refine ⟨Q, hQpos, fun P hP => ?_⟩
  let w : ℕ → ℝ := fun r =>
    ((idealNorm P : ℝ) ^ (r * (n - s)))⁻¹ *
      codeContainmentCorrection P n s r
  let G : IntegralMatrix K n m → ℝ := fun A =>
    f ((liftScale P n s)⁻¹ • embedMatrix A) * w (integralMatrixRank A)
  have hT : 0 < liftScale P n s := liftScale_pos P n s
  have hG : Summable G := by
    apply summable_of_hasFiniteSupport
    refine (finite_scaledSupport_integralMatrices f h_f hT).subset ?_
    intro A hA
    change f ((liftScale P n s)⁻¹ • embedMatrix A) ≠ 0
    intro hfzero
    apply hA
    simp [G, hfzero]
  have hsum :
      ∀ k : Fin (m + 1),
        Summable (fun A : {A : IntegralMatrix K n m //
          integralMatrixRank A = k.1} =>
            f ((liftScale P n s)⁻¹ • embedMatrix A.1)) := by
    intro k
    exact (summable_scaled_integralMatrices f h_f hT).comp_injective
      Subtype.val_injective
  calc
    liftsMoment P n m s f = ∑' A : IntegralMatrix K n m, G A := by
      simpa [G, w] using hfull P hP
    _ = ∑ k : Fin (m + 1),
        ∑' A : {A : IntegralMatrix K n m //
          integralMatrixRank A = k.1}, G A :=
      tsum_integralMatrix_eq_sum_rank G hG
    _ = ∑ k : Fin (m + 1),
        w k.1 * fixedRankSum n m k.1 f (liftScale P n s) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [fixedRankSum_eq_tsum_rank_subtype]
      calc
        (∑' A : {A : IntegralMatrix K n m //
            integralMatrixRank A = k.1}, G A) =
            ∑' A : {A : IntegralMatrix K n m //
              integralMatrixRank A = k.1},
              w k.1 * f ((liftScale P n s)⁻¹ • embedMatrix A.1) := by
          apply tsum_congr
          intro A
          change f ((liftScale P n s)⁻¹ • embedMatrix A.1) *
              w (integralMatrixRank A.1) =
            w k.1 * f ((liftScale P n s)⁻¹ • embedMatrix A.1)
          rw [A.2]
          exact mul_comm _ _
        _ = w k.1 *
            ∑' A : {A : IntegralMatrix K n m //
              integralMatrixRank A = k.1},
              f ((liftScale P n s)⁻¹ • embedMatrix A.1) :=
          (hsum k).tsum_mul_left _
    _ = ∑ k : Fin (m + 1),
        (((idealNorm P : ℝ) ^ (k.1 * (n - s)))⁻¹ *
          codeContainmentCorrection P n s k.1) *
          fixedRankSum n m k.1 f (liftScale P n s) := by
      apply Finset.sum_congr rfl
      intro k hk
      rfl

/- Rewrite the same identity using the paper's scale power rather than the
   equivalent ideal-norm power. -/
theorem exists_liftsMoment_eq_sum_fixedRankScaleWeighted
    {K : Type*} [Field K] [NumberField K]
    {n m s : ℕ} (hm : 0 < m) (hmn : m ≤ n) (hms : m ≤ s)
    (hsn : s ≤ n)
    (hcond : 1 - (s : ℝ) / (n : ℝ) < 1 / (m : ℝ))
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f) :
    ∃ Q : ℝ, 0 < Q ∧
      ∀ P : PrimeIdeal K, Q ≤ (idealNorm P : ℝ) →
        liftsMoment P n m s f =
          ∑ k : Fin (m + 1),
            (((liftScale P n s) ^ (k.1 * n * degree K))⁻¹ *
              codeContainmentCorrection P n s k.1) *
              fixedRankSum n m k.1 f (liftScale P n s) := by
  obtain ⟨Q, hQpos, hweighted⟩ := exists_liftsMoment_eq_sum_fixedRankWeighted
    hm hmn hms hsn hcond f h_f
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  refine ⟨Q, hQpos, fun P hP => ?_⟩
  calc
    liftsMoment P n m s f =
        ∑ k : Fin (m + 1),
          (((idealNorm P : ℝ) ^ (k.1 * (n - s)))⁻¹ *
            codeContainmentCorrection P n s k.1) *
            fixedRankSum n m k.1 f (liftScale P n s) := hweighted P hP
    _ = ∑ k : Fin (m + 1),
          (((liftScale P n s) ^ (k.1 * n * degree K))⁻¹ *
            codeContainmentCorrection P n s k.1) *
            fixedRankSum n m k.1 f (liftScale P n s) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [liftScale_pow_eq_idealNorm_pow P hsn hn]

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

/- The same decomposition written with the paper's row-matrix lattice
   `M_n(Λ_D)`, using the rank-filtered reindexing proved in RowLattice. -/
theorem fixedRankSum_eq_tsum_rowSpaces_rowMatrixZLattice
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    {T : ℝ} (hT : 0 < T) :
    fixedRankSum n m k f T =
      ∑' V : Grassmannian K m k,
        ∑' A : {A : rowMatrixZLattice V n // rowMatrixRank V A = k},
          f (T⁻¹ • (((A.1 : rowMatrixRealSpan V n) :
            M n m (K_ℝ[K])))) := by
  rw [fixedRankSum_eq_tsum_rowSpaces f h_f hT]
  apply tsum_congr
  intro V
  exact (tsum_rowMatrixZLattice_rank_eq_integralRowMatrices V f T).symm

/- The fixed-row-space version of the paper's low-rank decomposition: the
   full row-lattice sum is the rank-k part plus the strictly lower-rank part.
   This is the algebraic split used before applying the induction estimates. -/
theorem rowSpaceSum_eq_rank_add_lower
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (V : Grassmannian K m k)
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    {T : ℝ} (hT : 0 < T) :
    (∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V A},
      f (T⁻¹ • embedMatrix A.1)) =
      (∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule V A ∧ integralMatrixRank A = k},
        f (T⁻¹ • embedMatrix A.1)) +
      (∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule V A ∧ integralMatrixRank A < k},
        f (T⁻¹ • embedMatrix A.1)) := by
  let g : IntegralMatrix K n m → ℝ := fun A =>
    f (T⁻¹ • embedMatrix A)
  let S : Set (IntegralMatrix K n m) :=
    {A | rowsInIntegralRowModule V A}
  let R : Set (IntegralMatrix K n m) :=
    {A | rowsInIntegralRowModule V A ∧ integralMatrixRank A = k}
  let L : Set (IntegralMatrix K n m) :=
    {A | rowsInIntegralRowModule V A ∧ integralMatrixRank A < k}
  have hsum (U : Set (IntegralMatrix K n m)) :
      Summable (fun A : IntegralMatrix K n m => U.indicator g A) := by
    apply summable_of_hasFiniteSupport
    refine (finite_scaledSupport_integralMatrices f h_f hT).subset ?_
    intro A hA
    by_contra hzero
    have hgzero : g A = 0 := not_ne_iff.mp hzero
    apply hA
    simp [g, hgzero]
  have hsplit (A : IntegralMatrix K n m) :
      S.indicator g A = R.indicator g A + L.indicator g A := by
    by_cases hrows : rowsInIntegralRowModule V A
    · have hle := integralMatrixRank_le_of_rowsInIntegralRowModule V A hrows
      obtain hEq | hLt := eq_or_lt_of_le hle
      · simp [S, R, L, hrows, hEq]
      · simp [S, R, L, hrows, hLt, Nat.ne_of_lt hLt]
    · simp [S, R, L, hrows]
  have hS := hsum S
  have hR := hsum R
  have hL := hsum L
  calc
    (∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V A}, g A) =
        ∑' A : IntegralMatrix K n m, S.indicator g A :=
      tsum_subtype S g
    _ = ∑' A : IntegralMatrix K n m,
        (R.indicator g A + L.indicator g A) := by
      exact tsum_congr hsplit
    _ = (∑' A : IntegralMatrix K n m, R.indicator g A) +
        (∑' A : IntegralMatrix K n m, L.indicator g A) :=
      hR.tsum_add hL
    _ = (∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule V A ∧ integralMatrixRank A = k}, g A) +
        (∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule V A ∧ integralMatrixRank A < k}, g A) := by
      rw [(tsum_subtype R g).symm, (tsum_subtype L g).symm]
      rfl
    _ = (∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule V A ∧ integralMatrixRank A = k},
        f (T⁻¹ • embedMatrix A.1)) +
        (∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule V A ∧ integralMatrixRank A < k},
        f (T⁻¹ • embedMatrix A.1)) := by
      rfl

/- The preceding split can also be stated directly for `M_n(Λ_D)`: the
   rank-k lattice sum is the desired term, while the lower-rank integral
   matrices are precisely the correction that the paper estimates by
   induction. -/
theorem rowMatrixZLatticeSum_eq_rank_add_lower
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (V : Grassmannian K m k)
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    {T : ℝ} (hT : 0 < T) :
    (∑' A : rowMatrixZLattice V n,
      f (T⁻¹ • (((A : rowMatrixRealSpan V n) : M n m (K_ℝ[K]))))) =
      (∑' A : {A : rowMatrixZLattice V n // rowMatrixRank V A = k},
        f (T⁻¹ • (((A.1 : rowMatrixRealSpan V n) :
          M n m (K_ℝ[K]))))) +
      (∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule V A ∧ integralMatrixRank A < k},
        f (T⁻¹ • embedMatrix A.1)) := by
  rw [tsum_rowMatrixZLattice_eq_integralRowMatrices V f T]
  rw [rowSpaceSum_eq_rank_add_lower V f h_f hT]
  rw [← tsum_rowMatrixZLattice_rank_eq_integralRowMatrices V f T]

/- The rank-zero row-matrix stratum is the single zero matrix.  This is the
   base case that is separated from the positive-rank induction in the
   manuscript. -/
theorem rowMatrixZLattice_rank_zero_sum
    {K : Type*} [Field K] [NumberField K]
    {m k n : ℕ} (V : Grassmannian K m k)
    (f : M n m (K_ℝ[K]) → ℝ) (T : ℝ) :
    (∑' A : {A : rowMatrixZLattice V n // rowMatrixRank V A = 0},
      f (T⁻¹ • (((A.1 : rowMatrixRealSpan V n) :
        M n m (K_ℝ[K]))))) = f 0 := by
  let z : {A : rowMatrixZLattice V n // rowMatrixRank V A = 0} :=
    ⟨0, (rowMatrixRank_eq_zero_iff V (0 : rowMatrixZLattice V n)).2 rfl⟩
  have hterm (A : {A : rowMatrixZLattice V n // rowMatrixRank V A = 0}) :
      f (T⁻¹ • (((A.1 : rowMatrixRealSpan V n) :
        M n m (K_ℝ[K])))) = if A = z then f 0 else 0 := by
    by_cases hA : A = z
    · subst A
      simp [z]
    · have hzero : A.1 = 0 :=
        (rowMatrixRank_eq_zero_iff V A.1).1 A.2
      exact False.elim (hA (Subtype.ext hzero))
  rw [show (fun A : {A : rowMatrixZLattice V n // rowMatrixRank V A = 0} =>
      f (T⁻¹ • (((A.1 : rowMatrixRealSpan V n) :
        M n m (K_ℝ[K]))))) =
      (fun A => if A = z then f 0 else 0) by funext A; exact hterm A]
  have htsum :
      (∑' A : {A : rowMatrixZLattice V n // rowMatrixRank V A = 0},
        if A = z then f 0 else 0) =
      (if z = z then f 0 else 0) :=
    tsum_eq_single z (by
      intro A hA
      simp [hA])
  simpa using htsum

theorem integralRowMatrices_rank_zero_sum
    {K : Type*} [Field K] [NumberField K]
    {m k n : ℕ} (V : Grassmannian K m k)
    (f : M n m (K_ℝ[K]) → ℝ) (T : ℝ) :
    (∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V A ∧ integralMatrixRank A = 0},
      f (T⁻¹ • embedMatrix A.1)) = f 0 := by
  let z : {A : IntegralMatrix K n m //
      rowsInIntegralRowModule V A ∧ integralMatrixRank A = 0} :=
    ⟨0, ⟨by
      intro i
      exact (integralRowModule V).zero_mem, by
      change Matrix.rank (algebraicMatrix (0 : IntegralMatrix K n m)) = 0
      rw [show algebraicMatrix (0 : IntegralMatrix K n m) = 0 by
        ext i j
        simp [algebraicMatrix]]
      exact Matrix.rank_zero⟩⟩
  have hterm (A : {A : IntegralMatrix K n m //
      rowsInIntegralRowModule V A ∧ integralMatrixRank A = 0}) :
      f (T⁻¹ • embedMatrix A.1) = if A = z then f 0 else 0 := by
    by_cases hA : A = z
    · subst A
      have hzeroEmbed : embedMatrix (0 : IntegralMatrix K n m) = 0 := by
        ext i j
        simp [embedMatrix]
      rw [hzeroEmbed]
      simp
    · have hzero : A.1 = 0 :=
        integralMatrix_eq_zero_of_integralMatrixRank_eq_zero A.1 A.2.2
      exact False.elim (hA (Subtype.ext hzero))
  rw [show (fun A : {A : IntegralMatrix K n m //
      rowsInIntegralRowModule V A ∧ integralMatrixRank A = 0} =>
      f (T⁻¹ • embedMatrix A.1)) =
      (fun A => if A = z then f 0 else 0) by funext A; exact hterm A]
  have htsum :
      (∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V A ∧ integralMatrixRank A = 0},
        if A = z then f 0 else 0) =
      (if z = z then f 0 else 0) :=
    tsum_eq_single z (by
      intro A hA
      simp [hA])
  simpa using htsum

/- Split the lower-rank correction into its individual rank strata, as in
   the induction over `l < k` in the paper. -/
theorem rowSpaceLowerSum_eq_sum_ranks
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (V : Grassmannian K m k)
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    {T : ℝ} (hT : 0 < T) :
    (∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V A ∧ integralMatrixRank A < k},
      f (T⁻¹ • embedMatrix A.1)) =
      ∑ l : Fin k, ∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule V A ∧ integralMatrixRank A = l.1},
        f (T⁻¹ • embedMatrix A.1) := by
  let g : {A : IntegralMatrix K n m //
      rowsInIntegralRowModule V A ∧ integralMatrixRank A < k} → ℝ :=
    fun A => f (T⁻¹ • embedMatrix A.1)
  have hg : Summable g := by
    exact (summable_scaled_integralMatrices f h_f hT).comp_injective
      Subtype.val_injective
  let e :
      (Σ l : Fin k, {A : IntegralMatrix K n m //
          rowsInIntegralRowModule V A ∧ integralMatrixRank A = l.1}) ≃
        {A : IntegralMatrix K n m //
          rowsInIntegralRowModule V A ∧ integralMatrixRank A < k} :=
    { toFun := fun A =>
        ⟨A.2.1, A.2.2.1, by simpa [A.2.2.2] using A.1.isLt⟩
      invFun := fun A =>
        let l : Fin k := ⟨integralMatrixRank A.1, A.2.2⟩
        ⟨l, ⟨A.1, ⟨A.2.1, rfl⟩⟩⟩
      left_inv := by
        intro A
        apply Sigma.subtype_ext
        · apply Fin.ext
          exact A.2.2.2
        · rfl
      right_inv := by
        intro A
        apply Subtype.ext
        rfl }
  have he : Summable (g ∘ e) := e.summable_iff.mpr hg
  calc
    (∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V A ∧ integralMatrixRank A < k}, g A) =
        ∑' A : Σ l : Fin k, {A : IntegralMatrix K n m //
          rowsInIntegralRowModule V A ∧ integralMatrixRank A = l.1},
          g (e A) := (e.tsum_eq g).symm
    _ = ∑' l : Fin k, ∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule V A ∧ integralMatrixRank A = l.1},
          (g ∘ e) ⟨l, A⟩ := he.tsum_sigma
    _ = ∑ l : Fin k, ∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule V A ∧ integralMatrixRank A = l.1},
        f (T⁻¹ • embedMatrix A.1) := by
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro l hl
      apply tsum_congr
      intro A
      rfl

/- A lower-rank matrix in the row lattice of `V` has a unique row space
   `W`, and that row space is contained in `V`.  This is the exact
   row-space version of the regrouping used in the paper's low-rank
   overcount. -/
noncomputable def rowSpaceContainedRankEquiv
    {K : Type*} [Field K] [NumberField K]
    {n m k l : ℕ} (V : Grassmannian K m k) :
    {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V A ∧ integralMatrixRank A = l} ≃
      Σ W : {W : Grassmannian K m l // W.1 ≤ V.1},
        {A : IntegralMatrix K n m //
          rowsInIntegralRowModule W.1 A ∧ integralMatrixRank A = l} := by
  let e0 := rankMatrixEquivRowSpaces (K := K) (n := n) (m := m) (k := l)
  let p : {A : IntegralMatrix K n m // integralMatrixRank A = l} → Prop :=
    fun A => rowsInIntegralRowModule V A.1
  let q : Grassmannian K m l → Prop := fun W => W.1 ≤ V.1
  let qSig : (Σ W : Grassmannian K m l,
      {A : IntegralMatrix K n m //
        rowsInIntegralRowModule W A ∧ integralMatrixRank A = l}) → Prop :=
    fun WA => q WA.1
  have hpq : ∀ A, p A ↔ qSig (e0 A) := by
    intro A
    constructor
    · intro hA
      change q (e0 A).1
      change matrixRowSpace A.1 ≤ V.1
      exact (rowsInIntegralRowModule_iff_rowSpace_le V A.1).1 hA
    · intro hA
      change matrixRowSpace A.1 ≤ V.1 at hA
      exact (rowsInIntegralRowModule_iff_rowSpace_le V A.1).2 hA
  let esub := e0.subtypeEquiv hpq
  let esigma := Equiv.subtypeSigmaEquiv
    (fun W : Grassmannian K m l => {A : IntegralMatrix K n m //
      rowsInIntegralRowModule W A ∧ integralMatrixRank A = l}) q
  let eflat := esub.trans esigma
  let hsource :
      (fun A : IntegralMatrix K n m =>
        rowsInIntegralRowModule V A ∧ integralMatrixRank A = l) =
      (fun A : IntegralMatrix K n m =>
        integralMatrixRank A = l ∧ rowsInIntegralRowModule V A) := by
    funext A
    apply propext
    constructor <;> intro h <;> exact ⟨h.2, h.1⟩
  let esource :
      {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V A ∧ integralMatrixRank A = l} ≃
      {A : {A : IntegralMatrix K n m // integralMatrixRank A = l} //
        rowsInIntegralRowModule V A.1} :=
    (Equiv.subtypeEquivProp hsource).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun A : IntegralMatrix K n m => integralMatrixRank A = l)
        (fun A : IntegralMatrix K n m => rowsInIntegralRowModule V A)).symm
  exact esource.trans eflat

theorem tsum_integralMatrices_in_rowSpace_eq_sum_contained_rowSpaces
    {K : Type*} [Field K] [NumberField K]
    {n m k l : ℕ} (V : Grassmannian K m k)
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    {T : ℝ} (hT : 0 < T) :
    (∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V A ∧ integralMatrixRank A = l},
      f (T⁻¹ • embedMatrix A.1)) =
      ∑' W : {W : Grassmannian K m l // W.1 ≤ V.1},
        ∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule W.1 A ∧ integralMatrixRank A = l},
          f (T⁻¹ • embedMatrix A.1) := by
  let g : {A : IntegralMatrix K n m //
      rowsInIntegralRowModule V A ∧ integralMatrixRank A = l} → ℝ :=
    fun A => f (T⁻¹ • embedMatrix A.1)
  let e := rowSpaceContainedRankEquiv (n := n) (m := m) (k := k) (l := l) V
  have hg : Summable g := by
    exact (summable_scaled_integralMatrices f h_f hT).comp_injective
      Subtype.val_injective
  have hge : Summable (g ∘ e.symm) := e.symm.summable_iff.mpr hg
  calc
    (∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V A ∧ integralMatrixRank A = l}, g A) =
        ∑' WA, g (e.symm WA) := (e.symm.tsum_eq g).symm
    _ = ∑' W : {W : Grassmannian K m l // W.1 ≤ V.1},
        ∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule W.1 A ∧ integralMatrixRank A = l},
          (g ∘ e.symm) ⟨W, A⟩ := hge.tsum_sigma
    _ = ∑' W : {W : Grassmannian K m l // W.1 ≤ V.1},
        ∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule W.1 A ∧ integralMatrixRank A = l},
          f (T⁻¹ • embedMatrix A.1) := by
      apply tsum_congr
      intro W
      apply tsum_congr
      intro A
      have hA : (e.symm ⟨W, A⟩).1 = A.1 := by
        have h := congrArg (fun X => X.2.1) (e.apply_symm_apply ⟨W, A⟩)
        change (e.symm ⟨W, A⟩).1 = A.1 at h
        exact h
      simp [g, hA]

/- Regrouping all strictly lower-rank matrices by their own row space.  The
   `Fin k` index includes rank zero and is the form used by the subsequent
   induction and extension-count estimates. -/
theorem rowSpaceLowerSum_eq_sum_contained_rowSpaces
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (V : Grassmannian K m k)
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    {T : ℝ} (hT : 0 < T) :
    (∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V A ∧ integralMatrixRank A < k},
      f (T⁻¹ • embedMatrix A.1)) =
      ∑ l : Fin k, ∑' W : {W : Grassmannian K m l.1 // W.1 ≤ V.1},
        ∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule W.1 A ∧ integralMatrixRank A = l.1},
          f (T⁻¹ • embedMatrix A.1) := by
  rw [rowSpaceLowerSum_eq_sum_ranks V f h_f hT]
  apply Finset.sum_congr rfl
  intro l hl
  exact tsum_integralMatrices_in_rowSpace_eq_sum_contained_rowSpaces
    V f h_f hT

/- The same regrouping in the lattice notation used by the Riemann-sum
   estimate.  The conversion is rank-filtered, so no lower-rank terms are
   silently identified with full-rank lattice points. -/
theorem rowSpaceLowerSum_eq_sum_contained_rowMatrixZLattices
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (V : Grassmannian K m k)
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    {T : ℝ} (hT : 0 < T) :
    (∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V A ∧ integralMatrixRank A < k},
      f (T⁻¹ • embedMatrix A.1)) =
      ∑ l : Fin k, ∑' W : {W : Grassmannian K m l.1 // W.1 ≤ V.1},
        ∑' A : {A : rowMatrixZLattice W.1 n // rowMatrixRank W.1 A = l.1},
          f (T⁻¹ • (((A.1 : rowMatrixRealSpan W.1 n) :
            M n m (K_ℝ[K])))) := by
  rw [rowSpaceLowerSum_eq_sum_contained_rowSpaces V f h_f hT]
  apply Finset.sum_congr rfl
  intro l hl
  apply tsum_congr
  intro W
  exact (tsum_rowMatrixZLattice_rank_eq_integralRowMatrices W.1 f T).symm

/- A finite-family Fubini/reindexing lemma for the overcount in the paper's
   proof of `le:low_rank_terms` (around lines 1518--1534).  The finite
   support hypothesis is the condition that permits the two summation orders
   to be exchanged without importing an analytic estimate. -/
private theorem sum_indicator_eq_ncard_mul
    {β : Type*} {B : Set β} [Fintype B] (g : ℝ) (r : β → Prop) :
    (∑ b : B, if r b.1 then g else 0) =
      (B ∩ {b | r b}).ncard * g := by
  classical
  rw [show (∑ b : B, if r b.1 then g else 0) =
      (∑ b : B, if r b.1 then (1 : ℝ) else 0) * g by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases h : r b.1 <;> simp [h]]
  rw [Finset.sum_boole]
  have hcard : Fintype.card {b : B // r b.1} =
      (B ∩ {b | r b}).ncard := by
    let hfin : (B ∩ {b | r b}).Finite :=
      (Set.toFinite B).subset Set.inter_subset_left
    letI : Fintype (↥(B ∩ {b | r b})) := hfin.fintype
    let e : {b : B // r b.1} ≃ (↥(B ∩ {b | r b})) :=
      { toFun := fun b => ⟨b.1, b.1.2, b.2⟩
        invFun := fun b => ⟨⟨b.1, b.2.1⟩, b.2.2⟩
        left_inv := by intro b; rfl
        right_inv := by intro b; rfl }
    calc
      Fintype.card {b : B // r b.1} = Fintype.card (↥(B ∩ {b | r b})) :=
        Fintype.card_congr e
      _ = hfin.toFinset.card := hfin.card_toFinset.symm
      _ = (B ∩ {b | r b}).ncard :=
        (Set.ncard_eq_toFinset_card _ hfin).symm
  rw [← Fintype.card_subtype, hcard]

theorem finite_sum_tsum_subtype_eq_tsum_ncard_mul
    {α β : Type*} (B : Set α) [Fintype B] (g : β → ℝ)
    (hg : (Function.support g).Finite) (r : β → α → Prop) :
    (∑ b : B, ∑' x : {x : β // r x b.1}, g x.1) =
      ∑' x : β, ((B ∩ {b | r x b}).ncard : ℝ) * g x := by
  classical
  let F : B → β → ℝ := fun b x => ({x | r x b.1}).indicator g x
  have hsupport : (Function.support (Function.uncurry F)).Finite := by
    refine (Set.finite_univ.prod hg).subset ?_
    intro p hp
    change F p.1 p.2 ≠ 0 at hp
    by_cases hrel : r p.2 p.1.1
    · have hg' : g p.2 ≠ 0 := by
        intro hzero
        apply hp
        simp [F, hrel, hzero]
      exact ⟨Set.mem_univ _, hg'⟩
    · exfalso
      apply hp
      simp [F, hrel]
  have hF : Summable (Function.uncurry F) :=
    summable_of_hasFiniteSupport hsupport
  calc
    (∑ b : B, ∑' x : {x : β // r x b.1}, g x.1) =
        ∑' b : B, ∑' x : {x : β // r x b.1}, g x.1 := by
      rw [tsum_fintype]
    _ = ∑' b : B, ∑' x : β, F b x := by
      apply tsum_congr
      intro b
      exact tsum_subtype ({x : β | r x b.1}) g
    _ = ∑' x : β, ∑' b : B, F b x := hF.tsum_comm.symm
    _ = ∑' x : β, ((B ∩ {b | r x b}).ncard : ℝ) * g x := by
      apply tsum_congr
      intro x
      rw [tsum_fintype]
      exact sum_indicator_eq_ncard_mul (B := B) (g x)
        (fun b : α => r x b)

/- This is the exact finite-family version of the manuscript's `n_k(D')`
   correction.  A lower-rank matrix is first assigned its own row space,
   while the cardinality records how many members of the chosen rank-k
   family contain that row space.  The theorem is deliberately qualitative:
   the paper's bound for this cardinality still needs the projected-lattice
   covolume argument. -/
theorem finite_rowSpaceLowerSum_eq_sum_containedRowSpaceCounts
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (B : Set (Grassmannian K m k)) [Fintype B]
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    {T : ℝ} (hT : 0 < T) :
    (∑ V : B, ∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
      f (T⁻¹ • embedMatrix A.1)) =
      ∑ l : Fin k, ∑' W : Grassmannian K m l.1,
        ((B ∩ {V | W.1 ≤ V.1}).ncard : ℝ) *
          (∑' A : {A : IntegralMatrix K n m //
            rowsInIntegralRowModule W A ∧ integralMatrixRank A = l.1},
            f (T⁻¹ • embedMatrix A.1)) := by
  classical
  let g : ∀ l : Fin k, Grassmannian K m l.1 → ℝ := fun l W =>
    ∑' A : {A : IntegralMatrix K n m //
      rowsInIntegralRowModule W A ∧ integralMatrixRank A = l.1},
      f (T⁻¹ • embedMatrix A.1)
  have hg : ∀ l : Fin k, (Function.support (g l)).Finite := by
    intro l
    let U : Set (IntegralMatrix K n m) :=
      {A | f (T⁻¹ • embedMatrix A) ≠ 0}
    have hU : U.Finite := by
      simpa [U] using finite_scaledSupport_integralMatrices f h_f hT
    let R : Set {A : IntegralMatrix K n m // integralMatrixRank A = l.1} :=
      {A | A.1 ∈ U}
    have hR : R.Finite := by
      apply hU.preimage Subtype.val_injective.injOn
    let S : Set (Grassmannian K m l.1) := rowSpaceOfRank '' R
    have hS : S.Finite := hR.image rowSpaceOfRank
    refine hS.subset ?_
    intro W hW
    by_contra hnot
    have hz : g l W = 0 := by
      rw [← tsum_zero]
      apply tsum_congr
      intro A
      by_contra hA
      apply hnot
      refine ⟨⟨A.1, A.2.2⟩, ?_, ?_⟩
      · change A.1 ∈ U
        change f (T⁻¹ • embedMatrix A.1) ≠ 0 at hA
        exact hA
      · apply Subtype.ext
        exact rowSpace_eq_of_rowsIn_of_rank W A.1 A.2.1 A.2.2
    exact hW hz
  calc
    (∑ V : B, ∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
      f (T⁻¹ • embedMatrix A.1)) =
        ∑ V : B, ∑ l : Fin k, ∑' W : {W : Grassmannian K m l.1 //
          W.1 ≤ V.1}, g l W.1 := by
      apply Finset.sum_congr rfl
      intro V hV
      rw [rowSpaceLowerSum_eq_sum_contained_rowSpaces V.1 f h_f hT]
    _ = ∑ l : Fin k, ∑ V : B, ∑' W : {W : Grassmannian K m l.1 //
          W.1 ≤ V.1}, g l W.1 := by
      rw [Finset.sum_comm]
    _ = ∑ l : Fin k, ∑' W : Grassmannian K m l.1,
        ((B ∩ {V | W.1 ≤ V.1}).ncard : ℝ) * g l W := by
      apply Finset.sum_congr rfl
      intro l hl
      exact finite_sum_tsum_subtype_eq_tsum_ncard_mul B (g l) (hg l)
        (fun W V => W.1 ≤ V.1)
    _ = ∑ l : Fin k, ∑' W : Grassmannian K m l.1,
        ((B ∩ {V | W.1 ≤ V.1}).ncard : ℝ) *
          (∑' A : {A : IntegralMatrix K n m //
            rowsInIntegralRowModule W A ∧ integralMatrixRank A = l.1},
            f (T⁻¹ • embedMatrix A.1)) := by
      apply Finset.sum_congr rfl
      intro l hl
      apply tsum_congr
      intro W
      rfl

/- The lower-rank correction splits into the isolated rank-zero term and the
   positive lower ranks.  This is the form needed before applying the
   induction hypothesis to `1 ≤ l < k`. -/
theorem rowSpaceLowerSum_eq_zero_add_positive_ranks
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (V : Grassmannian K m k)
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    {T : ℝ} (hT : 0 < T) (hk : 0 < k) :
    (∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V A ∧ integralMatrixRank A < k},
      f (T⁻¹ • embedMatrix A.1)) =
      f 0 + ∑ l : Fin (k - 1), ∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V A ∧ integralMatrixRank A = l.succ.1},
        f (T⁻¹ • embedMatrix A.1) := by
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  rw [rowSpaceLowerSum_eq_sum_ranks V f h_f hT]
  rw [Fin.sum_univ_succ]
  have hz := integralRowMatrices_rank_zero_sum V f T
  simpa using hz

/- Combining the two preceding identities gives the row-lattice version of
   the rank induction split: every point is either rank `k` or lies in one of
   the lower rank strata. -/
theorem rowMatrixZLatticeSum_eq_rank_add_ranks
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (V : Grassmannian K m k)
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    {T : ℝ} (hT : 0 < T) :
    (∑' A : rowMatrixZLattice V n,
      f (T⁻¹ • (((A : rowMatrixRealSpan V n) : M n m (K_ℝ[K]))))) =
      (∑' A : {A : rowMatrixZLattice V n // rowMatrixRank V A = k},
        f (T⁻¹ • (((A.1 : rowMatrixRealSpan V n) :
          M n m (K_ℝ[K]))))) +
      ∑ l : Fin k, ∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule V A ∧ integralMatrixRank A = l.1},
        f (T⁻¹ • embedMatrix A.1) := by
  rw [rowMatrixZLatticeSum_eq_rank_add_lower V f h_f hT]
  rw [rowSpaceLowerSum_eq_sum_ranks V f h_f hT]

/- Exponents for the corrected low-rank summation-by-parts argument.  These
   are written in `ℤ` so that the negative powers in the paper's calculation
   are represented without hidden natural-number subtraction. -/
def lowRankHeightExponent (n m k l : ℕ) : ℤ :=
  (m : ℤ) + k - l - n

def lowRankScaleExponent (n m k l : ℕ) : ℤ :=
  ((k : ℤ) - l) * ((m : ℤ) - l) + (n : ℤ) * ((l : ℤ) - k)

theorem lowRankScaleExponent_eq (n m k l : ℕ) :
    lowRankScaleExponent n m k l =
      -((k : ℤ) - l) * ((n : ℤ) - m + l) := by
  dsimp [lowRankScaleExponent]
  ring

theorem lowRankCombinedExponent_eq (n m k l : ℕ) :
    lowRankScaleExponent n m k l + (l : ℤ) * lowRankHeightExponent n m k l =
      -(k : ℤ) * ((n : ℤ) - m) := by
  dsimp [lowRankScaleExponent, lowRankHeightExponent]
  ring

theorem lowRankScaleExponent_le_corrected
    {n m k l : ℕ} (hnm : m < n) (hl : 1 ≤ l) (hlk : l < k) :
    lowRankScaleExponent n m k l ≤
      -((n - m + k - 1 : ℕ) : ℤ) := by
  have hq : 1 ≤ k - l := by omega
  have hb : 0 < n - m + l := by omega
  have hmul : n - m + k - 1 ≤ (k - l) * (n - m + l) := by
    let q : ℕ := k - l
    let b : ℕ := n - m + l
    have hq' : 1 ≤ q := by simpa [q] using hq
    have hb' : 0 < b := by simpa [b] using hb
    have hmul' : b - 1 ≤ q * (b - 1) := by
      simpa using (Nat.mul_le_mul_right (b - 1) hq')
    have hprod : q + b - 1 ≤ q * b := by
      calc
        q + b - 1 = q + (b - 1) := by omega
        _ ≤ q + q * (b - 1) := Nat.add_le_add_left hmul' q
        _ = q * b := by
          calc
            q + q * (b - 1) = q * (b - 1) + q := by omega
            _ = q * (b - 1 + 1) := by simp [Nat.mul_add]
            _ = q * b := by rw [Nat.sub_add_cancel hb']
    dsimp [q, b] at hprod
    omega
  have hcast : ((n - m + k - 1 : ℕ) : ℤ) ≤
      (((k - l) * (n - m + l) : ℕ) : ℤ) := by
    exact_mod_cast hmul
  have hneg : -((((k - l) * (n - m + l) : ℕ) : ℤ)) ≤
      -(((n - m + k - 1 : ℕ) : ℤ)) := neg_le_neg hcast
  calc
    lowRankScaleExponent n m k l =
        -((k : ℤ) - l) * ((n : ℤ) - m + l) :=
      lowRankScaleExponent_eq n m k l
    _ = -((((k - l) * (n - m + l) : ℕ) : ℤ)) := by
      rw [Nat.cast_mul, Nat.cast_sub hlk.le, Nat.cast_add,
        Nat.cast_sub hnm.le]
      ring
    _ ≤ -(((n - m + k - 1 : ℕ) : ℤ)) := hneg

theorem lowRankScaleExponent_le_neg_one
    {n m k l : ℕ} (hnm : m < n) (hl : 1 ≤ l) (hlk : l < k) :
    lowRankScaleExponent n m k l ≤ -1 := by
  have hmain := lowRankScaleExponent_le_corrected hnm hl hlk
  have hpositive : 1 ≤ n - m + k - 1 := by omega
  have hpositive' : (1 : ℤ) ≤ ((n - m + k - 1 : ℕ) : ℤ) := by
    exact_mod_cast hpositive
  omega

/- For `T ≥ 1`, the corrected low-rank exponent is at most the reciprocal
   scale.  This is the direct real-power form of the exponent bookkeeping in
   equation (19) and is useful when assembling the error estimate. -/
theorem lowRankScalePower_le_inv
    {n m k l : ℕ} {T : ℝ} (hT : 1 ≤ T)
    (hnm : m < n) (hl : 1 ≤ l) (hlk : l < k) :
    T ^ (lowRankScaleExponent n m k l : ℤ) ≤ T⁻¹ := by
  rw [← zpow_neg_one]
  exact zpow_le_zpow_right₀ hT
    (lowRankScaleExponent_le_neg_one hnm hl hlk)

/- The fixed-row-space estimate after restoring the rank condition.  This is
   the exact local form of the comparison in the proof of `th:main`; the
   lower-rank sum is left visible for the induction argument. -/
theorem Admissible.rowMatrix_rank_lattice_estimate_with_lower
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (V : Grassmannian K m k)
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    (hk : 0 < k) (hn : 0 < n) :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧ ∀ T : ℝ, 0 < T →
      rowMatrixFundamentalRadius V n / T ≤ 1 →
      |(∑' A : {A : rowMatrixZLattice V n // rowMatrixRank V A = k},
          f (T⁻¹ • (((A.1 : rowMatrixRealSpan V n) :
            M n m (K_ℝ[K]))))) /
            T ^ (n * (k * degree K)) -
          (rowMatrixLatticeCovolume V n)⁻¹ *
            rowMatrixSubspaceIntegral V n f| ≤
        Cₐ * rowMatrixFundamentalRadius V n /
          (rowMatrixLatticeCovolume V n * T) +
        |(∑' A : {A : IntegralMatrix K n m //
            rowsInIntegralRowModule V A ∧ integralMatrixRank A < k},
          f (T⁻¹ • embedMatrix A.1))| /
            T ^ (n * (k * degree K)) := by
  obtain ⟨Cₐ, hCₐ, hestimate⟩ :=
    h_f.rowMatrix_latticeRiemann_estimate_rank V hk hn
  refine ⟨Cₐ, hCₐ, fun T hT hRadius => ?_⟩
  let q : ℝ := T ^ (n * (k * degree K))
  let R : ℝ := ∑' A : {A : rowMatrixZLattice V n // rowMatrixRank V A = k},
    f (T⁻¹ • (((A.1 : rowMatrixRealSpan V n) : M n m (K_ℝ[K]))))
  let L : ℝ := ∑' A : {A : IntegralMatrix K n m //
      rowsInIntegralRowModule V A ∧ integralMatrixRank A < k},
    f (T⁻¹ • embedMatrix A.1)
  let M : ℝ := (rowMatrixLatticeCovolume V n)⁻¹ *
    rowMatrixSubspaceIntegral V n f
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hsplit := rowMatrixZLatticeSum_eq_rank_add_lower V f h_f hT
  have hmain := hestimate T hT hRadius
  rw [← tsum_rowMatrixZLattice_eq_integralRowMatrices V f T] at hmain
  rw [hsplit] at hmain
  have hmain' : |(R + L) / q - M| ≤
      Cₐ * rowMatrixFundamentalRadius V n /
          (rowMatrixLatticeCovolume V n * T) := by
    simpa [R, L, q, M] using hmain
  change |R / q - M| ≤
      Cₐ * rowMatrixFundamentalRadius V n /
          (rowMatrixLatticeCovolume V n * T) + |L| / q
  calc
    |R / q - M| = |(R + L) / q - M - L / q| := by
      congr 1
      field_simp [hq.ne']
      ring
    _ ≤ |(R + L) / q - M| + |L / q| := by
      simpa using (abs_sub_le ((R + L) / q - M) 0 (L / q))
    _ ≤ Cₐ * rowMatrixFundamentalRadius V n /
          (rowMatrixLatticeCovolume V n * T) + |L| / q := by
      rw [abs_div, abs_of_pos hq]
      exact add_le_add hmain' le_rfl

/- Row spaces that can contribute to the fixed-rank sum at scale `T`.  This
   is the Grassmannian version of the paper's support-sensitive family
   `𝓕_k(T)`. -/
def activeRowSpaces
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (T : ℝ) :
    Set (Grassmannian K m k) :=
  {V | ∃ A : IntegralMatrix K n m,
    rowsInIntegralRowModule V A ∧ integralMatrixRank A = k ∧
      f (T⁻¹ • embedMatrix A) ≠ 0}

theorem exists_scaledSupport_integralMatrix_norm_bound
    {K : Type*} [Field K] [NumberField K]
    {n m : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f) :
    ∃ Csup : ℝ, 0 < Csup ∧ ∀ T : ℝ, 0 < T →
      ∀ A : IntegralMatrix K n m,
        f (T⁻¹ • embedMatrix A) ≠ 0 →
          ‖embedMatrix A‖ ≤ Csup * T := by
  obtain ⟨R, hR⟩ :=
    h_f.compactSupport.isBounded.subset_closedBall
      (0 : M n m (K_ℝ[K]))
  let Csup : ℝ := max R 0 + 1
  refine ⟨Csup, ?_, fun T hT A hA => ?_⟩
  · dsimp [Csup]
    linarith [le_max_right R 0]
  · have hSupport : T⁻¹ • embedMatrix A ∈ tsupport f :=
      subset_closure (show T⁻¹ • embedMatrix A ∈ Function.support f from hA)
    have hBall := hR hSupport
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
      Real.norm_eq_abs, abs_inv, abs_of_pos hT] at hBall
    have hnorm : ‖embedMatrix A‖ ≤ R * T := by
      calc
        ‖embedMatrix A‖ = T * (T⁻¹ * ‖embedMatrix A‖) := by
          rw [← mul_assoc, mul_inv_cancel₀ hT.ne', one_mul]
        _ ≤ T * R := mul_le_mul_of_nonneg_left hBall hT.le
        _ = R * T := mul_comm _ _
    exact hnorm.trans (mul_le_mul_of_nonneg_right
      (le_max_left R 0 |>.trans (by linarith)) hT.le)

def boundedRowSpaces
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (Csup T : ℝ) : Set (Grassmannian K m k) :=
  {V | ∃ A : IntegralMatrix K n m,
    rowsInIntegralRowModule V A ∧ integralMatrixRank A = k ∧
      ‖embedMatrix A‖ ≤ Csup * T}

theorem finite_boundedRowSpaces
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (Csup T : ℝ) :
    (boundedRowSpaces (K := K) (n := n) (m := m) (k := k) Csup T).Finite := by
  let U : Set (IntegralMatrix K n m) :=
    {A | ‖embedMatrix A‖ ≤ Csup * T}
  have hU : U.Finite := by
    simpa [U] using finite_integralMatrices_norm_le (K := K) (Csup * T)
  let R : Set {A : IntegralMatrix K n m // integralMatrixRank A = k} :=
    {A | A.1 ∈ U}
  have hR : R.Finite := by
    apply hU.preimage Subtype.val_injective.injOn
  have himage : (rowSpaceOfRank '' R).Finite := hR.image rowSpaceOfRank
  refine himage.subset ?_
  intro V hV
  rcases hV with ⟨A, hrows, hrank, hbound⟩
  refine ⟨⟨A, hrank⟩, ?_, ?_⟩
  · simpa [R, U] using hbound
  · apply Subtype.ext
    exact rowSpace_eq_of_rowsIn_of_rank V A hrows hrank

theorem activeRowSpaces_subset_boundedRowSpaces
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f) :
    ∃ Csup : ℝ, 0 < Csup ∧ ∀ T : ℝ, 0 < T →
      activeRowSpaces (K := K) (k := k) f T ⊆
        boundedRowSpaces (K := K) (n := n) (m := m) (k := k) Csup T := by
  obtain ⟨Csup, hCsup, hbound⟩ :=
    exists_scaledSupport_integralMatrix_norm_bound f h_f
  refine ⟨Csup, hCsup, fun T hT V hV => ?_⟩
  rcases hV with ⟨A, hrows, hrank, hnonzero⟩
  exact ⟨A, hrows, hrank, hbound T hT A hnonzero⟩

theorem finite_activeRowSpaces
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (f : M n m (K_ℝ[K]) → ℝ)
    (h_f : Admissible f) {T : ℝ} (hT : 0 < T) :
    (activeRowSpaces (k := k) f T).Finite := by
  let U : Set (IntegralMatrix K n m) :=
    {A | f (T⁻¹ • embedMatrix A) ≠ 0}
  have hU : U.Finite := by
    simpa [U] using finite_scaledSupport_integralMatrices f h_f hT
  let R : Set {A : IntegralMatrix K n m // integralMatrixRank A = k} :=
    {A | A.1 ∈ U}
  have hR : R.Finite := by
    apply hU.preimage Subtype.val_injective.injOn
  have himage : (rowSpaceOfRank '' R).Finite := hR.image rowSpaceOfRank
  refine himage.subset ?_
  intro V hV
  rcases hV with ⟨A, hrows, hrank, hnonzero⟩
  refine ⟨⟨A, hrank⟩, ?_, ?_⟩
  · simpa [R, U] using hnonzero
  · apply Subtype.ext
    exact rowSpace_eq_of_rowsIn_of_rank V A hrows hrank

theorem fixedRankSum_eq_tsum_activeRowSpaces
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    {T : ℝ} (hT : 0 < T) :
    fixedRankSum n m k f T =
      ∑' V : {V : Grassmannian K m k // V ∈ activeRowSpaces f T},
        ∑' A : {A : IntegralMatrix K n m //
            rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A = k},
          f (T⁻¹ • embedMatrix A.1) := by
  rw [fixedRankSum_eq_tsum_rowSpaces f h_f hT]
  let S : Set (Grassmannian K m k) := activeRowSpaces f T
  let g : Grassmannian K m k → ℝ := fun V =>
    ∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V A ∧ integralMatrixRank A = k},
      f (T⁻¹ • embedMatrix A.1)
  have hgzero (V : Grassmannian K m k) (hV : V ∉ S) : g V = 0 := by
    rw [← tsum_zero]
    apply tsum_congr
    intro A
    by_contra hA
    apply hV
    exact ⟨A.1, A.2.1, A.2.2, hA⟩
  calc
    (∑' V : Grassmannian K m k,
        ∑' A : {A : IntegralMatrix K n m //
            rowsInIntegralRowModule V A ∧ integralMatrixRank A = k},
          f (T⁻¹ • embedMatrix A.1)) = ∑' V, g V := by
      rfl
    _ = ∑' V : Grassmannian K m k, S.indicator g V := by
      apply tsum_congr
      intro V
      by_cases hV : V ∈ S
      · simp [S, hV, g]
      · simp [S, hV, hgzero V hV]
    _ = ∑' V : S, g V := (tsum_subtype S g).symm
    _ = ∑' V : S,
        ∑' A : {A : IntegralMatrix K n m //
            rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A = k},
          f (T⁻¹ • embedMatrix A.1) := by
      rfl

/- The support reduction may be enlarged from active row spaces to the
   norm-bounded family.  The extra row spaces contribute zero, so this is the
   exact finite-family form of the paper's `le:crude_bound`. -/
theorem fixedRankSum_eq_tsum_boundedRowSpaces
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    {T Csup : ℝ} (hT : 0 < T)
    (hactive : activeRowSpaces (K := K) (k := k) f T ⊆
      boundedRowSpaces (K := K) (n := n) (m := m) (k := k) Csup T) :
    fixedRankSum n m k f T =
      ∑' V : {V : Grassmannian K m k //
          V ∈ boundedRowSpaces (K := K) (n := n) (m := m) (k := k) Csup T},
        ∑' A : {A : IntegralMatrix K n m //
            rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A = k},
          f (T⁻¹ • embedMatrix A.1) := by
  rw [fixedRankSum_eq_tsum_activeRowSpaces f h_f hT]
  let S : Set (Grassmannian K m k) := activeRowSpaces f T
  let B : Set (Grassmannian K m k) :=
    boundedRowSpaces (K := K) (n := n) (m := m) (k := k) Csup T
  let g : Grassmannian K m k → ℝ := fun V =>
    ∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V A ∧ integralMatrixRank A = k},
      f (T⁻¹ • embedMatrix A.1)
  have hgzero (V : Grassmannian K m k) (hV : V ∉ S) : g V = 0 := by
    rw [← tsum_zero]
    apply tsum_congr
    intro A
    by_contra hA
    apply hV
    exact ⟨A.1, A.2.1, A.2.2, hA⟩
  have hindicator (V : Grassmannian K m k) :
      S.indicator g V = B.indicator g V := by
    by_cases hS : V ∈ S
    · have hB : V ∈ B := hactive hS
      simp [S, B, hS, hB]
    · have hz := hgzero V hS
      by_cases hB : V ∈ B
      · simp [S, B, hS, hB, hz]
      · simp [S, B, hS, hB]
  calc
    (∑' V : S, g V) =
        ∑' V : Grassmannian K m k, S.indicator g V :=
      tsum_subtype S g
    _ = ∑' V : Grassmannian K m k, B.indicator g V := by
      apply tsum_congr
      exact hindicator
    _ = ∑' V : B, g V := (tsum_subtype B g).symm
    _ = ∑' V : {V : Grassmannian K m k //
        V ∈ boundedRowSpaces (K := K) (n := n) (m := m) (k := k) Csup T},
        ∑' A : {A : IntegralMatrix K n m //
            rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A = k},
          f (T⁻¹ • embedMatrix A.1) := by
      rfl

theorem exists_fixedRankSum_eq_tsum_boundedRowSpaces
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    {T : ℝ} (hT : 0 < T) :
    ∃ Csup : ℝ, 0 < Csup ∧
      fixedRankSum n m k f T =
        ∑' V : {V : Grassmannian K m k //
            V ∈ boundedRowSpaces (K := K) (n := n) (m := m) (k := k) Csup T},
          ∑' A : {A : IntegralMatrix K n m //
              rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A = k},
            f (T⁻¹ • embedMatrix A.1) := by
  obtain ⟨Csup, hCsup, hbound⟩ :=
    activeRowSpaces_subset_boundedRowSpaces f h_f
  exact ⟨Csup, hCsup, fixedRankSum_eq_tsum_boundedRowSpaces f h_f hT
    (hbound T hT)⟩

/- The same finite-family reduction in the row-lattice language used by the
   Riemann-sum estimate. -/
theorem fixedRankSum_eq_tsum_boundedRowSpaces_rowMatrixZLattice
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    {T Csup : ℝ} (hT : 0 < T)
    (hactive : activeRowSpaces (K := K) (k := k) f T ⊆
      boundedRowSpaces (K := K) (n := n) (m := m) (k := k) Csup T) :
    fixedRankSum n m k f T =
      ∑' V : {V : Grassmannian K m k //
          V ∈ boundedRowSpaces (K := K) (n := n) (m := m) (k := k) Csup T},
        ∑' A : {A : rowMatrixZLattice V.1 n // rowMatrixRank V.1 A = k},
          f (T⁻¹ • (((A.1 : rowMatrixRealSpan V.1 n) :
            M n m (K_ℝ[K])))) := by
  rw [fixedRankSum_eq_tsum_boundedRowSpaces f h_f hT hactive]
  apply tsum_congr
  intro V
  exact (tsum_rowMatrixZLattice_rank_eq_integralRowMatrices V.1 f T).symm

theorem exists_fixedRankSum_eq_tsum_boundedRowSpaces_rowMatrixZLattice
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    {T : ℝ} (hT : 0 < T) :
    ∃ Csup : ℝ, 0 < Csup ∧
      fixedRankSum n m k f T =
        ∑' V : {V : Grassmannian K m k //
            V ∈ boundedRowSpaces (K := K) (n := n) (m := m) (k := k) Csup T},
          ∑' A : {A : rowMatrixZLattice V.1 n // rowMatrixRank V.1 A = k},
            f (T⁻¹ • (((A.1 : rowMatrixRealSpan V.1 n) :
              M n m (K_ℝ[K])))) := by
  obtain ⟨Csup, hCsup, hbound⟩ :=
    activeRowSpaces_subset_boundedRowSpaces f h_f
  exact ⟨Csup, hCsup,
    fixedRankSum_eq_tsum_boundedRowSpaces_rowMatrixZLattice f h_f hT
      (hbound T hT)⟩

theorem fixedRankSum_eq_tsum_activeRowSpaces_rowMatrixZLattice
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    {T : ℝ} (hT : 0 < T) :
    fixedRankSum n m k f T =
      ∑' V : {V : Grassmannian K m k // V ∈ activeRowSpaces f T},
        ∑' A : {A : rowMatrixZLattice V.1 n // rowMatrixRank V.1 A = k},
          f (T⁻¹ • (((A.1 : rowMatrixRealSpan V.1 n) :
            M n m (K_ℝ[K])))) := by
  rw [fixedRankSum_eq_tsum_activeRowSpaces f h_f hT]
  apply tsum_congr
  intro V
  exact (tsum_rowMatrixZLattice_rank_eq_integralRowMatrices V.1 f T).symm

/- The main-term constant from the paper's formula (19).  This is indexed by
   the Grassmannian point rather than by a chosen echelon representative.
   The manuscript identifies the corresponding summand with the normalized
   integral over the row-matrix subspace (lines 844--858); the row-space
   indexing is the new Lean replacement for the paper's echelon indexing. -/
noncomputable def mainConstant
    {K : Type*} [Field K] [NumberField K]
    (n m k : ℕ) (f : M n m (K_ℝ[K]) → ℝ) : ℝ :=
  ∑' V : Grassmannian K m k,
    (rowMatrixLatticeCovolume V n)⁻¹ * rowMatrixSubspaceIntegral V n f

/- Error constant and relative error in the statement of `th:main`. -/
opaque errorConstant
    {K : Type*} [Field K] [NumberField K]
    (n m k : ℕ) (f : M n m (K_ℝ[K]) → ℝ) : ℝ

opaque relativeError
    {K : Type*} [Field K] [NumberField K]
    (n m k : ℕ) (f : M n m (K_ℝ[K]) → ℝ) (T : ℝ) : ℝ

/- The limiting expression in Theorem `th:higher_moments`.  The rank-zero
   echelon term is `f 0`; the positive-rank terms are the row-space form of
   the manuscript's normalized echelon integrals. -/
noncomputable def echelonIntegralLimit
    {K : Type*} [Field K] [NumberField K]
    (n m s : ℕ) (f : M n m (K_ℝ[K]) → ℝ) : ℝ :=
  f 0 + ∑ k : Fin m, mainConstant n m (k.1 + 1) f

/- The norm parameter used in the paper is cofinal along the filter on prime
   ideals.  This is the filter form of the phrase `N(P) → ∞`. -/
theorem idealNorm_real_tendsto_atTop
    {K : Type*} [Field K] [NumberField K] :
    Tendsto (fun P : PrimeIdeal K => (idealNorm P : ℝ))
      (comap (idealNorm : PrimeIdeal K → ℕ) atTop) atTop := by
  exact tendsto_natCast_atTop_atTop.comp
    (tendsto_comap : Tendsto (idealNorm : PrimeIdeal K → ℕ)
      (comap (idealNorm : PrimeIdeal K → ℕ) atTop) atTop)

/- Since the admissible parameters always satisfy `s < n`, the normalizing
   scale in (eq:def_of_L) tends to infinity as the prime norm does. -/
theorem liftScale_tendsto_atTop
    {K : Type*} [Field K] [NumberField K]
    {n s : ℕ} (hsn : s < n) :
    Tendsto (fun P : PrimeIdeal K => liftScale P n s)
      (comap (idealNorm : PrimeIdeal K → ℕ) atTop) atTop := by
  have hn : 0 < n := by omega
  have hd : 0 < degree K := Module.finrank_pos
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hdR : 0 < (degree K : ℝ) := by exact_mod_cast hd
  have hsnR : (s : ℝ) < (n : ℝ) := by exact_mod_cast hsn
  have hfrac : (s : ℝ) / (n : ℝ) < 1 := by
    rw [div_lt_iff₀ hnR]
    simpa using hsnR
  have hexp : 0 < (1 - (s : ℝ) / (n : ℝ)) / (degree K : ℝ) :=
    div_pos (sub_pos.mpr hfrac) hdR
  change Tendsto
    (fun P : PrimeIdeal K =>
      Real.rpow (idealNorm P : ℝ)
        ((1 - (s : ℝ) / (n : ℝ)) / (degree K : ℝ)))
    (comap (idealNorm : PrimeIdeal K → ℕ) atTop) atTop
  exact (tendsto_rpow_atTop hexp).comp
    (idealNorm_real_tendsto_atTop (K := K))

/- The `O(N(P)⁻¹)` estimate in `le:counting` is enough to pass from the
   finite-field correction factor to its limiting value. -/
theorem codeContainmentCorrection_tendsto_one
    {K : Type*} [Field K] [NumberField K]
    {n s k : ℕ} (hks : k ≤ s) (hsn : s ≤ n) :
    Tendsto (fun P : PrimeIdeal K => codeContainmentCorrection P n s k)
      (comap (idealNorm : PrimeIdeal K → ℕ) atTop) (𝓝 1) := by
  let C : ℝ :=
    (((s - k : ℕ) : ℝ) * 2 ^ (s - k) + (s : ℝ) * 2 ^ s) * 2 ^ s
  have hnorm : Tendsto (fun P : PrimeIdeal K => (idealNorm P : ℝ))
      (comap (idealNorm : PrimeIdeal K → ℕ) atTop) atTop :=
    idealNorm_real_tendsto_atTop (K := K)
  have hinv : Tendsto (fun P : PrimeIdeal K => (idealNorm P : ℝ)⁻¹)
      (comap (idealNorm : PrimeIdeal K → ℕ) atTop) (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hnorm
  have hright : Tendsto
      (fun P : PrimeIdeal K => C * (idealNorm P : ℝ)⁻¹)
      (comap (idealNorm : PrimeIdeal K → ℕ) atTop) (𝓝 0) := by
    simpa using
      (tendsto_const_nhds (x := C)).mul hinv
  have habs : Tendsto
      (fun P : PrimeIdeal K =>
        |codeContainmentCorrection P n s k - 1|)
      (comap (idealNorm : PrimeIdeal K → ℕ) atTop) (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall (fun P => abs_nonneg _)
    · exact Eventually.of_forall (fun P => by
        simpa [C, codeContainmentError, div_eq_mul_inv] using
          (codeContainmentError_bound P hks hsn))
    · exact hright
  apply tendsto_sub_nhds_zero_iff.1
  exact (tendsto_zero_iff_abs_tendsto_zero _).2 habs

def tendsToAtNorm
    {K : Type*} [Field K] [NumberField K]
    (F : PrimeIdeal K → ℝ) (limit : ℝ) : Prop :=
  Tendsto F (comap (idealNorm : PrimeIdeal K → ℕ) atTop) (𝓝 limit)

end Katznelson
