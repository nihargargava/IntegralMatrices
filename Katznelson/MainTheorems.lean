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
import Katznelson.Counting.Echelon
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

/- Exponents for the corrected low-rank summation-by-parts argument.  These
   are written in `ℤ` so that the negative powers in the paper's calculation
   are represented without hidden natural-number subtraction. -/
def lowRankHeightExponent (n m k l : ℕ) : ℤ :=
  (m : ℤ) + k - l - n

def lowRankScaleExponent (n m k l : ℕ) : ℤ :=
  ((k : ℤ) - l) * ((m : ℤ) - l) + (n : ℤ) * ((l : ℤ) - k)

/- [paper, lines 1612--1618] The manuscript's `α_l` is the exponent of
   `T` coming from the fixed lower-rank lattice estimate.  It is distinct
   from the height exponent `m + k - l - n` and from the quantity `B_l(T)`
   below. -/
def alpha_l (n m k l d : ℕ) : ℤ :=
  (d : ℤ) * lowRankScaleExponent n m k l

/- [paper, lines 1602--1612] The manuscript's `B_l(T)` denotes the entire
   piecewise height-sum bound, including its constant; it is not an exponent.
   The internal `lowRankHeightExponent` is used only to express the three
   cases without natural-number subtraction. -/
noncomputable def B_l (n m k l d : ℕ) (Ccrudenew T : ℝ) : ℝ :=
  Ccrudenew *
    if 0 < lowRankHeightExponent n m k l then
      T ^ ((l * d : ℤ) * lowRankHeightExponent n m k l)
    else if lowRankHeightExponent n m k l = 0 then
      1 + Real.log T
    else 1

/- The absolute-value version of the finite row-space regrouping.  This is
   the step used in the manuscript when it replaces `f` by `|f|`: the
   triangle inequality is applied before the finite overcount is evaluated.
   It only needs the original admissibility hypothesis, since compact
   support gives finite support for both `f` and its pointwise absolute value.
   In particular, it does not assume that the paper's admissibility
   hypothesis has separately been shown to be closed under absolute values. -/
set_option maxHeartbeats 800000 in
theorem finite_rowSpaceLowerSum_abs_le_of_rank_bounds
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (B : Set (Grassmannian K m k)) [Fintype B]
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    {T : ℝ} (hT : 0 < T) :
    (∑ V : B, |∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
        f (T⁻¹ • embedMatrix A.1)|) ≤
      ∑ l : Fin k, ∑' W : Grassmannian K m l.1,
        ((B ∩ {V | W.1 ≤ V.1}).ncard : ℝ) *
          (∑' A : {A : IntegralMatrix K n m //
            rowsInIntegralRowModule W A ∧ integralMatrixRank A = l.1},
            |f (T⁻¹ • embedMatrix A.1)|) := by
  classical
  let g : ∀ l : Fin k, Grassmannian K m l.1 → ℝ := fun l W =>
    ∑' A : {A : IntegralMatrix K n m //
      rowsInIntegralRowModule W A ∧ integralMatrixRank A = l.1},
      f (T⁻¹ • embedMatrix A.1)
  let q : ∀ l : Fin k, Grassmannian K m l.1 → ℝ := fun l W =>
    ∑' A : {A : IntegralMatrix K n m //
      rowsInIntegralRowModule W A ∧ integralMatrixRank A = l.1},
      |f (T⁻¹ • embedMatrix A.1)|
  have hU : ({A : IntegralMatrix K n m |
      f (T⁻¹ • embedMatrix A) ≠ 0}).Finite := by
    simpa using finite_scaledSupport_integralMatrices f h_f hT
  have hq : ∀ l : Fin k, (Function.support (q l)).Finite := by
    intro l
    let R : Set {A : IntegralMatrix K n m // integralMatrixRank A = l.1} :=
      {A | f (T⁻¹ • embedMatrix A.1) ≠ 0}
    have hR : R.Finite := by
      apply hU.preimage Subtype.val_injective.injOn
    let S : Set (Grassmannian K m l.1) := rowSpaceOfRank '' R
    have hS : S.Finite := hR.image rowSpaceOfRank
    refine hS.subset ?_
    intro W hW
    by_contra hnot
    have hz : q l W = 0 := by
      rw [← tsum_zero]
      apply tsum_congr
      intro A
      by_contra hA
      apply hnot
      refine ⟨⟨A.1, A.2.2⟩, ?_, ?_⟩
      · change f (T⁻¹ • embedMatrix A.1) ≠ 0
        exact (abs_ne_zero.mp hA)
      · apply Subtype.ext
        exact rowSpace_eq_of_rowsIn_of_rank W A.1 A.2.1 A.2.2
    exact hW hz
  have hnorm : ∀ (l : Fin k) (W : Grassmannian K m l.1),
      |g l W| ≤ q l W := by
    intro l W
    have hs : Summable (fun A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule W A ∧ integralMatrixRank A = l.1} =>
        f (T⁻¹ • embedMatrix A.1)) := by
      exact (summable_scaled_integralMatrices f h_f hT).comp_injective
        Subtype.val_injective
    have hs' : Summable (fun A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule W A ∧ integralMatrixRank A = l.1} =>
        |f (T⁻¹ • embedMatrix A.1)|) := by
      simpa [Real.norm_eq_abs] using hs.norm
    have hnorm' :
        ‖∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule W A ∧ integralMatrixRank A = l.1},
          f (T⁻¹ • embedMatrix A.1)‖ ≤
        ∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule W A ∧ integralMatrixRank A = l.1},
          ‖f (T⁻¹ • embedMatrix A.1)‖ :=
      norm_tsum_le_tsum_norm hs.norm
    change |∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule W A ∧ integralMatrixRank A = l.1},
        f (T⁻¹ • embedMatrix A.1)| ≤
      ∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule W A ∧ integralMatrixRank A = l.1},
        |f (T⁻¹ • embedMatrix A.1)|
    simpa only [Real.norm_eq_abs] using hnorm'
  have hq_nonneg : ∀ (l : Fin k) (W : Grassmannian K m l.1),
      0 ≤ q l W := by
    intro l W
    dsimp [q]
    exact tsum_nonneg (fun A => abs_nonneg _)
  have hg : ∀ l : Fin k, (Function.support (g l)).Finite := by
    intro l
    apply (hq l).subset
    intro W hW
    change g l W ≠ 0 at hW
    change q l W ≠ 0
    intro hz
    have hqzero : q l W = 0 := by
      exact le_antisymm (by rw [hz]) (hq_nonneg l W)
    have hqle : q l W ≤ 0 := by rw [hz]
    exact hW (abs_eq_zero.mp (le_antisymm ((hnorm l W).trans hqle)
      (abs_nonneg _)))
  have htriangle (l : Fin k) (V : B) :
      |∑' W : {W : Grassmannian K m l.1 // W.1 ≤ V.1}, g l W.1| ≤
        ∑' W : {W : Grassmannian K m l.1 // W.1 ≤ V.1}, q l W.1 := by
    have hs : Summable (fun W : {W : Grassmannian K m l.1 // W.1 ≤ V.1} =>
        g l W.1) := by
      exact (summable_of_hasFiniteSupport ((hg l).preimage
        (Set.injOn_subtype_val)))
    have hs' : Summable (fun W : {W : Grassmannian K m l.1 // W.1 ≤ V.1} =>
        |g l W.1|) := by
      exact hs.norm
    have hq' : Summable (fun W : {W : Grassmannian K m l.1 // W.1 ≤ V.1} =>
        q l W.1) := by
      exact summable_of_hasFiniteSupport ((hq l).preimage
        (Set.injOn_subtype_val))
    calc
      |∑' W : {W : Grassmannian K m l.1 // W.1 ≤ V.1}, g l W.1| ≤
          ∑' W : {W : Grassmannian K m l.1 // W.1 ≤ V.1}, |g l W.1| :=
        norm_tsum_le_tsum_norm hs.norm
      _ ≤ ∑' W : {W : Grassmannian K m l.1 // W.1 ≤ V.1}, q l W.1 := by
        exact hs'.tsum_le_tsum (fun W => hnorm l W.1) hq'
  have hperV (V : B) :
      (∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
        f (T⁻¹ • embedMatrix A.1)) =
      ∑ l : Fin k, ∑' W : {W : Grassmannian K m l.1 // W.1 ≤ V.1},
        g l W.1 := by
    simpa [g] using rowSpaceLowerSum_eq_sum_contained_rowSpaces
      V.1 f h_f hT
  calc
    (∑ V : B, |∑' A : {A : IntegralMatrix K n m //
            rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
          f (T⁻¹ • embedMatrix A.1)|) =
        ∑ V : B, |∑ l : Fin k,
          ∑' W : {W : Grassmannian K m l.1 // W.1 ≤ V.1}, g l W.1| := by
      apply Finset.sum_congr rfl
      intro V hV
      rw [hperV V]
    _ ≤ ∑ V : B, ∑ l : Fin k,
          |∑' W : {W : Grassmannian K m l.1 // W.1 ≤ V.1}, g l W.1| := by
      apply Finset.sum_le_sum
      intro V hV
      simpa only [Real.norm_eq_abs] using
        (norm_sum_le (s := (Finset.univ : Finset (Fin k)))
          (f := fun l : Fin k =>
            ∑' W : {W : Grassmannian K m l.1 // W.1 ≤ V.1}, g l W.1))
    _ = ∑ l : Fin k, ∑ V : B,
          |∑' W : {W : Grassmannian K m l.1 // W.1 ≤ V.1}, g l W.1| := by
      rw [Finset.sum_comm]
    _ ≤ ∑ l : Fin k, ∑ V : B,
          ∑' W : {W : Grassmannian K m l.1 // W.1 ≤ V.1}, q l W.1 := by
      apply Finset.sum_le_sum
      intro l hl
      exact Finset.sum_le_sum (fun V hV => htriangle l V)
    _ = ∑ l : Fin k, ∑' W : Grassmannian K m l.1,
          ((B ∩ {V | W.1 ≤ V.1}).ncard : ℝ) * q l W := by
      apply Finset.sum_congr rfl
      intro l hl
      exact finite_sum_tsum_subtype_eq_tsum_ncard_mul B (q l) (hq l)
        (fun W V => W.1 ≤ V.1)
    _ = ∑ l : Fin k, ∑' W : Grassmannian K m l.1,
          ((B ∩ {V | W.1 ≤ V.1}).ncard : ℝ) *
            (∑' A : {A : IntegralMatrix K n m //
              rowsInIntegralRowModule W A ∧ integralMatrixRank A = l.1},
              |f (T⁻¹ • embedMatrix A.1)|) := by
      apply Finset.sum_congr rfl
      intro l hl
      apply tsum_congr
      intro W
      rfl

/- This is the quantitative form needed by the manuscript's local error
   estimate.  The left side is a sum of absolute values over the rank-k
   family, not the absolute value of the total lower-rank sum.  The positive
   rank terms are therefore supplied as bounds for the nonnegative
   `|f|`-regrouping produced by the preceding theorem. -/
set_option maxHeartbeats 800000 in
theorem finite_rowSpaceLowerSum_normalized_sum_abs_le
    {K : Type*} [Field K] [NumberField K]
    {n m k d : ℕ} (B : Set (Grassmannian K m k)) [Fintype B]
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    {T Csize C₃ Ccrudenew : ℝ}
    (hT : 1 ≤ T) (hnm : m < n) (hk : 1 ≤ k) (hd : 0 < d)
    (hB : (B.ncard : ℝ) ≤ Csize * T ^ (k * m * d))
    (hC₃ : 0 ≤ C₃) (hCcrudenew : 0 ≤ Ccrudenew)
    (hsum_alpha :
      (∑ l ∈ Finset.Ico 1 k,
        T ^ alpha_l n m k l d * B_l n m k l d Ccrudenew T) ≤
      ((Finset.Ico 1 k).card : ℝ) *
        (Ccrudenew * (1 + Real.log T) *
          T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ))))
    (hpoint : ∀ l ∈ Finset.Ico 1 k,
      (∑' W : Grassmannian K m l,
        ((B ∩ {V | W.1 ≤ V.1}).ncard : ℝ) *
          (∑' A : {A : IntegralMatrix K n m //
            rowsInIntegralRowModule W A ∧ integralMatrixRank A = l}, |f
              (T⁻¹ • embedMatrix A.1)|)) /
          T ^ (k * n * d) ≤
        C₃ * T ^ alpha_l n m k l d *
          B_l n m k l d Ccrudenew T) :
    (∑ V : B, |∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
        f (T⁻¹ • embedMatrix A.1)|) /
        T ^ (k * n * d) ≤
      Csize * |f 0| *
          T ^ (-(d : ℤ) * (k : ℤ) * ((n : ℤ) - m)) +
        ((Finset.Ico 1 k).card : ℝ) * C₃ * Ccrudenew *
          (1 + Real.log T) *
          T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ)) := by
  have hden : 0 < T ^ (k * n * d) := by
    exact pow_pos (lt_of_lt_of_le zero_lt_one hT) _
  let u : ℕ → ℝ := fun l =>
    ∑' W : Grassmannian K m l,
      ((B ∩ {V | W.1 ≤ V.1}).ncard : ℝ) *
        (∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule W A ∧ integralMatrixRank A = l},
          |f (T⁻¹ • embedMatrix A.1)|)
  have hreg := finite_rowSpaceLowerSum_abs_le_of_rank_bounds B f h_f
    (lt_of_lt_of_le zero_lt_one hT)
  have hreg' :
      (∑ V : B, |∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
          f (T⁻¹ • embedMatrix A.1)|) ≤
        ∑ l : Fin k, u l.1 := by
    simpa [u] using hreg
  have hu0 : u 0 = (B.ncard : ℝ) * |f 0| := by
    dsimp [u]
    let W₀ : Grassmannian K m 0 := ⟨⊥, by simp⟩
    have htsum :
        (∑' W : Grassmannian K m 0,
          ((B ∩ {V | W.1 ≤ V.1}).ncard : ℝ) *
            (∑' A : {A : IntegralMatrix K n m //
              rowsInIntegralRowModule W A ∧ integralMatrixRank A = 0},
              |f (T⁻¹ • embedMatrix A.1)|)) =
        ((B ∩ {V | W₀.1 ≤ V.1}).ncard : ℝ) *
          (∑' A : {A : IntegralMatrix K n m //
            rowsInIntegralRowModule W₀ A ∧ integralMatrixRank A = 0},
            |f (T⁻¹ • embedMatrix A.1)|) := by
      apply tsum_eq_single W₀
      intro W hW
      have hEq : W = W₀ := Subsingleton.elim W W₀
      exact False.elim (hW hEq)
    have hW₀ : W₀.1 = ⊥ := grassmannian_zeroRank_eq_bot W₀
    have hcontain : B ∩ {V | W₀.1 ≤ V.1} = B := by
      ext V
      constructor
      · intro hV
        exact hV.1
      · intro hV
        refine ⟨hV, ?_⟩
        change W₀.1 ≤ V.1
        rw [hW₀]
        exact bot_le
    have hcount :
        (B ∩ {V | W₀.1 ≤ V.1}).ncard = B.ncard := by
      rw [hcontain]
    have hinner :
        (∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule W₀ A ∧ integralMatrixRank A = 0},
          |f (T⁻¹ • embedMatrix A.1)|) = |f 0| := by
      simpa using integralRowMatrices_rank_zero_sum W₀
        (fun x => |f x|) T
    rw [htsum, hcount, hinner]
  have hzero :
      (B.ncard : ℝ) * |f 0| / T ^ (k * n * d) ≤
        Csize * |f 0| *
          T ^ (-(d : ℤ) * (k : ℤ) * ((n : ℤ) - m)) := by
    have hT₀ : 0 < T := lt_of_lt_of_le zero_lt_one hT
    have hcard : 0 ≤ (B.ncard : ℝ) := by positivity
    have hnum :
        (B.ncard : ℝ) * |f 0| ≤
          (Csize * T ^ (k * m * d)) * |f 0| :=
      mul_le_mul_of_nonneg_right hB (abs_nonneg _)
    have hpow :
        T ^ (k * m * d) / T ^ (k * n * d) =
          T ^ (-(d : ℤ) * (k : ℤ) * ((n : ℤ) - m)) := by
      rw [← zpow_natCast T (k * m * d),
        ← zpow_natCast T (k * n * d), ← zpow_sub₀ hT₀.ne']
      congr 1
      push_cast
      ring
    calc
      (B.ncard : ℝ) * |f 0| / T ^ (k * n * d) ≤
          (Csize * T ^ (k * m * d)) * |f 0| /
            T ^ (k * n * d) :=
        div_le_div_of_nonneg_right hnum hden.le
      _ = Csize * |f 0| *
          (T ^ (k * m * d) / T ^ (k * n * d)) := by ring
      _ = Csize * |f 0| *
          T ^ (-(d : ℤ) * (k : ℤ) * ((n : ℤ) - m)) := by rw [hpow]
  have hsum_point :
      (∑ l ∈ Finset.Ico 1 k, u l / T ^ (k * n * d)) ≤
        ∑ l ∈ Finset.Ico 1 k,
          C₃ * (T ^ alpha_l n m k l d *
            B_l n m k l d Ccrudenew T) := by
    exact Finset.sum_le_sum (fun l hl => by
      simpa [u, mul_assoc] using hpoint l hl)
  have hsum_positive :
      (∑ l ∈ Finset.Ico 1 k, u l / T ^ (k * n * d)) ≤
        ((Finset.Ico 1 k).card : ℝ) * C₃ * Ccrudenew *
          (1 + Real.log T) *
          T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ)) := by
    calc
      (∑ l ∈ Finset.Ico 1 k, u l / T ^ (k * n * d)) ≤
          ∑ l ∈ Finset.Ico 1 k,
            C₃ * (T ^ alpha_l n m k l d *
              B_l n m k l d Ccrudenew T) := hsum_point
      _ = C₃ * ∑ l ∈ Finset.Ico 1 k,
          T ^ alpha_l n m k l d * B_l n m k l d Ccrudenew T := by
        rw [Finset.mul_sum]
      _ ≤ C₃ * (((Finset.Ico 1 k).card : ℝ) *
          (Ccrudenew * (1 + Real.log T) *
            T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ)))) :=
        mul_le_mul_of_nonneg_left hsum_alpha hC₃
      _ = ((Finset.Ico 1 k).card : ℝ) * C₃ * Ccrudenew *
          (1 + Real.log T) *
          T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ)) := by ring
  have hsplit : (∑ l : Fin k, u l) = u 0 +
      ∑ l ∈ Finset.Ico 1 k, u l := by
    rw [Fin.sum_univ_eq_sum_range]
    rw [← Finset.sum_range_add_sum_Ico u hk]
    simp
  have hreg_div :
      (∑ V : B, |∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
          f (T⁻¹ • embedMatrix A.1)|) /
          T ^ (k * n * d) ≤
        u 0 / T ^ (k * n * d) +
          ∑ l ∈ Finset.Ico 1 k, u l / T ^ (k * n * d) := by
    calc
      (∑ V : B, |∑' A : {A : IntegralMatrix K n m //
            rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
          f (T⁻¹ • embedMatrix A.1)|) /
            T ^ (k * n * d) ≤
          (∑ l : Fin k, u l.1) / T ^ (k * n * d) :=
        div_le_div_of_nonneg_right hreg' hden.le
      _ = u 0 / T ^ (k * n * d) +
          ∑ l ∈ Finset.Ico 1 k, u l / T ^ (k * n * d) := by
        rw [hsplit, add_div, Finset.sum_div]
  calc
    (∑ V : B, |∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
        f (T⁻¹ • embedMatrix A.1)|) /
        T ^ (k * n * d) ≤
        u 0 / T ^ (k * n * d) +
          ∑ l ∈ Finset.Ico 1 k, u l / T ^ (k * n * d) := hreg_div
    _ = (B.ncard : ℝ) * |f 0| / T ^ (k * n * d) +
          ∑ l ∈ Finset.Ico 1 k, u l / T ^ (k * n * d) := by rw [hu0]
    _ ≤ Csize * |f 0| *
          T ^ (-(d : ℤ) * (k : ℤ) * ((n : ℤ) - m)) +
          ((Finset.Ico 1 k).card : ℝ) * C₃ * Ccrudenew *
            (1 + Real.log T) *
            T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ)) :=
      add_le_add hzero hsum_positive

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

/- The row-space form of the manuscript's `n_k(D')`: it counts the members of
   a chosen finite rank-`k` family whose row spaces contain `W`. -/
noncomputable def rowSpaceExtensionCount
    {K : Type*} [Field K] [NumberField K]
    {m k l : ℕ} (B : Set (Grassmannian K m k))
    (W : Grassmannian K m l) : ℝ :=
  ((B ∩ {V | W.1 ≤ V.1}).ncard : ℝ)

theorem rowSpaceExtensionCount_nonneg
    {K : Type*} [Field K] [NumberField K]
    {m k l : ℕ} (B : Set (Grassmannian K m k))
    (W : Grassmannian K m l) :
    0 ≤ rowSpaceExtensionCount B W := by
  dsimp [rowSpaceExtensionCount]
  exact_mod_cast Nat.zero_le (B ∩ {V | W.1 ≤ V.1}).ncard

/- The rank-filtered inner matrix sum in the row-space notation used by the
   Riemann-sum estimate.  This is the term denoted by the inner sum over
   `M_n(Λ_{D'})` in the low-rank part of the manuscript. -/
noncomputable def rowSpaceRankSum
    {K : Type*} [Field K] [NumberField K]
    {n m l : ℕ} (W : Grassmannian K m l)
    (f : M n m (K_ℝ[K]) → ℝ) (T : ℝ) : ℝ :=
  ∑' A : {A : IntegralMatrix K n m //
      rowsInIntegralRowModule W A ∧ integralMatrixRank A = l},
    f (T⁻¹ • embedMatrix A.1)

/- The regrouped contribution of a fixed lower rank `l`. -/
noncomputable def rowSpaceLowerStratumTerm
    {K : Type*} [Field K] [NumberField K]
    {n m k l : ℕ} (B : Set (Grassmannian K m k))
    (f : M n m (K_ℝ[K]) → ℝ) (T : ℝ) : ℝ :=
  ∑' W : Grassmannian K m l,
    rowSpaceExtensionCount B W * rowSpaceRankSum W f T

theorem finite_rowSpaceLowerSum_eq_sum_lowerStratumTerms
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (B : Set (Grassmannian K m k)) [Fintype B]
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    {T : ℝ} (hT : 0 < T) :
    (∑ V : B, ∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
      f (T⁻¹ • embedMatrix A.1)) =
      ∑ l : Fin k, rowSpaceLowerStratumTerm (l := l.1) B f T := by
  rw [finite_rowSpaceLowerSum_eq_sum_containedRowSpaceCounts B f h_f hT]
  rfl

theorem rowSpaceLowerStratumTerm_zero_eq
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (B : Set (Grassmannian K m k))
    (f : M n m (K_ℝ[K]) → ℝ) (T : ℝ) :
    rowSpaceLowerStratumTerm (l := 0) B f T =
      (B.ncard : ℝ) * f 0 := by
  let W₀ : Grassmannian K m 0 := ⟨⊥, by simp⟩
  have htsum :
      (∑' W : Grassmannian K m 0,
        rowSpaceExtensionCount B W * rowSpaceRankSum W f T) =
        rowSpaceExtensionCount B W₀ * rowSpaceRankSum W₀ f T := by
    apply tsum_eq_single W₀
    intro W hW
    have hEq : W = W₀ := Subsingleton.elim W W₀
    exact False.elim (hW hEq)
  have hW₀ : W₀.1 = ⊥ := grassmannian_zeroRank_eq_bot W₀
  have hcontain :
      B ∩ {V | W₀.1 ≤ V.1} = B := by
    ext V
    constructor
    · intro hV
      exact hV.1
    · intro hV
      refine ⟨hV, ?_⟩
      change W₀.1 ≤ V.1
      rw [hW₀]
      exact bot_le
  have hcount : rowSpaceExtensionCount B W₀ = (B.ncard : ℝ) := by
    dsimp [rowSpaceExtensionCount]
    rw [hcontain]
  have hinner : rowSpaceRankSum W₀ f T = f 0 := by
    dsimp [rowSpaceRankSum]
    exact integralRowMatrices_rank_zero_sum W₀ f T
  rw [rowSpaceLowerStratumTerm, htsum, hcount, hinner]

/- The normalized rank-zero contribution in lines 1529--1537 of the
   manuscript.  The cardinality estimate for the rank-`k` family is exposed
   as `hB`; the remaining power calculation is proved here. -/
theorem rowSpaceLowerStratumTerm_zero_normalized_le
    {K : Type*} [Field K] [NumberField K]
    {n m k d : ℕ} (B : Set (Grassmannian K m k))
    (f : M n m (K_ℝ[K]) → ℝ) {T Csize : ℝ}
    (hT : 1 ≤ T) (hB : (B.ncard : ℝ) ≤ Csize * T ^ (k * m * d)) :
    |rowSpaceLowerStratumTerm (l := 0) B f T| /
        T ^ (k * n * d) ≤
      Csize * |f 0| *
        T ^ (-(d : ℤ) * (k : ℤ) * ((n : ℤ) - m)) := by
  have hT₀ : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hden : 0 < T ^ (k * n * d) := pow_pos hT₀ _
  have hcard : 0 ≤ (B.ncard : ℝ) := by positivity
  have hnum :
      (B.ncard : ℝ) * |f 0| ≤
        (Csize * T ^ (k * m * d)) * |f 0| :=
    mul_le_mul_of_nonneg_right hB (abs_nonneg _)
  have hpow :
      T ^ (k * m * d) / T ^ (k * n * d) =
        T ^ (-(d : ℤ) * (k : ℤ) * ((n : ℤ) - m)) := by
    rw [← zpow_natCast T (k * m * d),
      ← zpow_natCast T (k * n * d), ← zpow_sub₀ hT₀.ne']
    congr 1
    push_cast
    ring
  rw [rowSpaceLowerStratumTerm_zero_eq B f T]
  rw [abs_mul, abs_of_nonneg hcard]
  calc
    (B.ncard : ℝ) * |f 0| / T ^ (k * n * d) ≤
        (Csize * T ^ (k * m * d)) * |f 0| /
          T ^ (k * n * d) :=
      div_le_div_of_nonneg_right hnum (le_of_lt hden)
    _ = Csize * |f 0| *
          (T ^ (k * m * d) / T ^ (k * n * d)) := by ring
    _ = Csize * |f 0| *
          T ^ (-(d : ℤ) * (k : ℤ) * ((n : ℤ) - m)) := by rw [hpow]

/- The finite rank decomposition has one rank-zero stratum and the positive
   strata `1 ≤ l < k`.  This is the exact finite-index splitting used before
   the induction estimate in the manuscript. -/
theorem sum_fin_lowerStratum_eq_zero_add_positive
    {k : ℕ} (hk : 1 ≤ k) (u : ℕ → ℝ) :
    (∑ l : Fin k, u l) = u 0 + ∑ l ∈ Finset.Ico 1 k, u l := by
  rw [Fin.sum_univ_eq_sum_range]
  rw [← Finset.sum_range_add_sum_Ico u hk]
  simp

theorem finite_rowSpaceLowerSum_eq_zero_add_positive_terms
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (B : Set (Grassmannian K m k)) [Fintype B]
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    {T : ℝ} (hT : 0 < T) (hk : 1 ≤ k) :
    (∑ V : B, ∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
      f (T⁻¹ • embedMatrix A.1)) =
      (B.ncard : ℝ) * f 0 +
        ∑ l ∈ Finset.Ico 1 k,
          rowSpaceLowerStratumTerm (l := l) B f T := by
  rw [finite_rowSpaceLowerSum_eq_sum_lowerStratumTerms B f h_f hT]
  let u : ℕ → ℝ := fun l => rowSpaceLowerStratumTerm (l := l) B f T
  have hsplit := sum_fin_lowerStratum_eq_zero_add_positive hk u
  change (∑ l : Fin k, u l) = _
  rw [hsplit]
  have hu0 : u 0 = (B.ncard : ℝ) * f 0 := by
    dsimp [u]
    exact rowSpaceLowerStratumTerm_zero_eq B f T
  rw [hu0]

/- The natural-number exponent used by the inverse-height shell sum has the
   same three cases as the manuscript's integer exponent
   `m + k - l - n`. -/
theorem lowRankHeightExponent_pos_iff
    {n m k l : ℕ} (hnm : m < n) (hkm : k ≤ m) (hlk : l < k) :
    n + l - k < m ↔ 0 < lowRankHeightExponent n m k l := by
  have hk : k ≤ n + l := by omega
  have hqcast : ((n + l - k : ℕ) : ℤ) = (n : ℤ) + l - k := by
    rw [Nat.cast_sub hk]
    push_cast
    ring
  have heq : lowRankHeightExponent n m k l =
      (m : ℤ) - ((n + l - k : ℕ) : ℤ) := by
    dsimp [lowRankHeightExponent]
    rw [hqcast]
    ring
  constructor
  · intro h
    rw [heq]
    have h' : (n + l - k : ℤ) < m := by exact_mod_cast h
    omega
  · intro h
    rw [heq] at h
    have h' : (n + l - k : ℤ) < m := by omega
    exact_mod_cast h'

theorem lowRankHeightExponent_eq_zero_iff
    {n m k l : ℕ} (hnm : m < n) (hkm : k ≤ m) (hlk : l < k) :
    m = n + l - k ↔ lowRankHeightExponent n m k l = 0 := by
  have hk : k ≤ n + l := by omega
  have hqcast : ((n + l - k : ℕ) : ℤ) = (n : ℤ) + l - k := by
    rw [Nat.cast_sub hk]
    push_cast
    ring
  have heq : lowRankHeightExponent n m k l =
      (m : ℤ) - ((n + l - k : ℕ) : ℤ) := by
    dsimp [lowRankHeightExponent]
    rw [hqcast]
    ring
  constructor
  · intro h
    rw [heq]
    have h' : (m : ℤ) = (n + l - k : ℕ) := by exact_mod_cast h
    omega
  · intro h
    rw [heq] at h
    have h' : (m : ℤ) = (n + l - k : ℕ) := by omega
    exact_mod_cast h'

theorem lowRankHeightExponent_neg_iff
    {n m k l : ℕ} (hnm : m < n) (hkm : k ≤ m) (hlk : l < k) :
    m < n + l - k ↔ lowRankHeightExponent n m k l < 0 := by
  have hk : k ≤ n + l := by omega
  have hqcast : ((n + l - k : ℕ) : ℤ) = (n : ℤ) + l - k := by
    rw [Nat.cast_sub hk]
    push_cast
    ring
  have heq : lowRankHeightExponent n m k l =
      (m : ℤ) - ((n + l - k : ℕ) : ℤ) := by
    dsimp [lowRankHeightExponent]
    rw [hqcast]
    ring
  constructor
  · intro h
    rw [heq]
    have h' : (m : ℤ) < (n + l - k : ℕ) := by exact_mod_cast h
    omega
  · intro h
    rw [heq] at h
    have h' : (m : ℤ) < (n + l - k : ℕ) := by omega
    exact_mod_cast h'

/- [paper, lines 1612--1626] Notation bridge for the exponent calculation
   that applies to the power term in `B_l(T)` when its positive-height
   branch is selected. -/
theorem alpha_l_add_heightExponent_eq
    (n m k l d : ℕ) :
    alpha_l n m k l d +
        (l * d : ℤ) * lowRankHeightExponent n m k l =
      -(d : ℤ) * (k : ℤ) * ((n : ℤ) - m) := by
  dsimp [alpha_l]
  dsimp [lowRankScaleExponent, lowRankHeightExponent]
  ring

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

/- The same identity with the number-field degree restored.  This is the
   exponent appearing after the inner lattice count and the height sum are
   multiplied in the manuscript's low-rank estimate. -/
theorem lowRankCombinedExponent_mul_degree_eq
    (n m k l d : ℕ) :
    (d : ℤ) * lowRankScaleExponent n m k l +
        (l * d : ℤ) * lowRankHeightExponent n m k l =
      -(d : ℤ) * (k : ℤ) * ((n : ℤ) - m) := by
  calc
    (d : ℤ) * lowRankScaleExponent n m k l +
        (l * d : ℤ) * lowRankHeightExponent n m k l =
      (d : ℤ) * (lowRankScaleExponent n m k l +
        (l : ℤ) * lowRankHeightExponent n m k l) := by
          ring
    _ = (d : ℤ) * (-(k : ℤ) * ((n : ℤ) - m)) := by
      rw [lowRankCombinedExponent_eq]
    _ = -(d : ℤ) * (k : ℤ) * ((n : ℤ) - m) := by ring

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

theorem lowRankScaleExponent_mul_degree_le_neg_degree
    {n m k l d : ℕ} (hd : 0 < d)
    (hnm : m < n) (hl : 1 ≤ l) (hlk : l < k) :
    (d : ℤ) * lowRankScaleExponent n m k l ≤ -(d : ℤ) := by
  have hscale := lowRankScaleExponent_le_neg_one hnm hl hlk
  have hdnonneg : (0 : ℤ) ≤ d := by exact_mod_cast hd.le
  calc
    (d : ℤ) * lowRankScaleExponent n m k l ≤ (d : ℤ) * (-1) :=
      mul_le_mul_of_nonneg_left hscale hdnonneg
    _ = -(d : ℤ) := by ring

/- Degree-scaled form of the reciprocal-scale estimate. -/
theorem lowRankScalePower_mul_degree_le_inv_degree
    {n m k l d : ℕ} {T : ℝ} (hT : 1 ≤ T) (hd : 0 < d)
    (hnm : m < n) (hl : 1 ≤ l) (hlk : l < k) :
    T ^ ((d : ℤ) * lowRankScaleExponent n m k l) ≤
      T ^ (-(d : ℤ)) := by
  exact zpow_le_zpow_right₀ hT
    (lowRankScaleExponent_mul_degree_le_neg_degree hd hnm hl hlk)

/- The common exponent used after the three cases in the manuscript's
   definition of `B_l(T)`.  This is the arithmetic comparison needed before
   the analytic low-rank estimate can be assembled. -/
theorem lowRankCombinedExponent_le_corrected
    {n m k l d : ℕ} (hd : 0 < d)
    (hnm : m < n) (hl : 1 ≤ l) (hlk : l < k) :
    -(d : ℤ) * (k : ℤ) * ((n : ℤ) - m) ≤
      -(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ) := by
  have hA : 1 ≤ n - m := by omega
  have hk : 1 ≤ k := by omega
  have hmul_sub : k - 1 ≤ (k - 1) * (n - m) := by
    calc
      k - 1 = (k - 1) * 1 := by simp
      _ ≤ (k - 1) * (n - m) := Nat.mul_le_mul_left _ hA
  have hmul : n - m + k - 1 ≤ k * (n - m) := by
    calc
      n - m + k - 1 = (n - m) + (k - 1) := by omega
      _ ≤ (n - m) + (k - 1) * (n - m) :=
        Nat.add_le_add_left hmul_sub _
      _ = ((k - 1) + 1) * (n - m) := by ring
      _ = k * (n - m) := by rw [Nat.sub_add_cancel hk]
  have hmul' : d * (n - m + k - 1) ≤ d * (k * (n - m)) :=
    Nat.mul_le_mul_left d hmul
  have hneg :
      -((d * (k * (n - m)) : ℕ) : ℤ) ≤
        -((d * (n - m + k - 1) : ℕ) : ℤ) := by
    exact neg_le_neg (by exact_mod_cast hmul')
  simpa [Nat.cast_mul, Nat.cast_sub hnm.le, mul_assoc] using hneg

theorem alpha_l_le_corrected
    {n m k l d : ℕ} (hd : 0 < d)
    (hnm : m < n) (hl : 1 ≤ l) (hlk : l < k) :
    alpha_l n m k l d ≤
      -(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ) := by
  have hdnonneg : (0 : ℤ) ≤ d := by exact_mod_cast hd.le
  calc
    alpha_l n m k l d = (d : ℤ) * lowRankScaleExponent n m k l := rfl
    _ ≤ (d : ℤ) * (-((n - m + k - 1 : ℕ) : ℤ)) := by
      exact mul_le_mul_of_nonneg_left
        (lowRankScaleExponent_le_corrected hnm hl hlk) hdnonneg
    _ = -(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ) := by ring

/- [paper, lines 1612--1631] The three branches of the manuscript's
   `B_l(T)` estimate have a common, valid decay bound.  This theorem keeps
   `alpha_l` and `B_l(T)` visible, so the arithmetic does not get hidden in a
   replacement notation. -/
theorem alpha_l_mul_B_l_le_corrected
    {n m k l d : ℕ} {Ccrudenew T : ℝ}
    (hC : 0 ≤ Ccrudenew) (hT : 1 ≤ T) (hd : 0 < d)
    (hnm : m < n) (hl : 1 ≤ l) (hlk : l < k) :
    T ^ alpha_l n m k l d * B_l n m k l d Ccrudenew T ≤
      Ccrudenew * (1 + Real.log T) *
        T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ)) := by
  have hT0 : T ≠ 0 := by linarith
  have hTnonneg : 0 ≤ T := by linarith
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT
  have hfactor : 1 ≤ 1 + Real.log T := by linarith
  have hfactor_nonneg : 0 ≤ 1 + Real.log T := le_trans (by norm_num) hfactor
  have htarget_nonneg :
      0 ≤ T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ)) :=
    zpow_nonneg hTnonneg _
  have htarget_le :
      T ^ alpha_l n m k l d ≤
        T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ)) := by
    exact zpow_le_zpow_right₀ hT
      (alpha_l_le_corrected hd hnm hl hlk)
  have hcombined_exp :=
    lowRankCombinedExponent_le_corrected hd hnm hl hlk
  have hcombined_pow :
      T ^ (-(d : ℤ) * (k : ℤ) * ((n : ℤ) - m)) ≤
        T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ)) :=
    zpow_le_zpow_right₀ hT hcombined_exp
  have hcombined_with_factor :
      T ^ (-(d : ℤ) * (k : ℤ) * ((n : ℤ) - m)) ≤
        (1 + Real.log T) *
          T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ)) := by
    calc
      T ^ (-(d : ℤ) * (k : ℤ) * ((n : ℤ) - m)) ≤
          1 * T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ)) := by
        simpa using hcombined_pow
      _ ≤ (1 + Real.log T) *
          T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ)) :=
        mul_le_mul_of_nonneg_right hfactor htarget_nonneg
  by_cases hpos : 0 < lowRankHeightExponent n m k l
  · simp only [B_l, hpos, if_pos]
    calc
      T ^ alpha_l n m k l d *
          (Ccrudenew * T ^ ((l * d : ℤ) *
            lowRankHeightExponent n m k l)) =
          Ccrudenew *
            (T ^ alpha_l n m k l d *
              T ^ ((l * d : ℤ) * lowRankHeightExponent n m k l)) := by
        ring
      _ = Ccrudenew *
          T ^ (alpha_l n m k l d +
            (l * d : ℤ) * lowRankHeightExponent n m k l) := by
        rw [← zpow_add₀ hT0]
      _ = Ccrudenew *
          T ^ (-(d : ℤ) * (k : ℤ) * ((n : ℤ) - m)) := by
        rw [alpha_l_add_heightExponent_eq]
      _ ≤ Ccrudenew *
          ((1 + Real.log T) *
            T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ))) :=
        mul_le_mul_of_nonneg_left hcombined_with_factor hC
      _ = Ccrudenew * (1 + Real.log T) *
          T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ)) := by ring
  · by_cases hzero : lowRankHeightExponent n m k l = 0
    · simp only [B_l, if_neg hpos, if_pos hzero]
      have halpha_eq :
          alpha_l n m k l d =
            -(d : ℤ) * (k : ℤ) * ((n : ℤ) - m) := by
        have h := alpha_l_add_heightExponent_eq n m k l d
        rw [hzero, mul_zero, add_zero] at h
        exact h
      have halpha_pow :
          T ^ alpha_l n m k l d ≤
            T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ)) := by
        rw [halpha_eq]
        exact hcombined_pow
      calc
        T ^ alpha_l n m k l d * (Ccrudenew * (1 + Real.log T)) =
            Ccrudenew * (1 + Real.log T) *
              T ^ alpha_l n m k l d := by ring
        _ ≤ Ccrudenew * (1 + Real.log T) *
            T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ)) :=
          mul_le_mul_of_nonneg_left halpha_pow
            (mul_nonneg hC hfactor_nonneg)
    · simp only [B_l, if_neg hpos, if_neg hzero, mul_one]
      calc
        T ^ alpha_l n m k l d * Ccrudenew ≤
            Ccrudenew *
              T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ)) := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left htarget_le hC
        _ ≤ Ccrudenew * (1 + Real.log T) *
            T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ)) := by
          have hCfactor : Ccrudenew ≤ Ccrudenew * (1 + Real.log T) := by
            calc
              Ccrudenew = Ccrudenew * 1 := by ring
              _ ≤ Ccrudenew * (1 + Real.log T) :=
                mul_le_mul_of_nonneg_left hfactor hC
          exact mul_le_mul_of_nonneg_right hCfactor htarget_nonneg

/- [paper, lines 1617--1631] The pointwise branch estimate can now be summed
   over the manuscript's range `1 ≤ l < k`.  The finite cardinality is left
   explicit here; for fixed `k` it is absorbed into the constant exactly as
   in the paper. -/
theorem sum_alpha_l_mul_B_l_le_corrected
    {n m k d : ℕ} {Ccrudenew T : ℝ}
    (hC : 0 ≤ Ccrudenew) (hT : 1 ≤ T) (hd : 0 < d)
    (hnm : m < n) (hk : 1 ≤ k) :
    (∑ l ∈ Finset.Ico 1 k,
      T ^ alpha_l n m k l d * B_l n m k l d Ccrudenew T) ≤
      ((Finset.Ico 1 k).card : ℝ) *
        (Ccrudenew * (1 + Real.log T) *
          T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ))) := by
  have hterm : ∀ l ∈ Finset.Ico 1 k,
      T ^ alpha_l n m k l d * B_l n m k l d Ccrudenew T ≤
        Ccrudenew * (1 + Real.log T) *
          T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ)) := by
    intro l hl
    have hl' := Finset.mem_Ico.mp hl
    exact alpha_l_mul_B_l_le_corrected hC hT hd hnm hl'.1 hl'.2
  calc
    (∑ l ∈ Finset.Ico 1 k,
        T ^ alpha_l n m k l d * B_l n m k l d Ccrudenew T) ≤
        ∑ l ∈ Finset.Ico 1 k,
          Ccrudenew * (1 + Real.log T) *
            T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ)) := by
      exact Finset.sum_le_sum (fun l hl => hterm l hl)
    _ = ((Finset.Ico 1 k).card : ℝ) *
        (Ccrudenew * (1 + Real.log T) *
          T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ))) := by
      simp

/- This is the positive-rank height-summation step in equations (19)--(21) of
   the manuscript.  The function `w` is the product of the extension count
   `n_k(D')` and the rank-`l` inner matrix sum.  The pointwise estimate is left
   explicit because its projected-lattice proof is the separate missing
   geometry-of-numbers module; the height summation itself is proved here. -/
theorem single_lower_rank_height_term_le
    {K : Type*} [Field K] [NumberField K]
    {n m k l d : ℕ} {T C₃ : ℝ} (hT : 1 ≤ T)
    (hnm : m < n) (hkm : k ≤ m) (hl : 1 ≤ l) (hlk : l < k)
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := l)) m)
    {b : ℕ} (hb : 1 ≤ b)
    (S : Set (Grassmannian K m l)) (hS : S.Finite)
    (hS_one : ∀ W ∈ S, 1 ≤ rowSpaceHeight W)
    (hS_bound : ∀ W ∈ S, rowSpaceHeight W ≤ (b : ℝ))
    (w : Grassmannian K m l → ℝ)
    (hzero : ∀ W ∉ S, w W = 0) (hC₃ : 0 ≤ C₃)
    (hpoint : ∀ W ∈ S,
      |w W| ≤ C₃ * T ^ alpha_l n m k l d *
        (rowSpaceHeight W) ^ ((k : ℤ) - l - n)) :
    ∃ D : ℝ, 0 < D ∧
      |∑' W : Grassmannian K m l, w W| ≤
        if n + l - k < m then
          C₃ * D * T ^ alpha_l n m k l d *
            (b : ℝ) ^ ((m - (n + l - k) : ℕ) : ℝ)
        else if m = n + l - k then
          C₃ * D * T ^ alpha_l n m k l d *
            (1 + Real.log (b : ℝ))
        else C₃ * D * T ^ alpha_l n m k l d := by
  let Cscale : ℝ := C₃ * T ^ alpha_l n m k l d
  have hCscale : 0 ≤ Cscale := by
    dsimp [Cscale]
    exact mul_nonneg hC₃ (zpow_nonneg (by linarith) _)
  have hk_nl : k ≤ n + l := by omega
  have hqcast : ((n + l - k : ℕ) : ℤ) = (n : ℤ) + l - k := by
    rw [Nat.cast_sub hk_nl]
    push_cast
    ring
  have hexp : (k : ℤ) - l - n = -((n + l - k : ℕ) : ℤ) := by
    rw [hqcast]
    ring
  have hpoint' : ∀ W ∈ S,
      |w W| ≤ Cscale * (rowSpaceHeight W)⁻¹ ^ (n + l - k) := by
    intro W hW
    calc
      |w W| ≤ C₃ * T ^ alpha_l n m k l d *
          (rowSpaceHeight W) ^ ((k : ℤ) - l - n) := hpoint W hW
      _ = Cscale * (rowSpaceHeight W)⁻¹ ^ (n + l - k) := by
        rw [hexp, zpow_neg, zpow_natCast, inv_pow]
  obtain ⟨D, hD, hbound⟩ :=
    tsum_abs_le_finite_height_inv_pow hcount hb w S hS hS_one hS_bound
      hzero Cscale hCscale hpoint'
  refine ⟨D, hD, ?_⟩
  by_cases hqpm : n + l - k < m
  · have hbound' :
        |∑' W : Grassmannian K m l, w W| ≤
          Cscale * D * (b : ℝ) ^ ((m - (n + l - k) : ℕ) : ℝ) := by
      simpa only [if_pos hqpm] using hbound
    have htarget :
        |∑' W : Grassmannian K m l, w W| ≤
          C₃ * D * T ^ alpha_l n m k l d *
            (b : ℝ) ^ ((m - (n + l - k) : ℕ) : ℝ) := by
      calc
      |∑' W : Grassmannian K m l, w W| ≤
          Cscale * D * (b : ℝ) ^ ((m - (n + l - k) : ℕ) : ℝ) := hbound'
      _ = C₃ * D * T ^ alpha_l n m k l d *
          (b : ℝ) ^ ((m - (n + l - k) : ℕ) : ℝ) := by
        dsimp [Cscale]
        ring
    simpa only [if_pos hqpm] using htarget
  · by_cases hmeq : m = n + l - k
    · have hbound' :
          |∑' W : Grassmannian K m l, w W| ≤
            Cscale * D * (1 + Real.log (b : ℝ)) := by
        simpa only [if_neg hqpm, if_pos hmeq] using hbound
      have htarget :
          |∑' W : Grassmannian K m l, w W| ≤
            C₃ * D * T ^ alpha_l n m k l d *
              (1 + Real.log (b : ℝ)) := by
        calc
        |∑' W : Grassmannian K m l, w W| ≤
            Cscale * D * (1 + Real.log (b : ℝ)) := hbound'
        _ = C₃ * D * T ^ alpha_l n m k l d *
            (1 + Real.log (b : ℝ)) := by
          dsimp [Cscale]
          ring
      simpa only [if_neg hqpm, if_pos hmeq] using htarget
    · have hbound' :
          |∑' W : Grassmannian K m l, w W| ≤ Cscale * D := by
        simpa only [if_neg hqpm, if_neg hmeq] using hbound
      have htarget :
          |∑' W : Grassmannian K m l, w W| ≤
            C₃ * D * T ^ alpha_l n m k l d := by
        calc
        |∑' W : Grassmannian K m l, w W| ≤ Cscale * D := hbound'
        _ = C₃ * D * T ^ alpha_l n m k l d := by
          dsimp [Cscale]
          ring
      simpa only [if_neg hqpm, if_neg hmeq] using htarget

/- Finite summation of the positive lower-rank strata, corresponding to
   equations (19)--(21) after the height estimate has been inserted.  The
   hypothesis `hpoint` is precisely the output still needed from the
   extension-count and rank-`l` lattice-counting lemmas. -/
theorem finite_lower_rank_sum_abs_le
    {n m k d : ℕ} {T C₃ Ccrudenew : ℝ}
    (hC₃ : 0 ≤ C₃) (hCcrudenew : 0 ≤ Ccrudenew) (hT : 1 ≤ T)
    (hd : 0 < d) (hnm : m < n) (hk : 1 ≤ k)
    (u : ℕ → ℝ)
    (hpoint : ∀ l ∈ Finset.Ico 1 k,
      |u l| ≤ C₃ * T ^ alpha_l n m k l d *
        B_l n m k l d Ccrudenew T) :
    |∑ l ∈ Finset.Ico 1 k, u l| ≤
      ((Finset.Ico 1 k).card : ℝ) * C₃ * Ccrudenew *
        (1 + Real.log T) *
          T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ)) := by
  have hnorm :
      |∑ l ∈ Finset.Ico 1 k, u l| ≤
        ∑ l ∈ Finset.Ico 1 k, |u l| := by
    simpa [Real.norm_eq_abs] using
      (norm_sum_le (s := Finset.Ico 1 k) (f := u))
  have hpoint_sum :
      (∑ l ∈ Finset.Ico 1 k, |u l|) ≤
        ∑ l ∈ Finset.Ico 1 k,
          C₃ * (T ^ alpha_l n m k l d *
            B_l n m k l d Ccrudenew T) := by
    exact Finset.sum_le_sum (fun l hl => by
      simpa [mul_assoc] using hpoint l hl)
  have hscaled :
      (∑ l ∈ Finset.Ico 1 k,
          C₃ * (T ^ alpha_l n m k l d *
            B_l n m k l d Ccrudenew T)) =
        C₃ * ∑ l ∈ Finset.Ico 1 k,
          T ^ alpha_l n m k l d * B_l n m k l d Ccrudenew T := by
    rw [Finset.mul_sum]
  have hsum := sum_alpha_l_mul_B_l_le_corrected
    hCcrudenew hT hd hnm hk
  calc
    |∑ l ∈ Finset.Ico 1 k, u l| ≤
        ∑ l ∈ Finset.Ico 1 k, |u l| := hnorm
    _ ≤ ∑ l ∈ Finset.Ico 1 k,
          C₃ * (T ^ alpha_l n m k l d *
            B_l n m k l d Ccrudenew T) := hpoint_sum
    _ = C₃ * ∑ l ∈ Finset.Ico 1 k,
          T ^ alpha_l n m k l d * B_l n m k l d Ccrudenew T := hscaled
    _ ≤ C₃ * (((Finset.Ico 1 k).card : ℝ) *
          (Ccrudenew * (1 + Real.log T) *
            T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ)))) :=
      mul_le_mul_of_nonneg_left hsum hC₃
    _ = ((Finset.Ico 1 k).card : ℝ) * C₃ * Ccrudenew *
          (1 + Real.log T) *
            T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ)) := by
      ring

/- The algebraic form of the two estimates used in equation (19).  Here `c`
   is the extension count `n_k(D')`, `g` is the rank-`l` inner matrix sum,
   and the quotient by `T^(k*n*d)` is the normalization in the manuscript.
   The hypotheses are deliberately the displayed counting estimates, so the
   later projected-lattice module can be substituted without changing this
   bridge. -/
theorem normalized_rowSpace_product_abs_le
    {K : Type*} [Field K] [NumberField K]
    {n m k l d : ℕ} {T C₁ C₂ : ℝ}
    (W : Grassmannian K m l) (hT : 1 ≤ T)
    (hH : 1 ≤ rowSpaceHeight W) (hkm : k ≤ m) (hlk : l < k)
    (c g : Grassmannian K m l → ℝ)
    (hc₀ : 0 ≤ c W)
    (hc : c W ≤ C₁ * T ^ (d * (k - l) * (m - l)) *
      (rowSpaceHeight W) ^ (k - l))
    (hg : |g W| ≤ C₂ * (rowSpaceHeight W)⁻¹ ^ n * T ^ (l * n * d))
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    |c W * g W / T ^ (k * n * d)| ≤
      C₁ * C₂ * T ^ alpha_l n m k l d *
        (rowSpaceHeight W) ^ ((k : ℤ) - l - n) := by
  have hT₀ : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hH₀ : 0 < rowSpaceHeight W :=
    lt_of_lt_of_le zero_lt_one hH
  have hden : 0 < T ^ (k * n * d) := pow_pos hT₀ _
  have hcg : |c W * g W| ≤
      (C₁ * T ^ (d * (k - l) * (m - l)) *
        (rowSpaceHeight W) ^ (k - l)) *
        (C₂ * (rowSpaceHeight W)⁻¹ ^ n * T ^ (l * n * d)) := by
    rw [abs_mul, abs_of_nonneg hc₀]
    exact mul_le_mul hc hg (abs_nonneg _) (by positivity)
  have hpowH :
      (rowSpaceHeight W) ^ (k - l) *
          (rowSpaceHeight W)⁻¹ ^ n =
        (rowSpaceHeight W) ^ ((k : ℤ) - l - n) := by
    rw [inv_pow, ← zpow_natCast (rowSpaceHeight W) (k - l),
      ← zpow_natCast (rowSpaceHeight W) n,
      ← zpow_neg (rowSpaceHeight W) (n : ℤ),
      ← zpow_add₀ hH₀.ne']
    congr 1
    push_cast
    rw [Nat.cast_sub hlk.le]
    ring
  have hpowT :
      T ^ (d * (k - l) * (m - l)) * T ^ (l * n * d) /
          T ^ (k * n * d) = T ^ alpha_l n m k l d := by
    rw [← zpow_natCast T (d * (k - l) * (m - l)),
      ← zpow_natCast T (l * n * d), ← zpow_natCast T (k * n * d),
      ← zpow_add₀ hT₀.ne', ← zpow_sub₀ hT₀.ne']
    congr 1
    dsimp [alpha_l, lowRankScaleExponent]
    push_cast
    rw [Nat.cast_sub hlk.le, Nat.cast_sub (le_trans hlk.le hkm)]
    ring
  rw [abs_div, abs_of_pos hden]
  have hscaled :
      |c W * g W| / T ^ (k * n * d) ≤
        ((C₁ * T ^ (d * (k - l) * (m - l)) *
          (rowSpaceHeight W) ^ (k - l)) *
          (C₂ * (rowSpaceHeight W)⁻¹ ^ n * T ^ (l * n * d))) /
            T ^ (k * n * d) := by
    exact div_le_div_of_nonneg_right hcg (le_of_lt hden)
  calc
    |c W * g W| / T ^ (k * n * d) ≤
        ((C₁ * T ^ (d * (k - l) * (m - l)) *
          (rowSpaceHeight W) ^ (k - l)) *
          (C₂ * (rowSpaceHeight W)⁻¹ ^ n * T ^ (l * n * d))) /
            T ^ (k * n * d) := hscaled
    _ = C₁ * C₂ *
          (T ^ (d * (k - l) * (m - l)) * T ^ (l * n * d) /
            T ^ (k * n * d)) *
          ((rowSpaceHeight W) ^ (k - l) *
            (rowSpaceHeight W)⁻¹ ^ n) := by ring
    _ = C₁ * C₂ * T ^ alpha_l n m k l d *
          (rowSpaceHeight W) ^ ((k : ℤ) - l - n) := by
      rw [hpowT, hpowH]

/- The complete single-positive-stratum estimate in the notation of the
   manuscript.  The support family `S`, the extension-count estimate, and the
   rank-`l` lattice estimate are kept as explicit inputs; the theorem performs
   the normalization and the height summation itself. -/
theorem rowSpaceLowerStratumTerm_abs_le_of_bounds
    {K : Type*} [Field K] [NumberField K]
    {n m k l d : ℕ} (B : Set (Grassmannian K m k)) [Fintype B]
    (f : M n m (K_ℝ[K]) → ℝ) {T C₁ C₂ : ℝ}
    (hT : 1 ≤ T) (hnm : m < n) (hkm : k ≤ m) (hl : 1 ≤ l) (hlk : l < k)
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := l)) m)
    {b : ℕ} (hb : 1 ≤ b)
    (S : Set (Grassmannian K m l)) (hS : S.Finite)
    (hS_one : ∀ W ∈ S, 1 ≤ rowSpaceHeight W)
    (hS_bound : ∀ W ∈ S, rowSpaceHeight W ≤ (b : ℝ))
    (hc : ∀ W ∈ S,
      rowSpaceExtensionCount B W ≤ C₁ * T ^ (d * (k - l) * (m - l)) *
        (rowSpaceHeight W) ^ (k - l))
    (hg : ∀ W ∈ S,
      |rowSpaceRankSum W f T| ≤ C₂ * (rowSpaceHeight W)⁻¹ ^ n *
        T ^ (l * n * d))
    (hzero : ∀ W ∉ S, rowSpaceRankSum W f T = 0)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    ∃ D : ℝ, 0 < D ∧
      |rowSpaceLowerStratumTerm (l := l) B f T| /
          T ^ (k * n * d) ≤
        if n + l - k < m then
          C₁ * C₂ * D * T ^ alpha_l n m k l d *
            (b : ℝ) ^ ((m - (n + l - k) : ℕ) : ℝ)
        else if m = n + l - k then
          C₁ * C₂ * D * T ^ alpha_l n m k l d *
            (1 + Real.log (b : ℝ))
        else C₁ * C₂ * D * T ^ alpha_l n m k l d := by
  let c : Grassmannian K m l → ℝ := fun W => rowSpaceExtensionCount B W
  let g : Grassmannian K m l → ℝ := fun W => rowSpaceRankSum W f T
  let w : Grassmannian K m l → ℝ := fun W =>
    c W * g W / T ^ (k * n * d)
  have hwzero : ∀ W ∉ S, w W = 0 := by
    intro W hW
    dsimp [w, c, g]
    rw [hzero W hW, mul_zero, zero_div]
  have hwpoint : ∀ W ∈ S,
      |w W| ≤ C₁ * C₂ * T ^ alpha_l n m k l d *
        (rowSpaceHeight W) ^ ((k : ℤ) - l - n) := by
    intro W hW
    dsimp [w, c, g]
    exact normalized_rowSpace_product_abs_le W hT (hS_one W hW)
      hkm hlk c g
      (rowSpaceExtensionCount_nonneg B W) (hc W hW) (hg W hW) hC₁ hC₂
  obtain ⟨D, hD, hbound⟩ := single_lower_rank_height_term_le hT
    hnm hkm hl hlk hcount hb S hS hS_one hS_bound w hwzero
      (mul_nonneg hC₁ hC₂) hwpoint
  refine ⟨D, hD, ?_⟩
  have hwsupp : (Function.support w).Finite := by
    apply hS.subset
    intro W hW
    by_contra hWnot
    apply hW
    exact hwzero W hWnot
  have hwSummable : Summable w := summable_of_hasFiniteSupport hwsupp
  have hden : 0 < T ^ (k * n * d) := by
    exact pow_pos (lt_of_lt_of_le zero_lt_one hT) _
  have hscale :
      rowSpaceLowerStratumTerm (l := l) B f T =
        T ^ (k * n * d) * (∑' W, w W) := by
    calc
      rowSpaceLowerStratumTerm (l := l) B f T =
          ∑' W : Grassmannian K m l, c W * g W := by
        rfl
      _ = ∑' W : Grassmannian K m l,
          T ^ (k * n * d) * w W := by
        apply tsum_congr
        intro W
        dsimp [w]
        field_simp [ne_of_gt hden]
      _ = T ^ (k * n * d) * (∑' W, w W) := hwSummable.tsum_mul_left _
  have hnormalized :
      |rowSpaceLowerStratumTerm (l := l) B f T| /
          T ^ (k * n * d) = |∑' W, w W| := by
    rw [hscale, abs_mul, abs_of_pos hden]
    field_simp [ne_of_gt hden]
  rw [hnormalized]
  exact hbound

/- The nonnegative counterpart of the preceding estimate is the one that
   actually enters the manuscript's sum of absolute lower-rank terms.  Here
   `q` is the rank-`l` sum after replacing `f` by `|f|`; its support and its
   pointwise height bound are explicit, while the conclusion is the positive
   weighted sum required in equation (1678). -/
set_option maxHeartbeats 800000 in
theorem rowSpacePositiveStratum_normalized_le_of_bounds
    {K : Type*} [Field K] [NumberField K]
    {n m k l d : ℕ} (B : Set (Grassmannian K m k)) [Fintype B]
    {T C₁ C₂ : ℝ} (hT : 1 ≤ T) (hnm : m < n) (hkm : k ≤ m)
    (hl : 1 ≤ l) (hlk : l < k)
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := l)) m)
    {b : ℕ} (hb : 1 ≤ b)
    (S : Set (Grassmannian K m l)) (hS : S.Finite)
    (hS_one : ∀ W ∈ S, 1 ≤ rowSpaceHeight W)
    (hS_bound : ∀ W ∈ S, rowSpaceHeight W ≤ (b : ℝ))
    (q : Grassmannian K m l → ℝ)
    (hzero : ∀ W ∉ S, q W = 0)
    (hq_nonneg : ∀ W, 0 ≤ q W)
    (hc : ∀ W ∈ S,
      rowSpaceExtensionCount B W ≤ C₁ * T ^ (d * (k - l) * (m - l)) *
        (rowSpaceHeight W) ^ (k - l))
    (hq : ∀ W ∈ S,
      q W ≤ C₂ * (rowSpaceHeight W)⁻¹ ^ n * T ^ (l * n * d))
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    ∃ D : ℝ, 0 < D ∧
      (∑' W : Grassmannian K m l,
        rowSpaceExtensionCount B W * q W) / T ^ (k * n * d) ≤
        if n + l - k < m then
          C₁ * C₂ * D * T ^ alpha_l n m k l d *
            (b : ℝ) ^ ((m - (n + l - k) : ℕ) : ℝ)
        else if m = n + l - k then
          C₁ * C₂ * D * T ^ alpha_l n m k l d *
            (1 + Real.log (b : ℝ))
        else C₁ * C₂ * D * T ^ alpha_l n m k l d := by
  let c : Grassmannian K m l → ℝ := fun W => rowSpaceExtensionCount B W
  let w : Grassmannian K m l → ℝ := fun W =>
    c W * q W / T ^ (k * n * d)
  have hwzero : ∀ W ∉ S, w W = 0 := by
    intro W hW
    dsimp [w, c]
    rw [hzero W hW, mul_zero, zero_div]
  have hwpoint : ∀ W ∈ S,
      |w W| ≤ C₁ * C₂ * T ^ alpha_l n m k l d *
        (rowSpaceHeight W) ^ ((k : ℤ) - l - n) := by
    intro W hW
    dsimp [w, c]
    apply normalized_rowSpace_product_abs_le W hT (hS_one W hW)
      hkm hlk c q (rowSpaceExtensionCount_nonneg B W) (hc W hW) ?_
      hC₁ hC₂
    rw [abs_of_nonneg (hq_nonneg W)]
    exact hq W hW
  obtain ⟨D, hD, hbound⟩ := single_lower_rank_height_term_le hT
    hnm hkm hl hlk hcount hb S hS hS_one hS_bound w hwzero
      (mul_nonneg hC₁ hC₂) hwpoint
  refine ⟨D, hD, ?_⟩
  have hwsupp : (Function.support w).Finite := by
    apply hS.subset
    intro W hW
    by_contra hWnot
    apply hW
    exact hwzero W hWnot
  have hwSummable : Summable w := summable_of_hasFiniteSupport hwsupp
  have hden : 0 < T ^ (k * n * d) := by
    exact pow_pos (lt_of_lt_of_le zero_lt_one hT) _
  have hw_nonneg : ∀ W, 0 ≤ w W := by
    intro W
    dsimp [w, c]
    exact div_nonneg
      (mul_nonneg (rowSpaceExtensionCount_nonneg B W) (hq_nonneg W))
      hden.le
  have hsum_nonneg : 0 ≤ ∑' W, w W := tsum_nonneg hw_nonneg
  have hscale :
      (∑' W : Grassmannian K m l,
        rowSpaceExtensionCount B W * q W) =
        T ^ (k * n * d) * (∑' W, w W) := by
    calc
      (∑' W : Grassmannian K m l,
          rowSpaceExtensionCount B W * q W) =
          ∑' W : Grassmannian K m l, c W * q W := by
        rfl
      _ = ∑' W : Grassmannian K m l, T ^ (k * n * d) * w W := by
        apply tsum_congr
        intro W
        dsimp [w]
        field_simp [ne_of_gt hden]
      _ = T ^ (k * n * d) * (∑' W, w W) := hwSummable.tsum_mul_left _
  have hnormalized :
      (∑' W : Grassmannian K m l,
        rowSpaceExtensionCount B W * q W) / T ^ (k * n * d) =
        ∑' W, w W := by
    rw [hscale]
    field_simp [ne_of_gt hden]
  rw [hnormalized]
  simpa [abs_of_nonneg hsum_nonneg] using hbound

/- This is the manuscript-facing specialization of the preceding positive
   stratum estimate.  The paper obtains its pointwise rank-`l` bound from the
   inner matrix count.  We keep that inner count in the paper's notation and
   derive the nonnegative `|f|`-sum used by equation (1678) from the original
   admissibility hypothesis.  No closure theorem for `Admissible (|f|)` is
   being assumed here. -/
set_option maxHeartbeats 800000 in
theorem rowSpacePositiveStratum_normalized_le_of_matrix_bounds
    {K : Type*} [Field K] [NumberField K]
    {n m k l d : ℕ} (B : Set (Grassmannian K m k)) [Fintype B]
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    {T C₁ C₂ : ℝ} (hT : 1 ≤ T) (hnm : m < n) (hkm : k ≤ m)
    (hl : 1 ≤ l) (hlk : l < k)
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := l)) m)
    {b : ℕ} (hb : 1 ≤ b)
    (S : Set (Grassmannian K m l)) (hS : S.Finite)
    (hS_one : ∀ W ∈ S, 1 ≤ rowSpaceHeight W)
    (hS_bound : ∀ W ∈ S, rowSpaceHeight W ≤ (b : ℝ))
    (hc : ∀ W ∈ S,
      rowSpaceExtensionCount B W ≤ C₁ * T ^ (d * (k - l) * (m - l)) *
        (rowSpaceHeight W) ^ (k - l))
    (hinner : ∀ W ∈ S,
      (∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule W A ∧ integralMatrixRank A = l},
        |f (T⁻¹ • embedMatrix A.1)|) ≤
      C₂ * (rowSpaceHeight W)⁻¹ ^ n * T ^ (l * n * d))
    (hzero : ∀ W ∉ S,
      ∀ A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule W A ∧ integralMatrixRank A = l},
        f (T⁻¹ • embedMatrix A.1) = 0)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    ∃ D : ℝ, 0 < D ∧
      (∑' W : Grassmannian K m l,
        rowSpaceExtensionCount B W *
          (∑' A : {A : IntegralMatrix K n m //
            rowsInIntegralRowModule W A ∧ integralMatrixRank A = l},
            |f (T⁻¹ • embedMatrix A.1)|)) /
          T ^ (k * n * d) ≤
        if n + l - k < m then
          C₁ * C₂ * D * T ^ alpha_l n m k l d *
            (b : ℝ) ^ ((m - (n + l - k) : ℕ) : ℝ)
        else if m = n + l - k then
          C₁ * C₂ * D * T ^ alpha_l n m k l d *
            (1 + Real.log (b : ℝ))
        else C₁ * C₂ * D * T ^ alpha_l n m k l d := by
  let q : Grassmannian K m l → ℝ := fun W =>
    ∑' A : {A : IntegralMatrix K n m //
      rowsInIntegralRowModule W A ∧ integralMatrixRank A = l},
      |f (T⁻¹ • embedMatrix A.1)|
  have hqzero : ∀ W ∉ S, q W = 0 := by
    intro W hW
    rw [← tsum_zero]
    apply tsum_congr
    intro A
    rw [hzero W hW A]
    simp
  have hq_nonneg : ∀ W, 0 ≤ q W := by
    intro W
    dsimp [q]
    exact tsum_nonneg (fun A => abs_nonneg _)
  have hq : ∀ W ∈ S,
      q W ≤ C₂ * (rowSpaceHeight W)⁻¹ ^ n * T ^ (l * n * d) := by
    intro W hW
    dsimp [q]
    exact hinner W hW
  simpa [q] using rowSpacePositiveStratum_normalized_le_of_bounds
    B hT hnm hkm hl hlk hcount hb S hS hS_one hS_bound q hqzero
      hq_nonneg hc hq hC₁ hC₂

/- The assembled lower-rank estimate: the rank-zero contribution is separated
   from the positive strata exactly as in the manuscript, and the latter are
   fed into the corrected three-case summation estimate. -/
theorem finite_rowSpaceLowerSum_normalized_abs_le
    {K : Type*} [Field K] [NumberField K]
    {n m k d : ℕ} (B : Set (Grassmannian K m k)) [Fintype B]
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    {T Csize C₃ Ccrudenew : ℝ}
    (hT : 1 ≤ T) (hnm : m < n) (hk : 1 ≤ k) (hd : 0 < d)
    (hB : (B.ncard : ℝ) ≤ Csize * T ^ (k * m * d))
    (hC₃ : 0 ≤ C₃) (hCcrudenew : 0 ≤ Ccrudenew)
    (hpoint : ∀ l ∈ Finset.Ico 1 k,
      |rowSpaceLowerStratumTerm (l := l) B f T| /
          T ^ (k * n * d) ≤
        C₃ * T ^ alpha_l n m k l d *
          B_l n m k l d Ccrudenew T) :
    |(∑ V : B, ∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
      f (T⁻¹ • embedMatrix A.1)) /
        T ^ (k * n * d)| ≤
      Csize * |f 0| *
          T ^ (-(d : ℤ) * (k : ℤ) * ((n : ℤ) - m)) +
        ((Finset.Ico 1 k).card : ℝ) * C₃ * Ccrudenew *
          (1 + Real.log T) *
          T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ)) := by
  have hden : 0 < T ^ (k * n * d) := by
    exact pow_pos (lt_of_lt_of_le zero_lt_one hT) _
  have hzero := rowSpaceLowerStratumTerm_zero_normalized_le B f hT hB
  rw [rowSpaceLowerStratumTerm_zero_eq B f T] at hzero
  have hpositive := finite_lower_rank_sum_abs_le
    (u := fun l => rowSpaceLowerStratumTerm (l := l) B f T /
      T ^ (k * n * d)) hC₃ hCcrudenew hT hd hnm hk
      (fun l hl => by
        simpa [abs_div, abs_of_pos hden] using hpoint l hl)
  have hsplit := finite_rowSpaceLowerSum_eq_zero_add_positive_terms
    B f h_f (lt_of_lt_of_le zero_lt_one hT) hk
  have hnormalized :
      (∑ V : B, ∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
        f (T⁻¹ • embedMatrix A.1)) /
          T ^ (k * n * d) =
        ((B.ncard : ℝ) * f 0) / T ^ (k * n * d) +
          ∑ l ∈ Finset.Ico 1 k,
            rowSpaceLowerStratumTerm (l := l) B f T /
              T ^ (k * n * d) := by
    rw [hsplit]
    rw [add_div, Finset.sum_div]
  rw [hnormalized]
  have hzero' :
      |(B.ncard : ℝ) * f 0 / T ^ (k * n * d)| ≤
        Csize * |f 0| *
          T ^ (-(d : ℤ) * (k : ℤ) * ((n : ℤ) - m)) := by
    rw [abs_div, abs_of_pos hden, abs_mul, abs_of_nonneg (by positivity)]
    rw [abs_mul, abs_of_nonneg (by positivity)] at hzero
    exact hzero
  calc
    |(B.ncard : ℝ) * f 0 / T ^ (k * n * d) +
          ∑ l ∈ Finset.Ico 1 k,
            rowSpaceLowerStratumTerm (l := l) B f T /
              T ^ (k * n * d)| ≤
        |(B.ncard : ℝ) * f 0 / T ^ (k * n * d)| +
          |∑ l ∈ Finset.Ico 1 k,
            rowSpaceLowerStratumTerm (l := l) B f T /
              T ^ (k * n * d)| := abs_add_le _ _
    _ ≤ Csize * |f 0| *
          T ^ (-(d : ℤ) * (k : ℤ) * ((n : ℤ) - m)) +
          ((Finset.Ico 1 k).card : ℝ) * C₃ * Ccrudenew *
            (1 + Real.log T) *
            T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ)) := by
      apply add_le_add
      · exact hzero'
      · simpa using hpositive

/- [paper, `le:low_rank_terms`, lines 1495--1499] Assemble the rank-zero
   contribution and the positive lower-rank strata into the corrected scalar
   bound.  The exponent `n - m + k - 1` is the one obtained from the three
   height cases; this theorem keeps the paper's `alpha_l` and `B_l` inputs
   explicit rather than hiding the corrected estimate behind a new axiom. -/
set_option maxHeartbeats 800000 in
theorem finite_rowSpaceLowerSum_normalized_abs_le_corrected
    {K : Type*} [Field K] [NumberField K]
    {n m k d : ℕ} (B : Set (Grassmannian K m k)) [Fintype B]
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    {T Csize C₃ Ccrudenew : ℝ}
    (hT : 1 ≤ T) (hnm : m < n) (hk : 1 ≤ k) (hd : 0 < d)
    (hCsize : 0 ≤ Csize)
    (hB : (B.ncard : ℝ) ≤ Csize * T ^ (k * m * d))
    (hC₃ : 0 ≤ C₃) (hCcrudenew : 0 ≤ Ccrudenew)
    (hpoint : ∀ l ∈ Finset.Ico 1 k,
      |rowSpaceLowerStratumTerm (l := l) B f T| /
          T ^ (k * n * d) ≤
        C₃ * T ^ alpha_l n m k l d *
          B_l n m k l d Ccrudenew T) :
    |(∑ V : B, ∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
      f (T⁻¹ • embedMatrix A.1)) /
        T ^ (k * n * d)| ≤
      (Csize * |f 0| + ((Finset.Ico 1 k).card : ℝ) * C₃ * Ccrudenew) *
        (1 + Real.log T) *
        T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ)) := by
  have hbound := finite_rowSpaceLowerSum_normalized_abs_le B f h_f hT hnm hk hd
    hB hC₃ hCcrudenew hpoint
  have hq : 1 ≤ n - m := by omega
  have hnat : n - m + k - 1 ≤ k * (n - m) := by
    calc
      n - m + k - 1 = (n - m) + (k - 1) := by omega
      _ ≤ (n - m) + (k - 1) * (n - m) := by
        have hkminus : k - 1 ≤ (k - 1) * (n - m) := by
          calc
            k - 1 = (k - 1) * 1 := by simp
            _ ≤ (k - 1) * (n - m) := Nat.mul_le_mul_left _ hq
        exact Nat.add_le_add_left hkminus _
      _ = k * (n - m) := by
        calc
          (n - m) + (k - 1) * (n - m) =
              (1 + (k - 1)) * (n - m) := by
            rw [Nat.add_mul]
            simp
          _ = k * (n - m) := by
            congr 1
            omega
  have hmul : d * (n - m + k - 1) ≤ d * (k * (n - m)) :=
    Nat.mul_le_mul_left d hnat
  have hneg :
      -((d * (k * (n - m)) : ℕ) : ℤ) ≤
        -((d * (n - m + k - 1) : ℕ) : ℤ) := by
    exact neg_le_neg (by exact_mod_cast hmul)
  have hpow :
      T ^ (-(d : ℤ) * (k : ℤ) * ((n : ℤ) - m)) ≤
        T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ)) := by
    apply zpow_le_zpow_right₀ hT
    simpa [Nat.cast_mul, Nat.cast_sub hnm.le, mul_assoc] using hneg
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT
  have hfactor : (1 : ℝ) ≤ 1 + Real.log T := by linarith
  have hfactor_nonneg : 0 ≤ 1 + Real.log T := le_trans (by norm_num) hfactor
  have htarget_nonneg :
      0 ≤ T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ)) :=
    zpow_nonneg (by linarith) _
  have hzero_coeff : 0 ≤ Csize * |f 0| :=
    mul_nonneg hCsize (abs_nonneg _)
  have hpositive_coeff :
      0 ≤ ((Finset.Ico 1 k).card : ℝ) * C₃ * Ccrudenew := by
    positivity
  have hzero_factor :
      T ^ (-(d : ℤ) * (k : ℤ) * ((n : ℤ) - m)) ≤
        (1 + Real.log T) *
          T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ)) := by
    calc
      T ^ (-(d : ℤ) * (k : ℤ) * ((n : ℤ) - m)) ≤
          T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ)) := hpow
      _ = 1 * T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ)) := by ring
      _ ≤ (1 + Real.log T) *
          T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ)) :=
        mul_le_mul_of_nonneg_right hfactor htarget_nonneg
  calc
    |(∑ V : B, ∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
      f (T⁻¹ • embedMatrix A.1)) /
        T ^ (k * n * d)| ≤
        Csize * |f 0| *
            T ^ (-(d : ℤ) * (k : ℤ) * ((n : ℤ) - m)) +
          ((Finset.Ico 1 k).card : ℝ) * C₃ * Ccrudenew *
            (1 + Real.log T) *
            T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ)) := hbound
    _ ≤ Csize * |f 0| *
          ((1 + Real.log T) *
            T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ))) +
        ((Finset.Ico 1 k).card : ℝ) * C₃ * Ccrudenew *
          ((1 + Real.log T) *
            T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ))) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hzero_factor hzero_coeff
      · ring_nf
        exact le_rfl
    _ = (Csize * |f 0| + ((Finset.Ico 1 k).card : ℝ) * C₃ * Ccrudenew) *
          (1 + Real.log T) *
          T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ)) := by ring

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

/- This is the finite-family summation step in equations (20)--(21) of the
   manuscript (lines 1671--1679).  It keeps the rank-restricted row-lattice
   term, the unrestricted Riemann-sum error, and the lower-rank correction
   visible.  The only input is the pointwise estimate; no uniformity is
   smuggled in by reindexing an infinite sum. -/
theorem finite_rowMatrix_rank_error_with_lower
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (B : Set (Grassmannian K m k)) [Fintype B]
    {f : M n m (K_ℝ[K]) → ℝ} {T Cₐ : ℝ}
    (hpoint : ∀ V : B,
      |(∑' A : {A : rowMatrixZLattice V.1 n // rowMatrixRank V.1 A = k},
          f (T⁻¹ • (((A.1 : rowMatrixRealSpan V.1 n) :
            M n m (K_ℝ[K]))))) /
            T ^ (n * (k * degree K)) -
          (rowMatrixLatticeCovolume V.1 n)⁻¹ *
            rowMatrixSubspaceIntegral V.1 n f| ≤
        Cₐ * rowMatrixFundamentalRadius V.1 n /
          (rowMatrixLatticeCovolume V.1 n * T) +
        |(∑' A : {A : IntegralMatrix K n m //
            rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
          f (T⁻¹ • embedMatrix A.1))| /
            T ^ (n * (k * degree K))) :
    |(∑ V : B,
        (∑' A : {A : rowMatrixZLattice V.1 n // rowMatrixRank V.1 A = k},
          f (T⁻¹ • (((A.1 : rowMatrixRealSpan V.1 n) :
            M n m (K_ℝ[K]))))) /
          T ^ (n * (k * degree K))) -
      ∑ V : B,
        (rowMatrixLatticeCovolume V.1 n)⁻¹ *
          rowMatrixSubspaceIntegral V.1 n f| ≤
      ∑ V : B,
        (Cₐ * rowMatrixFundamentalRadius V.1 n /
          (rowMatrixLatticeCovolume V.1 n * T) +
        |(∑' A : {A : IntegralMatrix K n m //
            rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
          f (T⁻¹ • embedMatrix A.1))| /
            T ^ (n * (k * degree K))) := by
  classical
  let r : B → ℝ := fun V =>
    (∑' A : {A : rowMatrixZLattice V.1 n // rowMatrixRank V.1 A = k},
      f (T⁻¹ • (((A.1 : rowMatrixRealSpan V.1 n) :
        M n m (K_ℝ[K]))))) /
      T ^ (n * (k * degree K))
  let mainTerm : B → ℝ := fun V =>
    (rowMatrixLatticeCovolume V.1 n)⁻¹ *
      rowMatrixSubspaceIntegral V.1 n f
  let e : B → ℝ := fun V =>
    Cₐ * rowMatrixFundamentalRadius V.1 n /
        (rowMatrixLatticeCovolume V.1 n * T) +
      |(∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
        f (T⁻¹ • embedMatrix A.1))| /
        T ^ (n * (k * degree K))
  have hsum :
      (∑ V : B, r V) - ∑ V : B, mainTerm V =
        ∑ V : B, (r V - mainTerm V) := by
    symm
    exact Finset.sum_sub_distrib _ _
  have hpoint' : ∀ V : B, |r V - mainTerm V| ≤ e V := by
    intro V
    simpa [r, mainTerm, e] using hpoint V
  change |(∑ V : B, r V) - ∑ V : B, mainTerm V| ≤ ∑ V : B, e V
  rw [hsum]
  calc
    |∑ V : B, (r V - mainTerm V)| ≤ ∑ V : B, |r V - mainTerm V| := by
      simpa only [Real.norm_eq_abs] using
        (norm_sum_le (s := Finset.univ)
          (f := fun V : B => r V - mainTerm V))
    _ ≤ ∑ V : B, e V := by
      exact Finset.sum_le_sum (fun V hV => hpoint' V)

/- The form used in the manuscript after the lower-rank lemma has been
   inserted: the lower-rank contribution is first summed in absolute value
   over the finite family, exactly as in equation (1678), and is then bounded
   by one scalar error term. -/
set_option maxHeartbeats 800000 in
theorem finite_rowMatrix_rank_error_with_lower_of_sum_abs_bound
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (B : Set (Grassmannian K m k)) [Fintype B]
    {f : M n m (K_ℝ[K]) → ℝ} {T Cₐ E_lower : ℝ}
    (hpoint : ∀ V : B,
      |(∑' A : {A : rowMatrixZLattice V.1 n // rowMatrixRank V.1 A = k},
          f (T⁻¹ • (((A.1 : rowMatrixRealSpan V.1 n) :
            M n m (K_ℝ[K]))))) /
            T ^ (n * (k * degree K)) -
          (rowMatrixLatticeCovolume V.1 n)⁻¹ *
            rowMatrixSubspaceIntegral V.1 n f| ≤
        Cₐ * rowMatrixFundamentalRadius V.1 n /
          (rowMatrixLatticeCovolume V.1 n * T) +
        |(∑' A : {A : IntegralMatrix K n m //
            rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
          f (T⁻¹ • embedMatrix A.1))| /
            T ^ (n * (k * degree K)))
    (hLower :
      (∑ V : B, |∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
          f (T⁻¹ • embedMatrix A.1)|) /
          T ^ (n * (k * degree K)) ≤ E_lower) :
    |(∑ V : B,
        (∑' A : {A : rowMatrixZLattice V.1 n // rowMatrixRank V.1 A = k},
          f (T⁻¹ • (((A.1 : rowMatrixRealSpan V.1 n) :
            M n m (K_ℝ[K]))))) /
          T ^ (n * (k * degree K))) -
      ∑ V : B,
        (rowMatrixLatticeCovolume V.1 n)⁻¹ *
          rowMatrixSubspaceIntegral V.1 n f| ≤
      ∑ V : B,
        Cₐ * rowMatrixFundamentalRadius V.1 n /
          (rowMatrixLatticeCovolume V.1 n * T) + E_lower := by
  have hfamily := finite_rowMatrix_rank_error_with_lower B hpoint
  calc
    |(∑ V : B,
        (∑' A : {A : rowMatrixZLattice V.1 n // rowMatrixRank V.1 A = k},
          f (T⁻¹ • (((A.1 : rowMatrixRealSpan V.1 n) :
            M n m (K_ℝ[K]))))) /
          T ^ (n * (k * degree K))) -
      ∑ V : B,
        (rowMatrixLatticeCovolume V.1 n)⁻¹ *
          rowMatrixSubspaceIntegral V.1 n f| ≤
        ∑ V : B,
          (Cₐ * rowMatrixFundamentalRadius V.1 n /
            (rowMatrixLatticeCovolume V.1 n * T) +
          |(∑' A : {A : IntegralMatrix K n m //
              rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
            f (T⁻¹ • embedMatrix A.1))| /
            T ^ (n * (k * degree K))) := hfamily
    _ = ∑ V : B,
          Cₐ * rowMatrixFundamentalRadius V.1 n /
            (rowMatrixLatticeCovolume V.1 n * T) +
          (∑ V : B, |∑' A : {A : IntegralMatrix K n m //
              rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
            f (T⁻¹ • embedMatrix A.1)|) /
            T ^ (n * (k * degree K)) := by
      rw [Finset.sum_add_distrib]
      rw [Finset.sum_div]
    _ ≤ ∑ V : B,
          Cₐ * rowMatrixFundamentalRadius V.1 n /
            (rowMatrixLatticeCovolume V.1 n * T) + E_lower := by
      have h' := add_le_add_right hLower
        (∑ V : B, Cₐ * rowMatrixFundamentalRadius V.1 n /
          (rowMatrixLatticeCovolume V.1 n * T))
      simpa [add_comm] using h'

/- [paper, lines 1687--1694] Sum the row-space Riemann errors after the
   lower-rank term has been isolated.  The paper supplies the corresponding
   radius/height estimate later; here it remains an explicit hypothesis. -/
theorem finite_rowMatrix_radius_error_sum_le
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (B : Set (Grassmannian K m k)) [Fintype B]
    {T Cₐ C_R : ℝ} (hT : 0 < T) (hCₐ : 0 ≤ Cₐ)
    (hRadius :
      (∑ V : B,
        rowMatrixFundamentalRadius V.1 n /
          rowMatrixLatticeCovolume V.1 n) ≤ C_R) :
    ∑ V : B,
        Cₐ * rowMatrixFundamentalRadius V.1 n /
          (rowMatrixLatticeCovolume V.1 n * T) ≤
      Cₐ * C_R / T := by
  have hterm : ∀ V : B,
      Cₐ * rowMatrixFundamentalRadius V.1 n /
          (rowMatrixLatticeCovolume V.1 n * T) =
        (Cₐ / T) *
          (rowMatrixFundamentalRadius V.1 n /
            rowMatrixLatticeCovolume V.1 n) := by
    intro V
    have hCovol : 0 < rowMatrixLatticeCovolume V.1 n :=
      rowMatrixLatticeCovolume_pos V.1
    field_simp [ne_of_gt hT, ne_of_gt hCovol]
  calc
    ∑ V : B,
        Cₐ * rowMatrixFundamentalRadius V.1 n /
          (rowMatrixLatticeCovolume V.1 n * T) =
        ∑ V : B, (Cₐ / T) *
          (rowMatrixFundamentalRadius V.1 n /
            rowMatrixLatticeCovolume V.1 n) := by
      apply Finset.sum_congr rfl
      intro V hV
      exact hterm V
    _ = (Cₐ / T) *
        (∑ V : B,
          rowMatrixFundamentalRadius V.1 n /
            rowMatrixLatticeCovolume V.1 n) := by
      rw [Finset.mul_sum]
    _ ≤ (Cₐ / T) * C_R := by
      exact mul_le_mul_of_nonneg_left hRadius
        (div_nonneg hCₐ hT.le)
    _ = Cₐ * C_R / T := by
      ring

/- [paper, lines 1671--1694] Combine the finite-family Riemann estimate, the
   scalar lower-rank error, and the radius/covolume sum.  This is the exact
   global error shape needed before the remaining paper-specific bounds are
   supplied. -/
theorem finite_rowMatrix_rank_error_with_radius_sum_bound
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (B : Set (Grassmannian K m k)) [Fintype B]
    {f : M n m (K_ℝ[K]) → ℝ} {T Cₐ C_R E_lower : ℝ}
    (hT : 0 < T) (hCₐ : 0 ≤ Cₐ)
    (hpoint : ∀ V : B,
      |(∑' A : {A : rowMatrixZLattice V.1 n // rowMatrixRank V.1 A = k},
          f (T⁻¹ • (((A.1 : rowMatrixRealSpan V.1 n) :
            M n m (K_ℝ[K]))))) /
            T ^ (n * (k * degree K)) -
          (rowMatrixLatticeCovolume V.1 n)⁻¹ *
            rowMatrixSubspaceIntegral V.1 n f| ≤
        Cₐ * rowMatrixFundamentalRadius V.1 n /
          (rowMatrixLatticeCovolume V.1 n * T) +
        |(∑' A : {A : IntegralMatrix K n m //
            rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
          f (T⁻¹ • embedMatrix A.1))| /
            T ^ (n * (k * degree K)))
    (hLower :
      (∑ V : B, |∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
          f (T⁻¹ • embedMatrix A.1)|) /
          T ^ (n * (k * degree K)) ≤ E_lower)
    (hRadius :
      (∑ V : B,
        rowMatrixFundamentalRadius V.1 n /
          rowMatrixLatticeCovolume V.1 n) ≤ C_R) :
    |(∑ V : B,
        (∑' A : {A : rowMatrixZLattice V.1 n // rowMatrixRank V.1 A = k},
          f (T⁻¹ • (((A.1 : rowMatrixRealSpan V.1 n) :
            M n m (K_ℝ[K]))))) /
          T ^ (n * (k * degree K))) -
      ∑ V : B,
        (rowMatrixLatticeCovolume V.1 n)⁻¹ *
          rowMatrixSubspaceIntegral V.1 n f| ≤
      Cₐ * C_R / T + E_lower := by
  have hfamily := finite_rowMatrix_rank_error_with_lower_of_sum_abs_bound
    B hpoint hLower
  have hradius := finite_rowMatrix_radius_error_sum_le B hT hCₐ hRadius
  calc
    |(∑ V : B,
        (∑' A : {A : rowMatrixZLattice V.1 n // rowMatrixRank V.1 A = k},
          f (T⁻¹ • (((A.1 : rowMatrixRealSpan V.1 n) :
            M n m (K_ℝ[K]))))) /
          T ^ (n * (k * degree K))) -
      ∑ V : B,
        (rowMatrixLatticeCovolume V.1 n)⁻¹ *
          rowMatrixSubspaceIntegral V.1 n f| ≤
        ∑ V : B,
          Cₐ * rowMatrixFundamentalRadius V.1 n /
            (rowMatrixLatticeCovolume V.1 n * T) + E_lower := hfamily
    _ ≤ Cₐ * C_R / T + E_lower := add_le_add hradius le_rfl

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

/- This is the first explicit bridge from the manuscript's echelon family to
   the Grassmannian finite-family infrastructure.  A witness in
   `M_n(Λ_D)` is transported through the already-defined rank-filtered row
   lattice equivalence; the remaining identification of echelon matrices
   with row spaces is isolated in `EchelonRowSpaceBridge`. -/
theorem echelon_calF_subset_boundedRowSpaces
    {K : Type*} [Field K] [NumberField K]
    {l m n : ℕ} {Csup T : ℝ} :
    echelonRowSpace (K := K) (l := l) (m := m) ''
        calF (K := K) (l := l) (m := m) (n := n) Csup T ⊆
      boundedRowSpaces (K := K) (n := n) (m := m) (k := l) Csup T := by
  rintro _ ⟨D, hD, rfl⟩
  rcases hD with ⟨A, hArank, hAnorm⟩
  let V : Grassmannian K m l := echelonRowSpace D
  let e := rankIntegralRowMatricesEquivRowMatrixZLattice (n := n) V
  let B := e.symm ⟨A, hArank⟩
  have hBrow : rowsInIntegralRowModule V B.1 := B.2.1
  have hBrank : integralMatrixRank B.1 = l := B.2.2
  refine ⟨B.1, hBrow, hBrank, ?_⟩
  have hBA := rankIntegralRowMatricesEquivRowMatrixZLattice_coe V B
  have hBeq : e B = (⟨A, hArank⟩ :
      {A : rowMatrixZLattice V n // rowMatrixRank V A = l}) := by
    exact e.apply_symm_apply _
  have hBA' :
      (((A : rowMatrixZLattice V n) : rowMatrixRealSpan V n) :
        M n m (K_ℝ[K])) = embedMatrix B.1 := by
    change (((e B).1 : rowMatrixZLattice V n) :
      rowMatrixRealSpan V n) = embedMatrix B.1 at hBA
    rw [hBeq] at hBA
    exact hBA
  rw [← hBA']
  exact hAnorm

/- The same support reduction stated with the manuscript's direct
   `M_n(Λ_D)` definition.  The preceding theorem is its row-lattice form;
   `calFDirect_eq_calF` is the proved algebraic identification used here. -/
theorem echelon_calFDirect_subset_boundedRowSpaces
    {K : Type*} [Field K] [NumberField K]
    {l m n : ℕ} {Csup T : ℝ} :
    echelonRowSpace (K := K) (l := l) (m := m) ''
        calFDirect (K := K) (l := l) (m := m) (n := n) Csup T ⊆
      boundedRowSpaces (K := K) (n := n) (m := m) (k := l) Csup T := by
  rw [calFDirect_eq_calF]
  exact echelon_calF_subset_boundedRowSpaces

/- Manuscript-facing form of Lemma `le:without_rank_cond` (lines
   1038--1061).  The direct `M_n(Λ_D)` sum is reindexed by the proved
   echelon-to-row-lattice equivalence, and the exponent is rewritten using
   the established real-span dimension formula. -/
theorem Admissible.echelon_latticeRiemann_estimate
    {K : Type*} [Field K] [NumberField K]
    {l m n : ℕ} (D : EchelonMatrix K l m)
    {f : M n m (K_ℝ[K]) → ℝ} (h_f : Admissible f)
    (hl : 0 < l) (hn : 0 < n) :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧ ∀ T : ℝ, 0 < T →
      rowMatrixFundamentalRadius (echelonRowSpace D) n / T ≤ 1 →
      |(∑' A : echelonIntegralMatrices (n := n) D,
          f (T⁻¹ • embedMatrix A.1)) /
            T ^ (n * (l * degree K)) -
          (rowMatrixLatticeCovolume (echelonRowSpace D) n)⁻¹ *
            rowMatrixSubspaceIntegral (echelonRowSpace D) n f| ≤
        Cₐ * rowMatrixFundamentalRadius (echelonRowSpace D) n /
          (rowMatrixLatticeCovolume (echelonRowSpace D) n * T) := by
  obtain ⟨Cₐ, hCₐ, hestimate⟩ :=
    h_f.rowMatrix_latticeRiemann_estimate
      (echelonRowSpace D)
      (rowMatrixRealSpan_ne_bot_of_pos (echelonRowSpace D) hl hn)
  refine ⟨Cₐ, hCₐ, fun T hT hRadius => ?_⟩
  rw [tsum_echelonIntegralMatrices_eq_integralRowMatrices D f T]
  simpa [rowMatrixRealSpan_finrank] using hestimate T hT hRadius

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

/- [derived consequence, paper Lemma `le:schmidt_makes_c1_finite`, lines
   837--858] The paper's main-term summands are absolutely summable once the
   height count and the reciprocal-height estimate (equation
   `eq:summable_matrices`) have been supplied.  The estimate is explicit here;
   it is the missing covolume/Jacobian bridge, not a hidden assumption. -/
theorem summable_mainConstant_terms_of_height_count
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (hnm : m < n)
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := k)) m)
    {f : M n m (K_ℝ[K]) → ℝ} {C : ℝ} (hC : 0 < C)
    (hdom : ∀ V : Grassmannian K m k, 1 ≤ rowSpaceHeight V →
      |(rowMatrixLatticeCovolume V n)⁻¹ *
        rowMatrixSubspaceIntegral V n f| ≤
        C * (rowSpaceHeight V)⁻¹ ^ n) :
    Summable (fun V : Grassmannian K m k =>
      (rowMatrixLatticeCovolume V n)⁻¹ * rowMatrixSubspaceIntegral V n f) := by
  exact summable_of_abs_le_height_inv_pow_all hcount hnm hdom

/- [derived consequence, paper corollary `co:tail`, lines 1130--1169]
   Quantitative row-space form of the tail estimate.  The paper's echelon
   summand is represented by the row-space integral term; the exact
   identification is deliberately left as a separate normalization bridge. -/
theorem mainConstant_height_tail_abs_le
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (hnm : m < n)
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := k)) m)
    {f : M n m (K_ℝ[K]) → ℝ} {C : ℝ} (hC : 0 < C)
    (hdom : ∀ V : Grassmannian K m k, 1 ≤ rowSpaceHeight V →
      |(rowMatrixLatticeCovolume V n)⁻¹ *
        rowMatrixSubspaceIntegral V n f| ≤
        C * (rowSpaceHeight V)⁻¹ ^ n) :
    ∃ Ctail : ℝ, 0 < Ctail ∧ ∀ {N : ℕ}, 1 ≤ N →
      |∑' V : {V : Grassmannian K m k //
          (N : ℝ) ≤ rowSpaceHeight V},
        (rowMatrixLatticeCovolume V.1 n)⁻¹ *
          rowMatrixSubspaceIntegral V.1 n f| ≤
        Ctail * ((N : ℝ) ^ (-((n - m : ℕ) : ℝ))) := by
  exact weighted_height_tsum_tail_abs_le hcount hnm hC hdom

/- [derived consequence, paper corollary `co:tail`, lines 1130--1169]
   Compare the main-term sum over a finite family with the full constant.  The
   manuscript obtains the displayed height cutoff from the lower-height bound
   for echelon matrices; that comparison is exposed here as `houtside`. -/
set_option maxHeartbeats 800000 in
theorem finite_mainConstant_tail_abs_le
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (hnm : m < n)
    (B : Finset (Grassmannian K m k))
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := k)) m)
    {f : M n m (K_ℝ[K]) → ℝ} {C : ℝ} {N : ℕ} (hC : 0 < C)
    (hN : 1 ≤ N)
    (houtside : ∀ V : Grassmannian K m k, V ∉ (B : Set (Grassmannian K m k)) →
      (N : ℝ) ≤ rowSpaceHeight V)
    (hdom : ∀ V : Grassmannian K m k, 1 ≤ rowSpaceHeight V →
      |(rowMatrixLatticeCovolume V n)⁻¹ *
        rowMatrixSubspaceIntegral V n f| ≤
        C * (rowSpaceHeight V)⁻¹ ^ n) :
    ∃ Ctail : ℝ, 0 < Ctail ∧
      |mainConstant n m k f -
        ∑ V ∈ B,
          (rowMatrixLatticeCovolume V n)⁻¹ *
            rowMatrixSubspaceIntegral V n f| ≤
        Ctail * ((N : ℝ) ^ (-((n - m : ℕ) : ℝ))) := by
  let g : Grassmannian K m k → ℝ := fun V =>
    (rowMatrixLatticeCovolume V n)⁻¹ * rowMatrixSubspaceIntegral V n f
  have hsum : Summable g := by
    simpa [g] using
      (summable_mainConstant_terms_of_height_count hnm hcount hC hdom)
  obtain ⟨Ctail, hCtail, htail⟩ :=
    weighted_height_tsum_tail_inv_pow_le hcount hnm hC hdom
  let β := {V : Grassmannian K m k // V ∉ (B : Set (Grassmannian K m k))}
  let βN := {V : Grassmannian K m k // N ≤ rowSpaceHeight V}
  let e : β → βN := fun V =>
    ⟨V.1, houtside V.1 V.2⟩
  have he : Function.Injective e := by
    intro V W hVW
    apply Subtype.ext
    exact congrArg (fun U : βN => U.1) hVW
  have hsum_compl : Summable (fun V : β => g V.1) := by
    have hinc : Function.Injective (fun V : β => V.1) := by
      intro V W hVW
      apply Subtype.ext
      exact hVW
    exact hsum.comp_injective hinc
  have hdecomp := hsum.sum_add_tsum_subtype_compl B
  have htail_subset :
      (∑' V : β, |g V.1|) ≤
        ∑' V : βN, |g V.1| := by
    have hsum_abs : Summable (fun V : Grassmannian K m k => |g V|) := by
      apply summable_of_abs_le_height_inv_pow_all hcount hnm
      intro V hV
      simpa [g] using hdom V hV
    have hsum_tail : Summable (fun V : βN => |g V.1|) := by
      have hinc : Function.Injective (fun V : βN => V.1) := by
        intro V W hVW
        apply Subtype.ext
        exact hVW
      exact hsum_abs.comp_injective hinc
    have hle : ∀ V : β, |g V.1| ≤ |g (e V).1| := by
      intro V
      rfl
    exact hsum_tail.tsum_le_tsum_of_inj e he
      (fun V hV => abs_nonneg (g V)) hle
  have htail' :
      (∑' V : βN, |g V.1|) ≤ Ctail *
        ((N : ℝ) ^ (-((n - m : ℕ) : ℝ))) := by
    simpa [βN, g] using htail hN
  have hcompl_abs :
      |∑' V : β, g V.1| ≤ Ctail *
        ((N : ℝ) ^ (-((n - m : ℕ) : ℝ))) := by
    calc
      |∑' V : β, g V.1| ≤ ∑' V : β, |g V.1| :=
        norm_tsum_le_tsum_norm hsum_compl
      _ ≤ ∑' V : βN, |g V.1| := htail_subset
      _ ≤ Ctail * (N ^ (-((n - m : ℕ) : ℝ))) := htail'
  have hdecomp' :
      mainConstant n m k f =
        (∑ V ∈ B, g V) + ∑' V : β, g V.1 := by
    simpa [mainConstant, g, β] using hdecomp.symm
  refine ⟨Ctail, hCtail, ?_⟩
  rw [hdecomp']
  simpa [g, abs_sub_comm] using hcompl_abs

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
