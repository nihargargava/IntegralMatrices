import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Logic.Equiv.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.RamificationInertia.Inertia
import Katznelson.Foundations
import Katznelson.Counting.Admissible
import Katznelson.Counting.FiniteField
import Katznelson.Counting.LiftAverage
import Katznelson.Counting.RowSpaces
import Katznelson.Counting.RowLatticeRiemann
import Katznelson.Counting.GeometryOfNumbers
import Katznelson.Counting.SuccessiveMinima
import Katznelson.Counting.Schmidt
import Katznelson.Counting.Echelon
import Katznelson.Counting.CrudeHeight
import Katznelson.Counting.MinimumInjection
import Katznelson.Counting.MinimaSums
import Katznelson.Counting.CriticalRankOne
import Katznelson.Counting.CriticalMinima
import Katznelson.Counting.FixedRankError
import Katznelson.Counting.PaperMetricRowSpaces
import Katznelson.Lifts

namespace Katznelson

open scoped Classical
open Filter MeasureTheory
open scoped BigOperators NumberField Topology

/- Mathlib keeps matrix norms non-global because several choices are natural;
   the paper's Euclidean matrix norm is represented here by the Frobenius norm. -/
attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

/- [Lean infrastructure] `Matrix` is definitionally a finite iterated function
space, but its
   product measure instance is not exposed through the matrix wrapper. -/
noncomputable instance matrixMeasureSpace {m n R : Type*} [Fintype m] [Fintype n]
    [MeasureSpace R] :
    MeasureSpace (Matrix m n R) := by
  change MeasureSpace (m → n → R)
  infer_instance

/- [Lean infrastructure] The Frobenius norm gives matrices their Euclidean
topology.  Make its
   Borel measurable space explicit: typeclass search does not unfold the
   `Matrix` wrapper here. -/
noncomputable local instance matrixMeasurableSpace
    {m n R : Type*} [TopologicalSpace (Matrix m n R)] :
    MeasurableSpace (Matrix m n R) := borel (Matrix m n R)

local instance matrixBorelSpace
    {m n R : Type*} [TopologicalSpace (Matrix m n R)] :
    BorelSpace (Matrix m n R) := ⟨rfl⟩

/- [Lean infrastructure for paper Theorem `th:main`, lines 157--203] The
summand in the theorem, with the rank condition made explicit. -/
noncomputable def fixedRankTerm
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (T : ℝ)
    (A : IntegralMatrix K n m) : ℝ :=
  if integralMatrixRank A = k then
    f (T⁻¹ • embedMatrix A)
  else 0

/- [paper, Theorem `th:main`, lines 157--203] The sum over all integral
matrices of rank `k`. -/
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

/- [derived consequence, paper `eq:inequality_semifinal`, lines 1602--1612]
   The manuscript's unspecified multiplicative constant in `B_l(T)` is
   monotone.  This elementary fact is used only to make the finite-in-`l`
   uniformization of those constants explicit. -/
theorem B_l_mono
    {n m k l d : ℕ} {C C' T : ℝ} (hC : C ≤ C') (hT : 1 ≤ T) :
    B_l n m k l d C T ≤ B_l n m k l d C' T := by
  unfold B_l
  by_cases hpos : 0 < lowRankHeightExponent n m k l
  · rw [if_pos hpos]
    exact mul_le_mul_of_nonneg_right hC (zpow_nonneg (by linarith) _)
  · by_cases hzero : lowRankHeightExponent n m k l = 0
    · rw [if_neg hpos, if_pos hzero]
      have hlog : 0 ≤ Real.log T := Real.log_nonneg hT
      exact mul_le_mul_of_nonneg_right hC (by linarith)
    · rw [if_neg hpos, if_neg hzero]
      simpa using hC

/- [derived consequence, paper `eq:inequality_semifinal`, lines 1602--1612]
   Each branch of `B_l(T)` is nonnegative for the manuscript's range
   `T ≥ 1` and a nonnegative implicit constant. -/
theorem B_l_nonneg
    {n m k l d : ℕ} {C T : ℝ} (hC : 0 ≤ C) (hT : 1 ≤ T) :
    0 ≤ B_l n m k l d C T := by
  have hzero : B_l n m k l d 0 T = 0 := by
    simp [B_l]
  rw [← hzero]
  exact B_l_mono hC hT

/- [Lean infrastructure] The manuscript absorbs the finitely many constants
   arising for `1 ≤ l < k` into one implicit constant.  This is the explicit
   finite-sum bookkeeping version, retaining the paper's `alpha_l` and
   `B_l(T)` expressions without a change of summation argument. -/
theorem exists_uniform_B_l_point_bound
    {n m k d : ℕ} {T : ℝ} (hT : 1 ≤ T) (E : ℕ → ℝ)
    (hpoint : ∀ l ∈ Finset.Ico 1 k,
      ∃ C₁ C₂ Ccrudenew : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < Ccrudenew ∧
        E l ≤ C₁ * C₂ * T ^ alpha_l n m k l d *
          B_l n m k l d Ccrudenew T) :
    ∃ C₃ Ccrudenew : ℝ, 0 < C₃ ∧ 0 < Ccrudenew ∧
      ∀ l ∈ Finset.Ico 1 k,
        E l ≤ C₃ * T ^ alpha_l n m k l d *
          B_l n m k l d Ccrudenew T := by
  classical
  let F : Finset ℕ := Finset.Ico 1 k
  choose c₁ c₂ c hc₁ hc₂ hc hbound using fun l : F =>
    hpoint l.1 (by simpa [F] using l.2)
  let C₃ : ℝ := 1 + ∑ l ∈ F.attach, c₁ l * c₂ l
  let Ccrudenew : ℝ := 1 + ∑ l ∈ F.attach, c l
  have hsum₃_nonneg : 0 ≤ ∑ l ∈ F.attach, c₁ l * c₂ l := by
    exact Finset.sum_nonneg (fun l _ => mul_nonneg (hc₁ l).le (hc₂ l).le)
  have hsumC_nonneg : 0 ≤ ∑ l ∈ F.attach, c l := by
    exact Finset.sum_nonneg (fun l _ => (hc l).le)
  have hC₃ : 0 < C₃ := by
    dsimp [C₃]
    linarith
  have hCcrudenew : 0 < Ccrudenew := by
    dsimp [Ccrudenew]
    linarith
  refine ⟨C₃, Ccrudenew, hC₃, hCcrudenew, ?_⟩
  intro l hl
  let lF : F := ⟨l, by simpa [F] using hl⟩
  have hcprod_nonneg : 0 ≤ c₁ lF * c₂ lF :=
    mul_nonneg (hc₁ lF).le (hc₂ lF).le
  have hcprod_sum : c₁ lF * c₂ lF ≤ ∑ u ∈ F.attach, c₁ u * c₂ u := by
    exact Finset.single_le_sum (fun u _ => mul_nonneg (hc₁ u).le (hc₂ u).le)
      (F.mem_attach lF)
  have hcprod_uniform : c₁ lF * c₂ lF ≤ C₃ := by
    dsimp [C₃]
    linarith
  have hc_sum : c lF ≤ ∑ u ∈ F.attach, c u := by
    exact Finset.single_le_sum (fun u _ => (hc u).le) (F.mem_attach lF)
  have hc_uniform : c lF ≤ Ccrudenew := by
    dsimp [Ccrudenew]
    linarith
  have hTpow_nonneg : 0 ≤ T ^ alpha_l n m k l d :=
    zpow_nonneg (by linarith) _
  have hBmono : B_l n m k l d (c lF) T ≤
      B_l n m k l d Ccrudenew T :=
    B_l_mono hc_uniform hT
  have hB_nonneg : 0 ≤ B_l n m k l d Ccrudenew T :=
    B_l_nonneg hCcrudenew.le hT
  have hproduct_nonneg : 0 ≤
      T ^ alpha_l n m k l d * B_l n m k l d Ccrudenew T :=
    mul_nonneg hTpow_nonneg hB_nonneg
  have hbound_l : E l ≤ c₁ lF * c₂ lF * T ^ alpha_l n m k l d *
      B_l n m k l d (c lF) T := by
    simpa [lF] using hbound lF
  calc
    E l ≤ c₁ lF * c₂ lF * T ^ alpha_l n m k l d *
        B_l n m k l d (c lF) T := hbound_l
    _ = (c₁ lF * c₂ lF) *
        (T ^ alpha_l n m k l d * B_l n m k l d (c lF) T) := by ring
    _ ≤ (c₁ lF * c₂ lF) *
        (T ^ alpha_l n m k l d * B_l n m k l d Ccrudenew T) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hBmono hTpow_nonneg) hcprod_nonneg
    _ ≤ C₃ * (T ^ alpha_l n m k l d *
        B_l n m k l d Ccrudenew T) :=
      mul_le_mul_of_nonneg_right hcprod_uniform hproduct_nonneg
    _ = C₃ * T ^ alpha_l n m k l d *
        B_l n m k l d Ccrudenew T := by ring

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

/- [paper, `le:low_rank_induction`, lines 1431--1450]
   The paper's extension count is written in the original echelon notation:
   it counts `D ∈ 𝓕_k(T)` for which `Λ_{D'} ⊆ Λ_D`.  The row-space count
   below is a separate reindexing interface, not a replacement of this
   manuscript-facing quantity. -/
noncomputable def echelonExtensionCount
    {K : Type*} [Field K] [NumberField K]
    {m k l : ℕ} (B : Set (EchelonMatrix K k m))
    (D' : EchelonMatrix K l m) : ℝ :=
  ((B ∩ {D | echelonLambda D' ≤ echelonLambda D}).ncard : ℝ)

/- [derived consequence, paper `le:low_rank_induction`, lines 1431--1450]
   Transfer the preceding paper-facing count through the proved echelon--row
   space bijection.  The lattice inclusion is converted using the proved
   primitive-lattice/rational-row-space equivalence. -/
theorem echelonExtensionCount_eq_rowSpaceExtensionCount_image
    {K : Type*} [Field K] [NumberField K]
    {m k l : ℕ} (B : Set (EchelonMatrix K k m))
    (D' : EchelonMatrix K l m) :
    echelonExtensionCount B D' =
      rowSpaceExtensionCount (echelonRowSpace '' B) (echelonRowSpace D') := by
  have hset : echelonRowSpace ''
        (B ∩ {D | echelonLambda D' ≤ echelonLambda D}) =
      (echelonRowSpace '' B) ∩
        {V | (echelonRowSpace D').1 ≤ V.1} := by
    ext V
    constructor
    · rintro ⟨D, ⟨hDB, hD⟩, rfl⟩
      refine ⟨⟨D, hDB, rfl⟩, ?_⟩
      exact (echelonLambda_le_iff_echelonRowSpace_le D D').mp hD
    · rintro ⟨⟨D, hDB, rfl⟩, hD⟩
      refine ⟨D, ⟨hDB, ?_⟩, rfl⟩
      exact (echelonLambda_le_iff_echelonRowSpace_le D D').mpr hD
  dsimp [echelonExtensionCount, rowSpaceExtensionCount]
  rw [← Set.ncard_image_of_injective _
    (echelonRowSpace_injective (K := K) (l := k) (m := m))]
  rw [hset]

/- [derived consequence, paper `le:low_rank_induction`, lines 1471--1480]
   The paper overcounts extensions by choosing `k - l` vectors, one at a
   time, after projection modulo `Λ_{D'}`.  This is the exact finite
   combinatorial statement behind that overcount.  The choice map is kept as
   an explicit hypothesis: constructing it from the projected lattice is the
   separate geometric part of the paper's argument, and is not smuggled in
   through an opaque declaration. -/
theorem echelonExtensionCount_le_of_choice
    {α : Type*} {K : Type*} [Field K] [NumberField K]
    {m k l : ℕ} (B : Set (EchelonMatrix K k m)) [Fintype B]
    (D' : EchelonMatrix K l m) (S : Set α) (hS : S.Finite)
    (choice : EchelonMatrix K k m → Fin (k - l) → S)
    (hchoice : Set.InjOn (fun D => fun i => choice D i)
      (B ∩ {D | echelonLambda D' ≤ echelonLambda D})) :
    echelonExtensionCount B D' ≤ (S.ncard : ℝ) ^ (k - l) := by
  classical
  let E : Set (EchelonMatrix K k m) :=
    B ∩ {D | echelonLambda D' ≤ echelonLambda D}
  have hB : B.Finite := Set.toFinite B
  have hE : E.Finite := by
    exact hB.subset (by intro D hD; exact hD.1)
  letI : Fintype S := hS.fintype
  let c : EchelonMatrix K k m → (Fin (k - l) → S) :=
    fun D i => choice D i
  have hc : Set.InjOn c E := by
    intro D hD E' hE' hEq
    exact hchoice hD hE' hEq
  have hcard : E.ncard ≤ S.ncard ^ (k - l) := by
    calc
      E.ncard = (c '' E).ncard :=
        ((Set.ncard_image_iff hE).2 hc).symm
      _ ≤ (Set.univ : Set (Fin (k - l) → S)).ncard :=
        Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
      _ = Nat.card (Fin (k - l) → S) := Set.ncard_univ _
      _ = Nat.card S ^ Nat.card (Fin (k - l)) := Nat.card_fun
      _ = S.ncard ^ (k - l) := by
        rw [Nat.card_coe_set_eq, Nat.card_fin]
  dsimp [echelonExtensionCount, E]
  exact_mod_cast hcard

/- [Lean infrastructure] The orthogonal-complement subtype does not inherit a
   usable `BorelSpace` instance through the dependent row-span family.  Use
   its canonical Borel measurable space for the conditional ball-count
   bridge below. -/
noncomputable local instance mainTheoremsAmbientRowMeasurableSpace
    {K : Type*} [Field K] [NumberField K] {m : ℕ} :
    MeasurableSpace (RowVector K m) := borel (RowVector K m)

local instance mainTheoremsAmbientRowBorelSpace
    {K : Type*} [Field K] [NumberField K] {m : ℕ} :
    BorelSpace (RowVector K m) := ⟨rfl⟩

noncomputable local instance projectedRowMeasurableSpace
    {K : Type*} [Field K] [NumberField K]
    {m l : ℕ} (V : Grassmannian K m l) :
    MeasurableSpace ((rowRealSpan V)ᗮ) := borel ((rowRealSpan V)ᗮ)

local instance projectedRowBorelSpace
    {K : Type*} [Field K] [NumberField K]
    {m l : ℕ} (V : Grassmannian K m l) :
    BorelSpace ((rowRealSpan V)ᗮ) := ⟨rfl⟩

/- [derived consequence, paper `le:low_rank_induction`, lines 1475--1480]
   The manuscript applies `le:ballvol` to the projection of the ambient
   algebraic-integer row lattice.  Its exact covolume `H(D')⁻¹` and the
   radius comparison are kept explicit here; discreteness and fullness of the
   projected module are proved in `RowLattice.lean`.  The theorem is therefore
   a proved ball-count bridge, with only the normalization input still open. -/
theorem projectedAmbientRowModule_ball_count_of_geometry
    {K : Type*} [Field K] [NumberField K]
    {m l : ℕ} (V : Grassmannian K m l)
    {T R : ℝ} (hT : 0 < T)
    (μ : Measure ((rowRealSpan V)ᗮ)) [Measure.IsAddHaarMeasure μ]
    (hRadius : latticeFundamentalRadius
        (projectedAmbientRowModule (K := K) V) ≤ R)
    (hcov : ZLattice.covolume
        (projectedAmbientRowModule (K := K) V)
        μ =
      (rowSpaceHeight V)⁻¹) :
    ∃ C : ℝ, 0 < C ∧
      (Set.ncard {v : projectedAmbientRowModule (K := K) V |
        ‖(v : (rowRealSpan V)ᗮ)‖ ≤ T} : ℝ) ≤
        C * (T + R) ^ (m * degree K - l * degree K) *
          rowSpaceHeight V := by
  have hcover : LatticeCovering
      (projectedAmbientRowModule (K := K) V) R := by
    intro x
    obtain ⟨v, hv⟩ := latticeCovering_latticeCoveringRadius
      (projectedAmbientRowModule (K := K) V) x
    refine ⟨v, hv.trans ?_⟩
    exact (latticeCoveringRadius_le_latticeFundamentalRadius
      (projectedAmbientRowModule (K := K) V)).trans hRadius
  obtain ⟨C, hC, hcount⟩ := lattice_ball_count_of_latticeCovering
    (L := projectedAmbientRowModule (K := K) V) μ hT hcover
  have hdim : Module.finrank ℝ ((rowRealSpan V)ᗮ) =
      m * degree K - l * degree K := by
    calc
      Module.finrank ℝ ((rowRealSpan V)ᗮ) =
          Module.finrank ℝ (⊤ : Submodule ℝ ((rowRealSpan V)ᗮ)) := by
        rw [finrank_top]
      _ = Module.finrank ℝ
          (Submodule.span ℝ
            (projectedAmbientRowModule (K := K) V :
              Set ((rowRealSpan V)ᗮ))) := by
        rw [projectedAmbientRowModule_span_top]
      _ = m * degree K - l * degree K :=
        projectedAmbientRowModule_finrank V
  refine ⟨C, hC, ?_⟩
  calc
    (Set.ncard {v : projectedAmbientRowModule (K := K) V |
          ‖(v : (rowRealSpan V)ᗮ)‖ ≤ T} : ℝ) ≤
        C * (T + R) ^ Module.finrank ℝ ((rowRealSpan V)ᗮ) *
          (ZLattice.covolume (projectedAmbientRowModule (K := K) V)
            μ)⁻¹ :=
      hcount
    _ = C * (T + R) ^ (m * degree K - l * degree K) *
          rowSpaceHeight V := by
      rw [hdim, hcov, inv_inv]

/- [derived consequence, paper `le:low_rank_induction`, lines 1475--1480]
   The same bridge using the manuscript's intrinsic covering-radius input.
   The exact projected covolume remains an explicit hypothesis, while the
   radius comparison, discreteness, and fullness are proved by
   `projectedAmbientRowModule_isLatticeCovering_of_ambient`. -/
set_option maxHeartbeats 800000 in
theorem projectedAmbientRowModule_ball_count_of_covering
    {K : Type*} [Field K] [NumberField K]
    {m l : ℕ} (V : Grassmannian K m l)
    {T R : ℝ} (hT : 0 < T)
    (μ : Measure ((rowRealSpan V)ᗮ)) [Measure.IsAddHaarMeasure μ]
    (hcover : LatticeCovering
      (projectedAmbientRowModule (K := K) V) R)
    (hcov : ZLattice.covolume
        (projectedAmbientRowModule (K := K) V)
        μ = (rowSpaceHeight V)⁻¹) :
    ∃ C : ℝ, 0 < C ∧
      (Set.ncard {v : projectedAmbientRowModule (K := K) V |
        ‖(v : (rowRealSpan V)ᗮ)‖ ≤ T} : ℝ) ≤
        C * (T + R) ^ (m * degree K - l * degree K) *
          rowSpaceHeight V := by
  obtain ⟨C, hC, hcount⟩ := lattice_ball_count_of_latticeCovering
    (L := projectedAmbientRowModule (K := K) V) μ hT hcover
  have hdim : Module.finrank ℝ ((rowRealSpan V)ᗮ) =
      m * degree K - l * degree K := by
    calc
      Module.finrank ℝ ((rowRealSpan V)ᗮ) =
          Module.finrank ℝ (⊤ : Submodule ℝ ((rowRealSpan V)ᗮ)) := by
        rw [finrank_top]
      _ = Module.finrank ℝ
          (Submodule.span ℝ
            (projectedAmbientRowModule (K := K) V :
              Set ((rowRealSpan V)ᗮ))) := by
        rw [projectedAmbientRowModule_span_top]
      _ = m * degree K - l * degree K :=
        projectedAmbientRowModule_finrank V
  have hheight : 0 < rowSpaceHeight V := rowSpaceHeight_pos V
  refine ⟨C, hC, ?_⟩
  calc
    (Set.ncard {v : projectedAmbientRowModule (K := K) V |
          ‖(v : (rowRealSpan V)ᗮ)‖ ≤ T} : ℝ) ≤
        C * (T + R) ^ Module.finrank ℝ ((rowRealSpan V)ᗮ) *
          (ZLattice.covolume (projectedAmbientRowModule (K := K) V)
            μ)⁻¹ := hcount
    _ = C * (T + R) ^ (m * degree K - l * degree K) *
          rowSpaceHeight V := by
      rw [hdim, hcov, inv_inv]

/- [derived consequence, paper `le:low_rank_induction`, lines 1475--1480]
   This is the coarse raw-Euclidean version of the projected-lattice ball
   bound.  The raw primitive-projection formula from `RowLattice.lean`
   replaces the normalization-sensitive hypothesis above: the covolume of
   the fixed ambient integral-row lattice is absorbed into `C`.  Thus this
   proves the `≪` form needed for the induction without identifying it with
   the manuscript's exact paper-metric displayed equality `H(D')⁻¹`. -/
set_option maxHeartbeats 800000 in
theorem projectedAmbientRowModule_ball_count_of_raw_covering
    {K : Type*} [Field K] [NumberField K]
    {m l : ℕ} (V : Grassmannian K m l)
    {T R : ℝ} (hT : 0 < T)
    (hcover : LatticeCovering
      (projectedAmbientRowModule (K := K) V) R) :
    ∃ C : ℝ, 0 < C ∧
      (Set.ncard {v : projectedAmbientRowModule (K := K) V |
        ‖(v : (rowRealSpan V)ᗮ)‖ ≤ T} : ℝ) ≤
        C * (T + R) ^ (m * degree K - l * degree K) *
          rowSpaceHeight V := by
  let μ : Measure ((rowRealSpan V)ᗮ) :=
    μHE[Module.finrank ℝ ((rowRealSpan V)ᗮ)]
  obtain ⟨C, hC, hcount⟩ := lattice_ball_count_of_latticeCovering
    (L := projectedAmbientRowModule (K := K) V) μ hT hcover
  let A : ℝ := ZLattice.covolume (ambientIntegralRowModule (K := K) m)
    (μHE[Module.finrank ℝ (RowVector K m)])
  let P : ℝ := ZLattice.covolume (projectedAmbientRowModule (K := K) V) μ
  let H : ℝ := rowSpaceHeight V
  have hA : 0 < A := by
    dsimp [A]
    exact ZLattice.covolume_pos (ambientIntegralRowModule (K := K) m)
      (μHE[Module.finrank ℝ (RowVector K m)])
  have hP : 0 < P := by
    dsimp [P, μ]
    exact ZLattice.covolume_pos (projectedAmbientRowModule (K := K) V)
      (μHE[Module.finrank ℝ ((rowRealSpan V)ᗮ)])
  have hH : 0 < H := by
    dsimp [H]
    exact rowSpaceHeight_pos V
  have hprod : A = H * P := by
    dsimp [A, H, P, μ]
    exact ambientIntegralRowModule_covolume_eq_rowSpaceHeight_mul_projectedCovolume V
  have hinv : P⁻¹ = A⁻¹ * H := by
    rw [hprod]
    field_simp
  have hdim : Module.finrank ℝ ((rowRealSpan V)ᗮ) =
      m * degree K - l * degree K := by
    calc
      Module.finrank ℝ ((rowRealSpan V)ᗮ) =
          Module.finrank ℝ (⊤ : Submodule ℝ ((rowRealSpan V)ᗮ)) := by
        rw [finrank_top]
      _ = Module.finrank ℝ
          (Submodule.span ℝ
            (projectedAmbientRowModule (K := K) V :
              Set ((rowRealSpan V)ᗮ))) := by
        rw [projectedAmbientRowModule_span_top]
      _ = m * degree K - l * degree K :=
        projectedAmbientRowModule_finrank V
  refine ⟨C * A⁻¹, mul_pos hC (inv_pos.mpr hA), ?_⟩
  change (Set.ncard {v : projectedAmbientRowModule (K := K) V |
        ‖(v : (rowRealSpan V)ᗮ)‖ ≤ T} : ℝ) ≤
      (C * A⁻¹) * (T + R) ^ (m * degree K - l * degree K) * H
  calc
    (Set.ncard {v : projectedAmbientRowModule (K := K) V |
          ‖(v : (rowRealSpan V)ᗮ)‖ ≤ T} : ℝ) ≤
        C * (T + R) ^ Module.finrank ℝ ((rowRealSpan V)ᗮ) * P⁻¹ := by
          exact hcount
    _ = (C * A⁻¹) * (T + R) ^ (m * degree K - l * degree K) * H := by
      rw [hdim, hinv]
      ring

/- [derived consequence, paper `le:low_rank_induction`, lines 1475--1480]
   Uniform raw-Euclidean version of the preceding projected ball count.  The
   Euclidean unit-ball volume depends only on the fixed complementary
   dimension `d * (m - l)`, and the ambient covolume depends only on `K,m`.
   Thus the displayed constant is independent of the lower row space and of
   `T`, exactly as required by the manuscript's implicit-constant notation.
   This remains a raw-metric estimate; it does not identify that constant
   with the paper's normalized `H(D')^{-1}` covolume formula. -/
set_option maxHeartbeats 800000 in
theorem projectedAmbientRowModule_ball_count_of_raw_covering_uniform
    {K : Type*} [Field K] [NumberField K]
    {m l : ℕ} (hlm : l < m) (V : Grassmannian K m l)
    {T R : ℝ} (hT : 0 < T)
    (hcover : LatticeCovering
      (projectedAmbientRowModule (K := K) V) R) :
    (Set.ncard {v : projectedAmbientRowModule (K := K) V |
        ‖(v : (rowRealSpan V)ᗮ)‖ ≤ T} : ℝ) ≤
      (euclideanUnitBallVolume (m * degree K - l * degree K) *
        (ZLattice.covolume (ambientIntegralRowModule (K := K) m)
          (μHE[Module.finrank ℝ (RowVector K m)]))⁻¹) *
        (T + R) ^ (m * degree K - l * degree K) *
          rowSpaceHeight V := by
  let μ : Measure ((rowRealSpan V)ᗮ) :=
    μHE[Module.finrank ℝ ((rowRealSpan V)ᗮ)]
  let A : ℝ := ZLattice.covolume (ambientIntegralRowModule (K := K) m)
    (μHE[Module.finrank ℝ (RowVector K m)])
  let P : ℝ := ZLattice.covolume (projectedAmbientRowModule (K := K) V) μ
  let H : ℝ := rowSpaceHeight V
  have hdim : Module.finrank ℝ ((rowRealSpan V)ᗮ) =
      m * degree K - l * degree K := by
    calc
      Module.finrank ℝ ((rowRealSpan V)ᗮ) =
          Module.finrank ℝ (⊤ : Submodule ℝ ((rowRealSpan V)ᗮ)) := by
        rw [finrank_top]
      _ = Module.finrank ℝ
          (Submodule.span ℝ
            (projectedAmbientRowModule (K := K) V :
              Set ((rowRealSpan V)ᗮ))) := by
        rw [projectedAmbientRowModule_span_top]
      _ = m * degree K - l * degree K :=
        projectedAmbientRowModule_finrank V
  have hqpos : 0 < Module.finrank ℝ ((rowRealSpan V)ᗮ) := by
    rw [hdim]
    apply Nat.sub_pos_iff_lt.mpr
    exact Nat.mul_lt_mul_of_pos_right hlm Module.finrank_pos
  letI : Nontrivial ((rowRealSpan V)ᗮ) :=
    Module.nontrivial_of_finrank_pos hqpos
  have hunit : μ.real (Metric.closedBall (0 : ((rowRealSpan V)ᗮ)) 1) =
      euclideanUnitBallVolume (m * degree K - l * degree K) := by
    simpa [μ, hdim] using
      (euclideanHausdorffMeasureReal_unitClosedBall
        (E := ((rowRealSpan V)ᗮ)))
  have hA : 0 < A := by
    dsimp [A]
    exact ZLattice.covolume_pos (ambientIntegralRowModule (K := K) m)
      (μHE[Module.finrank ℝ (RowVector K m)])
  have hP : 0 < P := by
    dsimp [P, μ]
    exact ZLattice.covolume_pos (projectedAmbientRowModule (K := K) V)
      (μHE[Module.finrank ℝ ((rowRealSpan V)ᗮ)])
  have hH : 0 < H := by
    dsimp [H]
    exact rowSpaceHeight_pos V
  have hprod : A = H * P := by
    dsimp [A, H, P, μ]
    exact ambientIntegralRowModule_covolume_eq_rowSpaceHeight_mul_projectedCovolume V
  have hinv : P⁻¹ = A⁻¹ * H := by
    rw [hprod]
    field_simp
  have hcount :
      (Set.ncard {v : projectedAmbientRowModule (K := K) V |
          ‖(v : (rowRealSpan V)ᗮ)‖ ≤ T} : ℝ) ≤
        μ.real (Metric.closedBall (0 : ((rowRealSpan V)ᗮ)) 1) *
          (T + R) ^ Module.finrank ℝ ((rowRealSpan V)ᗮ) * P⁻¹ := by
    exact lattice_ball_count_of_latticeCovering_unitBall
      (L := projectedAmbientRowModule (K := K) V) μ hT hcover
  change (Set.ncard {v : projectedAmbientRowModule (K := K) V |
        ‖(v : (rowRealSpan V)ᗮ)‖ ≤ T} : ℝ) ≤
      (euclideanUnitBallVolume (m * degree K - l * degree K) * A⁻¹) *
        (T + R) ^ (m * degree K - l * degree K) * H
  calc
    (Set.ncard {v : projectedAmbientRowModule (K := K) V |
        ‖(v : (rowRealSpan V)ᗮ)‖ ≤ T} : ℝ) ≤
        μ.real (Metric.closedBall (0 : ((rowRealSpan V)ᗮ)) 1) *
          (T + R) ^ Module.finrank ℝ ((rowRealSpan V)ᗮ) * P⁻¹ := by
      exact hcount
    _ = (euclideanUnitBallVolume (m * degree K - l * degree K) * A⁻¹) *
        (T + R) ^ (m * degree K - l * degree K) * H := by
      rw [hunit, hdim, hinv]
      ring

/- [derived consequence, paper `le:low_rank_induction`, lines 1431--1480]
   Join the paper-facing finite choice overcount to the projected ball count.
   The codomain of `choice` is exactly the projected ambient module in the
   paper's construction, and the injectivity hypothesis is the formal version
   of the assertion that the chosen projected vectors distinguish the
   extensions.  The projected module's covolume and the choice construction
   remain explicit hypotheses; this declaration does not hide either input. -/
set_option maxHeartbeats 800000 in
theorem echelonExtensionCount_le_of_projected_ball
    {K : Type*} [Field K] [NumberField K]
    {m k l : ℕ} (B : Set (EchelonMatrix K k m)) [Fintype B]
    (D' : EchelonMatrix K l m) {T R : ℝ} (hT : 0 < T)
    (μ : Measure ((rowRealSpan (echelonRowSpace D'))ᗮ))
    [Measure.IsAddHaarMeasure μ]
    (hRadius : latticeFundamentalRadius
      (projectedAmbientRowModule (K := K) (echelonRowSpace D')) ≤ R)
    (hcov : ZLattice.covolume
      (projectedAmbientRowModule (K := K) (echelonRowSpace D')) μ =
        (rowSpaceHeight (echelonRowSpace D'))⁻¹)
    (choice : EchelonMatrix K k m → Fin (k - l) →
      {v : projectedAmbientRowModule (K := K) (echelonRowSpace D') |
        ‖(v : (rowRealSpan (echelonRowSpace D'))ᗮ)‖ ≤ T})
    (hchoice : Set.InjOn (fun D => fun i => choice D i)
      (B ∩ {D | echelonLambda D' ≤ echelonLambda D})) :
    ∃ C : ℝ, 0 < C ∧
      echelonExtensionCount B D' ≤
        (C * (T + R) ^ (m * degree K - l * degree K) *
          rowSpaceHeight (echelonRowSpace D')) ^ (k - l) := by
  let S : Set (projectedAmbientRowModule (K := K)
      (echelonRowSpace D')) := {v |
        ‖(v : (rowRealSpan (echelonRowSpace D'))ᗮ)‖ ≤ T}
  have hS : S.Finite := by
    change {v : projectedAmbientRowModule (K := K)
        (echelonRowSpace D') |
        ‖(v : (rowRealSpan (echelonRowSpace D'))ᗮ)‖ ≤ T}.Finite
    exact lattice_ball_finite
      (projectedAmbientRowModule (K := K) (echelonRowSpace D'))
  obtain ⟨C, hC, hball⟩ :=
    projectedAmbientRowModule_ball_count_of_geometry
      (echelonRowSpace D') hT μ hRadius hcov
  let choice' : EchelonMatrix K k m → Fin (k - l) → S :=
    fun D i => ⟨choice D i, (choice D i).property⟩
  have hchoice' : Set.InjOn (fun D => fun i => choice' D i)
      (B ∩ {D | echelonLambda D' ≤ echelonLambda D}) := by
    intro D hD E hE hEq
    apply hchoice hD hE
    funext i
    apply Subtype.ext
    exact congrArg (fun x : S => x.1) (congrFun hEq i)
  have hcount := echelonExtensionCount_le_of_choice
    B D' S hS choice' hchoice'
  have hball' :
      (S.ncard : ℝ) ≤
        C * (T + R) ^ (m * degree K - l * degree K) *
          rowSpaceHeight (echelonRowSpace D') := by
    change (Set.ncard {v : projectedAmbientRowModule (K := K)
        (echelonRowSpace D') |
        ‖(v : (rowRealSpan (echelonRowSpace D'))ᗮ)‖ ≤ T} : ℝ) ≤ _
    exact hball
  have hbase : 0 ≤ (S.ncard : ℝ) := by positivity
  refine ⟨C, hC, ?_⟩
  calc
    echelonExtensionCount B D' ≤ (S.ncard : ℝ) ^ (k - l) := hcount
    _ ≤ (C * (T + R) ^ (m * degree K - l * degree K) *
          rowSpaceHeight (echelonRowSpace D')) ^ (k - l) :=
      pow_le_pow_left₀ hbase hball' _

/- [derived consequence, paper `le:low_rank_induction`, lines 1431--1480]
   Normalize the preceding `(T + R)` estimate to the exact polynomial scale
   displayed by the manuscript.  The constant absorbs only the fixed radius
   bound and the unit-ball constant; it is independent of `T` and `D'`. -/
set_option maxHeartbeats 800000 in
theorem echelonExtensionCount_le_of_projected_geometry
    {K : Type*} [Field K] [NumberField K]
    {m k l : ℕ} (B : Set (EchelonMatrix K k m)) [Fintype B]
    (D' : EchelonMatrix K l m) {T R : ℝ} (hT : 1 ≤ T)
    (μ : Measure ((rowRealSpan (echelonRowSpace D'))ᗮ))
    [Measure.IsAddHaarMeasure μ]
    (hdisc : DiscreteTopology
      (projectedAmbientRowModule (K := K) (echelonRowSpace D')))
    (hZ : IsZLattice ℝ
      (projectedAmbientRowModule (K := K) (echelonRowSpace D')))
    (hRadius : latticeFundamentalRadius
      (projectedAmbientRowModule (K := K) (echelonRowSpace D')) ≤ R)
    (hcov : ZLattice.covolume
      (projectedAmbientRowModule (K := K) (echelonRowSpace D')) μ =
        (rowSpaceHeight (echelonRowSpace D'))⁻¹)
    (choice : EchelonMatrix K k m → Fin (k - l) →
      {v : projectedAmbientRowModule (K := K) (echelonRowSpace D') |
        ‖(v : (rowRealSpan (echelonRowSpace D'))ᗮ)‖ ≤ T})
    (hchoice : Set.InjOn (fun D => fun i => choice D i)
      (B ∩ {D | echelonLambda D' ≤ echelonLambda D})) :
    ∃ C : ℝ, 0 < C ∧
      echelonExtensionCount B D' ≤
        C * T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight (echelonRowSpace D') ^ (k - l) := by
  have hT₀ : 0 < T := lt_of_lt_of_le zero_lt_one hT
  obtain ⟨C₀, hC₀, hball⟩ :=
    echelonExtensionCount_le_of_projected_ball B D' hT₀ μ
      hRadius hcov choice hchoice
  let q : ℕ := m * degree K - l * degree K
  have hlm : l ≤ m := by
    have hdim := Submodule.finrank_le (echelonRowSpace D').1
    rw [echelonRowSpace_rank, Module.finrank_pi_fintype] at hdim
    simpa using hdim
  have hqeq : q = degree K * (m - l) := by
    dsimp [q]
    calc
      m * degree K - l * degree K = (m - l) * degree K :=
        (Nat.sub_mul m l (degree K)).symm
      _ = degree K * (m - l) := Nat.mul_comm _ _
  have hball' :
      echelonExtensionCount B D' ≤
        (C₀ * (T + R) ^ q *
          rowSpaceHeight (echelonRowSpace D')) ^ (k - l) := by
    simpa [q] using hball
  have hR : 0 ≤ R := le_trans
    (latticeFundamentalRadius_nonneg
      (projectedAmbientRowModule (K := K) (echelonRowSpace D'))) hRadius
  have hRT : R ≤ R * T := by
    calc
      R = R * 1 := by ring
      _ ≤ R * T := mul_le_mul_of_nonneg_left hT hR
  have hTR : T + R ≤ (1 + R) * T := by
    calc
      T + R = T + R * 1 := by ring
      _ ≤ T + R * T := by
        simpa [add_comm] using add_le_add_left hRT T
      _ = (1 + R) * T := by ring
  have hTR_nonneg : 0 ≤ T + R := by linarith
  have hH : 0 ≤ rowSpaceHeight (echelonRowSpace D') :=
    (rowSpaceHeight_pos (echelonRowSpace D')).le
  have hinner :
      C₀ * (T + R) ^ q * rowSpaceHeight (echelonRowSpace D') ≤
        C₀ * ((1 + R) ^ q * T ^ q) *
          rowSpaceHeight (echelonRowSpace D') := by
    calc
      C₀ * (T + R) ^ q * rowSpaceHeight (echelonRowSpace D') ≤
          C₀ * ((1 + R) * T) ^ q *
            rowSpaceHeight (echelonRowSpace D') := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hTR_nonneg hTR q) hC₀.le) hH
      _ = C₀ * ((1 + R) ^ q * T ^ q) *
            rowSpaceHeight (echelonRowSpace D') := by
        rw [mul_pow]
  have hbase_nonneg :
      0 ≤ C₀ * (T + R) ^ q * rowSpaceHeight (echelonRowSpace D') := by
    exact mul_nonneg (mul_nonneg hC₀.le (pow_nonneg hTR_nonneg _)) hH
  have hpow := pow_le_pow_left₀ hbase_nonneg hinner (k - l)
  let C₁ : ℝ := (C₀ * (1 + R) ^ q) ^ (k - l)
  have hC₁ : 0 < C₁ := by
    dsimp [C₁]
    exact pow_pos (mul_pos hC₀ (pow_pos (by linarith) _)) _
  have hrewrite :
      (C₀ * ((1 + R) ^ q * T ^ q) *
          rowSpaceHeight (echelonRowSpace D')) ^ (k - l) =
        C₁ * T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight (echelonRowSpace D') ^ (k - l) := by
    calc
      (C₀ * ((1 + R) ^ q * T ^ q) *
          rowSpaceHeight (echelonRowSpace D')) ^ (k - l) =
          ((C₀ * (1 + R) ^ q) * T ^ q *
            rowSpaceHeight (echelonRowSpace D')) ^ (k - l) := by
        congr 1
        ring
      _ = (C₀ * (1 + R) ^ q) ^ (k - l) *
          (T ^ q) ^ (k - l) *
            rowSpaceHeight (echelonRowSpace D') ^ (k - l) := by
        rw [mul_pow, mul_pow]
      _ = (C₀ * (1 + R) ^ q) ^ (k - l) *
          T ^ (q * (k - l)) *
            rowSpaceHeight (echelonRowSpace D') ^ (k - l) := by
        rw [← pow_mul]
      _ = C₁ * T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight (echelonRowSpace D') ^ (k - l) := by
        dsimp [C₁]
        rw [hqeq]
        congr 2
        ring
  refine ⟨C₁, hC₁, ?_⟩
  calc
    echelonExtensionCount B D' ≤
        (C₀ * (T + R) ^ q *
          rowSpaceHeight (echelonRowSpace D')) ^ (k - l) := hball'
    _ ≤ (C₀ * ((1 + R) ^ q * T ^ q) *
          rowSpaceHeight (echelonRowSpace D')) ^ (k - l) := hpow
    _ = C₁ * T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight (echelonRowSpace D') ^ (k - l) := hrewrite

/- [derived consequence, paper `le:low_rank_induction`, lines 1431--1480]
   The extension overcount with the manuscript's covering-radius input. -/
set_option maxHeartbeats 800000 in
theorem echelonExtensionCount_le_of_projected_covering
    {K : Type*} [Field K] [NumberField K]
    {m k l : ℕ} (B : Set (EchelonMatrix K k m)) [Fintype B]
    (D' : EchelonMatrix K l m) {T R : ℝ} (hT : 0 < T)
    (μ : Measure ((rowRealSpan (echelonRowSpace D'))ᗮ))
    [Measure.IsAddHaarMeasure μ]
    (hcover : LatticeCovering
      (projectedAmbientRowModule (K := K) (echelonRowSpace D')) R)
    (hcov : ZLattice.covolume
      (projectedAmbientRowModule (K := K) (echelonRowSpace D')) μ =
        (rowSpaceHeight (echelonRowSpace D'))⁻¹)
    (choice : EchelonMatrix K k m → Fin (k - l) →
      {v : projectedAmbientRowModule (K := K) (echelonRowSpace D') |
        ‖(v : (rowRealSpan (echelonRowSpace D'))ᗮ)‖ ≤ T})
    (hchoice : Set.InjOn (fun D => fun i => choice D i)
      (B ∩ {D | echelonLambda D' ≤ echelonLambda D})) :
    ∃ C : ℝ, 0 < C ∧
      echelonExtensionCount B D' ≤
        (C * (T + R) ^ (m * degree K - l * degree K) *
          rowSpaceHeight (echelonRowSpace D')) ^ (k - l) := by
  let S : Set (projectedAmbientRowModule (K := K)
      (echelonRowSpace D')) := {v |
        ‖(v : (rowRealSpan (echelonRowSpace D'))ᗮ)‖ ≤ T}
  have hS : S.Finite := by
    change {v : projectedAmbientRowModule (K := K)
        (echelonRowSpace D') |
        ‖(v : (rowRealSpan (echelonRowSpace D'))ᗮ)‖ ≤ T}.Finite
    exact lattice_ball_finite
      (projectedAmbientRowModule (K := K) (echelonRowSpace D'))
  obtain ⟨C, hC, hball⟩ :=
    projectedAmbientRowModule_ball_count_of_covering
      (echelonRowSpace D') hT μ hcover hcov
  let choice' : EchelonMatrix K k m → Fin (k - l) → S :=
    fun D i => ⟨choice D i, (choice D i).property⟩
  have hchoice' : Set.InjOn (fun D => fun i => choice' D i)
      (B ∩ {D | echelonLambda D' ≤ echelonLambda D}) := by
    intro D hD E hE hEq
    apply hchoice hD hE
    funext i
    apply Subtype.ext
    exact congrArg (fun x : S => x.1) (congrFun hEq i)
  have hcount := echelonExtensionCount_le_of_choice
    B D' S hS choice' hchoice'
  have hball' :
      (S.ncard : ℝ) ≤
        C * (T + R) ^ (m * degree K - l * degree K) *
          rowSpaceHeight (echelonRowSpace D') := by
    change (Set.ncard {v : projectedAmbientRowModule (K := K)
        (echelonRowSpace D') |
        ‖(v : (rowRealSpan (echelonRowSpace D'))ᗮ)‖ ≤ T} : ℝ) ≤ _
    exact hball
  have hbase : 0 ≤ (S.ncard : ℝ) := by positivity
  refine ⟨C, hC, ?_⟩
  calc
    echelonExtensionCount B D' ≤ (S.ncard : ℝ) ^ (k - l) := hcount
    _ ≤ (C * (T + R) ^ (m * degree K - l * degree K) *
          rowSpaceHeight (echelonRowSpace D')) ^ (k - l) :=
      pow_le_pow_left₀ hbase hball' _

/- [derived consequence, paper `le:low_rank_induction`, lines 1431--1480]
   Raw-Euclidean counterpart of the preceding extension bound.  It uses the
   proved raw primitive-projection covolume formula, with the covolume of the
   fixed ambient row lattice absorbed into the implicit constant.  It does
   not assert the manuscript's paper-metric normalization. -/
set_option maxHeartbeats 800000 in
theorem echelonExtensionCount_le_of_raw_projected_covering
    {K : Type*} [Field K] [NumberField K]
    {m k l : ℕ} (B : Set (EchelonMatrix K k m)) [Fintype B]
    (D' : EchelonMatrix K l m) {T R : ℝ} (hT : 0 < T)
    (hcover : LatticeCovering
      (projectedAmbientRowModule (K := K) (echelonRowSpace D')) R)
    (choice : EchelonMatrix K k m → Fin (k - l) →
      {v : projectedAmbientRowModule (K := K) (echelonRowSpace D') |
        ‖(v : (rowRealSpan (echelonRowSpace D'))ᗮ)‖ ≤ T})
    (hchoice : Set.InjOn (fun D => fun i => choice D i)
      (B ∩ {D | echelonLambda D' ≤ echelonLambda D})) :
    ∃ C : ℝ, 0 < C ∧
      echelonExtensionCount B D' ≤
        (C * (T + R) ^ (m * degree K - l * degree K) *
          rowSpaceHeight (echelonRowSpace D')) ^ (k - l) := by
  let S : Set (projectedAmbientRowModule (K := K)
      (echelonRowSpace D')) := {v |
        ‖(v : (rowRealSpan (echelonRowSpace D'))ᗮ)‖ ≤ T}
  have hS : S.Finite := by
    change {v : projectedAmbientRowModule (K := K)
        (echelonRowSpace D') |
        ‖(v : (rowRealSpan (echelonRowSpace D'))ᗮ)‖ ≤ T}.Finite
    exact lattice_ball_finite
      (projectedAmbientRowModule (K := K) (echelonRowSpace D'))
  obtain ⟨C, hC, hball⟩ :=
    projectedAmbientRowModule_ball_count_of_raw_covering
      (echelonRowSpace D') hT hcover
  let choice' : EchelonMatrix K k m → Fin (k - l) → S :=
    fun D i => ⟨choice D i, (choice D i).property⟩
  have hchoice' : Set.InjOn (fun D => fun i => choice' D i)
      (B ∩ {D | echelonLambda D' ≤ echelonLambda D}) := by
    intro D hD E hE hEq
    apply hchoice hD hE
    funext i
    apply Subtype.ext
    exact congrArg (fun x : S => x.1) (congrFun hEq i)
  have hcount := echelonExtensionCount_le_of_choice
    B D' S hS choice' hchoice'
  have hball' :
      (S.ncard : ℝ) ≤
        C * (T + R) ^ (m * degree K - l * degree K) *
          rowSpaceHeight (echelonRowSpace D') := by
    change (Set.ncard {v : projectedAmbientRowModule (K := K)
        (echelonRowSpace D') |
        ‖(v : (rowRealSpan (echelonRowSpace D'))ᗮ)‖ ≤ T} : ℝ) ≤ _
    exact hball
  have hbase : 0 ≤ (S.ncard : ℝ) := by positivity
  refine ⟨C, hC, ?_⟩
  calc
    echelonExtensionCount B D' ≤ (S.ncard : ℝ) ^ (k - l) := hcount
    _ ≤ (C * (T + R) ^ (m * degree K - l * degree K) *
          rowSpaceHeight (echelonRowSpace D')) ^ (k - l) :=
      pow_le_pow_left₀ hbase hball' _

/- [derived consequence, paper `le:low_rank_induction`, lines 1431--1480]
   Raw-Euclidean extension count with its ball-volume constant retained
   explicitly.  Unlike the existential convenience form above, this statement
   preserves the fact that the constant depends only on the fixed field and
   dimensions, not on `D'` or `T`. -/
set_option maxHeartbeats 1200000 in
theorem echelonExtensionCount_le_of_raw_projected_covering_uniform
    {K : Type*} [Field K] [NumberField K]
    {m k l : ℕ} (B : Set (EchelonMatrix K k m)) [Fintype B]
    (D' : EchelonMatrix K l m) (hlm : l < m) {T R : ℝ} (hT : 0 < T)
    (hcover : LatticeCovering
      (projectedAmbientRowModule (K := K) (echelonRowSpace D')) R)
    (choice : EchelonMatrix K k m → Fin (k - l) →
      {v : projectedAmbientRowModule (K := K) (echelonRowSpace D') |
        ‖(v : (rowRealSpan (echelonRowSpace D'))ᗮ)‖ ≤ T})
    (hchoice : Set.InjOn (fun D => fun i => choice D i)
      (B ∩ {D | echelonLambda D' ≤ echelonLambda D})) :
    echelonExtensionCount B D' ≤
      ((euclideanUnitBallVolume (m * degree K - l * degree K) *
        (ZLattice.covolume (ambientIntegralRowModule (K := K) m)
          (μHE[Module.finrank ℝ (RowVector K m)]))⁻¹) *
        (T + R) ^ (m * degree K - l * degree K) *
          rowSpaceHeight (echelonRowSpace D')) ^ (k - l) := by
  let S : Set (projectedAmbientRowModule (K := K)
      (echelonRowSpace D')) := {v |
        ‖(v : (rowRealSpan (echelonRowSpace D'))ᗮ)‖ ≤ T}
  have hS : S.Finite := by
    change {v : projectedAmbientRowModule (K := K)
        (echelonRowSpace D') |
        ‖(v : (rowRealSpan (echelonRowSpace D'))ᗮ)‖ ≤ T}.Finite
    exact lattice_ball_finite
      (projectedAmbientRowModule (K := K) (echelonRowSpace D'))
  have hball := projectedAmbientRowModule_ball_count_of_raw_covering_uniform
    (K := K) hlm (echelonRowSpace D') hT hcover
  let choice' : EchelonMatrix K k m → Fin (k - l) → S :=
    fun D i => ⟨choice D i, (choice D i).property⟩
  have hchoice' : Set.InjOn (fun D => fun i => choice' D i)
      (B ∩ {D | echelonLambda D' ≤ echelonLambda D}) := by
    intro D hD E hE hEq
    apply hchoice hD hE
    funext i
    apply Subtype.ext
    exact congrArg (fun x : S => x.1) (congrFun hEq i)
  have hcount := echelonExtensionCount_le_of_choice
    B D' S hS choice' hchoice'
  have hball' :
      (S.ncard : ℝ) ≤
        (euclideanUnitBallVolume (m * degree K - l * degree K) *
          (ZLattice.covolume (ambientIntegralRowModule (K := K) m)
            (μHE[Module.finrank ℝ (RowVector K m)]))⁻¹) *
          (T + R) ^ (m * degree K - l * degree K) *
            rowSpaceHeight (echelonRowSpace D') := by
    change (Set.ncard {v : projectedAmbientRowModule (K := K)
        (echelonRowSpace D') |
        ‖(v : (rowRealSpan (echelonRowSpace D'))ᗮ)‖ ≤ T} : ℝ) ≤ _
    exact hball
  have hbase : 0 ≤ (S.ncard : ℝ) := by positivity
  calc
    echelonExtensionCount B D' ≤ (S.ncard : ℝ) ^ (k - l) := hcount
    _ ≤ ((euclideanUnitBallVolume (m * degree K - l * degree K) *
          (ZLattice.covolume (ambientIntegralRowModule (K := K) m)
            (μHE[Module.finrank ℝ (RowVector K m)]))⁻¹) *
          (T + R) ^ (m * degree K - l * degree K) *
            rowSpaceHeight (echelonRowSpace D')) ^ (k - l) :=
      pow_le_pow_left₀ hbase hball' _

/- [derived consequence, paper `le:low_rank_induction`, lines 1431--1480]
   Normalize the covering-radius extension estimate to the exact scale in
   the lemma statement. -/
set_option maxHeartbeats 800000 in
theorem echelonExtensionCount_le_of_projected_covering_geometry
    {K : Type*} [Field K] [NumberField K]
    {m k l : ℕ} (B : Set (EchelonMatrix K k m)) [Fintype B]
    (D' : EchelonMatrix K l m) {T R : ℝ} (hT : 1 ≤ T)
    (μ : Measure ((rowRealSpan (echelonRowSpace D'))ᗮ))
    [Measure.IsAddHaarMeasure μ]
    (hcover : LatticeCovering
      (projectedAmbientRowModule (K := K) (echelonRowSpace D')) R)
    (hcov : ZLattice.covolume
      (projectedAmbientRowModule (K := K) (echelonRowSpace D')) μ =
        (rowSpaceHeight (echelonRowSpace D'))⁻¹)
    (choice : EchelonMatrix K k m → Fin (k - l) →
      {v : projectedAmbientRowModule (K := K) (echelonRowSpace D') |
        ‖(v : (rowRealSpan (echelonRowSpace D'))ᗮ)‖ ≤ T})
    (hchoice : Set.InjOn (fun D => fun i => choice D i)
      (B ∩ {D | echelonLambda D' ≤ echelonLambda D})) :
    ∃ C : ℝ, 0 < C ∧
      echelonExtensionCount B D' ≤
        C * T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight (echelonRowSpace D') ^ (k - l) := by
  have hT₀ : 0 < T := lt_of_lt_of_le zero_lt_one hT
  obtain ⟨C₀, hC₀, hball⟩ :=
    echelonExtensionCount_le_of_projected_covering B D' hT₀ μ
      hcover hcov choice hchoice
  let q : ℕ := m * degree K - l * degree K
  have hlm : l ≤ m := by
    have hdim := Submodule.finrank_le (echelonRowSpace D').1
    rw [echelonRowSpace_rank, Module.finrank_pi_fintype] at hdim
    simpa using hdim
  have hqeq : q = degree K * (m - l) := by
    dsimp [q]
    calc
      m * degree K - l * degree K = (m - l) * degree K :=
        (Nat.sub_mul m l (degree K)).symm
      _ = degree K * (m - l) := Nat.mul_comm _ _
  have hball' :
      echelonExtensionCount B D' ≤
        (C₀ * (T + R) ^ q *
          rowSpaceHeight (echelonRowSpace D')) ^ (k - l) := by
    simpa [q] using hball
  have hR : 0 ≤ R := le_trans
    (latticeCoveringRadius_nonneg
      (projectedAmbientRowModule (K := K) (echelonRowSpace D')))
    (latticeCoveringRadius_le_of_latticeCovering
      (projectedAmbientRowModule (K := K) (echelonRowSpace D')) hcover)
  have hRT : R ≤ R * T := by
    calc
      R = R * 1 := by ring
      _ ≤ R * T := mul_le_mul_of_nonneg_left hT hR
  have hTR : T + R ≤ (1 + R) * T := by
    calc
      T + R = T + R * 1 := by ring
      _ ≤ T + R * T := by
        simpa [add_comm] using add_le_add_left hRT T
      _ = (1 + R) * T := by ring
  have hTR_nonneg : 0 ≤ T + R := by linarith
  have hH : 0 ≤ rowSpaceHeight (echelonRowSpace D') :=
    (rowSpaceHeight_pos (echelonRowSpace D')).le
  have hinner :
      C₀ * (T + R) ^ q * rowSpaceHeight (echelonRowSpace D') ≤
        C₀ * ((1 + R) ^ q * T ^ q) *
          rowSpaceHeight (echelonRowSpace D') := by
    calc
      C₀ * (T + R) ^ q * rowSpaceHeight (echelonRowSpace D') ≤
          C₀ * ((1 + R) * T) ^ q *
            rowSpaceHeight (echelonRowSpace D') := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hTR_nonneg hTR q) hC₀.le) hH
      _ = C₀ * ((1 + R) ^ q * T ^ q) *
            rowSpaceHeight (echelonRowSpace D') := by
        rw [mul_pow]
  have hbase_nonneg :
      0 ≤ C₀ * (T + R) ^ q * rowSpaceHeight (echelonRowSpace D') := by
    exact mul_nonneg (mul_nonneg hC₀.le (pow_nonneg hTR_nonneg _)) hH
  have hpow := pow_le_pow_left₀ hbase_nonneg hinner (k - l)
  let C₁ : ℝ := (C₀ * (1 + R) ^ q) ^ (k - l)
  have hC₁ : 0 < C₁ := by
    dsimp [C₁]
    exact pow_pos (mul_pos hC₀ (pow_pos (by linarith) _)) _
  have hrewrite :
      (C₀ * ((1 + R) ^ q * T ^ q) *
          rowSpaceHeight (echelonRowSpace D')) ^ (k - l) =
        C₁ * T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight (echelonRowSpace D') ^ (k - l) := by
    calc
      (C₀ * ((1 + R) ^ q * T ^ q) *
          rowSpaceHeight (echelonRowSpace D')) ^ (k - l) =
          ((C₀ * (1 + R) ^ q) * T ^ q *
            rowSpaceHeight (echelonRowSpace D')) ^ (k - l) := by
        congr 1
        ring
      _ = (C₀ * (1 + R) ^ q) ^ (k - l) *
          (T ^ q) ^ (k - l) *
            rowSpaceHeight (echelonRowSpace D') ^ (k - l) := by
        rw [mul_pow, mul_pow]
      _ = (C₀ * (1 + R) ^ q) ^ (k - l) *
          T ^ (q * (k - l)) *
            rowSpaceHeight (echelonRowSpace D') ^ (k - l) := by
        rw [← pow_mul]
      _ = C₁ * T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight (echelonRowSpace D') ^ (k - l) := by
        dsimp [C₁]
        rw [hqeq]
        congr 2
        ring
  refine ⟨C₁, hC₁, ?_⟩
  calc
    echelonExtensionCount B D' ≤
        (C₀ * (T + R) ^ q *
          rowSpaceHeight (echelonRowSpace D')) ^ (k - l) := hball'
    _ ≤ (C₀ * ((1 + R) ^ q * T ^ q) *
          rowSpaceHeight (echelonRowSpace D')) ^ (k - l) := hpow
    _ = C₁ * T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight (echelonRowSpace D') ^ (k - l) := hrewrite

/- [derived consequence, paper `le:low_rank_induction`, lines 1431--1480]
   The paper's fixed-radius version: instantiate the projected covering
   bound with the intrinsic radius of the ambient integral row module. -/
set_option maxHeartbeats 800000 in
theorem echelonExtensionCount_le_of_ambient_row_covering
    {K : Type*} [Field K] [NumberField K]
    {m k l : ℕ} (B : Set (EchelonMatrix K k m)) [Fintype B]
    (D' : EchelonMatrix K l m) {T : ℝ} (hT : 1 ≤ T)
    (μ : Measure ((rowRealSpan (echelonRowSpace D'))ᗮ))
    [Measure.IsAddHaarMeasure μ]
    (hcov : ZLattice.covolume
      (projectedAmbientRowModule (K := K) (echelonRowSpace D')) μ =
        (rowSpaceHeight (echelonRowSpace D'))⁻¹)
    (choice : EchelonMatrix K k m → Fin (k - l) →
      {v : projectedAmbientRowModule (K := K) (echelonRowSpace D') |
        ‖(v : (rowRealSpan (echelonRowSpace D'))ᗮ)‖ ≤ T})
    (hchoice : Set.InjOn (fun D => fun i => choice D i)
      (B ∩ {D | echelonLambda D' ≤ echelonLambda D})) :
    ∃ C : ℝ, 0 < C ∧
      echelonExtensionCount B D' ≤
        C * T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight (echelonRowSpace D') ^ (k - l) := by
  exact echelonExtensionCount_le_of_projected_covering_geometry B D' hT μ
    (projectedAmbientRowModule_isLatticeCovering_of_ambientRadius
      (echelonRowSpace D')) hcov choice hchoice

/- [derived consequence, paper `le:low_rank_induction`, lines 1431--1480]
   The raw-metric fixed-radius extension estimate.  This is the direct
   manuscript-shaped `(Csup * T + rho)` stage before the elementary
   normalization of the radius term; the ambient covolume is already absorbed
   in its implicit constant. -/
set_option maxHeartbeats 800000 in
theorem echelonExtensionCount_le_of_raw_ambient_row_covering
    {K : Type*} [Field K] [NumberField K]
    {m k l : ℕ} (B : Set (EchelonMatrix K k m)) [Fintype B]
    (D' : EchelonMatrix K l m) {T : ℝ} (hT : 0 < T)
    (choice : EchelonMatrix K k m → Fin (k - l) →
      {v : projectedAmbientRowModule (K := K) (echelonRowSpace D') |
        ‖(v : (rowRealSpan (echelonRowSpace D'))ᗮ)‖ ≤ T})
    (hchoice : Set.InjOn (fun D => fun i => choice D i)
      (B ∩ {D | echelonLambda D' ≤ echelonLambda D})) :
    ∃ C : ℝ, 0 < C ∧
      echelonExtensionCount B D' ≤
        (C * (T + latticeCoveringRadius
          (ambientIntegralRowModule (K := K) m)) ^
            (m * degree K - l * degree K) *
          rowSpaceHeight (echelonRowSpace D')) ^ (k - l) := by
  exact echelonExtensionCount_le_of_raw_projected_covering B D' hT
    (projectedAmbientRowModule_isLatticeCovering_of_ambientRadius
      (echelonRowSpace D')) choice hchoice

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

/- [derived consequence, paper `le:low_rank_terms`, lines 1558--1568]
   Transfer the row-matrix ball-count estimate to the manuscript's
   integral-matrix notation.  The absolute value of the rank-filtered sum is
   bounded by the sum of absolute values before the proved row-lattice
   reindexing is applied. -/
set_option maxHeartbeats 800000 in
theorem Admissible.rowSpaceRankSum_abs_le_of_radius
    {K : Type*} [Field K] [NumberField K]
    {n m l : ℕ} (W : Grassmannian K m l)
    {f : M n m (K_ℝ[K]) → ℝ} (h_f : Admissible f)
    (hl : 0 < l) (hn : 0 < n) {T C_R : ℝ}
    (hT : 1 ≤ T) (hC_R : 0 ≤ C_R)
    (hRadius : rowMatrixFundamentalRadius W n / T ≤ C_R) :
    ∃ C₂ : ℝ, 0 < C₂ ∧
      |rowSpaceRankSum W f T| ≤
        C₂ * (rowSpaceHeight W)⁻¹ ^ n *
          T ^ (n * (l * degree K)) := by
  obtain ⟨C₂, hC₂, hbound⟩ :=
    h_f.rowMatrix_rank_sum_abs_le_of_radius W hl hn hT hC_R hRadius
  refine ⟨C₂, hC₂, ?_⟩
  have hT₀ : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hs : Summable (fun A : {A : IntegralMatrix K n m //
      rowsInIntegralRowModule W A ∧ integralMatrixRank A = l} =>
      f (T⁻¹ • embedMatrix A.1)) := by
    exact (summable_scaled_integralMatrices f h_f hT₀).comp_injective
      Subtype.val_injective
  have hnorm := norm_tsum_le_tsum_norm hs.norm
  calc
    |rowSpaceRankSum W f T| =
        |∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule W A ∧ integralMatrixRank A = l},
          f (T⁻¹ • embedMatrix A.1)| := by
      rfl
    _ ≤ ∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule W A ∧ integralMatrixRank A = l},
          |f (T⁻¹ • embedMatrix A.1)| := by
      simpa only [Real.norm_eq_abs] using hnorm
    _ = ∑' A : {A : rowMatrixZLattice W n // rowMatrixRank W A = l},
          |f (T⁻¹ • (((A.1 : rowMatrixRealSpan W n) :
            M n m (K_ℝ[K]))))| := by
      exact (tsum_rowMatrixZLattice_rank_eq_integralRowMatrices W
        (fun x => |f x|) T).symm
    _ ≤ C₂ * (rowSpaceHeight W)⁻¹ ^ n *
          T ^ (n * (l * degree K)) := hbound

/- [derived consequence, paper `le:low_rank_terms`, lines 1558--1568]
   Fixed-coefficient row-space form of the inner rank-`l` sum.  The explicit
   support and value bounds are passed through the already-proved
   row-matrix/integral-matrix reindexing; no finite-family choice is made in
   this statement. -/
set_option maxHeartbeats 1000000 in
theorem Admissible.rowSpaceRankSum_abs_le_of_radius_uniform_of_bounds
    {K : Type*} [Field K] [NumberField K]
    {n m l : ℕ} (W : Grassmannian K m l)
    {f : M n m (K_ℝ[K]) → ℝ} (h_f : Admissible f)
    (hl : 0 < l) (hn : 0 < n) {T C_R R C : ℝ}
    (hT : 1 ≤ T) (hC_R : 0 ≤ C_R)
    (hRadius : rowMatrixFundamentalRadius W n / T ≤ C_R)
    (hR : 0 ≤ R)
    (hsupport : ∀ A : rowMatrixZLattice W n,
      |f (T⁻¹ • (((A : rowMatrixRealSpan W n) : M n m (K_ℝ[K]))))| ≠ 0 →
        ‖(A : rowMatrixRealSpan W n)‖ ≤ (R + 1) * T)
    (hC : 0 ≤ C)
    (hbound : ∀ A : rowMatrixZLattice W n,
      |(|f (T⁻¹ • (((A : rowMatrixRealSpan W n) : M n m (K_ℝ[K]))))|)| ≤ C) :
    |rowSpaceRankSum W f T| ≤
      C * euclideanUnitBallVolume (n * (l * degree K)) *
        (R + 1 + C_R) ^ (n * (l * degree K)) *
        (rowSpaceHeight W)⁻¹ ^ n * T ^ (n * (l * degree K)) := by
  have hmatrix :=
    h_f.rowMatrix_rank_sum_abs_le_of_radius_uniform_of_bounds
      W hl hn hT hC_R hRadius hR hsupport hC hbound
  have hT₀ : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hs : Summable (fun A : {A : IntegralMatrix K n m //
      rowsInIntegralRowModule W A ∧ integralMatrixRank A = l} =>
      f (T⁻¹ • embedMatrix A.1)) := by
    exact (summable_scaled_integralMatrices f h_f hT₀).comp_injective
      Subtype.val_injective
  have hnorm := norm_tsum_le_tsum_norm hs.norm
  calc
    |rowSpaceRankSum W f T| =
        |∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule W A ∧ integralMatrixRank A = l},
          f (T⁻¹ • embedMatrix A.1)| := by
      rfl
    _ ≤ ∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule W A ∧ integralMatrixRank A = l},
          |f (T⁻¹ • embedMatrix A.1)| := by
      simpa only [Real.norm_eq_abs] using hnorm
    _ = ∑' A : {A : rowMatrixZLattice W n // rowMatrixRank W A = l},
          |f (T⁻¹ • (((A.1 : rowMatrixRealSpan W n) :
            M n m (K_ℝ[K]))))| := by
      exact (tsum_rowMatrixZLattice_rank_eq_integralRowMatrices W
        (fun x => |f x|) T).symm
    _ ≤ C * euclideanUnitBallVolume (n * (l * degree K)) *
          (R + 1 + C_R) ^ (n * (l * degree K)) *
          (rowSpaceHeight W)⁻¹ ^ n * T ^ (n * (l * degree K)) := hmatrix

/- [derived consequence, paper `le:low_rank_terms`, lines 1558--1568]
   The same row-space inner-sum estimate in the manuscript's intrinsic
   `sqrt n * rho(Λ_D)` notation.  This is a reindexing of the proved
   row-matrix estimate; the support and value constants are unchanged. -/
set_option maxHeartbeats 1000000 in
theorem Admissible.rowSpaceRankSum_abs_le_of_latticeVoronoi_radius_uniform_of_bounds
    {K : Type*} [Field K] [NumberField K]
    {n m l : ℕ} (W : Grassmannian K m l)
    {f : M n m (K_ℝ[K]) → ℝ} (h_f : Admissible f)
    (hl : 0 < l) (hn : 0 < n) {T C_R R C : ℝ}
    (hT : 1 ≤ T) (hC_R : 0 ≤ C_R)
    (hRadius :
      (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice W)) / T ≤ C_R)
    (hR : 0 ≤ R)
    (hsupport : ∀ A : rowMatrixZLattice W n,
      |f (T⁻¹ • (((A : rowMatrixRealSpan W n) : M n m (K_ℝ[K]))))| ≠ 0 →
        ‖(A : rowMatrixRealSpan W n)‖ ≤ (R + 1) * T)
    (hC : 0 ≤ C)
    (hbound : ∀ A : rowMatrixZLattice W n,
      |(|f (T⁻¹ • (((A : rowMatrixRealSpan W n) : M n m (K_ℝ[K]))))|)| ≤ C) :
    |rowSpaceRankSum W f T| ≤
      C * euclideanUnitBallVolume (n * (l * degree K)) *
        (R + 1 + C_R) ^ (n * (l * degree K)) *
        (rowSpaceHeight W)⁻¹ ^ n * T ^ (n * (l * degree K)) := by
  have hmatrix :=
    h_f.rowMatrix_rank_sum_abs_le_of_latticeVoronoi_radius_uniform_of_bounds
      W hl hn hT hC_R hRadius hR hsupport hC hbound
  have hT₀ : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hs : Summable (fun A : {A : IntegralMatrix K n m //
      rowsInIntegralRowModule W A ∧ integralMatrixRank A = l} =>
      f (T⁻¹ • embedMatrix A.1)) := by
    exact (summable_scaled_integralMatrices f h_f hT₀).comp_injective
      Subtype.val_injective
  have hnorm := norm_tsum_le_tsum_norm hs.norm
  calc
    |rowSpaceRankSum W f T| =
        |∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule W A ∧ integralMatrixRank A = l},
          f (T⁻¹ • embedMatrix A.1)| := by
      rfl
    _ ≤ ∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule W A ∧ integralMatrixRank A = l},
          |f (T⁻¹ • embedMatrix A.1)| := by
      simpa only [Real.norm_eq_abs] using hnorm
    _ = ∑' A : {A : rowMatrixZLattice W n // rowMatrixRank W A = l},
          |f (T⁻¹ • (((A.1 : rowMatrixRealSpan W n) :
            M n m (K_ℝ[K]))))| := by
      exact (tsum_rowMatrixZLattice_rank_eq_integralRowMatrices W
        (fun x => |f x|) T).symm
    _ ≤ C * euclideanUnitBallVolume (n * (l * degree K)) *
          (R + 1 + C_R) ^ (n * (l * degree K)) *
          (rowSpaceHeight W)⁻¹ ^ n * T ^ (n * (l * degree K)) := hmatrix

/- [derived consequence, paper `le:low_rank_terms`, lines 1558--1568]
   The ball-count constant for one lower row space can be made uniform over
   the finite family that occurs in the manuscript's height sum.  This is
   only finite-family bookkeeping: it retains the same radius hypothesis and
   the same `H(W)⁻ⁿ T^(lnd)` term from the displayed inner estimate. -/
set_option maxHeartbeats 800000 in
theorem Admissible.exists_uniform_rowSpaceRankSum_abs_le_of_radius
    {K : Type*} [Field K] [NumberField K]
    {n m l : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    (hl : 0 < l) (hn : 0 < n) {T C_R : ℝ}
    (hT : 1 ≤ T) (hC_R : 0 ≤ C_R)
    (S : Set (Grassmannian K m l)) (hS : S.Finite)
    (hRadius : ∀ W ∈ S, rowMatrixFundamentalRadius W n / T ≤ C_R) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ W ∈ S,
      |rowSpaceRankSum W f T| ≤
        C₂ * (rowSpaceHeight W)⁻¹ ^ n *
          T ^ (n * (l * degree K)) := by
  classical
  let F : Finset (Grassmannian K m l) := hS.toFinset
  have hF : (F : Set (Grassmannian K m l)) = S := hS.coe_toFinset
  choose c hc hbound using fun W : F =>
    h_f.rowSpaceRankSum_abs_le_of_radius W.1 hl hn hT hC_R
      (hRadius W.1 (by
        rw [← hF]
        exact W.2))
  let C₂ : ℝ := 1 + ∑ W ∈ F.attach, c W
  have hsum_nonneg : 0 ≤ ∑ W ∈ F.attach, c W := by
    exact Finset.sum_nonneg (fun W _ => (hc W).le)
  have hC₂ : 0 < C₂ := by
    dsimp [C₂]
    linarith
  refine ⟨C₂, hC₂, ?_⟩
  intro W hW
  let wF : F := ⟨W, by
    change W ∈ (F : Set (Grassmannian K m l))
    rw [hF]
    exact hW⟩
  have hc_sum : c wF ≤ ∑ U ∈ F.attach, c U := by
    exact Finset.single_le_sum (fun U _ => (hc U).le)
      (F.mem_attach wF)
  have hc_uniform : c wF ≤ C₂ := by
    dsimp [C₂]
    linarith
  have hfactor :
      0 ≤ (rowSpaceHeight W)⁻¹ ^ n * T ^ (n * (l * degree K)) := by
    exact mul_nonneg
      (pow_nonneg (inv_nonneg.mpr (rowSpaceHeight_pos W).le) n)
      (pow_nonneg (le_trans zero_le_one hT) _)
  have hboundW :
      |rowSpaceRankSum W f T| ≤
        c wF * (rowSpaceHeight W)⁻¹ ^ n *
          T ^ (n * (l * degree K)) := by
    simpa [wF] using hbound wF
  calc
    |rowSpaceRankSum W f T| ≤
        c wF * (rowSpaceHeight W)⁻¹ ^ n *
          T ^ (n * (l * degree K)) := hboundW
    _ = c wF * ((rowSpaceHeight W)⁻¹ ^ n *
          T ^ (n * (l * degree K))) := by ring
    _ ≤ C₂ * ((rowSpaceHeight W)⁻¹ ^ n *
          T ^ (n * (l * degree K))) :=
      mul_le_mul_of_nonneg_right hc_uniform hfactor
    _ = C₂ * (rowSpaceHeight W)⁻¹ ^ n *
          T ^ (n * (l * degree K)) := by ring

/- [derived consequence, paper `le:low_rank_terms`, lines 1558--1568]
   Global uniformization of the inner rank-`l` sum.  Unlike the preceding
   finite-family convenience lemma, `R`, the bound for `f`, and hence `C₂`
   are chosen from admissibility before `T` and the row space range over the
   displayed family. -/
set_option maxHeartbeats 1200000 in
theorem Admissible.exists_uniform_rowSpaceRankSum_abs_le_of_radius_global
    {K : Type*} [Field K] [NumberField K]
    {n m l : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    (hl : 0 < l) (hn : 0 < n) {T C_R : ℝ}
    (hT : 1 ≤ T) (hC_R : 0 ≤ C_R)
    (S : Set (Grassmannian K m l))
    (hRadius : ∀ W ∈ S, rowMatrixFundamentalRadius W n / T ≤ C_R) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ W ∈ S,
      |rowSpaceRankSum W f T| ≤
        C₂ * (rowSpaceHeight W)⁻¹ ^ n *
          T ^ (n * (l * degree K)) := by
  obtain ⟨R, hR, hRsupport⟩ := h_f.exists_support_radius
  obtain ⟨C₀, hC₀, hC₀bound⟩ := h_f.exists_uniform_bound
  let C : ℝ := C₀ + 1
  have hC : 0 < C := by
    dsimp [C]
    linarith
  let C₂ : ℝ := C * euclideanUnitBallVolume (n * (l * degree K)) *
    (R + 1 + C_R) ^ (n * (l * degree K))
  have hbase : 0 < R + 1 + C_R := by linarith
  have hC₂ : 0 < C₂ := by
    dsimp [C₂]
    exact mul_pos (mul_pos hC (euclideanUnitBallVolume_pos _))
      (pow_pos hbase _)
  refine ⟨C₂, hC₂, ?_⟩
  intro W hW
  have hT₀ : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hsupport : ∀ A : rowMatrixZLattice W n,
      |f (T⁻¹ • (((A : rowMatrixRealSpan W n) : M n m (K_ℝ[K]))))| ≠ 0 →
        ‖(A : rowMatrixRealSpan W n)‖ ≤ (R + 1) * T := by
    intro A hA
    have hfnonzero : f (T⁻¹ • (((A : rowMatrixRealSpan W n) :
        M n m (K_ℝ[K])))) ≠ 0 := by
      exact abs_ne_zero.mp hA
    have hball := hRsupport _ hfnonzero
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hT₀] at hball
    calc
      ‖(A : rowMatrixRealSpan W n)‖ =
          T * (T⁻¹ * ‖(A : rowMatrixRealSpan W n)‖) := by
        rw [← mul_assoc, mul_inv_cancel₀ hT₀.ne', one_mul]
      _ ≤ T * R := mul_le_mul_of_nonneg_left hball hT₀.le
      _ ≤ T * (R + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hT₀.le
      _ = (R + 1) * T := by ring
  have hbound : ∀ A : rowMatrixZLattice W n,
      |(|f (T⁻¹ • (((A : rowMatrixRealSpan W n) :
        M n m (K_ℝ[K]))))|)| ≤ C := by
    intro A
    rw [abs_abs]
    exact (hC₀bound _).trans (by
      dsimp [C]
      linarith)
  have hmain := h_f.rowSpaceRankSum_abs_le_of_radius_uniform_of_bounds
    W hl hn hT hC_R (hRadius W hW) hR hsupport hC.le hbound
  calc
    |rowSpaceRankSum W f T| ≤
        C * euclideanUnitBallVolume (n * (l * degree K)) *
          (R + 1 + C_R) ^ (n * (l * degree K)) *
          (rowSpaceHeight W)⁻¹ ^ n * T ^ (n * (l * degree K)) := hmain
    _ = C₂ * (rowSpaceHeight W)⁻¹ ^ n *
          T ^ (n * (l * degree K)) := by
      dsimp [C₂]

/- [derived consequence, paper `le:low_rank_terms`, lines 1558--1568]
   Global uniformization of the intrinsic-radius lower-rank inner sum.  The
   constants are selected before both `T` and `W`, while the radius hypothesis
   is exactly the manuscript's `sqrt n * rho(Λ_D)` condition. -/
set_option maxHeartbeats 1200000 in
theorem Admissible.exists_uniform_rowSpaceRankSum_abs_le_of_latticeVoronoi_radius_global
    {K : Type*} [Field K] [NumberField K]
    {n m l : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    (hl : 0 < l) (hn : 0 < n) {T C_R : ℝ}
    (hT : 1 ≤ T) (hC_R : 0 ≤ C_R)
    (S : Set (Grassmannian K m l))
    (hRadius : ∀ W ∈ S,
      (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice W)) / T ≤ C_R) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ W ∈ S,
      |rowSpaceRankSum W f T| ≤
        C₂ * (rowSpaceHeight W)⁻¹ ^ n *
          T ^ (n * (l * degree K)) := by
  obtain ⟨R, hR, hRsupport⟩ := h_f.exists_support_radius
  obtain ⟨C₀, hC₀, hC₀bound⟩ := h_f.exists_uniform_bound
  let C : ℝ := C₀ + 1
  have hC : 0 < C := by
    dsimp [C]
    linarith
  let C₂ : ℝ := C * euclideanUnitBallVolume (n * (l * degree K)) *
    (R + 1 + C_R) ^ (n * (l * degree K))
  have hbase : 0 < R + 1 + C_R := by linarith
  have hC₂ : 0 < C₂ := by
    dsimp [C₂]
    exact mul_pos (mul_pos hC (euclideanUnitBallVolume_pos _))
      (pow_pos hbase _)
  refine ⟨C₂, hC₂, ?_⟩
  intro W hW
  have hT₀ : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hsupport : ∀ A : rowMatrixZLattice W n,
      |f (T⁻¹ • (((A : rowMatrixRealSpan W n) : M n m (K_ℝ[K]))))| ≠ 0 →
        ‖(A : rowMatrixRealSpan W n)‖ ≤ (R + 1) * T := by
    intro A hA
    have hfnonzero : f (T⁻¹ • (((A : rowMatrixRealSpan W n) :
        M n m (K_ℝ[K])))) ≠ 0 := by
      exact abs_ne_zero.mp hA
    have hball := hRsupport _ hfnonzero
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hT₀] at hball
    calc
      ‖(A : rowMatrixRealSpan W n)‖ =
          T * (T⁻¹ * ‖(A : rowMatrixRealSpan W n)‖) := by
        rw [← mul_assoc, mul_inv_cancel₀ hT₀.ne', one_mul]
      _ ≤ T * R := mul_le_mul_of_nonneg_left hball hT₀.le
      _ ≤ T * (R + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hT₀.le
      _ = (R + 1) * T := by ring
  have hbound : ∀ A : rowMatrixZLattice W n,
      |(|f (T⁻¹ • (((A : rowMatrixRealSpan W n) :
        M n m (K_ℝ[K]))))|)| ≤ C := by
    intro A
    rw [abs_abs]
    exact (hC₀bound _).trans (by
      dsimp [C]
      linarith)
  have hmain :=
    h_f.rowSpaceRankSum_abs_le_of_latticeVoronoi_radius_uniform_of_bounds
      W hl hn hT hC_R (hRadius W hW) hR hsupport hC.le hbound
  calc
    |rowSpaceRankSum W f T| ≤
        C * euclideanUnitBallVolume (n * (l * degree K)) *
          (R + 1 + C_R) ^ (n * (l * degree K)) *
          (rowSpaceHeight W)⁻¹ ^ n * T ^ (n * (l * degree K)) := hmain
    _ = C₂ * (rowSpaceHeight W)⁻¹ ^ n *
          T ^ (n * (l * degree K)) := by
      dsimp [C₂]

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

/- [derived consequence, paper `eq:inequality_semifinal`, lines 1602--1612]
   This elementary identity keeps the manuscript's signed height exponent
   connected to the nonnegative rank difference used by the ordinary-shell
   estimate. -/
theorem lowRankHeightExponent_eq_sub_rank
    {n m k l : ℕ} (hnm : m < n) (hkm : k ≤ m) :
    lowRankHeightExponent n m k l =
      (m : ℤ) - ((n + l - k : ℕ) : ℤ) := by
  have hk : k ≤ n + l := by omega
  dsimp [lowRankHeightExponent]
  rw [Nat.cast_sub hk]
  push_cast
  ring

/- [derived consequence, paper `eq:inequality_semifinal`, lines 1602--1612]
   In the positive branch, the signed exponent is literally the natural
   difference that occurs in the shell bound. -/
theorem lowRankHeightExponent_eq_natCast_sub_of_lt
    {n m k l : ℕ} (hnm : m < n) (hkm : k ≤ m)
    (h : n + l - k < m) :
    lowRankHeightExponent n m k l =
      ((m - (n + l - k) : ℕ) : ℤ) := by
  rw [lowRankHeightExponent_eq_sub_rank hnm hkm, ← Nat.cast_sub h.le]

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

/- [derived consequence, paper `eq:ineqluaty_abel` and
   `eq:inequality_semifinal`, lines 1579--1612] This is the explicit bridge
   from the internally rounded ordinary-shell endpoint back to the paper's
   `B_l(T)`.  The real cutoff remains `C * T^(l*d)`; the extra fixed factors
   from rounding are absorbed into the unspecified constant `Ccrudenew`. -/
theorem exists_B_l_bound_of_nat_shell_cutoff
    {n m k l d : ℕ} {C D T : ℝ} {b : ℕ}
    (hC : 0 ≤ C) (hD : 0 < D) (hT : 1 ≤ T) (hb : 1 ≤ b)
    (hupper : (b : ℝ) < max 1 (C * T ^ (l * d)) + 1)
    (hnm : m < n) (hkm : k ≤ m) (hlk : l < k) :
    ∃ Ccrudenew : ℝ, 0 < Ccrudenew ∧
      (if n + l - k < m then
        D * (b : ℝ) ^ ((m - (n + l - k) : ℕ) : ℝ) ≤
          B_l n m k l d Ccrudenew T
      else if m = n + l - k then
        D * (1 + Real.log (b : ℝ)) ≤ B_l n m k l d Ccrudenew T
      else D ≤ B_l n m k l d Ccrudenew T) := by
  by_cases hpos : n + l - k < m
  · have hexp : 0 < lowRankHeightExponent n m k l :=
      (lowRankHeightExponent_pos_iff hnm hkm hlk).mp hpos
    let Ccrudenew : ℝ :=
      D * (C + 2) ^ (m - (n + l - k))
    have hCtwo : 0 < C + 2 := by linarith
    have hCcrudenew : 0 < Ccrudenew := by
      dsimp [Ccrudenew]
      positivity
    have hround := nat_shell_cutoff_rpow_le_scaled
      (a := l * d) (r := m - (n + l - k)) hC hT hupper
    have hExpCast :
        (l * d : ℤ) * lowRankHeightExponent n m k l =
          (((l * d) * (m - (n + l - k)) : ℕ) : ℤ) := by
      rw [lowRankHeightExponent_eq_natCast_sub_of_lt hnm hkm hpos]
      norm_cast
    have hTexp :
        T ^ ((l * d) * (m - (n + l - k)) : ℕ) =
          T ^ ((l * d : ℤ) * lowRankHeightExponent n m k l) := by
      rw [hExpCast, zpow_natCast]
    have hbound :
        D * (b : ℝ) ^ ((m - (n + l - k) : ℕ) : ℝ) ≤
          Ccrudenew *
            T ^ ((l * d : ℤ) * lowRankHeightExponent n m k l) := by
      calc
        D * (b : ℝ) ^ ((m - (n + l - k) : ℕ) : ℝ) ≤
            D * ((C + 2) ^ (m - (n + l - k) : ℕ) *
              T ^ ((l * d) * (m - (n + l - k)) : ℕ)) :=
          mul_le_mul_of_nonneg_left hround hD.le
        _ = Ccrudenew * T ^ ((l * d) * (m - (n + l - k)) : ℕ) := by
          dsimp [Ccrudenew]
          ring
        _ = Ccrudenew *
            T ^ ((l * d : ℤ) * lowRankHeightExponent n m k l) := by
          rw [hTexp]
    refine ⟨Ccrudenew, hCcrudenew, ?_⟩
    simp only [if_pos hpos]
    rw [B_l, if_pos hexp]
    exact hbound
  · by_cases hzero : m = n + l - k
    · have hexp : lowRankHeightExponent n m k l = 0 :=
        (lowRankHeightExponent_eq_zero_iff hnm hkm hlk).mp hzero
      let L : ℝ := 1 + Real.log (C + 2) + (l * d : ℝ)
      let Ccrudenew : ℝ := D * L
      have hCtwo : 1 ≤ C + 2 := by linarith
      have hlogCtwo : 0 ≤ Real.log (C + 2) := Real.log_nonneg hCtwo
      have hld : 0 ≤ (l * d : ℝ) := by positivity
      have hLone : 1 ≤ L := by
        dsimp [L]
        linarith
      have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hLone
      have hCcrudenew : 0 < Ccrudenew := mul_pos hD hLpos
      have hround : 1 + Real.log (b : ℝ) ≤
          L * (1 + Real.log T) := by
        simpa [L] using
          (one_add_log_nat_shell_cutoff_le_scaled
            (a := l * d) hC hT hb hupper)
      have hbound : D * (1 + Real.log (b : ℝ)) ≤
          Ccrudenew * (1 + Real.log T) := by
        calc
          D * (1 + Real.log (b : ℝ)) ≤
              D * (L * (1 + Real.log T)) :=
            mul_le_mul_of_nonneg_left hround hD.le
          _ = Ccrudenew * (1 + Real.log T) := by
            dsimp [Ccrudenew]
            ring
      have hnotpos : ¬ 0 < lowRankHeightExponent n m k l := by
        rw [hexp]
        exact lt_irrefl _
      refine ⟨Ccrudenew, hCcrudenew, ?_⟩
      simp only [if_neg hpos, if_pos hzero]
      rw [B_l, if_neg hnotpos, if_pos hexp]
      exact hbound
    · have hneg_case : m < n + l - k := by omega
      have hexp : lowRankHeightExponent n m k l < 0 :=
        (lowRankHeightExponent_neg_iff hnm hkm hlk).mp hneg_case
      have hnotpos : ¬ 0 < lowRankHeightExponent n m k l := by omega
      have hnotzero : lowRankHeightExponent n m k l ≠ 0 := by omega
      refine ⟨D, hD, ?_⟩
      simp only [if_neg hpos, if_neg hzero]
      rw [B_l, if_neg hnotpos, if_neg hnotzero]
      simpa using (le_refl D)

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
    tsum_abs_le_finite_height_inv_pow_of_pos hcount
      (fun W => rowSpaceHeight_pos W) hb w S hS hS_bound hzero
      Cscale hCscale hpoint'
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
    (hH : 0 < rowSpaceHeight W) (hkm : k ≤ m) (hlk : l < k)
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
  have hH₀ : 0 < rowSpaceHeight W := hH
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
    exact normalized_rowSpace_product_abs_le W hT (rowSpaceHeight_pos W)
      hkm hlk c g
      (rowSpaceExtensionCount_nonneg B W) (hc W hW) (hg W hW) hC₁ hC₂
  obtain ⟨D, hD, hbound⟩ := single_lower_rank_height_term_le hT
    hnm hkm hl hlk hcount hb S hS hS_bound w hwzero
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
    apply normalized_rowSpace_product_abs_le W hT (rowSpaceHeight_pos W)
      hkm hlk c q (rowSpaceExtensionCount_nonneg B W) (hc W hW) ?_
      hC₁ hC₂
    rw [abs_of_nonneg (hq_nonneg W)]
    exact hq W hW
  obtain ⟨D, hD, hbound⟩ := single_lower_rank_height_term_le hT
    hnm hkm hl hlk hcount hb S hS hS_bound w hwzero
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
    B hT hnm hkm hl hlk hcount hb S hS hS_bound q hqzero
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

/- [paper, `le:without_rank_cond` and equations (19)--(21), lines
   1038--1061 and 1671--1679] This is the same rank-restoration comparison
   with the manuscript's intrinsic covering radius.  The factor `sqrt n`
   comes from the product-row lattice estimate at lines 428--431. -/
theorem Admissible.rowMatrix_rank_latticeVoronoi_estimate_with_lower
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (V : Grassmannian K m k)
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    (hk : 0 < k) (hn : 0 < n) :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧ ∀ T : ℝ, 0 < T →
      (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V)) / T ≤ 1 →
      |(∑' A : {A : rowMatrixZLattice V n // rowMatrixRank V A = k},
          f (T⁻¹ • (((A.1 : rowMatrixRealSpan V n) :
            M n m (K_ℝ[K]))))) /
            T ^ (n * (k * degree K)) -
          (rowMatrixLatticeCovolume V n)⁻¹ *
            rowMatrixSubspaceIntegral V n f| ≤
        Cₐ * (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V)) /
          (rowMatrixLatticeCovolume V n * T) +
        |(∑' A : {A : IntegralMatrix K n m //
            rowsInIntegralRowModule V A ∧ integralMatrixRank A < k},
          f (T⁻¹ • embedMatrix A.1))| /
            T ^ (n * (k * degree K)) := by
  obtain ⟨Cₐ, hCₐ, hestimate⟩ :=
    h_f.rowMatrix_latticeVoronoiRiemann_estimate_rank V hk hn
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
      Cₐ * (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V)) /
          (rowMatrixLatticeCovolume V n * T) := by
    simpa [R, L, q, M] using hmain
  change |R / q - M| ≤
      Cₐ * (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V)) /
          (rowMatrixLatticeCovolume V n * T) + |L| / q
  calc
    |R / q - M| = |(R + L) / q - M - L / q| := by
      congr 1
      field_simp [hq.ne']
      ring
    _ ≤ |(R + L) / q - M| + |L / q| := by
      simpa using (abs_sub_le ((R + L) / q - M) 0 (L / q))
    _ ≤ Cₐ * (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V)) /
          (rowMatrixLatticeCovolume V n * T) + |L| / q := by
      rw [abs_div, abs_of_pos hq]
      exact add_le_add hmain' le_rfl

/- [derived consequence, paper `le:without_rank_cond` and equations
   (19)--(21), lines 1038--1061 and 1671--1679] The local Riemann constants
   supplied for individual row spaces can be made uniform on the finite
   family by summing them and adding one.  This is finite-family bookkeeping;
   it does not assert the paper's later uniform radius or height estimates. -/
set_option maxHeartbeats 800000 in
theorem exists_finite_rowMatrix_rank_lattice_estimate_with_lower
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (B : Set (Grassmannian K m k)) [Fintype B]
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    (hk : 0 < k) (hn : 0 < n) {T : ℝ} (hT : 0 < T)
    (hRadius : ∀ V : B,
      rowMatrixFundamentalRadius V.1 n / T ≤ 1) :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧
      ∀ V : B,
        |(∑' A : {A : rowMatrixZLattice V.1 n //
            rowMatrixRank V.1 A = k},
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
            T ^ (n * (k * degree K)) := by
  classical
  choose c hc hestimate using fun V : B =>
    Admissible.rowMatrix_rank_lattice_estimate_with_lower V.1 f h_f hk hn
  let Cₐ : ℝ := 1 + ∑ V : B, c V
  have hsum_nonneg : 0 ≤ ∑ V : B, c V := by
    exact Finset.sum_nonneg (fun V _ => (hc V).le)
  have hCₐ : 0 < Cₐ := by
    dsimp [Cₐ]
    linarith
  refine ⟨Cₐ, hCₐ, ?_⟩
  intro V
  have hc_sum : c V ≤ ∑ W : B, c W := by
    exact Finset.single_le_sum (fun W _ => (hc W).le)
      (Finset.mem_univ V)
  have hc_uniform : c V ≤ Cₐ := by
    dsimp [Cₐ]
    linarith
  have hfactor : 0 ≤ rowMatrixFundamentalRadius V.1 n /
      (rowMatrixLatticeCovolume V.1 n * T) := by
    exact div_nonneg (rowMatrixFundamentalRadius_nonneg V.1)
      (mul_nonneg (rowMatrixLatticeCovolume_pos V.1).le hT.le)
  have hterm : c V * rowMatrixFundamentalRadius V.1 n /
        (rowMatrixLatticeCovolume V.1 n * T) ≤
      Cₐ * rowMatrixFundamentalRadius V.1 n /
        (rowMatrixLatticeCovolume V.1 n * T) := by
    calc
      c V * rowMatrixFundamentalRadius V.1 n /
          (rowMatrixLatticeCovolume V.1 n * T) =
          c V * (rowMatrixFundamentalRadius V.1 n /
            (rowMatrixLatticeCovolume V.1 n * T)) := by ring
      _ ≤ Cₐ * (rowMatrixFundamentalRadius V.1 n /
            (rowMatrixLatticeCovolume V.1 n * T)) :=
        mul_le_mul_of_nonneg_right hc_uniform hfactor
      _ = Cₐ * rowMatrixFundamentalRadius V.1 n /
          (rowMatrixLatticeCovolume V.1 n * T) := by ring
  calc
    |(∑' A : {A : rowMatrixZLattice V.1 n // rowMatrixRank V.1 A = k},
        f (T⁻¹ • (((A.1 : rowMatrixRealSpan V.1 n) :
          M n m (K_ℝ[K]))))) /
          T ^ (n * (k * degree K)) -
        (rowMatrixLatticeCovolume V.1 n)⁻¹ *
          rowMatrixSubspaceIntegral V.1 n f| ≤
        c V * rowMatrixFundamentalRadius V.1 n /
          (rowMatrixLatticeCovolume V.1 n * T) +
        |(∑' A : {A : IntegralMatrix K n m //
            rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
          f (T⁻¹ • embedMatrix A.1))| /
          T ^ (n * (k * degree K)) :=
      hestimate V T hT (hRadius V)
    _ ≤ Cₐ * rowMatrixFundamentalRadius V.1 n /
          (rowMatrixLatticeCovolume V.1 n * T) +
        |(∑' A : {A : IntegralMatrix K n m //
            rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
          f (T⁻¹ • embedMatrix A.1))| /
          T ^ (n * (k * degree K)) := by
      exact add_le_add hterm le_rfl

/- [paper, `le:without_rank_cond` and equations (19)--(21), lines
   1038--1061 and 1671--1679] Finite-family uniformization of the
   manuscript-facing intrinsic-radius estimate.  The displayed
   `sqrt n * rho(Λ_D)` is retained instead of the auxiliary fundamental
   parallelepiped radius used by the older bookkeeping lemma above. -/
set_option maxHeartbeats 800000 in
theorem exists_finite_rowMatrix_rank_latticeVoronoi_estimate_with_lower
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (B : Set (Grassmannian K m k)) [Fintype B]
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    (hk : 0 < k) (hn : 0 < n) {T : ℝ} (hT : 0 < T)
    (hRadius : ∀ V : B,
      (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1)) / T ≤ 1) :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧
      ∀ V : B,
        |(∑' A : {A : rowMatrixZLattice V.1 n // rowMatrixRank V.1 A = k},
            f (T⁻¹ • (((A.1 : rowMatrixRealSpan V.1 n) :
              M n m (K_ℝ[K]))))) /
            T ^ (n * (k * degree K)) -
          (rowMatrixLatticeCovolume V.1 n)⁻¹ *
            rowMatrixSubspaceIntegral V.1 n f| ≤
          Cₐ * (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1)) /
            (rowMatrixLatticeCovolume V.1 n * T) +
          |(∑' A : {A : IntegralMatrix K n m //
              rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
            f (T⁻¹ • embedMatrix A.1))| /
            T ^ (n * (k * degree K)) := by
  classical
  choose c hc hestimate using fun V : B =>
    Admissible.rowMatrix_rank_latticeVoronoi_estimate_with_lower V.1 f h_f hk hn
  let Cₐ : ℝ := 1 + ∑ V : B, c V
  have hsum_nonneg : 0 ≤ ∑ V : B, c V := by
    exact Finset.sum_nonneg (fun V _ => (hc V).le)
  have hCₐ : 0 < Cₐ := by
    dsimp [Cₐ]
    linarith
  refine ⟨Cₐ, hCₐ, ?_⟩
  intro V
  have hc_sum : c V ≤ ∑ W : B, c W := by
    exact Finset.single_le_sum (fun W _ => (hc W).le)
      (Finset.mem_univ V)
  have hc_uniform : c V ≤ Cₐ := by
    dsimp [Cₐ]
    linarith
  have hrad : 0 ≤ Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1) :=
    mul_nonneg (Real.sqrt_nonneg _) (latticeCoveringRadius_nonneg _)
  have hfactor : 0 ≤
      (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1)) /
        (rowMatrixLatticeCovolume V.1 n * T) := by
    exact div_nonneg hrad
      (mul_nonneg (rowMatrixLatticeCovolume_pos V.1).le hT.le)
  have hterm : c V *
        (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1)) /
          (rowMatrixLatticeCovolume V.1 n * T) ≤
      Cₐ * (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1)) /
          (rowMatrixLatticeCovolume V.1 n * T) := by
    calc
      c V * (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1)) /
          (rowMatrixLatticeCovolume V.1 n * T) =
          c V * ((Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1)) /
            (rowMatrixLatticeCovolume V.1 n * T)) := by ring
      _ ≤ Cₐ * ((Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1)) /
            (rowMatrixLatticeCovolume V.1 n * T)) :=
        mul_le_mul_of_nonneg_right hc_uniform hfactor
      _ = Cₐ * (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1)) /
          (rowMatrixLatticeCovolume V.1 n * T) := by ring
  calc
    |(∑' A : {A : rowMatrixZLattice V.1 n // rowMatrixRank V.1 A = k},
        f (T⁻¹ • (((A.1 : rowMatrixRealSpan V.1 n) :
          M n m (K_ℝ[K]))))) /
          T ^ (n * (k * degree K)) -
        (rowMatrixLatticeCovolume V.1 n)⁻¹ *
          rowMatrixSubspaceIntegral V.1 n f| ≤
        c V * (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1)) /
          (rowMatrixLatticeCovolume V.1 n * T) +
        |(∑' A : {A : IntegralMatrix K n m //
            rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
          f (T⁻¹ • embedMatrix A.1))| /
          T ^ (n * (k * degree K)) :=
      hestimate V T hT (hRadius V)
    _ ≤ Cₐ * (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1)) /
          (rowMatrixLatticeCovolume V.1 n * T) +
        |(∑' A : {A : IntegralMatrix K n m //
            rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
          f (T⁻¹ • embedMatrix A.1))| /
          T ^ (n * (k * degree K)) := by
      exact add_le_add hterm le_rfl

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

/- [Lean infrastructure] Finite triangle-inequality bookkeeping used by both
   radius presentations below.  It has no geometric content and is kept
   separate so that the paper-facing statements retain their displayed
   errors verbatim. -/
theorem finite_sum_abs_sub_le_sum
    {α : Type*} [Fintype α] (r mainTerm e : α → ℝ)
    (hpoint : ∀ x : α, |r x - mainTerm x| ≤ e x) :
    |(∑ x : α, r x) - ∑ x : α, mainTerm x| ≤ ∑ x : α, e x := by
  classical
  have hsum :
      (∑ x : α, r x) - ∑ x : α, mainTerm x =
        ∑ x : α, (r x - mainTerm x) := by
    symm
    exact Finset.sum_sub_distrib _ _
  rw [hsum]
  calc
    |∑ x : α, (r x - mainTerm x)| ≤
        ∑ x : α, |r x - mainTerm x| := by
      simpa only [Real.norm_eq_abs] using
        (norm_sum_le (s := Finset.univ)
          (f := fun x : α => r x - mainTerm x))
    _ ≤ ∑ x : α, e x :=
      Finset.sum_le_sum (fun x hx => hpoint x)

/- [paper, equations (19)--(21), lines 1671--1679] Sum the fixed-row-space
   errors with the manuscript's intrinsic covering radius
   `sqrt n * rho(Λ_D)`.  The lower-rank term remains visible for the
   rank-induction estimate. -/
theorem finite_rowMatrix_rank_latticeVoronoi_error_with_lower
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
        Cₐ * (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1)) /
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
        (Cₐ * (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1)) /
          (rowMatrixLatticeCovolume V.1 n * T) +
        |(∑' A : {A : IntegralMatrix K n m //
            rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
          f (T⁻¹ • embedMatrix A.1))| /
            T ^ (n * (k * degree K))) := by
  let r : B → ℝ := fun V =>
    (∑' A : {A : rowMatrixZLattice V.1 n // rowMatrixRank V.1 A = k},
      f (T⁻¹ • (((A.1 : rowMatrixRealSpan V.1 n) : M n m (K_ℝ[K]))))) /
      T ^ (n * (k * degree K))
  let mainTerm : B → ℝ := fun V =>
    (rowMatrixLatticeCovolume V.1 n)⁻¹ *
      rowMatrixSubspaceIntegral V.1 n f
  let e : B → ℝ := fun V =>
    Cₐ * (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1)) /
        (rowMatrixLatticeCovolume V.1 n * T) +
      |(∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
        f (T⁻¹ • embedMatrix A.1))| /
        T ^ (n * (k * degree K))
  have hpoint' : ∀ V : B, |r V - mainTerm V| ≤ e V := by
    intro V
    simpa [r, mainTerm, e] using hpoint V
  simpa [r, mainTerm, e] using
    (finite_sum_abs_sub_le_sum r mainTerm e hpoint')

/- [paper, equations (19)--(21), lines 1671--1679] Insert the finite
   lower-rank absolute-sum bound into the intrinsic-radius finite-family
   estimate. -/
set_option maxHeartbeats 3000000 in
theorem finite_rowMatrix_rank_latticeVoronoi_error_with_lower_of_sum_abs_bound
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
        Cₐ * (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1)) /
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
        Cₐ * (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1)) /
          (rowMatrixLatticeCovolume V.1 n * T) + E_lower := by
  have hfamily :=
    finite_rowMatrix_rank_latticeVoronoi_error_with_lower B hpoint
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
          (Cₐ * (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1)) /
            (rowMatrixLatticeCovolume V.1 n * T) +
          |(∑' A : {A : IntegralMatrix K n m //
              rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
            f (T⁻¹ • embedMatrix A.1))| /
            T ^ (n * (k * degree K))) := hfamily
    _ = ∑ V : B,
          Cₐ * (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1)) /
            (rowMatrixLatticeCovolume V.1 n * T) +
          (∑ V : B, |∑' A : {A : IntegralMatrix K n m //
              rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
            f (T⁻¹ • embedMatrix A.1)|) /
            T ^ (n * (k * degree K)) := by
      rw [Finset.sum_add_distrib]
      rw [Finset.sum_div]
    _ ≤ ∑ V : B,
          Cₐ * (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1)) /
            (rowMatrixLatticeCovolume V.1 n * T) + E_lower := by
      have h' := add_le_add_right hLower
        (∑ V : B,
          Cₐ * (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1)) /
            (rowMatrixLatticeCovolume V.1 n * T))
      simpa [add_comm] using h'

/- [paper, lines 1687--1694] Bound the sum of the manuscript's intrinsic
   row-space Riemann errors by a stated radius/covolume estimate. -/
theorem finite_rowMatrix_latticeVoronoi_radius_error_sum_le
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (B : Set (Grassmannian K m k)) [Fintype B]
    {T Cₐ C_R : ℝ} (hT : 0 < T) (hCₐ : 0 ≤ Cₐ)
    (hRadius :
      (∑ V : B,
        (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1)) /
          rowMatrixLatticeCovolume V.1 n) ≤ C_R) :
    ∑ V : B,
        Cₐ * (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1)) /
          (rowMatrixLatticeCovolume V.1 n * T) ≤
      Cₐ * C_R / T := by
  have hterm : ∀ V : B,
      Cₐ * (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1)) /
          (rowMatrixLatticeCovolume V.1 n * T) =
        (Cₐ / T) *
          ((Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1)) /
            rowMatrixLatticeCovolume V.1 n) := by
    intro V
    have hCovol : 0 < rowMatrixLatticeCovolume V.1 n :=
      rowMatrixLatticeCovolume_pos V.1
    field_simp [ne_of_gt hT, ne_of_gt hCovol]
  calc
    ∑ V : B,
        Cₐ * (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1)) /
          (rowMatrixLatticeCovolume V.1 n * T) =
        ∑ V : B, (Cₐ / T) *
          ((Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1)) /
            rowMatrixLatticeCovolume V.1 n) := by
      apply Finset.sum_congr rfl
      intro V hV
      exact hterm V
    _ = (Cₐ / T) *
        (∑ V : B,
          (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1)) /
            rowMatrixLatticeCovolume V.1 n) := by
      rw [Finset.mul_sum]
    _ ≤ (Cₐ / T) * C_R := by
      exact mul_le_mul_of_nonneg_left hRadius
        (div_nonneg hCₐ hT.le)
    _ = Cₐ * C_R / T := by
      ring

/- [paper, lines 1671--1694] Combine the finite-family intrinsic-radius
   Riemann estimate, the scalar lower-rank error, and the intrinsic
   radius/covolume sum. -/
theorem finite_rowMatrix_rank_error_with_latticeVoronoi_radius_sum_bound
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
        Cₐ * (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1)) /
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
        (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1)) /
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
  have hfamily :=
    finite_rowMatrix_rank_latticeVoronoi_error_with_lower_of_sum_abs_bound
      B hpoint hLower
  have hradius :=
    finite_rowMatrix_latticeVoronoi_radius_error_sum_le B hT hCₐ hRadius
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
          Cₐ * (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1)) /
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

/- [derived consequence, paper `eq:defi_of_calF`, lines 784--803]
   A fixed support bound gives the inclusion in the manuscript's exact
   echelon family at any rank.  Keeping the bound as an input makes clear
   that one and the same `Csup` can be used for every `𝓕_l(T)` in the
   low-rank decomposition. -/
theorem activeRowSpaces_subset_echelon_calF_image_of_support_bound
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (f : M n m (K_ℝ[K]) → ℝ)
    {Csup T : ℝ} (hT : 0 < T)
    (hbound : ∀ A : IntegralMatrix K n m,
      f (T⁻¹ • embedMatrix A) ≠ 0 →
        ‖embedMatrix A‖ ≤ Csup * T) :
    activeRowSpaces (K := K) (k := k) f T ⊆
      echelonRowSpace (K := K) ''
        calF (K := K) (l := k) (m := m) (n := n) Csup T := by
  intro V hV
  rcases hV with ⟨A, hrows, hArank, hnonzero⟩
  let e := echelonRowSpaceEquiv (K := K) (l := k) (m := m)
  let D : EchelonMatrix K k m := e.symm V
  have hDV : echelonRowSpace D = V := e.apply_symm_apply V
  have hrowsD : A ∈ echelonIntegralRowMatrixModule D n := by
    rw [echelonIntegralRowMatrixModule_eq D]
    rw [hDV]
    exact hrows
  refine ⟨D, ?_, hDV⟩
  rw [← calFDirect_eq_calF]
  refine ⟨⟨A, hrowsD⟩, hArank, ?_⟩
  exact hbound A hnonzero

/- [derived consequence, paper `eq:defi_of_calF`, lines 784--803]
   A rank-`l` inner sum can be nonzero only at an active row space.  This is
   the termwise support observation used when the paper enlarges the active
   family to `𝓕_l(T)`; it does not replace that family by a different index. -/
theorem rowSpaceRankSum_eq_zero_of_not_mem_activeRowSpaces
    {K : Type*} [Field K] [NumberField K]
    {n m l : ℕ} (W : Grassmannian K m l)
    (f : M n m (K_ℝ[K]) → ℝ) (T : ℝ)
    (hW : W ∉ activeRowSpaces (K := K) (k := l) f T) :
    rowSpaceRankSum W f T = 0 := by
  change (∑' A : {A : IntegralMatrix K n m //
    rowsInIntegralRowModule W A ∧ integralMatrixRank A = l},
    f (T⁻¹ • embedMatrix A.1)) = 0
  rw [← tsum_zero]
  apply tsum_congr
  intro A
  by_contra hA
  apply hW
  exact ⟨A.1, A.2.1, A.2.2, hA⟩

/- [derived consequence, paper `eq:defi_of_calF`, lines 784--803 and
   `le:new_bijection`, lines 1051--1061] The exact support-sensitive family
   expressed in echelon notation is carried to `activeRowSpaces`.  This
   separates the paper's norm-bounded family `𝓕_l(T)` from the later support
   observation that only its nonzero summands matter. -/
noncomputable def echelonActiveFamily
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (T : ℝ) :
    Set (EchelonMatrix K k m) :=
  {D | ∃ A : echelonIntegralMatrices (n := n) D,
    integralMatrixRank A.1 = k ∧ f (T⁻¹ • embedMatrix A.1) ≠ 0}

/- [derived consequence, paper `eq:defi_of_calF`, lines 784--803 and
   `le:new_bijection`, lines 1051--1061] Exact equality of the two support
   families, using the proved direct-module/echelon and row-space bridges. -/
theorem echelonActiveFamily_image_eq_activeRowSpaces
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (T : ℝ) :
    echelonRowSpace (K := K) '' echelonActiveFamily f T =
      activeRowSpaces (K := K) (k := k) f T := by
  ext V
  constructor
  · rintro ⟨D, ⟨A, hArank, hnonzero⟩, rfl⟩
    have hAmod : A.1 ∈ integralRowMatrixModule (echelonRowSpace D) n := by
      rw [← echelonIntegralRowMatrixModule_eq D]
      exact A.2
    have hrows : rowsInIntegralRowModule (echelonRowSpace D) A.1 :=
      (mem_integralRowMatrixModule_iff _ _).mp hAmod
    exact ⟨A.1, hrows, hArank, hnonzero⟩
  · rintro ⟨A, hrows, hArank, hnonzero⟩
    let e := echelonRowSpaceEquiv (K := K) (l := k) (m := m)
    let D : EchelonMatrix K k m := e.symm V
    have hDV : echelonRowSpace D = V := e.apply_symm_apply V
    have hrowsD : A ∈ echelonIntegralRowMatrixModule D n := by
      rw [echelonIntegralRowMatrixModule_eq D]
      rw [hDV]
      exact hrows
    refine ⟨D, ⟨⟨A, hrowsD⟩, hArank, hnonzero⟩, hDV⟩

/- [derived consequence, paper `eq:defi_of_calF`, lines 784--803]
   The compact-support choice of `Csup` puts every genuinely contributing
   row space into the manuscript's exact echelon family.  The direct
   `M_n(Λ_D)` form is used here and then converted to `calF` by the proved
   equality `calFDirect_eq_calF`. -/
theorem exists_activeRowSpaces_subset_echelon_calF_image
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (f : M n m (K_ℝ[K]) → ℝ)
    (h_f : Admissible f) :
    ∃ Csup : ℝ, 0 < Csup ∧ ∀ T : ℝ, 0 < T →
      activeRowSpaces (K := K) (k := k) f T ⊆
        echelonRowSpace (K := K) '' calF (K := K) (l := k) (m := m)
          (n := n) Csup T := by
  obtain ⟨Csup, hCsup, hbound⟩ :=
    exists_scaledSupport_integralMatrix_norm_bound f h_f
  refine ⟨Csup, hCsup, ?_⟩
  intro T hT
  exact activeRowSpaces_subset_echelon_calF_image_of_support_bound
    f hT (hbound T hT)

def boundedRowSpaces
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (Csup T : ℝ) : Set (Grassmannian K m k) :=
  {V | ∃ A : IntegralMatrix K n m,
    rowsInIntegralRowModule V A ∧ integralMatrixRank A = k ∧
      ‖embedMatrix A‖ ≤ Csup * T}

/- [paper, proof of `le:lower_bound_not_in_F`, lines 1138--1142]
   The first `k` successive minima are assembled as the rows of an integral
   `n × m` matrix, with zero rows appended.  The rank and row identities are
   proved here because the later support-family argument needs this exact
   witness, rather than only an abstract span statement. -/
set_option maxHeartbeats 1200000 in
theorem exists_integralMatrix_of_successiveMinima
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (V : Grassmannian K m k) (hkn : k ≤ n) :
    ∃ A : IntegralMatrix K n m,
      rowsInIntegralRowModule V A ∧ integralMatrixRank A = k ∧
        (∀ i : Fin k,
          rowVectorOfFun ((embedMatrix A) ⟨i.val, by omega⟩) =
            ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)) ∧
        (∀ i : Fin n, k ≤ i.val →
          rowVectorOfFun ((embedMatrix A) i) = 0) := by
  have hmem (i : Fin k) :
      (((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) :
        RowVector K m) ∈
        embeddedIntegralRowModule V := by
    change (((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) :
      RowVector K m) ∈
      embeddedIntegralRowModule V
    exact (rowSuccessiveMinimum V i).property
  choose v hv hveq using fun i =>
    (mem_embeddedIntegralRowModule_iff V
      (((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) :
        RowVector K m)).1 (hmem i)
  let u : Fin k → V.1 := fun i => integralRowToRowSpace V ⟨v i, hv i⟩
  have hu_embed (i : Fin k) :
      rowSpaceVectorEmbeddingK V (u i) =
        rowRealSpanSubtypeKLinearMap V
          ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) := by
    apply PiLp.ext
    intro j
    have hj := congrArg (fun z : RowVector K m => z j) (hveq i)
    simpa [u, rowSpaceVectorEmbeddingK, rowRealSpanSubtypeKLinearMap] using hj
  have hminLI : LinearIndependent K (fun i : Fin k =>
      rowRealSpanSubtypeKLinearMap V
        ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)) := by
    have hLI := (rowSuccessiveMinimum_linearIndependent V).map'
      (rowRealSpanSubtypeKLinearMap V)
      (LinearMap.ker_eq_bot.mpr (rowRealSpanSubtypeKLinearMap_injective V))
    simpa [Function.comp_def] using hLI
  have huLI : LinearIndependent K u := by
    apply LinearIndependent.of_comp (rowSpaceVectorEmbeddingK V)
    have heq : rowSpaceVectorEmbeddingK V ∘ u = fun i =>
        rowRealSpanSubtypeKLinearMap V
          ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) := by
      funext i
      exact hu_embed i
    rw [heq]
    exact hminLI
  let A : IntegralMatrix K n m := fun i =>
    if hi : i.val < k then v ⟨i.val, hi⟩ else 0
  have hArows : rowsInIntegralRowModule V A := by
    intro i
    by_cases hi : i.val < k
    · change A i ∈ integralRowModule V
      simpa [A, hi] using (hv ⟨i.val, hi⟩)
    · change A i ∈ integralRowModule V
      simpa [A, hi] using (integralRowModule V).zero_mem
  have hu_span_le :
      Submodule.span K (Set.range (fun i : Fin k => (u i : Fin m → K))) ≤ V.1 := by
    rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact (u i).property
  have hu_span_finrank : Module.finrank K
      (Submodule.span K (Set.range (fun i : Fin k => (u i : Fin m → K)))) = k := by
    have huLI' : LinearIndependent K (fun i : Fin k => (u i : Fin m → K)) :=
      huLI.map' V.1.subtype
        (LinearMap.ker_eq_bot.mpr V.1.subtype_injective)
    rw [finrank_span_eq_card huLI']
    simp
  have hu_span :
      Submodule.span K (Set.range (fun i : Fin k => (u i : Fin m → K))) = V.1 := by
    apply Submodule.eq_of_le_of_finrank_eq hu_span_le
    rw [hu_span_finrank, V.2]
  have hu_mem_matrixRowSpace : ∀ i : Fin k,
      (u i : Fin m → K) ∈ matrixRowSpace A := by
    intro i
    have hrow :
        (fun j => ((v i) j : K)) =
          (algebraicMatrix A).row ⟨i.val, by omega⟩ := by
      ext j
      simp [A, algebraicMatrix, i.isLt]
    change (fun j => ((v i) j : K)) ∈ matrixRowSpace A
    rw [hrow]
    exact Submodule.subset_span ⟨⟨i.val, by omega⟩, rfl⟩
  have hspan_le_matrix :
      Submodule.span K (Set.range (fun i : Fin k => (u i : Fin m → K))) ≤
        matrixRowSpace A := by
    rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact hu_mem_matrixRowSpace i
  have hmatrixRowSpace : matrixRowSpace A = V.1 := by
    apply le_antisymm
    · exact (rowsInIntegralRowModule_iff_rowSpace_le V A).1 hArows
    · rw [← hu_span]
      exact hspan_le_matrix
  have hArank : integralMatrixRank A = k := by
    have hfin := congrArg (fun W : Submodule K (Fin m → K) => Module.finrank K W)
      hmatrixRowSpace
    simpa [finrank_matrixRowSpace, V.2] using hfin
  refine ⟨A, hArows, hArank, ?_, ?_⟩
  · intro i
    calc
      rowVectorOfFun ((embedMatrix A) ⟨i.val, by omega⟩) =
          integralVectorEmbedding (K := K) m (v i) := by
            apply PiLp.ext
            intro j
            simp [A, embedMatrix, integralVectorEmbedding, i.isLt]
      _ = (((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V) :
          RowVector K m) := hveq i
  · intro i hi
    apply PiLp.ext
    intro j
    have hnot : ¬ i.val < k := by omega
    simp [A, embedMatrix, hnot]

/- [paper, proof of `le:lower_bound_not_in_F`, lines 1138--1142]
   The matrix assembled from the minima has Frobenius norm at most
   `sqrt(k) * ||l_k||`: the first `k` row norms are bounded by the last
   minimum and the remaining rows vanish. -/
set_option maxHeartbeats 1200000 in
theorem exists_integralMatrix_of_successiveMinima_norm_le
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (V : Grassmannian K m k) (hkn : k ≤ n) (hk : 0 < k) :
    ∃ A : IntegralMatrix K n m,
      rowsInIntegralRowModule V A ∧ integralMatrixRank A = k ∧
        ‖embedMatrix A‖ ≤
          Real.sqrt (k : ℝ) *
            ‖((rowSuccessiveMinimum V ⟨k - 1, by omega⟩ : rowZLattice V) :
              rowRealSpan V)‖ := by
  obtain ⟨A, hArows, hArank, hminrow, hzerorow⟩ :=
    exists_integralMatrix_of_successiveMinima V hkn
  let last : Fin k := ⟨k - 1, by omega⟩
  let q : Fin n → ℝ := fun i =>
    ‖rowVectorOfFun ((embedMatrix A) i)‖ ^ 2
  have hrow : ∀ i : Fin n,
      ‖rowVectorOfFun ((embedMatrix A) i)‖ ≤
        ‖((rowSuccessiveMinimum V last : rowZLattice V) : rowRealSpan V)‖ := by
    intro i
    by_cases hi : i.val < k
    · let j : Fin k := ⟨i.val, hi⟩
      have hij : i = ⟨j.val, by omega⟩ := by
        apply Fin.ext
        rfl
      rw [hij, hminrow j]
      exact rowSuccessiveMinimum_norm_le_of_index_le V j last (by
        dsimp [j, last]
        omega)
    · rw [hzerorow i (by omega)]
      simpa only [norm_zero] using
        (norm_nonneg
          (((rowSuccessiveMinimum V last : rowZLattice V) : rowRealSpan V)))
  let e : Fin k ↪ Fin n :=
    { toFun := fun i => ⟨i.val, lt_of_lt_of_le i.isLt hkn⟩
      inj' := by
        intro i j hij
        apply Fin.ext
        simpa using congrArg Fin.val hij }
  let s : Finset (Fin n) :=
    (Finset.univ : Finset (Fin n)).filter (fun i => i.val < k)
  have hs : s = (Finset.univ : Finset (Fin k)).map e := by
    ext i
    constructor
    · intro hi
      have hi' : i.val < k := (Finset.mem_filter.mp hi).2
      let j : Fin k := ⟨i.val, hi'⟩
      apply Finset.mem_map.mpr
      exact ⟨j, Finset.mem_univ _, by
        apply Fin.ext
        rfl⟩
    · intro hi
      rcases Finset.mem_map.mp hi with ⟨j, hj, hji⟩
      have hlt : (e j).val < k := by
        dsimp [e]
        exact j.isLt
      rw [← hji]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
  have hout :
      (∑ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => ¬ (i.val < k)), q i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi' : ¬ i.val < k := (Finset.mem_filter.mp hi).2
    dsimp [q]
    rw [hzerorow i (by omega)]
    simp
  have hsum : (∑ i : Fin n, q i) ≤
      (k : ℝ) *
        ‖((rowSuccessiveMinimum V last : rowZLattice V) : rowRealSpan V)‖ ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (Finset.univ : Finset (Fin n)) (fun i => i.val < k) q]
    rw [hout, add_zero]
    calc
      (∑ i ∈ s, q i) ≤
          ∑ i ∈ s,
            ‖((rowSuccessiveMinimum V last : rowZLattice V) : rowRealSpan V)‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact pow_le_pow_left₀ (norm_nonneg _) (hrow i) 2
      _ = (s.card : ℝ) *
          ‖((rowSuccessiveMinimum V last : rowZLattice V) : rowRealSpan V)‖ ^ 2 := by
        rw [Finset.sum_const]
        simp only [nsmul_eq_mul]
      _ = (k : ℝ) *
          ‖((rowSuccessiveMinimum V last : rowZLattice V) : rowRealSpan V)‖ ^ 2 := by
        rw [hs, Finset.card_map, Finset.card_univ]
        simp only [Fintype.card_fin]
  have hnorm_formula :
      ‖embedMatrix A‖ = √(∑ i : Fin n, q i) := by
    rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [q]
    rw [PiLp.norm_sq_eq_of_L2]
    simp [rowVectorOfFun]
  refine ⟨A, hArows, hArank, ?_⟩
  rw [hnorm_formula]
  calc
    √(∑ i : Fin n, q i) ≤
        √((k : ℝ) *
          ‖((rowSuccessiveMinimum V last : rowZLattice V) : rowRealSpan V)‖ ^ 2) :=
      Real.sqrt_le_sqrt hsum
    _ = √(k : ℝ) *
        ‖((rowSuccessiveMinimum V last : rowZLattice V) : rowRealSpan V)‖ := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs, abs_of_nonneg]
      exact norm_nonneg _

/- [paper, proof of `le:lower_bound_not_in_F`, lines 1134--1142]
   This is the manuscript-facing support implication.  The displayed cutoff
   uses the paper's `k^(-1/2) C^{sup} T`; the preceding witness theorem proves
   the matrix estimate needed to turn a small last minimum into membership in
   `𝓕_k(T)`. -/
set_option maxHeartbeats 1200000 in
theorem echelon_mem_calF_of_last_successiveMinimum_norm_le
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (D : EchelonMatrix K k m) (hkn : k ≤ n) (hk : 0 < k)
    {Csup T : ℝ} (hCsup : 0 < Csup) (hT : 0 < T)
    (hlast :
      ‖((rowSuccessiveMinimum (echelonRowSpace D) ⟨k - 1, by omega⟩ :
          rowZLattice (echelonRowSpace D)) :
          rowRealSpan (echelonRowSpace D))‖ ≤
        (k : ℝ) ^ (-1 / 2 : ℝ) * Csup * T) :
    D ∈ calF (K := K) (l := k) (m := m) (n := n) Csup T := by
  let V : Grassmannian K m k := echelonRowSpace D
  obtain ⟨A, hArows, hArank, hnorm⟩ :=
    exists_integralMatrix_of_successiveMinima_norm_le V hkn hk
  have hnorm' : ‖embedMatrix A‖ ≤ Csup * T := by
    have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
    have hsqrt : 0 < √(k : ℝ) := Real.sqrt_pos.2 hkreal
    have hrpow : (k : ℝ) ^ (-1 / 2 : ℝ) = (√(k : ℝ))⁻¹ := by
      rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
        Real.rpow_neg hkreal.le, ← Real.sqrt_eq_rpow]
    calc
      ‖embedMatrix A‖ ≤ √(k : ℝ) *
          ‖((rowSuccessiveMinimum V ⟨k - 1, by omega⟩ : rowZLattice V) :
            rowRealSpan V)‖ := hnorm
      _ ≤ √(k : ℝ) * ((k : ℝ) ^ (-1 / 2 : ℝ) * Csup * T) := by
        exact mul_le_mul_of_nonneg_left hlast (Real.sqrt_nonneg _)
      _ = Csup * T := by
        rw [hrpow]
        field_simp
  rw [← calFDirect_eq_calF]
  exact ⟨⟨A, hArows⟩, hArank, hnorm'⟩

/- [paper, proof of `le:lower_bound_not_in_F`, lines 1142--1143]
   The paper's uniform constant `c^{minnorm}` is obtained by viewing every
   integral row in the fixed ambient lattice `𝓞_K^m`.  This theorem makes that
   fixed-lattice comparison explicit and proves positivity from discreteness. -/
set_option maxHeartbeats 1200000 in
theorem exists_uniform_integral_row_minimum_lower_bound
    {K : Type*} [Field K] [NumberField K]
    {m k : ℕ} (V : Grassmannian K m k) (hkm : k ≤ m) (hk : 0 < k) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i : Fin k,
      δ ≤ ‖((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖ := by
  have hm : 0 < m := lt_of_lt_of_le hk hkm
  let Vfull : Grassmannian K m m :=
    ⟨⊤, by simp⟩
  letI : MeasurableSpace (RowVector K m) := borel (RowVector K m)
  letI : BorelSpace (RowVector K m) := ⟨rfl⟩
  letI : MeasurableSpace (rowRealSpan Vfull) :=
    @Subtype.instMeasurableSpace (RowVector K m)
      (fun x => x ∈ rowRealSpan Vfull) (borel (RowVector K m))
  letI : BorelSpace (rowRealSpan Vfull) :=
    @Subtype.borelSpace (RowVector K m) _ (borel (RowVector K m))
      ⟨rfl⟩ (fun x => x ∈ rowRealSpan Vfull)
  letI : Nontrivial (rowRealSpan Vfull) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    rw [rowRealSpan_finrank]
    exact Nat.mul_pos hm Module.finrank_pos
  obtain ⟨v₀, hv₀, hvmin⟩ :=
    exists_shortest_nonzero_latticeVector (rowZLattice Vfull)
  have hv₀' : (v₀ : rowRealSpan Vfull) ≠ 0 := by
    intro h
    apply hv₀
    exact Subtype.ext h
  refine ⟨‖(v₀ : rowRealSpan Vfull)‖, norm_pos_iff.mpr hv₀', ?_⟩
  intro i
  let x : rowRealSpan V :=
    ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)
  have hxint : (x : RowVector K m) ∈ embeddedIntegralRowModule V := by
    change ((rowSuccessiveMinimum V i : rowZLattice V) : RowVector K m) ∈
      embeddedIntegralRowModule V
    exact (rowSuccessiveMinimum V i).property
  obtain ⟨a, haV, hax⟩ :=
    (mem_embeddedIntegralRowModule_iff V (x : RowVector K m)).1 hxint
  have haFull : a ∈ integralRowModule Vfull := by
    change (fun j => (a j : K)) ∈ Vfull.1
    change (fun j => (a j : K)) ∈ (⊤ : Submodule K (Fin m → K))
    simp
  have hxFullInt : (x : RowVector K m) ∈ embeddedIntegralRowModule Vfull := by
    exact (mem_embeddedIntegralRowModule_iff Vfull _).2 ⟨a, haFull, hax⟩
  have hxFullSpan : (x : RowVector K m) ∈ rowRealSpan Vfull := by
    apply Submodule.subset_span
    exact hxFullInt
  let y : rowZLattice Vfull :=
    ⟨⟨x, hxFullSpan⟩, by
      change (x : RowVector K m) ∈ embeddedIntegralRowModule Vfull
      exact hxFullInt⟩
  have hyne : y ≠ 0 := by
    intro hy
    have hy' : (y : rowRealSpan Vfull) = 0 := congrArg Subtype.val hy
    have hxzero : (x : RowVector K m) = 0 := by
      exact congrArg (fun z : rowRealSpan Vfull => (z : RowVector K m)) hy'
    apply rowSuccessiveMinimum_ne_zero V i
    apply Subtype.ext
    exact hxzero
  change ‖(v₀ : rowRealSpan Vfull)‖ ≤ ‖(x : rowRealSpan V)‖
  calc
    ‖(v₀ : rowRealSpan Vfull)‖ ≤ ‖(y : rowRealSpan Vfull)‖ := hvmin y hyne
    _ = ‖(x : rowRealSpan V)‖ := by rfl

/- [derived consequence of paper `le:lower_bound_not_in_F`, lines
   1142--1143] The preceding theorem is pointwise in `V`; this strengthened
   form exposes the uniformity actually used by the manuscript.  The same
   shortest nonzero vector in the fixed ambient lattice `𝓞_K^m` is compared
   with every positive-rank row lattice in that ambient space. -/
set_option maxHeartbeats 1200000 in
theorem exists_uniform_integral_row_minimum_lower_bound_all
    {K : Type*} [Field K] [NumberField K]
    {m : ℕ} (hm : 0 < m) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {k : ℕ} (V : Grassmannian K m k), k ≤ m → 0 < k →
        ∀ i : Fin k,
          δ ≤ ‖((rowSuccessiveMinimum V i : rowZLattice V) :
            rowRealSpan V)‖ := by
  let Vfull : Grassmannian K m m :=
    ⟨⊤, by simp⟩
  letI : MeasurableSpace (RowVector K m) := borel (RowVector K m)
  letI : BorelSpace (RowVector K m) := ⟨rfl⟩
  letI : MeasurableSpace (rowRealSpan Vfull) :=
    @Subtype.instMeasurableSpace (RowVector K m)
      (fun x => x ∈ rowRealSpan Vfull) (borel (RowVector K m))
  letI : BorelSpace (rowRealSpan Vfull) :=
    @Subtype.borelSpace (RowVector K m) _ (borel (RowVector K m))
      ⟨rfl⟩ (fun x => x ∈ rowRealSpan Vfull)
  letI : Nontrivial (rowRealSpan Vfull) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    rw [rowRealSpan_finrank]
    exact Nat.mul_pos hm Module.finrank_pos
  obtain ⟨v₀, hv₀, hvmin⟩ :=
    exists_shortest_nonzero_latticeVector (rowZLattice Vfull)
  have hv₀' : (v₀ : rowRealSpan Vfull) ≠ 0 := by
    intro h
    apply hv₀
    exact Subtype.ext h
  refine ⟨‖(v₀ : rowRealSpan Vfull)‖, norm_pos_iff.mpr hv₀', ?_⟩
  intro k V hkm hk i
  let x : rowRealSpan V :=
    ((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)
  have hxint : (x : RowVector K m) ∈ embeddedIntegralRowModule V := by
    change ((rowSuccessiveMinimum V i : rowZLattice V) : RowVector K m) ∈
      embeddedIntegralRowModule V
    exact (rowSuccessiveMinimum V i).property
  obtain ⟨a, haV, hax⟩ :=
    (mem_embeddedIntegralRowModule_iff V (x : RowVector K m)).1 hxint
  have haFull : a ∈ integralRowModule Vfull := by
    change (fun j => (a j : K)) ∈ Vfull.1
    change (fun j => (a j : K)) ∈ (⊤ : Submodule K (Fin m → K))
    simp
  have hxFullInt : (x : RowVector K m) ∈ embeddedIntegralRowModule Vfull := by
    exact (mem_embeddedIntegralRowModule_iff Vfull _).2 ⟨a, haFull, hax⟩
  have hxFullSpan : (x : RowVector K m) ∈ rowRealSpan Vfull := by
    apply Submodule.subset_span
    exact hxFullInt
  let y : rowZLattice Vfull :=
    ⟨⟨x, hxFullSpan⟩, by
      change (x : RowVector K m) ∈ embeddedIntegralRowModule Vfull
      exact hxFullInt⟩
  have hyne : y ≠ 0 := by
    intro hy
    have hy' : (y : rowRealSpan Vfull) = 0 := congrArg Subtype.val hy
    have hxzero : (x : RowVector K m) = 0 := by
      exact congrArg (fun z : rowRealSpan Vfull => (z : RowVector K m)) hy'
    apply rowSuccessiveMinimum_ne_zero V i
    apply Subtype.ext
    exact hxzero
  change ‖(v₀ : rowRealSpan Vfull)‖ ≤ ‖(x : rowRealSpan V)‖
  calc
    ‖(v₀ : rowRealSpan Vfull)‖ ≤ ‖(y : rowRealSpan Vfull)‖ := hvmin y hyne
    _ = ‖(x : rowRealSpan V)‖ := by rfl

/- [derived consequence of paper `le:lower_bound_not_in_F`, lines
   1130--1154] Combining the manuscript's support exclusion with the
   fixed-lattice lower bound and the product estimate gives the lower-height
   bound used for the tail.  The product estimate remains an explicit input:
   it is the cited geometry-of-numbers ingredient, not an unproved local
   theorem or an axiom. -/
set_option maxHeartbeats 1200000 in
theorem exists_echelon_height_lower_bound_of_not_mem_calF
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (D : EchelonMatrix K k m)
    (hkn : k ≤ n) (hkm : k ≤ m) (hk : 0 < k)
    {Csup T Cprod : ℝ}
    (hCsup : 0 < Csup) (hT : 0 < T) (hCprod : 0 < Cprod)
    (hprod : (∏ i : Fin k,
        ‖((rowSuccessiveMinimum (echelonRowSpace D) i :
            rowZLattice (echelonRowSpace D)) :
            rowRealSpan (echelonRowSpace D))‖ ^ degree K) ≤
      Cprod * rowSpaceHeight (echelonRowSpace D))
    (hD : D ∉ calF (K := K) (l := k) (m := m) (n := n) Csup T) :
    ∃ Clower : ℝ, 0 < Clower ∧
      Clower * T ^ degree K ≤ rowSpaceHeight (echelonRowSpace D) := by
  let V : Grassmannian K m k := echelonRowSpace D
  obtain ⟨δ, hδ, hmin⟩ :=
    exists_uniform_integral_row_minimum_lower_bound V hkm hk
  let Ccut : ℝ := (k : ℝ) ^ (-1 / 2 : ℝ) * Csup
  have hCcut : 0 < Ccut := by
    dsimp [Ccut]
    positivity
  have hlast_not : ¬
      ‖((rowSuccessiveMinimum V ⟨k - 1, by omega⟩ : rowZLattice V) :
          rowRealSpan V)‖ ≤ Ccut * T := by
    intro hle
    apply hD
    apply echelon_mem_calF_of_last_successiveMinimum_norm_le
      D hkn hk hCsup hT
    change ‖((rowSuccessiveMinimum (echelonRowSpace D) ⟨k - 1, by omega⟩ :
        rowZLattice (echelonRowSpace D)) :
        rowRealSpan (echelonRowSpace D))‖ ≤
      (k : ℝ) ^ (-1 / 2 : ℝ) * Csup * T at hle
    exact hle
  have hlast_strict : Ccut * T <
      ‖((rowSuccessiveMinimum V ⟨k - 1, by omega⟩ : rowZLattice V) :
          rowRealSpan V)‖ :=
    lt_of_not_ge hlast_not
  have hlast : Ccut * T ≤
      ‖((rowSuccessiveMinimum V ⟨k - 1, by omega⟩ : rowZLattice V) :
          rowRealSpan V)‖ := hlast_strict.le
  have hd : 0 < degree K := Module.finrank_pos
  change (∏ i : Fin k,
      ‖((rowSuccessiveMinimum (echelonRowSpace D) i :
          rowZLattice (echelonRowSpace D)) :
          rowRealSpan (echelonRowSpace D))‖ ^ degree K) ≤
    Cprod * rowSpaceHeight (echelonRowSpace D) at hprod
  have hbound := rowSpaceHeight_lower_bound_of_minima
    (V := V) (d := degree K) hd hk hδ hCcut hCprod hT hmin hlast hprod
  let Clower : ℝ := ((δ ^ (k - 1) * Ccut) ^ degree K) / Cprod
  have hClower : 0 < Clower := by
    dsimp [Clower]
    positivity
  refine ⟨Clower, hClower, ?_⟩
  change (((δ ^ (k - 1) * Ccut) ^ degree K) / Cprod) * T ^ degree K ≤
    rowSpaceHeight V
  exact hbound

/- [derived consequence of paper `le:lower_bound_not_in_F`, lines
   1130--1154] Uniform version of the lower-height estimate.  This is the
   interface needed to turn the complement of the manuscript's finite
   support family into one height tail.  The product estimate is deliberately
   quantified over all echelon matrices as an explicit cited input. -/
set_option maxHeartbeats 1200000 in
theorem exists_uniform_echelon_height_lower_bound_of_not_mem_calF
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (hkn : k ≤ n) (hkm : k ≤ m) (hk : 0 < k)
    {Csup T Cprod : ℝ}
    (hCsup : 0 < Csup) (hT : 0 < T) (hCprod : 0 < Cprod)
    (hprod : ∀ D : EchelonMatrix K k m,
      (∏ i : Fin k,
        ‖((rowSuccessiveMinimum (echelonRowSpace D) i :
            rowZLattice (echelonRowSpace D)) :
            rowRealSpan (echelonRowSpace D))‖ ^ degree K) ≤
    Cprod * rowSpaceHeight (echelonRowSpace D)) :
    ∃ Clower : ℝ, 0 < Clower ∧
      ∀ D : EchelonMatrix K k m,
        D ∉ calF (K := K) (l := k) (m := m) (n := n) Csup T →
        Clower * T ^ degree K ≤ rowSpaceHeight (echelonRowSpace D) := by
  have hm : 0 < m := lt_of_lt_of_le hk hkm
  obtain ⟨δ, hδ, hmin⟩ :=
    exists_uniform_integral_row_minimum_lower_bound_all (K := K) (m := m) hm
  let Ccut : ℝ := (k : ℝ) ^ (-1 / 2 : ℝ) * Csup
  have hCcut : 0 < Ccut := by
    dsimp [Ccut]
    positivity
  let Clower : ℝ := ((δ ^ (k - 1) * Ccut) ^ degree K) / Cprod
  have hClower : 0 < Clower := by
    dsimp [Clower]
    positivity
  refine ⟨Clower, hClower, ?_⟩
  intro D hD
  let V : Grassmannian K m k := echelonRowSpace D
  have hminV : ∀ i : Fin k,
      δ ≤ ‖((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖ :=
    hmin V hkm hk
  have hlast_not : ¬
      ‖((rowSuccessiveMinimum V ⟨k - 1, by omega⟩ : rowZLattice V) :
          rowRealSpan V)‖ ≤ Ccut * T := by
    intro hle
    apply hD
    apply echelon_mem_calF_of_last_successiveMinimum_norm_le
      D hkn hk hCsup hT
    change ‖((rowSuccessiveMinimum (echelonRowSpace D) ⟨k - 1, by omega⟩ :
        rowZLattice (echelonRowSpace D)) :
        rowRealSpan (echelonRowSpace D))‖ ≤
      (k : ℝ) ^ (-1 / 2 : ℝ) * Csup * T at hle
    exact hle
  have hlast_strict : Ccut * T <
      ‖((rowSuccessiveMinimum V ⟨k - 1, by omega⟩ : rowZLattice V) :
          rowRealSpan V)‖ := lt_of_not_ge hlast_not
  have hlast : Ccut * T ≤
      ‖((rowSuccessiveMinimum V ⟨k - 1, by omega⟩ : rowZLattice V) :
          rowRealSpan V)‖ := hlast_strict.le
  have hd : 0 < degree K := Module.finrank_pos
  have hprodD := hprod D
  change (∏ i : Fin k,
      ‖((rowSuccessiveMinimum (echelonRowSpace D) i :
          rowZLattice (echelonRowSpace D)) :
          rowRealSpan (echelonRowSpace D))‖ ^ degree K) ≤
    Cprod * rowSpaceHeight (echelonRowSpace D) at hprodD
  have hbound := rowSpaceHeight_lower_bound_of_minima
    (V := V) (d := degree K) hd hk hδ hCcut hCprod hT hminV hlast hprodD
  change (((δ ^ (k - 1) * Ccut) ^ degree K) / Cprod) * T ^ degree K ≤
    rowSpaceHeight V
  exact hbound

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

/- [derived consequence of paper `eq:defi_of_calF`, lines 784--803] The
echelon presentation of `𝓕_l(T)` and the row-space presentation used by the
finite Riemann sum are exactly the same family.  This is an equality, not a
support enlargement: the reverse inclusion chooses the proved unique echelon
representative and transports its integral-matrix witness through the direct
`M_n(Λ_D)` definition. -/
theorem echelon_calF_image_eq_boundedRowSpaces
    {K : Type*} [Field K] [NumberField K]
    {l m n : ℕ} {Csup T : ℝ} :
    echelonRowSpace (K := K) (l := l) (m := m) ''
        calF (K := K) (l := l) (m := m) (n := n) Csup T =
      boundedRowSpaces (K := K) (n := n) (m := m) (k := l) Csup T := by
  ext V
  constructor
  · intro hV
    exact echelon_calF_subset_boundedRowSpaces
      (K := K) (l := l) (m := m) (n := n) (Csup := Csup) (T := T) hV
  · rintro ⟨A, hArows, hArank, hAnorm⟩
    let e := echelonRowSpaceEquiv (K := K) (l := l) (m := m)
    let D : EchelonMatrix K l m := e.symm V
    have hDV : echelonRowSpace D = V := e.apply_symm_apply V
    refine ⟨D, ?_, hDV⟩
    rw [← calFDirect_eq_calF]
    have hArowsD : A ∈ echelonIntegralRowMatrixModule D n := by
      rw [echelonIntegralRowMatrixModule_eq D, hDV]
      exact hArows
    exact ⟨⟨A, hArowsD⟩, hArank, hAnorm⟩

/- [paper, `co:covering_bound`, lines 1239--1248] For an echelon matrix in
   the manuscript's exact family `𝓕_k(T)`, the rank-`k` witness in
   `M_n(Λ_D)` supplies `k` independent bounded rows.  Applying the selected
   successive-minimum construction and Part 2 of `le:props_of_minima` gives
   the displayed covering-radius bound.  The explicit fixed coefficient
   below realizes the paper's `C^{covering} C^{minima}` without changing the
   family or its norm. -/
theorem echelon_calF_coveringRadius_le
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (D : EchelonMatrix K k m) (hk : 0 < k)
    {Csup T : ℝ}
    (hD : D ∈ calF (K := K) (l := k) (m := m) (n := n) Csup T) :
    latticeCoveringRadius (rowZLattice (echelonRowSpace D)) ≤
      (Fintype.card (Σ _ : Fin k, IntegralBasisIndex K) : ℝ) *
          rowScalarActionBoundSum (K := K) (m := m) * (Csup * T) := by
  rcases hD with ⟨A, hArank, hAnorm⟩
  let V : Grassmannian K m k := echelonRowSpace D
  obtain ⟨e, he⟩ :=
    exists_linearIndependent_rows_of_rowMatrixRank_eq V A hArank
  have hrow : ∀ i : Fin k,
      ‖((rowMatrixZLatticeEquiv V A (e i) : rowZLattice V) : rowRealSpan V)‖ ≤
        Csup * T := by
    intro i
    rw [rowMatrixZLatticeEquiv_norm_coe]
    calc
      ‖rowVectorOfFun
          (((A : rowMatrixRealSpan V n) : M n m (K_ℝ[K])) (e i))‖ ≤
          ‖((A : rowMatrixRealSpan V n) : M n m (K_ℝ[K]))‖ :=
        norm_rowVectorOfFun_le_frobenius _ _
      _ ≤ Csup * T := hAnorm
  have hlast :
      ‖((rowSuccessiveMinimum V ⟨k - 1, by omega⟩ : rowZLattice V) :
          rowRealSpan V)‖ ≤ Csup * T :=
    rowSuccessiveMinimum_last_norm_le_of_independent_bounded V hk ⟨
      fun i => rowMatrixZLatticeEquiv V A (e i), he, hrow⟩
  have hconst : 0 ≤
      (Fintype.card (Σ _ : Fin k, IntegralBasisIndex K) : ℝ) *
        rowScalarActionBoundSum (K := K) (m := m) := by
    exact mul_nonneg (Nat.cast_nonneg _)
      (rowScalarActionBoundSum_nonneg (K := K) (m := m))
  calc
    latticeCoveringRadius (rowZLattice (echelonRowSpace D)) =
        latticeCoveringRadius (rowZLattice V) := by rfl
    _ ≤ (Fintype.card (Σ _ : Fin k, IntegralBasisIndex K) : ℝ) *
          rowScalarActionBoundSum (K := K) (m := m) *
        ‖((rowSuccessiveMinimum V ⟨k - 1, by omega⟩ : rowZLattice V) :
          rowRealSpan V)‖ :=
      rowCoveringRadius_le_of_successiveMinima V hk
    _ ≤ (Fintype.card (Σ _ : Fin k, IntegralBasisIndex K) : ℝ) *
          rowScalarActionBoundSum (K := K) (m := m) * (Csup * T) :=
      mul_le_mul_of_nonneg_left hlast hconst

/- [derived consequence of paper `co:covering_bound`, lines 1239--1248, and
   `le:without_rank_cond`, lines 1028--1045] Dividing the exact covering
   bound for `𝓕_k(T)` by `T` gives the fixed manuscript-scale quantity used
   in the Riemann estimate.  The right-hand side is deliberately left as an
   arbitrary fixed threshold rather than specialized to `1`: this is the
   constant denoted `C^{arbit1}` when `co:covering_bound` is applied after
   `le:Riemann_estimate`. -/
theorem echelon_calF_matrixCoveringRadius_div_le
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (D : EchelonMatrix K k m) (hk : 0 < k)
    {Csup T : ℝ} (hT : 0 < T)
    (hD : D ∈ calF (K := K) (l := k) (m := m) (n := n) Csup T) :
    (Real.sqrt (n : ℝ) *
        latticeCoveringRadius (rowZLattice (echelonRowSpace D))) / T ≤
      Real.sqrt (n : ℝ) *
        (Fintype.card (Σ _ : Fin k, IntegralBasisIndex K) : ℝ) *
          rowScalarActionBoundSum (K := K) (m := m) * Csup := by
  have hcover := echelon_calF_coveringRadius_le D hk hD
  have hsqrt : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hcover hsqrt
  calc
    (Real.sqrt (n : ℝ) *
        latticeCoveringRadius (rowZLattice (echelonRowSpace D))) / T ≤
        (Real.sqrt (n : ℝ) *
          ((Fintype.card (Σ _ : Fin k, IntegralBasisIndex K) : ℝ) *
            rowScalarActionBoundSum (K := K) (m := m) * (Csup * T))) / T := by
      exact div_le_div_of_nonneg_right hmul hT.le
    _ = Real.sqrt (n : ℝ) *
        (Fintype.card (Σ _ : Fin k, IntegralBasisIndex K) : ℝ) *
          rowScalarActionBoundSum (K := K) (m := m) * Csup := by
      field_simp

/- [derived consequence of paper `co:covering_bound`, lines 1239--1248]
   This is the preceding intrinsic covering-radius estimate expressed on the
   manuscript's row-space family `echelonRowSpace '' 𝓕_k(T)`.  It is only the
   exact echelon/row-space reindexing, so the radius remains
   `sqrt n * rho(Λ_W)` rather than an auxiliary choice of basis radius. -/
theorem echelon_calF_image_matrixCoveringRadius_div_le
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (hk : 0 < k)
    {Csup T : ℝ} (hT : 0 < T)
    {W : Grassmannian K m k}
    (hW : W ∈ echelonRowSpace (K := K) ''
      calF (K := K) (l := k) (m := m) (n := n) Csup T) :
    (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice W)) / T ≤
      Real.sqrt (n : ℝ) *
        (Fintype.card (Σ _ : Fin k, IntegralBasisIndex K) : ℝ) *
          rowScalarActionBoundSum (K := K) (m := m) * Csup := by
  rcases hW with ⟨D, hD, rfl⟩
  exact echelon_calF_matrixCoveringRadius_div_le D hk hT hD

/- [Lean infrastructure for paper `eq:defi_of_calF`, lines 784--803]
   Restrict the proved echelon/row-space trijection to the exact finite
   family `𝓕_l(T)`.  The target is the manuscript's row-space family used in
   the Riemann sum, and the membership proof is the preceding equality; this
   introduces no alternate parametrization. -/
noncomputable def calFEquivBoundedRowSpaces
    {K : Type*} [Field K] [NumberField K]
    {l m n : ℕ} {Csup T : ℝ} :
    {D : EchelonMatrix K l m //
      D ∈ calF (K := K) (l := l) (m := m) (n := n) Csup T} ≃
      boundedRowSpaces (K := K) (n := n) (m := m) (k := l) Csup T := by
  let e := echelonRowSpaceEquiv (K := K) (l := l) (m := m)
  refine
    { toFun := fun D => ⟨echelonRowSpace D.1, ?_⟩
      invFun := fun V => ⟨e.symm V.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hDimage : echelonRowSpace D.1 ∈
        echelonRowSpace (K := K) (l := l) (m := m) ''
          calF (K := K) (l := l) (m := m) (n := n) Csup T :=
      ⟨D.1, D.2, rfl⟩
    rw [echelon_calF_image_eq_boundedRowSpaces
      (K := K) (l := l) (m := m) (n := n) (Csup := Csup) (T := T)] at hDimage
    exact hDimage
  · have hVimage : V.1 ∈
        echelonRowSpace (K := K) (l := l) (m := m) ''
          calF (K := K) (l := l) (m := m) (n := n) Csup T := by
      rw [echelon_calF_image_eq_boundedRowSpaces
        (K := K) (l := l) (m := m) (n := n) (Csup := Csup) (T := T)]
      exact V.2
    rcases hVimage with ⟨D, hD, hDV⟩
    have heD : e.symm V.1 = D := by
      apply echelonRowSpace_injective
      change e (e.symm V.1) = echelonRowSpace D
      rw [e.apply_symm_apply]
      exact hDV.symm
    rw [heD]
    exact hD
  · intro D
    apply Subtype.ext
    change e.symm (e D.1) = D.1
    exact e.symm_apply_apply D.1
  · intro V
    apply Subtype.ext
    change e (e.symm V.1) = V.1
    exact e.apply_symm_apply V.1

/- [derived consequence of paper `eq:defi_of_calF` and
   `eq:just_as_before`, lines 784--803 and 1724--1753] Reindex the finite
   radius sum between the manuscript's echelon family `𝓕_k(T)` and its exact
   row-space family.  This is only the proved trijection restricted to the
   displayed family, so the sum retains the paper's normalization. -/
theorem sum_boundedRowSpaces_coveringRadius_div_height_pow_eq_sum_calF
    {K : Type*} [Field K] [NumberField K]
    {m k n : ℕ} {Csup C T : ℝ} (hCproj :
      rowKRealSmulBound (K := K) (m := m) * numberFieldCoefficientRadius K ≤ C)
    (hCsup : Csup ≤ C) (hT : 0 ≤ T) (hk : 0 < k)
    [Fintype (boundedRowSpaces (K := K) (n := n) (m := m) (k := k) Csup T)] :
    (∑ V : boundedRowSpaces (K := K) (n := n) (m := m) (k := k) Csup T,
      latticeCoveringRadius (rowZLattice V.1) /
        (rowSpaceHeight V.1) ^ n) =
      ∑ D ∈ (finite_calF_of_possibleSuccessiveMinima
        (K := K) (m := m) (k := k) (n := n)
        hCproj hCsup hT hk).toFinset,
        latticeCoveringRadius (rowZLattice (echelonRowSpace D)) /
          (rowSpaceHeight (echelonRowSpace D)) ^ n := by
  classical
  let F : Set (EchelonMatrix K k m) :=
    calF (K := K) (l := k) (m := m) (n := n) Csup T
  let hF : F.Finite := by
    simpa [F] using (finite_calF_of_possibleSuccessiveMinima
      (K := K) (m := m) (k := k) (n := n) hCproj hCsup hT hk)
  letI : Fintype {D : EchelonMatrix K k m // D ∈ F} := hF.fintype
  let e := calFEquivBoundedRowSpaces
    (K := K) (l := k) (m := m) (n := n) (Csup := Csup) (T := T)
  calc
    (∑ V : boundedRowSpaces (K := K) (n := n) (m := m) (k := k) Csup T,
      latticeCoveringRadius (rowZLattice V.1) /
        (rowSpaceHeight V.1) ^ n) =
        ∑ D : {D : EchelonMatrix K k m // D ∈ F},
          latticeCoveringRadius (rowZLattice (echelonRowSpace D.1)) /
            (rowSpaceHeight (echelonRowSpace D.1)) ^ n := by
      symm
      exact Fintype.sum_equiv e
        (fun D => latticeCoveringRadius (rowZLattice (echelonRowSpace D.1)) /
          (rowSpaceHeight (echelonRowSpace D.1)) ^ n)
        (fun V => latticeCoveringRadius (rowZLattice V.1) /
          (rowSpaceHeight V.1) ^ n)
        (fun _ => rfl)
    _ = ∑ D ∈ hF.toFinset,
        latticeCoveringRadius (rowZLattice (echelonRowSpace D)) /
          (rowSpaceHeight (echelonRowSpace D)) ^ n := by
      symm
      apply Finset.sum_subtype
      intro D
      exact hF.mem_toFinset
    _ = ∑ D ∈ (finite_calF_of_possibleSuccessiveMinima
        (K := K) (m := m) (k := k) (n := n)
        hCproj hCsup hT hk).toFinset,
        latticeCoveringRadius (rowZLattice (echelonRowSpace D)) /
          (rowSpaceHeight (echelonRowSpace D)) ^ n := by
      rfl

/- [derived consequence of paper equation `eq:just_as_before`, lines
   1724--1753] Transfer the noncritical uniform `𝓕_k(T)` radius bound to
   the exactly equal row-space family used in the finite Riemann sum.  Its
   product comparison remains explicit here because this is the generic
   assembly theorem; the specialized wrapper below supplies it from the
   proved Fieker--Stehlé/Minkowski-II derivation. -/
theorem exists_uniform_boundedRowSpaces_coveringRadius_sum_bound_of_noncritical
    {K : Type*} [Field K] [NumberField K]
    {m n j : ℕ} {Cprod : ℝ} (hm : 0 < m)
    (hgap : 1 < (n - m) * degree K) (hCprod : 0 ≤ Cprod) :
    ∃ Cfinite : ℝ, 0 < Cfinite ∧
      ∀ {Csup C T : ℝ}
        [Fintype (boundedRowSpaces (K := K) (n := n) (m := m) (k := j + 1)
          Csup T)]
        (hCproj : rowKRealSmulBound (K := K) (m := m) *
          numberFieldCoefficientRadius K ≤ C)
        (hCsup : Csup ≤ C) (hT : 0 ≤ T)
        (hprod : ∀ D : EchelonMatrix K (j + 1) m,
          D ∈ calF (K := K) (l := j + 1) (m := m) (n := n) Csup T →
            (∏ i : Fin (j + 1),
              ‖((rowSuccessiveMinimum (echelonRowSpace D) i :
                rowZLattice (echelonRowSpace D)) :
                  rowRealSpan (echelonRowSpace D))‖ ^ degree K) ≤
              Cprod * rowSpaceHeight (echelonRowSpace D)),
        (∑ V : boundedRowSpaces (K := K) (n := n) (m := m) (k := j + 1)
          Csup T,
          latticeCoveringRadius (rowZLattice V.1) /
            (rowSpaceHeight V.1) ^ n) ≤ Cfinite := by
  obtain ⟨Cfinite, hCfinite, hbound⟩ :=
    exists_uniform_calF_coveringRadius_sum_bound_of_noncritical
      (K := K) (j := j) hm hgap hCprod
  refine ⟨Cfinite, hCfinite, ?_⟩
  intro Csup C T _ hCproj hCsup hT hprod
  rw [sum_boundedRowSpaces_coveringRadius_div_height_pow_eq_sum_calF
    (K := K) (m := m) (k := j + 1) (n := n) hCproj hCsup hT
    (Nat.succ_pos j)]
  exact hbound hCproj hCsup hT hprod

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

/- [derived consequence of paper `le:lower_bound_not_in_F` and `co:tail`,
   lines 1130--1169] Transfer the uniform echelon height bound to the
   complement of the norm-bounded row-space family.  The cutoff is stated in
   the integer form consumed by the Abel/Schmidt tail theorem; its only
   additional requirement is `N ≤ C_lower T^d`. -/
set_option maxHeartbeats 1200000 in
theorem exists_boundedRowSpaces_complement_height_cutoff
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (hkn : k ≤ n) (hkm : k ≤ m) (hk : 0 < k)
    {Csup T Cprod : ℝ}
    (hCsup : 0 < Csup) (hT : 0 < T) (hCprod : 0 < Cprod)
    (hprod : ∀ D : EchelonMatrix K k m,
      (∏ i : Fin k,
        ‖((rowSuccessiveMinimum (echelonRowSpace D) i :
            rowZLattice (echelonRowSpace D)) :
            rowRealSpan (echelonRowSpace D))‖ ^ degree K) ≤
        Cprod * rowSpaceHeight (echelonRowSpace D)) :
    ∃ Clower : ℝ, 0 < Clower ∧
      ∀ {N : ℕ}, (N : ℝ) ≤ Clower * T ^ degree K →
        ∀ V : Grassmannian K m k,
          V ∉ boundedRowSpaces (K := K) (n := n) (m := m) (k := k) Csup T →
            (N : ℝ) ≤ rowSpaceHeight V := by
  obtain ⟨Clower, hClower, hheight⟩ :=
    exists_uniform_echelon_height_lower_bound_of_not_mem_calF
      hkn hkm hk hCsup hT hCprod hprod
  refine ⟨Clower, hClower, ?_⟩
  intro N hN V hV
  let e := echelonRowSpaceEquiv (K := K) (l := k) (m := m)
  let D : EchelonMatrix K k m := e.symm V
  have hDV : echelonRowSpace D = V := by
    exact e.apply_symm_apply V
  have hDnot : D ∉ calF (K := K) (l := k) (m := m) (n := n) Csup T := by
    intro hDcal
    apply hV
    have hbound : echelonRowSpace D ∈
        boundedRowSpaces (K := K) (n := n) (m := m) (k := k) Csup T :=
      echelon_calF_subset_boundedRowSpaces
        (K := K) (l := k) (m := m) (n := n) (Csup := Csup) (T := T)
        ⟨D, hDcal, rfl⟩
    rw [hDV] at hbound
    exact hbound
  have hheightD := hheight D hDnot
  have hheightN : (N : ℝ) ≤ rowSpaceHeight (echelonRowSpace D) :=
    hN.trans hheightD
  rw [hDV] at hheightN
  exact hheightN

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
          (rowSpaceHeight (echelonRowSpace D))⁻¹ ^ n *
            rowMatrixSubspaceIntegral (echelonRowSpace D) n f| ≤
        Cₐ * rowMatrixFundamentalRadius (echelonRowSpace D) n /
          ((rowSpaceHeight (echelonRowSpace D)) ^ n * T) := by
  obtain ⟨Cₐ, hCₐ, hestimate⟩ :=
    h_f.rowMatrix_latticeRiemann_estimate
      (echelonRowSpace D)
      (rowMatrixRealSpan_ne_bot_of_pos (echelonRowSpace D) hl hn)
  refine ⟨Cₐ, hCₐ, fun T hT hRadius => ?_⟩
  rw [tsum_echelonIntegralMatrices_eq_integralRowMatrices D f T]
  simpa [rowMatrixRealSpan_finrank,
    rowMatrixLatticeCovolume_eq_rowSpaceHeight_pow] using hestimate T hT hRadius

/- [paper, `le:without_rank_cond`, lines 1038--1061] The same direct
   `M_n(Λ_D)` statement in the manuscript's intrinsic Voronoi notation.
   This is a proved reindexing of the row-lattice estimate: the displayed
   `sqrt n * rho(Λ_D)` is not replaced by an auxiliary fundamental-domain
   radius. -/
theorem Admissible.echelon_latticeVoronoiRiemann_estimate
    {K : Type*} [Field K] [NumberField K]
    {l m n : ℕ} (D : EchelonMatrix K l m)
    {f : M n m (K_ℝ[K]) → ℝ} (h_f : Admissible f)
    (hl : 0 < l) (hn : 0 < n) :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧ ∀ T : ℝ, 0 < T →
      (Real.sqrt (n : ℝ) *
        latticeCoveringRadius (rowZLattice (echelonRowSpace D))) / T ≤ 1 →
      |(∑' A : echelonIntegralMatrices (n := n) D,
          f (T⁻¹ • embedMatrix A.1)) /
            T ^ (n * (l * degree K)) -
          (rowSpaceHeight (echelonRowSpace D))⁻¹ ^ n *
            rowMatrixSubspaceIntegral (echelonRowSpace D) n f| ≤
        Cₐ * (Real.sqrt (n : ℝ) *
          latticeCoveringRadius (rowZLattice (echelonRowSpace D))) /
          ((rowSpaceHeight (echelonRowSpace D)) ^ n * T) := by
  obtain ⟨Cₐ, hCₐ, hestimate⟩ :=
    h_f.rowMatrix_latticeVoronoiRiemann_estimate_rank
      (echelonRowSpace D) hl hn
  refine ⟨Cₐ, hCₐ, fun T hT hRadius => ?_⟩
  rw [tsum_echelonIntegralMatrices_eq_integralRowMatrices D f T]
  simpa [rowMatrixLatticeCovolume_eq_rowSpaceHeight_pow] using
    hestimate T hT hRadius

/- [derived consequence of paper `le:without_rank_cond`, lines 1038--1061,
   and `re:help`, lines 550--562, conditional on
   `AdmissibleErrorControlUpTo`] This is the same direct `M_n(Λ_D)` estimate
   with the manuscript's arbitrary fixed threshold in place of the base
   threshold `1`.  The family, height, and intrinsic radius are unchanged. -/
theorem Admissible.echelon_latticeVoronoiRiemann_estimate_of_errorControlUpTo
    {K : Type*} [Field K] [NumberField K]
    {l m n : ℕ} (D : EchelonMatrix K l m)
    {f : M n m (K_ℝ[K]) → ℝ} (h_f : Admissible f)
    {εMax : ℝ} (hUpdate : AdmissibleErrorControlUpTo f εMax)
    (hl : 0 < l) (hn : 0 < n) :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧ ∀ T : ℝ, 0 < T →
      (Real.sqrt (n : ℝ) *
        latticeCoveringRadius (rowZLattice (echelonRowSpace D))) / T ≤ εMax →
      |(∑' A : echelonIntegralMatrices (n := n) D,
          f (T⁻¹ • embedMatrix A.1)) /
            T ^ (n * (l * degree K)) -
          (rowSpaceHeight (echelonRowSpace D))⁻¹ ^ n *
            rowMatrixSubspaceIntegral (echelonRowSpace D) n f| ≤
        Cₐ * (Real.sqrt (n : ℝ) *
          latticeCoveringRadius (rowZLattice (echelonRowSpace D))) /
          ((rowSpaceHeight (echelonRowSpace D)) ^ n * T) := by
  obtain ⟨Cₐ, hCₐ, hestimate⟩ :=
    h_f.rowMatrix_latticeVoronoiRiemann_estimate_rank_of_errorControlUpTo
      (echelonRowSpace D) hUpdate hl hn
  refine ⟨Cₐ, hCₐ, fun T hT hRadius => ?_⟩
  rw [tsum_echelonIntegralMatrices_eq_integralRowMatrices D f T]
  simpa [rowMatrixLatticeCovolume_eq_rowSpaceHeight_pow] using
    hestimate T hT hRadius

/- [derived consequence of paper `co:covering_bound`, lines 1239--1248,
   `le:without_rank_cond`, lines 1028--1045, and the application at lines
   1665--1694, conditional on `AdmissibleErrorControlUpTo`] This is the
   paper's choice of the arbitrary Riemann threshold for one exact member of
   `𝓕_k(T)`.  The explicit threshold below is the `C^{arbit1}` used in the
   proof of `le:Riemann_estimate`; the factor `sqrt n` is retained as in
   `le:without_rank_cond`. -/
theorem echelon_calF_latticeVoronoiRiemann_estimate_of_updated_control
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (D : EchelonMatrix K k m) (hk : 0 < k) (hn : 0 < n)
    {Csup T εMax : ℝ} (hT : 0 < T)
    (hD : D ∈ calF (K := K) (l := k) (m := m) (n := n) Csup T)
    {f : M n m (K_ℝ[K]) → ℝ} (h_f : Admissible f)
    (hUpdate : AdmissibleErrorControlUpTo f εMax)
    (hThreshold :
      Real.sqrt (n : ℝ) *
        (Fintype.card (Σ _ : Fin k, IntegralBasisIndex K) : ℝ) *
          rowScalarActionBoundSum (K := K) (m := m) * Csup ≤ εMax) :
    ∃ Cₐ : ℝ, 0 < Cₐ ∧
      |(∑' A : echelonIntegralMatrices (n := n) D,
          f (T⁻¹ • embedMatrix A.1)) /
            T ^ (n * (k * degree K)) -
          (rowSpaceHeight (echelonRowSpace D))⁻¹ ^ n *
            rowMatrixSubspaceIntegral (echelonRowSpace D) n f| ≤
        Cₐ * (Real.sqrt (n : ℝ) *
          latticeCoveringRadius (rowZLattice (echelonRowSpace D))) /
          ((rowSpaceHeight (echelonRowSpace D)) ^ n * T) := by
  obtain ⟨Cₐ, hCₐ, hestimate⟩ :=
    h_f.echelon_latticeVoronoiRiemann_estimate_of_errorControlUpTo
      D hUpdate hk hn
  refine ⟨Cₐ, hCₐ, ?_⟩
  apply hestimate T hT
  exact (echelon_calF_matrixCoveringRadius_div_le D hk hT hD).trans hThreshold

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

/- [derived consequence, paper `eq:defi_of_calF`, lines 784--803]
   The norm-bounded echelon family is finite.  Its row-space image is a
   subset of the finite family `boundedRowSpaces`; injectivity of the proved
   echelon representative map then transfers finiteness back to `calF`. -/
theorem finite_calF
    {K : Type*} [Field K] [NumberField K]
    {l m n : ℕ} {Csup T : ℝ} :
    (calF (K := K) (l := l) (m := m) (n := n) Csup T).Finite := by
  apply Set.Finite.of_finite_image
    (f := echelonRowSpace (K := K) (l := l) (m := m))
  · exact (finite_boundedRowSpaces (K := K) (n := n) (m := m) (k := l) Csup T).subset
      (echelon_calF_subset_boundedRowSpaces (K := K) (l := l) (m := m) (n := n))
  · exact (echelonRowSpace_injective (K := K) (l := l) (m := m)).injOn

/- [derived consequence of paper `le:low_rank_induction`, lines 1447--1449]
   The paper's set
     `S = {v ∈ M_{1×m}(𝓞_K) | ‖v‖ ≤ Csup*T}`
   contains a K-spanning family for every row space represented by an element
   of `𝓕_k(T)`.  The subtype in the conclusion is the paper's `S` intersected
   with the relevant row space; it is the form needed by the complement
   selection lemma.  The row witness is the one supplied by the direct
   `M_n(Λ_D)` definition of `calF`. -/
set_option maxHeartbeats 1200000 in
theorem echelon_boundedIntegralRowVectors_span
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} {Csup T : ℝ}
    (D : EchelonMatrix K k m)
    (hD : D ∈ calF (K := K) (l := k) (m := m) (n := n) Csup T) :
    let S : Set (Fin m → 𝓞 K) :=
      {x | ‖integralVectorEmbedding (K := K) m x‖ ≤ Csup * T}
    Submodule.span K
        {v : (echelonRowSpace D).1 | ∃ x ∈ S,
          (fun j => (x j : K)) = v.1} = ⊤ := by
  dsimp
  rw [← calFDirect_eq_calF] at hD
  rcases hD with ⟨A, hArank, hAnorm⟩
  have hAmod : A.1 ∈ integralRowMatrixModule (echelonRowSpace D) n := by
    rw [← echelonIntegralRowMatrixModule_eq D]
    exact A.2
  have hrows : rowsInIntegralRowModule (echelonRowSpace D) A.1 :=
    (mem_integralRowMatrixModule_iff _ _).mp hAmod
  have hspace : matrixRowSpace A.1 = (echelonRowSpace D).1 :=
    rowSpace_eq_of_rowsIn_of_rank (echelonRowSpace D) A.1 hrows hArank
  have hrow_le (i : Fin n) :
      ‖integralVectorEmbedding (K := K) m (A.1.row i)‖ ≤ Csup * T := by
    change ‖rowVectorOfFun (embedMatrix A.1 i)‖ ≤ Csup * T
    calc
      ‖rowVectorOfFun (embedMatrix A.1 i)‖ ≤ ‖embedMatrix A.1‖ := by
        rw [PiLp.norm_eq_of_L2, Matrix.frobenius_norm_def]
        rw [Real.sqrt_eq_rpow]
        have hsum : (∑ j, ‖embedMatrix A.1 i j‖ ^ 2) ≤
            ∑ i', ∑ j, ‖embedMatrix A.1 i' j‖ ^ 2 := by
          have h := Finset.single_le_sum
            (s := (Finset.univ : Finset (Fin n)))
            (f := fun i' => ∑ j, ‖embedMatrix A.1 i' j‖ ^ 2)
            (fun i' hi' => Finset.sum_nonneg fun j hj => sq_nonneg _)
            (Finset.mem_univ i)
          simpa using h
        apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
        simpa using hsum
      _ ≤ Csup * T := hAnorm
  have hrowspan : Submodule.span K (Set.range (fun i : Fin n =>
      (fun j : Fin m => (A.1.row i j : K)))) = (echelonRowSpace D).1 := by
    have hrowspan' : Submodule.span K (Set.range (fun i : Fin n =>
        (fun j : Fin m => (A.1.row i j : K)))) = matrixRowSpace A.1 := by
      unfold matrixRowSpace
      congr 1
    exact hrowspan'.trans hspace
  let rowK : Fin n → (echelonRowSpace D).1 := fun i =>
    ⟨(fun j : Fin m => (A.1.row i j : K)), by
      exact hrows i⟩
  have hrows_subtype : Submodule.span K (Set.range (fun i : Fin n =>
      rowK i)) = ⊤ := by
    apply (Submodule.span_range_subtype_eq_top_iff
      (echelonRowSpace D).1 (s := fun i : Fin n =>
        (fun j : Fin m => (A.1.row i j : K))) (fun i => hrows i)).2
    exact hrowspan
  have hrow_le_S : Submodule.span K (Set.range (fun i : Fin n =>
      rowK i)) ≤
      Submodule.span K {v : (echelonRowSpace D).1 | ∃ x : Fin m → 𝓞 K,
        ‖integralVectorEmbedding (K := K) m x‖ ≤ Csup * T ∧
        (fun j => (x j : K)) = v.1} := by
    apply Submodule.span_le.2
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    exact ⟨A.1.row i, hrow_le i, rfl⟩
  apply le_antisymm
  · exact le_top
  · rw [← hrows_subtype]
    exact hrow_le_S

/- [derived consequence, paper `le:low_rank_induction`, lines 1444--1455]
   The paper's assertion that a spanning bounded set supplies `k-l`
   complement vectors is now discharged by the quotient-basis lemma.  The set
   `S` is deliberately left as a paper-facing input here: the separate claim
   that the norm ball contains a basis of each `Λ_D ⊗ K` still has to be
   obtained from the chosen height/minima argument. -/
theorem exists_echelon_complement_from_spanningSet
    {K : Type*} [Field K] [NumberField K]
    {m k l : ℕ} (D' : EchelonMatrix K l m)
    (D : EchelonMatrix K k m)
    (hLambda : echelonLambda D' ≤ echelonLambda D)
    (S : Set (echelonRowSpace D).1)
    (hspan : Submodule.span K S = ⊤) :
    ∃ v : Fin (k - l) → S,
      (echelonRowSpace D').1.comap (echelonRowSpace D).1.subtype ⊔
          Submodule.span K (Set.range
            (fun i => (v i : (echelonRowSpace D).1))) = ⊤ := by
  have hsub : (echelonRowSpace D').1 ≤ (echelonRowSpace D).1 :=
    (echelonLambda_le_iff_echelonRowSpace_le D D').mp hLambda
  let U : Submodule K (echelonRowSpace D).1 :=
    (echelonRowSpace D').1.comap (echelonRowSpace D).1.subtype
  have hUdim : Module.finrank K U = l := by
    dsimp [U]
    rw [(Submodule.comapSubtypeEquivOfLe hsub).finrank_eq]
    exact echelonRowSpace_rank D'
  have hquot : Module.finrank K ((echelonRowSpace D).1 ⧸ U) = k - l := by
    have hsum := Submodule.finrank_quotient_add_finrank U
    rw [echelonRowSpace_rank D, hUdim] at hsum
    exact Nat.eq_sub_of_add_eq (by simpa [Nat.add_comm] using hsum)
  obtain ⟨v, hv⟩ := exists_fin_basis_extension_from_spanningSet U S hspan hquot
  exact ⟨v, hv⟩

/- [derived consequence of paper `le:low_rank_induction`, lines 1452--1455]
   Uniformly choose the paper's integral vectors `l_j^(i)` for every upper
   echelon matrix.  On the relevant family, the bounded-spanning theorem and
   the quotient-basis selection lemma supply the complement; the subtype
   complement is converted to the ambient row-space equation by the proved
   linear-algebra bridge. -/
set_option maxHeartbeats 1200000 in
theorem exists_echelon_complement_lifts_of_calF
    {K : Type*} [Field K] [NumberField K]
    {n m k l : ℕ} {Csup T : ℝ}
    (D' : EchelonMatrix K l m) :
    ∃ lift : EchelonMatrix K k m → Fin (k - l) → (Fin m → 𝓞 K),
      ∀ D : EchelonMatrix K k m,
        D ∈ calF (K := K) (l := k) (m := m) (n := n) Csup T ∩
          {D | echelonLambda D' ≤ echelonLambda D} →
        (∀ i, ‖integralVectorEmbedding (K := K) m (lift D i)‖ ≤ Csup * T) ∧
        (echelonRowSpace D').1 ⊔
            Submodule.span K (Set.range
              (fun i : Fin (k - l) =>
                (fun j : Fin m => (lift D i j : K)))) =
          (echelonRowSpace D).1 := by
  let relevant : EchelonMatrix K k m → Prop := fun D =>
    D ∈ calF (K := K) (l := k) (m := m) (n := n) Csup T ∩
      {D | echelonLambda D' ≤ echelonLambda D}
  have hlocal (D : EchelonMatrix K k m) (hD : relevant D) :
      ∃ liftD : Fin (k - l) → (Fin m → 𝓞 K),
        (∀ i, ‖integralVectorEmbedding (K := K) m (liftD i)‖ ≤ Csup * T) ∧
        (echelonRowSpace D').1 ⊔
            Submodule.span K (Set.range
              (fun i : Fin (k - l) =>
                (fun j : Fin m => (liftD i j : K)))) =
          (echelonRowSpace D).1 := by
    have hDcal : D ∈ calF (K := K) (l := k) (m := m) (n := n) Csup T := hD.1
    have hLambda : echelonLambda D' ≤ echelonLambda D := hD.2
    let S : Set (echelonRowSpace D).1 := {v | ∃ x : Fin m → 𝓞 K,
      ‖integralVectorEmbedding (K := K) m x‖ ≤ Csup * T ∧
      (fun j => (x j : K)) = v.1}
    have hS : Submodule.span K S = ⊤ := by
      simpa [S] using (echelon_boundedIntegralRowVectors_span D hDcal)
    obtain ⟨v, hv⟩ := exists_echelon_complement_from_spanningSet
      D' D hLambda S hS
    choose liftD hlift using fun i => (v i).property
    have hsub : (echelonRowSpace D').1 ≤ (echelonRowSpace D).1 :=
      (echelonLambda_le_iff_echelonRowSpace_le D D').mp hLambda
    have hcompV := sup_eq_of_comap_sup_span_eq_top
      (echelonRowSpace D').1 (echelonRowSpace D).1 hsub
      (fun i => (v i : (echelonRowSpace D).1)) hv
    have hpoint : (fun i : Fin (k - l) =>
        (fun j : Fin m => (liftD i j : K))) =
        (fun i : Fin (k - l) =>
          ((v i : (echelonRowSpace D).1) : Fin m → K)) := by
      funext i j
      exact congrFun (hlift i).2 j
    rw [← hpoint] at hcompV
    refine ⟨liftD, ?_, hcompV⟩
    intro i
    exact (hlift i).1
  let lift : EchelonMatrix K k m → Fin (k - l) → (Fin m → 𝓞 K) := fun D =>
    if hD : relevant D then Classical.choose (hlocal D hD) else fun _ => 0
  refine ⟨lift, ?_⟩
  intro D hD
  have hD' : relevant D := hD
  simpa [lift, hD'] using
    (Classical.choose_spec (hlocal D hD'))

/- [derived consequence, paper `le:low_rank_induction`, lines 1452--1455]
   Paper-facing form of the quotient-span criterion.  The sets `S₁` and `S₂`
   represent the K-row vectors selected for two possible upper-rank matrices;
   the theorem records exactly the paper's conclusion that equality of their
   spans modulo the lower-rank row space implies equality of the row spaces. -/
theorem echelonRowSpace_eq_of_quotient_map_eq
    {K : Type*} [Field K] [NumberField K]
    {m k l : ℕ}
    (D' : EchelonMatrix K l m)
    (D₁ D₂ : EchelonMatrix K k m)
    (hD₁ : echelonLambda D' ≤ echelonLambda D₁)
    (hD₂ : echelonLambda D' ≤ echelonLambda D₂)
    (S₁ S₂ : Set (Fin m → K))
    (hV₁ : (echelonRowSpace D').1 ⊔ Submodule.span K S₁ =
      (echelonRowSpace D₁).1)
    (hV₂ : (echelonRowSpace D').1 ⊔ Submodule.span K S₂ =
      (echelonRowSpace D₂).1)
    (hquot : Submodule.map (echelonRowSpace D').1.mkQ
        (Submodule.span K S₁) =
      Submodule.map (echelonRowSpace D').1.mkQ
        (Submodule.span K S₂)) :
    echelonRowSpace D₁ = echelonRowSpace D₂ := by
  have hD₁' : (echelonRowSpace D').1 ≤ (echelonRowSpace D₁).1 :=
    (echelonLambda_le_iff_echelonRowSpace_le D₁ D').mp hD₁
  have hD₂' : (echelonRowSpace D').1 ≤ (echelonRowSpace D₂).1 :=
    (echelonLambda_le_iff_echelonRowSpace_le D₂ D').mp hD₂
  have hrows : (echelonRowSpace D₁).1 = (echelonRowSpace D₂).1 :=
    sup_eq_of_quotient_map_eq
      (echelonRowSpace D').1 (echelonRowSpace D₁).1
      (echelonRowSpace D₂).1 S₁ S₂ hD₁' hD₂' hV₁ hV₂ hquot
  exact Subtype.ext hrows

/- [derived consequence, paper `le:low_rank_induction`, lines 1444--1455]
   The paper-facing tuple-injectivity argument.  `hchoice` says that the
   projected choices are projections of integral K-row vectors, while the
   proved row-space bridge converts membership in the real lower span back to
   membership in the lower K-row space.  The real projection lemma and the
   quotient-span criterion then prove injectivity. -/
theorem echelonProjectedChoice_inj_of_real_quotient_bridge
    {K : Type*} [Field K] [NumberField K]
    {m k l : ℕ} (B : Set (EchelonMatrix K k m))
    (D' : EchelonMatrix K l m)
    (R : ℝ)
    (choice : EchelonMatrix K k m → Fin (k - l) →
      {v : projectedAmbientRowModule (K := K) (echelonRowSpace D') |
        ‖(v : (rowRealSpan (echelonRowSpace D'))ᗮ)‖ ≤ R})
    (lift : EchelonMatrix K k m → Fin (k - l) → (Fin m → 𝓞 K))
    (hchoice : ∀ (D : EchelonMatrix K k m) (i : Fin (k - l)),
      D ∈ B ∩ {D | echelonLambda D' ≤ echelonLambda D} →
      (choice D i : (rowRealSpan (echelonRowSpace D'))ᗮ) =
        projectedAmbientRowMap (echelonRowSpace D')
          (integralVectorEmbedding (K := K) m (lift D i)))
    (hcomp : ∀ (D : EchelonMatrix K k m),
      D ∈ B ∩ {D | echelonLambda D' ≤ echelonLambda D} →
      (echelonRowSpace D').1 ⊔
          Submodule.span K (Set.range
            (fun i : Fin (k - l) =>
              (fun j : Fin m => (lift D i j : K)))) =
        (echelonRowSpace D).1) :
    Set.InjOn (fun D => fun i => choice D i)
      (B ∩ {D | echelonLambda D' ≤ echelonLambda D}) := by
  intro D hD E hE hEq
  have hquot_pointwise : ∀ i : Fin (k - l),
      (echelonRowSpace D').1.mkQ
          (fun j : Fin m => (lift D i j : K)) =
        (echelonRowSpace D').1.mkQ
          (fun j : Fin m => (lift E i j : K)) := by
    intro i
    have hproj :
        projectedAmbientRowMap (echelonRowSpace D')
            (integralVectorEmbedding (K := K) m (lift D i)) =
          projectedAmbientRowMap (echelonRowSpace D')
            (integralVectorEmbedding (K := K) m (lift E i)) := by
      calc
        projectedAmbientRowMap (echelonRowSpace D')
              (integralVectorEmbedding (K := K) m (lift D i)) =
            (choice D i : (rowRealSpan (echelonRowSpace D'))ᗮ) :=
          (hchoice D i hD).symm
        _ = (choice E i : (rowRealSpan (echelonRowSpace D'))ᗮ) := by
          exact congrArg
            (fun z : {v : projectedAmbientRowModule (K := K)
                (echelonRowSpace D') |
                ‖(v : (rowRealSpan (echelonRowSpace D'))ᗮ)‖ ≤ R} =>
              (z : (rowRealSpan (echelonRowSpace D'))ᗮ))
            (congrFun hEq i)
        _ = projectedAmbientRowMap (echelonRowSpace D')
              (integralVectorEmbedding (K := K) m (lift E i)) :=
          hchoice E i hE
    have hdiffReal :
        integralVectorEmbedding (K := K) m (lift D i) -
            integralVectorEmbedding (K := K) m (lift E i) ∈
          rowRealSpan (echelonRowSpace D') := by
      have hproj' := (orthogonalProjectionOnto_eq_iff_sub_mem
        (rowRealSpan (echelonRowSpace D'))).mp hproj
      simpa [projectedAmbientRowMap] using hproj'
    have hdiffK :
        (fun j : Fin m => (lift D i j : K)) -
            (fun j : Fin m => (lift E i j : K)) ∈
          (echelonRowSpace D').1 :=
      rowRealSpan_mem_integral_difference_to_mem
        (echelonRowSpace D') (lift D i) (lift E i) hdiffReal
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact (Submodule.Quotient.mk_eq_zero (echelonRowSpace D').1).mpr hdiffK
  have hquot :
      Submodule.map (echelonRowSpace D').1.mkQ
          (Submodule.span K (Set.range
            (fun i : Fin (k - l) =>
              (fun j : Fin m => (lift D i j : K)))) ) =
        Submodule.map (echelonRowSpace D').1.mkQ
          (Submodule.span K (Set.range
            (fun i : Fin (k - l) =>
              (fun j : Fin m => (lift E i j : K)))) ) :=
    quotient_map_span_range_eq_of_forall
      (echelonRowSpace D').1
      (fun i : Fin (k - l) => fun j : Fin m => (lift D i j : K))
      (fun i : Fin (k - l) => fun j : Fin m => (lift E i j : K))
      hquot_pointwise
  have hrows := echelonRowSpace_eq_of_quotient_map_eq
    D' D E hD.2 hE.2
      (Set.range (fun i : Fin (k - l) =>
        (fun j : Fin m => (lift D i j : K))))
      (Set.range (fun i : Fin (k - l) =>
        (fun j : Fin m => (lift E i j : K))))
      (hcomp D hD) (hcomp E hE) hquot
  exact (echelonRowSpace_injective (K := K) (l := k) (m := m)) hrows

/- [derived consequence, paper `le:low_rank_induction`, lines 1431--1480]
   Manuscript-facing specialization of the projected overcount.  The source
   chooses vectors from the ball of radius `Csup * T`; this radius is kept in
   the choice type rather than silently normalized to `T`. -/
set_option maxHeartbeats 1000000 in
theorem echelonCalFExtensionCount_le_of_ambient_row_covering
    {K : Type*} [Field K] [NumberField K]
    {n m k l : ℕ} {Csup T : ℝ}
    (hCsup : 0 < Csup) (hT : 1 ≤ T)
    (D' : EchelonMatrix K l m)
    (_hD' : D' ∈ calF (K := K) (l := l) (m := m) (n := n) Csup T)
    (μ : Measure ((rowRealSpan (echelonRowSpace D'))ᗮ))
    [Measure.IsAddHaarMeasure μ]
    (hcov : ZLattice.covolume
      (projectedAmbientRowModule (K := K) (echelonRowSpace D')) μ =
        (rowSpaceHeight (echelonRowSpace D'))⁻¹)
    (choice : EchelonMatrix K k m → Fin (k - l) →
      {v : projectedAmbientRowModule (K := K) (echelonRowSpace D') |
        ‖(v : (rowRealSpan (echelonRowSpace D'))ᗮ)‖ ≤ Csup * T})
    (hchoice : Set.InjOn (fun D => fun i => choice D i)
      ((calF (K := K) (l := k) (m := m) (n := n) Csup T) ∩
        {D | echelonLambda D' ≤ echelonLambda D})) :
    ∃ C : ℝ, 0 < C ∧
      echelonExtensionCount
          (calF (K := K) (l := k) (m := m) (n := n) Csup T) D' ≤
        (C * (Csup * T + latticeCoveringRadius
          (ambientIntegralRowModule (K := K) m)) ^
            (m * degree K - l * degree K) *
          rowSpaceHeight (echelonRowSpace D')) ^ (k - l) := by
  letI : Fintype (calF (K := K) (l := k) (m := m) (n := n) Csup T) :=
    (finite_calF (K := K) (l := k) (m := m) (n := n)
    (Csup := Csup) (T := T)).fintype
  have hscale : 0 < Csup * T := mul_pos hCsup
    (lt_of_lt_of_le zero_lt_one hT)
  obtain ⟨C, hC, hcount⟩ :=
    echelonExtensionCount_le_of_projected_covering
      (B := calF (K := K) (l := k) (m := m) (n := n) Csup T)
      D' hscale μ
      (projectedAmbientRowModule_isLatticeCovering_of_ambientRadius
        (echelonRowSpace D')) hcov choice hchoice
  refine ⟨C, hC, ?_⟩
  exact hcount

/- [derived consequence, paper `le:low_rank_induction`, lines 1431--1480]
   Raw-metric specialization of the preceding paper-facing extension count.
   The family `𝓕_k(T)`, the projected choice type, and the radius
   `Csup * T` are unchanged; only the unproved paper-metric covolume premise
   is replaced by the proved raw primitive-projection formula. -/
set_option maxHeartbeats 1000000 in
theorem echelonCalFExtensionCount_le_of_raw_ambient_row_covering
    {K : Type*} [Field K] [NumberField K]
    {n m k l : ℕ} {Csup T : ℝ}
    (hCsup : 0 < Csup) (hT : 1 ≤ T)
    (D' : EchelonMatrix K l m)
    (_hD' : D' ∈ calF (K := K) (l := l) (m := m) (n := n) Csup T)
    (choice : EchelonMatrix K k m → Fin (k - l) →
      {v : projectedAmbientRowModule (K := K) (echelonRowSpace D') |
        ‖(v : (rowRealSpan (echelonRowSpace D'))ᗮ)‖ ≤ Csup * T})
    (hchoice : Set.InjOn (fun D => fun i => choice D i)
      ((calF (K := K) (l := k) (m := m) (n := n) Csup T) ∩
        {D | echelonLambda D' ≤ echelonLambda D})) :
    ∃ C : ℝ, 0 < C ∧
      echelonExtensionCount
          (calF (K := K) (l := k) (m := m) (n := n) Csup T) D' ≤
        (C * (Csup * T + latticeCoveringRadius
          (ambientIntegralRowModule (K := K) m)) ^
            (m * degree K - l * degree K) *
          rowSpaceHeight (echelonRowSpace D')) ^ (k - l) := by
  letI : Fintype (calF (K := K) (l := k) (m := m) (n := n) Csup T) :=
    (finite_calF (K := K) (l := k) (m := m) (n := n)
    (Csup := Csup) (T := T)).fintype
  have hscale : 0 < Csup * T := mul_pos hCsup
    (lt_of_lt_of_le zero_lt_one hT)
  exact echelonExtensionCount_le_of_raw_ambient_row_covering
    (B := calF (K := K) (l := k) (m := m) (n := n) Csup T)
    D' hscale choice hchoice

/- [derived consequence, paper `le:low_rank_induction`, lines 1447--1481]
   Construct the paper's projected choices from integral lifts.  The original
   norm bound on the lifts is transferred to the projected norm by the
   contraction lemma.  The complement bridge remains explicit; the
   number-field quotient bridge is supplied by the proved row-space lemma. -/
set_option maxHeartbeats 1000000 in
theorem echelonCalFExtensionCount_le_of_ambient_row_covering_of_lifts
    {K : Type*} [Field K] [NumberField K]
    {n m k l : ℕ} {Csup T : ℝ}
    (hCsup : 0 < Csup) (hT : 1 ≤ T)
    (D' : EchelonMatrix K l m)
    (hD' : D' ∈ calF (K := K) (l := l) (m := m) (n := n) Csup T)
    (μ : Measure ((rowRealSpan (echelonRowSpace D'))ᗮ))
    [Measure.IsAddHaarMeasure μ]
    (hcov : ZLattice.covolume
      (projectedAmbientRowModule (K := K) (echelonRowSpace D')) μ =
        (rowSpaceHeight (echelonRowSpace D'))⁻¹)
    (lift : EchelonMatrix K k m → Fin (k - l) → (Fin m → 𝓞 K))
    (hlift_bound : ∀ (D : EchelonMatrix K k m) (i : Fin (k - l)),
      ‖integralVectorEmbedding (K := K) m (lift D i)‖ ≤ Csup * T)
    (hcomp : ∀ (D : EchelonMatrix K k m),
      D ∈ calF (K := K) (l := k) (m := m) (n := n) Csup T ∩
        {D | echelonLambda D' ≤ echelonLambda D} →
      (echelonRowSpace D').1 ⊔
          Submodule.span K (Set.range
            (fun i : Fin (k - l) =>
              (fun j : Fin m => (lift D i j : K)))) =
        (echelonRowSpace D).1) :
    ∃ C : ℝ, 0 < C ∧
      echelonExtensionCount
          (calF (K := K) (l := k) (m := m) (n := n) Csup T) D' ≤
        (C * (Csup * T + latticeCoveringRadius
          (ambientIntegralRowModule (K := K) m)) ^
            (m * degree K - l * degree K) *
          rowSpaceHeight (echelonRowSpace D')) ^ (k - l) := by
  let choice : EchelonMatrix K k m → Fin (k - l) →
      {v : projectedAmbientRowModule (K := K) (echelonRowSpace D') |
        ‖(v : (rowRealSpan (echelonRowSpace D'))ᗮ)‖ ≤ Csup * T} :=
    fun D i => ⟨⟨
      projectedAmbientRowMap (echelonRowSpace D')
        (integralVectorEmbedding (K := K) m (lift D i)),
      projectedAmbientRowMap_mem_projectedAmbientRowModule
        (echelonRowSpace D')
        (integralVectorEmbedding_mem_ambientIntegralRowModule m (lift D i))⟩,
      le_trans
        (by
          change ‖(rowRealSpan (echelonRowSpace D'))ᗮ.orthogonalProjectionOnto
              (integralVectorEmbedding (K := K) m (lift D i))‖ ≤
            ‖integralVectorEmbedding (K := K) m (lift D i)‖
          exact Submodule.norm_orthogonalProjectionOnto_apply_le
            (rowRealSpan (echelonRowSpace D'))ᗮ
            (integralVectorEmbedding (K := K) m (lift D i)))
        (hlift_bound D i)⟩
  have hchoice : Set.InjOn (fun D => fun i => choice D i)
      (calF (K := K) (l := k) (m := m) (n := n) Csup T ∩
        {D | echelonLambda D' ≤ echelonLambda D}) := by
    apply echelonProjectedChoice_inj_of_real_quotient_bridge
      (B := calF (K := K) (l := k) (m := m) (n := n) Csup T)
      D' (Csup * T) choice lift
    · intro D i hD
      rfl
    · exact hcomp
  exact echelonCalFExtensionCount_le_of_ambient_row_covering
    hCsup hT D' hD' μ hcov choice hchoice

/- [derived consequence of paper `le:low_rank_induction`, lines 1431--1481]
   The manuscript-facing estimate with the choices `l_j^(i)` constructed from
   the bounded set `S`.  The projected covolume hypothesis remains explicit
   because its exact number-field normalization is still the geometric input
   to be matched with the cited source. -/
set_option maxHeartbeats 1600000 in
theorem echelonCalFExtensionCount_le_of_constructed_complement
    {K : Type*} [Field K] [NumberField K]
    {n m k l : ℕ} {Csup T : ℝ}
    (hCsup : 0 < Csup) (hT : 1 ≤ T)
    (D' : EchelonMatrix K l m)
    (hD' : D' ∈ calF (K := K) (l := l) (m := m) (n := n) Csup T)
    (μ : Measure ((rowRealSpan (echelonRowSpace D'))ᗮ))
    [Measure.IsAddHaarMeasure μ]
    (hcov : ZLattice.covolume
      (projectedAmbientRowModule (K := K) (echelonRowSpace D')) μ =
        (rowSpaceHeight (echelonRowSpace D'))⁻¹) :
    ∃ C : ℝ, 0 < C ∧
      echelonExtensionCount
          (calF (K := K) (l := k) (m := m) (n := n) Csup T) D' ≤
        (C * (Csup * T + latticeCoveringRadius
          (ambientIntegralRowModule (K := K) m)) ^
            (m * degree K - l * degree K) *
          rowSpaceHeight (echelonRowSpace D')) ^ (k - l) := by
  obtain ⟨lift, hlift⟩ := exists_echelon_complement_lifts_of_calF
    (K := K) (n := n) (m := m) (k := k) (l := l)
    (Csup := Csup) (T := T) D'
  have hscale : 0 < Csup * T := mul_pos hCsup
    (lt_of_lt_of_le zero_lt_one hT)
  let choice : EchelonMatrix K k m → Fin (k - l) →
      {v : projectedAmbientRowModule (K := K) (echelonRowSpace D') |
        ‖(v : (rowRealSpan (echelonRowSpace D'))ᗮ)‖ ≤ Csup * T} :=
    fun D i => if hD : D ∈ calF (K := K) (l := k) (m := m) (n := n) Csup T ∩
        {D | echelonLambda D' ≤ echelonLambda D} then
      ⟨⟨projectedAmbientRowMap (echelonRowSpace D')
          (integralVectorEmbedding (K := K) m (lift D i)),
        projectedAmbientRowMap_mem_projectedAmbientRowModule
          (echelonRowSpace D')
          (integralVectorEmbedding_mem_ambientIntegralRowModule m
            (lift D i))⟩,
        le_trans
          (by
            change ‖(rowRealSpan (echelonRowSpace D'))ᗮ.orthogonalProjectionOnto
                (integralVectorEmbedding (K := K) m (lift D i))‖ ≤
              ‖integralVectorEmbedding (K := K) m (lift D i)‖
            exact Submodule.norm_orthogonalProjectionOnto_apply_le
              (rowRealSpan (echelonRowSpace D'))ᗮ
              (integralVectorEmbedding (K := K) m (lift D i)))
          ((hlift D hD).1 i)⟩
    else ⟨0, by
      change ‖(0 : (rowRealSpan (echelonRowSpace D'))ᗮ)‖ ≤ Csup * T
      rw [norm_zero]
      exact hscale.le⟩
  have hchoice : Set.InjOn (fun D => fun i => choice D i)
      (calF (K := K) (l := k) (m := m) (n := n) Csup T ∩
        {D | echelonLambda D' ≤ echelonLambda D}) := by
    apply echelonProjectedChoice_inj_of_real_quotient_bridge
      (B := calF (K := K) (l := k) (m := m) (n := n) Csup T)
      D' (Csup * T) choice lift
    · intro D i hD
      simp only [choice, dif_pos hD]
    · intro D hD
      exact (hlift D hD).2
  exact echelonCalFExtensionCount_le_of_ambient_row_covering
    hCsup hT D' hD' μ hcov choice hchoice

/- [derived consequence, paper `le:low_rank_induction`, lines 1431--1481]
   The same manuscript-facing complement construction in the raw Euclidean
   metric.  The lifts `l_j^(i)`, their projection, and the injectivity
   argument are precisely those of the paper; only the raw covolume bridge is
   used to discharge the coarse lattice-count constant. -/
set_option maxHeartbeats 1600000 in
theorem echelonCalFExtensionCount_le_of_raw_constructed_complement
    {K : Type*} [Field K] [NumberField K]
    {n m k l : ℕ} {Csup T : ℝ}
    (hCsup : 0 < Csup) (hT : 1 ≤ T)
    (D' : EchelonMatrix K l m)
    (hD' : D' ∈ calF (K := K) (l := l) (m := m) (n := n) Csup T) :
    ∃ C : ℝ, 0 < C ∧
      echelonExtensionCount
          (calF (K := K) (l := k) (m := m) (n := n) Csup T) D' ≤
        (C * (Csup * T + latticeCoveringRadius
          (ambientIntegralRowModule (K := K) m)) ^
            (m * degree K - l * degree K) *
          rowSpaceHeight (echelonRowSpace D')) ^ (k - l) := by
  obtain ⟨lift, hlift⟩ := exists_echelon_complement_lifts_of_calF
    (K := K) (n := n) (m := m) (k := k) (l := l)
    (Csup := Csup) (T := T) D'
  have hscale : 0 < Csup * T := mul_pos hCsup
    (lt_of_lt_of_le zero_lt_one hT)
  let choice : EchelonMatrix K k m → Fin (k - l) →
      {v : projectedAmbientRowModule (K := K) (echelonRowSpace D') |
        ‖(v : (rowRealSpan (echelonRowSpace D'))ᗮ)‖ ≤ Csup * T} :=
    fun D i => if hD : D ∈ calF (K := K) (l := k) (m := m) (n := n) Csup T ∩
        {D | echelonLambda D' ≤ echelonLambda D} then
      ⟨⟨projectedAmbientRowMap (echelonRowSpace D')
          (integralVectorEmbedding (K := K) m (lift D i)),
        projectedAmbientRowMap_mem_projectedAmbientRowModule
          (echelonRowSpace D')
          (integralVectorEmbedding_mem_ambientIntegralRowModule m
            (lift D i))⟩,
        le_trans
          (by
            change ‖(rowRealSpan (echelonRowSpace D'))ᗮ.orthogonalProjectionOnto
                (integralVectorEmbedding (K := K) m (lift D i))‖ ≤
              ‖integralVectorEmbedding (K := K) m (lift D i)‖
            exact Submodule.norm_orthogonalProjectionOnto_apply_le
              (rowRealSpan (echelonRowSpace D'))ᗮ
              (integralVectorEmbedding (K := K) m (lift D i)))
          ((hlift D hD).1 i)⟩
    else ⟨0, by
      change ‖(0 : (rowRealSpan (echelonRowSpace D'))ᗮ)‖ ≤ Csup * T
      rw [norm_zero]
      exact hscale.le⟩
  have hchoice : Set.InjOn (fun D => fun i => choice D i)
      (calF (K := K) (l := k) (m := m) (n := n) Csup T ∩
        {D | echelonLambda D' ≤ echelonLambda D}) := by
    apply echelonProjectedChoice_inj_of_real_quotient_bridge
      (B := calF (K := K) (l := k) (m := m) (n := n) Csup T)
      D' (Csup * T) choice lift
    · intro D i hD
      simp only [choice, dif_pos hD]
    · intro D hD
      exact (hlift D hD).2
  exact echelonCalFExtensionCount_le_of_raw_ambient_row_covering
    hCsup hT D' hD' choice hchoice

/- [derived consequence, paper `le:low_rank_induction`, lines 1431--1481]
   The same complement-lift construction with the raw ball-volume coefficient
   retained explicitly.  This is the paper's choice of the vectors
   `l_j^(i)` and its projection/injectivity argument; spelling out the
   coefficient only prevents the fixed implicit constant from being
   reselected after `T` or `D'` has been fixed. -/
set_option maxHeartbeats 1600000 in
theorem echelonCalFExtensionCount_le_of_raw_constructed_complement_uniform
    {K : Type*} [Field K] [NumberField K]
    {n m k l : ℕ} {Csup T : ℝ}
    (hCsup : 0 < Csup) (hT : 1 ≤ T)
    (D' : EchelonMatrix K l m) (hlm : l < m)
    (hD' : D' ∈ calF (K := K) (l := l) (m := m) (n := n) Csup T) :
    echelonExtensionCount
        (calF (K := K) (l := k) (m := m) (n := n) Csup T) D' ≤
      ((euclideanUnitBallVolume (m * degree K - l * degree K) *
        (ZLattice.covolume (ambientIntegralRowModule (K := K) m)
          (μHE[Module.finrank ℝ (RowVector K m)]))⁻¹) *
        (Csup * T + latticeCoveringRadius
          (ambientIntegralRowModule (K := K) m)) ^
            (m * degree K - l * degree K) *
        rowSpaceHeight (echelonRowSpace D')) ^ (k - l) := by
  letI : Fintype (calF (K := K) (l := k) (m := m) (n := n) Csup T) :=
    (finite_calF (K := K) (l := k) (m := m) (n := n)
      (Csup := Csup) (T := T)).fintype
  obtain ⟨lift, hlift⟩ := exists_echelon_complement_lifts_of_calF
    (K := K) (n := n) (m := m) (k := k) (l := l)
    (Csup := Csup) (T := T) D'
  have hscale : 0 < Csup * T := mul_pos hCsup
    (lt_of_lt_of_le zero_lt_one hT)
  let choice : EchelonMatrix K k m → Fin (k - l) →
      {v : projectedAmbientRowModule (K := K) (echelonRowSpace D') |
        ‖(v : (rowRealSpan (echelonRowSpace D'))ᗮ)‖ ≤ Csup * T} :=
    fun D i => if hD : D ∈ calF (K := K) (l := k) (m := m) (n := n) Csup T ∩
        {D | echelonLambda D' ≤ echelonLambda D} then
      ⟨⟨projectedAmbientRowMap (echelonRowSpace D')
          (integralVectorEmbedding (K := K) m (lift D i)),
        projectedAmbientRowMap_mem_projectedAmbientRowModule
          (echelonRowSpace D')
          (integralVectorEmbedding_mem_ambientIntegralRowModule m
            (lift D i))⟩,
        le_trans
          (by
            change ‖(rowRealSpan (echelonRowSpace D'))ᗮ.orthogonalProjectionOnto
                (integralVectorEmbedding (K := K) m (lift D i))‖ ≤
              ‖integralVectorEmbedding (K := K) m (lift D i)‖
            exact Submodule.norm_orthogonalProjectionOnto_apply_le
              (rowRealSpan (echelonRowSpace D'))ᗮ
              (integralVectorEmbedding (K := K) m (lift D i)))
          ((hlift D hD).1 i)⟩
    else ⟨0, by
      change ‖(0 : (rowRealSpan (echelonRowSpace D'))ᗮ)‖ ≤ Csup * T
      rw [norm_zero]
      exact hscale.le⟩
  have hchoice : Set.InjOn (fun D => fun i => choice D i)
      (calF (K := K) (l := k) (m := m) (n := n) Csup T ∩
        {D | echelonLambda D' ≤ echelonLambda D}) := by
    apply echelonProjectedChoice_inj_of_real_quotient_bridge
      (B := calF (K := K) (l := k) (m := m) (n := n) Csup T)
      D' (Csup * T) choice lift
    · intro D i hD
      simp only [choice, dif_pos hD]
    · intro D hD
      exact (hlift D hD).2
  exact echelonExtensionCount_le_of_raw_projected_covering_uniform
    (B := calF (K := K) (l := k) (m := m) (n := n) Csup T)
    D' hlm hscale
    (projectedAmbientRowModule_isLatticeCovering_of_ambientRadius
      (echelonRowSpace D')) choice hchoice

/- [derived consequence, paper `le:low_rank_induction`, lines 1431--1480]
   Normalize the preceding manuscript-facing estimate.  The only scale
   change is the elementary fixed-constant bound
   `Csup * T + rho ≤ (Csup + rho) * T` for `T ≥ 1`; the exponent and height
   factor are exactly those displayed in the paper. -/
set_option maxHeartbeats 1000000 in
theorem echelonCalFExtensionCount_le_of_ambient_row_covering_geometry
    {K : Type*} [Field K] [NumberField K]
    {n m k l : ℕ} {Csup T : ℝ}
    (hCsup : 0 < Csup) (hT : 1 ≤ T)
    (D' : EchelonMatrix K l m)
    (_hD' : D' ∈ calF (K := K) (l := l) (m := m) (n := n) Csup T)
    (μ : Measure ((rowRealSpan (echelonRowSpace D'))ᗮ))
    [Measure.IsAddHaarMeasure μ]
    (hcov : ZLattice.covolume
      (projectedAmbientRowModule (K := K) (echelonRowSpace D')) μ =
        (rowSpaceHeight (echelonRowSpace D'))⁻¹)
    (choice : EchelonMatrix K k m → Fin (k - l) →
      {v : projectedAmbientRowModule (K := K) (echelonRowSpace D') |
        ‖(v : (rowRealSpan (echelonRowSpace D'))ᗮ)‖ ≤ Csup * T})
    (hchoice : Set.InjOn (fun D => fun i => choice D i)
      ((calF (K := K) (l := k) (m := m) (n := n) Csup T) ∩
        {D | echelonLambda D' ≤ echelonLambda D})) :
    ∃ C : ℝ, 0 < C ∧
      echelonExtensionCount
          (calF (K := K) (l := k) (m := m) (n := n) Csup T) D' ≤
        C * T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight (echelonRowSpace D') ^ (k - l) := by
  obtain ⟨C₀, hC₀, hbound⟩ :=
    echelonCalFExtensionCount_le_of_ambient_row_covering
      hCsup hT D' _hD' μ hcov choice hchoice
  have hscale : 0 < Csup * T := mul_pos hCsup
    (lt_of_lt_of_le zero_lt_one hT)
  let R : ℝ := latticeCoveringRadius (ambientIntegralRowModule (K := K) m)
  let q : ℕ := m * degree K - l * degree K
  have hlm : l ≤ m := by
    have hdim := Submodule.finrank_le (echelonRowSpace D').1
    rw [echelonRowSpace_rank, Module.finrank_pi_fintype] at hdim
    simpa using hdim
  have hqeq : q = degree K * (m - l) := by
    dsimp [q]
    calc
      m * degree K - l * degree K = (m - l) * degree K :=
        (Nat.sub_mul m l (degree K)).symm
      _ = degree K * (m - l) := Nat.mul_comm _ _
  have hR : 0 ≤ R := by
    dsimp [R]
    exact latticeCoveringRadius_nonneg _
  have hCTR : Csup * T + R ≤ (Csup + R) * T := by
    calc
      Csup * T + R = Csup * T + R * 1 := by ring
      _ ≤ Csup * T + R * T := by
        simpa [add_comm] using add_le_add_left
          (mul_le_mul_of_nonneg_left hT hR) (Csup * T)
      _ = (Csup + R) * T := by ring
  have hbase : 0 ≤ Csup * T + R := by
    exact add_nonneg (le_of_lt hscale) hR
  have hinner :
      C₀ * (Csup * T + R) ^ q * rowSpaceHeight (echelonRowSpace D') ≤
        C₀ * ((Csup + R) ^ q * T ^ q) *
          rowSpaceHeight (echelonRowSpace D') := by
    have hheight : 0 ≤ rowSpaceHeight (echelonRowSpace D') :=
      (rowSpaceHeight_pos (echelonRowSpace D')).le
    calc
      C₀ * (Csup * T + R) ^ q * rowSpaceHeight (echelonRowSpace D') ≤
          C₀ * ((Csup + R) * T) ^ q *
            rowSpaceHeight (echelonRowSpace D') := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hbase hCTR q) hC₀.le) hheight
      _ = C₀ * ((Csup + R) ^ q * T ^ q) *
          rowSpaceHeight (echelonRowSpace D') := by
        rw [mul_pow]
  have hbase_nonneg :
      0 ≤ C₀ * (Csup * T + R) ^ q * rowSpaceHeight (echelonRowSpace D') := by
    exact mul_nonneg (mul_nonneg hC₀.le (pow_nonneg hbase _))
      (rowSpaceHeight_pos (echelonRowSpace D')).le
  have hpow := pow_le_pow_left₀ hbase_nonneg hinner (k - l)
  let C₁ : ℝ := (C₀ * (Csup + R) ^ q) ^ (k - l)
  have hC₁ : 0 < C₁ := by
    dsimp [C₁]
    exact pow_pos (mul_pos hC₀
      (pow_pos (by linarith [hCsup, hR]) _)) _
  have hrewrite :
      (C₀ * ((Csup + R) ^ q * T ^ q) *
          rowSpaceHeight (echelonRowSpace D')) ^ (k - l) =
        C₁ * T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight (echelonRowSpace D') ^ (k - l) := by
    calc
      (C₀ * ((Csup + R) ^ q * T ^ q) *
          rowSpaceHeight (echelonRowSpace D')) ^ (k - l) =
          ((C₀ * (Csup + R) ^ q) * T ^ q *
            rowSpaceHeight (echelonRowSpace D')) ^ (k - l) := by
        congr 1
        ring
      _ = (C₀ * (Csup + R) ^ q) ^ (k - l) *
          (T ^ q) ^ (k - l) *
            rowSpaceHeight (echelonRowSpace D') ^ (k - l) := by
        rw [mul_pow, mul_pow]
      _ = (C₀ * (Csup + R) ^ q) ^ (k - l) *
          T ^ (q * (k - l)) *
            rowSpaceHeight (echelonRowSpace D') ^ (k - l) := by
        rw [← pow_mul]
      _ = C₁ * T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight (echelonRowSpace D') ^ (k - l) := by
        dsimp [C₁]
        rw [hqeq]
        congr 2
        ring
  refine ⟨C₁, hC₁, ?_⟩
  calc
    echelonExtensionCount
          (calF (K := K) (l := k) (m := m) (n := n) Csup T) D' ≤
        (C₀ * (Csup * T + R) ^ q *
          rowSpaceHeight (echelonRowSpace D')) ^ (k - l) := by
      simpa [R, q] using hbound
    _ ≤ (C₀ * ((Csup + R) ^ q * T ^ q) *
          rowSpaceHeight (echelonRowSpace D')) ^ (k - l) := hpow
    _ = C₁ * T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight (echelonRowSpace D') ^ (k - l) := hrewrite

/- [derived consequence, paper `le:low_rank_induction`, lines 1431--1480]
   Normalize the projected-ball estimate independently of how the projected
   choices were obtained.  This is the elementary passage from the
   manuscript's `(T + O(1))` bound to its displayed `T`-power bound. -/
set_option maxHeartbeats 1200000 in
theorem normalize_echelonExtensionCount_bound
    {K : Type*} [Field K] [NumberField K]
    {n m k l : ℕ} {Csup T C₀ R : ℝ}
    (hCsup : 0 < Csup) (hT : 1 ≤ T)
    (D' : EchelonMatrix K l m) (hC₀ : 0 < C₀) (hR : 0 ≤ R)
    (hbound :
      echelonExtensionCount
          (calF (K := K) (l := k) (m := m) (n := n) Csup T) D' ≤
        (C₀ * (Csup * T + R) ^ (m * degree K - l * degree K) *
          rowSpaceHeight (echelonRowSpace D')) ^ (k - l)) :
    ∃ C : ℝ, 0 < C ∧
      echelonExtensionCount
          (calF (K := K) (l := k) (m := m) (n := n) Csup T) D' ≤
        C * T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight (echelonRowSpace D') ^ (k - l) := by
  let q : ℕ := m * degree K - l * degree K
  have hlm : l ≤ m := by
    have hdim := Submodule.finrank_le (echelonRowSpace D').1
    rw [echelonRowSpace_rank, Module.finrank_pi_fintype] at hdim
    simpa using hdim
  have hqeq : q = degree K * (m - l) := by
    dsimp [q]
    calc
      m * degree K - l * degree K = (m - l) * degree K :=
        (Nat.sub_mul m l (degree K)).symm
      _ = degree K * (m - l) := Nat.mul_comm _ _
  have hscale : 0 < Csup * T := mul_pos hCsup
    (lt_of_lt_of_le zero_lt_one hT)
  have hCTR : Csup * T + R ≤ (Csup + R) * T := by
    calc
      Csup * T + R = Csup * T + R * 1 := by ring
      _ ≤ Csup * T + R * T := by
        simpa [add_comm] using add_le_add_left
          (mul_le_mul_of_nonneg_left hT hR) (Csup * T)
      _ = (Csup + R) * T := by ring
  have hbase : 0 ≤ Csup * T + R := by
    exact add_nonneg (le_of_lt hscale) hR
  have hinner :
      C₀ * (Csup * T + R) ^ q * rowSpaceHeight (echelonRowSpace D') ≤
        C₀ * ((Csup + R) ^ q * T ^ q) *
          rowSpaceHeight (echelonRowSpace D') := by
    have hheight : 0 ≤ rowSpaceHeight (echelonRowSpace D') :=
      (rowSpaceHeight_pos (echelonRowSpace D')).le
    calc
      C₀ * (Csup * T + R) ^ q * rowSpaceHeight (echelonRowSpace D') ≤
          C₀ * ((Csup + R) * T) ^ q *
            rowSpaceHeight (echelonRowSpace D') := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hbase hCTR q) hC₀.le) hheight
      _ = C₀ * ((Csup + R) ^ q * T ^ q) *
          rowSpaceHeight (echelonRowSpace D') := by
        rw [mul_pow]
  have hbase_nonneg :
      0 ≤ C₀ * (Csup * T + R) ^ q *
        rowSpaceHeight (echelonRowSpace D') := by
    exact mul_nonneg (mul_nonneg hC₀.le (pow_nonneg hbase _))
      (rowSpaceHeight_pos (echelonRowSpace D')).le
  have hpow := pow_le_pow_left₀ hbase_nonneg hinner (k - l)
  let C₁ : ℝ := (C₀ * (Csup + R) ^ q) ^ (k - l)
  have hC₁ : 0 < C₁ := by
    dsimp [C₁]
    exact pow_pos (mul_pos hC₀
      (pow_pos (by linarith [hCsup, hR]) _)) _
  have hrewrite :
      (C₀ * ((Csup + R) ^ q * T ^ q) *
          rowSpaceHeight (echelonRowSpace D')) ^ (k - l) =
        C₁ * T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight (echelonRowSpace D') ^ (k - l) := by
    calc
      (C₀ * ((Csup + R) ^ q * T ^ q) *
          rowSpaceHeight (echelonRowSpace D')) ^ (k - l) =
          ((C₀ * (Csup + R) ^ q) * T ^ q *
            rowSpaceHeight (echelonRowSpace D')) ^ (k - l) := by
        congr 1
        ring
      _ = (C₀ * (Csup + R) ^ q) ^ (k - l) *
          (T ^ q) ^ (k - l) *
            rowSpaceHeight (echelonRowSpace D') ^ (k - l) := by
        rw [mul_pow, mul_pow]
      _ = (C₀ * (Csup + R) ^ q) ^ (k - l) *
          T ^ (q * (k - l)) *
            rowSpaceHeight (echelonRowSpace D') ^ (k - l) := by
        rw [← pow_mul]
      _ = C₁ * T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight (echelonRowSpace D') ^ (k - l) := by
        dsimp [C₁]
        rw [hqeq]
        congr 2
        ring
  refine ⟨C₁, hC₁, ?_⟩
  calc
    echelonExtensionCount
          (calF (K := K) (l := k) (m := m) (n := n) Csup T) D' ≤
        (C₀ * (Csup * T + R) ^ q *
          rowSpaceHeight (echelonRowSpace D')) ^ (k - l) := by
      simpa [q] using hbound
    _ ≤ (C₀ * ((Csup + R) ^ q * T ^ q) *
          rowSpaceHeight (echelonRowSpace D')) ^ (k - l) := hpow
    _ = C₁ * T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight (echelonRowSpace D') ^ (k - l) := hrewrite

/- [derived consequence, paper `le:low_rank_induction`, lines 1475--1480]
   Deterministic form of the preceding elementary normalization.  Keeping
   `C₀` in the conclusion records that the resulting coefficient is fixed
   before the lower row space or the scale `T` is chosen. -/
set_option maxHeartbeats 1000000 in
theorem normalize_echelonExtensionCount_bound_uniform
    {K : Type*} [Field K] [NumberField K]
    {n m k l : ℕ} {Csup T C₀ R : ℝ}
    (hCsup : 0 < Csup) (hT : 1 ≤ T)
    (D' : EchelonMatrix K l m) (hC₀ : 0 < C₀) (hR : 0 ≤ R)
    (hbound :
      echelonExtensionCount
          (calF (K := K) (l := k) (m := m) (n := n) Csup T) D' ≤
        (C₀ * (Csup * T + R) ^ (m * degree K - l * degree K) *
          rowSpaceHeight (echelonRowSpace D')) ^ (k - l)) :
    echelonExtensionCount
        (calF (K := K) (l := k) (m := m) (n := n) Csup T) D' ≤
      (C₀ * (Csup + R) ^ (m * degree K - l * degree K)) ^ (k - l) *
        T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight (echelonRowSpace D') ^ (k - l) := by
  let q : ℕ := m * degree K - l * degree K
  have hlm : l ≤ m := by
    have hdim := Submodule.finrank_le (echelonRowSpace D').1
    rw [echelonRowSpace_rank, Module.finrank_pi_fintype] at hdim
    simpa using hdim
  have hqeq : q = degree K * (m - l) := by
    dsimp [q]
    calc
      m * degree K - l * degree K = (m - l) * degree K :=
        (Nat.sub_mul m l (degree K)).symm
      _ = degree K * (m - l) := Nat.mul_comm _ _
  have hscale : 0 < Csup * T := mul_pos hCsup
    (lt_of_lt_of_le zero_lt_one hT)
  have hCTR : Csup * T + R ≤ (Csup + R) * T := by
    calc
      Csup * T + R = Csup * T + R * 1 := by ring
      _ ≤ Csup * T + R * T := by
        simpa [add_comm] using add_le_add_left
          (mul_le_mul_of_nonneg_left hT hR) (Csup * T)
      _ = (Csup + R) * T := by ring
  have hbase : 0 ≤ Csup * T + R := by
    exact add_nonneg (le_of_lt hscale) hR
  have hinner :
      C₀ * (Csup * T + R) ^ q * rowSpaceHeight (echelonRowSpace D') ≤
        C₀ * ((Csup + R) ^ q * T ^ q) *
          rowSpaceHeight (echelonRowSpace D') := by
    have hheight : 0 ≤ rowSpaceHeight (echelonRowSpace D') :=
      (rowSpaceHeight_pos (echelonRowSpace D')).le
    calc
      C₀ * (Csup * T + R) ^ q * rowSpaceHeight (echelonRowSpace D') ≤
          C₀ * ((Csup + R) * T) ^ q *
            rowSpaceHeight (echelonRowSpace D') := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hbase hCTR q) hC₀.le) hheight
      _ = C₀ * ((Csup + R) ^ q * T ^ q) *
          rowSpaceHeight (echelonRowSpace D') := by
        rw [mul_pow]
  have hbase_nonneg :
      0 ≤ C₀ * (Csup * T + R) ^ q *
        rowSpaceHeight (echelonRowSpace D') := by
    exact mul_nonneg (mul_nonneg hC₀.le (pow_nonneg hbase _))
      (rowSpaceHeight_pos (echelonRowSpace D')).le
  have hpow := pow_le_pow_left₀ hbase_nonneg hinner (k - l)
  let C₁ : ℝ := (C₀ * (Csup + R) ^ q) ^ (k - l)
  have hrewrite :
      (C₀ * ((Csup + R) ^ q * T ^ q) *
          rowSpaceHeight (echelonRowSpace D')) ^ (k - l) =
        C₁ * T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight (echelonRowSpace D') ^ (k - l) := by
    calc
      (C₀ * ((Csup + R) ^ q * T ^ q) *
          rowSpaceHeight (echelonRowSpace D')) ^ (k - l) =
          ((C₀ * (Csup + R) ^ q) * T ^ q *
            rowSpaceHeight (echelonRowSpace D')) ^ (k - l) := by
        congr 1
        ring
      _ = (C₀ * (Csup + R) ^ q) ^ (k - l) *
          (T ^ q) ^ (k - l) *
            rowSpaceHeight (echelonRowSpace D') ^ (k - l) := by
        rw [mul_pow, mul_pow]
      _ = (C₀ * (Csup + R) ^ q) ^ (k - l) *
          T ^ (q * (k - l)) *
            rowSpaceHeight (echelonRowSpace D') ^ (k - l) := by
        rw [← pow_mul]
      _ = C₁ * T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight (echelonRowSpace D') ^ (k - l) := by
        dsimp [C₁]
        rw [hqeq]
        congr 2
        ring
  calc
    echelonExtensionCount
          (calF (K := K) (l := k) (m := m) (n := n) Csup T) D' ≤
        (C₀ * (Csup * T + R) ^ q *
          rowSpaceHeight (echelonRowSpace D')) ^ (k - l) := by
      simpa [q] using hbound
    _ ≤ (C₀ * ((Csup + R) ^ q * T ^ q) *
          rowSpaceHeight (echelonRowSpace D')) ^ (k - l) := hpow
    _ = (C₀ * (Csup + R) ^ (m * degree K - l * degree K)) ^ (k - l) *
          T ^ (degree K * (k - l) * (m - l)) *
            rowSpaceHeight (echelonRowSpace D') ^ (k - l) := by
      simpa [C₁, q] using hrewrite

/- [paper, `le:low_rank_induction`, lines 1431--1480] The complete
   manuscript-facing extension-count estimate.  The projected lattice's
   covolume identity is retained as an explicit hypothesis because the exact
   number-field height normalization is recorded as Lean infrastructure work
   in `notes/formalization-issues.md`; the manuscript's normalized identity
   itself is valid. -/
set_option maxHeartbeats 1600000 in
theorem echelonCalFExtensionCount_le_of_low_rank_induction
    {K : Type*} [Field K] [NumberField K]
    {n m k l : ℕ} (hl : 1 ≤ l) (hlk : l < k)
    {Csup T : ℝ} (hCsup : 0 < Csup) (hT : 1 ≤ T)
    (D' : EchelonMatrix K l m)
    (hD' : D' ∈ calF (K := K) (l := l) (m := m) (n := n) Csup T)
    (μ : Measure ((rowRealSpan (echelonRowSpace D'))ᗮ))
    [Measure.IsAddHaarMeasure μ]
    (hcov : ZLattice.covolume
      (projectedAmbientRowModule (K := K) (echelonRowSpace D')) μ =
        (rowSpaceHeight (echelonRowSpace D'))⁻¹) :
    ∃ C : ℝ, 0 < C ∧
      echelonExtensionCount
          (calF (K := K) (l := k) (m := m) (n := n) Csup T) D' ≤
        C * T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight (echelonRowSpace D') ^ (k - l) := by
  obtain ⟨C₀, hC₀, hbound⟩ :=
    echelonCalFExtensionCount_le_of_constructed_complement
      hCsup hT D' hD' μ hcov
  exact normalize_echelonExtensionCount_bound hCsup hT D' hC₀
    (latticeCoveringRadius_nonneg
      (ambientIntegralRowModule (K := K) m)) hbound

/- [derived consequence, paper `le:low_rank_induction`, lines 1431--1480]
   Raw-Euclidean complete extension estimate.  This follows the same
   complement-lift construction and the paper's elementary radius
   normalization, while keeping its raw-height status visible in the theorem
   name rather than silently identifying it with the exact paper metric. -/
set_option maxHeartbeats 1600000 in
theorem echelonCalFExtensionCount_le_of_raw_low_rank_induction
    {K : Type*} [Field K] [NumberField K]
    {n m k l : ℕ} (_hl : 1 ≤ l) (_hlk : l < k)
    {Csup T : ℝ} (hCsup : 0 < Csup) (hT : 1 ≤ T)
    (D' : EchelonMatrix K l m)
    (hD' : D' ∈ calF (K := K) (l := l) (m := m) (n := n) Csup T) :
    ∃ C : ℝ, 0 < C ∧
      echelonExtensionCount
          (calF (K := K) (l := k) (m := m) (n := n) Csup T) D' ≤
        C * T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight (echelonRowSpace D') ^ (k - l) := by
  obtain ⟨C₀, hC₀, hbound⟩ :=
    echelonCalFExtensionCount_le_of_raw_constructed_complement
      hCsup hT D' hD'
  exact normalize_echelonExtensionCount_bound hCsup hT D' hC₀
    (latticeCoveringRadius_nonneg
      (ambientIntegralRowModule (K := K) m)) hbound

/- [derived consequence, paper `le:low_rank_induction`, lines 1431--1481]
   Uniform raw-Euclidean complete extension estimate.  The coefficient is
   displayed rather than existentially quantified so it is fixed by the
   field, dimensions, and support radius before `D'` and `T` vary.  The
   paper's hypotheses `l < k ≤ m` give the displayed `l < m` premise. -/
set_option maxHeartbeats 1600000 in
theorem echelonCalFExtensionCount_le_of_raw_low_rank_induction_uniform
    {K : Type*} [Field K] [NumberField K]
    {n m k l : ℕ} (hlm : l < m)
    {Csup T : ℝ} (hCsup : 0 < Csup) (hT : 1 ≤ T)
    (D' : EchelonMatrix K l m)
    (hD' : D' ∈ calF (K := K) (l := l) (m := m) (n := n) Csup T) :
    echelonExtensionCount
        (calF (K := K) (l := k) (m := m) (n := n) Csup T) D' ≤
      ((euclideanUnitBallVolume (m * degree K - l * degree K) *
        (ZLattice.covolume (ambientIntegralRowModule (K := K) m)
          (μHE[Module.finrank ℝ (RowVector K m)]))⁻¹) *
        (Csup + latticeCoveringRadius
          (ambientIntegralRowModule (K := K) m)) ^
            (m * degree K - l * degree K)) ^ (k - l) *
        T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight (echelonRowSpace D') ^ (k - l) := by
  have hC₀ : 0 <
      euclideanUnitBallVolume (m * degree K - l * degree K) *
        (ZLattice.covolume (ambientIntegralRowModule (K := K) m)
          (μHE[Module.finrank ℝ (RowVector K m)]))⁻¹ := by
    exact mul_pos (euclideanUnitBallVolume_pos _)
      (inv_pos.mpr
        (ZLattice.covolume_pos (ambientIntegralRowModule (K := K) m)
          (μHE[Module.finrank ℝ (RowVector K m)])))
  have hbound :=
    echelonCalFExtensionCount_le_of_raw_constructed_complement_uniform
      (k := k) hCsup hT D' hlm hD'
  exact normalize_echelonExtensionCount_bound_uniform
    (C₀ := euclideanUnitBallVolume (m * degree K - l * degree K) *
      (ZLattice.covolume (ambientIntegralRowModule (K := K) m)
        (μHE[Module.finrank ℝ (RowVector K m)]))⁻¹)
    (R := latticeCoveringRadius (ambientIntegralRowModule (K := K) m))
    hCsup hT D' hC₀
    (latticeCoveringRadius_nonneg
      (ambientIntegralRowModule (K := K) m)) hbound

/- [derived consequence, paper `le:low_rank_induction`, lines 1431--1480]
   Transfer the manuscript-facing extension estimate to the row-space count
   used by the lower-rank summation.  The representative is recovered through
   the proved echelon/Grassmannian equivalence; no new choice of notation or
   counting argument is introduced here. -/
set_option maxHeartbeats 1600000 in
theorem rowSpaceExtensionCount_image_calF_le_of_low_rank_induction
    {K : Type*} [Field K] [NumberField K]
    {n m k l : ℕ} (hl : 1 ≤ l) (hlk : l < k)
    {Csup T : ℝ} (hCsup : 0 < Csup) (hT : 1 ≤ T)
    (W : Grassmannian K m l)
    (hW : W ∈ echelonRowSpace (K := K) ''
      calF (K := K) (l := l) (m := m) (n := n) Csup T)
    (μ : Measure ((rowRealSpan W)ᗮ))
    [Measure.IsAddHaarMeasure μ]
    (hcov : ZLattice.covolume
      (projectedAmbientRowModule (K := K) W) μ =
        (rowSpaceHeight W)⁻¹) :
    ∃ C : ℝ, 0 < C ∧
      rowSpaceExtensionCount
          (echelonRowSpace (K := K) ''
            calF (K := K) (l := k) (m := m) (n := n) Csup T) W ≤
        C * T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight W ^ (k - l) := by
  rcases hW with ⟨D', hD', hD'W⟩
  subst W
  obtain ⟨C, hC, hcount⟩ :=
    echelonCalFExtensionCount_le_of_low_rank_induction
      hl hlk hCsup hT D' hD' μ hcov
  have hcount' :
      rowSpaceExtensionCount
          (echelonRowSpace (K := K) ''
            calF (K := K) (l := k) (m := m) (n := n) Csup T)
          (echelonRowSpace D') ≤
        C * T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight (echelonRowSpace D') ^ (k - l) := by
    rw [← echelonExtensionCount_eq_rowSpaceExtensionCount_image]
    exact hcount
  exact ⟨C, hC, hcount'⟩

/- [derived consequence, paper `le:low_rank_induction`, lines 1431--1480]
   Raw-Euclidean row-space form of the extension bound.  The transfer through
   the echelon/Grassmannian trijection is unchanged from the manuscript-facing
   proof above; it merely invokes the raw complete extension estimate. -/
set_option maxHeartbeats 1600000 in
theorem rowSpaceExtensionCount_image_calF_le_of_raw_low_rank_induction
    {K : Type*} [Field K] [NumberField K]
    {n m k l : ℕ} (hl : 1 ≤ l) (hlk : l < k)
    {Csup T : ℝ} (hCsup : 0 < Csup) (hT : 1 ≤ T)
    (W : Grassmannian K m l)
    (hW : W ∈ echelonRowSpace (K := K) ''
      calF (K := K) (l := l) (m := m) (n := n) Csup T) :
    ∃ C : ℝ, 0 < C ∧
      rowSpaceExtensionCount
          (echelonRowSpace (K := K) ''
            calF (K := K) (l := k) (m := m) (n := n) Csup T) W ≤
        C * T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight W ^ (k - l) := by
  rcases hW with ⟨D', hD', hD'W⟩
  subst W
  obtain ⟨C, hC, hcount⟩ :=
    echelonCalFExtensionCount_le_of_raw_low_rank_induction
      hl hlk hCsup hT D' hD'
  have hcount' :
      rowSpaceExtensionCount
          (echelonRowSpace (K := K) ''
            calF (K := K) (l := k) (m := m) (n := n) Csup T)
          (echelonRowSpace D') ≤
        C * T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight (echelonRowSpace D') ^ (k - l) := by
    rw [← echelonExtensionCount_eq_rowSpaceExtensionCount_image]
    exact hcount
  exact ⟨C, hC, hcount'⟩

/- [derived consequence, paper `le:low_rank_induction`, lines 1431--1481]
   Row-space form of the fixed-coefficient raw extension bound.  The only
   operation here is the proved correspondence between the echelon
   representative and its row space; in particular, the coefficient is not
   reselected over a finite family. -/
set_option maxHeartbeats 1600000 in
theorem rowSpaceExtensionCount_image_calF_le_of_raw_low_rank_induction_uniform
    {K : Type*} [Field K] [NumberField K]
    {n m k l : ℕ} (hlm : l < m)
    {Csup T : ℝ} (hCsup : 0 < Csup) (hT : 1 ≤ T)
    (W : Grassmannian K m l)
    (hW : W ∈ echelonRowSpace (K := K) ''
      calF (K := K) (l := l) (m := m) (n := n) Csup T) :
    rowSpaceExtensionCount
        (echelonRowSpace (K := K) ''
          calF (K := K) (l := k) (m := m) (n := n) Csup T) W ≤
      ((euclideanUnitBallVolume (m * degree K - l * degree K) *
        (ZLattice.covolume (ambientIntegralRowModule (K := K) m)
          (μHE[Module.finrank ℝ (RowVector K m)]))⁻¹) *
        (Csup + latticeCoveringRadius
          (ambientIntegralRowModule (K := K) m)) ^
            (m * degree K - l * degree K)) ^ (k - l) *
        T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight W ^ (k - l) := by
  rcases hW with ⟨D', hD', hD'W⟩
  subst W
  have hcount :=
    echelonCalFExtensionCount_le_of_raw_low_rank_induction_uniform
      (k := k) hlm hCsup hT D' hD'
  rw [← echelonExtensionCount_eq_rowSpaceExtensionCount_image]
  exact hcount

/- [derived consequence, paper `le:low_rank_induction`, lines 1431--1480]
   The extension-count constant can be chosen uniformly on the finite family
   of lower row spaces used in the manuscript's height summation.  The
   projected-lattice covolume identity remains a premise for every member of
   the family: this is finite-family bookkeeping, not a replacement of the
   paper's normalization. -/
set_option maxHeartbeats 1600000 in
theorem exists_uniform_rowSpaceExtensionCount_image_calF_le_of_low_rank_induction
    {K : Type*} [Field K] [NumberField K]
    {n m k l : ℕ} (hl : 1 ≤ l) (hlk : l < k)
    {Csup T : ℝ} (hCsup : 0 < Csup) (hT : 1 ≤ T)
    (S : Set (Grassmannian K m l)) (hS : S.Finite)
    (hS_image : ∀ W ∈ S, W ∈ echelonRowSpace (K := K) ''
      calF (K := K) (l := l) (m := m) (n := n) Csup T)
    (μ : ∀ W : S, Measure ((rowRealSpan W.1)ᗮ))
    (hhaar : ∀ W, Measure.IsAddHaarMeasure (μ W))
    (hcov : ∀ W : S, ZLattice.covolume
      (projectedAmbientRowModule (K := K) W.1) (μ W) =
        (rowSpaceHeight W.1)⁻¹) :
    ∃ C : ℝ, 0 < C ∧ ∀ W ∈ S,
      rowSpaceExtensionCount
          (echelonRowSpace (K := K) ''
            calF (K := K) (l := k) (m := m) (n := n) Csup T) W ≤
        C * T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight W ^ (k - l) := by
  classical
  let F : Finset (Grassmannian K m l) := hS.toFinset
  have hF : (F : Set (Grassmannian K m l)) = S := hS.coe_toFinset
  choose c hc hbound using fun W : F => by
    let wS : S := ⟨W.1, by
      rw [← hF]
      exact W.2⟩
    letI : Measure.IsAddHaarMeasure (μ wS) := hhaar wS
    simpa [wS] using
      (rowSpaceExtensionCount_image_calF_le_of_low_rank_induction
        hl hlk hCsup hT W.1 (hS_image W.1 wS.2) (μ wS) (hcov wS))
  let C : ℝ := 1 + ∑ W ∈ F.attach, c W
  have hsum_nonneg : 0 ≤ ∑ W ∈ F.attach, c W := by
    exact Finset.sum_nonneg (fun W _ => (hc W).le)
  have hC : 0 < C := by
    dsimp [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro W hW
  let wF : F := ⟨W, by
    change W ∈ (F : Set (Grassmannian K m l))
    rw [hF]
    exact hW⟩
  have hc_sum : c wF ≤ ∑ U ∈ F.attach, c U := by
    exact Finset.single_le_sum (fun U _ => (hc U).le)
      (F.mem_attach wF)
  have hc_uniform : c wF ≤ C := by
    dsimp [C]
    linarith
  have hfactor :
      0 ≤ T ^ (degree K * (k - l) * (m - l)) *
        rowSpaceHeight W ^ (k - l) := by
    exact mul_nonneg
      (pow_nonneg (le_trans zero_le_one hT) _)
      (pow_nonneg (rowSpaceHeight_pos W).le _)
  have hboundW :
      rowSpaceExtensionCount
          (echelonRowSpace (K := K) ''
            calF (K := K) (l := k) (m := m) (n := n) Csup T) W ≤
        c wF * T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight W ^ (k - l) := by
    simpa [wF] using hbound wF
  calc
    rowSpaceExtensionCount
          (echelonRowSpace (K := K) ''
            calF (K := K) (l := k) (m := m) (n := n) Csup T) W ≤
        c wF * T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight W ^ (k - l) := hboundW
    _ = c wF * (T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight W ^ (k - l)) := by ring
    _ ≤ C * (T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight W ^ (k - l)) :=
      mul_le_mul_of_nonneg_right hc_uniform hfactor
    _ = C * T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight W ^ (k - l) := by ring

/- [derived consequence, paper `le:low_rank_induction`, lines 1431--1480]
   Uniformize the raw-metric extension constants over the finite lower-rank
   row-space family.  This is exactly the finite-family bookkeeping used
   above, now with no pointwise projected-covolume hypothesis. -/
set_option maxHeartbeats 1600000 in
theorem exists_uniform_rowSpaceExtensionCount_image_calF_le_of_raw_low_rank_induction
    {K : Type*} [Field K] [NumberField K]
    {n m k l : ℕ} (hl : 1 ≤ l) (hlk : l < k)
    {Csup T : ℝ} (hCsup : 0 < Csup) (hT : 1 ≤ T)
    (S : Set (Grassmannian K m l)) (hS : S.Finite)
    (hS_image : ∀ W ∈ S, W ∈ echelonRowSpace (K := K) ''
      calF (K := K) (l := l) (m := m) (n := n) Csup T) :
    ∃ C : ℝ, 0 < C ∧ ∀ W ∈ S,
      rowSpaceExtensionCount
          (echelonRowSpace (K := K) ''
            calF (K := K) (l := k) (m := m) (n := n) Csup T) W ≤
        C * T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight W ^ (k - l) := by
  classical
  let F : Finset (Grassmannian K m l) := hS.toFinset
  have hF : (F : Set (Grassmannian K m l)) = S := hS.coe_toFinset
  choose c hc hbound using fun W : F => by
    let wS : S := ⟨W.1, by
      rw [← hF]
      exact W.2⟩
    simpa [wS] using
      (rowSpaceExtensionCount_image_calF_le_of_raw_low_rank_induction
        hl hlk hCsup hT W.1 (hS_image W.1 wS.2))
  let C : ℝ := 1 + ∑ W ∈ F.attach, c W
  have hsum_nonneg : 0 ≤ ∑ W ∈ F.attach, c W := by
    exact Finset.sum_nonneg (fun W _ => (hc W).le)
  have hC : 0 < C := by
    dsimp [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro W hW
  let wF : F := ⟨W, by
    change W ∈ (F : Set (Grassmannian K m l))
    rw [hF]
    exact hW⟩
  have hc_sum : c wF ≤ ∑ U ∈ F.attach, c U := by
    exact Finset.single_le_sum (fun U _ => (hc U).le)
      (F.mem_attach wF)
  have hc_uniform : c wF ≤ C := by
    dsimp [C]
    linarith
  have hfactor :
      0 ≤ T ^ (degree K * (k - l) * (m - l)) *
        rowSpaceHeight W ^ (k - l) := by
    exact mul_nonneg
      (pow_nonneg (le_trans zero_le_one hT) _)
      (pow_nonneg (rowSpaceHeight_pos W).le _)
  have hboundW :
      rowSpaceExtensionCount
          (echelonRowSpace (K := K) ''
            calF (K := K) (l := k) (m := m) (n := n) Csup T) W ≤
        c wF * T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight W ^ (k - l) := by
    simpa [wF] using hbound wF
  calc
    rowSpaceExtensionCount
          (echelonRowSpace (K := K) ''
            calF (K := K) (l := k) (m := m) (n := n) Csup T) W ≤
        c wF * T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight W ^ (k - l) := hboundW
    _ = c wF * (T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight W ^ (k - l)) := by ring
    _ ≤ C * (T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight W ^ (k - l)) :=
      mul_le_mul_of_nonneg_right hc_uniform hfactor
    _ = C * T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight W ^ (k - l) := by ring

/- [derived consequence, paper `le:low_rank_terms`, lines 1513--1577]
   This combines the two displayed pointwise estimates for the manuscript's
   exact families `𝓕_l(T)` and `𝓕_k(T)`.  The support inclusion makes the
   inner rank-`l` sum vanish away from `𝓕_l(T)`; the finite-family constants
   are then inserted into the paper's three-case Abel estimate.  The
   projected-covolume identity is still an explicit premise, so this does not
   conceal the unresolved Lean normalization bridge recorded in
   `notes/formalization-issues.md`. -/
set_option maxHeartbeats 2400000 in
theorem exists_echelon_calF_lowerStratumTerm_abs_le_of_radius
    {K : Type*} [Field K] [NumberField K]
    {n m k l : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    (hnm : m < n) (hkm : k ≤ m) (hl : 1 ≤ l) (hlk : l < k)
    {Csup T C_R : ℝ} (hCsup : 0 < Csup) (hT : 1 ≤ T) (hC_R : 0 ≤ C_R)
    (hSupport : ∀ A : IntegralMatrix K n m,
      f (T⁻¹ • embedMatrix A) ≠ 0 →
        ‖embedMatrix A‖ ≤ Csup * T)
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := l)) m)
    {b : ℕ} (hb : 1 ≤ b)
    (hS_bound : ∀ W ∈ echelonRowSpace (K := K) ''
      calF (K := K) (l := l) (m := m) (n := n) Csup T,
      rowSpaceHeight W ≤ (b : ℝ))
    (hRadius : ∀ W ∈ echelonRowSpace (K := K) ''
      calF (K := K) (l := l) (m := m) (n := n) Csup T,
      rowMatrixFundamentalRadius W n / T ≤ C_R)
    (μ : ∀ W : (echelonRowSpace (K := K) ''
      calF (K := K) (l := l) (m := m) (n := n) Csup T),
      Measure ((rowRealSpan W.1)ᗮ))
    (hhaar : ∀ W, Measure.IsAddHaarMeasure (μ W))
    (hcov : ∀ W : (echelonRowSpace (K := K) ''
      calF (K := K) (l := l) (m := m) (n := n) Csup T),
      ZLattice.covolume (projectedAmbientRowModule (K := K) W.1) (μ W) =
        (rowSpaceHeight W.1)⁻¹) :
    ∃ C₁ C₂ D : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < D ∧
      |rowSpaceLowerStratumTerm (l := l)
          (echelonRowSpace (K := K) ''
            calF (K := K) (l := k) (m := m) (n := n) Csup T) f T| /
          T ^ (k * n * degree K) ≤
        if n + l - k < m then
          C₁ * C₂ * D * T ^ alpha_l n m k l (degree K) *
            (b : ℝ) ^ ((m - (n + l - k) : ℕ) : ℝ)
        else if m = n + l - k then
          C₁ * C₂ * D * T ^ alpha_l n m k l (degree K) *
            (1 + Real.log (b : ℝ))
        else C₁ * C₂ * D * T ^ alpha_l n m k l (degree K) := by
  let S : Set (Grassmannian K m l) := echelonRowSpace (K := K) ''
    calF (K := K) (l := l) (m := m) (n := n) Csup T
  let B : Set (Grassmannian K m k) := echelonRowSpace (K := K) ''
    calF (K := K) (l := k) (m := m) (n := n) Csup T
  have hS : S.Finite := by
    dsimp [S]
    exact (finite_calF (K := K) (l := l) (m := m) (n := n)
      (Csup := Csup) (T := T)).image _
  have hB : B.Finite := by
    dsimp [B]
    exact (finite_calF (K := K) (l := k) (m := m) (n := n)
      (Csup := Csup) (T := T)).image _
  letI : Fintype B := hB.fintype
  have hS_image : ∀ W ∈ S, W ∈ echelonRowSpace (K := K) ''
      calF (K := K) (l := l) (m := m) (n := n) Csup T := by
    intro W hW
    simpa [S] using hW
  have hS_bound' : ∀ W ∈ S, rowSpaceHeight W ≤ (b : ℝ) := by
    intro W hW
    exact hS_bound W (by simpa [S] using hW)
  have hRadius' : ∀ W ∈ S, rowMatrixFundamentalRadius W n / T ≤ C_R := by
    intro W hW
    exact hRadius W (by simpa [S] using hW)
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hactive : activeRowSpaces (K := K) (k := l) f T ⊆ S := by
    intro W hW
    simpa [S] using
      (activeRowSpaces_subset_echelon_calF_image_of_support_bound
        f hTpos hSupport hW)
  have hzero : ∀ W ∉ S, rowSpaceRankSum W f T = 0 := by
    intro W hW
    apply rowSpaceRankSum_eq_zero_of_not_mem_activeRowSpaces W f T
    intro hWactive
    exact hW (hactive hWactive)
  obtain ⟨C₁, hC₁, hc⟩ :=
    exists_uniform_rowSpaceExtensionCount_image_calF_le_of_low_rank_induction
      hl hlk hCsup hT S hS hS_image μ hhaar hcov
  have hlpos : 0 < l := by omega
  have hn : 0 < n := by omega
  obtain ⟨C₂, hC₂, hg⟩ :=
    Admissible.exists_uniform_rowSpaceRankSum_abs_le_of_radius_global
      (f := f) h_f hlpos hn hT hC_R S hRadius'
  obtain ⟨D, hD, hbound⟩ :=
    rowSpaceLowerStratumTerm_abs_le_of_bounds (d := degree K)
      B f hT hnm hkm hl hlk hcount hb S hS hS_bound'
      (fun W hW => by simpa [B] using hc W hW)
      (fun W hW => by
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hg W hW)
      hzero hC₁.le hC₂.le
  refine ⟨C₁, C₂, D, hC₁, hC₂, hD, ?_⟩
  simpa [B] using hbound

/- [derived consequence, paper `le:low_rank_terms`, lines 1513--1577]
   Raw-Euclidean form of the lower-stratum estimate.  It preserves the
   manuscript's families `𝓕_l(T)`, `𝓕_k(T)`, cutoff `b`, three-case Abel
   bound, and intrinsic `sqrt n * rho(Λ_D)` radius.  The only changed input
   is the now-proved raw extension-count bridge, so no projected paper-metric
   covolume hypothesis is required here. -/
set_option maxHeartbeats 2400000 in
theorem exists_echelon_calF_lowerStratumTerm_abs_le_of_raw_radius
    {K : Type*} [Field K] [NumberField K]
    {n m k l : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    (hnm : m < n) (hkm : k ≤ m) (hl : 1 ≤ l) (hlk : l < k)
    {Csup T C_R : ℝ} (hCsup : 0 < Csup) (hT : 1 ≤ T) (hC_R : 0 ≤ C_R)
    (hSupport : ∀ A : IntegralMatrix K n m,
      f (T⁻¹ • embedMatrix A) ≠ 0 →
        ‖embedMatrix A‖ ≤ Csup * T)
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := l)) m)
    {b : ℕ} (hb : 1 ≤ b)
    (hS_bound : ∀ W ∈ echelonRowSpace (K := K) ''
      calF (K := K) (l := l) (m := m) (n := n) Csup T,
      rowSpaceHeight W ≤ (b : ℝ))
    (hRadius : ∀ W ∈ echelonRowSpace (K := K) ''
      calF (K := K) (l := l) (m := m) (n := n) Csup T,
      (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice W)) / T ≤ C_R) :
    ∃ C₁ C₂ D : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < D ∧
      |rowSpaceLowerStratumTerm (l := l)
          (echelonRowSpace (K := K) ''
            calF (K := K) (l := k) (m := m) (n := n) Csup T) f T| /
          T ^ (k * n * degree K) ≤
        if n + l - k < m then
          C₁ * C₂ * D * T ^ alpha_l n m k l (degree K) *
            (b : ℝ) ^ ((m - (n + l - k) : ℕ) : ℝ)
        else if m = n + l - k then
          C₁ * C₂ * D * T ^ alpha_l n m k l (degree K) *
            (1 + Real.log (b : ℝ))
        else C₁ * C₂ * D * T ^ alpha_l n m k l (degree K) := by
  let S : Set (Grassmannian K m l) := echelonRowSpace (K := K) ''
    calF (K := K) (l := l) (m := m) (n := n) Csup T
  let B : Set (Grassmannian K m k) := echelonRowSpace (K := K) ''
    calF (K := K) (l := k) (m := m) (n := n) Csup T
  have hS : S.Finite := by
    dsimp [S]
    exact (finite_calF (K := K) (l := l) (m := m) (n := n)
      (Csup := Csup) (T := T)).image _
  have hB : B.Finite := by
    dsimp [B]
    exact (finite_calF (K := K) (l := k) (m := m) (n := n)
      (Csup := Csup) (T := T)).image _
  letI : Fintype B := hB.fintype
  have hS_image : ∀ W ∈ S, W ∈ echelonRowSpace (K := K) ''
      calF (K := K) (l := l) (m := m) (n := n) Csup T := by
    intro W hW
    simpa [S] using hW
  have hS_bound' : ∀ W ∈ S, rowSpaceHeight W ≤ (b : ℝ) := by
    intro W hW
    exact hS_bound W (by simpa [S] using hW)
  have hRadius' : ∀ W ∈ S,
      (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice W)) / T ≤ C_R := by
    intro W hW
    exact hRadius W (by simpa [S] using hW)
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hactive : activeRowSpaces (K := K) (k := l) f T ⊆ S := by
    intro W hW
    simpa [S] using
      (activeRowSpaces_subset_echelon_calF_image_of_support_bound
        f hTpos hSupport hW)
  have hzero : ∀ W ∉ S, rowSpaceRankSum W f T = 0 := by
    intro W hW
    apply rowSpaceRankSum_eq_zero_of_not_mem_activeRowSpaces W f T
    intro hWactive
    exact hW (hactive hWactive)
  have hlm : l < m := lt_of_lt_of_le hlk hkm
  have hR : 0 ≤ latticeCoveringRadius
      (ambientIntegralRowModule (K := K) m) :=
    latticeCoveringRadius_nonneg _
  let C₁ : ℝ :=
    ((euclideanUnitBallVolume (m * degree K - l * degree K) *
      (ZLattice.covolume (ambientIntegralRowModule (K := K) m)
        (μHE[Module.finrank ℝ (RowVector K m)]))⁻¹) *
      (Csup + latticeCoveringRadius
        (ambientIntegralRowModule (K := K) m)) ^
          (m * degree K - l * degree K)) ^ (k - l)
  have hC₁ : 0 < C₁ := by
    dsimp [C₁]
    apply pow_pos
    apply mul_pos
    · exact mul_pos (euclideanUnitBallVolume_pos _)
        (inv_pos.mpr
          (ZLattice.covolume_pos (ambientIntegralRowModule (K := K) m)
            (μHE[Module.finrank ℝ (RowVector K m)])))
    · exact pow_pos (by linarith [hCsup, hR]) _
  have hc : ∀ W ∈ S,
      rowSpaceExtensionCount
          (echelonRowSpace (K := K) ''
            calF (K := K) (l := k) (m := m) (n := n) Csup T) W ≤
        C₁ * T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight W ^ (k - l) := by
    intro W hW
    simpa [C₁] using
      (rowSpaceExtensionCount_image_calF_le_of_raw_low_rank_induction_uniform
        (k := k) hlm hCsup hT W (hS_image W hW))
  have hlpos : 0 < l := by omega
  have hn : 0 < n := by omega
  obtain ⟨C₂, hC₂, hg⟩ :=
    Admissible.exists_uniform_rowSpaceRankSum_abs_le_of_latticeVoronoi_radius_global
      (f := f) h_f hlpos hn hT hC_R S hRadius'
  obtain ⟨D, hD, hbound⟩ :=
    rowSpaceLowerStratumTerm_abs_le_of_bounds (d := degree K)
      B f hT hnm hkm hl hlk hcount hb S hS hS_bound'
      (fun W hW => by simpa [B] using hc W hW)
      (fun W hW => by
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hg W hW)
      hzero hC₁.le hC₂.le
  refine ⟨C₁, C₂, D, hC₁, hC₂, hD, ?_⟩
  simpa [B] using hbound

/- [derived consequence, paper `le:crude_early` and `le:low_rank_terms`,
   lines 1091--1120 and 1579--1612] The paper's real cutoff
   `X = Crude2 * T^(l*d)` is rounded only to index the ordinary height
   shells.  This theorem makes that bridge explicit and then invokes the
   exact `𝓕_l(T)` low-rank estimate above; it does not replace the displayed
   Abel summation or change its cutoff. -/
set_option maxHeartbeats 2400000 in
theorem exists_echelon_calF_lowerStratumTerm_abs_le_of_crude_height
    {K : Type*} [Field K] [NumberField K]
    {n m k l : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    (hnm : m < n) (hkm : k ≤ m) (hl : 1 ≤ l) (hlk : l < k)
    {Csup T C_R Ccrude2 : ℝ} (hCsup : 0 < Csup) (hT : 1 ≤ T)
    (hC_R : 0 ≤ C_R)
    (hSupport : ∀ A : IntegralMatrix K n m,
      f (T⁻¹ • embedMatrix A) ≠ 0 →
        ‖embedMatrix A‖ ≤ Csup * T)
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := l)) m)
    (hcrude : ∀ D : EchelonMatrix K l m,
      D ∈ calF (K := K) (l := l) (m := m) (n := n) Csup T →
      rowSpaceHeight (echelonRowSpace D) ≤
        Ccrude2 * T ^ (l * degree K))
    (hRadius : ∀ W ∈ echelonRowSpace (K := K) ''
      calF (K := K) (l := l) (m := m) (n := n) Csup T,
      rowMatrixFundamentalRadius W n / T ≤ C_R)
    (μ : ∀ W : (echelonRowSpace (K := K) ''
      calF (K := K) (l := l) (m := m) (n := n) Csup T),
      Measure ((rowRealSpan W.1)ᗮ))
    (hhaar : ∀ W, Measure.IsAddHaarMeasure (μ W))
    (hcov : ∀ W : (echelonRowSpace (K := K) ''
      calF (K := K) (l := l) (m := m) (n := n) Csup T),
      ZLattice.covolume (projectedAmbientRowModule (K := K) W.1) (μ W) =
        (rowSpaceHeight W.1)⁻¹) :
    ∃ b : ℕ, 1 ≤ b ∧
      Ccrude2 * T ^ (l * degree K) ≤ (b : ℝ) ∧
      (b : ℝ) < max 1 (Ccrude2 * T ^ (l * degree K)) + 1 ∧
      ∃ C₁ C₂ D : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < D ∧
        |rowSpaceLowerStratumTerm (l := l)
            (echelonRowSpace (K := K) ''
              calF (K := K) (l := k) (m := m) (n := n) Csup T) f T| /
            T ^ (k * n * degree K) ≤
          if n + l - k < m then
            C₁ * C₂ * D * T ^ alpha_l n m k l (degree K) *
              (b : ℝ) ^ ((m - (n + l - k) : ℕ) : ℝ)
          else if m = n + l - k then
            C₁ * C₂ * D * T ^ alpha_l n m k l (degree K) *
              (1 + Real.log (b : ℝ))
          else C₁ * C₂ * D * T ^ alpha_l n m k l (degree K) := by
  let X : ℝ := Ccrude2 * T ^ (l * degree K)
  obtain ⟨b, hb, hXb, hbupper⟩ := exists_nat_shell_cutoff X
  have hS_bound : ∀ W ∈ echelonRowSpace (K := K) ''
      calF (K := K) (l := l) (m := m) (n := n) Csup T,
      rowSpaceHeight W ≤ (b : ℝ) := by
    rintro W ⟨D, hD, rfl⟩
    exact (hcrude D hD).trans (by simpa [X] using hXb)
  obtain ⟨C₁, C₂, D, hC₁, hC₂, hD, hbound⟩ :=
    exists_echelon_calF_lowerStratumTerm_abs_le_of_radius
      f h_f hnm hkm hl hlk hCsup hT hC_R hSupport hcount hb
      hS_bound hRadius μ hhaar hcov
  refine ⟨b, hb, ?_, ?_, C₁, C₂, D, hC₁, hC₂, hD, ?_⟩
  · simpa [X] using hXb
  · simpa [X] using hbupper
  · exact hbound

/- [derived consequence, paper `le:crude_early` and `le:low_rank_terms`,
   lines 1091--1120 and 1579--1612] Raw-Euclidean cutoff specialization of
   the preceding intrinsic-radius estimate.  The cutoff remains the paper's
   `X = Ccrude2 * T^(l*d)` and is rounded only for its ordinary height-shell
   index; no alternate shell decomposition is introduced. -/
set_option maxHeartbeats 2400000 in
theorem exists_echelon_calF_lowerStratumTerm_abs_le_of_raw_crude_height
    {K : Type*} [Field K] [NumberField K]
    {n m k l : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    (hnm : m < n) (hkm : k ≤ m) (hl : 1 ≤ l) (hlk : l < k)
    {Csup T C_R Ccrude2 : ℝ} (hCsup : 0 < Csup) (hT : 1 ≤ T)
    (hC_R : 0 ≤ C_R)
    (hSupport : ∀ A : IntegralMatrix K n m,
      f (T⁻¹ • embedMatrix A) ≠ 0 →
        ‖embedMatrix A‖ ≤ Csup * T)
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := l)) m)
    (hcrude : ∀ D : EchelonMatrix K l m,
      D ∈ calF (K := K) (l := l) (m := m) (n := n) Csup T →
      rowSpaceHeight (echelonRowSpace D) ≤
        Ccrude2 * T ^ (l * degree K))
    (hRadius : ∀ W ∈ echelonRowSpace (K := K) ''
      calF (K := K) (l := l) (m := m) (n := n) Csup T,
      (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice W)) / T ≤ C_R) :
    ∃ b : ℕ, 1 ≤ b ∧
      Ccrude2 * T ^ (l * degree K) ≤ (b : ℝ) ∧
      (b : ℝ) < max 1 (Ccrude2 * T ^ (l * degree K)) + 1 ∧
      ∃ C₁ C₂ D : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < D ∧
        |rowSpaceLowerStratumTerm (l := l)
            (echelonRowSpace (K := K) ''
              calF (K := K) (l := k) (m := m) (n := n) Csup T) f T| /
            T ^ (k * n * degree K) ≤
          if n + l - k < m then
            C₁ * C₂ * D * T ^ alpha_l n m k l (degree K) *
              (b : ℝ) ^ ((m - (n + l - k) : ℕ) : ℝ)
          else if m = n + l - k then
            C₁ * C₂ * D * T ^ alpha_l n m k l (degree K) *
              (1 + Real.log (b : ℝ))
          else C₁ * C₂ * D * T ^ alpha_l n m k l (degree K) := by
  let X : ℝ := Ccrude2 * T ^ (l * degree K)
  obtain ⟨b, hb, hXb, hbupper⟩ := exists_nat_shell_cutoff X
  have hS_bound : ∀ W ∈ echelonRowSpace (K := K) ''
      calF (K := K) (l := l) (m := m) (n := n) Csup T,
      rowSpaceHeight W ≤ (b : ℝ) := by
    rintro W ⟨D, hD, rfl⟩
    exact (hcrude D hD).trans (by simpa [X] using hXb)
  obtain ⟨C₁, C₂, D, hC₁, hC₂, hD, hbound⟩ :=
    exists_echelon_calF_lowerStratumTerm_abs_le_of_raw_radius
      f h_f hnm hkm hl hlk hCsup hT hC_R hSupport hcount hb
      hS_bound hRadius
  refine ⟨b, hb, ?_, ?_, C₁, C₂, D, hC₁, hC₂, hD, ?_⟩
  · simpa [X] using hXb
  · simpa [X] using hbupper
  · exact hbound

/- [derived consequence, paper `le:crude_early`, `eq:ineqluaty_abel`, and
   `eq:inequality_semifinal`, lines 1091--1120 and 1579--1612] This returns
   the ordinary-shell lower-rank estimate to the manuscript's displayed
   `B_l(T)` notation.  The exact family `𝓕_l(T)` and its real cutoff remain
   visible in the preceding theorem; only the fixed rounding factor is
   absorbed into `Ccrudenew`, as permitted by the paper's implicit constants.
-/
set_option maxHeartbeats 3000000 in
theorem exists_echelon_calF_lowerStratumTerm_abs_le_B_l_of_crude_height
    {K : Type*} [Field K] [NumberField K]
    {n m k l : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    (hnm : m < n) (hkm : k ≤ m) (hl : 1 ≤ l) (hlk : l < k)
    {Csup T C_R Ccrude2 : ℝ} (hCsup : 0 < Csup) (hT : 1 ≤ T)
    (hC_R : 0 ≤ C_R) (hCcrude2 : 0 ≤ Ccrude2)
    (hSupport : ∀ A : IntegralMatrix K n m,
      f (T⁻¹ • embedMatrix A) ≠ 0 →
        ‖embedMatrix A‖ ≤ Csup * T)
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := l)) m)
    (hcrude : ∀ D : EchelonMatrix K l m,
      D ∈ calF (K := K) (l := l) (m := m) (n := n) Csup T →
      rowSpaceHeight (echelonRowSpace D) ≤
        Ccrude2 * T ^ (l * degree K))
    (hRadius : ∀ W ∈ echelonRowSpace (K := K) ''
      calF (K := K) (l := l) (m := m) (n := n) Csup T,
      rowMatrixFundamentalRadius W n / T ≤ C_R)
    (μ : ∀ W : (echelonRowSpace (K := K) ''
      calF (K := K) (l := l) (m := m) (n := n) Csup T),
      Measure ((rowRealSpan W.1)ᗮ))
    (hhaar : ∀ W, Measure.IsAddHaarMeasure (μ W))
    (hcov : ∀ W : (echelonRowSpace (K := K) ''
      calF (K := K) (l := l) (m := m) (n := n) Csup T),
      ZLattice.covolume (projectedAmbientRowModule (K := K) W.1) (μ W) =
        (rowSpaceHeight W.1)⁻¹) :
    ∃ C₁ C₂ Ccrudenew : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < Ccrudenew ∧
      |rowSpaceLowerStratumTerm (l := l)
          (echelonRowSpace (K := K) ''
            calF (K := K) (l := k) (m := m) (n := n) Csup T) f T| /
          T ^ (k * n * degree K) ≤
        C₁ * C₂ * T ^ alpha_l n m k l (degree K) *
          B_l n m k l (degree K) Ccrudenew T := by
  obtain ⟨b, hb, hcut, hupper, C₁, C₂, D, hC₁, hC₂, hD, hterm⟩ :=
    exists_echelon_calF_lowerStratumTerm_abs_le_of_crude_height
      f h_f hnm hkm hl hlk hCsup hT hC_R hSupport hcount hcrude hRadius
      μ hhaar hcov
  obtain ⟨Ccrudenew, hCcrudenew, hB⟩ :=
    exists_B_l_bound_of_nat_shell_cutoff
      (d := degree K) hCcrude2 hD hT hb hupper hnm hkm hlk
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hfactor_nonneg :
      0 ≤ C₁ * C₂ * T ^ alpha_l n m k l (degree K) := by
    exact mul_nonneg (mul_nonneg hC₁.le hC₂.le) (zpow_nonneg hTpos.le _)
  refine ⟨C₁, C₂, Ccrudenew, hC₁, hC₂, hCcrudenew, ?_⟩
  by_cases hpos : n + l - k < m
  · have hterm_pos :
        |rowSpaceLowerStratumTerm (l := l)
            (echelonRowSpace (K := K) ''
              calF (K := K) (l := k) (m := m) (n := n) Csup T) f T| /
            T ^ (k * n * degree K) ≤
          C₁ * C₂ * D * T ^ alpha_l n m k l (degree K) *
            (b : ℝ) ^ ((m - (n + l - k) : ℕ) : ℝ) := by
      simpa only [if_pos hpos] using hterm
    have hB_pos : D * (b : ℝ) ^ ((m - (n + l - k) : ℕ) : ℝ) ≤
        B_l n m k l (degree K) Ccrudenew T := by
      simpa only [if_pos hpos] using hB
    calc
      |rowSpaceLowerStratumTerm (l := l)
          (echelonRowSpace (K := K) ''
            calF (K := K) (l := k) (m := m) (n := n) Csup T) f T| /
          T ^ (k * n * degree K) ≤
          C₁ * C₂ * D * T ^ alpha_l n m k l (degree K) *
            (b : ℝ) ^ ((m - (n + l - k) : ℕ) : ℝ) := hterm_pos
      _ = (C₁ * C₂ * T ^ alpha_l n m k l (degree K)) *
          (D * (b : ℝ) ^ ((m - (n + l - k) : ℕ) : ℝ)) := by ring
      _ ≤ (C₁ * C₂ * T ^ alpha_l n m k l (degree K)) *
          B_l n m k l (degree K) Ccrudenew T :=
        mul_le_mul_of_nonneg_left hB_pos hfactor_nonneg
      _ = C₁ * C₂ * T ^ alpha_l n m k l (degree K) *
          B_l n m k l (degree K) Ccrudenew T := by ring
  · by_cases hzero : m = n + l - k
    · have hterm_zero :
          |rowSpaceLowerStratumTerm (l := l)
              (echelonRowSpace (K := K) ''
                calF (K := K) (l := k) (m := m) (n := n) Csup T) f T| /
              T ^ (k * n * degree K) ≤
            C₁ * C₂ * D * T ^ alpha_l n m k l (degree K) *
              (1 + Real.log (b : ℝ)) := by
        simpa only [if_neg hpos, if_pos hzero] using hterm
      have hB_zero : D * (1 + Real.log (b : ℝ)) ≤
          B_l n m k l (degree K) Ccrudenew T := by
        simpa only [if_neg hpos, if_pos hzero] using hB
      calc
        |rowSpaceLowerStratumTerm (l := l)
            (echelonRowSpace (K := K) ''
              calF (K := K) (l := k) (m := m) (n := n) Csup T) f T| /
            T ^ (k * n * degree K) ≤
            C₁ * C₂ * D * T ^ alpha_l n m k l (degree K) *
              (1 + Real.log (b : ℝ)) := hterm_zero
        _ = (C₁ * C₂ * T ^ alpha_l n m k l (degree K)) *
            (D * (1 + Real.log (b : ℝ))) := by ring
        _ ≤ (C₁ * C₂ * T ^ alpha_l n m k l (degree K)) *
            B_l n m k l (degree K) Ccrudenew T :=
          mul_le_mul_of_nonneg_left hB_zero hfactor_nonneg
        _ = C₁ * C₂ * T ^ alpha_l n m k l (degree K) *
            B_l n m k l (degree K) Ccrudenew T := by ring
    · have hterm_neg :
          |rowSpaceLowerStratumTerm (l := l)
              (echelonRowSpace (K := K) ''
                calF (K := K) (l := k) (m := m) (n := n) Csup T) f T| /
              T ^ (k * n * degree K) ≤
            C₁ * C₂ * D * T ^ alpha_l n m k l (degree K) := by
        simpa only [if_neg hpos, if_neg hzero] using hterm
      have hB_neg : D ≤ B_l n m k l (degree K) Ccrudenew T := by
        simpa only [if_neg hpos, if_neg hzero] using hB
      calc
        |rowSpaceLowerStratumTerm (l := l)
            (echelonRowSpace (K := K) ''
              calF (K := K) (l := k) (m := m) (n := n) Csup T) f T| /
            T ^ (k * n * degree K) ≤
            C₁ * C₂ * D * T ^ alpha_l n m k l (degree K) := hterm_neg
        _ = (C₁ * C₂ * T ^ alpha_l n m k l (degree K)) * D := by ring
        _ ≤ (C₁ * C₂ * T ^ alpha_l n m k l (degree K)) *
            B_l n m k l (degree K) Ccrudenew T :=
          mul_le_mul_of_nonneg_left hB_neg hfactor_nonneg
        _ = C₁ * C₂ * T ^ alpha_l n m k l (degree K) *
            B_l n m k l (degree K) Ccrudenew T := by ring

/- [derived consequence, paper `le:crude_early`, `eq:ineqluaty_abel`, and
   `eq:inequality_semifinal`, lines 1091--1120 and 1579--1612] Raw-Euclidean
   `B_l(T)` packaging of the same ordinary-shell estimate.  It retains the
   paper's exact cutoff and all three displayed branches; its separate name
   records that the height is still the raw-metric realization. -/
set_option maxHeartbeats 3000000 in
theorem exists_echelon_calF_lowerStratumTerm_abs_le_B_l_of_raw_crude_height
    {K : Type*} [Field K] [NumberField K]
    {n m k l : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    (hnm : m < n) (hkm : k ≤ m) (hl : 1 ≤ l) (hlk : l < k)
    {Csup T C_R Ccrude2 : ℝ} (hCsup : 0 < Csup) (hT : 1 ≤ T)
    (hC_R : 0 ≤ C_R) (hCcrude2 : 0 ≤ Ccrude2)
    (hSupport : ∀ A : IntegralMatrix K n m,
      f (T⁻¹ • embedMatrix A) ≠ 0 →
        ‖embedMatrix A‖ ≤ Csup * T)
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := l)) m)
    (hcrude : ∀ D : EchelonMatrix K l m,
      D ∈ calF (K := K) (l := l) (m := m) (n := n) Csup T →
      rowSpaceHeight (echelonRowSpace D) ≤
        Ccrude2 * T ^ (l * degree K))
    (hRadius : ∀ W ∈ echelonRowSpace (K := K) ''
      calF (K := K) (l := l) (m := m) (n := n) Csup T,
      (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice W)) / T ≤ C_R) :
    ∃ C₁ C₂ Ccrudenew : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < Ccrudenew ∧
      |rowSpaceLowerStratumTerm (l := l)
          (echelonRowSpace (K := K) ''
            calF (K := K) (l := k) (m := m) (n := n) Csup T) f T| /
          T ^ (k * n * degree K) ≤
        C₁ * C₂ * T ^ alpha_l n m k l (degree K) *
          B_l n m k l (degree K) Ccrudenew T := by
  obtain ⟨b, hb, hcut, hupper, C₁, C₂, D, hC₁, hC₂, hD, hterm⟩ :=
    exists_echelon_calF_lowerStratumTerm_abs_le_of_raw_crude_height
      f h_f hnm hkm hl hlk hCsup hT hC_R hSupport hcount hcrude hRadius
  obtain ⟨Ccrudenew, hCcrudenew, hB⟩ :=
    exists_B_l_bound_of_nat_shell_cutoff
      (d := degree K) hCcrude2 hD hT hb hupper hnm hkm hlk
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hfactor_nonneg :
      0 ≤ C₁ * C₂ * T ^ alpha_l n m k l (degree K) := by
    exact mul_nonneg (mul_nonneg hC₁.le hC₂.le) (zpow_nonneg hTpos.le _)
  refine ⟨C₁, C₂, Ccrudenew, hC₁, hC₂, hCcrudenew, ?_⟩
  by_cases hpos : n + l - k < m
  · have hterm_pos :
        |rowSpaceLowerStratumTerm (l := l)
            (echelonRowSpace (K := K) ''
              calF (K := K) (l := k) (m := m) (n := n) Csup T) f T| /
              T ^ (k * n * degree K) ≤
            C₁ * C₂ * D * T ^ alpha_l n m k l (degree K) *
              (b : ℝ) ^ ((m - (n + l - k) : ℕ) : ℝ) := by
      simpa only [if_pos hpos] using hterm
    have hB_pos : D * (b : ℝ) ^ ((m - (n + l - k) : ℕ) : ℝ) ≤
        B_l n m k l (degree K) Ccrudenew T := by
      simpa only [if_pos hpos] using hB
    calc
      |rowSpaceLowerStratumTerm (l := l)
          (echelonRowSpace (K := K) ''
            calF (K := K) (l := k) (m := m) (n := n) Csup T) f T| /
          T ^ (k * n * degree K) ≤
          C₁ * C₂ * D * T ^ alpha_l n m k l (degree K) *
            (b : ℝ) ^ ((m - (n + l - k) : ℕ) : ℝ) := hterm_pos
      _ = (C₁ * C₂ * T ^ alpha_l n m k l (degree K)) *
          (D * (b : ℝ) ^ ((m - (n + l - k) : ℕ) : ℝ)) := by ring
      _ ≤ (C₁ * C₂ * T ^ alpha_l n m k l (degree K)) *
          B_l n m k l (degree K) Ccrudenew T :=
        mul_le_mul_of_nonneg_left hB_pos hfactor_nonneg
      _ = C₁ * C₂ * T ^ alpha_l n m k l (degree K) *
          B_l n m k l (degree K) Ccrudenew T := by ring
  · by_cases hzero : m = n + l - k
    · have hterm_zero :
          |rowSpaceLowerStratumTerm (l := l)
              (echelonRowSpace (K := K) ''
                calF (K := K) (l := k) (m := m) (n := n) Csup T) f T| /
              T ^ (k * n * degree K) ≤
            C₁ * C₂ * D * T ^ alpha_l n m k l (degree K) *
              (1 + Real.log (b : ℝ)) := by
        simpa only [if_neg hpos, if_pos hzero] using hterm
      have hB_zero : D * (1 + Real.log (b : ℝ)) ≤
          B_l n m k l (degree K) Ccrudenew T := by
        simpa only [if_neg hpos, if_pos hzero] using hB
      calc
        |rowSpaceLowerStratumTerm (l := l)
            (echelonRowSpace (K := K) ''
              calF (K := K) (l := k) (m := m) (n := n) Csup T) f T| /
            T ^ (k * n * degree K) ≤
            C₁ * C₂ * D * T ^ alpha_l n m k l (degree K) *
              (1 + Real.log (b : ℝ)) := hterm_zero
        _ = (C₁ * C₂ * T ^ alpha_l n m k l (degree K)) *
            (D * (1 + Real.log (b : ℝ))) := by ring
        _ ≤ (C₁ * C₂ * T ^ alpha_l n m k l (degree K)) *
            B_l n m k l (degree K) Ccrudenew T :=
          mul_le_mul_of_nonneg_left hB_zero hfactor_nonneg
        _ = C₁ * C₂ * T ^ alpha_l n m k l (degree K) *
            B_l n m k l (degree K) Ccrudenew T := by ring
    · have hterm_neg :
          |rowSpaceLowerStratumTerm (l := l)
              (echelonRowSpace (K := K) ''
                calF (K := K) (l := k) (m := m) (n := n) Csup T) f T| /
              T ^ (k * n * degree K) ≤
            C₁ * C₂ * D * T ^ alpha_l n m k l (degree K) := by
        simpa only [if_neg hpos, if_neg hzero] using hterm
      have hB_neg : D ≤ B_l n m k l (degree K) Ccrudenew T := by
        simpa only [if_neg hpos, if_neg hzero] using hB
      calc
        |rowSpaceLowerStratumTerm (l := l)
            (echelonRowSpace (K := K) ''
              calF (K := K) (l := k) (m := m) (n := n) Csup T) f T| /
            T ^ (k * n * degree K) ≤
            C₁ * C₂ * D * T ^ alpha_l n m k l (degree K) := hterm_neg
        _ = (C₁ * C₂ * T ^ alpha_l n m k l (degree K)) * D := by ring
        _ ≤ (C₁ * C₂ * T ^ alpha_l n m k l (degree K)) *
            B_l n m k l (degree K) Ccrudenew T :=
          mul_le_mul_of_nonneg_left hB_neg hfactor_nonneg
        _ = C₁ * C₂ * T ^ alpha_l n m k l (degree K) *
            B_l n m k l (degree K) Ccrudenew T := by ring

/- [derived consequence, paper lemma `le:crude_early` and lemma
   `le:low_rank_terms`, lines 1091--1120 and 1495--1633] This discharges the
   generic height-cutoff hypothesis in the preceding lower-rank estimate with
   the proved, manuscript-normalized `C^crude2`.  In particular, the proof
   continues to use the exact echelon family `𝓕_l(T)` rather than an
   alternative shell decomposition. -/
set_option maxHeartbeats 3000000 in
theorem exists_echelon_calF_lowerStratumTerm_abs_le_B_l_of_proved_crude_height
    {K : Type*} [Field K] [NumberField K]
    {n m k l : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    (hnm : m < n) (hkm : k ≤ m) (hl : 1 ≤ l) (hlk : l < k)
    {Csup T C_R : ℝ} (hCsup : 0 < Csup) (hT : 1 ≤ T)
    (hC_R : 0 ≤ C_R)
    (hSupport : ∀ A : IntegralMatrix K n m,
      f (T⁻¹ • embedMatrix A) ≠ 0 →
        ‖embedMatrix A‖ ≤ Csup * T)
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := l)) m)
    (hRadius : ∀ W ∈ echelonRowSpace (K := K) ''
      calF (K := K) (l := l) (m := m) (n := n) Csup T,
      rowMatrixFundamentalRadius W n / T ≤ C_R)
    (μ : ∀ W : (echelonRowSpace (K := K) ''
      calF (K := K) (l := l) (m := m) (n := n) Csup T),
      Measure ((rowRealSpan W.1)ᗮ))
    (hhaar : ∀ W, Measure.IsAddHaarMeasure (μ W))
    (hcov : ∀ W : (echelonRowSpace (K := K) ''
      calF (K := K) (l := l) (m := m) (n := n) Csup T),
      ZLattice.covolume (projectedAmbientRowModule (K := K) W.1) (μ W) =
        (rowSpaceHeight W.1)⁻¹) :
    ∃ C₁ C₂ Ccrudenew : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < Ccrudenew ∧
      |rowSpaceLowerStratumTerm (l := l)
          (echelonRowSpace (K := K) ''
            calF (K := K) (l := k) (m := m) (n := n) Csup T) f T| /
          T ^ (k * n * degree K) ≤
        C₁ * C₂ * T ^ alpha_l n m k l (degree K) *
          B_l n m k l (degree K) Ccrudenew T := by
  have hlpos : 0 < l := by omega
  have hCcrude2 : 0 ≤ Ccrude2 (K := K) (m := m) (k := l) Csup :=
    (Ccrude2_pos (K := K) (m := m) (k := l) Csup hCsup hlpos).le
  exact exists_echelon_calF_lowerStratumTerm_abs_le_B_l_of_crude_height
    (Ccrude2 := Ccrude2 (K := K) (m := m) (k := l) Csup)
    f h_f hnm hkm hl hlk hCsup hT hC_R hCcrude2 hSupport hcount
    (fun D hD => echelon_mem_calF_height_le_Ccrude2 D Csup T hlpos hD)
    hRadius μ hhaar hcov

/- [derived consequence, paper lemma `le:crude_early` and lemma
   `le:low_rank_terms`, lines 1091--1120 and 1495--1633] Raw-Euclidean
   version with the proved manuscript-facing `C^crude2` height cutoff.  The
   cutoff and the exact echelon family are unchanged; only the raw extension
   count is used beneath the Abel estimate. -/
set_option maxHeartbeats 3000000 in
theorem exists_echelon_calF_lowerStratumTerm_abs_le_B_l_of_raw_proved_crude_height
    {K : Type*} [Field K] [NumberField K]
    {n m k l : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    (hnm : m < n) (hkm : k ≤ m) (hl : 1 ≤ l) (hlk : l < k)
    {Csup T C_R : ℝ} (hCsup : 0 < Csup) (hT : 1 ≤ T)
    (hC_R : 0 ≤ C_R)
    (hSupport : ∀ A : IntegralMatrix K n m,
      f (T⁻¹ • embedMatrix A) ≠ 0 →
        ‖embedMatrix A‖ ≤ Csup * T)
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := l)) m)
    (hRadius : ∀ W ∈ echelonRowSpace (K := K) ''
      calF (K := K) (l := l) (m := m) (n := n) Csup T,
      (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice W)) / T ≤ C_R) :
    ∃ C₁ C₂ Ccrudenew : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < Ccrudenew ∧
      |rowSpaceLowerStratumTerm (l := l)
          (echelonRowSpace (K := K) ''
            calF (K := K) (l := k) (m := m) (n := n) Csup T) f T| /
          T ^ (k * n * degree K) ≤
        C₁ * C₂ * T ^ alpha_l n m k l (degree K) *
          B_l n m k l (degree K) Ccrudenew T := by
  have hlpos : 0 < l := by omega
  have hCcrude2 : 0 ≤ Ccrude2 (K := K) (m := m) (k := l) Csup :=
    (Ccrude2_pos (K := K) (m := m) (k := l) Csup hCsup hlpos).le
  exact exists_echelon_calF_lowerStratumTerm_abs_le_B_l_of_raw_crude_height
    (Ccrude2 := Ccrude2 (K := K) (m := m) (k := l) Csup)
    f h_f hnm hkm hl hlk hCsup hT hC_R hCcrude2 hSupport hcount
    (fun D hD => echelon_mem_calF_height_le_Ccrude2 D Csup T hlpos hD)
    hRadius

/- [derived consequence of paper corollary `co:covering_bound` and lemmas
   `le:crude_early`, `le:low_rank_terms`, lines 1091--1120 and 1239--1248,
   1495--1633] The preceding raw lower-rank estimate no longer needs an
   externally supplied radius threshold: `co:covering_bound` supplies its
   exact intrinsic threshold on every row space in `𝓕_l(T)`.  The cutoff,
   height, and Abel-summation notation are those of the manuscript. -/
set_option maxHeartbeats 3000000 in
theorem exists_echelon_calF_lowerStratumTerm_abs_le_B_l_of_raw_covering_bound
    {K : Type*} [Field K] [NumberField K]
    {n m k l : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    (hnm : m < n) (hkm : k ≤ m) (hl : 1 ≤ l) (hlk : l < k)
    {Csup T : ℝ} (hCsup : 0 < Csup) (hT : 1 ≤ T)
    (hSupport : ∀ A : IntegralMatrix K n m,
      f (T⁻¹ • embedMatrix A) ≠ 0 →
        ‖embedMatrix A‖ ≤ Csup * T)
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := l)) m) :
    ∃ C₁ C₂ Ccrudenew : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < Ccrudenew ∧
      |rowSpaceLowerStratumTerm (l := l)
          (echelonRowSpace (K := K) ''
            calF (K := K) (l := k) (m := m) (n := n) Csup T) f T| /
          T ^ (k * n * degree K) ≤
        C₁ * C₂ * T ^ alpha_l n m k l (degree K) *
          B_l n m k l (degree K) Ccrudenew T := by
  have hlpos : 0 < l := by omega
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  let C_R : ℝ := Real.sqrt (n : ℝ) *
    (Fintype.card (Σ _ : Fin l, IntegralBasisIndex K) : ℝ) *
      rowScalarActionBoundSum (K := K) (m := m) * Csup
  have hC_R : 0 ≤ C_R := by
    dsimp [C_R]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _))
        (rowScalarActionBoundSum_nonneg (K := K) (m := m)))
      hCsup.le
  apply exists_echelon_calF_lowerStratumTerm_abs_le_B_l_of_raw_proved_crude_height
    (C_R := C_R) f h_f hnm hkm hl hlk hCsup hT hC_R hSupport hcount
  intro W hW
  exact echelon_calF_image_matrixCoveringRadius_div_le hlpos hTpos hW

/- [derived consequence, paper `le:low_rank_terms`, lines 1495--1631]
   Restore the paper-facing echelon-family notation after finite-in-`l`
   uniformization.  The hypothesis is precisely the preceding pointwise
   `𝓕_l(T)` estimate; the finite sum is Lean bookkeeping for the manuscript's
   implicit constants. -/
theorem exists_uniform_echelon_calF_lowerStratumTerm_abs_le_B_l
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (f : M n m (K_ℝ[K]) → ℝ) {Csup T : ℝ} (hT : 1 ≤ T)
    (hpoint : ∀ l ∈ Finset.Ico 1 k,
      ∃ C₁ C₂ Ccrudenew : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < Ccrudenew ∧
        |rowSpaceLowerStratumTerm (l := l)
            (echelonRowSpace (K := K) ''
              calF (K := K) (l := k) (m := m) (n := n) Csup T) f T| /
            T ^ (k * n * degree K) ≤
          C₁ * C₂ * T ^ alpha_l n m k l (degree K) *
            B_l n m k l (degree K) Ccrudenew T) :
    ∃ C₃ Ccrudenew : ℝ, 0 < C₃ ∧ 0 < Ccrudenew ∧
      ∀ l ∈ Finset.Ico 1 k,
        |rowSpaceLowerStratumTerm (l := l)
            (echelonRowSpace (K := K) ''
              calF (K := K) (l := k) (m := m) (n := n) Csup T) f T| /
            T ^ (k * n * degree K) ≤
          C₃ * T ^ alpha_l n m k l (degree K) *
            B_l n m k l (degree K) Ccrudenew T := by
  simpa using
    (exists_uniform_B_l_point_bound (n := n) (m := m) (k := k)
      (d := degree K) hT
      (fun l =>
        |rowSpaceLowerStratumTerm (l := l)
            (echelonRowSpace (K := K) ''
              calF (K := K) (l := k) (m := m) (n := n) Csup T) f T| /
          T ^ (k * n * degree K)) hpoint)

/- [derived consequence, paper `le:low_rank_terms`, lines 1495--1633]
   Assemble the manuscript's rank-zero and positive lower-rank contributions.
   `hB_eq` is an explicit proved bridge from the internal finite row-space
   representation back to the exact echelon family `𝓕_k(T)`, rather than a
   replacement of the paper's indexing. -/
set_option maxHeartbeats 2400000 in
theorem exists_echelon_calF_lowerSum_normalized_abs_le_corrected
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (B : Set (Grassmannian K m k)) [Fintype B]
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    (hnm : m < n) (hk : 1 ≤ k) {Csup T Csize : ℝ}
    (hT : 1 ≤ T) (hCsize : 0 ≤ Csize)
    (hB_eq : B = echelonRowSpace (K := K) ''
      calF (K := K) (l := k) (m := m) (n := n) Csup T)
    (hB : (B.ncard : ℝ) ≤ Csize * T ^ (k * m * degree K))
    (hpoint : ∀ l ∈ Finset.Ico 1 k,
      ∃ C₁ C₂ Ccrudenew : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < Ccrudenew ∧
        |rowSpaceLowerStratumTerm (l := l)
            (echelonRowSpace (K := K) ''
              calF (K := K) (l := k) (m := m) (n := n) Csup T) f T| /
            T ^ (k * n * degree K) ≤
          C₁ * C₂ * T ^ alpha_l n m k l (degree K) *
            B_l n m k l (degree K) Ccrudenew T) :
    ∃ C₃ Ccrudenew : ℝ, 0 < C₃ ∧ 0 < Ccrudenew ∧
      |(∑ V : B,
          ∑' A : {A : IntegralMatrix K n m //
            rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
            f (T⁻¹ • embedMatrix A.1)) /
          T ^ (k * n * degree K)| ≤
        (Csize * |f 0| + ((Finset.Ico 1 k).card : ℝ) * C₃ * Ccrudenew) *
          (1 + Real.log T) *
          T ^ (-(degree K : ℤ) *
            ((n - m + k - 1 : ℕ) : ℤ)) := by
  obtain ⟨C₃, Ccrudenew, hC₃, hCcrudenew, hpoint_uniform⟩ :=
    exists_uniform_echelon_calF_lowerStratumTerm_abs_le_B_l f hT hpoint
  refine ⟨C₃, Ccrudenew, hC₃, hCcrudenew, ?_⟩
  have hpoint_uniform_B : ∀ l ∈ Finset.Ico 1 k,
      |rowSpaceLowerStratumTerm (l := l) B f T| /
          T ^ (k * n * degree K) ≤
        C₃ * T ^ alpha_l n m k l (degree K) *
          B_l n m k l (degree K) Ccrudenew T := by
    intro l hl
    rw [hB_eq]
    exact hpoint_uniform l hl
  simpa using
    (finite_rowSpaceLowerSum_normalized_abs_le_corrected B f h_f hT hnm hk
      (d := degree K) Module.finrank_pos hCsize hB
      hC₃.le hCcrudenew.le hpoint_uniform_B)

/- [paper, corollary `co:counting_matrices`, lines 1091--1100]
   The manuscript's crude height estimate implies the stated cardinality
   bound for the echelon family.  The height estimate itself is kept as the
   preceding paper step's explicit input; this theorem proves the counting
   corollary from Schmidt's height-count interface and the injective echelon
   representative map. -/
set_option maxHeartbeats 800000 in
theorem echelonCalF_ncard_le_of_height_bound
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} {Csup Cheight T : ℝ}
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := k)) m)
    (hCheight : 1 ≤ Cheight) (hT : 1 ≤ T)
    (hcrude : ∀ D : EchelonMatrix K k m,
      D ∈ calF (K := K) (l := k) (m := m) (n := n) Csup T →
      rowSpaceHeight (echelonRowSpace D) ≤
        Cheight * T ^ (k * degree K)) :
    ∃ Csize : ℝ, 0 < Csize ∧
      (Set.ncard
        (calF (K := K) (l := k) (m := m) (n := n) Csup T) : ℝ) ≤
        Csize * T ^ (k * m * degree K) := by
  obtain ⟨cᵤ, hcᵤ, hupper⟩ :=
    heightBoundedRowSpaces_count_upper (K := K) hcount
  let F : Set (EchelonMatrix K k m) :=
    calF (K := K) (l := k) (m := m) (n := n) Csup T
  let B : Set (Grassmannian K m k) :=
    echelonRowSpace (K := K) '' F
  let H : Set (Grassmannian K m k) :=
    heightBoundedRowSpaces (K := K) (m := m) (k := k) Cheight T
  have hHfin : H.Finite := by
    simpa [H] using heightBoundedRowSpaces_finite hcount hCheight hT
  have hsubset : B ⊆ H := by
    rintro V ⟨D, hD, rfl⟩
    change rowSpaceHeight (echelonRowSpace D) ≤
      Cheight * T ^ (k * degree K)
    exact hcrude D hD
  have hcard : B.ncard ≤ H.ncard := by
    exact Set.ncard_le_ncard hsubset hHfin
  have hcardR : (B.ncard : ℝ) ≤ (H.ncard : ℝ) := by
    exact_mod_cast hcard
  have hupper' : (H.ncard : ℝ) ≤
      cᵤ * (Cheight * T ^ (k * degree K)) ^ m := by
    exact hupper hCheight hT
  let Csize : ℝ := cᵤ * Cheight ^ m
  have hCsize : 0 < Csize := by
    dsimp [Csize]
    positivity
  have himage_ncard : B.ncard = F.ncard := by
    dsimp [B]
    exact Set.ncard_image_of_injective _
      (echelonRowSpace_injective (K := K) (l := k) (m := m))
  refine ⟨Csize, hCsize, ?_⟩
  have hFcardR : (F.ncard : ℝ) ≤
      Csize * T ^ (k * m * degree K) := by
    rw [← himage_ncard]
    calc
      (B.ncard : ℝ) ≤ (H.ncard : ℝ) := hcardR
      _ ≤ cᵤ * (Cheight * T ^ (k * degree K)) ^ m := hupper'
      _ = Csize * T ^ (k * m * degree K) := by
        dsimp [Csize]
        rw [mul_pow, ← pow_mul]
        rw [show k * degree K * m = k * m * degree K by ring]
        ring
  simpa [F] using hFcardR

/- [derived consequence, paper corollary `co:counting_matrices`,
   lines 1121--1129] This discharges the preceding generic crude-height
   hypothesis using the proved manuscript lemma `le:crude_early`.  The
   auxiliary `max 1` is Lean infrastructure required by the existing
   height-count interface; the exact `C^crude2` cutoff remains visible in
   `echelon_mem_calF_height_le_Ccrude2`. -/
set_option maxHeartbeats 1200000 in
theorem echelonCalF_ncard_le_of_proved_crude_height
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} {Csup T : ℝ}
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := k)) m)
    (hT : 1 ≤ T) (hk : 0 < k) :
    ∃ Csize : ℝ, 0 < Csize ∧
      (Set.ncard
        (calF (K := K) (l := k) (m := m) (n := n) Csup T) : ℝ) ≤
        Csize * T ^ (k * m * degree K) := by
  let Cheight : ℝ := max 1 (Ccrude2 (K := K) (m := m) (k := k) Csup)
  have hCheight : 1 ≤ Cheight := by
    dsimp [Cheight]
    exact le_max_left _ _
  apply echelonCalF_ncard_le_of_height_bound hcount hCheight hT
  intro D hD
  have hcrude := echelon_mem_calF_height_le_Ccrude2 D Csup T hk hD
  have hTnonneg : 0 ≤ T ^ (k * degree K) :=
    pow_nonneg (le_trans zero_le_one hT) _
  calc
    rowSpaceHeight (echelonRowSpace D) ≤
        Ccrude2 (K := K) (m := m) (k := k) Csup * T ^ (k * degree K) := hcrude
    _ ≤ Cheight * T ^ (k * degree K) :=
      mul_le_mul_of_nonneg_right (by
        dsimp [Cheight]
        exact le_max_right _ _) hTnonneg

/- [derived consequence, paper corollary `co:counting_matrices`,
   lines 1121--1128] Transfer the cardinality estimate from the manuscript's
   echelon representatives to the finite row-space family used internally.
   The equality is justified by the proved injectivity of the echelon
   representative map, so it retains the exact `𝓕_k(T)` indexing. -/
theorem echelonCalF_rowSpace_image_ncard_le_of_height_bound
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} {Csup Cheight T : ℝ}
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := k)) m)
    (hCheight : 1 ≤ Cheight) (hT : 1 ≤ T)
    (hcrude : ∀ D : EchelonMatrix K k m,
      D ∈ calF (K := K) (l := k) (m := m) (n := n) Csup T →
      rowSpaceHeight (echelonRowSpace D) ≤
        Cheight * T ^ (k * degree K)) :
    ∃ Csize : ℝ, 0 < Csize ∧
      ((echelonRowSpace (K := K) ''
        calF (K := K) (l := k) (m := m) (n := n) Csup T).ncard : ℝ) ≤
        Csize * T ^ (k * m * degree K) := by
  obtain ⟨Csize, hCsize, hbound⟩ :=
    echelonCalF_ncard_le_of_height_bound hcount hCheight hT hcrude
  refine ⟨Csize, hCsize, ?_⟩
  rw [Set.ncard_image_of_injective _
    (echelonRowSpace_injective (K := K) (l := k) (m := m))]
  exact hbound

/- [derived consequence of paper lemma `le:crude_early` and corollary
   `co:counting_matrices`, lines 1091--1129] This is the proved-crude-height
   specialization of the preceding cardinality estimate, on the exact
   row-space image of `𝓕_k(T)`.  The image is kept explicit because it is the
   finite family used by the lower-rank sum. -/
set_option maxHeartbeats 1200000 in
theorem echelonCalF_rowSpace_image_ncard_le_of_proved_crude_height
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} {Csup T : ℝ}
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := k)) m)
    (hT : 1 ≤ T) (hk : 0 < k) :
    ∃ Csize : ℝ, 0 < Csize ∧
      ((echelonRowSpace (K := K) ''
        calF (K := K) (l := k) (m := m) (n := n) Csup T).ncard : ℝ) ≤
        Csize * T ^ (k * m * degree K) := by
  let Cheight : ℝ := max 1 (Ccrude2 (K := K) (m := m) (k := k) Csup)
  have hCheight : 1 ≤ Cheight := by
    dsimp [Cheight]
    exact le_max_left _ _
  apply echelonCalF_rowSpace_image_ncard_le_of_height_bound
    hcount hCheight hT
  intro D hD
  have hcrude := echelon_mem_calF_height_le_Ccrude2 D Csup T hk hD
  have hTnonneg : 0 ≤ T ^ (k * degree K) :=
    pow_nonneg (le_trans zero_le_one hT) _
  calc
    rowSpaceHeight (echelonRowSpace D) ≤
        Ccrude2 (K := K) (m := m) (k := k) Csup * T ^ (k * degree K) := hcrude
    _ ≤ Cheight * T ^ (k * degree K) :=
      mul_le_mul_of_nonneg_right (by
        dsimp [Cheight]
        exact le_max_right _ _) hTnonneg

/- [derived consequence of paper `le:low_rank_terms`, `le:crude_early`, and
   `co:counting_matrices`, lines 1091--1129 and 1495--1633] This discharges
   both finite-family inputs in the lower-rank assembly from the proved crude
   height estimate and the intrinsic covering bound.  The only remaining
   external arithmetic input is the explicitly attributed Schmidt height
   count, supplied for each rank occurring in the manuscript's sum. -/
set_option maxHeartbeats 3000000 in
theorem exists_echelon_calF_lowerSum_normalized_abs_le_of_raw_covering_bound
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    (hnm : m < n) (hkm : k ≤ m) (hk : 1 ≤ k)
    {Csup T : ℝ} (hCsup : 0 < Csup) (hT : 1 ≤ T)
    (hSupport : ∀ A : IntegralMatrix K n m,
      f (T⁻¹ • embedMatrix A) ≠ 0 →
        ‖embedMatrix A‖ ≤ Csup * T)
    (hcount : ∀ l ∈ Finset.Icc 1 k,
      HasHeightCountBounds
        (rowSpaceHeight (K := K) (m := m) (k := l)) m) :
    ∃ C₃ Ccrudenew Csize : ℝ,
      0 < C₃ ∧ 0 < Ccrudenew ∧ 0 < Csize ∧
      |(∑' V : (echelonRowSpace (K := K) ''
          calF (K := K) (l := k) (m := m) (n := n) Csup T),
          ∑' A : {A : IntegralMatrix K n m //
            rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
            f (T⁻¹ • embedMatrix A.1)) /
          T ^ (k * n * degree K)| ≤
        (Csize * |f 0| + ((Finset.Ico 1 k).card : ℝ) * C₃ * Ccrudenew) *
          (1 + Real.log T) *
          T ^ (-(degree K : ℤ) *
            ((n - m + k - 1 : ℕ) : ℤ)) := by
  let B : Set (Grassmannian K m k) := echelonRowSpace (K := K) ''
    calF (K := K) (l := k) (m := m) (n := n) Csup T
  have hBfinite : B.Finite := by
    dsimp [B]
    exact (finite_calF (K := K) (l := k) (m := m) (n := n)
      (Csup := Csup) (T := T)).image _
  letI : Fintype B := hBfinite.fintype
  have hkpos : 0 < k := by omega
  have hkIcc : k ∈ Finset.Icc 1 k :=
    Finset.mem_Icc.mpr ⟨hk, le_rfl⟩
  obtain ⟨Csize, hCsize, hBcard⟩ :=
    echelonCalF_rowSpace_image_ncard_le_of_proved_crude_height
      (K := K) (n := n) (m := m) (k := k) (Csup := Csup) (T := T)
      (hcount k hkIcc) hT hkpos
  have hpoint : ∀ l ∈ Finset.Ico 1 k,
      ∃ C₁ C₂ Ccrudenew : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < Ccrudenew ∧
        |rowSpaceLowerStratumTerm (l := l)
            (echelonRowSpace (K := K) ''
              calF (K := K) (l := k) (m := m) (n := n) Csup T) f T| /
            T ^ (k * n * degree K) ≤
          C₁ * C₂ * T ^ alpha_l n m k l (degree K) *
            B_l n m k l (degree K) Ccrudenew T := by
    intro l hl
    have hlIcc : l ∈ Finset.Icc 1 k :=
      Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp hl).1,
        (Finset.mem_Ico.mp hl).2.le⟩
    exact exists_echelon_calF_lowerStratumTerm_abs_le_B_l_of_raw_covering_bound
      f h_f hnm hkm (Finset.mem_Ico.mp hl).1 (Finset.mem_Ico.mp hl).2
      hCsup hT hSupport (hcount l hlIcc)
  obtain ⟨C₃, Ccrudenew, hC₃, hCcrudenew, hsum⟩ :=
    exists_echelon_calF_lowerSum_normalized_abs_le_corrected
      B f h_f hnm hk hT hCsize.le (by rfl) (by simpa [B] using hBcard)
      hpoint
  refine ⟨C₃, Ccrudenew, Csize, hC₃, hCcrudenew, hCsize, ?_⟩
  simpa [B, tsum_fintype] using hsum

/- [paper, `co:counting_matrices`, lines 1091--1100]
   Convert a height cutoff for the norm-bounded support family into the
   manuscript's `T^(m*k*d)` cardinality bound.  The cutoff inclusion is kept
   explicit: proving it is the paper's separate crude height estimate. -/
theorem boundedRowSpaces_ncard_le_of_height_subset
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} {Csup Cheight T : ℝ}
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := k)) m)
    (hCheight : 1 ≤ Cheight) (hT : 1 ≤ T)
    (hsubset :
      boundedRowSpaces (K := K) (n := n) (m := m) (k := k) Csup T ⊆
        heightBoundedRowSpaces (K := K) (m := m) (k := k) Cheight T) :
    ∃ Csize : ℝ, 0 < Csize ∧
      (Set.ncard
        (boundedRowSpaces (K := K) (n := n) (m := m) (k := k) Csup T) : ℝ) ≤
        Csize * T ^ (k * m * degree K) := by
  obtain ⟨cᵤ, hcᵤ, hupper⟩ :=
    heightBoundedRowSpaces_count_upper (K := K) hcount
  let B : Set (Grassmannian K m k) :=
    boundedRowSpaces (K := K) (n := n) (m := m) (k := k) Csup T
  let H : Set (Grassmannian K m k) :=
    heightBoundedRowSpaces (K := K) (m := m) (k := k) Cheight T
  have hHfin : H.Finite := by
    simpa [H] using heightBoundedRowSpaces_finite hcount hCheight hT
  have hcard : B.ncard ≤ H.ncard := by
    apply Set.ncard_le_ncard
    · simpa [B, H] using hsubset
    · exact hHfin
  have hcardR : (B.ncard : ℝ) ≤ (H.ncard : ℝ) := by
    exact_mod_cast hcard
  have hupper' : (H.ncard : ℝ) ≤
      cᵤ * (Cheight * T ^ (k * degree K)) ^ m := by
    exact hupper hCheight hT
  let Csize : ℝ := cᵤ * Cheight ^ m
  have hCsize : 0 < Csize := by
    dsimp [Csize]
    positivity
  refine ⟨Csize, hCsize, ?_⟩
  calc
    (B.ncard : ℝ) ≤ (H.ncard : ℝ) := hcardR
    _ ≤ cᵤ * (Cheight * T ^ (k * degree K)) ^ m := hupper'
    _ = Csize * T ^ (k * m * degree K) := by
      dsimp [Csize]
      rw [mul_pow, ← pow_mul]
      rw [show k * degree K * m = k * m * degree K by ring]
      ring

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

/- [derived consequence, paper equations `eq:main_eq` and `eq:left_side`,
   lines 758--815 and 1671--1679] Enlarge the support-sensitive row-space
   family to any finite family containing it.  This generic version is used
   to keep the manuscript's echelon family visible in the final assembly. -/
theorem fixedRankSum_eq_tsum_of_active_subset
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (B : Set (Grassmannian K m k))
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    {T : ℝ} (hT : 0 < T)
    (hactive : activeRowSpaces (K := K) (k := k) f T ⊆ B) :
    fixedRankSum n m k f T =
      ∑' V : {V : Grassmannian K m k // V ∈ B},
        ∑' A : {A : IntegralMatrix K n m //
            rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A = k},
          f (T⁻¹ • embedMatrix A.1) := by
  rw [fixedRankSum_eq_tsum_activeRowSpaces f h_f hT]
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
  have hindicator (V : Grassmannian K m k) :
      S.indicator g V = B.indicator g V := by
    by_cases hS : V ∈ S
    · have hB : V ∈ B := hactive hS
      simp [S, hS, hB]
    · have hz := hgzero V hS
      by_cases hB : V ∈ B
      · simp [S, hS, hB, hz]
      · simp [S, hS, hB]
  calc
    (∑' V : S, g V) =
        ∑' V : Grassmannian K m k, S.indicator g V :=
      tsum_subtype S g
    _ = ∑' V : Grassmannian K m k, B.indicator g V := by
      apply tsum_congr
      exact hindicator
    _ = ∑' V : B, g V := (tsum_subtype B g).symm
    _ = ∑' V : {V : Grassmannian K m k // V ∈ B},
        ∑' A : {A : IntegralMatrix K n m //
            rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A = k},
          f (T⁻¹ • embedMatrix A.1) := by
      rfl

/- [paper, `le:crude_bound` and `eq:left_side`, lines 784--815]
   The compact-support reduction is now stated with the manuscript's exact
   echelon family `𝓕_k(T)`.  The row-space image is only the indexing bridge;
   the summands are converted back to the row-lattice language by the proved
   `Λ_D`/row-lattice equality. -/
theorem exists_fixedRankSum_eq_tsum_echelon_calF_rowMatrixZLattice
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    {T : ℝ} (hT : 0 < T) :
    ∃ Csup : ℝ, 0 < Csup ∧
      fixedRankSum n m k f T =
        ∑' V : {V : Grassmannian K m k //
            V ∈ echelonRowSpace (K := K) ''
              calF (K := K) (l := k) (m := m) (n := n) Csup T},
          ∑' A : {A : rowMatrixZLattice V.1 n //
              rowMatrixRank V.1 A = k},
            f (T⁻¹ • (((A.1 : rowMatrixRealSpan V.1 n) :
              M n m (K_ℝ[K])))) := by
  obtain ⟨Csup, hCsup, hactive⟩ :=
    exists_activeRowSpaces_subset_echelon_calF_image f h_f
  refine ⟨Csup, hCsup, ?_⟩
  have hdecomp := fixedRankSum_eq_tsum_of_active_subset
    (B := echelonRowSpace (K := K) ''
      calF (K := K) (l := k) (m := m) (n := n) Csup T)
    f h_f hT (hactive T hT)
  calc
    fixedRankSum n m k f T =
        ∑' V : {V : Grassmannian K m k //
            V ∈ echelonRowSpace (K := K) ''
              calF (K := K) (l := k) (m := m) (n := n) Csup T},
          ∑' A : {A : IntegralMatrix K n m //
              rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A = k},
            f (T⁻¹ • embedMatrix A.1) := hdecomp
    _ = ∑' V : {V : Grassmannian K m k //
            V ∈ echelonRowSpace (K := K) ''
              calF (K := K) (l := k) (m := m) (n := n) Csup T},
          ∑' A : {A : rowMatrixZLattice V.1 n //
              rowMatrixRank V.1 A = k},
            f (T⁻¹ • (((A.1 : rowMatrixRealSpan V.1 n) :
              M n m (K_ℝ[K])))) := by
      apply tsum_congr
      intro V
      exact (tsum_rowMatrixZLattice_rank_eq_integralRowMatrices V.1 f T).symm

/- [derived consequence, paper `le:crude_bound` and `eq:left_side`,
   lines 784--815 and 1671--1679] This is the preceding support reduction
   with the manuscript's chosen support constant left explicit.  It is the
   form used by the final estimate, where the same `Csup` must also control
   every lower-rank family `𝓕_l(T)`. -/
theorem fixedRankSum_eq_tsum_echelon_calF_rowMatrixZLattice_of_support_bound
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    {Csup T : ℝ} (hT : 0 < T)
    (hSupport : ∀ A : IntegralMatrix K n m,
      f (T⁻¹ • embedMatrix A) ≠ 0 →
        ‖embedMatrix A‖ ≤ Csup * T) :
    fixedRankSum n m k f T =
      ∑' V : {V : Grassmannian K m k //
          V ∈ echelonRowSpace (K := K) ''
            calF (K := K) (l := k) (m := m) (n := n) Csup T},
        ∑' A : {A : rowMatrixZLattice V.1 n //
            rowMatrixRank V.1 A = k},
          f (T⁻¹ • (((A.1 : rowMatrixRealSpan V.1 n) :
            M n m (K_ℝ[K])))) := by
  let B : Set (Grassmannian K m k) := echelonRowSpace (K := K) ''
    calF (K := K) (l := k) (m := m) (n := n) Csup T
  have hactive : activeRowSpaces (K := K) (k := k) f T ⊆ B := by
    intro V hV
    simpa [B] using
      (activeRowSpaces_subset_echelon_calF_image_of_support_bound
        (K := K) (n := n) (m := m) (k := k) f hT hSupport hV)
  have hdecomp := fixedRankSum_eq_tsum_of_active_subset B f h_f hT hactive
  calc
    fixedRankSum n m k f T =
        ∑' V : B,
          ∑' A : {A : IntegralMatrix K n m //
              rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A = k},
            f (T⁻¹ • embedMatrix A.1) := hdecomp
    _ = ∑' V : B,
          ∑' A : {A : rowMatrixZLattice V.1 n //
              rowMatrixRank V.1 A = k},
            f (T⁻¹ • (((A.1 : rowMatrixRealSpan V.1 n) :
              M n m (K_ℝ[K])))) := by
      apply tsum_congr
      intro V
      exact (tsum_rowMatrixZLattice_rank_eq_integralRowMatrices V.1 f T).symm
    _ = ∑' V : {V : Grassmannian K m k //
          V ∈ echelonRowSpace (K := K) ''
            calF (K := K) (l := k) (m := m) (n := n) Csup T},
        ∑' A : {A : rowMatrixZLattice V.1 n //
            rowMatrixRank V.1 A = k},
          f (T⁻¹ • (((A.1 : rowMatrixRealSpan V.1 n) :
            M n m (K_ℝ[K])))) := by
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

/- [Lean infrastructure for paper equation `eq:value_of_c`, lines 197--202]
   Internally index the main term by its Grassmannian point.  The exact proved
   bridge back to the manuscript's echelon representative, denominator
   `𝔇(D)⁻ⁿ`, and coordinate integral is
   `tsum_echelon_denominator_integral_eq_mainConstant` in
   `Counting/MainTermNormalization.lean`; this definition is therefore not
   presented as a notation-changing replacement for the paper's formula. -/
noncomputable def mainConstant
    {K : Type*} [Field K] [NumberField K]
    (n m k : ℕ) (f : M n m (K_ℝ[K]) → ℝ) : ℝ :=
  ∑' V : Grassmannian K m k,
    (rowMatrixLatticeCovolume V n)⁻¹ * rowMatrixSubspaceIntegral V n f

/- [derived consequence, paper equation `eq:value_of_c`, lines 197--203,
   and `le:without_rank_cond`, lines 1038--1040] The row-space main-term
   constant has the manuscript's reciprocal-height normalization.  The
   equality is proved from the exact product-covolume identity; it is not a
   replacement of the paper's echelon-indexed definition. -/
theorem mainConstant_eq_height_normalized
    {K : Type*} [Field K] [NumberField K]
    (n m k : ℕ) (f : M n m (K_ℝ[K]) → ℝ) :
    mainConstant n m k f =
      ∑' V : Grassmannian K m k,
        (rowSpaceHeight V)⁻¹ ^ n * rowMatrixSubspaceIntegral V n f := by
  unfold mainConstant
  apply tsum_congr
  intro V
  rw [rowMatrixLatticeCovolume_eq_rowSpaceHeight_pow]
  rw [inv_pow]

/- [derived consequence of paper equation `eq:just_as_before`, lines
   1724--1753] This is the noncritical radius-sum estimate in the exact form
   consumed by the manuscript's Voronoi Riemann-sum error: the previously
   proved `𝓕_k(T)` bound is reindexed to its equal row-space family and the
   product-covolume identity converts the denominator. -/
theorem exists_uniform_boundedRowSpaces_latticeVoronoi_radius_sum_bound_of_noncritical
    {K : Type*} [Field K] [NumberField K]
    {m n j : ℕ} {Cprod : ℝ} (hm : 0 < m)
    (hgap : 1 < (n - m) * degree K) (hCprod : 0 ≤ Cprod) :
    ∃ C_R : ℝ, 0 < C_R ∧
      ∀ {Csup C T : ℝ}
        [Fintype (boundedRowSpaces (K := K) (n := n) (m := m) (k := j + 1)
          Csup T)]
        (hCproj : rowKRealSmulBound (K := K) (m := m) *
          numberFieldCoefficientRadius K ≤ C)
        (hCsup : Csup ≤ C) (hT : 0 ≤ T)
        (hprod : ∀ D : EchelonMatrix K (j + 1) m,
          D ∈ calF (K := K) (l := j + 1) (m := m) (n := n) Csup T →
            (∏ i : Fin (j + 1),
              ‖((rowSuccessiveMinimum (echelonRowSpace D) i :
                rowZLattice (echelonRowSpace D)) :
                  rowRealSpan (echelonRowSpace D))‖ ^ degree K) ≤
              Cprod * rowSpaceHeight (echelonRowSpace D)),
        (∑ V : boundedRowSpaces (K := K) (n := n) (m := m) (k := j + 1)
          Csup T,
          (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1)) /
            rowMatrixLatticeCovolume V.1 n) ≤ C_R := by
  obtain ⟨Cfinite, hCfinite, hbound⟩ :=
    exists_uniform_boundedRowSpaces_coveringRadius_sum_bound_of_noncritical
      (K := K) (j := j) hm hgap hCprod
  let C_R : ℝ := Real.sqrt (n : ℝ) * Cfinite + 1
  have hsqrt : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  refine ⟨C_R, ?_, ?_⟩
  · have hnonneg : 0 ≤ Real.sqrt (n : ℝ) * Cfinite :=
      mul_nonneg hsqrt hCfinite.le
    dsimp [C_R]
    linarith
  · intro Csup C T _ hCproj hCsup hT hprod
    have hradius := hbound hCproj hCsup hT hprod
    have hrewrite :
        (∑ V : boundedRowSpaces (K := K) (n := n) (m := m) (k := j + 1)
          Csup T,
          (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1)) /
            rowMatrixLatticeCovolume V.1 n) =
          Real.sqrt (n : ℝ) *
            (∑ V : boundedRowSpaces (K := K) (n := n) (m := m) (k := j + 1)
              Csup T,
              latticeCoveringRadius (rowZLattice V.1) /
                (rowSpaceHeight V.1) ^ n) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro V _
      rw [rowMatrixLatticeCovolume_eq_rowSpaceHeight_pow]
      ring
    rw [hrewrite]
    calc
      Real.sqrt (n : ℝ) *
          (∑ V : boundedRowSpaces (K := K) (n := n) (m := m) (k := j + 1)
            Csup T,
            latticeCoveringRadius (rowZLattice V.1) /
              (rowSpaceHeight V.1) ^ n) ≤
          Real.sqrt (n : ℝ) * Cfinite :=
        mul_le_mul_of_nonneg_left hradius hsqrt
      _ ≤ C_R := by
        dsimp [C_R]
        linarith

/- [derived consequence] Paper equation `eq:just_as_before`,
   `papers/katznelson.tex`, lines 1724--1753, consumes a product bound for
   the successive minima uniformly in the echelon matrix.  The proved
   Fieker--Stehlé/Minkowski-II derivation in `FiekerStehle.lean` supplies that
   bound, and this theorem then applies the preceding reindexing/Voronoi
   estimate. -/
theorem exists_uniform_boundedRowSpaces_latticeVoronoi_radius_sum_bound_of_noncritical_of_fiekerStehle
    {K : Type*} [Field K] [NumberField K]
    {m n j : ℕ} (hm : 0 < m)
    (hgap : 1 < (n - m) * degree K) :
    ∃ C_R : ℝ, 0 < C_R ∧
      ∀ {Csup C T : ℝ}
        [Fintype (boundedRowSpaces (K := K) (n := n) (m := m) (k := j + 1)
          Csup T)]
        (hCproj : rowKRealSmulBound (K := K) (m := m) *
          numberFieldCoefficientRadius K ≤ C)
        (hCsup : Csup ≤ C) (hT : 0 ≤ T),
        (∑ V : boundedRowSpaces (K := K) (n := n) (m := m) (k := j + 1)
          Csup T,
          (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1)) /
            rowMatrixLatticeCovolume V.1 n) ≤ C_R := by
  obtain ⟨Cprod, hCprod, hprod⟩ :=
    exists_rowSuccessiveMinimum_product_le_height_of_euclideanMinkowskiSecond
      (K := K) (m := m) (k := j + 1) (Nat.succ_pos j)
  obtain ⟨C_R, hC_R, hbound⟩ :=
    exists_uniform_boundedRowSpaces_latticeVoronoi_radius_sum_bound_of_noncritical
      (K := K) (j := j) hm hgap hCprod.le
  refine ⟨C_R, hC_R, ?_⟩
  intro Csup C T _ hCproj hCsup hT
  apply hbound hCproj hCsup hT
  intro D _
  exact hprod (echelonRowSpace D)

/- [derived consequence of paper equation `eq:just_as_before`, lines
   1724--1753] In rank one, the product-of-minima estimate required in the
   preceding noncritical radius argument is proved locally from the first
   Minkowski theorem (`exists_rowSuccessiveMinimum_prod_norm_pow_le_rank_one`),
   rather than assumed through the all-rank Fieker--Stehlé interface.  This is
   a supporting Lean proof of the rank-one input; it does not claim to replace
   the cited all-rank theorem. -/
theorem exists_uniform_boundedRowSpaces_latticeVoronoi_radius_sum_bound_of_noncritical_rank_one
    {K : Type*} [Field K] [NumberField K]
    {m n : ℕ} (hm : 0 < m)
    (hgap : 1 < (n - m) * degree K) :
    ∃ C_R : ℝ, 0 < C_R ∧
      ∀ {Csup C T : ℝ}
        [Fintype (boundedRowSpaces (K := K) (n := n) (m := m) (k := 1)
          Csup T)]
        (hCproj : rowKRealSmulBound (K := K) (m := m) *
          numberFieldCoefficientRadius K ≤ C)
        (hCsup : Csup ≤ C) (hT : 0 ≤ T),
        (∑ V : boundedRowSpaces (K := K) (n := n) (m := m) (k := 1)
          Csup T,
          (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1)) /
            rowMatrixLatticeCovolume V.1 n) ≤ C_R := by
  obtain ⟨Cprod, hCprod, hprod⟩ :=
    exists_rowSuccessiveMinimum_prod_norm_pow_le_rank_one (K := K) m
  obtain ⟨C_R, hC_R, hbound⟩ :=
    exists_uniform_boundedRowSpaces_latticeVoronoi_radius_sum_bound_of_noncritical
      (K := K) (j := 0) hm hgap hCprod.le
  refine ⟨C_R, hC_R, ?_⟩
  intro Csup C T _ hCproj hCsup hT
  apply hbound hCproj hCsup hT
  intro D _
  exact hprod (echelonRowSpace D)

/- The two finite-family expressions used in the final fixed-rank assembly.
   Naming them keeps the later triangle-inequality bridge readable while
   preserving the paper's row-space summands. -/
noncomputable def finiteRowMatrixRankNormalizedSum
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (B : Set (Grassmannian K m k))
    [Fintype B]
    (f : M n m (K_ℝ[K]) → ℝ) (T : ℝ) : ℝ :=
  ∑ V : B,
    (∑' A : {A : rowMatrixZLattice V.1 n // rowMatrixRank V.1 A = k},
      f (T⁻¹ • (((A.1 : rowMatrixRealSpan V.1 n) :
        M n m (K_ℝ[K]))))) /
      T ^ (n * (k * degree K))

noncomputable def finiteRowMatrixMainTermSum
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (B : Set (Grassmannian K m k))
    [Fintype B]
    (f : M n m (K_ℝ[K]) → ℝ) : ℝ :=
  ∑ V : B,
    (rowMatrixLatticeCovolume V.1 n)⁻¹ *
      rowMatrixSubspaceIntegral V.1 n f

/- Normalize the finite-family rank sum.  This is the algebraic passage from
   the manuscript's finite sum in `eq:left_side` to the scale used in the
   Riemann estimate; the finite-family reindexing itself is supplied by
   `fixedRankSum_eq_tsum_boundedRowSpaces_rowMatrixZLattice`. -/
theorem fixedRankSum_normalized_eq_finiteRowMatrixRankNormalizedSum
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (B : Set (Grassmannian K m k)) [Fintype B]
    {f : M n m (K_ℝ[K]) → ℝ} {T : ℝ} (hT : 0 < T)
    (hdecomp :
      fixedRankSum n m k f T =
        ∑' V : B,
          ∑' A : {A : rowMatrixZLattice V.1 n // rowMatrixRank V.1 A = k},
            f (T⁻¹ • (((A.1 : rowMatrixRealSpan V.1 n) :
              M n m (K_ℝ[K]))))) :
    fixedRankSum n m k f T / T ^ (n * (k * degree K)) =
      finiteRowMatrixRankNormalizedSum B f T := by
  rw [hdecomp]
  simp only [tsum_fintype]
  unfold finiteRowMatrixRankNormalizedSum
  rw [Finset.sum_div]

/- Transfer any finite-family error estimate back to the original rank sum.
   This is the final reindexing step needed before inserting the quantitative
   bounds from the manuscript. -/
theorem fixedRankSum_normalized_error_of_finite_family
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (B : Set (Grassmannian K m k)) [Fintype B]
    {f : M n m (K_ℝ[K]) → ℝ} {T E : ℝ} (hT : 0 < T)
    (hdecomp :
      fixedRankSum n m k f T =
        ∑' V : B,
          ∑' A : {A : rowMatrixZLattice V.1 n // rowMatrixRank V.1 A = k},
            f (T⁻¹ • (((A.1 : rowMatrixRealSpan V.1 n) :
              M n m (K_ℝ[K])))))
    (hfinite :
      |finiteRowMatrixRankNormalizedSum B f T -
        mainConstant n m k f| ≤ E) :
    |fixedRankSum n m k f T / T ^ (n * (k * degree K)) -
        mainConstant n m k f| ≤ E := by
  rw [fixedRankSum_normalized_eq_finiteRowMatrixRankNormalizedSum B hT hdecomp]
  exact hfinite

/- The preceding identity specialized to the norm-bounded support family
   `𝓕_k(T)`.  Finiteness is proved from the integral-matrix norm bound, so the
   finite sum is available without adding a finiteness axiom. -/
theorem fixedRankSum_normalized_eq_boundedRowSpaces
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    {T Csup : ℝ}
    [Fintype (boundedRowSpaces (K := K) (n := n) (m := m) (k := k) Csup T)]
    (hT : 0 < T)
    (hactive : activeRowSpaces (K := K) (k := k) f T ⊆
      boundedRowSpaces (K := K) (n := n) (m := m) (k := k) Csup T) :
    fixedRankSum n m k f T / T ^ (n * (k * degree K)) =
      finiteRowMatrixRankNormalizedSum
        (boundedRowSpaces (K := K) (n := n) (m := m) (k := k) Csup T) f T := by
  let B : Set (Grassmannian K m k) :=
    boundedRowSpaces (K := K) (n := n) (m := m) (k := k) Csup T
  have hdecomp : fixedRankSum n m k f T =
      ∑' V : B,
        ∑' A : {A : rowMatrixZLattice V.1 n // rowMatrixRank V.1 A = k},
          f (T⁻¹ • (((A.1 : rowMatrixRealSpan V.1 n) :
            M n m (K_ℝ[K])))) := by
    exact fixedRankSum_eq_tsum_boundedRowSpaces_rowMatrixZLattice
      f h_f hT hactive
  exact fixedRankSum_normalized_eq_finiteRowMatrixRankNormalizedSum
    B hT hdecomp

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
      |(rowSpaceHeight V)⁻¹ ^ n * rowMatrixSubspaceIntegral V n f| ≤
        C * (rowSpaceHeight V)⁻¹ ^ n) :
    Summable (fun V : Grassmannian K m k =>
      (rowMatrixLatticeCovolume V n)⁻¹ * rowMatrixSubspaceIntegral V n f) := by
  apply summable_of_abs_le_height_inv_pow_all hcount hnm
  intro V hV
  simpa [rowMatrixLatticeCovolume_eq_rowSpaceHeight_pow, inv_pow] using hdom V hV

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
      |(rowSpaceHeight V)⁻¹ ^ n * rowMatrixSubspaceIntegral V n f| ≤
        C * (rowSpaceHeight V)⁻¹ ^ n) :
    ∃ Ctail : ℝ, 0 < Ctail ∧ ∀ {N : ℕ}, 1 ≤ N →
      |∑' V : {V : Grassmannian K m k //
          (N : ℝ) ≤ rowSpaceHeight V},
        (rowMatrixLatticeCovolume V.1 n)⁻¹ *
          rowMatrixSubspaceIntegral V.1 n f| ≤
        Ctail * ((N : ℝ) ^ (-((n - m : ℕ) : ℝ))) := by
  refine weighted_height_tsum_tail_abs_le
    (w := fun V =>
      (rowMatrixLatticeCovolume V n)⁻¹ * rowMatrixSubspaceIntegral V n f)
    hcount hnm hC ?_
  intro V hV
  simpa [rowMatrixLatticeCovolume_eq_rowSpaceHeight_pow, inv_pow] using hdom V hV

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
      |(rowSpaceHeight V)⁻¹ ^ n * rowMatrixSubspaceIntegral V n f| ≤
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
    weighted_height_tsum_tail_inv_pow_le (w := g) hcount hnm hC (by
      intro V hV
      simpa [g, rowMatrixLatticeCovolume_eq_rowSpaceHeight_pow, inv_pow] using
        hdom V hV)
  let β := {V : Grassmannian K m k // V ∉ B}
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
  have hsum_abs : Summable (fun V : Grassmannian K m k => |g V|) := by
    apply summable_of_abs_le_height_inv_pow_all hcount hnm
    intro V hV
    simpa [g, rowMatrixLatticeCovolume_eq_rowSpaceHeight_pow, inv_pow] using
      hdom V hV
  have hsum_compl_abs : Summable (fun V : β => |g V.1|) := by
    have hinc : Function.Injective (fun V : β => V.1) := by
      intro V W hVW
      apply Subtype.ext
      exact hVW
    exact hsum_abs.comp_injective hinc
  have hdecomp := hsum.sum_add_tsum_subtype_compl B
  have htail_subset :
      (∑' V : β, |g V.1|) ≤
        ∑' V : βN, |g V.1| := by
    have hsum_tail : Summable (fun V : βN => |g V.1|) := by
      have hinc : Function.Injective (fun V : βN => V.1) := by
        intro V W hVW
        apply Subtype.ext
        exact hVW
      exact hsum_abs.comp_injective hinc
    have hle : ∀ V : β, |g V.1| ≤ |g (e V).1| := by
      intro V
      rfl
    exact hsum_compl_abs.tsum_le_tsum_of_inj e he
      (fun V hV => abs_nonneg (g V)) hle hsum_tail
  have htail' :
      (∑' V : βN, |g V.1|) ≤ Ctail *
        ((N : ℝ) ^ (-((n - m : ℕ) : ℝ))) := by
    simpa [βN, g] using htail hN
  have hcompl_abs :
      |∑' V : β, g V.1| ≤ Ctail *
        ((N : ℝ) ^ (-((n - m : ℕ) : ℝ))) := by
    have hsum_compl_norm : Summable (fun V : β => ‖g V.1‖) := by
      simpa [Real.norm_eq_abs] using hsum_compl_abs
    calc
      |∑' V : β, g V.1| ≤ ∑' V : β, |g V.1| :=
        by simpa [Real.norm_eq_abs] using
          (norm_tsum_le_tsum_norm hsum_compl_norm)
      _ ≤ ∑' V : βN, |g V.1| := htail_subset
      _ ≤ Ctail * ((N : ℝ) ^ (-((n - m : ℕ) : ℝ))) := htail'
  have hdecomp' :
      mainConstant n m k f =
        (∑ V ∈ B, g V) + ∑' V : β, g V.1 := by
    simpa [mainConstant, g, β] using hdecomp.symm
  refine ⟨Ctail, hCtail, ?_⟩
  rw [hdecomp']
  simpa [g, abs_sub_comm] using hcompl_abs

/- The same tail estimate in the set/subtype notation used by the finite
   row-space decomposition. -/
set_option maxHeartbeats 800000 in
theorem finite_mainConstant_subtype_tail_abs_le
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (hnm : m < n)
    (B : Set (Grassmannian K m k)) [Fintype B]
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := k)) m)
    {f : M n m (K_ℝ[K]) → ℝ} {C : ℝ} {N : ℕ} (hC : 0 < C)
    (hN : 1 ≤ N)
    (houtside : ∀ V : Grassmannian K m k, V ∉ B →
      (N : ℝ) ≤ rowSpaceHeight V)
    (hdom : ∀ V : Grassmannian K m k, 1 ≤ rowSpaceHeight V →
      |(rowSpaceHeight V)⁻¹ ^ n * rowMatrixSubspaceIntegral V n f| ≤
        C * (rowSpaceHeight V)⁻¹ ^ n) :
    ∃ Ctail : ℝ, 0 < Ctail ∧
      |mainConstant n m k f - finiteRowMatrixMainTermSum B f| ≤
        Ctail * ((N : ℝ) ^ (-((n - m : ℕ) : ℝ))) := by
  let hBfin : B.Finite := Set.toFinite B
  let F : Finset (Grassmannian K m k) := hBfin.toFinset
  have hFB : (F : Set (Grassmannian K m k)) = B := by
    exact hBfin.coe_toFinset
  have houtsideF : ∀ V : Grassmannian K m k,
      V ∉ (F : Set (Grassmannian K m k)) →
        (N : ℝ) ≤ rowSpaceHeight V := by
    intro V hV
    apply houtside V
    rw [← hFB]
    exact hV
  obtain ⟨Ctail, hCtail, htail⟩ := finite_mainConstant_tail_abs_le
    hnm F hcount hC hN houtsideF hdom
  refine ⟨Ctail, hCtail, ?_⟩
  let e : B ≃ (F : Set (Grassmannian K m k)) :=
    (Set.equivOfEq hFB).symm
  have hsum_subtype :
      (∑ V : B,
        (rowMatrixLatticeCovolume V.1 n)⁻¹ *
          rowMatrixSubspaceIntegral V.1 n f) =
        ∑ V ∈ F,
          (rowMatrixLatticeCovolume V n)⁻¹ *
            rowMatrixSubspaceIntegral V n f := by
    calc
      (∑ V : B,
          (rowMatrixLatticeCovolume V.1 n)⁻¹ *
            rowMatrixSubspaceIntegral V.1 n f) =
          ∑ V : (F : Set (Grassmannian K m k)),
            (rowMatrixLatticeCovolume V.1 n)⁻¹ *
              rowMatrixSubspaceIntegral V.1 n f := by
        calc
          (∑ V : B,
              (rowMatrixLatticeCovolume V.1 n)⁻¹ *
                rowMatrixSubspaceIntegral V.1 n f) =
              ∑ V : B,
                (rowMatrixLatticeCovolume (e V).1 n)⁻¹ *
                  rowMatrixSubspaceIntegral (e V).1 n f := by
            apply Fintype.sum_congr
            intro V
            rfl
          _ = ∑ V : (F : Set (Grassmannian K m k)),
              (rowMatrixLatticeCovolume V.1 n)⁻¹ *
                rowMatrixSubspaceIntegral V.1 n f :=
            e.sum_comp (fun V : (F : Set (Grassmannian K m k)) =>
              (rowMatrixLatticeCovolume V.1 n)⁻¹ *
                rowMatrixSubspaceIntegral V.1 n f)
      _ = ∑ V ∈ F,
          (rowMatrixLatticeCovolume V n)⁻¹ *
            rowMatrixSubspaceIntegral V n f := by
        simpa using (F.tsum_subtype (fun V =>
          (rowMatrixLatticeCovolume V n)⁻¹ *
            rowMatrixSubspaceIntegral V n f))
  simpa [finiteRowMatrixMainTermSum, hsum_subtype] using htail

/- [derived consequence of paper `co:tail`, lines 1156--1170] Apply the
   manuscript's summation-by-parts tail bound to the concrete bounded family
   used in the finite-rank decomposition.  The Schmidt height count, the
   product estimate, and the normalized integral domination are all explicit
   hypotheses; no cited theorem is silently imported as an axiom. -/
set_option maxHeartbeats 1200000 in
theorem exists_boundedRowSpaces_mainConstant_tail_abs_le
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (hnm : m < n) (hkn : k ≤ n) (hkm : k ≤ m) (hk : 0 < k)
    {Csup T Cprod : ℝ}
    (hCsup : 0 < Csup) (hT : 0 < T) (hCprod : 0 < Cprod)
    [Fintype (boundedRowSpaces (K := K) (n := n) (m := m) (k := k)
      Csup T)]
    (hprod : ∀ D : EchelonMatrix K k m,
      (∏ i : Fin k,
        ‖((rowSuccessiveMinimum (echelonRowSpace D) i :
            rowZLattice (echelonRowSpace D)) :
            rowRealSpan (echelonRowSpace D))‖ ^ degree K) ≤
        Cprod * rowSpaceHeight (echelonRowSpace D))
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := k)) m)
    {f : M n m (K_ℝ[K]) → ℝ} {C : ℝ} (hC : 0 < C)
    (hdom : ∀ V : Grassmannian K m k, 1 ≤ rowSpaceHeight V →
      |(rowSpaceHeight V)⁻¹ ^ n * rowMatrixSubspaceIntegral V n f| ≤
        C * (rowSpaceHeight V)⁻¹ ^ n) :
    ∃ Clower : ℝ, 0 < Clower ∧
      ∀ {N : ℕ}, 1 ≤ N → (N : ℝ) ≤ Clower * T ^ degree K →
        ∃ Ctail : ℝ, 0 < Ctail ∧
          |mainConstant n m k f -
              finiteRowMatrixMainTermSum
                (boundedRowSpaces (K := K) (n := n) (m := m) (k := k)
                  Csup T) f| ≤
            Ctail * ((N : ℝ) ^ (-((n - m : ℕ) : ℝ))) := by
  obtain ⟨Clower, hClower, hcutoff⟩ :=
    exists_boundedRowSpaces_complement_height_cutoff
      hkn hkm hk hCsup hT hCprod hprod
  refine ⟨Clower, hClower, ?_⟩
  intro N hN hNcut
  have houtside : ∀ V : Grassmannian K m k,
      V ∉ boundedRowSpaces (K := K) (n := n) (m := m) (k := k) Csup T →
      (N : ℝ) ≤ rowSpaceHeight V := by
    intro V hV
    exact hcutoff hNcut V hV
  obtain ⟨Ctail, hCtail, htail⟩ :=
    finite_mainConstant_subtype_tail_abs_le hnm
      (boundedRowSpaces (K := K) (n := n) (m := m) (k := k) Csup T)
      hcount hC hN
      houtside hdom
  refine ⟨Ctail, hCtail, ?_⟩
  exact htail

/- [paper, equations (19)--(21) and `co:tail`, lines 1671--1694]
   Add the omitted main-term tail to the finite-family error.  The finite
   estimate and tail estimate are kept as separate hypotheses so that the
   source of every constant remains visible. -/
theorem finite_rowMatrix_rank_error_with_mainConstant_bound
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (B : Set (Grassmannian K m k)) [Fintype B]
    {f : M n m (K_ℝ[K]) → ℝ} {T Cₐ C_R E_lower E_tail : ℝ}
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
          rowMatrixLatticeCovolume V.1 n) ≤ C_R)
    (hTail :
      |mainConstant n m k f - finiteRowMatrixMainTermSum B f| ≤ E_tail) :
    |finiteRowMatrixRankNormalizedSum B f T -
      mainConstant n m k f| ≤ Cₐ * C_R / T + E_lower + E_tail := by
  have hfinite := finite_rowMatrix_rank_error_with_radius_sum_bound
    B hT hCₐ hpoint hLower hRadius
  have hfinite' :
      |finiteRowMatrixRankNormalizedSum B f T -
        finiteRowMatrixMainTermSum B f| ≤ Cₐ * C_R / T + E_lower := by
    simpa [finiteRowMatrixRankNormalizedSum, finiteRowMatrixMainTermSum]
      using hfinite
  have htail' :
      |finiteRowMatrixMainTermSum B f - mainConstant n m k f| ≤ E_tail := by
    simpa [abs_sub_comm] using hTail
  have hsplit : finiteRowMatrixRankNormalizedSum B f T -
      mainConstant n m k f =
      (finiteRowMatrixRankNormalizedSum B f T -
        finiteRowMatrixMainTermSum B f) +
      (finiteRowMatrixMainTermSum B f - mainConstant n m k f) := by ring
  rw [hsplit]
  calc
    |(finiteRowMatrixRankNormalizedSum B f T -
        finiteRowMatrixMainTermSum B f) +
        (finiteRowMatrixMainTermSum B f - mainConstant n m k f)| ≤
        |finiteRowMatrixRankNormalizedSum B f T -
          finiteRowMatrixMainTermSum B f| +
        |finiteRowMatrixMainTermSum B f - mainConstant n m k f| :=
      abs_add_le _ _
    _ ≤ (Cₐ * C_R / T + E_lower) + E_tail :=
      add_le_add hfinite' htail'
    _ = Cₐ * C_R / T + E_lower + E_tail := by ring

/- [derived consequence of paper equations (19)--(21) and `co:tail`, lines
   1156--1170 and 1671--1694] This is the same finite-family/main-term-tail
   assembly with the paper's displayed intrinsic error
   `sqrt n * rho(Λ_D)`, rather than the auxiliary fundamental-domain radius.
   It is derived from the already paper-facing finite-family estimate. -/
theorem finite_rowMatrix_rank_latticeVoronoi_error_with_mainConstant_bound
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (B : Set (Grassmannian K m k)) [Fintype B]
    {f : M n m (K_ℝ[K]) → ℝ} {T Cₐ C_R E_lower E_tail : ℝ}
    (hT : 0 < T) (hCₐ : 0 ≤ Cₐ)
    (hpoint : ∀ V : B,
      |(∑' A : {A : rowMatrixZLattice V.1 n // rowMatrixRank V.1 A = k},
          f (T⁻¹ • (((A.1 : rowMatrixRealSpan V.1 n) :
            M n m (K_ℝ[K]))))) /
            T ^ (n * (k * degree K)) -
          (rowMatrixLatticeCovolume V.1 n)⁻¹ *
            rowMatrixSubspaceIntegral V.1 n f| ≤
        Cₐ * (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1)) /
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
        (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1)) /
          rowMatrixLatticeCovolume V.1 n) ≤ C_R)
    (hTail :
      |mainConstant n m k f - finiteRowMatrixMainTermSum B f| ≤ E_tail) :
    |finiteRowMatrixRankNormalizedSum B f T -
      mainConstant n m k f| ≤ Cₐ * C_R / T + E_lower + E_tail := by
  have hfinite := finite_rowMatrix_rank_error_with_latticeVoronoi_radius_sum_bound
    B hT hCₐ hpoint hLower hRadius
  have hfinite' :
      |finiteRowMatrixRankNormalizedSum B f T -
        finiteRowMatrixMainTermSum B f| ≤ Cₐ * C_R / T + E_lower := by
    simpa [finiteRowMatrixRankNormalizedSum, finiteRowMatrixMainTermSum]
      using hfinite
  have htail' :
      |finiteRowMatrixMainTermSum B f - mainConstant n m k f| ≤ E_tail := by
    simpa [abs_sub_comm] using hTail
  have hsplit : finiteRowMatrixRankNormalizedSum B f T -
      mainConstant n m k f =
      (finiteRowMatrixRankNormalizedSum B f T -
        finiteRowMatrixMainTermSum B f) +
      (finiteRowMatrixMainTermSum B f - mainConstant n m k f) := by ring
  rw [hsplit]
  calc
    |(finiteRowMatrixRankNormalizedSum B f T -
        finiteRowMatrixMainTermSum B f) +
        (finiteRowMatrixMainTermSum B f - mainConstant n m k f)| ≤
        |finiteRowMatrixRankNormalizedSum B f T -
          finiteRowMatrixMainTermSum B f| +
        |finiteRowMatrixMainTermSum B f - mainConstant n m k f| :=
      abs_add_le _ _
    _ ≤ (Cₐ * C_R / T + E_lower) + E_tail :=
      add_le_add hfinite' htail'
    _ = Cₐ * C_R / T + E_lower + E_tail := by ring

/- [paper, equations (19)--(21) and `co:tail`, lines 1671--1694]
   Once the finite-family estimates and the height cutoff are available, this
   is the complete fixed-rank estimate for that family.  The theorem exposes
   every paper-specific input instead of packaging it as an axiom. -/
theorem finite_rowMatrix_rank_error_with_height_tail_bound
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (B : Set (Grassmannian K m k)) [Fintype B]
    {f : M n m (K_ℝ[K]) → ℝ} {T Cₐ C_R E_lower C_height : ℝ} {N : ℕ}
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
          rowMatrixLatticeCovolume V.1 n) ≤ C_R)
    (hnm : m < n)
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := k)) m)
    (hCheight : 0 < C_height) (hN : 1 ≤ N)
    (houtside : ∀ V : Grassmannian K m k, V ∉ B →
      (N : ℝ) ≤ rowSpaceHeight V)
    (hdom : ∀ V : Grassmannian K m k, 1 ≤ rowSpaceHeight V →
      |(rowSpaceHeight V)⁻¹ ^ n * rowMatrixSubspaceIntegral V n f| ≤
        C_height * (rowSpaceHeight V)⁻¹ ^ n) :
    ∃ Ctail : ℝ, 0 < Ctail ∧
      |finiteRowMatrixRankNormalizedSum B f T -
        mainConstant n m k f| ≤
        Cₐ * C_R / T + E_lower +
          Ctail * ((N : ℝ) ^ (-((n - m : ℕ) : ℝ))) := by
  obtain ⟨Ctail, hCtail, hTail⟩ :=
    finite_mainConstant_subtype_tail_abs_le hnm B hcount hCheight hN
      houtside hdom
  refine ⟨Ctail, hCtail, ?_⟩
  exact finite_rowMatrix_rank_error_with_mainConstant_bound
    B hT hCₐ hpoint hLower hRadius hTail

/- [derived consequence of paper equations (19)--(21) and `co:tail`, lines
   1156--1170 and 1671--1694] Insert the paper's height-tail estimate into
   the finite intrinsic-Voronoi-radius estimate.  The height count is still
   an explicitly attributed input through `HasHeightCountBounds`. -/
theorem finite_rowMatrix_rank_latticeVoronoi_error_with_height_tail_bound
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (B : Set (Grassmannian K m k)) [Fintype B]
    {f : M n m (K_ℝ[K]) → ℝ} {T Cₐ C_R E_lower C_height : ℝ} {N : ℕ}
    (hT : 0 < T) (hCₐ : 0 ≤ Cₐ)
    (hpoint : ∀ V : B,
      |(∑' A : {A : rowMatrixZLattice V.1 n // rowMatrixRank V.1 A = k},
          f (T⁻¹ • (((A.1 : rowMatrixRealSpan V.1 n) :
            M n m (K_ℝ[K]))))) /
            T ^ (n * (k * degree K)) -
          (rowMatrixLatticeCovolume V.1 n)⁻¹ *
            rowMatrixSubspaceIntegral V.1 n f| ≤
        Cₐ * (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1)) /
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
        (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1)) /
          rowMatrixLatticeCovolume V.1 n) ≤ C_R)
    (hnm : m < n)
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := k)) m)
    (hCheight : 0 < C_height) (hN : 1 ≤ N)
    (houtside : ∀ V : Grassmannian K m k, V ∉ B →
      (N : ℝ) ≤ rowSpaceHeight V)
    (hdom : ∀ V : Grassmannian K m k, 1 ≤ rowSpaceHeight V →
      |(rowSpaceHeight V)⁻¹ ^ n * rowMatrixSubspaceIntegral V n f| ≤
        C_height * (rowSpaceHeight V)⁻¹ ^ n) :
    ∃ Ctail : ℝ, 0 < Ctail ∧
      |finiteRowMatrixRankNormalizedSum B f T -
        mainConstant n m k f| ≤
        Cₐ * C_R / T + E_lower +
          Ctail * ((N : ℝ) ^ (-((n - m : ℕ) : ℝ))) := by
  obtain ⟨Ctail, hCtail, hTail⟩ :=
    finite_mainConstant_subtype_tail_abs_le hnm B hcount hCheight hN
      houtside hdom
  refine ⟨Ctail, hCtail, ?_⟩
  exact finite_rowMatrix_rank_latticeVoronoi_error_with_mainConstant_bound
    B hT hCₐ hpoint hLower hRadius hTail

/- [derived consequence, paper equations (19)--(21) and `co:tail`, lines
   1038--1061, 1156--1170, and 1671--1694] Assemble the fixed-rank estimate
   for a finite row-space family.  The local Riemann constants are selected
   uniformly by the preceding finite-family lemma; the lower-rank, radius,
   and height-tail estimates remain explicit inputs from the corresponding
   paper steps. -/
set_option maxHeartbeats 1200000 in
theorem exists_fixedRankSum_normalized_error_of_finite_family_height_tail
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (B : Set (Grassmannian K m k)) [Fintype B]
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    (hk : 0 < k) (hn : 0 < n) {T C_R E_lower C_height : ℝ} {N : ℕ}
    (hT : 0 < T)
    (hRadiusPoint : ∀ V : B,
      rowMatrixFundamentalRadius V.1 n / T ≤ 1)
    (hLower :
      (∑ V : B, |∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
          f (T⁻¹ • embedMatrix A.1)|) /
          T ^ (n * (k * degree K)) ≤ E_lower)
    (hRadius :
      (∑ V : B,
        rowMatrixFundamentalRadius V.1 n /
          rowMatrixLatticeCovolume V.1 n) ≤ C_R)
    (hnm : m < n)
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := k)) m)
    (hCheight : 0 < C_height) (hN : 1 ≤ N)
    (houtside : ∀ V : Grassmannian K m k, V ∉ B →
      (N : ℝ) ≤ rowSpaceHeight V)
    (hdom : ∀ V : Grassmannian K m k, 1 ≤ rowSpaceHeight V →
      |(rowSpaceHeight V)⁻¹ ^ n * rowMatrixSubspaceIntegral V n f| ≤
        C_height * (rowSpaceHeight V)⁻¹ ^ n)
    (hdecomp :
      fixedRankSum n m k f T =
        ∑' V : B,
          ∑' A : {A : rowMatrixZLattice V.1 n //
              rowMatrixRank V.1 A = k},
            f (T⁻¹ • (((A.1 : rowMatrixRealSpan V.1 n) :
              M n m (K_ℝ[K]))))) :
    ∃ Cₐ Ctail : ℝ, 0 < Cₐ ∧ 0 < Ctail ∧
      |fixedRankSum n m k f T / T ^ (n * (k * degree K)) -
          mainConstant n m k f| ≤
        Cₐ * C_R / T + E_lower +
          Ctail * ((N : ℝ) ^ (-((n - m : ℕ) : ℝ))) := by
  obtain ⟨Cₐ, hCₐ, hpoint⟩ :=
    exists_finite_rowMatrix_rank_lattice_estimate_with_lower
      B f h_f hk hn hT hRadiusPoint
  obtain ⟨Ctail, hCtail, hfinite⟩ :=
    finite_rowMatrix_rank_error_with_height_tail_bound
      B hT hCₐ.le hpoint hLower hRadius hnm hcount hCheight hN houtside hdom
  refine ⟨Cₐ, Ctail, hCₐ, hCtail, ?_⟩
  exact fixedRankSum_normalized_error_of_finite_family B hT hdecomp hfinite

/- [derived consequence of paper equations (19)--(21) and `co:tail`, lines
   1038--1061, 1156--1170, and 1671--1694] Assemble the finite-row-space
   fixed-rank estimate while retaining the manuscript's pointwise condition
   and summed error `sqrt n * rho(Λ_D)`.  This is the paper-facing route;
   the older fundamental-domain-radius statement remains only auxiliary
   Lean infrastructure. -/
set_option maxHeartbeats 1200000 in
theorem exists_fixedRankSum_normalized_error_of_finite_family_latticeVoronoi_height_tail
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (B : Set (Grassmannian K m k)) [Fintype B]
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    (hk : 0 < k) (hn : 0 < n) {T C_R E_lower C_height : ℝ} {N : ℕ}
    (hT : 0 < T)
    (hRadiusPoint : ∀ V : B,
      (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1)) / T ≤ 1)
    (hLower :
      (∑ V : B, |∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
          f (T⁻¹ • embedMatrix A.1)|) /
          T ^ (n * (k * degree K)) ≤ E_lower)
    (hRadius :
      (∑ V : B,
        (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice V.1)) /
          rowMatrixLatticeCovolume V.1 n) ≤ C_R)
    (hnm : m < n)
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := k)) m)
    (hCheight : 0 < C_height) (hN : 1 ≤ N)
    (houtside : ∀ V : Grassmannian K m k, V ∉ B →
      (N : ℝ) ≤ rowSpaceHeight V)
    (hdom : ∀ V : Grassmannian K m k, 1 ≤ rowSpaceHeight V →
      |(rowSpaceHeight V)⁻¹ ^ n * rowMatrixSubspaceIntegral V n f| ≤
        C_height * (rowSpaceHeight V)⁻¹ ^ n)
    (hdecomp :
      fixedRankSum n m k f T =
        ∑' V : B,
          ∑' A : {A : rowMatrixZLattice V.1 n //
              rowMatrixRank V.1 A = k},
            f (T⁻¹ • (((A.1 : rowMatrixRealSpan V.1 n) :
              M n m (K_ℝ[K]))))) :
    ∃ Cₐ Ctail : ℝ, 0 < Cₐ ∧ 0 < Ctail ∧
      |fixedRankSum n m k f T / T ^ (n * (k * degree K)) -
          mainConstant n m k f| ≤
        Cₐ * C_R / T + E_lower +
          Ctail * ((N : ℝ) ^ (-((n - m : ℕ) : ℝ))) := by
  obtain ⟨Cₐ, hCₐ, hpoint⟩ :=
    exists_finite_rowMatrix_rank_latticeVoronoi_estimate_with_lower
      B f h_f hk hn hT hRadiusPoint
  obtain ⟨Ctail, hCtail, hfinite⟩ :=
    finite_rowMatrix_rank_latticeVoronoi_error_with_height_tail_bound
      B hT hCₐ.le hpoint hLower hRadius hnm hcount hCheight hN houtside hdom
  refine ⟨Cₐ, Ctail, hCₐ, hCtail, ?_⟩
  exact fixedRankSum_normalized_error_of_finite_family B hT hdecomp hfinite

/- [Lean infrastructure for paper Theorem `th:higher_moments`] The limiting
expression in Theorem `th:higher_moments`.  The rank-zero
   echelon term is `f 0`; the positive-rank terms are the row-space form of
   the manuscript's normalized echelon integrals. -/
noncomputable def echelonIntegralLimit
    {K : Type*} [Field K] [NumberField K]
    (n m s : ℕ) (f : M n m (K_ℝ[K]) → ℝ) : ℝ :=
  f 0 + ∑ k : Fin m, mainConstant n m (k.1 + 1) f

/- [Lean infrastructure for paper Theorem `th:higher_moments`] The
prime-norm pullback filter below must be nontrivial for the manuscript's phrase
`𝓝(𝓟) → ∞` to have its intended meaning.  This derived fact uses Euclid's
infinitude of rational primes (`Nat.exists_infinite_primes`), Mathlib's
formalized lying-over theorem
`Ideal.exists_maximal_ideal_liesOver_of_isIntegral`, and the standard norm
formula `Ideal.pow_inertiaDeg` for a prime ideal above `(p)`. -/
theorem exists_primeIdeal_idealNorm_ge
    {K : Type*} [Field K] [NumberField K] (N : ℕ) :
    ∃ P : PrimeIdeal K, N ≤ idealNorm P := by
  obtain ⟨p, hNp, hp⟩ := Nat.exists_infinite_primes N
  let pIdeal : Ideal ℤ := Ideal.span {(p : ℤ)}
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : pIdeal.IsMaximal := by
    dsimp [pIdeal]
    infer_instance
  obtain ⟨P, hPmax, hPover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (R := ℤ) (S := NumberField.RingOfIntegers K) pIdeal
  letI : P.IsMaximal := hPmax
  letI : P.IsPrime := hPmax.isPrime
  letI : P.LiesOver pIdeal := hPover
  have hPne : P ≠ ⊥ := Ideal.IsMaximal.ne_bot_of_isIntegral_int P
  let Q : PrimeIdeal K := ⟨P, ⟨inferInstance, hPne⟩⟩
  refine ⟨Q, ?_⟩
  have hnorm : p ^ P.inertiaDeg ℤ = Ideal.absNorm P := by
    simpa [pIdeal] using Ideal.pow_inertiaDeg p P
  change N ≤ Ideal.absNorm P
  rw [← hnorm]
  exact hNp.trans (Nat.le_pow (Ideal.inertiaDeg_pos P ℤ))

/- [Lean infrastructure for paper Theorem `th:higher_moments`] Consequently,
the pullback filter encoding `𝓝(𝓟) → ∞` is nontrivial; limits stated on this
filter are therefore not vacuous. -/
noncomputable instance idealNorm_comap_neBot
    {K : Type*} [Field K] [NumberField K] :
    NeBot (comap (idealNorm : PrimeIdeal K → ℕ) atTop) := by
  apply Filter.comap_neBot
  intro t ht
  obtain ⟨N, hN⟩ := Filter.mem_atTop_sets.mp ht
  obtain ⟨P, hP⟩ := exists_primeIdeal_idealNorm_ge (K := K) N
  exact ⟨P, hN _ hP⟩

/- [Lean infrastructure for paper Theorem `th:higher_moments`] The norm
parameter used in the paper is the defining map of the pullback filter on prime
   ideals.  This is the filter form of the phrase `N(P) → ∞`. -/
theorem idealNorm_real_tendsto_atTop
    {K : Type*} [Field K] [NumberField K] :
    Tendsto (fun P : PrimeIdeal K => (idealNorm P : ℝ))
      (comap (idealNorm : PrimeIdeal K → ℕ) atTop) atTop := by
  exact tendsto_natCast_atTop_atTop.comp
    (tendsto_comap : Tendsto (idealNorm : PrimeIdeal K → ℕ)
      (comap (idealNorm : PrimeIdeal K → ℕ) atTop) atTop)

/- [derived consequence of paper equation `eq:def_of_L`] Since the admissible
parameters always satisfy `s < n`, the normalizing
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

/- [derived consequence of paper Lemma `le:counting`] The `O(N(P)⁻¹)`
estimate is enough to pass from the
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

/- [Lean infrastructure for paper Theorem `th:higher_moments`] Named filter
form of convergence as `N(𝓟) → ∞`. -/
def tendsToAtNorm
    {K : Type*} [Field K] [NumberField K]
    (F : PrimeIdeal K → ℝ) (limit : ℝ) : Prop :=
  Tendsto F (comap (idealNorm : PrimeIdeal K → ℕ) atTop) (𝓝 limit)

end Katznelson
