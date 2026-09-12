import Katznelson.Counting.UniformLowerRank

/-!
# Literal termwise-absolute lower-rank estimate

This module supplies the manuscript-literal endpoint for Lemma
`le:low_rank_terms` of `papers/katznelson.tex`, lines 1495--1635.  In
particular, its left side is
`∑ V, ∑' A, |f (T⁻¹ • embedMatrix A)|`, not
`∑ V, |∑' A, f (T⁻¹ • embedMatrix A)|`.

The reindexing is first proved for an arbitrary summable function on integral
matrices.  Admissibility enters only afterward, to supply summability and
finite support for the manuscript's function `A ↦ |f (T⁻¹A)|`.
-/

namespace Katznelson

open Filter MeasureTheory Set
open scoped BigOperators Classical NumberField Topology

attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

/- [Lean infrastructure for paper lemma `le:low_rank_terms`, lines
   1495--1537] Partition matrices of rank `< k` by their exact rank. -/
noncomputable def lowerRankSigmaEquiv
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (V : Grassmannian K m k) :
    (Σ l : Fin k, {A : IntegralMatrix K n m //
      rowsInIntegralRowModule V A ∧ integralMatrixRank A = l.1}) ≃
      {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V A ∧ integralMatrixRank A < k} :=
  { toFun := fun A =>
      ⟨A.2.1, A.2.2.1, by simpa [A.2.2.2] using A.1.isLt⟩
    invFun := fun A =>
      let l : Fin k := ⟨integralMatrixRank A.1, A.2.2⟩
      ⟨l, ⟨A.1, A.2.1, rfl⟩⟩
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

/- [Lean infrastructure for paper lemma `le:low_rank_terms`, lines
   1495--1537] Generic summable-function rank decomposition.  Separating this
   analytic-free reindexing prevents the manuscript bridge from duplicating
   the `Admissible` machinery. -/
theorem tsum_lowerRank_eq_sum_ranks_of_summable
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (V : Grassmannian K m k)
    (w : IntegralMatrix K n m → ℝ) (hw : Summable w) :
    (∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V A ∧ integralMatrixRank A < k}, w A.1) =
      ∑ l : Fin k, ∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V A ∧ integralMatrixRank A = l.1}, w A.1 := by
  let g : {A : IntegralMatrix K n m //
      rowsInIntegralRowModule V A ∧ integralMatrixRank A < k} → ℝ :=
    fun A => w A.1
  let e := lowerRankSigmaEquiv (n := n) (m := m) V
  have hg : Summable g := hw.comp_injective Subtype.val_injective
  have hge : Summable (g ∘ e) := e.summable_iff.mpr hg
  calc
    (∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V A ∧ integralMatrixRank A < k}, w A.1) =
        ∑' A, g (e A) := (e.tsum_eq g).symm
    _ = ∑' l : Fin k, ∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V A ∧ integralMatrixRank A = l.1},
        (g ∘ e) ⟨l, A⟩ := hge.tsum_sigma
    _ = ∑ l : Fin k, ∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V A ∧ integralMatrixRank A = l.1}, w A.1 := by
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro l hl
      apply tsum_congr
      intro A
      rfl

/- [Lean infrastructure for paper lemma `le:low_rank_terms`, lines
   1495--1537] Generic summable-function form of regrouping a fixed-rank
   matrix by its unique row space, using `rowSpaceContainedRankEquiv`. -/
theorem tsum_rank_eq_sum_contained_rowSpaces_of_summable
    {K : Type*} [Field K] [NumberField K]
    {n m k l : ℕ} (V : Grassmannian K m k)
    (w : IntegralMatrix K n m → ℝ) (hw : Summable w) :
    (∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V A ∧ integralMatrixRank A = l}, w A.1) =
      ∑' W : {W : Grassmannian K m l // W.1 ≤ V.1},
        ∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule W.1 A ∧ integralMatrixRank A = l}, w A.1 := by
  let g : {A : IntegralMatrix K n m //
      rowsInIntegralRowModule V A ∧ integralMatrixRank A = l} → ℝ :=
    fun A => w A.1
  let e := rowSpaceContainedRankEquiv
    (n := n) (m := m) (k := k) (l := l) V
  have hg : Summable g := hw.comp_injective Subtype.val_injective
  have hge : Summable (g ∘ e.symm) := e.symm.summable_iff.mpr hg
  calc
    (∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V A ∧ integralMatrixRank A = l}, w A.1) =
        ∑' WA, g (e.symm WA) := (e.symm.tsum_eq g).symm
    _ = ∑' W : {W : Grassmannian K m l // W.1 ≤ V.1},
        ∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule W.1 A ∧ integralMatrixRank A = l},
          (g ∘ e.symm) ⟨W, A⟩ := hge.tsum_sigma
    _ = ∑' W : {W : Grassmannian K m l // W.1 ≤ V.1},
        ∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule W.1 A ∧ integralMatrixRank A = l}, w A.1 := by
      apply tsum_congr
      intro W
      apply tsum_congr
      intro A
      have hA : (e.symm ⟨W, A⟩).1 = A.1 := by
        have h := congrArg (fun X => X.2.1) (e.apply_symm_apply ⟨W, A⟩)
        change (e.symm ⟨W, A⟩).1 = A.1 at h
        exact h
      simp [g, hA]

/- [Lean infrastructure for paper lemma `le:low_rank_terms`, lines
   1495--1537] Generic finite-family Fubini bridge.  The right side is the
   manuscript's extension multiplicity `n_k(D')`, represented by the proved
   row-space count `((B ∩ {V | W ≤ V}).ncard : ℝ)`. -/
set_option maxHeartbeats 1600000 in
theorem finite_lowerRank_sum_eq_sum_containedRowSpaceCounts_of_summable
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (B : Set (Grassmannian K m k)) [Fintype B]
    (w : IntegralMatrix K n m → ℝ) (hw : Summable w)
    (hwsupport : (Function.support w).Finite) :
    (∑ V : B, ∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k}, w A.1) =
      ∑ l : Fin k, ∑' W : Grassmannian K m l.1,
        ((B ∩ {V | W.1 ≤ V.1}).ncard : ℝ) *
          (∑' A : {A : IntegralMatrix K n m //
            rowsInIntegralRowModule W A ∧ integralMatrixRank A = l.1},
            w A.1) := by
  classical
  let q : ∀ l : Fin k, Grassmannian K m l.1 → ℝ := fun l W =>
    ∑' A : {A : IntegralMatrix K n m //
      rowsInIntegralRowModule W A ∧ integralMatrixRank A = l.1}, w A.1
  have hq : ∀ l : Fin k, (Function.support (q l)).Finite := by
    intro l
    let R : Set {A : IntegralMatrix K n m // integralMatrixRank A = l.1} :=
      {A | A.1 ∈ Function.support w}
    have hR : R.Finite :=
      hwsupport.preimage Subtype.val_injective.injOn
    let S : Set (Grassmannian K m l.1) := rowSpaceOfRank '' R
    have hS : S.Finite := hR.image rowSpaceOfRank
    refine hS.subset ?_
    intro W hW
    by_contra hWnot
    apply hW
    rw [← tsum_zero]
    apply tsum_congr
    intro A
    by_contra hA
    apply hWnot
    refine ⟨⟨A.1, A.2.2⟩, hA, ?_⟩
    apply Subtype.ext
    exact rowSpace_eq_of_rowsIn_of_rank W A.1 A.2.1 A.2.2
  have hperV (V : B) :
      (∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k}, w A.1) =
        ∑ l : Fin k,
          ∑' W : {W : Grassmannian K m l.1 // W.1 ≤ V.1}, q l W.1 := by
    rw [tsum_lowerRank_eq_sum_ranks_of_summable V.1 w hw]
    apply Finset.sum_congr rfl
    intro l hl
    simpa [q] using
      (tsum_rank_eq_sum_contained_rowSpaces_of_summable
        (n := n) (m := m) (k := k) (l := l.1) V.1 w hw)
  calc
    (∑ V : B, ∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k}, w A.1) =
        ∑ V : B, ∑ l : Fin k,
          ∑' W : {W : Grassmannian K m l.1 // W.1 ≤ V.1}, q l W.1 := by
      apply Finset.sum_congr rfl
      intro V hV
      exact hperV V
    _ = ∑ l : Fin k, ∑ V : B,
          ∑' W : {W : Grassmannian K m l.1 // W.1 ≤ V.1}, q l W.1 := by
      rw [Finset.sum_comm]
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
              w A.1) := by
      rfl

/- [paper, lemma `le:low_rank_terms`, lines 1495--1537] Exact bridge for
   the manuscript's termwise-absolute summand.  The left side retains the
   literal lower-rank condition and the right side retains the extension
   multiplicity indexed by the matrix's own rank-`l` row space. -/
theorem finite_rowSpaceLowerAbsSum_eq_sum_containedRowSpaceCounts_literal
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (B : Set (Grassmannian K m k)) [Fintype B]
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    {T : ℝ} (hT : 0 < T) :
    (∑ V : B, ∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
      |f (T⁻¹ • embedMatrix A.1)|) =
      ∑ l : Fin k, ∑' W : Grassmannian K m l.1,
        ((B ∩ {V | W.1 ≤ V.1}).ncard : ℝ) *
          (∑' A : {A : IntegralMatrix K n m //
            rowsInIntegralRowModule W A ∧ integralMatrixRank A = l.1},
            |f (T⁻¹ • embedMatrix A.1)|) := by
  let w : IntegralMatrix K n m → ℝ := fun A => |f (T⁻¹ • embedMatrix A)|
  have hw : Summable w := by
    simpa only [w, Real.norm_eq_abs] using
      (summable_scaled_integralMatrices f h_f hT).norm
  have hsupport : (Function.support w).Finite := by
    apply (finite_scaledSupport_integralMatrices f h_f hT).subset
    intro A hA
    simpa [w, Function.mem_support] using hA
  simpa [w] using
    finite_lowerRank_sum_eq_sum_containedRowSpaceCounts_of_summable
      B w hw hsupport

/- [derived consequence of paper lemma `le:low_rank_terms`, lines
   1495--1635] Quantitative normalized form of the exact bridge above.  Its
   left side is literally the manuscript's sum over `V` of the inner sum of
   `|f(T⁻¹A)|`; the right side uses the paper's rank-zero term, `alpha_l`,
   and `B_l(T)`. -/
set_option maxHeartbeats 1200000 in
theorem finite_rowSpaceLowerAbsSum_normalized_le_literal
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
            rowsInIntegralRowModule W A ∧ integralMatrixRank A = l},
            |f (T⁻¹ • embedMatrix A.1)|)) /
          T ^ (k * n * d) ≤
        C₃ * T ^ alpha_l n m k l d *
          B_l n m k l d Ccrudenew T) :
    (∑ V : B, ∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
        |f (T⁻¹ • embedMatrix A.1)|) /
        T ^ (k * n * d) ≤
      Csize * |f 0| *
          T ^ (-(d : ℤ) * (k : ℤ) * ((n : ℤ) - m)) +
        ((Finset.Ico 1 k).card : ℝ) * C₃ * Ccrudenew *
          (1 + Real.log T) *
          T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ)) := by
  have hden : 0 < T ^ (k * n * d) :=
    pow_pos (lt_of_lt_of_le zero_lt_one hT) _
  let u : ℕ → ℝ := fun l =>
    ∑' W : Grassmannian K m l,
      ((B ∩ {V | W.1 ≤ V.1}).ncard : ℝ) *
        (∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule W A ∧ integralMatrixRank A = l},
          |f (T⁻¹ • embedMatrix A.1)|)
  have hreg :
      (∑ V : B, ∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
          |f (T⁻¹ • embedMatrix A.1)|) = ∑ l : Fin k, u l.1 := by
    simpa [u] using
      finite_rowSpaceLowerAbsSum_eq_sum_containedRowSpaceCounts_literal
        B f h_f (lt_of_lt_of_le zero_lt_one hT)
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
      exact False.elim (hW (Subsingleton.elim W W₀))
    have hcontain : B ∩ {V | W₀.1 ≤ V.1} = B := by
      ext V
      simp [grassmannian_zeroRank_eq_bot W₀]
    have hinner :
        (∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule W₀ A ∧ integralMatrixRank A = 0},
          |f (T⁻¹ • embedMatrix A.1)|) = |f 0| := by
      simpa using integralRowMatrices_rank_zero_sum W₀ (fun x => |f x|) T
    rw [htsum, hcontain, hinner]
  have hzero :
      (B.ncard : ℝ) * |f 0| / T ^ (k * n * d) ≤
        Csize * |f 0| *
          T ^ (-(d : ℤ) * (k : ℤ) * ((n : ℤ) - m)) := by
    have hT₀ : 0 < T := lt_of_lt_of_le zero_lt_one hT
    have hnum : (B.ncard : ℝ) * |f 0| ≤
        (Csize * T ^ (k * m * d)) * |f 0| :=
      mul_le_mul_of_nonneg_right hB (abs_nonneg _)
    have hpow : T ^ (k * m * d) / T ^ (k * n * d) =
        T ^ (-(d : ℤ) * (k : ℤ) * ((n : ℤ) - m)) := by
      rw [← zpow_natCast T (k * m * d), ← zpow_natCast T (k * n * d),
        ← zpow_sub₀ hT₀.ne']
      congr 1
      push_cast
      ring
    calc
      (B.ncard : ℝ) * |f 0| / T ^ (k * n * d) ≤
          (Csize * T ^ (k * m * d)) * |f 0| / T ^ (k * n * d) :=
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
  calc
    (∑ V : B, ∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
        |f (T⁻¹ • embedMatrix A.1)|) / T ^ (k * n * d) =
        (∑ l : Fin k, u l.1) / T ^ (k * n * d) := by rw [hreg]
    _ = u 0 / T ^ (k * n * d) +
        ∑ l ∈ Finset.Ico 1 k, u l / T ^ (k * n * d) := by
      rw [hsplit, add_div, Finset.sum_div]
    _ = (B.ncard : ℝ) * |f 0| / T ^ (k * n * d) +
        ∑ l ∈ Finset.Ico 1 k, u l / T ^ (k * n * d) := by rw [hu0]
    _ ≤ Csize * |f 0| *
          T ^ (-(d : ℤ) * (k : ℤ) * ((n : ℤ) - m)) +
        ((Finset.Ico 1 k).card : ℝ) * C₃ * Ccrudenew *
          (1 + Real.log T) *
          T ^ (-(d : ℤ) * ((n - m + k - 1 : ℕ) : ℤ)) :=
      add_le_add hzero hsum_positive

/- [paper, lemma `le:low_rank_terms` and its use in theorem `th:main`,
   lines 1495--1635 and 1671--1683] Final uniform manuscript-facing
   lower-rank estimate.  The outer family is exactly the row-space image of
   `𝓕_k(T) = calF ...`, and the inner sum contains the termwise absolute
   values `|f(T⁻¹A)|`.  The Schmidt height count remains the explicit,
   attributed hypothesis `hcount`. -/
set_option maxHeartbeats 6000000 in
theorem exists_uniform_echelon_calF_lowerRank_normalized_abs_sum_le_of_raw_covering_bound_literal
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    (hnm : m < n) (hkm : k ≤ m) (hk : 1 ≤ k)
    {Csup : ℝ} (hCsup : 0 < Csup)
    (hSupport : ∀ T : ℝ, 0 < T → ∀ A : IntegralMatrix K n m,
      f (T⁻¹ • embedMatrix A) ≠ 0 → ‖embedMatrix A‖ ≤ Csup * T)
    (hcount : ∀ l ∈ Finset.Icc 1 k,
      HasHeightCountBounds
        (rowSpaceHeight (K := K) (m := m) (k := l)) m) :
    ∃ C_lower : ℝ, 0 < C_lower ∧ ∀ T : ℝ, 2 ≤ T →
      (∑' V : (echelonRowSpace (K := K) ''
          calF (K := K) (l := k) (m := m) (n := n) Csup T),
          ∑' A : {A : IntegralMatrix K n m //
            rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
            |f (T⁻¹ • embedMatrix A.1)|) /
        T ^ (k * n * degree K) ≤
          C_lower * (1 + Real.log T) *
            T ^ (-(degree K : ℤ) *
              ((n - m + k - 1 : ℕ) : ℤ)) := by
  classical
  have hkpos : 0 < k := by omega
  have hkIcc : k ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨hk, le_rfl⟩
  obtain ⟨Csize, hCsize, hBcard⟩ :=
    exists_uniform_echelonCalF_rowSpace_image_ncard_le_of_proved_crude_height
      (K := K) (n := n) (m := m) (k := k) (Csup := Csup)
      (hcount k hkIcc) hkpos
  let E : ℕ → ℝ → ℝ := fun l T =>
    (∑' W : Grassmannian K m l,
      (((echelonRowSpace (K := K) ''
          calF (K := K) (l := k) (m := m) (n := n) Csup T) ∩
            {V | W.1 ≤ V.1}).ncard : ℝ) *
        (∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule W A ∧ integralMatrixRank A = l},
          |f (T⁻¹ • embedMatrix A.1)|)) /
      T ^ (k * n * degree K)
  have hpoint_by_rank : ∀ l ∈ Finset.Ico 1 k,
      ∃ C₁ C₂ Ccrudenew : ℝ,
        0 < C₁ ∧ 0 < C₂ ∧ 0 < Ccrudenew ∧
        ∀ T : ℝ, 2 ≤ T →
          E l T ≤ C₁ * C₂ * T ^ alpha_l n m k l (degree K) *
            B_l n m k l (degree K) Ccrudenew T := by
    intro l hl
    have hl' := Finset.mem_Ico.mp hl
    have hlIcc : l ∈ Finset.Icc 1 k :=
      Finset.mem_Icc.mpr ⟨hl'.1, hl'.2.le⟩
    simpa [E] using
      (exists_uniform_echelon_calF_positiveLowerStratum_le_B_l_of_raw_covering_bound
        (K := K) f h_f hnm hkm hl'.1 hl'.2 hCsup hSupport
        (hcount l hlIcc))
  obtain ⟨C₃, Ccrudenew, hC₃, hCcrudenew, hpoint_uniform⟩ :=
    exists_uniform_B_l_point_bound_forall
      (n := n) (m := m) (k := k) (d := degree K) E hpoint_by_rank
  let C_lower : ℝ :=
    Csize * |f 0| + ((Finset.Ico 1 k).card : ℝ) * C₃ * Ccrudenew + 1
  have hzeroCoeff : 0 ≤ Csize * |f 0| :=
    mul_nonneg hCsize.le (abs_nonneg _)
  have hpositiveCoeff :
      0 ≤ ((Finset.Ico 1 k).card : ℝ) * C₃ * Ccrudenew := by
    positivity
  have hC_lower : 0 < C_lower := by
    dsimp [C_lower]
    linarith
  refine ⟨C_lower, hC_lower, ?_⟩
  intro T hTtwo
  have hT : 1 ≤ T := by linarith
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  let B : Set (Grassmannian K m k) := echelonRowSpace (K := K) ''
    calF (K := K) (l := k) (m := m) (n := n) Csup T
  have hBfinite : B.Finite := by
    dsimp [B]
    exact (finite_calF (K := K) (l := k) (m := m) (n := n)
      (Csup := Csup) (T := T)).image _
  letI : Fintype B := hBfinite.fintype
  have hBcard' : (B.ncard : ℝ) ≤
      Csize * T ^ (k * m * degree K) := by
    simpa [B] using hBcard T hT
  have hpoint : ∀ l ∈ Finset.Ico 1 k,
      (∑' W : Grassmannian K m l,
        ((B ∩ {V | W.1 ≤ V.1}).ncard : ℝ) *
          (∑' A : {A : IntegralMatrix K n m //
            rowsInIntegralRowModule W A ∧ integralMatrixRank A = l},
            |f (T⁻¹ • embedMatrix A.1)|)) /
        T ^ (k * n * degree K) ≤
          C₃ * T ^ alpha_l n m k l (degree K) *
            B_l n m k l (degree K) Ccrudenew T := by
    intro l hl
    simpa [E, B] using hpoint_uniform T hTtwo l hl
  have hdegree : 0 < degree K := Module.finrank_pos
  have hsum_alpha := sum_alpha_l_mul_B_l_le_corrected
    (n := n) (m := m) (k := k) (d := degree K)
    hCcrudenew.le hT hdegree hnm hk
  have hraw := finite_rowSpaceLowerAbsSum_normalized_le_literal
    B f h_f hT hnm hk Module.finrank_pos hBcard'
      hC₃.le hCcrudenew.le hsum_alpha hpoint
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
  have hmul : degree K * (n - m + k - 1) ≤
      degree K * (k * (n - m)) := Nat.mul_le_mul_left _ hnat
  have hneg :
      -((degree K * (k * (n - m)) : ℕ) : ℤ) ≤
        -((degree K * (n - m + k - 1) : ℕ) : ℤ) := by
    exact neg_le_neg (by exact_mod_cast hmul)
  have hpow :
      T ^ (-(degree K : ℤ) * (k : ℤ) * ((n : ℤ) - m)) ≤
        T ^ (-(degree K : ℤ) *
          ((n - m + k - 1 : ℕ) : ℤ)) := by
    apply zpow_le_zpow_right₀ hT
    simpa [Nat.cast_mul, Nat.cast_sub hnm.le, mul_assoc] using hneg
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT
  have hfactor : (1 : ℝ) ≤ 1 + Real.log T := by linarith
  have htarget_nonneg :
      0 ≤ T ^ (-(degree K : ℤ) *
        ((n - m + k - 1 : ℕ) : ℤ)) := zpow_nonneg hTpos.le _
  have htargetFactor_nonneg :
      0 ≤ (1 + Real.log T) *
        T ^ (-(degree K : ℤ) *
          ((n - m + k - 1 : ℕ) : ℤ)) :=
    mul_nonneg (by linarith) htarget_nonneg
  have hzero_factor :
      T ^ (-(degree K : ℤ) * (k : ℤ) * ((n : ℤ) - m)) ≤
        (1 + Real.log T) *
          T ^ (-(degree K : ℤ) *
            ((n - m + k - 1 : ℕ) : ℤ)) := by
    calc
      T ^ (-(degree K : ℤ) * (k : ℤ) * ((n : ℤ) - m)) ≤
          T ^ (-(degree K : ℤ) *
            ((n - m + k - 1 : ℕ) : ℤ)) := hpow
      _ = 1 * T ^ (-(degree K : ℤ) *
            ((n - m + k - 1 : ℕ) : ℤ)) := by ring
      _ ≤ (1 + Real.log T) *
          T ^ (-(degree K : ℤ) *
            ((n - m + k - 1 : ℕ) : ℤ)) :=
        mul_le_mul_of_nonneg_right hfactor htarget_nonneg
  change
    (∑' V : B, ∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
        |f (T⁻¹ • embedMatrix A.1)|) / T ^ (k * n * degree K) ≤
      C_lower * (1 + Real.log T) *
        T ^ (-(degree K : ℤ) *
          ((n - m + k - 1 : ℕ) : ℤ))
  rw [tsum_fintype]
  change
    (∑ V : B, ∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
        |f (T⁻¹ • embedMatrix A.1)|) / T ^ (k * n * degree K) ≤
      C_lower * (1 + Real.log T) *
        T ^ (-(degree K : ℤ) *
          ((n - m + k - 1 : ℕ) : ℤ))
  calc
    (∑ V : B, ∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
        |f (T⁻¹ • embedMatrix A.1)|) / T ^ (k * n * degree K) ≤
        Csize * |f 0| *
            T ^ (-(degree K : ℤ) * (k : ℤ) * ((n : ℤ) - m)) +
          ((Finset.Ico 1 k).card : ℝ) * C₃ * Ccrudenew *
            (1 + Real.log T) *
            T ^ (-(degree K : ℤ) *
              ((n - m + k - 1 : ℕ) : ℤ)) := hraw
    _ ≤ Csize * |f 0| *
          ((1 + Real.log T) *
            T ^ (-(degree K : ℤ) *
              ((n - m + k - 1 : ℕ) : ℤ))) +
        ((Finset.Ico 1 k).card : ℝ) * C₃ * Ccrudenew *
          ((1 + Real.log T) *
            T ^ (-(degree K : ℤ) *
              ((n - m + k - 1 : ℕ) : ℤ))) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hzero_factor hzeroCoeff
      · ring_nf
        exact le_rfl
    _ = (Csize * |f 0| +
          ((Finset.Ico 1 k).card : ℝ) * C₃ * Ccrudenew) *
          ((1 + Real.log T) *
            T ^ (-(degree K : ℤ) *
              ((n - m + k - 1 : ℕ) : ℤ))) := by ring
    _ ≤ C_lower *
          ((1 + Real.log T) *
            T ^ (-(degree K : ℤ) *
              ((n - m + k - 1 : ℕ) : ℤ))) := by
      apply mul_le_mul_of_nonneg_right _ htargetFactor_nonneg
      dsimp [C_lower]
      linarith
    _ = C_lower * (1 + Real.log T) *
        T ^ (-(degree K : ℤ) *
          ((n - m + k - 1 : ℕ) : ℤ)) := by ring

end Katznelson
