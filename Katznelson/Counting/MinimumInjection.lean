import Katznelson.Counting.RowLattice
import Katznelson.Counting.SuccessiveMinima
import Katznelson.Counting.Echelon
import Katznelson.Counting.MinimumBound

/-!
# The minima tuple attached to a bounded echelon family

This module isolates the paper's `le:injective_minima` step from the large
theorem file.  The statements retain the manuscript's `𝓕_k(T)` and
`𝓑_k^(C)(T)` notation as represented in `Echelon` and `SuccessiveMinima`.
-/

namespace Katznelson

open scoped Classical NumberField

/- Mathlib keeps matrix norms non-global because several choices are natural;
   the paper's Euclidean matrix norm is represented here by the Frobenius norm. -/
attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

variable {K : Type*} [Field K] [NumberField K]

/- [paper, proof of `le:injective_minima`, lines 1221--1225] Membership in
   `𝓕_k(T)` supplies a matrix whose rows span the row space and whose
   Frobenius norm is at most `C^{sup} T`.  The matrix-level bridge in
   `MinimumBound` therefore bounds the last successive minimum by the same
   cutoff. -/
set_option maxHeartbeats 1200000 in
theorem echelon_successiveMinimum_last_norm_le_of_mem_calF
    {m k n : ℕ} (D : EchelonMatrix K k m) (hk : 0 < k)
    {Csup T : ℝ}
    (hD : D ∈ calF (K := K) (l := k) (m := m) (n := n) Csup T) :
    ‖((rowSuccessiveMinimum (echelonRowSpace D) ⟨k - 1, by omega⟩ :
        rowZLattice (echelonRowSpace D)) :
        rowRealSpan (echelonRowSpace D))‖ ≤ Csup * T := by
  change ∃ A : echelonRowMatrixLattice D,
      rowMatrixRank (echelonRowSpace D) A = k ∧
        ‖((A.1 : rowMatrixRealSpan (echelonRowSpace D) n) :
          M n m (K_ℝ[K]))‖ ≤ Csup * T at hD
  rcases hD with ⟨A, hArank, hAnorm⟩
  exact rowMatrix_successiveMinimum_last_norm_le_of_rank_eq
    (echelonRowSpace D) A hk
    hArank hAnorm

/- [paper, both parts of `le:injective_minima`, lines 1199--1234] The
   manuscript-facing correspondence is now available in one statement: the
   minima rows of every member of `𝓕_k(T)` lie in the exact set
   `𝓑_k^(C)(T)` when `C` dominates the projection constant, and the
   correspondence is injective. -/
set_option maxHeartbeats 4000000 in
theorem echelon_successiveMinimumIntegralRow_mem_possible_and_injective
    {m k n : ℕ} {Csup C T : ℝ} (hCproj :
      rowKRealSmulBound (K := K) (m := m) * numberFieldCoefficientRadius K ≤ C)
    (hCsup : Csup ≤ C) (hT : 0 ≤ T) (hk : 0 < k) :
    (∀ D : EchelonMatrix K k m,
      D ∈ calF (K := K) (l := k) (m := m) (n := n) Csup T →
        rowSuccessiveMinimumIntegralRow (echelonRowSpace D) ∈
          possibleSuccessiveMinimaSet (K := K) (m := m) C T) ∧
    Function.Injective (fun D : EchelonMatrix K k m =>
      rowSuccessiveMinimumIntegralRow (echelonRowSpace D)) := by
  constructor
  · intro D hD
    have hlast := echelon_successiveMinimum_last_norm_le_of_mem_calF D hk hD
    apply rowSuccessiveMinimumIntegralTuple_mem_possibleSuccessiveMinimaSet
      (echelonRowSpace D) hk hCproj
    exact hlast.trans (mul_le_mul_of_nonneg_right hCsup hT)
  · intro D E hDE
    apply echelonRowSpace_injective
    apply rowSuccessiveMinimum_ambient_tuple_injective (K := K)
    funext i
    have hi := congrArg (fun l : Fin k → Fin m → 𝓞 K =>
        integralVectorEmbedding (K := K) m (l i)) hDE
    rw [integralVectorEmbedding_rowSuccessiveMinimumIntegralRow,
      integralVectorEmbedding_rowSuccessiveMinimumIntegralRow] at hi
    exact hi

/- [Lean infrastructure for paper equation `eq:just_as_before`, lines
   1730--1738] This names the reciprocal-minima weight on the manuscript's
   tuple space `𝓑_k(T)`.  Lean totalizes inversion at zero so the function is
   defined on the full displayed set; the proved bridge below shows that on
   the actual image of `𝓕_k(T)` it is exactly the paper's reciprocal product,
   whose selected minima are all nonzero. -/
noncomputable def possibleSuccessiveMinimaRadiusWeight
    {m k : ℕ} (n : ℕ) (hk : 0 < k)
    (l : Fin k → Fin m → 𝓞 K) : ℝ :=
  ((∏ i : Fin k,
    ‖integralVectorEmbedding (K := K) m (l i)‖ ^ degree K)⁻¹) ^ n *
      ‖integralVectorEmbedding (K := K) m
        (l ⟨k - 1, Nat.pred_lt hk.ne'⟩)‖

/- [Lean infrastructure for paper equation `eq:just_as_before`, lines
   1730--1738] The internal totalized tuple weight agrees, on a selected
   minima tuple, with the literal product of the paper's nonzero minima. -/
theorem possibleSuccessiveMinimaRadiusWeight_selected
    {m k : ℕ} (V : Grassmannian K m k) (n : ℕ) (hk : 0 < k) :
    possibleSuccessiveMinimaRadiusWeight (K := K) (m := m) n hk
      (rowSuccessiveMinimumIntegralRow V) =
        ((∏ i : Fin k,
          ‖((rowSuccessiveMinimum V i : rowZLattice V) : rowRealSpan V)‖ ^
            degree K)⁻¹) ^ n *
          ‖((rowSuccessiveMinimum V ⟨k - 1, Nat.pred_lt hk.ne'⟩ :
            rowZLattice V) : rowRealSpan V)‖ := by
  unfold possibleSuccessiveMinimaRadiusWeight
  simp_rw [integralVectorEmbedding_rowSuccessiveMinimumIntegralRow]
  rfl

/- [Lean infrastructure for paper equation `eq:just_as_before`, lines
   1730--1738] The totalized tuple weight is nonnegative, which is the sole
   order property needed to apply the finite injection comparison. -/
theorem possibleSuccessiveMinimaRadiusWeight_nonneg
    {m k : ℕ} (n : ℕ) (hk : 0 < k)
    (l : Fin k → Fin m → 𝓞 K) :
    0 ≤ possibleSuccessiveMinimaRadiusWeight (K := K) (m := m) n hk l := by
  unfold possibleSuccessiveMinimaRadiusWeight
  apply mul_nonneg
  · exact pow_nonneg (inv_nonneg.mpr
      (Finset.prod_nonneg fun i hi =>
        pow_nonneg (norm_nonneg _) _)) _
  · exact norm_nonneg _

/- [derived consequence of paper `le:injective_minima`, lines 1199--1234]
   The two asserted parts of the manuscript correspondence imply that its
   exact source family `𝓕_k(T)` is finite: it embeds in the already finite
   tuple family `𝓑_k^(C)(T)`.  This is a second, paper-local finiteness proof
   of the source family, independent of the later height-counting route. -/
theorem finite_calF_of_possibleSuccessiveMinima
    {m k n : ℕ} {Csup C T : ℝ} (hCproj :
      rowKRealSmulBound (K := K) (m := m) * numberFieldCoefficientRadius K ≤ C)
    (hCsup : Csup ≤ C) (hT : 0 ≤ T) (hk : 0 < k) :
    (calF (K := K) (l := k) (m := m) (n := n) Csup T).Finite := by
  let phi : EchelonMatrix K k m → (Fin k → Fin m → 𝓞 K) := fun D =>
    rowSuccessiveMinimumIntegralRow (echelonRowSpace D)
  obtain ⟨hmap, hinj⟩ :=
    echelon_successiveMinimumIntegralRow_mem_possible_and_injective
      (K := K) (m := m) (k := k) (n := n) hCproj hCsup hT hk
  have himage :
      (phi '' calF (K := K) (l := k) (m := m) (n := n) Csup T).Finite := by
    apply (finite_possibleSuccessiveMinimaSet (K := K) (m := m) (k := k)
      (C := C) (T := T)).subset
    rintro l ⟨D, hD, rfl⟩
    exact hmap D hD
  apply himage.of_finite_image
  intro D hD E hE hDE
  apply hinj
  exact hDE

/- [derived consequence of paper equation (22), lines 1730--1738, and
   `le:injective_minima`, lines 1199--1234] This is the finite-sum form of
   the manuscript's injection from `𝓕_k(T)` to `𝓑_k^(C)(T)`: any nonnegative
   weight of the selected minima may be summed over the latter family.  It
   retains both manuscript sets and does not replace their indexing with an
   unrelated parameter space. -/
theorem sum_calF_le_sum_possibleSuccessiveMinima
    {m k n : ℕ} {Csup C T : ℝ} (hCproj :
      rowKRealSmulBound (K := K) (m := m) * numberFieldCoefficientRadius K ≤ C)
    (hCsup : Csup ≤ C) (hT : 0 ≤ T) (hk : 0 < k)
    (g : (Fin k → Fin m → 𝓞 K) → ℝ) (hg : ∀ l, 0 ≤ g l) :
    (∑ D ∈ (finite_calF_of_possibleSuccessiveMinima
      (K := K) (m := m) (k := k) (n := n) hCproj hCsup hT hk).toFinset,
      g (rowSuccessiveMinimumIntegralRow (echelonRowSpace D))) ≤
      ∑ l ∈ (finite_possibleSuccessiveMinimaSet
        (K := K) (m := m) (k := k) (C := C) (T := T)).toFinset,
        g l := by
  classical
  let phi : EchelonMatrix K k m → (Fin k → Fin m → 𝓞 K) := fun D =>
    rowSuccessiveMinimumIntegralRow (echelonRowSpace D)
  obtain ⟨hmap, hinj⟩ :=
    echelon_successiveMinimumIntegralRow_mem_possible_and_injective
      (K := K) (m := m) (k := k) (n := n) hCproj hCsup hT hk
  let F := (finite_calF_of_possibleSuccessiveMinima
    (K := K) (m := m) (k := k) (n := n) hCproj hCsup hT hk).toFinset
  let B := (finite_possibleSuccessiveMinimaSet
    (K := K) (m := m) (k := k) (C := C) (T := T)).toFinset
  change (∑ D ∈ F, g (phi D)) ≤ ∑ l ∈ B, g l
  exact Finset.sum_le_sum_of_injOn phi hinj.injOn
    (by
      intro l hl
      rw [Finset.mem_image] at hl
      rcases hl with ⟨D, hD, rfl⟩
      have hD' : D ∈ calF (K := K) (l := k) (m := m) (n := n) Csup T := by
        simpa [F] using hD
      simpa [B] using hmap D hD')
    (by intro D hD; rfl)
    (by intro l hl hnot; exact hg l)

/- [derived consequence of paper equation `eq:just_as_before`, lines
   1730--1738] This is the exact finite-family radius sum from the main
   counting proof.  The source remains `𝓕_k(T)`, the target remains
   `𝓑_k^(C)(T)`, and the product estimate is kept as the visibly cited
   Fieker--Stehlé input used by the manuscript. -/
set_option maxHeartbeats 1200000 in
theorem sum_calF_coveringRadius_div_height_pow_le_possibleMinimaWeight
    {m k n : ℕ} {Csup C T Cprod : ℝ} (hCproj :
      rowKRealSmulBound (K := K) (m := m) * numberFieldCoefficientRadius K ≤ C)
    (hCsup : Csup ≤ C) (hT : 0 ≤ T) (hk : 0 < k) (hCprod : 0 ≤ Cprod)
    (hprod : ∀ D : EchelonMatrix K k m,
      D ∈ calF (K := K) (l := k) (m := m) (n := n) Csup T →
        (∏ i : Fin k,
          ‖((rowSuccessiveMinimum (echelonRowSpace D) i :
            rowZLattice (echelonRowSpace D)) :
              rowRealSpan (echelonRowSpace D))‖ ^ degree K) ≤
          Cprod * rowSpaceHeight (echelonRowSpace D)) :
    (∑ D ∈ (finite_calF_of_possibleSuccessiveMinima
      (K := K) (m := m) (k := k) (n := n) hCproj hCsup hT hk).toFinset,
      latticeCoveringRadius (rowZLattice (echelonRowSpace D)) /
        (rowSpaceHeight (echelonRowSpace D)) ^ n) ≤
      (Fintype.card (Σ _ : Fin k, IntegralBasisIndex K) : ℝ) *
        rowScalarActionBoundSum (K := K) (m := m) * Cprod ^ n *
        (∑ l ∈ (finite_possibleSuccessiveMinimaSet
          (K := K) (m := m) (k := k) (C := C) (T := T)).toFinset,
          possibleSuccessiveMinimaRadiusWeight (K := K) (m := m) n hk l) := by
  classical
  let F := (finite_calF_of_possibleSuccessiveMinima
    (K := K) (m := m) (k := k) (n := n) hCproj hCsup hT hk).toFinset
  let B := (finite_possibleSuccessiveMinimaSet
    (K := K) (m := m) (k := k) (C := C) (T := T)).toFinset
  let phi : EchelonMatrix K k m → (Fin k → Fin m → 𝓞 K) := fun D =>
    rowSuccessiveMinimumIntegralRow (echelonRowSpace D)
  let R : ℝ := (Fintype.card (Σ _ : Fin k, IntegralBasisIndex K) : ℝ) *
    rowScalarActionBoundSum (K := K) (m := m)
  have hRnonneg : 0 ≤ R := by
    dsimp [R]
    exact mul_nonneg (Nat.cast_nonneg _)
      (rowScalarActionBoundSum_nonneg (K := K) (m := m))
  have hpoint (D : EchelonMatrix K k m)
      (hD : D ∈ calF (K := K) (l := k) (m := m) (n := n) Csup T) :
      latticeCoveringRadius (rowZLattice (echelonRowSpace D)) /
        (rowSpaceHeight (echelonRowSpace D)) ^ n ≤
        R * Cprod ^ n *
          possibleSuccessiveMinimaRadiusWeight (K := K) (m := m) n hk (phi D) := by
    have h := rowCoveringRadius_div_height_pow_le_successiveMinimumWeight
      (V := echelonRowSpace D) n hk (hprod D hD)
    have hweight := possibleSuccessiveMinimaRadiusWeight_selected
      (K := K) (m := m) (V := echelonRowSpace D) n hk
    calc
      latticeCoveringRadius (rowZLattice (echelonRowSpace D)) /
          (rowSpaceHeight (echelonRowSpace D)) ^ n ≤
          R * Cprod ^ n *
            ((∏ i : Fin k,
              ‖((rowSuccessiveMinimum (echelonRowSpace D) i :
                rowZLattice (echelonRowSpace D)) :
                  rowRealSpan (echelonRowSpace D))‖ ^ degree K)⁻¹) ^ n *
              ‖((rowSuccessiveMinimum (echelonRowSpace D)
                ⟨k - 1, Nat.pred_lt hk.ne'⟩ :
                  rowZLattice (echelonRowSpace D)) :
                    rowRealSpan (echelonRowSpace D))‖ := h
      _ = R * Cprod ^ n *
          (((∏ i : Fin k,
            ‖((rowSuccessiveMinimum (echelonRowSpace D) i :
              rowZLattice (echelonRowSpace D)) :
                rowRealSpan (echelonRowSpace D))‖ ^ degree K)⁻¹) ^ n *
            ‖((rowSuccessiveMinimum (echelonRowSpace D)
              ⟨k - 1, Nat.pred_lt hk.ne'⟩ :
                rowZLattice (echelonRowSpace D)) :
                  rowRealSpan (echelonRowSpace D))‖) := by ring
      _ = R * Cprod ^ n *
          possibleSuccessiveMinimaRadiusWeight (K := K) (m := m) n hk (phi D) := by
        rw [show phi D = rowSuccessiveMinimumIntegralRow (echelonRowSpace D) by rfl,
          hweight]
  have hsum_point :
      (∑ D ∈ F,
        latticeCoveringRadius (rowZLattice (echelonRowSpace D)) /
          (rowSpaceHeight (echelonRowSpace D)) ^ n) ≤
        ∑ D ∈ F, R * Cprod ^ n *
          possibleSuccessiveMinimaRadiusWeight (K := K) (m := m) n hk (phi D) := by
    apply Finset.sum_le_sum
    intro D hD
    apply hpoint D
    simpa [F] using hD
  have hinject :
      (∑ D ∈ F,
        possibleSuccessiveMinimaRadiusWeight (K := K) (m := m) n hk (phi D)) ≤
        ∑ l ∈ B,
          possibleSuccessiveMinimaRadiusWeight (K := K) (m := m) n hk l := by
    exact sum_calF_le_sum_possibleSuccessiveMinima
      (K := K) (m := m) (k := k) (n := n) hCproj hCsup hT hk
      (possibleSuccessiveMinimaRadiusWeight (K := K) (m := m) n hk)
      (possibleSuccessiveMinimaRadiusWeight_nonneg (K := K) (m := m) n hk)
  change (∑ D ∈ F,
      latticeCoveringRadius (rowZLattice (echelonRowSpace D)) /
        (rowSpaceHeight (echelonRowSpace D)) ^ n) ≤
      R * Cprod ^ n *
        (∑ l ∈ B,
          possibleSuccessiveMinimaRadiusWeight (K := K) (m := m) n hk l)
  calc
    (∑ D ∈ F,
      latticeCoveringRadius (rowZLattice (echelonRowSpace D)) /
        (rowSpaceHeight (echelonRowSpace D)) ^ n) ≤
        ∑ D ∈ F, R * Cprod ^ n *
          possibleSuccessiveMinimaRadiusWeight (K := K) (m := m) n hk (phi D) :=
      hsum_point
    _ = R * Cprod ^ n *
        (∑ D ∈ F,
          possibleSuccessiveMinimaRadiusWeight (K := K) (m := m) n hk (phi D)) := by
      rw [Finset.mul_sum]
    _ ≤ R * Cprod ^ n *
        (∑ l ∈ B,
          possibleSuccessiveMinimaRadiusWeight (K := K) (m := m) n hk l) :=
      mul_le_mul_of_nonneg_left hinject
        (mul_nonneg hRnonneg (pow_nonneg hCprod _))

end Katznelson
