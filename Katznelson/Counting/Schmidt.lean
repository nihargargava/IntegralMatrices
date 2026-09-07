import Katznelson.Counting.RowLattice

/-!
# Height counting for rational row spaces

The manuscript uses the height-counting theorem for rational subspaces to
control echelon-matrix tails.  This file fixes the Lean interface for that
input.  The theorem below is an imported mathematical result: its source is
W. M. Schmidt, *On Heights of Algebraic Subspaces and Diophantine
Approximations*, Ann. of Math. (2) 85 (1967), Theorem 3 (p. 440).  J. L.
Thunder, *An Asymptotic Estimate for Heights of Algebraic Subspaces*, Trans.
Amer. Math. Soc. 331 (1992), Theorem 1 (p. 395), proves a sharper asymptotic
for the same count.  Thunder is recorded here as a refinement, not as a
second attribution of Schmidt’s original argument.

   The row-space and covolume definitions used in the statement are new Lean
   infrastructure corresponding to Definition `de:height_definition` and the
   row-space discussion in lines 758--815 of `papers/katznelson.tex`.  The
   current Lean row representation uses an equivalent finite-dimensional norm;
   for fixed `K`, norm equivalence changes only the constants in the count,
   not the exponent `m`.
-/

namespace Katznelson

open Set
open scoped Classical NumberField

section

variable {K : Type*} [Field K] [NumberField K]

def rowSpaceHeightBall {m k : ℕ} (T : ℝ) : Set (Grassmannian K m k) :=
  {V | rowSpaceHeight V ≤ T}

/- This is the height-cutoff family corresponding to the manuscript's crude
   estimate `H(D) ≤ C T^(k d)` (lines 1091--1100).  The identification of the
   norm-bounded support family with this height cutoff is a separate geometry-
   of-numbers step; this definition keeps that step explicit. -/
def heightBoundedRowSpaces {m k : ℕ} (C T : ℝ) :
    Set (Grassmannian K m k) :=
  rowSpaceHeightBall (m := m) (k := k) (C * T ^ (k * degree K))

def HasHeightCountBounds {α : Type*} (H : α → ℝ) (p : ℕ) : Prop :=
  ∃ cₗ cᵤ : ℝ, 0 < cₗ ∧ 0 < cᵤ ∧
    ∀ T : ℝ, 1 ≤ T →
      (Set.Finite {x | H x ≤ T}) ∧
        cₗ * T ^ p ≤ (Set.ncard {x | H x ≤ T} : ℝ) ∧
        (Set.ncard {x | H x ≤ T} : ℝ) ≤ cᵤ * T ^ p

/- Imported source theorem.  This is intentionally an explicit interface so
   later Lean proofs can distinguish the cited height count from new
   consequences proved in this repository. -/
axiom schmidt_rowSpaceHeight_count
    {m k : ℕ} (hk : 0 < k) (hkm : k < m) :
    HasHeightCountBounds (rowSpaceHeight (K := K) (m := m) (k := k)) m

/- The intermediate-rank hypothesis in Schmidt's theorem is essential to its
   formulation, but the full-rank stratum is elementary: there is only the
   ambient subspace.  We record this boundary case separately rather than
   forcing it through the imported theorem. -/
theorem grassmannian_fullRank_eq_top {m : ℕ}
    (V : Grassmannian K m m) : V.1 = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  simpa using V.2

instance grassmannian_fullRank_subsingleton (m : ℕ) :
    Subsingleton (Grassmannian K m m) where
  allEq V W := by
    apply Subtype.ext
    rw [grassmannian_fullRank_eq_top V, grassmannian_fullRank_eq_top W]

theorem rowSpaceHeightBall_finite_fullRank {m : ℕ} {T : ℝ} :
    (rowSpaceHeightBall (K := K) (m := m) (k := m) T).Finite := by
  have hsub :
      (rowSpaceHeightBall (K := K) (m := m) (k := m) T).Subsingleton := by
    intro V hV W hW
    exact Subsingleton.elim V W
  exact hsub.finite

theorem grassmannian_zeroRank_eq_bot {m : ℕ}
    (V : Grassmannian K m 0) : V.1 = ⊥ := by
  apply Submodule.finrank_eq_zero.mp
  exact V.2

instance grassmannian_zeroRank_subsingleton (m : ℕ) :
    Subsingleton (Grassmannian K m 0) where
  allEq V W := by
    apply Subtype.ext
    rw [grassmannian_zeroRank_eq_bot V, grassmannian_zeroRank_eq_bot W]

theorem rowSpaceHeightBall_finite_zeroRank {m : ℕ} {T : ℝ} :
    (rowSpaceHeightBall (K := K) (m := m) (k := 0) T).Finite := by
  have hsub :
      (rowSpaceHeightBall (K := K) (m := m) (k := 0) T).Subsingleton := by
    intro V hV W hW
    exact Subsingleton.elim V W
  exact hsub.finite

theorem rowSpaceHeightBall_finite
    {m k : ℕ} (hk : 0 < k) (hkm : k < m) {T : ℝ} (hT : 1 ≤ T) :
    (rowSpaceHeightBall (K := K) (m := m) (k := k) T).Finite := by
  obtain ⟨cₗ, cᵤ, hcₗ, hcᵤ, hcount⟩ :=
    schmidt_rowSpaceHeight_count (K := K) hk hkm
  exact (hcount T hT).1

theorem rowSpaceHeightBall_finite_of_intermediate
    {m k : ℕ} (hk : 0 < k) (hkm : k < m) {T : ℝ} :
    (rowSpaceHeightBall (K := K) (m := m) (k := k) T).Finite := by
  by_cases hT : 1 ≤ T
  · exact rowSpaceHeightBall_finite hk hkm hT
  · apply Set.Finite.subset (rowSpaceHeightBall_finite hk hkm le_rfl)
    intro V hV
    change rowSpaceHeight V ≤ T at hV
    change rowSpaceHeight V ≤ 1
    exact hV.trans (le_of_not_ge hT)

theorem rowSpaceHeightBall_finite_of_rank_le
    {m k : ℕ} (hkm : k ≤ m) {T : ℝ} :
    (rowSpaceHeightBall (K := K) (m := m) (k := k) T).Finite := by
  by_cases hk0 : k = 0
  · subst k
    exact rowSpaceHeightBall_finite_zeroRank
  by_cases hkeq : k = m
  · subst k
    exact rowSpaceHeightBall_finite_fullRank
  · exact rowSpaceHeightBall_finite_of_intermediate
      (Nat.pos_of_ne_zero hk0) (lt_of_le_of_ne hkm hkeq)

theorem rowSpaceHeightBall_count_upper
    {m k : ℕ} (hk : 0 < k) (hkm : k < m) :
    ∃ cᵤ : ℝ, 0 < cᵤ ∧ ∀ {T : ℝ}, 1 ≤ T →
      (Set.ncard (rowSpaceHeightBall (K := K) (m := m) (k := k) T) : ℝ) ≤
        cᵤ * T ^ m := by
  obtain ⟨cₗ, cᵤ, hcₗ, hcᵤ, hcount⟩ :=
    schmidt_rowSpaceHeight_count (K := K) hk hkm
  refine ⟨cᵤ, hcᵤ, ?_⟩
  intro T hT
  simpa [rowSpaceHeightBall] using (hcount T hT).2.2

/- The two boundary ranks have one Grassmannian point, so the same upper
   bound is available uniformly for every `k ≤ m`. -/
theorem rowSpaceHeightBall_count_upper_of_rank_le
    {m k : ℕ} (hkm : k ≤ m) :
    ∃ cᵤ : ℝ, 0 < cᵤ ∧ ∀ {T : ℝ}, 1 ≤ T →
      (Set.ncard (rowSpaceHeightBall (K := K) (m := m) (k := k) T) : ℝ) ≤
        cᵤ * T ^ m := by
  by_cases hk0 : k = 0
  · subst k
    refine ⟨1, one_pos, ?_⟩
    intro T hT
    have hcard : Set.ncard
        (rowSpaceHeightBall (K := K) (m := m) (k := 0) T) ≤ 1 :=
      Set.ncard_le_one_of_subsingleton _
    have hcardR :
        (Set.ncard
          (rowSpaceHeightBall (K := K) (m := m) (k := 0) T) : ℝ) ≤ 1 := by
      exact_mod_cast hcard
    exact hcardR.trans (by simpa using (one_le_pow₀ hT))
  by_cases hkm_eq : k = m
  · subst k
    refine ⟨1, one_pos, ?_⟩
    intro T hT
    have hcard : Set.ncard
        (rowSpaceHeightBall (K := K) (m := m) (k := m) T) ≤ 1 :=
      Set.ncard_le_one_of_subsingleton _
    have hcardR :
        (Set.ncard
          (rowSpaceHeightBall (K := K) (m := m) (k := m) T) : ℝ) ≤ 1 := by
      exact_mod_cast hcard
    exact hcardR.trans (by simpa using (one_le_pow₀ hT))
  exact rowSpaceHeightBall_count_upper (K := K)
    (Nat.pos_of_ne_zero hk0) (lt_of_le_of_ne hkm hkm_eq)

theorem heightBoundedRowSpaces_finite
    {m k : ℕ} (hk : 0 < k) (hkm : k < m)
    {C T : ℝ} (hC : 1 ≤ C) (hT : 1 ≤ T) :
    (heightBoundedRowSpaces (K := K) (m := m) (k := k) C T).Finite := by
  apply rowSpaceHeightBall_finite hk hkm
  calc
    (1 : ℝ) = 1 * 1 := by norm_num
    _ ≤ C * T ^ (k * degree K) :=
      mul_le_mul hC (one_le_pow₀ hT) (by norm_num)
        (le_trans (by norm_num) hC)

theorem heightBoundedRowSpaces_count_upper
    {m k : ℕ} (hk : 0 < k) (hkm : k < m) :
    ∃ cᵤ : ℝ, 0 < cᵤ ∧ ∀ {C T : ℝ}, 1 ≤ C → 1 ≤ T →
      (Set.ncard (heightBoundedRowSpaces (K := K) (m := m) (k := k) C T) : ℝ) ≤
        cᵤ * (C * T ^ (k * degree K)) ^ m := by
  obtain ⟨cᵤ, hcᵤ, hcount⟩ :=
    rowSpaceHeightBall_count_upper (K := K) hk hkm
  refine ⟨cᵤ, hcᵤ, ?_⟩
  intro C T hC hT
  have hB : (1 : ℝ) ≤ C * T ^ (k * degree K) := by
    calc
      (1 : ℝ) = 1 * 1 := by norm_num
      _ ≤ C * T ^ (k * degree K) :=
        mul_le_mul hC (one_le_pow₀ hT) (by norm_num)
          (le_trans (by norm_num) hC)
  simpa [heightBoundedRowSpaces] using
    hcount hB

theorem heightBoundedRowSpaces_count_upper_of_rank_le
    {m k : ℕ} (hkm : k ≤ m) :
    ∃ cᵤ : ℝ, 0 < cᵤ ∧ ∀ {C T : ℝ}, 1 ≤ C → 1 ≤ T →
      (Set.ncard (heightBoundedRowSpaces (K := K) (m := m) (k := k) C T) : ℝ) ≤
        cᵤ * (C * T ^ (k * degree K)) ^ m := by
  by_cases hk0 : k = 0
  · subst k
    refine ⟨1, one_pos, ?_⟩
    intro C T hC hT
    have hcard : Set.ncard
        (heightBoundedRowSpaces (K := K) (m := m) (k := 0) C T) ≤ 1 := by
      apply Set.ncard_le_one_of_subsingleton
    have hcardR :
        (Set.ncard
          (heightBoundedRowSpaces (K := K) (m := m) (k := 0) C T) : ℝ) ≤ 1 := by
      exact_mod_cast hcard
    have hbase : (1 : ℝ) ≤ C * T ^ (0 * degree K) := by
      simp only [zero_mul, pow_zero, mul_one]
      exact hC
    exact hcardR.trans (by simpa using (one_le_pow₀ hbase :
      (1 : ℝ) ≤ (C * T ^ (0 * degree K)) ^ m))
  by_cases hkm_eq : k = m
  · subst k
    refine ⟨1, one_pos, ?_⟩
    intro C T hC hT
    have hcard : Set.ncard
        (heightBoundedRowSpaces (K := K) (m := m) (k := m) C T) ≤ 1 := by
      apply Set.ncard_le_one_of_subsingleton
    have hcardR :
        (Set.ncard
          (heightBoundedRowSpaces (K := K) (m := m) (k := m) C T) : ℝ) ≤ 1 := by
      exact_mod_cast hcard
    have hbase : (1 : ℝ) ≤ C * T ^ (m * degree K) := by
      calc
        (1 : ℝ) = 1 * 1 := by norm_num
        _ ≤ C * T ^ (m * degree K) :=
          mul_le_mul hC (one_le_pow₀ hT) (by norm_num)
            (le_trans (by norm_num) hC)
    exact hcardR.trans (by simpa using (one_le_pow₀ hbase :
      (1 : ℝ) ≤ (C * T ^ (m * degree K)) ^ m))
  exact heightBoundedRowSpaces_count_upper (K := K)
    (Nat.pos_of_ne_zero hk0) (lt_of_le_of_ne hkm hkm_eq)

end

end Katznelson
