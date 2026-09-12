import Katznelson.MainTheorems
import Katznelson.Counting.CriticalMinimaSums
import Katznelson.Counting.FixedRankError
import Katznelson.Counting.MainTermNormalization
import Katznelson.Counting.LiftCovolume
import Katznelson.Counting.UniformFiniteAssembly
import Katznelson.Counting.UniformHeightTail
import Katznelson.Counting.UniformHeightTailLiteral
import Katznelson.Counting.UniformIntegral
import Katznelson.Counting.UniformLowerRank
import Katznelson.Counting.UniformLowerRankLiteral

/-!
# Final assembly of the paper's two main theorems

This module joins the manuscript-facing estimates proved in the counting
modules.  It deliberately contains only the final case split and error-term
assembly; the geometric, Riemann-sum, lower-rank, and height-tail estimates
remain visible as separately attributed inputs.
-/

namespace Katznelson

open Set
open scoped Classical NumberField

attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

/- [Lean infrastructure for paper `co:covering_bound`, lines 1239--1248]
One fixed auxiliary cutoff dominates the support constant, the coefficient
projection constant, and `1`.  It is selected before the scale `T`, as the
manuscript requires. -/
noncomputable def fixedRankAuxiliaryBound
    (K : Type*) [Field K] [NumberField K] (m : ℕ) (Csup : ℝ) : ℝ :=
  max 1 (max Csup
    (rowKRealSmulBound (K := K) (m := m) *
      numberFieldCoefficientRadius K))

/- [Lean infrastructure for `fixedRankAuxiliaryBound`] -/
theorem fixedRankAuxiliaryBound_one_le
    {K : Type*} [Field K] [NumberField K] (m : ℕ) (Csup : ℝ) :
    1 ≤ fixedRankAuxiliaryBound K m Csup := by
  exact le_max_left _ _

/- [Lean infrastructure for `fixedRankAuxiliaryBound`] -/
theorem fixedRankAuxiliaryBound_support_le
    {K : Type*} [Field K] [NumberField K] (m : ℕ) (Csup : ℝ) :
    Csup ≤ fixedRankAuxiliaryBound K m Csup := by
  exact (le_max_left _ _).trans (le_max_right _ _)

/- [Lean infrastructure for `fixedRankAuxiliaryBound`] -/
theorem fixedRankAuxiliaryBound_projection_le
    {K : Type*} [Field K] [NumberField K] (m : ℕ) (Csup : ℝ) :
    rowKRealSmulBound (K := K) (m := m) *
        numberFieldCoefficientRadius K ≤
      fixedRankAuxiliaryBound K m Csup := by
  exact (le_max_right _ _).trans (le_max_right _ _)

/- [Lean infrastructure for paper Theorem `th:main`, lines 1641--1800]
The radius estimate has exactly two dimension regimes: the strictly
convergent case, or `degree K = 1` and `n = m + 1`. -/
theorem fixedRank_radius_gap_or_critical
    {n m d : ℕ} (hnm : m < n) (hd : 1 ≤ d) :
    1 < (n - m) * d ∨ (d = 1 ∧ n = m + 1) := by
  have hcodim : 1 ≤ n - m := by omega
  by_cases hdone : d = 1
  · subst d
    by_cases hcodim_one : n - m = 1
    · right
      constructor
      · rfl
      · omega
    · left
      simp only [mul_one]
      omega
  · left
    have hdtwo : 2 ≤ d := by omega
    nlinarith

/- [Lean infrastructure for paper Theorem `th:main`, lines 1716--1800]
Inside the critical radius regime, the manuscript separates rank one from
the higher-rank argument beginning with equation `eq:two_terms`. -/
theorem fixedRank_critical_rank_cases {k : ℕ} (hk : 1 ≤ k) :
    k = 1 ∨ 2 ≤ k := by
  omega

/- [derived consequence of the two manuscript case splits above] The only
failure of the paper's better `T⁻¹` error criterion is precisely its stated
degree-one, rank-one, codimension-one exception. -/
theorem fixedRank_exceptional_of_not_nonexceptional
    {n m k d : ℕ} (hnm : m < n) (hk : 1 ≤ k) (hd : 1 ≤ d)
    (hnot : ¬ 1 < (n - m) * d * k) :
    d = 1 ∧ k = 1 ∧ m = n - 1 := by
  have hcodim : 1 ≤ n - m := by omega
  have hprod : (n - m) * d * k ≤ 1 := Nat.le_of_not_gt hnot
  have hd_le_prod : d ≤ (n - m) * d * k := by
    simpa using Nat.mul_le_mul (Nat.mul_le_mul hcodim (le_refl d)) hk
  have hk_le_prod : k ≤ (n - m) * d * k := by
    simpa using Nat.mul_le_mul (Nat.mul_le_mul hcodim hd) (le_refl k)
  have hd_one : d = 1 := by omega
  have hk_one : k = 1 := by omega
  subst d
  subst k
  simp only [mul_one] at hprod
  refine ⟨rfl, rfl, ?_⟩
  omega

/- [derived consequence of the preceding arithmetic split] Away from the
exception displayed in `th:main`, the exponent controlling the assembled
error terms is strictly larger than one. -/
theorem fixedRank_nonexceptional_exponent
    {n m k d : ℕ} (hnm : m < n) (hk : 1 ≤ k) (hd : 1 ≤ d)
    (hnot : ¬(d = 1 ∧ k = 1 ∧ m = n - 1)) :
    1 < (n - m) * d * k := by
  by_contra h
  exact hnot (fixedRank_exceptional_of_not_nonexceptional hnm hk hd h)

/- [derived consequence of paper equation `eq:just_as_before`, lines
   1724--1800] Outside the stated degree-one/rank-one/codimension-one
   exception, the exact bounded-row-space family has a radius sum bounded by
   one constant selected before `T`.  The proof follows the manuscript's two
   cases: the convergent minimum sum, or its critical higher-rank argument. -/
theorem exists_fixedRank_nonexceptional_latticeVoronoi_radius_sum_bound
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (hnm : m < n) (hkm : k ≤ m) (hk : 1 ≤ k)
    (hnonexceptional :
      ¬(degree K = 1 ∧ k = 1 ∧ m = n - 1))
    (c : ℝ) (hc : 1 ≤ c) :
    ∃ C_R : ℝ, 0 < C_R ∧
      ∀ {Csup T : ℝ}
        [Fintype (boundedRowSpaces (K := K) (n := n) (m := m)
          (k := k) Csup T)]
        (hCproj : rowKRealSmulBound (K := K) (m := m) *
          numberFieldCoefficientRadius K ≤ c)
        (hCsup : Csup ≤ c) (hT : 0 ≤ T),
        (∑ V : boundedRowSpaces (K := K) (n := n) (m := m)
          (k := k) Csup T,
          (Real.sqrt (n : ℝ) *
              latticeCoveringRadius (rowZLattice V.1)) /
            rowMatrixLatticeCovolume V.1 n) ≤ C_R := by
  have hm : 0 < m := by omega
  cases k with
  | zero => omega
  | succ j =>
      rcases fixedRank_radius_gap_or_critical hnm
          (show 1 ≤ degree K from Module.finrank_pos) with hgap | hcritical
      · obtain ⟨C_R, hC_R, hbound⟩ :=
          exists_uniform_boundedRowSpaces_latticeVoronoi_radius_sum_bound_of_noncritical_of_fiekerStehle
            (K := K) (m := m) (n := n) (j := j) hm hgap
        refine ⟨C_R, hC_R, ?_⟩
        intro Csup T _ hCproj hCsup hT
        exact hbound hCproj hCsup hT
      · rcases hcritical with ⟨hdegree, hn⟩
        cases j with
        | zero =>
            exfalso
            apply hnonexceptional
            refine ⟨hdegree, rfl, ?_⟩
            omega
        | succ q =>
            have hmtwo : 1 < m := by omega
            subst n
            obtain ⟨C_R, hC_R, hbound⟩ :=
              exists_uniform_boundedRowSpaces_latticeVoronoi_radius_sum_bound_of_critical_higher_rank
                (K := K) (m := m) (j := q) hmtwo hdegree c hc
            refine ⟨C_R, hC_R, ?_⟩
            intro Csup T _ hCproj hCsup hT
            exact hbound hCproj hCsup hT

/- [derived consequence; author-approved adaptation around paper subsection
   `ss:log_term`, lines 324--358, and its use at lines 1716--1724] In the
   unique exceptional dimensions, prove the logarithmic radius sum on the
   exact bounded-row-space family.  The manuscript discusses the unit-ball
   case; the author has permitted this replacement for arbitrary admissible
   functions only in this exceptional branch. -/
theorem exists_fixedRank_exceptional_latticeVoronoi_radius_sum_bound
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (hkm : k ≤ m)
    (hexceptional : degree K = 1 ∧ k = 1 ∧ m = n - 1)
    (c : ℝ) (hc : 0 ≤ c) :
    ∃ C_R : ℝ, 0 < C_R ∧
      ∀ {Csup T : ℝ}
        [Fintype (boundedRowSpaces (K := K) (n := n) (m := m)
          (k := k) Csup T)]
        (hCproj : rowKRealSmulBound (K := K) (m := m) *
          numberFieldCoefficientRadius K ≤ c)
        (hCsup : Csup ≤ c) (hT : 1 ≤ T),
        (∑ V : boundedRowSpaces (K := K) (n := n) (m := m)
          (k := k) Csup T,
          (Real.sqrt (n : ℝ) *
              latticeCoveringRadius (rowZLattice V.1)) /
            rowMatrixLatticeCovolume V.1 n) ≤
          C_R * (1 + Real.log T) := by
  rcases hexceptional with ⟨hdegree, hkone, hm⟩
  have hn : n = m + 1 := by omega
  have hmpos : 0 < m := by omega
  subst k
  subst n
  exact
    exists_boundedRowSpaces_latticeVoronoi_radius_sum_bound_of_critical_rank_one
      (K := K) (m := m) hmpos hdegree c hc

/- [derived consequence of the manuscript's exceptional error scale, line
   1651] The factor produced by the literal rank-one radius sum is absorbed
   into `T⁻¹ log T` on the paper's range `T ≥ 2`. -/
theorem one_add_log_div_le_three_inv_mul_log
    {T : ℝ} (hT : 2 ≤ T) :
    (1 + Real.log T) / T ≤ 3 * (T⁻¹ * Real.log T) := by
  simpa [div_eq_mul_inv, zpow_neg_one] using
    one_add_log_mul_zpow_neg_one_le_three_inv_mul_log hT

/- [derived consequence of paper lines 1641--1724] Arithmetic wrapper for
the finite-family estimate in the exceptional degree-one, rank-one,
codimension-one case.  The first term is exactly the logarithmic radius sum;
the remaining two are the displayed lower-rank and height-tail errors. -/
theorem fixedRankError_le_inv_log_of_critical_rank_one_bounds
    {n m d : ℕ} {T E C_a C_R C_lower C_tail : ℝ}
    (hT : 2 ≤ T) (hn : n = m + 1) (hd : d = 1)
    (hC_a : 0 ≤ C_a) (hC_R : 0 ≤ C_R)
    (hC_lower : 0 ≤ C_lower) (hC_tail : 0 ≤ C_tail)
    (hsplit : E ≤
      C_a * (C_R * (1 + Real.log T)) / T +
        C_lower * ((1 + Real.log T) *
          T ^ (-(d : ℤ) * ((n - m + 1 - 1 : ℕ) : ℤ))) +
        C_tail * T ^ (-(d : ℤ))) :
    E ≤ (3 * C_a * C_R + 3 * C_lower + 2 * C_tail) *
      (T⁻¹ * Real.log T) := by
  have hcoeff : 0 ≤ C_a * C_R := mul_nonneg hC_a hC_R
  have hradius : C_a * (C_R * (1 + Real.log T)) / T ≤
      (3 * C_a * C_R) * (T⁻¹ * Real.log T) := by
    calc
      C_a * (C_R * (1 + Real.log T)) / T =
          (C_a * C_R) * ((1 + Real.log T) / T) := by ring
      _ ≤ (C_a * C_R) * (3 * (T⁻¹ * Real.log T)) :=
        mul_le_mul_of_nonneg_left
          (one_add_log_div_le_three_inv_mul_log hT) hcoeff
      _ = (3 * C_a * C_R) * (T⁻¹ * Real.log T) := by ring
  have hmain := fixedRankError_le_inv_log_of_exceptional_bounds
    (n := n) (m := m) (k := 1) (d := d) (T := T) (E := E)
    (E_exceptional := C_a * (C_R * (1 + Real.log T)) / T)
    (E_radius := 0)
    (E_lower := C_lower * ((1 + Real.log T) *
      T ^ (-(d : ℤ) * ((n - m + 1 - 1 : ℕ) : ℤ))))
    (E_tail := C_tail * T ^ (-(d : ℤ)))
    (C_exceptional := 3 * C_a * C_R) (C_radius := 0)
    (C_lower := C_lower) (C_tail := C_tail)
    hT hn rfl hd (by norm_num) hC_lower hC_tail
    (by simpa using hsplit) hradius (by norm_num) le_rfl le_rfl
  simpa using hmain

/- [Lean infrastructure for paper Lemma `le:low_rank_terms`, lines
1495--1501] The manuscript's termwise-absolute lower-rank sum dominates the
absolute value of each inner lower-rank sum.  This is the sole bridge needed
to feed the stronger literal lemma into the finite-family error assembly. -/
theorem finite_lowerRank_sum_abs_le_termwiseAbs
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (B : Set (Grassmannian K m k)) [Fintype B]
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    {T : ℝ} (hT : 0 < T) :
    (∑ V : B, |∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
        f (T⁻¹ • embedMatrix A.1)|) ≤
      ∑ V : B, ∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
        |f (T⁻¹ • embedMatrix A.1)| := by
  apply Finset.sum_le_sum
  intro V hV
  have hs : Summable (fun A : {A : IntegralMatrix K n m //
      rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k} =>
      f (T⁻¹ • embedMatrix A.1)) :=
    (summable_scaled_integralMatrices f h_f hT).comp_injective
      Subtype.val_injective
  simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs.norm

/- [derived consequence of paper Theorem `th:main`, proof lines
   1641--1800] Assemble the manuscript's exact finite family, its pointwise
   Voronoi estimate, the literal lower-rank contribution, the height tail,
   and the two non-exceptional radius arguments.  All constants are chosen
   before `T`; Schmidt's cited height count remains the explicit hypothesis
   `hcount`. -/
set_option maxHeartbeats 6000000 in
theorem exists_fixedRank_nonexceptional_normalized_error_bound
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (hnm : m < n) (hkm : k ≤ m) (hk : 1 ≤ k)
    (hnonexceptional :
      ¬(degree K = 1 ∧ k = 1 ∧ m = n - 1))
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    (hcount : ∀ l : ℕ, 1 ≤ l → l ≤ k → l < m →
      HasHeightCountBounds
        (rowSpaceHeight (K := K) (m := m) (k := l)) m) :
    ∃ C_error : ℝ, 0 < C_error ∧ ∀ T : ℝ, 2 ≤ T →
      |fixedRankSum n m k f T / T ^ (k * n * degree K) -
          mainConstant n m k f| ≤ C_error * T⁻¹ := by
  have hkpos : 0 < k := by omega
  have hnpos : 0 < n := by omega
  have hkn : k ≤ n := hkm.trans hnm.le
  have hd : 1 ≤ degree K := Module.finrank_pos
  have hcountAll := heightCountBounds_upTo_of_intermediate
    (K := K) hkm hcount
  obtain ⟨Csup, hCsup, hSupport⟩ :=
    exists_scaledSupport_integralMatrix_norm_bound f h_f
  let c : ℝ := fixedRankAuxiliaryBound K m Csup
  have hc : 1 ≤ c := fixedRankAuxiliaryBound_one_le m Csup
  have hCproj :
      rowKRealSmulBound (K := K) (m := m) *
          numberFieldCoefficientRadius K ≤ c :=
    fixedRankAuxiliaryBound_projection_le m Csup
  have hCsup_c : Csup ≤ c := fixedRankAuxiliaryBound_support_le m Csup
  obtain ⟨_εMax, Cₐ, _hεMax, hCₐ, hpoint⟩ :=
    h_f.exists_uniform_boundedRowSpaces_rank_latticeVoronoi_estimate_with_lower
      f hkpos hnpos Csup hCsup
  obtain ⟨C_lower, hC_lower, hLower⟩ :=
    exists_uniform_echelon_calF_lowerRank_normalized_abs_sum_le_of_raw_covering_bound_literal
      f h_f hnm hkm hk hCsup hSupport hcountAll
  obtain ⟨C_dom, hC_dom, hdom⟩ :=
    h_f.exists_uniform_mainSummand_integral_domination f hnpos hkpos
  have hkIcc : k ∈ Finset.Icc 1 k :=
    Finset.mem_Icc.mpr ⟨hk, le_rfl⟩
  obtain ⟨C_tail, hC_tail, hTail⟩ :=
    exists_uniform_boundedRowSpaces_mainConstant_tail_abs_le_literal
      hnm hkn hkm hkpos hCsup (hcountAll k hkIcc) hC_dom hdom
  obtain ⟨C_R, hC_R, hRadius⟩ :=
    exists_fixedRank_nonexceptional_latticeVoronoi_radius_sum_bound
      hnm hkm hk hnonexceptional c hc
  let C_error : ℝ := Cₐ * C_R + C_lower + C_tail
  have hC_error : 0 < C_error := by
    dsimp [C_error]
    positivity
  refine ⟨C_error, hC_error, ?_⟩
  intro T hTtwo
  have hTone : 1 ≤ T := by linarith
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hTone
  have hTnonneg : 0 ≤ T := hTpos.le
  letI : Fintype
      (boundedRowSpaces (K := K) (n := n) (m := m) (k := k) Csup T) :=
    (finite_boundedRowSpaces (K := K) (n := n) (m := m) (k := k)
      Csup T).fintype
  have hactive : activeRowSpaces (K := K) (k := k) f T ⊆
      boundedRowSpaces (K := K) (n := n) (m := m) (k := k) Csup T := by
    rintro V ⟨A, hrows, hrank, hnonzero⟩
    exact ⟨A, hrows, hrank, hSupport T hTpos A hnonzero⟩
  have hexponent : k * n * degree K = n * (k * degree K) := by ring
  have hLowerT :
      (∑ V : boundedRowSpaces (K := K) (n := n) (m := m) (k := k)
          Csup T,
          |∑' A : {A : IntegralMatrix K n m //
            rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
            f (T⁻¹ • embedMatrix A.1)|) /
        T ^ (n * (k * degree K)) ≤
          C_lower * (1 + Real.log T) *
            T ^ (-(degree K : ℤ) *
              ((n - m + k - 1 : ℕ) : ℤ)) := by
    have hLower' := hLower T hTtwo
    rw [echelon_calF_image_eq_boundedRowSpaces
      (K := K) (l := k) (m := m) (n := n) (Csup := Csup) (T := T)] at hLower'
    have hLiteral :
        (∑ V : boundedRowSpaces (K := K) (n := n) (m := m) (k := k)
            Csup T,
            ∑' A : {A : IntegralMatrix K n m //
              rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
              |f (T⁻¹ • embedMatrix A.1)|) /
          T ^ (n * (k * degree K)) ≤
            C_lower * (1 + Real.log T) *
              T ^ (-(degree K : ℤ) *
                ((n - m + k - 1 : ℕ) : ℤ)) := by
      simpa only [tsum_fintype, hexponent] using hLower'
    have hnumerator := finite_lowerRank_sum_abs_le_termwiseAbs
      (boundedRowSpaces (K := K) (n := n) (m := m) (k := k) Csup T)
      f h_f hTpos
    exact (div_le_div_of_nonneg_right hnumerator
      (pow_pos hTpos _).le).trans hLiteral
  have hfinite :=
    finite_rowMatrix_rank_latticeVoronoi_error_with_mainConstant_bound
      (boundedRowSpaces (K := K) (n := n) (m := m) (k := k) Csup T)
      (f := f) (T := T) (Cₐ := Cₐ) (C_R := C_R)
      (E_lower := C_lower * (1 + Real.log T) *
        T ^ (-(degree K : ℤ) *
          ((n - m + k - 1 : ℕ) : ℤ)))
      (E_tail := C_tail * T ^ (-(degree K : ℤ)))
      hTpos hCₐ.le (hpoint T hTpos) hLowerT
      (hRadius hCproj hCsup_c hTnonneg) (hTail T hTtwo)
  have hfinite_inv := fixedRankError_le_inv_of_nonexceptional_bounds
    (n := n) (m := m) (k := k) (d := degree K) (T := T)
    (E := |finiteRowMatrixRankNormalizedSum
      (boundedRowSpaces (K := K) (n := n) (m := m) (k := k) Csup T)
        f T - mainConstant n m k f|)
    (E_radius := Cₐ * C_R / T)
    (E_lower := C_lower * (1 + Real.log T) *
      T ^ (-(degree K : ℤ) *
        ((n - m + k - 1 : ℕ) : ℤ)))
    (E_tail := C_tail * T ^ (-(degree K : ℤ)))
    (C_radius := Cₐ * C_R) (C_lower := C_lower) (C_tail := C_tail)
    hTone hnm hk hd
      (fixedRank_nonexceptional_exponent hnm hk hd hnonexceptional)
    hC_lower.le hC_tail.le hfinite le_rfl
      (by ring_nf; exact le_rfl) le_rfl
  have hnormalized :=
    fixedRankSum_normalized_eq_boundedRowSpaces f h_f hTpos hactive
  calc
    |fixedRankSum n m k f T / T ^ (k * n * degree K) -
        mainConstant n m k f| =
        |fixedRankSum n m k f T / T ^ (n * (k * degree K)) -
          mainConstant n m k f| := by rw [hexponent]
    _ = |finiteRowMatrixRankNormalizedSum
          (boundedRowSpaces (K := K) (n := n) (m := m) (k := k) Csup T)
          f T - mainConstant n m k f| := by rw [hnormalized]
    _ ≤ C_error * T⁻¹ := by
      simpa [C_error, div_eq_mul_inv] using hfinite_inv

/- [derived consequence; author-approved adaptation around paper Theorem
   `th:main`, exceptional case at lines 1716--1724] Assemble the same exact
   finite-family decomposition in degree one, rank one, and codimension one,
   using the proved critical logarithmic radius sum.  The author has permitted
   this replacement argument only for this exceptional branch. -/
set_option maxHeartbeats 6000000 in
theorem exists_fixedRank_exceptional_normalized_error_bound
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (hnm : m < n) (hkm : k ≤ m) (hk : 1 ≤ k)
    (hexceptional : degree K = 1 ∧ k = 1 ∧ m = n - 1)
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    (hcount : ∀ l : ℕ, 1 ≤ l → l ≤ k → l < m →
      HasHeightCountBounds
        (rowSpaceHeight (K := K) (m := m) (k := l)) m) :
    ∃ C_error : ℝ, 0 < C_error ∧ ∀ T : ℝ, 2 ≤ T →
      |fixedRankSum n m k f T / T ^ (k * n * degree K) -
          mainConstant n m k f| ≤ C_error * T⁻¹ * Real.log T := by
  rcases hexceptional with ⟨hdegree, hkone, hm⟩
  subst k
  have hmpos : 0 < m := by omega
  have hnpos : 0 < n := by omega
  have hn : n = m + 1 := by omega
  have hkn : 1 ≤ n := by omega
  have hcountAll := heightCountBounds_upTo_of_intermediate
    (K := K) hkm hcount
  obtain ⟨Csup, hCsup, hSupport⟩ :=
    exists_scaledSupport_integralMatrix_norm_bound f h_f
  let c : ℝ := fixedRankAuxiliaryBound K m Csup
  have hc : 1 ≤ c := fixedRankAuxiliaryBound_one_le m Csup
  have hCproj :
      rowKRealSmulBound (K := K) (m := m) *
          numberFieldCoefficientRadius K ≤ c :=
    fixedRankAuxiliaryBound_projection_le m Csup
  have hCsup_c : Csup ≤ c := fixedRankAuxiliaryBound_support_le m Csup
  obtain ⟨_εMax, Cₐ, _hεMax, hCₐ, hpoint⟩ :=
    h_f.exists_uniform_boundedRowSpaces_rank_latticeVoronoi_estimate_with_lower
      (k := 1) f (by omega) hnpos Csup hCsup
  obtain ⟨C_lower, hC_lower, hLower⟩ :=
    exists_uniform_echelon_calF_lowerRank_normalized_abs_sum_le_of_raw_covering_bound_literal
      f h_f hnm hkm (by omega) hCsup hSupport hcountAll
  obtain ⟨C_dom, hC_dom, hdom⟩ :=
    h_f.exists_uniform_mainSummand_integral_domination
      (k := 1) f hnpos (by omega)
  have hkIcc : 1 ∈ Finset.Icc 1 1 := by simp
  obtain ⟨C_tail, hC_tail, hTail⟩ :=
    exists_uniform_boundedRowSpaces_mainConstant_tail_abs_le_literal
      (k := 1) (f := f) hnm hkn hkm (by omega) hCsup
      (hcountAll 1 hkIcc) hC_dom hdom
  obtain ⟨C_R, hC_R, hRadius⟩ :=
    exists_fixedRank_exceptional_latticeVoronoi_radius_sum_bound
      (K := K) (n := n) (m := m) (k := 1) hkm
      ⟨hdegree, rfl, hm⟩ c (le_trans zero_le_one hc)
  let C_error : ℝ := 3 * Cₐ * C_R + 3 * C_lower + 2 * C_tail
  have hC_error : 0 < C_error := by
    dsimp [C_error]
    positivity
  refine ⟨C_error, hC_error, ?_⟩
  intro T hTtwo
  have hTone : 1 ≤ T := by linarith
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hTone
  letI : Fintype
      (boundedRowSpaces (K := K) (n := n) (m := m) (k := 1) Csup T) :=
    (finite_boundedRowSpaces (K := K) (n := n) (m := m) (k := 1)
      Csup T).fintype
  have hactive : activeRowSpaces (K := K) (k := 1) f T ⊆
      boundedRowSpaces (K := K) (n := n) (m := m) (k := 1) Csup T := by
    rintro V ⟨A, hrows, hrank, hnonzero⟩
    exact ⟨A, hrows, hrank, hSupport T hTpos A hnonzero⟩
  have hexponent : 1 * n * degree K = n * (1 * degree K) := by ring
  have hLowerT :
      (∑ V : boundedRowSpaces (K := K) (n := n) (m := m) (k := 1)
          Csup T,
          |∑' A : {A : IntegralMatrix K n m //
            rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < 1},
            f (T⁻¹ • embedMatrix A.1)|) /
        T ^ (n * (1 * degree K)) ≤
          C_lower * (1 + Real.log T) *
            T ^ (-(degree K : ℤ) *
              ((n - m + 1 - 1 : ℕ) : ℤ)) := by
    have hLower' := hLower T hTtwo
    rw [echelon_calF_image_eq_boundedRowSpaces
      (K := K) (l := 1) (m := m) (n := n) (Csup := Csup) (T := T)] at hLower'
    have hLiteral :
        (∑ V : boundedRowSpaces (K := K) (n := n) (m := m) (k := 1)
            Csup T,
            ∑' A : {A : IntegralMatrix K n m //
              rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < 1},
              |f (T⁻¹ • embedMatrix A.1)|) /
          T ^ (n * (1 * degree K)) ≤
            C_lower * (1 + Real.log T) *
              T ^ (-(degree K : ℤ) *
                ((n - m + 1 - 1 : ℕ) : ℤ)) := by
      simpa only [tsum_fintype, hexponent] using hLower'
    have hnumerator := finite_lowerRank_sum_abs_le_termwiseAbs
      (boundedRowSpaces (K := K) (n := n) (m := m) (k := 1) Csup T)
      f h_f hTpos
    exact (div_le_div_of_nonneg_right hnumerator
      (pow_pos hTpos _).le).trans hLiteral
  have hfinite :=
    finite_rowMatrix_rank_latticeVoronoi_error_with_mainConstant_bound
      (boundedRowSpaces (K := K) (n := n) (m := m) (k := 1) Csup T)
      (f := f) (T := T) (Cₐ := Cₐ)
      (C_R := C_R * (1 + Real.log T))
      (E_lower := C_lower * (1 + Real.log T) *
        T ^ (-(degree K : ℤ) *
          ((n - m + 1 - 1 : ℕ) : ℤ)))
      (E_tail := C_tail * T ^ (-(degree K : ℤ)))
      hTpos hCₐ.le (hpoint T hTpos) hLowerT
      (hRadius hCproj hCsup_c hTone) (hTail T hTtwo)
  have hfinite_log := fixedRankError_le_inv_log_of_critical_rank_one_bounds
    (n := n) (m := m) (d := degree K) (T := T)
    (E := |finiteRowMatrixRankNormalizedSum
      (boundedRowSpaces (K := K) (n := n) (m := m) (k := 1) Csup T)
        f T - mainConstant n m 1 f|)
    (C_a := Cₐ) (C_R := C_R) (C_lower := C_lower) (C_tail := C_tail)
    hTtwo hn hdegree hCₐ.le hC_R.le hC_lower.le hC_tail.le
    (by simpa [mul_assoc] using hfinite)
  have hnormalized :=
    fixedRankSum_normalized_eq_boundedRowSpaces f h_f hTpos hactive
  calc
    |fixedRankSum n m 1 f T / T ^ (1 * n * degree K) -
        mainConstant n m 1 f| =
        |fixedRankSum n m 1 f T / T ^ (n * (1 * degree K)) -
          mainConstant n m 1 f| := by rw [hexponent]
    _ = |finiteRowMatrixRankNormalizedSum
          (boundedRowSpaces (K := K) (n := n) (m := m) (k := 1) Csup T)
          f T - mainConstant n m 1 f| := by rw [hnormalized]
    _ ≤ C_error * T⁻¹ * Real.log T := by
      simpa [C_error, mul_assoc] using hfinite_log

/- [derived consequence; paper Theorem `th:main` plus the author-approved
   exceptional-case adaptation above] Final quantified assembly.  The main
   constant and both error regimes retain the manuscript's notation and
   normalization `T^(k*n*degree K)`.  The only external arithmetic input is
   Schmidt's attributed bounded-height count, exposed as `hcount`. -/
theorem fixed_rank_count_from_assembled_estimates
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (h_dimensions : n > m ∧ m ≥ k ∧ k ≥ 1)
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    (hcount : ∀ l : ℕ, 1 ≤ l → l ≤ k → l < m →
      HasHeightCountBounds
        (rowSpaceHeight (K := K) (m := m) (k := l)) m) :
    ∃ cMain cError : ℝ, 0 < cError ∧
      cMain = mainConstant n m k f ∧
      (∀ T : ℝ, 2 ≤ T →
          |fixedRankSum n m k f T / T ^ (k * n * degree K) - cMain| ≤
            cError * T⁻¹ * Real.log T) ∧
      (¬(degree K = 1 ∧ k = 1 ∧ m = n - 1) →
        ∀ T : ℝ, 2 ≤ T →
          |fixedRankSum n m k f T / T ^ (k * n * degree K) - cMain| ≤
            cError * T⁻¹) := by
  rcases h_dimensions with ⟨hnm, hkm, hk⟩
  by_cases hexceptional : degree K = 1 ∧ k = 1 ∧ m = n - 1
  · obtain ⟨C_error, hC_error, hlog⟩ :=
      exists_fixedRank_exceptional_normalized_error_bound
        hnm hkm hk hexceptional f h_f hcount
    refine ⟨mainConstant n m k f, C_error, hC_error, rfl, hlog, ?_⟩
    intro hnonexceptional
    exact (hnonexceptional hexceptional).elim
  · obtain ⟨C_error, hC_error, hbetter⟩ :=
      exists_fixedRank_nonexceptional_normalized_error_bound
        hnm hkm hk hexceptional f h_f hcount
    let cError : ℝ := 2 * C_error
    have hcError : 0 < cError := by
      dsimp [cError]
      positivity
    refine ⟨mainConstant n m k f, cError, hcError, rfl, ?_, ?_⟩
    · intro T hTtwo
      have hscale := inv_le_two_mul_inv_mul_log_of_two_le hTtwo
      have hscale' : C_error * T⁻¹ ≤
          (2 * C_error) * (T⁻¹ * Real.log T) := by
        calc
          C_error * T⁻¹ ≤ C_error * (2 * (T⁻¹ * Real.log T)) :=
            mul_le_mul_of_nonneg_left hscale hC_error.le
          _ = (2 * C_error) * (T⁻¹ * Real.log T) := by ring
      calc
        |fixedRankSum n m k f T / T ^ (k * n * degree K) -
            mainConstant n m k f| ≤ C_error * T⁻¹ := hbetter T hTtwo
        _ ≤ (2 * C_error) * (T⁻¹ * Real.log T) := hscale'
        _ = cError * T⁻¹ * Real.log T := by
          dsimp [cError]
          ring
    · intro _hnonexceptional T hTtwo
      have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hTtwo
      calc
        |fixedRankSum n m k f T / T ^ (k * n * degree K) -
            mainConstant n m k f| ≤ C_error * T⁻¹ := hbetter T hTtwo
        _ ≤ cError * T⁻¹ := by
          apply mul_le_mul_of_nonneg_right
          · dsimp [cError]
            linarith
          · exact inv_nonneg.mpr hTpos.le

end Katznelson
