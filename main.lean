import Katznelson.MainTheorems
import Mathlib.Analysis.Matrix.Normed

/-!
# Katznelson formalization

This project formalizes `papers/katznelson.tex`, the checked-in source of the
preprint *Integral matrices of fixed rank over number fields* (arXiv:2510.11673).
The TeX source is authoritative; the arXiv handle is included for reference.
-/

namespace Katznelson

open scoped Classical
open scoped Topology
open Filter

/- Use the Frobenius norm for the paper's Euclidean matrix space. -/
attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

/-!
## Main counting theorem

This is Theorem `th:main` of `papers/katznelson.tex`: for an admissible
function on `M_{n × m}(K_ℝ)`, the rank-k integral-matrix sum has order
`T^(k*n*d)`, with normalized additive error bounded by `T⁻¹ log T`.
Unless `d = k = 1` and `m = n - 1`, the logarithm can be dropped.
-/
theorem fixed_rank_count
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (h_dimensions : n > m ∧ m ≥ k ∧ k ≥ 1)
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f) :
    ∃ cMain cError : ℝ, 0 < cError ∧
      cMain = mainConstant n m k f ∧
      (∀ T : ℝ, 2 ≤ T →
          |fixedRankSum n m k f T / T ^ (k * n * degree K) - cMain| ≤
            cError * T⁻¹ * Real.log T) ∧
      (¬(degree K = 1 ∧ k = 1 ∧ m = n - 1) →
        ∀ T : ℝ, 2 ≤ T →
          |fixedRankSum n m k f T / T ^ (k * n * degree K) - cMain| ≤
            cError * T⁻¹) := by
  sorry

/- The first consequence needed in the lifts argument is the genuine limit
   form of `th:main`.  The paper states an explicit `T⁻¹ log T` error; this
   lemma packages that estimate as convergence along the real scale. -/
theorem fixedRankSum_normalized_tendsto
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} (h_dimensions : n > m ∧ m ≥ k ∧ k ≥ 1)
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f) :
    Tendsto
      (fun T : ℝ => fixedRankSum n m k f T / T ^ (k * n * degree K))
      atTop (𝓝 (mainConstant n m k f)) := by
  obtain ⟨cMain, cError, hcError, hcMain, hestimate, _hbetter⟩ :=
    fixed_rank_count h_dimensions f h_f
  have hlog : Tendsto (fun T : ℝ => Real.log T / T) atTop (𝓝 0) := by
    simpa using
      (Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) 0 1 one_ne_zero)
  have herror : Tendsto
      (fun T : ℝ => cError * T⁻¹ * Real.log T) atTop (𝓝 0) := by
    have hmul : Tendsto
        (fun T : ℝ => cError * (Real.log T / T)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := cError)).mul hlog
    refine hmul.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    field_simp [ne_of_gt hT]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero'
  · exact Eventually.of_forall (fun T => norm_nonneg _)
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with T hT
    simpa [hcMain, Real.norm_eq_abs] using hestimate T hT
  · exact herror

/- Composing the fixed-rank limit with the scale from (eq:def_of_L) gives the
   form used term-by-term in the lifts proof. -/
theorem fixedRankSum_normalized_liftScale_tendsto
    {K : Type*} [Field K] [NumberField K]
    {n m k s : ℕ} (h_dimensions : n > m ∧ m ≥ k ∧ k ≥ 1)
    (hsn : s < n) (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f) :
    Tendsto
      (fun P : PrimeIdeal K =>
        fixedRankSum n m k f (liftScale P n s) /
          (liftScale P n s) ^ (k * n * degree K))
      (comap (idealNorm : PrimeIdeal K → ℕ) atTop)
      (𝓝 (mainConstant n m k f)) := by
  simpa [Function.comp_def] using
    (fixedRankSum_normalized_tendsto h_dimensions f h_f).comp
      (liftScale_tendsto_atTop hsn)

/-!
## Main lifts-of-codes theorem

This is Theorem `th:higher_moments`: for the permitted `s`, the m-th moment
over `𝓛(𝓟,s)` converges as `𝓝(𝓟) → ∞` to the echelon-matrix integral sum.
-/
theorem lifts_of_codes_convergence
    {K : Type*} [Field K] [NumberField K]
    {n m s : ℕ} (h_n : 2 ≤ n) (h_m : 1 ≤ m ∧ m < n)
    (h_s : s = n - 1 ∨ (m ≤ s ∧ s < n ∧ m * (n - s) < n))
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f) :
    tendsToAtNorm
      (fun P => liftsMoment P n m s f)
      (echelonIntegralLimit n m s f) := by
  have hmpos : 0 < m := h_m.1
  have hmnlt : m < n := h_m.2
  have hmn : m ≤ n := hmnlt.le
  have hnpos : 0 < n := lt_of_lt_of_le hmpos hmn
  have hms : m ≤ s := by
    rcases h_s with hs | hs
    · omega
    · exact hs.1
  have hsn : s ≤ n := by
    rcases h_s with hs | hs
    · omega
    · exact hs.2.1.le
  have hsnlt : s < n := by
    rcases h_s with hs | hs
    · omega
    · exact hs.2.1
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hmpos
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hmnR : (m : ℝ) < (n : ℝ) := by exact_mod_cast hmnlt
  have hcond : 1 - (s : ℝ) / (n : ℝ) < 1 / (m : ℝ) := by
    rcases h_s with hs | hs
    · subst s
      have hn1 : 1 ≤ n := by omega
      rw [Nat.cast_sub hn1]
      norm_num only [Nat.cast_one]
      have hrewrite :
          1 - ((n : ℝ) - 1) / (n : ℝ) = 1 / (n : ℝ) := by
        field_simp [ne_of_gt hnR]
        ring
      rw [hrewrite]
      exact one_div_lt_one_div_of_lt hmR hmnR
    · have hprod : (m : ℝ) * ((n - s : ℕ) : ℝ) < (n : ℝ) := by
        exact_mod_cast hs.2.2
      have hprod' : (m : ℝ) * ((n : ℝ) - (s : ℝ)) < (n : ℝ) := by
        rw [← Nat.cast_sub hsn]
        exact hprod
      apply (lt_div_iff₀ hmR).2
      calc
        (1 - (s : ℝ) / (n : ℝ)) * (m : ℝ) =
            ((m : ℝ) * ((n : ℝ) - (s : ℝ))) / (n : ℝ) := by
              field_simp [ne_of_gt hnR]
        _ < (n : ℝ) / (n : ℝ) := by
          exact div_lt_div_of_pos_right hprod' hnR
        _ = 1 := by field_simp [ne_of_gt hnR]
  obtain ⟨Q, hQpos, hidentity⟩ :=
    exists_liftsMoment_eq_sum_fixedRankScaleWeighted
      hmpos hmn hms hsn hcond f h_f
  let weighted (P : PrimeIdeal K) (j : Fin (m + 1)) : ℝ :=
    (((liftScale P n s) ^ (j.1 * n * degree K))⁻¹ *
      codeContainmentCorrection P n s j.1) *
      fixedRankSum n m j.1 f (liftScale P n s)
  let limitTerm (j : Fin (m + 1)) : ℝ :=
    Fin.cases (f 0)
      (fun i : Fin m => mainConstant n m (i.1 + 1) f) j
  have hterm : ∀ j : Fin (m + 1),
      Tendsto (fun P : PrimeIdeal K => weighted P j)
        (comap (idealNorm : PrimeIdeal K → ℕ) atTop)
        (𝓝 (limitTerm j)) := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · have hcorr := codeContainmentCorrection_tendsto_one
        (K := K) (n := n) (s := s) (k := 0) (Nat.zero_le s) hsn
      simpa [weighted, limitTerm, fixedRankSum_zero] using
        hcorr.mul_const (f 0)
    · have hik : i.1 + 1 ≤ m := by omega
      have hdim : n > m ∧ m ≥ i.1 + 1 ∧ i.1 + 1 ≥ 1 := by
        omega
      have hnorm := fixedRankSum_normalized_liftScale_tendsto
        (K := K) (n := n) (m := m) (k := i.1 + 1) (s := s)
        hdim hsnlt f h_f
      have hcorr := codeContainmentCorrection_tendsto_one
        (K := K) (n := n) (s := s) (k := i.1 + 1)
        (le_trans hik hms) hsn
      have hprod : Tendsto
          (fun P : PrimeIdeal K =>
            (fixedRankSum n m (i.1 + 1) f (liftScale P n s) /
              (liftScale P n s) ^ ((i.1 + 1) * n * degree K)) *
              codeContainmentCorrection P n s (i.1 + 1))
          (comap (idealNorm : PrimeIdeal K → ℕ) atTop)
          (𝓝 (mainConstant n m (i.1 + 1) f * 1)) :=
        hnorm.mul hcorr
      have hrewrite (P : PrimeIdeal K) :
          weighted P (Fin.succ i) =
            (fixedRankSum n m (i.1 + 1) f (liftScale P n s) /
              (liftScale P n s) ^ ((i.1 + 1) * n * degree K)) *
              codeContainmentCorrection P n s (i.1 + 1) := by
        dsimp [weighted]
        have hscale : 0 < liftScale P n s := liftScale_pos P n s
        have hpow : (liftScale P n s) ^ ((i.1 + 1) * n * degree K) ≠ 0 :=
          ne_of_gt (pow_pos hscale _)
        field_simp [hpow]
      have hweight : Tendsto
          (fun P : PrimeIdeal K => weighted P (Fin.succ i))
          (comap (idealNorm : PrimeIdeal K → ℕ) atTop)
          (𝓝 (mainConstant n m (i.1 + 1) f)) := by
        have hprod' := hprod.congr'
          (Eventually.of_forall (fun P => (hrewrite P).symm))
        simpa using hprod'
      simpa [limitTerm] using hweight
  have hsum : Tendsto
      (fun P : PrimeIdeal K => ∑ j : Fin (m + 1), weighted P j)
      (comap (idealNorm : PrimeIdeal K → ℕ) atTop)
      (𝓝 (∑ j : Fin (m + 1), limitTerm j)) := by
    simpa using
      (tendsto_finsetSum (Finset.univ : Finset (Fin (m + 1)))
        (fun j _ => hterm j))
  have hlimit : (∑ j : Fin (m + 1), limitTerm j) =
      echelonIntegralLimit n m s f := by
    rw [Fin.sum_univ_succ]
    rfl
  have hQevent : ∀ᶠ P : PrimeIdeal K in
      (comap (idealNorm : PrimeIdeal K → ℕ) atTop),
      Q ≤ (idealNorm P : ℝ) := by
    exact (idealNorm_real_tendsto_atTop (K := K)).eventually
      (eventually_ge_atTop Q)
  have hsum' : Tendsto
      (fun P : PrimeIdeal K => ∑ j : Fin (m + 1), weighted P j)
      (comap (idealNorm : PrimeIdeal K → ℕ) atTop)
      (𝓝 (echelonIntegralLimit n m s f)) := by
    rw [← hlimit]
    exact hsum
  change Tendsto (fun P : PrimeIdeal K => liftsMoment P n m s f)
    (comap (idealNorm : PrimeIdeal K → ℕ) atTop)
    (𝓝 (echelonIntegralLimit n m s f))
  exact hsum'.congr' (hQevent.mono fun P hP => by
    simpa [weighted] using (hidentity P hP).symm)

end Katznelson
