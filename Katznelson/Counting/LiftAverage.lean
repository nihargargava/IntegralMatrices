import Katznelson.Counting.Support
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The finite-field expansion of the lift average

This module records the exact bridge between the finite average over lifted
codes and the reduced-column containment condition used in the paper's proof
of `th:higher_moments`.
-/

namespace Katznelson

open Set
open Filter
open scoped BigOperators Classical NumberField

attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

section

variable {K : Type*} [Field K] [NumberField K]

theorem liftCodeSum_eq_tsum_integralMatrix_indicator
    (P : PrimeIdeal K) {n m s : ℕ} (S : Code P n s)
    (f : M n m (K_ℝ[K]) → ℝ) :
    liftCodeSum P S f =
      ∑' A : IntegralMatrix K n m,
        (matricesInLift P S).indicator
          (fun A => f ((liftScale P n s)⁻¹ • embedMatrix A)) A := by
  change (∑' A : {A : IntegralMatrix K n m // A ∈ matricesInLift P S},
      (fun A : IntegralMatrix K n m =>
        f ((liftScale P n s)⁻¹ • embedMatrix A)) A) = _
  exact tsum_subtype (matricesInLift P S)
    (fun A : IntegralMatrix K n m =>
      f ((liftScale P n s)⁻¹ • embedMatrix A))

theorem liftCodeSum_eq_tsum_integralMatrix_indicator_if
    (P : PrimeIdeal K) {n m s : ℕ} (S : Code P n s)
    (f : M n m (K_ℝ[K]) → ℝ) :
    liftCodeSum P S f =
      ∑' A : IntegralMatrix K n m,
        if A ∈ matricesInLift P S then
          f ((liftScale P n s)⁻¹ • embedMatrix A)
        else 0 := by
  rw [liftCodeSum_eq_tsum_integralMatrix_indicator]
  apply tsum_congr
  intro A
  by_cases hA : A ∈ matricesInLift P S <;> simp [Set.indicator, hA]

theorem sum_code_indicator_eq_card_containingCodes_mul
    (P : PrimeIdeal K) {n m s : ℕ} (A : IntegralMatrix K n m)
    (c : ℝ) :
    (∑ S : Code P n s,
      if A ∈ matricesInLift P S then c else 0) =
        (containingCodes P (n := n) (s := s) (k := m)
          (residueColumns P A)).card * c := by
  classical
  rw [← Finset.sum_filter]
  · rw [show (Finset.univ.filter (fun S : Code P n s =>
        A ∈ matricesInLift P S)) =
      containingCodes P (n := n) (s := s) (k := m)
        (residueColumns P A) by
        ext S
        simp [containingCodes, mem_matricesInLift_iff_codeSpan_le]]
    simp [nsmul_eq_mul]

theorem liftsMoment_eq_tsum_codeContainmentProbability
    (P : PrimeIdeal K) (n m s : ℕ)
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f) :
    liftsMoment P n m s f =
      ∑' A : IntegralMatrix K n m,
        f ((liftScale P n s)⁻¹ • embedMatrix A) *
          codeContainmentProbability P n s m (residueColumns P A) := by
  classical
  let g : IntegralMatrix K n m → ℝ := fun A =>
    f ((liftScale P n s)⁻¹ • embedMatrix A)
  let F : Code P n s → IntegralMatrix K n m → ℝ := fun S A =>
    (matricesInLift P S).indicator g A
  have hg : Summable g := by
    dsimp [g]
    exact summable_scaled_integralMatrices f h_f (liftScale_pos P n s)
  have hF (S : Code P n s) : Summable (F S) := by
    exact hg.indicator (matricesInLift P S)
  have hsumF : Summable (fun A : IntegralMatrix K n m =>
      ∑ S : Code P n s, F S A) := by
    exact summable_sum (s := Finset.univ) (f := F)
      (fun S _ => hF S)
  rw [liftsMoment]
  calc
    (Fintype.card (Code P n s) : ℝ)⁻¹ *
          ∑ S : Code P n s, liftCodeSum P S f =
        (Fintype.card (Code P n s) : ℝ)⁻¹ *
          ∑ S : Code P n s, ∑' A : IntegralMatrix K n m, F S A := by
      congr 1
      apply Finset.sum_congr rfl
      intro S hS
      rw [liftCodeSum_eq_tsum_integralMatrix_indicator_if]
      rfl
    _ = (Fintype.card (Code P n s) : ℝ)⁻¹ *
          ∑' A : IntegralMatrix K n m, ∑ S : Code P n s, F S A := by
      congr 1
      symm
      exact Summable.tsum_finsetSum (s := Finset.univ)
        (fun S _ => hF S)
    _ = ∑' A : IntegralMatrix K n m,
          (Fintype.card (Code P n s) : ℝ)⁻¹ *
            (∑ S : Code P n s, F S A) := by
      exact hsumF.tsum_mul_left _ |>.symm
    _ = ∑' A : IntegralMatrix K n m,
          g A * codeContainmentProbability P n s m (residueColumns P A) := by
      apply tsum_congr
      intro A
      have hinner :
          (∑ S : Code P n s, F S A) =
            (containingCodes P (n := n) (s := s) (k := m)
              (residueColumns P A)).card * g A := by
        calc
          (∑ S : Code P n s, F S A) =
              ∑ S : Code P n s,
                if A ∈ matricesInLift P S then g A else 0 := by
            apply Finset.sum_congr rfl
            intro S hS
            by_cases hA : A ∈ matricesInLift P S <;>
              simp [F, Set.indicator, hA]
          _ = (containingCodes P (n := n) (s := s) (k := m)
              (residueColumns P A)).card * g A :=
            sum_code_indicator_eq_card_containingCodes_mul P A (g A)
      rw [hinner, codeContainmentProbability]
      dsimp [g]
      simp [div_eq_mul_inv]
      ring

/- The containment probability depends only on the span of the prescribed
   vectors.  This removes the temporary independence assumption in the
   Gaussian-binomial formula and makes the formula rank-sensitive. -/
theorem codeContainmentProbability_eq_of_finrank_codeSpan
    (P : PrimeIdeal K) {n s m r : ℕ}
    (y : Fin m → (Fin n → residueField P))
    (hr : Module.finrank (residueField P) (codeSpan P y) = r)
    (hrs : r ≤ s) (hsn : s ≤ n) :
    codeContainmentProbability P n s m y =
      ((idealNorm P : ℝ) ^ (r * (n - s)))⁻¹ *
    codeContainmentCorrection P n s r := by
  have hfin :
      Module.finrank (residueField P)
          (Submodule.span (residueField P) (Set.range y)) = r := by
    exact hr
  obtain ⟨e, he⟩ :=
    exists_linearIndependent_subfamily_of_finrank_span_eq y hfin
  have hle : codeSpan P (y ∘ e) ≤ codeSpan P y := by
    rw [codeSpan, codeSpan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span (Set.mem_range_self (e i))
  have hspanrank :
      Module.finrank (residueField P) (codeSpan P (y ∘ e)) = r := by
    rw [codeSpan, finrank_span_eq_card he]
    simp
  have hspan : codeSpan P (y ∘ e) = codeSpan P y :=
    Submodule.eq_of_le_of_finrank_eq hle (hspanrank.trans hr.symm)
  have hcodes :
      containingCodes P (n := n) (s := s) (k := r) (y ∘ e) =
        containingCodes P (n := n) (s := s) (k := m) y := by
    ext S
    simp [containingCodes, hspan]
  have hprob :
      codeContainmentProbability P n s m y =
        codeContainmentProbability P n s r (y ∘ e) := by
    simp [codeContainmentProbability, hcodes]
  rw [hprob]
  exact codeContainmentProbability_eq P (y ∘ e) he hrs hsn

theorem codeContainmentProbability_eq_of_reduceMatrixRank_eq
    (P : PrimeIdeal K) {n m s r : ℕ}
    (A : IntegralMatrix K n m)
    (hrank : matrixRank (reduceMatrix P A) = r)
    (hrs : r ≤ s) (hsn : s ≤ n) :
    codeContainmentProbability P n s m (residueColumns P A) =
      ((idealNorm P : ℝ) ^ (r * (n - s)))⁻¹ *
        codeContainmentCorrection P n s r := by
  apply codeContainmentProbability_eq_of_finrank_codeSpan P
    (residueColumns P A) (r := r) ?_ hrs hsn
  exact (reduceMatrix_rank_eq_span_finrank P A).symm.trans hrank

/- The rank-drop terms are eventually outside the compact support.  This is
   the support reduction used in the proof of `th:higher_moments`; the
   algebraic lower bound comes from `le:rankdrop`, while the positive
   exponent is exactly the paper's hypothesis
   `1 - s/n < 1/m`. -/
theorem exists_rankDrop_support_threshold
    {n m s : ℕ} (hm : 0 < m) (hmn : m ≤ n) (_hms : m ≤ s)
    (hcond : 1 - (s : ℝ) / (n : ℝ) < 1 / (m : ℝ))
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f) :
    ∃ Q : ℝ, 0 < Q ∧
      ∀ P : PrimeIdeal K, Q ≤ (idealNorm P : ℝ) →
      ∀ k : ℕ, 1 ≤ k → k ≤ m →
      ∀ A : IntegralMatrix K n m, integralMatrixRank A = k →
        matrixRank (reduceMatrix P A) < k →
          f ((liftScale P n s)⁻¹ • embedMatrix A) = 0 := by
  obtain ⟨R, hR, hsupport⟩ := h_f.exists_support_radius
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  have hd : 0 < degree K := Module.finrank_pos
  have hnd : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmd : 0 < (m : ℝ) := by exact_mod_cast hm
  have hdd : 0 < (degree K : ℝ) := by exact_mod_cast hd
  let δ : ℝ :=
    (1 / (m : ℝ) - (1 - (s : ℝ) / (n : ℝ))) / (degree K : ℝ)
  have hδ : 0 < δ := by
    dsimp [δ]
    apply div_pos
    · linarith
    · exact hdd
  have hfactor : 0 < (m.factorial : ℝ)⁻¹ := by
    positivity
  have hlim : Tendsto
      (fun q : ℝ => (m.factorial : ℝ)⁻¹ * q ^ δ) atTop atTop :=
    Tendsto.const_mul_atTop hfactor (tendsto_rpow_atTop hδ)
  obtain ⟨Q₀, hQ₀⟩ := (tendsto_atTop_atTop.mp hlim) (R + 1)
  let Q : ℝ := max Q₀ 1
  refine ⟨Q, ?_, ?_⟩
  · dsimp [Q]
    exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  · intro P hP k hk hkm A hA hdrop
    have hq : 0 < (idealNorm P : ℝ) := by
      exact lt_of_lt_of_le (by norm_num) (two_le_idealNorm_real P)
    have hqone : 1 ≤ (idealNorm P : ℝ) :=
      le_trans (le_max_right Q₀ 1) hP
    have hqbound : Q₀ ≤ (idealNorm P : ℝ) :=
      le_trans (le_max_left Q₀ 1) hP
    have hlarge : R + 1 ≤
        (m.factorial : ℝ)⁻¹ * (idealNorm P : ℝ) ^ δ := hQ₀ _ hqbound
    have hlarge' : R <
        (m.factorial : ℝ)⁻¹ * (idealNorm P : ℝ) ^ δ :=
      lt_of_lt_of_le (by linarith) hlarge
    have hk' : 0 < k := by omega
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast hk'
    have hkmcast : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hkm
    have hinv : 1 / (m : ℝ) ≤ 1 / (k : ℝ) :=
      one_div_le_one_div_of_le hkpos hkmcast
    have hexp : δ ≤
        1 / ((k : ℝ) * (degree K : ℝ)) -
          (1 - (s : ℝ) / (n : ℝ)) / (degree K : ℝ) := by
      dsimp [δ]
      calc
        (1 / (m : ℝ) - (1 - (s : ℝ) / (n : ℝ))) /
            (degree K : ℝ) ≤
            (1 / (k : ℝ) - (1 - (s : ℝ) / (n : ℝ))) /
              (degree K : ℝ) :=
          (div_le_div_iff_of_pos_right hdd).2
            (sub_le_sub_right hinv (1 - (s : ℝ) / (n : ℝ)))
        _ = 1 / ((k : ℝ) * (degree K : ℝ)) -
            (1 - (s : ℝ) / (n : ℝ)) / (degree K : ℝ) := by
          field_simp [ne_of_gt hkpos, ne_of_gt hdd]
    have hpow : (idealNorm P : ℝ) ^ δ ≤
        (idealNorm P : ℝ) ^
          (1 / ((k : ℝ) * (degree K : ℝ)) -
            (1 - (s : ℝ) / (n : ℝ)) / (degree K : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hqone hexp
    have hscaled : R <
        (m.factorial : ℝ)⁻¹ *
          (idealNorm P : ℝ) ^
            (1 / ((k : ℝ) * (degree K : ℝ)) -
              (1 - (s : ℝ) / (n : ℝ)) / (degree K : ℝ)) := by
      exact lt_of_lt_of_le hlarge'
        (mul_le_mul_of_nonneg_left hpow (le_of_lt hfactor))
    have hdropnorm := rankDrop_norm_lower_bound P hk hkm A hA hdrop
    have hscale : 0 < liftScale P n s := liftScale_pos P n s
    have hnormlower : R <
        ‖(liftScale P n s)⁻¹ • embedMatrix A‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hscale)]
      calc
        R < (m.factorial : ℝ)⁻¹ *
            (idealNorm P : ℝ) ^
              (1 / ((k : ℝ) * (degree K : ℝ)) -
                (1 - (s : ℝ) / (n : ℝ)) / (degree K : ℝ)) := hscaled
        _ = (liftScale P n s)⁻¹ *
            ((m.factorial : ℝ)⁻¹ *
              (idealNorm P : ℝ) ^ (1 / ((k : ℝ) * (degree K : ℝ)))) := by
          dsimp [liftScale]
          rw [← Real.rpow_neg hq.le]
          calc
            (m.factorial : ℝ)⁻¹ *
                (idealNorm P : ℝ) ^
                  (1 / ((k : ℝ) * (degree K : ℝ)) -
                    (1 - (s : ℝ) / (n : ℝ)) / (degree K : ℝ)) =
                (m.factorial : ℝ)⁻¹ *
                  ((idealNorm P : ℝ) ^
                      (-((1 - (s : ℝ) / (n : ℝ)) /
                        (degree K : ℝ))) *
                    (idealNorm P : ℝ) ^
                      (1 / ((k : ℝ) * (degree K : ℝ)))) := by
              rw [← Real.rpow_add hq]
              congr 2
              ring
            _ = (idealNorm P : ℝ) ^
                  (-((1 - (s : ℝ) / (n : ℝ)) /
                    (degree K : ℝ))) *
                ((m.factorial : ℝ)⁻¹ *
                  (idealNorm P : ℝ) ^
                    (1 / ((k : ℝ) * (degree K : ℝ)))) := by
              ring
        _ ≤ (liftScale P n s)⁻¹ * ‖embedMatrix A‖ := by
          exact mul_le_mul_of_nonneg_left hdropnorm (le_of_lt (inv_pos.mpr hscale))
    by_contra hnonzero
    exact (not_lt_of_ge (hsupport _ hnonzero)) hnormlower

theorem reduceMatrix_rank_eq_of_support_nonzero
    {n m s : ℕ} (hm : 0 < m) (hmn : m ≤ n) (hms : m ≤ s)
    (hcond : 1 - (s : ℝ) / (n : ℝ) < 1 / (m : ℝ))
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f) :
    ∃ Q : ℝ, 0 < Q ∧
      ∀ P : PrimeIdeal K, Q ≤ (idealNorm P : ℝ) →
      ∀ k : ℕ, 1 ≤ k → k ≤ m →
      ∀ A : IntegralMatrix K n m, integralMatrixRank A = k →
        f ((liftScale P n s)⁻¹ • embedMatrix A) ≠ 0 →
          matrixRank (reduceMatrix P A) = k := by
  obtain ⟨Q, hQ, hdrop⟩ := exists_rankDrop_support_threshold
    hm hmn hms hcond f h_f
  refine ⟨Q, hQ, fun P hP k hk hkm A hA hnonzero => ?_⟩
  have heq := reduceMatrix_rank_eq_of_not_lt P A (by
    intro hdropRank
    exact hnonzero (hdrop P hP k hk hkm A hA (by simpa [hA] using hdropRank)))
  rw [hA] at heq
  exact heq

/- Once rank-drop terms have been removed, the finite-field factor can be
   replaced pointwise by the factor indexed by the algebraic rank.  The
   zero-rank case is handled separately because the support lemma only needs
   to exclude positive-rank drops. -/
theorem weightedContainmentTerm_eq_of_large_prime
    {n m s : ℕ} (hms : m ≤ s) (hsn : s ≤ n)
    (f : M n m (K_ℝ[K]) → ℝ)
    {Q : ℝ}
    (hpres : ∀ P : PrimeIdeal K, Q ≤ (idealNorm P : ℝ) →
      ∀ k : ℕ, 1 ≤ k → k ≤ m →
      ∀ A : IntegralMatrix K n m, integralMatrixRank A = k →
        f ((liftScale P n s)⁻¹ • embedMatrix A) ≠ 0 →
          matrixRank (reduceMatrix P A) = k)
    {P : PrimeIdeal K} (hP : Q ≤ (idealNorm P : ℝ))
    (A : IntegralMatrix K n m) :
    f ((liftScale P n s)⁻¹ • embedMatrix A) *
        codeContainmentProbability P n s m (residueColumns P A) =
      f ((liftScale P n s)⁻¹ • embedMatrix A) *
        (((idealNorm P : ℝ) ^
            (integralMatrixRank A * (n - s)))⁻¹ *
          codeContainmentCorrection P n s (integralMatrixRank A)) := by
  have hq : 0 < (idealNorm P : ℝ) := by
    exact lt_of_lt_of_le (by norm_num) (two_le_idealNorm_real P)
  have hrankle : integralMatrixRank A ≤ m := by
    exact Matrix.rank_le_width (algebraicMatrix A)
  by_cases hzero : f ((liftScale P n s)⁻¹ • embedMatrix A) = 0
  · simp [hzero]
  · by_cases hrankzero : integralMatrixRank A = 0
    · have hredle : matrixRank (reduceMatrix P A) ≤ 0 := by
        simpa [hrankzero] using reduceMatrix_rank_le P A
      have hredzero : matrixRank (reduceMatrix P A) = 0 :=
        Nat.eq_zero_of_le_zero hredle
      have hprob := codeContainmentProbability_eq_of_reduceMatrixRank_eq
        P (r := 0) A hredzero (by omega) hsn
      rw [hprob]
      simp [hrankzero]
    · have hrankpos : 1 ≤ integralMatrixRank A :=
        Nat.one_le_iff_ne_zero.mpr hrankzero
      have hred : matrixRank (reduceMatrix P A) = integralMatrixRank A :=
        hpres P hP
          (integralMatrixRank A) hrankpos hrankle A rfl hzero
      have hprob := codeContainmentProbability_eq_of_reduceMatrixRank_eq
        P (r := integralMatrixRank A) A hred
          (le_trans hrankle hms) hsn
      rw [hprob]

theorem exists_liftsMoment_eq_tsum_rankWeighted
    {n m s : ℕ} (hm : 0 < m) (hmn : m ≤ n) (hms : m ≤ s)
    (hsn : s ≤ n)
    (hcond : 1 - (s : ℝ) / (n : ℝ) < 1 / (m : ℝ))
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f) :
    ∃ Q : ℝ, 0 < Q ∧
      ∀ P : PrimeIdeal K, Q ≤ (idealNorm P : ℝ) →
        liftsMoment P n m s f =
          ∑' A : IntegralMatrix K n m,
            f ((liftScale P n s)⁻¹ • embedMatrix A) *
              (((idealNorm P : ℝ) ^
                  (integralMatrixRank A * (n - s)))⁻¹ *
                codeContainmentCorrection P n s (integralMatrixRank A)) := by
  obtain ⟨Q, hQpos, hpres⟩ := reduceMatrix_rank_eq_of_support_nonzero
    hm hmn hms hcond f h_f
  refine ⟨Q, hQpos, fun P hP => ?_⟩
  rw [liftsMoment_eq_tsum_codeContainmentProbability P n m s f h_f]
  apply tsum_congr
  intro A
  by_cases hzero : f ((liftScale P n s)⁻¹ • embedMatrix A) = 0
  · simp [hzero]
  · exact weightedContainmentTerm_eq_of_large_prime hms hsn f hpres hP A

end

end Katznelson
