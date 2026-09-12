import Katznelson.MainTheorems

/-!
# Uniform constants in the lower-rank estimate

This module repairs the quantifier order in the lower-rank estimate used in
Lemma `le:low_rank_terms` of `papers/katznelson.tex`.  In particular, every
constant below is selected before the scale `T`.  The public estimate retains
the manuscript's literal echelon families `\mathcal F_l(T)`, its cutoff
`X = C^crude2 T^(l d)`, its ordinary Abel summation, and the named quantities
`alpha_l` and `B_l(T)`.
-/

namespace Katznelson

open Filter MeasureTheory Set
open scoped BigOperators Classical NumberField Topology

attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

/- [Lean infrastructure, paper lemma `le:low_rank_terms`, lines 1495--1633]
   Make explicit the canonical Borel structure on the manuscript's ambient
   row space.  This is the same local structure used in `MainTheorems` for the
   covolume and covering-radius bounds; it changes neither norm nor measure. -/
noncomputable local instance uniformLowerRankAmbientRowMeasurableSpace
    {K : Type*} [Field K] [NumberField K] {m : ℕ} :
    MeasurableSpace (RowVector K m) := borel (RowVector K m)

local instance uniformLowerRankAmbientRowBorelSpace
    {K : Type*} [Field K] [NumberField K] {m : ℕ} :
    @BorelSpace (RowVector K m) _
      uniformLowerRankAmbientRowMeasurableSpace := ⟨rfl⟩

/- [paper, equations `eq:ineqluaty_abel` and `eq:ineqluaty_schmidt`,
   lines 1583--1601] The manuscript's counting function
   `η(x) = ∑_{D' echelon, H(D') ≤ x} 1`.  Its codomain is `ℝ` because it is
   inserted directly into the displayed Abel integral. -/
noncomputable def η (K : Type*) [Field K] [NumberField K]
    (l m : ℕ) (x : ℝ) : ℝ :=
  (Set.ncard {D : EchelonMatrix K l m |
    rowSpaceHeight (echelonRowSpace D) ≤ x} : ℝ)

/- [derived consequence of paper Proposition `pr:trijection` and equation
   `eq:ineqluaty_schmidt`, lines 1583--1601] The literal echelon count `η`
   is exactly Schmidt's Grassmannian height count.  This is the explicit
   bridge that permits the internally verified ordinary-shell Abel estimate
   to reindex by row spaces. -/
theorem eta_eq_rowSpaceHeightBall_ncard
    {K : Type*} [Field K] [NumberField K] (l m : ℕ) (x : ℝ) :
    η K l m x =
      (Set.ncard (rowSpaceHeightBall (K := K) (m := m) (k := l) x) : ℝ) := by
  let e := echelonRowSpaceEquiv (K := K) (l := l) (m := m)
  have hncard :
      Set.ncard (e ⁻¹' rowSpaceHeightBall (K := K) (m := m) (k := l) x) =
        Set.ncard (rowSpaceHeightBall (K := K) (m := m) (k := l) x) := by
    apply Set.ncard_preimage_of_injective_subset_range e.injective
    intro V hV
    exact ⟨e.symm V, e.apply_symm_apply V⟩
  rw [show η K l m x =
    (Set.ncard (e ⁻¹'
      rowSpaceHeightBall (K := K) (m := m) (k := l) x) : ℝ) by rfl]
  exact_mod_cast hncard

/- [derived consequence of the cited Schmidt input represented by
   `HasHeightCountBounds`, for paper equation `eq:ineqluaty_schmidt`, lines
   1595--1601] Schmidt's bound is now stated in the manuscript's literal
   `η(x)` notation. -/
theorem eta_le_of_height_count
    {K : Type*} [Field K] [NumberField K] {l m : ℕ}
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := l)) m) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → η K l m x ≤ C * x ^ m := by
  obtain ⟨C, hC, hbound⟩ := hcount
  refine ⟨C, hC, ?_⟩
  intro x hx
  rw [eta_eq_rowSpaceHeightBall_ncard]
  exact (hbound x hx).2

/- [derived consequence, paper equation `eq:ineqluaty_abel` and
   `eq:inequality_semifinal`, lines 1579--1612] Uniform-in-the-cutoff form of
   the manuscript's ordinary Abel summation.  This is the same unit-shell
   argument as `heightShell_sum_Ioc_one_le_by_exponent`; only the quantifier
   order is strengthened so its coefficient is chosen before `b`. -/
set_option maxHeartbeats 1600000 in
theorem exists_uniform_heightShell_sum_Ioc_one_le_by_exponent
    {α : Type*} {H : α → ℝ} {p q : ℕ}
    (hcount : HasHeightCountBounds H p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {b : ℕ}, 1 ≤ b →
      (∑ n ∈ Finset.Ioc 1 b,
        (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q)) ≤
        if q < p then C * (b : ℝ) ^ ((p - q : ℕ) : ℝ)
        else if p = q then C * (1 + Real.log (b : ℝ))
        else C := by
  obtain ⟨C, hC, hpartial⟩ := heightShell_full_partial_sum_upper hcount
  by_cases hqp : q < p
  · have hpq : p ≠ q := by omega
    have hqple : q ≤ p := hqp.le
    have hdiff : 0 < (p : ℝ) - q := by
      exact sub_pos.mpr (by exact_mod_cast hqp)
    let D : ℝ := C * (1 + (q : ℝ) / ((p : ℝ) - q))
    have hD : 0 < D := by
      dsimp [D]
      positivity
    refine ⟨D, hD, ?_⟩
    intro b hb
    have hbR : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    have hbpos : (0 : ℝ) < (b : ℝ) := lt_of_lt_of_le zero_lt_one hbR
    have hmain := sum_Ioc_inv_pow_le_of_partial_sum
      (φ := fun n => (Set.ncard (heightShell H n) : ℝ))
      (C := C) (a := 1) (b := b) (p := p) (q := q)
      le_rfl hb hC.le (fun _ => by positivity) hpartial
    norm_num at hmain
    have hdiff_cast : (p : ℝ) - q = ((p - q : ℕ) : ℝ) := by
      rw [Nat.cast_sub hqple]
    have hendpoint_base :
        (b : ℝ) ^ p * ((b : ℝ)⁻¹ ^ q) =
          (b : ℝ) ^ ((p : ℝ) - q) := by
      rw [← Real.rpow_natCast (b : ℝ) p,
        ← Real.rpow_natCast ((b : ℝ)⁻¹) q,
        Real.inv_rpow hbpos.le, ← Real.rpow_neg hbpos.le,
        ← Real.rpow_add hbpos]
      congr 1
    have hendpoint :
        (b : ℝ) ^ p * ((b : ℝ)⁻¹ ^ q) =
          (b : ℝ) ^ ((p - q : ℕ) : ℝ) := by
      rw [hendpoint_base, hdiff_cast]
    have hIntegral := intervalIntegral_nat_power_inv_power
      (p := p) (q := q) (N := b) hb hpq
    have hIntegralBound :
        (((b : ℝ) ^ ((p - q : ℕ) : ℝ) - 1) /
          ((p : ℝ) - q)) ≤
          (b : ℝ) ^ ((p - q : ℕ) : ℝ) / ((p : ℝ) - q) := by
      apply div_le_div_of_nonneg_right _ hdiff.le
      linarith
    simp only [hqp, if_pos]
    calc
      (∑ n ∈ Finset.Ioc 1 b,
          (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q)) ≤
          C * (b : ℝ) ^ p * ((b : ℝ)⁻¹ ^ q) +
            C * (q : ℝ) *
              (∫ x in (1 : ℝ)..(b : ℝ),
                x ^ p * (x⁻¹ ^ (q + 1))) := by
        simpa only [inv_pow] using hmain
      _ = C * (b : ℝ) ^ ((p - q : ℕ) : ℝ) +
            C * (q : ℝ) *
              (((b : ℝ) ^ ((p - q : ℕ) : ℝ) - 1) /
                ((p : ℝ) - q)) := by
          rw [show C * (b : ℝ) ^ p * ((b : ℝ)⁻¹ ^ q) =
            C * ((b : ℝ) ^ p * ((b : ℝ)⁻¹ ^ q)) by ring,
            hendpoint, hIntegral, hdiff_cast]
      _ ≤ C * (b : ℝ) ^ ((p - q : ℕ) : ℝ) +
            C * (q : ℝ) *
              ((b : ℝ) ^ ((p - q : ℕ) : ℝ) / ((p : ℝ) - q)) := by
        gcongr
      _ = D * (b : ℝ) ^ ((p - q : ℕ) : ℝ) := by
        dsimp [D]
        ring
  · by_cases hpq : p = q
    · subst q
      let D : ℝ := C * (1 + (p : ℝ))
      have hD : 0 < D := by
        dsimp [D]
        positivity
      refine ⟨D, hD, ?_⟩
      intro b hb
      have hbR : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
      have hbpos : (0 : ℝ) < (b : ℝ) := lt_of_lt_of_le zero_lt_one hbR
      have hmain := sum_Ioc_inv_pow_le_of_partial_sum
        (φ := fun n => (Set.ncard (heightShell H n) : ℝ))
        (C := C) (a := 1) (b := b) (p := p) (q := p)
        le_rfl hb hC.le (fun _ => by positivity) hpartial
      norm_num at hmain
      have hIntegral := intervalIntegral_nat_power_inv_power_eq_log
        (p := p) (N := b) hb
      have hendpoint :
          (b : ℝ) ^ p * ((b : ℝ)⁻¹ ^ p) = 1 := by
        rw [← Real.rpow_natCast (b : ℝ) p,
          ← Real.rpow_natCast ((b : ℝ)⁻¹) p,
          Real.inv_rpow hbpos.le, ← Real.rpow_neg hbpos.le,
          ← Real.rpow_add hbpos]
        rw [show (p : ℝ) + -(p : ℝ) = 0 by ring, Real.rpow_zero]
      have hendpoint_C :
          C * (b : ℝ) ^ p * ((b : ℝ)⁻¹ ^ p) = C := by
        calc
          C * (b : ℝ) ^ p * ((b : ℝ)⁻¹ ^ p) =
              C * ((b : ℝ) ^ p * ((b : ℝ)⁻¹ ^ p)) := by ring
          _ = C := by rw [hendpoint]; ring
      have hlog : 0 ≤ Real.log (b : ℝ) := Real.log_nonneg hbR
      simp only [lt_irrefl, if_false, if_pos]
      calc
        (∑ n ∈ Finset.Ioc 1 b,
            (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ p)) ≤
            C * (b : ℝ) ^ p * ((b : ℝ)⁻¹ ^ p) +
              C * (p : ℝ) *
                (∫ x in (1 : ℝ)..(b : ℝ),
                  x ^ p * (x⁻¹ ^ (p + 1))) := by
          simpa only [inv_pow] using hmain
        _ = C + C * (p : ℝ) * Real.log (b : ℝ) := by
          rw [hendpoint_C, hIntegral]
        _ ≤ D * (1 + Real.log (b : ℝ)) := by
          dsimp [D]
          have hnonneg : 0 ≤ C * ((p : ℝ) + Real.log (b : ℝ)) :=
            mul_nonneg hC.le (add_nonneg (by positivity) hlog)
          nlinarith
    · have hpq' : p < q := by omega
      have hdiff : 0 < (q : ℝ) - p := by
        exact sub_pos.mpr (by exact_mod_cast hpq')
      let D : ℝ := C * (1 + (q : ℝ) / ((q : ℝ) - p))
      have hD : 0 < D := by
        dsimp [D]
        positivity
      refine ⟨D, hD, ?_⟩
      intro b hb
      have hbR : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
      have hbpos : (0 : ℝ) < (b : ℝ) := lt_of_lt_of_le zero_lt_one hbR
      have hmain := sum_Ioc_inv_pow_le_of_partial_sum
        (φ := fun n => (Set.ncard (heightShell H n) : ℝ))
        (C := C) (a := 1) (b := b) (p := p) (q := q)
        le_rfl hb hC.le (fun _ => by positivity) hpartial
      norm_num at hmain
      have hdiff_cast : (q : ℝ) - p = ((q - p : ℕ) : ℝ) := by
        rw [Nat.cast_sub hpq'.le]
      have hendpoint_base :
          (b : ℝ) ^ p * ((b : ℝ)⁻¹ ^ q) =
            (b : ℝ) ^ ((p : ℝ) - q) := by
        rw [← Real.rpow_natCast (b : ℝ) p,
          ← Real.rpow_natCast ((b : ℝ)⁻¹) q,
          Real.inv_rpow hbpos.le, ← Real.rpow_neg hbpos.le,
          ← Real.rpow_add hbpos]
        congr 1
      have hnegdiff_cast : (p : ℝ) - q = -((q - p : ℕ) : ℝ) := by
        rw [Nat.cast_sub hpq'.le]
        ring
      have hendpoint :
          (b : ℝ) ^ p * ((b : ℝ)⁻¹ ^ q) =
            (b : ℝ) ^ (-((q - p : ℕ) : ℝ)) := by
        rw [hendpoint_base, hnegdiff_cast]
      have hIntegral := intervalIntegral_nat_power_inv_power
        (p := p) (q := q) (N := b) hb (by omega)
      have hIntegralBound :
          (((b : ℝ) ^ (-((q - p : ℕ) : ℝ)) - 1) /
            ((p : ℝ) - q)) ≤ 1 / ((q : ℝ) - p) := by
        rw [hnegdiff_cast]
        calc
          ((b : ℝ) ^ (-((q - p : ℕ) : ℝ)) - 1) /
              (-((q - p : ℕ) : ℝ)) =
              (1 - (b : ℝ) ^ (-((q - p : ℕ) : ℝ))) /
                ((q - p : ℕ) : ℝ) := by ring
          _ ≤ 1 / ((q - p : ℕ) : ℝ) := by
            apply div_le_div_of_nonneg_right _ (le_of_lt (by exact_mod_cast
              (show 0 < q - p by omega)))
            exact sub_le_self 1
              (Real.rpow_nonneg (le_trans (by norm_num) hbR) _)
          _ = 1 / ((q : ℝ) - p) := by rw [hdiff_cast]
      have hIntegralBound' :
          (((b : ℝ) ^ ((p : ℝ) - q) - 1) /
            ((p : ℝ) - q)) ≤ 1 / ((q : ℝ) - p) := by
        have hpowdiff :
            (b : ℝ) ^ ((p : ℝ) - q) =
              (b : ℝ) ^ (-((q - p : ℕ) : ℝ)) := by
          rw [hnegdiff_cast]
        simpa only [hpowdiff] using hIntegralBound
      simp only [hqp, hpq, if_false]
      calc
        (∑ n ∈ Finset.Ioc 1 b,
            (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q)) ≤
            C * (b : ℝ) ^ p * ((b : ℝ)⁻¹ ^ q) +
              C * (q : ℝ) *
                (∫ x in (1 : ℝ)..(b : ℝ),
                  x ^ p * (x⁻¹ ^ (q + 1))) := by
          simpa only [inv_pow] using hmain
        _ ≤ C * 1 + C * (q : ℝ) * (1 / ((q : ℝ) - p)) := by
          rw [show C * (b : ℝ) ^ p * ((b : ℝ)⁻¹ ^ q) =
            C * ((b : ℝ) ^ p * ((b : ℝ)⁻¹ ^ q)) by ring,
            hendpoint, hIntegral]
          have hbpow_le :
              (b : ℝ) ^ (-((q - p : ℕ) : ℝ)) ≤ 1 := by
            have hnegexp : -((q - p : ℕ) : ℝ) ≤ 0 := by
              have hdiff_nat : 0 < ((q - p : ℕ) : ℝ) := by
                exact_mod_cast (show 0 < q - p by omega)
              linarith
            simpa using Real.rpow_le_rpow_of_exponent_le hbR hnegexp
          exact add_le_add
            (by simpa using mul_le_mul_of_nonneg_left hbpow_le hC.le)
            (mul_le_mul_of_nonneg_left hIntegralBound'
              (mul_nonneg hC.le (by positivity)))
        _ = D := by
          dsimp [D]
          ring

/- [derived consequence, paper equation `eq:ineqluaty_abel` and
   `eq:inequality_semifinal`, lines 1579--1612] Restore the first ordinary
   height shell in the preceding uniform Abel estimate.  This is the exact
   `1 <= H(D') <= b` range used after rounding the manuscript's cutoff `X`. -/
set_option maxHeartbeats 1200000 in
theorem exists_uniform_heightShell_sum_Icc_one_le_by_exponent
    {α : Type*} {H : α → ℝ} {p q : ℕ}
    (hcount : HasHeightCountBounds H p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {b : ℕ}, 1 ≤ b →
      (∑ n ∈ Finset.Icc 1 b,
        (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q)) ≤
        if q < p then C * (b : ℝ) ^ ((p - q : ℕ) : ℝ)
        else if p = q then C * (1 + Real.log (b : ℝ))
        else C := by
  obtain ⟨C₀, hC₀, hIoc⟩ :=
    exists_uniform_heightShell_sum_Ioc_one_le_by_exponent
      (p := p) (q := q) hcount
  obtain ⟨C₁, hC₁, hshell⟩ := heightShell_ncard_upper hcount
  let C : ℝ := C₀ + C₁ * (2 : ℝ) ^ p
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro b hb
  have hshell₁ : (Set.ncard (heightShell H 1) : ℝ) ≤
      C₁ * (2 : ℝ) ^ p := by
    simpa using (hshell (n := 1) (by omega : 1 ≤ (1 : ℕ)))
  have hsplit : Finset.Icc 1 b = insert 1 (Finset.Ioc 1 b) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
    omega
  have hsum :
      (∑ n ∈ Finset.Icc 1 b,
        (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q)) =
      (Set.ncard (heightShell H 1) : ℝ) +
        ∑ n ∈ Finset.Ioc 1 b,
          (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q) := by
    rw [hsplit, Finset.sum_insert]
    · simp
    · simp
  have hbR : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hlog : 1 ≤ 1 + Real.log (b : ℝ) := by
    linarith [Real.log_nonneg hbR]
  by_cases hqp : q < p
  · have hpow : (1 : ℝ) ≤ (b : ℝ) ^ ((p - q : ℕ) : ℝ) := by
      exact Real.one_le_rpow hbR (by positivity)
    have hIoc' :
        (∑ n ∈ Finset.Ioc 1 b,
          (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q)) ≤
          C₀ * (b : ℝ) ^ ((p - q : ℕ) : ℝ) := by
      simpa only [if_pos hqp] using hIoc hb
    simp only [if_pos hqp]
    calc
      (∑ n ∈ Finset.Icc 1 b,
          (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q)) =
          (Set.ncard (heightShell H 1) : ℝ) +
            ∑ n ∈ Finset.Ioc 1 b,
              (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q) := hsum
      _ ≤ C₁ * (2 : ℝ) ^ p +
          C₀ * (b : ℝ) ^ ((p - q : ℕ) : ℝ) :=
        add_le_add hshell₁ hIoc'
      _ ≤ (C₀ + C₁ * (2 : ℝ) ^ p) *
          (b : ℝ) ^ ((p - q : ℕ) : ℝ) := by
        have hsmall : C₁ * (2 : ℝ) ^ p ≤
            (C₁ * (2 : ℝ) ^ p) *
              (b : ℝ) ^ ((p - q : ℕ) : ℝ) := by
          calc
            C₁ * (2 : ℝ) ^ p = (C₁ * (2 : ℝ) ^ p) * 1 := by ring
            _ ≤ (C₁ * (2 : ℝ) ^ p) *
                (b : ℝ) ^ ((p - q : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_left hpow (by positivity)
        calc
          C₁ * (2 : ℝ) ^ p + C₀ * (b : ℝ) ^ ((p - q : ℕ) : ℝ) ≤
              (C₁ * (2 : ℝ) ^ p) * (b : ℝ) ^ ((p - q : ℕ) : ℝ) +
                C₀ * (b : ℝ) ^ ((p - q : ℕ) : ℝ) :=
            add_le_add hsmall le_rfl
          _ = (C₀ + C₁ * (2 : ℝ) ^ p) *
              (b : ℝ) ^ ((p - q : ℕ) : ℝ) := by ring
      _ = C * (b : ℝ) ^ ((p - q : ℕ) : ℝ) := by rfl
  · by_cases hpq : p = q
    · have hIoc' :
          (∑ n ∈ Finset.Ioc 1 b,
            (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q)) ≤
            C₀ * (1 + Real.log (b : ℝ)) := by
        simpa only [if_neg hqp, if_pos hpq] using hIoc hb
      simp only [if_neg hqp, if_pos hpq]
      calc
        (∑ n ∈ Finset.Icc 1 b,
            (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q)) =
            (Set.ncard (heightShell H 1) : ℝ) +
              ∑ n ∈ Finset.Ioc 1 b,
                (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q) := hsum
        _ ≤ C₁ * (2 : ℝ) ^ p + C₀ * (1 + Real.log (b : ℝ)) :=
          add_le_add hshell₁ hIoc'
        _ ≤ (C₀ + C₁ * (2 : ℝ) ^ p) *
            (1 + Real.log (b : ℝ)) := by
          have hC₁pow : 0 ≤ C₁ * (2 : ℝ) ^ p := by positivity
          nlinarith
        _ = C * (1 + Real.log (b : ℝ)) := by rfl
    · have hIoc' :
          (∑ n ∈ Finset.Ioc 1 b,
            (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q)) ≤ C₀ := by
        simpa only [if_neg hqp, if_neg hpq] using hIoc hb
      simp only [if_neg hqp, if_neg hpq]
      calc
        (∑ n ∈ Finset.Icc 1 b,
            (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q)) =
            (Set.ncard (heightShell H 1) : ℝ) +
              ∑ n ∈ Finset.Ioc 1 b,
                (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q) := hsum
        _ ≤ C₁ * (2 : ℝ) ^ p + C₀ := add_le_add hshell₁ hIoc'
        _ = C := by dsimp [C]; ring

/- [derived consequence, paper equation `eq:ineqluaty_abel`, lines
   1579--1606] Uniform finite-family form of the same ordinary-shell
   estimate.  The family and the cutoff may vary, but the Abel coefficient is
   fixed by the Schmidt input before either is introduced. -/
set_option maxHeartbeats 1600000 in
theorem exists_uniform_finite_height_inv_pow_sum_le_by_exponent
    {α : Type*} {H : α → ℝ} {p q : ℕ}
    (hcount : HasHeightCountBounds H p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {b : ℕ}, 1 ≤ b →
      ∀ (S : Set α) (hS : S.Finite),
        (∀ x ∈ S, 1 ≤ H x) → (∀ x ∈ S, H x ≤ (b : ℝ)) →
        (∑ x ∈ hS.toFinset, (H x)⁻¹ ^ q) ≤
          if q < p then C * (b : ℝ) ^ ((p - q : ℕ) : ℝ)
          else if p = q then C * (1 + Real.log (b : ℝ))
          else C := by
  classical
  obtain ⟨C, hC, hshell⟩ :=
    exists_uniform_heightShell_sum_Icc_one_le_by_exponent hcount
  refine ⟨C, hC, ?_⟩
  intro b hb S hS hS_one hS_bound
  let I : Finset ℕ := Finset.Icc 1 b
  have hShellFin (n : ℕ) (hn : n ∈ I) : (heightShell H n).Finite := by
    apply heightShell_finite hcount
    exact (Finset.mem_Icc.mp hn).1
  have hFfin (n : ℕ) : (S ∩ heightShell H n).Finite := by
    exact hS.subset Set.inter_subset_left
  let F : ℕ → Finset α := fun n => (hFfin n).toFinset
  let U : Finset α := I.biUnion F
  have hdisj : (I : Set ℕ).PairwiseDisjoint F := by
    intro i hi j hj hne
    change Disjoint (F i) (F j)
    rw [Finset.disjoint_left]
    intro x hxi hxj
    apply Set.disjoint_left.1 (heightShell_disjoint hne)
    · exact ((hFfin i).mem_toFinset.mp hxi).2
    · exact ((hFfin j).mem_toFinset.mp hxj).2
  have hU : (U : Set α) = S := by
    ext x
    constructor
    · intro hx
      simp only [U, Finset.mem_coe, Finset.mem_biUnion] at hx
      obtain ⟨n, hn, hxn⟩ := hx
      exact ((hFfin n).mem_toFinset.mp hxn).1
    · intro hx
      obtain ⟨n, hn, hxn⟩ := exists_mem_heightShell_of_one_le (hS_one x hx)
      have hnb : n ≤ b := by
        have hnr : (n : ℝ) ≤ (b : ℝ) := hxn.1.trans (hS_bound x hx)
        exact_mod_cast hnr
      have hnI : n ∈ I := Finset.mem_Icc.2 ⟨hn, hnb⟩
      exact Finset.mem_biUnion.2 ⟨n, hnI,
        (hFfin n).mem_toFinset.2 ⟨hx, hxn⟩⟩
  have hUfin : U = hS.toFinset := by
    apply Finset.ext
    intro x
    change x ∈ (U : Set α) ↔ x ∈ hS.toFinset
    rw [hU, hS.mem_toFinset]
  have hsumU :
      (∑ x ∈ U, (H x)⁻¹ ^ q) =
        ∑ n ∈ I, ∑ x ∈ F n, (H x)⁻¹ ^ q := by
    simpa [U] using
      (Finset.sum_biUnion (s := I) (t := F) hdisj
        (f := fun x : α => (H x)⁻¹ ^ q))
  have hFsum (n : ℕ) (hn : n ∈ I) :
      (∑ x ∈ F n, (H x)⁻¹ ^ q) ≤
        (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q) := by
    have hnpos : 0 < n := lt_of_lt_of_le (by omega) (Finset.mem_Icc.mp hn).1
    have hfull := heightShell_sum_inv_pow_le (q := q) hcount hnpos
    have hsubset : F n ⊆ (hShellFin n hn).toFinset := by
      intro x hx
      exact (hShellFin n hn).mem_toFinset.2
        ((hFfin n).mem_toFinset.mp hx).2
    have hnonneg : ∀ x ∈ (hShellFin n hn).toFinset,
        x ∉ F n → 0 ≤ (H x)⁻¹ ^ q := by
      intro x hx _
      have hxn := (hShellFin n hn).mem_toFinset.mp hx
      have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
      have hHR : 0 < H x := lt_of_lt_of_le hnR hxn.1
      exact pow_nonneg (inv_nonneg.mpr hHR.le) q
    calc
      (∑ x ∈ F n, (H x)⁻¹ ^ q) ≤
          ∑ x ∈ (hShellFin n hn).toFinset, (H x)⁻¹ ^ q :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg
      _ ≤ (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q) := by
        simpa using hfull
  calc
    (∑ x ∈ hS.toFinset, (H x)⁻¹ ^ q) =
        ∑ x ∈ U, (H x)⁻¹ ^ q := by rw [hUfin]
    _ = ∑ n ∈ I, ∑ x ∈ F n, (H x)⁻¹ ^ q := hsumU
    _ ≤ ∑ n ∈ I,
        (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q) :=
      Finset.sum_le_sum (fun n hn => hFsum n hn)
    _ ≤ if q < p then C * (b : ℝ) ^ ((p - q : ℕ) : ℝ)
        else if p = q then C * (1 + Real.log (b : ℝ))
        else C := by simpa [I] using hshell hb

/- [derived consequence, paper equation `eq:ineqluaty_abel` and
   `eq:inequality_semifinal`, lines 1579--1612] Uniform version including the
   finitely many positive-height row spaces below height one.  That fixed set
   is independent of the manuscript cutoff `X`, so its contribution is
   selected before `b` and `T`. -/
set_option maxHeartbeats 1800000 in
theorem exists_uniform_finite_height_inv_pow_sum_le_by_exponent_of_pos
    {α : Type*} {H : α → ℝ} {p q : ℕ}
    (hcount : HasHeightCountBounds H p) (hHpos : ∀ x, 0 < H x) :
    ∃ C : ℝ, 0 < C ∧ ∀ {b : ℕ}, 1 ≤ b →
      ∀ (S : Set α) (hS : S.Finite),
        (∀ x ∈ S, H x ≤ (b : ℝ)) →
        (∑ x ∈ hS.toFinset, (H x)⁻¹ ^ q) ≤
          if q < p then C * (b : ℝ) ^ ((p - q : ℕ) : ℝ)
          else if p = q then C * (1 + Real.log (b : ℝ))
          else C := by
  classical
  obtain ⟨Cplus, hCplus, hplus⟩ :=
    exists_uniform_finite_height_inv_pow_sum_le_by_exponent
      (q := q) hcount
  obtain ⟨cᵤ, hcᵤ, hcut⟩ := hcount
  let L : Set α := {x | H x < 1}
  have hL : L.Finite := by
    apply (hcut 1 le_rfl).1.subset
    intro x hx
    change H x < 1 at hx
    exact hx.le
  let M : ℝ := ∑ x ∈ hL.toFinset, (H x)⁻¹ ^ q
  have hMnonneg : 0 ≤ M := by
    dsimp [M]
    exact Finset.sum_nonneg (fun x _ =>
      pow_nonneg (inv_nonneg.mpr (hHpos x).le) q)
  let C : ℝ := Cplus + M + 1
  have hC : 0 < C := by
    dsimp [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro b hb S hS hS_bound
  let Splus : Set α := S ∩ {x | 1 ≤ H x}
  let Sminus : Set α := S ∩ L
  have hSplus : Splus.Finite := hS.subset Set.inter_subset_left
  have hSminus : Sminus.Finite := hS.subset Set.inter_subset_left
  have hSplus_one : ∀ x ∈ Splus, 1 ≤ H x := fun _ hx => hx.2
  have hSplus_bound : ∀ x ∈ Splus, H x ≤ (b : ℝ) :=
    fun x hx => hS_bound x hx.1
  have hplus' := hplus hb Splus hSplus hSplus_one hSplus_bound
  have hSminus_sub : hSminus.toFinset ⊆ hL.toFinset := by
    intro x hx
    exact hL.mem_toFinset.mpr ((hSminus.mem_toFinset.mp hx).2)
  have hsplit : hS.toFinset = hSplus.toFinset ∪ hSminus.toFinset := by
    apply Finset.ext
    intro x
    constructor
    · intro hx
      have hxS : x ∈ S := hS.mem_toFinset.mp hx
      by_cases hxplus : 1 ≤ H x
      · exact Finset.mem_union_left _
          (hSplus.mem_toFinset.mpr ⟨hxS, hxplus⟩)
      · exact Finset.mem_union_right _
          (hSminus.mem_toFinset.mpr ⟨hxS, lt_of_not_ge hxplus⟩)
    · intro hx
      rcases Finset.mem_union.mp hx with hxplus | hxminus
      · exact hS.mem_toFinset.mpr ((hSplus.mem_toFinset.mp hxplus).1)
      · exact hS.mem_toFinset.mpr ((hSminus.mem_toFinset.mp hxminus).1)
  have hdisjoint : Disjoint hSplus.toFinset hSminus.toFinset := by
    rw [Finset.disjoint_left]
    intro x hxplus hxminus
    have hxlt : H x < 1 := by
      change H x < 1
      exact (hSminus.mem_toFinset.mp hxminus).2
    exact (not_lt_of_ge ((hSplus.mem_toFinset.mp hxplus).2)) hxlt
  have hminus_le :
      (∑ x ∈ hSminus.toFinset, (H x)⁻¹ ^ q) ≤ M := by
    dsimp [M]
    exact Finset.sum_le_sum_of_subset_of_nonneg hSminus_sub
      (fun x _ _ => pow_nonneg (inv_nonneg.mpr (hHpos x).le) q)
  have hbase :
      (∑ x ∈ hS.toFinset, (H x)⁻¹ ^ q) ≤
        (∑ x ∈ hSplus.toFinset, (H x)⁻¹ ^ q) + M := by
    rw [hsplit, Finset.sum_union hdisjoint]
    exact add_le_add le_rfl hminus_le
  by_cases hqp : q < p
  · simp only [if_pos hqp] at hplus' ⊢
    let F : ℝ := (b : ℝ) ^ ((p - q : ℕ) : ℝ)
    have hFone : 1 ≤ F := by
      dsimp [F]
      have hbR : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
      exact Real.one_le_rpow hbR (by positivity)
    have hCM : Cplus + M ≤ C := by dsimp [C]; linarith
    calc
      (∑ x ∈ hS.toFinset, (H x)⁻¹ ^ q) ≤
          (∑ x ∈ hSplus.toFinset, (H x)⁻¹ ^ q) + M := hbase
      _ ≤ Cplus * F + M := by
        simpa [F] using add_le_add hplus' (le_refl M)
      _ ≤ Cplus * F + M * F := by
        gcongr
        simpa using mul_le_mul_of_nonneg_left hFone hMnonneg
      _ = (Cplus + M) * F := by ring
      _ ≤ C * F := mul_le_mul_of_nonneg_right hCM (by positivity)
  · by_cases hpq : p = q
    · simp only [if_neg hqp, if_pos hpq] at hplus' ⊢
      let F : ℝ := 1 + Real.log (b : ℝ)
      have hFone : 1 ≤ F := by
        dsimp [F]
        have hbR : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
        linarith [Real.log_nonneg hbR]
      have hCM : Cplus + M ≤ C := by dsimp [C]; linarith
      calc
        (∑ x ∈ hS.toFinset, (H x)⁻¹ ^ q) ≤
            (∑ x ∈ hSplus.toFinset, (H x)⁻¹ ^ q) + M := hbase
        _ ≤ Cplus * F + M := by
          simpa [F] using add_le_add hplus' (le_refl M)
        _ ≤ Cplus * F + M * F := by
          gcongr
          simpa using mul_le_mul_of_nonneg_left hFone hMnonneg
        _ = (Cplus + M) * F := by ring
        _ ≤ C * F := mul_le_mul_of_nonneg_right hCM (by positivity)
    · simp only [if_neg hqp, if_neg hpq] at hplus' ⊢
      have hCM : Cplus + M ≤ C := by dsimp [C]; linarith
      exact hbase.trans ((add_le_add hplus' (le_refl M)).trans hCM)

/- [derived consequence, paper equation `eq:ineqluaty_abel`, lines
   1579--1606] Uniform weighted form of the preceding height estimate.  It is
   the manuscript's summation-by-parts bound applied to a summand dominated by
   `Cscale * H(D')^(-q)`; its coefficient is independent of `b`, `S`, and `T`.
-/
set_option maxHeartbeats 1800000 in
theorem exists_uniform_tsum_abs_le_finite_height_inv_pow_of_pos
    {α : Type*} {H : α → ℝ} {p q : ℕ}
    (hcount : HasHeightCountBounds H p) (hHpos : ∀ x, 0 < H x) :
    ∃ D : ℝ, 0 < D ∧ ∀ {b : ℕ}, 1 ≤ b →
      ∀ (w : α → ℝ) (S : Set α) (hS : S.Finite),
        (∀ x ∈ S, H x ≤ (b : ℝ)) →
        (∀ x ∉ S, w x = 0) →
        ∀ (Cscale : ℝ), 0 ≤ Cscale →
          (∀ x ∈ S, |w x| ≤ Cscale * (H x)⁻¹ ^ q) →
          |∑' x : α, w x| ≤
            if q < p then Cscale * D * (b : ℝ) ^ ((p - q : ℕ) : ℝ)
            else if p = q then Cscale * D * (1 + Real.log (b : ℝ))
            else Cscale * D := by
  obtain ⟨D, hD, hheight⟩ :=
    exists_uniform_finite_height_inv_pow_sum_le_by_exponent_of_pos
      (q := q) hcount hHpos
  refine ⟨D, hD, ?_⟩
  intro b hb w S hS hS_bound hzero Cscale hCscale hw
  have hzero' : ∀ x ∉ hS.toFinset, w x = 0 := by
    intro x hx
    apply hzero
    exact fun hxs => hx (hS.mem_toFinset.2 hxs)
  have hsum : (∑' x : α, w x) = ∑ x ∈ hS.toFinset, w x :=
    tsum_eq_sum hzero'
  have hsumabs :
      |∑ x ∈ hS.toFinset, w x| ≤ ∑ x ∈ hS.toFinset, |w x| := by
    simpa [Real.norm_eq_abs] using
      (norm_sum_le (s := hS.toFinset) (f := w))
  have hpoint_sum :
      (∑ x ∈ hS.toFinset, |w x|) ≤
        ∑ x ∈ hS.toFinset, Cscale * (H x)⁻¹ ^ q :=
    Finset.sum_le_sum (fun x hx => hw x (hS.mem_toFinset.1 hx))
  have hheight' := hheight hb S hS hS_bound
  have hscaled :
      Cscale * (∑ x ∈ hS.toFinset, (H x)⁻¹ ^ q) ≤
        Cscale * (if q < p then D * (b : ℝ) ^ ((p - q : ℕ) : ℝ)
          else if p = q then D * (1 + Real.log (b : ℝ)) else D) :=
    mul_le_mul_of_nonneg_left hheight' hCscale
  rw [hsum]
  calc
    |∑ x ∈ hS.toFinset, w x| ≤ ∑ x ∈ hS.toFinset, |w x| := hsumabs
    _ ≤ ∑ x ∈ hS.toFinset, Cscale * (H x)⁻¹ ^ q := hpoint_sum
    _ = Cscale * ∑ x ∈ hS.toFinset, (H x)⁻¹ ^ q := by
      rw [Finset.mul_sum]
    _ ≤ Cscale * (if q < p then D * (b : ℝ) ^ ((p - q : ℕ) : ℝ)
        else if p = q then D * (1 + Real.log (b : ℝ)) else D) := hscaled
    _ = if q < p then Cscale * D * (b : ℝ) ^ ((p - q : ℕ) : ℝ)
        else if p = q then Cscale * D * (1 + Real.log (b : ℝ))
        else Cscale * D := by
      by_cases hqp : q < p
      · simp only [if_pos hqp]
        ring
      · by_cases hpq : p = q
        · simp only [if_neg hqp, if_pos hpq]
          ring
        · simp only [if_neg hqp, if_neg hpq]

/- [derived consequence, paper `eq:ineqluaty_abel` and
   `eq:inequality_semifinal`, lines 1579--1612] Uniform rounding bridge from
   the natural shell endpoint to the paper's real cutoff
   `X = C * T^(l*d)`.  The output is the manuscript's literal `B_l(T)`, with
   one coefficient chosen before `T` and `b`. -/
set_option maxHeartbeats 1200000 in
theorem exists_uniform_B_l_bound_of_nat_shell_cutoff
    {n m k l d : ℕ} {C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 < D) (hnm : m < n) (hkm : k ≤ m)
    (hlk : l < k) :
    ∃ Ccrudenew : ℝ, 0 < Ccrudenew ∧
      ∀ {T : ℝ} {b : ℕ}, 1 ≤ T → 1 ≤ b →
        (b : ℝ) < max 1 (C * T ^ (l * d)) + 1 →
        (if n + l - k < m then
          D * (b : ℝ) ^ ((m - (n + l - k) : ℕ) : ℝ) ≤
            B_l n m k l d Ccrudenew T
        else if m = n + l - k then
          D * (1 + Real.log (b : ℝ)) ≤
            B_l n m k l d Ccrudenew T
        else D ≤ B_l n m k l d Ccrudenew T) := by
  by_cases hpos : n + l - k < m
  · have hexp : 0 < lowRankHeightExponent n m k l :=
      (lowRankHeightExponent_pos_iff hnm hkm hlk).mp hpos
    let Ccrudenew : ℝ := D * (C + 2) ^ (m - (n + l - k))
    have hCcrudenew : 0 < Ccrudenew := by
      dsimp [Ccrudenew]
      positivity
    refine ⟨Ccrudenew, hCcrudenew, ?_⟩
    intro T b hT hb hupper
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
    simp only [if_pos hpos]
    rw [B_l, if_pos hexp]
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
  · by_cases hzero : m = n + l - k
    · have hexp : lowRankHeightExponent n m k l = 0 :=
        (lowRankHeightExponent_eq_zero_iff hnm hkm hlk).mp hzero
      let L : ℝ := 1 + Real.log (C + 2) + (l * d : ℝ)
      let Ccrudenew : ℝ := D * L
      have hCtwo : 1 ≤ C + 2 := by linarith
      have hLpos : 0 < L := by
        dsimp [L]
        have hlogCtwo : 0 ≤ Real.log (C + 2) := Real.log_nonneg hCtwo
        positivity
      have hCcrudenew : 0 < Ccrudenew := mul_pos hD hLpos
      refine ⟨Ccrudenew, hCcrudenew, ?_⟩
      intro T b hT hb hupper
      have hround : 1 + Real.log (b : ℝ) ≤ L * (1 + Real.log T) := by
        simpa [L] using
          (one_add_log_nat_shell_cutoff_le_scaled
            (a := l * d) hC hT hb hupper)
      have hnotpos : ¬ 0 < lowRankHeightExponent n m k l := by omega
      simp only [if_neg hpos, if_pos hzero]
      rw [B_l, if_neg hnotpos, if_pos hexp]
      calc
        D * (1 + Real.log (b : ℝ)) ≤ D * (L * (1 + Real.log T)) :=
          mul_le_mul_of_nonneg_left hround hD.le
        _ = Ccrudenew * (1 + Real.log T) := by
          dsimp [Ccrudenew]
          ring
    · have hneg_case : m < n + l - k := by omega
      have hexp : lowRankHeightExponent n m k l < 0 :=
        (lowRankHeightExponent_neg_iff hnm hkm hlk).mp hneg_case
      have hnotpos : ¬ 0 < lowRankHeightExponent n m k l := by omega
      have hnotzero : lowRankHeightExponent n m k l ≠ 0 := by omega
      refine ⟨D, hD, ?_⟩
      intro T b hT hb hupper
      simp only [if_neg hpos, if_neg hzero]
      rw [B_l, if_neg hnotpos, if_neg hnotzero]
      simpa using (le_refl D)

/- [derived consequence, paper lemma `le:low_rank_terms`, lines 1560--1570]
   Fixed-coefficient form of the manuscript's innermost `|f|` sum.  The
   support radius and uniform bound of `f`, and hence `C₂`, are selected
   before `T` and the row space `W`; the proof is the existing intrinsic
   Voronoi-radius lattice count followed by the proved integral-row-matrix
   reindexing. -/
set_option maxHeartbeats 1600000 in
theorem Admissible.exists_uniform_integralRowMatrices_rank_sum_abs_le_of_latticeVoronoi
    {K : Type*} [Field K] [NumberField K]
    {n m l : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    (hl : 0 < l) (hn : 0 < n) (C_R : ℝ) (hC_R : 0 ≤ C_R) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ {T : ℝ}, 1 ≤ T →
      ∀ W : Grassmannian K m l,
        (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice W)) / T ≤ C_R →
        (∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule W A ∧ integralMatrixRank A = l},
          |f (T⁻¹ • embedMatrix A.1)|) ≤
          C₂ * (rowSpaceHeight W)⁻¹ ^ n * T ^ (l * n * degree K) := by
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
  intro T hT W hRadius
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hsupport : ∀ A : rowMatrixZLattice W n,
      |f (T⁻¹ • (((A : rowMatrixRealSpan W n) : M n m (K_ℝ[K]))))| ≠ 0 →
        ‖(A : rowMatrixRealSpan W n)‖ ≤ (R + 1) * T := by
    intro A hA
    have hfnonzero : f (T⁻¹ • (((A : rowMatrixRealSpan W n) :
        M n m (K_ℝ[K])))) ≠ 0 := abs_ne_zero.mp hA
    have hball := hRsupport _ hfnonzero
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hTpos] at hball
    calc
      ‖(A : rowMatrixRealSpan W n)‖ =
          T * (T⁻¹ * ‖(A : rowMatrixRealSpan W n)‖) := by
        rw [← mul_assoc, mul_inv_cancel₀ hTpos.ne', one_mul]
      _ ≤ T * R := mul_le_mul_of_nonneg_left hball hTpos.le
      _ ≤ T * (R + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hTpos.le
      _ = (R + 1) * T := by ring
  have hbound : ∀ A : rowMatrixZLattice W n,
      |(|f (T⁻¹ • (((A : rowMatrixRealSpan W n) :
        M n m (K_ℝ[K]))))|)| ≤ C := by
    intro A
    rw [abs_abs]
    exact (hC₀bound _).trans (by dsimp [C]; linarith)
  have hmatrix :=
    h_f.rowMatrix_rank_sum_abs_le_of_latticeVoronoi_radius_uniform_of_bounds
      W hl hn hT hC_R hRadius hR hsupport hC.le hbound
  calc
    (∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule W A ∧ integralMatrixRank A = l},
        |f (T⁻¹ • embedMatrix A.1)|) =
        ∑' A : {A : rowMatrixZLattice W n // rowMatrixRank W A = l},
          |f (T⁻¹ • (((A.1 : rowMatrixRealSpan W n) :
            M n m (K_ℝ[K]))))| := by
      exact (tsum_rowMatrixZLattice_rank_eq_integralRowMatrices W
        (fun x => |f x|) T).symm
    _ ≤ C * euclideanUnitBallVolume (n * (l * degree K)) *
          (R + 1 + C_R) ^ (n * (l * degree K)) *
          (rowSpaceHeight W)⁻¹ ^ n * T ^ (n * (l * degree K)) := hmatrix
    _ = C₂ * (rowSpaceHeight W)⁻¹ ^ n *
          T ^ (l * n * degree K) := by
      dsimp [C₂]
      rw [show n * (l * degree K) = l * n * degree K by ring]

/- [derived consequence, paper lemma `le:low_rank_terms`, lines 1541--1612]
   Uniform-quantifier version of the manuscript's positive rank-`l` stratum.
   It uses the same extension count `n_k(D')`, the same rank-`l` `|f|` sum,
   and the same ordinary Abel height estimate as
   `rowSpacePositiveStratum_normalized_le_of_matrix_bounds`.  Only the order
   of quantifiers is repaired: `D` is fixed by Schmidt's height-count input
   before `T`, `b`, and the finite family are introduced. -/
set_option maxHeartbeats 2400000 in
theorem exists_uniform_rowSpacePositiveStratum_normalized_le_of_bounds
    {K : Type*} [Field K] [NumberField K]
    {n m k l d : ℕ}
    (hnm : m < n) (hkm : k ≤ m) (hl : 1 ≤ l) (hlk : l < k)
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := l)) m) :
    ∃ D : ℝ, 0 < D ∧
      ∀ {T C₁ C₂ : ℝ}, 1 ≤ T →
      ∀ (B : Set (Grassmannian K m k)) {b : ℕ}, 1 ≤ b →
      ∀ (S : Set (Grassmannian K m l)), S.Finite →
        (∀ W ∈ S, rowSpaceHeight W ≤ (b : ℝ)) →
      ∀ (q : Grassmannian K m l → ℝ),
        (∀ W ∉ S, q W = 0) →
        (∀ W, 0 ≤ q W) →
        (∀ W ∈ S,
          rowSpaceExtensionCount B W ≤
            C₁ * T ^ (d * (k - l) * (m - l)) *
              (rowSpaceHeight W) ^ (k - l)) →
        (∀ W ∈ S,
          q W ≤ C₂ * (rowSpaceHeight W)⁻¹ ^ n * T ^ (l * n * d)) →
        0 ≤ C₁ → 0 ≤ C₂ →
        (∑' W : Grassmannian K m l,
          rowSpaceExtensionCount B W * q W) / T ^ (k * n * d) ≤
          if n + l - k < m then
            (C₁ * C₂ * T ^ alpha_l n m k l d) * D *
              (b : ℝ) ^ ((m - (n + l - k) : ℕ) : ℝ)
          else if m = n + l - k then
            (C₁ * C₂ * T ^ alpha_l n m k l d) * D *
              (1 + Real.log (b : ℝ))
          else (C₁ * C₂ * T ^ alpha_l n m k l d) * D := by
  obtain ⟨D, hD, hheight⟩ :=
    exists_uniform_tsum_abs_le_finite_height_inv_pow_of_pos
      (q := n + l - k) hcount (fun W => rowSpaceHeight_pos W)
  refine ⟨D, hD, ?_⟩
  intro T C₁ C₂ hT B b hb S hS hS_bound q hzero hq_nonneg hc hq hC₁ hC₂
  let c : Grassmannian K m l → ℝ := fun W => rowSpaceExtensionCount B W
  let w : Grassmannian K m l → ℝ := fun W =>
    c W * q W / T ^ (k * n * d)
  have hwzero : ∀ W ∉ S, w W = 0 := by
    intro W hW
    dsimp [w, c]
    rw [hzero W hW, mul_zero, zero_div]
  have hwpoint_zpow : ∀ W ∈ S,
      |w W| ≤ C₁ * C₂ * T ^ alpha_l n m k l d *
        (rowSpaceHeight W) ^ ((k : ℤ) - l - n) := by
    intro W hW
    dsimp [w, c]
    apply normalized_rowSpace_product_abs_le W hT (rowSpaceHeight_pos W)
      hkm hlk c q (rowSpaceExtensionCount_nonneg B W) (hc W hW) ?_
      hC₁ hC₂
    rw [abs_of_nonneg (hq_nonneg W)]
    exact hq W hW
  let Cscale : ℝ := C₁ * C₂ * T ^ alpha_l n m k l d
  have hCscale : 0 ≤ Cscale := by
    dsimp [Cscale]
    exact mul_nonneg (mul_nonneg hC₁ hC₂)
      (zpow_nonneg (by linarith) _)
  have hk_nl : k ≤ n + l := by omega
  have hqcast : ((n + l - k : ℕ) : ℤ) = (n : ℤ) + l - k := by
    rw [Nat.cast_sub hk_nl]
    push_cast
    ring
  have hexp : (k : ℤ) - l - n = -((n + l - k : ℕ) : ℤ) := by
    rw [hqcast]
    ring
  have hwpoint : ∀ W ∈ S,
      |w W| ≤ Cscale * (rowSpaceHeight W)⁻¹ ^ (n + l - k) := by
    intro W hW
    calc
      |w W| ≤ C₁ * C₂ * T ^ alpha_l n m k l d *
          (rowSpaceHeight W) ^ ((k : ℤ) - l - n) := hwpoint_zpow W hW
      _ = Cscale * (rowSpaceHeight W)⁻¹ ^ (n + l - k) := by
        rw [hexp, zpow_neg, zpow_natCast, inv_pow]
  have hbound := hheight hb w S hS hS_bound hwzero Cscale hCscale hwpoint
  have hwsupp : (Function.support w).Finite := by
    apply hS.subset
    intro W hW
    by_contra hWnot
    exact hW (hwzero W hWnot)
  have hwSummable : Summable w := summable_of_hasFiniteSupport hwsupp
  have hden : 0 < T ^ (k * n * d) := by
    exact pow_pos (lt_of_lt_of_le zero_lt_one hT) _
  have hw_nonneg : ∀ W, 0 ≤ w W := by
    intro W
    dsimp [w, c]
    exact div_nonneg
      (mul_nonneg (rowSpaceExtensionCount_nonneg B W) (hq_nonneg W)) hden.le
  have hsum_nonneg : 0 ≤ ∑' W, w W := tsum_nonneg hw_nonneg
  have hscale :
      (∑' W : Grassmannian K m l, rowSpaceExtensionCount B W * q W) =
        T ^ (k * n * d) * (∑' W, w W) := by
    calc
      (∑' W : Grassmannian K m l, rowSpaceExtensionCount B W * q W) =
          ∑' W : Grassmannian K m l, c W * q W := by rfl
      _ = ∑' W : Grassmannian K m l, T ^ (k * n * d) * w W := by
        apply tsum_congr
        intro W
        dsimp [w]
        field_simp [ne_of_gt hden]
      _ = T ^ (k * n * d) * (∑' W, w W) := hwSummable.tsum_mul_left _
  have hnormalized :
      (∑' W : Grassmannian K m l, rowSpaceExtensionCount B W * q W) /
          T ^ (k * n * d) = ∑' W, w W := by
    rw [hscale]
    field_simp [ne_of_gt hden]
  rw [hnormalized]
  simpa only [abs_of_nonneg hsum_nonneg, Cscale] using hbound

/- [derived consequence of paper lemmas `le:low_rank_induction`,
   `le:crude_early`, `co:covering_bound`, and `le:low_rank_terms`, lines
   1091--1120, 1239--1248, 1431--1480, and 1516--1615] Uniform positive
   rank-`l` estimate on the literal row-space image of `𝓕_l(T)`.  The
   displayed cutoff is `X = C^crude2 T^(l*d)`, the height sum is the paper's
   ordinary Abel sum, and the conclusion is expressed with its `alpha_l` and
   `B_l(T)`.  All three constants are fixed before `T`. -/
set_option maxHeartbeats 4000000 in
theorem exists_uniform_echelon_calF_positiveLowerStratum_le_B_l_of_raw_covering_bound
    {K : Type*} [Field K] [NumberField K]
    {n m k l : ℕ} (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    (hnm : m < n) (hkm : k ≤ m) (hl : 1 ≤ l) (hlk : l < k)
    {Csup : ℝ} (hCsup : 0 < Csup)
    (hSupport : ∀ T : ℝ, 0 < T → ∀ A : IntegralMatrix K n m,
      f (T⁻¹ • embedMatrix A) ≠ 0 → ‖embedMatrix A‖ ≤ Csup * T)
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := l)) m) :
    ∃ C₁ C₂ Ccrudenew : ℝ,
      0 < C₁ ∧ 0 < C₂ ∧ 0 < Ccrudenew ∧
      ∀ T : ℝ, 2 ≤ T →
        (∑' W : Grassmannian K m l,
          (((echelonRowSpace (K := K) ''
              calF (K := K) (l := k) (m := m) (n := n) Csup T) ∩
                {V | W.1 ≤ V.1}).ncard : ℝ) *
            (∑' A : {A : IntegralMatrix K n m //
              rowsInIntegralRowModule W A ∧ integralMatrixRank A = l},
              |f (T⁻¹ • embedMatrix A.1)|)) /
            T ^ (k * n * degree K) ≤
          C₁ * C₂ * T ^ alpha_l n m k l (degree K) *
            B_l n m k l (degree K) Ccrudenew T := by
  have hlpos : 0 < l := by omega
  have hnpos : 0 < n := by omega
  have hlm : l < m := lt_of_lt_of_le hlk hkm
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
  let C₁ : ℝ :=
    ((euclideanUnitBallVolume (m * degree K - l * degree K) *
      (ZLattice.covolume (ambientIntegralRowModule (K := K) m)
        (μHE[Module.finrank ℝ (RowVector K m)]))⁻¹) *
      (Csup + latticeCoveringRadius
        (ambientIntegralRowModule (K := K) m)) ^
          (m * degree K - l * degree K)) ^ (k - l)
  have hambientRadius : 0 ≤ latticeCoveringRadius
      (ambientIntegralRowModule (K := K) m) := latticeCoveringRadius_nonneg _
  have hC₁ : 0 < C₁ := by
    dsimp [C₁]
    apply pow_pos
    apply mul_pos
    · exact mul_pos (euclideanUnitBallVolume_pos _)
        (inv_pos.mpr
          (ZLattice.covolume_pos (ambientIntegralRowModule (K := K) m)
            (μHE[Module.finrank ℝ (RowVector K m)])))
    · exact pow_pos (by linarith [hCsup, hambientRadius]) _
  obtain ⟨C₂, hC₂, hinner⟩ :=
    Admissible.exists_uniform_integralRowMatrices_rank_sum_abs_le_of_latticeVoronoi
      (f := f) h_f hlpos hnpos C_R hC_R
  obtain ⟨D, hD, hpositive⟩ :=
    exists_uniform_rowSpacePositiveStratum_normalized_le_of_bounds
      hnm hkm hl hlk hcount
  let Ccrude : ℝ := Ccrude2 (K := K) (m := m) (k := l) Csup
  have hCcrude : 0 ≤ Ccrude := by
    dsimp [Ccrude]
    exact (Ccrude2_pos (K := K) (m := m) (k := l)
      Csup hCsup hlpos).le
  obtain ⟨Ccrudenew, hCcrudenew, hBbridge⟩ :=
    exists_uniform_B_l_bound_of_nat_shell_cutoff
      (n := n) (m := m) (k := k) (l := l) (d := degree K)
      hCcrude hD hnm hkm hlk
  refine ⟨C₁, C₂, Ccrudenew, hC₁, hC₂, hCcrudenew, ?_⟩
  intro T hTtwo
  have hT : 1 ≤ T := by linarith
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  let X : ℝ := Ccrude * T ^ (l * degree K)
  obtain ⟨b, hb, hXb, hbupper⟩ := exists_nat_shell_cutoff X
  let S : Set (Grassmannian K m l) := echelonRowSpace (K := K) ''
    calF (K := K) (l := l) (m := m) (n := n) Csup T
  let B : Set (Grassmannian K m k) := echelonRowSpace (K := K) ''
    calF (K := K) (l := k) (m := m) (n := n) Csup T
  have hS : S.Finite := by
    dsimp [S]
    exact (finite_calF (K := K) (l := l) (m := m) (n := n)
      (Csup := Csup) (T := T)).image _
  have hS_bound : ∀ W ∈ S, rowSpaceHeight W ≤ (b : ℝ) := by
    rintro W ⟨E, hE, rfl⟩
    have hcrude := echelon_mem_calF_height_le_Ccrude2
      E Csup T hlpos hE
    exact hcrude.trans (by simpa [X, Ccrude] using hXb)
  let q : Grassmannian K m l → ℝ := fun W =>
    ∑' A : {A : IntegralMatrix K n m //
      rowsInIntegralRowModule W A ∧ integralMatrixRank A = l},
      |f (T⁻¹ • embedMatrix A.1)|
  have hactive : activeRowSpaces (K := K) (k := l) (fun x => |f x|) T ⊆ S := by
    intro W hW
    simpa [S] using
      (activeRowSpaces_subset_echelon_calF_image_of_support_bound
        (K := K) (k := l) (fun x => |f x|) hTpos
        (fun A hA => hSupport T hTpos A (abs_ne_zero.mp hA)) hW)
  have hqzero : ∀ W ∉ S, q W = 0 := by
    intro W hW
    change rowSpaceRankSum W (fun x => |f x|) T = 0
    apply rowSpaceRankSum_eq_zero_of_not_mem_activeRowSpaces
    intro hWactive
    exact hW (hactive hWactive)
  have hq_nonneg : ∀ W, 0 ≤ q W := by
    intro W
    dsimp [q]
    exact tsum_nonneg (fun A => abs_nonneg _)
  have hRadius : ∀ W ∈ S,
      (Real.sqrt (n : ℝ) * latticeCoveringRadius (rowZLattice W)) / T ≤ C_R := by
    intro W hW
    exact echelon_calF_image_matrixCoveringRadius_div_le
      hlpos hTpos (by simpa [S] using hW)
  have hc : ∀ W ∈ S,
      rowSpaceExtensionCount B W ≤
        C₁ * T ^ (degree K * (k - l) * (m - l)) *
          rowSpaceHeight W ^ (k - l) := by
    intro W hW
    simpa [B, C₁] using
      (rowSpaceExtensionCount_image_calF_le_of_raw_low_rank_induction_uniform
        (k := k) hlm hCsup hT W (by simpa [S] using hW))
  have hq : ∀ W ∈ S,
      q W ≤ C₂ * (rowSpaceHeight W)⁻¹ ^ n *
        T ^ (l * n * degree K) := by
    intro W hW
    dsimp [q]
    exact hinner hT W (hRadius W hW)
  have hstratum := hpositive hT B hb S hS hS_bound q hqzero hq_nonneg
    hc hq hC₁.le hC₂.le
  have hB := hBbridge hT hb (by simpa [X] using hbupper)
  have hfactor_nonneg :
      0 ≤ C₁ * C₂ * T ^ alpha_l n m k l (degree K) := by
    exact mul_nonneg (mul_nonneg hC₁.le hC₂.le)
      (zpow_nonneg hTpos.le _)
  change
    (∑' W : Grassmannian K m l, rowSpaceExtensionCount B W * q W) /
        T ^ (k * n * degree K) ≤
      C₁ * C₂ * T ^ alpha_l n m k l (degree K) *
        B_l n m k l (degree K) Ccrudenew T
  by_cases hpos : n + l - k < m
  · have hstratum' :
        (∑' W : Grassmannian K m l, rowSpaceExtensionCount B W * q W) /
            T ^ (k * n * degree K) ≤
          (C₁ * C₂ * T ^ alpha_l n m k l (degree K)) * D *
            (b : ℝ) ^ ((m - (n + l - k) : ℕ) : ℝ) := by
      simpa only [if_pos hpos] using hstratum
    have hB' : D * (b : ℝ) ^ ((m - (n + l - k) : ℕ) : ℝ) ≤
        B_l n m k l (degree K) Ccrudenew T := by
      simpa only [if_pos hpos] using hB
    calc
      (∑' W : Grassmannian K m l, rowSpaceExtensionCount B W * q W) /
          T ^ (k * n * degree K) ≤
          (C₁ * C₂ * T ^ alpha_l n m k l (degree K)) * D *
            (b : ℝ) ^ ((m - (n + l - k) : ℕ) : ℝ) := hstratum'
      _ = (C₁ * C₂ * T ^ alpha_l n m k l (degree K)) *
          (D * (b : ℝ) ^ ((m - (n + l - k) : ℕ) : ℝ)) := by ring
      _ ≤ (C₁ * C₂ * T ^ alpha_l n m k l (degree K)) *
          B_l n m k l (degree K) Ccrudenew T :=
        mul_le_mul_of_nonneg_left hB' hfactor_nonneg
  · by_cases hzero : m = n + l - k
    · have hstratum' :
          (∑' W : Grassmannian K m l, rowSpaceExtensionCount B W * q W) /
              T ^ (k * n * degree K) ≤
            (C₁ * C₂ * T ^ alpha_l n m k l (degree K)) * D *
              (1 + Real.log (b : ℝ)) := by
        simpa only [if_neg hpos, if_pos hzero] using hstratum
      have hB' : D * (1 + Real.log (b : ℝ)) ≤
          B_l n m k l (degree K) Ccrudenew T := by
        simpa only [if_neg hpos, if_pos hzero] using hB
      calc
        (∑' W : Grassmannian K m l, rowSpaceExtensionCount B W * q W) /
            T ^ (k * n * degree K) ≤
            (C₁ * C₂ * T ^ alpha_l n m k l (degree K)) * D *
              (1 + Real.log (b : ℝ)) := hstratum'
        _ = (C₁ * C₂ * T ^ alpha_l n m k l (degree K)) *
            (D * (1 + Real.log (b : ℝ))) := by ring
        _ ≤ (C₁ * C₂ * T ^ alpha_l n m k l (degree K)) *
            B_l n m k l (degree K) Ccrudenew T :=
          mul_le_mul_of_nonneg_left hB' hfactor_nonneg
    · have hstratum' :
          (∑' W : Grassmannian K m l, rowSpaceExtensionCount B W * q W) /
              T ^ (k * n * degree K) ≤
            (C₁ * C₂ * T ^ alpha_l n m k l (degree K)) * D := by
        simpa only [if_neg hpos, if_neg hzero] using hstratum
      have hB' : D ≤ B_l n m k l (degree K) Ccrudenew T := by
        simpa only [if_neg hpos, if_neg hzero] using hB
      exact hstratum'.trans
        (mul_le_mul_of_nonneg_left hB' hfactor_nonneg)

/- [Lean infrastructure for paper lemma `le:low_rank_terms`, lines
   1614--1635] The manuscript absorbs the finitely many rank-dependent
   constants for `1 ≤ l < k` into one constant.  This is the same bookkeeping
   as `exists_uniform_B_l_point_bound`, but with its constants chosen before
   the scale `T`; the paper's `alpha_l` and `B_l(T)` are unchanged. -/
set_option maxHeartbeats 1600000 in
theorem exists_uniform_B_l_point_bound_forall
    {n m k d : ℕ} (E : ℕ → ℝ → ℝ)
    (hpoint : ∀ l ∈ Finset.Ico 1 k,
      ∃ C₁ C₂ Ccrudenew : ℝ,
        0 < C₁ ∧ 0 < C₂ ∧ 0 < Ccrudenew ∧
        ∀ T : ℝ, 2 ≤ T →
          E l T ≤ C₁ * C₂ * T ^ alpha_l n m k l d *
            B_l n m k l d Ccrudenew T) :
    ∃ C₃ Ccrudenew : ℝ, 0 < C₃ ∧ 0 < Ccrudenew ∧
      ∀ T : ℝ, 2 ≤ T → ∀ l ∈ Finset.Ico 1 k,
        E l T ≤ C₃ * T ^ alpha_l n m k l d *
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
  intro T hTtwo l hl
  have hT : 1 ≤ T := by linarith
  let lF : F := ⟨l, by simpa [F] using hl⟩
  have hcprod_nonneg : 0 ≤ c₁ lF * c₂ lF :=
    mul_nonneg (hc₁ lF).le (hc₂ lF).le
  have hcprod_sum : c₁ lF * c₂ lF ≤
      ∑ u ∈ F.attach, c₁ u * c₂ u := by
    exact Finset.single_le_sum
      (fun u _ => mul_nonneg (hc₁ u).le (hc₂ u).le) (F.mem_attach lF)
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
      B_l n m k l d Ccrudenew T := B_l_mono hc_uniform hT
  have hB_nonneg : 0 ≤ B_l n m k l d Ccrudenew T :=
    B_l_nonneg hCcrudenew.le hT
  have hproduct_nonneg : 0 ≤
      T ^ alpha_l n m k l d * B_l n m k l d Ccrudenew T :=
    mul_nonneg hTpow_nonneg hB_nonneg
  have hbound_l : E l T ≤
      c₁ lF * c₂ lF * T ^ alpha_l n m k l d *
        B_l n m k l d (c lF) T := by
    simpa [lF] using hbound lF T hTtwo
  calc
    E l T ≤ c₁ lF * c₂ lF * T ^ alpha_l n m k l d *
        B_l n m k l d (c lF) T := hbound_l
    _ = (c₁ lF * c₂ lF) *
        (T ^ alpha_l n m k l d * B_l n m k l d (c lF) T) := by ring
    _ ≤ (c₁ lF * c₂ lF) *
        (T ^ alpha_l n m k l d * B_l n m k l d Ccrudenew T) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hBmono hTpow_nonneg) hcprod_nonneg
    _ ≤ C₃ *
        (T ^ alpha_l n m k l d * B_l n m k l d Ccrudenew T) :=
      mul_le_mul_of_nonneg_right hcprod_uniform hproduct_nonneg
    _ = C₃ * T ^ alpha_l n m k l d *
        B_l n m k l d Ccrudenew T := by ring

/- [derived consequence of paper lemma `le:crude_early` and corollary
   `co:counting_matrices`, lines 1091--1129] The Schmidt upper-count
   coefficient and the manuscript's crude-height coefficient are fixed before
   `T`.  The counted family is exactly the row-space image of `𝓕_k(T)`,
   which is equal to the manuscript echelon family by the proved injective
   echelon/Grassmannian correspondence. -/
set_option maxHeartbeats 1200000 in
theorem exists_uniform_echelonCalF_rowSpace_image_ncard_le_of_proved_crude_height
    {K : Type*} [Field K] [NumberField K]
    {n m k : ℕ} {Csup : ℝ}
    (hcount : HasHeightCountBounds
      (rowSpaceHeight (K := K) (m := m) (k := k)) m)
    (hk : 0 < k) :
    ∃ Csize : ℝ, 0 < Csize ∧ ∀ T : ℝ, 1 ≤ T →
      ((echelonRowSpace (K := K) ''
        calF (K := K) (l := k) (m := m) (n := n) Csup T).ncard : ℝ) ≤
        Csize * T ^ (k * m * degree K) := by
  obtain ⟨cᵤ, hcᵤ, hupper⟩ :=
    heightBoundedRowSpaces_count_upper (K := K) hcount
  let Cheight : ℝ := max 1 (Ccrude2 (K := K) (m := m) (k := k) Csup)
  have hCheight : 1 ≤ Cheight := by
    dsimp [Cheight]
    exact le_max_left _ _
  let Csize : ℝ := cᵤ * Cheight ^ m
  have hCsize : 0 < Csize := by
    dsimp [Csize]
    positivity
  refine ⟨Csize, hCsize, ?_⟩
  intro T hT
  let B : Set (Grassmannian K m k) := echelonRowSpace (K := K) ''
    calF (K := K) (l := k) (m := m) (n := n) Csup T
  let H : Set (Grassmannian K m k) :=
    heightBoundedRowSpaces (K := K) (m := m) (k := k) Cheight T
  have hHfin : H.Finite := by
    simpa [H] using heightBoundedRowSpaces_finite hcount hCheight hT
  have hsubset : B ⊆ H := by
    rintro V ⟨D, hD, rfl⟩
    change rowSpaceHeight (echelonRowSpace D) ≤
      Cheight * T ^ (k * degree K)
    have hcrude := echelon_mem_calF_height_le_Ccrude2 D Csup T hk hD
    exact hcrude.trans (mul_le_mul_of_nonneg_right (by
      dsimp [Cheight]
      exact le_max_right _ _) (pow_nonneg (by linarith) _))
  have hcard : B.ncard ≤ H.ncard := Set.ncard_le_ncard hsubset hHfin
  have hcardR : (B.ncard : ℝ) ≤ (H.ncard : ℝ) := by exact_mod_cast hcard
  have hupper' : (H.ncard : ℝ) ≤
      cᵤ * (Cheight * T ^ (k * degree K)) ^ m := hupper hCheight hT
  change (B.ncard : ℝ) ≤ Csize * T ^ (k * m * degree K)
  calc
    (B.ncard : ℝ) ≤ (H.ncard : ℝ) := hcardR
    _ ≤ cᵤ * (Cheight * T ^ (k * degree K)) ^ m := hupper'
    _ = Csize * T ^ (k * m * degree K) := by
      dsimp [Csize]
      rw [mul_pow, ← pow_mul]
      rw [show k * degree K * m = k * m * degree K by ring]
      ring

/-
SUPERSEDED PROTOTYPE: retained only as development history.  None of the
declarations in this outer comment are active or counted as formalization
coverage; the verified literal versions are in `UniformLowerRankLiteral.lean`.

/- [Lean infrastructure for paper lemma `le:low_rank_terms`, lines
   1495--1537] Rank-preserving absolute-value version of the manuscript's
   regrouping by the matrix row space.  The equivalence is the already
   proved `rowSpaceContainedRankEquiv`; admissibility is used only to prove
   absolute summability. -/
set_option maxHeartbeats 6000000 in
theorem tsum_abs_integralMatrices_in_rowSpace_eq_sum_contained_rowSpaces
    {K : Type*} [Field K] [NumberField K]
    {n m k l : ℕ} (V : Grassmannian K m k)
    (f : M n m (K_ℝ[K]) → ℝ) (h_f : Admissible f)
    {T : ℝ} (hT : 0 < T) :
    (∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V A ∧ integralMatrixRank A = l},
      |f (T⁻¹ • embedMatrix A.1)|) =
      ∑' W : {W : Grassmannian K m l // W.1 ≤ V.1},
        ∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule W.1 A ∧ integralMatrixRank A = l},
          |f (T⁻¹ • embedMatrix A.1)| := by
  let r : {A : IntegralMatrix K n m //
      rowsInIntegralRowModule V A ∧ integralMatrixRank A = l} → ℝ :=
    fun A => |f (T⁻¹ • embedMatrix A.1)|
  let e := rowSpaceContainedRankEquiv
    (n := n) (m := m) (k := k) (l := l) V
  have hs : Summable (fun A : IntegralMatrix K n m =>
      |f (T⁻¹ • embedMatrix A)|) := by
    simpa only [Real.norm_eq_abs] using
      (summable_scaled_integralMatrices f h_f hT).norm
  have hr : Summable r := hs.comp_injective Subtype.val_injective
  have hre : Summable (r ∘ e.symm) := e.symm.summable_iff.mpr hr
  calc
    (∑' A, |f (T⁻¹ • embedMatrix A.1)|) =
        ∑' WA, r (e.symm WA) := (e.symm.tsum_eq r).symm
    _ = ∑' W : {W : Grassmannian K m l // W.1 ≤ V.1},
        ∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule W.1 A ∧ integralMatrixRank A = l},
          (r ∘ e.symm) ⟨W, A⟩ := hre.tsum_sigma
    _ = ∑' W : {W : Grassmannian K m l // W.1 ≤ V.1},
        ∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule W.1 A ∧ integralMatrixRank A = l},
          |f (T⁻¹ • embedMatrix A.1)| := by
      apply tsum_congr
      intro W
      apply tsum_congr
      intro A
      have hA : (e.symm ⟨W, A⟩).1 = A.1 := by
        have h := congrArg (fun X => X.2.1) (e.apply_symm_apply ⟨W, A⟩)
        change (e.symm ⟨W, A⟩).1 = A.1 at h
        exact h
      simp [r, hA]

/-
/- [Lean infrastructure for paper lemma `le:low_rank_terms`, lines
   1495--1537] This is the proved bridge from the manuscript's literal
   termwise-absolute lower-rank sum to the positive rank strata indexed by
   their own row spaces.  It uses `rowSpaceContainedRankEquiv` and the
   finite-support Fubini lemma already proved in `MainTheorems`; no
   admissibility assertion for the auxiliary function `|f|` is assumed. -/
set_option maxHeartbeats 6000000 in
theorem finite_rowSpaceLowerAbsSum_eq_sum_containedRowSpaceCounts
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
  classical
  let q : ∀ l : Fin k, Grassmannian K m l.1 → ℝ := fun l W =>
    ∑' A : {A : IntegralMatrix K n m //
      rowsInIntegralRowModule W A ∧ integralMatrixRank A = l.1},
      |f (T⁻¹ • embedMatrix A.1)|
  have hscaledAbs : Summable (fun A : IntegralMatrix K n m =>
      |f (T⁻¹ • embedMatrix A)|) := by
    simpa only [Real.norm_eq_abs] using
      (summable_scaled_integralMatrices f h_f hT).norm
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
        exact abs_ne_zero.mp hA
      · apply Subtype.ext
        exact rowSpace_eq_of_rowsIn_of_rank W A.1 A.2.1 A.2.2
    exact hW hz
  have hperV (V : B) :
      (∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
        |f (T⁻¹ • embedMatrix A.1)|) =
        ∑ l : Fin k, ∑' W : {W : Grassmannian K m l.1 // W.1 ≤ V.1},
          q l W.1 := by
    let g : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k} → ℝ :=
      fun A => |f (T⁻¹ • embedMatrix A.1)|
    have hg : Summable g :=
      hscaledAbs.comp_injective Subtype.val_injective
    let eRank :
        (Σ l : Fin k, {A : IntegralMatrix K n m //
          rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A = l.1}) ≃
          {A : IntegralMatrix K n m //
            rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k} :=
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
    have hge : Summable (g ∘ eRank) := eRank.summable_iff.mpr hg
    calc
      (∑' A : {A : IntegralMatrix K n m //
          rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k}, g A) =
          ∑' A : Σ l : Fin k, {A : IntegralMatrix K n m //
            rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A = l.1},
            g (eRank A) := (eRank.tsum_eq g).symm
      _ = ∑' l : Fin k, ∑' A : {A : IntegralMatrix K n m //
            rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A = l.1},
            (g ∘ eRank) ⟨l, A⟩ := hge.tsum_sigma
      _ = ∑ l : Fin k, ∑' A : {A : IntegralMatrix K n m //
            rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A = l.1},
            |f (T⁻¹ • embedMatrix A.1)| := by
        rw [tsum_fintype]
        apply Finset.sum_congr rfl
        intro l hl
        apply tsum_congr
        intro A
        rfl
      _ = ∑ l : Fin k,
          ∑' W : {W : Grassmannian K m l.1 // W.1 ≤ V.1}, q l W.1 := by
        apply Finset.sum_congr rfl
        intro l hl
        simpa [q] using
          (tsum_abs_integralMatrices_in_rowSpace_eq_sum_contained_rowSpaces
            (n := n) (m := m) (k := k) (l := l.1) V.1 f h_f hT)
  calc
    (∑ V : B, ∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
        |f (T⁻¹ • embedMatrix A.1)|) =
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
              |f (T⁻¹ • embedMatrix A.1)|) := by
      apply Finset.sum_congr rfl
      intro l hl
      apply tsum_congr
      intro W
      rfl
-/

/-
/- [derived consequence, paper lemma `le:low_rank_terms`, lines
   1495--1635] Quantitative form of the preceding exact bridge.  Its left
   side is literally the manuscript's sum of the inner `|f(T⁻¹A)|` sums;
   the rank-zero term and every positive stratum retain the paper's
   normalization, `alpha_l`, and `B_l(T)`. -/
set_option maxHeartbeats 6000000 in
theorem finite_rowSpaceLowerAbsSum_normalized_le
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
    simpa [u] using finite_rowSpaceLowerAbsSum_eq_sum_containedRowSpaceCounts
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
-/

-/

/- [derived consequence, paper lemma `le:low_rank_terms` and its use in the
   proof of `th:main`, lines 1495--1635 and 1671--1683] Uniform form of the
   manuscript-required lower-rank estimate.  Its left side is the sum over
   the literal rank-`k` family of the absolute value of each lower-rank inner
   sum, not the absolute value of their aggregate.  The proof uses
   `finite_rowSpaceLowerSum_normalized_sum_abs_le`, whose positive terms are
   the `|f|` strata above.  Schmidt's theorem remains the explicit attributed
   hypotheses `hcount`; no axiom or hidden instance is introduced. -/
set_option maxHeartbeats 6000000 in
theorem exists_uniform_echelon_calF_lowerRank_normalized_sum_abs_le_of_raw_covering_bound
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
          |∑' A : {A : IntegralMatrix K n m //
            rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
            f (T⁻¹ • embedMatrix A.1)|) /
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
  have hraw := finite_rowSpaceLowerSum_normalized_sum_abs_le
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
    (∑' V : B, |∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
        f (T⁻¹ • embedMatrix A.1)|) / T ^ (k * n * degree K) ≤
      C_lower * (1 + Real.log T) *
        T ^ (-(degree K : ℤ) *
          ((n - m + k - 1 : ℕ) : ℤ))
  rw [tsum_fintype]
  change
    (∑ V : B, |∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
        f (T⁻¹ • embedMatrix A.1)|) / T ^ (k * n * degree K) ≤
      C_lower * (1 + Real.log T) *
        T ^ (-(degree K : ℤ) *
          ((n - m + k - 1 : ℕ) : ℤ))
  calc
    (∑ V : B, |∑' A : {A : IntegralMatrix K n m //
        rowsInIntegralRowModule V.1 A ∧ integralMatrixRank A < k},
        f (T⁻¹ • embedMatrix A.1)|) / T ^ (k * n * degree K) ≤
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
