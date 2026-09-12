import Katznelson.Counting.CriticalMinima
import Katznelson.Counting.FiekerStehle
import Katznelson.MainTheorems

/-!
# The critical higher-rank minima sums

This module completes the ordinary-shell argument in the degree-one,
`n = m + 1`, `k ≥ 2` branch of `th:main` (lines 1765--1800 of the checked-in
manuscript).  The critical innermost sum is split exactly at
`C * ‖l_{k-1}‖`, as in equation `eq:two_terms`.  Its near part is bounded by
the endpoint Abel formula, while its far part uses the projection-slab count
proved in `CriticalMinima.lean` and the strict `m - 1 < m` Abel tail.  All
shells are ordinary unit norm shells; no dyadic decomposition is used.
-/

namespace Katznelson

open MeasureTheory Set
open scoped Classical NumberField

variable {K : Type*} [Field K] [NumberField K]

/- [paper, first term of equation `eq:two_terms`, lines 1774--1787] Abel
   summation over ordinary unit shells bounds the reciprocal-`m` norm sum in
   every multiplicative annulus `‖x‖ ≤ ‖y‖ ≤ c ‖x‖`, uniformly in the
   nonzero integral row `x`.  The below-unit case is a fixed finite lattice
   contribution; it is the harmless endpoint absorbed in the manuscript's
   unspecified constant. -/
set_option maxHeartbeats 2400000 in
theorem exists_ambientIntegralRowModule_critical_annulus_sum_bound
    (m : ℕ) (hm : 0 < m) (hdegree : degree K = 1)
    (c : ℝ) (hc : 1 ≤ c) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (x : ambientIntegralRowModule (K := K) m), x ≠ 0 →
      ∀ S : Finset (ambientIntegralRowModule (K := K) m),
        (∀ y ∈ S,
          ‖(x : RowVector K m)‖ ≤ ‖(y : RowVector K m)‖ ∧
          ‖(y : RowVector K m)‖ ≤ c * ‖(x : RowVector K m)‖) →
        (∑ y ∈ S, ‖(y : RowVector K m)‖⁻¹ ^ m) ≤ C := by
  classical
  obtain ⟨Cball, hCball, hpartial⟩ :=
    ambientIntegralRowModule_norm_shell_partial_sum (K := K) m
  let H : ambientIntegralRowModule (K := K) m → ℝ := fun v =>
    ‖(v : RowVector K m)‖
  have hpartial' : ∀ {N : ℕ}, 1 ≤ N →
      (∑ i ∈ Finset.Icc 0 N,
        (Set.ncard (heightShell H i) : ℝ)) ≤
        Cball * (N : ℝ) ^ m := by
    intro N hN
    simpa [H, hdegree] using hpartial hN
  let smallSet : Set (ambientIntegralRowModule (K := K) m) :=
    {v | H v ≤ 2 * c}
  have hsmallFinite : smallSet.Finite := by
    apply (lattice_ball_finite
      (ambientIntegralRowModule (K := K) m)).subset
    intro v hv
    simpa [smallSet, H] using hv
  let small : Finset (ambientIntegralRowModule (K := K) m) :=
    hsmallFinite.toFinset
  let Csmall : ℝ := ∑ v ∈ small, (H v)⁻¹ ^ m
  have hCsmall : 0 ≤ Csmall := by
    dsimp [Csmall]
    exact Finset.sum_nonneg fun v hv =>
      pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) m
  let Alog : ℝ := 2 * c
  have hAlog : 1 ≤ Alog := by
    dsimp [Alog]
    linarith
  have hlogA : 0 ≤ Real.log Alog := Real.log_nonneg hAlog
  let Clarge : ℝ := 2 * Cball + Cball * (m : ℝ) * Real.log Alog
  have hClarge : 0 < Clarge := by
    dsimp [Clarge]
    have hmnonneg : 0 ≤ (m : ℝ) := by positivity
    nlinarith [mul_nonneg (mul_nonneg hCball.le hmnonneg) hlogA]
  let Ctotal : ℝ := Csmall + Clarge + 1
  have hCtotal : 0 < Ctotal := by
    dsimp [Ctotal]
    linarith
  refine ⟨Ctotal, hCtotal, ?_⟩
  intro x hx S hS
  have hxambient : (x : RowVector K m) ≠ 0 := by
    intro hzero
    apply hx
    exact Subtype.ext hzero
  have hxpos : 0 < H x := by
    dsimp [H]
    exact norm_pos_iff.mpr hxambient
  by_cases hxsmall : H x < 2
  · have hSsub : S ⊆ small := by
      intro y hy
      apply hsmallFinite.mem_toFinset.mpr
      have hyupper : H y ≤ c * H x := by
        simpa [H] using (hS y hy).2
      have hcnonneg : 0 ≤ c := le_trans zero_le_one hc
      change H y ≤ 2 * c
      calc
        H y ≤ c * H x := hyupper
        _ ≤ c * 2 := mul_le_mul_of_nonneg_left hxsmall.le hcnonneg
        _ = 2 * c := by ring
    have hsumSmall :
        (∑ y ∈ S, (H y)⁻¹ ^ m) ≤ Csmall := by
      dsimp [Csmall]
      exact Finset.sum_le_sum_of_subset_of_nonneg hSsub
        (fun y hy hnot => pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) m)
    change (∑ y ∈ S, (H y)⁻¹ ^ m) ≤ Ctotal
    exact hsumSmall.trans (by
      dsimp [Ctotal]
      linarith [hClarge])
  · have hxlarge : 2 ≤ H x := le_of_not_gt hxsmall
    let N : ℕ := ⌊H x⌋₊
    let b : ℕ := ⌊c * H x⌋₊
    have hN : 1 ≤ N := by
      dsimp [N]
      exact (Nat.one_le_floor_iff (H x)).2 (by linarith)
    have hNpos : (0 : ℝ) < N := by
      exact_mod_cast (show 0 < N by omega)
    have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
    have hcxnonneg : 0 ≤ c * H x :=
      mul_nonneg hcpos.le hxpos.le
    have hNb : N ≤ b := by
      dsimp [N, b]
      apply Nat.floor_mono
      exact (le_mul_iff_one_le_left hxpos).2 hc
    have hbpos : (0 : ℝ) < b := by
      exact_mod_cast (lt_of_lt_of_le (show 0 < N by omega) hNb)
    have hxFloor : (N : ℝ) ≤ H x := by
      dsimp [N]
      exact Nat.floor_le hxpos.le
    have hxFloorUpper : H x < (N : ℝ) + 1 := by
      dsimp [N]
      simpa [Nat.cast_add_one] using Nat.lt_floor_add_one (H x)
    have hNstep : (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by
      have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    have hbA : (b : ℝ) ≤ Alog * (N : ℝ) := by
      have hbFloor : (b : ℝ) ≤ c * H x := by
        dsimp [b]
        exact Nat.floor_le hcxnonneg
      calc
        (b : ℝ) ≤ c * H x := hbFloor
        _ ≤ c * (2 * (N : ℝ)) :=
          mul_le_mul_of_nonneg_left (hxFloorUpper.le.trans hNstep) hcpos.le
        _ = Alog * (N : ℝ) := by
          dsimp [Alog]
          ring
    have hlogRatio : Real.log (b : ℝ) - Real.log (N : ℝ) ≤
        Real.log Alog := by
      have hApos : 0 < Alog := lt_of_lt_of_le zero_lt_one hAlog
      have hANpos : 0 < Alog * (N : ℝ) := mul_pos hApos hNpos
      have hlogle : Real.log (b : ℝ) ≤
          Real.log (Alog * (N : ℝ)) :=
        Real.log_le_log hbpos hbA
      rw [Real.log_mul hApos.ne' hNpos.ne'] at hlogle
      linarith
    let index : ambientIntegralRowModule (K := K) m → ℕ := fun y => ⌊H y⌋₊
    let I : Finset ℕ := Finset.Icc N b
    let F : ℕ → Finset (ambientIntegralRowModule (K := K) m) := fun i =>
      S.filter (fun y => y ∈ heightShell H i)
    let U : Finset (ambientIntegralRowModule (K := K) m) := I.biUnion F
    have hindexShell (y : ambientIntegralRowModule (K := K) m) :
        y ∈ heightShell H (index y) := by
      constructor
      · dsimp [index]
        exact Nat.floor_le (norm_nonneg _)
      · dsimp [index]
        simpa [Nat.cast_add_one] using Nat.lt_floor_add_one (H y)
    have hNindex (y : ambientIntegralRowModule (K := K) m) (hy : y ∈ S) :
        N ≤ index y := by
      apply Nat.floor_mono
      simpa [N, index, H] using (hS y hy).1
    have hindexb (y : ambientIntegralRowModule (K := K) m) (hy : y ∈ S) :
        index y ≤ b := by
      apply Nat.floor_mono
      simpa [b, index, H] using (hS y hy).2
    have hdisj : (I : Set ℕ).PairwiseDisjoint F := by
      intro i hi j hj hij
      change Disjoint (F i) (F j)
      rw [Finset.disjoint_left]
      intro y hyi hyj
      apply Set.disjoint_left.1 (heightShell_disjoint hij)
      · exact (Finset.mem_filter.mp hyi).2
      · exact (Finset.mem_filter.mp hyj).2
    have hU : U = S := by
      apply Finset.Subset.antisymm
      · intro y hy
        simp only [U, Finset.mem_biUnion] at hy
        obtain ⟨i, hi, hyi⟩ := hy
        exact (Finset.mem_filter.mp hyi).1
      · intro y hy
        exact Finset.mem_biUnion.mpr ⟨index y,
          Finset.mem_Icc.mpr ⟨hNindex y hy, hindexb y hy⟩,
          Finset.mem_filter.mpr ⟨hy, hindexShell y⟩⟩
    have hsumU :
        (∑ y ∈ U, (H y)⁻¹ ^ m) =
          ∑ i ∈ I, ∑ y ∈ F i, (H y)⁻¹ ^ m := by
      simpa [U] using
        (Finset.sum_biUnion (s := I) (t := F) hdisj
          (f := fun y : ambientIntegralRowModule (K := K) m =>
            (H y)⁻¹ ^ m))
    have hfinShell (i : ℕ) : (heightShell H i).Finite := by
      apply (lattice_ball_finite
        (ambientIntegralRowModule (K := K) m)).subset
      intro y hy
      simpa [H] using hy.2.le
    have hFsum (i : ℕ) (hi : i ∈ I) :
        (∑ y ∈ F i, (H y)⁻¹ ^ m) ≤
          (Set.ncard (heightShell H i) : ℝ) * ((i : ℝ)⁻¹ ^ m) := by
      have hiN : N ≤ i := (Finset.mem_Icc.mp hi).1
      have hipos : 0 < i := lt_of_lt_of_le (by omega) hiN
      have hFsub : F i ⊆ (hfinShell i).toFinset := by
        intro y hy
        exact (hfinShell i).mem_toFinset.mpr (Finset.mem_filter.mp hy).2
      have hcard : ((F i).card : ℝ) ≤
          (Set.ncard (heightShell H i) : ℝ) := by
        calc
          ((F i).card : ℝ) ≤ ((hfinShell i).toFinset.card : ℝ) := by
            exact_mod_cast Finset.card_le_card hFsub
          _ = (Set.ncard (heightShell H i) : ℝ) := by
            exact_mod_cast (Set.ncard_eq_toFinset_card
              (heightShell H i) (hfinShell i)).symm
      calc
        (∑ y ∈ F i, (H y)⁻¹ ^ m) ≤
            ∑ y ∈ F i, ((i : ℝ)⁻¹ ^ m) := by
          apply Finset.sum_le_sum
          intro y hy
          exact heightShell_inv_pow_le hipos (Finset.mem_filter.mp hy).2
        _ = ((F i).card : ℝ) * ((i : ℝ)⁻¹ ^ m) := by
          simp [Finset.sum_const]
        _ ≤ (Set.ncard (heightShell H i) : ℝ) * ((i : ℝ)⁻¹ ^ m) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
    have hphiN :
        (Set.ncard (heightShell H N) : ℝ) ≤
          Cball * (N : ℝ) ^ m := by
      calc
        (Set.ncard (heightShell H N) : ℝ) ≤
            ∑ i ∈ Finset.Icc 0 N,
              (Set.ncard (heightShell H i) : ℝ) := by
          exact Finset.single_le_sum
            (s := Finset.Icc 0 N)
            (f := fun i : ℕ => (Set.ncard (heightShell H i) : ℝ))
            (fun i hi => by positivity) (by simp)
        _ ≤ Cball * (N : ℝ) ^ m := hpartial' hN
    have htermN :
        (Set.ncard (heightShell H N) : ℝ) * ((N : ℝ)⁻¹ ^ m) ≤ Cball := by
      calc
        (Set.ncard (heightShell H N) : ℝ) * ((N : ℝ)⁻¹ ^ m) ≤
            (Cball * (N : ℝ) ^ m) * ((N : ℝ)⁻¹ ^ m) := by gcongr
        _ = Cball := by
          rw [show (Cball * (N : ℝ) ^ m) * ((N : ℝ)⁻¹ ^ m) =
            Cball * ((N : ℝ) * (N : ℝ)⁻¹) ^ m by rw [mul_pow]; ring]
          rw [mul_inv_cancel₀ hNpos.ne', one_pow, mul_one]
    have hIocRaw := sum_Ioc_inv_pow_le_of_partial_sum
      (φ := fun i : ℕ => (Set.ncard (heightShell H i) : ℝ))
      (C := Cball) (a := N) (b := b) (p := m) (q := m)
      hN hNb hCball.le (fun i => by positivity) hpartial'
    have hIntegral :
        (∫ z in (N : ℝ)..(b : ℝ),
          z ^ m * (z⁻¹ ^ (m + 1))) =
            Real.log (b : ℝ) - Real.log (N : ℝ) := by
      have hpow : ∀ z ∈ Set.uIcc (N : ℝ) (b : ℝ),
          z ^ m * (z⁻¹ ^ (m + 1)) = z⁻¹ := by
        intro z hz
        rw [Set.uIcc_of_le (by exact_mod_cast hNb)] at hz
        have hzpos : 0 < z := lt_of_lt_of_le hNpos hz.1
        rw [← Real.rpow_natCast, ← Real.rpow_natCast,
          Real.inv_rpow hzpos.le, ← Real.rpow_neg hzpos.le,
          ← Real.rpow_add hzpos]
        rw [show (m : ℝ) + -((m + 1 : ℕ) : ℝ) = -1 by
          push_cast
          ring]
        exact Real.rpow_neg_one z
      rw [intervalIntegral.integral_congr hpow]
      calc
        (∫ z in (N : ℝ)..(b : ℝ), z⁻¹) =
            Real.log ((b : ℝ) / (N : ℝ)) :=
          integral_inv_of_pos hNpos hbpos
        _ = Real.log (b : ℝ) - Real.log (N : ℝ) :=
          Real.log_div hbpos.ne' hNpos.ne'
    have hendpoint :
        (b : ℝ) ^ m * ((b : ℝ)⁻¹ ^ m) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hbpos.ne', one_pow]
    have hIoc :
        (∑ i ∈ Finset.Ioc N b,
          (Set.ncard (heightShell H i) : ℝ) * ((i : ℝ)⁻¹ ^ m)) ≤
          Cball + Cball * (m : ℝ) * Real.log Alog := by
      calc
        (∑ i ∈ Finset.Ioc N b,
          (Set.ncard (heightShell H i) : ℝ) * ((i : ℝ)⁻¹ ^ m)) ≤
            Cball * (b : ℝ) ^ m * ((b : ℝ)⁻¹ ^ m) +
              Cball * (m : ℝ) *
                (∫ z in (N : ℝ)..(b : ℝ),
                  z ^ m * (z⁻¹ ^ (m + 1))) := hIocRaw
        _ = Cball + Cball * (m : ℝ) *
              (Real.log (b : ℝ) - Real.log (N : ℝ)) := by
          rw [show Cball * (b : ℝ) ^ m * ((b : ℝ)⁻¹ ^ m) =
            Cball * ((b : ℝ) ^ m * ((b : ℝ)⁻¹ ^ m)) by ring,
            hendpoint, hIntegral]
          ring
        _ ≤ Cball + Cball * (m : ℝ) * Real.log Alog := by
          gcongr
    have hshellSum :
        (∑ i ∈ I,
          (Set.ncard (heightShell H i) : ℝ) * ((i : ℝ)⁻¹ ^ m)) ≤
          Clarge := by
      have hsplit : Finset.Icc N b = insert N (Finset.Ioc N b) := by
        ext i
        simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
        omega
      dsimp [I]
      rw [hsplit, Finset.sum_insert]
      · change
          (Set.ncard (heightShell H N) : ℝ) * ((N : ℝ)⁻¹ ^ m) +
              ∑ i ∈ Finset.Ioc N b,
                (Set.ncard (heightShell H i) : ℝ) * ((i : ℝ)⁻¹ ^ m) ≤
            Clarge
        calc
          _ ≤ Cball +
              (Cball + Cball * (m : ℝ) * Real.log Alog) :=
            add_le_add htermN hIoc
          _ = Clarge := by
            dsimp [Clarge]
            ring
      · simp
    change (∑ y ∈ S, (H y)⁻¹ ^ m) ≤ Ctotal
    calc
      (∑ y ∈ S, (H y)⁻¹ ^ m) =
          ∑ y ∈ U, (H y)⁻¹ ^ m := by rw [hU]
      _ = ∑ i ∈ I, ∑ y ∈ F i, (H y)⁻¹ ^ m := hsumU
      _ ≤ ∑ i ∈ I,
          (Set.ncard (heightShell H i) : ℝ) * ((i : ℝ)⁻¹ ^ m) :=
        Finset.sum_le_sum hFsum
      _ ≤ Clarge := hshellSum
      _ ≤ Ctotal := by
        dsimp [Ctotal]
        linarith [hCsmall]

/- [paper, second term of equation `eq:two_terms`, lines 1774--1799] The
   degree-one slab count gives cumulative exponent `m - 1`; ordinary-shell
   Abel summation against `‖y‖⁻ᵐ` therefore leaves the factor
   `‖x‖ / (c ‖x‖)`.  This theorem records the resulting bound uniformly in
   the preceding nonzero row `x`.  The finite below-unit shell is kept
   explicitly, exactly as in the other manuscript shell arguments. -/
set_option maxHeartbeats 3600000 in
theorem exists_ambientIntegralRowModule_critical_projection_slab_tail_bound
    (m : ℕ) (hm : 1 < m) (hdegree : degree K = 1)
    {delta : ℝ} (hdelta : 0 < delta)
    (hmin : ∀ v : ambientIntegralRowModule (K := K) m,
      v ≠ 0 → delta ≤ ‖(v : RowVector K m)‖)
    (c : ℝ) (hc : 1 ≤ c) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (x : ambientIntegralRowModule (K := K) m), x ≠ 0 →
      ∀ S : Finset (ambientIntegralRowModule (K := K) m),
        (∀ y ∈ S,
          c * ‖(x : RowVector K m)‖ ≤ ‖(y : RowVector K m)‖ ∧
          ‖rowAmbientProjection (K := K) (m := m)
            (x : RowVector K m) (y : RowVector K m)‖ ≤
              c * ‖(x : RowVector K m)‖) →
        (∑ y ∈ S, ‖(y : RowVector K m)‖⁻¹ ^ m) ≤ C := by
  classical
  obtain ⟨Cslab, hCslab, hslab⟩ :=
    exists_ambientIntegralRowModule_projection_slab_count_of_degree_one
      (K := K) m hm hdegree hdelta hmin c (le_trans zero_le_one hc)
  let H : ambientIntegralRowModule (K := K) m → ℝ := fun v =>
    ‖(v : RowVector K m)‖
  let smallSet : Set (ambientIntegralRowModule (K := K) m) :=
    {v | H v < 1}
  have hsmallFinite : smallSet.Finite := by
    apply (lattice_ball_finite
      (ambientIntegralRowModule (K := K) m)).subset
    intro v hv
    simpa [smallSet, H] using hv.le
  let small : Finset (ambientIntegralRowModule (K := K) m) :=
    hsmallFinite.toFinset
  let Csmall : ℝ := ∑ v ∈ small, (H v)⁻¹ ^ m
  have hCsmall : 0 ≤ Csmall := by
    dsimp [Csmall]
    exact Finset.sum_nonneg fun v hv =>
      pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) m
  let Dbase : ℝ := Cslab * (2 : ℝ) ^ (m - 1)
  have hDbase : 0 < Dbase := mul_pos hCslab (pow_pos (by positivity) _)
  let Dlarge : ℝ := 2 * Dbase * (2 + (m : ℝ))
  have hDlarge : 0 < Dlarge := by
    dsimp [Dlarge]
    positivity
  let Ctotal : ℝ := Csmall + Dlarge + 1
  have hCtotal : 0 < Ctotal := by
    dsimp [Ctotal]
    linarith
  refine ⟨Ctotal, hCtotal, ?_⟩
  intro x hx S hS
  have hxambient : (x : RowVector K m) ≠ 0 := by
    intro hzero
    apply hx
    exact Subtype.ext hzero
  have hxpos : 0 < H x := by
    dsimp [H]
    exact norm_pos_iff.mpr hxambient
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  let N : ℕ := max 1 ⌊c * H x⌋₊
  have hN : 1 ≤ N := by
    dsimp [N]
    exact le_max_left _ _
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (show 0 < N by omega)
  have hfloorN : ⌊c * H x⌋₊ ≤ N := by
    dsimp [N]
    exact le_max_right _ _
  have hcxpos : 0 < c * H x := mul_pos hcpos hxpos
  have hcxUpper : c * H x < (N : ℝ) + 1 := by
    have hfloorUpper : c * H x < ((⌊c * H x⌋₊ + 1 : ℕ) : ℝ) := by
      simpa [Nat.cast_add_one] using Nat.lt_floor_add_one (c * H x)
    have hcast : ((⌊c * H x⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast hfloorN
    rw [Nat.cast_add_one] at hfloorUpper
    linarith
  have hNstep : (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hxTwoN : H x < 2 * (N : ℝ) := by
    have hxc : H x ≤ c * H x := (le_mul_iff_one_le_left hxpos).2 hc
    exact lt_of_le_of_lt hxc (hcxUpper.trans_le hNstep)
  have hxNinv : H x * (N : ℝ)⁻¹ ≤ 2 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hNpos]
    exact hxTwoN.le
  let slabShell : ℕ → Set (ambientIntegralRowModule (K := K) m) := fun i =>
    {y | N ≤ i ∧
      ‖rowAmbientProjection (K := K) (m := m)
        (x : RowVector K m) (y : RowVector K m)‖ ≤ c * H x ∧
      y ∈ heightShell H i}
  have hslabShellFinite (i : ℕ) : (slabShell i).Finite := by
    apply (lattice_ball_finite
      (ambientIntegralRowModule (K := K) m)).subset
    intro y hy
    simpa [slabShell, H] using hy.2.2.2.le
  let phi : ℕ → ℝ := fun i => (Set.ncard (slabShell i) : ℝ)
  let Cshell : ℝ := Dbase * H x
  have hCshell : 0 < Cshell := mul_pos hDbase hxpos
  have hphi : ∀ i : ℕ, 0 ≤ phi i := fun i => by
    dsimp [phi]
    positivity
  have hpartial : ∀ {n : ℕ}, 1 ≤ n →
      (∑ i ∈ Finset.Icc 0 n, phi i) ≤
        Cshell * (n : ℝ) ^ (m - 1) := by
    intro n hn
    by_cases hnN : n < N
    · have hzero : ∀ i ∈ Finset.Icc 0 n, phi i = 0 := by
        intro i hi
        have hiN : ¬ N ≤ i :=
          not_le_of_gt (lt_of_le_of_lt (Finset.mem_Icc.mp hi).2 hnN)
        simp [phi, slabShell, hiN]
      rw [Finset.sum_eq_zero hzero]
      exact mul_nonneg hCshell.le (pow_nonneg (by positivity) _)
    · have hNn : N ≤ n := le_of_not_gt hnN
      let I : Finset ℕ := Finset.Icc N n
      let F : ℕ → Finset (ambientIntegralRowModule (K := K) m) := fun i =>
        (hslabShellFinite i).toFinset
      let U : Finset (ambientIntegralRowModule (K := K) m) := I.biUnion F
      have hdisj : (I : Set ℕ).PairwiseDisjoint F := by
        intro i hi j hj hij
        change Disjoint (F i) (F j)
        rw [Finset.disjoint_left]
        intro y hyi hyj
        apply Set.disjoint_left.1 (heightShell_disjoint hij)
        · exact (hslabShellFinite i).mem_toFinset.mp hyi |>.2.2
        · exact (hslabShellFinite j).mem_toFinset.mp hyj |>.2.2
      have hcardU : U.card = ∑ i ∈ I, (F i).card := by
        simpa [U] using Finset.card_biUnion hdisj
      have hsumRestrict :
          (∑ i ∈ Finset.Icc 0 n, phi i) = ∑ i ∈ I, phi i := by
        symm
        apply Finset.sum_subset
        · intro i hi
          exact Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp hi).2⟩
        · intro i hi hnot
          have hiN : ¬ N ≤ i := by
            intro hNi
            apply hnot
            exact Finset.mem_Icc.mpr ⟨hNi, (Finset.mem_Icc.mp hi).2⟩
          simp [phi, slabShell, hiN]
      have hsumCard : (∑ i ∈ I, phi i) = (U.card : ℝ) := by
        calc
          (∑ i ∈ I, phi i) = ∑ i ∈ I, ((F i).card : ℝ) := by
            apply Finset.sum_congr rfl
            intro i hi
            dsimp [phi, F]
            exact_mod_cast Set.ncard_eq_toFinset_card
              (slabShell i) (hslabShellFinite i)
          _ = (U.card : ℝ) := by exact_mod_cast hcardU.symm
      have hUsub : (U : Set (ambientIntegralRowModule (K := K) m)) ⊆
          {y | ‖rowAmbientProjection (K := K) (m := m)
              (x : RowVector K m) (y : RowVector K m)‖ ≤ c * H x ∧
            H y ≤ ((n + 1 : ℕ) : ℝ)} := by
        intro y hy
        simp only [U, Finset.mem_coe, Finset.mem_biUnion] at hy
        obtain ⟨i, hi, hyi⟩ := hy
        have hy' := (hslabShellFinite i).mem_toFinset.mp hyi
        refine ⟨hy'.2.1, ?_⟩
        have hin : i ≤ n := (Finset.mem_Icc.mp hi).2
        exact hy'.2.2.2.le.trans (by exact_mod_cast Nat.succ_le_succ hin)
      have hxX : ‖(x : RowVector K m)‖ ≤ ((n + 1 : ℕ) : ℝ) := by
        change H x ≤ ((n + 1 : ℕ) : ℝ)
        have hcx : H x ≤ c * H x := (le_mul_iff_one_le_left hxpos).2 hc
        have hNcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNn
        calc
          H x ≤ c * H x := hcx
          _ ≤ (N : ℝ) + 1 := hcxUpper.le
          _ ≤ (n : ℝ) + 1 := by linarith
          _ = ((n + 1 : ℕ) : ℝ) := by simp
      have htargetFinite :
          {y : ambientIntegralRowModule (K := K) m |
            ‖rowAmbientProjection (K := K) (m := m)
              (x : RowVector K m) (y : RowVector K m)‖ ≤ c * H x ∧
            H y ≤ ((n + 1 : ℕ) : ℝ)}.Finite := by
        apply (lattice_ball_finite
          (ambientIntegralRowModule (K := K) m)).subset
        intro y hy
        simpa [H] using hy.2
      have hcardLe : (U.card : ℝ) ≤
          (Set.ncard {y : ambientIntegralRowModule (K := K) m |
            ‖rowAmbientProjection (K := K) (m := m)
              (x : RowVector K m) (y : RowVector K m)‖ ≤ c * H x ∧
            H y ≤ ((n + 1 : ℕ) : ℝ)} : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard hUsub htargetFinite
      have hslabN := hslab x hx hxX
      have hcount : (U.card : ℝ) ≤
          Cslab * H x * (((n + 1 : ℕ) : ℝ) ^ (m - 1)) := by
        exact hcardLe.trans (by simpa [H] using hslabN)
      have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hnStep : ((n + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
        rw [Nat.cast_add, Nat.cast_one]
        linarith
      have hpow : (((n + 1 : ℕ) : ℝ) ^ (m - 1)) ≤
          (2 * (n : ℝ)) ^ (m - 1) :=
        pow_le_pow_left₀ (by positivity) hnStep _
      calc
        (∑ i ∈ Finset.Icc 0 n, phi i) = ∑ i ∈ I, phi i := hsumRestrict
        _ = (U.card : ℝ) := hsumCard
        _ ≤ Cslab * H x * (((n + 1 : ℕ) : ℝ) ^ (m - 1)) := hcount
        _ ≤ Cslab * H x * (2 * (n : ℝ)) ^ (m - 1) := by
          gcongr
        _ = Cshell * (n : ℝ) ^ (m - 1) := by
          dsimp [Cshell, Dbase]
          rw [mul_pow]
          ring
  let Ssmall : Finset (ambientIntegralRowModule (K := K) m) :=
    S.filter (fun y => H y < 1)
  let Slarge : Finset (ambientIntegralRowModule (K := K) m) :=
    S.filter (fun y => ¬ H y < 1)
  have hsmallSub : Ssmall ⊆ small := by
    intro y hy
    apply hsmallFinite.mem_toFinset.mpr
    exact (Finset.mem_filter.mp hy).2
  have hsmallBound : (∑ y ∈ Ssmall, (H y)⁻¹ ^ m) ≤ Csmall := by
    dsimp [Csmall]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsmallSub
      (fun y hy hnot => pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) m)
  by_cases hlargeNonempty : Slarge.Nonempty
  · let index : ambientIntegralRowModule (K := K) m → ℕ := fun y => ⌊H y⌋₊
    have hindexImage : (Slarge.image index).Nonempty :=
      hlargeNonempty.image index
    let b : ℕ := (Slarge.image index).max' hindexImage
    have hindexShell (y : ambientIntegralRowModule (K := K) m) :
        y ∈ heightShell H (index y) := by
      constructor
      · dsimp [index]
        exact Nat.floor_le (norm_nonneg _)
      · dsimp [index]
        simpa [Nat.cast_add_one] using Nat.lt_floor_add_one (H y)
    have hNindex (y : ambientIntegralRowModule (K := K) m)
        (hy : y ∈ Slarge) : N ≤ index y := by
      have hyS : y ∈ S := (Finset.mem_filter.mp hy).1
      have hyOne : 1 ≤ H y := le_of_not_gt (Finset.mem_filter.mp hy).2
      dsimp [N]
      apply max_le
      · dsimp [index]
        exact (Nat.one_le_floor_iff (H y)).2 hyOne
      · dsimp [index]
        apply Nat.floor_mono
        simpa [H] using (hS y hyS).1
    have hNb : N ≤ b := by
      obtain ⟨y, hy⟩ := hlargeNonempty
      have hyImage : index y ∈ Slarge.image index :=
        Finset.mem_image.mpr ⟨y, hy, rfl⟩
      exact (hNindex y hy).trans
        (Finset.le_max' (Slarge.image index) (index y) hyImage)
    let I : Finset ℕ := Finset.Icc N b
    let F : ℕ → Finset (ambientIntegralRowModule (K := K) m) := fun i =>
      Slarge.filter (fun y => y ∈ heightShell H i)
    let U : Finset (ambientIntegralRowModule (K := K) m) := I.biUnion F
    have hdisj : (I : Set ℕ).PairwiseDisjoint F := by
      intro i hi j hj hij
      change Disjoint (F i) (F j)
      rw [Finset.disjoint_left]
      intro y hyi hyj
      apply Set.disjoint_left.1 (heightShell_disjoint hij)
      · exact (Finset.mem_filter.mp hyi).2
      · exact (Finset.mem_filter.mp hyj).2
    have hU : U = Slarge := by
      apply Finset.Subset.antisymm
      · intro y hy
        simp only [U, Finset.mem_biUnion] at hy
        obtain ⟨i, hi, hyi⟩ := hy
        exact (Finset.mem_filter.mp hyi).1
      · intro y hy
        have hyImage : index y ∈ Slarge.image index :=
          Finset.mem_image.mpr ⟨y, hy, rfl⟩
        exact Finset.mem_biUnion.mpr ⟨index y,
          Finset.mem_Icc.mpr ⟨hNindex y hy,
            Finset.le_max' (Slarge.image index) (index y) hyImage⟩,
          Finset.mem_filter.mpr ⟨hy, hindexShell y⟩⟩
    have hsumU : (∑ y ∈ U, (H y)⁻¹ ^ m) =
        ∑ i ∈ I, ∑ y ∈ F i, (H y)⁻¹ ^ m := by
      simpa [U] using
        (Finset.sum_biUnion (s := I) (t := F) hdisj
          (f := fun y : ambientIntegralRowModule (K := K) m =>
            (H y)⁻¹ ^ m))
    have hFsum (i : ℕ) (hi : i ∈ I) :
        (∑ y ∈ F i, (H y)⁻¹ ^ m) ≤ phi i * ((i : ℝ)⁻¹ ^ m) := by
      have hiN : N ≤ i := (Finset.mem_Icc.mp hi).1
      have hipos : 0 < i := lt_of_lt_of_le (by omega) hiN
      have hFsub : F i ⊆ (hslabShellFinite i).toFinset := by
        intro y hy
        have hy' := Finset.mem_filter.mp hy
        have hyS : y ∈ S := (Finset.mem_filter.mp hy'.1).1
        apply hslabShellFinite i |>.mem_toFinset.mpr
        exact ⟨hiN, (hS y hyS).2, hy'.2⟩
      have hcard : ((F i).card : ℝ) ≤ phi i := by
        dsimp [phi]
        calc
          ((F i).card : ℝ) ≤ ((hslabShellFinite i).toFinset.card : ℝ) := by
            exact_mod_cast Finset.card_le_card hFsub
          _ = (Set.ncard (slabShell i) : ℝ) := by
            exact_mod_cast (Set.ncard_eq_toFinset_card
              (slabShell i) (hslabShellFinite i)).symm
      calc
        (∑ y ∈ F i, (H y)⁻¹ ^ m) ≤
            ∑ y ∈ F i, ((i : ℝ)⁻¹ ^ m) := by
          apply Finset.sum_le_sum
          intro y hy
          exact heightShell_inv_pow_le hipos (Finset.mem_filter.mp hy).2
        _ = ((F i).card : ℝ) * ((i : ℝ)⁻¹ ^ m) := by
          simp [Finset.sum_const]
        _ ≤ phi i * ((i : ℝ)⁻¹ ^ m) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
    have hphiN : phi N ≤ Cshell * (N : ℝ) ^ (m - 1) := by
      calc
        phi N ≤ ∑ i ∈ Finset.Icc 0 N, phi i := by
          exact Finset.single_le_sum
            (s := Finset.Icc 0 N) (f := phi)
            (fun i hi => hphi i) (by simp)
        _ ≤ Cshell * (N : ℝ) ^ (m - 1) := hpartial hN
    have htermN : phi N * ((N : ℝ)⁻¹ ^ m) ≤
        Cshell * (N : ℝ)⁻¹ := by
      calc
        phi N * ((N : ℝ)⁻¹ ^ m) ≤
            (Cshell * (N : ℝ) ^ (m - 1)) * ((N : ℝ)⁻¹ ^ m) := by
          gcongr
        _ = Cshell * (N : ℝ)⁻¹ := by
          have hmEq : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
          have hinvPow : ((N : ℝ)⁻¹ ^ m) =
              (N : ℝ)⁻¹ ^ (m - 1) * (N : ℝ)⁻¹ := by
            nth_rewrite 1 [← hmEq]
            rw [pow_add, pow_one]
          have hcancel : (N : ℝ) ^ (m - 1) * ((N : ℝ)⁻¹ ^ m) =
              (N : ℝ)⁻¹ := by
            rw [hinvPow, ← mul_assoc, ← mul_pow,
              mul_inv_cancel₀ hNpos.ne', one_pow, one_mul]
          rw [show (Cshell * (N : ℝ) ^ (m - 1)) * ((N : ℝ)⁻¹ ^ m) =
            Cshell * ((N : ℝ) ^ (m - 1) * ((N : ℝ)⁻¹ ^ m)) by ring,
            hcancel]
    have hIoc := sum_Ioc_inv_pow_tail_le_of_partial_sum
      (φ := phi) (C := Cshell) (N := N) (b := b)
      (p := m - 1) (q := m) hCshell hN hNb (by omega) hphi hpartial
    have hshellBound :
        (∑ i ∈ I, phi i * ((i : ℝ)⁻¹ ^ m)) ≤
          Cshell * (2 + (m : ℝ)) * (N : ℝ)⁻¹ := by
      have hsplit : Finset.Icc N b = insert N (Finset.Ioc N b) := by
        ext i
        simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
        omega
      dsimp [I]
      rw [hsplit, Finset.sum_insert]
      · calc
          phi N * ((N : ℝ)⁻¹ ^ m) +
              ∑ i ∈ Finset.Ioc N b, phi i * ((i : ℝ)⁻¹ ^ m) ≤
            Cshell * (N : ℝ)⁻¹ +
              Cshell * (1 + (m : ℝ) /
                ((m : ℝ) - ((m - 1 : ℕ) : ℝ))) *
                (N : ℝ) ^ (-((m - (m - 1) : ℕ) : ℝ)) :=
            add_le_add htermN hIoc
          _ = Cshell * (2 + (m : ℝ)) * (N : ℝ)⁻¹ := by
            have hmSub : m - (m - 1) = 1 := by omega
            have hcastSub : (m : ℝ) - ((m - 1 : ℕ) : ℝ) = 1 := by
              rw [Nat.cast_sub (by omega : 1 ≤ m)]
              push_cast
              ring
            rw [hmSub, hcastSub]
            rw [← Real.rpow_neg_one (N : ℝ)]
            ring
      · simp
    have hlargeBound : (∑ y ∈ Slarge, (H y)⁻¹ ^ m) ≤ Dlarge := by
      have hcore : (∑ y ∈ Slarge, (H y)⁻¹ ^ m) ≤
          Cshell * (2 + (m : ℝ)) * (N : ℝ)⁻¹ := by
        calc
          (∑ y ∈ Slarge, (H y)⁻¹ ^ m) =
              ∑ y ∈ U, (H y)⁻¹ ^ m := by rw [hU]
          _ = ∑ i ∈ I, ∑ y ∈ F i, (H y)⁻¹ ^ m := hsumU
          _ ≤ ∑ i ∈ I, phi i * ((i : ℝ)⁻¹ ^ m) :=
            Finset.sum_le_sum hFsum
          _ ≤ Cshell * (2 + (m : ℝ)) * (N : ℝ)⁻¹ := hshellBound
      calc
        (∑ y ∈ Slarge, (H y)⁻¹ ^ m) ≤
            Cshell * (2 + (m : ℝ)) * (N : ℝ)⁻¹ := hcore
        _ = Dbase * (2 + (m : ℝ)) * (H x * (N : ℝ)⁻¹) := by
          dsimp [Cshell]
          ring
        _ ≤ Dbase * (2 + (m : ℝ)) * 2 := by
          exact mul_le_mul_of_nonneg_left hxNinv
            (mul_nonneg hDbase.le (by positivity))
        _ = Dlarge := by
          dsimp [Dlarge]
          ring
    have hsplit : (∑ y ∈ S, (H y)⁻¹ ^ m) =
        (∑ y ∈ Ssmall, (H y)⁻¹ ^ m) +
          ∑ y ∈ Slarge, (H y)⁻¹ ^ m := by
      dsimp [Ssmall, Slarge]
      rw [← Finset.sum_filter_add_sum_filter_not S (fun y => H y < 1)]
    change (∑ y ∈ S, (H y)⁻¹ ^ m) ≤ Ctotal
    calc
      (∑ y ∈ S, (H y)⁻¹ ^ m) =
          (∑ y ∈ Ssmall, (H y)⁻¹ ^ m) +
            ∑ y ∈ Slarge, (H y)⁻¹ ^ m := hsplit
      _ ≤ Csmall + Dlarge := add_le_add hsmallBound hlargeBound
      _ ≤ Ctotal := by
        dsimp [Ctotal]
        linarith
  · have hlargeEmpty : Slarge = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hlargeNonempty
    have hSsmall : Ssmall = S := by
      dsimp [Ssmall, Slarge] at hlargeEmpty ⊢
      apply Finset.ext
      intro y
      by_cases hyS : y ∈ S
      · have hySmall : H y < 1 := by
          by_contra hnot
          have : y ∈ S.filter (fun z => ¬ H z < 1) :=
            Finset.mem_filter.mpr ⟨hyS, hnot⟩
          rw [hlargeEmpty] at this
          simp at this
        simp [hyS, hySmall]
      · simp [hyS]
    change (∑ y ∈ S, (H y)⁻¹ ^ m) ≤ Ctotal
    rw [← hSsmall]
    exact hsmallBound.trans (by
      dsimp [Ctotal]
      linarith [hDlarge])

/- [paper, equation `eq:two_terms` and its estimates, lines 1769--1800]
   This is the literal manuscript split of the innermost row family at
   `c * ‖x‖`.  The first filtered sum is the multiplicative annulus and the
   complementary filtered sum is the projection slab; the preceding two
   theorems prove the two bounds obtained by ordinary Abel summation. -/
set_option maxHeartbeats 1200000 in
theorem exists_ambientIntegralRowModule_critical_innermost_sum_bound
    (m : ℕ) (hm : 1 < m) (hdegree : degree K = 1)
    {delta : ℝ} (hdelta : 0 < delta)
    (hmin : ∀ v : ambientIntegralRowModule (K := K) m,
      v ≠ 0 → delta ≤ ‖(v : RowVector K m)‖)
    (c : ℝ) (hc : 1 ≤ c) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (x : ambientIntegralRowModule (K := K) m), x ≠ 0 →
      ∀ S : Finset (ambientIntegralRowModule (K := K) m),
        (∀ y ∈ S,
          ‖(x : RowVector K m)‖ ≤ ‖(y : RowVector K m)‖ ∧
          ‖rowAmbientProjection (K := K) (m := m)
            (x : RowVector K m) (y : RowVector K m)‖ ≤
              c * ‖(x : RowVector K m)‖) →
        (∑ y ∈ S, ‖(y : RowVector K m)‖⁻¹ ^ m) ≤ C := by
  classical
  obtain ⟨Cnear, hCnear, hnear⟩ :=
    exists_ambientIntegralRowModule_critical_annulus_sum_bound
      (K := K) m (by omega) hdegree c hc
  obtain ⟨Cfar, hCfar, hfar⟩ :=
    exists_ambientIntegralRowModule_critical_projection_slab_tail_bound
      (K := K) m hm hdegree hdelta hmin c hc
  refine ⟨Cnear + Cfar, add_pos hCnear hCfar, ?_⟩
  intro x hx S hS
  let Snear : Finset (ambientIntegralRowModule (K := K) m) :=
    S.filter (fun y =>
      ‖(y : RowVector K m)‖ ≤ c * ‖(x : RowVector K m)‖)
  let Sfar : Finset (ambientIntegralRowModule (K := K) m) :=
    S.filter (fun y =>
      ¬ ‖(y : RowVector K m)‖ ≤ c * ‖(x : RowVector K m)‖)
  have hnearBound :
      (∑ y ∈ Snear, ‖(y : RowVector K m)‖⁻¹ ^ m) ≤ Cnear := by
    apply hnear x hx Snear
    intro y hy
    have hy' := Finset.mem_filter.mp hy
    exact ⟨(hS y hy'.1).1, hy'.2⟩
  have hfarBound :
      (∑ y ∈ Sfar, ‖(y : RowVector K m)‖⁻¹ ^ m) ≤ Cfar := by
    apply hfar x hx Sfar
    intro y hy
    have hy' := Finset.mem_filter.mp hy
    exact ⟨(le_of_lt (lt_of_not_ge hy'.2)), (hS y hy'.1).2⟩
  have htwoTerms :
      (∑ y ∈ S, ‖(y : RowVector K m)‖⁻¹ ^ m) =
        (∑ y ∈ Snear, ‖(y : RowVector K m)‖⁻¹ ^ m) +
          ∑ y ∈ Sfar, ‖(y : RowVector K m)‖⁻¹ ^ m := by
    dsimp [Snear, Sfar]
    rw [← Finset.sum_filter_add_sum_filter_not S
      (fun y => ‖(y : RowVector K m)‖ ≤
        c * ‖(x : RowVector K m)‖)]
  rw [htwoTerms]
  exact add_le_add hnearBound hfarBound

/- [Lean infrastructure for paper lines 1765--1768] The recursive relaxed
   tuple weight is rewritten with the manuscript's last row singled out.
   This is the explicit bridge used below to keep the outer `k - 1` rows and
   the critical innermost row in their displayed order. -/
theorem orderedNormTupleWeight_eq_init_prod_mul_last
    {alpha : Type*} (H : alpha → ℝ) (a q : ℕ) :
    ∀ {j : ℕ} (l : Fin (j + 1) → alpha),
      orderedNormTupleWeight H a q l =
        (∏ i : Fin j, (H (l i.castSucc))⁻¹ ^ a) *
          (H (l (Fin.last j)))⁻¹ ^ q := by
  intro j
  induction j with
  | zero =>
      intro l
      simp [orderedNormTupleWeight]
  | succ j ih =>
      intro l
      rw [orderedNormTupleWeight, ih, Fin.prod_univ_succ]
      have hfirst : (H (l 0))⁻¹ ^ a =
          (H (l (Fin.castSucc (0 : Fin (j + 1)))))⁻¹ ^ a := by
        congr 3
      have hmiddle :
          (∏ i : Fin j, (H ((Fin.tail l) i.castSucc))⁻¹ ^ a) =
            ∏ i : Fin j, (H (l i.succ.castSucc))⁻¹ ^ a := by
        apply Finset.prod_congr rfl
        intro i hi
        congr 3
      have hlast : (H ((Fin.tail l) (Fin.last j)))⁻¹ ^ q =
          (H (l (Fin.last (j + 1))))⁻¹ ^ q := by
        congr 3
      rw [hfirst, hmiddle, hlast]
      ring

/- [Lean infrastructure for paper lines 1765--1773] When every row has the
   same reciprocal exponent, the recursive tuple weight is the ordinary
   product over those rows.  This bridge lets the outer `k - 1` rows be fed
   directly to the already proved ordered-row sum. -/
theorem orderedNormTupleWeight_same_eq_prod
    {alpha : Type*} (H : alpha → ℝ) (a : ℕ) :
    ∀ {j : ℕ} (l : Fin (j + 1) → alpha),
      orderedNormTupleWeight H a a l =
        ∏ i : Fin (j + 1), (H (l i))⁻¹ ^ a := by
  intro j l
  rw [orderedNormTupleWeight_eq_init_prod_mul_last]
  exact (Fin.prod_univ_castSucc
    (fun i : Fin (j + 1) => (H (l i))⁻¹ ^ a)).symm

/- [derived consequence of paper equation `eq:two_terms`, lines 1769--1800]
   Transfer the proved ordinary-shell innermost estimate from the fixed
   ambient integral-row lattice back to the manuscript's rows in
   `\mathcal O_K^m`.  The Minkowski embedding is injective and preserves
   every norm and projection appearing in the statement definitionally. -/
theorem exists_integralRow_critical_innermost_sum_bound
    (m : ℕ) (hm : 1 < m) (hdegree : degree K = 1)
    {delta : ℝ} (hdelta : 0 < delta)
    (hmin : ∀ v : ambientIntegralRowModule (K := K) m,
      v ≠ 0 → delta ≤ ‖(v : RowVector K m)‖)
    (c : ℝ) (hc : 1 ≤ c) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (x : Fin m → 𝓞 K), x ≠ 0 →
      ∀ S : Finset (Fin m → 𝓞 K),
        (∀ y ∈ S,
          ‖integralVectorEmbedding (K := K) m x‖ ≤
              ‖integralVectorEmbedding (K := K) m y‖ ∧
          ‖rowAmbientProjection (K := K) (m := m)
            (integralVectorEmbedding (K := K) m x)
            (integralVectorEmbedding (K := K) m y)‖ ≤
              c * ‖integralVectorEmbedding (K := K) m x‖) →
        (∑ y ∈ S, ‖integralVectorEmbedding (K := K) m y‖⁻¹ ^ m) ≤ C := by
  classical
  obtain ⟨C, hC, hbound⟩ :=
    exists_ambientIntegralRowModule_critical_innermost_sum_bound
      (K := K) m hm hdegree hdelta hmin c hc
  refine ⟨C, hC, ?_⟩
  intro x hx S hS
  let e : (Fin m → 𝓞 K) → ambientIntegralRowModule (K := K) m := fun y =>
    ⟨integralVectorEmbedding (K := K) m y,
      integralVectorEmbedding_mem_ambientIntegralRowModule (K := K) m y⟩
  have he : Function.Injective e := by
    intro y z hyz
    apply integralVectorEmbedding_injective (K := K) m
    exact congrArg Subtype.val hyz
  have hex : e x ≠ 0 := by
    intro hzero
    apply hx
    apply integralVectorEmbedding_injective (K := K) m
    simpa [e] using congrArg Subtype.val hzero
  let Sambient : Finset (ambientIntegralRowModule (K := K) m) := S.image e
  have hSambient : ∀ v ∈ Sambient,
      ‖((e x : ambientIntegralRowModule (K := K) m) : RowVector K m)‖ ≤
          ‖(v : RowVector K m)‖ ∧
      ‖rowAmbientProjection (K := K) (m := m)
        ((e x : ambientIntegralRowModule (K := K) m) : RowVector K m)
        (v : RowVector K m)‖ ≤
          c * ‖((e x : ambientIntegralRowModule (K := K) m) : RowVector K m)‖ := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨y, hy, rfl⟩
    simpa [e] using hS y hy
  have hambient := hbound (e x) hex Sambient hSambient
  calc
    (∑ y ∈ S, ‖integralVectorEmbedding (K := K) m y‖⁻¹ ^ m) =
        ∑ v ∈ Sambient, ‖(v : RowVector K m)‖⁻¹ ^ m := by
      symm
      dsimp [Sambient]
      rw [Finset.sum_image he.injOn]
    _ ≤ C := hambient

/- [derived consequence of paper lines 1765--1800] After the literal
   `eq:two_terms` estimate is applied to the final row, the first `k - 1`
   ordered rows carry reciprocal exponent `m + 1`.  Their ordinary-shell
   sum is strictly convergent because `m * degree K < m + 1`.  This theorem
   performs exactly that outer summation for `k = j + 2`. -/
set_option maxHeartbeats 4800000 in
theorem possibleSuccessiveMinima_nonzero_critical_higher_rank_weight_sum_le
    {m j : ℕ} (hm : 1 < m) (hdegree : degree K = 1)
    (c : ℝ) (hc : 1 ≤ c) :
    ∃ M : ℝ, 0 < M ∧ ∀ T : ℝ,
      (∑ l ∈ possibleSuccessiveMinimaNonzeroFinset
        (K := K) (m := m) (k := j + 2) c T,
        orderedNormTupleWeight
          (fun x : Fin m → 𝓞 K =>
            ‖integralVectorEmbedding (K := K) m x‖)
          (m + 1) m l) ≤ M := by
  classical
  obtain ⟨delta, hdelta, hmin⟩ :=
    exists_ambientIntegralRowModule_norm_lower_bound
      (K := K) m (by omega)
  obtain ⟨Cinner, hCinner, hinner⟩ :=
    exists_integralRow_critical_innermost_sum_bound
      (K := K) m hm hdegree hdelta hmin c hc
  have hgap : m * degree K < m + 1 := by
    rw [hdegree]
    omega
  obtain ⟨Couter, hCouter, houter⟩ :=
    integralRow_orderedNormTupleWeight_sum_le
      (K := K) (m := m) (a := m + 1) (q := m + 1) (j := j)
      (by omega) hgap hgap hdelta
  refine ⟨Cinner * Couter, mul_pos hCinner hCouter, ?_⟩
  intro T
  let H : (Fin m → 𝓞 K) → ℝ := fun x =>
    ‖integralVectorEmbedding (K := K) m x‖
  let B : Finset (Fin (j + 2) → Fin m → 𝓞 K) :=
    possibleSuccessiveMinimaNonzeroFinset
      (K := K) (m := m) (k := j + 2) c T
  let pref : (Fin (j + 2) → Fin m → 𝓞 K) →
      (Fin (j + 1) → Fin m → 𝓞 K) := Fin.init
  let lastRow : (Fin (j + 2) → Fin m → 𝓞 K) →
      (Fin m → 𝓞 K) := fun l => l (Fin.last (j + 1))
  let P : Finset (Fin (j + 1) → Fin m → 𝓞 K) := B.image pref
  let fiber : (Fin (j + 1) → Fin m → 𝓞 K) →
      Finset (Fin (j + 2) → Fin m → 𝓞 K) := fun p =>
    B.filter (fun l => pref l = p)
  let finalRows : (Fin (j + 1) → Fin m → 𝓞 K) →
      Finset (Fin m → 𝓞 K) := fun p => (fiber p).image lastRow
  have hBdata (l : Fin (j + 2) → Fin m → 𝓞 K) (hl : l ∈ B) :
      l ∈ possibleSuccessiveMinimaSet
          (K := K) (m := m) (k := j + 2) c T ∧
        ∀ i, l i ≠ 0 := by
    have hlfilter : l ∈
        (finite_possibleSuccessiveMinimaSet
          (K := K) (m := m) (k := j + 2) (C := c) (T := T)).toFinset.filter
            (fun l => ∀ i, l i ≠ 0) := by
      simpa [B, possibleSuccessiveMinimaNonzeroFinset] using hl
    exact ⟨(finite_possibleSuccessiveMinimaSet
      (K := K) (m := m) (k := j + 2) (C := c) (T := T)).mem_toFinset.mp
        (Finset.mem_filter.mp hlfilter).1,
      (Finset.mem_filter.mp hlfilter).2⟩
  have hPcondition : ∀ p ∈ P,
      (∀ i, delta ≤ H (p i)) ∧
        ∀ i : Fin j, H (p i.castSucc) ≤ H (p i.succ) := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨l, hlB, rfl⟩
    have hl := hBdata l hlB
    refine ⟨?_, ?_⟩
    · intro i
      let v : ambientIntegralRowModule (K := K) m :=
        ⟨integralVectorEmbedding (K := K) m ((pref l) i),
          integralVectorEmbedding_mem_ambientIntegralRowModule
            (K := K) m ((pref l) i)⟩
      have hprefne : (pref l) i ≠ 0 := by
        dsimp [pref]
        exact hl.2 i.castSucc
      have hv : v ≠ 0 := by
        intro hzero
        apply hprefne
        apply integralVectorEmbedding_injective (K := K) m
        simpa [v] using congrArg Subtype.val hzero
      simpa [H, v] using hmin v hv
    · intro i
      have hordered := hl.1.1
        i.castSucc.castSucc i.succ.castSucc (Nat.le_succ i.val)
      change
        ‖integralVectorEmbedding (K := K) m (l i.castSucc.castSucc)‖ ≤
          ‖integralVectorEmbedding (K := K) m (l i.succ.castSucc)‖
      exact hordered
  have houterBound :
      (∑ p ∈ P, orderedNormTupleWeight H (m + 1) (m + 1) p) ≤
        Couter := by
    simpa [H] using houter P hPcondition
  have hweightSplit (l : Fin (j + 2) → Fin m → 𝓞 K) :
      orderedNormTupleWeight H (m + 1) m l =
        orderedNormTupleWeight H (m + 1) (m + 1) (pref l) *
          (H (lastRow l))⁻¹ ^ m := by
    rw [orderedNormTupleWeight_eq_init_prod_mul_last,
      orderedNormTupleWeight_same_eq_prod]
    rfl
  have hlastInj
      (p : Fin (j + 1) → Fin m → 𝓞 K) :
      Set.InjOn lastRow (fiber p : Set
        (Fin (j + 2) → Fin m → 𝓞 K)) := by
    intro l hl l' hl' hlast
    have hlprefix := (Finset.mem_filter.mp hl).2
    have hl'prefix := (Finset.mem_filter.mp hl').2
    have hprefix : Fin.init l = Fin.init l' := by
      change Fin.init l = p at hlprefix
      change Fin.init l' = p at hl'prefix
      exact hlprefix.trans hl'prefix.symm
    change l (Fin.last (j + 1)) = l' (Fin.last (j + 1)) at hlast
    calc
      l = Fin.snoc (Fin.init l) (l (Fin.last (j + 1))) :=
        (Fin.snoc_init_self l).symm
      _ = Fin.snoc (Fin.init l') (l' (Fin.last (j + 1))) := by
        rw [hprefix, hlast]
      _ = l' := Fin.snoc_init_self l'
  have hfiberBound
      (p : Fin (j + 1) → Fin m → 𝓞 K) (hp : p ∈ P) :
      (∑ l ∈ fiber p, orderedNormTupleWeight H (m + 1) m l) ≤
        orderedNormTupleWeight H (m + 1) (m + 1) p * Cinner := by
    rcases Finset.mem_image.mp hp with ⟨lzero, hlzeroB, hlzeroPrefix⟩
    let x : Fin m → 𝓞 K := p (Fin.last j)
    have hx : x ≠ 0 := by
      have hlzero := (hBdata lzero hlzeroB).2
      have hxEq : x = lzero (Fin.last j).castSucc := by
        dsimp [x]
        exact (congrFun hlzeroPrefix (Fin.last j)).symm
      rw [hxEq]
      exact hlzero (Fin.last j).castSucc
    have hfinalRows : ∀ y ∈ finalRows p,
        H x ≤ H y ∧
          ‖rowAmbientProjection (K := K) (m := m)
            (integralVectorEmbedding (K := K) m x)
            (integralVectorEmbedding (K := K) m y)‖ ≤ c * H x := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨l, hlfiber, rfl⟩
      have hlf := Finset.mem_filter.mp hlfiber
      have hl := hBdata l hlf.1
      have hxEq : x = l (Fin.last j).castSucc := by
        dsimp [x]
        exact (congrFun hlf.2 (Fin.last j)).symm
      have hindexlt : (Fin.last j).castSucc.val <
          (Fin.last (j + 1)).val := by simp
      constructor
      · rw [hxEq]
        exact hl.1.1 (Fin.last j).castSucc (Fin.last (j + 1))
          hindexlt.le
      · simpa [H, lastRow, hxEq] using
          hl.1.2.2 (Fin.last j).castSucc (Fin.last (j + 1)) hindexlt
    have hinnerBound := hinner x hx (finalRows p) (by
      simpa [H] using hfinalRows)
    have hsumImage :
        (∑ y ∈ finalRows p, (H y)⁻¹ ^ m) =
          ∑ l ∈ fiber p, (H (lastRow l))⁻¹ ^ m := by
      dsimp [finalRows]
      rw [Finset.sum_image (hlastInj p)]
    have hprefixNonneg :
        0 ≤ orderedNormTupleWeight H (m + 1) (m + 1) p := by
      rw [orderedNormTupleWeight_same_eq_prod]
      exact Finset.prod_nonneg fun i hi =>
        pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _
    calc
      (∑ l ∈ fiber p, orderedNormTupleWeight H (m + 1) m l) =
          ∑ l ∈ fiber p,
            orderedNormTupleWeight H (m + 1) (m + 1) p *
              (H (lastRow l))⁻¹ ^ m := by
        apply Finset.sum_congr rfl
        intro l hlf
        rw [hweightSplit]
        rw [(Finset.mem_filter.mp hlf).2]
      _ = orderedNormTupleWeight H (m + 1) (m + 1) p *
          (∑ l ∈ fiber p, (H (lastRow l))⁻¹ ^ m) := by
        rw [Finset.mul_sum]
      _ = orderedNormTupleWeight H (m + 1) (m + 1) p *
          (∑ y ∈ finalRows p, (H y)⁻¹ ^ m) := by
        rw [hsumImage]
      _ ≤ orderedNormTupleWeight H (m + 1) (m + 1) p * Cinner :=
        mul_le_mul_of_nonneg_left hinnerBound hprefixNonneg
  have hmaps : ∀ l ∈ B, pref l ∈ P := by
    intro l hl
    exact Finset.mem_image.mpr ⟨l, hl, rfl⟩
  have hdecomp := Finset.sum_fiberwise_of_maps_to hmaps
    (fun l : Fin (j + 2) → Fin m → 𝓞 K =>
      orderedNormTupleWeight H (m + 1) m l)
  change (∑ l ∈ B, orderedNormTupleWeight H (m + 1) m l) ≤
    Cinner * Couter
  calc
    (∑ l ∈ B, orderedNormTupleWeight H (m + 1) m l) =
        ∑ p ∈ P, ∑ l ∈ B with pref l = p,
          orderedNormTupleWeight H (m + 1) m l := hdecomp.symm
    _ ≤ ∑ p ∈ P,
        orderedNormTupleWeight H (m + 1) (m + 1) p * Cinner := by
      apply Finset.sum_le_sum
      intro p hp
      exact hfiberBound p hp
    _ = Cinner *
        (∑ p ∈ P, orderedNormTupleWeight H (m + 1) (m + 1) p) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ Cinner * Couter :=
      mul_le_mul_of_nonneg_left houterBound hCinner.le

/- [paper, exceptional critical branch at lines 1765--1800] Uniform bound
   for the literal `possibleSuccessiveMinimaRadiusWeight` sum when
   `degree K = 1`, `n = m + 1`, and `k = j + 2 ≥ 2`.  The exact nonzero
   bridge retains the manuscript's `\mathcal B_k^{(c)}(T)` notation; the
   preceding theorem supplies its ordinary-shell proof. -/
theorem possibleSuccessiveMinimaRadiusWeight_sum_le_of_critical_higher_rank
    {m j : ℕ} (hm : 1 < m) (hdegree : degree K = 1)
    (c : ℝ) (hc : 1 ≤ c) :
    ∃ M : ℝ, 0 < M ∧ ∀ T : ℝ,
      (∑ l ∈ (finite_possibleSuccessiveMinimaSet
        (K := K) (m := m) (k := j + 2) (C := c) (T := T)).toFinset,
        possibleSuccessiveMinimaRadiusWeight
          (K := K) (m := m) (m + 1) (by omega) l) ≤ M := by
  classical
  obtain ⟨M, hM, hbound⟩ :=
    possibleSuccessiveMinima_nonzero_critical_higher_rank_weight_sum_le
      (K := K) (j := j) hm hdegree c hc
  refine ⟨M, hM, ?_⟩
  intro T
  rw [sum_possibleSuccessiveMinimaRadiusWeight_eq_nonzero_product_weight
    (K := K) (m := m) (n := m + 1) (j := j + 1)
    (by omega) (by omega) c T]
  have hweight (l : Fin (j + 2) → Fin m → 𝓞 K)
      (hl : l ∈ possibleSuccessiveMinimaNonzeroFinset
        (K := K) (m := m) (k := j + 2) c T) :
      ((∏ i : Fin (j + 2),
        ‖integralVectorEmbedding (K := K) m (l i)‖ ^ degree K)⁻¹) ^
          (m + 1) *
        ‖integralVectorEmbedding (K := K) m (l (Fin.last (j + 1)))‖ =
      orderedNormTupleWeight
        (fun x : Fin m → 𝓞 K =>
          ‖integralVectorEmbedding (K := K) m x‖)
        (m + 1) m l := by
    have hlfilter : l ∈
        (finite_possibleSuccessiveMinimaSet
          (K := K) (m := m) (k := j + 2) (C := c) (T := T)).toFinset.filter
            (fun l => ∀ i, l i ≠ 0) := by
      simpa [possibleSuccessiveMinimaNonzeroFinset] using hl
    have hnorm (i : Fin (j + 2)) :
        ‖integralVectorEmbedding (K := K) m (l i)‖ ≠ 0 := by
      apply norm_ne_zero_iff.mpr
      intro hzero
      apply (Finset.mem_filter.mp hlfilter).2 i
      apply integralVectorEmbedding_injective (K := K) m
      simpa using hzero
    have hbridge := product_inv_pow_mul_last_eq_orderedNormTupleWeight
      (fun x : Fin m → 𝓞 K =>
        ‖integralVectorEmbedding (K := K) m x‖)
      (m + 1) (degree K) (by omega) Module.finrank_pos l hnorm
    simpa [hdegree] using hbridge
  calc
    (∑ l ∈ possibleSuccessiveMinimaNonzeroFinset
      (K := K) (m := m) (k := j + 2) c T,
      ((∏ i : Fin (j + 2),
        ‖integralVectorEmbedding (K := K) m (l i)‖ ^ degree K)⁻¹) ^
          (m + 1) *
        ‖integralVectorEmbedding (K := K) m (l (Fin.last (j + 1)))‖) =
        ∑ l ∈ possibleSuccessiveMinimaNonzeroFinset
          (K := K) (m := m) (k := j + 2) c T,
          orderedNormTupleWeight
            (fun x : Fin m → 𝓞 K =>
              ‖integralVectorEmbedding (K := K) m x‖)
            (m + 1) m l := by
      apply Finset.sum_congr rfl
      intro l hl
      exact hweight l hl
    _ ≤ M := hbound T

/- [derived consequence of paper equation `eq:just_as_before` and the
   exceptional critical argument, lines 1724--1800] Transfer the literal
   higher-rank tuple bound to the exact echelon family `\mathcal F_k(T)`.
   The manuscript's product-of-minima comparison remains an explicit
   argument at this interface. -/
theorem exists_uniform_calF_coveringRadius_sum_bound_of_critical_higher_rank
    {m j : ℕ} {Cprod : ℝ} (hm : 1 < m)
    (hdegree : degree K = 1) (hCprod : 0 ≤ Cprod)
    (c : ℝ) (hc : 1 ≤ c) :
    ∃ Cfinite : ℝ, 0 < Cfinite ∧
      ∀ {Csup T : ℝ}
        (hCproj : rowKRealSmulBound (K := K) (m := m) *
          numberFieldCoefficientRadius K ≤ c)
        (hCsup : Csup ≤ c) (hT : 0 ≤ T)
        (_hprod : ∀ D : EchelonMatrix K (j + 2) m,
          D ∈ calF (K := K) (l := j + 2) (m := m) (n := m + 1) Csup T →
            (∏ i : Fin (j + 2),
              ‖((rowSuccessiveMinimum (echelonRowSpace D) i :
                rowZLattice (echelonRowSpace D)) :
                  rowRealSpan (echelonRowSpace D))‖ ^ degree K) ≤
              Cprod * rowSpaceHeight (echelonRowSpace D)),
        (∑ D ∈ (finite_calF_of_possibleSuccessiveMinima
          (K := K) (m := m) (k := j + 2) (n := m + 1)
          hCproj hCsup hT (by omega)).toFinset,
          latticeCoveringRadius (rowZLattice (echelonRowSpace D)) /
            (rowSpaceHeight (echelonRowSpace D)) ^ (m + 1)) ≤ Cfinite := by
  obtain ⟨M, hM, htuple⟩ :=
    possibleSuccessiveMinimaRadiusWeight_sum_le_of_critical_higher_rank
      (K := K) (j := j) hm hdegree c hc
  let R : ℝ :=
    (Fintype.card (Σ _ : Fin (j + 2), IntegralBasisIndex K) : ℝ) *
      rowScalarActionBoundSum (K := K) (m := m)
  let A : ℝ := R * Cprod ^ (m + 1)
  let Cfinite : ℝ := A * M + 1
  have hR : 0 ≤ R := by
    dsimp [R]
    exact mul_nonneg (Nat.cast_nonneg _)
      (rowScalarActionBoundSum_nonneg (K := K) (m := m))
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg hR (pow_nonneg hCprod _)
  have hCfinite : 0 < Cfinite := by
    dsimp [Cfinite]
    linarith [mul_nonneg hA hM.le]
  refine ⟨Cfinite, hCfinite, ?_⟩
  intro Csup T hCproj hCsup hT _hprod
  have hsum :=
    sum_calF_coveringRadius_div_height_pow_le_possibleMinimaWeight
      (K := K) (m := m) (k := j + 2) (n := m + 1)
      hCproj hCsup hT (by omega) hCprod _hprod
  have htupleT := htuple T
  have hsum' :
      (∑ D ∈ (finite_calF_of_possibleSuccessiveMinima
        (K := K) (m := m) (k := j + 2) (n := m + 1)
        hCproj hCsup hT (by omega)).toFinset,
        latticeCoveringRadius (rowZLattice (echelonRowSpace D)) /
          (rowSpaceHeight (echelonRowSpace D)) ^ (m + 1)) ≤
        A *
          (∑ l ∈ (finite_possibleSuccessiveMinimaSet
            (K := K) (m := m) (k := j + 2) (C := c) (T := T)).toFinset,
            possibleSuccessiveMinimaRadiusWeight
              (K := K) (m := m) (m + 1) (by omega) l) := by
    simpa [A, R] using hsum
  calc
    (∑ D ∈ (finite_calF_of_possibleSuccessiveMinima
      (K := K) (m := m) (k := j + 2) (n := m + 1)
      hCproj hCsup hT (by omega)).toFinset,
      latticeCoveringRadius (rowZLattice (echelonRowSpace D)) /
        (rowSpaceHeight (echelonRowSpace D)) ^ (m + 1)) ≤
        A *
          (∑ l ∈ (finite_possibleSuccessiveMinimaSet
            (K := K) (m := m) (k := j + 2) (C := c) (T := T)).toFinset,
            possibleSuccessiveMinimaRadiusWeight
              (K := K) (m := m) (m + 1) (by omega) l) := hsum'
    _ ≤ A * M := mul_le_mul_of_nonneg_left htupleT hA
    _ ≤ Cfinite := by
      dsimp [Cfinite]
      linarith

/- [derived consequence of paper equation `eq:just_as_before`, lines
   1724--1800] The critical higher-rank `\mathcal F_k(T)` estimate with the
   product comparison discharged by the proved Fieker--Stehlé selection and
   Euclidean Minkowski-II theorem in `FiekerStehle.lean`. -/
theorem exists_uniform_calF_coveringRadius_sum_bound_of_critical_higher_rank_of_fiekerStehle
    {m j : ℕ} (hm : 1 < m) (hdegree : degree K = 1)
    (c : ℝ) (hc : 1 ≤ c) :
    ∃ Cfinite : ℝ, 0 < Cfinite ∧
      ∀ {Csup T : ℝ}
        (hCproj : rowKRealSmulBound (K := K) (m := m) *
          numberFieldCoefficientRadius K ≤ c)
        (hCsup : Csup ≤ c) (hT : 0 ≤ T),
        (∑ D ∈ (finite_calF_of_possibleSuccessiveMinima
          (K := K) (m := m) (k := j + 2) (n := m + 1)
          hCproj hCsup hT (by omega)).toFinset,
          latticeCoveringRadius (rowZLattice (echelonRowSpace D)) /
            (rowSpaceHeight (echelonRowSpace D)) ^ (m + 1)) ≤ Cfinite := by
  obtain ⟨Cprod, hCprod, hprod⟩ :=
    exists_rowSuccessiveMinimum_product_le_height_of_euclideanMinkowskiSecond
      (K := K) (m := m) (k := j + 2) (by omega)
  obtain ⟨Cfinite, hCfinite, hbound⟩ :=
    exists_uniform_calF_coveringRadius_sum_bound_of_critical_higher_rank
      (K := K) (j := j) hm hdegree hCprod.le c hc
  refine ⟨Cfinite, hCfinite, ?_⟩
  intro Csup T hCproj hCsup hT
  apply hbound hCproj hCsup hT
  intro D hD
  exact hprod (echelonRowSpace D)

/- [derived consequence of paper equation `eq:just_as_before`, lines
   1727--1741, and the exceptional critical argument, lines 1759--1800]
   Reindex the hypothesis-free higher-rank `\mathcal F_k(T)` estimate to the
   manuscript's exactly equal bounded row-space family.  The preceding
   theorem discharges the product input by the proved Fieker--Stehlé/
   Euclidean Minkowski-II derivation in `FiekerStehle.lean`. -/
theorem exists_uniform_boundedRowSpaces_coveringRadius_sum_bound_of_critical_higher_rank
    {m j : ℕ} (hm : 1 < m) (hdegree : degree K = 1)
    (c : ℝ) (hc : 1 ≤ c) :
    ∃ Cfinite : ℝ, 0 < Cfinite ∧
      ∀ {Csup T : ℝ}
        [Fintype (boundedRowSpaces (K := K) (n := m + 1) (m := m)
          (k := j + 2) Csup T)]
        (hCproj : rowKRealSmulBound (K := K) (m := m) *
          numberFieldCoefficientRadius K ≤ c)
        (hCsup : Csup ≤ c) (hT : 0 ≤ T),
        (∑ V : boundedRowSpaces (K := K) (n := m + 1) (m := m)
          (k := j + 2) Csup T,
          latticeCoveringRadius (rowZLattice V.1) /
            (rowSpaceHeight V.1) ^ (m + 1)) ≤ Cfinite := by
  obtain ⟨Cfinite, hCfinite, hbound⟩ :=
    exists_uniform_calF_coveringRadius_sum_bound_of_critical_higher_rank_of_fiekerStehle
      (K := K) (j := j) hm hdegree c hc
  refine ⟨Cfinite, hCfinite, ?_⟩
  intro Csup T _ hCproj hCsup hT
  rw [sum_boundedRowSpaces_coveringRadius_div_height_pow_eq_sum_calF
    (K := K) (m := m) (k := j + 2) (n := m + 1) (C := c)
    hCproj hCsup hT (by omega)]
  exact hbound hCproj hCsup hT

/- [derived consequence of paper lemma `le:without_rank_cond`, lines
   1032--1044, equation `eq:ineq212`, lines 1685--1696, and the exceptional
   critical argument, lines 1759--1800] This is the exact intrinsic summand
   consumed by the fixed-rank Voronoi assembly: the `sqrt n` factor is
   explicit and the denominator is the row-matrix lattice covolume.  Its
   product input is the same proved Fieker--Stehlé/Minkowski-II derivation. -/
theorem exists_uniform_boundedRowSpaces_latticeVoronoi_radius_sum_bound_of_critical_higher_rank
    {m j : ℕ} (hm : 1 < m) (hdegree : degree K = 1)
    (c : ℝ) (hc : 1 ≤ c) :
    ∃ C_R : ℝ, 0 < C_R ∧
      ∀ {Csup T : ℝ}
        [Fintype (boundedRowSpaces (K := K) (n := m + 1) (m := m)
          (k := j + 2) Csup T)]
        (hCproj : rowKRealSmulBound (K := K) (m := m) *
          numberFieldCoefficientRadius K ≤ c)
        (hCsup : Csup ≤ c) (hT : 0 ≤ T),
        (∑ V : boundedRowSpaces (K := K) (n := m + 1) (m := m)
          (k := j + 2) Csup T,
          (Real.sqrt ((m + 1 : ℕ) : ℝ) *
              latticeCoveringRadius (rowZLattice V.1)) /
            rowMatrixLatticeCovolume V.1 (m + 1)) ≤ C_R := by
  obtain ⟨Cfinite, hCfinite, hbound⟩ :=
    exists_uniform_boundedRowSpaces_coveringRadius_sum_bound_of_critical_higher_rank
      (K := K) (j := j) hm hdegree c hc
  let C_R : ℝ := Real.sqrt ((m + 1 : ℕ) : ℝ) * Cfinite + 1
  have hsqrt : 0 ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) := Real.sqrt_nonneg _
  refine ⟨C_R, ?_, ?_⟩
  · have hnonneg :
        0 ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) * Cfinite :=
      mul_nonneg hsqrt hCfinite.le
    dsimp [C_R]
    linarith
  · intro Csup T _ hCproj hCsup hT
    have hradius := hbound hCproj hCsup hT
    have hrewrite :
        (∑ V : boundedRowSpaces (K := K) (n := m + 1) (m := m)
          (k := j + 2) Csup T,
          (Real.sqrt ((m + 1 : ℕ) : ℝ) *
              latticeCoveringRadius (rowZLattice V.1)) /
            rowMatrixLatticeCovolume V.1 (m + 1)) =
          Real.sqrt ((m + 1 : ℕ) : ℝ) *
            (∑ V : boundedRowSpaces (K := K) (n := m + 1) (m := m)
              (k := j + 2) Csup T,
              latticeCoveringRadius (rowZLattice V.1) /
                (rowSpaceHeight V.1) ^ (m + 1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro V _
      rw [rowMatrixLatticeCovolume_eq_rowSpaceHeight_pow]
      ring
    rw [hrewrite]
    calc
      Real.sqrt ((m + 1 : ℕ) : ℝ) *
          (∑ V : boundedRowSpaces (K := K) (n := m + 1) (m := m)
            (k := j + 2) Csup T,
            latticeCoveringRadius (rowZLattice V.1) /
              (rowSpaceHeight V.1) ^ (m + 1)) ≤
          Real.sqrt ((m + 1 : ℕ) : ℝ) * Cfinite :=
        mul_le_mul_of_nonneg_left hradius hsqrt
      _ ≤ C_R := by
        dsimp [C_R]
        linarith

/- [derived consequence of the rank-one argument in subsection
   `ss:log_term`, lines 324--358, its use at lines 1716--1724, and equation
   `eq:just_as_before`, lines 1733--1741] Reindex the proved first-Minkowski
   rank-one `\mathcal F_1(T)` estimate to the exact bounded row-space family. -/
theorem exists_boundedRowSpaces_coveringRadius_sum_bound_of_critical_rank_one
    {m : ℕ} (hm : 0 < m) (hdegree : degree K = 1)
    (c : ℝ) (hc : 0 ≤ c) :
    ∃ Cfinite : ℝ, 0 < Cfinite ∧
      ∀ {Csup T : ℝ}
        [Fintype (boundedRowSpaces (K := K) (n := m + 1) (m := m)
          (k := 1) Csup T)]
        (hCproj : rowKRealSmulBound (K := K) (m := m) *
          numberFieldCoefficientRadius K ≤ c)
        (hCsup : Csup ≤ c) (hT : 1 ≤ T),
        (∑ V : boundedRowSpaces (K := K) (n := m + 1) (m := m)
          (k := 1) Csup T,
          latticeCoveringRadius (rowZLattice V.1) /
            (rowSpaceHeight V.1) ^ (m + 1)) ≤
          Cfinite * (1 + Real.log T) := by
  obtain ⟨Cfinite, hCfinite, hbound⟩ :=
    exists_calF_coveringRadius_sum_bound_of_critical_rank_one_of_firstMinkowski
      (K := K) hm hdegree c hc
  refine ⟨Cfinite, hCfinite, ?_⟩
  intro Csup T _ hCproj hCsup hT
  rw [sum_boundedRowSpaces_coveringRadius_div_height_pow_eq_sum_calF
    (K := K) (m := m) (k := 1) (n := m + 1) (C := c)
    hCproj hCsup (le_trans zero_le_one hT) (by omega)]
  exact hbound hCproj hCsup hT

/- [derived consequence of paper lemma `le:without_rank_cond`, lines
   1032--1044, the rank-one argument at lines 324--358 and 1716--1724, and
   equation `eq:ineq212`, lines 1685--1696] This is the logarithmic
   rank-one counterpart of the exact intrinsic critical higher-rank endpoint. -/
theorem exists_boundedRowSpaces_latticeVoronoi_radius_sum_bound_of_critical_rank_one
    {m : ℕ} (hm : 0 < m) (hdegree : degree K = 1)
    (c : ℝ) (hc : 0 ≤ c) :
    ∃ C_R : ℝ, 0 < C_R ∧
      ∀ {Csup T : ℝ}
        [Fintype (boundedRowSpaces (K := K) (n := m + 1) (m := m)
          (k := 1) Csup T)]
        (hCproj : rowKRealSmulBound (K := K) (m := m) *
          numberFieldCoefficientRadius K ≤ c)
        (hCsup : Csup ≤ c) (hT : 1 ≤ T),
        (∑ V : boundedRowSpaces (K := K) (n := m + 1) (m := m)
          (k := 1) Csup T,
          (Real.sqrt ((m + 1 : ℕ) : ℝ) *
              latticeCoveringRadius (rowZLattice V.1)) /
            rowMatrixLatticeCovolume V.1 (m + 1)) ≤
          C_R * (1 + Real.log T) := by
  obtain ⟨Cfinite, hCfinite, hbound⟩ :=
    exists_boundedRowSpaces_coveringRadius_sum_bound_of_critical_rank_one
      (K := K) hm hdegree c hc
  let C_R : ℝ := Real.sqrt ((m + 1 : ℕ) : ℝ) * Cfinite + 1
  have hsqrt : 0 ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) := Real.sqrt_nonneg _
  refine ⟨C_R, ?_, ?_⟩
  · have hnonneg :
        0 ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) * Cfinite :=
      mul_nonneg hsqrt hCfinite.le
    dsimp [C_R]
    linarith
  · intro Csup T _ hCproj hCsup hT
    have hradius := hbound hCproj hCsup hT
    have hlog : 0 ≤ 1 + Real.log T := by
      linarith [Real.log_nonneg hT]
    have hrewrite :
        (∑ V : boundedRowSpaces (K := K) (n := m + 1) (m := m)
          (k := 1) Csup T,
          (Real.sqrt ((m + 1 : ℕ) : ℝ) *
              latticeCoveringRadius (rowZLattice V.1)) /
            rowMatrixLatticeCovolume V.1 (m + 1)) =
          Real.sqrt ((m + 1 : ℕ) : ℝ) *
            (∑ V : boundedRowSpaces (K := K) (n := m + 1) (m := m)
              (k := 1) Csup T,
              latticeCoveringRadius (rowZLattice V.1) /
                (rowSpaceHeight V.1) ^ (m + 1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro V _
      rw [rowMatrixLatticeCovolume_eq_rowSpaceHeight_pow]
      ring
    rw [hrewrite]
    calc
      Real.sqrt ((m + 1 : ℕ) : ℝ) *
          (∑ V : boundedRowSpaces (K := K) (n := m + 1) (m := m)
            (k := 1) Csup T,
            latticeCoveringRadius (rowZLattice V.1) /
              (rowSpaceHeight V.1) ^ (m + 1)) ≤
          Real.sqrt ((m + 1 : ℕ) : ℝ) *
            (Cfinite * (1 + Real.log T)) :=
        mul_le_mul_of_nonneg_left hradius hsqrt
      _ = (Real.sqrt ((m + 1 : ℕ) : ℝ) * Cfinite) *
          (1 + Real.log T) := by ring
      _ ≤ C_R * (1 + Real.log T) := by
        apply mul_le_mul_of_nonneg_right
        · dsimp [C_R]
          linarith
        · exact hlog

end Katznelson
