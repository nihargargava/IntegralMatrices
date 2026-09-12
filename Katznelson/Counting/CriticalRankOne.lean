import Katznelson.Counting.MinimaSums

/-!
# The exceptional critical rank-one minima sum

This module formalizes the logarithmic endpoint in the manuscript's case
`d = 1`, `k = 1`, and `n = m + 1`.  It keeps the literal
`possibleSuccessiveMinimaSet` (`\mathcal B_1^{(C)}(T)`) and `calF`
(`\mathcal F_1(T)`) interfaces.  Internally, their single row is grouped into
the same ordinary unit norm shells used in the manuscript's Abel-summation
argument; no dyadic decomposition is introduced.
-/

namespace Katznelson

open MeasureTheory Set
open scoped Classical NumberField

variable {K : Type*} [Field K] [NumberField K]

/- [paper, subsection `ss:log_term`, lines 344--358, and the exceptional
   branch of `th:main`, lines 1716--1724] At the endpoint `d = 1`, the
   ambient row-count exponent and reciprocal-norm exponent are both `m`.
   Abel summation over the manuscript's ordinary unit shells therefore gives
   the retained `1 + log b` factor. -/
set_option maxHeartbeats 1200000 in
theorem ambientIntegralRowModule_norm_shell_sum_Icc_critical_rank_one
    (m : ℕ) (hdegree : degree K = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ {b : ℕ}, 1 ≤ b →
      (∑ i ∈ Finset.Icc 1 b,
        (Set.ncard (heightShell
          (fun v : ambientIntegralRowModule (K := K) m =>
            ‖(v : RowVector K m)‖) i) : ℝ) * ((i : ℝ)⁻¹ ^ m)) ≤
        C * (1 + Real.log (b : ℝ)) := by
  obtain ⟨C, hC, hpartial⟩ :=
    ambientIntegralRowModule_norm_shell_partial_sum (K := K) m
  let H : ambientIntegralRowModule (K := K) m → ℝ := fun v =>
    ‖(v : RowVector K m)‖
  have hpartial' : ∀ {N : ℕ}, 1 ≤ N →
      (∑ i ∈ Finset.Icc 0 N,
        (Set.ncard (heightShell H i) : ℝ)) ≤ C * (N : ℝ) ^ m := by
    intro N hN
    simpa [H, hdegree] using hpartial hN
  let Ccritical : ℝ := C * (2 + (m : ℝ))
  refine ⟨Ccritical, ?_, ?_⟩
  · dsimp [Ccritical]
    positivity
  · intro b hb
    have hbR : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    have hbpos : (0 : ℝ) < (b : ℝ) := lt_of_lt_of_le zero_lt_one hbR
    have hmain := sum_Ioc_inv_pow_le_of_partial_sum
      (φ := fun i : ℕ => (Set.ncard (heightShell H i) : ℝ))
      (C := C) (a := 1) (b := b) (p := m) (q := m)
      le_rfl hb hC.le (fun i => by positivity) hpartial'
    have hIntegral := intervalIntegral_nat_power_inv_power_eq_log
      (p := m) (N := b) hb
    have hendpoint :
        (b : ℝ) ^ m * ((b : ℝ)⁻¹ ^ m) = 1 := by
      rw [← Real.rpow_natCast (b : ℝ) m,
        ← Real.rpow_natCast ((b : ℝ)⁻¹) m,
        Real.inv_rpow hbpos.le, ← Real.rpow_neg hbpos.le,
        ← Real.rpow_add hbpos]
      simp
    have hIoc :
        (∑ i ∈ Finset.Ioc 1 b,
          (Set.ncard (heightShell H i) : ℝ) * ((i : ℝ)⁻¹ ^ m)) ≤
          C * (1 + (m : ℝ)) * (1 + Real.log (b : ℝ)) := by
      have hlog : 0 ≤ Real.log (b : ℝ) := Real.log_nonneg hbR
      calc
        (∑ i ∈ Finset.Ioc 1 b,
          (Set.ncard (heightShell H i) : ℝ) * ((i : ℝ)⁻¹ ^ m)) ≤
            C * (b : ℝ) ^ m * ((b : ℝ)⁻¹ ^ m) +
              C * (m : ℝ) *
                (∫ x in (1 : ℝ)..(b : ℝ),
                  x ^ m * (x⁻¹ ^ (m + 1))) := by
          simpa only [Nat.cast_one] using hmain
        _ = C + C * (m : ℝ) * Real.log (b : ℝ) := by
          rw [show C * (b : ℝ) ^ m * ((b : ℝ)⁻¹ ^ m) =
            C * ((b : ℝ) ^ m * ((b : ℝ)⁻¹ ^ m)) by ring,
            hendpoint, hIntegral]
          ring
        _ ≤ C * (1 + (m : ℝ)) * (1 + Real.log (b : ℝ)) := by
          have hnonneg : 0 ≤ C * ((m : ℝ) + Real.log (b : ℝ)) :=
            mul_nonneg hC.le (add_nonneg (by positivity) hlog)
          nlinarith
    have hshellOne :
        (Set.ncard (heightShell H 1) : ℝ) ≤ C := by
      have h := hpartial' (N := 1) (by omega)
      have hsingle :
          (Set.ncard (heightShell H 1) : ℝ) ≤
            ∑ i ∈ Finset.Icc 0 1,
              (Set.ncard (heightShell H i) : ℝ) := by
        exact Finset.single_le_sum
          (s := Finset.Icc 0 1)
          (f := fun i : ℕ => (Set.ncard (heightShell H i) : ℝ))
          (fun i hi => by positivity) (by simp)
      exact hsingle.trans (by simpa using h)
    have hsplit : Finset.Icc 1 b = insert 1 (Finset.Ioc 1 b) := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
      omega
    have hone_log : 1 ≤ 1 + Real.log (b : ℝ) := by
      linarith [Real.log_nonneg hbR]
    have hCscale : C ≤ C * (1 + Real.log (b : ℝ)) := by
      calc
        C = C * 1 := by ring
        _ ≤ C * (1 + Real.log (b : ℝ)) :=
          mul_le_mul_of_nonneg_left hone_log hC.le
    calc
      (∑ i ∈ Finset.Icc 1 b,
        (Set.ncard (heightShell H i) : ℝ) * ((i : ℝ)⁻¹ ^ m)) =
          (Set.ncard (heightShell H 1) : ℝ) +
            ∑ i ∈ Finset.Ioc 1 b,
              (Set.ncard (heightShell H i) : ℝ) * ((i : ℝ)⁻¹ ^ m) := by
        rw [hsplit, Finset.sum_insert]
        · simp
        · simp
      _ ≤ C + C * (1 + (m : ℝ)) * (1 + Real.log (b : ℝ)) :=
        add_le_add hshellOne hIoc
      _ ≤ C * (1 + Real.log (b : ℝ)) +
          C * (1 + (m : ℝ)) * (1 + Real.log (b : ℝ)) :=
        add_le_add hCscale le_rfl
      _ = Ccritical * (1 + Real.log (b : ℝ)) := by
        simp [Ccritical]
        ring

/- [derived consequence of the paper endpoint at lines 344--358] The
   ordinary-shell estimate bounds any finite family of ambient integral rows
   lying below an integer cutoff.  The fixed shell below norm one is retained
   explicitly; it is finite by discreteness of `\mathcal O_K^m`. -/
set_option maxHeartbeats 1800000 in
theorem ambientIntegralRowModule_finite_norm_inv_pow_sum_le_log_at_nat
    (m : ℕ) (hdegree : degree K = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ {b : ℕ}, 1 ≤ b →
      ∀ S : Finset (ambientIntegralRowModule (K := K) m),
        (∀ v ∈ S, ‖(v : RowVector K m)‖ ≤ (b : ℝ)) →
        (∑ v ∈ S, ‖(v : RowVector K m)‖⁻¹ ^ m) ≤
          C * (1 + Real.log (b : ℝ)) := by
  classical
  obtain ⟨Cshell, hCshell, hshell⟩ :=
    ambientIntegralRowModule_norm_shell_sum_Icc_critical_rank_one
      (K := K) m hdegree
  let H : ambientIntegralRowModule (K := K) m → ℝ := fun v =>
    ‖(v : RowVector K m)‖
  let smallSet : Set (ambientIntegralRowModule (K := K) m) :=
    {v | H v < 1}
  have hsmallFinite : smallSet.Finite := by
    apply (lattice_ball_finite (ambientIntegralRowModule (K := K) m)).subset
    intro v hv
    simpa [smallSet, H] using hv.le
  let small : Finset (ambientIntegralRowModule (K := K) m) :=
    hsmallFinite.toFinset
  let Csmall : ℝ := ∑ v ∈ small, (H v)⁻¹ ^ m
  have hCsmall : 0 ≤ Csmall := by
    dsimp [Csmall]
    exact Finset.sum_nonneg fun v hv =>
      pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) m
  let Ctotal : ℝ := Cshell + Csmall + 1
  have hCtotal : 0 < Ctotal := by
    dsimp [Ctotal]
    linarith
  refine ⟨Ctotal, hCtotal, ?_⟩
  intro b hb S hSbound
  let Ssmall : Finset (ambientIntegralRowModule (K := K) m) :=
    S.filter (fun v => H v < 1)
  let Slarge : Finset (ambientIntegralRowModule (K := K) m) :=
    S.filter (fun v => ¬ H v < 1)
  have hsmallSub : Ssmall ⊆ small := by
    intro v hv
    apply hsmallFinite.mem_toFinset.mpr
    exact (Finset.mem_filter.mp hv).2
  have hsmallBound :
      (∑ v ∈ Ssmall, (H v)⁻¹ ^ m) ≤ Csmall := by
    dsimp [Csmall]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsmallSub
      (fun v hv hnot => pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) m)
  let I : Finset ℕ := Finset.Icc 1 b
  have hfinShell (i : ℕ) : (heightShell H i).Finite := by
    apply (lattice_ball_finite
      (ambientIntegralRowModule (K := K) m)).subset
    intro v hv
    simpa [H] using hv.2.le
  let F : ℕ → Finset (ambientIntegralRowModule (K := K) m) := fun i =>
    (hfinShell i).toFinset
  let U : Finset (ambientIntegralRowModule (K := K) m) := I.biUnion F
  have hdisj : (I : Set ℕ).PairwiseDisjoint F := by
    intro i hi j hj hij
    change Disjoint (F i) (F j)
    rw [Finset.disjoint_left]
    intro v hvi hvj
    apply Set.disjoint_left.1 (heightShell_disjoint hij)
    · exact (hfinShell i).mem_toFinset.mp hvi
    · exact (hfinShell j).mem_toFinset.mp hvj
  have hlargeSub : Slarge ⊆ U := by
    intro v hv
    have hvS : v ∈ S := (Finset.mem_filter.mp hv).1
    have hvone : 1 ≤ H v := le_of_not_gt (Finset.mem_filter.mp hv).2
    obtain ⟨i, hi, hvi⟩ := exists_mem_heightShell_of_one_le hvone
    have hibR : (i : ℝ) ≤ (b : ℝ) :=
      hvi.1.trans (by simpa [H] using hSbound v hvS)
    have hib : i ≤ b := by exact_mod_cast hibR
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_Icc.mpr ⟨hi, hib⟩, ?_⟩
    exact (hfinShell i).mem_toFinset.mpr hvi
  have hweightNonneg (v : ambientIntegralRowModule (K := K) m) :
      0 ≤ (H v)⁻¹ ^ m :=
    pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) m
  have hlargeToU :
      (∑ v ∈ Slarge, (H v)⁻¹ ^ m) ≤
        ∑ v ∈ U, (H v)⁻¹ ^ m :=
    Finset.sum_le_sum_of_subset_of_nonneg hlargeSub
      (fun v hv hnot => hweightNonneg v)
  have hsumU :
      (∑ v ∈ U, (H v)⁻¹ ^ m) =
        ∑ i ∈ I, ∑ v ∈ F i, (H v)⁻¹ ^ m := by
    simpa [U] using
      (Finset.sum_biUnion (s := I) (t := F) hdisj
        (f := fun v : ambientIntegralRowModule (K := K) m =>
          (H v)⁻¹ ^ m))
  have hFsum (i : ℕ) (hi : i ∈ I) :
      (∑ v ∈ F i, (H v)⁻¹ ^ m) ≤
        (Set.ncard (heightShell H i) : ℝ) * ((i : ℝ)⁻¹ ^ m) := by
    have hipos : 0 < i := by
      have hiOne := (Finset.mem_Icc.mp hi).1
      omega
    calc
      (∑ v ∈ F i, (H v)⁻¹ ^ m) ≤
          ∑ v ∈ F i, (i : ℝ)⁻¹ ^ m := by
        apply Finset.sum_le_sum
        intro v hv
        exact heightShell_inv_pow_le hipos
          ((hfinShell i).mem_toFinset.mp hv)
      _ = ((F i).card : ℝ) * ((i : ℝ)⁻¹ ^ m) := by
        simp [Finset.sum_const]
      _ = (Set.ncard (heightShell H i) : ℝ) * ((i : ℝ)⁻¹ ^ m) := by
        rw [Set.ncard_eq_toFinset_card (heightShell H i) (hfinShell i)]
  have hlargeBound :
      (∑ v ∈ Slarge, (H v)⁻¹ ^ m) ≤
        Cshell * (1 + Real.log (b : ℝ)) := by
    calc
      (∑ v ∈ Slarge, (H v)⁻¹ ^ m) ≤
          ∑ v ∈ U, (H v)⁻¹ ^ m := hlargeToU
      _ = ∑ i ∈ I, ∑ v ∈ F i, (H v)⁻¹ ^ m := hsumU
      _ ≤ ∑ i ∈ I,
          (Set.ncard (heightShell H i) : ℝ) * ((i : ℝ)⁻¹ ^ m) :=
        Finset.sum_le_sum hFsum
      _ ≤ Cshell * (1 + Real.log (b : ℝ)) := by
        simpa [I, H] using hshell hb
  have hsplit :
      (∑ v ∈ S, (H v)⁻¹ ^ m) =
        (∑ v ∈ Ssmall, (H v)⁻¹ ^ m) +
          ∑ v ∈ Slarge, (H v)⁻¹ ^ m := by
    dsimp [Ssmall, Slarge]
    rw [← Finset.sum_filter_add_sum_filter_not S (fun v => H v < 1)]
  have hbR : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have honeLog : 1 ≤ 1 + Real.log (b : ℝ) := by
    linarith [Real.log_nonneg hbR]
  have hcoeff : Csmall + Cshell ≤ Ctotal := by
    dsimp [Ctotal]
    linarith
  have hsmallScale :
      Csmall ≤ Csmall * (1 + Real.log (b : ℝ)) := by
    calc
      Csmall = Csmall * 1 := by ring
      _ ≤ Csmall * (1 + Real.log (b : ℝ)) :=
        mul_le_mul_of_nonneg_left honeLog hCsmall
  change (∑ v ∈ S, (H v)⁻¹ ^ m) ≤
    Ctotal * (1 + Real.log (b : ℝ))
  calc
    (∑ v ∈ S, (H v)⁻¹ ^ m) =
        (∑ v ∈ Ssmall, (H v)⁻¹ ^ m) +
          ∑ v ∈ Slarge, (H v)⁻¹ ^ m := hsplit
    _ ≤ Csmall + Cshell * (1 + Real.log (b : ℝ)) :=
      add_le_add hsmallBound hlargeBound
    _ ≤ Csmall * (1 + Real.log (b : ℝ)) +
        Cshell * (1 + Real.log (b : ℝ)) := by
      exact add_le_add hsmallScale le_rfl
    _ = (Csmall + Cshell) * (1 + Real.log (b : ℝ)) := by ring
    _ ≤ Ctotal * (1 + Real.log (b : ℝ)) :=
      mul_le_mul_of_nonneg_right hcoeff (by linarith)

/- [Lean infrastructure for paper lines 344--358] The manuscript's cutoff
   is the real number `C T`, while the ordinary shells have a natural endpoint.
   This theorem applies the already proved rounding bridge and returns the
   estimate to the exact factor `1 + log T`. -/
theorem ambientIntegralRowModule_finite_norm_inv_pow_sum_le_log
    (m : ℕ) (hdegree : degree K = 1) (Ccut : ℝ) (hCcut : 0 ≤ Ccut) :
    ∃ M : ℝ, 0 < M ∧ ∀ {T : ℝ}, 1 ≤ T →
      ∀ S : Finset (ambientIntegralRowModule (K := K) m),
        (∀ v ∈ S, ‖(v : RowVector K m)‖ ≤ Ccut * T) →
        (∑ v ∈ S, ‖(v : RowVector K m)‖⁻¹ ^ m) ≤
          M * (1 + Real.log T) := by
  obtain ⟨C, hC, hbound⟩ :=
    ambientIntegralRowModule_finite_norm_inv_pow_sum_le_log_at_nat
      (K := K) m hdegree
  let L : ℝ := 1 + Real.log (Ccut + 2) + 1
  have hCtwo : 1 ≤ Ccut + 2 := by linarith
  have hL : 0 < L := by
    dsimp [L]
    have hlog : 0 ≤ Real.log (Ccut + 2) := Real.log_nonneg hCtwo
    linarith
  refine ⟨C * L, mul_pos hC hL, ?_⟩
  intro T hT S hS
  obtain ⟨b, hb, hcut, hround⟩ := exists_nat_shell_cutoff (Ccut * T)
  have hS' : ∀ v ∈ S, ‖(v : RowVector K m)‖ ≤ (b : ℝ) := by
    intro v hv
    exact (hS v hv).trans hcut
  have hnat := hbound hb S hS'
  have hround' :
      1 + Real.log (b : ℝ) ≤ L * (1 + Real.log T) := by
    have h := one_add_log_nat_shell_cutoff_le_scaled
      (C := Ccut) (T := T) (a := 1) (b := b)
      hCcut hT hb (by simpa using hround)
    simpa [L] using h
  calc
    (∑ v ∈ S, ‖(v : RowVector K m)‖⁻¹ ^ m) ≤
        C * (1 + Real.log (b : ℝ)) := hnat
    _ ≤ C * (L * (1 + Real.log T)) :=
      mul_le_mul_of_nonneg_left hround' hC.le
    _ = (C * L) * (1 + Real.log T) := by ring

/- [paper, subsection `ss:log_term`, lines 328--358, and the exceptional
   branch at lines 1716--1724] This is the logarithmic estimate on the
   manuscript's literal one-row set `\mathcal B_1^{(C)}(T)`.  The exact
   bridge through `possibleSuccessiveMinimaNonzeroFinset` removes only the
   zero row, whose totalized radius weight was already proved to vanish. -/
set_option maxHeartbeats 1800000 in
theorem possibleSuccessiveMinimaRadiusWeight_sum_le_of_critical_rank_one
    {m : ℕ} (hm : 0 < m) (hdegree : degree K = 1)
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ M : ℝ, 0 < M ∧ ∀ {T : ℝ}, 1 ≤ T →
      (∑ l ∈ (finite_possibleSuccessiveMinimaSet
        (K := K) (m := m) (k := 1) (C := C) (T := T)).toFinset,
        possibleSuccessiveMinimaRadiusWeight
          (K := K) (m := m) (m + 1) (by omega) l) ≤
        M * (1 + Real.log T) := by
  classical
  obtain ⟨M, hM, hbound⟩ :=
    ambientIntegralRowModule_finite_norm_inv_pow_sum_le_log
      (K := K) m hdegree C hC
  refine ⟨M, hM, ?_⟩
  intro T hT
  let B : Finset (Fin 1 → Fin m → 𝓞 K) :=
    possibleSuccessiveMinimaNonzeroFinset
      (K := K) (m := m) (k := 1) C T
  let e : (Fin 1 → Fin m → 𝓞 K) →
      ambientIntegralRowModule (K := K) m := fun l =>
    ⟨integralVectorEmbedding (K := K) m (l 0),
      integralVectorEmbedding_mem_ambientIntegralRowModule
        (K := K) m (l 0)⟩
  let S : Finset (ambientIntegralRowModule (K := K) m) := B.image e
  have he : Function.Injective e := by
    intro l l' hll'
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    apply integralVectorEmbedding_injective (K := K) m
    exact congrArg Subtype.val hll'
  have hweight (l : Fin 1 → Fin m → 𝓞 K) (hl : l ∈ B) :
      ((∏ i : Fin 1,
        ‖integralVectorEmbedding (K := K) m (l i)‖ ^ degree K)⁻¹) ^
          (m + 1) *
        ‖integralVectorEmbedding (K := K) m (l (Fin.last 0))‖ =
      ‖integralVectorEmbedding (K := K) m (l 0)‖⁻¹ ^ m := by
    have hlFilter : l ∈
        (finite_possibleSuccessiveMinimaSet
          (K := K) (m := m) (k := 1) (C := C) (T := T)).toFinset.filter
            (fun l => ∀ i, l i ≠ 0) := by
      simpa [B, possibleSuccessiveMinimaNonzeroFinset] using hl
    have hlzero : l 0 ≠ 0 := (Finset.mem_filter.mp hlFilter).2 0
    have hembzero : integralVectorEmbedding (K := K) m (l 0) ≠ 0 := by
      intro hz
      apply hlzero
      apply integralVectorEmbedding_injective (K := K) m
      simpa using hz
    have hxne : ‖integralVectorEmbedding (K := K) m (l 0)‖ ≠ 0 :=
      norm_ne_zero_iff.mpr hembzero
    have hprod :
        (∏ i : Fin 1,
          ‖integralVectorEmbedding (K := K) m (l i)‖ ^ degree K) =
          ‖integralVectorEmbedding (K := K) m (l 0)‖ := by
      simp [hdegree]
    have hlast : Fin.last 0 = (0 : Fin 1) := by
      apply Fin.ext
      simp
    rw [hprod, hlast, pow_succ]
    calc
      ‖integralVectorEmbedding (K := K) m (l 0)‖⁻¹ ^ m *
          ‖integralVectorEmbedding (K := K) m (l 0)‖⁻¹ *
            ‖integralVectorEmbedding (K := K) m (l 0)‖ =
          ‖integralVectorEmbedding (K := K) m (l 0)‖⁻¹ ^ m *
            (‖integralVectorEmbedding (K := K) m (l 0)‖⁻¹ *
              ‖integralVectorEmbedding (K := K) m (l 0)‖) := by ring
      _ = ‖integralVectorEmbedding (K := K) m (l 0)‖⁻¹ ^ m := by
        rw [inv_mul_cancel₀ hxne, mul_one]
  have hsum :
      (∑ l ∈ B,
        ((∏ i : Fin 1,
          ‖integralVectorEmbedding (K := K) m (l i)‖ ^ degree K)⁻¹) ^
            (m + 1) *
          ‖integralVectorEmbedding (K := K) m (l (Fin.last 0))‖) =
        ∑ v ∈ S, ‖(v : RowVector K m)‖⁻¹ ^ m := by
    symm
    dsimp [S]
    rw [Finset.sum_image he.injOn]
    apply Finset.sum_congr rfl
    intro l hl
    exact (hweight l hl).symm
  have hSbound : ∀ v ∈ S, ‖(v : RowVector K m)‖ ≤ C * T := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨l, hl, rfl⟩
    have hlFilter : l ∈
        (finite_possibleSuccessiveMinimaSet
          (K := K) (m := m) (k := 1) (C := C) (T := T)).toFinset.filter
            (fun l => ∀ i, l i ≠ 0) := by
      simpa [B, possibleSuccessiveMinimaNonzeroFinset] using hl
    have hlPossible : l ∈ possibleSuccessiveMinimaSet
        (K := K) (m := m) (k := 1) C T :=
      (finite_possibleSuccessiveMinimaSet
        (K := K) (m := m) (k := 1) (C := C) (T := T)).mem_toFinset.mp
          (Finset.mem_filter.mp hlFilter).1
    simpa [e] using hlPossible.2.1 (0 : Fin 1)
  rw [sum_possibleSuccessiveMinimaRadiusWeight_eq_nonzero_product_weight
    (K := K) (m := m) (n := m + 1) (j := 0)
    (by omega) (by omega) C T]
  change (∑ l ∈ B,
    ((∏ i : Fin 1,
      ‖integralVectorEmbedding (K := K) m (l i)‖ ^ degree K)⁻¹) ^
        (m + 1) *
      ‖integralVectorEmbedding (K := K) m (l (Fin.last 0))‖) ≤
    M * (1 + Real.log T)
  rw [hsum]
  exact hbound hT S hSbound

/- [derived consequence of paper equation `eq:just_as_before` and the
   exceptional branch at lines 1716--1724] The logarithmic tuple estimate is
   returned to the manuscript's exact family `\mathcal F_1(T)` through the
   proved minima injection and covering-radius comparison.  The product
   inequality is explicit here so this theorem can also consume any faithfully
   normalized proof of that manuscript input. -/
theorem exists_calF_coveringRadius_sum_bound_of_critical_rank_one
    {m : ℕ} (hm : 0 < m) (hdegree : degree K = 1)
    {Cprod : ℝ} (hCprod : 0 ≤ Cprod) (C : ℝ) (hC : 0 ≤ C) :
    ∃ Cfinite : ℝ, 0 < Cfinite ∧
      ∀ {Csup T : ℝ}
        (hCproj : rowKRealSmulBound (K := K) (m := m) *
          numberFieldCoefficientRadius K ≤ C)
        (hCsup : Csup ≤ C) (hT : 1 ≤ T)
        (_hprod : ∀ D : EchelonMatrix K 1 m,
          D ∈ calF (K := K) (l := 1) (m := m) (n := m + 1) Csup T →
            (∏ i : Fin 1,
              ‖((rowSuccessiveMinimum (echelonRowSpace D) i :
                rowZLattice (echelonRowSpace D)) :
                  rowRealSpan (echelonRowSpace D))‖ ^ degree K) ≤
              Cprod * rowSpaceHeight (echelonRowSpace D)),
        (∑ D ∈ (finite_calF_of_possibleSuccessiveMinima
          (K := K) (m := m) (k := 1) (n := m + 1)
          hCproj hCsup (le_trans zero_le_one hT) (by omega)).toFinset,
          latticeCoveringRadius (rowZLattice (echelonRowSpace D)) /
            (rowSpaceHeight (echelonRowSpace D)) ^ (m + 1)) ≤
          Cfinite * (1 + Real.log T) := by
  obtain ⟨M, hM, htuple⟩ :=
    possibleSuccessiveMinimaRadiusWeight_sum_le_of_critical_rank_one
      (K := K) hm hdegree C hC
  let R : ℝ :=
    (Fintype.card (Σ _ : Fin 1, IntegralBasisIndex K) : ℝ) *
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
      (K := K) (m := m) (k := 1) (n := m + 1)
      hCproj hCsup (le_trans zero_le_one hT) (by omega) hCprod _hprod
  have htupleT := htuple hT
  have hsum' :
      (∑ D ∈ (finite_calF_of_possibleSuccessiveMinima
        (K := K) (m := m) (k := 1) (n := m + 1)
        hCproj hCsup (le_trans zero_le_one hT) (by omega)).toFinset,
        latticeCoveringRadius (rowZLattice (echelonRowSpace D)) /
          (rowSpaceHeight (echelonRowSpace D)) ^ (m + 1)) ≤
        A *
          (∑ l ∈ (finite_possibleSuccessiveMinimaSet
            (K := K) (m := m) (k := 1) (C := C) (T := T)).toFinset,
            possibleSuccessiveMinimaRadiusWeight
              (K := K) (m := m) (m + 1) (by omega) l) := by
    simpa [A, R] using hsum
  have hlog : 1 ≤ 1 + Real.log T := by
    linarith [Real.log_nonneg hT]
  calc
    (∑ D ∈ (finite_calF_of_possibleSuccessiveMinima
      (K := K) (m := m) (k := 1) (n := m + 1)
      hCproj hCsup (le_trans zero_le_one hT) (by omega)).toFinset,
      latticeCoveringRadius (rowZLattice (echelonRowSpace D)) /
        (rowSpaceHeight (echelonRowSpace D)) ^ (m + 1)) ≤
        A *
          (∑ l ∈ (finite_possibleSuccessiveMinimaSet
            (K := K) (m := m) (k := 1) (C := C) (T := T)).toFinset,
            possibleSuccessiveMinimaRadiusWeight
              (K := K) (m := m) (m + 1) (by omega) l) := hsum'
    _ ≤ A * (M * (1 + Real.log T)) :=
      mul_le_mul_of_nonneg_left htupleT hA
    _ = (A * M) * (1 + Real.log T) := by ring
    _ ≤ Cfinite * (1 + Real.log T) := by
      apply mul_le_mul_of_nonneg_right
      · dsimp [Cfinite]
        linarith
      · linarith

/- [derived consequence of the preceding paper-facing theorem and the
   locally proved first-Minkowski rank-one product estimate] This is the
   hypothesis-free rank-one radius-sum interface needed by fixed-rank
   assembly.  It introduces no external cited input. -/
theorem exists_calF_coveringRadius_sum_bound_of_critical_rank_one_of_firstMinkowski
    {m : ℕ} (hm : 0 < m) (hdegree : degree K = 1)
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ Cfinite : ℝ, 0 < Cfinite ∧
      ∀ {Csup T : ℝ}
        (hCproj : rowKRealSmulBound (K := K) (m := m) *
          numberFieldCoefficientRadius K ≤ C)
        (hCsup : Csup ≤ C) (hT : 1 ≤ T),
        (∑ D ∈ (finite_calF_of_possibleSuccessiveMinima
          (K := K) (m := m) (k := 1) (n := m + 1)
          hCproj hCsup (le_trans zero_le_one hT) (by omega)).toFinset,
          latticeCoveringRadius (rowZLattice (echelonRowSpace D)) /
            (rowSpaceHeight (echelonRowSpace D)) ^ (m + 1)) ≤
          Cfinite * (1 + Real.log T) := by
  obtain ⟨Cprod, hCprod, hprod⟩ :=
    exists_rowSuccessiveMinimum_prod_norm_pow_le_rank_one (K := K) m
  obtain ⟨Cfinite, hCfinite, hbound⟩ :=
    exists_calF_coveringRadius_sum_bound_of_critical_rank_one
      (K := K) hm hdegree hCprod.le C hC
  refine ⟨Cfinite, hCfinite, ?_⟩
  intro Csup T hCproj hCsup hT
  apply hbound hCproj hCsup hT
  intro D hD
  exact hprod (echelonRowSpace D)

end Katznelson
