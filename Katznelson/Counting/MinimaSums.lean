import Katznelson.Counting.MinimumInjection
import Katznelson.Counting.Schmidt
import Katznelson.Counting.FiekerStehle

/-!
# The noncritical successive-minima sum

This module formalizes the ordinary nested norm-sum argument in the
noncritical branch of the proof of `th:main`.  In particular, it retains the
unit-shell/Abel-summation route of `le:domain_dimension_bound` rather than
introducing a different decomposition.
-/

namespace Katznelson

open MeasureTheory Set
open scoped Classical NumberField

variable {K : Type*} [Field K] [NumberField K]

/- [Lean infrastructure] `PiLp` carries the Euclidean topology needed for
   the paper's fixed row norm, but its Borel measurable-space instance is not
   inferred through the abbreviation.  Record the canonical Borel structure
   locally for the ambient lattice-count application. -/
noncomputable local instance ambientRowMeasurableSpace (m : ℕ) :
    MeasurableSpace (RowVector K m) := borel (RowVector K m)

local instance ambientRowBorelSpace (m : ℕ) :
    BorelSpace (RowVector K m) := ⟨rfl⟩

/- [derived consequence of paper `le:domain_dimension_bound`, lines
   618--653] The fixed ambient lattice of algebraic-integer rows has the
   polynomial ball-count hypothesis required by the paper's ordinary-shell
   estimate.  This is obtained from the already proved lattice fundamental
   domain count, with its fixed radius absorbed into the constant for
   `T ≥ 1`. -/
theorem ambientIntegralRowModule_norm_ball_count
    (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      (Set.ncard {v : ambientIntegralRowModule (K := K) m |
        ‖(v : RowVector K m)‖ ≤ T} : ℝ) ≤
        C * T ^ (m * degree K) := by
  let L : Submodule ℤ (RowVector K m) :=
    ambientIntegralRowModule (K := K) m
  obtain ⟨Cball, hCball, hball⟩ := lattice_ball_count_uniform
    (L := L) (μHE[Module.finrank ℝ (RowVector K m)])
  let R : ℝ := latticeFundamentalRadius L
  let p : ℕ := m * degree K
  let cov : ℝ := ZLattice.covolume L
    (μHE[Module.finrank ℝ (RowVector K m)])
  have hR : 0 ≤ R := by
    dsimp [R]
    exact latticeFundamentalRadius_nonneg L
  have hcov : 0 < cov := by
    dsimp [cov]
    exact ZLattice.covolume_pos L
      (μHE[Module.finrank ℝ (RowVector K m)])
  refine ⟨Cball * (1 + R) ^ p * cov⁻¹, ?_, ?_⟩
  · have hRp : 0 < (1 + R) ^ p := pow_pos (by linarith) _
    positivity
  · intro T hT
    have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
    have hTR : T + R ≤ (1 + R) * T := by
      have hRT : R ≤ R * T := by
        calc
          R = R * 1 := by ring
          _ ≤ R * T := mul_le_mul_of_nonneg_left hT hR
      calc
        T + R = T + R * 1 := by ring
        _ ≤ T + R * T := by linarith
        _ = (1 + R) * T := by ring
    have hdim : Module.finrank ℝ (RowVector K m) = p := by
      dsimp [p]
      exact rowVector_finrank (K := K) (m := m)
    have hballT := hball hTpos
    change (Set.ncard {v : L | ‖(v : RowVector K m)‖ ≤ T} : ℝ) ≤
      (Cball * (1 + R) ^ p * cov⁻¹) * T ^ p
    calc
      (Set.ncard {v : L | ‖(v : RowVector K m)‖ ≤ T} : ℝ) ≤
          Cball * (T + R) ^ p * cov⁻¹ := by
        simpa [R, cov, hdim] using hballT
      _ ≤ Cball * ((1 + R) * T) ^ p * cov⁻¹ := by
        gcongr
      _ = (Cball * (1 + R) ^ p * cov⁻¹) * T ^ p := by
        rw [mul_pow]
        ring

/- [derived consequence of paper `le:domain_dimension_bound`, lines
   618--653] Group the ambient algebraic-integer rows into the paper's
   ordinary unit norm shells.  Their cumulative cardinality has the required
   degree-`m d` polynomial bound.  This is the exact partial-sum input to the
   Abel estimate below; no dyadic partition is used. -/
set_option maxHeartbeats 1200000 in
theorem ambientIntegralRowModule_norm_shell_partial_sum
    (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ}, 1 ≤ N →
      (∑ i ∈ Finset.Icc 0 N,
        (Set.ncard (heightShell
          (fun v : ambientIntegralRowModule (K := K) m =>
            ‖(v : RowVector K m)‖) i) : ℝ)) ≤
        C * (N : ℝ) ^ (m * degree K) := by
  classical
  obtain ⟨Cball, hCball, hball⟩ :=
    ambientIntegralRowModule_norm_ball_count (K := K) m
  let L : Submodule ℤ (RowVector K m) :=
    ambientIntegralRowModule (K := K) m
  let H : L → ℝ := fun v => ‖(v : RowVector K m)‖
  let p : ℕ := m * degree K
  refine ⟨Cball * (2 : ℝ) ^ p, by positivity, ?_⟩
  intro N hN
  let I : Finset ℕ := Finset.Icc 0 N
  have hfin (i : ℕ) : (heightShell H i).Finite := by
    apply (lattice_ball_finite L).subset
    intro v hv
    change ‖(v : RowVector K m)‖ ≤ ((i + 1 : ℕ) : ℝ)
    exact hv.2.le
  let F : ℕ → Finset L := fun i => (hfin i).toFinset
  let U : Finset L := I.biUnion F
  have hdisj : (I : Set ℕ).PairwiseDisjoint F := by
    intro i hi j hj hne
    change Disjoint (F i) (F j)
    rw [Finset.disjoint_left]
    intro v hvi hvj
    apply Set.disjoint_left.1 (heightShell_disjoint hne)
    · exact (hfin i).mem_toFinset.mp hvi
    · exact (hfin j).mem_toFinset.mp hvj
  have hcardU : U.card = ∑ i ∈ I, (F i).card := by
    simpa [U] using (Finset.card_biUnion (s := I) hdisj)
  have hsum :
      (∑ i ∈ I, (Set.ncard (heightShell H i) : ℝ)) = (U.card : ℝ) := by
    calc
      (∑ i ∈ I, (Set.ncard (heightShell H i) : ℝ)) =
          ∑ i ∈ I, ((F i).card : ℝ) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact_mod_cast Set.ncard_eq_toFinset_card (heightShell H i) (hfin i)
      _ = (U.card : ℝ) := by exact_mod_cast hcardU.symm
  have hUsub : (U : Set L) ⊆ {v : L |
      ‖(v : RowVector K m)‖ ≤ ((N + 1 : ℕ) : ℝ)} := by
    intro v hv
    simp only [U, Finset.mem_coe, Finset.mem_biUnion] at hv
    obtain ⟨i, hi, hvi⟩ := hv
    have hvi' := (hfin i).mem_toFinset.mp hvi
    have hiN : i ≤ N := (Finset.mem_Icc.mp hi).2
    change ‖(v : RowVector K m)‖ ≤ ((N + 1 : ℕ) : ℝ)
    exact (lt_of_lt_of_le hvi'.2 (by
      exact_mod_cast Nat.succ_le_succ hiN)).le
  have hballfinite : {v : L |
      ‖(v : RowVector K m)‖ ≤ ((N + 1 : ℕ) : ℝ)}.Finite := by
    exact lattice_ball_finite L
  have hUcard : (U.card : ℝ) ≤ Cball * ((N + 1 : ℕ) ^ p : ℝ) := by
    have hNplus : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ N + 1)
    have hballN := hball ((N + 1 : ℕ) : ℝ) hNplus
    calc
      (U.card : ℝ) ≤ (Set.ncard {v : L |
          ‖(v : RowVector K m)‖ ≤ ((N + 1 : ℕ) : ℝ)} : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard hUsub hballfinite
      _ ≤ Cball * ((N + 1 : ℕ) ^ p : ℝ) := by
        simpa [L, p] using hballN
  have hstep : ((N + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
    have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    rw [Nat.cast_add, Nat.cast_one]
    nlinarith
  have hpow : ((N + 1 : ℕ) ^ p : ℝ) ≤ (2 * (N : ℝ)) ^ p := by
    exact pow_le_pow_left₀ (by positivity) hstep p
  calc
    (∑ i ∈ Finset.Icc 0 N,
      (Set.ncard (heightShell
        (fun v : ambientIntegralRowModule (K := K) m =>
          ‖(v : RowVector K m)‖) i) : ℝ)) =
        ∑ i ∈ I, (Set.ncard (heightShell H i) : ℝ) := by rfl
    _ = (U.card : ℝ) := hsum
    _ ≤ Cball * ((N + 1 : ℕ) ^ p : ℝ) := hUcard
    _ ≤ Cball * (2 * (N : ℝ)) ^ p := by
      exact mul_le_mul_of_nonneg_left hpow hCball.le
    _ = (Cball * (2 : ℝ) ^ p) * (N : ℝ) ^ p := by
      rw [mul_pow]
      ring

/- [paper, proof of `le:lower_bound_not_in_F`, lines 1142--1143] The
   manuscript's constant `c^{minnorm}` is the norm of a shortest nonzero
   vector of the fixed ambient lattice `\mathcal O_K^m`.  It gives the stated
   positive lower bound for every nonzero integral row, independently of a
   varying row space. -/
theorem exists_ambientIntegralRowModule_norm_lower_bound
    (m : ℕ) (hm : 0 < m) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v : ambientIntegralRowModule (K := K) m,
      v ≠ 0 → δ ≤ ‖(v : RowVector K m)‖ := by
  letI : Nontrivial (RowVector K m) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    rw [rowVector_finrank]
    exact Nat.mul_pos hm Module.finrank_pos
  obtain ⟨v₀, hv₀, hvmin⟩ :=
    exists_shortest_nonzero_latticeVector
      (ambientIntegralRowModule (K := K) m)
  have hv₀' : (v₀ : RowVector K m) ≠ 0 := by
    intro h
    apply hv₀
    exact Subtype.ext h
  refine ⟨‖(v₀ : RowVector K m)‖, norm_pos_iff.mpr hv₀', ?_⟩
  intro v hv
  exact hvmin v hv

/- [derived consequence of paper `le:domain_dimension_bound`, lines
   1745--1750] The ordinary unit-shell Abel estimate applied to the ambient
   algebraic-integer row lattice.  This is the quantitative form of the
   paper's innermost tail input: its exponent is the ambient dimension
   `m * d`, and the hypothesis is exactly that the reciprocal-norm exponent
   lies strictly above it. -/
theorem ambientIntegralRowModule_norm_shell_tsum_tail
    {m q : ℕ} (hgap : m * degree K < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ}, 1 ≤ N →
      (∑' i : ℕ, if N ≤ i then
        (Set.ncard (heightShell
          (fun v : ambientIntegralRowModule (K := K) m =>
            ‖(v : RowVector K m)‖) i) : ℝ) * ((i : ℝ)⁻¹ ^ q) else 0) ≤
        C * ((N : ℝ) ^ (-((q - m * degree K : ℕ) : ℝ))) := by
  obtain ⟨C, hC, hpartial⟩ :=
    ambientIntegralRowModule_norm_shell_partial_sum (K := K) m
  let p : ℕ := m * degree K
  have hpq : p < q := by simpa [p] using hgap
  have hpqle : p ≤ q := Nat.le_of_lt hpq
  let Ctail : ℝ := C * (2 + (q : ℝ) / ((q : ℝ) - (p : ℝ)))
  refine ⟨Ctail, ?_, ?_⟩
  · dsimp [Ctail]
    have hqmpR : (0 : ℝ) < (q : ℝ) - (p : ℝ) := by
      rw [← Nat.cast_sub hpqle]
      exact_mod_cast (Nat.sub_pos_of_lt hpq)
    positivity
  · intro N hN
    dsimp [Ctail]
    simpa [p] using
      (tsum_indicator_Ici_inv_pow_le_of_partial_sum
        (φ := fun i : ℕ =>
          (Set.ncard (heightShell
            (fun v : ambientIntegralRowModule (K := K) m =>
              ‖(v : RowVector K m)‖) i) : ℝ))
        (C := C) (N := N) (p := p) (q := q)
        hC hN hpq
        (fun i => by positivity)
        (fun {i} hi => by simpa [p] using hpartial hi))

/- [derived consequence of paper `le:domain_dimension_bound`, lines
   1745--1750] Finite endpoint form of the ambient ordinary-shell tail.  The
   manuscript first bounds a finite innermost sum and then lets its upper
   cutoff be harmless; this declaration is that finite form, with both shell
   endpoints retained. -/
theorem ambientIntegralRowModule_norm_shell_sum_Icc_tail
    {m q : ℕ} (hgap : m * degree K < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ {N b : ℕ}, 1 ≤ N → N ≤ b →
      (∑ i ∈ Finset.Icc N b,
        (Set.ncard (heightShell
          (fun v : ambientIntegralRowModule (K := K) m =>
            ‖(v : RowVector K m)‖) i) : ℝ) * ((i : ℝ)⁻¹ ^ q)) ≤
        C * ((N : ℝ) ^ (-((q - m * degree K : ℕ) : ℝ))) := by
  obtain ⟨C, hC, hpartial⟩ :=
    ambientIntegralRowModule_norm_shell_partial_sum (K := K) m
  let p : ℕ := m * degree K
  have hpq : p < q := by simpa [p] using hgap
  let Ctail : ℝ := C * (2 + (q : ℝ) / ((q : ℝ) - (p : ℝ)))
  refine ⟨Ctail, ?_, ?_⟩
  · dsimp [Ctail]
    have hqmpR : (0 : ℝ) < (q : ℝ) - (p : ℝ) := by
      rw [← Nat.cast_sub (Nat.le_of_lt hpq)]
      exact_mod_cast (Nat.sub_pos_of_lt hpq)
    positivity
  · intro N b hN hNb
    have hphiN :
        (Set.ncard (heightShell
          (fun v : ambientIntegralRowModule (K := K) m =>
            ‖(v : RowVector K m)‖) N) : ℝ) ≤ C * (N : ℝ) ^ p := by
      calc
        (Set.ncard (heightShell
          (fun v : ambientIntegralRowModule (K := K) m =>
            ‖(v : RowVector K m)‖) N) : ℝ) =
            ∑ i ∈ ({N} : Finset ℕ),
              (Set.ncard (heightShell
                (fun v : ambientIntegralRowModule (K := K) m =>
                  ‖(v : RowVector K m)‖) i) : ℝ) := by simp
        _ ≤ ∑ i ∈ Finset.Icc 0 N,
            (Set.ncard (heightShell
              (fun v : ambientIntegralRowModule (K := K) m =>
                ‖(v : RowVector K m)‖) i) : ℝ) := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro i hi
                simp only [Finset.mem_singleton] at hi
                subst i
                simp
              · intro i hi hnot
                positivity
        _ ≤ C * (N : ℝ) ^ p := by
          simpa [p] using hpartial hN
    have hNpos : (0 : ℝ) < N := by
      exact_mod_cast (show 0 < N by omega)
    have htermN_eq :
        (N : ℝ) ^ p * ((N : ℝ)⁻¹ ^ q) =
          (N : ℝ) ^ (-((q - p : ℕ) : ℝ)) := by
      rw [← Real.rpow_natCast (N : ℝ) p,
        ← Real.rpow_natCast ((N : ℝ)⁻¹) q,
        Real.inv_rpow hNpos.le, ← Real.rpow_neg hNpos.le,
        ← Real.rpow_add hNpos]
      congr 1
      rw [Nat.cast_sub (Nat.le_of_lt hpq)]
      ring
    have htermN :
        (Set.ncard (heightShell
          (fun v : ambientIntegralRowModule (K := K) m =>
            ‖(v : RowVector K m)‖) N) : ℝ) * ((N : ℝ)⁻¹ ^ q) ≤
          C * ((N : ℝ) ^ (-((q - p : ℕ) : ℝ))) := by
      calc
        (Set.ncard (heightShell
          (fun v : ambientIntegralRowModule (K := K) m =>
            ‖(v : RowVector K m)‖) N) : ℝ) * ((N : ℝ)⁻¹ ^ q) ≤
            (C * (N : ℝ) ^ p) * ((N : ℝ)⁻¹ ^ q) := by
              gcongr
        _ = C * ((N : ℝ) ^ p * ((N : ℝ)⁻¹ ^ q)) := by ring
        _ = C * ((N : ℝ) ^ (-((q - p : ℕ) : ℝ))) := by rw [htermN_eq]
    have hIoc := sum_Ioc_inv_pow_tail_le_of_partial_sum
      (φ := fun i : ℕ =>
        (Set.ncard (heightShell
          (fun v : ambientIntegralRowModule (K := K) m =>
            ‖(v : RowVector K m)‖) i) : ℝ))
      (C := C) (N := N) (b := b) (p := p) (q := q)
      hC hN hNb hpq
      (fun i => by positivity)
      (fun {i} hi => by simpa [p] using hpartial hi)
    dsimp [Ctail]
    calc
      (∑ i ∈ Finset.Icc N b,
        (Set.ncard (heightShell
          (fun v : ambientIntegralRowModule (K := K) m =>
            ‖(v : RowVector K m)‖) i) : ℝ) * ((i : ℝ)⁻¹ ^ q)) =
          (Set.ncard (heightShell
            (fun v : ambientIntegralRowModule (K := K) m =>
              ‖(v : RowVector K m)‖) N) : ℝ) * ((N : ℝ)⁻¹ ^ q) +
            ∑ i ∈ Finset.Ioc N b,
              (Set.ncard (heightShell
                (fun v : ambientIntegralRowModule (K := K) m =>
                  ‖(v : RowVector K m)‖) i) : ℝ) * ((i : ℝ)⁻¹ ^ q) := by
            exact (Finset.add_sum_Ioc_eq_sum_Icc hNb).symm
      _ ≤ C * ((N : ℝ) ^ (-((q - p : ℕ) : ℝ))) +
            C * (1 + (q : ℝ) / ((q : ℝ) - (p : ℝ))) *
              ((N : ℝ) ^ (-((q - p : ℕ) : ℝ))) :=
          add_le_add htermN hIoc
      _ = C * (2 + (q : ℝ) / ((q : ℝ) - (p : ℝ))) *
            ((N : ℝ) ^ (-((q - p : ℕ) : ℝ))) := by ring
      _ = Ctail * ((N : ℝ) ^ (-((q - m * degree K : ℕ) : ℝ))) := by
            simp [Ctail, p]

/- [derived consequence of paper `le:domain_dimension_bound`, lines
   1745--1750] A finite family of ambient integral rows above an integral
   norm threshold obeys the same ordinary-shell tail bound.  This is the
   finite nested-sum form needed for the paper's displayed sum over
   `\mathcal B_k(T)`: the proof partitions only the given finite family into
   the manuscript's unit norm shells. -/
set_option maxHeartbeats 1800000 in
theorem ambientIntegralRowModule_finite_norm_tail_at_nat
    {m q : ℕ} (hgap : m * degree K < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ}, 1 ≤ N →
      ∀ S : Finset (ambientIntegralRowModule (K := K) m),
        (∀ v ∈ S, (N : ℝ) ≤ ‖(v : RowVector K m)‖) →
        (∑ v ∈ S, ‖(v : RowVector K m)‖⁻¹ ^ q) ≤
          C * ((N : ℝ) ^ (-((q - m * degree K : ℕ) : ℝ))) := by
  classical
  obtain ⟨C, hC, hshell⟩ :=
    ambientIntegralRowModule_norm_shell_sum_Icc_tail (K := K) hgap
  refine ⟨C, hC, ?_⟩
  intro N hN S hS
  let H : ambientIntegralRowModule (K := K) m → ℝ := fun v =>
    ‖(v : RowVector K m)‖
  change (∑ v ∈ S, (H v)⁻¹ ^ q) ≤
    C * ((N : ℝ) ^ (-((q - m * degree K : ℕ) : ℝ)))
  have hHnonneg (v : ambientIntegralRowModule (K := K) m) : 0 ≤ H v := by
    dsimp [H]
    positivity
  by_cases hSnonempty : S.Nonempty
  · let index : ambientIntegralRowModule (K := K) m → ℕ := fun v => ⌊H v⌋₊
    have hindex_image : (S.image index).Nonempty := hSnonempty.image index
    let b : ℕ := (S.image index).max' hindex_image
    have hindex_mem_shell (v : ambientIntegralRowModule (K := K) m) :
        v ∈ heightShell H (index v) := by
      constructor
      · dsimp [index]
        exact Nat.floor_le (hHnonneg v)
      · dsimp [index]
        simpa [Nat.cast_add_one] using Nat.lt_floor_add_one (H v)
    have hNindex (v : ambientIntegralRowModule (K := K) m) (hv : v ∈ S) :
        N ≤ index v := by
      by_contra hnot
      have hlt : index v < N := Nat.lt_of_not_ge hnot
      have hstep : ((index v + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt hlt
      have hvN : (N : ℝ) ≤ H v := by
        simpa [H] using hS v hv
      exact (not_lt_of_ge hvN)
        (lt_of_lt_of_le (hindex_mem_shell v).2 hstep)
    have hNb : N ≤ b := by
      obtain ⟨v, hv⟩ := hSnonempty
      have hvimage : index v ∈ S.image index :=
        Finset.mem_image.mpr ⟨v, hv, rfl⟩
      exact (hNindex v hv).trans
        (Finset.le_max' (S.image index) (index v) hvimage)
    let I : Finset ℕ := Finset.Icc N b
    let F : ℕ → Finset (ambientIntegralRowModule (K := K) m) := fun i =>
      S.filter (fun v => v ∈ heightShell H i)
    let U : Finset (ambientIntegralRowModule (K := K) m) := I.biUnion F
    have hdisj : (I : Set ℕ).PairwiseDisjoint F := by
      intro i hi j hj hne
      change Disjoint (F i) (F j)
      rw [Finset.disjoint_left]
      intro v hvi hvj
      apply Set.disjoint_left.1 (heightShell_disjoint hne)
      · exact (Finset.mem_filter.mp hvi).2
      · exact (Finset.mem_filter.mp hvj).2
    have hU : U = S := by
      apply Finset.Subset.antisymm
      · intro v hv
        simp only [U, Finset.mem_biUnion] at hv
        obtain ⟨i, hi, hvi⟩ := hv
        exact (Finset.mem_filter.mp hvi).1
      · intro v hv
        have hvindex : index v ∈ S.image index :=
          Finset.mem_image.mpr ⟨v, hv, rfl⟩
        have hib : index v ≤ b :=
          Finset.le_max' (S.image index) (index v) hvindex
        exact Finset.mem_biUnion.mpr ⟨index v,
          Finset.mem_Icc.mpr ⟨hNindex v hv, hib⟩,
          Finset.mem_filter.mpr ⟨hv, hindex_mem_shell v⟩⟩
    have hsumU :
        (∑ v ∈ U, (H v)⁻¹ ^ q) =
          ∑ i ∈ I, ∑ v ∈ F i, (H v)⁻¹ ^ q := by
      simpa [U] using
        (Finset.sum_biUnion (s := I) (t := F) hdisj
          (f := fun v : ambientIntegralRowModule (K := K) m =>
            (H v)⁻¹ ^ q))
    have hfin_shell (i : ℕ) : (heightShell H i).Finite := by
      apply (lattice_ball_finite (ambientIntegralRowModule (K := K) m)).subset
      intro v hv
      simpa [H] using hv.2.le
    have hFsum (i : ℕ) (hi : i ∈ I) :
        (∑ v ∈ F i, (H v)⁻¹ ^ q) ≤
          (Set.ncard (heightShell H i) : ℝ) * ((i : ℝ)⁻¹ ^ q) := by
      have hNi : N ≤ i := (Finset.mem_Icc.mp hi).1
      have hipos : 0 < i := by omega
      have hFsub : F i ⊆ (hfin_shell i).toFinset := by
        intro v hv
        exact (hfin_shell i).mem_toFinset.mpr
          (Finset.mem_filter.mp hv).2
      have hcard : ((F i).card : ℝ) ≤
          (Set.ncard (heightShell H i) : ℝ) := by
        calc
          ((F i).card : ℝ) ≤ ((hfin_shell i).toFinset.card : ℝ) := by
            exact_mod_cast Finset.card_le_card hFsub
          _ = (Set.ncard (heightShell H i) : ℝ) := by
            exact_mod_cast (Set.ncard_eq_toFinset_card
              (heightShell H i) (hfin_shell i)).symm
      calc
        (∑ v ∈ F i, (H v)⁻¹ ^ q) ≤
            ∑ v ∈ F i, ((i : ℝ)⁻¹ ^ q) := by
              apply Finset.sum_le_sum
              intro v hv
              exact heightShell_inv_pow_le hipos
                (Finset.mem_filter.mp hv).2
        _ = ((F i).card : ℝ) * ((i : ℝ)⁻¹ ^ q) := by
          simp [Finset.sum_const]
        _ ≤ (Set.ncard (heightShell H i) : ℝ) * ((i : ℝ)⁻¹ ^ q) := by
          exact mul_le_mul_of_nonneg_right hcard (by positivity)
    calc
      (∑ v ∈ S, (H v)⁻¹ ^ q) = ∑ v ∈ U, (H v)⁻¹ ^ q := by rw [hU]
      _ = ∑ i ∈ I, ∑ v ∈ F i, (H v)⁻¹ ^ q := hsumU
      _ ≤ ∑ i ∈ I,
          (Set.ncard (heightShell H i) : ℝ) * ((i : ℝ)⁻¹ ^ q) := by
            apply Finset.sum_le_sum
            intro i hi
            exact hFsum i hi
      _ ≤ C * ((N : ℝ) ^ (-((q - m * degree K : ℕ) : ℝ))) := by
        simpa [I, H] using hshell hN hNb
  · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSnonempty
    rw [hSempty]
    simp only [Finset.sum_empty]
    exact mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _)

/- [derived consequence of paper `le:domain_dimension_bound`, lines
   1745--1750] The same finite ambient-row tail with the paper's actual real
   lower cutoff, provided that cutoff is at least one.  Passing from a real
   cutoff to its floor changes only the fixed constant; the proof retains the
   ordinary unit shells and does not introduce a different decomposition. -/
theorem ambientIntegralRowModule_finite_norm_tail_of_one_le
    {m q : ℕ} (hgap : m * degree K < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ {r : ℝ}, 1 ≤ r →
      ∀ S : Finset (ambientIntegralRowModule (K := K) m),
        (∀ v ∈ S, r ≤ ‖(v : RowVector K m)‖) →
        (∑ v ∈ S, ‖(v : RowVector K m)‖⁻¹ ^ q) ≤
          C * (r ^ (-((q - m * degree K : ℕ) : ℝ))) := by
  obtain ⟨C, hC, htail⟩ :=
    ambientIntegralRowModule_finite_norm_tail_at_nat (K := K) hgap
  let p : ℕ := m * degree K
  have hpq : p < q := by simpa [p] using hgap
  let d : ℕ := q - p
  let Ctail : ℝ := C * ((2 : ℝ) ^ (d : ℝ))
  refine ⟨Ctail, ?_, ?_⟩
  · dsimp [Ctail]
    positivity
  · intro r hr S hS
    let N : ℕ := ⌊r⌋₊
    have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
    have hN : 1 ≤ N := by
      dsimp [N]
      exact Nat.one_le_floor_iff r |>.2 hr
    have hNpos : (0 : ℝ) < N := by
      exact_mod_cast (show 0 < N by omega)
    have hfloor : (N : ℝ) ≤ r := by
      dsimp [N]
      exact Nat.floor_le hrpos.le
    have hSN : ∀ v ∈ S, (N : ℝ) ≤ ‖(v : RowVector K m)‖ := by
      intro v hv
      exact hfloor.trans (hS v hv)
    have hmain := htail hN S hSN
    have hrlt : r < ((N + 1 : ℕ) : ℝ) := by
      dsimp [N]
      simpa [Nat.cast_add_one] using Nat.lt_floor_add_one r
    have hNstep : ((N + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
      have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      rw [Nat.cast_add, Nat.cast_one]
      nlinarith
    have hrle : r ≤ 2 * (N : ℝ) := hrlt.le.trans hNstep
    have hhalf : r / 2 ≤ (N : ℝ) := by linarith
    have hhalfpos : 0 < r / 2 := by positivity
    have hdpos : 0 < d := by
      dsimp [d]
      exact Nat.sub_pos_of_lt hpq
    have hneg : -((d : ℕ) : ℝ) < 0 := by
      exact neg_lt_zero.mpr (by exact_mod_cast hdpos)
    have hmon :
        (N : ℝ) ^ (-((d : ℕ) : ℝ)) ≤
          (r / 2) ^ (-((d : ℕ) : ℝ)) := by
      exact (Real.rpow_le_rpow_iff_of_neg hNpos hhalfpos hneg).2 hhalf
    have hscale :
        (r / 2) ^ (-((d : ℕ) : ℝ)) =
          (2 : ℝ) ^ (d : ℝ) * r ^ (-((d : ℕ) : ℝ)) := by
      rw [Real.div_rpow hrpos.le (by positivity)]
      rw [Real.rpow_neg (by positivity : 0 ≤ r),
        Real.rpow_neg (by positivity : 0 ≤ (2 : ℝ))]
      simp only [div_eq_mul_inv, inv_inv]
      ring
    have hscaled :
        (N : ℝ) ^ (-((d : ℕ) : ℝ)) ≤
          (2 : ℝ) ^ (d : ℝ) * r ^ (-((d : ℕ) : ℝ)) :=
      hmon.trans_eq hscale
    change (∑ v ∈ S, ‖(v : RowVector K m)‖⁻¹ ^ q) ≤
      Ctail * (r ^ (-((q - m * degree K : ℕ) : ℝ)))
    calc
      (∑ v ∈ S, ‖(v : RowVector K m)‖⁻¹ ^ q) ≤
          C * ((N : ℝ) ^ (-((q - m * degree K : ℕ) : ℝ))) := hmain
      _ ≤ C * ((2 : ℝ) ^ (d : ℝ) * r ^ (-((d : ℕ) : ℝ))) := by
        apply mul_le_mul_of_nonneg_left
        simpa [d, p] using hscaled
        exact hC.le
      _ = Ctail * (r ^ (-((q - m * degree K : ℕ) : ℝ))) := by
        simp [Ctail, d, p]
        ring

/- [derived consequence of paper `le:domain_dimension_bound`, lines
   1745--1750, together with `c^{minnorm}` at lines 1142--1143] The ambient
   integral-row tail at every positive real lower cutoff.  The finitely many
   rows of norm below one are controlled using the paper's fixed positive
   minimum norm; above one this is exactly the preceding ordinary-shell
   estimate. -/
set_option maxHeartbeats 2400000 in
theorem ambientIntegralRowModule_finite_norm_tail
    {m q : ℕ} (hm : 0 < m) (hgap : m * degree K < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ {r : ℝ}, 0 < r →
      ∀ S : Finset (ambientIntegralRowModule (K := K) m),
        (∀ v ∈ S, r ≤ ‖(v : RowVector K m)‖) →
        (∑ v ∈ S, ‖(v : RowVector K m)‖⁻¹ ^ q) ≤
          C * (r ^ (-((q - m * degree K : ℕ) : ℝ))) := by
  classical
  obtain ⟨δ, hδ, hmin⟩ :=
    exists_ambientIntegralRowModule_norm_lower_bound (K := K) m hm
  obtain ⟨C₁, hC₁, htail⟩ :=
    ambientIntegralRowModule_finite_norm_tail_of_one_le (K := K) hgap
  let H : ambientIntegralRowModule (K := K) m → ℝ := fun v =>
    ‖(v : RowVector K m)‖
  let smallSet : Set (ambientIntegralRowModule (K := K) m) :=
    {v | v ≠ 0 ∧ H v < 1}
  have hsmallfinite : smallSet.Finite := by
    apply (lattice_ball_finite (ambientIntegralRowModule (K := K) m)).subset
    intro v hv
    simpa [smallSet, H] using hv.2.le
  let small : Finset (ambientIntegralRowModule (K := K) m) :=
    hsmallfinite.toFinset
  let Csmall : ℝ := (small.card : ℝ) * (δ⁻¹ ^ q)
  let Ctail : ℝ := Csmall + C₁
  have hCsmall : 0 ≤ Csmall := by
    dsimp [Csmall]
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (inv_nonneg.mpr hδ.le) _)
  have hCtail : 0 < Ctail := by
    dsimp [Ctail]
    linarith
  refine ⟨Ctail, hCtail, ?_⟩
  intro r hr S hS
  change (∑ v ∈ S, (H v)⁻¹ ^ q) ≤
    Ctail * (r ^ (-((q - m * degree K : ℕ) : ℝ)))
  by_cases hrone : 1 ≤ r
  · have hmain := htail hrone S (by
      intro v hv
      simpa [H] using hS v hv)
    have hpow_nonneg : 0 ≤ r ^ (-((q - m * degree K : ℕ) : ℝ)) := by
      positivity
    calc
      (∑ v ∈ S, (H v)⁻¹ ^ q) ≤
          C₁ * (r ^ (-((q - m * degree K : ℕ) : ℝ))) := by
            simpa [H] using hmain
      _ ≤ Ctail * (r ^ (-((q - m * degree K : ℕ) : ℝ))) := by
            apply mul_le_mul_of_nonneg_right
            dsimp [Ctail]
            linarith
            exact hpow_nonneg
  · have hrlt : r < 1 := lt_of_not_ge hrone
    have hrle : r ≤ 1 := hrlt.le
    let Ssmall : Finset (ambientIntegralRowModule (K := K) m) :=
      S.filter (fun v => H v < 1)
    let Slarge : Finset (ambientIntegralRowModule (K := K) m) :=
      S.filter (fun v => ¬ H v < 1)
    have hsmallsub : Ssmall ⊆ small := by
      intro v hv
      have hv' := Finset.mem_filter.mp hv
      apply hsmallfinite.mem_toFinset.mpr
      refine ⟨?_, hv'.2⟩
      have hvpos : 0 < H v := lt_of_lt_of_le hr (by
        simpa [H] using hS v hv'.1)
      intro hvzero
      have hzero : H v = 0 := by
        rw [hvzero]
        simp [H]
      exact (ne_of_gt hvpos) hzero
    have hsmallpoint (v : ambientIntegralRowModule (K := K) m)
        (hv : v ∈ Ssmall) :
        (H v)⁻¹ ^ q ≤ δ⁻¹ ^ q := by
      have hv' := Finset.mem_filter.mp hv
      have hvpos : 0 < H v := lt_of_lt_of_le hr (by
        simpa [H] using hS v hv'.1)
      have hvne : v ≠ 0 := by
        intro hvzero
        have hzero : H v = 0 := by
          rw [hvzero]
          simp [H]
        exact (ne_of_gt hvpos) hzero
      have hinv : (H v)⁻¹ ≤ δ⁻¹ :=
        (inv_le_inv₀ hvpos hδ).2 (hmin v hvne)
      exact pow_le_pow_left₀ (inv_nonneg.mpr hvpos.le) hinv q
    have hsmallbound :
        (∑ v ∈ Ssmall, (H v)⁻¹ ^ q) ≤ Csmall := by
      have hcard : ((Ssmall.card : ℕ) : ℝ) ≤ (small.card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsmallsub
      calc
        (∑ v ∈ Ssmall, (H v)⁻¹ ^ q) ≤
            ∑ v ∈ Ssmall, δ⁻¹ ^ q := by
              apply Finset.sum_le_sum
              intro v hv
              exact hsmallpoint v hv
        _ = (Ssmall.card : ℝ) * (δ⁻¹ ^ q) := by
          simp [Finset.sum_const]
        _ ≤ (small.card : ℝ) * (δ⁻¹ ^ q) := by
          exact mul_le_mul_of_nonneg_right hcard
            (pow_nonneg (inv_nonneg.mpr hδ.le) _)
        _ = Csmall := rfl
    have hlarge (v : ambientIntegralRowModule (K := K) m)
        (hv : v ∈ Slarge) : (1 : ℝ) ≤ H v :=
      le_of_not_gt (Finset.mem_filter.mp hv).2
    have hlargebound :
        (∑ v ∈ Slarge, (H v)⁻¹ ^ q) ≤ C₁ := by
      have h := htail (r := (1 : ℝ)) le_rfl Slarge (by
        intro v hv
        simpa [H] using hlarge v hv)
      simpa [H] using h
    have hsplit :
        (∑ v ∈ S, (H v)⁻¹ ^ q) =
          (∑ v ∈ Ssmall, (H v)⁻¹ ^ q) +
            ∑ v ∈ Slarge, (H v)⁻¹ ^ q := by
      dsimp [Ssmall, Slarge]
      rw [← Finset.sum_filter_add_sum_filter_not
        S (fun v => H v < 1)]
    have hpower : 1 ≤ r ^ (-((q - m * degree K : ℕ) : ℝ)) := by
      apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hrle
      exact neg_nonpos.mpr (Nat.cast_nonneg _)
    calc
      (∑ v ∈ S, (H v)⁻¹ ^ q) =
          (∑ v ∈ Ssmall, (H v)⁻¹ ^ q) +
            ∑ v ∈ Slarge, (H v)⁻¹ ^ q := hsplit
      _ ≤ Csmall + C₁ := add_le_add hsmallbound hlargebound
      _ = Ctail * 1 := by
        dsimp [Ctail]
        ring
      _ ≤ Ctail * (r ^ (-((q - m * degree K : ℕ) : ℝ))) := by
        exact mul_le_mul_of_nonneg_left hpower hCtail.le

/- [Lean infrastructure for paper lines 1743--1753] The nested finite sum
   written in the order used by the manuscript: there are `j` preceding rows
   of reciprocal exponent `a`, followed by the final row of exponent `q`.
   The real argument is the lower norm cutoff on the first row. -/
noncomputable def orderedNormNestedSum {α : Type*}
    (S : Finset α) (H : α → ℝ) (a q : ℕ) : ℕ → ℝ → ℝ
  | 0, r => ∑ v ∈ S.filter (fun v => r ≤ H v), (H v)⁻¹ ^ q
  | j + 1, r => ∑ v ∈ S.filter (fun v => r ≤ H v),
      (H v)⁻¹ ^ a * orderedNormNestedSum S H a q j (H v)

/- [Lean infrastructure for paper lines 1745--1753] The exponent remaining
   after each application of the manuscript's innermost tail estimate. -/
def orderedNormNestedTailExponent (p a q : ℕ) : ℕ → ℕ
  | 0 => q - p
  | j + 1 => a + orderedNormNestedTailExponent p a q j - p

/- [Lean infrastructure for paper lines 1741--1753] The literal weight of an
ordered tuple in the relaxed sum: all but its final row have exponent `a`,
and its final row has exponent `q`.  The recursive presentation matches the
nesting order of `orderedNormNestedSum`. -/
noncomputable def orderedNormTupleWeight {α : Type*}
    (H : α → ℝ) (a q : ℕ) :
    ∀ {j : ℕ}, (Fin (j + 1) → α) → ℝ
  | 0, l => (H (l 0))⁻¹ ^ q
  | j + 1, l => (H (l 0))⁻¹ ^ a *
      orderedNormTupleWeight H a q (Fin.tail l)

/- [Lean infrastructure for paper lines 1741--1753] Reindexing the rows of
an ordered tuple through an embedding commutes with its recursive weight. -/
theorem orderedNormTupleWeight_map
    {α β : Type*} (H : β → ℝ) (f : α → β) (a q : ℕ) :
    ∀ {j : ℕ} (l : Fin (j + 1) → α),
      orderedNormTupleWeight H a q (fun i => f (l i)) =
        orderedNormTupleWeight (fun x => H (f x)) a q l := by
  intro j
  induction j with
  | zero =>
      intro l
      rfl
  | succ j ih =>
      intro l
      change (H (f (l 0)))⁻¹ ^ a *
          orderedNormTupleWeight H a q (Fin.tail (fun i => f (l i))) =
        (H (f (l 0)))⁻¹ ^ a *
          orderedNormTupleWeight (fun x => H (f x)) a q (Fin.tail l)
      rw [show Fin.tail (fun i => f (l i)) =
        fun i => f ((Fin.tail l) i) by rfl]
      rw [ih]

/- [Lean infrastructure for paper lines 1741--1753] Membership in the
finite ordered tuple family used after the manuscript drops the projection
conditions: every coordinate belongs to the finite row family, the first
norm is at least `r`, and consecutive norms are nondecreasing. -/
def orderedNormTupleCondition {α : Type*}
    (S : Finset α) (H : α → ℝ) (r : ℝ) {j : ℕ}
    (l : Fin (j + 1) → α) : Prop :=
  (∀ i, l i ∈ S) ∧ r ≤ H (l 0) ∧
    ∀ i : Fin j, H (l i.castSucc) ≤ H (l i.succ)

/- [derived consequence of paper `le:domain_dimension_bound`, lines
   1741--1753] A finite family of the manuscript's ordered tuples is bounded
by the recursively written nested sum.  This is the explicit bridge from the
displayed tuple sum to `orderedNormNestedSum`; it introduces no replacement
summation argument. -/
theorem sum_orderedNormTupleWeight_le_orderedNormNestedSum
    {α : Type*} (S : Finset α) (H : α → ℝ) (a q : ℕ)
    (hHnonneg : ∀ x ∈ S, 0 ≤ H x) :
    ∀ {j : ℕ} {r : ℝ} (B : Finset (Fin (j + 1) → α)),
      (∀ l ∈ B, orderedNormTupleCondition S H r l) →
      (∑ l ∈ B, orderedNormTupleWeight H a q l) ≤
        orderedNormNestedSum S H a q j r := by
  classical
  intro j r B hB
  induction j generalizing r with
  | zero =>
      let R : Finset α := S.filter (fun x => r ≤ H x)
      let e : (Fin 1 → α) → α := fun l => l 0
      have he_inj : Set.InjOn e (B : Set (Fin 1 → α)) := by
        intro l hl l' hl' hll'
        funext i
        have hi : i = 0 := Fin.eq_zero i
        simpa [e, hi] using hll'
      have hmaps : ∀ l ∈ B, e l ∈ R := by
        intro l hl
        have hl' := hB l hl
        exact Finset.mem_filter.mpr ⟨hl'.1 0, hl'.2.1⟩
      have himage : B.image e ⊆ R := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨l, hl, rfl⟩
        exact hmaps l hl
      have hweight_nonneg (x : α) (hx : x ∈ R) :
          0 ≤ (H x)⁻¹ ^ q := by
        apply pow_nonneg
        apply inv_nonneg.mpr
        exact hHnonneg x (Finset.mem_filter.mp hx).1
      calc
        (∑ l ∈ B, orderedNormTupleWeight H a q l) =
            ∑ x ∈ B.image e, (H x)⁻¹ ^ q := by
              symm
              simpa [e, orderedNormTupleWeight] using
                (Finset.sum_image he_inj (f := fun x : α => (H x)⁻¹ ^ q))
        _ ≤ ∑ x ∈ R, (H x)⁻¹ ^ q := by
              apply Finset.sum_le_sum_of_subset_of_nonneg himage
              intro x hx hnot
              exact hweight_nonneg x hx
        _ = orderedNormNestedSum S H a q 0 r := by rfl
  | succ j ih =>
      let R : Finset α := S.filter (fun x => r ≤ H x)
      let fiber : α → Finset (Fin (j + 1) → α) := fun x =>
        (B.filter (fun l => l 0 = x)).image Fin.tail
      have hmaps : ∀ l ∈ B, l 0 ∈ R := by
        intro l hl
        have hl' := hB l hl
        exact Finset.mem_filter.mpr ⟨hl'.1 0, hl'.2.1⟩
      have hfiber_condition (x : α) (hx : x ∈ R) :
          ∀ t ∈ fiber x, orderedNormTupleCondition S H (H x) t := by
        intro t ht
        rcases Finset.mem_image.mp ht with ⟨l, hl, rfl⟩
        have hlfilter := Finset.mem_filter.mp hl
        have hlB := hlfilter.1
        have hlx : l 0 = x := hlfilter.2
        have hcond := hB l hlB
        refine ⟨?_, ?_, ?_⟩
        · intro i
          exact hcond.1 i.succ
        · simpa [Fin.tail, hlx] using
            (hcond.2.2 (0 : Fin (j + 1)))
        · intro i
          simpa [Fin.tail] using hcond.2.2 i.succ
      have htail_bound (x : α) (hx : x ∈ R) :
          (∑ t ∈ fiber x, orderedNormTupleWeight H a q t) ≤
            orderedNormNestedSum S H a q j (H x) :=
        ih (B := fiber x) (hfiber_condition x hx)
      have htail_inj (x : α) :
          Set.InjOn Fin.tail (↑(B.filter (fun l => l 0 = x)) :
            Set (Fin (j + 2) → α)) := by
        intro l hl l' hl' htail
        funext i
        refine Fin.cases ?_ ?_ i
        · exact (Finset.mem_filter.mp hl).2.trans
            (Finset.mem_filter.mp hl').2.symm
        · intro i
          exact congrFun htail i
      have hfiber_sum (x : α) :
          (∑ l ∈ B with l 0 = x, orderedNormTupleWeight H a q l) =
            ∑ t ∈ fiber x,
              (H x)⁻¹ ^ a * orderedNormTupleWeight H a q t := by
        symm
        dsimp [fiber]
        rw [Finset.sum_image (htail_inj x)]
        apply Finset.sum_congr rfl
        intro l hl
        have hlx : l 0 = x := (Finset.mem_filter.mp hl).2
        simp [orderedNormTupleWeight, hlx]
      have hinner (x : α) (hx : x ∈ R) :
          (∑ l ∈ B with l 0 = x, orderedNormTupleWeight H a q l) ≤
            (H x)⁻¹ ^ a * orderedNormNestedSum S H a q j (H x) := by
        calc
          (∑ l ∈ B with l 0 = x, orderedNormTupleWeight H a q l) =
              ∑ t ∈ fiber x,
                (H x)⁻¹ ^ a * orderedNormTupleWeight H a q t := hfiber_sum x
          _ = (H x)⁻¹ ^ a *
              (∑ t ∈ fiber x, orderedNormTupleWeight H a q t) := by
                rw [Finset.mul_sum]
          _ ≤ (H x)⁻¹ ^ a * orderedNormNestedSum S H a q j (H x) := by
                apply mul_le_mul_of_nonneg_left (htail_bound x hx)
                apply pow_nonneg
                apply inv_nonneg.mpr
                exact hHnonneg x (Finset.mem_filter.mp hx).1
      have hdecomp := Finset.sum_fiberwise_of_maps_to hmaps
        (fun l : Fin (j + 2) → α => orderedNormTupleWeight H a q l)
      calc
        (∑ l ∈ B, orderedNormTupleWeight H a q l) =
            ∑ x ∈ R, ∑ l ∈ B with l 0 = x,
              orderedNormTupleWeight H a q l := hdecomp.symm
        _ ≤ ∑ x ∈ R,
            (H x)⁻¹ ^ a * orderedNormNestedSum S H a q j (H x) := by
              apply Finset.sum_le_sum
              intro x hx
              exact hinner x hx
        _ = orderedNormNestedSum S H a q (j + 1) r := by rfl

/- [Lean infrastructure for paper equation `eq:just_as_before`, lines
   1731--1743] Algebraic bridge from the manuscript's product weight to the
recursive ordered-tuple weight.  The nonzero hypothesis is precisely the
domain condition needed for the displayed reciprocal factors. -/
theorem product_inv_pow_mul_last_eq_orderedNormTupleWeight
    {α : Type*} (H : α → ℝ) (n d : ℕ)
    (hn : 0 < n) (hd : 0 < d) :
    ∀ {j : ℕ} (l : Fin (j + 1) → α),
      (∀ i, H (l i) ≠ 0) →
      ((∏ i : Fin (j + 1), H (l i) ^ d)⁻¹) ^ n *
          H (l (Fin.last j)) =
        orderedNormTupleWeight H (n * d) (n * d - 1) l := by
  intro j
  induction j with
  | zero =>
      intro l hl
      have hx : H (l 0) ≠ 0 := hl 0
      have hnd : 1 ≤ n * d := Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (Nat.mul_pos hn hd))
      rw [Fin.prod_univ_one, Fin.last_zero, orderedNormTupleWeight]
      rw [inv_pow, ← pow_mul, Nat.mul_comm d n]
      rw [← inv_pow]
      rw [← Nat.sub_add_cancel hnd, pow_add, pow_one]
      field_simp
      congr 1
  | succ j ih =>
      intro l hl
      let P : ℝ := ∏ i : Fin (j + 1), H (l i.succ) ^ d
      let Q : ℝ := ∏ i : Fin (j + 1), H ((Fin.tail l) i) ^ d
      have htail := ih (Fin.tail l) (fun i => hl i.succ)
      have hPQ : P = Q := by rfl
      have htailQ : (Q⁻¹) ^ n * H ((Fin.tail l) (Fin.last j)) =
          orderedNormTupleWeight H (n * d) (n * d - 1) (Fin.tail l) := by
        simpa [Q] using htail
      rw [Fin.prod_univ_succ, orderedNormTupleWeight]
      change ((H (l 0) ^ d * P)⁻¹) ^ n * H (l (Fin.last (j + 1))) =
        (H (l 0))⁻¹ ^ (n * d) *
          orderedNormTupleWeight H (n * d) (n * d - 1) (Fin.tail l)
      have hlast : H (l (Fin.last (j + 1))) =
          H ((Fin.tail l) (Fin.last j)) := by rfl
      rw [hlast]
      calc
        ((H (l 0) ^ d * P)⁻¹) ^ n * H ((Fin.tail l) (Fin.last j)) =
            ((H (l 0) ^ d)⁻¹) ^ n *
              ((P⁻¹) ^ n * H ((Fin.tail l) (Fin.last j))) := by ring
        _ = (H (l 0))⁻¹ ^ (n * d) *
              ((P⁻¹) ^ n * H ((Fin.tail l) (Fin.last j))) := by
              rw [inv_pow, ← pow_mul, Nat.mul_comm d n, ← inv_pow]
        _ = (H (l 0))⁻¹ ^ (n * d) *
              ((Q⁻¹) ^ n * H ((Fin.tail l) (Fin.last j))) := by rw [hPQ]
        _ = (H (l 0))⁻¹ ^ (n * d) *
              orderedNormTupleWeight H (n * d) (n * d - 1) (Fin.tail l) := by
              rw [htailQ]

/- [derived consequence of paper `le:domain_dimension_bound`, lines
   1745--1753] Iterating the paper's innermost norm tail in the displayed
   order.  Each iteration raises the preceding reciprocal exponent by the
   already obtained tail exponent, exactly as in the manuscript's phrase
   “the rest of the nested sums inductively.” -/
set_option maxHeartbeats 3600000 in
theorem ambientIntegralRowModule_orderedNormNestedSum_tail
    {m a q : ℕ} (hm : 0 < m)
    (hpa : m * degree K < a) (hpq : m * degree K < q) :
    ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ S : Finset (ambientIntegralRowModule (K := K) m),
      ∀ {r : ℝ}, 0 < r →
        orderedNormNestedSum S
            (fun v : ambientIntegralRowModule (K := K) m =>
              ‖(v : RowVector K m)‖) a q j r ≤
          C * (r ^ (-((orderedNormNestedTailExponent
            (m * degree K) a q j : ℕ) : ℝ))) := by
  let H : ambientIntegralRowModule (K := K) m → ℝ := fun v =>
    ‖(v : RowVector K m)‖
  let p : ℕ := m * degree K
  have hpa' : p < a := by simpa [p] using hpa
  have hpq' : p < q := by simpa [p] using hpq
  change ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ S : Finset (ambientIntegralRowModule (K := K) m),
    ∀ {r : ℝ}, 0 < r →
      orderedNormNestedSum S H a q j r ≤
        C * (r ^ (-((orderedNormNestedTailExponent p a q j : ℕ) : ℝ)))
  intro j
  induction j with
  | zero =>
      obtain ⟨C, hC, htail⟩ :=
        ambientIntegralRowModule_finite_norm_tail (K := K) hm hpq'
      refine ⟨C, hC, ?_⟩
      intro S
      intro r hr
      have h := htail hr (S.filter (fun v => r ≤ H v)) (by
        intro v hv
        exact (Finset.mem_filter.mp hv).2)
      simpa [orderedNormNestedSum, orderedNormNestedTailExponent, H, p] using h
  | succ j ih =>
      obtain ⟨C, hC, hind⟩ := ih
      let e : ℕ := orderedNormNestedTailExponent p a q j
      let qnext : ℕ := a + e
      have hpqnext : p < qnext := by
        dsimp [qnext]
        omega
      obtain ⟨D, hD, htail⟩ :=
        ambientIntegralRowModule_finite_norm_tail (K := K) hm hpqnext
      refine ⟨C * D, mul_pos hC hD, ?_⟩
      intro S
      intro r hr
      let Sr : Finset (ambientIntegralRowModule (K := K) m) :=
        S.filter (fun v => r ≤ H v)
      have hind_point (v : ambientIntegralRowModule (K := K) m)
          (hv : v ∈ Sr) :
          orderedNormNestedSum S H a q j (H v) ≤
            C * (H v ^ (-((e : ℕ) : ℝ))) := by
        have hvpos : 0 < H v :=
          lt_of_lt_of_le hr (Finset.mem_filter.mp hv).2
        simpa [e] using hind S (r := H v) hvpos
      have hpow_join (x : ℝ) (hx : 0 < x) :
          (x⁻¹ ^ a) * x ^ (-((e : ℕ) : ℝ)) =
            x⁻¹ ^ (a + e) := by
        rw [← Real.rpow_natCast x⁻¹ a,
          Real.inv_rpow hx.le, ← Real.rpow_neg hx.le,
          ← Real.rpow_add hx,
          ← Real.rpow_natCast x⁻¹ (a + e),
          Real.inv_rpow hx.le, ← Real.rpow_neg hx.le]
        congr 1
        push_cast
        ring
      have hpoint (v : ambientIntegralRowModule (K := K) m)
          (hv : v ∈ Sr) :
          (H v)⁻¹ ^ a * orderedNormNestedSum S H a q j (H v) ≤
            C * ((H v)⁻¹ ^ qnext) := by
        have hvpos : 0 < H v :=
          lt_of_lt_of_le hr (Finset.mem_filter.mp hv).2
        calc
          (H v)⁻¹ ^ a * orderedNormNestedSum S H a q j (H v) ≤
              (H v)⁻¹ ^ a *
                (C * (H v ^ (-((e : ℕ) : ℝ)))) := by
                  exact mul_le_mul_of_nonneg_left (hind_point v hv)
                    (pow_nonneg (inv_nonneg.mpr hvpos.le) _)
          _ = C * ((H v)⁻¹ ^ a * H v ^ (-((e : ℕ) : ℝ))) := by ring
          _ = C * ((H v)⁻¹ ^ (a + e)) := by
            rw [hpow_join (H v) hvpos]
          _ = C * ((H v)⁻¹ ^ qnext) := by rfl
      have hsum_point :
          (∑ v ∈ Sr,
            (H v)⁻¹ ^ a * orderedNormNestedSum S H a q j (H v)) ≤
            C * ∑ v ∈ Sr, (H v)⁻¹ ^ qnext := by
        calc
          (∑ v ∈ Sr,
            (H v)⁻¹ ^ a * orderedNormNestedSum S H a q j (H v)) ≤
              ∑ v ∈ Sr, C * ((H v)⁻¹ ^ qnext) := by
                apply Finset.sum_le_sum
                intro v hv
                exact hpoint v hv
          _ = C * ∑ v ∈ Sr, (H v)⁻¹ ^ qnext := by
            rw [Finset.mul_sum]
      have htail_sum := htail hr Sr (by
        intro v hv
        simpa [H] using (Finset.mem_filter.mp hv).2)
      have htail_sum' :
          (∑ v ∈ Sr, (H v)⁻¹ ^ qnext) ≤
            D * (r ^ (-((qnext - p : ℕ) : ℝ))) := by
        simpa [H, p] using htail_sum
      change orderedNormNestedSum S H a q (j + 1) r ≤
        (C * D) *
          (r ^ (-((orderedNormNestedTailExponent p a q (j + 1) : ℕ) : ℝ)))
      calc
        orderedNormNestedSum S H a q (j + 1) r =
            ∑ v ∈ Sr,
              (H v)⁻¹ ^ a * orderedNormNestedSum S H a q j (H v) := by
                rfl
        _ ≤ C * ∑ v ∈ Sr, (H v)⁻¹ ^ qnext := hsum_point
        _ ≤ C * (D * (r ^ (-((qnext - p : ℕ) : ℝ))) ) := by
          exact mul_le_mul_of_nonneg_left htail_sum' hC.le
        _ = (C * D) *
            (r ^ (-((orderedNormNestedTailExponent p a q (j + 1) : ℕ) : ℝ))) := by
              simp [orderedNormNestedTailExponent, e, qnext]
              ring

/- [derived consequence of paper `le:domain_dimension_bound`, lines
   1741--1753] Uniform finite-family form of the noncritical ordered-tuple
sum.  The constant is quantified before the finite row family, so it is
genuinely independent of the manuscript cutoff `T`; the fixed positive
lower norm cutoff is supplied by `c^{minnorm}`. -/
theorem ambientIntegralRowModule_orderedNormTupleWeight_sum_le
    {m a q j : ℕ} (hm : 0 < m)
    (hpa : m * degree K < a) (hpq : m * degree K < q)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ S : Finset (ambientIntegralRowModule (K := K) m),
      ∀ B : Finset (Fin (j + 1) → ambientIntegralRowModule (K := K) m),
      (∀ l ∈ B, orderedNormTupleCondition S
        (fun v : ambientIntegralRowModule (K := K) m =>
          ‖(v : RowVector K m)‖) δ l) →
      (∑ l ∈ B,
        orderedNormTupleWeight
          (fun v : ambientIntegralRowModule (K := K) m =>
            ‖(v : RowVector K m)‖) a q l) ≤ C := by
  obtain ⟨Ctail, hCtail, htail⟩ :=
    ambientIntegralRowModule_orderedNormNestedSum_tail
      (K := K) hm hpa hpq j
  let e : ℕ := orderedNormNestedTailExponent (m * degree K) a q j
  let C : ℝ := Ctail * δ ^ (-((e : ℕ) : ℝ))
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    exact mul_pos hCtail (Real.rpow_pos_of_pos hδ _)
  · intro S B hB
    have hcompare := sum_orderedNormTupleWeight_le_orderedNormNestedSum
      S (fun v : ambientIntegralRowModule (K := K) m =>
        ‖(v : RowVector K m)‖) a q
      (fun v hv => norm_nonneg _) B hB
    have htailδ := htail S hδ
    calc
      (∑ l ∈ B,
        orderedNormTupleWeight
          (fun v : ambientIntegralRowModule (K := K) m =>
            ‖(v : RowVector K m)‖) a q l) ≤
          orderedNormNestedSum S
            (fun v : ambientIntegralRowModule (K := K) m =>
              ‖(v : RowVector K m)‖) a q j δ := hcompare
      _ ≤ Ctail * δ ^ (-((orderedNormNestedTailExponent
          (m * degree K) a q j : ℕ) : ℝ)) := htailδ
      _ = C := by rfl

/- [derived consequence of paper `le:domain_dimension_bound`, lines
   1741--1753] Transfer the uniform ordered-tuple bound from the fixed
ambient lattice to algebraic-integer rows.  The finite family is mapped by
the manuscript's Minkowski embedding, and its image supplies exactly the
finite row set used by the nested tail estimate. -/
theorem integralRow_orderedNormTupleWeight_sum_le
    {m a q j : ℕ} (hm : 0 < m)
    (hpa : m * degree K < a) (hpq : m * degree K < q)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ B : Finset (Fin (j + 1) → Fin m → 𝓞 K),
      (∀ l ∈ B,
        (∀ i, δ ≤ ‖integralVectorEmbedding (K := K) m (l i)‖) ∧
        ∀ i : Fin j,
          ‖integralVectorEmbedding (K := K) m (l i.castSucc)‖ ≤
            ‖integralVectorEmbedding (K := K) m (l i.succ)‖) →
      (∑ l ∈ B,
        orderedNormTupleWeight
          (fun x : Fin m → 𝓞 K =>
            ‖integralVectorEmbedding (K := K) m x‖) a q l) ≤ C := by
  classical
  obtain ⟨C, hC, hbound⟩ :=
    ambientIntegralRowModule_orderedNormTupleWeight_sum_le
      (K := K) (j := j) hm hpa hpq hδ
  refine ⟨C, hC, ?_⟩
  intro B hB
  let e : (Fin m → 𝓞 K) → ambientIntegralRowModule (K := K) m := fun x =>
    ⟨integralVectorEmbedding (K := K) m x,
      integralVectorEmbedding_mem_ambientIntegralRowModule (K := K) m x⟩
  let eTuple : (Fin (j + 1) → Fin m → 𝓞 K) →
      Fin (j + 1) → ambientIntegralRowModule (K := K) m := fun l i => e (l i)
  let S : Finset (ambientIntegralRowModule (K := K) m) :=
    B.biUnion (fun l =>
      Finset.univ.image (fun i : Fin (j + 1) => e (l i)))
  let Bambient : Finset
      (Fin (j + 1) → ambientIntegralRowModule (K := K) m) :=
    B.image eTuple
  have he : Function.Injective e := by
    intro x y hxy
    apply integralVectorEmbedding_injective (K := K) m
    exact congrArg Subtype.val hxy
  have heTuple : Function.Injective eTuple := by
    intro l l' hll'
    funext i
    apply he
    exact congrFun hll' i
  have hmemS (l : Fin (j + 1) → Fin m → 𝓞 K) (hl : l ∈ B)
      (i : Fin (j + 1)) : e (l i) ∈ S := by
    apply Finset.mem_biUnion.mpr
    refine ⟨l, hl, ?_⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hcondition : ∀ t ∈ Bambient, orderedNormTupleCondition S
      (fun v : ambientIntegralRowModule (K := K) m =>
        ‖(v : RowVector K m)‖) δ t := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨l, hl, rfl⟩
    have hlB := hB l hl
    refine ⟨?_, hlB.1 0, ?_⟩
    · intro i
      exact hmemS l hl i
    · intro i
      exact hlB.2 i
  have hweight (l : Fin (j + 1) → Fin m → 𝓞 K) :
      orderedNormTupleWeight
        (fun v : ambientIntegralRowModule (K := K) m =>
          ‖(v : RowVector K m)‖) a q (eTuple l) =
        orderedNormTupleWeight
          (fun x : Fin m → 𝓞 K =>
            ‖integralVectorEmbedding (K := K) m x‖) a q l := by
    simpa [eTuple, e] using
      (orderedNormTupleWeight_map
        (fun v : ambientIntegralRowModule (K := K) m =>
          ‖(v : RowVector K m)‖) e a q l)
  have hambient := hbound S Bambient hcondition
  calc
    (∑ l ∈ B,
      orderedNormTupleWeight
        (fun x : Fin m → 𝓞 K =>
          ‖integralVectorEmbedding (K := K) m x‖) a q l) =
        ∑ t ∈ Bambient,
          orderedNormTupleWeight
            (fun v : ambientIntegralRowModule (K := K) m =>
              ‖(v : RowVector K m)‖) a q t := by
          symm
          dsimp [Bambient]
          rw [Finset.sum_image heTuple.injOn]
          apply Finset.sum_congr rfl
          intro l hl
          exact hweight l
    _ ≤ C := hambient

/- [Lean infrastructure for paper `le:injective_minima`, lines 1205--1208,
   and `eq:just_as_before`, lines 1731--1748] Finite representation of the
intended nonzero part of `𝓑_k(T)`.  The separate name retains the literal
checked-in definition while making the reciprocal product mathematically
defined; see `notes/paper-issues.md`. -/
noncomputable def possibleSuccessiveMinimaNonzeroFinset
    {m k : ℕ} (C T : ℝ) : Finset (Fin k → Fin m → 𝓞 K) :=
  ((finite_possibleSuccessiveMinimaSet (K := K) (m := m) (k := k)
    (C := C) (T := T)).toFinset).filter (fun l => ∀ i, l i ≠ 0)

/- [derived consequence of the noncritical branch of
   `le:domain_dimension_bound`, lines 1724--1753] The strict noncritical
condition gives exactly the two ambient summability gaps required by the
manuscript's final-row exponent `n d - 1` and the preceding-row exponent
`n d`. -/
theorem noncritical_ambient_exponent_gaps
    {m n : ℕ} (hgap : 1 < (n - m) * degree K) :
    m * degree K < n * degree K ∧
      m * degree K < n * degree K - 1 := by
  have hprodpos : 0 < (n - m) * degree K := by omega
  have hsubpos : 0 < n - m := Nat.pos_of_mul_pos_right hprodpos
  have hmn : m < n := Nat.sub_pos_iff_lt.mp hsubpos
  have hmul : n * degree K =
      m * degree K + (n - m) * degree K := by
    calc
      n * degree K = (m + (n - m)) * degree K := by
        congr 1
        omega
      _ = m * degree K + (n - m) * degree K := by rw [Nat.add_mul]
  constructor <;> rw [hmul] <;> omega

/- [derived consequence of paper `eq:just_as_before` and
   `le:domain_dimension_bound`, lines 1731--1753] The paper's relaxed
noncritical reciprocal-minima sum is uniformly bounded on the explicitly
nonzero version of `𝓑_{j+1}(T)`.  This is the literal ordinary-shell nested
summation argument, with `c^{minnorm}` supplying the lower cutoff. -/
set_option maxHeartbeats 3600000 in
theorem possibleSuccessiveMinima_nonzero_product_weight_sum_le
    {m n j : ℕ} (hm : 0 < m)
    (hgap : 1 < (n - m) * degree K) :
    ∃ M : ℝ, 0 < M ∧ ∀ C T : ℝ,
      (∑ l ∈ possibleSuccessiveMinimaNonzeroFinset
        (K := K) (m := m) (k := j + 1) C T,
        ((∏ i : Fin (j + 1),
          ‖integralVectorEmbedding (K := K) m (l i)‖ ^ degree K)⁻¹) ^ n *
          ‖integralVectorEmbedding (K := K) m (l (Fin.last j))‖) ≤ M := by
  classical
  obtain ⟨δ, hδ, hmin⟩ :=
    exists_ambientIntegralRowModule_norm_lower_bound (K := K) m hm
  obtain ⟨hpa, hpq⟩ := noncritical_ambient_exponent_gaps (K := K) hgap
  obtain ⟨M, hM, hbound⟩ :=
    integralRow_orderedNormTupleWeight_sum_le
      (K := K) (j := j) hm hpa hpq hδ
  refine ⟨M, hM, ?_⟩
  intro C T
  let B : Finset (Fin (j + 1) → Fin m → 𝓞 K) :=
    possibleSuccessiveMinimaNonzeroFinset
      (K := K) (m := m) (k := j + 1) C T
  have hB : ∀ l ∈ B,
      (∀ i, δ ≤ ‖integralVectorEmbedding (K := K) m (l i)‖) ∧
      ∀ i : Fin j,
        ‖integralVectorEmbedding (K := K) m (l i.castSucc)‖ ≤
          ‖integralVectorEmbedding (K := K) m (l i.succ)‖ := by
    intro l hl
    have hlfilter : l ∈
        (finite_possibleSuccessiveMinimaSet (K := K) (m := m) (k := j + 1)
          (C := C) (T := T)).toFinset.filter (fun l => ∀ i, l i ≠ 0) := by
      simpa [B, possibleSuccessiveMinimaNonzeroFinset] using hl
    have hlpossible : l ∈ possibleSuccessiveMinimaSet
        (K := K) (m := m) (k := j + 1) C T :=
      (finite_possibleSuccessiveMinimaSet (K := K) (m := m) (k := j + 1)
        (C := C) (T := T)).mem_toFinset.mp (Finset.mem_filter.mp hlfilter).1
    refine ⟨?_, ?_⟩
    · intro i
      let v : ambientIntegralRowModule (K := K) m :=
        ⟨integralVectorEmbedding (K := K) m (l i),
          integralVectorEmbedding_mem_ambientIntegralRowModule (K := K) m (l i)⟩
      have hvne : v ≠ 0 := by
        intro hvzero
        apply (Finset.mem_filter.mp hlfilter).2 i
        apply integralVectorEmbedding_injective (K := K) m
        simpa [v] using congrArg Subtype.val hvzero
      simpa [v] using hmin v hvne
    · intro i
      exact hlpossible.1 i.castSucc i.succ (Nat.le_succ i.val)
  have hsum := hbound B hB
  have hprodpos : 0 < (n - m) * degree K := by omega
  have hsubpos : 0 < n - m := Nat.pos_of_mul_pos_right hprodpos
  have hn : 0 < n := by
    have hmn : m < n := Nat.sub_pos_iff_lt.mp hsubpos
    omega
  have hd : 0 < degree K := Module.finrank_pos
  have hweight (l : Fin (j + 1) → Fin m → 𝓞 K) (hl : l ∈ B) :
      ((∏ i : Fin (j + 1),
        ‖integralVectorEmbedding (K := K) m (l i)‖ ^ degree K)⁻¹) ^ n *
          ‖integralVectorEmbedding (K := K) m (l (Fin.last j))‖ =
        orderedNormTupleWeight
          (fun x : Fin m → 𝓞 K =>
            ‖integralVectorEmbedding (K := K) m x‖)
          (n * degree K) (n * degree K - 1) l := by
    apply product_inv_pow_mul_last_eq_orderedNormTupleWeight
      (fun x : Fin m → 𝓞 K =>
        ‖integralVectorEmbedding (K := K) m x‖) n (degree K) hn hd l
    intro i hzero
    have hlfilter : l ∈
        (finite_possibleSuccessiveMinimaSet (K := K) (m := m) (k := j + 1)
          (C := C) (T := T)).toFinset.filter (fun l => ∀ i, l i ≠ 0) := by
      simpa [B, possibleSuccessiveMinimaNonzeroFinset] using hl
    apply (Finset.mem_filter.mp hlfilter).2 i
    apply integralVectorEmbedding_injective (K := K) m
    have hembzero : integralVectorEmbedding (K := K) m (l i) = 0 :=
      norm_eq_zero.mp hzero
    simpa using hembzero
  change (∑ l ∈ B,
    ((∏ i : Fin (j + 1),
      ‖integralVectorEmbedding (K := K) m (l i)‖ ^ degree K)⁻¹) ^ n *
        ‖integralVectorEmbedding (K := K) m (l (Fin.last j))‖) ≤ M
  calc
    (∑ l ∈ B,
      ((∏ i : Fin (j + 1),
        ‖integralVectorEmbedding (K := K) m (l i)‖ ^ degree K)⁻¹) ^ n *
          ‖integralVectorEmbedding (K := K) m (l (Fin.last j))‖) =
        ∑ l ∈ B,
          orderedNormTupleWeight
            (fun x : Fin m → 𝓞 K =>
              ‖integralVectorEmbedding (K := K) m x‖)
            (n * degree K) (n * degree K - 1) l := by
              apply Finset.sum_congr rfl
              intro l hl
              exact hweight l hl
    _ ≤ M := hsum

/- [Lean infrastructure for paper equation `eq:just_as_before`, lines
   1731--1743] Under Lean's totalized inversion convention, a tuple with a
zero row has zero radius weight.  This proves the bridge from the literal
finite set in the checked-in manuscript to its explicitly nonzero intended
reciprocal-sum domain. -/
theorem possibleSuccessiveMinimaRadiusWeight_eq_zero_of_some_zero
    {m k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (l : Fin k → Fin m → 𝓞 K) (i : Fin k) (hi : l i = 0) :
    possibleSuccessiveMinimaRadiusWeight (K := K) (m := m) n hk l = 0 := by
  unfold possibleSuccessiveMinimaRadiusWeight
  have hd : 0 < degree K := Module.finrank_pos
  have hprod : (∏ j : Fin k,
      ‖integralVectorEmbedding (K := K) m (l j)‖ ^ degree K) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi, zero_pow (Nat.ne_of_gt hd)]
  rw [hprod, inv_zero, zero_pow (Nat.ne_of_gt hn), zero_mul]

/- [Lean infrastructure for paper equation `eq:just_as_before`, lines
   1731--1743] Exact finite-sum bridge between the current literal Lean
encoding of `𝓑_{j+1}(T)` and the nonzero ordered reciprocal product.  It is
not presented as a substitute for the manuscript notation: the zero-domain
clarification is recorded separately in `notes/paper-issues.md`. -/
theorem sum_possibleSuccessiveMinimaRadiusWeight_eq_nonzero_product_weight
    {m n j : ℕ} (hk : 0 < j + 1) (hn : 0 < n) (C T : ℝ) :
    (∑ l ∈ (finite_possibleSuccessiveMinimaSet
      (K := K) (m := m) (k := j + 1) (C := C) (T := T)).toFinset,
      possibleSuccessiveMinimaRadiusWeight (K := K) (m := m) n hk l) =
      ∑ l ∈ possibleSuccessiveMinimaNonzeroFinset
        (K := K) (m := m) (k := j + 1) C T,
        ((∏ i : Fin (j + 1),
          ‖integralVectorEmbedding (K := K) m (l i)‖ ^ degree K)⁻¹) ^ n *
          ‖integralVectorEmbedding (K := K) m (l (Fin.last j))‖ := by
  classical
  let F : Finset (Fin (j + 1) → Fin m → 𝓞 K) :=
    (finite_possibleSuccessiveMinimaSet
      (K := K) (m := m) (k := j + 1) (C := C) (T := T)).toFinset
  let P : (Fin (j + 1) → Fin m → 𝓞 K) → Prop := fun l => ∀ i, l i ≠ 0
  let B : Finset (Fin (j + 1) → Fin m → 𝓞 K) := F.filter P
  have hzero (l : Fin (j + 1) → Fin m → 𝓞 K)
      (hl : l ∈ F.filter (fun l => ¬ P l)) :
      possibleSuccessiveMinimaRadiusWeight (K := K) (m := m) n hk l = 0 := by
    obtain ⟨i, hi⟩ := not_forall.mp (Finset.mem_filter.mp hl).2
    exact possibleSuccessiveMinimaRadiusWeight_eq_zero_of_some_zero hk hn l i
      (not_ne_iff.mp hi)
  have hlast : (⟨j + 1 - 1, Nat.pred_lt hk.ne'⟩ : Fin (j + 1)) = Fin.last j := by
    apply Fin.ext
    simp
  have hweight (l : Fin (j + 1) → Fin m → 𝓞 K)
      (hl : l ∈ F.filter P) :
      possibleSuccessiveMinimaRadiusWeight (K := K) (m := m) n hk l =
        ((∏ i : Fin (j + 1),
          ‖integralVectorEmbedding (K := K) m (l i)‖ ^ degree K)⁻¹) ^ n *
          ‖integralVectorEmbedding (K := K) m (l (Fin.last j))‖ := by
    unfold possibleSuccessiveMinimaRadiusWeight
    rw [hlast]
  change (∑ l ∈ F,
      possibleSuccessiveMinimaRadiusWeight (K := K) (m := m) n hk l) =
    ∑ l ∈ B,
      ((∏ i : Fin (j + 1),
        ‖integralVectorEmbedding (K := K) m (l i)‖ ^ degree K)⁻¹) ^ n *
        ‖integralVectorEmbedding (K := K) m (l (Fin.last j))‖
  calc
    (∑ l ∈ F,
      possibleSuccessiveMinimaRadiusWeight (K := K) (m := m) n hk l) =
        (∑ l ∈ F.filter P,
          possibleSuccessiveMinimaRadiusWeight (K := K) (m := m) n hk l) +
          ∑ l ∈ F.filter (fun l => ¬ P l),
            possibleSuccessiveMinimaRadiusWeight (K := K) (m := m) n hk l := by
              rw [← Finset.sum_filter_add_sum_filter_not F P]
    _ = ∑ l ∈ F.filter P,
          possibleSuccessiveMinimaRadiusWeight (K := K) (m := m) n hk l := by
            rw [Finset.sum_eq_zero hzero, add_zero]
    _ = ∑ l ∈ B,
          ((∏ i : Fin (j + 1),
            ‖integralVectorEmbedding (K := K) m (l i)‖ ^ degree K)⁻¹) ^ n *
            ‖integralVectorEmbedding (K := K) m (l (Fin.last j))‖ := by
              apply Finset.sum_congr rfl
              intro l hl
              exact hweight l hl

/- [derived consequence of paper equation `eq:just_as_before`, lines
   1731--1753] This returns the ordinary-shell bound to the literal
`possibleSuccessiveMinimaRadiusWeight` occurring in the finite injection from
`𝓕_{j+1}(T)`.  The preceding exact bridge is retained so that this is a bound
in the manuscript's notation, rather than a notation-changing replacement. -/
theorem possibleSuccessiveMinimaRadiusWeight_sum_le_of_noncritical
    {m n j : ℕ} (hm : 0 < m)
    (hgap : 1 < (n - m) * degree K) :
    ∃ M : ℝ, 0 < M ∧ ∀ C T : ℝ,
      (∑ l ∈ (finite_possibleSuccessiveMinimaSet
        (K := K) (m := m) (k := j + 1) (C := C) (T := T)).toFinset,
        possibleSuccessiveMinimaRadiusWeight (K := K) (m := m) n
          (Nat.succ_pos j) l) ≤ M := by
  have hprodpos : 0 < (n - m) * degree K := by omega
  have hsubpos : 0 < n - m := Nat.pos_of_mul_pos_right hprodpos
  have hn : 0 < n := by
    have hmn : m < n := Nat.sub_pos_iff_lt.mp hsubpos
    omega
  obtain ⟨M, hM, hbound⟩ :=
    possibleSuccessiveMinima_nonzero_product_weight_sum_le
      (K := K) (j := j) hm hgap
  refine ⟨M, hM, ?_⟩
  intro C T
  rw [sum_possibleSuccessiveMinimaRadiusWeight_eq_nonzero_product_weight
    (K := K) (m := m) (n := n) (j := j) (Nat.succ_pos j) hn C T]
  exact hbound C T

/- [derived consequence of paper equation `eq:just_as_before`, lines
   1724--1753] This is the stated uniform bound for the finite manuscript
family `𝓕_{j+1}(T)` in the noncritical branch.  The displayed product
comparison is the same Fieker--Stehlé input used in
`sum_calF_coveringRadius_div_height_pow_le_possibleMinimaWeight`; it remains
an explicit hypothesis here rather than being silently replaced by a new
geometry-of-numbers assertion. -/
theorem exists_uniform_calF_coveringRadius_sum_bound_of_noncritical
    {m n j : ℕ} {Cprod : ℝ} (hm : 0 < m)
    (hgap : 1 < (n - m) * degree K) (hCprod : 0 ≤ Cprod) :
    ∃ Cfinite : ℝ, 0 < Cfinite ∧
      ∀ {Csup C T : ℝ}
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
        (∑ D ∈ (finite_calF_of_possibleSuccessiveMinima
          (K := K) (m := m) (k := j + 1) (n := n)
          hCproj hCsup hT (Nat.succ_pos j)).toFinset,
          latticeCoveringRadius (rowZLattice (echelonRowSpace D)) /
            (rowSpaceHeight (echelonRowSpace D)) ^ n) ≤ Cfinite := by
  obtain ⟨M, hM, hMbound⟩ :=
    possibleSuccessiveMinimaRadiusWeight_sum_le_of_noncritical
      (K := K) (j := j) hm hgap
  let R : ℝ := (Fintype.card (Σ _ : Fin (j + 1), IntegralBasisIndex K) : ℝ) *
    rowScalarActionBoundSum (K := K) (m := m)
  let Cfinite : ℝ := R * Cprod ^ n * M + 1
  have hR : 0 ≤ R := by
    dsimp [R]
    exact mul_nonneg (Nat.cast_nonneg _)
      (rowScalarActionBoundSum_nonneg (K := K) (m := m))
  have hfactor : 0 ≤ R * Cprod ^ n :=
    mul_nonneg hR (pow_nonneg hCprod _)
  refine ⟨Cfinite, ?_, ?_⟩
  · have hnonneg : 0 ≤ R * Cprod ^ n * M :=
      mul_nonneg hfactor hM.le
    dsimp [Cfinite]
    linarith
  · intro Csup C T hCproj hCsup hT hprod
    have hsum :=
      sum_calF_coveringRadius_div_height_pow_le_possibleMinimaWeight
        (K := K) (m := m) (k := j + 1) (n := n)
        hCproj hCsup hT (Nat.succ_pos j) hCprod hprod
    have htuple := hMbound C T
    have hsum' :
        (∑ D ∈ (finite_calF_of_possibleSuccessiveMinima
          (K := K) (m := m) (k := j + 1) (n := n)
          hCproj hCsup hT (Nat.succ_pos j)).toFinset,
          latticeCoveringRadius (rowZLattice (echelonRowSpace D)) /
            (rowSpaceHeight (echelonRowSpace D)) ^ n) ≤
          R * Cprod ^ n *
            (∑ l ∈ (finite_possibleSuccessiveMinimaSet
              (K := K) (m := m) (k := j + 1) (C := C) (T := T)).toFinset,
              possibleSuccessiveMinimaRadiusWeight (K := K) (m := m) n
                (Nat.succ_pos j) l) := by
      simpa [R] using hsum
    calc
      (∑ D ∈ (finite_calF_of_possibleSuccessiveMinima
        (K := K) (m := m) (k := j + 1) (n := n)
        hCproj hCsup hT (Nat.succ_pos j)).toFinset,
        latticeCoveringRadius (rowZLattice (echelonRowSpace D)) /
          (rowSpaceHeight (echelonRowSpace D)) ^ n) ≤
          R * Cprod ^ n *
            (∑ l ∈ (finite_possibleSuccessiveMinimaSet
              (K := K) (m := m) (k := j + 1) (C := C) (T := T)).toFinset,
              possibleSuccessiveMinimaRadiusWeight (K := K) (m := m) n
                (Nat.succ_pos j) l) := hsum'
      _ ≤ R * Cprod ^ n * M :=
        mul_le_mul_of_nonneg_left htuple hfactor
      _ ≤ Cfinite := by
        dsimp [Cfinite]
        linarith [mul_nonneg hfactor hM.le]

/- [derived consequence, paper equation `eq:just_as_before`, lines
   1731--1753] This specializes the noncritical `𝓕_{j+1}(T)` radius sum to
   the proved Fieker--Stehlé/Minkowski-II product derivation in
   `FiekerStehle.lean`.  It supplies the manuscript's one constant
   `C^{okhadamard}` uniformly over the echelon family. -/
theorem exists_uniform_calF_coveringRadius_sum_bound_of_noncritical_of_fiekerStehle
    {m n j : ℕ} (hm : 0 < m)
    (hgap : 1 < (n - m) * degree K) :
    ∃ Cfinite : ℝ, 0 < Cfinite ∧
      ∀ {Csup C T : ℝ}
        (hCproj : rowKRealSmulBound (K := K) (m := m) *
          numberFieldCoefficientRadius K ≤ C)
        (hCsup : Csup ≤ C) (hT : 0 ≤ T),
        (∑ D ∈ (finite_calF_of_possibleSuccessiveMinima
          (K := K) (m := m) (k := j + 1) (n := n)
          hCproj hCsup hT (Nat.succ_pos j)).toFinset,
          latticeCoveringRadius (rowZLattice (echelonRowSpace D)) /
            (rowSpaceHeight (echelonRowSpace D)) ^ n) ≤ Cfinite := by
  obtain ⟨Cprod, hCprod, hprod⟩ :=
    exists_rowSuccessiveMinimum_product_le_height_of_euclideanMinkowskiSecond
      (K := K) (m := m) (k := j + 1) (Nat.succ_pos j)
  obtain ⟨Cfinite, hCfinite, hbound⟩ :=
    exists_uniform_calF_coveringRadius_sum_bound_of_noncritical
      (K := K) (j := j) hm hgap hCprod.le
  refine ⟨Cfinite, hCfinite, ?_⟩
  intro Csup C T hCproj hCsup hT
  apply hbound hCproj hCsup hT
  intro D hD
  exact hprod (echelonRowSpace D)


end Katznelson
