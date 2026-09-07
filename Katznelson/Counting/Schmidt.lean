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

/- The unit-height shells used in the paper's summation-by-parts argument.
   They retain the integer indexing of the count function while making the
   lower and upper height cutoffs explicit. -/
def heightShell {α : Type*} (H : α → ℝ) (n : ℕ) : Set α :=
  {x | (n : ℝ) ≤ H x ∧ H x < ((n + 1 : ℕ) : ℝ)}

theorem heightShell_disjoint {α : Type*} {H : α → ℝ} {n₁ n₂ : ℕ}
    (hne : n₁ ≠ n₂) : Disjoint (heightShell H n₁) (heightShell H n₂) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hltR : (n₁ : ℝ) + 1 ≤ n₂ := by
      exact_mod_cast (Nat.succ_le_of_lt hlt)
    rw [Set.disjoint_left]
    intro x h₁ h₂
    have hupper : H x < (n₁ : ℝ) + 1 := by
      simpa [heightShell, Nat.cast_add_one] using h₁.2
    exact (not_le_of_gt hupper) (hltR.trans h₂.1)
  · have hgtR : (n₂ : ℝ) + 1 ≤ n₁ := by
      exact_mod_cast (Nat.succ_le_of_lt hgt)
    rw [Set.disjoint_left]
    intro x h₁ h₂
    have hupper : H x < (n₂ : ℝ) + 1 := by
      simpa [heightShell, Nat.cast_add_one] using h₂.2
    exact (not_le_of_gt hupper) (hgtR.trans h₁.1)

theorem heightShell_pairwiseDisjoint {α : Type*} {H : α → ℝ} :
    (Set.univ : Set {n : ℕ // 1 ≤ n}).PairwiseDisjoint
      (fun n => heightShell H n) := by
  intro n hn m hm hne
  apply heightShell_disjoint
  intro hnm
  exact hne (Subtype.ext hnm)

theorem mem_heightShell_unique {α : Type*} {H : α → ℝ} {x : α}
    {n₁ n₂ : ℕ} (h₁ : x ∈ heightShell H n₁)
    (h₂ : x ∈ heightShell H n₂) : n₁ = n₂ := by
  by_contra hne
  exact Set.disjoint_left.1 (heightShell_disjoint hne) h₁ h₂

theorem exists_mem_heightShell_of_one_le {α : Type*} {H : α → ℝ} {x : α}
    (hx : 1 ≤ H x) : ∃ n : ℕ, 1 ≤ n ∧ x ∈ heightShell H n := by
  let n : ℕ := ⌊H x⌋₊
  refine ⟨n, ?_, ?_⟩
  · exact Nat.one_le_floor_iff (H x) |>.2 hx
  · constructor
    · exact Nat.floor_le (by positivity)
    · simpa [n, Nat.cast_add_one] using (Nat.lt_floor_add_one (H x))

theorem iUnion_heightShell {α : Type*} {H : α → ℝ} :
    ⋃ n : {n : ℕ // 1 ≤ n}, heightShell H n = {x | 1 ≤ H x} := by
  ext x
  constructor
  · intro hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨n, hn⟩ := hx
    exact le_trans (by exact_mod_cast n.property) hn.1
  · intro hx
    obtain ⟨n, hn, hxn⟩ := exists_mem_heightShell_of_one_le hx
    exact Set.mem_iUnion.2 ⟨⟨n, hn⟩, hxn⟩

/- Dyadic shells give the optimal summability threshold `p < q` from a
   polynomial height count.  Unlike the unit shells above, their geometric
   size absorbs the polynomial factor without introducing an extra `+ 1`. -/
def heightDyadicShell {α : Type*} (H : α → ℝ) (j : ℕ) : Set α :=
  {x | ((2 ^ j : ℕ) : ℝ) ≤ H x ∧ H x < ((2 ^ (j + 1) : ℕ) : ℝ)}

theorem heightDyadicShell_disjoint {α : Type*} {H : α → ℝ} {j₁ j₂ : ℕ}
    (hne : j₁ ≠ j₂) : Disjoint (heightDyadicShell H j₁) (heightDyadicShell H j₂) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hpow : 2 ^ (j₁ + 1) ≤ 2 ^ j₂ := by
      apply Nat.pow_le_pow_right
      · omega
      · omega
    rw [Set.disjoint_left]
    intro x h₁ h₂
    have hupper : H x < ((2 ^ (j₁ + 1) : ℕ) : ℝ) := h₁.2
    have hlower : ((2 ^ j₂ : ℕ) : ℝ) ≤ H x := h₂.1
    have hpowR : ((2 ^ (j₁ + 1) : ℕ) : ℝ) ≤ ((2 ^ j₂ : ℕ) : ℝ) := by
      exact_mod_cast hpow
    exact (not_le_of_gt hupper) (hpowR.trans hlower)
  · have hpow : 2 ^ (j₂ + 1) ≤ 2 ^ j₁ := by
      apply Nat.pow_le_pow_right
      · omega
      · omega
    rw [Set.disjoint_left]
    intro x h₁ h₂
    have hupper : H x < ((2 ^ (j₂ + 1) : ℕ) : ℝ) := h₂.2
    have hlower : ((2 ^ j₁ : ℕ) : ℝ) ≤ H x := h₁.1
    have hpowR : ((2 ^ (j₂ + 1) : ℕ) : ℝ) ≤ ((2 ^ j₁ : ℕ) : ℝ) := by
      exact_mod_cast hpow
    exact (not_le_of_gt hupper) (hpowR.trans hlower)

theorem heightDyadicShell_pairwiseDisjoint {α : Type*} {H : α → ℝ} :
    (Set.univ : Set ℕ).PairwiseDisjoint (heightDyadicShell H) := by
  intro j _ l _ hne
  exact heightDyadicShell_disjoint hne

theorem exists_mem_heightDyadicShell_of_one_le {α : Type*} {H : α → ℝ} {x : α}
    (hx : 1 ≤ H x) : ∃ j : ℕ, x ∈ heightDyadicShell H j := by
  let n : ℕ := ⌊H x⌋₊
  have hnpos : 0 < n := by
    exact (Nat.one_le_floor_iff (H x)).2 hx
  let j : ℕ := Nat.log 2 n
  have hlowN : 2 ^ j ≤ n := by
    exact Nat.pow_log_le_self 2 (Nat.ne_of_gt hnpos)
  have hlowNreal : ((2 ^ j : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hlowN
  have hfloorle : (n : ℝ) ≤ H x := by
    simpa [n] using (Nat.floor_le (show 0 ≤ H x by positivity))
  have hlow : ((2 ^ j : ℕ) : ℝ) ≤ H x := hlowNreal.trans hfloorle
  have huppow : n < 2 ^ (j + 1) := by
    simpa [j, Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self (b := 2) (by omega) n
  have huppN : n + 1 ≤ 2 ^ (j + 1) := Nat.succ_le_of_lt huppow
  have hupp : H x < ((2 ^ (j + 1) : ℕ) : ℝ) := by
    exact (Nat.lt_floor_add_one (H x)).trans_le (by exact_mod_cast huppN)
  exact ⟨j, hlow, hupp⟩

theorem iUnion_heightDyadicShell {α : Type*} {H : α → ℝ} :
    ⋃ j : ℕ, heightDyadicShell H j = {x | 1 ≤ H x} := by
  ext x
  constructor
  · intro hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨j, hj⟩ := hx
    have hpowpos : 0 < 2 ^ j := pow_pos (by omega) _
    exact le_trans (by exact_mod_cast
      (Nat.one_le_iff_ne_zero.mpr hpowpos.ne')) hj.1
  · intro hx
    obtain ⟨j, hj⟩ := exists_mem_heightDyadicShell_of_one_le hx
    exact Set.mem_iUnion.2 ⟨j, hj⟩

theorem heightDyadicShell_finite {α : Type*} {H : α → ℝ} {p : ℕ}
    (hcount : HasHeightCountBounds H p) {j : ℕ} :
    (heightDyadicShell H j).Finite := by
  obtain ⟨cₗ, cᵤ, hcₗ, hcᵤ, hcut⟩ := hcount
  have hT : (1 : ℝ) ≤ ((2 ^ (j + 1) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega)))
  apply (hcut _ hT).1.subset
  intro x hx
  exact hx.2.le

theorem heightShell_finite {α : Type*} {H : α → ℝ} {p : ℕ}
    (hcount : HasHeightCountBounds H p) {n : ℕ} (hn : 1 ≤ n) :
    (heightShell H n).Finite := by
  obtain ⟨cₗ, cᵤ, hcₗ, hcᵤ, hcut⟩ := hcount
  have hT : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ n + 1)
  apply (hcut ((n + 1 : ℕ) : ℝ) hT).1.subset
  intro x hx
  exact hx.2.le

theorem heightShell_ncard_upper {α : Type*} {H : α → ℝ} {p : ℕ}
    (hcount : HasHeightCountBounds H p) :
    ∃ cᵤ : ℝ, 0 < cᵤ ∧ ∀ {n : ℕ}, 1 ≤ n →
      (Set.ncard (heightShell H n) : ℝ) ≤
        cᵤ * ((n + 1 : ℕ) : ℝ) ^ p := by
  obtain ⟨cₗ, cᵤ, hcₗ, hcᵤ, hcut⟩ := hcount
  refine ⟨cᵤ, hcᵤ, ?_⟩
  intro n hn
  have hT : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ n + 1)
  have hfinite :
      (Set.Finite {x | H x ≤ ((n + 1 : ℕ) : ℝ)}) :=
    (hcut ((n + 1 : ℕ) : ℝ) hT).1
  have hsubset : heightShell H n ⊆
      {x | H x ≤ ((n + 1 : ℕ) : ℝ)} := by
    intro x hx
    exact hx.2.le
  have hcard := Set.ncard_le_ncard hsubset hfinite
  have hupper := (hcut ((n + 1 : ℕ) : ℝ) hT).2.2
  have hcardR : (Set.ncard (heightShell H n) : ℝ) ≤
      (Set.ncard {x | H x ≤ ((n + 1 : ℕ) : ℝ)} : ℝ) := by
    exact_mod_cast hcard
  exact hcardR.trans hupper

theorem heightShell_inv_pow_le {α : Type*} {H : α → ℝ}
    {n q : ℕ} (hn : 0 < n) {x : α} (hx : x ∈ heightShell H n) :
    (H x)⁻¹ ^ q ≤ (n : ℝ)⁻¹ ^ q := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hHR : 0 < H x := lt_of_lt_of_le hnR hx.1
  have hinv : (H x)⁻¹ ≤ (n : ℝ)⁻¹ :=
    (inv_le_inv₀ hHR hnR).2 hx.1
  exact pow_le_pow_left₀ (inv_nonneg.mpr hHR.le) hinv q

/- Finite-shell form of the preceding pointwise estimate.  This is the
   summand bound used when a height sum is grouped by integer shells. -/
theorem heightShell_sum_inv_pow_le
    {α : Type*} {H : α → ℝ} {p n q : ℕ}
    (hcount : HasHeightCountBounds H p) (hn : 0 < n) :
    let hs := heightShell_finite hcount (by exact hn)
    (∑ x ∈ hs.toFinset, (H x)⁻¹ ^ q) ≤
      (Set.ncard (heightShell H n) : ℝ) * (n : ℝ)⁻¹ ^ q := by
  let hs := heightShell_finite hcount (by exact hn)
  letI : Fintype (heightShell H n) := hs.fintype
  have hsum : (∑ x ∈ hs.toFinset, (H x)⁻¹ ^ q) ≤
      ∑ x ∈ hs.toFinset, (n : ℝ)⁻¹ ^ q := by
    apply Finset.sum_le_sum
    intro x hx
    apply heightShell_inv_pow_le hn
    exact hs.mem_toFinset.mp hx
  have hcard : (Set.ncard (heightShell H n) : ℝ) =
      (hs.toFinset.card : ℝ) := by
    rw [Set.ncard_eq_toFinset_card (heightShell H n) hs]
  rw [hcard]
  simpa using hsum

/- Polynomial height counts give the summable shell majorant used in the
   paper's summation-by-parts argument.  The shift by one keeps every
   denominator strictly positive, while the strict gap `p + 1 < q` is the
   convergent range for the resulting p-series. -/
theorem summable_heightShell_inv_pow
    {α : Type*} {H : α → ℝ} {p q : ℕ}
    (hcount : HasHeightCountBounds H p) (hgap : p + 1 < q) :
    Summable (fun n : ℕ =>
      (Set.ncard (heightShell H (n + 1)) : ℝ) *
        (((n + 1 : ℕ) : ℝ)⁻¹ ^ q)) := by
  obtain ⟨cᵤ, hcᵤ, hcard⟩ := heightShell_ncard_upper hcount
  have hpq : p ≤ q := by omega
  have hqmp : 1 < q - p := by omega
  have hbase : Summable (fun n : ℕ =>
      (((n + 1 : ℕ) : ℝ)⁻¹ ^ (q - p))) := by
    have hbase0 : Summable (fun n : ℕ =>
        ((n : ℝ)⁻¹ ^ (q - p))) :=
      by simpa [inv_pow] using
        (Real.summable_nat_pow_inv (p := q - p)).mpr hqmp
    simpa [Nat.cast_add] using
      (summable_nat_add_iff (G := ℝ) (f := fun n : ℕ =>
        ((n : ℝ)⁻¹ ^ (q - p))) 1).2 hbase0
  have hbound : ∀ n : ℕ,
      (Set.ncard (heightShell H (n + 1)) : ℝ) *
          (((n + 1 : ℕ) : ℝ)⁻¹ ^ q) ≤
        (cᵤ * (2 : ℝ) ^ p) *
          (((n + 1 : ℕ) : ℝ)⁻¹ ^ (q - p)) := by
    intro n
    have hcardn := hcard (n := n + 1) (by omega)
    have hnpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hstep : ((n + 1 : ℕ) : ℝ) + 1 ≤ 2 * ((n + 1 : ℕ) : ℝ) := by
      have hone : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
      nlinarith
    have hpow : (((n + 1 : ℕ) : ℝ) + 1) ^ p ≤
        (2 * ((n + 1 : ℕ) : ℝ)) ^ p := by
      exact pow_le_pow_left₀ (by positivity) hstep p
    have hpow' : (((n + 2 : ℕ) : ℝ) ^ p) ≤
        (2 : ℝ) ^ p * ((n + 1 : ℕ) : ℝ) ^ p := by
      norm_num [Nat.cast_add, add_assoc, add_left_comm, add_comm, mul_pow] at hpow ⊢
      exact hpow
    calc
      (Set.ncard (heightShell H (n + 1)) : ℝ) *
          (((n + 1 : ℕ) : ℝ)⁻¹ ^ q) ≤
          (cᵤ * ((n + 2 : ℕ) : ℝ) ^ p) *
            (((n + 1 : ℕ) : ℝ)⁻¹ ^ q) := by
              exact mul_le_mul_of_nonneg_right hcardn (by positivity)
      _ ≤ (cᵤ * ((2 : ℝ) ^ p * ((n + 1 : ℕ) : ℝ) ^ p)) *
            (((n + 1 : ℕ) : ℝ)⁻¹ ^ q) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hpow' hcᵤ.le) (by positivity)
      _ = (cᵤ * (2 : ℝ) ^ p) *
            (((n + 1 : ℕ) : ℝ)⁻¹ ^ (q - p)) := by
              have hident : ((n + 1 : ℕ) : ℝ) ^ p *
                  (((n + 1 : ℕ) : ℝ)⁻¹ ^ q) =
                  (((n + 1 : ℕ) : ℝ)⁻¹ ^ (q - p)) := by
                simp only [inv_pow]
                field_simp [ne_of_gt hnpos]
                rw [← pow_add, Nat.add_sub_of_le hpq]
              calc
                (cᵤ * ((2 : ℝ) ^ p * ((n + 1 : ℕ) : ℝ) ^ p)) *
                    (((n + 1 : ℕ) : ℝ)⁻¹ ^ q) =
                    (cᵤ * (2 : ℝ) ^ p) *
                      (((n + 1 : ℕ) : ℝ) ^ p *
                        (((n + 1 : ℕ) : ℝ)⁻¹ ^ q)) := by ring
                _ = (cᵤ * (2 : ℝ) ^ p) *
                    (((n + 1 : ℕ) : ℝ)⁻¹ ^ (q - p)) := by rw [hident]
  apply Summable.of_nonneg_of_le (fun n => by positivity) hbound
  exact hbase.mul_left (cᵤ * (2 : ℝ) ^ p)

/- The shell majorant can be assembled into the actual reciprocal-height sum.
   We restrict to the positive-height part because the reciprocal power is
   used only for row spaces with `H ≥ 1` in the manuscript's tail argument. -/
theorem summable_height_inv_pow_of_one_le
    {α : Type*} {H : α → ℝ} {p q : ℕ}
    (hcount : HasHeightCountBounds H p) (hgap : p + 1 < q) :
    Summable (fun x : {x : α // 1 ≤ H x} => (H x.1)⁻¹ ^ q) := by
  let β := {x : α // 1 ≤ H x}
  let f : β → ℝ := fun x => (H x.1)⁻¹ ^ q
  let s : {n : ℕ // 1 ≤ n} → Set β :=
    fun n => {x | (x.1 : α) ∈ heightShell H n}
  have hs_unique : ∀ i : β, ∃! j : {n : ℕ // 1 ≤ n}, i ∈ s j := by
    intro i
    obtain ⟨n, hn, hin⟩ := exists_mem_heightShell_of_one_le i.2
    refine ⟨⟨n, hn⟩, hin, ?_⟩
    intro j hj
    apply Subtype.ext
    change (i : α) ∈ heightShell H j at hj
    exact mem_heightShell_unique hj hin
  have hs_finite : ∀ j, (s j).Finite := by
    intro j
    have hpre : ({x : β | (x : α) ∈ heightShell H j}).Finite := by
      apply (heightShell_finite hcount j.property).preimage
      intro x hx y hy hxy
      exact Subtype.ext hxy
    simpa [s] using hpre
  have hf_nonneg : ∀ i : β, 0 ≤ f i := by
    intro i
    apply pow_nonneg
    exact inv_nonneg.mpr (le_trans zero_le_one i.2)
  rw [summable_partition hf_nonneg hs_unique]
  constructor
  · intro j
    exact (hs_finite j).summable (fun i : β => f i)
  · let a : ℕ → ℝ := fun n =>
      (Set.ncard (heightShell H n) : ℝ) * ((n : ℝ)⁻¹ ^ q)
    have hshift : Summable (fun n : ℕ => a (n + 1)) := by
      simpa [a, Nat.cast_add_one] using
        (summable_heightShell_inv_pow hcount hgap)
    have ha : Summable a := (summable_nat_add_iff 1).1 hshift
    have ha_sub : Summable (fun j : {n : ℕ // 1 ≤ n} => a j) := by
      simpa [Function.comp_def] using ha.subtype (fun n : ℕ => 1 ≤ n)
    let g : {n : ℕ // 1 ≤ n} → ℝ := fun j => ∑' i : s j, f i
    change Summable g
    refine Summable.of_nonneg_of_le
      (f := fun j : {n : ℕ // 1 ≤ n} => a j) (g := g)
      (fun j => tsum_nonneg (fun i => hf_nonneg i))
      (fun j => ?_)
      ha_sub
    let hs := hs_finite j
    letI : Fintype (s j) := hs.fintype
    have hcard : Fintype.card (s j) =
        Set.ncard (heightShell H j) := by
      have himage : ((fun x : β => (x : α)) '' s j) = heightShell H j := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact hy
        · intro hx
          have hxone : 1 ≤ H x :=
            le_trans (by exact_mod_cast j.property) hx.1
          refine ⟨⟨x, hxone⟩, hx, rfl⟩
      have himcard : ((fun x : β => (x : α)) '' s j).ncard =
          (s j).ncard := by
        apply (Set.ncard_image_iff hs).2
        intro x hx y hy hxy
        exact Subtype.ext hxy
      calc
        Fintype.card (s j) = (s j).ncard := Set.fintypeCard_eq_ncard (s j)
        _ = ((fun x : β => (x : α)) '' s j).ncard := himcard.symm
        _ = Set.ncard (heightShell H j) := by rw [himage]
    have hinner : g j ≤ a j := by
      change (∑' i : s j, f i) ≤ a j
      rw [tsum_eq_sum (s := Finset.univ) (fun b hb =>
        (hb (Finset.mem_univ b)).elim)]
      calc
        (∑ x : s j, f x) ≤
            ∑ x : s j, ((j : ℝ)⁻¹ ^ q) := by
          apply Finset.sum_le_sum
          intro x hx
          have hjpos : 0 < (j : ℕ) :=
            lt_of_lt_of_le Nat.zero_lt_one j.property
          exact heightShell_inv_pow_le hjpos x.property
        _ = (Set.ncard (heightShell H j) : ℝ) * ((j : ℝ)⁻¹ ^ q) := by
          simp [Finset.sum_const, hcard]
        _ = a j := rfl
    exact hinner

theorem summable_heightDyadicShell_inv_pow
    {α : Type*} {H : α → ℝ} {p q : ℕ}
    (hcount : HasHeightCountBounds H p) (hpq : p < q) :
    Summable (fun j : ℕ =>
      (Set.ncard (heightDyadicShell H j) : ℝ) *
        (((2 ^ j : ℕ) : ℝ)⁻¹ ^ q)) := by
  obtain ⟨cₗ, cᵤ, hcₗ, hcᵤ, hcut⟩ := hcount
  have hcard : ∀ j : ℕ,
      (Set.ncard (heightDyadicShell H j) : ℝ) ≤
        cᵤ * ((2 ^ (j + 1) : ℕ) : ℝ) ^ p := by
    intro j
    have hT : (1 : ℝ) ≤ ((2 ^ (j + 1) : ℕ) : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega)))
    have hfinite :
        (Set.Finite {x | H x ≤ ((2 ^ (j + 1) : ℕ) : ℝ)}) :=
      (hcut _ hT).1
    have hsubset : heightDyadicShell H j ⊆
        {x | H x ≤ ((2 ^ (j + 1) : ℕ) : ℝ)} := by
      intro x hx
      exact hx.2.le
    have hcard' := Set.ncard_le_ncard hsubset hfinite
    have hcardR : (Set.ncard (heightDyadicShell H j) : ℝ) ≤
        (Set.ncard {x | H x ≤ ((2 ^ (j + 1) : ℕ) : ℝ)} : ℝ) := by
      exact_mod_cast hcard'
    exact hcardR.trans ((hcut _ hT).2.2)
  let d : ℕ := q - p
  have hd : 0 < d := by omega
  let r : ℝ := (2 : ℝ)⁻¹ ^ d
  have hr0 : 0 ≤ r := by
    exact pow_nonneg (by positivity) _
  have hr1 : r < 1 := by
    dsimp [r]
    apply pow_lt_one₀
    · positivity
    · norm_num
    · omega
  have hgeom : Summable (fun j : ℕ => r ^ j) :=
    summable_geometric_of_lt_one hr0 hr1
  have hbound : ∀ j : ℕ,
      (Set.ncard (heightDyadicShell H j) : ℝ) *
          (((2 ^ j : ℕ) : ℝ)⁻¹ ^ q) ≤
        (cᵤ * (2 : ℝ) ^ p) * r ^ j := by
    intro j
    have hcardj := hcard j
    have hstep : ((2 ^ (j + 1) : ℕ) : ℝ) =
        (2 : ℝ) * ((2 ^ j : ℕ) : ℝ) := by
      norm_num [pow_succ, Nat.cast_mul, mul_comm]
    have hbpos : 0 < ((2 ^ j : ℕ) : ℝ) := by positivity
    have hpow : ((2 ^ (j + 1) : ℕ) : ℝ) ^ p ≤
        (2 : ℝ) ^ p * ((2 ^ j : ℕ) : ℝ) ^ p := by
      rw [hstep, mul_pow]
    have hident : ((2 ^ j : ℕ) : ℝ) ^ p *
        (((2 ^ j : ℕ) : ℝ)⁻¹ ^ q) =
        (((2 ^ j : ℕ) : ℝ)⁻¹ ^ (q - p)) := by
      simp only [inv_pow]
      field_simp [ne_of_gt hbpos]
      rw [← pow_add, Nat.add_sub_of_le (by omega)]
    have hrident : (((2 ^ j : ℕ) : ℝ)⁻¹ ^ (q - p)) = r ^ j := by
      dsimp [r, d]
      calc
        (((2 ^ j : ℕ) : ℝ)⁻¹ ^ (q - p)) =
            (((2 : ℝ) ^ j)⁻¹ ^ (q - p)) := by norm_num
        _ = (((2 : ℝ)⁻¹) ^ j) ^ (q - p) := by rw [← inv_pow]
        _ = ((2 : ℝ)⁻¹) ^ (j * (q - p)) := by rw [pow_mul]
        _ = ((2 : ℝ)⁻¹) ^ ((q - p) * j) := by rw [Nat.mul_comm]
        _ = (((2 : ℝ)⁻¹) ^ (q - p)) ^ j := by rw [pow_mul]
    calc
      (Set.ncard (heightDyadicShell H j) : ℝ) *
          (((2 ^ j : ℕ) : ℝ)⁻¹ ^ q) ≤
          (cᵤ * ((2 ^ (j + 1) : ℕ) : ℝ) ^ p) *
            (((2 ^ j : ℕ) : ℝ)⁻¹ ^ q) := by
              exact mul_le_mul_of_nonneg_right hcardj (by positivity)
      _ ≤ (cᵤ * ((2 : ℝ) ^ p * ((2 ^ j : ℕ) : ℝ) ^ p)) *
            (((2 ^ j : ℕ) : ℝ)⁻¹ ^ q) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hpow hcᵤ.le) (by positivity)
      _ = (cᵤ * (2 : ℝ) ^ p) * r ^ j := by
              rw [show (cᵤ * ((2 : ℝ) ^ p * ((2 ^ j : ℕ) : ℝ) ^ p)) *
                    (((2 ^ j : ℕ) : ℝ)⁻¹ ^ q) =
                    (cᵤ * (2 : ℝ) ^ p) *
                      (((2 ^ j : ℕ) : ℝ) ^ p *
                        (((2 ^ j : ℕ) : ℝ)⁻¹ ^ q)) by ring]
              rw [hident, hrident]
  apply Summable.of_nonneg_of_le (fun j => by positivity) hbound
  exact hgeom.mul_left (cᵤ * (2 : ℝ) ^ p)

theorem heightDyadicShell_inv_pow_le {α : Type*} {H : α → ℝ}
    {j q : ℕ} {x : α} (hx : x ∈ heightDyadicShell H j) :
    (H x)⁻¹ ^ q ≤ (((2 ^ j : ℕ) : ℝ)⁻¹ ^ q) := by
  have hbpos : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
  have hHx : 0 < H x := lt_of_lt_of_le hbpos hx.1
  have hinv : (H x)⁻¹ ≤ ((2 ^ j : ℕ) : ℝ)⁻¹ :=
    (inv_le_inv₀ hHx hbpos).2 hx.1
  exact pow_le_pow_left₀ (inv_nonneg.mpr hHx.le) hinv q

theorem summable_height_inv_pow_of_one_le_dyadic
    {α : Type*} {H : α → ℝ} {p q : ℕ}
    (hcount : HasHeightCountBounds H p) (hpq : p < q) :
    Summable (fun x : {x : α // 1 ≤ H x} => (H x.1)⁻¹ ^ q) := by
  let β := {x : α // 1 ≤ H x}
  let f : β → ℝ := fun x => (H x.1)⁻¹ ^ q
  let s : ℕ → Set β :=
    fun j => {x | (x.1 : α) ∈ heightDyadicShell H j}
  have hs_unique : ∀ i : β, ∃! j : ℕ, i ∈ s j := by
    intro i
    obtain ⟨j, hij⟩ := exists_mem_heightDyadicShell_of_one_le i.2
    refine ⟨j, hij, ?_⟩
    intro j' hj'
    by_contra hne
    exact Set.disjoint_left.1 (heightDyadicShell_disjoint hne) hj' hij
  have hs_finite : ∀ j, (s j).Finite := by
    intro j
    have hpre : ({x : β | (x : α) ∈ heightDyadicShell H j}).Finite := by
      apply (heightDyadicShell_finite hcount).preimage
      intro x hx y hy hxy
      exact Subtype.ext hxy
    simpa [s] using hpre
  have hf_nonneg : ∀ i : β, 0 ≤ f i := by
    intro i
    apply pow_nonneg
    exact inv_nonneg.mpr (le_trans zero_le_one i.2)
  rw [summable_partition hf_nonneg hs_unique]
  constructor
  · intro j
    exact (hs_finite j).summable (fun i : β => f i)
  · let a : ℕ → ℝ := fun j =>
      (Set.ncard (heightDyadicShell H j) : ℝ) *
        (((2 ^ j : ℕ) : ℝ)⁻¹ ^ q)
    have ha : Summable a := by
      simpa [a] using summable_heightDyadicShell_inv_pow hcount hpq
    let g : ℕ → ℝ := fun j => ∑' i : s j, f i
    change Summable g
    refine Summable.of_nonneg_of_le
      (f := a) (g := g)
      (fun j => tsum_nonneg (fun i => hf_nonneg i))
      (fun j => ?_) ha
    let hs := hs_finite j
    letI : Fintype (s j) := hs.fintype
    have hcard : Fintype.card (s j) =
        Set.ncard (heightDyadicShell H j) := by
      have himage : ((fun x : β => (x : α)) '' s j) = heightDyadicShell H j := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact hy
        · intro hx
          have hpowone : 1 ≤ 2 ^ j :=
            Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
          have hpowoneR : (1 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
            exact_mod_cast hpowone
          have hxone : 1 ≤ H x := hpowoneR.trans hx.1
          refine ⟨⟨x, hxone⟩, hx, rfl⟩
      have himcard : ((fun x : β => (x : α)) '' s j).ncard =
          (s j).ncard := by
        apply (Set.ncard_image_iff hs).2
        intro x hx y hy hxy
        exact Subtype.ext hxy
      calc
        Fintype.card (s j) = (s j).ncard := Set.fintypeCard_eq_ncard (s j)
        _ = ((fun x : β => (x : α)) '' s j).ncard := himcard.symm
        _ = Set.ncard (heightDyadicShell H j) := by rw [himage]
    have hinner : g j ≤ a j := by
      change (∑' i : s j, f i) ≤ a j
      rw [tsum_eq_sum (s := Finset.univ) (fun b hb =>
        (hb (Finset.mem_univ b)).elim)]
      calc
        (∑ x : s j, f x) ≤
            ∑ x : s j, (((2 ^ j : ℕ) : ℝ)⁻¹ ^ q) := by
          apply Finset.sum_le_sum
          intro x hx
          exact heightDyadicShell_inv_pow_le x.property
        _ = (Set.ncard (heightDyadicShell H j) : ℝ) *
            (((2 ^ j : ℕ) : ℝ)⁻¹ ^ q) := by
          simp [Finset.sum_const, hcard]
        _ = a j := rfl
    exact hinner

/- Imported source theorem.  This is intentionally an explicit interface so
   later Lean proofs can distinguish the cited height count from new
   consequences proved in this repository. -/
axiom schmidt_rowSpaceHeight_count
    {m k : ℕ} (hk : 0 < k) (hkm : k < m) :
    HasHeightCountBounds (rowSpaceHeight (K := K) (m := m) (k := k)) m

/- Specialization to the row-space height.  Schmidt's theorem supplies the
   polynomial exponent `m`; the analytic shell summation is proved locally
   above rather than being hidden inside the imported interface. -/
theorem summable_rowSpaceHeightShell_inv_pow
    {m k q : ℕ} (hk : 0 < k) (hkm : k < m) (hgap : m + 1 < q) :
    Summable (fun n : ℕ =>
      (Set.ncard (heightShell
        (rowSpaceHeight (K := K) (m := m) (k := k)) (n + 1)) : ℝ) *
        (((n + 1 : ℕ) : ℝ)⁻¹ ^ q)) := by
  exact summable_heightShell_inv_pow
    (schmidt_rowSpaceHeight_count (K := K) hk hkm) hgap

theorem summable_rowSpaceHeight_inv_pow_of_one_le
    {m k q : ℕ} (hk : 0 < k) (hkm : k < m) (hgap : m + 1 < q) :
    Summable (fun V : {V : Grassmannian K m k //
      1 ≤ rowSpaceHeight V} => (rowSpaceHeight V.1)⁻¹ ^ q) := by
  exact summable_height_inv_pow_of_one_le
    (schmidt_rowSpaceHeight_count (K := K) hk hkm) hgap

/- This is the version used by the manuscript's tail estimate: Schmidt's
   exponent is `m`, and the reciprocal power is summable for every `m < q`.
   The dyadic grouping above is a formal counterpart of the paper's
   summation-by-parts step. -/
theorem summable_rowSpaceHeight_inv_pow_of_one_le_of_lt
    {m k q : ℕ} (hk : 0 < k) (hkm : k < m) (hmq : m < q) :
    Summable (fun V : {V : Grassmannian K m k //
      1 ≤ rowSpaceHeight V} => (rowSpaceHeight V.1)⁻¹ ^ q) := by
  exact summable_height_inv_pow_of_one_le_dyadic
    (schmidt_rowSpaceHeight_count (K := K) hk hkm) hmq

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
